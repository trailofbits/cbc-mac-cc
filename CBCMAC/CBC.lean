import Commons.Definitions.Ideal
import ConstructiveCryptography.Notation
import CBCMAC.Upstream.Program
import CBCMAC.Upstream.Resource

/-!
# The CBC construction

CR18 §6.2.3 (printed pp. 125–126). The CBC function folds encoded blocks through a round
function from zero. The converter `cbc` computes it against a primitive answering at the
interface `Evaluation X X` of a function, with one inside call per block, so messages of
different lengths use the same converter. The filter `θ` restricts a system on messages to
histories of at most `q` encoded blocks in total. Against a fixed round function, CBC makes the
calls of the fold of a message's blocks and returns their CBC value, so attached to that
function it is the CBC function on messages. After `θ`, CBC makes at most `q` primitive queries:
`θ ≫ cbc` is CBC typed by encoded blocks, `cbc.exact`, followed by the query filter `⟪q⟫`
(CR18's equation (6.1)).

## Main definitions

* `URF X Y`: the uniform random function from `X` to `Y` (local notation for `Commons.URF`)
* `cbcFunction f blocks`: the CBC function
* `cbc blockForm`: CBC as a converter, and `cbc.exact` its typing by encoded blocks
* `θ blockForm q`: at most `q` encoded blocks, on the interface `MessageBlocks blockForm q n`

## Main results

* `cbc_exchanges`, `cbc_answer`: CBC against a round function
* `cbc_smul_ofFunction`: CBC on a function is the CBC function on messages
* `theta_cbc_eq`: CR18's equation (6.1), `θ ≫ cbc = cbc.exact ≫ ⟪q⟫`
-/

open SystemAlgebra SystemAlgebra.DSL Probability Commons CategoryTheory
open scoped SystemAlgebra SystemAlgebra.DSL

namespace CBCMAC

/-- The uniform random function from `X` to `Y`, answering at the interface `Evaluation X Y`. -/
scoped notation "URF " X:max Y:max => Commons.URF (Evaluation X Y _)

section CBCFunction

universe u

variable {X : Type u} [Zero X] [Add X]

/-- CR18 §6.2.3 (printed p. 125): the CBC function, folding the blocks through the round
function `f` from zero. -/
def cbcFunction (f : X → X) (blocks : List X) : X :=
  blocks.foldl (fun chaining block => f (chaining + block)) 0

@[simp]
theorem cbcFunction_append (f : X → X) (blocks : List X) (block : X) :
    cbcFunction f (blocks ++ [block]) = f (cbcFunction f blocks + block) := by
  simp [cbcFunction]

end CBCFunction

variable {M X : Type} [Fintype M] [Fintype X] [Zero X] [Add X]

-- CR18 §6.2.3 (printed p. 125): fold the encoded blocks from zero, querying the primitive on
-- the sum of the previous reply and the next block. `cbc` makes at most `cbc.bound` primitive
-- queries per message; each message costs one query per encoded block, so `cbc.exact` acts from
-- `q` primitive queries to `q` encoded blocks in total.
converter cbc(blockForm : M → List X) : Evaluation M X
  inside primitive : Evaluation X X
  on eval(message : M) → X
    tag ← (0 : X)
    for block ∈ blockForm message
      tag ← primitive.eval(tag + block)
    return tag

omit [Add X] in
/-- A message costs one primitive query per encoded block. -/
@[simp] theorem cbc_cost (blockForm : M → List X) (i : (Evaluation M X 0).I) (message : M) :
    cbc.cost blockForm i message = (blockForm message).length := by
  cases i
  simp [cbc.cost]

-- CR18 §6.2.3 (printed p. 126): forward messages while at most `q` encoded blocks, the cost of
-- `cbc`, have been submitted in total, then stop.
filter θ(blockForm : M → List X) (q : ℕ) : Evaluation M X
  domain us ↦ (us.map fun u => cbc.cost blockForm u.1 u.2).sum ≤ q

/-- Message histories of at most `q` encoded blocks in total: the outside interface of `θ`, and of
`cbc.exact`. -/
abbrev MessageBlocks (blockForm : M → List X) (q n : ℕ) : Interface :=
  (Evaluation M X n).restrict (fun us => (us.map fun u => cbc.cost blockForm u.1 u.2).sum ≤ q)
    (cost_prefix_closed _ _)

/-- **CBC against a round function**: from every state, against `f`, CBC makes the calls of the
fold of a message's blocks itself and then returns their CBC value. -/
theorem cbc_exchanges (blockForm : M → List X) (f : X → X) (t : Option (TypeOf ())) (m : M) :
    (cbc.body blockForm).Consistent t .eval m
        (foldTranscript Evaluation.Port.eval (fun tag block => tag + block) (fun _ _ y => y) f
          (blockForm m) 0) ∧
      cbc.body blockForm t .eval m
          (foldTranscript Evaluation.Port.eval (fun tag block => tag + block) (fun _ _ y => y) f
            (blockForm m) 0) =
        .inl (some (), cbcFunction f (blockForm m)) := by
  have body : cbc.body blockForm t .eval m =
      (blockForm m).foldr (fun b next (c : M × X) => callProg .eval (c.2 + b)
        (fun y => next (c.1, y))) (fun c => returnProg (some (), c.2)) (m, 0) := by
    cases t <;> rfl
  have fold := foldr_call_const (A := Option (TypeOf ()) × X) (X := (Evaluation X X 0).X)
    (Y := (Evaluation X X 0).Y) Evaluation.Port.eval (fun _ tag block => tag + block)
    (fun _ _ _ y => y) (fun _ tag => (some (), tag)) (blockForm m) m 0
  refine ⟨?_, ?_⟩
  · show Program.ExchangesOf (cbc.body blockForm t .eval m) _
    rw [body, fold]
    exact exchangesOf_foldTranscript (X := (Evaluation X X 0).X) (Y := (Evaluation X X 0).Y) _ _ _
      f _ _ _
  · rw [body, fold, foldr_call_foldTranscript]
    rfl

/-- A message makes at most `cbc.bound` primitive calls: one per encoded block. -/
theorem cbc_length_le_bound (blockForm : M → List X) (m : M) :
    (blockForm m).length ≤ cbc.bound blockForm := by
  simpa only [foldTranscript_length] using
    (cbc_exchanges blockForm id none m).1.length_le (cbc.bound_spec blockForm)

/-- Against the round function `f`, CBC answers each message with the CBC function of its
blocks. -/
theorem cbc_answer (blockForm : M → List X) (f : X → X) (t : Option (TypeOf ())) (m : M) :
    (cbc.body blockForm).answer (fun _ => f) t .eval m (cbc.bound blockForm) [] =
      some (some (), cbcFunction f (blockForm m)) :=
  Program.answer_of_exchanges (cbc_exchanges blockForm f t m).1
    (foldTranscript_answers _ _ _ (fun _ => f) _ _) (cbc_exchanges blockForm f t m).2 _
    ((cbc_exchanges blockForm f t m).1.length_le (cbc.bound_spec blockForm))

/-- **CBC on a function** is the CBC function on messages. -/
theorem cbc_smul_ofFunction (blockForm : M → List X) {n : ℕ} (f : X → X) :
    cbc blockForm (budget := n) • Interface.Resource.ofFunction (fun _ => f) =
      Interface.Resource.ofFunction (fun _ m => cbcFunction f (blockForm m)) := by
  unfold cbc cbc.program Interface.Converter.ofProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction (A := Evaluation M X n)
    (B := Evaluation X X (cbc.bound blockForm * n)) none (cbc.body blockForm)
    (cbc.bound_spec blockForm) _ (fun _ => f) (fun _ m => cbcFunction f (blockForm m))
    fun t o m => ?_
  cases o
  exact ⟨_, cbc_answer blockForm f t m⟩

/-- **CR18's equation (6.1)** (printed p. 126): after `θ`, CBC makes at most `q` primitive
queries. `θ ≫ cbc` is CBC typed by encoded blocks, `cbc.exact`, followed by the query filter from
`q` queries to CBC's inside budget. -/
theorem theta_cbc_eq (blockForm : M → List X) {q n : ℕ} (hq : q ≤ cbc.bound blockForm * n) :
    θ blockForm q (budget := n) ≫ cbc blockForm =
      cbc.exact blockForm (budget := q) (queries := n) ≫ Interface.queryFilter _ _ _ hq := by
  have hprog := (DDC.ofProgram_isResponsiveDDC (s := none) (cbc.bound_spec blockForm)).isDDC
  rw [Interface.comp_eq, Interface.comp_eq]
  unfold θ Interface.filter cbc cbc.program Interface.Converter.ofProgram cbc.exact
    Interface.Converter.ofCostedProgram Interface.queryFilter Interface.ofDDC
  rw [PDCBehavior.comp_ofDDC, PDCBehavior.comp_ofDDC]
  refine PDCBehavior.ofDDC_eq_of_le _ _ (W := DDC.ofProgram none (cbc.body blockForm)) ?_ ?_
  · intro xs ys hr
    rw [← IsDDC.trim_id_serialM hprog, replies_trim_iff]
    rw [replies_trim_iff] at hr
    unfold serialM at hr ⊢
    refine hr.interconnect_mono (pair_mono (fun h y hy => ?_) (fun h y hy => ?_))
    · exact ((filterDom_mem_iff _ _ h y).mp hy).2
    · exact ((filterDom_mem_iff _ _ h y).mp hy).2
  · intro xs ys hr
    rw [← IsDDC.trim_serialM_id hprog, replies_trim_iff]
    rw [replies_trim_iff] at hr
    unfold serialM at hr ⊢
    refine hr.interconnect_mono (pair_mono (fun h y hy => ?_) (fun h y hy => ?_))
    · exact ((filterDom_mem_iff _ _ h y).mp hy).2
    · exact ((filterDom_mem_iff _ _ h y).mp hy).2

end CBCMAC
