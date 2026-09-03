import CBCMAC.Combinatorics
import RandomSystems.Converter.QueryLimit
import RandomSystems.RandomFunction

set_option autoImplicit false

/-!
# CBC-MAC random-system objects

CR18, Section 6.2.3 (printed p. 125), defines CBC by digesting the block-former
output against a round function and returning the final state.

The argument `blockForm` is the block sequence after the source's prefix-free
encoding and zero padding; this module does not implement that encoding.  The
finite type `M` is the repository's bounded-message specialization needed by
the normalized finite-support PDS carrier.  Replacing bitwise XOR by an
arbitrary additive commutative group is a repository generalization.

The CBC DDC and the application-specific restrictions are functions on
complete histories. Rejection by a partial round-function DDS is forwarded as
outer rejection; this is a repository extension of the source's total random
function case.
-/

namespace CBCMAC

noncomputable section

open Probability (Distribution)
open RandomSystems.Ambient

universe u

variable {X M : Type u}

/-- Extract all successful answers, returning `none` when any attempted inner
query was rejected. -/
def answerValues : List (Option X) → Option (List X)
  | [] => some []
  | none :: _ => none
  | some answer :: remaining =>
      (answerValues remaining).map (answer :: ·)

lemma answerValues_eq_some_iff {answers : List (Option X)}
    {values : List X} :
    answerValues answers = some values ↔ answers = values.map some := by
  -- Traverse the attempted replies and distinguish rejection from success.
  induction answers generalizing values with
  | nil => simp [answerValues]
  | cons answer remaining inductionHypothesis =>
      cases answer with
      | none =>
          constructor
          · simp [answerValues]
          · intro equal
            cases values <;> cases equal
      | some answer =>
          cases values with
          | nil => simp [answerValues]
          | cons value values =>
              simp [answerValues, inductionHypothesis, and_comm]

lemma answerValues_map_some (values : List X) :
    answerValues (values.map some) = some values :=
  -- Every reply in the list is successful.
  answerValues_eq_some_iff.mpr rfl

/-- CBC's response after the displayed inner replies of the current message.
The first missing inner answer closes the round with rejection. -/
def response [AddMonoid X] (blockForm : M → List X)
    (message : M) (answers : List (Option X)) : X ⊕ Option X :=
  match answerValues answers with
  | none => Sum.inr none
  | some values =>
      if values.length < (blockForm message).length then
        Sum.inl (values.getLastD 0 +
          (blockForm message).getD values.length 0)
      else
        Sum.inr (some (values.getLastD 0))

/-- At the uniform block bound CBC must close the current outer round. -/
def closeResponse [AddMonoid X] (_ : M)
    (answers : List (Option X)) : Option X :=
  (answerValues answers).map (fun values => values.getLastD 0)

/-! ## Deterministic CBC recurrence equations -/

/-- Successful CBC values after the first `count` block positions. -/
def successfulValues [AddMonoid X] (function : X → X)
    (blocks : List X) (count : Nat) : List X :=
  (List.range count).map fun position =>
    CBCCombinatorics.cbc function (blocks.take (position + 1))

/-- The corresponding complete list of successful inner replies. -/
def successfulReplies [AddMonoid X] (function : X → X)
    (blocks : List X) (count : Nat) : List (Option X) :=
  (successfulValues function blocks count).map some

@[simp]
lemma successfulReplies_length [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    (successfulReplies function blocks count).length = count := by
  -- There is one successful reply for each enumerated block position.
  simp [successfulReplies, successfulValues]

@[simp]
lemma successfulValues_length [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    (successfulValues function blocks count).length = count := by
  -- The range enumerating positions has the requested length.
  simp [successfulValues]

lemma successfulReplies_succ [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    successfulReplies function blocks (count + 1) =
      successfulReplies function blocks count ++
        [some (CBCCombinatorics.cbc function
          (blocks.take (count + 1)))] := by
  -- Extending the position range appends the next CBC state.
  simp [successfulReplies, successfulValues, List.range_succ]

lemma successfulValues_getLastD [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    (successfulValues function blocks count).getLast?.getD 0 =
        CBCCombinatorics.cbc function (blocks.take count) := by
  -- Split the empty prefix from a positive prefix.
  cases count with
  | zero => simp [successfulValues, CBCCombinatorics.cbc]
  | succ count =>
      simp [successfulValues, List.range_succ]

lemma cbc_take_succ [AddMonoid X]
    (function : X → X) (blocks : List X) {count : Nat}
    (below : count < blocks.length) :
    CBCCombinatorics.cbc function (blocks.take (count + 1)) =
      function (CBCCombinatorics.cbcInput function blocks count) := by
  -- Expose the next block at the end of the taken prefix.
  rw [List.take_add_one, List.getElem?_eq_getElem below]
  simp only [Option.toList_some]
  rw [CBCCombinatorics.cbc_append]
  -- The appended-block recurrence uses the same block selected at this position.
  congr 2
  rw [List.getD_eq_getElem _ _ below]

lemma response_successfulReplies_of_lt [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M)
    {count : Nat} (below : count < (blockForm message).length) :
    response blockForm message
        (successfulReplies function (blockForm message) count) =
      Sum.inl (CBCCombinatorics.cbcInput function
        (blockForm message) count) := by
  -- Successful prior replies expose precisely the next feedback input.
  simp [response, successfulReplies, answerValues_map_some,
    successfulValues_length, below, CBCCombinatorics.cbcInput,
    successfulValues_getLastD]

lemma response_successfulReplies_length [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M) :
    response blockForm message
        (successfulReplies function (blockForm message)
          (blockForm message).length) =
      Sum.inr (some (CBCCombinatorics.cbc function
        (blockForm message))) := by
  -- At the encoded length, the response closes with the final CBC state.
  simp [response, successfulReplies, answerValues_map_some,
    successfulValues_length, successfulValues_getLastD]

/-- Bounded-inner-query DDC presentation of the CBC converter from CR18,
Section 6.2.3. -/
def cbc [Fintype M] [AddMonoid X] (blockForm : M → List X) :
    DDC (Interface.single M X) (Interface.single X X) :=
  DDC.ofBoundedInnerQueries (CBCCombinatorics.blockBound blockForm)
    (fun message answers _ => response blockForm message answers)
    closeResponse

scoped notation:max "CBC[" blockForm "]" => DDC.asHom (cbc blockForm)

/-- The total-block restriction `θ`. -/
def theta (blockForm : M → List X) (limit : Nat) :
    RandomSystems.DomainFilter M where
  predicate messages :=
    CBCCombinatorics.totalBlocks blockForm messages ≤ limit
  prefixClosed _ _ isPrefix admitted :=
    (CBCCombinatorics.totalBlocks_mono blockForm isPrefix).trans admitted

/-- Exact complete-history equation for the block-count restriction. -/
lemma applySystem_theta
    (blockForm : M → List X) (limit : Nat)
    (system : DDS (Interface.single M X)) :
    applySystem ((theta blockForm limit).toDDC (Y := X)) system =
      fun history =>
        if CBCCombinatorics.totalBlocks blockForm history.queries ≤ limit then
          system history
        else
          none := by
  classical
  unfold RandomSystems.DomainFilter.toDDC
  rw [DDC.applySystem_filter_of_prefix_closed
    (theta blockForm limit).predicate
    (fun {_ _} isPrefix admitted =>
      (theta blockForm limit).prefixClosed isPrefix admitted)
    id (fun (_ : M) (answer : Option X) => answer) system]
  funext history
  by_cases admitted :
      CBCCombinatorics.totalBlocks blockForm history.queries ≤ limit
  · have restricted :
        (theta blockForm limit).predicate history.queries :=
      admitted
    rw [if_pos restricted, if_pos admitted, History.map_id]
  · have restricted :
        ¬ (theta blockForm limit).predicate history.queries :=
      admitted
    rw [if_neg restricted, if_neg admitted]

/-- CBC applied to a finite random function. -/
def cbcPDS [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (roundFunction : RandomSystems.RandomFunction X X) :
    PDS (Interface.single M X) :=
  ⟨Distribution.fTransform
      (fun function : X → X =>
        DDS.ofFunction (A := Interface.single M X) (fun message =>
          CBCCombinatorics.cbc function (blockForm message)))
      roundFunction.law.1,
    Distribution.fTransform_isProbDist _
      roundFunction.law.2⟩

/-- The fixed-interface law of CBC over a round-function law, as a
`functionEvaluator` pushforward. Distinct from converter attachment
`CBC[blockForm] • R`, which acts on ambient systems. -/
scoped notation:max "CBCLaw[" blockForm "] " roundFunction:max =>
  Distribution.fTransform
    (fun function =>
      RandomSystems.System.functionEvaluator fun message =>
        CBCCombinatorics.cbc function (blockForm message))
    (roundFunction : Distribution (_ → _))

end


end CBCMAC
