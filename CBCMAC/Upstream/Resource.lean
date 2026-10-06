import ConstructiveCryptography.Functional
import ConstructiveCryptography.InterfaceFilter
import ConstructiveCryptography.DSL.Converters
import CBCMAC.Upstream.ProgramAttachment

/-!
# Upstream candidates: converters on sampled functions

Candidates for `ConstructiveCryptography.Functional`, `ConstructiveCryptography.InterfaceFilter`
(`Interface.queryFilter`) and `ConstructiveCryptography.DSL.Converters`
(`Interface.ofDDC_ofProgramOn_smul_ofFunction`, beside `ofDDC_ofProgramOn_smul_ofAutomaton`).
Sampling along a map samples the composite;
attaching a converter to a sampled resource attaches it to each sample; a filter on a function is
the function on the restricted interface;
a function is a deterministic resource, and the converter of a program attached to a function
is the function the program computes against it; the query filter forwards at most `q` queries
to an interface admitting more.

## Main definitions

* `Interface.queryFilter`: the query filter from `q` queries to `B ≥ q`

## Main results

* `Interface.Resource.sample_fTransform`: sampling along a map
* `Interface.Resource.smul_sample`: attaching to a sampled resource
* `Interface.filter_smul_ofFunction`: a filter on a function
* `Interface.Resource.ofFunction_eq_ofDeterministic`: a function as a deterministic resource
* `Interface.ofDDC_ofProgramOn_smul_ofFunction`: the converter of a program on a function
-/

namespace SystemAlgebra.Interface

open Classical Probability

variable {A : Interface}

/-- **Sampling along a map** samples the composite. -/
theorem Resource.sample_fTransform {K K' : Type} (φ : K → K') (P : Distribution K)
    [Distribution.IsProbability P] (R : K' → Resource A) :
    Resource.sample (Distribution.fTransform φ P) R = Resource.sample P (fun k => R (φ k)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Resource.sample_mass, Resource.sample_mass]
  exact Distribution.sum_fTransform_mul φ P (fun k => (R k).1 h)

/-- **Attaching to a sampled resource** attaches to each sample. -/
theorem Resource.smul_sample {B : Interface} (α : A ⟶ B) {K : Type} (P : Distribution K)
    [Distribution.IsProbability P] (R : K → Resource B) :
    α • Resource.sample P R = Resource.sample P (fun k => α • R k) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Resource.sample_mass]
  change (RandomSystem.parallel α.1 (RandomSystem.mix _ fun k => (R k).1)).connectionLaw
    resourceRoute resourceInput (h.map Prod.fst) _ (h.map Prod.snd) = _
  rw [RandomSystem.parallel_mix_right, RandomSystem.connectionLaw_mix]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- **A filter on a function** is the function on the restricted interface. -/
theorem filter_smul_ofFunction (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) (f : ∀ i, A.X i → A.Y i) :
    filter A D hD • Resource.ofFunction f = Resource.ofFunction (A := A.restrict D hD) f := by
  apply Subtype.ext
  rw [filter_smul]
  ext h
  change (if Admitted _ h then _ else _) = _
  rw [admitted_ofInputs_iff (A.restrict D hD).nonempty_prefix, Resource.ofFunction_mass,
    Resource.ofFunction_mass]
  by_cases hd : h = [] ∨ (A.restrict D hD).domain (h.map Prod.fst)
  · have hA : h = [] ∨ A.domain (h.map Prod.fst) := hd.imp id fun hd => hd.1
    simp only [hd, hA, true_and, ↓reduceIte]
  · rw [if_neg hd, if_neg fun hc => hd hc.1]

/-- **A function is a deterministic resource**: the system of the function on the interface's
domain. -/
theorem Resource.ofFunction_eq_ofDeterministic (g : ∀ i, A.X i → A.Y i) :
    Resource.ofFunction g = ofDeterministic (filterDom A.domain (functionSystem g))
      ⟨(functionSystem_isDDS g).filterDom _ A.nonempty_prefix.2,
        fun h x y hy => functionSystem_replies g h x y ((filterDom_mem_iff _ _ _ _).mp hy).2,
        fun h => by
          rw [filterDom_dom, functionSystem_dom]
          exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => A.nonempty_prefix.1 (he ▸ hd)⟩⟩⟩ := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  have replies : h.map Prod.snd = (h.map Prod.fst).map (fun x => ⟨x.1, g x.1 x.2⟩) ↔
      ∀ z ∈ h, z.2 = ⟨z.1.1, g z.1.1 z.1.2⟩ := by
    rw [List.map_map, List.map_eq_map_iff]
    rfl
  have evaluator : filterDom A.domain (functionSystem g) =
      (DDS.ofFunction A.domain A.nonempty_prefix (fun x => ⟨x.1, g x.1 x.2⟩)).1 := rfl
  rw [Resource.ofFunction_mass, ofDeterministic_mass, evaluator, DDS.replies_ofFunction_iff, replies,
    List.map_eq_nil_iff]
  congr 1

/-- **The converter of a program on a function**: if, against `g`, every invocation on `u`
returns `f u` from every state, attaching the program's converter to the function `g` gives the
function `f`. -/
theorem ofDDC_ofProgramOn_smul_ofFunction {B : Interface} {S : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    (g : ∀ j, B.X j → B.Y j) (f : ∀ o, A.X o → A.Y o)
    (answers : ∀ t o u, ∃ t', P.answer g t o u b [] = some (t', f o u)) :
    Interface.ofDDC (DDC.ofProgramOn s P A.domain) hα • Resource.ofFunction g =
      Resource.ofFunction f := by
  rw [Resource.ofFunction_eq_ofDeterministic g, Resource.ofFunction_eq_ofDeterministic f]
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [ofDeterministic, ofDDC_ofProgramOn_smul_ofPDS s P hb hα, Distribution.mass_single,
    ← Program.trim_apply_ofProgramOn s hb A.domain A.nonempty_prefix.2,
    Program.trim_apply_ofProgramOn_function hb g f s answers B.nonempty_prefix A.nonempty_prefix
      hα, ofDeterministic_mass]

/-- **The query filter** from `q` queries to `B ≥ q` (CR18, §3.4.3, printed p. 62): it forwards
the queries of a history of at most `q`. -/
noncomputable def queryFilter (I : Type) [Fintype I] (X Y : I → Type) [∀ i, Fintype (X i)]
    [∀ i, Fintype (Y i)] {q B : ℕ} (hqB : q ≤ B) : queryBudget I X Y q ⟶ queryBudget I X Y B :=
  ofDDC (DDC.filter (Y := Y) (fun h => h = [] ∨ (queryBudget I X Y q).domain h)
      (prefix_or_nil (queryBudget I X Y q).nonempty_prefix.2)).1
    ((isDDCFrom_filter (queryBudget I X Y q).nonempty_prefix).inside_mono
      fun _ hd => ⟨hd.1, hd.2.trans hqB⟩)

end SystemAlgebra.Interface
