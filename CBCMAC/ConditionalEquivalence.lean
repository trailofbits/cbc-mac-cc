import CBCMAC.Combinatorics
import RandomSystems.RandomFunction
import RandomSystems.Technique.ConditionalEquivalence.FunctionEvaluator

set_option autoImplicit false

/-!
# Conditional equivalence of CBC and a uniform random function

Conditioned on the absence of a nontrivial collision between inputs to the
round function, CBC has the transcript law of a uniform random function.
-/

namespace CBCMAC

noncomputable section

open Classical
open Probability
open RandomSystems
open RandomSystems.ConditionalEquivalence

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-- CBC is conditionally equivalent to a uniform random function when the
supplied monotone condition records exactly its nontrivial round-input
collisions. -/
theorem cbc_conditionallyEquivalent_urf_of_condition_eq_cbcBad
    [Nontrivial M]
    (blockForm : M → List X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (condition : (X → X) → System.MC M)
    (condition_eq_cbcBad : ∀ function messages,
      (condition function).1 messages = decide
        (CBCCombinatorics.cbcBad function blockForm messages)) :
    RandomSystems.PDG.ofFunction
        (RandomFunction.uniform X X).law.1
        (fun function message =>
          CBCCombinatorics.cbc function (blockForm message))
        condition |≡ (RandomFunction.uniform M X : RandomSystems.PDS M X) := by
  unfold RandomFunction.toPDS RandomFunction.uniform Distribution.PMF
  apply ConditionalEquivalence.ofFunction_of_mass_eq
    (initiallyFalse := by
      intro function _
      rw [condition_eq_cbcBad]
      simp [CBCCombinatorics.cbcBad])
    (targetProbability := Distribution.uniform_isProbDist)
  intro messages answers
  simp_rw [condition_eq_cbcBad]
  simpa only [decide_eq_false_iff_not] using
    CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq
      blockForm prefixFree messages answers

end

end CBCMAC
