import CBCMAC.Combinatorics
import RandomSystems.Game.FunctionEvaluator
import RandomSystems.RandomFunction
import RandomSystems.Technique.ConditionalEquivalence
import RandomSystems.Technique.ConditionalEquivalence.Blind

set_option autoImplicit false

/-!
# CBC blind winning probability

CR18, Theorem 6.1 (printed pp. 126--127), reduces CBC security to the
probability that its collision condition is reached under the total-block
restriction.
-/

namespace CBCMAC

noncomputable section

open Classical
open Probability
open RandomSystems
open RandomSystems.ConditionalEquivalence

universe u

variable {X M : Type u}

/-- Histories using at most `q` encoded blocks are prefix-closed. -/
lemma prefixClosed_totalBlocks_le (blockForm : M → List X) (q : Nat) :
    RandomSystems.PrefixClosed
      (fun messages => CBCCombinatorics.totalBlocks blockForm messages ≤ q) :=
  fun _ _ isPrefix admitted =>
    (CBCCombinatorics.totalBlocks_mono blockForm isPrefix).trans admitted

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [DecidableEq M]

/-- CR18, Theorem 6.1: the blind winning probability of the restricted CBC
collision game is at most `q² / (2 |X|)` (printed pp. 126--127). -/
theorem supWinProb_blind_filterDom_cbc_le
    (blockForm : M → List X) (q : Nat)
    (condition : (X → X) → System.MC M)
    (condition_eq_cbcBad : ∀ function messages,
      (condition function).1 messages =
        decide (CBCCombinatorics.cbcBad function blockForm messages)) :
    Γ(RandomSystems.PDG.blind
        (RandomSystems.PDG.filterDom
          (fun messages =>
            CBCCombinatorics.totalBlocks blockForm messages ≤ q)
          (prefixClosed_totalBlocks_le blockForm q)
          (RandomSystems.PDG.ofFunction
            (RandomFunction.uniform X X).law.1
            (fun function message =>
              CBCCombinatorics.cbc function (blockForm message))
            condition))) ≤
      (q : ℝ) ^ 2 / (2 * Fintype.card X) := by
  unfold RandomFunction.uniform RandomSystems.PDG.ofFunction
  refine RandomSystems.PDG.supWinProb_blind_filterDom_fTransform_le
      (source := Distribution.uniform (X → X))
      (toGame := fun function =>
        System.DDG.ofFunction
          (fun message =>
            CBCCombinatorics.cbc function (blockForm message))
          (condition function))
      (domain := {messages : List M | messages ≠ []})
      (hasDomain := ?_)
      (allowed := fun messages =>
        CBCCombinatorics.totalBlocks blockForm messages ≤ q)
      (prefixClosed := prefixClosed_totalBlocks_le blockForm q)
      (nilAllowed := ?_)
      (bad := fun function messages =>
        CBCCombinatorics.cbcBad function blockForm messages)
      (winImpliesBad := ?_)
      (sourceNonnegative := Distribution.uniform_nonNeg)
      (boundNonnegative := by positivity)
      (badMass_le := ?_)
  · intro function
    exact System.dom_functionEvaluator _
  · simp [CBCCombinatorics.totalBlocks]
  · intro function messages conditionTrue
    change (condition function).1 messages = true at conditionTrue
    rw [condition_eq_cbcBad function messages] at conditionTrue
    exact of_decide_eq_true conditionTrue
  · intro messages messagesLimit
    calc
      (Distribution.uniform (X → X)).mass (fun function =>
          CBCCombinatorics.cbcBad function blockForm messages) ≤
          (q : ℝ) * ((q : ℝ) - 1) /
            (2 * Fintype.card X) :=
        CBCCombinatorics.mass_cbcBad_le blockForm q messages messagesLimit
      _ ≤ (q : ℝ) ^ 2 / (2 * Fintype.card X) := by
        gcongr
        nlinarith [show (0 : ℝ) ≤ q by positivity]

end

end CBCMAC
