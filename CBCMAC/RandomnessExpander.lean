import CBCMAC.Collisions
import ConstructiveCryptography.GameBound

/-!
# CBC is a randomness expander

CR18, Theorem 6.1 (printed p. 126): with a prefix-free block former and at most `q` encoded
blocks, CBC under the uniform random function `URF X X` constructs the uniform random function
`URF M X`, within `q²/(2|X|)`. The bound is the generic game-equivalence bound for the collision
game; the blind winning probability is bounded by counting collisions.

## Main results

* `URF_eq`: the uniform random function samples a function once
* `cbc_game_equiv`: until two round inputs collide, CBC is the restricted ideal
* `cbc_randomness_expander`: CR18, Theorem 6.1
-/

namespace CBCMAC

open Classical Probability SystemAlgebra SystemAlgebra.Interface SystemAlgebra.DSL Commons
  Collisions CategoryTheory
open scoped SystemAlgebra SystemAlgebra.DSL

/-- The functions from `X` to `Y` are the functions of the interface `Evaluation X Y`. -/
def evaluationEquiv (X Y : Type) [Fintype X] [Fintype Y] (q : ℕ) :
    (X → Y) ≃ (∀ i, (Evaluation X Y q).X i → (Evaluation X Y q).Y i) where
  toFun f _ := f
  invFun F := F .eval
  left_inv _ := rfl
  right_inv F := funext fun i => by cases i; rfl

/-- The uniform random function samples a function once and evaluates it. -/
theorem URF_eq (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {q : ℕ} :
    (URF X Y : Resource (Evaluation X Y q)) =
      Resource.sample (Distribution.uniform (X → Y)) (fun f => Resource.ofFunction fun _ => f) := by
  refine Eq.trans ?_
    (Resource.sample_fTransform (evaluationEquiv X Y q) _ Resource.ofFunction)
  rw [Commons.URF]
  congr 1
  convert (Distribution.fTransform_equiv_uniform (evaluationEquiv X Y q)).symm

variable {M X : Type} [Fintype M] [Fintype X] [Nonempty X] [AddCommGroup X] [DecidableEq X]

/-- CR18 §6.2.3 (printed p. 126): CBC under a uniform round function, with the hidden condition
that two round inputs collide. -/
noncomputable def cbcGame (blockForm : M → List X) (q n : ℕ) :=
  PDG.ofSingleFunction (MessageBlocks blockForm q n).domain
    (MessageBlocks blockForm q n).nonempty_prefix (MessageBlocks blockForm q n).bound
    (MessageBlocks blockForm q n).length_le (Distribution.uniform (X → X))
    (fun f m => cbcFunction f (blockForm m))
    (fun f => ⟨cbcBad f blockForm, fun {_ _} hp => cbcBad_monotone f blockForm hp⟩)

/-- Without a collision, CBC's transcripts have the law of the restricted ideal. -/
theorem cbc_game_equiv [Nontrivial M] (blockForm : M → List X) (q n : ℕ)
    (prefixFree : ∀ m m', m ≠ m' → ¬ blockForm m <+: blockForm m') :
    cbcGame blockForm q n |≡ θ blockForm q (budget := n) • URF M X := by
  simp only [URF_eq, Resource.smul_sample, θ, filter_smul_ofFunction]
  apply PDG.ofSingleFunction_gameEquivalent
  exact mass_cbcFunction_outputs_and_not_cbcBad_eq blockForm prefixFree

/-- Blind winning is a collision among at most `q` round inputs. -/
theorem cbcGame_blind_bound (blockForm : M → List X) (q n : ℕ) :
    ν((cbcGame blockForm q n).blind (MessageBlocks blockForm q n).nonempty_prefix) ≤
      (q : ℝ) ^ 2 / (2 * Fintype.card X) := by
  apply PDG.ofFunction_blind_le (by positivity)
  intro us admitted
  have budget : totalBlocks blockForm (us.map Sigma.snd) ≤ q := by
    rcases admitted with rfl | hd
    · simp [totalBlocks]
    · simpa only [totalBlocks, cbc_cost, List.map_map, Function.comp_def] using hd.2
  calc
    _ ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) :=
      mass_cbcBad_le blockForm q (us.map Sigma.snd) budget
    _ ≤ (q : ℝ) ^ 2 / (2 * Fintype.card X) := by
      gcongr
      nlinarith [show (0 : ℝ) ≤ q by positivity]

/-- **CR18, Theorem 6.1** (printed p. 126): prefix-free CBC with a total budget of `q` encoded
blocks, under the uniform random function, is within `q²/(2|X|)` of the uniform message function
restricted to the same budget. -/
theorem cbc_randomness_expander [Nontrivial M] (blockForm : M → List X) (q n : ℕ)
    (prefixFree : ∀ m m', m ≠ m' → ¬ blockForm m <+: blockForm m') :
    Δ ((θ blockForm q (budget := n) ≫ cbc blockForm) • URF X X) (θ blockForm q • URF M X) ≤
      ENNReal.ofReal ((q : ℝ) ^ 2 / (2 * Fintype.card X)) := by
  calc
    _ ≤ ENNReal.ofReal ν((cbcGame blockForm q n).blind (MessageBlocks blockForm q n).nonempty_prefix) :=
      (cbc_game_equiv blockForm q n prefixFree).game_dist_ofSingleFunction_le (by
        rw [comp_smul, URF_eq, Resource.smul_sample, Resource.smul_sample]
        simp only [cbc_smul_ofFunction, θ, filter_smul_ofFunction]
        rfl)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (cbcGame_blind_bound blockForm q n)

end CBCMAC
