import CBCMAC.Probability
import CBCMAC.ConditionalEquivalence
import RandomSystems.Converter.ConditionalEquivalence
import RandomSystems.Converter.RandomSystemAction
import RandomSystems.RandomFunction
import RandomSystems.Tactics.ProofAutomation
import RandomSystems.Technique.ConditionalEquivalence.Filter

set_option autoImplicit false

/-!
# CBC-MAC as a randomness expander

This module defines the real and ideal random systems and states the
normalized finite-message specialization of CR18, Theorem 6.1 (printed
p. 126). The argument `blockForm` is the encoded and padded block sequence.
-/

namespace CBCMAC

noncomputable section

open CategoryTheory
open RandomSystems.Ambient
open scoped CBCMAC RandomSystems.Ambient.DDC
  RandomSystems.ConditionalEquivalence


universe u

section

variable {X M : Type u} [Fintype M] [AddMonoid X]

local notation:max "[" q "]ᶜ" =>
  DDC.asHom (DDC.queryLimit (X := X) (Y := X) q)
local notation:max "θ[" blockForm ", " q "]" =>
  DDC.asHom (RandomSystems.DomainFilter.toDDC (Y := X)
    (theta (X := X) (M := M) blockForm q))

/-- The restriction `θ_q` makes the round-function query limit `[q]`
irrelevant after CBC. -/
lemma theta_cbc_eq_theta_cbc_queryLimit
    (blockForm : M → List X) (q : Nat) :
    θ[blockForm, q] ≫ CBC[blockForm] =
      θ[blockForm, q] ≫ (CBC[blockForm] ≫ [q]ᶜ) := by
  -- Regard `θ ≫ CBC` as the converter querying the round function.
  let outer : DDC (Interface.single M X) (Interface.single X X) :=
    θ[blockForm, q] ≫ CBC[blockForm]
  -- Every round-function query allowed by `θ` occurs before the `q`-query limit.
  have withinLimit : ∀ {history query},
      Sum.inl query ∈ outer history →
      history.receivedInnerQueries.length < q := by
    intro history query responds
    exact cbc_inner_query_within_limit blockForm q history query responds
  calc
    -- Attaching the forwarding converter leaves `outer` unchanged.
    θ[blockForm, q] ≫ CBC[blockForm] =
      outer ≫ 𝟙 (Interface.single X X) :=
        by
          rw [Category.comp_id]
    -- On the queries emitted by `outer`, `[q]` behaves exactly like forwarding.
    _ = outer ≫ [q]ᶜ :=
      DDC.serial_forwarding_eq_serial_queryLimit outer q withinLimit
    -- Reassociate serial composition to obtain `θ ≫ (CBC ≫ [q])`.
    _ = θ[blockForm, q] ≫ (CBC[blockForm] ≫ [q]ᶜ) :=
      Category.assoc _ _ _

end

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-- The uniform round function. -/
def R : RandomSystems.RandomFunction X X :=
  RandomSystems.RandomFunction.uniform X X

/-- The ideal variable-input-length random function. -/
def V : RandomSystems.RandomFunction M X :=
  RandomSystems.RandomFunction.uniform M X

local notation "R" => CBCMAC.R (X := X)
local notation "V" => CBCMAC.V (M := M) (X := X)

local notation:max "Δ(" left ", " right ")" =>
  dist (left : RandomSystem (Interface.single M X))
    (right : RandomSystem (Interface.single M X))
local notation:max "Adv(" left ", " right ")" =>
  RandomSystem.advantage
    (left : RandomSystem (Interface.single M X))
    (right : RandomSystem (Interface.single M X))
local notation:max "[" q "]ᶜ" =>
  DDC.asHom (DDC.queryLimit (X := X) (Y := X) q)
local notation:max "θ[" blockForm ", " q "]" =>
  theta blockForm q

/-- A block former is prefix-free when no encoding of one message is a proper
prefix of the encoding of a different message. -/
def PrefixFree (blockForm : M → List X) : Prop :=
  ∀ left right, left ≠ right → ¬ blockForm left <+: blockForm right

/-- The MBO reached by a nontrivial collision between CBC round-function
inputs. -/
def cbcCollisionCondition (blockForm : M → List X) (function : X → X) :
    RandomSystems.System.MC M :=
  ⟨fun messages => decide
      (CBCCombinatorics.cbcBad function blockForm messages),
    by
      intro initial final isPrefix bad
      rw [decide_eq_true_eq] at bad ⊢
      exact CBCCombinatorics.cbcBad_monotone function blockForm isPrefix bad⟩

omit [Fintype X] [Nonempty X] [Fintype M] in
@[simp]
lemma cbcCollisionCondition_apply (blockForm : M → List X)
    (function : X → X) (messages : List M) :
    (cbcCollisionCondition blockForm function).1 messages =
      decide (CBCCombinatorics.cbcBad function blockForm messages) :=
  rfl

/-- CBC over a normalized round-function law, augmented with its collision
MBO. -/
def cbcCollisionGame (blockForm : M → List X)
    (roundFunction : RandomSystems.RandomFunction X X) :
    Probability.Distribution.ProbDist (RandomSystems.System.DDG M X) :=
  ⟨RandomSystems.PDG.ofFunction
      roundFunction.law.1
      (fun function message =>
        CBCCombinatorics.cbc function (blockForm message))
      (cbcCollisionCondition blockForm),
    RandomSystems.PDG.isProbDist_ofFunction
      roundFunction.law.1
      (fun function message =>
        CBCCombinatorics.cbc function (blockForm message))
      (cbcCollisionCondition blockForm) roundFunction.law.2⟩

local notation:max "CBĈ[" blockForm "]" =>
  cbcCollisionGame blockForm R
local notation:max "Γ(b " game ")" =>
  (fun normalized : Probability.Distribution.ProbDist
      (RandomSystems.System.DDG M X) =>
    RandomSystems.PDG.supWinProb
      (RandomSystems.PDG.blind (Subtype.val normalized))) game
/-- CBC and the variable-input-length random function are conditionally
equivalent until the collision MBO is reached. -/
lemma cbcCollisionGame_conditionallyEquivalent [Nontrivial M]
    (blockForm : M → List X) (prefixFree : PrefixFree blockForm) :
    CBĈ[blockForm].1 |≡ (V : RandomSystems.PDS M X) := by
  simpa only [cbcCollisionGame, CBCMAC.R, CBCMAC.V] using
    cbc_conditionallyEquivalent_urf_of_condition_eq_cbcBad
      blockForm prefixFree (cbcCollisionCondition blockForm)
      (cbcCollisionCondition_apply blockForm)

/-- Restricting both systems by the total-block condition preserves their
conditional equivalence. -/
lemma theta_cbcCollisionGame_conditionallyEquivalent [Nontrivial M]
    (blockForm : M → List X) (q : Nat)
    (conditionalEquivalence :
      CBĈ[blockForm].1 |≡ (V : RandomSystems.PDS M X)) :
    (θ[blockForm, q] • CBĈ[blockForm]).1 |≡
      (θ[blockForm, q] • V :
        Probability.Distribution.ProbDist
          (RandomSystems.System.DDS M X)).1 :=
  conditionalEquivalence.domain_filter (theta blockForm q)

omit [Fintype M] in
@[rs_side_condition]
lemma theta_cbcCollisionGame_hasDomain
    (blockForm : M → List X) (q : Nat) :
    RandomSystems.PDG.HasDomain
      (θ[blockForm, q] • CBĈ[blockForm]).1
      (restrictedDomain blockForm q) := by
  simpa only [HSMul.hSMul, theta, cbcCollisionGame,
      restrictedDomain, Set.mem_ofPred_eq] using
    RandomSystems.PDG.hasDomain_filterDom
      (fun messages =>
        CBCCombinatorics.totalBlocks blockForm messages ≤ q)
      (prefixClosed_totalBlocks_le blockForm q)
      (RandomSystems.PDG.ofFunction
        R.law.1
        (fun function message =>
          CBCCombinatorics.cbc function (blockForm message))
        (cbcCollisionCondition blockForm))
      {history : List M | history ≠ []}
      (RandomSystems.PDG.hasDomain_ofFunction
        R.law.1
        (fun function message =>
          CBCCombinatorics.cbc function (blockForm message))
        (cbcCollisionCondition blockForm))

omit [Fintype X] [Nonempty X] [Fintype M] in
@[rs_normalization]
lemma underlying_theta_cbcCollisionGame
    (blockForm : M → List X) (q : Nat)
    (roundFunction : RandomSystems.RandomFunction X X) :
    RandomSystems.PDG.underlying
        (theta blockForm q • cbcCollisionGame blockForm roundFunction).1 =
      theta blockForm q • (CBC[blockForm] • roundFunction) := by
  change RandomSystems.PDG.underlying
      (RandomSystems.PDG.filterDom
        (theta blockForm q).predicate
        (theta blockForm q).prefixClosed
        (cbcCollisionGame blockForm roundFunction).1) =
    RandomSystems.PDS.filterDom
      (theta blockForm q).predicate
      (theta blockForm q).prefixClosed
      (CBC[blockForm] • roundFunction)
  rw [RandomSystems.PDG.underlying_filterDom]
  simp only [cbcCollisionGame]
  rw [RandomSystems.PDG.underlying_ofFunction]

/-- CR18, Theorem 6.1: CBC with a prefix-free block former is within
`q² / (2 |X|)` of the ideal random function under a total block budget `q`. -/
theorem cbc_randomness_expander [Nontrivial M]
    -- Message-to-block encoding.
    (blockForm : M → List X)
    -- Total-block budget.
    (q : Nat)
    -- Prefix-free encoding.
    (prefixFree : PrefixFree blockForm) :

    -- Distinguishing advantage bound between:
    -- Real: CBC with a random function restricted to `q` blocks.
    Δ((θ[blockForm, q] ≫ CBC[blockForm]) • ([q]ᶜ • R),
    -- Ideal: the restricted variable-input-length random function.
      θ[blockForm, q] • V) ≤
      (q : ℝ) ^ 2 / (2 * Fintype.card X) := by

  -- Equation (6.1): the block restriction makes `[q]` after CBC redundant.
  have thetaCBC_eq_thetaCBCQueryLimit :
      (θ[blockForm, q] : (Interface.single M X) ⟶ (Interface.single M X)) ≫
          CBC[blockForm] =
        (θ[blockForm, q] :
            (Interface.single M X) ⟶ (Interface.single M X)) ≫
          (CBC[blockForm] ≫ [q]ᶜ) :=
    theta_cbc_eq_theta_cbc_queryLimit blockForm q

  -- CBC and the random function agree until a round-input collision.
  have CBCGameCondEquivToV :
      CBĈ[blockForm].1 |≡ (V : RandomSystems.PDS M X) :=
    cbcCollisionGame_conditionallyEquivalent blockForm prefixFree
  -- Preserve that agreement under the total-block restriction.
  have restrictedCBCCondEquivRestrictedV :
      (θ[blockForm, q] • CBĈ[blockForm]).1 |≡
        (θ[blockForm, q] • V :
          Probability.Distribution.ProbDist
            (RandomSystems.System.DDS M X)).1 :=
    theta_cbcCollisionGame_conditionallyEquivalent
      blockForm q CBCGameCondEquivToV
  -- Bound the blind collision probability.
  have blindWinningLePColl :
    Γ(b (θ[blockForm, q] • CBĈ[blockForm])) ≤
        (q : ℝ) ^ 2 / (2 * Fintype.card X) :=
    by
      exact
        supWinProb_blind_filterDom_cbc_le blockForm q
          (cbcCollisionCondition blockForm)
          (cbcCollisionCondition_apply blockForm)
  calc
    -- Attach Equation (6.1) to `R` and remove the redundant query limit.
    Δ((θ[blockForm, q] ≫ CBC[blockForm]) • ([q]ᶜ • R),
        θ[blockForm, q] • V)
    = Δ((θ[blockForm, q] ≫ CBC[blockForm]) • R,
        θ[blockForm, q] • V) := by
        -- Converter equality is preserved when both sides are attached to `R`.
        congr 1
        simpa only [DDC.hom_smul_randomFunction_eq, DDC.comp_smul] using
          congrArg
            (fun converter =>
              (converter • R : RandomSystem (Interface.single M X)))
          thetaCBC_eq_thetaCBCQueryLimit.symm
    -- For normalized random systems, `Δ` is their distinguishing advantage.
    _ = Adv((θ[blockForm, q] ≫ CBC[blockForm]) • R,
        θ[blockForm, q] • V) :=
      RandomSystem.dist_eq_advantage _ _
    -- Conditional equivalence bounds this advantage by blind collision winning.
    _ ≤ Γ(b (θ[blockForm, q] • CBĈ[blockForm])) := by
      refine
        RandomSystem.advantage_le_supWinProb_blind_of_conditionallyEquivalent
          (game := θ[blockForm, q] • CBĈ[blockForm])
          (target := θ[blockForm, q] • V)
          (domain := restrictedDomain blockForm q)
          ?_ ?_ restrictedCBCCondEquivRestrictedV ?_
      -- The restricted collision game is defined on the histories admitted by `θ`.
      · exact theta_cbcCollisionGame_hasDomain blockForm q
      -- The restricted ideal function has the same domain.
      · exact restrictedIdealFunctionPDS_hasDomain blockForm q V
      -- Forgetting the MBO leaves `θ • CBC(R)`.
      · rw [underlying_theta_cbcCollisionGame blockForm q R]
        -- Express the same attached systems as normalized PDSs.
        rw [DDC.hom_smul_randomFunction_eq,
          RandomSystems.DomainFilter.smul_randomSystem_eq,
          RandomSystems.RandomFunction.toRandomSystem,
          DDC.smul_toRandomSystem_pds,
          RandomSystems.RandomFunction.toRandomSystem,
          DDC.smul_toRandomSystem_pds,
          RandomSystem.advantage_toRandomSystem_eq]
        -- Evaluate the serial attachment as `θ` applied to `CBC(R)`.
        simp only [DDC.comp_smul_pds]
        rw [apply_cbc_randomFunction]
        -- Apply the fixed-interface CBC comparison bound.
        exact
          cbcPDS_advantage_le_restrictedCBCPDS_advantage blockForm q R V
    -- Substitute the computed blind collision bound.
    _ ≤ (q : ℝ) ^ 2 / (2 * Fintype.card X) :=
      blindWinningLePColl
end

end CBCMAC
