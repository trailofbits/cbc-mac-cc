import CBCMAC.Attachment
import CBCMAC.Blind
import RandomSystems.Converter.CommonDomainEmbedding
import RandomSystems.Tactics.ProofAutomation

set_option autoImplicit false

/-!
# CBC advantage bound

CR18, Theorem 6.1 (printed pp. 126--127), applies conditional equivalence
under the total-block restriction and bounds the resulting blind collision
game. This module then identifies that fixed-interface bound with the public
CBC attachment.
-/

namespace CBCMAC

noncomputable section

open Classical
open Probability
open RandomSystems
open RandomSystems.System
open RandomSystems.Ambient
open scoped CBCMAC ConditionalEquivalence RandomSystems.Ambient.DDC
  RandomSystems.PDS

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

def filterDDS (blockForm : M → List X) (q : Nat) :
    System.DDS M X → System.DDS M X :=
  System.filterDom
    (fun messages =>
      CBCCombinatorics.totalBlocks blockForm messages ≤ q)
    (prefixClosed_totalBlocks_le blockForm q)

@[rs_normalization]
def restrictedCBCPDS (blockForm : M → List X) (q : Nat)
    (roundFunction : RandomSystems.RandomFunction X X) :
    RandomSystems.PDS M X :=
  Distribution.fTransform (filterDDS blockForm q)
    (Distribution.fTransform
      (fun function : X → X =>
        System.functionEvaluator fun message : M =>
          CBCCombinatorics.cbc function (blockForm message))
      roundFunction.law.1)

def restrictedIdealFunctionPDS
    (blockForm : M → List X) (q : Nat)
    (idealFunction : RandomSystems.RandomFunction M X) :
    RandomSystems.PDS M X :=
  RandomSystems.PDS.filterDom
    (fun messages => CBCCombinatorics.totalBlocks blockForm messages ≤ q)
    (prefixClosed_totalBlocks_le blockForm q)
    idealFunction.toPDS

/-- The common domain of the restricted CBC and ideal systems. -/
def restrictedDomain (blockForm : M → List X) (q : Nat) :
    Set (List M) :=
  {history | history ≠ [] ∧
    CBCCombinatorics.totalBlocks blockForm history ≤ q}

omit [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M] in
@[rs_side_condition]
lemma restrictedCBCPDS_isProbDist
    (blockForm : M → List X) (q : Nat)
    (roundFunction : RandomSystems.RandomFunction X X) :
    (restrictedCBCPDS blockForm q roundFunction).isProbDist := by
  unfold restrictedCBCPDS filterDDS
  exact Distribution.fTransform_isProbDist _
    (Distribution.fTransform_isProbDist _ roundFunction.law.2)

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    [Fintype M] [DecidableEq M] in
@[rs_side_condition]
lemma restrictedIdealFunctionPDS_isProbDist
    (blockForm : M → List X) (q : Nat)
    (idealFunction : RandomSystems.RandomFunction M X) :
    (restrictedIdealFunctionPDS blockForm q idealFunction).isProbDist := by
  unfold restrictedIdealFunctionPDS
  exact RandomSystems.PDS.isProbDist_filterDom _ _
    idealFunction.isProbDist_toPDS

omit [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M] in
@[rs_side_condition]
lemma restrictedCBCPDS_hasDomain
    (blockForm : M → List X) (q : Nat)
    (roundFunction : RandomSystems.RandomFunction X X) :
    RandomSystems.PDS.HasDomain
      (restrictedCBCPDS blockForm q roundFunction)
      (restrictedDomain blockForm q) := by
  simpa only [restrictedCBCPDS, filterDDS, restrictedDomain,
      RandomSystems.PDS.filterDom, Set.mem_ofPred_eq]
    using RandomSystems.PDS.hasDomain_filterDom
      (fun messages => CBCCombinatorics.totalBlocks blockForm messages ≤ q)
      (prefixClosed_totalBlocks_le blockForm q)
      (Distribution.fTransform
        (fun function : X → X =>
          System.functionEvaluator fun message : M =>
            CBCCombinatorics.cbc function (blockForm message))
        roundFunction.law.1)
      {history : List M | history ≠ []}
      (RandomSystems.PDS.hasDomain_fTransform_functionEvaluator
        (fun function : X → X => fun message : M =>
          CBCCombinatorics.cbc function (blockForm message))
        roundFunction.law.1)

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    [Fintype M] [DecidableEq M] in
@[rs_side_condition]
lemma restrictedIdealFunctionPDS_hasDomain
    (blockForm : M → List X) (q : Nat)
    (idealFunction : RandomSystems.RandomFunction M X) :
    RandomSystems.PDS.HasDomain
      (restrictedIdealFunctionPDS blockForm q idealFunction)
      (restrictedDomain blockForm q) := by
  simpa only [restrictedIdealFunctionPDS, restrictedDomain, Set.mem_ofPred_eq]
    using RandomSystems.PDS.hasDomain_filterDom
      (fun messages => CBCCombinatorics.totalBlocks blockForm messages ≤ q)
      (prefixClosed_totalBlocks_le blockForm q)
      idealFunction.toPDS
      {history : List M | history ≠ []}
      idealFunction.hasDomain_toPDS

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    [Fintype M] [DecidableEq M] in
lemma embed_restricted_function_of_admitted
    (blockForm : M → List X) (q : Nat) (function : M → X)
    (history : Ambient.History (Interface.single M X))
    (admitted :
      CBCCombinatorics.totalBlocks blockForm history.queries ≤ q) :
    CommonDomain.embedDDS
        (filterDDS blockForm q
          (System.functionEvaluator function)) history =
      some (function history.last) := by
  -- The admitted complete history belongs to the restricted partial DDS.
  apply (CommonDomain.embedDDS_eq_some_iff _ history _).2
  have inDomain : history.queries ∈
      System.dom
        (filterDDS blockForm q (System.functionEvaluator function)) := by
    unfold filterDDS
    rw [System.mem_dom_filterDom, System.dom_functionEvaluator]
    exact ⟨history.nonempty, admitted⟩
  refine ⟨inDomain, ?_⟩
  -- On that domain, filtering preserves the function evaluator's answer.
  change System.output
      (filterDDS blockForm q (System.functionEvaluator function))
      history.queries inDomain = function history.last
  unfold filterDDS at inDomain ⊢
  rw [System.output_filterDom]
  simpa only [Ambient.History.last] using
    System.output_functionEvaluator function history.queries inDomain.1

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    [Fintype M] [DecidableEq M] in
lemma applySystem_theta_embed_restricted_function
    (blockForm : M → List X) (q : Nat) (function : M → X) :
    applySystem ((theta blockForm q).toDDC (Y := X))
        (CommonDomain.embedDDS
          (filterDDS blockForm q
            (System.functionEvaluator function))) =
      applySystem ((theta blockForm q).toDDC (Y := X))
        (DDS.ofFunction function) := by
  -- Evaluate the `θ_r` restriction on both systems.
  rw [applySystem_theta, applySystem_theta]
  apply DDS.ext
  intro history
  by_cases admitted :
      CBCCombinatorics.totalBlocks blockForm history.queries ≤ q
  -- On admitted histories, the embedding returns the function value.
  · simp only [admitted, if_pos]
    exact embed_restricted_function_of_admitted blockForm q function
      history admitted
  · simp [admitted]

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    [Fintype M] [DecidableEq M] in
lemma apply_theta_restricted_function_law
    {A : Type u} (blockForm : M → List X) (q : Nat)
    (toFunction : A → M → X) (source : Distribution A) :
    Distribution.fTransform
        (applySystem ((theta blockForm q).toDDC (Y := X)))
        (Distribution.fTransform CommonDomain.embedDDS
          (Distribution.fTransform
            (filterDDS blockForm q)
            (Distribution.fTransform
              (fun value => System.functionEvaluator (toFunction value))
              source))) =
      Distribution.fTransform
          (applySystem ((theta blockForm q).toDDC (Y := X)))
      (Distribution.fTransform
          (fun value => DDS.ofFunction (toFunction value)) source) := by
  -- Flatten the nested pushforwards to compare their pointwise attached DDSs.
  rs_probability
  apply Distribution.fTransform_congr
  -- Theta makes the embedded restricted evaluator agree with the total evaluator.
  intro value _
  simpa only [Function.comp_apply] using
    applySystem_theta_embed_restricted_function blockForm q
      (toFunction value)

omit [Fintype X] [DecidableEq X] [Nonempty X] [DecidableEq M] in
lemma apply_theta_embed_restrictedCBCPDS
    (blockForm : M → List X) (q : Nat)
    (roundFunction : RandomSystems.RandomFunction X X) :
    PDS.apply ((theta blockForm q).toDDC (Y := X))
        (CommonDomain.embedPDS
          ⟨restrictedCBCPDS blockForm q roundFunction,
            restrictedCBCPDS_isProbDist blockForm q roundFunction⟩) =
      PDS.apply ((theta blockForm q).toDDC (Y := X))
        (cbcPDS blockForm roundFunction) := by
  -- Compare the normalized laws after applying the same restriction.
  apply Subtype.ext
  change Distribution.fTransform
      (applySystem ((theta blockForm q).toDDC (Y := X)))
      (Distribution.fTransform CommonDomain.embedDDS
        (restrictedCBCPDS blockForm q roundFunction)) = _
  rw [restrictedCBCPDS]
  change _ = Distribution.fTransform
    (applySystem ((theta blockForm q).toDDC (Y := X)))
    (Distribution.fTransform
      (fun function => DDS.ofFunction (fun message =>
        CBCCombinatorics.cbc function (blockForm message)))
      roundFunction.law.1)
  -- Theta identifies the embedded restricted evaluator with the total CBC law.
  simpa only [cbcPDS, filterDDS] using
    apply_theta_restricted_function_law blockForm q
    (fun function : X → X => fun message : M =>
      CBCCombinatorics.cbc function (blockForm message))
    roundFunction.law.1

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    [Fintype M] [DecidableEq M] in
lemma apply_theta_embed_restrictedIdealFunctionPDS
    (blockForm : M → List X) (q : Nat)
    (idealFunction : RandomSystems.RandomFunction M X) :
    PDS.apply ((theta blockForm q).toDDC (Y := X))
        (CommonDomain.embedPDS
          ⟨restrictedIdealFunctionPDS blockForm q idealFunction,
            restrictedIdealFunctionPDS_isProbDist blockForm q idealFunction⟩) =
      PDS.apply ((theta blockForm q).toDDC (Y := X))
        idealFunction.toAmbientPDS := by
  -- Compare the normalized laws after applying the same restriction.
  apply Subtype.ext
  change Distribution.fTransform
      (applySystem ((theta blockForm q).toDDC (Y := X)))
      (Distribution.fTransform CommonDomain.embedDDS
        (restrictedIdealFunctionPDS blockForm q idealFunction)) = _
  rw [restrictedIdealFunctionPDS, RandomSystems.PDS.filterDom,
    RandomSystems.RandomFunction.toPDS, Probability.Distribution.PMF]
  change _ = Distribution.fTransform
    (applySystem ((theta blockForm q).toDDC (Y := X)))
    (Distribution.fTransform DDS.ofFunction idealFunction.law.1)
  -- Theta identifies the embedded restricted evaluator with the total ideal law.
  simpa only [RandomSystems.RandomFunction.toAmbientPDS,
    Probability.Distribution.PMF, filterDDS] using
    apply_theta_restricted_function_law blockForm q
    (fun function : M → X => function) idealFunction.law.1

omit [Fintype X] [DecidableEq X] [Nonempty X] [DecidableEq M] in
/-- The public attached CBC comparison is bounded by its restricted
fixed-interface presentation. -/
lemma cbcPDS_advantage_le_restrictedCBCPDS_advantage
    (blockForm : M → List X) (q : Nat)
    (roundFunction : RandomSystems.RandomFunction X X)
    (idealFunction : RandomSystems.RandomFunction M X) :
    Ambient.PDS.advantage
        (DDC.asHom ((theta blockForm q).toDDC (Y := X)) •
          cbcPDS blockForm roundFunction)
        (DDC.asHom ((theta blockForm q).toDDC (Y := X)) •
          idealFunction.toAmbientPDS) ≤
      Adv(theta blockForm q • (CBC[blockForm] • roundFunction),
        (theta blockForm q • idealFunction :
          Distribution.ProbDist (System.DDS M X))) := by
  -- Package the two common-domain probability laws.
  let realLaw : Distribution.ProbDist (System.DDS M X) :=
    ⟨restrictedCBCPDS blockForm q roundFunction,
      restrictedCBCPDS_isProbDist blockForm q roundFunction⟩
  let idealLaw : Distribution.ProbDist (System.DDS M X) :=
    ⟨restrictedIdealFunctionPDS blockForm q idealFunction,
      restrictedIdealFunctionPDS_isProbDist blockForm q idealFunction⟩
  have realApplication :
      PDS.apply ((theta blockForm q).toDDC (Y := X))
          (CommonDomain.embedPDS realLaw) =
        PDS.apply ((theta blockForm q).toDDC (Y := X))
          (cbcPDS blockForm roundFunction) := by
    -- Theta identifies the embedded restricted CBC law with the public CBC law.
    simpa only [realLaw] using
      apply_theta_embed_restrictedCBCPDS blockForm q roundFunction
  have idealApplication :
      PDS.apply ((theta blockForm q).toDDC (Y := X))
          (CommonDomain.embedPDS idealLaw) =
        PDS.apply ((theta blockForm q).toDDC (Y := X))
          idealFunction.toAmbientPDS := by
    -- Theta identifies the embedded restricted ideal law with the public ideal law.
    simpa only [idealLaw] using
      apply_theta_embed_restrictedIdealFunctionPDS blockForm q idealFunction
  -- Apply data processing, the common-domain bridge, and the fixed-interface bound.
  calc
    Ambient.PDS.advantage
        (PDS.apply ((theta blockForm q).toDDC (Y := X))
          (cbcPDS blockForm roundFunction))
        (PDS.apply ((theta blockForm q).toDDC (Y := X))
          idealFunction.toAmbientPDS) ≤
      Adv(realLaw.1, idealLaw.1) :=
      by
        -- Attachment by theta is non-expanding on the ambient quotient.
        rw [← realApplication, ← idealApplication]
        calc
          Ambient.PDS.advantage
              (PDS.apply ((theta blockForm q).toDDC (Y := X))
                (CommonDomain.embedPDS realLaw))
              (PDS.apply ((theta blockForm q).toDDC (Y := X))
                (CommonDomain.embedPDS idealLaw)) ≤
            Ambient.PDS.advantage
              (CommonDomain.embedPDS realLaw)
              (CommonDomain.embedPDS idealLaw) :=
            Ambient.PDS.advantage_apply_le
              ((theta blockForm q).toDDC (Y := X))
              (CommonDomain.embedPDS realLaw)
              (CommonDomain.embedPDS idealLaw)
          _ = Adv(realLaw.1, idealLaw.1) :=
            CommonDomain.advantage_embedPDS_eq_advantage_of_hasDomain
              realLaw idealLaw
              (restrictedCBCPDS_hasDomain blockForm q roundFunction)
              (restrictedIdealFunctionPDS_hasDomain blockForm q idealFunction)
end

end CBCMAC
