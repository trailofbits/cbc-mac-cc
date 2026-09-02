import CBCMAC.Objects
import Mathlib.Tactic
import Probability.Simp

set_option autoImplicit false

/-!
# CBC proof automation

These tactics discharge the routine probability normalization and finite CBC
recurrence obligations used by the attachment proof.
-/

open Lean.Parser.Tactic

/-- Normalize probability-law bookkeeping and synthesize its first-order
consequences from the fixed distribution rule list. -/
macro "rs_probability" : tactic =>
  `(tactic|
    simp -failIfUnchanged only [dist_simp,
      Probability.Distribution.isProbDist.weight_eq,
      Probability.Distribution.isProbDist.nonNeg,
      Probability.Distribution.fTransform_isProbDist,
      Probability.Distribution.uniform_isProbDist] <;>
    try (first
      | grind only [
          = Probability.Distribution.weight_fTransform,
          = Probability.Distribution.weight_uniform,
          = Probability.Distribution.isProbDist.weight_eq]
      | omega
      | ring
      | abel
      | positivity))

/-- Normalize only the CBC recurrence equations demonstrated in the current
application proof. -/
macro "cbc_simp" : tactic =>
  `(tactic| simp -failIfUnchanged only [
    CBCMAC.CBCCombinatorics.cbc_append,
    CBCMAC.CBCCombinatorics.cbcInput_append_of_lt,
    CBCMAC.CBCCombinatorics.cbcInput_append_length,
    CBCMAC.CBCCombinatorics.cbcInput_take_of_lt,
    CBCMAC.successfulReplies_length,
    CBCMAC.successfulReplies_succ,
    CBCMAC.cbc_take_succ,
    CBCMAC.response_successfulReplies_of_lt,
    CBCMAC.response_successfulReplies_length,
    List.length_append,
    List.length_cons,
    List.length_nil,
    List.length_singleton,
    zero_add])

/-- CBC-local first-order synthesis.  The induction and its invariant remain
explicit at the call site; this tactic closes only normalized branches. -/
syntax (name := cbcGrind) "cbc_grind"
  (" [" withoutPosition(Lean.Parser.Tactic.grindParam,*) "]")? : tactic

macro_rules
  | `(tactic| cbc_grind) =>
      `(tactic| cbc_grind [])
  | `(tactic| cbc_grind [$rules:grindParam,*]) =>
      `(tactic| cbc_simp <;> grind only [
        = CBCMAC.CBCCombinatorics.cbc_append,
        = CBCMAC.CBCCombinatorics.cbcInput_append_of_lt,
        = CBCMAC.CBCCombinatorics.cbcInput_append_length,
        = CBCMAC.CBCCombinatorics.cbcInput_take_of_lt,
        = CBCMAC.successfulReplies_length,
        = CBCMAC.successfulReplies_succ,
        = CBCMAC.cbc_take_succ,
        = CBCMAC.response_successfulReplies_of_lt,
        = CBCMAC.response_successfulReplies_length,
        = List.length_append,
        = List.length_cons,
        = List.length_singleton,
        $rules,*])
