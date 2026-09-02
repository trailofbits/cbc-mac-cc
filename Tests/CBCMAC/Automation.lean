import CBCMAC.Main

set_option autoImplicit false

namespace CBCMAC.AutomationTests

noncomputable section

open Probability

universe u

variable {X M : Type u}

example [Fintype X] [DecidableEq X] [Nonempty X] :
    (Distribution.uniform X).weight = 1 := by
  rs_probability

attribute [-simp] CBCMAC.successfulReplies_length

example [AddMonoid X] (function : X → X) (blocks : List X) (count : Nat) :
    (successfulReplies function blocks count).length = count := by
  fail_if_success simp only [List.length_nil]
  cbc_simp

attribute [simp] CBCMAC.successfulReplies_length

example [AddMonoid X] (function : X → X) (blocks : List X)
    {count : Nat} (below : count < blocks.length) :
    CBCCombinatorics.cbc function (blocks.take (count + 1)) =
      function (CBCCombinatorics.cbcInput function blocks count) := by
  fail_if_success grind only
  cbc_grind

example (blocks : List X) (count distance : Nat)
    (lengthEquation : count + (distance + 1) = blocks.length) :
    count < blocks.length := by
  cbc_grind

example [Nontrivial M] (blockForm : M → List X)
    (prefixFree : PrefixFree blockForm) (message : M) :
    blockForm message ≠ [] := by
  fail_if_success cbc_grind
  exact CBCCombinatorics.blockForm_ne_nil_of_prefixFree prefixFree message

end

end CBCMAC.AutomationTests
