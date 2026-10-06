import CBCMAC.RandomnessExpander
import Commons.Schemes.BlockCipher.AES
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.List

/-!
# AES-256 CBC-MAC

CBC over AES-256, for bit-string messages, with a total budget of `q` encoded blocks.

Blocks are 128-bit strings, with pointwise addition giving XOR. AES-256 is the Commons block
cipher, on blocks read as sixteen bytes, most significant bit first (FIPS 197, §3.3).

The block former prepends the message's bit length as a block, most significant bit first, and
then the payload bits, zero-padding only the last block. Messages have fewer than `2^128` bits,
so the header never wraps. The encoding is prefix-free, as the randomness-expander theorem
requires; it is a variant of Boneh–Shoup §6.6.1, method 1, which prepends the number of blocks of
an already block-aligned message.

After `θ`, CBC makes at most `q` block queries (CR18's equation (6.1)), so replacing AES by a
uniform random function under the query filter `⟪q⟫` costs its PRF advantage at `q` queries,
which is an assumption; CBC then contributes the randomness-expander bound.

## Main definitions

* `Block`: 128-bit blocks, and `blockEquiv` their bytes
* `aes256`: AES-256 on bit blocks, as a block cipher
* `Message`, `blockForm`: bit strings and the length-prefixed block former

## Main results

* `blockForm_prefixFree`: the block former is prefix-free
* `one_le_cbc_bound`: every message makes at least one AES call
* `aes256_cbc_prf`: AES-256 CBC-MAC is within `ε + q²/2^129` of the uniform message function
-/

namespace AESCBC

open Commons

/-! ## Blocks and AES-256 -/

/-- A 128-bit block, with pointwise addition giving XOR rather than integer addition. -/
abbrev Block := Fin 128 → ZMod 2

/-- The eight bits of a byte, most significant bit first. -/
def byteEquiv : (Fin 8 → ZMod 2) ≃ UInt8 :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans <|
    finFunctionFinEquiv.trans <| (finCongr (by decide)).trans
      ⟨UInt8.ofFin, UInt8.toFin, UInt8.toFin_ofFin, UInt8.ofFin_toFin⟩

/-- The sixteen bytes of a block: bit `8i + j` is bit `j` of byte `i`, most significant bit
first (FIPS 197, §3.3). -/
def blockEquiv : Block ≃ AES.Block :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (ZMod 2))).trans <|
    (Equiv.curry _ _ _).trans <|
      (Equiv.arrowCongr (Equiv.refl (Fin 16)) byteEquiv).trans (vectorEquivFun UInt8 16).symm

/-- **AES-256 on bit blocks**: the AES-256 block cipher on the bytes of a block. -/
def aes256 : BlockCipher (AES.Key .aes256) Block where
  encrypt key x := blockEquiv.symm ((AES.blockCipher .aes256).encrypt key (blockEquiv x))
  decrypt key y := blockEquiv.symm ((AES.blockCipher .aes256).decrypt key (blockEquiv y))
  decrypt_encrypt key x := by
    simp only [Equiv.apply_symm_apply, BlockCipher.decrypt_encrypt, Equiv.symm_apply_apply]

/-! ### AES-256 tests -/

-- NIST SP 800-38A, F.1.5: the four AES-256 encryption vectors, through the bit order of blocks.
#guard
  let key : AES.Key .aes256 :=
    Vector.ofFn fun i : Fin 32 =>
      UInt8.ofNat (0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4 /
        2 ^ (8 * (31 - i.val)))
  let vectors : List (Nat × Nat) := [
    (0x6bc1bee22e409f96e93d7e117393172a, 0xf3eed1bdb5d2a03c064b5a7e3db181f8),
    (0xae2d8a571e03ac9c9eb76fac45af8e51, 0x591ccb10d410ed26dc5ba74a31362870),
    (0x30c81c46a35ce411e5fbc1191a0a52ef, 0xb6ed21b99ca6f4f9f153e7b1beafed1d),
    (0xf69f2445df4f9b17ad2b417be66c3710, 0x23304b7a39f9f3ff067d8d8f9e24ecc7)]
  vectors.all fun (input, expected) =>
    let block : Block := fun bit => if (BitVec.ofNat 128 input).getMsbD bit.val then 1 else 0
    blockEquiv (aes256.encrypt key block) ==
      Vector.ofFn fun i : Fin 16 => UInt8.ofNat (expected / 2 ^ (8 * (15 - i.val)))

/-! ## The length-prefixed block former -/

/-- A bit string whose length fits in one 128-bit header. -/
abbrev Message := { bits : List Bool // bits.length < 2 ^ 128 }

/-- The bit length encoded as a big-endian 128-bit block. -/
def lengthBlock (length : Fin (2 ^ 128)) : Block :=
  -- The length bound guarantees that all length bits fit without truncation.
  fun bit => if (BitVec.ofFin length).getMsbD bit.val then 1 else 0

/-- One length block followed by the payload, zero-padded to a block boundary.

Examples: messages are written as bits; each bracket is one 16-byte block
in hexadecimal, and `×` denotes repetition.

```text
message   length header    padded payload   AES calls
empty     [00 × 16]        none             1
101       [00 × 15, 03]    [a0, 00 × 15]     2
1010      [00 × 15, 04]    [a0, 00 × 15]     2
```

The last two messages have the same padded payload but different headers.
-/
def blockForm (message : Message) : List Block :=
  -- Include the length header even for the empty message.
  lengthBlock ⟨message.1.length, message.2⟩ ::
    -- Round the payload length up to a whole number of 128-bit blocks.
    List.ofFn (fun block : Fin ((message.1.length + 127) / 128) =>
      fun bit : Fin 128 =>
        -- Preserve each message bit; only positions beyond its end become padding.
        if withinMessage : 128 * block.val + bit.val < message.1.length then
          if message.1[128 * block.val + bit.val] then 1 else 0
        else 0)

noncomputable instance : Fintype Message :=
  -- Bounded-length lists over the finite bit alphabet form a finite message space.
  (List.finite_length_lt Bool (2 ^ 128)).fintype

instance : Nontrivial Message := by
  -- The empty message and the one-bit zero message are both admitted and distinct.
  refine ⟨⟨⟨[], by norm_num⟩, ⟨[false], by norm_num⟩, ?_⟩⟩
  intro equal
  have := congrArg Subtype.val equal
  simp at this

/-- Equal length headers and matching payload blocks recover the same message. -/
lemma blockForm_prefixFree : ∀ m n, m ≠ n → ¬ blockForm m <+: blockForm n := by
  intro left right different isPrefix
  have bitEncoding_injective : Function.Injective
      (fun bit : Bool => if bit then (1 : ZMod 2) else 0) := by
    intro a b equal
    cases a <;> cases b <;> simp_all
  obtain ⟨headerEqual, payloadPrefix⟩ := List.cons_prefix_cons.mp isPrefix
  -- The header determines the original message length without truncation.
  have lengthEqual : left.1.length = right.1.length := by
    have bitsEqual : BitVec.ofFin ⟨left.1.length, left.2⟩ =
        BitVec.ofFin ⟨right.1.length, right.2⟩ := by
      apply BitVec.eq_of_getMsbD_eq
      intro bit withinBlock
      exact bitEncoding_injective (congrFun headerEqual ⟨bit, withinBlock⟩)
    exact congrArg BitVec.toNat bitsEqual
  apply different
  apply Subtype.ext
  apply List.ext_getElem lengthEqual
  intro bit leftBound rightBound
  -- Read each original bit from its block and offset, before the padding boundary.
  have blockIndex : bit / 128 < (left.1.length + 127) / 128 := by omega
  have blockEqual := payloadPrefix.getElem (i := bit / 128)
    (by simpa only [List.length_ofFn] using blockIndex)
  simp only [List.getElem_ofFn] at blockEqual
  have same := congrFun blockEqual ⟨bit % 128, Nat.mod_lt _ (by norm_num)⟩
  have position : 128 * (bit / 128) + bit % 128 = bit := by omega
  simp only [position, dif_pos leftBound, dif_pos rightBound] at same
  exact bitEncoding_injective same

/-! ### Block former tests -/

-- Length-header and padding checks at the empty message and block boundaries.
#guard
  let vectors : List (Fin 257 × List Nat) := [
    (0, [0]),
    (1, [1, 2 ^ 127]),
    (127, [127, 2 ^ 128 - 2]),
    (128, [128, 2 ^ 128 - 1]),
    (129, [129, 2 ^ 128 - 1, 2 ^ 127]),
    (255, [255, 2 ^ 128 - 1, 2 ^ 128 - 2]),
    (256, [256, 2 ^ 128 - 1, 2 ^ 128 - 1])]
  vectors.all fun (length, expected) =>
    let message : Message :=
      ⟨List.replicate length.val true, by
        rw [List.length_replicate]
        exact length.isLt.trans (by norm_num)⟩
    (blockForm message).map blockEquiv ==
      expected.map (fun block =>
        Vector.ofFn fun i : Fin 16 => UInt8.ofNat (block / 2 ^ (8 * (15 - i.val))))

/-! ## AES-256 CBC-MAC -/

open Classical SystemAlgebra SystemAlgebra.Interface CBCMAC CategoryTheory
open scoped SystemAlgebra

/-- Every message has its length block, so CBC makes at least one primitive call per message. -/
theorem one_le_cbc_bound : 1 ≤ cbc.bound blockForm := by
  simpa [blockForm] using cbc_length_le_bound blockForm ⟨[], by norm_num⟩

/-- `q` messages make at most `cbc.bound * q` primitive calls, at least `q`. -/
theorem le_cbc_bound_mul (q : ℕ) : q ≤ cbc.bound blockForm * q :=
  Nat.le_mul_of_pos_left q one_le_cbc_bound

section PRF

variable (q : ℕ)

/-- `⟪q⟫`: at most `q` queries to the primitive, within CBC's inside budget for `q` messages. -/
local notation "⟪q⟫" => Interface.queryFilter _ _ _ (le_cbc_bound_mul q)

/-- **AES-256 CBC-MAC** (CR18, Theorem 6.1 with the PRF assumption): replacing AES by a random
function under `⟪q⟫` costs its PRF advantage, by equation (6.1); CBC then contributes its
prefix-free collision bound. -/
theorem aes256_cbc_prf (ε : ENNReal) (aesPRF : Δ (⟪q⟫ • aes256.Real) (⟪q⟫ • URF Block Block) ≤ ε) :
    Δ ((θ blockForm q (budget := q) ≫ cbc blockForm) • aes256.Real)
        (θ blockForm q • URF Message Block) ≤
      ε + ENNReal.ofReal ((q : ℝ) ^ 2 / 2 ^ 129) := by
  calc
    _ ≤ Δ ((θ blockForm q (budget := q) ≫ cbc blockForm) • aes256.Real)
            ((θ blockForm q (budget := q) ≫ cbc blockForm) • URF Block Block) +
          Δ ((θ blockForm q (budget := q) ≫ cbc blockForm) • URF Block Block)
            (θ blockForm q • URF Message Block) :=
      distance_triangle _
    _ ≤ ε + ENNReal.ofReal ((q : ℝ) ^ 2 / (2 * Fintype.card Block)) := by
      refine add_le_add ?_ (cbc_randomness_expander blockForm q q blockForm_prefixFree)
      rw [theta_cbc_eq blockForm (le_cbc_bound_mul q), comp_smul, comp_smul]
      exact (distance_smul_le _ _ _).trans aesPRF
    _ = ε + ENNReal.ofReal ((q : ℝ) ^ 2 / 2 ^ 129) := by
      norm_num [Block, Fintype.card_fun, ZMod.card]

end PRF

end AESCBC
