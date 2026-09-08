import CBCMAC.Main
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

/-!
# AES-256 CBC-MAC with a length prefix

The first block contains the message's bit length, most significant bit first.
Payload bits follow in order; only the last payload block is zero-padded.
Messages have fewer than `2^128` bits, so the length header never wraps.

`mac` is the concrete keyed function; `apply_cbc_aes_eq_mac` identifies it
with the CBC converter attached to AES. `aes256_cbc_prf` adds the assumed
AES distinguishing advantage to the existing prefix-free CBC bound.
-/

namespace AESCBC

/-! ## Carriers -/

/-- A 128-bit block, with pointwise addition giving XOR rather than integer addition. -/
abbrev Block := Fin 128 → ZMod 2

/-- All 256-bit AES keys. -/
abbrev Key := Fin (2 ^ 256)

/-- A bit string whose length fits in one 128-bit header. -/
abbrev Message := { bits : List Bool // bits.length < 2 ^ 128 }

/-! ## AES-256 implementation -/

namespace AES256

/-- FIPS 197, Table 4: the AES substitution box, indexed by the input byte. -/
def sboxTable : Vector (Vector UInt8 16) 16 := #v[
  #v[0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76],
  #v[0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0],
  #v[0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15],
  #v[0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75],
  #v[0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84],
  #v[0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf],
  #v[0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8],
  #v[0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2],
  #v[0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73],
  #v[0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb],
  #v[0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79],
  #v[0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08],
  #v[0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a],
  #v[0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e],
  #v[0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf],
  #v[0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]]

def sbox (byte : UInt8) : UInt8 :=
  -- The high nibble selects the row; the low nibble selects the column.
  -- Example: 0x53 selects row 5, column 3, whose entry is 0xed.
  let row := sboxTable[byte.toNat / 16]'(by have := byte.toNat_lt; omega)
  row[byte.toNat % 16]

/-- FIPS 197, Equation (4.5): multiplication by x modulo x⁸+x⁴+x³+x+1. -/
def xtime (byte : UInt8) : UInt8 :=
  -- Shift once; a former top bit triggers reduction by the low polynomial bits.
  (byte <<< 1) ^^^ (if byte &&& 0x80 == 0 then 0 else 0x1b)

/-- FIPS 197, Algorithm 2, with Nk = 8 and Nr = 14. -/
def keyExpansion (key : Vector UInt8 32) : Vector UInt8 240 :=
  -- The first eight words are the key; subsequent words fill the remaining bytes.
  let initial : Vector UInt8 240 := Vector.ofFn fun i =>
    if h : i.val < 32 then key[i.val] else 0
  -- Derive words 8 through 59, carrying the expanded key between steps.
  (List.finRange 52).foldl (fun expanded word =>
    let i := 8 + word.val
    -- Each new word depends on the immediately preceding word.
    let previous : Vector UInt8 4 := Vector.ofFn fun j =>
      expanded[4 * (i - 1) + j.val]'(by have := word.isLt; have := j.isLt; omega)
    let transformed : Vector UInt8 4 :=
      -- Every eighth word uses RotWord, SubWord, and the round constant.
      if i % 8 = 0 then
        -- Successive round constants are powers of x in the AES byte field.
        let rcon := (List.range (i / 8 - 1)).foldl (fun value _ => xtime value) 1
        Vector.ofFn fun j =>
          sbox previous[(j.val + 1) % 4] ^^^ (if j.val = 0 then rcon else 0)
      -- Halfway through each group of eight, AES-256 applies SubWord alone.
      else if i % 8 = 4 then previous.map sbox
      else previous
    -- XOR with the word eight positions earlier to obtain the new four bytes.
    (List.finRange 4).foldl (fun result j =>
      let byte := expanded[4 * (i - 8) + j.val]'(by
        have := word.isLt; have := j.isLt; omega) ^^^ transformed[j]
      result.set (4 * i + j.val) byte (by
        have := word.isLt; have := j.isLt; omega)) expanded) initial

/-- FIPS 197, Equation (5.5), with state index r + 4c.

Positions in the flat input vector, arranged as the AES state:

```text
before ShiftRows       after ShiftRows
 0   4   8  12          0   4   8  12
 1   5   9  13          5   9  13   1
 2   6  10  14         10  14   2   6
 3   7  11  15         15   3   7  11
```
-/
def shiftRows (state : Vector UInt8 16) : Vector UInt8 16 :=
  -- Index i has row i % 4 and column i / 4; row r shifts left by r columns.
  Vector.ofFn fun i =>
    state[4 * ((i.val / 4 + i.val % 4) % 4) + i.val % 4]'(by omega)

/-- FIPS 197, Equation (5.8): the four-byte column transformation. -/
def mixColumns (state : Vector UInt8 16) : Vector UInt8 16 :=
  Vector.ofFn fun i =>
    -- Read the current column cyclically, starting at the output byte's row.
    let a := fun offset : Nat =>
      state[4 * (i.val / 4) + (i.val % 4 + offset) % 4]'(by
        have := i.isLt; omega)
    -- The coefficients are 2, 3, 1, 1; multiplication by 3 is xtime(a) XOR a.
    xtime (a 0) ^^^ xtime (a 1) ^^^ a 1 ^^^ a 2 ^^^ a 3

/-- FIPS 197, Equation (5.9): XOR the round key into the state. -/
def addRoundKey (state : Vector UInt8 16) (expanded : Vector UInt8 240)
    (round : Fin 15) : Vector UInt8 16 :=
  -- Round r uses bytes 16r through 16r + 15 of the expanded key.
  Vector.ofFn fun i =>
    state[i] ^^^ expanded[16 * round.val + i.val]'(by
      have := round.isLt; have := i.isLt; omega)

/-- AES-256 encryption: initial key addition, thirteen full rounds, then a
final round without MixColumns (FIPS 197, Algorithm 1). -/
def encryptBytes (key : Vector UInt8 32) (input : Vector UInt8 16) :
    Vector UInt8 16 :=
  -- Derive the fifteen round keys from the supplied 256-bit key.
  let expanded := keyExpansion key
  -- Rounds 1 through 13 perform substitution, row shifting, column mixing, and XOR.
  let state := (List.finRange 13).foldl (fun state round =>
    addRoundKey (mixColumns (shiftRows (state.map sbox))) expanded
      ⟨round.val + 1, by have := round.isLt; omega⟩)
    -- Before round 1, XOR the input with round key 0.
    (addRoundKey input expanded 0)
  -- Round 14 omits column mixing.
  addRoundKey (shiftRows (state.map sbox)) expanded 14

end AES256

/-- Pack a block into sixteen bytes, most significant bit first. -/
def blockBytes (block : Block) : Vector UInt8 16 :=
  -- Read each group of eight bits as a binary number, most significant bit first.
  Vector.ofFn fun byte => UInt8.ofNat
    ((List.finRange 8).foldl (fun value bit =>
      2 * value + (block ⟨8 * byte.val + bit.val, by
        have := byte.isLt; have := bit.isLt; omega⟩).val) 0)

/-- AES-256 on bit-string blocks, with the FIPS byte order at both boundaries. -/
def encrypt (key : Key) (input : Block) : Block :=
  -- Extract the key's bytes from most to least significant, retaining leading zeros.
  let keyBytes : Vector UInt8 32 := Vector.ofFn fun i =>
    UInt8.ofNat (key.val / 2 ^ (8 * (31 - i.val)))
  let output := AES256.encryptBytes keyBytes (blockBytes input)
  -- Recover bit i from byte i / 8, again numbering bits from the most significant end.
  fun bit => if
      (output[bit.val / 8]'(by have := bit.isLt; omega) >>>
        UInt8.ofNat (7 - bit.val % 8)) &&& 1 == 0 then 0 else 1

/-! ## Length-prefixed CBC-MAC -/

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

/-- Length-prefixed AES-256 CBC-MAC, starting from the all-zero block.

For a message occupying one payload block `P`, with length header `H`:

```text
0 -- XOR H --> H -- AES(key) --> c₁ -- XOR P --> c₁ XOR P -- AES(key) --> tag
```

The same key is used at both calls; the header is authenticated as a block.
-/
def mac (key : Key) (message : Message) : Block :=
  -- Fold c ← AES(key, c XOR block) from c = 0 and return the final chaining value.
  CBCMAC.CBCCombinatorics.cbc (encrypt key) (blockForm message)

/-! ## Random Systems model -/

noncomputable section

open CategoryTheory Probability RandomSystems.Ambient
open scoped CBCMAC RandomSystems.Ambient.DDC

/-- Sample one uniform AES-256 key and reuse it for every block query. -/
def AES : RandomSystems.RandomFunction Block Block :=
  -- Push the uniform key law through encryption, producing a law on block functions.
  ⟨Distribution.PMF
    ⟨Distribution.uniform Key, Distribution.uniform_isProbDist⟩ encrypt⟩

-- R answers block queries; V answers whole-message queries.
local notation "R" => CBCMAC.R (X := Block)
local notation "V" => CBCMAC.V (M := Message) (X := Block)
-- [q] limits calls to the round function.
local notation:max "[" q "]ᶜ" =>
  DDC.asHom (DDC.queryLimit (X := Block) (Y := Block) q)
-- θ limits the total encoded blocks across all submitted messages.
local notation:max "θ[" q "]" =>
  DDC.asHom (RandomSystems.DomainFilter.toDDC (Y := Block)
    (CBCMAC.theta blockForm q))
local notation:max "Δ(" left ", " right ")" => dist left right

/-! ## Proofs -/

section Proofs

noncomputable instance : Fintype Message :=
  -- Bounded-length lists over the finite bit alphabet form a finite message space.
  (List.finite_length_lt Bool (2 ^ 128)).fintype

instance : Nontrivial Message := by
  -- The empty message and the one-bit zero message are both admitted and distinct.
  refine ⟨⟨⟨[], by norm_num⟩, ⟨[false], by norm_num⟩, ?_⟩⟩
  intro equal
  have := congrArg Subtype.val equal
  simp at this

/-- A prefix relation between encodings forces the original messages to coincide.
In the drawings below, `H(n)` is the 128-bit encoding of bit length `n`,
and `L_j`, `R_j` are payload blocks numbered from zero. -/
lemma blockForm_prefixFree : CBCMAC.PrefixFree blockForm := by
  -- 1. Assume left ≠ right, but encoding(left) is a prefix of encoding(right).
  intro left right different isPrefix
  -- The prefix assumption gives equality at EVERY block position present on the left:
  --
  -- left:   [ H(nL) ] [ L_0 ] ... [ L_(k-1) ]
  --             =        =             =
  -- right:  [ H(nR) ] [ R_0 ] ... [ R_(k-1) ] [ possible extra blocks ]
  --
  -- At this point we have not ruled out extra blocks on the right.
  -- Removing the headers leaves the same alignment of the payload blocks.
  -- If k = 0, the left encoding consists only of its header.
  obtain ⟨headerEqual, payloadPrefix⟩ := List.cons_prefix_cons.mp isPrefix
  -- 2. Decode the equal headers to recover equal ORIGINAL message lengths.
  have lengthEqual : left.1.length = right.1.length := by
    let leftLength : Fin (2 ^ 128) := ⟨left.1.length, left.2⟩
    let rightLength : Fin (2 ^ 128) := ⟨right.1.length, right.2⟩
    -- First compare the 128 individual header bits:
    --
    -- H(nL):  [ hL_0 ... hL_j ... hL_127 ]
    --             =       =         =
    -- H(nR):  [ hR_0 ... hR_j ... hR_127 ]
    --
    -- Equality holds at every j, so the two BitVec length words are equal.
    have bitsEqual : BitVec.ofFin leftLength = BitVec.ofFin rightLength := by
      apply BitVec.eq_of_getMsbD_eq
      intro bit withinBlock
      have same := congrFun headerEqual ⟨bit, withinBlock⟩
      -- Header entries store false as 0 and true as 1; these values are distinct.
      change (if (BitVec.ofFin leftLength).getMsbD bit then (1 : ZMod 2) else 0) =
        (if (BitVec.ofFin rightLength).getMsbD bit then 1 else 0) at same
      cases hl : (BitVec.ofFin leftLength).getMsbD bit <;>
        cases hr : (BitVec.ofFin rightLength).getMsbD bit <;> simp_all
    -- H(nL) = H(nR)  --decode-->  nL = nR.
    -- Both lengths are below 2^128: decoding recovers nL and nR, not their residues.
    exact congrArg BitVec.toNat bitsEqual
  -- 3. Equal lengths give the same number of payload blocks and the same padding boundary:
  --
  -- left:   [ H(n) ] [ L_0 ] ... [ L_(k-1) ] END
  --             =       =            =
  -- right:  [ H(n) ] [ R_0 ] ... [ R_(k-1) ] END
  --
  -- Here k = ceil(n / 128), so the possible extra blocks have disappeared.
  -- To obtain left = right, now compare the original lists bit by bit.
  apply different
  apply Subtype.ext
  apply List.ext_getElem lengthEqual
  intro bit leftBound rightBound
  -- 4. Locate an arbitrary original bit in the payload (the header is excluded).
  -- Its block index is j = bit / 128 and its offset is t = bit % 128.
  --
  -- Example for a 131-bit message:
  -- payload block: [          0          ] [          1           ]
  -- bit positions: [ 0 ...          127 ] [ 128 129 130 | padding ]
  -- offsets:       [ 0 ...          127 ] [   0   1   2 | ...     ]
  --                                                ^
  --                                      bit 130 = 128 * 1 + 2
  --
  -- Since bit < n, its block index j is inside the left payload.
  have blockIndex : bit / 128 < (left.1.length + 127) / 128 := by
    omega
  -- 5. Select the matching blocks L_j = R_j from the payload prefix relation.
  have blockEqual := payloadPrefix.getElem (i := bit / 128)
    (by simpa only [List.length_ofFn] using blockIndex)
  simp only [List.getElem_ofFn] at blockEqual
  -- Read offset t in those equal blocks:
  --
  -- L_j:  [ ... left[bit]  ... ]
  --                 =
  -- R_j:  [ ... right[bit] ... ]
  --                 ^
  --              offset t
  have same := congrFun blockEqual ⟨bit % 128, Nat.mod_lt _ (by decide)⟩
  have position : 128 * (bit / 128) + bit % 128 = bit := by omega
  -- The selected bit is before the common padding boundary:
  --
  -- left:   [ original message bits ... | zero padding ]
  -- right:  [ original message bits ... | zero padding ]
  --                 ^ bit < n          ^ n
  --
  -- Thus blockForm supplies a message bit on both sides, not a padding zero.
  simp only [position, dif_pos leftBound, dif_pos rightBound] at same
  -- 6. The 0/1 entries agree, so the Boolean message bits agree.
  -- This holds for every bit: same length + same bits gives left = right,
  -- contradicting the initial assumption left ≠ right.
  cases hl : left.1[bit] <;> cases hr : right.1[bit] <;> simp_all

/-- An alternative prefix-freeness proof, splitting on equality of message lengths. -/
lemma blockForm_prefixFree_by_length_cases : CBCMAC.PrefixFree blockForm := by
  -- Suppose two distinct messages have encodings in a prefix relation.
  intro left right different isPrefix

  -- Encoding maps false to 0 and true to 1.
  -- Thus equal encoded values imply equal original bits.
  have bitEncoding_injective : Function.Injective
      (fun bit : Bool => if bit then (1 : ZMod 2) else 0) := by
    intro a b equal
    cases a <;> cases b <;> simp_all

  -- Every allowed length fits in 128 bits without truncation.
  -- Therefore equal headers encode equal lengths.
  have lengthBlock_injective : Function.Injective lengthBlock := by
    intro a b headerEqual
    -- Equal header entries decode to equal Boolean bits at every position.
    have bitsEqual : BitVec.ofFin a = BitVec.ofFin b := by
      apply BitVec.eq_of_getMsbD_eq
      intro bit withinBlock
      exact bitEncoding_injective (congrFun headerEqual ⟨bit, withinBlock⟩)
    -- Reading the equal bit vectors as numbers gives a = b.
    exact congrArg BitVec.toFin bitsEqual

  -- Equal message lengths put the padding boundary at the same position.
  -- Equal encodings therefore agree on all bits before that boundary: the messages.
  have message_eq_of_encoding_eq
      (sameLength : left.1.length = right.1.length)
      (sameEncoding : blockForm left = blockForm right) : left = right := by
    -- Remove the first block (the header); the remaining payload lists are equal.
    have payloadEqual := (List.cons.inj sameEncoding).2
    apply Subtype.ext
    -- The original lists have equal lengths; compare their bits at any position.
    apply List.ext_getElem sameLength
    intro bit leftBound rightBound
    -- Since bit < message length, payload block bit / 128 exists.
    have blockIndex : bit / 128 < (left.1.length + 127) / 128 := by omega
    -- Select that block from each of the equal payload lists.
    have blockEqual := List.getElem_of_eq payloadEqual
      (i := bit / 128) (by simpa only [List.length_ofFn] using blockIndex)
    simp only [List.getElem_ofFn] at blockEqual
    -- Equal blocks have equal entries at offset bit % 128.
    have same := congrFun blockEqual ⟨bit % 128, Nat.mod_lt _ (by decide)⟩
    have position : 128 * (bit / 128) + bit % 128 = bit := by omega
    -- This position is inside both messages, so neither side is a padding bit.
    simp only [position, dif_pos leftBound, dif_pos rightBound] at same
    exact bitEncoding_injective same

  by_cases lengthEqual : left.1.length = right.1.length
  -- Equal bit lengths give equal numbers of encoded blocks.
  -- The prefix relation matches every block, with no extra blocks on the right.
  · -- left:   [ H(n) ] [ L_0 ] ... [ L_(k-1) ] END
    --             =       =            =
    -- right:  [ H(n) ] [ R_0 ] ... [ R_(k-1) ] END
    have encodingsEqual : blockForm left = blockForm right :=
      isPrefix.eq_of_length (by
        simp only [blockForm, List.length_cons, List.length_ofFn, lengthEqual])
    -- Recovering equal messages contradicts the assumption that they are distinct.
    exact different (message_eq_of_encoding_eq lengthEqual encodingsEqual)
  -- Different bit lengths give different length headers.
  -- A prefix relation would require those very first blocks to agree.
  · -- left:   [ H(nL) ] [ ... payload ... ]
    --            ≠
    -- right:  [ H(nR) ] [ ... payload ... ]
    -- Extract the header equality required by the assumed prefix relation.
    have headerEqual := (List.cons_prefix_cons.mp isPrefix).1
    -- Decoding these equal headers gives equal lengths, contradicting this case.
    exact lengthEqual (congrArg Fin.val (lengthBlock_injective headerEqual))

/-- The CBC converter attached to AES evaluates `mac` under one uniform key. -/
lemma apply_cbc_aes_eq_mac :
    DDC.asHom (CBCMAC.cbc blockForm) • AES.toAmbientPDS =
      Distribution.PMF
        ⟨Distribution.uniform Key, Distribution.uniform_isProbDist⟩
        (fun key => DDS.ofFunction (mac key)) := by
  -- Use the generic attachment equation for CBC over a random function.
  rw [CBCMAC.apply_cbc_randomFunction]
  apply Subtype.ext
  -- Sampling a key, then its AES function, then CBC equals evaluating mac with that key.
  exact Distribution.fTransform_fTransform _ _ _

/-- The AES PRF error plus the prefix-free CBC collision bound. The hypothesis
uses full RS distinguishing advantage for at most `q` block queries. The budget
counts the length header and the padded payload of every message.

The two proved distances meet at CBC with a uniform round function:

```text
(θ[q] ≫ CBC[blockForm]) • ([q]ᶜ • AES)
    | replacement: distance ≤ ε
(θ[q] ≫ CBC[blockForm]) • ([q]ᶜ • R)
    | idealRoundFunction: distance ≤ q² / 2^129
θ[q] • V
```

The triangle inequality adds these two errors.
-/
theorem aes256_cbc_prf (q : Nat) (ε : ℝ)
    -- Assume AES is within ε of the uniform function under q block queries.
    (aesPRF : Δ([q]ᶜ • AES, [q]ᶜ • R) ≤ ε) :
    -- Compare the resulting length-prefixed CBC-MAC with the ideal message function.
    Δ((θ[q] ≫ CBC[blockForm]) • ([q]ᶜ • AES), θ[q] • V) ≤
      ε + (q : ℝ) ^ 2 / 2 ^ 129 := by
  -- Replacing AES by the uniform round function costs at most its PRF error.
  have replacement :
      Δ((θ[q] ≫ CBC[blockForm]) • ([q]ᶜ • AES),
        (θ[q] ≫ CBC[blockForm]) • ([q]ᶜ • R)) ≤ ε :=
    (RandomSystem.advantage_applyDDC_le
      (θ[q] ≫ CBC[blockForm]) ([q]ᶜ • AES) ([q]ᶜ • R)).trans aesPRF
  -- Apply the existing CBC theorem to the length-prefixed encoding.
  have idealRoundFunction :
      Δ((θ[q] ≫ CBC[blockForm]) • ([q]ᶜ • R), θ[q] • V) ≤
        (q : ℝ) ^ 2 / 2 ^ 129 := by
    -- There are 2^128 blocks, so the CBC denominator 2|X| is 2^129.
    convert CBCMAC.cbc_randomness_expander blockForm q blockForm_prefixFree using 1 <;>
      norm_num [Block, Fintype.card_fun, ZMod.card,
        RandomSystems.DomainFilter.smul_randomSystem_eq]
  -- Use CBC with a uniform round function as the intermediate system and add both errors.
  exact (dist_triangle _ _ _).trans (add_le_add replacement idealRoundFunction)

end Proofs

end

/-! ## Executable tests -/

section Tests

-- NIST SP 800-38A, F.1.5: all four AES-256 encryption vectors, including
-- the bit/byte conversions used by the random system.
#guard
  let key : Key :=
    ⟨0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4, by decide⟩
  let vectors : List (Nat × Nat) := [
    (0x6bc1bee22e409f96e93d7e117393172a, 0xf3eed1bdb5d2a03c064b5a7e3db181f8),
    (0xae2d8a571e03ac9c9eb76fac45af8e51, 0x591ccb10d410ed26dc5ba74a31362870),
    (0x30c81c46a35ce411e5fbc1191a0a52ef, 0xb6ed21b99ca6f4f9f153e7b1beafed1d),
    (0xf69f2445df4f9b17ad2b417be66c3710, 0x23304b7a39f9f3ff067d8d8f9e24ecc7)]
  vectors.all fun (input, expected) =>
    blockBytes (encrypt key (lengthBlock ⟨input % 2 ^ 128, Nat.mod_lt _ (by decide)⟩)) ==
      (Vector.ofFn fun i : Fin 16 => UInt8.ofNat (expected / 2 ^ (8 * (15 - i.val))))

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
    (blockForm message).map blockBytes ==
      expected.map (fun block =>
        Vector.ofFn fun i : Fin 16 => UInt8.ofNat (block / 2 ^ (8 * (15 - i.val))))

end Tests

end AESCBC
