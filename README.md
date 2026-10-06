# CBC-MAC in Constructive Cryptography

For a prefix-free block former `blockForm : M → List X`, with a finite nontrivial message type
`M` and a finite nonempty additive commutative group `X` of blocks, this project proves Theorem
6.1 of [1] (printed p. 126):

```lean
theorem cbc_randomness_expander [Nontrivial M] (blockForm : M → List X) (q n : ℕ)
    (prefixFree : ∀ m m', m ≠ m' → ¬ blockForm m <+: blockForm m') :
    Δ ((θ blockForm q (budget := n) ≫ cbc blockForm) • URF X X) (θ blockForm q • URF M X) ≤
      ENNReal.ofReal ((q : ℝ) ^ 2 / (2 * Fintype.card X))
```

CBC under the uniform random function on blocks, restricted by $\theta$ to $q$ encoded blocks,
is within $q^2/(2|X|)$ of the uniform random function on messages under the same restriction.
Here $q$ counts all encoded blocks, across all messages; it is not a message length, nor the
number of messages times their maximum length. `n` bounds the number of messages, and the bound
does not depend on it.

Equation (6.1) of [1] says that after $\theta$, CBC makes at most $q$ primitive queries:

```lean
theorem theta_cbc_eq (blockForm : M → List X) {q n : ℕ} (hq : q ≤ cbc.bound blockForm * n) :
    θ blockForm q (budget := n) ≫ cbc blockForm =
      cbc.exact blockForm (budget := q) (queries := n) ≫ Interface.queryFilter _ _ _ hq
```

Here `cbc.exact` is CBC typed by encoded blocks, and `Interface.queryFilter`, written $⟪q⟫$, is
the filter from $q$ primitive queries to CBC's inside budget. For AES-256 on 128-bit blocks,
with the length-prefixed block former for bit strings, `aes256_cbc_prf` concludes

$$\Delta\big((\theta \gg \mathrm{CBC})\,\mathrm{AES},\ \theta\,\mathrm{URF}\big) \le \varepsilon + q^2/2^{129}$$

from the assumption $\Delta(⟪q⟫\,\mathrm{AES},\ ⟪q⟫\,\mathrm{URF}) \le \varepsilon$: AES-256 is within
$\varepsilon$ of the uniform random function under $q$ block queries.

The theorem is the one of [1], a construction statement: the block former is prefix-free and the
distinguisher is unrestricted. It is not Theorem 6.3 of [2], which bounds prefix-free adversaries
against the CBC PRF by $\mathrm{PRFadv} + (Q\ell)^2/2|X|$.

## The proof

The proof is the one of [1]: CBC under a uniform round function is conditionally equivalent to
the uniform message function, the condition being that no two round inputs collide.

- **Systems.** The uniform random functions are sampled functions: `URF_eq` presents
  `URF X Y` as a function sampled uniformly once. The converter `cbc` is the converter of a
  program. Against a fixed round function `f`, it makes the calls of the fold of a message's
  blocks and returns their CBC value (`cbc_answer`), so the program attached to the system of
  `f` is the system of the CBC function, and CBC attached to `f` is the CBC function on
  messages (`cbc_smul_ofFunction`). CBC under the uniform round function is then the sampled CBC
  function, and the filter `θ` on it, or on the uniform message function, is the sampled
  function on the restricted interface.
- **Game.** The collision game `cbcGame` samples the round function with the hidden collision
  condition `cbcBad`. Until it is set, the CBC function has the law of the uniform message
  function (`cbc_game_equiv`, from the counting of `Collisions`), and the blind winning
  probability is at most $q(q-1)/(2|X|) \le q^2/(2|X|)$ (`cbcGame_blind_bound`).
- **Distance.** Game equivalence bounds the distance of the resources by the blind winning
  probability, which gives the theorem. For AES-256, equation (6.1) rewrites `θ ≫ cbc` as
  `cbc.exact ≫ ⟪q⟫`, and the triangle inequality and non-expansion of attachment add the PRF
  assumption at $q$ queries.

## Modules

Import `CBCMAC`. The modules follow the order of the argument:

1. [CBC](CBCMAC/CBC.lean): the CBC function `cbcFunction`, the converter `cbc` and its typing
   `cbc.exact`, the filter `θ`, `cbc_answer`, `cbc_smul_ofFunction` and equation (6.1),
   `theta_cbc_eq`.
2. [Collisions](CBCMAC/Collisions.lean): round-input collisions under a uniform round function.
3. [Randomness expander](CBCMAC/RandomnessExpander.lean): `URF_eq`, the collision game,
   `cbc_game_equiv`, `cbcGame_blind_bound` and `cbc_randomness_expander`.
4. [AES-CBC-MAC](CBCMAC/AESCBCMAC.lean): AES-256 of the library on 128-bit blocks, read as bytes
   as in [3, §3.3] and checked against the vectors of [4, F.1.5]; the length-prefixed block
   former, a variant of [2, §6.6.1, method 1], with its prefix-freeness and padding tests; and
   `aes256_cbc_prf`.

The components are declared in the DSL of the library: `converter cbc` and `filter θ`.
`URF X Y` is local notation for the library's uniform random function on the interface of a
function, `Evaluation X Y`, and AES-256 under a uniform key is the library's `BlockCipher.Real`.

## Upstream candidates

The argument needs lemmas the library does not have yet. They are in `CBCMAC/Upstream`, to be
proposed to the library; each file names the library module it belongs to.

| Declaration | Target module | Content |
|---|---|---|
| `functionSystem`, `Program.answer` | `RandomSystems.Converter.ProgramAttachment` | the system of a function, and an invocation run against a function |
| `Program.Consistent.of_snoc`, `Program.Consistent.length_le`, `Program.answer_of_exchanges` | `RandomSystems.Converter.ProgramAttachment` | an invocation whose body makes its exchanges itself returns what the body returns |
| `Program.feed_function`, `Program.inline_function`, `Program.trim_apply_ofProgramOn_function` | `RandomSystems.Converter.ProgramAttachment` | a program attached to a function, beside `inline_automatonSystem` |
| `DSL.foldTranscript` and its lemmas | `ConstructiveCryptography.DSL.Programs` | a loop against a function makes its calls and returns the fold |
| `Resource.sample_fTransform`, `Resource.smul_sample` | `ConstructiveCryptography.Functional` | sampling along a map, and attachment to a sampled resource |
| `filter_smul_ofFunction` | `ConstructiveCryptography.Functional` | a filter on a function is the function, from the library's `filter_smul` |
| `Resource.ofFunction_eq_ofDeterministic` | `ConstructiveCryptography.Functional` | a function is a deterministic resource |
| `ofDDC_ofProgramOn_smul_ofFunction` | `ConstructiveCryptography.DSL.Converters` | the converter of a program on a function, beside `ofDDC_ofProgramOn_smul_ofAutomaton` |
| `queryFilter` | `ConstructiveCryptography.InterfaceFilter` | the query filter from `q` queries to `B ≥ q` |

The files are [ProgramAttachment](CBCMAC/Upstream/ProgramAttachment.lean),
[Program](CBCMAC/Upstream/Program.lean) and [Resource](CBCMAC/Upstream/Resource.lean).

## Checking

The library is a Lake dependency, pinned in `lake-manifest.json`:

```sh
lake build CBCMAC CBCMACTests
```

[The axiom audit](Tests/CBCMAC/Axioms.lean) prints the axioms of the results. Only `propext`,
`Classical.choice` and `Quot.sound` appear. The AES-256 and block-former vectors are `#guard`
checks, run by the build.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
3. National Institute of Standards and Technology. *Advanced Encryption Standard (AES)*. FIPS 197,
   updated 2023.
4. M. Dworkin. *Recommendation for Block Cipher Modes of Operation: Methods and Techniques*. NIST
   Special Publication 800-38A, 2001.
