import CBCMAC.CBC
import CBCMAC.Collisions
import CBCMAC.RandomnessExpander
import CBCMAC.AESCBCMAC

/-!
# CBC-MAC in Constructive Cryptography

CR18, Section 6.2.3 (printed pp. 125–127), treats CBC-MAC as a randomness expander; Theorem 6.1
gives its collision bound for prefix-free block formers. The modules follow the order of the
argument:

1. `CBC`: the CBC function, the converter `cbc` with its exact typing `cbc.exact`, the filter
   `θ`, CBC on a function, `cbc_smul_ofFunction`, and CR18's equation (6.1),
   `θ ≫ cbc = cbc.exact ≫ ⟪q⟫`.
2. `Collisions`: counting round-input collisions under a uniform round function.
3. `RandomnessExpander`: CR18 Theorem 6.1,
   `Δ ((θ ≫ cbc) • URF X X) (θ • URF M X) ≤ q²/(2|X|)`, by conditional equivalence and the
   blind collision bound.
4. `AESCBCMAC`: AES-256 on bit blocks, the length-prefixed block former for bit strings, its
   prefix-freeness, and the AES instantiation `aes256_cbc_prf`.

`CBCMAC.Upstream` holds the upstream candidates: lemmas the argument needs that the library does
not have yet, to be proposed to it. They are a program attached to a function, loops against a
function, sampling, filters and programs on functions, and the query filter.
-/
