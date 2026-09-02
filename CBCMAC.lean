import CBCMAC.Main

/-!
# CBC-MAC at the Random Systems layer

CR18, Section 6.2.3 (printed pp. 125--127), defines CBC-MAC as a randomness
expander. Theorem 6.1 gives its collision bound for prefix-free block formers.

This library contains the normalized finite-message specialization of that
argument. `CBCMAC.Objects` defines the CBC functions, deterministic
converters, and probabilistic systems; `CBCMAC.Attachment` proves their exact
attachment equations; `CBCMAC.ConditionalEquivalence` and `CBCMAC.Blind`
formalize the two probabilistic steps; and `CBCMAC.Main` proves the resulting
`Δ` bound.

Constructive Cryptography construction statements intentionally live outside
this project.
-/
