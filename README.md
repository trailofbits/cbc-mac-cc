# CBC-MAC in Random Systems

A Lean 4 formalization of the finite-message Random Systems bound corresponding
to CR18, Theorem 6.1.

For a prefix-free block former $\mathsf{bf} : M \to \mathrm{List}(X)$ and a total
block budget $q$, the development proves

```math
\Delta\left(
  \theta_q \circ \mathrm{CBC}_{\mathsf{bf}}\bigl([q]R_{X,X}\bigr),
  \theta_q V_{M,X}
\right)
\leq \frac{q^2}{2\lvert X\rvert}.
```

Here $M$ is a finite nontrivial message type and $X$ is a finite nonempty
additive commutative group.

## Main result

[`CBCMAC.cbc_randomness_expander`](CBCMAC/Main.lean) compares the public random
systems `CBCMAC.cbcReal` and `CBCMAC.cbcIdeal`. The development also exposes:

- `CBCMAC.realPDS_eq`, the exact CBC attachment equation;
- `CBCMAC.cbcCollisionGame_conditionallyEquivalent_urf`, CR18 equation (6.2);
- `CBCMAC.supWinProb_blind_restrictedCBCCollisionGame_le`, the blind-game
  collision bound $q^2/(2\lvert X\rvert)$.

## Modules

| Module | Contents |
| --- | --- |
| [`CBCMAC.Combinatorics`](CBCMAC/Combinatorics.lean) | CBC recurrence, prefix-free collision condition, and finite counting |
| [`CBCMAC.Objects`](CBCMAC/Objects.lean) | CBC converter, restrictions, and real and ideal systems |
| [`CBCMAC.Attachment`](CBCMAC/Attachment.lean) | Exact converter-attachment equations |
| [`CBCMAC.ConditionalEquivalence`](CBCMAC/ConditionalEquivalence.lean) | CBC collision game and CR18 equation (6.2) |
| [`CBCMAC.Blind`](CBCMAC/Blind.lean) | Total-block restriction and blind collision bound |
| [`CBCMAC.Probability`](CBCMAC/Probability.lean) | Fixed-interface and attached-PDS identification |
| [`CBCMAC.Main`](CBCMAC/Main.lean) | CR18 proof chain and public Random Systems theorem |

Import `CBCMAC` for the complete public development or `CBCMAC.Main` for
the main theorem and its dependencies.

## Build

The project uses Lean 4.33.1 and expects `abstract-crypto` at
`../abstract-crypto`.

```sh
lake build CBCMAC CBCMACTests
```

`CBCMACTests` checks the proof automation and reports the axioms of the public
results.

## Reference

Ueli Maurer, *Cryptography Foundations*, ETH Zürich, Spring 2018,
Section 6.2.3, Theorem 6.1.
