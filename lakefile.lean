import Lake

open Lake DSL

package «cbc-mac-cc» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require ConstructiveCryptography from "../abstract-crypto"

@[default_target]
lean_lib CBCMAC where
  globs := #[.andSubmodules `CBCMAC]

lean_lib CBCMACTests where
  roots := #[`Tests.CBCMAC.Automation, `Tests.CBCMAC.Axioms]
