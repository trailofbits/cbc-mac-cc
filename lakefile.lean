import Lake

open Lake DSL

package «cbc-mac-cc» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- The library, from GitHub; `lake-manifest.json` pins the exact commit. -/
require ConstructiveCryptography from git
  "https://github.com/trailofbits/constructive-cryptography" @ "categorical"

@[default_target]
lean_lib CBCMAC where
  globs := #[.andSubmodules `CBCMAC]

lean_lib CBCMACTests where
  roots := #[`Tests.CBCMAC.Automation, `Tests.CBCMAC.Axioms]
