import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.32.2"

-- The unit-cost machine witness generation compiles to. See `Clean/Caliper/`.
require caliper from git "https://github.com/zksecurity/caliper"@"a34e40d246a69b204bea1bcffc8b2a761f9d5ca6"
