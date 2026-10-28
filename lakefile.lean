import Lake
open Lake DSL

package qrhDescent where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from "upstream/.lake/packages/mathlib"

@[default_target] lean_lib QRH
