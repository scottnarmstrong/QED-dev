/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Slash
public import QED.Frozen.Algebra.RestSpinor

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- The on-shell spinor `u_s(p)` of eq. (38.12) in closed form,
`u_s(p) = (m - p̸) u_s(0) / √(2m(m + p⁰))`. Source-facing for `m > 0` and on-shell `p` with
`p⁰ > 0`, where it equals the boosted rest spinor `exp(iη p̂·K) u_s(0)` of (38.12)
(`QED.Dirac.spinor_eq_exp_boost`, for `p⃗ ≠ 0`). Elsewhere the value is not meaningful. -/
noncomputable def spinor (m : ℝ) (p : Fin 4 → ℝ) (s : Fin 2) : Fin 4 → ℂ :=
  (((Real.sqrt (2 * m * (m + p 0)))⁻¹ : ℝ) : ℂ) •
    ((((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) - slash p) *ᵥ restSpinor m s)

end QED.Dirac

end
