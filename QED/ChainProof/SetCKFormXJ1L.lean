/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXG2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-1 `u`-integrand of `I(X)` in log letters

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+). With `Y = coordY1 X u = P/M`, `P = X² + (1 - X)u`, `M = coordM X u`, and
`s_lo = (X - u)(X + u - Xu)/P`:

**`formXJ1_eq_L`**: for `X ∈ (0, 1)`, `u ∈ (0, X)`, `formXJ1 X u = formXJ1L X u =
r₁ + ℓ₁ (log(1 - u) - log(X - u) - log(X + u - Xu) + log P)`, `ℓ₁ = b₂(Y, u)/(12(Y - 1))`
(`formXlc1`; closed form `formXlc1_eq`), `r₁ = formXJ1r` rational.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The rational part of the branch-1 `s`-antiderivative `A₁`. -/
noncomputable def formXA1r (Y u s : ℝ) : ℝ :=
  (-formXb0 Y u / (2 * s ^ 2) - formXb1 Y u / s + formXb3 Y u * s + formXb4 Y * s ^ 2 / 2) /
    (12 * (Y - 1))

/-- The rational part `r₁` of the branch-1 `u`-integrand. -/
noncomputable def formXJ1r (X u : ℝ) : ℝ :=
  formXA1r (coordY1 X u) u (1 - u) - formXA1r (coordY1 X u) u (coordSLo X u)

/-- The common log coefficient `ℓ₁ = b₂(Y, u)/(12(Y - 1))`. -/
noncomputable def formXlc1 (X u : ℝ) : ℝ :=
  formXb2 (coordY1 X u) u / (12 * (coordY1 X u - 1))

/-- **The branch-1 `u`-integrand in log letters.** -/
noncomputable def formXJ1L (X u : ℝ) : ℝ :=
  formXJ1r X u + formXlc1 X u *
    (log (1 - u) - log (X - u) - log (X + u - X * u) + log (X ^ 2 + (1 - X) * u))

section

variable {X u : ℝ}

theorem formXJ1_eq_L (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    formXJ1 X u = formXJ1L X u := by
  have h1 : 0 < X - u := by linarith [hu.2]
  have h2 : 0 < X + u - X * u := by nlinarith [hu.1, hX.2]
  have h3 : 0 < X ^ 2 + (1 - X) * u := by nlinarith [hu.1, hX.1, hX.2]
  have hl : log (coordSLo X u) =
      log (X - u) + log (X + u - X * u) - log (X ^ 2 + (1 - X) * u) := by
    unfold coordSLo
    rw [log_div (by positivity) h3.ne', log_mul h1.ne' h2.ne']
  unfold formXJ1 formXA1 formXJ1L formXJ1r formXA1r formXlc1
  rw [hl]
  ring

theorem hasDerivAt_coordM (X u : ℝ) : HasDerivAt (coordM X) (1 - X) u := by
  have h := (((hasDerivAt_id' u).const_add 1).const_mul (1 - X)).const_add (X ^ 2)
  unfold coordM
  exact h.congr_deriv (by ring)

/-- The closed form of `ℓ₁`. -/
theorem formXlc1_eq (hX : X ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) :
    formXlc1 X u =
    (12 * u ^ (5:ℕ) * X ^ (4:ℕ) - 48 * u ^ (5:ℕ) * X ^ (3:ℕ) + 72 * u ^ (5:ℕ) * X ^ (2:ℕ) -
    48 * u ^ (5:ℕ) * X + 12 * u ^ (5:ℕ) - 36 * u ^ (4:ℕ) * X ^ (5:ℕ) +
    136 * u ^ (4:ℕ) * X ^ (4:ℕ) - 220 * u ^ (4:ℕ) * X ^ (3:ℕ) + 204 * u ^ (4:ℕ) * X ^ (2:ℕ) -
    112 * u ^ (4:ℕ) * X + 28 * u ^ (4:ℕ) + 36 * u ^ (3:ℕ) * X ^ (6:ℕ) -
    117 * u ^ (3:ℕ) * X ^ (5:ℕ) + 172 * u ^ (3:ℕ) * X ^ (4:ℕ) - 139 * u ^ (3:ℕ) * X ^ (3:ℕ) +
    51 * u ^ (3:ℕ) * X ^ (2:ℕ) - 4 * u ^ (3:ℕ) * X + u ^ (3:ℕ) - 12 * u ^ (2:ℕ) * X ^ (7:ℕ) +
    17 * u ^ (2:ℕ) * X ^ (6:ℕ) + 36 * u ^ (2:ℕ) * X ^ (5:ℕ) - 168 * u ^ (2:ℕ) * X ^ (4:ℕ) +
    278 * u ^ (2:ℕ) * X ^ (3:ℕ) - 256 * u ^ (2:ℕ) * X ^ (2:ℕ) + 140 * u ^ (2:ℕ) * X -
    35 * u ^ (2:ℕ) + 13 * u * X ^ (7:ℕ) - 68 * u * X ^ (6:ℕ) + 171 * u * X ^ (5:ℕ) -
    254 * u * X ^ (4:ℕ) + 247 * u * X ^ (3:ℕ) - 157 * u * X ^ (2:ℕ) + 64 * u * X - 16 * u -
    X ^ (8:ℕ) + 8 * X ^ (7:ℕ) - 20 * X ^ (6:ℕ) + 25 * X ^ (5:ℕ) - 9 * X ^ (4:ℕ) - 21 * X ^ (3:ℕ) +
    35 * X ^ (2:ℕ) - 24 * X + 6) /
      (12 * (X - 1) * coordM X u ^ 3) := by
  have hM := (coordM_pos hX hu).ne'
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have h1X : 1 - X ≠ 0 := by linarith [hX.2]
  have hY : coordY1 X u - 1 = -(1 - X) / coordM X u := by
    unfold coordY1
    field_simp
    unfold coordM
    ring
  unfold formXlc1
  rw [hY]
  unfold formXb2 coordY1
  field_simp
  unfold coordM
  ring

end

end QED.ChainProof.SetCK

end
