/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXB1
public import QED.ChainProof.SetCKFormXSBd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the structure of the branch-2 integrand of `I(X)`

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 24+). On branch 2, with `B = u - X(1 - s)` (`formXLb`), `C = X(1 - s) + (1 - X)u`
(`formXLc`), `D = coordD`, `t = 1 - s`, the coordinates satisfy `Y - y₃ = BC/(sD)`
(**`formX_Y2_sub_Z2`**) and `y₃ = (X - u)(X + u - Xu) t/(sD)`; with the decomposition
`N₂ = t(d² N_a + t d N_b + t² N_c)`, `d = Y - y₃` (`formXN2_eq`) the Jacobian cancels:

**`formXKin2_eq`**: `formXKin2 X u s = (1 - X)/(12 s) (N_a/(s² D) + t N_b/(s B C) +
  t² D N_c/(B² C²))`, the `N`'s evaluated at `(Y, y₃) = Ψ₂(u, s)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `B = u - X(1 - s)`. -/
def formXLb (X u s : ℝ) : ℝ := u - X * (1 - s)

/-- `C = X(1 - s) + (1 - X)u`. -/
def formXLc (X u s : ℝ) : ℝ := X * (1 - s) + (1 - X) * u

section

variable {X u s : ℝ}

theorem formX_Y2_sub_Z2 (hs : s ≠ 0) (hD : coordD X u s ≠ 0) :
    coordY2 X u s - coordZ2 X u s = formXLb X u s * formXLc X u s / (s * coordD X u s) := by
  unfold coordY2 coordZ2 formXLb formXLc
  field_simp
  ring

/-- **The branch-2 integrand, structurally.** -/
theorem formXKin2_eq (hX : X ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (1 - X) 1) (hu : u ∈ Ioo (1 - s) X) :
    formXKin2 X u s = (1 - X) / (12 * s) *
      (formXNa (coordY2 X u s) (coordZ2 X u s) / (s ^ 2 * coordD X u s) +
        (1 - s) * formXNb (coordY2 X u s) (coordZ2 X u s) /
          (s * formXLb X u s * formXLc X u s) +
        (1 - s) ^ 2 * coordD X u s * formXNc (coordY2 X u s) (coordZ2 X u s) s /
          (formXLb X u s ^ 2 * formXLc X u s ^ 2)) := by
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hu0 : 0 < u := by linarith [hs.2, hu.1]
  have hD := coordD_pos hX hu0 hs.2
  have hs0 : 0 < s := by linarith [hs.1, hX.2]
  have h1s : 0 < 1 - s := by linarith [hs.2]
  have hs2 : s - 2 ≠ 0 := by linarith [hs.2]
  have h2s : 2 - s ≠ 0 := by linarith [hs.2]
  have hXu : 0 < X - u := by linarith [hu.2]
  have hA : 0 < X + u - X * u := by nlinarith [hX.2]
  have hB : 0 < formXLb X u s := by unfold formXLb; nlinarith [hu.1]
  have hC : 0 < formXLc X u s := by unfold formXLc; nlinarith
  have hd := formX_Y2_sub_Z2 hs0.ne' hD.ne'
  have hz : coordZ2 X u s = (X - u) * (1 - s) * (X + u - X * u) / (s * coordD X u s) := rfl
  unfold formXKin2 coordPsi2 formXS2 coordJ2
  simp only
  rw [formXN2_eq, hd]
  generalize formXNa (coordY2 X u s) (coordZ2 X u s) = na
  generalize formXNb (coordY2 X u s) (coordZ2 X u s) = nb
  generalize formXNc (coordY2 X u s) (coordZ2 X u s) s = nc
  have hzy : coordZ2 X u s - coordY2 X u s =
      -(formXLb X u s * formXLc X u s / (s * coordD X u s)) := by linarith
  rw [hzy, hz, show u - X * (1 - s) = formXLb X u s from rfl,
    show X * (1 - s) + (1 - X) * u = formXLc X u s from rfl]
  generalize formXLb X u s = b at hB ⊢
  generalize formXLc X u s = c at hC ⊢
  generalize coordD X u s = D at hD ⊢
  field_simp
  ring

end

end QED.ChainProof.SetCK

end
