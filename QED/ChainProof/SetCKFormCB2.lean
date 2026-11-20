/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCB1
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-2 integrand of the inner corner

Helper level (no frozen statement). On the second branch of the threshold, `m = e s²/(1 - s)`
with `e = y₃(Y - y₃)`, the closed form `S` of the `x`-integral (`formCS`) is a small rational
function of `(Y, y₃, s)`:

**`formCS_br2`**: `S = (s - 1) p₂(Y, y₃, s)/(12 s y₃ (Y - y₃)² (s - 2))` (`formCR2`, `p₂` cubic in
`s`, `formCP2`).

With the factorisations of `y₃` and `Y - y₃` on the branch-2 map the Jacobian cancels all but
two linear factors:

**`coordJ2_mul_formCS`**: `J₂ S(Ψ₂(u, s), s) = (1 - X) p₂(Y₂, y₃, s)/(12 B C)`,
`B = u - X(1 - s)`, `C = X(1 - s) + (1 - X)u` (`formCF2`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The cubic `p₂(Y, y₃, s)`** of the branch-2 closed form. -/
def formCP2 (Y y3 s : ℝ) : ℝ :=
  (Y ^ 2 * y3 - 2 * Y ^ 2 - 4 * Y * y3 ^ 2 + 10 * Y * y3 - 4 * Y + 3 * y3 ^ 3 - 2 * y3 ^ 2 -
      8 * y3 + 6) * s ^ 3 +
    (-3 * Y ^ 3 + 11 * Y ^ 2 * y3 - 7 * Y * y3 ^ 2 - 31 * Y * y3 + 27 * Y + 3 * y3 ^ 3 +
      y3 ^ 2 + 17 * y3 - 18) * s ^ 2 -
    3 * (-Y ^ 3 + 6 * Y ^ 2 * y3 - 5 * Y ^ 2 - 4 * Y * y3 ^ 2 - 10 * Y * y3 + 16 * Y +
      2 * y3 ^ 3 + 2 * y3 - 6) * s +
    (3 * Y ^ 3 + 2 * Y ^ 2 * y3 - 17 * Y ^ 2 - 4 * Y * y3 + 26 * Y - 4 * y3 - 6)

/-- The branch-2 closed form `S = (s - 1) p₂/(12 s y₃ (Y - y₃)² (s - 2))`. -/
noncomputable def formCR2 (Y y3 s : ℝ) : ℝ :=
  (s - 1) * formCP2 Y y3 s / (12 * s * y3 * (Y - y3) ^ 2 * (s - 2))

/-- The identity behind `formCS_br2`, in the variables `(Y, y₃, s)`. -/
theorem formCR2_eq {Y y3 s : ℝ} (hs : s ≠ 0) (h3 : y3 ≠ 0) (h34 : Y - y3 ≠ 0) (hs1 : 1 - s ≠ 0)
    (hs2 : s - 2 ≠ 0) :
    formCPrim Y y3 (y3 * (Y - y3) * s ^ 2 / (1 - s)) s - (1 - s) ^ 2 / 4 + cornInPhi Y y3 s =
      formCR2 Y y3 s := by
  have h34' : y3 - Y ≠ 0 := fun h => h34 (by linarith)
  unfold formCPrim formOSP6 formCk1 formCk2 formCk3 formCk4 cornInPhi cornInPl formCR2 formCP2
  simp only [hpoly]
  field_simp
  ring

/-- **The branch-2 closed form of the `x`-integral.** -/
theorem formCS_br2 {Y y3 X s : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hb : 1 - Y ≤ s * (1 - y3))
    (hm : cornInW0 Y y3 s = cornInWX Y X) : formCS Y y3 X s = formCR2 Y y3 s := by
  have hsx : cornInXs Y y3 ≤ s := by
    rw [cornInXs, div_le_iff₀ (by linarith)]
    linarith
  rw [formCS, max_eq_left hsx, ← hm, cornInW0_of_branch2 h3 hs.2 hb]
  exact formCR2_eq hs.1.ne' h3.ne' (by linarith) (by linarith [hs.2]) (by linarith [hs.2])

/-- **The branch-2 integrand** `(1 - X) p₂(Y₂, y₃, s)/(12 B C)`. -/
noncomputable def formCF2 (X u s : ℝ) : ℝ :=
  (1 - X) * formCP2 (coordY2 X u s) (coordZ2 X u s) s /
    (12 * (u - X * (1 - s)) * (X * (1 - s) + (1 - X) * u))

/-- **The branch-2 integrand in closed form.** -/
theorem coordJ2_mul_formCS {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR2 X) :
    coordJ2 X p.1 p.2 * formCS (coordPsi2 X p).1 (coordPsi2 X p).2 X p.2 =
      formCF2 X p.1 p.2 := by
  obtain ⟨⟨⟨hY0, hYX⟩, hz0, hzY⟩, hs, hw, hu⟩ := coordPsi2_spec hX hp
  obtain ⟨u, s⟩ := p
  obtain ⟨⟨hu0, huX⟩, hsl, hs1⟩ := hp
  simp only [coordPsi2] at hY0 hYX hz0 hzY hw hu hs hsl hu0 huX hs1 ⊢
  have hb : 1 - coordY2 X u s ≤ s * (1 - coordZ2 X u s) := by nlinarith
  rw [formCS_br2 hz0 hzY (hYX.trans hX.2) hs hb hw, formCR2]
  have hX0 := hX.1
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hD := coordD_pos hX hu0 hs1
  have hs0 : 0 < s := hs.1
  have hXu : 0 < X - u := by linarith
  have hA : 0 < X + u - X * u := by nlinarith
  have hB : 0 < u - X * (1 - s) := by nlinarith
  have hC : 0 < X * (1 - s) + (1 - X) * u := by positivity
  have hZ : coordZ2 X u s = (X - u) * (1 - s) * (X + u - X * u) / (s * coordD X u s) := rfl
  have hYZ : coordY2 X u s - coordZ2 X u s =
      (u - X * (1 - s)) * (X * (1 - s) + (1 - X) * u) / (s * coordD X u s) := by
    unfold coordY2 coordZ2; field_simp; ring
  set W := formCP2 (coordY2 X u s) (coordZ2 X u s) s
  rw [hYZ, hZ]
  unfold formCF2 coordJ2
  have : s - 2 ≠ 0 := by linarith
  have : 1 - s ≠ 0 := by linarith
  field_simp
  ring

end QED.ChainProof.SetCK

end
