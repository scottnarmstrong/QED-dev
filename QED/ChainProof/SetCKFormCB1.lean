/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCFub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-1 `s`-integral of the inner corner

Helper level (no frozen statement). On branch 1 of the threshold coordinates
(`coordPsi1`: `Y = Y(u)`, `y₃ = (Y - u)/s`, `m = w_Y(X) = (Y - u)(1 - Y)`) the integrand of
`cornInSig_ae_eq` is a Laurent polynomial in `s` with coefficients polynomial in `(Y, u)`
(`X` enters only through `Y = Y(u)`, since `J₁ = (1 - Y)²(Y - u)/s²`, `coordJ1_eq`):

**`coordJ1_mul_formCS`**: `J₁ S(Ψ₁(u, s), s) = (1 - Y) p(Y, u, s)/(12 s²)` (`formCF1`), with
`p = a₃ s³ + a₂ s² + a₁ s + a₀`. Its `s`-antiderivative is
`(1 - Y)/12 (a₃ s²/2 + a₂ s + a₁ log s - a₀/s)` (`formCA1`), so

**`integral_formCF1`**: `∫_{(a, b]} formCF1 Y u s ds = A₁(b) - A₁(a)` for `0 < a ≤ b`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- Coefficient `a₃` of `p`. -/
def formCa3 (Y : ℝ) : ℝ := 2 * Y - 2

/-- Coefficient `a₂` of `p`. -/
def formCa2 (Y u : ℝ) : ℝ := 2 * Y ^ 2 + Y * u - 7 * Y - u + 3

/-- Coefficient `a₁` of `p`. -/
def formCa1 (Y u : ℝ) : ℝ := -4 * Y ^ 2 + Y * u + 7 * Y - u

/-- Coefficient `a₀` of `p`. -/
def formCa0 (Y u : ℝ) : ℝ := 3 * (Y - u) * (Y - 1)

/-- **The branch-1 integrand** `(1 - Y) p(Y, u, s)/(12 s²)`. -/
noncomputable def formCF1 (Y u s : ℝ) : ℝ :=
  (1 - Y) * (formCa3 Y * s ^ 3 + formCa2 Y u * s ^ 2 + formCa1 Y u * s + formCa0 Y u) /
    (12 * s ^ 2)

/-- **Its `s`-antiderivative** `A₁`. -/
noncomputable def formCA1 (Y u s : ℝ) : ℝ :=
  (1 - Y) / 12 * (formCa3 Y * s ^ 2 / 2 + formCa2 Y u * s + formCa1 Y u * log s -
    formCa0 Y u / s)

/-- The branch-1 identity, as an identity of rational functions of `(Y, u, s)`. -/
theorem formCF1_eq {Y u s : ℝ} (hs : s ≠ 0) (hYu : Y - u ≠ 0) (hY : 1 - Y ≠ 0) :
    (1 - Y) ^ 2 * (Y - u) / s ^ 2 *
      (formCPrim Y ((Y - u) / s) ((Y - u) * (1 - Y)) s - (1 - s) ^ 2 / 4) =
      formCF1 Y u s := by
  unfold formCPrim formOSP6 formCk1 formCk2 formCk3 formCk4 formCF1 formCa3 formCa2 formCa1
    formCa0
  field_simp
  ring

theorem coordY1_lt_one {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) : coordY1 X u < 1 := by
  have hM := coordM_pos hX hu
  rw [coordY1, div_lt_one hM]
  unfold coordM
  linarith [hX.2]

/-- `J₁ = (1 - Y)²(Y - u)/s²` with `Y = Y(u)`. -/
theorem coordJ1_eq {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (s : ℝ) :
    coordJ1 X u s = (1 - coordY1 X u) ^ 2 * (coordY1 X u - u) / s ^ 2 := by
  have hM := (coordM_pos hX hu).ne'
  unfold coordJ1 coordY1
  field_simp
  unfold coordM
  ring

/-- **The branch-1 integrand in closed form.** -/
theorem coordJ1_mul_formCS {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ coordR1 X) :
    coordJ1 X p.1 p.2 * formCS (coordPsi1 X p).1 (coordPsi1 X p).2 X p.2 =
      formCF1 (coordY1 X p.1) p.1 p.2 := by
  obtain ⟨⟨⟨hY0, hYX⟩, hz0, hzY⟩, ⟨hs0, hs1⟩, hw, hu⟩ := coordPsi1_spec hX hp
  simp only [coordPsi1] at hY0 hYX hz0 hzY hw hu ⊢
  set Y := coordY1 X p.1
  set y3 := (Y - p.1) / p.2
  have hY1 : Y < 1 := hYX.trans hX.2
  have hsx : p.2 ≤ cornInXs Y y3 := by
    rw [cornInXs, le_div_iff₀ (by linarith)]
    have : p.2 * y3 = Y - p.1 := by simp only [y3]; field_simp
    linarith [hp.2.2]
  have hb : p.2 * (1 - y3) ≤ 1 - Y := cornIn_branch1_of_xs hz0 hzY hY1 hsx
  have hm : cornInWX Y X = (Y - p.1) * (1 - Y) := by
    rw [← hw, cornInW0, betaG_of_branch1 hz0 hs1 hb, cornerG_eq]
    simp only [y3]
    field_simp
  rw [coordJ1_eq hX hp.1.1.le, formCS, hm, max_eq_right hsx, cornInPhi_xs _ _ (by linarith),
    add_zero]
  have hYu : 0 < Y - p.1 := by nlinarith
  exact formCF1_eq hs0.ne' hYu.ne' (by linarith)

theorem hasDerivAt_formCA1 (Y u : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (formCA1 Y u) (formCF1 Y u s) s := by
  have h := ((((hasDerivAt_pow 2 s).const_mul (formCa3 Y)).div_const 2).add
    ((hasDerivAt_id' s).const_mul (formCa2 Y u))).add ((hasDerivAt_log hs).const_mul
      (formCa1 Y u)) |>.sub ((hasDerivAt_inv hs).const_mul (formCa0 Y u))
  refine (h.const_mul ((1 - Y) / 12)).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · unfold formCF1
    field_simp
    ring
  · exact Eventually.of_forall fun t => by
      simp only [formCA1, div_eq_mul_inv, Pi.add_apply, Pi.sub_apply]

/-- **The branch-1 `s`-integral** by the fundamental theorem of calculus. -/
theorem integral_formCF1 (Y u : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ s in Ioc a b, formCF1 Y u s = formCA1 Y u b - formCA1 Y u a := by
  have hc : ContinuousOn (formCF1 Y u) (uIcc a b) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have : s ≠ 0 := (ha.trans_le hs.1).ne'
    unfold formCF1
    exact (ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)).continuousWithinAt
  rw [← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_) hc.intervalIntegrable
  rw [uIcc_of_le hab] at hs
  exact hasDerivAt_formCA1 Y u (ha.trans_le hs.1).ne'

end QED.ChainProof.SetCK

end
