/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12Def
public import QED.DimReg.CpowHolder

/-!
# Set (d), master `I₁₂`: pointwise bounds on `Φ₀` and `Φ₁`

For `w = 2 - 3ε` with `‖ε‖ < 1/100` and `X, Y ∈ (0, 1]`, write
`E(X, Y) = (X + Y) ^ w - X ^ w - Y ^ w` (`QED.ThreeLoopD.i12E`), so that `Φ₀ = E / (X Y)`.
Each of `E`, `E - w X Y ^ (w - 1)`, the differences `E(X, Y₁) - E(X, Y₂)` and the numerator of
`Φ₁` is `w ∫ (…)` over an interval of length `X`, `Y₁ - Y₂` or `X Y`
(`QED.ThreeLoopD.i12_cpow_sub_eq`, `QED.ThreeLoopD.i12_cpow_shift_sub_eq`), with an integrand
controlled by the Hölder bound `QED.DimReg.norm_cpow_sub_cpow_le_sqrt`. This gives

* `‖Φ₀‖ ≤ 24 / √X`, `‖Φ₀‖ ≤ 24 / √Y`;
* `‖Φ₀ - w Y ^ (-3ε)‖ ≤ 27 √X / Y` and the mirror bound;
* for `Y₂ ≤ Y₁`: `‖Φ₀(X, Y₁) - Φ₀(X, Y₂)‖ ≤ 24 √(Y₁ - Y₂) / Y₁ + 24 (Y₁ - Y₂) / (Y₁ √Y₂)` and
  `≤ 48 (Y₁ - Y₂) / (Y₁ √X)`;
* `‖Φ₁‖ ≤ 27 √X`, `‖Φ₁‖ ≤ 27 √Y`.

These are the inputs of the dominating bounds of `QED.ThreeLoopD.SetDMastersI12RestAnalytic`.
-/

@[expose] public section

open Complex Set QED.DimReg MeasureTheory

namespace QED.ThreeLoopD

/-! ### Integral forms of differences of powers -/

/-- `p ^ w - q ^ w - w (p - q) c = w ∫_q^p (t ^ (w - 1) - c)`. -/
theorem i12_cpow_sub_eq (p q : ℝ) {w : ℂ} (hw : 0 < (w - 1).re) (c : ℂ) :
    (p : ℂ) ^ w - (q : ℂ) ^ w - w * ((p - q : ℝ) : ℂ) * c =
      w * ∫ t in q..p, ((t : ℂ) ^ (w - 1) - c) := by
  have hint := integral_cpow (a := q) (b := p) (r := w - 1) (Or.inl (by linarith))
  rw [sub_add_cancel] at hint
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
  have hc : Continuous fun t : ℝ => (t : ℂ) ^ (w - 1) := continuous_ofReal_cpow_const hw
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const, hint,
    intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  field_simp

/-- The shifted form: `((p + s) ^ w - (q + s) ^ w) - (p ^ w - q ^ w - w (p - q) c)`
`= w ∫_q^p ((t + s) ^ (w - 1) - (t ^ (w - 1) - c))`. -/
theorem i12_cpow_shift_sub_eq (p q s : ℝ) {w : ℂ} (hw : 0 < (w - 1).re) (c : ℂ) :
    (((p + s : ℝ) : ℂ) ^ w - ((q + s : ℝ) : ℂ) ^ w) -
        ((p : ℂ) ^ w - (q : ℂ) ^ w - w * ((p - q : ℝ) : ℂ) * c) =
      w * ∫ t in q..p, (((t + s : ℝ) : ℂ) ^ (w - 1) - ((t : ℂ) ^ (w - 1) - c)) := by
  have hc : Continuous fun t : ℝ => (t : ℂ) ^ (w - 1) := continuous_ofReal_cpow_const hw
  have hA : IntervalIntegrable (fun t : ℝ => ((t + s : ℝ) : ℂ) ^ (w - 1)) volume q p :=
    (hc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (w - 1) - c) volume q p :=
    (hc.sub continuous_const).intervalIntegrable _ _
  have hs : ∫ t in q..p, ((t + s : ℝ) : ℂ) ^ (w - 1) =
      ∫ t in q + s..p + s, ((t : ℝ) : ℂ) ^ (w - 1) :=
    intervalIntegral.integral_comp_add_right (fun t : ℝ => (t : ℂ) ^ (w - 1)) s
  have h1 := i12_cpow_sub_eq (p + s) (q + s) hw 0
  rw [intervalIntegral.integral_sub hA hB, mul_sub, hs, ← i12_cpow_sub_eq p q hw c]
  have h1' : w * ∫ t in q + s..p + s, ((t : ℝ) : ℂ) ^ (w - 1) =
      ((p + s : ℝ) : ℂ) ^ w - ((q + s : ℝ) : ℂ) ^ w := by
    rw [← sub_zero (w * _), ← mul_zero (w * ((p + s - (q + s) : ℝ) : ℂ))] at *
    simpa using h1.symm
  rw [h1']

/-- Norm bound from the integral form. -/
theorem i12_norm_int_le {q p M : ℝ} (hqp : q ≤ p) {f : ℝ → ℂ} (hM : ∀ t ∈ Ioc q p, ‖f t‖ ≤ M)
    (w : ℂ) : ‖w * ∫ t in q..p, f t‖ ≤ ‖w‖ * ((p - q) * M) := by
  rw [norm_mul]
  gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := q) (b := p) (f := f) (C := M)
    (by rwa [uIoc_of_le hqp])
  rwa [abs_of_nonneg (by linarith), mul_comm] at this


/-! ### The symmetric second difference `E(X, Y) = (X + Y) ^ w - X ^ w - Y ^ w` -/

/-- `E(X, Y) = (X + Y) ^ w - X ^ w - Y ^ w`, so that `Φ₀ = E / (X Y)` for `w = 2 - 3ε`. -/
noncomputable def i12E (w : ℂ) (X Y : ℝ) : ℂ :=
  ((X + Y : ℝ) : ℂ) ^ w - (X : ℂ) ^ w - (Y : ℂ) ^ w

theorem i12Phi0_eq (ε : ℂ) (X Y : ℝ) :
    i12Phi0 ε X Y = i12E (2 - 3 * ε) X Y / ((X * Y : ℝ) : ℂ) := rfl

theorem i12E_comm (w : ℂ) (X Y : ℝ) : i12E w X Y = i12E w Y X := by
  unfold i12E; rw [add_comm X Y]; ring

section E

variable {w : ℂ} (hz1 : 1 / 2 ≤ (w - 1).re) (hz2 : (w - 1).re ≤ 3 / 2)
include hz1 hz2

theorem i12_w_ne_zero : w ≠ 0 := by rintro rfl; norm_num at hz1

/-- `‖E(X, Y)‖ ≤ ‖w‖ X · 4 ‖w - 1‖ √Y`. -/
theorem norm_i12E_le {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : X + Y ≤ 2) :
    ‖i12E w X Y‖ ≤ ‖w‖ * (X * (4 * ‖w - 1‖ * √Y)) := by
  have hw : 0 < (w - 1).re := by linarith
  have h := i12_cpow_shift_sub_eq X 0 Y hw 0
  have e : i12E w X Y = (((X + Y : ℝ) : ℂ) ^ w - ((0 + Y : ℝ) : ℂ) ^ w) -
      ((X : ℂ) ^ w - ((0 : ℝ) : ℂ) ^ w - w * ((X - 0 : ℝ) : ℂ) * 0) := by
    rw [ofReal_zero, zero_cpow (i12_w_ne_zero hz1 hz2), zero_add, i12E]; ring
  rw [e, h]
  refine (i12_norm_int_le (M := 4 * ‖w - 1‖ * √Y) hX (fun t ht => ?_) w).trans_eq
    (by rw [sub_zero])
  rw [sub_zero]
  have := norm_cpow_sub_cpow_le_sqrt (p := t + Y) (q := t) (by linarith [ht.1]) ht.1.le
    (by linarith [ht.2]) (by linarith [ht.2]) hz1 hz2
  rwa [show t + Y - t = Y by ring, abs_of_nonneg hY] at this

/-- `‖E(X, Y) - w X Y ^ (w - 1)‖ ≤ ‖w‖ X (4 ‖w - 1‖ + 1) √X`. -/
theorem norm_i12E_sub_le {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hX1 : X ≤ 1) (hXY : X + Y ≤ 2) :
    ‖i12E w X Y - w * X * (Y : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * (X * ((4 * ‖w - 1‖ + 1) * √X)) := by
  have hw : 0 < (w - 1).re := by linarith
  have h := i12_cpow_shift_sub_eq X 0 Y hw (-(Y : ℂ) ^ (w - 1))
  have e : i12E w X Y - w * X * (Y : ℂ) ^ (w - 1) =
      (((X + Y : ℝ) : ℂ) ^ w - ((0 + Y : ℝ) : ℂ) ^ w) -
      ((X : ℂ) ^ w - ((0 : ℝ) : ℂ) ^ w - w * ((X - 0 : ℝ) : ℂ) * (-(Y : ℂ) ^ (w - 1))) := by
    rw [ofReal_zero, zero_cpow (i12_w_ne_zero hz1 hz2), zero_add, i12E]; push_cast; ring_nf
  rw [e, h]
  refine (i12_norm_int_le (M := (4 * ‖w - 1‖ + 1) * √X) hX (fun t ht => ?_) w).trans_eq
    (by rw [sub_zero])
  · have h1 := norm_cpow_sub_cpow_le_sqrt (p := t + Y) (q := Y) (by linarith [ht.1]) hY
      (by linarith [ht.2]) (by linarith [ht.2]) hz1 hz2
    rw [show t + Y - Y = t by ring, abs_of_nonneg ht.1.le] at h1
    have h2 := norm_cpow_le_sqrt ht.1.le (ht.2.trans hX1) hz1
    have hs : √t ≤ √X := Real.sqrt_le_sqrt ht.2
    have hK : 0 ≤ 4 * ‖w - 1‖ := by positivity
    calc _ = ‖(((t + Y : ℝ) : ℂ) ^ (w - 1) - (Y : ℂ) ^ (w - 1)) - (t : ℂ) ^ (w - 1)‖ := by
          congr 1; ring
      _ ≤ 4 * ‖w - 1‖ * √t + √t := (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ ≤ 4 * ‖w - 1‖ * √X + √X := by gcongr
      _ = _ := by ring

/-- `‖E(X, Y₁) - E(X, Y₂)‖ ≤ ‖w‖ X · 4 ‖w - 1‖ √(Y₁ - Y₂)` for `Y₂ ≤ Y₁`. -/
theorem norm_i12E_sub_right_le {X Y₁ Y₂ : ℝ} (hX : 0 ≤ X) (hY₂ : 0 ≤ Y₂) (hY : Y₂ ≤ Y₁)
    (hXY : X + Y₁ ≤ 2) :
    ‖i12E w X Y₁ - i12E w X Y₂‖ ≤ ‖w‖ * (X * (4 * ‖w - 1‖ * √(Y₁ - Y₂))) := by
  have hw : 0 < (w - 1).re := by linarith
  have h := i12_cpow_shift_sub_eq (X + Y₂) Y₂ (Y₁ - Y₂) hw 0
  have e : i12E w X Y₁ - i12E w X Y₂ =
      (((X + Y₂ + (Y₁ - Y₂) : ℝ) : ℂ) ^ w - ((Y₂ + (Y₁ - Y₂) : ℝ) : ℂ) ^ w) -
      (((X + Y₂ : ℝ) : ℂ) ^ w - (Y₂ : ℂ) ^ w - w * ((X + Y₂ - Y₂ : ℝ) : ℂ) * 0) := by
    rw [show X + Y₂ + (Y₁ - Y₂) = X + Y₁ by ring, show Y₂ + (Y₁ - Y₂) = Y₁ by ring, i12E,
      i12E]
    ring
  rw [e, h]
  refine (i12_norm_int_le (M := 4 * ‖w - 1‖ * √(Y₁ - Y₂)) (by linarith : Y₂ ≤ X + Y₂)
    (fun t ht => ?_) w).trans_eq (by rw [show X + Y₂ - Y₂ = X by ring])
  rw [sub_zero]
  have := norm_cpow_sub_cpow_le_sqrt (p := t + (Y₁ - Y₂)) (q := t) (by linarith [ht.1])
    (by linarith [ht.1]) (by linarith [ht.2]) (by linarith [ht.2]) hz1 hz2
  rwa [show t + (Y₁ - Y₂) - t = Y₁ - Y₂ by ring, abs_of_nonneg (by linarith)] at this

/-- `‖E(X, Y₁) - E(X, Y₂)‖ ≤ ‖w‖ (Y₁ - Y₂) · 4 ‖w - 1‖ √X` for `Y₂ ≤ Y₁`. -/
theorem norm_i12E_sub_right_le' {X Y₁ Y₂ : ℝ} (hX : 0 ≤ X) (hY₂ : 0 ≤ Y₂) (hY : Y₂ ≤ Y₁)
    (hXY : X + Y₁ ≤ 2) :
    ‖i12E w X Y₁ - i12E w X Y₂‖ ≤ ‖w‖ * ((Y₁ - Y₂) * (4 * ‖w - 1‖ * √X)) := by
  have hw : 0 < (w - 1).re := by linarith
  have h := i12_cpow_shift_sub_eq Y₁ Y₂ X hw 0
  have e : i12E w X Y₁ - i12E w X Y₂ =
      (((Y₁ + X : ℝ) : ℂ) ^ w - ((Y₂ + X : ℝ) : ℂ) ^ w) -
      ((Y₁ : ℂ) ^ w - (Y₂ : ℂ) ^ w - w * ((Y₁ - Y₂ : ℝ) : ℂ) * 0) := by
    rw [add_comm Y₁ X, add_comm Y₂ X, i12E, i12E]; ring
  rw [e, h]
  refine i12_norm_int_le hY (fun t ht => ?_) w
  rw [sub_zero]
  have := norm_cpow_sub_cpow_le_sqrt (p := t + X) (q := t) (by linarith [ht.1])
    (by linarith [ht.1]) (by linarith [ht.2]) (by linarith [ht.2]) hz1 hz2
  rwa [show t + X - t = X by ring, abs_of_nonneg hX] at this

end E

/-! ### Bounds on `Φ₀` and `Φ₁` for `‖ε‖ < 1/100` -/

theorem i12_norm_ofReal_mul {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    ‖((X * Y : ℝ) : ℂ)‖ = X * Y := by
  rw [norm_real, Real.norm_of_nonneg (by positivity)]

section Phi

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100)
include hε

theorem i12_eps_facts :
    |ε.re| ≤ 1 / 100 ∧ 1 / 2 ≤ (2 - 3 * ε - 1).re ∧ (2 - 3 * ε - 1).re ≤ 3 / 2 ∧
      ‖2 - 3 * ε‖ ≤ 3 ∧ ‖2 - 3 * ε - 1‖ ≤ 2 := by
  have hr : |ε.re| ≤ 1 / 100 := (abs_re_le_norm ε).trans hε.le
  have hr' := abs_le.mp hr
  have hre : (2 - 3 * ε - 1).re = 1 - 3 * ε.re := by simp; ring
  have h3 : ‖3 * ε‖ ≤ 3 / 100 := by rw [norm_mul]; norm_num; linarith
  refine ⟨hr, by rw [hre]; linarith, by rw [hre]; linarith, ?_, ?_⟩
  · calc ‖2 - 3 * ε‖ ≤ ‖(2 : ℂ)‖ + ‖3 * ε‖ := norm_sub_le _ _
      _ ≤ 3 := by norm_num; linarith
  · calc ‖2 - 3 * ε - 1‖ = ‖(1 : ℂ) - 3 * ε‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖3 * ε‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num; linarith

variable {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hX1 : X ≤ 1) (hY1 : Y ≤ 1)
include hX hY hX1 hY1

/-- `‖Φ₀(X, Y)‖ ≤ 24 / √X`. -/
theorem norm_i12Phi0_le_left : ‖i12Phi0 ε X Y‖ ≤ 24 / √X := by
  obtain ⟨-, h1, h2, hw, hw1⟩ := i12_eps_facts hε
  have hE := norm_i12E_le h1 h2 hY.le hX.le (by linarith)
  have hsX := Real.sqrt_pos.mpr hX
  rw [i12Phi0_eq, i12E_comm, norm_div, i12_norm_ofReal_mul hX hY, div_le_iff₀ (by positivity)]
  calc _ ≤ ‖2 - 3 * ε‖ * (Y * (4 * ‖2 - 3 * ε - 1‖ * √X)) := hE
    _ ≤ 3 * (Y * (4 * 2 * √X)) := by gcongr
    _ = 24 / √X * (X * Y) := by
        field_simp
        rw [Real.sq_sqrt hX.le]; ring

/-- `‖Φ₀(X, Y)‖ ≤ 24 / √Y`. -/
theorem norm_i12Phi0_le_right : ‖i12Phi0 ε X Y‖ ≤ 24 / √Y := by
  have := norm_i12Phi0_le_left hε hY hX hY1 hX1
  rwa [i12Phi0_eq, i12E_comm, mul_comm Y X, ← i12Phi0_eq] at this

/-- `‖Φ₀(X, Y) - (2 - 3ε) Y ^ (-3ε)‖ ≤ 27 √X / Y`. -/
theorem norm_i12Phi0_sub_le :
    ‖i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)‖ ≤ 27 * √X / Y := by
  obtain ⟨-, h1, h2, hw, hw1⟩ := i12_eps_facts hε
  have hE := norm_i12E_sub_le h1 h2 hX.le hY.le hX1 (by linarith)
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hc : (Y : ℂ) ^ (2 - 3 * ε - 1) = (Y : ℂ) ^ (-3 * ε) * Y := by
    rw [show (2 - 3 * ε - 1 : ℂ) = -3 * ε + 1 by ring, cpow_add _ _ hY0, cpow_one]
  have e : i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε) =
      (i12E (2 - 3 * ε) X Y - (2 - 3 * ε) * X * (Y : ℂ) ^ (2 - 3 * ε - 1)) /
        ((X * Y : ℝ) : ℂ) := by
    rw [i12Phi0_eq, hc]; push_cast; field_simp
  rw [e, norm_div, i12_norm_ofReal_mul hX hY, div_le_iff₀ (by positivity)]
  calc _ ≤ ‖2 - 3 * ε‖ * (X * ((4 * ‖2 - 3 * ε - 1‖ + 1) * √X)) := hE
    _ ≤ 3 * (X * ((4 * 2 + 1) * √X)) := by gcongr
    _ = 27 * √X / Y * (X * Y) := by field_simp; ring

/-- `‖Φ₀(X, Y) - (2 - 3ε) X ^ (-3ε)‖ ≤ 27 √Y / X`. -/
theorem norm_i12Phi0_sub_le' :
    ‖i12Phi0 ε X Y - (2 - 3 * ε) * (X : ℂ) ^ (-3 * ε)‖ ≤ 27 * √Y / X := by
  have := norm_i12Phi0_sub_le hε hY hX hY1 hX1
  rwa [i12Phi0_eq, i12E_comm, mul_comm Y X, ← i12Phi0_eq] at this

end Phi

section PhiDiff

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100)
  {X Y₁ Y₂ : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) (hY₂ : 0 < Y₂) (hY : Y₂ ≤ Y₁) (hY₁ : Y₁ ≤ 1)
include hε hX hX1 hY₂ hY hY₁

omit hε hX1 hY₁ in
theorem i12Phi0_sub_eq : i12Phi0 ε X Y₁ - i12Phi0 ε X Y₂ =
    (i12E (2 - 3 * ε) X Y₁ - i12E (2 - 3 * ε) X Y₂) / ((X * Y₁ : ℝ) : ℂ) +
      i12Phi0 ε X Y₂ * (((Y₂ - Y₁) / Y₁ : ℝ) : ℂ) := by
  have h1 : (Y₁ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have h2 : (Y₂ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY₂.ne'
  have h3 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  rw [i12Phi0_eq, i12Phi0_eq]; push_cast; field_simp; ring

/-- The difference in `Y` through the `X`-integral:
`‖Φ₀(X, Y₁) - Φ₀(X, Y₂)‖ ≤ 24 √(Y₁ - Y₂) / Y₁ + 24 (Y₁ - Y₂) / (Y₁ √Y₂)`. -/
theorem norm_i12Phi0_sub_right_le :
    ‖i12Phi0 ε X Y₁ - i12Phi0 ε X Y₂‖ ≤
      24 * √(Y₁ - Y₂) / Y₁ + 24 * (Y₁ - Y₂) / (Y₁ * √Y₂) := by
  obtain ⟨-, h1, h2, hw, hw1⟩ := i12_eps_facts hε
  have hY₁0 : 0 < Y₁ := by linarith
  have hE := norm_i12E_sub_right_le h1 h2 hX.le hY₂.le hY (by linarith)
  have hP := norm_i12Phi0_le_right hε hX hY₂ hX1 (by linarith)
  have hsY := Real.sqrt_pos.mpr hY₂
  rw [i12Phi0_sub_eq hX hY₂ hY]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, i12_norm_ofReal_mul hX hY₁0, div_le_iff₀ (by positivity)]
    calc _ ≤ ‖2 - 3 * ε‖ * (X * (4 * ‖2 - 3 * ε - 1‖ * √(Y₁ - Y₂))) := hE
      _ ≤ 3 * (X * (4 * 2 * √(Y₁ - Y₂))) := by gcongr
      _ = _ := by field_simp; ring
  · rw [norm_mul, norm_real, Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hY₁0.le)]
    have hq : 0 ≤ -((Y₂ - Y₁) / Y₁) := by
      rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hY₁0.le
    calc _ ≤ 24 / √Y₂ * (-((Y₂ - Y₁) / Y₁)) := by gcongr
      _ = _ := by field_simp; ring

/-- The difference in `Y` through the `Y`-integral:
`‖Φ₀(X, Y₁) - Φ₀(X, Y₂)‖ ≤ 48 (Y₁ - Y₂) / (Y₁ √X)`. -/
theorem norm_i12Phi0_sub_right_le' :
    ‖i12Phi0 ε X Y₁ - i12Phi0 ε X Y₂‖ ≤ 48 * (Y₁ - Y₂) / (Y₁ * √X) := by
  obtain ⟨-, h1, h2, hw, hw1⟩ := i12_eps_facts hε
  have hY₁0 : 0 < Y₁ := by linarith
  have hE := norm_i12E_sub_right_le' h1 h2 hX.le hY₂.le hY (by linarith)
  have hP := norm_i12Phi0_le_left hε hX hY₂ hX1 (by linarith)
  have hsX := Real.sqrt_pos.mpr hX
  rw [i12Phi0_sub_eq hX hY₂ hY]
  refine (norm_add_le _ _).trans ?_
  have hd : 0 ≤ Y₁ - Y₂ := by linarith
  have hX' := Real.sq_sqrt hX.le
  calc _ ≤ 24 * (Y₁ - Y₂) / (Y₁ * √X) + 24 * (Y₁ - Y₂) / (Y₁ * √X) := by
        refine add_le_add ?_ ?_
        · rw [norm_div, i12_norm_ofReal_mul hX hY₁0, div_le_iff₀ (by positivity)]
          calc _ ≤ ‖2 - 3 * ε‖ * ((Y₁ - Y₂) * (4 * ‖2 - 3 * ε - 1‖ * √X)) := hE
            _ ≤ 3 * ((Y₁ - Y₂) * (4 * 2 * √X)) := by gcongr
            _ = _ := by field_simp; rw [hX']; ring
        · rw [norm_mul, norm_real, Real.norm_of_nonpos
            (div_nonpos_of_nonpos_of_nonneg (by linarith) hY₁0.le)]
          have hq : 0 ≤ -((Y₂ - Y₁) / Y₁) := by
            rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hY₁0.le
          calc _ ≤ 24 / √X * (-((Y₂ - Y₁) / Y₁)) := by gcongr
            _ = _ := by field_simp; ring
    _ = _ := by ring

end PhiDiff

theorem i12Phi1_comm (ε : ℂ) (X Y : ℝ) : i12Phi1 ε X Y = i12Phi1 ε Y X := by
  unfold i12Phi1
  rw [show Y + X - Y * X = X + Y - X * Y by ring, add_comm Y X, mul_comm Y X]; ring

section Phi1

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100)
  {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hX1 : X ≤ 1) (hY1 : Y ≤ 1)
include hε hX hY hX1 hY1

/-- `‖Φ₁(X, Y)‖ ≤ 27 √Y`. -/
theorem norm_i12Phi1_le_right : ‖i12Phi1 ε X Y‖ ≤ 27 * √Y := by
  obtain ⟨-, h1, h2, hw, hw1⟩ := i12_eps_facts hε
  set w : ℂ := 2 - 3 * ε with hwdef
  set N : ℝ := X + Y - X * Y with hN
  have hN0 : 0 ≤ N := by nlinarith
  have hNp : N ≤ X + Y := by nlinarith
  have key := i12_cpow_sub_eq (X + Y) N (w := w) (by linarith)
    ((X : ℂ) ^ (w - 1) + (Y : ℂ) ^ (w - 1))
  have hXY0 : ((X * Y : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have e : i12Phi1 ε X Y = -(((X + Y : ℝ) : ℂ) ^ w - (N : ℂ) ^ w -
      w * ((X + Y - N : ℝ) : ℂ) * ((X : ℂ) ^ (w - 1) + (Y : ℂ) ^ (w - 1))) /
        ((X * Y : ℝ) : ℂ) := by
    have hs : (1 : ℂ) - 3 * ε = w - 1 := by rw [hwdef]; ring
    rw [i12Phi1, hs, show X + Y - N = X * Y by rw [hN]; ring]
    field_simp
    ring
  rw [e, key, norm_div, norm_neg, i12_norm_ofReal_mul hX hY, div_le_iff₀ (by positivity)]
  refine (i12_norm_int_le (M := (4 * ‖w - 1‖ + 1) * √Y) hNp (fun t ht => ?_) w).trans ?_
  · have ht0 : 0 ≤ t := hN0.trans ht.1.le
    have hd : |t - X| ≤ Y := by
      rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
    have hH := norm_cpow_sub_cpow_le_sqrt ht0 hX.le (by linarith [ht.2]) (by linarith) h1 h2
    have hYs := norm_cpow_le_sqrt hY.le hY1 h1
    calc _ = ‖((t : ℂ) ^ (w - 1) - (X : ℂ) ^ (w - 1)) - (Y : ℂ) ^ (w - 1)‖ := by
          congr 1; ring
      _ ≤ 4 * ‖w - 1‖ * √|t - X| + √Y := (norm_sub_le _ _).trans (add_le_add hH hYs)
      _ ≤ 4 * ‖w - 1‖ * √Y + √Y := by gcongr
      _ = _ := by ring
  · rw [show X + Y - N = X * Y by rw [hN]; ring]
    calc ‖w‖ * (X * Y * ((4 * ‖w - 1‖ + 1) * √Y)) ≤ 3 * (X * Y * ((4 * 2 + 1) * √Y)) := by
          gcongr
      _ = 27 * √Y * (X * Y) := by ring

/-- `‖Φ₁(X, Y)‖ ≤ 27 √X`. -/
theorem norm_i12Phi1_le_left : ‖i12Phi1 ε X Y‖ ≤ 27 * √X := by
  rw [i12Phi1_comm]; exact norm_i12Phi1_le_right hε hY hX hY1 hX1

end Phi1

end QED.ThreeLoopD
