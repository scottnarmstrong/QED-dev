/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Def
public import QED.DimReg.CpowHolder

/-!
# Set (d), master `I₉`: pointwise bounds on the subtracted integrands

For `x, w, y ∈ [0, 1]` and `s = 1 - 3ε` with `1/2 ≤ re s ≤ 3/2`, put `c = x(1 - x)` and
`K = 4 ‖s‖`. The Hölder bound `QED.DimReg.norm_cpow_sub_cpow_le_sqrt` gives

* `‖Ψ‖ ≤ (K + 1) √c` and `‖Ψ‖ ≤ (2K + 1) √w` (`QED.ThreeLoopD.norm_i9Psi_le_c`,
  `QED.ThreeLoopD.norm_i9Psi_le_w`);
* `‖Ψ_sub‖ ≤ M √t` for each of `t = c, w, y, 1 - y`, with `M = 3 (2K + 1)`, hence
  `‖Ψ_sub‖ ≤ M (c w y (1 - y)) ^ (1/8)` (`QED.ThreeLoopD.norm_i9PsiSub_le`), and
  `‖Ψ|_{y=1}‖ ≤ (2K + 1) (c w) ^ (1/4)` (`QED.ThreeLoopD.norm_i9Psi_one_le`).

These are the dominating bounds that make `QED.ThreeLoopD.i9K` and `QED.ThreeLoopD.i9Rem`
analytic near `ε = 0`.
-/

@[expose] public section

open Complex Set QED.DimReg

namespace QED.ThreeLoopD

variable {ε : ℂ} {x w y : ℝ}

theorem i9_c_nonneg (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ x * (1 - x) :=
  mul_nonneg hx.1 (by linarith [hx.2])

theorem i9_c_le (x : ℝ) : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]

theorem i9_mul_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

theorem i9Poly_nonneg (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ i9Poly x w y :=
  add_nonneg (mul_nonneg (i9_c_nonneg hx) (sq_nonneg _)) (mul_nonneg hw.1 hy.1)

theorem i9Poly_le (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    i9Poly x w y ≤ 2 := by
  have h1 : (1 - w) ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
  have h2 : x * (1 - x) * (1 - w) ^ 2 ≤ 1 / 4 :=
    (mul_le_of_le_one_right (i9_c_nonneg hx) h1).trans (i9_c_le x)
  have h3 : w * y ≤ 1 := i9_mul_le_one hw.2 hy.1 hy.2
  unfold i9Poly; linarith

/-- The Hölder bound with `K = 4 ‖s‖`. -/
theorem i9_holder {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hp : p ≤ 2) (hq : q ≤ 2)
    (h1 : 1 / 2 ≤ (1 - 3 * ε).re) (h2 : (1 - 3 * ε).re ≤ 3 / 2) :
    ‖(p : ℂ) ^ (1 - 3 * ε) - (q : ℂ) ^ (1 - 3 * ε)‖ ≤ 4 * ‖1 - 3 * ε‖ * √|p - q| :=
  norm_cpow_sub_cpow_le_sqrt hp0 hq0 hp hq h1 h2

theorem sqrt_le_sqrt_of_abs_le {a b : ℝ} (h : |a| ≤ b) : √|a| ≤ √b := Real.sqrt_le_sqrt h

section Bounds

variable (h1 : 1 / 2 ≤ (1 - 3 * ε).re) (h2 : (1 - 3 * ε).re ≤ 3 / 2)
  (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
include h1 h2 hx hw hy

theorem norm_i9Psi_le_c : ‖i9Psi ε x w y‖ ≤ (4 * ‖1 - 3 * ε‖ + 1) * √(x * (1 - x)) := by
  have hc0 := i9_c_nonneg hx
  have hc1 : x * (1 - x) ≤ 1 := (i9_c_le x).trans (by norm_num)
  have hwy0 : 0 ≤ w * y := mul_nonneg hw.1 hy.1
  have hwy1 : w * y ≤ 1 := i9_mul_le_one hw.2 hy.1 hy.2
  have hH := i9_holder (i9Poly_nonneg hx hw hy) hwy0 (i9Poly_le hx hw hy) (by linarith) h1 h2
  have hd : |i9Poly x w y - w * y| ≤ x * (1 - x) := by
    have e : i9Poly x w y - w * y = x * (1 - x) * (1 - w) ^ 2 := by unfold i9Poly; ring
    have h1w : (1 - w) ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
    rw [e, abs_of_nonneg (mul_nonneg hc0 (sq_nonneg _))]
    exact mul_le_of_le_one_right hc0 h1w
  have hcs := norm_cpow_le_sqrt hc0 hc1 h1
  have hK : 0 ≤ 4 * ‖1 - 3 * ε‖ := by positivity
  calc ‖i9Psi ε x w y‖ ≤ ‖((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) - ((w * y : ℝ) : ℂ) ^ (1 - 3 * ε)‖
        + ‖((x * (1 - x) : ℝ) : ℂ) ^ (1 - 3 * ε)‖ := norm_sub_le _ _
    _ ≤ 4 * ‖1 - 3 * ε‖ * √(x * (1 - x)) + √(x * (1 - x)) := by
        gcongr
        exact hH.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd) hK)
    _ = _ := by ring

theorem norm_i9Psi_le_w : ‖i9Psi ε x w y‖ ≤ (2 * (4 * ‖1 - 3 * ε‖) + 1) * √w := by
  have hc0 := i9_c_nonneg hx
  have hc4 := i9_c_le x
  have hwy0 : 0 ≤ w * y := mul_nonneg hw.1 hy.1
  have hwy1 : w * y ≤ 1 := i9_mul_le_one hw.2 hy.1 hy.2
  have hH := i9_holder (i9Poly_nonneg hx hw hy) hc0 (i9Poly_le hx hw hy) (by linarith) h1 h2
  have hd : |i9Poly x w y - x * (1 - x)| ≤ 4 * w := by
    have e : i9Poly x w y - x * (1 - x) = x * (1 - x) * (w ^ 2 - 2 * w) + w * y := by
      unfold i9Poly; ring
    rw [e, abs_le]
    constructor <;> nlinarith [hw.1, hw.2, hy.1, hy.2, mul_nonneg hc0 hw.1,
      mul_nonneg hc0 (mul_nonneg hw.1 hw.1)]
  have hs4 : √(4 * w) = 2 * √w := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hws : √(w * y) ≤ √w := Real.sqrt_le_sqrt (mul_le_of_le_one_right hw.1 hy.2)
  have hcs := (norm_cpow_le_sqrt hwy0 hwy1 h1).trans hws
  have hK : 0 ≤ 4 * ‖1 - 3 * ε‖ := by positivity
  have e : i9Psi ε x w y = (((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) -
      ((x * (1 - x) : ℝ) : ℂ) ^ (1 - 3 * ε)) - ((w * y : ℝ) : ℂ) ^ (1 - 3 * ε) := by
    unfold i9Psi; ring
  calc ‖i9Psi ε x w y‖ ≤ ‖((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) -
        ((x * (1 - x) : ℝ) : ℂ) ^ (1 - 3 * ε)‖ + ‖((w * y : ℝ) : ℂ) ^ (1 - 3 * ε)‖ := by
        rw [e]; exact norm_sub_le _ _
    _ ≤ 4 * ‖1 - 3 * ε‖ * (2 * √w) + √w := by
        gcongr
        exact hH.trans (mul_le_mul_of_nonneg_left (hs4 ▸ Real.sqrt_le_sqrt hd) hK)
    _ = _ := by ring

end Bounds

/-! ### Differences in `y` -/

theorem i9_zero_cpow (h1 : 1 / 2 ≤ (1 - 3 * ε).re) :
    ((w * 0 : ℝ) : ℂ) ^ (1 - 3 * ε) = 0 := by
  rw [mul_zero, ofReal_zero, zero_cpow]
  intro h; rw [h] at h1; simp at h1; linarith

section DiffY

variable (h1 : 1 / 2 ≤ (1 - 3 * ε).re) (h2 : (1 - 3 * ε).re ≤ 3 / 2)
  (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
include h1 h2 hx hw hy

theorem norm_i9Psi_sub_zero_le :
    ‖i9Psi ε x w y - i9Psi ε x w 0‖ ≤ (4 * ‖1 - 3 * ε‖ + 1) * √y := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hwy0 : 0 ≤ w * y := mul_nonneg hw.1 hy.1
  have hwy1 : w * y ≤ 1 := i9_mul_le_one hw.2 hy.1 hy.2
  have hH := i9_holder (i9Poly_nonneg hx hw hy) (i9Poly_nonneg hx hw h0) (i9Poly_le hx hw hy)
    (i9Poly_le hx hw h0) h1 h2
  have hd : |i9Poly x w y - i9Poly x w 0| ≤ y := by
    have e : i9Poly x w y - i9Poly x w 0 = w * y := by unfold i9Poly; ring
    rw [e, abs_of_nonneg hwy0]; exact mul_le_of_le_one_left hy.1 hw.2
  have hws : √(w * y) ≤ √y := Real.sqrt_le_sqrt (mul_le_of_le_one_left hy.1 hw.2)
  have hcs := (norm_cpow_le_sqrt hwy0 hwy1 h1).trans hws
  have hK : 0 ≤ 4 * ‖1 - 3 * ε‖ := by positivity
  have e : i9Psi ε x w y - i9Psi ε x w 0 = (((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) -
      ((i9Poly x w 0 : ℝ) : ℂ) ^ (1 - 3 * ε)) - ((w * y : ℝ) : ℂ) ^ (1 - 3 * ε) := by
    unfold i9Psi; rw [i9_zero_cpow h1]; ring
  calc _ ≤ ‖((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) - ((i9Poly x w 0 : ℝ) : ℂ) ^ (1 - 3 * ε)‖ +
        ‖((w * y : ℝ) : ℂ) ^ (1 - 3 * ε)‖ := by rw [e]; exact norm_sub_le _ _
    _ ≤ 4 * ‖1 - 3 * ε‖ * √y + √y := by
        gcongr
        exact hH.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd) hK)
    _ = _ := by ring

theorem norm_i9Psi_sub_one_le :
    ‖i9Psi ε x w y - i9Psi ε x w 1‖ ≤ 2 * (4 * ‖1 - 3 * ε‖) * √(1 - y) := by
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hwy0 : 0 ≤ w * y := mul_nonneg hw.1 hy.1
  have hwy1 : w * y ≤ 1 := i9_mul_le_one hw.2 hy.1 hy.2
  have hH := i9_holder (i9Poly_nonneg hx hw hy) (i9Poly_nonneg hx hw h1') (i9Poly_le hx hw hy)
    (i9Poly_le hx hw h1') h1 h2
  have hH2 := i9_holder hwy0 (mul_nonneg hw.1 zero_le_one) (by linarith)
    (by linarith [i9_mul_le_one hw.2 zero_le_one le_rfl]) h1 h2
  have hd : |i9Poly x w y - i9Poly x w 1| ≤ 1 - y := by
    have e : i9Poly x w y - i9Poly x w 1 = -(w * (1 - y)) := by unfold i9Poly; ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg hw.1 (by linarith [hy.2]))]
    exact mul_le_of_le_one_left (by linarith [hy.2]) hw.2
  have hd2 : |w * y - w * 1| ≤ 1 - y := by
    have e : w * y - w * 1 = -(w * (1 - y)) := by ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg hw.1 (by linarith [hy.2]))]
    exact mul_le_of_le_one_left (by linarith [hy.2]) hw.2
  have hK : 0 ≤ 4 * ‖1 - 3 * ε‖ := by positivity
  have e : i9Psi ε x w y - i9Psi ε x w 1 = (((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) -
      ((i9Poly x w 1 : ℝ) : ℂ) ^ (1 - 3 * ε)) - (((w * y : ℝ) : ℂ) ^ (1 - 3 * ε) -
      ((w * 1 : ℝ) : ℂ) ^ (1 - 3 * ε)) := by
    unfold i9Psi; ring
  calc _ ≤ ‖((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) - ((i9Poly x w 1 : ℝ) : ℂ) ^ (1 - 3 * ε)‖ +
        ‖((w * y : ℝ) : ℂ) ^ (1 - 3 * ε) - ((w * 1 : ℝ) : ℂ) ^ (1 - 3 * ε)‖ := by
        rw [e]; exact norm_sub_le _ _
    _ ≤ 4 * ‖1 - 3 * ε‖ * √(1 - y) + 4 * ‖1 - 3 * ε‖ * √(1 - y) := by
        gcongr
        · exact hH.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd) hK)
        · exact hH2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd2) hK)
    _ = _ := by ring

end DiffY

/-! ### The four bounds on `Ψ_sub` and their combination -/

/-- If `0 ≤ X ≤ M √aᵢ` for four nonnegative `aᵢ`, then `X ≤ M (a₁ a₂ a₃ a₄) ^ (1/8)`, written
as a product of powers. -/
theorem le_mul_rpow_eighth {X M a b c d : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : X ≤ M * √a) (h2 : X ≤ M * √b) (h3 : X ≤ M * √c)
    (h4 : X ≤ M * √d) :
    X ≤ M * (a ^ (1 / 8 : ℝ) * b ^ (1 / 8 : ℝ) * c ^ (1 / 8 : ℝ) * d ^ (1 / 8 : ℝ)) := by
  have hX4 : X ^ 4 ≤ M ^ 4 * (√a * √b * √c * √d) := by
    calc X ^ 4 = X * X * X * X := by ring
      _ ≤ (M * √a) * (M * √b) * (M * √c) * (M * √d) := by gcongr
      _ = _ := by ring
  have hr : X = (X ^ 4) ^ ((4 : ℕ)⁻¹ : ℝ) := (Real.pow_rpow_inv_natCast hX (by norm_num)).symm
  have hq : (√a * √b * √c * √d) ^ ((4 : ℕ)⁻¹ : ℝ) =
      a ^ (1 / 8 : ℝ) * b ^ (1 / 8 : ℝ) * c ^ (1 / 8 : ℝ) * d ^ (1 / 8 : ℝ) := by
    have e : ∀ t : ℝ, 0 ≤ t → (√t) ^ ((4 : ℕ)⁻¹ : ℝ) = t ^ (1 / 8 : ℝ) := fun t ht => by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]; norm_num
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), Real.mul_rpow (by positivity) (by positivity), e a ha, e b hb, e c hc,
      e d hd]
  rw [hr]
  calc (X ^ 4) ^ ((4 : ℕ)⁻¹ : ℝ) ≤ (M ^ 4 * (√a * √b * √c * √d)) ^ ((4 : ℕ)⁻¹ : ℝ) :=
        Real.rpow_le_rpow (by positivity) hX4 (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.pow_rpow_inv_natCast hM
          (by norm_num), hq]

/-- If `0 ≤ X ≤ M √a` and `X ≤ M √b`, then `X ≤ M a ^ (1/4) b ^ (1/4)`. -/
theorem le_mul_rpow_quarter {X M a b : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : X ≤ M * √a) (h2 : X ≤ M * √b) : X ≤ M * (a ^ (1 / 4 : ℝ) * b ^ (1 / 4 : ℝ)) := by
  have hX2 : X ^ 2 ≤ M ^ 2 * (√a * √b) := by
    calc X ^ 2 = X * X := by ring
      _ ≤ (M * √a) * (M * √b) := by gcongr
      _ = _ := by ring
  have hr : X = (X ^ 2) ^ ((2 : ℕ)⁻¹ : ℝ) := (Real.pow_rpow_inv_natCast hX (by norm_num)).symm
  have e : ∀ t : ℝ, 0 ≤ t → (√t) ^ ((2 : ℕ)⁻¹ : ℝ) = t ^ (1 / 4 : ℝ) := fun t ht => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]; norm_num
  rw [hr]
  calc (X ^ 2) ^ ((2 : ℕ)⁻¹ : ℝ) ≤ (M ^ 2 * (√a * √b)) ^ ((2 : ℕ)⁻¹ : ℝ) :=
        Real.rpow_le_rpow (by positivity) hX2 (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.pow_rpow_inv_natCast hM
          (by norm_num), Real.mul_rpow (by positivity) (by positivity), e a ha, e b hb]

theorem i9PsiSub_eq : i9PsiSub ε x w y =
    (1 - y : ℂ) * (i9Psi ε x w y - i9Psi ε x w 0) + (y : ℂ) * (i9Psi ε x w y - i9Psi ε x w 1) := by
  unfold i9PsiSub; ring

section Sub

variable (h1 : 1 / 2 ≤ (1 - 3 * ε).re) (h2 : (1 - 3 * ε).re ≤ 3 / 2)
  (hx : x ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
include h1 h2 hx hw hy

/-- **The bound on `Ψ_sub`.** `‖Ψ_sub‖ ≤ M (c w y (1 - y)) ^ (1/8)`, `M = 3 (2K + 1)`. -/
theorem norm_i9PsiSub_le : ‖i9PsiSub ε x w y‖ ≤ 3 * (2 * (4 * ‖1 - 3 * ε‖) + 1) *
    ((x * (1 - x)) ^ (1 / 8 : ℝ) * w ^ (1 / 8 : ℝ) * y ^ (1 / 8 : ℝ) * (1 - y) ^ (1 / 8 : ℝ)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set K := 4 * ‖1 - 3 * ε‖ with hKdef
  have hK : 0 ≤ K := by positivity
  have hc0 := i9_c_nonneg hx
  have hy0 : 0 ≤ 1 - y := by linarith [hy.2]
  have hny : ‖(1 - y : ℂ)‖ = 1 - y := by
    rw [show (1 - y : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg hy0]
  have hnY : ‖(y : ℂ)‖ = y := by rw [norm_real, Real.norm_of_nonneg hy.1]
  have hsc : √(x * (1 - x)) ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [i9_c_le x]
  have hsy1 : √y ≤ 1 := (Real.sqrt_le_left zero_le_one).mpr (by nlinarith [hy.2])
  have hsy : y ≤ √y := by nlinarith [Real.sqrt_nonneg y, Real.sq_sqrt hy.1]
  have hs1y : 1 - y ≤ √(1 - y) := by nlinarith [Real.sqrt_nonneg (1 - y), Real.sq_sqrt hy0,
    (Real.sqrt_le_left zero_le_one).mpr (show 1 - y ≤ 1 ^ 2 by nlinarith [hy.1])]
  have pc := fun t ht => norm_i9Psi_le_c (ε := ε) (x := x) (w := w) (y := t) h1 h2 hx hw ht
  have pw := fun t ht => norm_i9Psi_le_w (ε := ε) (x := x) (w := w) (y := t) h1 h2 hx hw ht
  have d0 := norm_i9Psi_sub_zero_le h1 h2 hx hw hy
  have d1 := norm_i9Psi_sub_one_le h1 h2 hx hw hy
  rw [← hKdef] at pc pw d0 d1
  have tri : ‖i9PsiSub ε x w y‖ ≤ ‖i9Psi ε x w y‖ + (1 - y) * ‖i9Psi ε x w 0‖ +
      y * ‖i9Psi ε x w 1‖ := by
    unfold i9PsiSub
    calc _ ≤ ‖i9Psi ε x w y - (1 - y : ℂ) * i9Psi ε x w 0‖ + ‖(y : ℂ) * i9Psi ε x w 1‖ :=
          norm_sub_le _ _
      _ ≤ ‖i9Psi ε x w y‖ + ‖(1 - y : ℂ) * i9Psi ε x w 0‖ + ‖(y : ℂ) * i9Psi ε x w 1‖ := by
          gcongr; exact norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul, hny, hnY]
  have tri2 : ‖i9PsiSub ε x w y‖ ≤ (1 - y) * ‖i9Psi ε x w y - i9Psi ε x w 0‖ +
      y * ‖i9Psi ε x w y - i9Psi ε x w 1‖ := by
    rw [i9PsiSub_eq]
    calc _ ≤ ‖(1 - y : ℂ) * (i9Psi ε x w y - i9Psi ε x w 0)‖ +
          ‖(y : ℂ) * (i9Psi ε x w y - i9Psi ε x w 1)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul, hny, hnY]
  have hpsi1 : ‖i9Psi ε x w y - i9Psi ε x w 1‖ ≤ K + 1 := by
    calc _ ≤ ‖i9Psi ε x w y‖ + ‖i9Psi ε x w 1‖ := norm_sub_le _ _
      _ ≤ (K + 1) * √(x * (1 - x)) + (K + 1) * √(x * (1 - x)) :=
          add_le_add (pc y hy) (pc 1 h1')
      _ ≤ (K + 1) * (1 / 2) + (K + 1) * (1 / 2) := by gcongr
      _ = K + 1 := by ring
  have hpsi0 : ‖i9Psi ε x w y - i9Psi ε x w 0‖ ≤ K + 1 :=
    d0.trans (by nlinarith [Real.sqrt_nonneg y])
  have hy1 := hy.2
  have hyy := hy.1
  refine le_mul_rpow_eighth (norm_nonneg _) (by positivity) hc0 hw.1 hy.1 hy0 ?_ ?_ ?_ ?_
  · refine tri.trans ?_
    have a := pc y hy; have b := pc 0 h0; have c := pc 1 h1'
    have : 0 ≤ (K + 1) * √(x * (1 - x)) := by positivity
    have hb' : (1 - y) * ‖i9Psi ε x w 0‖ ≤ (1 - y) * ((K + 1) * √(x * (1 - x))) :=
      mul_le_mul_of_nonneg_left b hy0
    have hc' : y * ‖i9Psi ε x w 1‖ ≤ y * ((K + 1) * √(x * (1 - x))) :=
      mul_le_mul_of_nonneg_left c hy.1
    nlinarith
  · refine tri.trans ?_
    have a := pw y hy; have b := pw 0 h0; have c := pw 1 h1'
    have : 0 ≤ (2 * K + 1) * √w := by positivity
    have hb' : (1 - y) * ‖i9Psi ε x w 0‖ ≤ (1 - y) * ((2 * K + 1) * √w) :=
      mul_le_mul_of_nonneg_left b hy0
    have hc' : y * ‖i9Psi ε x w 1‖ ≤ y * ((2 * K + 1) * √w) :=
      mul_le_mul_of_nonneg_left c hy.1
    nlinarith
  · refine tri2.trans ?_
    have : 0 ≤ (K + 1) * √y := by positivity
    have ha' : (1 - y) * ‖i9Psi ε x w y - i9Psi ε x w 0‖ ≤ (1 - y) * ((K + 1) * √y) :=
      mul_le_mul_of_nonneg_left d0 hy0
    have hb' : y * ‖i9Psi ε x w y - i9Psi ε x w 1‖ ≤ y * (K + 1) :=
      mul_le_mul_of_nonneg_left hpsi1 hy.1
    have hc' : y * (K + 1) ≤ √y * (K + 1) := mul_le_mul_of_nonneg_right hsy (by positivity)
    nlinarith
  · refine tri2.trans ?_
    have : 0 ≤ K * √(1 - y) := by positivity
    have ha' : (1 - y) * ‖i9Psi ε x w y - i9Psi ε x w 0‖ ≤ (1 - y) * (K + 1) :=
      mul_le_mul_of_nonneg_left hpsi0 hy0
    have hb' : y * ‖i9Psi ε x w y - i9Psi ε x w 1‖ ≤ y * (2 * K * √(1 - y)) :=
      mul_le_mul_of_nonneg_left d1 hy.1
    have hc' : (1 - y) * (K + 1) ≤ √(1 - y) * (K + 1) :=
      mul_le_mul_of_nonneg_right hs1y (by positivity)
    nlinarith [Real.sqrt_nonneg (1 - y)]

omit hy in
/-- **The bound on `Ψ|_{y=1}`.** `‖Ψ|_{y=1}‖ ≤ (2K + 1) (c w) ^ (1/4)`. -/
theorem norm_i9Psi_one_le : ‖i9Psi ε x w 1‖ ≤ (2 * (4 * ‖1 - 3 * ε‖) + 1) *
    ((x * (1 - x)) ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ)) := by
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hK : 0 ≤ 4 * ‖1 - 3 * ε‖ := by positivity
  refine le_mul_rpow_quarter (norm_nonneg _) (by positivity) (i9_c_nonneg hx) hw.1 ?_
    (norm_i9Psi_le_w h1 h2 hx hw h1')
  exact (norm_i9Psi_le_c h1 h2 hx hw h1').trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

end Sub

end QED.ThreeLoopD
