/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSGoodPt
public import QED.ThreeLoopD.SetDMastersI12RHighSRefl
public import QED.ThreeLoopD.SetDMastersI12RestSector

/-!
# Set (d), master `I₁₂`: an integrable majorant of the good part of the bulk remainder

The good part `QED.ThreeLoopD.i12HSGood` of the bulk remainder is dominated on
`(x, s, u) ∈ (0, 1) × (0, ∞) × (0, 1)`, uniformly in `‖ε‖ < 1/100`, by the integrable product

  `24000 x ^ (-4/5) g(s) u ^ (-3/5) (1 - u) ^ (-3/5)`,  `g(s) = s ^ (-4/5)` (`s < 1`),
  `g(s) = s ^ (-6/5)` (`s ≥ 1`)

(`QED.ThreeLoopD.i12HSGoodMaj`, `QED.ThreeLoopD.norm_i12HSGood_le`,
`QED.ThreeLoopD.integrableOn_i12HSGoodMaj`).

**Homogeneous form.** With `X = s k`, `k = u / (1 - u)`, the homogeneity of `Φ₀` gives
`H ^ (-ε - 1) D(s, k/H) = H ^ (2ε - 1) G(s, X, H)` (`QED.ThreeLoopD.i12HS_D_eq`), where
`G = Φ₀(X, H) - a H ^ (-3ε)` for `s < 1` and `G = Φ₀(X, H) - a X ^ (-3ε)` for `s ≥ 1`
(`QED.ThreeLoopD.i12HSG`, `a = 2 - 3ε`). For `X ≤ 1` the bounds on `Φ₀` of
`QED.ThreeLoopD.SetDMastersI12RestBounds` apply directly; for `X ≥ 1` after scaling,
`Φ₀(X, H) = X ^ (-3ε) Φ₀(1, H/X)`.

**The `x`-difference.** Writing `h = h(x)`, `h₀ = h(0)`, the difference
`h ^ (2ε - 1) G(h) - h₀ ^ (2ε - 1) G(h₀)` is bounded both without a factor `x` (by `‖G‖`) and
with a factor `x` (Lipschitz bounds in the second argument of `Φ₀`), and the two are combined by
`n ≤ A`, `n ≤ B`, `A³ B ≤ C⁴ t ⇒ n ≤ C t ^ (1/4)` (`QED.ThreeLoopD.i12HS_interp4`). The result
(`QED.ThreeLoopD.i12HS_norm_dF_le`) is `12000 x ^ (1/4) M(s, X)` with
`M = X ^ (1/4) + √X` for `s < 1` and `M = X ^ (-1/4) + 1/√X` for `s ≥ 1`
(`QED.ThreeLoopD.i12HSM`); the remaining factors `x ^ (ε - 1) s ^ (2ε - 1) w(u)` are bounded by
real powers, and the exponents are compared on `(0, 1]` and `[1, ∞)`.

## Main results

* `QED.ThreeLoopD.i12HS_D_eq`: the homogeneous form of one scale of the good part.
* `QED.ThreeLoopD.i12HS_norm_dF_le`: the bound on the `x`-difference.
* `QED.ThreeLoopD.norm_i12HSGood_le`: the pointwise domination.
* `QED.ThreeLoopD.measurable_i12HSGood`, `QED.ThreeLoopD.integrableOn_i12HSGoodMaj`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

theorem i12HS_interp4 {z A B C t : ℝ} (hz : 0 ≤ z) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hA : z ≤ A) (hB : z ≤ B) (h : A ^ 3 * B ≤ C ^ 4 * t) : z ≤ C * t ^ (1 / 4 : ℝ) := by
  have e : (C * t ^ (1 / 4 : ℝ)) ^ 4 = C ^ 4 * t := by
    rw [mul_pow, ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht]; norm_num
  have h4 : z ^ 4 ≤ (C * t ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [e]
    calc z ^ 4 = z ^ 3 * z := by ring
      _ ≤ A ^ 3 * B :=
        mul_le_mul (pow_le_pow_left₀ hz hA 3) hB hz (pow_nonneg (hz.trans hA) 3)
      _ ≤ _ := h
  exact (pow_le_pow_iff_left₀ hz (by positivity) (by norm_num)).1 h4

theorem i12HS_norm_cpow_ge_one {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {X : ℝ} (hX : 1 ≤ X) :
    ‖(X : ℂ) ^ (-3 * ε)‖ ≤ X ^ (1 / 16 : ℝ) := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hX (by simp; linarith)

theorem i12HS_rpow16_le_sqrt {X : ℝ} (hX : 1 ≤ X) : X ^ (1 / 16 : ℝ) ≤ √X := by
  rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

theorem i12HS_phi0_scale (ε : ℂ) {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    i12Phi0 ε X H = (X : ℂ) ^ (-3 * ε) * i12Phi0 ε 1 (H / X) := by
  have := i12Phi0_mul_mul ε hX one_pos (div_pos hH hX)
  rwa [mul_one, mul_div_cancel₀ _ hX.ne'] at this

/-- The kernel of the good part in homogeneous form. -/
noncomputable def i12HSG (ε : ℂ) (s X H : ℝ) : ℂ :=
  i12Phi0 ε X H -
    if s < 1 then (2 - 3 * ε) * (H : ℂ) ^ (-3 * ε) else (2 - 3 * ε) * (X : ℂ) ^ (-3 * ε)

theorem i12HS_D_eq (ε : ℂ) {s k H : ℝ} (hs : 0 < s) (hk : 0 < k) (hH : 0 < H) :
    (H : ℂ) ^ (-ε - 1) * i12HSD ε s (k / H) =
      (H : ℂ) ^ (2 * ε - 1) * i12HSG ε s (s * k) H := by
  have hH' : (H : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
  have hsc := i12Phi0_mul_mul ε (inv_pos.mpr hH) (mul_pos hs hk) hH
  rw [show H⁻¹ * (s * k) = s * (k / H) by field_simp, inv_mul_cancel₀ hH.ne'] at hsc
  have eP : ((H⁻¹ : ℝ) : ℂ) ^ (-3 * ε) = (H : ℂ) ^ (3 * ε) := by
    rw [i12_cpow_lin (inv_pos.2 hH), i12_cpow_lin hH, Real.log_inv]; push_cast; ring_nf
  have f1 : (H : ℂ) ^ (-ε - 1) * (H : ℂ) ^ (3 * ε) = (H : ℂ) ^ (2 * ε - 1) := by
    rw [← cpow_add _ _ hH']; ring_nf
  have f2 : (H : ℂ) ^ (2 * ε - 1) * (H : ℂ) ^ (-3 * ε) = (H : ℂ) ^ (-ε - 1) := by
    rw [← cpow_add _ _ hH']; ring_nf
  have f3 : ((s * (k / H) : ℝ) : ℂ) ^ (-3 * ε) =
      ((s * k : ℝ) : ℂ) ^ (-3 * ε) * (H : ℂ) ^ (3 * ε) := by
    rw [show s * (k / H) = (s * k) * H⁻¹ by ring, ofReal_mul,
      mul_cpow_ofReal_nonneg (by positivity) (by positivity), eP]
  simp only [i12HSD, i12HSG, hsc, eP]
  split_ifs
  · linear_combination (i12Phi0 ε (s * k) H) * f1 + (2 - 3 * ε) * f2
  · rw [f3]
    linear_combination (i12Phi0 ε (s * k) H - (2 - 3 * ε) * ((s * k : ℝ) : ℂ) ^ (-3 * ε)) * f1

theorem i12HS_sqrt_quarter {H : ℝ} (hH : 1 / 4 ≤ H) : 1 / √H ≤ 2 := by
  have h : 1 / 2 ≤ √H := by
    rw [show (1 / 2 : ℝ) = √(1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hH
  rw [div_le_iff₀ (by linarith)]; linarith

section Bounds

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100)
include hε

/-- `s < 1`: `‖Φ₀(X, H) - a H ^ (-3ε)‖ ≤ 108 √X`. -/
theorem i12HS_norm_G_lt {X H : ℝ} (hX : 0 < X) (hH : 1 / 4 ≤ H) (hH1 : H ≤ 1 / 2) {s : ℝ}
    (hs : s < 1) : ‖i12HSG ε s X H‖ ≤ 108 * √X := by
  obtain ⟨-, -, -, hw, -⟩ := i12_eps_facts hε
  have hH0 : 0 < H := by linarith
  simp only [i12HSG, hs, ↓reduceIte]
  rcases le_total X 1 with hX1 | hX1
  · have h := norm_i12Phi0_sub_le hε hX hH0 hX1 (by linarith)
    refine h.trans ?_
    rw [div_le_iff₀ hH0]
    have := Real.sqrt_nonneg X
    nlinarith
  · have hY := norm_i12_ypow_le hε hH0 (by linarith : H / 4 ≤ H) (by linarith : H ≤ 1)
    have hP := norm_i12Phi0_le_left hε one_pos (div_pos hH0 hX) le_rfl
      ((div_le_one hX).2 (by linarith))
    have hc := i12HS_norm_cpow_ge_one hε hX1
    have h16 := i12HS_rpow16_le_sqrt hX1
    have hq := i12HS_sqrt_quarter hH
    have h1 : 1 ≤ √X := Real.one_le_sqrt.mpr hX1
    rw [i12HS_phi0_scale ε hX hH0, Real.sqrt_one] at *
    calc _ ≤ ‖(X : ℂ) ^ (-3 * ε)‖ * ‖i12Phi0 ε 1 (H / X)‖ +
          ‖2 - 3 * ε‖ * ‖(H : ℂ) ^ (-3 * ε)‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ √X * (24 / 1) + 3 * 2 :=
          add_le_add (mul_le_mul (hc.trans h16) hP (norm_nonneg _) (Real.sqrt_nonneg _))
            (mul_le_mul hw (hY.trans hq) (norm_nonneg _) (by norm_num))
      _ ≤ 108 * √X := by linarith

/-- `s ≥ 1`, `X ≤ 1`: `‖Φ₀(X, H) - a X ^ (-3ε)‖ ≤ 51 / √X`. -/
theorem i12HS_norm_G_ge_small {X H : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) (hH : 1 / 4 ≤ H)
    (hH1 : H ≤ 1 / 2) {s : ℝ} (hs : ¬ s < 1) : ‖i12HSG ε s X H‖ ≤ 51 / √X := by
  obtain ⟨-, -, -, hw, -⟩ := i12_eps_facts hε
  have hH0 : 0 < H := by linarith
  simp only [i12HSG, hs, ↓reduceIte]
  have hP := norm_i12Phi0_le_right hε hX hH0 hX1 (by linarith)
  have hY := norm_i12_ypow_le hε hX (by linarith : X / 4 ≤ X) hX1
  have hq := i12HS_sqrt_quarter hH
  have hsX := Real.sqrt_pos.mpr hX
  have hs1 : √X ≤ 1 := Real.sqrt_le_one.mpr hX1
  have h1 : 1 ≤ 1 / √X := by rw [le_div_iff₀ hsX]; linarith
  calc _ ≤ ‖i12Phi0 ε X H‖ + ‖2 - 3 * ε‖ * ‖(X : ℂ) ^ (-3 * ε)‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ 24 * (1 / √H) + 3 * (1 / √X) := by
        refine add_le_add (by rw [mul_one_div]; exact hP) ?_
        exact mul_le_mul hw hY (norm_nonneg _) (by norm_num)
    _ ≤ 24 * 2 + 3 * (1 / √X) := by gcongr
    _ ≤ 51 * (1 / √X) := by linarith
    _ = 51 / √X := by ring

/-- `s ≥ 1`, `X ≥ 1`: `‖Φ₀(X, H) - a X ^ (-3ε)‖ ≤ 27 X ^ (1/16) / √X`. -/
theorem i12HS_norm_G_ge_large {X H : ℝ} (hX1 : 1 ≤ X) (hH : 1 / 4 ≤ H) (hH1 : H ≤ 1 / 2)
    {s : ℝ} (hs : ¬ s < 1) : ‖i12HSG ε s X H‖ ≤ 27 * X ^ (1 / 16 : ℝ) / √X := by
  have hX : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  simp only [i12HSG, hs, ↓reduceIte]
  have hY : 0 < H / X := div_pos hH0 hX
  have hY1 : H / X ≤ 1 := (div_le_one hX).2 (by linarith)
  have h := norm_i12Phi0_sub_le' hε one_pos hY le_rfl hY1
  rw [ofReal_one, one_cpow, mul_one, div_one] at h
  have e : i12Phi0 ε X H - (2 - 3 * ε) * (X : ℂ) ^ (-3 * ε) =
      (X : ℂ) ^ (-3 * ε) * (i12Phi0 ε 1 (H / X) - (2 - 3 * ε)) := by
    rw [i12HS_phi0_scale ε hX hH0]; ring
  rw [e, norm_mul]
  have hc := i12HS_norm_cpow_ge_one hε hX1
  have hsq : √(H / X) ≤ 1 / √X := by
    rw [Real.sqrt_div hH0.le]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_one.mpr (by linarith)) (Real.sqrt_nonneg _)
  calc _ ≤ X ^ (1 / 16 : ℝ) * (27 * (1 / √X)) :=
        mul_le_mul hc (h.trans (by gcongr)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem i12HS_norm_dPhi_small {X x : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖i12Phi0 ε X (i12H x) - i12Phi0 ε X (i12H 0)‖ ≤ 24 * x / √X := by
  have hh := i12H_mem hx
  have hle : i12H x ≤ i12H 0 := by unfold i12H; linarith [hx.1]
  have h := norm_i12Phi0_sub_right_le' hε hX hX1 (by linarith [hh.1]) hle
    (by rw [i12H_zero]; norm_num)
  rw [norm_sub_rev]
  refine h.trans (le_of_eq ?_)
  have hsX := Real.sqrt_pos.mpr hX
  rw [i12H_zero]; unfold i12H; field_simp; ring

theorem i12HS_norm_dPhi_large {X x : ℝ} (hX1 : 1 ≤ X) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖i12Phi0 ε X (i12H x) - i12Phi0 ε X (i12H 0)‖ ≤ 24 * x * X ^ (1 / 16 : ℝ) := by
  have hX : 0 < X := by linarith
  have hh := i12H_mem hx
  have hle : i12H x ≤ i12H 0 := by unfold i12H; linarith [hx.1]
  have hY2 : 0 < i12H x / X := div_pos (by linarith [hh.1]) hX
  have h := norm_i12Phi0_sub_right_le' hε one_pos le_rfl hY2
    (div_le_div_of_nonneg_right hle hX.le) ((div_le_one hX).2 (by rw [i12H_zero]; linarith))
  rw [i12HS_phi0_scale ε hX (by linarith [hh.1]),
    i12HS_phi0_scale ε hX (by rw [i12H_zero]; norm_num), ← mul_sub, norm_mul,
    norm_sub_rev (i12Phi0 ε 1 _)]
  have hc := i12HS_norm_cpow_ge_one hε hX1
  have e : 48 * (i12H 0 / X - i12H x / X) / (i12H 0 / X * √1) = 24 * x := by
    rw [i12H_zero, Real.sqrt_one]; unfold i12H; field_simp; ring
  rw [e] at h
  calc _ ≤ X ^ (1 / 16 : ℝ) * (24 * x) := mul_le_mul hc h (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem i12HS_norm_dA {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖(2 - 3 * ε) * ((i12H x : ℝ) : ℂ) ^ (-3 * ε) -
      (2 - 3 * ε) * ((i12H 0 : ℝ) : ℂ) ^ (-3 * ε)‖ ≤ x := by
  have hh := i12H_mem hx
  have hle : i12H x ≤ i12H 0 := by unfold i12H; linarith [hx.1]
  have h := norm_i12_wypow_sub_le hε one_pos (by linarith [hh.1] : (1 : ℝ) / 4 ≤ i12H x)
    (by linarith [hh.2]) hle
  rw [norm_sub_rev]
  refine h.trans ?_
  rw [Real.one_rpow, mul_one, div_le_iff₀ (by linarith [hh.1])]
  unfold i12H; nlinarith [hx.1, hx.2]

end Bounds

theorem i12HS_norm_dF_aux {P Q G1 G0 : ℂ} {x : ℝ} (hPQ : ‖P - Q‖ ≤ 32 * x) (hP : ‖P‖ ≤ 64)
    (hQ : ‖Q‖ ≤ 64) :
    ‖P * G1 - Q * G0‖ ≤ 32 * x * ‖G1‖ + 64 * ‖G1 - G0‖ ∧
      ‖P * G1 - Q * G0‖ ≤ 64 * ‖G1‖ + 64 * ‖G0‖ := by
  constructor
  · rw [show P * G1 - Q * G0 = (P - Q) * G1 + Q * (G1 - G0) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr

theorem i12HS_reg_lt_small {z g1 g0 d x X : ℝ} (hz : 0 ≤ z) (hX : 0 < X) (hX1 : X ≤ 1)
    (hx : 0 ≤ x) (hg1 : g1 ≤ 108 * √X) (hg0 : g0 ≤ 108 * √X)
    (hd : d ≤ 24 * x / √X + x) (hA : z ≤ 64 * g1 + 64 * g0) (hB : z ≤ 32 * x * g1 + 64 * d) :
    z ≤ 11000 * (x * X) ^ (1 / 4 : ℝ) := by
  have hsX := Real.sqrt_pos.mpr hX
  have hs1 : √X ≤ 1 := Real.sqrt_le_one.mpr hX1
  have hss := Real.mul_self_sqrt hX.le
  have hq1 : x * √X ≤ x / √X := by rw [le_div_iff₀ hsX]; nlinarith
  have hq2 : x ≤ x / √X := by rw [le_div_iff₀ hsX]; nlinarith
  have hA' : z ≤ 13824 * √X := by linarith
  have hB' : z ≤ 5056 * (x / √X) := by
    have h1 : 32 * x * g1 ≤ 32 * 108 * (x * √X) := by nlinarith
    have h2 : 24 * x / √X = 24 * (x / √X) := by ring
    linarith
  refine i12HS_interp4 hz (by norm_num) (by positivity) hA' hB' ?_
  have e : (13824 * √X) ^ 3 * (5056 * (x / √X)) = 13824 ^ 3 * 5056 * (x * √X ^ 2) := by
    field_simp
  rw [e, Real.sq_sqrt hX.le]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem i12HS_reg_lt_large {z g1 d x X : ℝ} (hX1 : 1 ≤ X) (hx : 0 ≤ x)
    (hg1 : g1 ≤ 108 * √X) (hd : d ≤ 24 * x * X ^ (1 / 16 : ℝ) + x)
    (hB : z ≤ 32 * x * g1 + 64 * d) : z ≤ 5056 * (x * √X) := by
  have h16 := i12HS_rpow16_le_sqrt hX1
  have h1 : 1 ≤ √X := Real.one_le_sqrt.mpr hX1
  have a1 : 32 * x * g1 ≤ 32 * 108 * (x * √X) := by nlinarith
  have a2 : x * X ^ (1 / 16 : ℝ) ≤ x * √X := mul_le_mul_of_nonneg_left h16 hx
  have a3 : x ≤ x * √X := by nlinarith
  nlinarith

theorem i12HS_reg_ge_small {z g1 d x X : ℝ} (hx : 0 ≤ x)
    (hg1 : g1 ≤ 51 / √X) (hd : d ≤ 24 * x / √X)
    (hB : z ≤ 32 * x * g1 + 64 * d) : z ≤ 3168 * (x / √X) := by
  have a1 : 32 * x * g1 ≤ 32 * 51 * (x / √X) := by
    have := mul_le_mul_of_nonneg_left hg1 (by positivity : 0 ≤ 32 * x)
    calc _ ≤ 32 * x * (51 / √X) := this
      _ = _ := by ring
  have a2 : 24 * x / √X = 24 * (x / √X) := by ring
  linarith

theorem i12HS_reg_ge_large {z g1 g0 d x X : ℝ} (hz : 0 ≤ z) (hX1 : 1 ≤ X) (hx : 0 ≤ x)
    (hg1 : g1 ≤ 27 * X ^ (1 / 16 : ℝ) / √X) (hg0 : g0 ≤ 27 * X ^ (1 / 16 : ℝ) / √X)
    (hd : d ≤ 24 * x * X ^ (1 / 16 : ℝ)) (hA : z ≤ 64 * g1 + 64 * g0)
    (hB : z ≤ 32 * x * g1 + 64 * d) : z ≤ 4000 * (x / X) ^ (1 / 4 : ℝ) := by
  have hX : 0 < X := by linarith
  have hsX := Real.sqrt_pos.mpr hX
  have h1 : 1 ≤ √X := Real.one_le_sqrt.mpr hX1
  set p := X ^ (1 / 16 : ℝ) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp4 : p ^ 4 ≤ √X := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hX.le, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hA' : z ≤ 3456 * (p / √X) := by
    have : 27 * p / √X = 27 * (p / √X) := by ring
    linarith
  have hB' : z ≤ 2400 * (x * p) := by
    have hq : p / √X ≤ p := div_le_self hp0 h1
    have a1 : 32 * x * g1 ≤ 32 * 27 * (x * p) := by
      have := mul_le_mul_of_nonneg_left hg1 (by positivity : 0 ≤ 32 * x)
      have e : 27 * p / √X = 27 * (p / √X) := by ring
      rw [e] at this
      nlinarith [mul_le_mul_of_nonneg_left hq hx]
    linarith
  refine i12HS_interp4 hz (by norm_num) (by positivity) hA' hB' ?_
  have e : (3456 * (p / √X)) ^ 3 * (2400 * (x * p)) = 3456 ^ 3 * 2400 * (x * p ^ 4 / √X ^ 3) := by
    field_simp
  rw [e]
  have h2 : x * p ^ 4 / √X ^ 3 ≤ x / X := by
    rw [div_le_div_iff₀ (by positivity) hX]
    have : √X ^ 3 = X * √X := by
      rw [pow_succ, sq, Real.mul_self_sqrt hX.le]
    rw [this]
    have := mul_le_mul_of_nonneg_left hp4 hx
    nlinarith
  have h3 : 0 ≤ x / X := by positivity
  nlinarith


/-- The `(s, X)`-profile of the bound on the `x`-difference. -/
noncomputable def i12HSM (s X : ℝ) : ℝ :=
  if s < 1 then X ^ (1 / 4 : ℝ) + √X else X ^ (-(1 / 4) : ℝ) + 1 / √X

/-- **The `x`-difference of one scale of the good part**, for `x ∈ (0, 1)`, `X > 0`. -/
theorem i12HS_norm_dF_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {x s X : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hX : 0 < X) :
    ‖((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) * i12HSG ε s X (i12H x) -
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * i12HSG ε s X (i12H 0)‖ ≤
      12000 * (x ^ (1 / 4 : ℝ) * i12HSM s X) := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hh := i12H_mem hxI
  have hh0 := i12H_mem h0I
  obtain ⟨d1, d2⟩ := i12HS_norm_dF_aux (G1 := i12HSG ε s X (i12H x))
    (G0 := i12HSG ε s X (i12H 0)) (norm_i12_hpow_sub_le hε hxI) (norm_i12_hpow_le hε hxI)
    (norm_i12_hpow_le hε h0I)
  have hxq : x ≤ x ^ (1 / 4 : ℝ) := i12_le_rpow_quarter hx.1 hx.2.le
  have hx0 := hx.1.le
  have hX4 : 0 ≤ X ^ (1 / 4 : ℝ) := by positivity
  have hsX := Real.sqrt_pos.mpr hX
  by_cases hs : s < 1
  · have eG : i12HSG ε s X (i12H x) - i12HSG ε s X (i12H 0) =
        (i12Phi0 ε X (i12H x) - i12Phi0 ε X (i12H 0)) -
          ((2 - 3 * ε) * ((i12H x : ℝ) : ℂ) ^ (-3 * ε) -
            (2 - 3 * ε) * ((i12H 0 : ℝ) : ℂ) ^ (-3 * ε)) := by
      simp only [i12HSG, hs, ↓reduceIte]; ring
    have hA := i12HS_norm_dA hε hxI
    simp only [i12HSM, hs, ↓reduceIte]
    have g1 := i12HS_norm_G_lt hε hX hh.1 hh.2 hs
    rcases le_total X 1 with hX1 | hX1
    · have hd : ‖i12HSG ε s X (i12H x) - i12HSG ε s X (i12H 0)‖ ≤ 24 * x / √X + x := by
        rw [eG]
        exact (norm_sub_le _ _).trans (add_le_add (i12HS_norm_dPhi_small hε hX hX1 hxI) hA)
      have h := i12HS_reg_lt_small (norm_nonneg _) hX hX1 hx0 g1
        (i12HS_norm_G_lt hε hX hh0.1 hh0.2 hs) hd d2 d1
      rw [Real.mul_rpow hx0 hX.le] at h
      have : 0 ≤ x ^ (1 / 4 : ℝ) * √X := by positivity
      nlinarith
    · have hd : ‖i12HSG ε s X (i12H x) - i12HSG ε s X (i12H 0)‖ ≤
          24 * x * X ^ (1 / 16 : ℝ) + x := by
        rw [eG]
        exact (norm_sub_le _ _).trans (add_le_add (i12HS_norm_dPhi_large hε hX1 hxI) hA)
      have h := i12HS_reg_lt_large hX1 hx0 g1 hd d1
      have : x * √X ≤ x ^ (1 / 4 : ℝ) * √X := mul_le_mul_of_nonneg_right hxq hsX.le
      have : 0 ≤ x ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ) := by positivity
      nlinarith
  · have eG : i12HSG ε s X (i12H x) - i12HSG ε s X (i12H 0) =
        i12Phi0 ε X (i12H x) - i12Phi0 ε X (i12H 0) := by
      simp only [i12HSG, hs, ↓reduceIte]; ring
    simp only [i12HSM, hs, ↓reduceIte]
    have hXm : 0 ≤ X ^ (-(1 / 4) : ℝ) := by positivity
    rcases le_total X 1 with hX1 | hX1
    · have h := i12HS_reg_ge_small hx0 (i12HS_norm_G_ge_small hε hX hX1 hh.1 hh.2 hs)
        (by rw [eG]; exact i12HS_norm_dPhi_small hε hX hX1 hxI) d1
      have : x / √X ≤ x ^ (1 / 4 : ℝ) * (1 / √X) := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hxq hsX.le
      have : 0 ≤ x ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ) := by positivity
      have : 0 ≤ x / √X := by positivity
      rw [mul_add]
      linarith
    · have h := i12HS_reg_ge_large (norm_nonneg _) hX1 hx0
        (i12HS_norm_G_ge_large hε hX1 hh.1 hh.2 hs) (i12HS_norm_G_ge_large hε hX1 hh0.1 hh0.2 hs)
        (by rw [eG]; exact i12HS_norm_dPhi_large hε hX1 hxI) d2 d1
      rw [Real.div_rpow hx0 hX.le, div_eq_mul_inv, ← Real.rpow_neg hX.le] at h
      have : 0 ≤ x ^ (1 / 4 : ℝ) * (1 / √X) := by positivity
      nlinarith


theorem i12HS_rpow3_le {s u v a b c a' b' c' : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hu : 0 < u)
    (hu1 : u ≤ 1) (hv : 0 < v) (hv1 : v ≤ 1) (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    s ^ a * (u ^ b * v ^ c) ≤ s ^ a' * (u ^ b' * v ^ c') :=
  mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hs hs1 ha)
    (mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hu hu1 hb)
      (Real.rpow_le_rpow_of_exponent_ge hv hv1 hc) (by positivity) (by positivity))
    (by positivity) (by positivity)

theorem i12HS_rpow3_le' {s u v a b c a' b' c' : ℝ} (hs1 : 1 ≤ s) (hu : 0 < u)
    (hu1 : u ≤ 1) (hv : 0 < v) (hv1 : v ≤ 1) (ha : a ≤ a') (hb : b' ≤ b) (hc : c' ≤ c) :
    s ^ a * (u ^ b * v ^ c) ≤ s ^ a' * (u ^ b' * v ^ c') :=
  mul_le_mul (Real.rpow_le_rpow_of_exponent_le hs1 ha)
    (mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hu hu1 hb)
      (Real.rpow_le_rpow_of_exponent_ge hv hv1 hc) (by positivity) (by positivity))
    (by positivity) (by linarith [Real.one_le_rpow hs1 (by norm_num : (0 : ℝ) ≤ 0),
      Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < s) a'])

theorem i12HS_k_rpow {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (r : ℝ) :
    i12HSk u ^ r = u ^ r * (1 - u) ^ (-r) := by
  have h1 : 0 < 1 - u := by linarith [hu.2]
  rw [i12HSk, Real.div_rpow hu.1.le h1.le, Real.rpow_neg h1.le, div_eq_mul_inv]

theorem i12HS_sk_rpow {s u : ℝ} (hs : 0 < s) (hu : u ∈ Ioo (0 : ℝ) 1) (r : ℝ) :
    (s * i12HSk u) ^ r = s ^ r * (u ^ r * (1 - u) ^ (-r)) := by
  have hk : 0 ≤ i12HSk u := (div_pos hu.1 (by linarith [hu.2])).le
  rw [Real.mul_rpow hs.le hk, i12HS_k_rpow hu]

/-- The integrable majorant of the good part on `(0, 1) × (0, ∞) × (0, 1)`. -/
noncomputable def i12HSGoodMaj (x s u : ℝ) : ℝ :=
  24000 * (x ^ (-(4 / 5) : ℝ) *
    ((if s < 1 then s ^ (-(4 / 5) : ℝ) else s ^ (-(6 / 5) : ℝ)) *
      (u ^ (-(3 / 5) : ℝ) * (1 - u) ^ (-(3 / 5) : ℝ))))

theorem i12HS_xpow_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x ^ (-(101 / 100) : ℝ) * x ^ (1 / 4 : ℝ) ≤ x ^ (-(4 / 5) : ℝ) := by
  rw [← Real.rpow_add hx.1]
  exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by norm_num)

theorem i12HS_maj_real {x s u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hu : u ∈ Ioo (0 : ℝ) 1) {Sn : ℝ} (hSn0 : 0 ≤ Sn)
    (hSn : Sn ≤ if s < 1 then s ^ (-(51 / 50) : ℝ) else s ^ (-(49 / 50) : ℝ)) :
    x ^ (-(101 / 100) : ℝ) * Sn * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) *
      (12000 * (x ^ (1 / 4 : ℝ) * i12HSM s (s * i12HSk u))) ≤ i12HSGoodMaj x s u := by
  have hv : 0 < 1 - u := by linarith [hu.2]
  have hv1 : 1 - u ≤ 1 := by linarith [hu.1]
  have hxp := i12HS_xpow_le hx
  have hx' := hx.1
  have hu' := hu.1
  have hk : 0 < i12HSk u := div_pos hu.1 hv
  have hW : 0 ≤ u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hv.le _)
  have hx0 : 0 ≤ x ^ (-(101 / 100) : ℝ) := by positivity
  have hx4 : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  set T := u ^ (-(3 / 5) : ℝ) * (1 - u) ^ (-(3 / 5) : ℝ) with hT
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (Real.rpow_nonneg hv.le _)
  -- the `(s, u)` part
  have key : (if s < 1 then s ^ (-(51 / 50) : ℝ) else s ^ (-(49 / 50) : ℝ)) *
      (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) * i12HSM s (s * i12HSk u) ≤
      2 * ((if s < 1 then s ^ (-(4 / 5) : ℝ) else s ^ (-(6 / 5) : ℝ)) * T) := by
    by_cases hs1 : s < 1
    · simp only [i12HSM, hs1, ↓reduceIte]
      rw [Real.sqrt_eq_rpow, i12HS_sk_rpow hs hu, i12HS_sk_rpow hs hu]
      have t1 : s ^ (-(51 / 50) : ℝ) * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) *
          (s ^ (1 / 4 : ℝ) * (u ^ (1 / 4 : ℝ) * (1 - u) ^ (-(1 / 4) : ℝ))) =
          s ^ (-(51 / 50) + 1 / 4 : ℝ) * (u ^ (-(1 / 100) + 1 / 4 : ℝ) *
            (1 - u) ^ (-(1 / 50) + -(1 / 4) : ℝ)) := by
        rw [Real.rpow_add hs, Real.rpow_add hu.1, Real.rpow_add hv]; ring
      have t2 : s ^ (-(51 / 50) : ℝ) * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) *
          (s ^ (1 / 2 : ℝ) * (u ^ (1 / 2 : ℝ) * (1 - u) ^ (-(1 / 2) : ℝ))) =
          s ^ (-(51 / 50) + 1 / 2 : ℝ) * (u ^ (-(1 / 100) + 1 / 2 : ℝ) *
            (1 - u) ^ (-(1 / 50) + -(1 / 2) : ℝ)) := by
        rw [Real.rpow_add hs, Real.rpow_add hu.1, Real.rpow_add hv]; ring
      have b1 := i12HS_rpow3_le (a' := -(4 / 5)) (b' := -(3 / 5)) (c' := -(3 / 5)) hs hs1.le hu.1
        hu.2.le hv hv1 (a := -(51 / 50) + 1 / 4) (b := -(1 / 100) + 1 / 4)
        (c := -(1 / 50) + -(1 / 4)) (by norm_num) (by norm_num) (by norm_num)
      have b2 := i12HS_rpow3_le (a' := -(4 / 5)) (b' := -(3 / 5)) (c' := -(3 / 5)) hs hs1.le hu.1
        hu.2.le hv hv1 (a := -(51 / 50) + 1 / 2) (b := -(1 / 100) + 1 / 2)
        (c := -(1 / 50) + -(1 / 2)) (by norm_num) (by norm_num) (by norm_num)
      rw [mul_add, t1, t2]
      linarith
    · simp only [i12HSM, hs1, ↓reduceIte]
      have hs1' : 1 ≤ s := not_lt.mp hs1
      rw [i12_inv_sqrt_eq (by positivity), i12HS_sk_rpow hs hu, i12HS_sk_rpow hs hu]
      have t1 : s ^ (-(49 / 50) : ℝ) * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) *
          (s ^ (-(1 / 4) : ℝ) * (u ^ (-(1 / 4) : ℝ) * (1 - u) ^ (-(-(1 / 4)) : ℝ))) =
          s ^ (-(49 / 50) + -(1 / 4) : ℝ) * (u ^ (-(1 / 100) + -(1 / 4) : ℝ) *
            (1 - u) ^ (-(1 / 50) + -(-(1 / 4)) : ℝ)) := by
        rw [Real.rpow_add hs, Real.rpow_add hu.1, Real.rpow_add hv]; ring
      have t2 : s ^ (-(49 / 50) : ℝ) * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) *
          (s ^ (-(1 / 2) : ℝ) * (u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (-(-(1 / 2)) : ℝ))) =
          s ^ (-(49 / 50) + -(1 / 2) : ℝ) * (u ^ (-(1 / 100) + -(1 / 2) : ℝ) *
            (1 - u) ^ (-(1 / 50) + -(-(1 / 2)) : ℝ)) := by
        rw [Real.rpow_add hs, Real.rpow_add hu.1, Real.rpow_add hv]; ring
      have b1 := i12HS_rpow3_le' (a' := -(6 / 5)) (b' := -(3 / 5)) (c' := -(3 / 5)) hs1' hu.1
        hu.2.le hv hv1 (a := -(49 / 50) + -(1 / 4)) (b := -(1 / 100) + -(1 / 4))
        (c := -(1 / 50) + -(-(1 / 4))) (by norm_num) (by norm_num) (by norm_num)
      have b2 := i12HS_rpow3_le' (a' := -(6 / 5)) (b' := -(3 / 5)) (c' := -(3 / 5)) hs1' hu.1
        hu.2.le hv hv1 (a := -(49 / 50) + -(1 / 2)) (b := -(1 / 100) + -(1 / 2))
        (c := -(1 / 50) + -(-(1 / 2))) (by norm_num) (by norm_num) (by norm_num)
      rw [mul_add, t1, t2]
      linarith
  have hM : 0 ≤ i12HSM s (s * i12HSk u) := by
    unfold i12HSM; split_ifs <;> positivity
  have hSn' : Sn * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) * i12HSM s (s * i12HSk u) ≤
      2 * ((if s < 1 then s ^ (-(4 / 5) : ℝ) else s ^ (-(6 / 5) : ℝ)) * T) :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSn hW) hM) key
  have hG : 0 ≤ (if s < 1 then s ^ (-(4 / 5) : ℝ) else s ^ (-(6 / 5) : ℝ)) * T := by
    split_ifs <;> positivity
  calc _ = 12000 * ((x ^ (-(101 / 100) : ℝ) * x ^ (1 / 4 : ℝ)) *
        (Sn * (u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ)) * i12HSM s (s * i12HSk u))) := by
        ring
    _ ≤ 12000 * (x ^ (-(4 / 5) : ℝ) *
        (2 * ((if s < 1 then s ^ (-(4 / 5) : ℝ) else s ^ (-(6 / 5) : ℝ)) * T))) := by
        gcongr
    _ = i12HSGoodMaj x s u := by rw [i12HSGoodMaj]; ring


/-- **Pointwise domination of the good part** on `(0, 1) × (0, ∞) × (0, 1)`, uniformly in
`‖ε‖ < 1/100`. -/
theorem norm_i12HSGood_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {x s u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hs : 0 < s) (hu : u ∈ Ioo (0 : ℝ) 1) : ‖i12HSGood ε x s u‖ ≤ i12HSGoodMaj x s u := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hv : 0 < 1 - u := by linarith [hu.2]
  have hk : 0 < i12HSk u := div_pos hu.1 hv
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hh := i12H_mem hxI
  have hh0 := i12H_mem (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
  have eG : i12HSGood ε x s u = (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
      (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) * i12HSG ε s (s * i12HSk u) (i12H x) -
        ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * i12HSG ε s (s * i12HSk u) (i12H 0)) := by
    rw [i12HSGood, i12HS_D_eq ε hs hk (by linarith [hh.1]),
      i12HS_D_eq ε hs hk (by linarith [hh0.1])]
  have hdF := i12HS_norm_dF_le hε hx (s := s) (mul_pos hs hk)
  have hX : ‖(x : ℂ) ^ (ε - 1)‖ ≤ x ^ (-(101 / 100) : ℝ) :=
    norm_cpow_le_rpow_of_le hx.1 hx.2.le (by simp; linarith)
  have hW : ‖i12HSw ε u‖ ≤ u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ) := by
    rw [i12HSw, norm_mul]
    exact mul_le_mul (norm_cpow_le_rpow_of_le hu.1 hu.2.le (by linarith))
      (norm_cpow_le_rpow_of_le hv (by linarith [hu.1]) (by simp; linarith))
      (norm_nonneg _) (Real.rpow_nonneg hu.1.le _)
  have hS : ‖(s : ℂ) ^ (2 * ε - 1)‖ ≤
      if s < 1 then s ^ (-(51 / 50) : ℝ) else s ^ (-(49 / 50) : ℝ) := by
    split_ifs with hs1
    · exact norm_cpow_le_rpow_of_le hs hs1.le (by simp; linarith)
    · rw [norm_cpow_eq_rpow_re_of_pos hs]
      exact Real.rpow_le_rpow_of_exponent_le (not_lt.mp hs1) (by simp; linarith)
  refine le_trans ?_ (i12HS_maj_real hx hs hu (norm_nonneg _) hS)
  rw [eG, norm_mul, norm_mul, norm_mul]
  have hW0 : 0 ≤ u ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(1 / 50) : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg hv.le _)
  refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hX (norm_nonneg _)) hW
    (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.1.le _) (norm_nonneg _))) hdF
    (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _) (norm_nonneg _)) hW0)

theorem measurable_i12HSD (ε : ℂ) : Measurable fun p : ℝ × ℝ => i12HSD ε p.1 p.2 := by
  unfold i12HSD i12Phi0
  refine Measurable.sub (by fun_prop) (Measurable.ite ?_ measurable_const (by fun_prop))
  exact measurableSet_lt measurable_fst measurable_const

theorem measurable_i12HSGood (ε : ℂ) :
    Measurable fun z : ℝ × ℝ × ℝ => i12HSGood ε z.1 z.2.1 z.2.2 := by
  have hm1 : Measurable fun z : ℝ × ℝ × ℝ => (z.2.1, i12HSk z.2.2 / i12H z.1) := by
    unfold i12HSk i12H; fun_prop
  have hm2 : Measurable fun z : ℝ × ℝ × ℝ => (z.2.1, i12HSk z.2.2 / i12H 0) := by
    unfold i12HSk i12H; fun_prop
  have h1 : Measurable fun z : ℝ × ℝ × ℝ => i12HSD ε z.2.1 (i12HSk z.2.2 / i12H z.1)  := by
    have := (measurable_i12HSD ε).comp hm1; exact this
  have h2 : Measurable fun z : ℝ × ℝ × ℝ => i12HSD ε z.2.1 (i12HSk z.2.2 / i12H 0)  := by
    have := (measurable_i12HSD ε).comp hm2; exact this
  have h3 : Measurable fun z : ℝ × ℝ × ℝ => ((i12H z.1 : ℝ) : ℂ) ^ (-ε - 1) := by
    unfold i12H; fun_prop
  have h4 : Measurable fun z : ℝ × ℝ × ℝ =>
      (z.1 : ℂ) ^ (ε - 1) * (z.2.1 : ℂ) ^ (2 * ε - 1) * i12HSw ε z.2.2 := by
    unfold i12HSw; fun_prop
  have h5 : Measurable fun _ : ℝ × ℝ × ℝ => ((i12H 0 : ℝ) : ℂ) ^ (-ε - 1) := measurable_const
  simp only [i12HSGood]
  exact h4.mul ((h3.mul h1).sub (h5.mul h2))

/-- **The majorant is integrable** on `(0, 1) × (0, ∞) × (0, 1)`. -/
theorem integrableOn_i12HSGoodMaj :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSGoodMaj z.1 z.2.1 z.2.2)
      (Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1)) := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (-(4 / 5) : ℝ)) (Ioo 0 1) :=
    integrableOn_rpow_Ioo (by norm_num)
  have h2 : IntegrableOn (fun s : ℝ => if s < 1 then s ^ (-(4 / 5) : ℝ) else s ^ (-(6 / 5) : ℝ))
      (Ioi 0) := by
    rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
    refine IntegrableOn.union ?_ ?_
    · exact (integrableOn_rpow_Ioo (a := -(4 / 5)) (by norm_num)).congr_fun
        (fun s hs => by simp only [hs.2, ↓reduceIte]) measurableSet_Ioo
    · refine ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => t ^ (-(6 / 5) : ℝ))).2
        (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).congr_fun (fun s hs => ?_)
        measurableSet_Ici
      simp only [not_lt.2 (mem_Ici.1 hs), ↓reduceIte]
  have h3 : IntegrableOn (fun u : ℝ => u ^ (-(3 / 5) : ℝ) * (1 - u) ^ (-(3 / 5) : ℝ))
      (Ioo 0 1) := by
    have := (i12HS_beta_unit (p := ((-(3 / 5) : ℝ) : ℂ)) (q := ((-(3 / 5) : ℝ) : ℂ))
      (by simp only [ofReal_re]; norm_num) (by simp only [ofReal_re]; norm_num)).1.norm
    refine IntegrableOn.congr_fun this (fun u hu => ?_) measurableSet_Ioo
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu.1,
      norm_cpow_eq_rpow_re_of_pos (by linarith [hu.2] : (0 : ℝ) < 1 - u), ofReal_re]
  unfold IntegrableOn
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  exact (Integrable.mul_prod h1 (Integrable.mul_prod h2 h3)).const_mul 24000

end QED.ThreeLoopD
