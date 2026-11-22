/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RestSector
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Set (d), master `I₁₂`: the remainder combination is analytic near `ε = 0`

On the disc `‖ε‖ < 1/100` the integrands of the five remainders of `QED.ThreeLoopD.i12Rest` are
dominated, uniformly in `ε`, by constant multiples of
`∏ (zᵢ (1 - zᵢ)) ^ (-9/10)` (`QED.ThreeLoopD.i12Maj3`, `QED.ThreeLoopD.i12Maj2`):

* `R₁`: `‖W‖ ≤ (c t) ^ (-51/50) (1 - t) ^ (-1/100) (u (1 - u)) ^ (-1/100)` and
  `‖Φ₁(X, Y)‖ ≤ 27 (X Y) ^ (1/4) ≤ 27 (c t) ^ (1/4)`;
* `R_A`, `R_B`: the sector weight `‖ρ ^ (ε - 1) θ ^ (2ε - 1)‖ ≤ ρ ^ (-101/100) θ ^ (-51/50)` times
  the mixed-difference bounds `20000 ρ ^ (1/4) θ ^ (1/8) …` of
  `QED.ThreeLoopD.SetDMastersI12RestSector`, with `(1 - ρθ) ^ (-3/5) ≤ (1 - ρ) ^ (-3/10)
  (1 - θ) ^ (-3/10)`;
* `T_A`, `T_B`: `θ ^ (-51/50)` times `64 · 108 θ ^ (1/4) …`, resp. `64 · 27 θ ^ (1/4) …`.

All integrands are entire in `ε` at each interior point, so each remainder is complex
differentiable on `‖ε‖ < 1/200` (`QED.DimReg.differentiableAt_integral_of_holomorphic`), and so is
`i12Rest`. At `ε = 0`, `Φ₀ = 2 = (2 - 3ε) Y ^ (-3ε)`, so the integrands of `T_A`, `T_B` vanish and
`i12Rest 0 = 0`.

## Main results

* `QED.ThreeLoopD.analyticOnNhd_i12Rest`, `QED.ThreeLoopD.analyticAt_i12Rest`.
* `QED.ThreeLoopD.i12Rest_zero`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric QED.DimReg

namespace QED.ThreeLoopD

/-! ### Converting the pointwise bounds into product majorants -/

/-- `t ^ a (1 - t) ^ b ≤ (t (1 - t)) ^ (-9/10)` on `(0, 1)` for `a, b ≥ -9/10`. -/
theorem i12_cv {t a b : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ha : -(9 / 10) ≤ a) (hb : -(9 / 10) ≤ b) :
    t ^ a * (1 - t) ^ b ≤ (t * (1 - t)) ^ (-(9 / 10) : ℝ) := by
  have h1 : 0 < 1 - t := by linarith [ht.2]
  rw [Real.mul_rpow ht.1.le h1.le]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le ha)
    (Real.rpow_le_rpow_of_exponent_ge h1 (by linarith [ht.1]) hb) (Real.rpow_nonneg h1.le _)
    (Real.rpow_nonneg ht.1.le _)

theorem i12_cv1 {t a : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ha : -(9 / 10) ≤ a) :
    t ^ a ≤ (t * (1 - t)) ^ (-(9 / 10) : ℝ) := by
  have := i12_cv ht ha (le_refl (-(9 / 10) : ℝ))
  have h1 : 0 < 1 - t := by linarith [ht.2]
  have h2 : 1 ≤ (1 - t) ^ (-(9 / 10) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos h1 (by linarith [ht.1]) (by norm_num)
  nlinarith [Real.rpow_nonneg ht.1.le a]

theorem i12_cvU {u c : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hc : u * (1 - u) ≤ c) :
    (u * (1 - u)) ^ (-(1 / 100) : ℝ) * c ^ (-(3 / 4) : ℝ) ≤ (u * (1 - u)) ^ (-(9 / 10) : ℝ) := by
  have hp : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
  have hp1 : u * (1 - u) ≤ 1 := by nlinarith [hu.1, hu.2]
  calc _ ≤ (u * (1 - u)) ^ (-(1 / 100) : ℝ) * (u * (1 - u)) ^ (-(3 / 4) : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hp hc (by norm_num))
          (Real.rpow_nonneg hp.le _)
    _ = (u * (1 - u)) ^ (-(76 / 100) : ℝ) := by rw [← Real.rpow_add hp]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num)

theorem i12_cvL {ρ θ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (1 - ρ * θ) ^ (-(3 / 5) : ℝ) ≤ (1 - ρ) ^ (-(3 / 10) : ℝ) * (1 - θ) ^ (-(3 / 10) : ℝ) := by
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have h2 : 0 < 1 - θ := by linarith [hθ.2]
  have h3 : 0 < 1 - ρ * θ := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  rw [← Real.mul_rpow h1.le h2.le, show (-(3 / 5) : ℝ) = 2 * (-(3 / 10)) by norm_num,
    Real.rpow_mul h3.le, Real.rpow_two]
  have k1 : 1 - ρ ≤ 1 - ρ * θ := by nlinarith [hρ.1, hθ.2]
  have k2 : 1 - θ ≤ 1 - ρ * θ := by nlinarith [hθ.1, hρ.2]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos h1 h2) (by nlinarith [mul_le_mul k1 k2 h2.le h3.le])
    (by norm_num)

theorem i12_rpow_mul_rpow {t a b : ℝ} (ht : 0 < t) : t ^ a * t ^ b = t ^ (a + b) :=
  (Real.rpow_add ht a b).symm

/-! ### The majorants -/

/-- The three-dimensional majorant `∏ (zᵢ (1 - zᵢ)) ^ (-9/10)`. -/
noncomputable def i12Maj3 (z : ℝ × ℝ × ℝ) : ℝ :=
  (z.1 * (1 - z.1)) ^ (-(9 / 10) : ℝ) *
    ((z.2.1 * (1 - z.2.1)) ^ (-(9 / 10) : ℝ) * (z.2.2 * (1 - z.2.2)) ^ (-(9 / 10) : ℝ))

/-- The two-dimensional majorant `∏ (zᵢ (1 - zᵢ)) ^ (-9/10)`. -/
noncomputable def i12Maj2 (z : ℝ × ℝ) : ℝ :=
  (z.1 * (1 - z.1)) ^ (-(9 / 10) : ℝ) * (z.2 * (1 - z.2)) ^ (-(9 / 10) : ℝ)

theorem integrable_i12Maj3 :
    Integrable i12Maj3 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) := by
  rw [volume_restrict_prod3]
  exact (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)))

theorem integrable_i12Maj2 :
    Integrable i12Maj2 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [volume_restrict_prod2]
  exact (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))

/-! ### The dominating bounds -/

section Dom

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100)
include hε

theorem norm_i12SecWt_le {ρ θ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ‖i12SecWt ε ρ θ‖ ≤ ρ ^ (-(101 / 100) : ℝ) * θ ^ (-(102 / 100) : ℝ) := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  rw [i12SecWt, norm_mul]
  exact mul_le_mul (norm_cpow_le_rpow_of_le hρ.1 hρ.2.le (by simp; linarith))
    (norm_cpow_le_rpow_of_le hθ.1 hθ.2.le (by simp; linarith)) (norm_nonneg _)
    (Real.rpow_nonneg hρ.1.le _)

/-- The dominating bound for `R_A`. -/
theorem norm_i12RA3_integrand_le {z : ℝ × ℝ × ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ‖i12SecWt ε z.1 z.2.1 * (i12GA ε z.1 z.2.1 z.2.2 - i12GA ε 0 z.2.1 z.2.2 -
      i12GA0 ε z.1 z.2.2 + i12GA0 ε 0 z.2.2)‖ ≤ 20000 * i12Maj3 z := by
  obtain ⟨hρ, hθ, hu⟩ := hz
  set ρ := z.1
  set θ := z.2.1
  set u := z.2.2
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hρ1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hθ1 : 0 < 1 - θ := by linarith [hθ.2]
  have hρθ : 0 < 1 - ρ * θ := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have hp : 0 < u * (1 - u) := mul_pos hu.1 hu1
  have := hρ.1
  have := hθ.1
  have := hu.1
  have hD := norm_i12RA3_diff_le hε hρ hθ hu
  have hW := norm_i12SecWt_le hε hρ hθ
  have hU := i12_cvU hu (show u * (1 - u) ≤ 1 - u by nlinarith [hu.2])
  have hL := i12_cvL hρ hθ
  rw [norm_mul]
  calc _ ≤ (ρ ^ (-(101 / 100) : ℝ) * θ ^ (-(102 / 100) : ℝ)) *
        (20000 * (ρ ^ (1 / 4 : ℝ) * θ ^ (1 / 8 : ℝ)) * ((u * (1 - u)) ^ (-(1 / 100) : ℝ) *
          (1 - ρ * θ) ^ (-(3 / 5) : ℝ) * (1 - u) ^ (-(3 / 4) : ℝ))) :=
        mul_le_mul hW hD (norm_nonneg _) (by positivity)
    _ = 20000 * ((ρ ^ (-(101 / 100) : ℝ) * ρ ^ (1 / 4 : ℝ)) *
        (θ ^ (-(102 / 100) : ℝ) * θ ^ (1 / 8 : ℝ)) * (1 - ρ * θ) ^ (-(3 / 5) : ℝ) *
        ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(3 / 4) : ℝ))) := by ring
    _ ≤ 20000 * (ρ ^ (-(76 / 100) : ℝ) * θ ^ (-(179 / 200) : ℝ) *
        ((1 - ρ) ^ (-(3 / 10) : ℝ) * (1 - θ) ^ (-(3 / 10) : ℝ)) *
        (u * (1 - u)) ^ (-(9 / 10) : ℝ)) := by
        rw [i12_rpow_mul_rpow hρ.1, i12_rpow_mul_rpow hθ.1]
        norm_num
        gcongr
    _ = 20000 * ((ρ ^ (-(76 / 100) : ℝ) * (1 - ρ) ^ (-(3 / 10) : ℝ)) *
        ((θ ^ (-(179 / 200) : ℝ) * (1 - θ) ^ (-(3 / 10) : ℝ)) *
          (u * (1 - u)) ^ (-(9 / 10) : ℝ))) := by ring
    _ ≤ 20000 * i12Maj3 z := by
        unfold i12Maj3
        gcongr
        · refine i12_cv hρ ?_ ?_ <;> norm_num
        · refine i12_cv hθ ?_ ?_ <;> norm_num

/-- The dominating bound for `R_B`. -/
theorem norm_i12RB3_integrand_le {z : ℝ × ℝ × ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ‖i12SecWt ε z.1 z.2.1 * (i12GB ε z.1 z.2.1 z.2.2 - i12GB ε 0 z.2.1 z.2.2 -
      i12GB0 ε z.1 z.2.2 + i12GB0 ε 0 z.2.2)‖ ≤ 20000 * i12Maj3 z := by
  obtain ⟨hρ, hθ, hu⟩ := hz
  set ρ := z.1
  set θ := z.2.1
  set u := z.2.2
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hρ1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hp : 0 < u * (1 - u) := mul_pos hu.1 hu1
  have := hρ.1
  have := hθ.1
  have := hu.1
  have hD := norm_i12RB3_diff_le hε hρ hθ hu
  have hW := norm_i12SecWt_le hε hρ hθ
  have hU := i12_cvU hu (show u * (1 - u) ≤ u by nlinarith [hu.1])
  rw [norm_mul]
  calc _ ≤ (ρ ^ (-(101 / 100) : ℝ) * θ ^ (-(102 / 100) : ℝ)) *
        (20000 * (ρ ^ (1 / 4 : ℝ) * θ ^ (1 / 8 : ℝ)) * ((u * (1 - u)) ^ (-(1 / 100) : ℝ) *
          (1 - ρ) ^ (-(3 / 5) : ℝ) * u ^ (-(3 / 4) : ℝ))) :=
        mul_le_mul hW hD (norm_nonneg _) (by positivity)
    _ = 20000 * ((ρ ^ (-(101 / 100) : ℝ) * ρ ^ (1 / 4 : ℝ)) * (1 - ρ) ^ (-(3 / 5) : ℝ) *
        ((θ ^ (-(102 / 100) : ℝ) * θ ^ (1 / 8 : ℝ)) *
        ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * u ^ (-(3 / 4) : ℝ)))) := by ring
    _ = 20000 * (ρ ^ (-(76 / 100) : ℝ) * (1 - ρ) ^ (-(3 / 5) : ℝ) *
        (θ ^ (-(179 / 200) : ℝ) * ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * u ^ (-(3 / 4) : ℝ)))) := by
        rw [i12_rpow_mul_rpow hρ.1, i12_rpow_mul_rpow hθ.1,
          show (-(101 / 100) : ℝ) + 1 / 4 = -(76 / 100) by norm_num,
          show (-(102 / 100) : ℝ) + 1 / 8 = -(179 / 200) by norm_num]
    _ ≤ 20000 * i12Maj3 z := by
        unfold i12Maj3
        have := Real.rpow_nonneg (mul_pos hθ.1 (by linarith [hθ.2] : (0 : ℝ) < 1 - θ)).le
          (-(9 / 10) : ℝ)
        gcongr
        · refine i12_cv hρ ?_ ?_ <;> norm_num
        · refine i12_cv1 hθ ?_; norm_num

/-- The dominating bound for `R₁`. -/
theorem norm_i12R1_integrand_le {z : ℝ × ℝ × ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ‖i12Wt ε (z.1 * (1 - z.1)) z.2.1 z.2.2 *
      i12Phi1 ε (z.2.2 * z.2.1) ((1 - z.2.2) * (z.1 * (1 - z.1)))‖ ≤ 27 * i12Maj3 z := by
  obtain ⟨hy, ht, hu⟩ := hz
  set y := z.1
  set t := z.2.1
  set u := z.2.2
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hc : 0 < y * (1 - y) := mul_pos hy.1 (by linarith [hy.2])
  have hc1 : y * (1 - y) ≤ 1 := by nlinarith [hy.1, hy.2]
  have hp : 0 < u * (1 - u) := mul_pos hu.1 hu1
  have hp1 : u * (1 - u) ≤ 1 := by nlinarith [hu.1, hu.2]
  have hct : 0 < y * (1 - y) * t := mul_pos hc ht.1
  have hct1 : y * (1 - y) * t ≤ 1 := by nlinarith [ht.2]
  have hX : 0 < u * t := mul_pos hu.1 ht.1
  have hX1 : u * t ≤ 1 := by nlinarith [hu.2, ht.2, hu.1, ht.1]
  have hY : 0 < (1 - u) * (y * (1 - y)) := mul_pos hu1 hc
  have hY1 : (1 - u) * (y * (1 - y)) ≤ 1 := by nlinarith [hu.1]
  have hW : ‖i12Wt ε (y * (1 - y)) t u‖ ≤ (y * (1 - y) * t) ^ (-(102 / 100) : ℝ) *
      (1 - t) ^ (-(1 / 100) : ℝ) * (u * (1 - u)) ^ (-(1 / 100) : ℝ) := by
    rw [i12Wt, norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (norm_cpow_le_rpow_of_le hct hct1 (by simp; linarith))
      (norm_cpow_le_rpow_of_le ht1 (by linarith [ht.1]) (by simp; linarith)) (norm_nonneg _)
      (Real.rpow_nonneg hct.le _)) (norm_cpow_le_rpow_of_le hp hp1 (by linarith))
      (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hct.le _) (Real.rpow_nonneg ht1.le _))
  have hP : ‖i12Phi1 ε (u * t) ((1 - u) * (y * (1 - y)))‖ ≤
      27 * (y * (1 - y) * t) ^ (1 / 4 : ℝ) := by
    have h1 := norm_i12Phi1_le_left hε hX hY hX1 hY1
    have h2 := norm_i12Phi1_le_right hε hX hY hX1 hY1
    have hXY : u * t * ((1 - u) * (y * (1 - y))) ≤ y * (1 - y) * t := by
      have : u * t * ((1 - u) * (y * (1 - y))) = u * (1 - u) * (y * (1 - y) * t) := by ring
      rw [this]; nlinarith
    refine i12_le_of_sq (norm_nonneg _) (by positivity) h1 h2 ?_
    have e : (27 * (y * (1 - y) * t) ^ (1 / 4 : ℝ)) ^ 2 = 729 * √(y * (1 - y) * t) := by
      rw [mul_pow, ← Real.rpow_natCast ((y * (1 - y) * t) ^ (1 / 4 : ℝ)),
        ← Real.rpow_mul hct.le, Real.sqrt_eq_rpow]; norm_num
    rw [e, show 27 * √(u * t) * (27 * √((1 - u) * (y * (1 - y)))) =
      729 * √(u * t * ((1 - u) * (y * (1 - y)))) by rw [Real.sqrt_mul hX.le]; ring]
    gcongr
  rw [norm_mul]
  calc _ ≤ ((y * (1 - y) * t) ^ (-(102 / 100) : ℝ) * (1 - t) ^ (-(1 / 100) : ℝ) *
        (u * (1 - u)) ^ (-(1 / 100) : ℝ)) * (27 * (y * (1 - y) * t) ^ (1 / 4 : ℝ)) :=
        mul_le_mul hW hP (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.rpow_nonneg hct.le _)
          (Real.rpow_nonneg ht1.le _)) (Real.rpow_nonneg hp.le _))
    _ = 27 * (((y * (1 - y) * t) ^ (-(102 / 100) : ℝ) * (y * (1 - y) * t) ^ (1 / 4 : ℝ)) *
        (1 - t) ^ (-(1 / 100) : ℝ) * (u * (1 - u)) ^ (-(1 / 100) : ℝ)) := by ring
    _ = 27 * ((y * (1 - y)) ^ (-(77 / 100) : ℝ) * (t ^ (-(77 / 100) : ℝ) *
        (1 - t) ^ (-(1 / 100) : ℝ)) * (u * (1 - u)) ^ (-(1 / 100) : ℝ)) := by
        rw [i12_rpow_mul_rpow hct, show (-(102 / 100) : ℝ) + 1 / 4 = -(77 / 100) by norm_num,
          Real.mul_rpow hc.le ht.1.le]
        ring
    _ ≤ 27 * i12Maj3 z := by
        have h1 : (y * (1 - y)) ^ (-(77 / 100) : ℝ) ≤ (y * (1 - y)) ^ (-(9 / 10) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hc hc1 (by norm_num)
        have h2 : t ^ (-(77 / 100) : ℝ) * (1 - t) ^ (-(1 / 100) : ℝ) ≤
            (t * (1 - t)) ^ (-(9 / 10) : ℝ) := i12_cv ht (by norm_num) (by norm_num)
        have h3 : (u * (1 - u)) ^ (-(1 / 100) : ℝ) ≤ (u * (1 - u)) ^ (-(9 / 10) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num)
        unfold i12Maj3
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        exact mul_le_mul h1 (mul_le_mul h2 h3 (Real.rpow_nonneg hp.le _)
          (Real.rpow_nonneg (mul_pos ht.1 ht1).le _)) (mul_nonneg (mul_nonneg
            (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg ht1.le _)) (Real.rpow_nonneg hp.le _))
          (Real.rpow_nonneg hc.le _)

/-- The dominating bound for `T_A`. -/
theorem norm_i12TA_integrand_le {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    ‖(z.1 : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)‖ ≤ 6912 * i12Maj2 z := by
  obtain ⟨hθ, hu⟩ := hz
  set θ := z.1
  set u := z.2
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have := hθ.1
  have := hu.1
  have hp : 0 < u * (1 - u) := mul_pos hu.1 hu1
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hX : 0 < u * θ := mul_pos hu.1 hθ.1
  have hX1 : u * θ ≤ 1 := by nlinarith [hu.2, hθ.2, hu.1, hθ.1]
  have hY0 : (1 - u) / 4 ≤ (1 - u) * i12H 0 := by rw [i12H_zero]; nlinarith
  have hY01 : (1 - u) * i12H 0 ≤ 1 := by rw [i12H_zero]; nlinarith [hu.1]
  have e : i12GA ε 0 θ u - i12GA0 ε 0 u = ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) *
      ((u * (1 - u) : ℝ) : ℂ) ^ ε * (i12Phi0 ε (u * θ) ((1 - u) * i12H 0) -
        (2 - 3 * ε) * (((1 - u) * i12H 0 : ℝ) : ℂ) ^ (-3 * ε)) := by
    simp only [i12GA, i12GA0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]; ring
  have hPQ := norm_i12Phi0_sub_le_quarter hε hu1 hY0 hY01 hX hX1
  have hθq : (u * θ) ^ (1 / 4 : ℝ) ≤ θ ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hX.le (by nlinarith [hu.2, hθ.1]) (by norm_num)
  have hU := i12_cvU hu (show u * (1 - u) ≤ 1 - u by nlinarith [hu.2])
  have hw : ‖(θ : ℂ) ^ (2 * ε - 1)‖ ≤ θ ^ (-(102 / 100) : ℝ) :=
    norm_cpow_le_rpow_of_le hθ.1 hθ.2.le (by simp; linarith)
  rw [e, norm_mul, norm_mul, norm_mul]
  calc _ ≤ θ ^ (-(102 / 100) : ℝ) * (64 * (u * (1 - u)) ^ (-(1 / 100) : ℝ) *
        (108 * (θ ^ (1 / 4 : ℝ) * (1 - u) ^ (-(3 / 4) : ℝ)))) := by
        gcongr
        · exact norm_i12_hpow_le hε h0I
        · exact norm_i12_upow_le hε hu
        · exact hPQ.trans (by gcongr)
    _ = 6912 * ((θ ^ (-(102 / 100) : ℝ) * θ ^ (1 / 4 : ℝ)) *
        ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(3 / 4) : ℝ))) := by ring
    _ = 6912 * (θ ^ (-(77 / 100) : ℝ) *
        ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * (1 - u) ^ (-(3 / 4) : ℝ))) := by
        rw [i12_rpow_mul_rpow hθ.1, show (-(102 / 100) : ℝ) + 1 / 4 = -(77 / 100) by norm_num]
    _ ≤ 6912 * i12Maj2 z := by
        unfold i12Maj2
        have h1 : θ ^ (-(77 / 100) : ℝ) ≤ (θ * (1 - θ)) ^ (-(9 / 10) : ℝ) :=
          i12_cv1 hθ (by norm_num)
        have h2 : 0 ≤ (θ * (1 - θ)) ^ (-(9 / 10) : ℝ) :=
          Real.rpow_nonneg (mul_pos hθ.1 (by linarith [hθ.2])).le _
        gcongr

/-- The dominating bound for `T_B`. -/
theorem norm_i12TB_integrand_le {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    ‖(z.1 : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)‖ ≤ 1728 * i12Maj2 z := by
  obtain ⟨hθ, hu⟩ := hz
  set θ := z.1
  set u := z.2
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have := hθ.1
  have := hu.1
  have hp : 0 < u * (1 - u) := mul_pos hu.1 hu1
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hY : 0 < (1 - u) * θ * i12H 0 := by rw [i12H_zero]; nlinarith [mul_pos hu1 hθ.1]
  have hYθ : (1 - u) * θ * i12H 0 ≤ θ := by rw [i12H_zero]; nlinarith [hu.1, hθ.1]
  have e : i12GB ε 0 θ u - i12GB0 ε 0 u = ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) *
      ((u * (1 - u) : ℝ) : ℂ) ^ ε * (i12Phi0 ε u ((1 - u) * θ * i12H 0) -
        (2 - 3 * ε) * (u : ℂ) ^ (-3 * ε)) := by
    simp only [i12GB, i12GB0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]; ring
  have hPQ := norm_i12Phi0_sub_le_mirror hε hu.1 hY hu.2.le (hYθ.trans hθ.2.le)
  have hθq : ((1 - u) * θ * i12H 0) ^ (1 / 4 : ℝ) ≤ θ ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hY.le hYθ (by norm_num)
  have hU := i12_cvU hu (show u * (1 - u) ≤ u by nlinarith [hu.1])
  have hw : ‖(θ : ℂ) ^ (2 * ε - 1)‖ ≤ θ ^ (-(102 / 100) : ℝ) :=
    norm_cpow_le_rpow_of_le hθ.1 hθ.2.le (by simp; linarith)
  rw [e, norm_mul, norm_mul, norm_mul]
  calc _ ≤ θ ^ (-(102 / 100) : ℝ) * (64 * (u * (1 - u)) ^ (-(1 / 100) : ℝ) *
        (27 * (θ ^ (1 / 4 : ℝ) * u ^ (-(3 / 4) : ℝ)))) := by
        gcongr
        · exact norm_i12_hpow_le hε h0I
        · exact norm_i12_upow_le hε hu
        · exact hPQ.trans (by gcongr)
    _ = 1728 * ((θ ^ (-(102 / 100) : ℝ) * θ ^ (1 / 4 : ℝ)) *
        ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * u ^ (-(3 / 4) : ℝ))) := by ring
    _ = 1728 * (θ ^ (-(77 / 100) : ℝ) *
        ((u * (1 - u)) ^ (-(1 / 100) : ℝ) * u ^ (-(3 / 4) : ℝ))) := by
        rw [i12_rpow_mul_rpow hθ.1, show (-(102 / 100) : ℝ) + 1 / 4 = -(77 / 100) by norm_num]
    _ ≤ 1728 * i12Maj2 z := by
        unfold i12Maj2
        have h1 : θ ^ (-(77 / 100) : ℝ) ≤ (θ * (1 - θ)) ^ (-(9 / 10) : ℝ) :=
          i12_cv1 hθ (by norm_num)
        have h2 : 0 ≤ (θ * (1 - θ)) ^ (-(9 / 10) : ℝ) :=
          Real.rpow_nonneg (mul_pos hθ.1 (by linarith [hθ.2])).le _
        gcongr

end Dom

/-! ### Holomorphy and measurability of the integrands -/

section Holo

variable {X Y c t u ρ θ : ℝ}

theorem differentiable_i12Phi0 (hX : 0 < X) (hY : 0 < Y) :
    Differentiable ℂ fun ε => i12Phi0 ε X Y := by
  have := add_pos hX hY
  unfold i12Phi0
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem differentiable_i12Phi1 (hX : 0 < X) (hY : 0 < Y) (hX1 : X < 1) :
    Differentiable ℂ fun ε => i12Phi1 ε X Y := by
  have : 0 < X + Y - X * Y := by nlinarith [mul_pos hY (sub_pos.mpr hX1)]
  have := add_pos hX hY
  unfold i12Phi1
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem differentiable_i12Wt (hc : 0 < c) (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun ε => i12Wt ε c t u := by
  have := mul_pos hc ht.1
  have := sub_pos.mpr ht.2
  have := mul_pos hu.1 (sub_pos.mpr hu.2)
  unfold i12Wt
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem i12H_pos {ρ : ℝ} (hρ : ρ < 2) : 0 < i12H ρ := by unfold i12H; linarith

theorem differentiable_i12GA (hρ : ρ ∈ Ico (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ fun ε => i12GA ε ρ θ u := by
  have h1 := i12H_pos (show ρ < 2 by linarith [hρ.2])
  have h2 : 0 < 1 - ρ * θ := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have h3 := mul_pos hu.1 (sub_pos.mpr hu.2)
  have hP := differentiable_i12Phi0 (mul_pos hu.1 hθ.1) (mul_pos (sub_pos.mpr hu.2) h1)
  unfold i12GA
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem differentiable_i12GA0 (hρ : ρ ∈ Ico (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun ε => i12GA0 ε ρ u := by
  have h1 := i12H_pos (show ρ < 2 by linarith [hρ.2])
  have h3 := mul_pos hu.1 (sub_pos.mpr hu.2)
  have h4 := mul_pos (sub_pos.mpr hu.2) h1
  unfold i12GA0
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem differentiable_i12GB (hρ : ρ ∈ Ico (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ fun ε => i12GB ε ρ θ u := by
  have h1 := i12H_pos (show ρ * θ < 2 by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2])
  have h2 : 0 < 1 - ρ := by linarith [hρ.2]
  have h3 := mul_pos hu.1 (sub_pos.mpr hu.2)
  have hP := differentiable_i12Phi0 hu.1 (mul_pos (mul_pos (sub_pos.mpr hu.2) hθ.1) h1)
  unfold i12GB
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem differentiable_i12GB0 (hρ : ρ ∈ Ico (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun ε => i12GB0 ε ρ u := by
  have h1 := i12H_pos (show (0 : ℝ) < 2 by norm_num)
  have h2 : 0 < 1 - ρ := by linarith [hρ.2]
  have h3 := mul_pos hu.1 (sub_pos.mpr hu.2)
  have h4 := hu.1
  unfold i12GB0
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

theorem differentiable_i12SecWt (hρ : 0 < ρ) (hθ : 0 < θ) :
    Differentiable ℂ fun ε => i12SecWt ε ρ θ := by
  unfold i12SecWt
  fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

end Holo

/-! ### Analyticity -/

theorem i12_ball_small {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    ∀ ε ∈ ball ε₀ (1 / 200), ‖ε‖ < 1 / 100 := fun ε hε => by
  have := norm_sub_norm_le ε ε₀
  rw [mem_ball, dist_eq_norm] at hε
  linarith

theorem i12_measurableSet3 :
    MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)

theorem i12_measurableSet2 : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem differentiableAt_i12R1 {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12R1 ε₀ := by
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 27 * i12Maj3 z) (integrable_i12Maj3.const_mul 27)
    (fun ε _ => (by unfold i12Wt i12Phi1; fun_prop : Measurable fun z : ℝ × ℝ × ℝ =>
      i12Wt ε (z.1 * (1 - z.1)) z.2.1 z.2.2 *
        i12Phi1 ε (z.2.2 * z.2.1) ((1 - z.2.2) * (z.1 * (1 - z.1)))).aestronglyMeasurable)
    ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      norm_i12R1_integrand_le (i12_ball_small h0 ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hy, ht, hu⟩ := hz
    have hc : 0 < z.1 * (1 - z.1) := mul_pos hy.1 (sub_pos.mpr hy.2)
    exact ((differentiable_i12Wt hc ht hu).mul (differentiable_i12Phi1 (mul_pos hu.1 ht.1)
      (mul_pos (sub_pos.mpr hu.2) hc) (by nlinarith [hu.1, hu.2, ht.1, ht.2]))).differentiableOn

theorem differentiableAt_i12RA3 {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12RA3 ε₀ := by
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 20000 * i12Maj3 z) (integrable_i12Maj3.const_mul 20000)
    (fun ε _ => (by unfold i12SecWt i12GA i12GA0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ × ℝ => i12SecWt ε z.1 z.2.1 * (i12GA ε z.1 z.2.1 z.2.2 -
        i12GA ε 0 z.2.1 z.2.2 - i12GA0 ε z.1 z.2.2 + i12GA0 ε 0 z.2.2)).aestronglyMeasurable)
    ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      norm_i12RA3_integrand_le (i12_ball_small h0 ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hρ, hθ, hu⟩ := hz
    have hρ' : z.1 ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    exact ((differentiable_i12SecWt hρ.1 hθ.1).mul
      ((((differentiable_i12GA hρ' hθ hu).sub (differentiable_i12GA h0' hθ hu)).sub
        (differentiable_i12GA0 hρ' hu)).add (differentiable_i12GA0 h0' hu))).differentiableOn

theorem differentiableAt_i12RB3 {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12RB3 ε₀ := by
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 20000 * i12Maj3 z) (integrable_i12Maj3.const_mul 20000)
    (fun ε _ => (by unfold i12SecWt i12GB i12GB0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ × ℝ => i12SecWt ε z.1 z.2.1 * (i12GB ε z.1 z.2.1 z.2.2 -
        i12GB ε 0 z.2.1 z.2.2 - i12GB0 ε z.1 z.2.2 + i12GB0 ε 0 z.2.2)).aestronglyMeasurable)
    ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      norm_i12RB3_integrand_le (i12_ball_small h0 ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hρ, hθ, hu⟩ := hz
    have hρ' : z.1 ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    exact ((differentiable_i12SecWt hρ.1 hθ.1).mul
      ((((differentiable_i12GB hρ' hθ hu).sub (differentiable_i12GB h0' hθ hu)).sub
        (differentiable_i12GB0 hρ' hu)).add (differentiable_i12GB0 h0' hu))).differentiableOn

theorem differentiableAt_i12TA {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12TA ε₀ := by
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 6912 * i12Maj2 z) (integrable_i12Maj2.const_mul 6912)
    (fun ε _ => (by unfold i12GA i12GA0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TA_integrand_le (i12_ball_small h0 ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
    obtain ⟨hθ, hu⟩ := hz
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    have hθ0 := hθ.1
    have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
      fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
    exact (hd.mul ((differentiable_i12GA h0' hθ hu).sub
      (differentiable_i12GA0 h0' hu))).differentiableOn

theorem differentiableAt_i12TB {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12TB ε₀ := by
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 1728 * i12Maj2 z) (integrable_i12Maj2.const_mul 1728)
    (fun ε _ => (by unfold i12GB i12GB0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TB_integrand_le (i12_ball_small h0 ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
    obtain ⟨hθ, hu⟩ := hz
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    have hθ0 := hθ.1
    have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
      fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
    exact (hd.mul ((differentiable_i12GB h0' hθ hu).sub
      (differentiable_i12GB0 h0' hu))).differentiableOn

theorem differentiableAt_i12Rest {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12Rest ε₀ :=
  (((differentiableAt_id.mul (((differentiableAt_i12R1 h0).add
    (differentiableAt_i12RA3 h0)).add (differentiableAt_i12RB3 h0))).add
    (differentiableAt_i12TA h0)).add (differentiableAt_i12TB h0) :)

/-- **The remainder combination is analytic near `0`.** -/
theorem analyticOnNhd_i12Rest : AnalyticOnNhd ℂ i12Rest (ball 0 (1 / 200)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i12Rest
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

theorem analyticAt_i12Rest : AnalyticAt ℂ i12Rest 0 :=
  analyticOnNhd_i12Rest 0 (mem_ball_self (by norm_num))

/-! ### The value at `ε = 0` -/

theorem i12Phi0_zero {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : i12Phi0 0 X Y = 2 := by
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  unfold i12Phi0
  rw [show (2 : ℂ) - 3 * 0 = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, cpow_natCast,
    cpow_natCast]
  push_cast
  field_simp
  ring

theorem i12TA_zero : i12TA 0 = 0 := by
  unfold i12TA
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  obtain ⟨hθ, hu⟩ := hz
  have h1 := i12H_pos (show (0 : ℝ) < 2 by norm_num)
  rw [i12GA, i12GA0, i12Phi0_zero (mul_pos hu.1 hθ.1) (mul_pos (sub_pos.mpr hu.2) h1)]
  simp

theorem i12TB_zero : i12TB 0 = 0 := by
  unfold i12TB
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  obtain ⟨hθ, hu⟩ := hz
  have h1 := i12H_pos (show (0 : ℝ) * z.1 < 2 by norm_num)
  rw [i12GB, i12GB0, i12Phi0_zero hu.1 (mul_pos (mul_pos (sub_pos.mpr hu.2) hθ.1) h1)]
  simp

/-- **The remainder combination vanishes at `ε = 0`.** -/
theorem i12Rest_zero : i12Rest 0 = 0 := by
  rw [i12Rest, i12TA_zero, i12TB_zero]; ring

end QED.ThreeLoopD
