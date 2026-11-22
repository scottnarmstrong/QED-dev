/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5RemTaylor

/-!
# Set (d), master `I₅`: the bound on the integrand of `Rem` on `(0, 1)`

For `‖ε‖ ≤ 1/10` the integrand of the triangle is at most `e ^ (π/20)` times
`U ^ (-4/5) X₀ ^ (-11/10) + U ^ (-6/5) X₀ ^ (-9/10)` (`QED.ThreeLoopD.i5_rpow_pair_le'`). Now
`X₀ ≥ c²` and `X₀ ≥ a t` give `X₀ ≥ (c²) ^ (2/5) (a t) ^ (3/5)`, so these terms are at most
`t ^ (-33/50)` and `t ^ (-27/50)` times `t`-independent integrable products
(`QED.ThreeLoopD.i5TriDomS_le`): `‖i5Tri ε t w‖ ≤ C t ^ (-33/50)` on `0 < t ≤ 1`
(`QED.ThreeLoopD.norm_i5Tri_le_small`). On shell `‖w‖ ≥ t` and `‖w‖ ≥ |im w| = 2 √t |z|`, so
`‖w⁻¹‖ ≤ t ^ (-11/20) |z| ^ (-9/10)` (`QED.ThreeLoopD.norm_inv_i5W_le`), integrable in `z`.
Hence `‖K_ε(t)‖ ≤ C t ^ (-121/100)` (`QED.ThreeLoopD.norm_i5Ker_le_small`), and with
`‖t ^ (1 - ε)‖ ≤ t ^ (9/10)`, `‖b_ε(t)‖ ≤ 2`,

  `‖t ^ (1 - ε) b_ε(t) K_ε(t)‖ ≤ C t ^ (-31/100)` on `(0, 1)`

(`QED.ThreeLoopD.norm_i5RemInt1_le`), the first bound asked for by
`QED.ThreeLoopD.hasTruncLaurent_i5Rem_coeff_of_bound`.

## Main results

* `QED.ThreeLoopD.norm_i5Tri_le_small`, `QED.ThreeLoopD.norm_i5Ker_le_small`.
* `QED.ThreeLoopD.norm_i5RemInt1_le`.
* `QED.ThreeLoopD.hasTruncLaurent_i5Rem_coeff_of_bound₂`,
  `QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_coeff₂`: what remains is the bound on `(1, ∞)`
  and the three coefficients.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-- The power pair at `|σ| ≤ s` is at most its values at `σ = ± s`. -/
theorem i5_rpow_pair_le' {U X : ℝ} (hU : 0 < U) (hX : 0 < X) {σ s : ℝ} (hσ : |σ| ≤ s) :
    U ^ (-1 + 2 * σ) * X ^ (-1 - σ) ≤
      U ^ (-1 + 2 * s) * X ^ (-1 - s) + U ^ (-1 - 2 * s) * X ^ (-1 + s) := by
  simp only [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hX, ← Real.exp_add]
  obtain ⟨hσ1, hσ2⟩ := abs_le.mp hσ
  rcases le_total 0 (2 * Real.log U - Real.log X) with h | h
  · have : Real.log U * (-1 + 2 * σ) + Real.log X * (-1 - σ) ≤
        Real.log U * (-1 + 2 * s) + Real.log X * (-1 - s) := by nlinarith
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have : Real.log U * (-1 + 2 * σ) + Real.log X * (-1 - σ) ≤
        Real.log U * (-1 - 2 * s) + Real.log X * (-1 + s) := by nlinarith
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- The two terms bounding the integrand of the triangle for `|re ε| ≤ 1/10`. -/
noncomputable def i5TriDomS (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  (1 + q.1 + q.2) ^ (-1 + 2 * (1 / 10 : ℝ)) * i5X0 t q ^ (-1 - (1 / 10 : ℝ)) +
    (1 + q.1 + q.2) ^ (-1 - 2 * (1 / 10 : ℝ)) * i5X0 t q ^ (-1 + (1 / 10 : ℝ))

/-- The first `t`-independent product. -/
noncomputable def i5P1 (q : ℝ × ℝ) : ℝ :=
  i5Dom 0 (-(33 / 50)) (-(63 / 50)) q.1 * i5Dom 0 (-(22 / 25)) (-(27 / 25)) q.2

/-- The second `t`-independent product. -/
noncomputable def i5P2 (q : ℝ × ℝ) : ℝ :=
  i5Dom 0 (-(27 / 50)) (-(67 / 50)) q.1 * i5Dom 0 (-(18 / 25)) (-(28 / 25)) q.2

theorem i5TriDomS_le {t : ℝ} (ht : 0 < t) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    i5TriDomS t (a, c) ≤ Real.exp (-(33 / 50) * Real.log t) * i5P1 (a, c) +
      Real.exp (-(27 / 50) * Real.log t) * i5P2 (a, c) := by
  obtain ⟨f1, f2, f3, -, -, -⟩ := i5_log_facts ht ha hc
  have hU : 0 < 1 + a + c := by linarith
  have hX : 0 < i5X0 t (a, c) := i5X0_pos ht ⟨ha, hc⟩
  have g1 : 2 * Real.log c ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_rpow hc, Real.rpow_two]
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  have g2 : Real.log a + Real.log t ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_mul ha.ne' ht.ne']
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  unfold i5TriDomS i5P1 i5P2 i5Dom
  simp only [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hX, ← Real.exp_add]
  refine add_le_add (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) <;>
    apply i5_le_add_min_add_min <;> linarith

theorem integrableOn_i5P1 : IntegrableOn i5P1 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  integrableOn_i5Dom_prod (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem integrableOn_i5P2 : IntegrableOn i5P2 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  integrableOn_i5Dom_prod (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem i5TriDomS_nonneg {t : ℝ} (ht : 0 < t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) : 0 ≤ i5TriDomS t q := by
  have hX := (i5X0_pos ht hq).le
  have hU : 0 ≤ 1 + q.1 + q.2 := by
    obtain ⟨h1, h2⟩ := hq
    simp only [mem_Ioi] at h1 h2
    linarith
  unfold i5TriDomS
  positivity

theorem norm_i5TriF_le_domS {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hw : w.re = t) {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ‖i5TriF ε t w q‖ ≤ Real.exp (Real.pi / 20) * i5TriDomS t q := by
  have hσ : |ε.re| ≤ 1 / 10 := (abs_re_le_norm ε).trans hε
  have hU : 0 < 1 + q.1 + q.2 := by
    obtain ⟨h1, h2⟩ := hq
    simp only [mem_Ioi] at h1 h2
    linarith
  refine (norm_i5TriF_le (by linarith [neg_abs_le ε.re]) ht hw hq).trans ?_
  have he : Real.exp (Real.pi / 2 * ‖ε‖) ≤ Real.exp (Real.pi / 20) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  exact mul_le_mul he (i5_rpow_pair_le' hU (i5X0_pos ht hq) hσ)
    (mul_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg (i5X0_pos ht hq).le _))
    (Real.exp_pos _).le

/-- The constant of the small-`t` bound on the triangle. -/
noncomputable def i5CT : ℝ :=
  Real.exp (Real.pi / 20) * ((∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P1 q) +
    ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P2 q)

/-- **The triangle at small `t`**: `‖i5Tri ε t w‖ ≤ C t ^ (-33/50)` for `0 < t ≤ 1`. -/
theorem norm_i5Tri_le_small {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : w.re = t) : ‖i5Tri ε t w‖ ≤ i5CT * t ^ (-(33 / 50 : ℝ)) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hp : t ^ (-(27 / 50 : ℝ)) ≤ t ^ (-(33 / 50 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have e1 : Real.exp (-(33 / 50) * Real.log t) = t ^ (-(33 / 50 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have e2 : Real.exp (-(27 / 50) * Real.log t) = t ^ (-(27 / 50 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have hB : IntegrableOn (fun q => t ^ (-(33 / 50 : ℝ)) * i5P1 q +
      t ^ (-(27 / 50 : ℝ)) * i5P2 q) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    (integrableOn_i5P1.const_mul _).add (integrableOn_i5P2.const_mul _)
  have hP1 : 0 ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P1 q :=
    setIntegral_nonneg hS fun q _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hP2 : 0 ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P2 q :=
    setIntegral_nonneg hS fun q _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc ‖i5Tri ε t w‖ ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), Real.exp (Real.pi / 20) *
        (t ^ (-(33 / 50 : ℝ)) * i5P1 q + t ^ (-(27 / 50 : ℝ)) * i5P2 q) := by
        refine norm_integral_le_of_norm_le (hB.const_mul _)
          (ae_restrict_of_forall_mem hS fun q hq => ?_)
        refine (norm_i5TriF_le_domS hε ht hw hq).trans ?_
        gcongr
        obtain ⟨a, c⟩ := q
        rw [← e1, ← e2]
        exact i5TriDomS_le ht hq.1 hq.2
    _ = Real.exp (Real.pi / 20) * (t ^ (-(33 / 50 : ℝ)) *
          (∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P1 q) + t ^ (-(27 / 50 : ℝ)) *
          ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P2 q) := by
        rw [integral_const_mul, integral_add (integrableOn_i5P1.const_mul _)
          (integrableOn_i5P2.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ Real.exp (Real.pi / 20) * (t ^ (-(33 / 50 : ℝ)) *
          (∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P1 q) + t ^ (-(33 / 50 : ℝ)) *
          ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P2 q) := by gcongr
    _ = i5CT * t ^ (-(33 / 50 : ℝ)) := by unfold i5CT; ring

/-! ### The angular factor -/

theorem norm_inv_i5W_le {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : z ≠ 0) :
    ‖(i5W t z)⁻¹‖ ≤ t ^ (-(11 / 20 : ℝ)) * |z| ^ (-(9 / 10 : ℝ)) := by
  have hw := i5W_ne_zero ht z
  have hn : 0 < ‖i5W t z‖ := norm_pos_iff.mpr hw
  have hz' : 0 < |z| := abs_pos.mpr hz
  have h1 : Real.log t ≤ Real.log ‖i5W t z‖ := Real.log_le_log ht (le_norm_i5W t z)
  have h2 : Real.log 2 + Real.log t / 2 + Real.log |z| ≤ Real.log ‖i5W t z‖ := by
    have him : 2 * Real.sqrt t * |z| ≤ ‖i5W t z‖ := by
      refine le_trans (le_of_eq ?_) (abs_im_le_norm (i5W t z))
      simp [i5W, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
      ring
    have hs : Real.log (Real.sqrt t) = Real.log t / 2 := by
      rw [Real.log_sqrt ht.le]
    rw [← hs, ← Real.log_mul two_ne_zero (Real.sqrt_pos.mpr ht).ne',
      ← Real.log_mul (by positivity) hz'.ne']
    exact Real.log_le_log (by positivity) him
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [norm_inv, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hz', ← Real.exp_add,
    ← Real.exp_log hn, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr (by linarith)

theorem i5_intervalIntegrable_abs_rpow {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun z : ℝ => |z| ^ r) volume (-1) 1 := by
  have h01 : IntervalIntegrable (fun z : ℝ => |z| ^ r) volume 0 1 := by
    refine (intervalIntegral.intervalIntegrable_rpow' hr).congr_ae ?_
    rw [uIoc_of_le zero_le_one]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun z hz => ?_
    simp [abs_of_pos hz.1]
  have hm : IntervalIntegrable (fun z : ℝ => |z| ^ r) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using h01.symm
  exact hm.trans h01

theorem integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun z : ℝ => |z| ^ r) (Ioo (-1) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
    (i5_intervalIntegrable_abs_rpow hr)

theorem i5Nrm_bound : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ‖i5Nrm ε‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (1 / 10)).exists_bound_of_continuousOn
    fun ε hε => (differentiableAt_i5Nrm (by
      rw [mem_closedBall, dist_zero_right] at hε; linarith)).continuousAt.continuousWithinAt
  exact ⟨C, fun ε hε => hC ε (by rw [mem_closedBall, dist_zero_right]; exact hε)⟩

/-- The integral `∫₋₁¹ |z| ^ (-9/10) dz`. -/
noncomputable def i5AZ : ℝ := ∫ z in Ioo (-1 : ℝ) 1, |z| ^ (-(9 / 10 : ℝ))

/-- **The kernel at small `t`**: `‖K_ε(t)‖ ≤ C_N C_T A t ^ (-121/100)` for `0 < t ≤ 1`. -/
theorem norm_i5Ker_le_small {CN : ℝ} (hN : ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ‖i5Nrm ε‖ ≤ CN) {ε : ℂ}
    (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖i5Ker ε t‖ ≤ CN * (i5CT * i5AZ) * t ^ (-(121 / 100 : ℝ)) := by
  have hI : IntegrableOn (fun z : ℝ => i5CT * t ^ (-(33 / 50 : ℝ)) *
      (t ^ (-(11 / 20 : ℝ)) * |z| ^ (-(9 / 10 : ℝ)))) (Ioo (-1) 1) :=
    ((integrableOn_abs_rpow (by norm_num)).const_mul _).const_mul _
  have hb : ∀ᵐ z ∂(volume.restrict (Ioo (-1 : ℝ) 1)), ‖i5KerF ε t z‖ ≤
      i5CT * t ^ (-(33 / 50 : ℝ)) * (t ^ (-(11 / 20 : ℝ)) * |z| ^ (-(9 / 10 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with z hz hz0
    unfold i5KerF
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    have h1 := norm_i5Wt_le (ε := ε) (by linarith [re_le_norm ε]) hz
    have hT := norm_i5Tri_le_small hε ht ht1 (re_i5W t z)
    have hT0 : 0 ≤ i5CT * t ^ (-(33 / 50 : ℝ)) := (norm_nonneg _).trans hT
    calc ‖((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)‖ * ‖i5Tri ε t (i5W t z)‖ * ‖(i5W t z)⁻¹‖ ≤
          1 * (i5CT * t ^ (-(33 / 50 : ℝ))) *
            (t ^ (-(11 / 20 : ℝ)) * |z| ^ (-(9 / 10 : ℝ))) := by
          gcongr
          exact norm_inv_i5W_le ht hz0
      _ = _ := by ring
  have hK := norm_integral_le_of_norm_le hI hb
  rw [integral_const_mul, integral_const_mul] at hK
  have hp : t ^ (-(33 / 50 : ℝ)) * t ^ (-(11 / 20 : ℝ)) = t ^ (-(121 / 100 : ℝ)) := by
    rw [← Real.rpow_add ht]; norm_num
  rw [i5Ker_eq, norm_mul]
  have hN0 : 0 ≤ CN := (norm_nonneg _).trans (hN 0 (by simp))
  calc ‖i5Nrm ε‖ * ‖∫ z in Ioo (-1 : ℝ) 1, i5KerF ε t z‖ ≤
        CN * (i5CT * t ^ (-(33 / 50 : ℝ)) * (t ^ (-(11 / 20 : ℝ)) * i5AZ)) :=
        mul_le_mul (hN ε hε) hK (norm_nonneg _) hN0
    _ = CN * (i5CT * i5AZ) * (t ^ (-(33 / 50 : ℝ)) * t ^ (-(11 / 20 : ℝ))) := by
        unfold i5AZ; ring
    _ = _ := by rw [hp]

/-- **The bound on `(0, 1)`**: `‖t ^ (1 - ε) b_ε(t) K_ε(t)‖ ≤ C t ^ (-31/100)`. -/
theorem norm_i5RemInt1_le : ∃ C, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 →
    ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t‖ ≤ C * t ^ (-(31 / 100 : ℝ)) := by
  obtain ⟨CN, hN⟩ := i5Nrm_bound
  refine ⟨2 * (CN * (i5CT * i5AZ)), fun t ht ε hε => ?_⟩
  have hre : |ε.re| ≤ 1 / 10 := (abs_re_le_norm ε).trans hε
  have h1 : ‖(t : ℂ) ^ (1 - ε)‖ ≤ t ^ ((9 : ℝ) / 10) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht.1]
    exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by
      simp; linarith [le_abs_self ε.re])
  have h2 : ‖i13Bub ε t‖ ≤ 2 := by
    refine (norm_i13Bub_le ε ht.1.le).trans ?_
    calc (1 + t / 4) ^ ‖ε‖ ≤ (1 + t / 4) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by linarith)
      _ ≤ 2 := by rw [Real.rpow_one]; linarith [ht.2]
  have h3 := norm_i5Ker_le_small hN hε ht.1 ht.2.le
  have hp : t ^ ((9 : ℝ) / 10) * t ^ (-(121 / 100 : ℝ)) = t ^ (-(31 / 100 : ℝ)) := by
    rw [← Real.rpow_add ht.1]; norm_num
  have hK0 : 0 ≤ CN * (i5CT * i5AZ) * t ^ (-(121 / 100 : ℝ)) := (norm_nonneg _).trans h3
  rw [norm_mul, norm_mul]
  calc ‖(t : ℂ) ^ (1 - ε)‖ * ‖i13Bub ε t‖ * ‖i5Ker ε t‖ ≤
        t ^ ((9 : ℝ) / 10) * 2 * (CN * (i5CT * i5AZ) * t ^ (-(121 / 100 : ℝ))) := by
        gcongr
        · exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (by norm_num)
        · exact Real.rpow_nonneg ht.1.le _
    _ = 2 * (CN * (i5CT * i5AZ)) * (t ^ ((9 : ℝ) / 10) * t ^ (-(121 / 100 : ℝ))) := by ring
    _ = _ := by rw [hp]

/-! ### The reduction to the bound on `(1, ∞)` -/

/-- **`Rem` to order `ε²`, given an integrable bound on `(1, ∞)`** on the circle `‖ε‖ = 1/10`. -/
theorem hasTruncLaurent_i5Rem_coeff_of_bound₂ {M₂ : ℝ → ℝ} (hM₂ : IntegrableOn M₂ (Ioi 1))
    (hb₂ : ∀ t ∈ Ioi (1 : ℝ), ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
      ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t‖ ≤ M₂ t) :
    HasTruncLaurent i5Rem (fun ε => ∑ k ∈ Finset.range 3, i5RemCoeff k * ε ^ k) 3 := by
  obtain ⟨C, hC⟩ := norm_i5RemInt1_le
  exact hasTruncLaurent_i5Rem_coeff_of_bound ((integrableOn_rpow_Ioo (by norm_num)).const_mul C)
    hM₂ (fun t ht ε hε => hC t ht ε hε.le) hb₂

section Coeff

open Real QED.Polylog

/-- **The master from the bound on `(1, ∞)` and the coefficients.** -/
theorem hasTruncLaurent_setDMasterI5_of_coeff₂ {M₂ : ℝ → ℝ} (hM₂ : IntegrableOn M₂ (Ioi 1))
    (hb₂ : ∀ t ∈ Ioi (1 : ℝ), ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
      ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t‖ ≤ M₂ t)
    (h0 : i5RemCoeff 0 = -1 / 3 * (π : ℂ) ^ 2 + 3)
    (h1 : i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25)
    (h2 : i5RemCoeff 2 = -29 / 40 * (π : ℂ) ^ 4 + 25 / 6 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      + 4 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 37 / 6 * (π : ℂ) ^ 2 - 36 * (zeta3 : ℂ)
      - 49 / 2 * (zeta5 : ℂ) + 143) :
    HasTruncLaurent setDMasterI5 setDLaurentI5 2 := by
  obtain ⟨C, hC⟩ := norm_i5RemInt1_le
  exact hasTruncLaurent_setDMasterI5_of_coeff ((integrableOn_rpow_Ioo (by norm_num)).const_mul C)
    hM₂ (fun t ht ε hε => hC t ht ε hε.le) hb₂ h0 h1 h2

end Coeff

end QED.ThreeLoopD
