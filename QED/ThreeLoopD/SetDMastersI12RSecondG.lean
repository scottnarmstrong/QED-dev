/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondK
import QED.Polylog.ExtraIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: the weight-two function `G` and the `θ`-integral of `G(θ q) / θ`

For `M > 0` let

  `G(M) = ∫₀¹ g(M u / (1 - u)) du`   (`QED.ThreeLoopD.i12RG`),

with `g = QED.ThreeLoopD.i12Rg`. Since `g = 3 - 3 r log (1 + 1/r) - 6 log (1 + r) - 3 log (1 + r)/r`
with both `r log (1 + 1/r)` and `log (1 + r) / r` in `[0, 1]`, `|g(r)| ≤ 3 + 6 log (1 + r)`, and
the integrand is dominated by `3 + 6 log (1 + M) - 6 log (1 - u)`.

**The `θ`-integral.** Since `Φ' = g / r` (`QED.ThreeLoopD.hasDerivAt_i12RPhi`), Fubini in
`(θ, u)` and the fundamental theorem of calculus in `θ` give, for `q > 0` and `0 < x < 1`,

  `∫ₓ¹ G(θ q) / θ dθ = K(q) - K(x q)`,

with `K = QED.ThreeLoopD.i12RK`.

## Main results

* `QED.ThreeLoopD.abs_i12Rg_le`, `QED.ThreeLoopD.integrableOn_i12RG`.
* `QED.ThreeLoopD.integral_i12RG_flip`: `∫₀¹ g(M (1 - u) / u) du = G(M)`.
* `QED.ThreeLoopD.integral_i12RG_div`: `∫ₓ¹ G(θ q) / θ dθ = K(q) - K(x q)`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- `G(M) = ∫₀¹ g(M u / (1 - u)) du`. -/
noncomputable def i12RG (M : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, i12Rg (M * u / (1 - u))

theorem measurable_i12Rg : Measurable i12Rg := by
  unfold i12Rg; fun_prop

/-- **The size of `g`**: `|g(r)| ≤ 3 + 6 log (1 + r)` for `r > 0`. -/
theorem abs_i12Rg_le {r : ℝ} (hr : 0 < r) : |i12Rg r| ≤ 3 + 6 * log (1 + r) := by
  have h1 : 0 < 1 + r := by linarith
  have hA0 : 0 ≤ log (1 + r) / r := div_nonneg (log_nonneg (by linarith)) hr.le
  have hA1 : log (1 + r) / r ≤ 1 := by
    rw [div_le_one hr]
    linarith [log_le_sub_one_of_pos h1]
  have hB0 : 0 ≤ r * log ((1 + r) / r) :=
    mul_nonneg hr.le (log_nonneg (by rw [le_div_iff₀ hr]; linarith))
  have hB1 : r * log ((1 + r) / r) ≤ 1 := by
    have := log_le_sub_one_of_pos (div_pos h1 hr)
    have e : r * ((1 + r) / r - 1) = 1 := by field_simp; ring
    nlinarith
  have hL : 0 ≤ log (1 + r) := log_nonneg (by linarith)
  have e : i12Rg r = 3 - 3 * (r * log ((1 + r) / r)) - 6 * log (1 + r) -
      3 * (log (1 + r) / r) := by
    rw [log_div h1.ne' hr.ne']
    simp only [i12Rg]
    field_simp
    ring
  rw [e, abs_le]
  constructor <;> nlinarith

theorem integrableOn_log_one_sub : IntegrableOn (fun u : ℝ => log (1 - u)) (Ioo 0 1) := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
  simp only [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h

/-- The bound of the integrand of `G(M)` and its relatives. -/
theorem abs_i12Rg_mul_le {M u θ : ℝ} (hM : 0 < M) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hθ : θ ∈ Ioc (0 : ℝ) 1) :
    |i12Rg (θ * (M * u / (1 - u)))| ≤ 3 + 6 * log (1 + M) - 6 * log (1 - u) := by
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hr : 0 < M * u / (1 - u) := div_pos (mul_pos hM hu.1) hu1
  have h := abs_i12Rg_le (mul_pos hθ.1 hr)
  obtain ⟨_, hl1⟩ := i12_log_one_add_le hM hu
  have hmono : log (1 + θ * (M * u / (1 - u))) ≤ log (1 + M * u / (1 - u)) :=
    log_le_log (by nlinarith [hθ.1]) (by nlinarith [hθ.2])
  linarith

theorem integrableOn_i12RG_bound {M : ℝ} :
    IntegrableOn (fun u : ℝ => 3 + 6 * log (1 + M) - 6 * log (1 - u)) (Ioo 0 1) :=
  (integrableOn_const (by simp)).sub (integrableOn_log_one_sub.const_mul 6)

/-- The integrand of `G(M)` is integrable on `(0, 1)`. -/
theorem integrableOn_i12RG {M : ℝ} (hM : 0 < M) :
    IntegrableOn (fun u => i12Rg (M * u / (1 - u))) (Ioo 0 1) := by
  refine (integrableOn_i12RG_bound (M := M)).mono'
    ((measurable_i12Rg.comp (by fun_prop)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
  have h := abs_i12Rg_mul_le hM hu ⟨one_pos, le_rfl⟩
  rw [one_mul] at h
  rwa [Real.norm_eq_abs]

/-- **`u ↦ 1 - u`**: `∫₀¹ g(M (1 - u) / u) du = G(M)`. -/
theorem integral_i12RG_flip (M : ℝ) :
    ∫ u in Ioo (0 : ℝ) 1, i12Rg (M * (1 - u) / u) = i12RG M := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, i12RG]
  have h := intervalIntegral.integral_comp_sub_left (fun u => i12Rg (M * u / (1 - u)))
    (a := 0) (b := 1) 1
  simp only [sub_sub_cancel, sub_zero, sub_self] at h
  exact h

theorem integrableOn_i12RG_flip {M : ℝ} (hM : 0 < M) :
    IntegrableOn (fun u => i12Rg (M * (1 - u) / u)) (Ioo 0 1) := by
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 (integrableOn_i12RG hM)
  have h2 := (h.comp_sub_left 1).symm
  simp only [sub_self, sub_zero, sub_sub_cancel] at h2
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h2

/-- **The `θ`-integral of `G(θ q) / θ`**: `∫ₓ¹ G(θ q) / θ dθ = K(q) - K(x q)`. -/
theorem integral_i12RG_div {q x : ℝ} (hq : 0 < q) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun θ => i12RG (θ * q) / θ) (Ioo x 1) ∧
      ∫ θ in Ioo x 1, i12RG (θ * q) / θ = i12RK q - i12RK (x * q) := by
  set F : ℝ × ℝ → ℝ := fun z => i12Rg (z.1 * (q * z.2 / (1 - z.2))) / z.1 with hF
  have hmF : Measurable F := by
    simp only [hF]; exact (measurable_i12Rg.comp (by fun_prop)).div measurable_fst
  have hint : Integrable F
      ((volume.restrict (Ioo x 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    have hb : Integrable (fun z : ℝ × ℝ => (1 / x) * (3 + 6 * log (1 + q) - 6 * log (1 - z.2)))
        ((volume.restrict (Ioo x 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
      have : IsFiniteMeasure (volume.restrict (Ioo x 1)) := by
        rw [isFiniteMeasure_restrict]; exact measure_Ioo_lt_top.ne
      exact (integrable_const (1 / x)).mul_prod integrableOn_i12RG_bound
    refine hb.mono' hmF.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo) fun z hz => ?_
    have hθ : z.1 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hx.1, hz.1.1], hz.1.2.le⟩
    have h := abs_i12Rg_mul_le hq hz.2 hθ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hθ.1, div_le_iff₀ hθ.1]
    have hb0 : 0 ≤ 3 + 6 * log (1 + q) - 6 * log (1 - z.2) := (abs_nonneg _).trans h
    have : 1 / x * z.1 ≥ 1 := by
      rw [ge_iff_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ hx.1]; linarith [hz.1.1]
    nlinarith
  have hslice : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ θ in Ioo x 1, F (θ, u) = i12RPhi (q * u / (1 - u)) - i12RPhi (x * (q * u / (1 - u))) := by
    filter_upwards [hint.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hui hu
    have hr : 0 < q * u / (1 - u) := div_pos (mul_pos hq hu.1) (by linarith [hu.2])
    have hd : ∀ θ ∈ uIcc x 1, HasDerivAt (fun θ => i12RPhi (θ * (q * u / (1 - u))))
        (F (θ, u)) θ := by
      intro θ hθ
      rw [uIcc_of_le hx.2.le] at hθ
      have hθ0 : 0 < θ := by linarith [hx.1, hθ.1]
      have h := (hasDerivAt_i12RPhi (mul_pos hθ0 hr)).comp θ
        ((hasDerivAt_id' θ).mul_const (q * u / (1 - u)))
      refine h.congr_deriv ?_
      have hu0 := hu.1.ne'
      have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
      simp only [hF]
      field_simp
    have hii : IntervalIntegrable (fun θ => F (θ, u)) volume x 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).2 hui
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii, one_mul]
  have hθslice : ∀ θ ∈ Ioo x 1, ∫ u in Ioo (0 : ℝ) 1, F (θ, u) = i12RG (θ * q) / θ := by
    intro θ _
    simp only [hF]
    rw [integral_div, i12RG, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    congr 2
    funext u
    ring_nf
  have hIq := integrableOn_i12RK hq
  have hIx := integrableOn_i12RK (mul_pos hx.1 hq)
  refine ⟨(show IntegrableOn (fun θ => ∫ u in Ioo (0 : ℝ) 1, F (θ, u)) (Ioo x 1) volume from
    hint.integral_prod_left).congr_fun hθslice measurableSet_Ioo, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioo hθslice, integral_integral_swap hint,
    integral_congr_ae hslice]
  have hIx' : IntegrableOn (fun u => i12RPhi (x * (q * u / (1 - u)))) (Ioo 0 1) := by
    refine hIx.congr_fun (fun u _ => ?_) measurableSet_Ioo
    ring_nf
  rw [integral_sub hIq hIx']
  simp only [i12RK, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  congr 2
  funext u
  ring_nf

end QED.ThreeLoopD
