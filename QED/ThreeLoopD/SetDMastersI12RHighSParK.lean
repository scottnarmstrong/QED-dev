/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ParamHPLLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Set (d), master `I₁₂`: the weight-2 kernel integral of `K₁`

The order-1 coefficient `K₁` of the parametric integral `K` of the piece `Qreg` of the bad part
reduces (by an integration by parts in `σ = 1 - ρ`) to elementary functions and the single
integral (`x ∈ (0, 1)`, `A(σ) = artanh σ = (log (1 + σ) - log (1 - σ))/2`)

  `W(x) = ∫₀¹ A(σ) x²σ/(1 - x²σ²) dσ = log² ((1 - x)/(1 + x)) / 8`

(`i12HSQKW_eq`), proved by the differential-equation method of `QED.Polylog.ParamHPL`: the
`x`-derivative of `W` is reduced by an integration by parts to
`log ((1 + x)/(1 - x)) / (2(1 - x²))`, and `W → 0` as `x → 0⁺`.

## Main definitions

* `QED.ThreeLoopD.i12HSQKA`: `A(σ) = (log (1 + σ) - log (1 - σ))/2`.
* `QED.ThreeLoopD.i12HSQKW`: `W(x)`.

## Main results

* `QED.ThreeLoopD.i12HSQKW_eq`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ThreeLoopD

open QED.Polylog.ParamHPL

/-- `A(σ) = artanh σ = (log (1 + σ) - log (1 - σ))/2`. -/
noncomputable def i12HSQKA (σ : ℝ) : ℝ := (log (1 + σ) - log (1 - σ)) / 2

/-- `W(x) = ∫₀¹ A(σ) x²σ/(1 - x²σ²) dσ`. -/
noncomputable def i12HSQKW (x : ℝ) : ℝ :=
  ∫ σ in Ioo (0 : ℝ) 1, i12HSQKA σ * (x ^ 2 * σ / (1 - x ^ 2 * σ ^ 2))

theorem i12HSQKA_zero : i12HSQKA 0 = 0 := by simp [i12HSQKA]

theorem hasDerivAt_i12HSQKA {σ : ℝ} (h0 : -1 < σ) (h1 : σ < 1) :
    HasDerivAt i12HSQKA (1 / (1 - σ ^ 2)) σ := by
  have a : 0 < 1 + σ := by linarith
  have b : 0 < 1 - σ := by linarith
  have da : HasDerivAt (fun σ => 1 + σ) 1 σ := by simpa using (hasDerivAt_id σ).const_add 1
  have db : HasDerivAt (fun σ => 1 - σ) (-1) σ := by simpa using (hasDerivAt_id σ).const_sub 1
  have h := ((da.log a.ne').sub (db.log b.ne')).div_const 2
  refine h.congr_deriv ?_
  have hs : 1 - σ ^ 2 = (1 - σ) * (1 + σ) := by ring
  rw [hs]
  field_simp
  ring

/-- `|A(σ)| ≤ log 2 + |log σ| + |log (1 - σ)|` on `(0, 1)`. -/
theorem abs_i12HSQKA_le {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |i12HSQKA σ| ≤ (log 2 + |log σ| + |log (1 - σ)|) ^ 1 := by
  have a0 : 0 ≤ log (1 + σ) := log_nonneg (by linarith [hσ.1])
  have a1 : log (1 + σ) ≤ log 2 := log_le_log (by linarith [hσ.1]) (by linarith [hσ.2])
  have hl := neg_abs_le (log (1 - σ))
  have hl' := le_abs_self (log (1 - σ))
  have hv := abs_nonneg (log σ)
  have l2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  unfold i12HSQKA
  rw [pow_one, abs_le]
  constructor <;> linarith

theorem continuousAt_i12HSQKA {σ : ℝ} (h0 : -1 < σ) (h1 : σ < 1) :
    ContinuousAt i12HSQKA σ :=
  (hasDerivAt_i12HSQKA h0 h1).continuousAt

theorem i12HSQK_log_two_nonneg : (0 : ℝ) ≤ log 2 := log_nonneg (by norm_num)

/-- `∂ₓ (x²σ/(1 - x²σ²)) = 2xσ/(1 - x²σ²)²`. -/
theorem hasDerivAt_i12HSQKW_kernel {x σ : ℝ} (h : 0 < 1 - x ^ 2 * σ ^ 2) :
    HasDerivAt (fun x => x ^ 2 * σ / (1 - x ^ 2 * σ ^ 2)) (2 * x * σ / (1 - x ^ 2 * σ ^ 2) ^ 2)
      x := by
  have d1 : HasDerivAt (fun x => x ^ 2 * σ) (2 * x * σ) x := by
    simpa using ((hasDerivAt_pow 2 x).mul_const σ)
  have d2 : HasDerivAt (fun x => 1 - x ^ 2 * σ ^ 2) (-(2 * x * σ ^ 2)) x := by
    simpa using ((hasDerivAt_pow 2 x).mul_const (σ ^ 2)).const_sub 1
  have hd := d1.div d2 h.ne'
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem i12HSQK_one_sub_sq_pos {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    0 < 1 - x ^ 2 * σ ^ 2 := by
  have : x ^ 2 * σ ^ 2 < 1 := by
    have h1 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    have h2 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
    nlinarith [sq_nonneg x, sq_nonneg σ]
  linarith

theorem i12HSQK_one_sub_sq_ge {x σ b : ℝ} (hx0 : 0 ≤ x) (hxb : x ≤ b) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    1 - b ^ 2 ≤ 1 - x ^ 2 * σ ^ 2 := by
  have h2 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have h3 : x ^ 2 ≤ b ^ 2 := by nlinarith
  nlinarith [sq_nonneg x, sq_nonneg σ]

theorem i12HSQKW_aux1 {x σ : ℝ} (hx : x ≠ 0) (hs : 1 - σ ^ 2 ≠ 0) (hq : 1 - x ^ 2 ≠ 0)
    (hp : 1 - x ^ 2 * σ ^ 2 ≠ 0) :
    1 / (1 - σ ^ 2) * ((1 / (1 - x ^ 2 * σ ^ 2) - 1 / (1 - x ^ 2)) / x) =
      -(x / ((1 - x ^ 2) * (1 - x ^ 2 * σ ^ 2))) := by
  rw [div_sub_div _ _ hp hq]
  field_simp
  ring

theorem i12HSQKW_aux2 {x σ : ℝ} (hx : x ≠ 0) (hq : 1 - x ^ 2 ≠ 0)
    (hp : 1 - x ^ 2 * σ ^ 2 ≠ 0) :
    (1 / (1 - x ^ 2 * σ ^ 2) - 1 / (1 - x ^ 2)) / x =
      -(1 - σ) * (x * (1 + σ) / ((1 - x ^ 2 * σ ^ 2) * (1 - x ^ 2))) := by
  rw [div_sub_div _ _ hp hq]
  field_simp
  ring

/-- The `x`-derivative of `W` after integration by parts:
`∫₀¹ A(σ) 2xσ/(1 - x²σ²)² dσ = (log (1 + x) - log (1 - x))/(2(1 - x²))`. -/
theorem integral_i12HSQKW_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ σ in Ioo (0 : ℝ) 1, i12HSQKA σ * (2 * x * σ / (1 - x ^ 2 * σ ^ 2) ^ 2) =
      (log (1 + x) - log (1 - x)) / (2 * (1 - x ^ 2)) := by
  have hx0 := hx.1
  have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.2]
  set g : ℝ → ℝ := fun σ => i12HSQKA σ * (2 * x * σ / (1 - x ^ 2 * σ ^ 2) ^ 2) with hg
  set k : ℝ → ℝ := fun σ => x / ((1 - x ^ 2) * (1 - x ^ 2 * σ ^ 2)) with hk
  set h : ℝ → ℝ := fun σ => i12HSQKA σ * ((1 / (1 - x ^ 2 * σ ^ 2) - 1 / (1 - x ^ 2)) / x)
    with hh
  set D : ℝ := 2 / (1 - x ^ 2) ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hkc : ContinuousOn k (Icc 0 1) := fun σ hσ => by
    have := (i12HSQK_one_sub_sq_pos hx hσ).ne'
    exact ContinuousAt.continuousWithinAt (by rw [hk]; fun_prop (disch := positivity))
  have hki : IntegrableOn k (Ioo 0 1) :=
    (hkc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  have hgi : IntegrableOn g (Ioo 0 1) := by
    refine integrableOn_Ioo_of_abs_le_logs i12HSQK_log_two_nonneg hD0 1
      ((continuousOn_of_forall_continuousAt fun σ hσ => ?_).aestronglyMeasurable
        measurableSet_Ioo) fun σ hσ => ?_
    · have := (i12HSQK_one_sub_sq_pos hx (Ioo_subset_Icc_self hσ)).ne'
      exact (continuousAt_i12HSQKA (by linarith [hσ.1]) hσ.2).mul
        (by fun_prop (disch := positivity))
    · have hp := i12HSQK_one_sub_sq_pos hx (Ioo_subset_Icc_self hσ)
      have hge := i12HSQK_one_sub_sq_ge hx0.le le_rfl (Ioo_subset_Icc_self hσ)
      rw [hg, abs_mul]
      refine (mul_le_mul_of_nonneg_left (c := D) ?_ (abs_nonneg _)).trans ?_
      · rw [abs_of_nonneg (by have := hσ.1; positivity), hD]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : (1 - x ^ 2) ^ 2 ≤ (1 - x ^ 2 * σ ^ 2) ^ 2 := pow_le_pow_left₀ hx2.le hge 2
        nlinarith [hσ.1, hσ.2, mul_pos hx0 hσ.1, sq_nonneg (1 - x ^ 2)]
      · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (abs_i12HSQKA_le hσ) hD0
  have hd : ∀ σ ∈ Ioo (0 : ℝ) 1, HasDerivAt h (g σ - k σ) σ := fun σ hσ => by
    have hp := i12HSQK_one_sub_sq_pos hx (Ioo_subset_Icc_self hσ)
    have hs : 0 < 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
    have d2 : HasDerivAt (fun σ => 1 - x ^ 2 * σ ^ 2) (-(x ^ 2 * (2 * σ))) σ := by
      simpa using ((hasDerivAt_pow 2 σ).const_mul (x ^ 2)).const_sub 1
    have dq := (((hasDerivAt_const σ (1 : ℝ)).div d2 hp.ne').sub_const
      (1 / (1 - x ^ 2))).div_const x
    have hd := (hasDerivAt_i12HSQKA (by linarith [hσ.1]) hσ.2).mul dq
    refine hd.congr_deriv ?_
    rw [hg, hk]
    simp only [Pi.div_apply]
    rw [i12HSQKW_aux1 hx0.ne' hs.ne' hx2.ne' hp.ne']
    have e : (0 * (1 - x ^ 2 * σ ^ 2) - 1 * -(x ^ 2 * (2 * σ))) / (1 - x ^ 2 * σ ^ 2) ^ 2 / x =
        2 * x * σ / (1 - x ^ 2 * σ ^ 2) ^ 2 := by
      field_simp
      ring
    rw [e]
    ring
  have hla : Tendsto h (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt h 0 := by
      have h1 : (1 : ℝ) - x ^ 2 * 0 ^ 2 ≠ 0 := by simp
      exact (continuousAt_i12HSQKA (by norm_num) (by norm_num)).mul
        (by fun_prop (disch := first | exact h1 | exact hx2.ne' | exact hx0.ne'))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hh, i12HSQKA_zero] using this
  have hlb : Tendsto h (𝓝[<] 1) (𝓝 0) := by
    have ht := tendsto_one_sub_mul_of_abs_le_logs (n := 1) i12HSQK_log_two_nonneg hD0
      (f := fun σ => -(i12HSQKA σ * (x * (1 + σ) / ((1 - x ^ 2 * σ ^ 2) * (1 - x ^ 2)))))
      fun σ hσ => by
        have hp := i12HSQK_one_sub_sq_pos hx (Ioo_subset_Icc_self hσ)
        have hge := i12HSQK_one_sub_sq_ge hx0.le le_rfl (Ioo_subset_Icc_self hσ)
        rw [abs_neg, abs_mul, mul_comm]
        refine mul_le_mul ?_ (abs_i12HSQKA_le hσ) (abs_nonneg _) hD0
        rw [abs_of_nonneg (by have := hσ.1; positivity), hD,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : (1 - x ^ 2) * (1 - x ^ 2) ≤ (1 - x ^ 2 * σ ^ 2) * (1 - x ^ 2) :=
          mul_le_mul_of_nonneg_right hge hx2.le
        nlinarith [hσ.1, hσ.2, hx.2, mul_pos hx0 hσ.1]
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
    have hp := i12HSQK_one_sub_sq_pos hx (Ioo_subset_Icc_self hσ)
    rw [hh]
    simp only
    rw [i12HSQKW_aux2 hx0.ne' hx2.ne' hp.ne']
    ring
  have key := setIntegral_Ioo_eq_add_of_eq_add_deriv (f := g) (k := k) (h := h)
    (h' := fun σ => g σ - k σ) zero_lt_one (fun σ _ => by ring) hki hd (hgi.sub hki) hla hlb
  have hkc' : ContinuousOn k (uIcc 0 1) := by rw [uIcc_of_le zero_le_one]; exact hkc
  have hprim : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun σ => (log (1 + x * σ) - log (1 - x * σ)) / (2 * (1 - x ^ 2))) (k σ) σ := by
    intro σ hσ
    rw [uIcc_of_le zero_le_one] at hσ
    have hp := i12HSQK_one_sub_sq_pos hx hσ
    have a : 0 < 1 + x * σ := by nlinarith [hσ.1]
    have b : 0 < 1 - x * σ := by nlinarith [hσ.2, hx.2, hσ.1]
    have da : HasDerivAt (fun σ => 1 + x * σ) x σ := by
      simpa using ((hasDerivAt_id σ).const_mul x).const_add 1
    have db : HasDerivAt (fun σ => 1 - x * σ) (-x) σ := by
      simpa using ((hasDerivAt_id σ).const_mul x).const_sub 1
    have hd := ((da.log a.ne').sub (db.log b.ne')).div_const (2 * (1 - x ^ 2))
    refine hd.congr_deriv ?_
    rw [hk]
    have e : 1 - x ^ 2 * σ ^ 2 = (1 + x * σ) * (1 - x * σ) := by ring
    simp only
    rw [e]
    field_simp
    ring
  rw [key, sub_self, add_zero, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hkc'.intervalIntegrable]
  simp

/-- The bound `|A(σ) x²σ/(1 - x²σ²)| ≤ (1 - b²)⁻¹ (log 2 + |log σ| + |log (1 - σ)|)` for
`0 ≤ x ≤ b < 1`. -/
theorem abs_i12HSQKW_integrand_le {x σ b : ℝ} (hx0 : 0 ≤ x) (hxb : x ≤ b) (hb : b < 1)
    (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |i12HSQKA σ * (x ^ 2 * σ / (1 - x ^ 2 * σ ^ 2))| ≤
      (1 - b ^ 2)⁻¹ * (log 2 + |log σ| + |log (1 - σ)|) ^ 1 := by
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith
  have hge := i12HSQK_one_sub_sq_ge hx0 hxb (Ioo_subset_Icc_self hσ)
  rw [abs_mul, mul_comm]
  refine mul_le_mul ?_ (abs_i12HSQKA_le hσ) (abs_nonneg _) (by positivity)
  have hp : 0 < 1 - x ^ 2 * σ ^ 2 := by linarith
  rw [abs_of_nonneg (div_nonneg (by have := hσ.1; positivity) hp.le), div_le_iff₀ hp]
  have h1 : x ^ 2 ≤ b ^ 2 := by nlinarith
  have h2 : x ^ 2 * σ ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have h3 : 1 ≤ (1 - b ^ 2)⁻¹ * (1 - x ^ 2 * σ ^ 2) := by
    rw [inv_mul_eq_div, le_div_iff₀ hb2]; linarith
  linarith

theorem continuousAt_i12HSQKW_integrand {x σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hxσ : 0 < 1 - x ^ 2 * σ ^ 2) :
    ContinuousAt (fun σ => i12HSQKA σ * (x ^ 2 * σ / (1 - x ^ 2 * σ ^ 2))) σ := by
  have := hxσ.ne'
  exact (continuousAt_i12HSQKA (by linarith [hσ.1]) hσ.2).mul (by fun_prop (disch := assumption))

/-- **`W(x) = log² ((1 - x)/(1 + x)) / 8`** on `(0, 1)`. -/
theorem i12HSQKW_eq_log {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i12HSQKW x = (log (1 - x) - log (1 + x)) ^ 2 / 8 := by
  refine eqOn_setIntegral_of_hasDerivAt_left
    (g := fun σ x => i12HSQKA σ * (x ^ 2 * σ / (1 - x ^ 2 * σ ^ 2)))
    (g' := fun σ x => i12HSQKA σ * (2 * x * σ / (1 - x ^ 2 * σ ^ 2) ^ 2))
    (G := fun x => (log (1 - x) - log (1 + x)) ^ 2 / 8)
    measurableSet_Ioo (p := 0) (q := 1) (c := 0) zero_lt_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x hx
  · intro y hy
    exact (continuousOn_of_forall_continuousAt fun σ hσ =>
      continuousAt_i12HSQKW_integrand hσ
        (i12HSQK_one_sub_sq_pos hy (Ioo_subset_Icc_self hσ))).aestronglyMeasurable measurableSet_Ioo
  · intro y hy
    have hb2 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    exact integrableOn_Ioo_of_abs_le_logs i12HSQK_log_two_nonneg (by positivity) 1
      ((continuousOn_of_forall_continuousAt fun σ hσ =>
        continuousAt_i12HSQKW_integrand hσ
        (i12HSQK_one_sub_sq_pos hy (Ioo_subset_Icc_self hσ))).aestronglyMeasurable
        measurableSet_Ioo) fun σ hσ => abs_i12HSQKW_integrand_le hy.1.le le_rfl hy.2 hσ
  · intro y hy
    refine (continuousOn_of_forall_continuousAt fun σ hσ => ?_).aestronglyMeasurable
      measurableSet_Ioo
    have := (i12HSQK_one_sub_sq_pos hy (Ioo_subset_Icc_self hσ)).ne'
    exact (continuousAt_i12HSQKA (by linarith [hσ.1]) hσ.2).mul
      (by fun_prop (disch := first | assumption | exact pow_ne_zero 2 this))
  · intro x₀ hx₀
    set b := (1 + x₀) / 2 with hbdef
    have hb : b < 1 := by rw [hbdef]; linarith [hx₀.2]
    have hb2 : 0 < 1 - b ^ 2 := by nlinarith [hx₀.1]
    have hBc : ContinuousOn (fun σ : ℝ =>
        (2 / (1 - b ^ 2) ^ 2) * (log 2 + |log σ| + |log (1 - σ)|) ^ 1) (Ioo 0 1) :=
      continuousOn_of_forall_continuousAt fun σ hσ => by
        have h0 : σ ≠ 0 := hσ.1.ne'
        have h1 : 1 - σ ≠ 0 := by linarith [hσ.2]
        fun_prop (disch := assumption)
    refine ⟨(1 - x₀) / 2, by linarith [hx₀.2], fun σ =>
      (2 / (1 - b ^ 2) ^ 2) * (log 2 + |log σ| + |log (1 - σ)|) ^ 1,
      integrableOn_Ioo_of_abs_le_logs i12HSQK_log_two_nonneg (by positivity) 1
        (hBc.aestronglyMeasurable measurableSet_Ioo)
        fun σ _ => (abs_of_nonneg (by positivity)).le, fun σ hσ y hy hyx => ?_⟩
    · have hyb : y ≤ b := by rw [abs_lt] at hyx; rw [hbdef]; linarith
      have hge := i12HSQK_one_sub_sq_ge hy.1.le hyb (Ioo_subset_Icc_self hσ)
      have hp := i12HSQK_one_sub_sq_pos hy (Ioo_subset_Icc_self hσ)
      rw [abs_mul, mul_comm]
      refine mul_le_mul ?_ (abs_i12HSQKA_le hσ) (abs_nonneg _) (by positivity)
      rw [abs_of_nonneg (by have := hσ.1; have := hy.1; positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : (1 - b ^ 2) ^ 2 ≤ (1 - y ^ 2 * σ ^ 2) ^ 2 := pow_le_pow_left₀ hb2.le hge 2
      nlinarith [hσ.1, hσ.2, hy.1, hy.2, mul_pos hy.1 hσ.1, sq_nonneg (1 - b ^ 2)]
  · intro σ hσ y hy
    exact (hasDerivAt_i12HSQKW_kernel
      (i12HSQK_one_sub_sq_pos hy (Ioo_subset_Icc_self hσ))).const_mul _
  · intro y hy
    rw [integral_i12HSQKW_deriv hy]
    have a : 0 < 1 - y := by linarith [hy.2]
    have b : 0 < 1 + y := by linarith [hy.1]
    have da : HasDerivAt (fun y => 1 - y) (-1) y := by simpa using (hasDerivAt_id y).const_sub 1
    have db : HasDerivAt (fun y => 1 + y) 1 y := by simpa using (hasDerivAt_id y).const_add 1
    have hd := (((da.log a.ne').sub (db.log b.ne')).pow 2).div_const 8
    refine hd.congr_deriv ?_
    have e : 1 - y ^ 2 = (1 - y) * (1 + y) := by ring
    simp only [Pi.sub_apply]
    rw [e]
    field_simp
    ring
  · have hb : ∀ᶠ y in 𝓝[>] (0 : ℝ), ∀ σ ∈ Ioo (0 : ℝ) 1,
        |i12HSQKA σ * (y ^ 2 * σ / (1 - y ^ 2 * σ ^ 2))| ≤
          (1 - (1 / 2 : ℝ) ^ 2)⁻¹ * (log 2 + |log σ| + |log (1 - σ)|) ^ 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy σ hσ
      exact abs_i12HSQKW_integrand_le hy.1.le hy.2.le (by norm_num) hσ
    have h := tendsto_setIntegral_param (g := fun σ x => i12HSQKA σ * (x ^ 2 * σ /
      (1 - x ^ 2 * σ ^ 2))) (g₀ := fun _ => 0) measurableSet_Ioo (l := 𝓝[>] (0 : ℝ))
      ?_ hb (integrableOn_Ioo_of_abs_le_logs i12HSQK_log_two_nonneg (by norm_num) 1
        ((continuousOn_of_forall_continuousAt fun σ hσ => by
          have h0 : σ ≠ 0 := hσ.1.ne'
          have h1 : 1 - σ ≠ 0 := by linarith [hσ.2]
          fun_prop (disch := assumption)).aestronglyMeasurable measurableSet_Ioo)
        fun σ _ => (abs_of_nonneg (by positivity)).le) ?_
    · simpa using h
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy
      exact (continuousOn_of_forall_continuousAt fun σ hσ =>
        continuousAt_i12HSQKW_integrand hσ
        (i12HSQK_one_sub_sq_pos hy (Ioo_subset_Icc_self hσ))).aestronglyMeasurable measurableSet_Ioo
    · intro σ hσ
      have hc : ContinuousAt (fun x => i12HSQKA σ * (x ^ 2 * σ / (1 - x ^ 2 * σ ^ 2))) 0 := by
        have h1 : (1 : ℝ) - 0 ^ 2 * σ ^ 2 ≠ 0 := by simp
        exact continuousAt_const.mul (by fun_prop (disch := exact h1))
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  · have hc : ContinuousAt (fun x : ℝ => (log (1 - x) - log (1 + x)) ^ 2 / 8) 0 := by
      have h1 : (1 : ℝ) - 0 ≠ 0 := by norm_num
      have h2 : (1 : ℝ) + 0 ≠ 0 := by norm_num
      fun_prop (disch := assumption)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

end QED.ThreeLoopD
