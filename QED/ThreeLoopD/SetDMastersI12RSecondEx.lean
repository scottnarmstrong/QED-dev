/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondR1y
public import QED.ThreeLoopD.SetDMastersI12RSecondTri
import QED.ThreeLoopD.SetDMastersI12RSecondG
import QED.Polylog.LiCalculus
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Deriv

/-!
# Set (d), master `I₁₂`: `E(c)` in one dimension

`E(c) = ∫₀¹ du ∫₀¹ dt (1 - ut) g(ut / ((1 - ut)(1 - u)c)) / t` (`QED.ThreeLoopD.i12RE`).
The substitution `x = ut` (`QED.ThreeLoopD.i12_integral_tri`) gives
`E(c) = ∫₀¹ dx (1 - x)/x ∫ₓ¹ g(k / (1 - θ)) dθ`, `k = x / ((1 - x)c)`, and the inner integral
is `A(k, 1 - x) - A(k, 0⁺)` with the explicit antiderivative `A` (`QED.ThreeLoopD.i12RA`) of
`w ↦ g(k / w)`; its only polylogarithm is `Li₂ (w / (w + k))`, argument in `(0, 1)`.

The integrability of the `E`-part on the square comes from that of the whole integrand of
`R₁'(0)` at fixed `c` and `g ≤ 0`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12RA`, `QED.ThreeLoopD.tendsto_i12RA_zero`.
* `QED.ThreeLoopD.integrable_i12R1Ee`.
* `QED.ThreeLoopD.i12RE_eq`: `E(c) = ∫₀¹ i12REx c x dx`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The `w`-antiderivative `A(k, w)` of `g(k / w)`. -/
noncomputable def i12RA (k w : ℝ) : ℝ :=
  3 * w - 3 / k * (((w ^ 2 - k ^ 2) / 2 + 2 * k * (w + k)) * log (w + k) + k * w / 2 +
    k ^ 2 * Li₂ (w / (w + k)) + k ^ 2 / 2 * log (w + k) ^ 2 - k ^ 2 * log k * log (w + k) -
    (w ^ 2 / 2 + 2 * k * w) * log w)

/-- `A(k, 0⁺)`. -/
noncomputable def i12RA0 (k : ℝ) : ℝ := -(9 / 2) * k * log k + 3 / 2 * k * log k ^ 2

theorem hasDerivAt_i12RA {k w : ℝ} (hk : 0 < k) (hw : 0 < w) :
    HasDerivAt (i12RA k) (i12Rg (k / w)) w := by
  have hwk : 0 < w + k := by linarith
  have hq : w / (w + k) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hw hwk, (div_lt_one hwk).2 (by linarith)⟩
  have hqd : HasDerivAt (fun w => w / (w + k)) (k / (w + k) ^ 2) w := by
    have := (hasDerivAt_id w).div ((hasDerivAt_id w).add_const k) hwk.ne'
    refine this.congr_deriv ?_
    simp only [id]; ring
  have hL := (hasDerivAt_Li₂' hq).comp w hqd
  have hl := ((hasDerivAt_id w).add_const k).log hwk.ne'
  have hlw := Real.hasDerivAt_log hw.ne'
  have hi := hasDerivAt_id w
  have P1 := ((((hi.pow 2).sub_const (k ^ 2)).div_const 2).add
    ((hi.add_const k).const_mul (2 * k))).mul hl
  have P := ((((P1.add ((hi.const_mul k).div_const 2)).add (hL.const_mul (k ^ 2))).add
    ((hl.pow 2).const_mul (k ^ 2 / 2))).sub (hl.const_mul (k ^ 2 * log k))).sub
    ((((hi.pow 2).div_const 2).add (hi.const_mul (2 * k))).mul hlw)
  have h := (hi.const_mul 3).sub (P.const_mul (3 / k))
  convert h using 1
  · funext w; simp [i12RA, Function.comp]
  have e1 : 1 - w / (w + k) = k / (w + k) := by field_simp; ring
  have e2 : 1 + k / w = (w + k) / w := by field_simp
  simp only [i12Rg, id, e1, e2]
  rw [Real.log_div hk.ne' hwk.ne', Real.log_div hwk.ne' hw.ne', Real.log_div hk.ne' hw.ne']
  have := hk.ne'
  have := hw.ne'
  have := hwk.ne'
  generalize log (w + k) = Lwk
  generalize log w = Lw
  generalize log k = Lk
  generalize Li₂ (w / (w + k)) = LL
  norm_num
  field_simp
  ring

theorem tendsto_i12RA_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (i12RA k) (𝓝[>] 0) (𝓝 (i12RA0 k)) := by
  have hq : ContinuousAt (fun w : ℝ => w / (w + k)) 0 :=
    continuousAt_id.div (continuousAt_id.add continuousAt_const) (by simpa using hk.ne')
  have hLi : ContinuousAt (fun w : ℝ => Li₂ (w / (w + k))) 0 :=
    ContinuousAt.comp (g := Li₂) (f := fun w : ℝ => w / (w + k))
      ((hasDerivAt_Li₂_tsum (x := (fun w : ℝ => w / (w + k)) 0) (by simp)).continuousAt) hq
  have hlog : ContinuousAt (fun w : ℝ => log (w + k)) 0 :=
    (continuousAt_id.add continuousAt_const).log (by simpa using hk.ne')
  have hG : ContinuousAt (fun w => 3 * w - 3 / k * (((w ^ 2 - k ^ 2) / 2 + 2 * k * (w + k)) *
      log (w + k) + k * w / 2 + k ^ 2 * Li₂ (w / (w + k)) + k ^ 2 / 2 * log (w + k) ^ 2 -
      k ^ 2 * log k * log (w + k) - (w / 2 + 2 * k) * i12ml w)) 0 := by
    have hm : ContinuousAt i12ml 0 := continuous_i12ml.continuousAt
    fun_prop
  have e : i12RA k = fun w => 3 * w - 3 / k * (((w ^ 2 - k ^ 2) / 2 + 2 * k * (w + k)) *
      log (w + k) + k * w / 2 + k ^ 2 * Li₂ (w / (w + k)) + k ^ 2 / 2 * log (w + k) ^ 2 -
      k ^ 2 * log k * log (w + k) - (w / 2 + 2 * k) * i12ml w) := by
    funext w; simp only [i12RA, i12ml]; ring
  rw [e]
  convert hG.tendsto.mono_left nhdsWithin_le_nhds using 2
  simp only [i12RA0, i12ml, zero_add, zero_div, Li₂_zero, Real.log_zero]
  have := hk.ne'
  field_simp
  ring

theorem i12_tendsto_one_sub_nhdsLT : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := ((continuous_sub_left (1 : ℝ)).tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with θ (hθ : θ < 1)
    exact sub_pos.2 hθ

/-- **The inner integral**: `∫ₓ¹ g(k / (1 - θ)) dθ = A(k, 1 - x) - A(k, 0⁺)`. -/
theorem integrableOn_and_integral_i12Rg_inner {k x : ℝ} (hk : 0 < k) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun θ => i12Rg (k / (1 - θ))) (Ioo x 1) ∧
      ∫ θ in Ioo x 1, i12Rg (k / (1 - θ)) = i12RA k (1 - x) - i12RA0 k := by
  have hd : ∀ θ ∈ Ioo x 1, HasDerivAt (fun θ => -i12RA k (1 - θ)) (i12Rg (k / (1 - θ))) θ := by
    intro θ hθ
    have := ((hasDerivAt_i12RA hk (sub_pos.2 hθ.2)).comp θ
      ((hasDerivAt_id θ).const_sub 1)).neg
    refine this.congr_deriv ?_
    simp
  have hc : ContinuousAt (fun θ => -i12RA k (1 - θ)) x :=
    (((hasDerivAt_i12RA hk (sub_pos.2 hx.2)).continuousAt).comp
      (continuous_sub_left (1 : ℝ)).continuousAt).neg
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonpos' hx.2 hd
    (fun θ hθ => i12Rg_nonpos (div_pos hk (sub_pos.2 hθ.2)))
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
    ((tendsto_i12RA_zero hk).comp i12_tendsto_one_sub_nhdsLT).neg
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).1 hi, ?_⟩
  rw [intervalIntegral.integral_of_le hx.2.le, integral_Ioc_eq_integral_Ioo] at hv
  rw [hv]
  ring

theorem i12R1Ee_nonpos {c t u : ℝ} (hc : 0 < c) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) : i12R1Ee c t u ≤ 0 := by
  have hX1 : 0 < 1 - u * t := by nlinarith [hu.1, hu.2, ht.1, ht.2]
  have hr : 0 < u * t / ((1 - u * t) * (1 - u) * c) :=
    div_pos (mul_pos hu.1 ht.1) (mul_pos (mul_pos hX1 (sub_pos.2 hu.2)) hc)
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hX1.le
    (i12Rg_nonpos hr)) ht.1.le

/-- **Integrability of the `E`-part** on the square, from that of the whole integrand. -/
theorem integrable_i12R1Ee {c : ℝ} (hc : 0 < c)
    (hi : Integrable (fun p : ℝ × ℝ => i12R1d c p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    Integrable (fun p : ℝ × ℝ => i12R1Ee c p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : 0 < 1 / c := by positivity
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => i12R1Ee c p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    (by unfold i12R1Ee i12Rg; fun_prop : Measurable fun p : ℝ × ℝ =>
      i12R1Ee c p.1 p.2).aestronglyMeasurable
  obtain ⟨hUi, -⟩ := intervalIntegrable_and_integral_i12R1U hc
  have hUo : IntegrableOn (i12R1U c) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hUi
  have hK := integrableOn_i12RK hm
  have hsec : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun t => i12R1Ee c t u) (Ioo 0 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ‖i12R1Ee c t u‖ = -(c * ((∫ t in Ioo (0 : ℝ) 1, i12R1d c t u) -
        (i12R1U c u - i12RPhi (1 / c * u / (1 - u)) / c))) := by
    filter_upwards [hi.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu hu'
    have hint : IntervalIntegrable (fun t => i12R1d c t u) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hu
    obtain ⟨h1, h2⟩ := integral_i12R1_t hc hu' hint
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h2
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h1, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonpos (i12R1Ee_nonpos hc ht hu')]), integral_neg, h2]
    have := hc.ne'
    field_simp
    ring
  rw [integrable_prod_iff' hmeas]
  refine ⟨hsec.mono fun u hu => hu.1, ?_⟩
  refine ((((hi.integral_prod_right.sub hUo).add (hK.div_const c)).const_mul c).neg).congr ?_
  filter_upwards [hsec] with u hu
  rw [hu.2]
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
  ring

/-- The `x`-integrand of `E(c)`: `(1 - x)/x (A(k, 1 - x) - A(k, 0⁺))`, `k = x / ((1 - x)c)`. -/
noncomputable def i12REx (c x : ℝ) : ℝ :=
  (1 - x) / x * (i12RA (x / ((1 - x) * c)) (1 - x) - i12RA0 (x / ((1 - x) * c)))

/-- **`E(c)` in one dimension** (`x = ut`, then `θ = u` from `x` to `1`). -/
theorem i12RE_eq {c : ℝ} (hc : 0 < c)
    (hi : Integrable (fun p : ℝ × ℝ => i12R1d c p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    IntegrableOn (i12REx c) (Ioo 0 1) ∧ i12RE c = ∫ x in Ioo (0 : ℝ) 1, i12REx c x := by
  have hEe := integrable_i12R1Ee hc hi
  set ψ : ℝ × ℝ → ℝ := fun q => (1 - q.1) * i12Rg (q.1 / ((1 - q.1) * (1 - q.2) * c)) * q.2 / q.1
    with hψdef
  have hmeas : (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : Measure (ℝ × ℝ)) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i12R1Ee c z.1 z.2 = ψ (z.1 * z.2, z.2) := by
    intro z hz
    have := hz.1.1.ne'
    have := hz.2.1.ne'
    simp only [i12R1Ee, hψdef, mul_comm z.1 z.2]
    field_simp
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hψ : IntegrableOn (fun z : ℝ × ℝ => ψ (z.1 * z.2, z.2))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    have h : IntegrableOn (fun z : ℝ × ℝ => i12R1Ee c z.1 z.2)
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
      rw [IntegrableOn, hmeas]; exact hEe
    exact h.congr_fun hpt hS
  obtain ⟨-, hint, heq⟩ := i12_integral_tri hψ
  have hin : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ θ in Ioo x 1, ψ (x, θ) / θ = i12REx c x := by
    intro x hx
    have hk : 0 < x / ((1 - x) * c) := div_pos hx.1 (mul_pos (sub_pos.2 hx.2) hc)
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun θ => (1 - x) / x *
      i12Rg (x / ((1 - x) * c) / (1 - θ))) (fun θ hθ => ?_), integral_const_mul,
      (integrableOn_and_integral_i12Rg_inner hk hx).2, i12REx]
    have hθ0 : θ ≠ 0 := (hx.1.trans hθ.1).ne'
    have hθ1 : 1 - θ ≠ 0 := (sub_pos.2 hθ.2).ne'
    have e : x / ((1 - x) * (1 - θ) * c) = x / ((1 - x) * c) / (1 - θ) := by
      field_simp
    simp only [hψdef, e]
    field_simp
  refine ⟨hint.congr_fun hin measurableSet_Ioo, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioo hin, ← heq, i12RE,
    setIntegral_congr_fun hS (fun z hz => (hpt z hz).symm), hmeas, integral_prod_symm _ hEe]

end QED.ThreeLoopD
