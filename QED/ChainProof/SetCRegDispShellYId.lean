/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellTailQ
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): the two Feynman-parameter identities on the shell

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. On the shell the photon
argument is `a₀(y) = m² y²/(1-y)` (`shellArg`). With `Tail = ∫_a^∞ R_T` and
`T₁ = quadTailVP = ∫_a^∞ R_T(t)/t dt` (`R_T = a Q`), two integrations by parts in `y` give

* **`shell_yId₀`**: `∫₀¹ ((2y - 1) Tail(a₀) + 3m² y² T₁(a₀)) dy = 0`
  (primitive `(y² - y) Tail(a₀) + m² y³ T₁(a₀)`);
* **`shell_yId₁`**:
  `∫₀¹ (Tail(a₀) + m²(4y - 2y²) R_T(a₀) + 2m²(3y² - y) T₁(a₀)) dy = Tail(0)`
  (primitive `(y - 1) Tail(a₀) + m²(2y³ - y²) T₁(a₀)`).

The boundary terms at `y = 1` vanish since both tails tend to `0` at infinity
(`integral_eq_of_hasDerivAt_tendsto`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitVPLink (photonVar photonD)

/-- **The fundamental theorem of calculus with a limit at the right endpoint.** -/
theorem integral_eq_of_hasDerivAt_tendsto {f Φ : ℝ → ℝ} {L : ℝ}
    (hΦ : ∀ y ∈ Ico (0 : ℝ) 1, HasDerivAt Φ (f y) y) (hf : IntervalIntegrable f volume 0 1)
    (hL : Tendsto Φ (𝓝[<] 1) (𝓝 L)) :
    ∫ y in (0 : ℝ)..1, f y = L - Φ 0 := by
  have hprim := intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
  rw [uIcc_of_le zero_le_one] at hprim
  have hlim : Tendsto (fun b => ∫ y in (0 : ℝ)..b, f y) (𝓝[<] 1) (𝓝 (∫ y in (0 : ℝ)..1, f y)) :=
    (hprim 1 (right_mem_Icc.2 zero_le_one)).tendsto.mono_left
      (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Ioo_subset_Icc_self))
  refine tendsto_nhds_unique hlim ((hL.sub_const (Φ 0)).congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with b hb
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hΦ y ?_)
    (hf.mono_set ?_)).symm
  · rw [uIcc_of_le hb.1.le] at hy
    exact ⟨hy.1, hy.2.trans_lt hb.2⟩
  · rw [uIcc_of_le hb.1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hb.2.le

/-- A measurable function bounded on `(0, 1]` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_unit_of_bound {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hb : ∀ y ∈ Ioc (0 : ℝ) 1, ‖g y‖ ≤ C) : IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb))

theorem hasDerivAt_shellArg (m : ℝ) {y : ℝ} (hy : y ≠ 1) :
    HasDerivAt (shellArg m) (m ^ 2 * ((2 * y * (1 - y) + y ^ 2) / (1 - y) ^ 2)) y := by
  have h1 : (1 : ℝ) - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have h := ((hasDerivAt_pow 2 y).div ((hasDerivAt_id y).const_sub 1) h1).const_mul (m ^ 2)
  convert h using 1
  · funext v
    simp only [shellArg, photonVar, Pi.div_apply, id]
  · simp only [id]
    push_cast
    ring

theorem tendsto_shellArg_atTop {m : ℝ} (hm : m ≠ 0) :
    Tendsto (shellArg m) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun y : ℝ => 1 - y) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))).mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 hy
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun y : ℝ => m ^ 2 * y ^ 2) (𝓝[<] 1) (𝓝 (m ^ 2 * 1 ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [one_pow, mul_one] at h3
  refine (h3.pos_mul_atTop (by positivity) h2).congr' (Eventually.of_forall fun y => ?_)
  simp only [shellArg, photonVar, Function.comp]
  ring

section Shell

variable {m mγ Λ T : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T)
  (hab : mγ ^ 2 ≠ Λ ^ 2) (hac : mγ ^ 2 ≠ T * m ^ 2) (hbc : Λ ^ 2 ≠ T * m ^ 2)

include hm hmγ hΛ hT in
theorem hasDerivAt_tail_shellArg {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (fun y => photonTail (vpPhotonT m mγ Λ T) (shellArg m y))
      (-vpPhotonT m mγ Λ T (shellArg m y) *
        (m ^ 2 * ((2 * y * (1 - y) + y ^ 2) / (1 - y) ^ 2))) y := by
  have ha := shellArg_nonneg m (Ico_subset_Icc_self hy)
  have hδ := vpMargin_pos hmγ hΛ hT hm
  exact (hasDerivAt_photonTail_vp hmγ hΛ hT hm (by linarith)).comp y
    (hasDerivAt_shellArg m hy.2.ne)

include hm hmγ hΛ hT hab hac hbc in
theorem hasDerivAt_quad_shellArg {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (fun y => quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y))
      (-bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) *
        (m ^ 2 * ((2 * y * (1 - y) + y ^ 2) / (1 - y) ^ 2))) y := by
  have ha := shellArg_nonneg m (Ico_subset_Icc_self hy)
  exact (hasDerivAt_quadTailVP hab hac hbc (by positivity) (by positivity)
    (by positivity)).comp y (hasDerivAt_shellArg m hy.2.ne)

theorem measurable_quadTailVP (A B U : ℝ) : Measurable (quadTailVP A B U) := by
  unfold quadTailVP
  fun_prop

include hm hmγ hΛ hT hab hac hbc in
theorem intervalIntegrable_quad_shellArg {c : ℝ → ℝ} (hc : Measurable c) {K : ℝ}
    (hK : ∀ y ∈ Ioc (0 : ℝ) 1, ‖c y‖ ≤ K) :
    IntervalIntegrable (fun y => c y * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y))
      volume 0 1 := by
  refine intervalIntegrable_unit_of_bound (hc.mul ((measurable_quadTailVP _ _ _).comp
    (measurable_shellArg m))) (K * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) 0) fun y hy => ?_
  have ha := shellArg_nonneg m (Ioc_subset_Icc_self hy)
  have h0 := quadTailVP_nonneg hab hac hbc (by positivity) (by positivity) (by positivity) ha
  have h1 := quadTailVP_le_at_zero hab hac hbc (by positivity) (by positivity) (by positivity) ha
  rw [norm_mul, Real.norm_of_nonneg h0]
  exact mul_le_mul (hK y hy) h1 h0 ((norm_nonneg _).trans (hK y hy))

include hm hmγ hΛ hT in
theorem intervalIntegrable_tail_shellArg {c : ℝ → ℝ} (hc : Measurable c) {K : ℝ}
    (hK0 : 0 < K) (hK : ∀ y ∈ Ioc (0 : ℝ) 1, ‖c y‖ ≤ K) :
    IntervalIntegrable (fun y => c y * photonTail (vpPhotonT m mγ Λ T) (shellArg m y))
      volume 0 1 := by
  have h := (intervalIntegrable_tail_vp hmγ hΛ hT hm (w := fun y => c y / K)
    (hc.div_const K) fun y hy => by
      rw [norm_div, Real.norm_of_nonneg hK0.le]
      exact (div_le_one hK0).2 (hK y hy)).const_mul K
  refine h.congr fun y _ => ?_
  field_simp

include hm hmγ hΛ hT in
theorem intervalIntegrable_vp_shellArg {c : ℝ → ℝ} (hc : Measurable c) {K : ℝ}
    (hK : ∀ y ∈ Ioc (0 : ℝ) 1, ‖c y‖ ≤ K) :
    IntervalIntegrable (fun y => c y * vpPhotonT m mγ Λ T (shellArg m y)) volume 0 1 := by
  have hmR : Measurable (vpPhotonT m mγ Λ T) :=
    (measurable_vpPhotonT m mγ Λ).comp (measurable_const.prodMk measurable_id)
  refine intervalIntegrable_unit_of_bound (hc.mul (hmR.comp (measurable_shellArg m)))
    (K * (photonK mγ Λ / (T * m ^ 2))) fun y hy => ?_
  have ha := shellArg_nonneg m (Ioc_subset_Icc_self hy)
  have h0 := vpPhotonT_nonneg hmγ hΛ hT hm ha
  have h1 := vpPhotonT_le hmγ hΛ hT hm ha
  have h2 : photonK mγ Λ / (T * m ^ 2) * (1 + shellArg m y ^ 2)⁻¹ ≤
      photonK mγ Λ / (T * m ^ 2) :=
    mul_le_of_le_one_right (div_nonneg (photonK_nonneg mγ Λ) (by positivity))
      (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (shellArg m y)]))
  rw [norm_mul, Real.norm_of_nonneg h0]
  exact mul_le_mul (hK y hy) (h1.trans h2) h0 ((norm_nonneg _).trans (hK y hy))

include hm hmγ hΛ hT hab hac hbc in
/-- **The value identity on the shell**: `∫₀¹ ((2y - 1) Tail(a₀) + 3m² y² T₁(a₀)) dy = 0`. -/
theorem shell_yId₀ :
    ∫ y in (0 : ℝ)..1, ((2 * y - 1) * photonTail (vpPhotonT m mγ Λ T) (shellArg m y) +
      3 * m ^ 2 * y ^ 2 * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y)) = 0 := by
  set Tl := fun y => photonTail (vpPhotonT m mγ Λ T) (shellArg m y) with hTl
  set Qt := fun y => quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) with hQt
  have hU : 0 < T * m ^ 2 := by positivity
  have hd : ∀ y ∈ Ico (0 : ℝ) 1, HasDerivAt (fun y => (y ^ 2 - y) * Tl y + m ^ 2 * y ^ 3 * Qt y)
      ((2 * y - 1) * Tl y + 3 * m ^ 2 * y ^ 2 * Qt y) y := by
    intro y hy
    have h1 : (1 : ℝ) - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy.2.ne)
    have dT := hasDerivAt_tail_shellArg hm hmγ hΛ hT hy
    have dQ := hasDerivAt_quad_shellArg hm hmγ hΛ hT hab hac hbc hy
    have h := (((hasDerivAt_pow 2 y).sub (hasDerivAt_id y)).mul dT).add
      (((hasDerivAt_pow 3 y).const_mul (m ^ 2)).mul dQ)
    convert h using 1
    · funext v
      simp only [hTl, hQt, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id]
    · rw [vpPhotonT_eq_mul_bubQ]
      simp only [hTl, hQt, Pi.sub_apply, id]
      generalize photonTail (vpPhotonT m mγ Λ T) (shellArg m y) = t
      generalize quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) = u
      generalize bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) = q
      simp only [shellArg, photonVar]
      field_simp
      ring
  have hf : IntervalIntegrable (fun y => (2 * y - 1) * Tl y + 3 * m ^ 2 * y ^ 2 * Qt y)
      volume 0 1 := by
    refine (intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun y => 2 * y - 1)
      (by fun_prop) one_pos fun y hy => ?_).add
      (intervalIntegrable_quad_shellArg hm hmγ hΛ hT hab hac hbc
        (c := fun y => 3 * m ^ 2 * y ^ 2) (by fun_prop) (K := 3 * m ^ 2) fun y hy => ?_)
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1, hy.2]
    · rw [Real.norm_of_nonneg (by positivity)]
      have : y ^ 2 ≤ 1 := pow_le_one₀ hy.1.le hy.2
      nlinarith [sq_nonneg m]
  have hL : Tendsto (fun y => (y ^ 2 - y) * Tl y + m ^ 2 * y ^ 3 * Qt y) (𝓝[<] 1) (𝓝 0) := by
    have ha := tendsto_shellArg_atTop hm.ne'
    have hT0 := (tendsto_photonTail_vp_atTop hab hac hbc hmγ hΛ hU).comp ha
    have hQ0 := (tendsto_quadTailVP_atTop hab hac hbc).comp ha
    have hp : Tendsto (fun y : ℝ => y ^ 2 - y) (𝓝[<] 1) (𝓝 (1 ^ 2 - 1)) :=
      (((continuous_pow 2).sub continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
    have hq : Tendsto (fun y : ℝ => m ^ 2 * y ^ 3) (𝓝[<] 1) (𝓝 (m ^ 2 * 1 ^ 3)) :=
      ((continuous_const.mul (continuous_pow 3)).tendsto 1).mono_left nhdsWithin_le_nhds
    have h := (hp.mul hT0).add (hq.mul hQ0)
    simpa using h
  have key := integral_eq_of_hasDerivAt_tendsto hd hf hL
  simp only [hTl, hQt] at key
  rw [key]
  simp [shellArg, photonVar]

include hm hmγ hΛ hT hab hac hbc in
/-- **The slope identity on the shell**:
`∫₀¹ (Tail(a₀) + m²(4y - 2y²) R_T(a₀) + 2m²(3y² - y) T₁(a₀)) dy = Tail(0)`. -/
theorem shell_yId₁ :
    ∫ y in (0 : ℝ)..1, (photonTail (vpPhotonT m mγ Λ T) (shellArg m y) +
      m ^ 2 * (4 * y - 2 * y ^ 2) * vpPhotonT m mγ Λ T (shellArg m y) +
      2 * m ^ 2 * (3 * y ^ 2 - y) * quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y)) =
      photonTail (vpPhotonT m mγ Λ T) 0 := by
  set Tl := fun y => photonTail (vpPhotonT m mγ Λ T) (shellArg m y) with hTl
  set Qt := fun y => quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) with hQt
  set Rv := fun y => vpPhotonT m mγ Λ T (shellArg m y) with hRv
  have hU : 0 < T * m ^ 2 := by positivity
  have hd : ∀ y ∈ Ico (0 : ℝ) 1,
      HasDerivAt (fun y => (y - 1) * Tl y + m ^ 2 * (2 * y ^ 3 - y ^ 2) * Qt y)
        (Tl y + m ^ 2 * (4 * y - 2 * y ^ 2) * Rv y + 2 * m ^ 2 * (3 * y ^ 2 - y) * Qt y) y := by
    intro y hy
    have h1 : (1 : ℝ) - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy.2.ne)
    have dT := hasDerivAt_tail_shellArg hm hmγ hΛ hT hy
    have dQ := hasDerivAt_quad_shellArg hm hmγ hΛ hT hab hac hbc hy
    have h := (((hasDerivAt_id y).sub_const 1).mul dT).add
      ((((hasDerivAt_pow 3 y).const_mul 2).sub (hasDerivAt_pow 2 y)).const_mul (m ^ 2) |>.mul
        dQ)
    convert h using 1
    · funext v
      simp only [hTl, hQt, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id]
    · simp only [hTl, hQt, hRv, vpPhotonT_eq_mul_bubQ, Pi.sub_apply, id]
      generalize photonTail (vpPhotonT m mγ Λ T) (shellArg m y) = t
      generalize quadTailVP (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) = u
      generalize bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) (shellArg m y) = q
      simp only [shellArg, photonVar]
      field_simp
      ring
  have hf : IntervalIntegrable
      (fun y => Tl y + m ^ 2 * (4 * y - 2 * y ^ 2) * Rv y + 2 * m ^ 2 * (3 * y ^ 2 - y) * Qt y)
      volume 0 1 := by
    have i1 := intervalIntegrable_tail_shellArg hm hmγ hΛ hT (c := fun _ => 1)
      measurable_const one_pos fun y _ => by simp
    have i2 := intervalIntegrable_vp_shellArg hm hmγ hΛ hT
      (c := fun y => m ^ 2 * (4 * y - 2 * y ^ 2)) (by fun_prop) (K := 4 * m ^ 2)
      fun y hy => by
        have h0 : 0 ≤ 4 * y - 2 * y ^ 2 := by nlinarith [hy.1, hy.2]
        rw [Real.norm_of_nonneg (by positivity)]
        nlinarith [sq_nonneg m, hy.1, hy.2]
    have i3 := intervalIntegrable_quad_shellArg hm hmγ hΛ hT hab hac hbc
      (c := fun y => 2 * m ^ 2 * (3 * y ^ 2 - y)) (by fun_prop) (K := 4 * m ^ 2)
      fun y hy => by
        have e1 : 3 * y ^ 2 - y ≤ 2 := by nlinarith [hy.1, hy.2]
        have e2 : -2 ≤ 3 * y ^ 2 - y := by nlinarith [hy.1, hy.2]
        have f1 := mul_le_mul_of_nonneg_left e1 (sq_nonneg m)
        have f2 := mul_le_mul_of_nonneg_left e2 (sq_nonneg m)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith
    simp only [one_mul] at i1
    exact (i1.add i2).add i3
  have hL : Tendsto (fun y => (y - 1) * Tl y + m ^ 2 * (2 * y ^ 3 - y ^ 2) * Qt y)
      (𝓝[<] 1) (𝓝 0) := by
    have ha := tendsto_shellArg_atTop hm.ne'
    have hT0 := (tendsto_photonTail_vp_atTop hab hac hbc hmγ hΛ hU).comp ha
    have hQ0 := (tendsto_quadTailVP_atTop hab hac hbc).comp ha
    have hp : Tendsto (fun y : ℝ => y - 1) (𝓝[<] 1) (𝓝 (1 - 1)) :=
      ((continuous_id.sub continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
    have hq : Tendsto (fun y : ℝ => m ^ 2 * (2 * y ^ 3 - y ^ 2)) (𝓝[<] 1)
        (𝓝 (m ^ 2 * (2 * 1 ^ 3 - 1 ^ 2))) :=
      ((continuous_const.mul ((continuous_const.mul (continuous_pow 3)).sub
        (continuous_pow 2))).tendsto 1).mono_left nhdsWithin_le_nhds
    have h := (hp.mul hT0).add (hq.mul hQ0)
    simpa using h
  have key := integral_eq_of_hasDerivAt_tendsto hd hf hL
  simp only [hTl, hQt, hRv] at key
  rw [key]
  simp [shellArg, photonVar]

end Shell

end QED.ChainProof.SetCRegDisp

end
