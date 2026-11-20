/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKLamOutCDecay
public import QED.TwoLoop.UnitSCLimitTotal
public import QED.TwoLoop.UnitSCCornerErr

/-!
# Set (c), Stage K: the outer-massive corner at a large inner photon mass, the limit

Helper level (no frozen statement). With `lamOutCE` (the corner integrand at inner photon mass
`Λ`, outer photon mass² `t > 0`, with `ℓ_C log M_Λ` added) and its iterated integrals
`lamOutCX t Λ Y y₃ = ∫₀¹ dx lamOutCE`, `lamOutCY t Λ Y = ∫₀^Y dy₃ lamOutCX`:

* `lamOutCX_bound`, `lamOutCY_bound`: integrability and the bounds by `2 scOutCDom`, integrated,
  for every `Λ` (in `y₃` almost everywhere: `M_Λ = Y² + (1-Y) Λ² - t y₃ (Y - y₃) ≠ 0` fails at
  at most two `y₃`, `ae_regMass_ne`);
* **`tendsto_integral_lamOutCY`**: `∫₀¹ dY lamOutCY t Λ Y → 0` as `Λ → ∞` (dominated convergence
  in `x`, `y₃` and `Y`, with the pointwise decay `tendsto_lamOutCE`; for fixed `(Y, y₃)` the mass
  `M_Λ` is eventually positive, `lamOut_eventually_mass_pos`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCCorner

/-- The `x`-integral of `lamOutCE`. -/
noncomputable def lamOutCX (t Lam Y y3 : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, lamOutCE t Lam Y y3 x

/-- The `(y₃, x)`-integral of `lamOutCE`. -/
noncomputable def lamOutCY (t Lam Y : ℝ) : ℝ := ∫ y3 in (0 : ℝ)..Y, lamOutCX t Lam Y y3

/-! ### Measurability -/

theorem measurable_lamOutCE_uncurry (t Lam : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => lamOutCE t Lam q.1.1 q.1.2 q.2 := by
  have hG : Measurable fun q : (ℝ × ℝ) × ℝ => cornerGm (√t) Lam q.1.2 (q.1.1 - q.1.2) q.2 :=
    (measurable_regCornerGm_uncurry (√t) Lam).comp
      (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.1.1 - q.1.2), q.2))
  have hc : Measurable fun x : ℝ => cornerC0 x / hOut t x := by
    unfold cornerC0 hOut ladderInnerMass
    fun_prop
  have hl : Measurable fun Y : ℝ => log (ladderInnerMass 1 Lam Y) := by
    unfold ladderInnerMass
    fun_prop
  have hL : Measurable fun q : (ℝ × ℝ) × ℝ =>
      cornerC0 q.2 / hOut t q.2 * log (ladderInnerMass 1 Lam q.1.1) :=
    (hc.comp measurable_snd).mul (hl.comp (measurable_fst.comp measurable_fst))
  unfold lamOutCE
  exact hG.add hL

theorem measurable_lamOutCE (t Lam Y y3 : ℝ) : Measurable (lamOutCE t Lam Y y3) := by
  have h := (measurable_lamOutCE_uncurry t Lam).comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ => ((Y, y3), x))
  simpa only [Function.comp_def] using h

theorem measurable_lamOutCX (t Lam : ℝ) : Measurable (uncurry (lamOutCX t Lam)) := by
  change Measurable fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..1, lamOutCE t Lam p.1 p.2 x
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact (measurable_lamOutCE_uncurry t Lam).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_lamOutCY (t Lam : ℝ) : Measurable (lamOutCY t Lam) := by
  have hu : Measurable (uncurry fun Y s => lamOutCX t Lam Y (Y * s)) := by
    change Measurable fun p : ℝ × ℝ => uncurry (lamOutCX t Lam) (p.1, p.1 * p.2)
    exact (measurable_lamOutCX t Lam).comp
      (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1, p.1 * p.2))
  have h : Measurable fun Y => ∫ s in (0 : ℝ)..1, lamOutCX t Lam Y (Y * s) :=
    measurable_intervalIntegral_of_uncurry hu
  have e : lamOutCY t Lam = fun Y => Y * ∫ s in (0 : ℝ)..1, lamOutCX t Lam Y (Y * s) := by
    funext Y
    have h' := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun y3 => lamOutCX t Lam Y y3) Y
    rw [mul_zero, mul_one, smul_eq_mul] at h'
    rw [lamOutCY, h']
  rw [e]
  exact measurable_id.mul h

/-! ### Bounds -/

theorem lamOutC_dom_eq (t Y y3 x : ℝ) : 2 * scOutCDom t Y y3 x =
    2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * regRootInv 8 x := by
  rw [scOutCDom_eq]
  ring

/-- The bound on the `x`-integral, with integrability. -/
theorem lamOutCX_bound {t Lam Y y3 : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hM : cornerMass (√t) Lam y3 (Y - y3) ≠ 0) :
    IntervalIntegrable (lamOutCE t Lam Y y3) volume 0 1 ∧
      |lamOutCX t Lam Y y3| ≤ 2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 *
        ∫ x in (0 : ℝ)..1, regRootInv 8 x := by
  obtain ⟨hi, hb⟩ := intervalIntegrable_of_abs_le (measurable_lamOutCE t Lam Y y3)
    ((regIntervalIntegrable_rootInv (n := 8) (by norm_num)).const_mul
      (2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3))
    fun x hx => (abs_lamOutCE_le ht hY h3 hx hM).trans (le_of_eq (lamOutC_dom_eq ..))
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_const_mul]

theorem lamOutC_intervalIntegrable_rootInv_Y {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (regRootInv 10) volume 0 Y :=
  (regIntervalIntegrable_rootInv (n := 10) (by norm_num)).mono_set (by
    rw [uIcc_of_le hY.1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc_right hY.2.le)

/-- The bound on the `(y₃, x)`-integral, with integrability, for every `Λ`. -/
theorem lamOutCY_bound {t Lam Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (lamOutCX t Lam Y) volume 0 Y ∧
      |lamOutCY t Lam Y| ≤ 2 * 200 * (1 + 1 / t) * regCOutA Y *
        (∫ y in (0 : ℝ)..1, regRootInv 10 y) * ∫ x in (0 : ℝ)..1, regRootInv 8 x := by
  set I8 := ∫ x in (0 : ℝ)..1, regRootInv 8 x
  have i10 := regIntervalIntegrable_rootInv (n := 10) (by norm_num)
  have i10Y := lamOutC_intervalIntegrable_rootInv_Y hY
  have hae : ∀ᵐ y3 ∂(volume : Measure ℝ), y3 ∈ Ioc (0 : ℝ) Y →
      ‖lamOutCX t Lam Y y3‖ ≤ 2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * I8 := by
    filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := Lam) ht.le hY]
      with y3 hy3 hM hy
    rw [Real.norm_eq_abs]
    exact (lamOutCX_bound ht hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩ hM).2
  have hg : IntervalIntegrable
      (fun y3 => 2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * I8) volume 0 Y :=
    i10Y.const_mul _ |>.mul_const _
  have hint : IntervalIntegrable (lamOutCX t Lam Y) volume 0 Y :=
    hg.mono_fun' ((measurable_lamOutCX t Lam).of_uncurry_left).aestronglyMeasurable
      (by
        rw [uIoc_of_le hY.1.le]
        refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
        filter_upwards [hae] with y3 h hy
        exact h hy)
  refine ⟨hint, ?_⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le hY.1.le
    (f := lamOutCX t Lam Y)
    (g := fun y3 => 2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * I8)
    (by
      filter_upwards [hae] with y3 h hy
      exact h hy) hg
  rw [Real.norm_eq_abs] at hb
  refine hb.trans ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  have hK : 0 ≤ 2 * 200 * (1 + 1 / t) * regCOutA Y := by
    have := regCOutA_nonneg hY
    have : 0 < 1 + 1 / t := by positivity
    positivity
  have hmono : ∫ y in (0 : ℝ)..Y, regRootInv 10 y ≤ ∫ y in (0 : ℝ)..1, regRootInv 10 y :=
    intervalIntegral.integral_mono_interval le_rfl hY.1.le hY.2.le
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact regRootInv_nonneg 10 hy.1.le) i10
  have hI8 := regIntegral_rootInv_nonneg 8
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hK) hI8

theorem lamOutCY_intervalIntegrable {t Lam : ℝ} (ht : 0 < t) :
    IntervalIntegrable (lamOutCY t Lam) volume 0 1 := by
  have hg : IntervalIntegrable (fun Y => 2 * 200 * (1 + 1 / t) * regCOutA Y *
      (∫ y in (0 : ℝ)..1, regRootInv 10 y) * ∫ x in (0 : ℝ)..1, regRootInv 8 x) volume 0 1 :=
    (regIntervalIntegrable_regCOutA.const_mul _ |>.mul_const _).mul_const _
  refine hg.mono_fun' (measurable_lamOutCY t Lam).aestronglyMeasurable ?_
  rw [uIoc_of_le zero_le_one]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
  rw [Real.norm_eq_abs]
  exact (lamOutCY_bound ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).2

/-! ### Dominated convergence as `Λ → ∞` -/

theorem lamOut_eventually_mass_pos {t Y y3 : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ Lam in atTop, 0 < cornerMass (√t) Lam y3 (Y - y3) := by
  have hMt : Tendsto (fun Lam => cornerMass (√t) Lam y3 (Y - y3)) atTop atTop := by
    have := (lamOut_tendsto_add_atTop (Y ^ 2) (-(t * (y3 * (Y - y3))))).comp
      (lamOut_tendsto_sq_mul hY.2)
    refine this.congr fun Lam => ?_
    simp only [Function.comp]
    rw [regMass_eq ht.le]
    ring
  exact hMt.eventually_gt_atTop 0

theorem tendsto_lamOutCX {t Y y3 : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) :
    Tendsto (fun Lam => lamOutCX t Lam Y y3) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ))
    (F := fun Lam x => lamOutCE t Lam Y y3 x) (f := fun _ => (0 : ℝ)) (a := 0) (b := 1)
    (fun x => 2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * regRootInv 8 x)
    (Eventually.of_forall fun Lam => (measurable_lamOutCE t Lam Y y3).aestronglyMeasurable) ?_
    ((regIntervalIntegrable_rootInv (n := 8) (by norm_num)).const_mul _) ?_
  · simp only [intervalIntegral.integral_zero] at h
    exact h
  · filter_upwards [lamOut_eventually_mass_pos (y3 := y3) ht hY] with Lam hM
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, ← lamOutC_dom_eq]
    exact abs_lamOutCE_le ht hY h3 ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ hM.ne'
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    exact tendsto_lamOutCE ht hY h3 ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

theorem tendsto_lamOutCY {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun Lam => lamOutCY t Lam Y) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ))
    (F := fun Lam y3 => lamOutCX t Lam Y y3) (f := fun _ => (0 : ℝ)) (a := 0) (b := Y)
    (fun y3 => 2 * 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 *
      ∫ x in (0 : ℝ)..1, regRootInv 8 x)
    (Eventually.of_forall fun Lam =>
      ((measurable_lamOutCX t Lam).of_uncurry_left).aestronglyMeasurable) ?_
    ((lamOutC_intervalIntegrable_rootInv_Y hY).const_mul _ |>.mul_const _) ?_
  · simp only [intervalIntegral.integral_zero] at h
    exact h
  · refine Eventually.of_forall fun Lam => ?_
    filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := Lam) ht.le hY]
      with y3 hy3 hM hy
    rw [uIoc_of_le hY.1.le] at hy
    rw [Real.norm_eq_abs]
    exact (lamOutCX_bound ht hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩ hM).2
  · filter_upwards [Measure.ae_ne volume Y] with y3 hy3 hy
    rw [uIoc_of_le hY.1.le] at hy
    exact tendsto_lamOutCX ht hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩

/-- **The corner at inner mass `Λ` with its subdivergence added vanishes as `Λ → ∞`.** -/
theorem tendsto_integral_lamOutCY {t : ℝ} (ht : 0 < t) :
    Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, lamOutCY t Lam Y) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ))
    (F := fun Lam Y => lamOutCY t Lam Y) (f := fun _ => (0 : ℝ)) (a := 0) (b := 1)
    (fun Y => 2 * 200 * (1 + 1 / t) * regCOutA Y * (∫ y in (0 : ℝ)..1, regRootInv 10 y) *
      ∫ x in (0 : ℝ)..1, regRootInv 8 x)
    (Eventually.of_forall fun Lam => (measurable_lamOutCY t Lam).aestronglyMeasurable) ?_
    ((regIntervalIntegrable_regCOutA.const_mul _ |>.mul_const _).mul_const _) ?_
  · simp only [intervalIntegral.integral_zero] at h
    exact h
  · refine Eventually.of_forall fun Lam => ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact (lamOutCY_bound ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).2
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact tendsto_lamOutCY ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

end QED.ChainProof.SetCK
