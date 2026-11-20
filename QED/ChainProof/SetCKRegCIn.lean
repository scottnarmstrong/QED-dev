/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegCInBd
public import QED.ChainProof.SetCKCornIn
public import QED.TwoLoop.UnitSCCornerMain
public import QED.TwoLoop.UnitLLinkLimit
public import QED.TwoLoop.UnitLCloseLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the regulator link of the corner unit with a massive inner photon

Helper level (no frozen statement). The corner unit `C(t, 0)` at outer photon mass `λ` and
`Λ = ∞` is eq. (6.3) of `docs/TWO-LOOP-UNITS.md` with the two photon masses separated (inner
mass² `t`, outer mass `λ`), with the counterterm `δ₁(t) F₂(λ)`:

`cornInRep t λ = 2 ∫₀¹ dY [∫₀^Y dy₃ ∫₀¹ dx cornerGm λ (√t) y₃ (Y-y₃) x
  - F₂(λ) Y ((Y² + 2Y - 2)/(2M) - (log M)/2)]`, `M = M_t(Y)`,

(`F₂(λ) = oneLoopF2 1 λ`). At `λ = 0` (`F₂(0) = 1/2`) it is `QED.ChainProof.SetCK.cornIn`.

* **`tendsto_cornInRep`**: `cornInRep t λ → cornIn t` as `λ → 0⁺`, for every `t > 0`
  (dominated convergence in `x`, `y₃`, `Y` with `regCornerGm_abs_le`:
  `|cornerGm λ √t| ≤ (C + t)/(Y √x √y₃ √(1-Y))`; `∫₀^Y y₃^(-1/2) = 2√Y`, so the `Y`-integrand is
  bounded by `4(C + t)/(√Y √(1-Y))`; `F₂(λ) → 1/2`).

Numerically (scratch `stageK/m5b/cnum.py`, Gauss–Legendre `120³`) `cornInRep 1 λ = 0.26451`
(`λ = 10⁻²`), `0.27290` (`λ = 10⁻³`), against `cornIn 1 = 0.27388`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCCornerMain

/-- **The corner unit with a massive inner photon at outer photon mass `λ`**: the two-mass form
of eq. (6.3), with the counterterm `δ₁(t) F₂(λ)`. -/
noncomputable def cornInRep (t lam : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ((∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, cornerGm lam (√t) y3 (Y - y3) x)
    - oneLoopF2 1 lam * (Y * ((Y ^ 2 + 2 * Y - 2) / (2 * massIn t Y) - log (massIn t Y) / 2)))

/-- The `x`-integral of the corner integrand. -/
noncomputable def regCInX (t lam Y y3 : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, cornerGm lam (√t) y3 (Y - y3) x

/-- The `(y₃, x)`-integral of the corner integrand. -/
noncomputable def regCInY (t lam Y : ℝ) : ℝ := ∫ y3 in (0 : ℝ)..Y, regCInX t lam Y y3

/-- The counterterm insertion `Y ((Y² + 2Y - 2)/(2M) - (log M)/2)`. -/
noncomputable def regCInCt (t Y : ℝ) : ℝ :=
  Y * ((Y ^ 2 + 2 * Y - 2) / (2 * massIn t Y) - log (massIn t Y) / 2)

/-- The constant of `regCornerGm_abs_le`. -/
noncomputable def regCInC : ℝ := regCornerGm_abs_le.choose

/-- The `(Y, y₃)`-factor `1/(Y √y₃ √(1-Y))` of the dominating function. -/
noncomputable def regCInW (Y y3 : ℝ) : ℝ := (Y * √y3 * √(1 - Y))⁻¹

theorem regCInC_nonneg : 0 ≤ regCInC := regCornerGm_abs_le.choose_spec.1

/-! ### Measurability -/

theorem measurable_regCornerGm_uncurry (la lb : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => cornerGm la lb q.1.1 q.1.2 q.2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hg⟩ := continuous_cornerCoeffs
  have mβ : Measurable fun q : (ℝ × ℝ) × ℝ => betaG (cornerG q.1.1 q.1.2) (q.1.1 * q.1.2) q.2 := by
    have := hg.measurable
    unfold betaG
    fun_prop
  have mh : Measurable fun q : (ℝ × ℝ) × ℝ => ladderInnerMass 1 la q.2 / q.2 := by
    unfold ladderInnerMass; fun_prop
  have mM : Measurable fun q : (ℝ × ℝ) × ℝ => cornerMass la lb q.1.1 q.1.2 := by
    unfold cornerMass; fun_prop
  exact measurable_cForm h0.measurable h1.measurable h2.measurable h3.measurable h4.measurable
    h5.measurable h6.measurable mβ mh mM (mM.add (mβ.mul mh)).log
    ((measurable_const.add (mM.div (mβ.mul mh))).log)

theorem measurable_regCornerGm (la lb y3 y4 : ℝ) : Measurable (cornerGm la lb y3 y4) := by
  have h := (measurable_regCornerGm_uncurry la lb).comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ => ((y3, y4), x))
  simpa only [Function.comp_def] using h

theorem measurable_regCInX (t lam : ℝ) : Measurable (uncurry (regCInX t lam)) := by
  have hG : Measurable fun q : (ℝ × ℝ) × ℝ => cornerGm lam (√t) q.1.2 (q.1.1 - q.1.2) q.2 :=
    (measurable_regCornerGm_uncurry lam (√t)).comp
      (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.1.1 - q.1.2), q.2))
  change Measurable fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..1, cornerGm lam (√t) p.2 (p.1 - p.2) x
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact hG.stronglyMeasurable.integral_prod_right'.measurable

theorem regCInY_eq (t lam Y : ℝ) :
    regCInY t lam Y = Y * ∫ s in (0 : ℝ)..1, regCInX t lam Y (Y * s) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun y3 => regCInX t lam Y y3) Y
  rw [mul_zero, mul_one, smul_eq_mul] at h
  rw [regCInY, h]

theorem measurable_regCInY (t lam : ℝ) : Measurable (regCInY t lam) := by
  have hu : Measurable (uncurry fun Y s => regCInX t lam Y (Y * s)) := by
    change Measurable fun p : ℝ × ℝ => uncurry (regCInX t lam) (p.1, p.1 * p.2)
    exact (measurable_regCInX t lam).comp
      (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1, p.1 * p.2))
  have h : Measurable fun Y => ∫ s in (0 : ℝ)..1, regCInX t lam Y (Y * s) :=
    measurable_intervalIntegral_of_uncurry hu
  have e : regCInY t lam = fun Y => Y * ∫ s in (0 : ℝ)..1, regCInX t lam Y (Y * s) :=
    funext (regCInY_eq t lam)
  rw [e]
  exact measurable_id.mul h

/-! ### The inverse square root -/

theorem regIntervalIntegrable_inv_sqrt {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun x : ℝ => (√x)⁻¹) volume 0 a := by
  refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a)
    (show -1 < -(1 / 2 : ℝ) by norm_num)).congr_uIoo fun x hx => ?_
  rw [uIoo_of_le ha] at hx
  exact rpow_neg_half' hx.1

theorem regIntegral_inv_sqrt {a : ℝ} (ha : 0 ≤ a) : ∫ x in (0 : ℝ)..a, (√x)⁻¹ = 2 * √a := by
  have e : ∫ x in (0 : ℝ)..a, (√x)⁻¹ = ∫ x in (0 : ℝ)..a, x ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le ha] at hx
    exact (rpow_neg_half' hx.1).symm
  rw [e, integral_rpow (Or.inl (by norm_num)), sqrt_eq_rpow]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_rpow (by norm_num)]
  ring

/-! ### The bounds -/

/-- The pointwise bound in the unit's variables, for `λ² ≤ 1`. -/
theorem abs_regCInG_le {t lam Y y3 x : ℝ} (ht : 0 ≤ t) (hl : lam ^ 2 ≤ 1) (h3 : 0 < y3)
    (h3Y : y3 < Y) (hY : Y < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    |cornerGm lam (√t) y3 (Y - y3) x| ≤ (regCInC + t) * regCInW Y y3 * (√x)⁻¹ := by
  have h := regCornerGm_abs_le.choose_spec.2 lam (√t) y3 (Y - y3) x hl h3 (by linarith)
    (by linarith) hx0 hx1
  rw [sq_sqrt ht] at h
  change _ ≤ (regCInC + t) * _ at h
  refine h.trans (le_of_eq ?_)
  unfold cornerMaj regCInW cornerG
  rw [show y3 + (Y - y3) = Y by ring, show 1 - y3 - (Y - y3) = 1 - Y by ring, sqrt_mul h3.le]
  simp only [mul_inv]
  ring

theorem abs_regCInX_le {t lam Y y3 : ℝ} (ht : 0 ≤ t) (hl : lam ^ 2 ≤ 1) (h3 : 0 < y3)
    (h3Y : y3 < Y) (hY : Y < 1) :
    |regCInX t lam Y y3| ≤ 2 * (regCInC + t) * regCInW Y y3 := by
  obtain ⟨-, hb⟩ := intervalIntegrable_of_abs_le (measurable_regCornerGm lam (√t) y3 (Y - y3))
    ((regIntervalIntegrable_inv_sqrt zero_le_one).const_mul ((regCInC + t) * regCInW Y y3))
    fun x hx => abs_regCInG_le ht hl h3 h3Y hY hx.1 hx.2
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, regIntegral_inv_sqrt zero_le_one, sqrt_one]
  ring

theorem regCInW_eq {Y y3 : ℝ} : regCInW Y y3 = (Y * √(1 - Y))⁻¹ * (√y3)⁻¹ := by
  unfold regCInW
  simp only [mul_inv]
  ring

theorem regIntervalIntegrable_bound {t Y : ℝ} (hY0 : 0 < Y) :
    IntervalIntegrable (fun y3 => 2 * (regCInC + t) * regCInW Y y3) volume 0 Y := by
  simp_rw [regCInW_eq]
  exact ((regIntervalIntegrable_inv_sqrt hY0.le).const_mul _).const_mul _

theorem abs_regCInY_le {t lam Y : ℝ} (ht : 0 ≤ t) (hl : lam ^ 2 ≤ 1) (hY0 : 0 < Y)
    (hY : Y < 1) :
    |regCInY t lam Y| ≤ 4 * (regCInC + t) * (√Y * √(1 - Y))⁻¹ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le hY0.le (f := regCInX t lam Y)
    (g := fun y3 => 2 * (regCInC + t) * regCInW Y y3) ?_ (regIntervalIntegrable_bound hY0)
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq ?_)
    simp_rw [regCInW_eq]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      regIntegral_inv_sqrt hY0.le]
    have hs : 0 < √Y := sqrt_pos.mpr hY0
    have hs1 : 0 < √(1 - Y) := sqrt_pos.mpr (by linarith)
    have hY2 : √Y ^ 2 = Y := sq_sqrt hY0.le
    have key : (Y * √(1 - Y))⁻¹ * (2 * √Y) = 2 * (√Y * √(1 - Y))⁻¹ := by
      have aux : ∀ s b : ℝ, 0 < s → 0 < b → (s ^ 2 * b)⁻¹ * (2 * s) = 2 * (s * b)⁻¹ :=
        fun s b hs hb => by field_simp
      have := aux (√Y) (√(1 - Y)) hs hs1
      rwa [hY2] at this
    rw [key]
    ring
  · filter_upwards [Measure.ae_ne volume Y] with y3 hy3 hy
    rw [Real.norm_eq_abs]
    exact abs_regCInX_le ht hl hy.1 (lt_of_le_of_ne hy.2 hy3) hY

theorem regIntervalIntegrable_boundY (t : ℝ) :
    IntervalIntegrable (fun Y => 4 * (regCInC + t) * (√Y * √(1 - Y))⁻¹) volume 0 1 :=
  ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    integrableOn_inv_sqrt_mul).const_mul _

theorem intervalIntegrable_regCInY {t lam : ℝ} (ht : 0 ≤ t) (hl : lam ^ 2 ≤ 1) :
    IntervalIntegrable (regCInY t lam) volume 0 1 := by
  refine (regIntervalIntegrable_boundY t).mono_fun'
    (measurable_regCInY t lam).aestronglyMeasurable ?_
  rw [uIoc_of_le zero_le_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (Measure.ae_ne volume 1)]
    with Y hY hY1
  rw [Real.norm_eq_abs]
  exact abs_regCInY_le ht hl hY.1 (lt_of_le_of_ne hY.2 hY1)

/-! ### Dominated convergence -/

theorem tendsto_regCInX {t Y y3 : ℝ} (ht : 0 ≤ t) (h3 : 0 < y3) (h3Y : y3 < Y) (hY : Y < 1) :
    Tendsto (fun lam => regCInX t lam Y y3) (𝓝[>] 0) (𝓝 (regCInX t 0 Y y3)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => (regCInC + t) * regCInW Y y3 * (√x)⁻¹)
    (Eventually.of_forall fun lam =>
      (measurable_regCornerGm lam (√t) y3 (Y - y3)).aestronglyMeasurable) ?_
    ((regIntervalIntegrable_inv_sqrt zero_le_one).const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs]
    exact abs_regCInG_le ht (by nlinarith [hlam.1, hlam.2]) h3 h3Y hY hx.1
      (lt_of_le_of_ne hx.2 hx1)
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    exact (continuousAt_regCornerGm h3 (by linarith) (by linarith) hx.1
      (lt_of_le_of_ne hx.2 hx1)).tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_regCInY {t Y : ℝ} (ht : 0 ≤ t) (hY0 : 0 < Y) (hY : Y < 1) :
    Tendsto (fun lam => regCInY t lam Y) (𝓝[>] 0) (𝓝 (regCInY t 0 Y)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun y3 => 2 * (regCInC + t) * regCInW Y y3)
    (Eventually.of_forall fun lam =>
      ((measurable_regCInX t lam).of_uncurry_left).aestronglyMeasurable) ?_
    (regIntervalIntegrable_bound hY0) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume Y] with y3 hy3 hy
    rw [uIoc_of_le hY0.le] at hy
    rw [Real.norm_eq_abs]
    exact abs_regCInX_le ht (by nlinarith [hlam.1, hlam.2]) hy.1 (lt_of_le_of_ne hy.2 hy3) hY
  · filter_upwards [Measure.ae_ne volume Y] with y3 hy3 hy
    rw [uIoc_of_le hY0.le] at hy
    exact tendsto_regCInX ht hy.1 (lt_of_le_of_ne hy.2 hy3) hY

theorem tendsto_integral_regCInY {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, regCInY t lam Y) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, regCInY t 0 Y)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 4 * (regCInC + t) * (√Y * √(1 - Y))⁻¹)
    (Eventually.of_forall fun lam => (measurable_regCInY t lam).aestronglyMeasurable) ?_
    (regIntervalIntegrable_boundY t) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact abs_regCInY_le ht (by nlinarith [hlam.1, hlam.2]) hY.1 (lt_of_le_of_ne hY.2 hY1)
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact tendsto_regCInY ht hY.1 (lt_of_le_of_ne hY.2 hY1)

/-! ### The link -/

theorem intervalIntegrable_regCInCt {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (regCInCt t) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hM : ∀ Y ∈ uIcc (0 : ℝ) 1, massIn t Y ≠ 0 := fun Y hY => by
    rw [uIcc_of_le zero_le_one] at hY; exact (massIn_pos ht hY).ne'
  have hM2 : ∀ Y ∈ uIcc (0 : ℝ) 1, 2 * massIn t Y ≠ 0 := fun Y hY =>
    mul_ne_zero two_ne_zero (hM Y hY)
  have hc : ContinuousOn (fun Y => massIn t Y) (uIcc 0 1) := by
    unfold massIn ladderInnerMass; fun_prop
  unfold regCInCt
  exact continuousOn_id.mul ((ContinuousOn.div (by fun_prop) (continuousOn_const.mul hc) hM2).sub
    ((hc.log hM).div_const 2))

theorem cornInRep_split {t lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) :
    cornInRep t lam = 2 * ((∫ Y in (0 : ℝ)..1, regCInY t lam Y) -
      oneLoopF2 1 lam * ∫ Y in (0 : ℝ)..1, regCInCt t Y) := by
  have e : cornInRep t lam =
      2 * ∫ Y in (0 : ℝ)..1, (regCInY t lam Y - oneLoopF2 1 lam * regCInCt t Y) := rfl
  rw [e, intervalIntegral.integral_sub (intervalIntegrable_regCInY ht.le hl)
    ((intervalIntegrable_regCInCt ht).const_mul _), intervalIntegral.integral_const_mul]

theorem cornIn_split {t : ℝ} (ht : 0 < t) :
    cornIn t = 2 * ((∫ Y in (0 : ℝ)..1, regCInY t 0 Y) -
      1 / 2 * ∫ Y in (0 : ℝ)..1, regCInCt t Y) := by
  have e : cornIn t = 2 * ∫ Y in (0 : ℝ)..1, (regCInY t 0 Y - 1 / 2 * regCInCt t Y) := by
    unfold cornIn
    congr 1
    refine intervalIntegral.integral_congr fun Y _ => ?_
    simp only [cornInIntegrand, regCInY, regCInX, regCInCt]
    ring
  rw [e, intervalIntegral.integral_sub (intervalIntegrable_regCInY ht.le (by norm_num))
    ((intervalIntegrable_regCInCt ht).const_mul _), intervalIntegral.integral_const_mul]

/-- **The regulator link of the inner-massive corner unit**: for `t > 0`,
`cornInRep t λ → cornIn t` as `λ → 0⁺`. -/
theorem tendsto_cornInRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => cornInRep t lam) (𝓝[>] 0) (𝓝 (cornIn t)) := by
  have h := ((tendsto_integral_regCInY ht.le).sub
    (tendsto_oneLoopF2_one.mul_const (∫ Y in (0 : ℝ)..1, regCInCt t Y))).const_mul 2
  rw [cornIn_split ht]
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
  exact (cornInRep_split ht (by nlinarith [hlam.1, hlam.2])).symm

end QED.ChainProof.SetCK
