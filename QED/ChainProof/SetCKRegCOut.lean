/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegCOutBd
public import QED.ChainProof.SetCKRegCIn
public import QED.ChainProof.SetCKRegSOut
public import QED.ChainProof.SetCKScOutCH

/-!
# Set (c), Stage K: the regulator link of the outer-massive corner and of the outer group

Helper level (no frozen statement). The two-loop part of the corner with the outer photon of
mass² `t > 0` and the inner photon of mass `λ`, at `Λ = ∞`, is

`scOutCRep t λ = 2 ∫₀¹ dY ∫₀^Y dy₃ ∫₀¹ dx cornerGm (√t) λ y₃ (Y - y₃) x`,

and `scOutCRep t 0 = scOutC t`. The outer group `S(0, t) + C(0, t)` with the corner counterterm
is `scOutRep t λ = scOutSRep t λ + scOutCRep t λ`.

* **`tendsto_scOutCRep`**: `scOutCRep t λ → scOutC t` as `λ → 0⁺` (dominated convergence in
  `x`, `y₃`, `Y` with `abs_regCornerGm_out_le`, `|cornerGm (√t) λ| ≤ scOutCDom t Y y₃ x`, valid
  where `M_λ = Y² + (1-Y) λ² - t y₃ (Y - y₃) ≠ 0`; for fixed `λ` and `Y` this fails at at most
  two `y₃` (`regMass_zero_finite`); the pointwise limit uses `M₀ ≠ 0`, again true for almost
  every `y₃`);
* **`tendsto_scOutRep`**: `scOutRep t λ → scOutS t + scOutC t` as `λ → 0⁺`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCCornerMain

/-- **The outer-massive corner unit at inner photon mass `λ`** (two-loop part). -/
noncomputable def scOutCRep (t lam : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, cornerGm (√t) lam y3 (Y - y3) x

/-- **The outer group** `S(0, t) + C(0, t)` with the corner counterterm, at inner photon mass
`λ`. -/
noncomputable def scOutRep (t lam : ℝ) : ℝ := scOutSRep t lam + scOutCRep t lam

/-- The `x`-integral of the outer-massive corner integrand. -/
noncomputable def regCOutX (t lam Y y3 : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, cornerGm (√t) lam y3 (Y - y3) x

/-- The `(y₃, x)`-integral of the outer-massive corner integrand. -/
noncomputable def regCOutY (t lam Y : ℝ) : ℝ := ∫ y3 in (0 : ℝ)..Y, regCOutX t lam Y y3

/-- The `Y`-factor of `scOutCDom`. -/
noncomputable def regCOutA (Y : ℝ) : ℝ := 1 / (Y ^ ((1 : ℝ) / 12)) ^ 8 + 1 / √(1 - Y)

/-- `y^(-n/12)`, written with twelfth roots. -/
noncomputable def regRootInv (n : ℕ) (y : ℝ) : ℝ := 1 / (y ^ ((1 : ℝ) / 12)) ^ n

theorem scOutCRep_zero (t : ℝ) : scOutCRep t 0 = scOutC t := rfl

theorem scOutCDom_eq (t Y y3 x : ℝ) :
    scOutCDom t Y y3 x = 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * regRootInv 8 x := by
  unfold scOutCDom regCOutA regRootInv
  ring

/-! ### The mass function -/

theorem regMass_eq {t lam Y y3 : ℝ} (ht : 0 ≤ t) :
    cornerMass (√t) lam y3 (Y - y3) = (Y ^ 2 + (1 - Y) * lam ^ 2) - t * (y3 * (Y - y3)) := by
  unfold cornerMass
  rw [sq_sqrt ht]
  ring

theorem regMass_zero_finite {t c Y : ℝ} (hc : c ≠ 0) :
    {y3 : ℝ | c - t * (y3 * (Y - y3)) = 0}.Finite := by
  open Polynomial in
  set p : ℝ[X] := C t * X ^ 2 - C (t * Y) * X + C c with hp
  have hev : ∀ y, p.eval y = c - t * (y * (Y - y)) := fun y => by
    simp only [hp, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    ring
  have hp0 : p ≠ 0 := fun h => by
    have := hev 0
    rw [h, eval_zero] at this
    exact hc (by linarith)
  refine (p.rootSet_finite ℝ).subset fun y hy => ?_
  rw [mem_rootSet]
  refine ⟨hp0, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval, hev]
  exact hy

theorem ae_regMass_ne {t lam Y : ℝ} (ht : 0 ≤ t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ y3 ∂(volume : Measure ℝ), cornerMass (√t) lam y3 (Y - y3) ≠ 0 := by
  have hc : Y ^ 2 + (1 - Y) * lam ^ 2 ≠ 0 := by
    have : 0 ≤ (1 - Y) * lam ^ 2 := mul_nonneg (by linarith [hY.2]) (sq_nonneg lam)
    have := pow_pos hY.1 2
    positivity
  rw [ae_iff]
  simp only [ne_eq, not_not, regMass_eq ht]
  exact (regMass_zero_finite hc).measure_zero _

theorem regScOutC_a_pos {t lam Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < cornerMass (√t) lam y3 (Y - y3) +
      betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x * (ladderInnerMass 1 (√t) x / x) := by
  have hρ := scOutRho_pos hx
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x =
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) := by
    unfold scOutCs
    field_simp
    ring
  rw [regScOutC_mass_eq (x := x) ht.le, hβ, ← hOut, hOut_eq_div_scOutRho ht.le hx]
  have hm := regScOutCm_pos hY h3 hx lam
  have hs := scOutCs_nonneg (Y := Y) (y3 := y3) hx
  have e : regScOutCm lam Y y3 x - y3 * (Y - y3) * (setCKQ x + t) +
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) * ((setCKQ x + t) / scOutRho x) =
      regScOutCm lam Y y3 x + scOutCs Y y3 x * (setCKQ x + t) := by
    field_simp
    ring
  rw [e]
  positivity

/-- **Continuity at `λ = 0`** of the outer-massive corner integrand in the inner mass, where
`M₀ ≠ 0`. -/
theorem continuousAt_regCornerGm_out {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM0 : cornerMass (√t) 0 y3 (Y - y3) ≠ 0) :
    ContinuousAt (fun lam => cornerGm (√t) lam y3 (Y - y3) x) 0 := by
  have hp := regScOutC_a_pos (lam := 0) ht hY h3 hx
  have hβ : 0 < betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x :=
    betaG_pos (cornerG_pos hY.2 h3.1)
  have hh : 0 < ladderInnerMass 1 (√t) x / x :=
    div_pos (ladderInnerMass_pos one_pos (sqrt_pos.2 ht) ⟨hx.1.le, hx.2.le⟩) hx.1
  have hMc : Continuous fun lam => cornerMass (√t) lam y3 (Y - y3) := by
    unfold cornerMass; fun_prop
  unfold cornerGm
  generalize betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = β at hβ hp ⊢
  generalize ladderInnerMass 1 (√t) x / x = h at hh hp ⊢
  have hp' : 0 < 1 + cornerMass (√t) 0 y3 (Y - y3) / (β * h) := by
    rw [one_add_div (by positivity)]
    exact div_pos (by linarith) (by positivity)
  have hF : ContinuousAt (fun m => cForm (cornerA0 x y3 (Y - y3)) (cornerA1 x y3 (Y - y3))
      (cornerA2 x y3 (Y - y3)) (cornerC0 x) (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3))
      (cornerC3 x y3 (Y - y3)) β h m (log (m + β * h)) (log (1 + m / (β * h))))
      (cornerMass (√t) 0 y3 (Y - y3)) := by
    generalize cornerMass (√t) 0 y3 (Y - y3) = m0 at hM0 hp hp' ⊢
    unfold cForm
    fun_prop (disch := (first | positivity | assumption))
  exact hF.comp (f := fun lam => cornerMass (√t) lam y3 (Y - y3)) hMc.continuousAt

/-! ### Measurability -/

theorem measurable_regCOutX (t lam : ℝ) : Measurable (uncurry (regCOutX t lam)) := by
  have hG : Measurable fun q : (ℝ × ℝ) × ℝ => cornerGm (√t) lam q.1.2 (q.1.1 - q.1.2) q.2 :=
    (measurable_regCornerGm_uncurry (√t) lam).comp
      (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.1.1 - q.1.2), q.2))
  change Measurable fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..1, cornerGm (√t) lam p.2 (p.1 - p.2) x
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact hG.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_regCOutY (t lam : ℝ) : Measurable (regCOutY t lam) := by
  have hu : Measurable (uncurry fun Y s => regCOutX t lam Y (Y * s)) := by
    change Measurable fun p : ℝ × ℝ => uncurry (regCOutX t lam) (p.1, p.1 * p.2)
    exact (measurable_regCOutX t lam).comp
      (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1, p.1 * p.2))
  have h : Measurable fun Y => ∫ s in (0 : ℝ)..1, regCOutX t lam Y (Y * s) :=
    measurable_intervalIntegral_of_uncurry hu
  have e : regCOutY t lam = fun Y => Y * ∫ s in (0 : ℝ)..1, regCOutX t lam Y (Y * s) := by
    funext Y
    have h' := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun y3 => regCOutX t lam Y y3) Y
    rw [mul_zero, mul_one, smul_eq_mul] at h'
    rw [regCOutY, h']
  rw [e]
  exact measurable_id.mul h

/-! ### The dominating functions -/

theorem regRootInv_nonneg (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ regRootInv n y := by
  unfold regRootInv
  have := rpow_nonneg hy ((1 : ℝ) / 12)
  positivity

theorem regIntervalIntegrable_rootInv {n : ℕ} (hn : n < 12) :
    IntervalIntegrable (regRootInv n) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (integrableOn_inv_root_pow hn)

theorem regIntervalIntegrable_regCOutA : IntervalIntegrable regCOutA volume 0 1 := by
  have i8 := regIntervalIntegrable_rootInv (n := 8) (by norm_num)
  have iS : IntervalIntegrable (fun Y : ℝ => 1 / √(1 - Y)) volume 0 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr ?_
    simpa only [one_div] using cornIn_integrableOn_one_sub integrableOn_inv_sqrt_Ioo
  exact i8.add iS

theorem regCOutA_nonneg {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : 0 ≤ regCOutA Y := by
  unfold regCOutA
  have := rpow_nonneg hY.1.le ((1 : ℝ) / 12)
  positivity

/-- The bound on the `x`-integral. -/
theorem abs_regCOutX_le {t lam Y y3 : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y)
    (hM : cornerMass (√t) lam y3 (Y - y3) ≠ 0) :
    |regCOutX t lam Y y3| ≤ 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 *
      ∫ x in (0 : ℝ)..1, regRootInv 8 x := by
  obtain ⟨-, hb⟩ := intervalIntegrable_of_abs_le (measurable_regCornerGm (√t) lam y3 (Y - y3))
    ((regIntervalIntegrable_rootInv (n := 8) (by norm_num)).const_mul
      (200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3))
    fun x hx => (abs_regCornerGm_out_le ht hl hY h3 hx hM).trans (le_of_eq (scOutCDom_eq ..))
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]

theorem regIntegral_rootInv_nonneg (n : ℕ) : 0 ≤ ∫ x in (0 : ℝ)..1, regRootInv n x :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hx => regRootInv_nonneg n hx.1

/-- The bound on the `(y₃, x)`-integral. -/
theorem abs_regCOutY_le {t lam Y : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    |regCOutY t lam Y| ≤ 200 * (1 + 1 / t) * regCOutA Y *
      (∫ y in (0 : ℝ)..1, regRootInv 10 y) * ∫ x in (0 : ℝ)..1, regRootInv 8 x := by
  set I8 := ∫ x in (0 : ℝ)..1, regRootInv 8 x
  have i10 := regIntervalIntegrable_rootInv (n := 10) (by norm_num)
  have i10Y : IntervalIntegrable (regRootInv 10) volume 0 Y :=
    i10.mono_set (by
      rw [uIcc_of_le hY.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right hY.2.le)
  have hb := intervalIntegral.norm_integral_le_of_norm_le hY.1.le (f := regCOutX t lam Y)
    (g := fun y3 => 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * I8) ?_
    (i10Y.const_mul _ |>.mul_const _)
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    have hK : 0 ≤ 200 * (1 + 1 / t) * regCOutA Y := by
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
  · filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := lam) ht.le hY]
      with y3 hy3 hM hy
    rw [Real.norm_eq_abs]
    exact abs_regCOutX_le ht hl hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩ hM

/-! ### Dominated convergence -/

theorem tendsto_regCOutX {t Y y3 : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hM0 : cornerMass (√t) 0 y3 (Y - y3) ≠ 0) :
    Tendsto (fun lam => regCOutX t lam Y y3) (𝓝[>] 0) (𝓝 (regCOutX t 0 Y y3)) := by
  have hMc : Continuous fun lam => cornerMass (√t) lam y3 (Y - y3) := by
    unfold cornerMass; fun_prop
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), cornerMass (√t) lam y3 (Y - y3) ≠ 0 :=
    (hMc.continuousAt.eventually_ne hM0).filter_mono nhdsWithin_le_nhds
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 * regRootInv 8 x)
    (Eventually.of_forall fun lam =>
      (measurable_regCornerGm (√t) lam y3 (Y - y3)).aestronglyMeasurable) ?_
    ((regIntervalIntegrable_rootInv (n := 8) (by norm_num)).const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hev] with lam hlam hM
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, ← scOutCDom_eq]
    exact abs_regCornerGm_out_le ht (by nlinarith [hlam.1, hlam.2]) hY h3
      ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ hM
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    exact (continuousAt_regCornerGm_out ht hY h3 ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
      hM0).tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_regCOutY {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun lam => regCOutY t lam Y) (𝓝[>] 0) (𝓝 (regCOutY t 0 Y)) := by
  have i10 := regIntervalIntegrable_rootInv (n := 10) (by norm_num)
  have i10Y : IntervalIntegrable (regRootInv 10) volume 0 Y :=
    i10.mono_set (by
      rw [uIcc_of_le hY.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right hY.2.le)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun y3 => 200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3 *
      ∫ x in (0 : ℝ)..1, regRootInv 8 x)
    (Eventually.of_forall fun lam =>
      ((measurable_regCOutX t lam).of_uncurry_left).aestronglyMeasurable) ?_
    (i10Y.const_mul _ |>.mul_const _) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := lam) ht.le hY]
      with y3 hy3 hM hy
    rw [uIoc_of_le hY.1.le] at hy
    rw [Real.norm_eq_abs]
    exact abs_regCOutX_le ht (by nlinarith [hlam.1, hlam.2]) hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩
      hM
  · filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := 0) ht.le hY]
      with y3 hy3 hM hy
    rw [uIoc_of_le hY.1.le] at hy
    exact tendsto_regCOutX ht hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩ hM

theorem tendsto_integral_regCOutY {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, regCOutY t lam Y) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, regCOutY t 0 Y)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 200 * (1 + 1 / t) * regCOutA Y * (∫ y in (0 : ℝ)..1, regRootInv 10 y) *
      ∫ x in (0 : ℝ)..1, regRootInv 8 x)
    (Eventually.of_forall fun lam => (measurable_regCOutY t lam).aestronglyMeasurable) ?_
    ((regIntervalIntegrable_regCOutA.const_mul _ |>.mul_const _).mul_const _) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact abs_regCOutY_le ht (by nlinarith [hlam.1, hlam.2]) ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact tendsto_regCOutY ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

/-! ### The links -/

/-- **The regulator link of the outer-massive corner**: for `t > 0`,
`scOutCRep t λ → scOutC t` as `λ → 0⁺`. -/
theorem tendsto_scOutCRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => scOutCRep t lam) (𝓝[>] 0) (𝓝 (scOutC t)) :=
  (tendsto_integral_regCOutY ht).const_mul 2

/-- **The regulator link of the outer group** `S(0, t) + C(0, t)` with the corner counterterm:
for `t > 0`, `scOutRep t λ → scOutS t + scOutC t` as `λ → 0⁺`. -/
theorem tendsto_scOutRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => scOutRep t lam) (𝓝[>] 0) (𝓝 (scOutS t + scOutC t)) :=
  (tendsto_scOutSRep ht).add (tendsto_scOutCRep ht)

end QED.ChainProof.SetCK
