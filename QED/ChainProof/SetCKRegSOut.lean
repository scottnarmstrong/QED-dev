/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegSOutBd
public import QED.ChainProof.SetCKSelfIn
public import QED.TwoLoop.UnitSCLimitSLimit
public import QED.TwoLoop.UnitLCloseLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the regulator link of the outer-massive self-energy group

Helper level (no frozen statement). The self-energy unit `S(0, t)` with the corner counterterm, at
inner photon mass `λ` and `Λ = ∞` (outer photon mass² `t`, `M = M_λ(Y) = Y² + (1-Y) λ²`), is

`scOutSRep t λ = 2 ∫₀¹ dY [∫₀¹ dx (selfGm (√t) λ Y x + k₂/h_t²) + d̄₂(Y, M) V_k(√t)
  + (d̄₂ - σ)(Y, M) V_m(√t) - F₂(√t) Y ((Y² + 2Y - 2)/(2M) - (log M)/2)]`,

the counterterms of `QED.ChainProof.SetCK.scOutS` before the infrared regrouping. Each
counterterm alone has a `1/Y` singularity as `λ → 0`; with `V_k + V_m + F₂ = 0` at the outer mass
(`selfVk_add_selfVm_add_oneLoopF2`) the bracket is, for every `λ` (`regOutCt_eq`),

`V_k ((1 - 2Y)/2 log M + Y²(2 - Y)/(2M)) + V_m ((1 - Y/2) log M + Y²(2 - Y)/(2M))`
(`regOutCtF`),

bounded by `(|V_k| + |V_m|)(1 - 2 log Y)` for `λ² ≤ 1` (`Y² ≤ M ≤ 1`), and at `λ = 0` its
integral is `V_k/4 - V_m = scOutSCt t / 2` (`regIntegral_fA`, `regIntegral_fB`).

* **`tendsto_scOutSRep`**: `scOutSRep t λ → scOutS t` as `λ → 0⁺`, for every `t > 0`
  (dominated convergence with `abs_scOutRegS_le` for the two-loop part).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCClose

/-- **The outer-massive self-energy unit with the corner counterterm at inner photon mass `λ`**:
the two-mass form of eq. (5.3) with the counterterms of `S(0, t)` and of the corner. -/
noncomputable def scOutSRep (t lam : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, (selfGm (√t) lam Y x + selfK2 Y x / hOut t x ^ 2)) +
    selfInD2 Y (ladderInnerMass 1 lam Y) * selfVk (√t) +
      (selfInD2 Y (ladderInnerMass 1 lam Y) - selfInSigma Y (ladderInnerMass 1 lam Y)) *
        selfVm (√t) -
      oneLoopF2 1 (√t) * (Y * ((Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 lam Y) -
        log (ladderInnerMass 1 lam Y) / 2)))

/-- The counterterm bracket after the infrared regrouping. -/
noncomputable def regOutCtF (a b M Y : ℝ) : ℝ :=
  a * ((1 - 2 * Y) / 2 * log M + Y ^ 2 * (2 - Y) / (2 * M)) +
    b * ((1 - Y / 2) * log M + Y ^ 2 * (2 - Y) / (2 * M))

/-! ### The counterterm bracket -/

/-- **The infrared regrouping of the counterterms**, for `V_k + V_m + F₂ = 0`. -/
theorem regOutCt_eq {a b f M Y : ℝ} (h : a + b + f = 0) (hM : M ≠ 0) :
    selfInD2 Y M * a + (selfInD2 Y M - selfInSigma Y M) * b -
        f * (Y * ((Y ^ 2 + 2 * Y - 2) / (2 * M) - log M / 2)) = regOutCtF a b M Y := by
  have hf : f = -a - b := by linarith
  subst hf
  unfold selfInD2 selfInSigma regOutCtF
  field_simp
  ring

theorem regAbs_add_mul_le {a b P R L : ℝ} (hP : |P| ≤ L) (hR : |R| ≤ L) :
    |a * P + b * R| ≤ (|a| + |b|) * L := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hP
  calc |a * P + b * R| ≤ |a| * |P| + |b| * |R| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |a| * L + |b| * L := by gcongr
    _ = (|a| + |b|) * L := by ring

theorem abs_regOutCtF_le {a b lam Y : ℝ} (hl : lam ^ 2 ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    |regOutCtF a b (ladderInnerMass 1 lam Y) Y| ≤ (|a| + |b|) * (1 + 2 * -log Y) := by
  obtain ⟨hMl, hMu⟩ := regMassOut_bounds hl hY
  have hY0 := hY.1
  have hY1 := hY.2
  have hM : 0 < ladderInnerMass 1 lam Y := (pow_pos hY0 2).trans_le hMl
  have hlM := regAbs_log_mass_le hl hY
  have hlY : 0 ≤ -log Y := neg_nonneg.2 (log_nonpos hY0.le hY1.le)
  have hr0 : 0 ≤ Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 lam Y) := by
    have : 0 ≤ 2 - Y := by linarith
    positivity
  have hr1 : Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 lam Y) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hrr : |Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 lam Y)| ≤ 1 := by
    rw [abs_of_nonneg hr0]; exact hr1
  unfold regOutCtF
  refine regAbs_add_mul_le ?_ ?_
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h1 : |(1 - 2 * Y) / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have := mul_le_mul h1 hlM (abs_nonneg _) (by norm_num)
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h1 : |1 - Y / 2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have := mul_le_mul h1 hlM (abs_nonneg _) (by norm_num)
    linarith

theorem continuousAt_regOutCtF {a b Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun lam => regOutCtF a b (ladderInnerMass 1 lam Y) Y) 0 := by
  have hY0 := hY.1
  unfold regOutCtF ladderInnerMass
  fun_prop (disch := (apply ne_of_gt; simp only [one_pow, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]; positivity))

theorem regIntervalIntegrable_fA :
    IntervalIntegrable (fun Y : ℝ => (1 - 2 * Y) * log Y + (2 - Y) / 2) volume 0 1 := by
  have h1 : IntervalIntegrable (fun Y : ℝ => (1 - 2 * Y) * log Y) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (by fun_prop)
  exact h1.add ((by fun_prop : Continuous fun Y : ℝ => (2 - Y) / 2).intervalIntegrable 0 1)

theorem regIntervalIntegrable_fB :
    IntervalIntegrable (fun Y : ℝ => (2 - Y) * log Y + (2 - Y) / 2) volume 0 1 := by
  have h1 : IntervalIntegrable (fun Y : ℝ => (2 - Y) * log Y) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (by fun_prop)
  exact h1.add ((by fun_prop : Continuous fun Y : ℝ => (2 - Y) / 2).intervalIntegrable 0 1)

/-- `∫₀¹ ((1 - 2Y) log Y + (2 - Y)/2) dY = 1/4`. -/
theorem regIntegral_fA :
    ∫ Y in (0 : ℝ)..1, ((1 - 2 * Y) * log Y + (2 - Y) / 2) = 1 / 4 := by
  have hc : ContinuousOn (fun Y : ℝ => (1 - Y) * (Y * log Y) + Y ^ 2 / 4) (Icc 0 1) :=
    ((continuous_const.sub continuous_id).mul Real.continuous_mul_log |>.add
      (by fun_prop)).continuousOn
  have hd : ∀ Y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun Y : ℝ => (1 - Y) * (Y * log Y) + Y ^ 2 / 4)
      ((1 - 2 * Y) * log Y + (2 - Y) / 2) Y := fun Y hY => by
    have h := (((hasDerivAt_id Y).const_sub 1).mul (Real.hasDerivAt_mul_log hY.1.ne')).add
      ((hasDerivAt_pow 2 Y).div_const 4)
    refine h.congr_deriv ?_
    simp only [id]
    norm_num
    ring
  have hi := regIntervalIntegrable_fA
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp

/-- `∫₀¹ ((2 - Y) log Y + (2 - Y)/2) dY = -1`. -/
theorem regIntegral_fB :
    ∫ Y in (0 : ℝ)..1, ((2 - Y) * log Y + (2 - Y) / 2) = -1 := by
  have hc : ContinuousOn (fun Y : ℝ => (2 - Y / 2) * (Y * log Y) - Y) (Icc 0 1) :=
    ((continuous_const.sub (continuous_id.div_const 2)).mul Real.continuous_mul_log |>.sub
      continuous_id).continuousOn
  have hd : ∀ Y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun Y : ℝ => (2 - Y / 2) * (Y * log Y) - Y)
      ((2 - Y) * log Y + (2 - Y) / 2) Y := fun Y hY => by
    have h := ((((hasDerivAt_id Y).div_const 2).const_sub 2).mul
      (Real.hasDerivAt_mul_log hY.1.ne')).sub (hasDerivAt_id Y)
    refine h.congr_deriv ?_
    simp only [id]
    ring
  have hi := regIntervalIntegrable_fB
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp

theorem regOutCtF_zero {a b Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    regOutCtF a b (ladderInnerMass 1 0 Y) Y =
      a * ((1 - 2 * Y) * log Y + (2 - Y) / 2) + b * ((2 - Y) * log Y + (2 - Y) / 2) := by
  have hY0 := hY.1.ne'
  have e : ladderInnerMass 1 0 Y = Y ^ 2 := by unfold ladderInnerMass; ring
  unfold regOutCtF
  rw [e, log_pow]
  push_cast
  field_simp

theorem integral_regOutCtF_zero (a b : ℝ) :
    ∫ Y in (0 : ℝ)..1, regOutCtF a b (ladderInnerMass 1 0 Y) Y = a / 4 - b := by
  have hA := regIntervalIntegrable_fA
  have hB := regIntervalIntegrable_fB
  have e : ∫ Y in (0 : ℝ)..1, regOutCtF a b (ladderInnerMass 1 0 Y) Y =
      ∫ Y in (0 : ℝ)..1, (a * ((1 - 2 * Y) * log Y + (2 - Y) / 2) +
        b * ((2 - Y) * log Y + (2 - Y) / 2)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact regOutCtF_zero ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  rw [e, intervalIntegral.integral_add (hA.const_mul a) (hB.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, regIntegral_fA,
    regIntegral_fB]
  ring

theorem regIntervalIntegrable_logY (c d : ℝ) :
    IntervalIntegrable (fun Y : ℝ => c * (d + 2 * -log Y)) volume 0 1 :=
  (intervalIntegrable_const.add
    (intervalIntegral.intervalIntegrable_log'.neg.const_mul 2)).const_mul c

theorem measurable_regOutCtF (a b lam : ℝ) :
    Measurable fun Y => regOutCtF a b (ladderInnerMass 1 lam Y) Y := by
  unfold regOutCtF ladderInnerMass
  fun_prop

theorem tendsto_integral_regOutCtF (a b : ℝ) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, regOutCtF a b (ladderInnerMass 1 lam Y) Y) (𝓝[>] 0)
      (𝓝 (a / 4 - b)) := by
  rw [← integral_regOutCtF_zero a b]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => (|a| + |b|) * (1 + 2 * -log Y))
    (Eventually.of_forall fun lam => (measurable_regOutCtF a b lam).aestronglyMeasurable) ?_
    (regIntervalIntegrable_logY _ _) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact abs_regOutCtF_le (by nlinarith [hlam.1, hlam.2]) ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact (continuousAt_regOutCtF ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).tendsto.mono_left
      nhdsWithin_le_nhds

/-! ### The two-loop part -/

theorem measurable_scOutRegS_uncurry (t lam : ℝ) :
    Measurable (uncurry fun Y x => scOutRegS t lam Y x) := by
  have h1 := measurable_selfGm_uncurry (√t) lam
  have h2 : Measurable (uncurry fun Y x => selfK2 Y x / hOut t x ^ 2) := by
    change Measurable fun p : ℝ × ℝ => selfK2 p.1 p.2 / hOut t p.2 ^ 2
    unfold selfK2 hOut ladderInnerMass
    fun_prop
  exact h1.add h2

theorem measurable_scOutRegS (t lam Y : ℝ) : Measurable fun x => scOutRegS t lam Y x :=
  (measurable_selfGm (√t) lam Y).add (by unfold selfK2 hOut ladderInnerMass; fun_prop)

theorem regIntervalIntegrable_scOutRegSDom (t Y : ℝ) :
    IntervalIntegrable (fun x => scOutRegSDom t Y x) volume 0 1 :=
  (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log'.neg).const_mul _

theorem regIntegral_scOutRegSDom (t Y : ℝ) :
    ∫ x in (0 : ℝ)..1, scOutRegSDom t Y x = 20 * (1 + 1 / t) * (2 + -log Y) := by
  unfold scOutRegSDom
  have h : ∫ x in (0 : ℝ)..1, (1 + -log Y + -log x) = 2 + -log Y := by
    have hl : IntervalIntegrable (fun x : ℝ => -log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'.neg
    rw [intervalIntegral.integral_add intervalIntegrable_const hl, intervalIntegral.integral_neg,
      integral_log]
    simp
    ring
  rw [intervalIntegral.integral_const_mul, h]

theorem intervalIntegrable_scOutRegS {t lam Y : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => scOutRegS t lam Y x) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, scOutRegS t lam Y x| ≤ 20 * (1 + 1 / t) * (2 + -log Y) := by
  obtain ⟨hi, hb⟩ := intervalIntegrable_of_abs_le (measurable_scOutRegS t lam Y)
    (regIntervalIntegrable_scOutRegSDom t Y) fun x hx => abs_scOutRegS_le ht hl hY hx
  exact ⟨hi, hb.trans (le_of_eq (regIntegral_scOutRegSDom t Y))⟩

theorem regIntervalIntegrable_dom2 (t : ℝ) :
    IntervalIntegrable (fun Y : ℝ => 20 * (1 + 1 / t) * (2 + -log Y)) volume 0 1 :=
  (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log'.neg).const_mul _

theorem intervalIntegrable_integral_scOutRegS {t lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, scOutRegS t lam Y x) volume 0 1 :=
  (intervalIntegrable_of_abs_le (measurable_intervalIntegral_of_uncurry
    (measurable_scOutRegS_uncurry t lam)) (regIntervalIntegrable_dom2 t)
    fun _ hY => (intervalIntegrable_scOutRegS ht hl hY).2).1

/-- **`∬ scOutRegS(λ) → ∬ scOutSG` as `λ → 0⁺`.** -/
theorem tendsto_integral_scOutRegS {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, scOutRegS t lam Y x) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, scOutRegS t 0 Y x)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 20 * (1 + 1 / t) * (2 + -log Y))
    (Eventually.of_forall fun lam => (measurable_intervalIntegral_of_uncurry
      (measurable_scOutRegS_uncurry t lam)).aestronglyMeasurable) ?_
    (regIntervalIntegrable_dom2 t) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact (intervalIntegrable_scOutRegS ht (by nlinarith [hlam.1, hlam.2])
      ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).2
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => scOutRegSDom t Y x)
      (Eventually.of_forall fun lam => (measurable_scOutRegS t lam Y).aestronglyMeasurable) ?_
      (regIntervalIntegrable_scOutRegSDom t Y) ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]
      exact abs_scOutRegS_le ht (by nlinarith [hlam.1, hlam.2]) hYo
        ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      exact (continuousAt_scOutRegS ht hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).tendsto.mono_left
        nhdsWithin_le_nhds

/-! ### The link -/

theorem scOutSRep_split {t lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) :
    scOutSRep t lam = 2 * ((∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, scOutRegS t lam Y x) +
      ∫ Y in (0 : ℝ)..1, regOutCtF (selfVk (√t)) (selfVm (√t)) (ladderInnerMass 1 lam Y) Y) := by
  have hid := selfVk_add_selfVm_add_oneLoopF2 (sqrt_pos.2 ht)
  have iS := intervalIntegrable_integral_scOutRegS ht hl
  have iC : IntervalIntegrable
      (fun Y => regOutCtF (selfVk (√t)) (selfVm (√t)) (ladderInnerMass 1 lam Y) Y) volume 0 1 :=
    (intervalIntegrable_of_abs_le (measurable_regOutCtF _ _ lam) (regIntervalIntegrable_logY _ 1)
      fun Y hY => abs_regOutCtF_le hl hY).1
  have e : scOutSRep t lam = 2 * ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, scOutRegS t lam Y x) +
      regOutCtF (selfVk (√t)) (selfVm (√t)) (ladderInnerMass 1 lam Y) Y) := by
    unfold scOutSRep
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    have hM : ladderInnerMass 1 lam Y ≠ 0 :=
      ((pow_pos hYo.1 2).trans_le (regMassOut_bounds hl hYo).1).ne'
    rw [← regOutCt_eq hid hM]
    simp only [scOutRegS]
    ring
  rw [e, intervalIntegral.integral_add iS iC]

theorem scOutSCt_eq_regOut {t : ℝ} (ht : 0 < t) :
    scOutSCt t = 2 * (selfVk (√t) / 4 - selfVm (√t)) := by
  have hid := selfVk_add_selfVm_add_oneLoopF2 (sqrt_pos.2 ht)
  unfold scOutSCt
  linarith

/-- **The regulator link of the outer-massive self-energy group**: for `t > 0`,
`scOutSRep t λ → scOutS t` as `λ → 0⁺`. -/
theorem tendsto_scOutSRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => scOutSRep t lam) (𝓝[>] 0) (𝓝 (scOutS t)) := by
  have h := ((tendsto_integral_scOutRegS ht).add
    (tendsto_integral_regOutCtF (selfVk (√t)) (selfVm (√t)))).const_mul 2
  have e : scOutS t = 2 * ((∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, scOutRegS t 0 Y x) +
      (selfVk (√t) / 4 - selfVm (√t))) := by
    rw [scOutS, scOutSCt_eq_regOut ht]
    simp only [scOutRegS_zero]
    ring
  rw [e]
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
  exact (scOutSRep_split ht (by nlinarith [hlam.1, hlam.2])).symm

end QED.ChainProof.SetCK
