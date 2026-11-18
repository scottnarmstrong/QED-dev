/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLLinkCt
public import QED.TwoLoop.UnitLLinkOuter
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: the limit `λ → 0` of the finite-`λ` representation (3.4)

Section 3.4 of `docs/TWO-LOOP-UNITS.md`, stage (3) of the L link. At photon mass `λ` and `Λ = ∞`
the document represents the L unit as (eq. (3.4), `m = 1`)

`L(λ) = ∫₀¹ dY {∫₀¹ G(λ; Y, x) dx - F₂⁽²⁾(λ) · CT(λ; Y)}`,

with `G` the `x`-integrand (`ladderG`) and `CT(λ; Y) = Y(Y² + 2Y - 2)/(2M) - (Y/2) log M`
(`ladderCtBracket`), `M = Y² + (1 - Y) λ²`. The term `T₁` (`ladderT1`) carries the soft outer
photon; it factorizes, `T₁(λ; Y, x) = -(Y²(1-Y)/M(Y)) · x(1-x)³/M(x)`, so that
`∬ T₁ = -F₂⁽²⁾(λ) · J(λ)` with `J(λ) = ∫₀¹ x(1-x)³/(x² + (1-x)λ²) dx` (`outerSoftJ`,
`integral_integral_ladderT1`). Hence, with `R = G - T₁` (`ladderR`),

`L(λ) = ∬ R(λ) - F₂⁽²⁾(λ) (J(λ) + ∫₀¹ CT(λ; Y) dY)`

(whenever `G(λ; Y, ·)` and `Y ↦ ∫ R dx` are integrable). This file proves:

* `tendsto_oneLoopF2_one`: `F₂⁽²⁾(λ) → 1/2`;
* `tendsto_outerSoftJ_add_integral_ladderCtBracket`: `J(λ) + ∫₀¹ CT(λ; Y) dY → -1/3`: the two
  logarithms `∓ log λ` (soft outer photon, soft inner photon) cancel inside one integrand, which
  is then bounded by a constant (dominated convergence);
* `tendsto_ladderCtTotal`: so `-F₂⁽²⁾(λ)(J(λ) + ∫ CT) → 1/6`, the constant of (3.6);
* `tendsto_ladderR`: `R(λ; Y, x) → R₀(Y, x)` pointwise on `(0,1)²`
  (`QED.TwoLoop.UnitLLink.ladderR0`),
  and `∫₀¹ R₀(Y, x) dx = K_L(Y)` (`QED.TwoLoop.UnitLLink.integral_ladderR0`);
* `tendsto_of_tendsto_integral_ladderR`: **if** `∬ R(λ) → ∬ R₀`, then
  `∬ R(λ) - F₂⁽²⁾(λ)(J(λ) + ∫ CT) → 11/48 + π²/18 = 11/48 + ζ(2)/3`, the value of (3.6).

**Proved in `QED.TwoLoop.UnitLLinkDominated`** (the remaining part of stage (3)): the convergence
`∬ R(λ) → ∬ R₀`, from the uniform bound `|R| ≤ 17 (1 - log x - log Y) / max(x, Y)` for `|λ| ≤ 1`
(`QED.TwoLoop.UnitLLinkDominatedBound`), and the integrability and Fubini facts needed for the
decomposition above; the unconditional limit of (3.4) is `tendsto_ladderRep`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitLLink

open QED.TwoLoop.Units

/-! ### The objects of eq. (3.4) at `m = 1` -/

/-- The counterterm bracket of eq. (3.4): `CT(λ; Y) = Y(Y² + 2Y - 2)/(2M) - (Y/2) log M`,
`M = Y² + (1 - Y) λ²` (the `δ₁` integrand of section 3.2 with `log M_Λ` removed). -/
noncomputable def ladderCtBracket (lam Y : ℝ) : ℝ :=
  Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 lam Y) - Y / 2 * log (ladderInnerMass 1 lam Y)

/-- The soft-outer-photon integral `J(λ) = ∫₀¹ x(1-x)³/(x² + (1-x)λ²) dx`. -/
noncomputable def outerSoftJ (lam : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x * (1 - x) ^ 3 / ladderInnerMass 1 lam x

/-- **The `x`-integrand `G` of eq. (3.4)**, with `c = Y(1-Y)`, `M = Y² + (1-Y)λ²`,
`h = (x² + (1-x)λ²)/x`, `ζ = (1-x)/x`, `q₀ = (3Y-2) + (4Y-Y²-2)ζ - 2cζ²`,
`Q = c(8M + 9ch - xq₀)`:
`G = Y x (1-x)/2 · [x q₀/(M h) - 9c/M - log(M + c h)/h + Q/M² · log(1 + M/(c h))]`. -/
noncomputable def ladderG (lam Y x : ℝ) : ℝ :=
  Y * x * (1 - x) / 2 *
    (x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
        2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) /
        (ladderInnerMass 1 lam Y * (ladderInnerMass 1 lam x / x)) -
      9 * (Y * (1 - Y)) / ladderInnerMass 1 lam Y -
      log (ladderInnerMass 1 lam Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) /
        (ladderInnerMass 1 lam x / x) +
      Y * (1 - Y) * (8 * ladderInnerMass 1 lam Y +
          9 * (Y * (1 - Y)) * (ladderInnerMass 1 lam x / x) -
          x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
            2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2)) / ladderInnerMass 1 lam Y ^ 2 *
        log (1 + ladderInnerMass 1 lam Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x))))

/-- **The soft-outer-photon term** `T₁ = -Y c x(1-x)³ / (M (x² + (1-x)λ²))` of section 3.4. -/
noncomputable def ladderT1 (lam Y x : ℝ) : ℝ :=
  -(Y * (Y * (1 - Y)) * x * (1 - x) ^ 3 / (ladderInnerMass 1 lam Y * ladderInnerMass 1 lam x))

/-- **The remainder** `R = G - T₁` of section 3.4. -/
noncomputable def ladderR (lam Y x : ℝ) : ℝ := ladderG lam Y x - ladderT1 lam Y x

/-! ### The soft-outer-photon term factorizes -/

theorem ladderT1_eq (lam Y x : ℝ) :
    ladderT1 lam Y x = -(Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 lam Y) *
      (x * (1 - x) ^ 3 / ladderInnerMass 1 lam x) := by
  unfold ladderT1
  ring

/-- **`∬ T₁ = -F₂⁽²⁾(λ) J(λ)`**. -/
theorem integral_integral_ladderT1 (lam : ℝ) :
    ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderT1 lam Y x =
      -(oneLoopF2 1 lam * outerSoftJ lam) := by
  simp only [ladderT1_eq, intervalIntegral.integral_const_mul, outerSoftJ, oneLoopF2,
    intervalIntegral.integral_mul_const, neg_mul, intervalIntegral.integral_neg]

/-! ### `F₂⁽²⁾(λ) → 1/2` -/

theorem ladderInnerMass_one_ge {lam Y : ℝ} (hY : Y ≤ 1) : Y ^ 2 ≤ ladderInnerMass 1 lam Y := by
  unfold ladderInnerMass
  have : 0 ≤ (1 - Y) * lam ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

theorem ladderInnerMass_one_le {lam Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) 1) (hlam : |lam| ≤ 1) :
    ladderInnerMass 1 lam Y ≤ 1 := by
  unfold ladderInnerMass
  have h1 : lam ^ 2 ≤ 1 := by
    have := sq_abs lam ▸ pow_le_pow_left₀ (abs_nonneg lam) hlam 2
    simpa using this
  have h2 : (1 - Y) * lam ^ 2 ≤ (1 - Y) * 1 := mul_le_mul_of_nonneg_left h1 (by linarith [hY.2])
  nlinarith [hY.1, hY.2]

/-- **`F₂⁽²⁾(λ) → 1/2` as `λ → 0⁺`.** -/
theorem tendsto_oneLoopF2_one : Tendsto (oneLoopF2 1) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hlim : ∫ Y in (0 : ℝ)..1, (1 - Y) = 1 / 2 := by
    simp only [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id,
      integral_id, intervalIntegral.integral_const]
    norm_num
  rw [← hlim]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    intervalIntegrable_const ?_
  · refine Eventually.of_forall fun lam => ?_
    exact (by unfold ladderInnerMass; fun_prop :
      Measurable fun Y : ℝ => Y ^ 2 * (1 - Y) * 1 ^ 2 /
        ladderInnerMass 1 lam Y).aestronglyMeasurable
  · refine Eventually.of_forall fun lam => ae_of_all _ fun Y hY => ?_
    rw [uIoc_of_le zero_le_one] at hY
    have hM := ladderInnerMass_one_ge (lam := lam) hY.2
    have hY2 : 0 < Y ^ 2 := by have := hY.1; positivity
    have hnum : 0 ≤ Y ^ 2 * (1 - Y) * 1 ^ 2 := by
      have : 0 ≤ 1 - Y := by linarith [hY.2]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum (hY2.le.trans hM))]
    rw [div_le_one (hY2.trans_le hM)]
    have : Y ^ 2 * (1 - Y) ≤ Y ^ 2 := by nlinarith [hY.1]
    linarith
  · refine ae_of_all _ fun Y hY => ?_
    rw [uIoc_of_le zero_le_one] at hY
    have hY0 : Y ≠ 0 := hY.1.ne'
    have hc : ContinuousAt
        (fun lam : ℝ => Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 lam Y) 0 := by
      unfold ladderInnerMass
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hY0])
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    convert h using 2
    simp only [ladderInnerMass]
    field_simp
    ring

/-! ### `J(λ) + ∫ CT → -1/3` -/

/-- The combined integrand of `J(λ) + ∫ CT(λ; ·)`: `Y²(-2 + 7Y/2 - Y²)/M - (Y/2) log M`. -/
noncomputable def softSum (lam Y : ℝ) : ℝ :=
  Y ^ 2 * (-2 + 7 / 2 * Y - Y ^ 2) / ladderInnerMass 1 lam Y - Y / 2 * log (ladderInnerMass 1 lam Y)

theorem outerSoftJ_add_eq {lam : ℝ} (hlam : 0 < lam) :
    outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y =
      ∫ Y in (0 : ℝ)..1, softSum lam Y := by
  have hM : ∀ Y ∈ Icc (0 : ℝ) 1, 0 < ladderInnerMass 1 lam Y := fun Y hY =>
    ladderInnerMass_pos one_pos hlam hY
  have hMc : ContinuousOn (fun Y => ladderInnerMass 1 lam Y) (Icc 0 1) := by
    unfold ladderInnerMass; fun_prop
  have h1 : IntervalIntegrable (fun x => x * (1 - x) ^ 3 / ladderInnerMass 1 lam x) volume 0 1 :=
    (ContinuousOn.div (by fun_prop) hMc fun Y hY => (hM Y hY).ne').intervalIntegrable_of_Icc
      zero_le_one
  have h2 : IntervalIntegrable (ladderCtBracket lam) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    exact (ContinuousOn.div (by fun_prop) (continuousOn_const.mul hMc) fun Y hY =>
      mul_ne_zero two_ne_zero (hM Y hY).ne').sub
      ((by fun_prop : ContinuousOn (fun Y : ℝ => Y / 2) (Icc 0 1)).mul
        (hMc.log fun Y hY => (hM Y hY).ne'))
  rw [outerSoftJ, ← intervalIntegral.integral_add h1 h2]
  refine intervalIntegral.integral_congr fun Y hY => ?_
  rw [uIcc_of_le zero_le_one] at hY
  have hM0 := (hM Y hY).ne'
  simp only [ladderCtBracket, softSum]
  field_simp
  ring

/-- `-Y log Y ≤ 1 - Y` on `(0, 1]` (from `log Y ≥ 1 - 1/Y`). -/
theorem neg_mul_log_le_one_sub {Y : ℝ} (hY : 0 < Y) : -(Y * log Y) ≤ 1 - Y := by
  have h := Real.one_sub_inv_le_log_of_pos hY
  have : Y * (1 - Y⁻¹) ≤ Y * log Y := mul_le_mul_of_nonneg_left h hY.le
  have e : Y * (1 - Y⁻¹) = Y - 1 := by field_simp
  linarith

theorem abs_softSum_le {lam Y : ℝ} (hlam : |lam| ≤ 1) (hY : Y ∈ Ioc (0 : ℝ) 1) :
    |softSum lam Y| ≤ 8 := by
  have hYI : Y ∈ Icc (0 : ℝ) 1 := ⟨hY.1.le, hY.2⟩
  have hY2 : 0 < Y ^ 2 := by have := hY.1; positivity
  have hge := ladderInnerMass_one_ge (lam := lam) hY.2
  have hle := ladderInnerMass_one_le hYI hlam
  have hMpos : 0 < ladderInnerMass 1 lam Y := hY2.trans_le hge
  -- the rational part
  have hr : |Y ^ 2 * (-2 + 7 / 2 * Y - Y ^ 2) / ladderInnerMass 1 lam Y| ≤ 7 := by
    rw [abs_div, abs_mul, abs_of_pos hY2, abs_of_pos hMpos]
    have hp : |-2 + 7 / 2 * Y - Y ^ 2| ≤ 7 := by
      rw [abs_le]; constructor <;> nlinarith [hY.1, hY.2]
    rw [div_le_iff₀ hMpos]
    calc Y ^ 2 * |-2 + 7 / 2 * Y - Y ^ 2| ≤ ladderInnerMass 1 lam Y * 7 := by
          have := mul_le_mul hge hp (abs_nonneg _) hMpos.le
          linarith
      _ = 7 * ladderInnerMass 1 lam Y := by ring
  -- the logarithmic part
  have hl : |Y / 2 * log (ladderInnerMass 1 lam Y)| ≤ 1 := by
    have hlog0 : log (ladderInnerMass 1 lam Y) ≤ 0 := Real.log_nonpos hMpos.le hle
    have hlog1 : 2 * log Y ≤ log (ladderInnerMass 1 lam Y) := by
      have h := Real.log_le_log hY2 hge
      rw [Real.log_pow] at h
      push_cast at h
      exact h
    have hYl := neg_mul_log_le_one_sub hY.1
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith [hY.1]) hlog0)]
    nlinarith [hY.1]
  unfold softSum
  calc |Y ^ 2 * (-2 + 7 / 2 * Y - Y ^ 2) / ladderInnerMass 1 lam Y -
        Y / 2 * log (ladderInnerMass 1 lam Y)|
      ≤ |Y ^ 2 * (-2 + 7 / 2 * Y - Y ^ 2) / ladderInnerMass 1 lam Y| +
        |Y / 2 * log (ladderInnerMass 1 lam Y)| := abs_sub _ _
    _ ≤ 8 := by linarith

theorem tendsto_softSum {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun lam => softSum lam Y) (𝓝 0) (𝓝 ((-2 + 7 / 2 * Y - Y ^ 2) - Y * log Y)) := by
  have hY0 : Y ≠ 0 := hY.ne'
  have hc : ContinuousAt (fun lam => softSum lam Y) 0 := by
    unfold softSum ladderInnerMass
    refine ContinuousAt.sub (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hY0]))
      (ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) (by simp [hY0])))
  convert hc.tendsto using 2
  simp only [softSum, ladderInnerMass]
  rw [show Y ^ 2 * 1 ^ 2 + (1 - Y) * (0 : ℝ) ^ 2 = Y ^ 2 by ring, Real.log_pow]
  field_simp
  push_cast
  ring

/-- `∫₀¹ Y log Y = -1/4`, with integrability. -/
theorem intervalIntegrable_and_integral_mul_log :
    IntervalIntegrable (fun Y : ℝ => Y * log Y) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, Y * log Y = -1 / 4 := by
  have hi : IntervalIntegrable (fun Y : ℝ => Y * log Y) volume 0 1 :=
    continuous_mul_log.intervalIntegrable 0 1
  refine ⟨hi, ?_⟩
  have hc : ContinuousOn (fun x : ℝ => x * (x * log x) / 2 - x ^ 2 / 4) (Icc 0 1) :=
    ((continuous_id.mul continuous_mul_log).div_const 2 |>.sub (by fun_prop)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc (fun x hx => ?_) hi]
  · simp; norm_num
  · have h1 := ((hasDerivAt_id' x).mul ((hasDerivAt_id' x).mul
      (hasDerivAt_log hx.1.ne'))).div_const 2 |>.sub ((hasDerivAt_pow 2 x).div_const 4)
    refine h1.congr_deriv ?_
    have := hx.1.ne'
    simp only [Pi.mul_apply]
    field_simp
    ring

theorem integral_softSum_limit :
    ∫ Y in (0 : ℝ)..1, ((-2 + 7 / 2 * Y - Y ^ 2) - Y * log Y) = -1 / 3 := by
  have hp : IntervalIntegrable (fun Y : ℝ => -2 + 7 / 2 * Y - Y ^ 2) volume 0 1 :=
    (by fun_prop : Continuous fun Y : ℝ => -2 + 7 / 2 * Y - Y ^ 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hp intervalIntegrable_and_integral_mul_log.1,
    intervalIntegrable_and_integral_mul_log.2]
  have e : ∫ Y in (0 : ℝ)..1, (-2 + 7 / 2 * Y - Y ^ 2) = -7 / 12 := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul]
    · simp only [intervalIntegral.integral_const, integral_id, integral_pow]
      norm_num
    all_goals first
      | exact intervalIntegrable_const
      | exact (intervalIntegral.intervalIntegrable_id.const_mul _)
      | exact (by fun_prop : Continuous fun Y : ℝ => Y ^ 2).intervalIntegrable 0 1
      | exact (intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_id.const_mul _))
  rw [e]
  norm_num

/-- **`J(λ) + ∫₀¹ CT(λ; Y) dY → -1/3` as `λ → 0⁺`**: the logarithms of the soft outer photon and
of the soft inner photon cancel. -/
theorem tendsto_outerSoftJ_add_integral_ladderCtBracket :
    Tendsto (fun lam => outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y) (𝓝[>] 0)
      (𝓝 (-1 / 3)) := by
  rw [← integral_softSum_limit]
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  have hT : Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, softSum lam Y) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ((-2 + 7 / 2 * Y - Y ^ 2) - Y * log Y))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 8) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun lam => ?_
      exact (by unfold softSum ladderInnerMass; fun_prop :
        Measurable fun Y : ℝ => softSum lam Y).aestronglyMeasurable
    · filter_upwards [hev] with lam hlam
      refine ae_of_all _ fun Y hY => ?_
      rw [uIoc_of_le zero_le_one] at hY
      rw [Real.norm_eq_abs]
      exact abs_softSum_le (by rw [abs_of_pos hlam.1]; exact hlam.2.le) hY
    · refine ae_of_all _ fun Y hY => ?_
      rw [uIoc_of_le zero_le_one] at hY
      exact (tendsto_softSum hY.1).mono_left nhdsWithin_le_nhds
  refine hT.congr' ?_
  filter_upwards [hev] with lam hlam
  exact (outerSoftJ_add_eq hlam.1).symm

/-- **The counterterm-and-soft total tends to `1/6`**:
`-F₂⁽²⁾(λ) (J(λ) + ∫₀¹ CT(λ; Y) dY) → 1/6`, the constant of eq. (3.6). -/
theorem tendsto_ladderCtTotal :
    Tendsto (fun lam =>
        -(oneLoopF2 1 lam * (outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y)))
      (𝓝[>] 0) (𝓝 (1 / 6)) := by
  have h := (tendsto_oneLoopF2_one.mul tendsto_outerSoftJ_add_integral_ladderCtBracket).neg
  convert h using 2
  norm_num

/-! ### The remainder: pointwise limit and the assembly -/

/-- **`R(λ; Y, x) → R₀(Y, x)` as `λ → 0`**, for `0 < Y, x < 1`. -/
theorem tendsto_ladderR {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun lam => ladderR lam Y x) (𝓝 0) (𝓝 (ladderR0 Y x)) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have h1Y : 0 < 1 - Y := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hc : ContinuousAt (fun lam => ladderR lam Y x) 0 := by
    unfold ladderR ladderG ladderT1 ladderInnerMass
    fun_prop (disch := (apply ne_of_gt; simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero]; positivity))
  have hW := ladderW_pos ⟨hY0, hY1⟩ hx0.le
  have hM : ladderInnerMass 1 0 Y = Y ^ 2 := by unfold ladderInnerMass; ring
  have hMx : ladderInnerMass 1 0 x = x ^ 2 := by unfold ladderInnerMass; ring
  have hl1 : log (Y ^ 2 + Y * (1 - Y) * (x ^ 2 / x)) = log Y + log (ladderW Y x) := by
    rw [← Real.log_mul hY0.ne' hW.ne']
    congr 1
    unfold ladderW
    field_simp
  have hl2 : log (1 + Y ^ 2 / (Y * (1 - Y) * (x ^ 2 / x))) =
      log (ladderW Y x) - log (1 - Y) - log x := by
    rw [sub_sub, ← Real.log_mul h1Y.ne' hx0.ne', ← Real.log_div hW.ne' (by positivity)]
    congr 1
    unfold ladderW
    field_simp
    ring
  have hval : ladderR 0 Y x = ladderR0 Y x := by
    simp only [ladderR, ladderG, ladderT1, hM, hMx, hl1, hl2, ladderR0, ladderP]
    generalize log Y = a
    generalize log x = b
    generalize log (1 - Y) = c
    generalize log (ladderW Y x) = d
    have := hY0.ne'
    have := hx0.ne'
    have := h1Y.ne'
    field_simp
    ring
  rw [← hval]
  exact hc.tendsto

/-- **The assembly of stage (3)**: if the remainder integral converges, `∬ R(λ) → ∬ R₀`, then
`∬ R(λ) - F₂⁽²⁾(λ)(J(λ) + ∫ CT) → 11/48 + π²/18 = 11/48 + ζ(2)/3`, the value of eq. (3.6). -/
theorem tendsto_of_tendsto_integral_ladderR
    (hR : Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR lam Y x) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR0 Y x))) :
    Tendsto (fun lam => (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR lam Y x) -
        oneLoopF2 1 lam * (outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y))
      (𝓝[>] 0) (𝓝 (11 / 48 + π ^ 2 / 18)) := by
  have hK : ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR0 Y x =
      ∫ Y in (0 : ℝ)..1, ladderKernel Y := by
    refine intervalIntegral.integral_congr_uIoo fun Y hY => ?_
    rw [uIoo_of_le zero_le_one] at hY
    exact integral_ladderR0 hY
  rw [hK] at hR
  have h := hR.add tendsto_ladderCtTotal
  rw [show (∫ Y in (0 : ℝ)..1, ladderKernel Y) + 1 / 6 = 11 / 48 + π ^ 2 / 18 by
    rw [← ladderUnit_value]; ring] at h
  refine h.congr fun lam => ?_
  ring

end QED.TwoLoop.UnitLLink

end
