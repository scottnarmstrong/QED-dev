/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKOuterL
public import QED.ChainProof.SetCKRegCt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Set (c), Stage K: the regulator link of the outer ladder placement

Helper level (no frozen statement). The outer ladder placement at photon mass `λ` on the inner
(massless) line and `Λ = ∞` is the representation (3.4) of `docs/TWO-LOOP-UNITS.md` with the two
photon masses separated (outer mass² `t`, inner mass `λ`):

`lOutRep t λ = ∫₀¹ dY [∫₀¹ dx G(√t, λ; Y, x) - F₂(t) CT(λ; Y)]` (`lOutRep`),

`G = ladderGm` (outer mass first). This file proves the link to the Stage K piece `lOuter`:

* `abs_gForm_outer_le`, `abs_ladderGm_le_of_sq_le_one`: `|G(la, lb; Y, x)| ≤ 4(1 + 1/h)²` with
  `h = M_la(x)/x`, for every inner mass `|lb| ≤ 1` (the bound of `abs_outerG_le`, which is the
  case `lb = 0`, with `Y² ≤ M ≤ 1` in place of `M = Y²`);
* `tendsto_integral_ladderGm_outer`: `∬ G(√t, λ) → ∬ G(√t, 0)` as `λ → 0⁺` (dominated
  convergence with a constant, since `h_t ≥ (3/4) min(1, t)`);
* **`tendsto_lOutRep`**: `lOutRep t λ + F₂(t) log λ → lOuter t` as `λ → 0⁺`, for `t > 0`; the
  infrared logarithm is that of the counterterm, `∫₀¹ CT(λ) - log λ → 3/2`
  (`tendsto_integral_ladderCtBracket_sub_log`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- **The uniform bound of the outer integrand for any inner mass** with `Y² ≤ M ≤ 1`. -/
theorem abs_gForm_outer_le {x Y h M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hh : 0 < h) (hMY : Y ^ 2 ≤ M) (hM1 : M ≤ 1) :
    |gForm (Y * x * (1 - x) / 2) (Y * (1 - Y)) (outerQ x Y) h M (log (M + Y * (1 - Y) * h))
      (log (1 + M / (Y * (1 - Y) * h)))| ≤ 4 * (1 + 1 / h) ^ 2 := by
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hc : 0 < Y * (1 - Y) := mul_pos hY0 hY1
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hMY
  have hA := outer_mass_pos hh (Ioo_subset_Icc_self hY)
  set A := h + (1 - h) * Y with hA_def
  have hYA : Y * A ≤ M + Y * (1 - Y) * h := by
    have : Y ^ 2 + Y * (1 - Y) * h = Y * A := by rw [hA_def]; ring
    linarith
  set r := 1 / h with hr_def
  have hr : 0 < r := by positivity
  have hrh : r * h = 1 := by rw [hr_def]; field_simp
  have hinvA : 1 / A ≤ 1 + r := by
    rcases le_or_gt h 1 with h1 | h1
    · have : h ≤ A := by rw [hA_def]; nlinarith
      have : 1 / A ≤ 1 / h := one_div_le_one_div_of_le hh this
      linarith
    · have : 1 ≤ A := by rw [hA_def]; nlinarith
      have : 1 / A ≤ 1 := by rw [div_le_one hA]; exact this
      linarith
  rw [gForm_eq_phi hM.ne' hh.ne' hc.ne']
  obtain ⟨hW0, hW1⟩ := phi_weight_bounds hc hh hM
  set u := M / (Y * (1 - Y) * h) with hu_def
  have hu0 : 0 ≤ u := by positivity
  set B := log (1 + u) with hB_def
  have hB0 : 0 ≤ B := log_one_add_nonneg hu0
  have hBu : B ≤ u := log_one_add_le_self hu0
  set W := Y * (1 - Y) * (u - B) / M ^ 2 with hW_def
  have hhW : h * W ≤ 1 / (Y * A) :=
    hW1.trans (one_div_le_one_div_of_le (by positivity) hYA)
  have hW : W ≤ r / (Y * A) := by
    have e : r / (Y * A) = (1 / (Y * A)) / h := by rw [hr_def]; field_simp
    rw [e, le_div_iff₀ hh, mul_comm]
    exact hhW
  have hq := mul_abs_outerQ_le hx hY
  set z := M + Y * (1 - Y) * h with hz_def
  have hz : 0 < z := by positivity
  set P := Y * x * (1 - x) / 2 with hP_def
  have hP0 : 0 ≤ P := by positivity
  have hxx : x * (1 - x) ≤ 1 / 4 := c_le_quarter x
  have hcq : Y * (1 - Y) ≤ 1 / 4 := c_le_quarter Y
  have hP8 : P ≤ 1 / 8 := by
    have h1 : Y * (x * (1 - x)) ≤ 1 * (1 / 4) :=
      mul_le_mul hY.2.le hxx (by positivity) zero_le_one
    calc P = Y * (x * (1 - x)) / 2 := by rw [hP_def]; ring
      _ ≤ 1 * (1 / 4) / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
      _ = 1 / 8 := by norm_num
  have e : P * (Y * (1 - Y) * (outerQ x Y - 9 * (Y * (1 - Y)) * h) * (u - B) / M ^ 2 +
      8 * (Y * (1 - Y)) * B / M - log z / h) =
      P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W) +
        8 * P * (Y * (1 - Y)) * B / M - P * r * log z := by
    rw [hW_def, hr_def]
    ring
  rw [e]
  have t1 : |P * outerQ x Y * W| ≤ 5 / 4 * (r * (1 + r)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hW0]
    calc P * |outerQ x Y| * W ≤ P * |outerQ x Y| * (r / (Y * A)) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (1 - x) / 2 * (x * |outerQ x Y|) * r * (1 / A) := by
          rw [hP_def]; field_simp
      _ ≤ 1 / 2 * (5 / 2) * r * (1 + r) := by
          have h1 : (1 - x) / 2 ≤ 1 / 2 := by linarith
          have h2 : 0 ≤ x * |outerQ x Y| := by positivity
          have h3 : 0 ≤ 1 / A := by positivity
          have := mul_le_mul h1 hq h2 (by norm_num)
          have := mul_le_mul this hinvA h3 (by positivity)
          nlinarith
      _ = 5 / 4 * (r * (1 + r)) := by ring
  have t2 : |9 * P * (Y * (1 - Y)) * (h * W)| ≤ 9 / 32 * (1 + r) := by
    have hhW0 : 0 ≤ h * W := mul_nonneg hh.le hW0
    rw [abs_of_nonneg (by positivity)]
    calc 9 * P * (Y * (1 - Y)) * (h * W) ≤ 9 * P * (Y * (1 - Y)) * (1 / (Y * A)) :=
          mul_le_mul_of_nonneg_left hhW (by positivity)
      _ = 9 / 2 * (x * (1 - x)) * (Y * (1 - Y)) * (1 / A) := by rw [hP_def]; field_simp
      _ ≤ 9 / 2 * (1 / 4) * (1 / 4) * (1 + r) := by
          have h0 : 0 ≤ x * (1 - x) := by positivity
          gcongr
      _ = 9 / 32 * (1 + r) := by ring
  have t3 : |8 * P * (Y * (1 - Y)) * B / M| ≤ r := by
    rw [abs_of_nonneg (by positivity)]
    have h1 : 8 * P * (Y * (1 - Y)) * B / M ≤ 8 * P * (Y * (1 - Y)) * u / M := by
      gcongr
    have h2 : 8 * P * (Y * (1 - Y)) * u / M = 8 * P * r := by
      rw [hu_def, hr_def]; field_simp
    have := mul_le_mul_of_nonneg_right hP8 hr.le
    linarith
  have t4 : |P * r * log z| ≤ 1 / 8 * r + 1 / 32 + 1 / 8 * (r * (1 + r)) := by
    have hlz := abs_log_le_add_inv hz
    have hz1 : z ≤ 1 + h / 4 := by
      have := mul_le_mul_of_nonneg_right hcq hh.le
      linarith [hz_def]
    have hz2 : 1 / z ≤ 1 / (Y * A) := one_div_le_one_div_of_le (by positivity) hYA
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ P * r)]
    have h3 : P * r * (1 / (Y * A)) = x * (1 - x) / 2 * r * (1 / A) := by
      rw [hP_def]; field_simp
    have h4 : x * (1 - x) / 2 * r * (1 / A) ≤ 1 / 8 * (r * (1 + r)) := by
      have h0 : 0 ≤ x * (1 - x) := by positivity
      have := mul_le_mul hxx hinvA (by positivity) (by norm_num)
      calc x * (1 - x) / 2 * r * (1 / A) = r / 2 * (x * (1 - x) * (1 / A)) := by ring
        _ ≤ r / 2 * (1 / 4 * (1 + r)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 1 / 8 * (r * (1 + r)) := by ring
    have h5 : P * r * (1 + h / 4) ≤ 1 / 8 * r + 1 / 32 := by
      have : P * r * (1 + h / 4) = P * r + P * (r * h) / 4 := by ring
      rw [this, hrh]
      have := mul_le_mul_of_nonneg_right hP8 hr.le
      linarith
    calc P * r * |log z| ≤ P * r * (z + 1 / z) := mul_le_mul_of_nonneg_left hlz (by positivity)
      _ ≤ P * r * ((1 + h / 4) + 1 / (Y * A)) := by gcongr
      _ = P * r * (1 + h / 4) + P * r * (1 / (Y * A)) := by ring
      _ ≤ 1 / 8 * r + 1 / 32 + 1 / 8 * (r * (1 + r)) := by linarith
  have habs := abs_sub (P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W) +
    8 * P * (Y * (1 - Y)) * B / M) (P * r * log z)
  have habs3 := abs_add_le (P * outerQ x Y * W - 9 * P * (Y * (1 - Y)) * (h * W))
    (8 * P * (Y * (1 - Y)) * B / M)
  have habs4 := abs_sub (P * outerQ x Y * W) (9 * P * (Y * (1 - Y)) * (h * W))
  have e3 : (1 + 1 / h) = 1 + r := by rw [hr_def]
  rw [e3]
  have hfin : 5 / 4 * (r * (1 + r)) + 9 / 32 * (1 + r) + r +
      (1 / 8 * r + 1 / 32 + 1 / 8 * (r * (1 + r))) ≤ 4 * (1 + r) ^ 2 := by
    nlinarith only [sq_nonneg r, hr.le]
  linarith only [t1, t2, t3, t4, habs, habs3, habs4, hfin]

theorem ladderInnerMass_mem {lb Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hlb : lb ^ 2 ≤ 1) :
    Y ^ 2 ≤ ladderInnerMass 1 lb Y ∧ ladderInnerMass 1 lb Y ≤ 1 := by
  unfold ladderInnerMass
  have h1 : 0 ≤ 1 - Y := by linarith [hY.2]
  constructor
  · nlinarith [mul_nonneg h1 (sq_nonneg lb)]
  · nlinarith [mul_le_mul_of_nonneg_left hlb h1, mul_nonneg hY.1.le h1]

/-- **The outer integrand is bounded uniformly in the inner mass** `|lb| ≤ 1`. -/
theorem abs_ladderGm_le_of_sq_le_one {la lb Y x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hh : 0 < ladderInnerMass 1 la x / x) (hlb : lb ^ 2 ≤ 1) :
    |ladderGm la lb Y x| ≤ 4 * (1 + 1 / (ladderInnerMass 1 la x / x)) ^ 2 := by
  obtain ⟨h1, h2⟩ := ladderInnerMass_mem hY hlb
  rw [ladderGm_eq_form]
  exact abs_gForm_outer_le hx hY hh h1 h2

/-- The ladder integrand is continuous in the inner mass, for `Y ∈ (0, 1]` and `h > 0`. -/
theorem continuous_ladderGm_inner {la Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hh : 0 < ladderInnerMass 1 la x / x) : Continuous fun lb => ladderGm la lb Y x := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  set h := ladderInnerMass 1 la x / x with h_def
  have hM : ∀ lb, 0 < ladderInnerMass 1 lb Y := fun lb =>
    ladderInnerMass_pos_of_pos hY.1 hY.2.le
  have hMc : Continuous fun lb => ladderInnerMass 1 lb Y := by unfold ladderInnerMass; fun_prop
  simp only [ladderGm_eq_form, gForm, ← h_def]
  have h1 : ∀ lb, ladderInnerMass 1 lb Y * h ≠ 0 := fun lb => mul_ne_zero (hM lb).ne' hh.ne'
  have h2 : ∀ lb, ladderInnerMass 1 lb Y ≠ 0 := fun lb => (hM lb).ne'
  have h3 : ∀ lb, ladderInnerMass 1 lb Y + Y * (1 - Y) * h ≠ 0 := fun lb => by
    have := hM lb; positivity
  have h4 : ∀ lb, 1 + ladderInnerMass 1 lb Y / (Y * (1 - Y) * h) ≠ 0 := fun lb => by
    have := hM lb; positivity
  have h5 : ∀ lb, ladderInnerMass 1 lb Y ^ 2 ≠ 0 := fun lb => pow_ne_zero 2 (hM lb).ne'
  fun_prop (disch := assumption)

/-- **The outer placement at inner photon mass `λ`**: the two-mass representation (3.4). -/
noncomputable def lOutRep (t lam : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) -
    oneLoopF2 1 (√t) * ladderCtBracket lam Y)

/-- The constant bounding the outer integrand. -/
noncomputable def lOutBd (t : ℝ) : ℝ := 4 * (1 + 1 / (3 / 4 * min 1 t)) ^ 2

theorem abs_ladderGm_outer_le {t lam Y x : ℝ} (ht : 0 < t) (hlam : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderGm (√t) lam Y x| ≤ lOutBd t := by
  have hh0 : 0 < 3 / 4 * min 1 t := by have := lt_min one_pos ht; positivity
  have hge := hOut_ge ht hx
  have hh : 0 < hOut t x := lt_of_lt_of_le hh0 hge
  refine (abs_ladderGm_le_of_sq_le_one hx hY hh hlam).trans ?_
  have : 1 / hOut t x ≤ 1 / (3 / 4 * min 1 t) := one_div_le_one_div_of_le hh0 hge
  have h1 : 0 ≤ 1 + 1 / hOut t x := by positivity
  unfold lOutBd
  change 4 * (1 + 1 / hOut t x) ^ 2 ≤ _
  gcongr

theorem abs_integral_ladderGm_outer_le {t lam Y : ℝ} (ht : 0 < t) (hlam : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) : |∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x| ≤ lOutBd t := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := lOutBd t) (f := fun x => ladderGm (√t) lam Y x) fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      rcases eq_or_lt_of_le hx.2 with h1 | h1
      · subst h1; simp [ladderGm, lOutBd]; positivity
      · rw [Real.norm_eq_abs]; exact abs_ladderGm_outer_le ht hlam hY ⟨hx.1, h1⟩
  simpa using this

theorem intervalIntegrable_ladderGm_outer {t lam Y : ℝ} (ht : 0 < t) (hlam : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => ladderGm (√t) lam Y x) volume 0 1 :=
  (intervalIntegrable_of_abs_le
    ((measurable_ladderGm_uncurry _ _).comp (measurable_const.prodMk measurable_id))
    (intervalIntegrable_const (c := lOutBd t))
    fun _ hx => abs_ladderGm_outer_le ht hlam hY hx).1

theorem intervalIntegrable_integral_ladderGm_outer {t lam : ℝ} (ht : 0 < t) (hlam : lam ^ 2 ≤ 1) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) volume 0 1 :=
  (intervalIntegrable_of_abs_le (measurable_intervalIntegral_of_uncurry
    (measurable_ladderGm_uncurry _ _)) (intervalIntegrable_const (c := lOutBd t))
    fun _ hY => abs_integral_ladderGm_outer_le ht hlam hY).1

/-- **`∬ G(√t, λ) → ∬ G(√t, 0)` as `λ → 0⁺`.** -/
theorem tendsto_integral_ladderGm_outer {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm (√t) 0 Y x)) := by
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ 2 ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with lam hl
    nlinarith [hl.1, hl.2]
  have hm : ∀ lam, Measurable fun Y => ∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x := fun lam =>
    measurable_intervalIntegral_of_uncurry (measurable_ladderGm_uncurry _ _)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => lOutBd t)
    (Eventually.of_forall fun lam => (hm lam).aestronglyMeasurable) ?_ intervalIntegrable_const ?_
  · filter_upwards [hev] with lam hl
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact abs_integral_ladderGm_outer_le ht hl ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => lOutBd t)
      (Eventually.of_forall fun lam => ((measurable_ladderGm_uncurry _ _).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
      intervalIntegrable_const ?_
    · filter_upwards [hev] with lam hl
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]
      exact abs_ladderGm_outer_le ht hl hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    · refine Eventually.of_forall fun x hx => ?_
      rw [uIoc_of_le zero_le_one] at hx
      have hh : 0 < ladderInnerMass 1 (√t) x / x :=
        div_pos (ladderInnerMass_pos one_pos (sqrt_pos.2 ht) ⟨hx.1.le, hx.2⟩) hx.1
      exact ((continuous_ladderGm_inner hYo hh).tendsto 0).mono_left nhdsWithin_le_nhds

theorem lOutRep_split {t lam : ℝ} (ht : 0 < t) (hlam : 0 < lam) (hlam1 : lam ^ 2 ≤ 1) :
    lOutRep t lam = (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm (√t) lam Y x) -
      oneLoopF2 1 (√t) * ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y := by
  rw [lOutRep, intervalIntegral.integral_sub (intervalIntegrable_integral_ladderGm_outer ht hlam1)
    ((intervalIntegrable_ladderCtBracket hlam).const_mul _), intervalIntegral.integral_const_mul]

/-- **The regulator link of the outer ladder placement**: for `t > 0`,
`lOutRep t λ + F₂(t) log λ → lOuter t` as `λ → 0⁺`. -/
theorem tendsto_lOutRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => lOutRep t lam + oneLoopF2 1 (√t) * log lam) (𝓝[>] 0)
      (𝓝 (lOuter t)) := by
  have := (tendsto_integral_ladderGm_outer ht).sub
    (tendsto_integral_ladderCtBracket_sub_log.const_mul (oneLoopF2 1 (√t)))
  rw [lOuter, mul_comm (3 / 2 : ℝ)]
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with lam hl
  rw [lOutRep_split ht hl.1 (by nlinarith [hl.1, hl.2])]
  ring

end QED.ChainProof.SetCK
