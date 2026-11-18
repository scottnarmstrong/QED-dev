/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLCloseLimit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: the joint regulator limit

Section 8 of `docs/TWO-LOOP-UNITS.md`, the L link, closed. With the decomposition of the L unit at
finite regulators (`QED.TwoLoop.UnitLLink.ladderTotal_eq`), every term other than the
representation (3.4) is bounded by a function of `Λ` alone that tends to `0`
(`abs_ladderTotal_sub_le`, `tendsto_ladderErrBound`); the representation (3.4) tends to
`11/48 + π²/18` as `λ → 0⁺` (`QED.TwoLoop.UnitLLink.tendsto_ladderRep`). Hence:

* `tendsto_ladderTotal`: `L(λ, Λ) → 11/48 + π²/18 = 11/48 + ζ(2)/3` as `(λ, Λ) → (0⁺, ∞)`
  **jointly**;
* `sixteen_pi_pow_four_mul_unitF2_L_eq_ladderTotal`: for `m = 1`, `0 < m_γ < Λ` and `d₁` fixed by the
  frozen charge condition, the model's L unit at charge `1`, normalized to the coefficient of
  `r² = (α/π)²`, is `L(m_γ, Λ)`;
* `unitF2_L_limit`: **the L unit link**. For every `η > 0` there are `δ > 0` and `R` such that for
  every parameter set with `m = 1`, `0 < m_γ < δ`, `Λ > R`, and every `d₁` satisfying the charge
  condition (K₀) (the other counterterms arbitrary),
  `‖16π⁴ · unitF2 .L (atUnitCharge P d₁ d₂ d_m d₃) - (11/48 + π²/18)‖ < η`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitLLink

open QED.WickModel QED.TwoLoop.UnitsRegulated

/-! ### Scalar bounds -/

theorem oneLoopF2_nonneg_le_one {μ : ℝ} (hμ : 0 < μ) :
    0 ≤ oneLoopF2 1 μ ∧ oneLoopF2 1 μ ≤ 1 := by
  have hint := intervalIntegrable_oneLoopF2_integrand one_pos hμ
  constructor
  · refine intervalIntegral.integral_nonneg zero_le_one fun Y hY => ?_
    have := ladderInnerMass_pos one_pos hμ hY
    have : 0 ≤ 1 - Y := by linarith [hY.2]
    have := hY.1
    positivity
  · calc oneLoopF2 1 μ ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
          refine intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
            fun Y hY => ?_
          have hM := ladderInnerMass_pos one_pos hμ hY
          rw [div_le_one hM]
          have := ladderInnerMass_one_ge (lam := μ) hY.2
          have : Y ^ 2 * (1 - Y) ≤ Y ^ 2 := by nlinarith [hY.1, hY.2]
          linarith
      _ = 1 := by simp

theorem oneLoopF2_le_inv_sq {Λ : ℝ} (hΛ : 1 ≤ Λ) : oneLoopF2 1 Λ ≤ 1 / Λ ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  calc oneLoopF2 1 Λ ≤ ∫ _ in (0 : ℝ)..1, 1 / Λ ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (intervalIntegrable_oneLoopF2_integrand one_pos hΛ0) intervalIntegrable_const
          fun Y hY => ?_
        have hM := ladderInnerMass_pos one_pos hΛ0 hY
        rw [div_le_div_iff₀ hM (by positivity)]
        unfold ladderInnerMass
        have h1 : Y ^ 2 ≤ 1 := by nlinarith [hY.1, hY.2]
        have h2 : 0 ≤ 1 - Y := by linarith [hY.2]
        have : Y ^ 2 * (1 - Y) * Λ ^ 2 ≤ 1 * (1 - Y) * Λ ^ 2 := by gcongr
        nlinarith [sq_nonneg Y]
    _ = 1 / Λ ^ 2 := by simp

theorem abs_outerSoftJ_add_le {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    |outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y| ≤ 8 := by
  rw [outerSoftJ_add_eq hlam, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 8)
    (f := softSum lam) fun Y hY => by
      rw [uIoc_of_le zero_le_one] at hY
      rw [Real.norm_eq_abs]
      exact abs_softSum_le (by rw [abs_of_pos hlam]; exact hlam1) hY
  simpa using h

theorem abs_ladderCtBracket_le {Lam Y : ℝ} (hLam : 1 ≤ Lam) (hY : Y ∈ Icc (0 : ℝ) 1) :
    |ladderCtBracket Lam Y| ≤ 2 + log Lam := by
  have hM1 := ladderInnerMass_ge_three_quarters hLam hY
  have hM2 := ladderInnerMass_le_sq hLam hY
  have hM0 : 0 < ladderInnerMass 1 Lam Y := by linarith
  have hp : |Y * (Y ^ 2 + 2 * Y - 2)| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith [hY.1, hY.2]
  have hl : |log (ladderInnerMass 1 Lam Y)| ≤ 1 + 2 * log Lam := by
    have h1 : log (3 / 4 : ℝ) ≤ log (ladderInnerMass 1 Lam Y) := log_le_log (by norm_num) hM1
    have h2 : log (ladderInnerMass 1 Lam Y) ≤ log (Lam ^ 2) := log_le_log hM0 hM2
    rw [log_pow] at h2
    have h34 : -1 ≤ log (3 / 4 : ℝ) := by
      have := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
      norm_num at this ⊢; linarith
    have := log_nonneg hLam
    push_cast at h2
    rw [abs_le]; constructor <;> linarith
  unfold ladderCtBracket
  have t1 : |Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 Lam Y)| ≤ 4 / 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * ladderInnerMass 1 Lam Y),
      div_le_iff₀ (by positivity)]
    linarith
  have t2 : |Y / 2 * log (ladderInnerMass 1 Lam Y)| ≤ 1 / 2 * (1 + 2 * log Lam) := by
    rw [abs_mul, abs_of_nonneg (by linarith [hY.1] : 0 ≤ Y / 2)]
    have := log_nonneg hLam
    have h0 : 0 ≤ |log (ladderInnerMass 1 Lam Y)| := abs_nonneg _
    calc Y / 2 * |log (ladderInnerMass 1 Lam Y)| ≤ 1 / 2 * |log (ladderInnerMass 1 Lam Y)| := by
          gcongr; linarith [hY.2]
      _ ≤ 1 / 2 * (1 + 2 * log Lam) := by gcongr
  calc _ ≤ |Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 Lam Y)| +
        |Y / 2 * log (ladderInnerMass 1 Lam Y)| := abs_sub _ _
    _ ≤ 2 + log Lam := by linarith

theorem abs_integral_ladderCtBracket_le {Lam : ℝ} (hLam : 1 ≤ Lam) :
    |∫ Y in (0 : ℝ)..1, ladderCtBracket Lam Y| ≤ 2 + log Lam := by
  rw [← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 2 + log Lam) (f := ladderCtBracket Lam) fun Y hY => by
      rw [uIoc_of_le zero_le_one] at hY
      rw [Real.norm_eq_abs]
      exact abs_ladderCtBracket_le hLam ⟨hY.1.le, hY.2⟩
  simpa using h

/-! ### The error bound -/

/-- **The error bound**, a function of `Λ` alone. -/
noncomputable def ladderErrBound (Lam : ℝ) : ℝ :=
  (∫ Y in (0 : ℝ)..1, e1Dom Lam Y) +
    2 * (∫ Y in (0 : ℝ)..1, (13 + log Lam + log 2 - log Y - log (1 - Y)) / Lam ^ 2) +
    |ladderS1 Lam| + 8 / Lam ^ 2 + (2 + log Lam) / Lam ^ 2

/-- **The terms other than the representation (3.4) are bounded uniformly in `λ`**:
`|L(λ, Λ) - Rep(λ)| ≤ ladderErrBound Λ` for `0 < λ ≤ 1 ≤ Λ`. -/
theorem abs_ladderTotal_sub_le {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam) :
    |ladderTotal lam Lam - ladderRep lam| ≤ ladderErrBound Lam := by
  have hLam0 : 0 < Lam := by linarith
  rw [ladderTotal_eq hlam hlam1 hLam]
  have b1 := (e1_Y_bound hlam hLam).2
  have b2 := (outer_Y_bound hLam hLam0 le_rfl).2
  have b3 := (outer_Y_bound hLam hlam (by linarith)).2
  obtain ⟨f0, f1⟩ := oneLoopF2_nonneg_le_one hlam
  obtain ⟨g0, -⟩ := oneLoopF2_nonneg_le_one hLam0
  have g1 := oneLoopF2_le_inv_sq hLam
  have hJ := abs_outerSoftJ_add_le hlam hlam1
  have hC := abs_integral_ladderCtBracket_le hLam
  have hl := log_nonneg hLam
  set A := ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x
  set B1 := ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm Lam Lam Y x
  set B2 := ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm Lam lam Y x
  set K := ∫ Y in (0 : ℝ)..1, (13 + log Lam + log 2 - log Y - log (1 - Y)) / Lam ^ 2
  set S := ladderS1 Lam
  set F := oneLoopF2 1 lam
  set FL := oneLoopF2 1 Lam
  set J := outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y
  set C := ∫ Y in (0 : ℝ)..1, ladderCtBracket Lam Y
  have t1 : |F * S| ≤ |S| := by
    rw [abs_mul, abs_of_nonneg f0]
    exact mul_le_of_le_one_left (abs_nonneg _) f1
  have t2 : |FL * J| ≤ 8 / Lam ^ 2 := by
    rw [abs_mul, abs_of_nonneg g0]
    calc FL * |J| ≤ 1 / Lam ^ 2 * 8 := mul_le_mul g1 hJ (abs_nonneg _) (by positivity)
      _ = 8 / Lam ^ 2 := by ring
  have t3 : |FL * C| ≤ (2 + log Lam) / Lam ^ 2 := by
    rw [abs_mul, abs_of_nonneg g0]
    calc FL * |C| ≤ 1 / Lam ^ 2 * (2 + log Lam) :=
          mul_le_mul g1 hC (abs_nonneg _) (by positivity)
      _ = (2 + log Lam) / Lam ^ 2 := by ring
  have e : ladderRep lam - A + (B1 - B2) + F * S + FL * J - FL * C - ladderRep lam =
      -A + B1 - B2 + F * S + FL * J - FL * C := by ring
  rw [e, ladderErrBound]
  have := abs_add_le (-A + B1 - B2 + F * S + FL * J) (-(FL * C))
  have := abs_add_le (-A + B1 - B2 + F * S) (FL * J)
  have := abs_add_le (-A + B1 - B2) (F * S)
  have := abs_sub (-A + B1) B2
  have := abs_add_le (-A) B1
  rw [abs_neg] at *
  have e2 : -A + B1 - B2 + F * S + FL * J - FL * C = -A + B1 - B2 + F * S + FL * J + -(FL * C) := by
    ring
  rw [e2]
  linarith

/-! ### The limit `Λ → ∞` of the error bound -/

theorem tendsto_ladderInnerMass_atTop {Y : ℝ} (hY : Y < 1) :
    Tendsto (fun Lam => ladderInnerMass 1 Lam Y) atTop atTop := by
  unfold ladderInnerMass
  exact tendsto_atTop_add_const_left _ _
    ((tendsto_pow_atTop two_ne_zero).const_mul_atTop (by linarith))

theorem tendsto_log_div_sq : Tendsto (fun Lam : ℝ => log Lam / Lam ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).mul tendsto_inv_atTop_zero
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Lam hLam
  simp only [pow_one, one_mul, add_zero]
  field_simp

theorem tendsto_const_div_sq (c : ℝ) : Tendsto (fun Lam : ℝ => c / Lam ^ 2) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)

theorem ell_nonneg {Y : ℝ} (hY : Y ∈ Ioc (0 : ℝ) 1) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ a - log Y - log (1 - Y) := by
  have h1 := log_nonpos hY.1.le hY.2
  have h2 : log (1 - Y) ≤ 0 := log_nonpos (by linarith [hY.2]) (by linarith [hY.1])
  linarith

theorem tendsto_integral_e1Dom :
    Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, e1Dom Lam Y) atTop (𝓝 0) := by
  suffices key : Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, e1Dom Lam Y) atTop
      (𝓝 (∫ _ in (0 : ℝ)..1, (0 : ℝ))) by simpa using key
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 12 * (2 + log 2 - log Y - log (1 - Y))) ?_ ?_
    ((intervalIntegrable_ellY (2 + log 2)).const_mul 12) ?_
  · refine Eventually.of_forall fun Lam => ?_
    exact (by unfold e1Dom ladderInnerMass; fun_prop :
      Measurable fun Y => e1Dom Lam Y).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with Lam hLam
    refine ae_of_all _ fun Y hY => ?_
    rw [uIoc_of_le zero_le_one] at hY
    have hM := ladderInnerMass_ge_three_quarters hLam ⟨hY.1.le, hY.2⟩
    have hs : 1 / 2 ≤ √(ladderInnerMass 1 Lam Y) := by
      have := Real.sqrt_le_sqrt (show (1 / 4 : ℝ) ≤ ladderInnerMass 1 Lam Y by linarith)
      rwa [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hk := ell_nonneg hY (2 + log 2) (by have := log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith)
    rw [Real.norm_eq_abs, e1Dom, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    nlinarith
  · filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hY' : Y < 1 := lt_of_le_of_ne hY.2 hY1
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_ladderInnerMass_atTop hY'))

theorem ladderS1_eq (Lam : ℝ) :
    ladderS1 Lam = ∫ Y in (0 : ℝ)..1, Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 Lam Y) := by
  refine intervalIntegral.integral_congr fun Y hY => ?_
  simp only [ladderCtBracket]
  ring

theorem tendsto_ladderS1 : Tendsto ladderS1 atTop (𝓝 0) := by
  have hT : Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1,
      Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 Lam Y)) atTop (𝓝 0) := by
    suffices key : Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1,
        Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 Lam Y)) atTop
        (𝓝 (∫ _ in (0 : ℝ)..1, (0 : ℝ))) by simpa using key
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun Lam => ?_
      exact (by unfold ladderInnerMass; fun_prop : Measurable fun Y : ℝ =>
        Y * (Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 Lam Y)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with Lam hLam
      refine ae_of_all _ fun Y hY => ?_
      rw [uIoc_of_le zero_le_one] at hY
      have hM := ladderInnerMass_ge_three_quarters hLam ⟨hY.1.le, hY.2⟩
      have hp : |Y * (Y ^ 2 + 2 * Y - 2)| ≤ 2 := by
        rw [abs_le]; constructor <;> nlinarith [hY.1, hY.2]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 2 * ladderInnerMass 1 Lam Y),
        div_le_iff₀ (by positivity)]
      linarith
    · filter_upwards [ladder_ae_ne_one] with Y hY1 hY
      rw [uIoc_of_le zero_le_one] at hY
      have hY' : Y < 1 := lt_of_le_of_ne hY.2 hY1
      exact tendsto_const_nhds.div_atTop
        ((tendsto_ladderInnerMass_atTop hY').const_mul_atTop two_pos)
  exact hT.congr fun Lam => (ladderS1_eq Lam).symm

theorem integral_outerDom_eq (Lam : ℝ) :
    ∫ Y in (0 : ℝ)..1, (13 + log Lam + log 2 - log Y - log (1 - Y)) / Lam ^ 2 =
      (log Lam + ∫ Y in (0 : ℝ)..1, (13 + log 2 - log Y - log (1 - Y))) / Lam ^ 2 := by
  rw [intervalIntegral.integral_div]
  congr 1
  have e : (fun Y => 13 + log Lam + log 2 - log Y - log (1 - Y)) =
      fun Y => log Lam + (13 + log 2 - log Y - log (1 - Y)) := by funext Y; ring
  rw [e, intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_ellY _),
    intervalIntegral.integral_const]
  simp

/-- **The error bound tends to `0` as `Λ → ∞`.** -/
theorem tendsto_ladderErrBound : Tendsto ladderErrBound atTop (𝓝 0) := by
  set K := ∫ Y in (0 : ℝ)..1, (13 + log 2 - log Y - log (1 - Y))
  have h2 : Tendsto (fun Lam => 2 * (∫ Y in (0 : ℝ)..1,
      (13 + log Lam + log 2 - log Y - log (1 - Y)) / Lam ^ 2)) atTop (𝓝 0) := by
    simp only [integral_outerDom_eq, add_div]
    simpa using (tendsto_log_div_sq.add (tendsto_const_div_sq K)).const_mul 2
  have h3 : Tendsto (fun Lam => |ladderS1 Lam|) atTop (𝓝 0) := by
    simpa using tendsto_ladderS1.abs
  have h5 : Tendsto (fun Lam : ℝ => (2 + log Lam) / Lam ^ 2) atTop (𝓝 0) := by
    simp only [add_div]
    simpa using (tendsto_const_div_sq 2).add tendsto_log_div_sq
  have := (((tendsto_integral_e1Dom.add h2).add h3).add (tendsto_const_div_sq 8)).add h5
  simp only [add_zero] at this
  exact this

/-! ### The joint limit -/

/-- **The L unit tends to `11/48 + π²/18 = 11/48 + ζ(2)/3` as `(λ, Λ) → (0⁺, ∞)` jointly.** -/
theorem tendsto_ladderTotal :
    Tendsto (fun p : ℝ × ℝ => ladderTotal p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (11 / 48 + π ^ 2 / 18)) := by
  have h1 : Tendsto (fun p : ℝ × ℝ => ladderRep p.1) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (11 / 48 + π ^ 2 / 18)) :=
    (tendsto_ladderRep : Tendsto ladderRep _ _).comp tendsto_fst
  have h2 : Tendsto (fun p : ℝ × ℝ => ladderErrBound p.2) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    tendsto_ladderErrBound.comp tendsto_snd
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, p.1 ∈ Ioo (0 : ℝ) 1 ∧ 1 ≤ p.2 :=
    ((show ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 from
      Ioo_mem_nhdsGT (by norm_num)).prod_inl _).and
      ((eventually_ge_atTop (1 : ℝ)).prod_inr _)
  have h3 : Tendsto (fun p : ℝ × ℝ => ladderTotal p.1 p.2 - ladderRep p.1) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [hev] with p hp
    rw [Real.norm_eq_abs]
    exact abs_ladderTotal_sub_le hp.1.1 hp.1.2.le hp.2
  have := h1.add h3
  simp only [add_zero, add_sub_cancel] at this
  exact this

/-! ### The model's L unit -/

/-- **The model's L unit is `L(m_γ, Λ)`**: for `m = 1`, `0 < m_γ < Λ` and `d₁` fixed by the frozen
charge condition at charge `1`, `16π⁴ · unitF2 .L (atUnitCharge P d₁ d₂ d_m d₃) = L(m_γ, Λ)`. -/
theorem sixteen_pi_pow_four_mul_unitF2_L_eq_ladderTotal (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm1 : P.m = 1) (hlt : P.mγ < P.Λ) {d₁ d₂ dm d₃ : ℝ}
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    16 * (π : ℂ) ^ 4 * unitF2 .L (atUnitCharge P d₁ d₂ dm d₃) =
      ((ladderTotal P.mγ P.Λ : ℝ) : ℂ) := by
  rw [sixteen_pi_pow_four_mul_unitF2_L P hm hmγ hΛ hch,
    sixteen_pi_pow_four_mul_graphHalf_eq_gsum (P := atUnitCharge P d₁ d₂ dm d₃) hm1 rfl hmγ hlt,
    hm1, ladderTotal]
  push_cast
  rfl

/-- **The L unit link** (joint regulator limit, as in the frozen headline): for every `η > 0`
there are `δ > 0` and `R` such that for every parameter set with `m = 1`, `0 < m_γ < δ`,
`Λ > R` and every `d₁` satisfying the frozen charge condition (K₀) at charge `1`,
`‖16π⁴ · unitF2 .L (atUnitCharge P d₁ d₂ d_m d₃) - (11/48 + π²/18)‖ < η`. -/
theorem unitF2_L_limit {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.m = 1 → P.mγ < δ → R < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * unitF2 .L (atUnitCharge P d₁ d₂ dm d₃) -
          ((11 / 48 + π ^ 2 / 18 : ℝ) : ℂ)‖ < η := by
  have hT := Metric.tendsto_nhds.mp tendsto_ladderTotal η hη
  obtain ⟨pa, hpa, pb, hpb, hp⟩ := eventually_prod_iff.mp hT
  obtain ⟨ε, hε, hεa⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨a, ha⟩ := eventually_atTop.mp hpb
  refine ⟨min ε 1, lt_min hε one_pos, max a 1, fun P hm hmγ hΛ hm1 hδ hR d₁ d₂ dm d₃ hch => ?_⟩
  have hlt : P.mγ < P.Λ := by
    have := min_le_right ε 1
    have := le_max_right a 1
    linarith
  rw [sixteen_pi_pow_four_mul_unitF2_L_eq_ladderTotal P hm hmγ hΛ hm1 hlt hch,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Real.dist_eq]
  refine hp (hεa ?_ hmγ) (ha _ ((le_max_left a 1).trans hR.le))
  rw [Real.dist_eq, sub_zero, abs_of_pos hmγ]
  exact lt_of_lt_of_le hδ (min_le_left ε 1)

end QED.TwoLoop.UnitLLink

end
