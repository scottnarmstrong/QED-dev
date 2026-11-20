/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXSBd
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Set (c), Stage K, closed forms: the crossed inner integrand by the FTC in the node variable

Helper level (no frozen statement). Step 1 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
sessions 19+, 22+), in the node variable. `formXSw Y y₃ X = S(Y, y₃, s(w_Y(X)))` is `S` at the
threshold of `m = w_Y(X)`; it is jointly measurable (**`measurable_formXSw`**). For
`0 < y₃ < Y < X < 1`:

* **`intervalIntegrable_formXSw`**: `X′ ↦ Q′(X′) S(Y, y₃, s(w_Y(X′)))` is integrable on `[Y, X]`
  (from `formXS_bound`);
* **`formXHin_eq_integral`**: `formXHin Y y₃ X = F(0⁺)/(1 - Y) + ∫_Y^X Q′(X′) formXSw Y y₃ X′ dX′`
  (FTC for `X′ ↦ formXFm(w_Y(X′))` off the single node where `w_Y(X′) = m*`, `F(w_Y(Y)) = F(0⁺)`);
* **`formX_setIntegral_abs_le`**: `∫_Y^X |Q′ S| ≤ C (log(y₃ + w_Y(X)) - log y₃)/(1 - Y)`,
  the bound used for the absolute integrability of the Fubini swap.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **`S` at the node**: `S(Y, y₃, s)` at the threshold `s` of `m = w_Y(X)`. -/
noncomputable def formXSw (Y y3 X : ℝ) : ℝ := formXS Y y3 (formXThr Y y3 (cornInWX Y X))

theorem measurable_formXS : Measurable fun p : ℝ × ℝ × ℝ => formXS p.1 p.2.1 p.2.2 := by
  unfold formXS formXS1 formXS2 formXN1 formXN2 cornInXs
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

theorem measurable_formXThr : Measurable fun p : ℝ × ℝ × ℝ => formXThr p.1 p.2.1 p.2.2 := by
  unfold formXThr cornerG cornInXs
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

theorem measurable_formXSw : Measurable fun p : ℝ × ℝ × ℝ => formXSw p.1 p.2.1 p.2.2 := by
  have hw : Measurable fun p : ℝ × ℝ × ℝ => cornInWX p.1 p.2.2 := by
    unfold cornInWX setCKQ
    fun_prop
  exact measurable_formXS.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_formXThr.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk hw)))))

section

variable {Y y3 X : ℝ}

/-- For fixed `0 < y₃ < Y ≤ X₀ < 1`, `S` at the node is bounded by `C/y₃` beyond `Y`. -/
theorem abs_formXSw_le {C X₀ : ℝ}
    (hC : ∀ Y y3 m, 0 < y3 → y3 < Y → Y ≤ X₀ → 0 < m →
      |formXS Y y3 (formXThr Y y3 m)| ≤ C / (y3 + m))
    (h3 : 0 < y3) (h34 : y3 < Y) (hYX : Y ≤ X₀) {X' : ℝ} (hX' : X' ∈ Ioo Y 1) :
    |formXSw Y y3 X'| ≤ C / (y3 + cornInWX Y X') :=
  hC Y y3 _ h3 h34 hYX (cornInWX_pos ⟨h3.trans h34, hX'.1.trans hX'.2⟩ hX')

/-- The node integrand `Q′ S` is interval integrable on `[Y, X]`. -/
theorem intervalIntegrable_formXSw (h3 : 0 < y3) (h34 : y3 < Y) (hYX : Y < X) (hX : X < 1) :
    IntervalIntegrable (fun X' => setCKdQ X' * formXSw Y y3 X') volume Y X := by
  obtain ⟨C, hC0, hC⟩ := formXS_bound hX
  have hcQ : ContinuousOn setCKdQ (Icc Y X) := fun x hx => by
    have : x < 1 := hx.2.trans_lt hX
    have h1 : (1 - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 this.ne')
    unfold setCKdQ
    exact ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).div
      ((continuousAt_const.sub continuousAt_id).pow 2) h1).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcQ
  have hm : Measurable fun X' => setCKdQ X' * formXSw Y y3 X' := by
    have : Measurable fun X' : ℝ => formXSw Y y3 X' :=
      measurable_formXSw.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    unfold setCKdQ
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hYX.le]
  refine IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable (B * (C / y3))
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_))
  have hx1 : x < 1 := hx.2.trans_lt hX
  have hw := cornInWX_pos ⟨h3.trans h34, hYX.trans hX⟩ ⟨hx.1, hx1⟩
  rw [norm_mul]
  refine mul_le_mul (hB x (Ioc_subset_Icc_self hx)) ?_ (norm_nonneg _)
    ((norm_nonneg _).trans (hB x (Ioc_subset_Icc_self hx)))
  refine (abs_formXSw_le hC h3 h34 hYX.le ⟨hx.1, hx1⟩).trans ?_
  exact div_le_div_of_nonneg_left hC0 h3 (by linarith)

/-- **The FTC in the node variable**: for `0 < y₃ < Y < X < 1`,
`formXHin Y y₃ X = F(0⁺)/(1 - Y) + ∫_Y^X Q′(X′) S(Y, y₃, s(w_Y(X′))) dX′`. -/
theorem formXHin_eq_integral (h3 : 0 < y3) (h34 : y3 < Y) (hYX : Y < X) (hX : X < 1) :
    formXHin Y y3 X = formXF0 Y y3 / (1 - Y) +
      ∫ X' in Y..X, setCKdQ X' * formXSw Y y3 X' := by
  have hY : Y < 1 := hYX.trans hX
  have hY0 : Y ∈ Ioo (0 : ℝ) 1 := ⟨h3.trans h34, hY⟩
  have h1Y : 0 < 1 - Y := by linarith
  set f := fun X' => formXFm Y y3 (cornInWX Y X') with hf
  have hcw : ∀ x, x < 1 → ContinuousAt (cornInWX Y) x := fun x hx =>
    (hasDerivAt_cornInWX hx).continuousAt
  have Hc : ContinuousOn f (Icc Y X) := fun x hx =>
    ((continuous_formXFm h3 h34 hY).continuousAt.comp
      (hcw x (hx.2.trans_lt hX))).continuousWithinAt
  set sE := {x | x ∈ Ioo Y 1 ∧ cornInWX Y x = formXMs Y y3}
  have hsE : sE.Countable := by
    refine Set.Subsingleton.countable fun a ha b hb => ?_
    exact (cornInWX_strictMonoOn hY0).injOn ha.1 hb.1 (ha.2.trans hb.2.symm)
  have Hd : ∀ x ∈ Ioo Y X \ sE, HasDerivAt f ((1 - Y) * (setCKdQ x * formXSw Y y3 x)) x := by
    rintro x ⟨hx, hxs⟩
    have hx1 : x < 1 := hx.2.trans hX
    have hw := cornInWX_pos hY0 ⟨hx.1, hx1⟩
    have hne : cornInWX Y x ≠ formXMs Y y3 := fun h => hxs ⟨⟨hx.1, hx1⟩, h⟩
    refine ((hasDerivAt_formXFm h3 h34 hY hw hne).comp x (hasDerivAt_cornInWX hx1)).congr_deriv ?_
    unfold formXSw
    ring
  have Hi := (intervalIntegrable_formXSw h3 h34 hYX hX).const_mul (1 - Y)
  have hF := integral_eq_of_hasDerivAt_off_countable_of_le f _ hYX.le hsE Hc Hd Hi
  rw [intervalIntegral.integral_const_mul] at hF
  have hfX : f X = formXF Y y3 (cornInWX Y X) (formXThr Y y3 (cornInWX Y X)) :=
    formXFm_eq h3 h34 hY (cornInWX_pos hY0 ⟨hYX, hX⟩)
  have hfY : f Y = formXF0 Y y3 := by
    have hms : 0 < formXMs Y y3 :=
      mul_pos (cornerG_pos hY h3) (cornInXs_mem h3 h34 hY).1
    simp only [hf, formXFm, show cornInWX Y Y = 0 by simp [cornInWX], ite_eq_left hms.le,
      formXF1_zero]
  rw [formXHin_eq_thr h3 h34 hYX hX, ← hfX]
  field_simp
  linarith

/-- **The norm bound of the node integrand**:
`∫_Y^X |Q′ S| ≤ C (log(y₃ + w_Y(X)) - log y₃)/(1 - Y)` for the constant `C` of `formXS_bound`. -/
theorem formX_setIntegral_abs_le {C X₀ : ℝ}
    (hC : ∀ Y y3 m, 0 < y3 → y3 < Y → Y ≤ X₀ → 0 < m →
      |formXS Y y3 (formXThr Y y3 m)| ≤ C / (y3 + m))
    (h3 : 0 < y3) (h34 : y3 < Y) (hYX : Y < X) (hX : X < 1) (hXX : X ≤ X₀) :
    ∫ X' in Ioo Y X, |setCKdQ X' * formXSw Y y3 X'| ≤
      C * ((log (y3 + cornInWX Y X) - log y3) / (1 - Y)) := by
  have hY : Y < 1 := hYX.trans hX
  have hY0 : Y ∈ Ioo (0 : ℝ) 1 := ⟨h3.trans h34, hY⟩
  have h1Y : 0 < 1 - Y := by linarith
  have hwn : ∀ x ∈ Icc Y X, 0 ≤ cornInWX Y x := fun x hx => by
    rcases hx.1.eq_or_lt with h | h
    · simp [← h, cornInWX]
    · exact (cornInWX_pos hY0 ⟨h, hx.2.trans_lt hX⟩).le
  have hD : ∀ x ∈ uIcc Y X, HasDerivAt (fun x => log (y3 + cornInWX Y x) / (1 - Y))
      (setCKdQ x / (y3 + cornInWX Y x)) x := by
    intro x hx
    rw [uIcc_of_le hYX.le] at hx
    have hp : 0 < y3 + cornInWX Y x := by linarith [hwn x hx]
    refine ((((hasDerivAt_cornInWX (hx.2.trans_lt hX)).const_add y3).log hp.ne').div_const
      (1 - Y)).congr_deriv ?_
    field_simp
  have hcont : ContinuousOn (fun x => setCKdQ x / (y3 + cornInWX Y x)) (uIcc Y X) := by
    intro x hx
    rw [uIcc_of_le hYX.le] at hx
    have hx1 : x < 1 := hx.2.trans_lt hX
    have hp : 0 < y3 + cornInWX Y x := by linarith [hwn x hx]
    have h1 : (1 - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hx1.ne')
    have hQ : ContinuousAt setCKdQ x := by
      unfold setCKdQ
      exact (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).div
        ((continuousAt_const.sub continuousAt_id).pow 2) h1
    exact (hQ.div (continuousAt_const.add (hasDerivAt_cornInWX hx1).continuousAt)
      hp.ne').continuousWithinAt
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable
  rw [intervalIntegral.integral_of_le hYX.le, integral_Ioc_eq_integral_Ioo] at hF
  have hI1 : IntegrableOn (fun X' => |setCKdQ X' * formXSw Y y3 X'|) (Ioo Y X) := by
    have := (intervalIntegrable_formXSw h3 h34 hYX hX).norm
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hYX.le] at this
    exact this
  have hI2 : IntegrableOn (fun x => setCKdQ x / (y3 + cornInWX Y x)) (Ioo Y X) := by
    have := hcont.intervalIntegrable (μ := volume)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hYX.le] at this
    exact this
  calc ∫ X' in Ioo Y X, |setCKdQ X' * formXSw Y y3 X'| ≤
        ∫ X' in Ioo Y X, C * (setCKdQ X' / (y3 + cornInWX Y X')) := by
        refine setIntegral_mono_on hI1 (hI2.const_mul C) measurableSet_Ioo fun x hx => ?_
        have hx1 : x < 1 := hx.2.trans hX
        have hQ := setCKdQ_pos ⟨h3.trans (h34.trans hx.1), hx1⟩
        rw [abs_mul, abs_of_pos hQ, mul_div_assoc', mul_comm C, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (abs_formXSw_le hC h3 h34 (hYX.le.trans hXX) ⟨hx.1, hx1⟩) hQ.le
    _ = C * ((log (y3 + cornInWX Y X) - log y3) / (1 - Y)) := by
        rw [integral_const_mul, hF, sub_div]
        simp [cornInWX]

end

end QED.ChainProof.SetCK

end
