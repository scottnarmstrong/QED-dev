/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXJ

/-!
# Set (c), Stage K, closed forms: the crossed weight reduced to the integral `I(X)`

Helper level (no frozen statement). Steps 1–3 of route D for `ρ_X` (scratch
`stageK/STATUS.md`, sessions 19+, 22+). With `μ = volume|(0, 1)`, for almost every `X ∈ (0, 1)`
the `(Y, y₃)`-integrand of `H_X` splits by the FTC in the node variable
(**`formXHin_ae_eq`**: `formXHin = formXG0 + ∫ formXJ(·, X′) dX′`); the `F(0⁺)` part integrates
to `∫₀^X e₁M(Y)/(1 - Y) dY` (**`integral_formXG0`**, from `integral_formXF0`) and Fubini on the
integrable kernel `formXJ` swaps the rest into `∫₀^X Q′(X′) I(X′) dX′`. Hence

**`crossTH_ae_eq_formXI`**: for almost every `X ∈ (0, 1)`, `Q′ I` is integrable on `(0, X)` and
`H_X(X) = ∫₀^X (e₁M(X′)/(1 - X′) + Q′(X′) I(X′)) dX′`,

so the target `crossTH = setCKRhoH rhoCrossX` a.e. reduces to the identity
`ρ_X(X) Q(X) = e₁M(X)/(1 - X) + Q′(X) I(X)` for a.e. `X` (steps 4–5). Also
**`ae_integrable_formXIin`**: the integrand of `I(X)` is integrable on the square for a.e. `X`
(the hypothesis of `coord_integral_square`/`coord_integral_thr`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The `F(0⁺)` part `1{y₃ < Y < X} F(0⁺)/(1 - Y)` of `formXHin`. -/
noncomputable def formXG0 (X : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.2 < q.1 ∧ q.1 < X then formXF0 q.1 q.2 / (1 - q.1) else 0

section

variable {X : ℝ}

/-- **The inner integrand split by the FTC** on the square. -/
theorem formXHin_ae_eq (hX : X ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))),
      formXHin q.1 q.2 X =
        formXG0 X q + ∫ X', formXJ X (q, X') ∂(volume.restrict (Ioo (0 : ℝ) 1)) := by
  filter_upwards [formX_ae_square] with q hq
  rw [integral_formXJ hX.2.le hq.1.1.le]
  unfold formXG0
  by_cases h : q.2 < q.1 ∧ q.1 < X
  · rw [formXHin_eq_integral hq.2.1 h.1 h.2 hX.2, ite_eq_left h, ite_eq_left h.1,
      intervalIntegral.integral_of_le h.2.le, integral_Ioc_eq_integral_Ioo]
  · have h0 : formXHin q.1 q.2 X = 0 := by unfold formXHin; exact ite_eq_right h
    rw [h0, ite_eq_right h]
    split_ifs with h1
    · rw [Ioo_eq_empty fun h2 => h ⟨h1, h2⟩, Measure.restrict_empty, integral_zero_measure]
      simp
    · simp

theorem integrable_formXG0 (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formXG0 X)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => formXF0 p.1 p.2 / (1 - p.1))
      (Icc 0 X ×ˢ Icc 0 1) := by
    unfold formXF0
    refine ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_)
      (by fun_prop) fun p hp => ?_
    · have : p.1 < 1 := hp.1.2.trans_lt hX.2
      have : -1 + p.1 ≠ 0 := by linarith
      positivity
    · have : p.1 < 1 := hp.1.2.trans_lt hX.2
      linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (0, 0) ⟨⟨le_rfl, hX.1.le⟩, ⟨le_rfl, zero_le_one⟩⟩)
  have hm : Measurable (formXG0 X) := by
    unfold formXG0 formXF0
    exact Measurable.ite ((measurableSet_lt measurable_snd measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)) (by fun_prop) measurable_const
  refine Integrable.of_bound hm.aestronglyMeasurable B ?_
  filter_upwards [formX_ae_square] with q hq
  unfold formXG0
  split_ifs with h
  · exact hB q ⟨⟨hq.1.1.le, h.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  · simpa using hB0

/-- **`∫∫ 1{y₃ < Y < X} F(0⁺)/(1 - Y) = ∫₀^X e₁M(Y)/(1 - Y) dY`.** -/
theorem integral_formXG0 (hX : X ∈ Ioo (0 : ℝ) 1) :
    ∫ q, formXG0 X q
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ Y in Ioo 0 X, formXe1M Y / (1 - Y) := by
  rw [integral_prod _ (integrable_formXG0 hX)]
  have hin : ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ y3, formXG0 X (Y, y3) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
        (Ioo 0 X).indicator (fun Y => formXe1M Y / (1 - Y)) Y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
    by_cases hYX : Y < X
    · rw [indicator_of_mem (show Y ∈ Ioo 0 X from ⟨hY.1, hYX⟩)]
      have he : ∀ᵐ y3 ∂(volume.restrict (Ioo (0 : ℝ) 1)), formXG0 X (Y, y3) =
          (Ioo 0 Y).indicator (fun y3 => formXF0 Y y3 / (1 - Y)) y3 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y3 hy3
        unfold formXG0
        by_cases h : y3 < Y
        · rw [ite_eq_left ⟨h, hYX⟩, indicator_of_mem (show y3 ∈ Ioo 0 Y from ⟨hy3.1, h⟩)]
        · rw [ite_eq_right fun h' => h h'.1, indicator_of_notMem fun h' => h h'.2]
      rw [integral_congr_ae he, formX_integral_indicator_Ioo le_rfl hY.2.le,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hY.1.le,
        intervalIntegral.integral_div, integral_formXF0 hY.2.ne]
    · rw [indicator_of_notMem fun h => hYX h.2]
      unfold formXG0
      simp [hYX]
  rw [integral_congr_ae hin, formX_integral_indicator_Ioo le_rfl hX.2.le]

/-- The `(Y, y₃)`-integral of the kernel: `1{X′ < X} Q′(X′) I(X′)`. -/
theorem integral_formXJ_q (X' : ℝ) :
    ∫ q, formXJ X (q, X')
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      if X' < X then setCKdQ X' * formXI X' else 0 := by
  unfold formXJ formXI
  split_ifs
  · exact integral_const_mul (setCKdQ X') fun q : ℝ × ℝ => formXIin q.1 q.2 X'
  · exact integral_zero _ _

/-- **Steps 1–3 of route D at a node**: given `H_X(X) = ∫∫ formXHin`, `Q′ I` is integrable on
`(0, X)` and `H_X(X) = ∫₀^X (e₁M(X′)/(1 - X′) + Q′(X′) I(X′)) dX′`. -/
theorem crossTH_eq_integral_formXI (hX : X ∈ Ioo (0 : ℝ) 1)
    (hH : crossTH X = ∫ q, formXHin q.1 q.2 X
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    IntegrableOn (fun X' => setCKdQ X' * formXI X') (Ioo 0 X) ∧
      crossTH X = ∫ X' in (0 : ℝ)..X, (formXe1M X' / (1 - X') + setCKdQ X' * formXI X') := by
  have hJ := integrable_formXJ hX
  have hfib : ∀ᵐ X' ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ q, formXJ X (q, X')
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      (Ioo 0 X).indicator (fun X' => setCKdQ X' * formXI X') X' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with X' hX'
    rw [integral_formXJ_q]
    by_cases h : X' < X
    · rw [ite_eq_left h, indicator_of_mem (show X' ∈ Ioo 0 X from ⟨hX'.1, h⟩)]
    · rw [ite_eq_right h, indicator_of_notMem fun h' => h h'.2]
  have hint : IntegrableOn (fun X' => setCKdQ X' * formXI X') (Ioo 0 X) := by
    rw [← formX_integrable_indicator_Ioo_iff le_rfl hX.2.le]
    exact hJ.integral_prod_right.congr hfib
  refine ⟨hint, ?_⟩
  have hE : IntegrableOn (fun Y => formXe1M Y / (1 - Y)) (Ioo 0 X) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
    unfold formXe1M
    refine ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop) fun Y hY => ?_)
      (by fun_prop) fun Y hY => ?_
    · have : Y < 1 := hY.2.trans_lt hX.2
      have : Y - 1 ≠ 0 := by linarith
      positivity
    · have : Y < 1 := hY.2.trans_lt hX.2
      linarith
  rw [hH, integral_congr_ae (formXHin_ae_eq hX),
    integral_add (integrable_formXG0 hX) hJ.integral_prod_left, integral_formXG0 hX,
    integral_integral_swap (f := fun q X' => formXJ X (q, X')) hJ, integral_congr_ae hfib,
    formX_integral_indicator_Ioo le_rfl hX.2.le, ← integral_add hE hint,
    intervalIntegral.integral_of_le hX.1.le, integral_Ioc_eq_integral_Ioo]

end

/-- **Route D, steps 1–3**: for almost every `X ∈ (0, 1)`,
`H_X(X) = ∫₀^X (e₁M(X′)/(1 - X′) + Q′(X′) I(X′)) dX′`, with `Q′ I` integrable on `(0, X)`. -/
theorem crossTH_ae_eq_formXI :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun X' => setCKdQ X' * formXI X') (Ioo 0 X) ∧
        crossTH X = ∫ X' in (0 : ℝ)..X, (formXe1M X' / (1 - X') + setCKdQ X' * formXI X') := by
  filter_upwards [crossTH_ae_eq, ae_restrict_mem measurableSet_Ioo] with X hI hX
  exact crossTH_eq_integral_formXI hX hI.2

/-- **The integrand of `I(X)` is integrable on the square for almost every `X`.** -/
theorem ae_integrable_formXIin :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun q : ℝ × ℝ => formXIin q.1 q.2 X)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hXn : ∀ n : ℕ, (1 - 1 / ((n : ℝ) + 2)) ∈ Ioo (0 : ℝ) 1 := fun n => by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    refine ⟨?_, by have := one_div_pos.2 h2; linarith⟩
    rw [sub_pos, div_lt_one h2]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h := ae_all_iff.2 fun n => (integrable_formXJ (hXn n)).prod_left_ae
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with X' hn hX'
  obtain ⟨n, hn'⟩ := exists_nat_gt (1 / (1 - X'))
  have h1 : 0 < 1 - X' := by linarith [hX'.2]
  have hlt : X' < 1 - 1 / ((n : ℝ) + 2) := by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : 1 / ((n : ℝ) + 2) < 1 - X' := by
      rw [div_lt_iff₀ h2]
      rw [div_lt_iff₀ h1] at hn'
      nlinarith
    linarith
  have hQ := setCKdQ_pos hX'
  refine (integrable_const_mul_iff (isUnit_iff_ne_zero.2 hQ.ne') _).1 ((hn n).congr ?_)
  exact Eventually.of_forall fun q => by simp only [formXJ, ite_eq_left hlt]

end QED.ChainProof.SetCK

end
