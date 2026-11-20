/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXSFtc

/-!
# Set (c), Stage K, closed forms: the crossed `m`-derivative kernel and its integrability

Helper level (no frozen statement). Step 3 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
sessions 19+, 22+), first half. On the square `(Y, y₃) ∈ (0, 1)²` (measure `μ ⊗ μ`,
`μ = volume|(0, 1)`):

* `formXIin Y y₃ X = 1{y₃ < Y < X} S(Y, y₃, s(w_Y(X)))` and
  **`formXI X = ∫∫ formXIin`** — `I(X)` of the plan, in the square form
  `∫∫_{(0,1)²} 1{y₃ < Y < X} f(Y, y₃, s)` of the shared coordinate layer
  (`coord_integral_square`, `coord_integral_thr` with `f = formXS`);
* the three-dimensional kernel `formXJ X ((Y, y₃), X′) = 1{X′ < X} Q′(X′) formXIin Y y₃ X′`,
  whose `X′`-sections are indicators of `(Y, X)` (**`formXJ_eq`**, **`integral_formXJ`**);
* **`integrable_formXJ`**: for `X ∈ (0, 1)` the kernel is integrable on `(μ ⊗ μ) ⊗ μ`, from
  `integrable_prod_iff`, the sections (`intervalIntegrable_formXSw`) and the norm bound
  `formX_setIntegral_abs_le` ≤ `C (log(1 + Q(X)) + |log y₃|)/(1 - X)`, integrable in `y₃`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The integrand of `I(X)`: `S` at the node on the triangle `y₃ < Y < X`. -/
noncomputable def formXIin (Y y3 X : ℝ) : ℝ := if y3 < Y ∧ Y < X then formXSw Y y3 X else 0

/-- **`I(X) = ∫∫_{0 < y₃ < Y < X} S(Y, y₃, s(w_Y(X))) dY dy₃`.** -/
noncomputable def formXI (X : ℝ) : ℝ :=
  ∫ q, formXIin q.1 q.2 X
    ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))

/-- The kernel `1{X′ < X} Q′(X′) 1{y₃ < Y < X′} S(Y, y₃, s(w_Y(X′)))` on `((Y, y₃), X′)`. -/
noncomputable def formXJ (X : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  if p.2 < X then setCKdQ p.2 * formXIin p.1.1 p.1.2 p.2 else 0

theorem measurable_formXJ (X : ℝ) : Measurable (formXJ X) := by
  have hS : Measurable fun p : (ℝ × ℝ) × ℝ => formXSw p.1.1 p.1.2 p.2 :=
    measurable_formXSw.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hI : Measurable fun p : (ℝ × ℝ) × ℝ => formXIin p.1.1 p.1.2 p.2 := by
    unfold formXIin
    have hs : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.2 < p.1.1 ∧ p.1.1 < p.2} :=
      (measurableSet_lt measurable_fst.snd measurable_fst.fst).inter
        (measurableSet_lt measurable_fst.fst measurable_snd)
    exact Measurable.ite hs hS measurable_const
  unfold formXJ setCKdQ
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
    measurable_const

/-- The `X′`-section of the kernel is an indicator of `(Y, X)`. -/
theorem formXJ_eq (X : ℝ) (q : ℝ × ℝ) (X' : ℝ) :
    formXJ X (q, X') = if q.2 < q.1 then
      (Ioo q.1 X).indicator (fun X' => setCKdQ X' * formXSw q.1 q.2 X') X' else 0 := by
  unfold formXJ formXIin
  by_cases h1 : q.2 < q.1 <;> by_cases h2 : X' < X <;> by_cases h3 : q.1 < X' <;>
    simp [h1, h2, h3, indicator, mem_Ioo]

/-- Integrals of indicators of subintervals of `(0, 1)`. -/
theorem formX_integral_indicator_Ioo {h : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∫ x, (Ioo a b).indicator h x ∂(volume.restrict (Ioo (0 : ℝ) 1)) = ∫ x in Ioo a b, h x := by
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Ioo_inter_Ioo, max_eq_left ha, min_eq_left hb]

theorem formX_integrable_indicator_Ioo_iff {h : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Integrable ((Ioo a b).indicator h) (volume.restrict (Ioo (0 : ℝ) 1)) ↔
      IntegrableOn h (Ioo a b) := by
  rw [integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Ioo, max_eq_left ha, min_eq_left hb]
  rfl

/-- The `X′`-integral of the kernel. -/
theorem integral_formXJ {X : ℝ} (hX : X ≤ 1) {q : ℝ × ℝ} (hq : 0 ≤ q.1) :
    ∫ X', formXJ X (q, X') ∂(volume.restrict (Ioo (0 : ℝ) 1)) = if q.2 < q.1 then
      ∫ X' in Ioo q.1 X, setCKdQ X' * formXSw q.1 q.2 X' else 0 := by
  simp only [formXJ_eq]
  split_ifs
  · exact formX_integral_indicator_Ioo hq hX
  · exact integral_zero _ _

/-- The `X′`-integral of the norm of the kernel. -/
theorem integral_norm_formXJ {X : ℝ} (hX : X ≤ 1) {q : ℝ × ℝ} (hq : 0 ≤ q.1) :
    ∫ X', ‖formXJ X (q, X')‖ ∂(volume.restrict (Ioo (0 : ℝ) 1)) = if q.2 < q.1 then
      ∫ X' in Ioo q.1 X, |setCKdQ X' * formXSw q.1 q.2 X'| else 0 := by
  simp only [formXJ_eq]
  split_ifs
  · simp only [norm_indicator_eq_indicator_norm, Real.norm_eq_abs]
    exact formX_integral_indicator_Ioo hq hX
  · simp

/-- Almost every point of the square has coordinates in `(0, 1)`. -/
theorem formX_ae_square :
    ∀ᵐ q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))),
      q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

/-- **Absolute integrability of the kernel** (the input of the Fubini swap). -/
theorem integrable_formXJ {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formXJ X) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  obtain ⟨C, hC0, hC⟩ := formXS_bound hX.2
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hQX : 0 ≤ setCKQ X := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
  rw [integrable_prod_iff (measurable_formXJ X).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [formX_ae_square] with q hq
    have hfun : (fun X' => formXJ X (q, X')) = if q.2 < q.1 ∧ q.1 < X then
        (Ioo q.1 X).indicator (fun X' => setCKdQ X' * formXSw q.1 q.2 X') else 0 := by
      funext X'
      rw [formXJ_eq]
      by_cases h1 : q.2 < q.1 <;> by_cases h2 : q.1 < X
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1]
      · simp [h1]
    rw [hfun]
    split_ifs with h
    · rw [formX_integrable_indicator_Ioo_iff hq.1.1.le hX.2.le]
      have := intervalIntegrable_formXSw hq.2.1 h.1 h.2 hX.2
      rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le (h.2.le)] at this
    · exact integrable_zero _ _ _
  · have hlog : Integrable (fun y : ℝ => |log y|) μ := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).norm
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at this
      exact this
    have hg : Integrable (fun q : ℝ × ℝ => C / (1 - X) * (log (1 + setCKQ X) + |log q.2|))
        (μ.prod μ) :=
      ((integrable_const _).add (hlog.comp_snd μ)).const_mul _
    refine hg.mono' ((measurable_formXJ X).norm.stronglyMeasurable.integral_prod_right'
      ).aestronglyMeasurable ?_
    filter_upwards [formX_ae_square] with q hq
    obtain ⟨⟨hY0, hY1⟩, ⟨h30, h31⟩⟩ := hq
    have hL0 : 0 ≤ log (1 + setCKQ X) := Real.log_nonneg (by linarith)
    have hgq : 0 ≤ C / (1 - X) * (log (1 + setCKQ X) + |log q.2|) := by positivity
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      integral_norm_formXJ hX.2.le hY0.le]
    split_ifs with h
    · by_cases h2 : q.1 < X
      · refine (formX_setIntegral_abs_le hC h30 h h2 hX.2 le_rfl).trans ?_
        have hw := cornInWX_pos ⟨hY0, hY1⟩ ⟨h2, hX.2⟩
        have hwle : cornInWX q.1 X ≤ setCKQ X := by
          have hQY := setCKQ_nonneg ⟨hY0.le, hY1.le⟩
          have hQ := setCKQ_lt hY0.le h2 hX.2
          unfold cornInWX
          nlinarith
        have hLL : log (q.2 + cornInWX q.1 X) - log q.2 ≤ log (1 + setCKQ X) + |log q.2| := by
          have := Real.log_le_log (by linarith) (show q.2 + cornInWX q.1 X ≤ 1 + setCKQ X by
            linarith)
          linarith [neg_le_abs (log q.2)]
        have hL : 0 ≤ log (q.2 + cornInWX q.1 X) - log q.2 :=
          sub_nonneg.2 (Real.log_le_log h30 (by linarith))
        have : (log (q.2 + cornInWX q.1 X) - log q.2) / (1 - q.1) ≤
            (log (1 + setCKQ X) + |log q.2|) / (1 - X) :=
          div_le_div₀ (by positivity) hLL h1X (by linarith)
        calc C * ((log (q.2 + cornInWX q.1 X) - log q.2) / (1 - q.1)) ≤
              C * ((log (1 + setCKQ X) + |log q.2|) / (1 - X)) :=
            mul_le_mul_of_nonneg_left this hC0
          _ = _ := by ring
      · rw [Ioo_eq_empty (not_lt.mpr (le_of_not_gt h2)), Measure.restrict_empty,
          integral_zero_measure]
        exact hgq
    · exact hgq

end QED.ChainProof.SetCK

end
