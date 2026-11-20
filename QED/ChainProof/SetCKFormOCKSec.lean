/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCKDom
public import QED.ChainProof.SetCKFormOCYInt

/-!
# Set (c), Stage K, closed forms: the `K`-part of the outer-massive corner at the node

Helper level (no frozen statement). Step 2 of the `ρ_oC` route (Stage K notes, Session 29+):
the part `K(v) = ∫₀^v k` of the outer-massive corner weight, at `v = Q(X) - Q(x)`, is moved to
the node variable `X'` by the substitution `v' = Q(X') - Q(x)`. For `0 < x < X < 1` and `k`
integrable on `(0, Q(X) - Q(x)]` (**`formOC_k_section`**):

`∫₀¹ 1{x < X' < X} Q'(X') k(Q(X') - Q(x)) dX' = ∫₀^{Q(X) - Q(x)} k`,

with integrability; and if `k/(Q(x) + 1 + v)` is integrable on `(0, ∞)`
(**`formOC_k_Ioc`**), `k` is integrable on `(0, Q(X) - Q(x)]` with
`∫₀^{Q(X) - Q(x)} |k| ≤ (Q(X) + 1) ∫₀^∞ |k|/(Q(x) + 1 + v)`.

**`formOCkY`** is `k` of the corner at `y₃ = a Y`, and **`measurable_formOCkY`** its joint
measurability.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **`k` of the outer-massive corner at `y₃ = a Y`.** -/
noncomputable def formOCkY (Y a x v : ℝ) : ℝ :=
  scOutCk (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y)) (cornerC2 x (a * Y) (Y - a * Y))
    (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y)) (scOutRho x)
    (scOutCs Y (a * Y) x) v

theorem measurable_formOCkY :
    Measurable fun r : ℝ × ℝ × ℝ × ℝ => formOCkY r.1 r.2.1 r.2.2.1 r.2.2.2 := by
  unfold formOCkY scOutCk scOutCs betaG cornerC0 cornerC1 cornerC2 cornerC3
    QED.TwoLoop.UnitSCReduce.cornerP2 cornerG cornerR scOutCm scOutRho setCKQ
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
    (by fun_prop)

section

variable {X x : ℝ}

theorem formOC_scOutVX_lt_iff (hX : X < 1) (hx : 0 ≤ x) (hxX : x ≤ X) {X' : ℝ}
    (hX' : X' ∈ Ioo x 1) : scOutVX x X' < scOutVX x X ↔ X' < X := by
  unfold scOutVX
  rw [sub_lt_sub_iff_right]
  constructor
  · intro h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | h''
    · exact lt_asymm h (setCKQ_lt (hx.trans hxX) h'' hX'.2)
    · rw [h''] at h
      exact lt_irrefl _ h
  · intro h
    exact setCKQ_lt (hx.trans hX'.1.le) h hX

/-- **The node substitution for the `K`-part.** -/
theorem formOC_k_section (hX : X < 1) (hx : x ∈ Ioo (0 : ℝ) X) {k : ℝ → ℝ}
    (hk : IntegrableOn k (Ioc 0 (scOutVX x X))) :
    IntegrableOn (fun X' => if x < X' ∧ X' < X then setCKdQ X' * k (scOutVX x X') else 0)
        (Ioo 0 1) ∧
      ∫ X' in Ioo (0 : ℝ) 1, (if x < X' ∧ X' < X then setCKdQ X' * k (scOutVX x X') else 0) =
        ∫ v in Ioc 0 (scOutVX x X), k v := by
  have hx1 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hX⟩
  set V := scOutVX x X with hV
  set g : ℝ → ℝ := (Iio V).indicator k with hg
  have hgi : IntegrableOn g (Ioi 0) := by
    refine (integrable_indicator_iff measurableSet_Iio).2 ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
    exact hk.mono_set Ioo_subset_Ioc_self
  have hgv : ∫ v in Ioi 0, g v = ∫ v in Ioc 0 V, k v := by
    rw [hg, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, integral_Ioc_eq_integral_Ioo]
  obtain ⟨hiff, hval⟩ := scOut_cv hx1 g
  have he : EqOn (fun X' => if x < X' ∧ X' < X then setCKdQ X' * k (scOutVX x X') else 0)
      ((Ioo x 1).indicator fun X' => setCKdQ X' * g (scOutVX x X')) (Ioo 0 1) := by
    intro X' hX'
    by_cases h : x < X'
    · have hm : X' ∈ Ioo x 1 := ⟨h, hX'.2⟩
      rw [indicator_of_mem hm]
      by_cases h2 : X' < X
      · have : scOutVX x X' ∈ Iio V := (formOC_scOutVX_lt_iff hX hx.1.le hx.2.le hm).2 h2
        simp only [h, h2, and_self, ↓reduceIte, hg, indicator_of_mem this]
      · have : scOutVX x X' ∉ Iio V := fun h3 =>
          h2 ((formOC_scOutVX_lt_iff hX hx.1.le hx.2.le hm).1 h3)
        simp only [h, h2, and_false, ↓reduceIte, hg, indicator_of_notMem this, mul_zero]
    · rw [indicator_of_notMem fun hm => h hm.1]
      simp only [h, false_and, ↓reduceIte]
  have hsub : Ioo (0 : ℝ) 1 ∩ Ioo x 1 = Ioo x 1 :=
    inter_eq_right.2 (Ioo_subset_Ioo_left hx1.1.le)
  refine ⟨?_, ?_⟩
  · refine IntegrableOn.congr_fun ?_ he.symm measurableSet_Ioo
    exact ((hiff.1 hgi).integrable_indicator measurableSet_Ioo).integrableOn
  · rw [setIntegral_congr_fun measurableSet_Ioo he, setIntegral_indicator measurableSet_Ioo, hsub,
      ← hval, hgv]

/-- `k` is integrable on `(0, Q(X) - Q(x)]` with an explicit `L¹` bound. -/
theorem formOC_k_Ioc (hX : X < 1) (hx : x ∈ Ioo (0 : ℝ) X) {k : ℝ → ℝ} (hkm : Measurable k)
    (hk : IntegrableOn (fun v => k v / (setCKQ x + 1 + v)) (Ioi 0)) :
    IntegrableOn k (Ioc 0 (scOutVX x X)) ∧
      ∫ v in Ioc 0 (scOutVX x X), |k v| ≤
        (setCKQ X + 1) * ∫ v in Ioi 0, |k v / (setCKQ x + 1 + v)| := by
  have hQ0 : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, (hx.2.trans hX).le⟩
  have hb : ∀ v ∈ Ioc 0 (scOutVX x X), |k v| ≤ (setCKQ X + 1) * |k v / (setCKQ x + 1 + v)| := by
    intro v hv
    have hu : 0 < setCKQ x + 1 + v := by linarith [hv.1]
    have hle : setCKQ x + 1 + v ≤ setCKQ X + 1 := by
      have := hv.2
      unfold scOutVX at this
      linarith
    rw [abs_div, abs_of_pos hu, mul_div_assoc']
    rw [le_div_iff₀ hu]
    nlinarith [abs_nonneg (k v)]
  have hI : IntegrableOn (fun v => (setCKQ X + 1) * |k v / (setCKQ x + 1 + v)|)
      (Ioc 0 (scOutVX x X)) :=
    ((hk.mono_set Ioc_subset_Ioi_self).abs).const_mul _
  have hki : IntegrableOn k (Ioc 0 (scOutVX x X)) := by
    refine Integrable.mono' hI hkm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs]
    exact hb v hv
  refine ⟨hki, ?_⟩
  calc ∫ v in Ioc 0 (scOutVX x X), |k v|
      ≤ ∫ v in Ioc 0 (scOutVX x X), (setCKQ X + 1) * |k v / (setCKQ x + 1 + v)| :=
        setIntegral_mono_on hki.abs hI measurableSet_Ioc hb
    _ = (setCKQ X + 1) * ∫ v in Ioc 0 (scOutVX x X), |k v / (setCKQ x + 1 + v)| :=
        integral_const_mul _ _
    _ ≤ (setCKQ X + 1) * ∫ v in Ioi 0, |k v / (setCKQ x + 1 + v)| := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hk.abs
          (Eventually.of_forall fun _ => abs_nonneg _) Ioc_subset_Ioi_self.eventuallyLE) ?_
        have := setCKQ_nonneg ⟨(hx.1.trans hx.2).le, hX.le⟩
        linarith

end

end QED.ChainProof.SetCK

end
