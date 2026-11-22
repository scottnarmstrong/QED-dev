/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDYA

/-!
# Set (a), stage D: the sheared coordinates `(w, v)` on the simplex `Δ₂`

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). The outer `VB` denominator is affine in the photon-line parameter
`v = y₂` at fixed `w = y₁ + βy₂` (the outer momentum fraction). This file changes variables
`(y₀, y₁) = (1 - w - (1 - β)v, w - βv)` (Jacobian `1`) on `Δ₂`, for `0 < β < 1`:

* **`ksD_integral_simplexTwo_shear`**: for `g` continuous on `Δ₂`,
  `∫_{Δ₂} g = ∫₀¹ ∫₀^{Ymax(w)} g(1 - w - (1-β)v, w - βv) dv dw`,
  `Ymax(w) = min(w/β, (1-w)/(1-β))`.

The proof writes both sides as integrals over `ℝ × ℝ` of indicators of compact triangles and
uses Fubini twice with the translation invariance of the Lebesgue measure in between.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint isCompact_simplexSet
  measurableSet_simplexSet)

/-- The upper end of the photon-line parameter at fixed `w`. -/
noncomputable def ksDYmax (β w : ℝ) : ℝ := min (w / β) ((1 - w) / (1 - β))

/-- The triangle `{t, v ≥ 0, t + v ≤ 1}` in the coordinates `(t, v) = (y₁, y₂)`. -/
def ksDTri : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

/-- The point of `Δ₂` at `(t, v) = (y₁, y₂)`. -/
def ksDPt (t v : ℝ) : Fin 2 → ℝ := ![1 - t - v, t]

theorem ksD_isCompact_tri : IsCompact ksDTri := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  · refine (Metric.isBounded_Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ))).subset ?_
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    exact ⟨⟨h1, h2⟩, ⟨by linarith, by linarith⟩⟩

theorem ksD_pt_mem {t v : ℝ} (h : (t, v) ∈ ksDTri) : ksDPt t v ∈ simplexSet 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [QED.Integration.SimplexMerge.mem_simplexSet_iff_le (by norm_num)]
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [ksDPt] <;> linarith
  · simp [ksDPt, Fin.sum_univ_two]
    linarith

theorem ksD_continuous_pt : Continuous fun p : ℝ × ℝ => ksDPt p.1 p.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [ksDPt] <;> fun_prop

/-- The integrand on `ℝ × ℝ`: `g` at the point `(t, v)`, cut off outside the triangle. -/
noncomputable def ksDH (g : (Fin 2 → ℝ) → ℝ) (t v : ℝ) : ℝ :=
  ksDTri.indicator (fun p => g (ksDPt p.1 p.2)) (t, v)

theorem ksD_integrable_H {g : (Fin 2 → ℝ) → ℝ} (hg : ContinuousOn g (simplexSet 2)) :
    Integrable (Function.uncurry (ksDH g)) (volume.prod volume) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => g (ksDPt p.1 p.2)) ksDTri :=
    hg.comp ksD_continuous_pt.continuousOn fun p hp => ksD_pt_mem hp
  have hi := (hc.integrableOn_compact (μ := (volume : Measure (ℝ × ℝ)))
    ksD_isCompact_tri).integrable_indicator
    ksD_isCompact_tri.isClosed.measurableSet
  rw [Measure.volume_eq_prod] at hi
  exact hi

/-- The sheared triangle `{(w, v) : (w - βv, v) ∈ ksDTri}`. -/
def ksDTriS (β : ℝ) : Set (ℝ × ℝ) := (fun p : ℝ × ℝ => (p.1 - β * p.2, p.2)) ⁻¹' ksDTri

theorem ksD_isCompact_triS {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) : IsCompact (ksDTriS β) := by
  have hcont : Continuous fun p : ℝ × ℝ => (p.1 - β * p.2, p.2) := by fun_prop
  refine Metric.isCompact_of_isClosed_isBounded
    (ksD_isCompact_tri.isClosed.preimage hcont) ?_
  refine (Metric.isBounded_Icc ((0 : ℝ), (0 : ℝ)) ((2 : ℝ), (1 : ℝ))).subset ?_
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only at h1 h2 h3
  have : β * p.2 ≤ p.2 := by nlinarith [hβ.2]
  have : 0 ≤ β * p.2 := mul_nonneg hβ.1 h2
  exact ⟨⟨by linarith, h2⟩, ⟨by linarith, by linarith⟩⟩

/-- The sheared integrand `ksDH g (w - βv) v` is integrable on `ℝ × ℝ`. -/
theorem ksD_integrable_H_shear {g : (Fin 2 → ℝ) → ℝ} (hg : ContinuousOn g (simplexSet 2))
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    Integrable (Function.uncurry fun w v => ksDH g (w - β * v) v) (volume.prod volume) := by
  have hφ : Continuous fun p : ℝ × ℝ => (p.1 - β * p.2, p.2) := by fun_prop
  have hc : ContinuousOn (fun p : ℝ × ℝ => g (ksDPt (p.1 - β * p.2) p.2)) (ksDTriS β) :=
    hg.comp (ksD_continuous_pt.comp hφ).continuousOn fun p hp => ksD_pt_mem hp
  have hi := (hc.integrableOn_compact (μ := (volume : Measure (ℝ × ℝ)))
    (ksD_isCompact_triS hβ)).integrable_indicator
    (ksD_isCompact_triS hβ).isClosed.measurableSet
  rw [Measure.volume_eq_prod] at hi
  convert hi using 1
  funext p
  simp only [Function.uncurry, ksDH, ksDTriS, indicator, mem_preimage]
  rfl

theorem ksD_H_eq_zero_of_not_mem {g : (Fin 2 → ℝ) → ℝ} {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1)
    (v : ℝ) : ksDH g t v = 0 := by
  refine indicator_of_notMem ?_ _
  rintro ⟨h1, h2, h3⟩
  exact ht ⟨h1, by simp only at h3 h2; linarith⟩

theorem ksD_H_section {g : (Fin 2 → ℝ) → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    (fun v => ksDH g t v) = (Icc 0 (1 - t)).indicator fun v => g (ksDPt t v) := by
  funext v
  simp only [ksDH, indicator, ksDTri, mem_ofPred_eq, mem_Icc]
  congr 1
  apply propext
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h2, h3⟩; exact ⟨ht, h2, by linarith⟩

theorem ksD_H_shear_section {g : (Fin 2 → ℝ) → ℝ} {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    (fun v => ksDH g (w - β * v) v) =
      (Icc 0 (ksDYmax β w)).indicator fun v => g (ksDPt (w - β * v) v) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  have h1β : 0 < 1 - β := by linarith
  funext v
  simp only [ksDH, indicator, ksDTri, mem_ofPred_eq, mem_Icc, ksDYmax, le_min_iff,
    le_div_iff₀ hβ0, le_div_iff₀ h1β]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by linarith, by linarith⟩
  · rintro ⟨h2, h3, h4⟩; exact ⟨by linarith, h2, by linarith⟩

theorem ksD_ksDYmax_nonneg {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    0 ≤ ksDYmax β w :=
  le_min (div_nonneg hw.1 hβ.1.le) (div_nonneg (by linarith [hw.2]) (by linarith [hβ.2]))

theorem ksD_H_shear_eq_zero {g : (Fin 2 → ℝ) → ℝ} {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∉ Icc (0 : ℝ) 1) (v : ℝ) : ksDH g (w - β * v) v = 0 := by
  refine indicator_of_notMem ?_ _
  rintro ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  have : 0 ≤ β * v := mul_nonneg hβ.1.le h2
  have : β * v ≤ v := by nlinarith [hβ.2]
  exact hw ⟨by linarith, by linarith⟩

/-- **The sheared coordinates on `Δ₂`**: for `0 < β < 1` and `g` continuous on `Δ₂`,
`∫_{Δ₂} g = ∫₀¹ ∫₀^{Ymax(w)} g(y₀, y₁) dv dw` at `(y₀, y₁) = (1 - (w - βv) - v, w - βv)`. -/
theorem ksD_integral_simplexTwo_shear {g : (Fin 2 → ℝ) → ℝ} (hg : ContinuousOn g (simplexSet 2))
    {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∫ y in simplexSet 2, g y =
      ∫ w in (0 : ℝ)..1, ∫ v in (0 : ℝ)..ksDYmax β w, g (ksDPt (w - β * v) v) := by
  have hgi : IntegrableOn g (simplexSet 2) := hg.integrableOn_compact (isCompact_simplexSet 2)
  -- the left side as an integral over `ℝ × ℝ`
  have hL : ∫ y in simplexSet 2, g y = ∫ t, ∫ v, ksDH g t v := by
    rw [ksD_integral_simplexTwo hgi]
    have hin : ∀ t ∈ uIcc (0 : ℝ) 1, ∫ r in (0 : ℝ)..(1 - t), g ![r, t] =
        ∫ v, ksDH g t v := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have h := intervalIntegral.integral_comp_sub_left (fun r => g ![r, t]) (1 - t)
        (a := 0) (b := 1 - t)
      simp only [sub_self, sub_zero] at h
      rw [← h, ksD_H_section ht.1, MeasureTheory.integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [ht.2])]
      rfl
    rw [intervalIntegral.integral_congr hin, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator measurableSet_Icc]
    congr 1
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht]
      simp [ksD_H_eq_zero_of_not_mem ht]
  rw [hL, integral_integral_swap (ksD_integrable_H hg)]
  have hT : ∀ v, ∫ t, ksDH g t v = ∫ w, ksDH g (w - β * v) v := fun v =>
    (integral_sub_right_eq_self (fun t => ksDH g t v) (β * v)).symm
  simp only [hT]
  rw [← integral_integral_swap (ksD_integrable_H_shear hg ⟨hβ.1.le, hβ.2.le⟩),
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  congr 1
  funext w
  by_cases hw : w ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hw, ksD_H_shear_section hβ,
      MeasureTheory.integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (ksD_ksDYmax_nonneg hβ hw)]
  · rw [indicator_of_notMem hw]
    simp [ksD_H_shear_eq_zero hβ hw]

end QED.ChainProof.SetAKS

end
