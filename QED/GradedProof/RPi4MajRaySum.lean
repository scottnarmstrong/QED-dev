/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajRayTerm
public import QED.TwoLoop.MassScalingBasic

/-!
# (R-Π₄) step L10: sums of ray monomials and dilated parametric coefficients

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. Two inputs of the
large-`s` bound of a parametric value along the ray `k = √s v`:

* the integral of a finite sum `∑ₜ gₜ φ_{jₜ nₜ}(s)` of the monomials
  `QED.GradedProof.RPi4.majPhi` is `O(s)` with increments `O(s - s')`, if each `‖gₜ‖ ωₜ` is
  integrable (`maj_integral_sum_phi`; one null set for all `s`);
* the parametric coefficients of the dilated quartic `ℓ ↦ a Q(ℓ/r)` at the momenta `r p` (the
  masses are not scaled) are `a T₁`, `a r⁻² T₂`, `a r⁻⁴ T₃` (`maj_coeffOne_dilateQ`, …); the third
  coefficient vanishes for a quartic without quartic part (`maj_coeffThree_of_quart`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.RPi4

/-! ### Sums of monomials -/

section Integral

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **Pointwise bounds integrate**: if `‖f s‖ ≤ s K` and `‖f s - f s'‖ ≤ (s - s') K` off one null
set, for all `s ≥ s' ≥ 1`, with `K` integrable, then `∫ f s` is `O(s)` with increments
`O(s - s')`. -/
theorem maj_integral_bounds {f : ℝ → ι → ℂ} {K : ι → ℝ} (hK : Integrable K μ)
    (hf : ∀ s : ℝ, 1 ≤ s → AEStronglyMeasurable (f s) μ)
    (hpt : ∀ᵐ x ∂μ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s →
      ‖f s x‖ ≤ s * K x ∧ ‖f s x - f s' x‖ ≤ (s - s') * K x) :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ‖∫ x, f s x ∂μ‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s → ‖∫ x, f s x ∂μ - ∫ x, f s' x ∂μ‖ ≤ C * (s - s') := by
  have hval : ∀ s : ℝ, 1 ≤ s → ∀ᵐ x ∂μ, ‖f s x‖ ≤ s * K x := fun s hs => by
    filter_upwards [hpt] with x hx using (hx s s hs le_rfl).1
  have hint : ∀ s : ℝ, 1 ≤ s → Integrable (f s) μ := fun s hs =>
    Integrable.mono' (hK.const_mul s) (hf s hs) (hval s hs)
  refine ⟨∫ x, K x ∂μ, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · calc ‖∫ x, f s x ∂μ‖ ≤ ∫ x, s * K x ∂μ := norm_integral_le_of_norm_le (hK.const_mul s)
          (hval s hs)
      _ = (∫ x, K x ∂μ) * s := by rw [integral_const_mul]; ring
  · rw [← integral_sub (hint s hs) (hint s' hs')]
    calc ‖∫ x, (f s x - f s' x) ∂μ‖ ≤ ∫ x, (s - s') * K x ∂μ :=
          norm_integral_le_of_norm_le (hK.const_mul _) (by
            filter_upwards [hpt] with x hx using (hx s s' hs' hss).2)
      _ = (∫ x, K x ∂μ) * (s - s') := by rw [integral_const_mul]; ring

/-- **The pointwise bounds of one term** `g φⱼ(s)`. -/
theorem maj_term_bounds {c V₀ B : ℝ} (hc : 0 < c) (hV₀ : c ≤ V₀) (hB : 0 ≤ B) {j n : ℕ}
    (hj : j ≤ 4) (hn : 1 ≤ n) (hBp : 3 ≤ j → 0 < B) (g : ℂ) {s s' : ℝ} (hs' : 1 ≤ s')
    (hss : s' ≤ s) :
    ‖g * (majPhi j n V₀ B s : ℂ)‖ ≤ s * ((4 + n) * (‖g‖ * majOmega j n c B)) ∧
      ‖g * (majPhi j n V₀ B s : ℂ) - g * (majPhi j n V₀ B s' : ℂ)‖ ≤
        (s - s') * ((4 + n) * (‖g‖ * majOmega j n c B)) := by
  obtain ⟨h1, h2⟩ := maj_phi_bounds hc hV₀ hB hn hs' hss hj hBp
  have hs : 0 ≤ s := by linarith
  have hφ : 0 ≤ majPhi j n V₀ B s := by
    unfold majPhi
    exact div_nonneg (by positivity) (pow_nonneg (maj_V_pos hc hV₀ hB hs).le n)
  have hω : 0 ≤ majOmega j n c B := by
    unfold majOmega
    split_ifs <;> positivity
  have hπω : 0 ≤ ‖g‖ * majOmega j n c B := mul_nonneg (norm_nonneg _) hω
  constructor
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ]
    calc ‖g‖ * majPhi j n V₀ B s ≤ ‖g‖ * (s * majOmega j n c B) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = s * (1 * (‖g‖ * majOmega j n c B)) := by ring
      _ ≤ s * ((4 + n) * (‖g‖ * majOmega j n c B)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hπω) hs
  · rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc ‖g‖ * |majPhi j n V₀ B s - majPhi j n V₀ B s'| ≤
          ‖g‖ * ((4 + n) * majOmega j n c B * (s - s')) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (s - s') * ((4 + n) * (‖g‖ * majOmega j n c B)) := by ring

/-- **The large-`s` tool for a finite sum of monomials**: if `f s = ∑ₜ gₜ φ_{jₜ nₜ}(s)` for all
`s ≥ 1` off one null set and each `‖gₜ‖ ωₜ` is integrable, then `∫ f s` is `O(s)` with increments
`O(s - s')`. -/
theorem maj_integral_sum_phi {κ : Type*} [Fintype κ] {c : ℝ} (hc : 0 < c) {V₀ B : ι → ℝ}
    {g : κ → ι → ℂ} {j n : κ → ℕ} (hj : ∀ t, j t ≤ 4) (hn : ∀ t, 1 ≤ n t)
    (hVB : ∀ᵐ x ∂μ, c ≤ V₀ x ∧ 0 ≤ B x ∧ ∀ t, 3 ≤ j t → 0 < B x)
    (hint : ∀ t, Integrable (fun x => ‖g t x‖ * majOmega (j t) (n t) c (B x)) μ)
    {f : ℝ → ι → ℂ} (hf : ∀ s : ℝ, 1 ≤ s → AEStronglyMeasurable (f s) μ)
    (hfe : ∀ᵐ x ∂μ, ∀ s : ℝ, 1 ≤ s →
      f s x = ∑ t, g t x * (majPhi (j t) (n t) (V₀ x) (B x) s : ℂ)) :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ‖∫ x, f s x ∂μ‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s → ‖∫ x, f s x ∂μ - ∫ x, f s' x ∂μ‖ ≤ C * (s - s') := by
  refine maj_integral_bounds (K := fun x => ∑ t, (4 + n t) * (‖g t x‖ *
    majOmega (j t) (n t) c (B x))) (integrable_finsetSum _ fun t _ => (hint t).const_mul _) hf ?_
  filter_upwards [hVB, hfe] with x ⟨h0, h1, h2⟩ he
  intro s s' hs' hss
  have hT := fun t => maj_term_bounds hc h0 h1 (hj t) (hn t) (h2 t) (g t x) hs' hss
  rw [he s (hs'.trans hss), he s' hs', ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  exact ⟨(norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => (hT t).1),
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => (hT t).2)⟩

end Integral

/-! ### Dilated quartics at scaled momenta -/

section Dilate

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling
open QED.Integration.Feynman (simplexPoint)

variable {m : ℕ} (Q : LoopQuartic) (a : ℂ) {r : ℝ} (hr : r ≠ 0) (α : Fin (m + 1) → Fin 2 → ℝ)
  (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ)
include hr

theorem maj_inv_smul_loopShift :
    r⁻¹ • -loopShift α (r • p) (simplexPoint x) = -loopShift α p (simplexPoint x) := by
  rw [loopShift_smul, smul_neg, smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem maj_loopComp_loopShift :
    (fun i => ((r⁻¹ : ℝ) : ℂ) * loopComp (-loopShift α (r • p) (simplexPoint x)) i) =
      loopComp (-loopShift α p (simplexPoint x)) := by
  rw [← maj_inv_smul_loopShift hr α p x]
  funext i
  simp [loopComp]

/-- The first coefficient of `ℓ ↦ a Q(ℓ/r)` at the momenta `r p` is `a T₁`. -/
theorem maj_coeffOne_dilateQ :
    coeffOne (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) x = a * coeffOne Q α p x := by
  simp only [coeffOne, eval_dilateQ, maj_inv_smul_loopShift hr]
  ring

/-- The second coefficient of `ℓ ↦ a Q(ℓ/r)` at the momenta `r p` is `a r⁻² T₂`. -/
theorem maj_coeffTwo_dilateQ :
    coeffTwo (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) x =
      a * ((r⁻¹ : ℝ) : ℂ) ^ 2 * coeffTwo Q α p x := by
  simp only [coeffTwo, contractTwo_dilateQ, maj_loopComp_loopShift hr]
  ring

omit hr in
/-- The third coefficient of `ℓ ↦ a Q(ℓ/r)` is `a r⁻⁴ T₃`. -/
theorem maj_coeffThree_dilateQ :
    coeffThree (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α x = a * ((r⁻¹ : ℝ) : ℂ) ^ 4 * coeffThree Q α x := by
  simp only [coeffThree, contractFour_dilateQ]
  ring

end Dilate

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit in
/-- The third coefficient vanishes for a quartic without quartic part. -/
theorem maj_coeffThree_of_quart {m : ℕ} {Q : LoopQuartic} (hQ : Q.quart = 0)
    (α : Fin (m + 1) → Fin 2 → ℝ) (x : Fin m → ℝ) : coeffThree Q α x = 0 := by
  simp [coeffThree, LoopQuartic.contractFour, hQ]

end QED.GradedProof.RPi4

end
