/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajRaySum
public import QED.GradedProof.RPi4MajTilt

/-!
# (R-Π₄) step L10: an eight-line parametric value along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. Let the
numerator along the ray `k = r v` (`v = majRayVec 1`, `r = √s`) be
`N(r v)(ℓ) = r⁴ Q₄(ℓ/r) + r² Q₂(ℓ/r)` with `Q₂` without quartic part, both depending on `ℓ₀`
only, and the line momenta `cᵢ k`. By the dilation of the coefficients
(`QED.GradedProof.RPi4.maj_coeffOne_dilateQ`, …) and `V = V₀ + s B`
(`QED.GradedProof.RPi4.maj_symanzikV_ray`) the parametric integrand is the sum of five monomials

`T₁(Q₄) s²/V⁴ + T₂(Q₄) s/V³ + T₃(Q₄)/V² + T₁(Q₂) s/V⁴ + T₂(Q₂)/V³`

with the coefficients at `r = 1`, integrable by `QED.TwoLoop.ClassLimit.integrableOn_coeff`.
The only monomial with `j = 4` needs `T₁(Q₄)/B` integrable: the numerator at the shift must
vanish where `B = 0`.

* `maj_majRayVec_eq`: `majRayVec s = √s • majRayVec 1`;
* **`maj_pv_ray`**: under these hypotheses the parametric value `pvOf (N (majRayVec s))` is
  `O(s)` with increments `O(s - s')` for `s ≥ s' ≥ 1`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.MassScaling
open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZeroLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZeroExplicit (paramNum_qsum)
open QED.Integration.Feynman (simplexSet simplexPoint)

theorem maj_majRayVec_eq {s : ℝ} (hs : 0 ≤ s) : majRayVec s = Real.sqrt s • majRayVec 1 := by
  have h : Real.sqrt (2 * Real.sqrt s ^ 2 - s) = Real.sqrt s := by
    rw [Real.sq_sqrt hs]
    ring_nf
  funext μ
  fin_cases μ <;> simp [majRayVec, tiltVec, h]
  norm_num

theorem maj_eval_smul_dep {Q : LoopQuartic} (h : ∀ ℓ, Q.eval ℓ = Q.eval ![ℓ 0, 0]) (t : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Q.eval (t • ℓ) = Q.eval (t • ![ℓ 0, 0]) := by
  rw [h (t • ℓ), h (t • ![ℓ 0, 0])]
  simp

/-- **An eight-line parametric value along the ray** is `O(s)` with increments `O(s - s')`. -/
theorem maj_pv_ray {α : Fin 8 → Fin 2 → ℝ} {cs M : Fin 8 → ℝ} {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hM : ∀ i, m₀ ≤ M i) {E : Finset (Fin 8)} (hcrit : NoSubdivergenceRefined 2 E α)
    (hE : E.card = 4) (hα : ∀ e ∈ E, α e = ![1, 0])
    {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {Q₄ Q₂ : LoopQuartic}
    (h₄ : ∀ ℓ, Q₄.eval ℓ = Q₄.eval ![ℓ 0, 0]) (h₂ : ∀ ℓ, Q₂.eval ℓ = Q₂.eval ![ℓ 0, 0])
    (hq₂ : Q₂.quart = 0)
    (hN : ∀ r : ℝ, 0 < r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      (r : ℂ) ^ 4 * Q₄.eval (r⁻¹ • ℓ) + (r : ℂ) ^ 2 * Q₂.eval (r⁻¹ • ℓ))
    (hBp : ∀ᵐ x ∂(volume.restrict (simplexSet 7)), 0 < remainder α (simplexPoint x) cs)
    (hint : Integrable (fun x => ‖coeffOne Q₄ α (fun i => cs i • majRayVec 1) x‖ /
      remainder α (simplexPoint x) cs) (volume.restrict (simplexSet 7))) :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s →
      ‖pvOf (N (majRayVec s)) α (fun i => cs i • majRayVec s) M‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s →
        ‖pvOf (N (majRayVec s)) α (fun i => cs i • majRayVec s) M -
          pvOf (N (majRayVec s')) α (fun i => cs i • majRayVec s') M‖ ≤ C * (s - s') := by
  set v := majRayVec 1 with hv
  set p₁ : Fin 8 → Fin 4 → ℝ := fun i => cs i • v with hp₁
  set ps : ℝ → Fin 8 → Fin 4 → ℝ := fun s i => cs i • majRayVec s with hps
  have hmom : ∀ s : ℝ, 0 ≤ s → ps s = Real.sqrt s • p₁ := fun s hs => by
    funext i
    simp only [hps, hp₁, Pi.smul_apply, maj_majRayVec_eq hs, hv]
    exact smul_comm _ _ _
  -- the quartic along the ray
  set R : ℝ → LoopQuartic := fun s => qsum Finset.univ
    ![((Real.sqrt s : ℝ) : ℂ) ^ 4, ((Real.sqrt s : ℝ) : ℂ) ^ 2]
    ![dilateQ 1 (((Real.sqrt s)⁻¹ : ℝ) : ℂ) Q₄, dilateQ 1 (((Real.sqrt s)⁻¹ : ℝ) : ℂ) Q₂] with hR
  have hRe : ∀ s : ℝ, 1 ≤ s → (R s).eval = N (majRayVec s) := fun s hs => by
    funext ℓ
    rw [maj_majRayVec_eq (by linarith), hN _ (Real.sqrt_pos.mpr (by linarith))]
    simp only [hR, eval_qsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      eval_dilateQ, one_mul]
  have hRd : ∀ s : ℝ, ∀ ℓ, (R s).eval ℓ = (R s).eval ![ℓ 0, 0] := fun s ℓ => by
    simp only [hR, eval_qsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      eval_dilateQ, maj_eval_smul_dep h₄ _ ℓ,
      maj_eval_smul_dep h₂ _ ℓ]
  -- the integrand
  set f : ℝ → (Fin 7 → ℝ) → ℂ := fun s x => paramIntegrand (R s) α (ps s) M 0 x with hf
  have hpv : ∀ s : ℝ, 1 ≤ s → pvOf (N (majRayVec s)) α (ps s) M =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet 7, f s x := fun s hs => pvOf_eq (hRe s hs) α _ M
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have hV₀ : ∀ z : Fin 8 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → m₀ ^ 2 ≤ ∑ i, z i * M i ^ 2 := by
    intro z hz hz1
    calc m₀ ^ 2 = ∑ i, z i * m₀ ^ 2 := by rw [← Finset.sum_mul, hz1, one_mul]
      _ ≤ ∑ i, z i * M i ^ 2 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm₀.le (hM i) 2) (hz i)
  have hVs : ∀ s : ℝ, 0 ≤ s → ∀ z : Fin 8 → ℝ, symanzikV α (ps s) M z =
      ∑ i, z i * M i ^ 2 + s * remainder α z cs := fun s hs z =>
    maj_symanzikV_ray α M z cs hs
  have hf_meas : ∀ s : ℝ, 1 ≤ s → AEStronglyMeasurable (f s) (volume.restrict (simplexSet 7)) :=
    fun s hs => (integrableOn_paramIntegrand_zero (R s) α (ps s) M le_rfl hcrit
      (refinedBound_of_dependsOnZero α hE hα (R s) (hRd s)) hm2 fun z hz hz1 hU => by
        rw [hVs s (by linarith) z]
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ s) (remainder_nonneg α hz hU cs)
        linarith [hV₀ z hz hz1]).aestronglyMeasurable
  -- the coefficients
  have hco := fun (Q : LoopQuartic) (hQ : ∀ ℓ, Q.eval ℓ = Q.eval ![ℓ 0, 0]) =>
    integrableOn_coeff Q α p₁ le_rfl hcrit (refinedBound_of_dependsOnZero α hE hα Q hQ)
  obtain ⟨i₄, j₄, -⟩ := hco Q₄ h₄
  obtain ⟨i₂, j₂, -⟩ := hco Q₂ h₂
  have k₄ := (hco Q₄ h₄).2.2
  set π₅ : Fin 5 → (Fin 7 → ℝ) → ℂ := ![coeffOne Q₄ α p₁, coeffTwo Q₄ α p₁, coeffThree Q₄ α,
    coeffOne Q₂ α p₁, coeffTwo Q₂ α p₁] with hπ₅
  set j₅ : Fin 5 → ℕ := ![4, 2, 0, 2, 0] with hj₅
  set n₅ : Fin 5 → ℕ := ![4, 3, 2, 4, 3] with hn₅
  have hmain : ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ‖∫ x in simplexSet 7, f s x‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s →
        ‖(∫ x in simplexSet 7, f s x) - ∫ x in simplexSet 7, f s' x‖ ≤ C * (s - s') := by
    refine maj_integral_sum_phi (κ := Fin 5) hm2 (V₀ := fun x => ∑ i, simplexPoint x i * M i ^ 2)
      (B := fun x => remainder α (simplexPoint x) cs) (g := π₅) (j := j₅) (n := n₅)
      (fun t => by fin_cases t <;> simp [hj₅]) (fun t => by fin_cases t <;> simp [hn₅]) ?_ ?_
      hf_meas ?_
    · filter_upwards [hBp, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet 7)]
        with x hB hx
      have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
      exact ⟨hV₀ _ hz.1 hz.2, hB.le, fun _ _ => hB⟩
    · intro t
      fin_cases t
      · refine (hint.const_mul (1 / (m₀ ^ 2) ^ 3)).congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [hπ₅, hj₅, hn₅, majOmega]
        simp
        ring
      · exact (j₄.norm.mul_const (1 / (m₀ ^ 2) ^ 3)).congr (Filter.Eventually.of_forall fun x => by
          simp [hπ₅, hj₅, hn₅, majOmega])
      · exact (k₄.norm.mul_const (1 / (m₀ ^ 2) ^ 2)).congr (Filter.Eventually.of_forall fun x => by
          simp [hπ₅, hj₅, hn₅, majOmega])
      · exact (i₂.norm.mul_const (1 / (m₀ ^ 2) ^ 4)).congr (Filter.Eventually.of_forall fun x => by
          simp [hπ₅, hj₅, hn₅, majOmega])
      · exact (j₂.norm.mul_const (1 / (m₀ ^ 2) ^ 3)).congr (Filter.Eventually.of_forall fun x => by
          simp [hπ₅, hj₅, hn₅, majOmega])
    · filter_upwards [hBp, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet 7)]
        with x hB hx
      have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
      intro s hs
      set r := Real.sqrt s with hr
      have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
      have hr2 : r ^ 2 = s := Real.sq_sqrt (by linarith)
      set V₀ := ∑ i, simplexPoint x i * M i ^ 2 with hV₀d
      set B := remainder α (simplexPoint x) cs with hBd
      have hVpos : 0 < V₀ + s * B := by
        have := hV₀ _ hz.1 hz.2
        nlinarith
      have hV : symanzikV α (ps s) M (simplexPoint x) = V₀ + s * B := hVs s (by linarith) _
      have hVr : symanzikV α (r • p₁) M (simplexPoint x) = V₀ + s * B := by
        rw [← hmom s (by linarith)]
        exact hV
      simp only [hf]
      rw [paramIntegrand_zero_eq (R s) α (ps s) M (by norm_num) (by rw [hV]; exact hVpos.ne')]
      simp only [hR, paramNum_qsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        hmom s (by linarith)]
      rw [← hr]
      simp only [paramNum, maj_coeffOne_dilateQ _ _ hr0.ne',
        maj_coeffTwo_dilateQ _ _ hr0.ne', maj_coeffThree_dilateQ, maj_coeffThree_of_quart hq₂,
        hVr]
      simp only [Fin.sum_univ_five, hπ₅, hj₅, hn₅, majPhi, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons]
      have hVc : ((V₀ + s * B : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hVpos.ne'
      have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
      have hs2 : (s : ℂ) = (r : ℂ) ^ 2 := by rw [← hr2]; push_cast; ring
      push_cast
      rw [hs2]
      field_simp
      ring
  obtain ⟨C, hC⟩ := hmain
  refine ⟨‖-((π : ℂ) ^ 4)‖ * C, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · rw [hpv s hs, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC s hs).1 (norm_nonneg _)
  · rw [hpv s hs, hpv s' hs', ← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hC s hs).2 s' hs' hss) (norm_nonneg _)

end QED.GradedProof.RPi4

end
