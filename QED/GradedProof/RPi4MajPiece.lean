/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajRayPv
public import QED.GradedProof.RPi4MajKinds

/-!
# (R-Π₄) step L10: one eight-line one-loop piece along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. For the line
kinds `kinds5 b` with `b₀ ≠ b₄` (some line carries `k`, some does not) the hypotheses of
`QED.GradedProof.RPi4.maj_pv_ray` reduce to one bound on the degree-four part of the numerator
at the shift `ℓ₀ = -σ v`, `σ = c/a`:

`‖Q₄(-σ v, 0)‖ ≤ K σ (1 - σ)` for `σ ∈ [0, 1]`.

Indeed `T₁(Q₄) = 6 Q₄(-S)/U²`, `B = a σ (1 - σ)` (`QED.GradedProof.RPi4.maj_remainder_kinds5`), so
`‖T₁(Q₄)‖ / B ≤ 6 K / (U² a)`, integrable (`QED.GradedProof.RPi4.maj_integrableOn_probe`).

* **`maj_piece_ray`**: the parametric value of such a piece along the ray is `O(s)` with
  increments `O(s - s')`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

theorem maj_measurable_remainder {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) :
    Measurable fun x : Fin m → ℝ => remainder α (simplexPoint x) cs := by
  have h := (measurable_symanzikV α (fun i => cs i • majRayVec 1) 0).comp
    (continuous_simplexPoint' (m := m)).measurable
  have e : (fun x : Fin m → ℝ => remainder α (simplexPoint x) cs) =
      (fun z => symanzikV α (fun i => cs i • majRayVec 1) 0 z) ∘ fun x => simplexPoint x := by
    funext x
    simp [maj_symanzikV_ray α 0 (simplexPoint x) cs zero_le_one]
  rw [e]
  exact h

/-- **One piece along the ray**: if the degree-four part of the numerator vanishes like
`σ (1 - σ)` at the shift, the parametric value is `O(s)` with increments `O(s - s')`. -/
theorem maj_piece_ray {b : Fin 5 → Bool} (hb : b 0 ≠ b 4) {Ms : Fin 5 → ℝ} {m₀ : ℝ}
    (hm₀ : 0 < m₀) (hMs : ∀ i, m₀ ≤ Ms i)
    {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {Q₄ Q₂ : LoopQuartic}
    (h₄ : ∀ ℓ, Q₄.eval ℓ = Q₄.eval ![ℓ 0, 0]) (h₂ : ∀ ℓ, Q₂.eval ℓ = Q₂.eval ![ℓ 0, 0])
    (hq₂ : Q₂.quart = 0)
    (hN : ∀ r : ℝ, 0 < r → ∀ ℓ, N (r • majRayVec 1) ℓ =
      (r : ℂ) ^ 4 * Q₄.eval (r⁻¹ • ℓ) + (r : ℂ) ^ 2 * Q₂.eval (r⁻¹ • ℓ))
    {K : ℝ} (hK : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      ‖Q₄.eval ![-(σ • majRayVec 1), 0]‖ ≤ K * (σ * (1 - σ))) :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s →
      ‖pvOf (N (majRayVec s)) (majKAlpha b) (fun i => majKCs b i • majRayVec s)
        ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀]‖ ≤ C * s ∧
      ∀ s' : ℝ, 1 ≤ s' → s' ≤ s →
        ‖pvOf (N (majRayVec s)) (majKAlpha b) (fun i => majKCs b i • majRayVec s)
            ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] -
          pvOf (N (majRayVec s')) (majKAlpha b) (fun i => majKCs b i • majRayVec s')
            ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀]‖ ≤ C * (s - s') := by
  have hij : ∃ i j : Fin 5, b i = true ∧ b j = false := by
    cases h0 : b 0 <;> cases h4 : b 4 <;> simp only [h0, h4, ne_eq, not_true_eq_false] at hb
    · exact ⟨4, 0, h4, h0⟩
    · exact ⟨0, 4, h0, h4⟩
  obtain ⟨i, j, hi, hj⟩ := hij
  have hpos : ∀ᵐ x ∂(volume.restrict (simplexSet 7)), ∀ l, 0 < simplexPoint x l := by
    filter_upwards [QED.TwoLoop.UnitSCCt.ae_mem_openSimplex' (by norm_num : 0 < 7)] with x hx
    exact QED.TwoLoop.UnitSCCt.simplexPoint_pos_of_mem_openSimplex' hx
  have hBp : ∀ᵐ x ∂(volume.restrict (simplexSet 7)),
      0 < remainder (majKAlpha b) (simplexPoint x) (majKCs b) := by
    filter_upwards [hpos] with x hz using maj_remainder_pos b hz hi hj
  refine maj_pv_ray hm₀ (fun l => by fin_cases l <;> simp [hMs]) (maj_crit_kinds5 b) (by decide)
    (maj_alpha_kinds5 b) h₄ h₂ hq₂ hN hBp ?_
  -- the weight of the degree-four monomial
  have hco := (integrableOn_coeff Q₄ (majKAlpha b) (fun i => majKCs b i • majRayVec 1) le_rfl
    (maj_crit_kinds5 b) (refinedBound_of_dependsOnZero _ (by decide) (maj_alpha_kinds5 b) Q₄
      h₄)).1
  have hK0 : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hK (1 / 2) (by norm_num) (by norm_num))
    nlinarith
  refine Integrable.mono' ((maj_integrableOn_probe b).const_mul (6 * K))
    ((hco.aestronglyMeasurable.norm.aemeasurable.div
      (maj_measurable_remainder _ _).aemeasurable).aestronglyMeasurable) ?_
  filter_upwards [hpos, hBp] with x hz hB
  set z := simplexPoint x with hzd
  have ha : 0 < majKA z := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4
    unfold majKA; linarith
  have hb' : 0 < majKB z := by
    have := hz 5; have := hz 6; have := hz 7
    unfold majKB; linarith
  set σ := majKC b z / majKA z with hσ
  have hBe : remainder (majKAlpha b) z (majKCs b) = majKA z * (σ * (1 - σ)) := by
    rw [maj_remainder_kinds5 b ha.ne' hb'.ne', hσ]
    field_simp
  have hσσ : 0 < σ * (1 - σ) := by
    rw [hBe] at hB
    exact pos_of_mul_pos_right hB ha.le
  have hσ0 : 0 ≤ σ := by
    by_contra h
    have := lt_of_not_ge h
    nlinarith
  have hσ1 : σ ≤ 1 := by
    by_contra h
    have := lt_of_not_ge h
    nlinarith
  -- the value of the numerator at the shift
  have hS : -loopShift (majKAlpha b) (fun i => majKCs b i • majRayVec 1) z =
      ![-(σ • majRayVec 1), -loopShift (majKAlpha b) (fun i => majKCs b i • majRayVec 1) z 1] := by
    funext t
    fin_cases t
    · simp [maj_loopShift_kinds5 b _ ha.ne' hb'.ne', hσ]
    · simp
  have hG : ‖Q₄.eval (-loopShift (majKAlpha b) (fun i => majKCs b i • majRayVec 1) z)‖ ≤
      K * (σ * (1 - σ)) := by
    rw [h₄, hS]
    simpa using hK σ hσ0 hσ1
  have hU : symanzikU (majKAlpha b) z = majKA z * majKB z := maj_symanzikU_kinds5 b z
  have hUp : 0 < (majKA z * majKB z) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hB.le), hBe]
  simp only [coeffOne, hU, ← hzd]
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hUp]
  have h6 : ‖(((7 - 4).factorial : ℕ) : ℂ)‖ = 6 := by norm_num [Nat.factorial]
  rw [h6, div_le_iff₀ (mul_pos ha hσσ)]
  calc ((majKA z * majKB z) ^ 2)⁻¹ * (6 * ‖Q₄.eval (-loopShift (majKAlpha b)
        (fun i => majKCs b i • majRayVec 1) z)‖) ≤
        ((majKA z * majKB z) ^ 2)⁻¹ * (6 * (K * (σ * (1 - σ)))) := by gcongr
    _ = 6 * K * (1 / ((majKA z * majKB z) ^ 2 * majKA z)) * (majKA z * (σ * (1 - σ))) := by
        field_simp

end QED.GradedProof.RPi4

end
