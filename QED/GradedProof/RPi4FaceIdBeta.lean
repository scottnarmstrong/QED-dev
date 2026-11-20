/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Join

/-!
# (R-Π₄) step L6d3: the volume of the simplex and a beta-type integral

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. Two elementary
integrals used when an auxiliary loop or a face block is integrated out of a parametric integral:

* **`faceId_volume_simplexSet`**: `vol(Δₘ) = 1/m!`; `faceId_volume_simplexSet_two`: `vol(Δ₂) = 1/2`;
* **`faceId_integral_beta`**: `∫₀¹ ρᵏ (ρa + (1 - ρ)b)^{-(k+2)} dρ = 1/((k+1) a^{k+1} b)` for
  `a, b > 0` (the antiderivative `ρ^{k+1}/((k+1) b (ρa + (1-ρ)b)^{k+1})`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.Feynman (simplexSet isCompact_simplexSet measurableSet_simplexSet)

/-- **The volume of the standard simplex**: `vol(Δₘ) = 1/m!`. -/
theorem faceId_volume_simplexSet (m : ℕ) :
    (volume (simplexSet m)).toReal = ((m.factorial : ℕ) : ℝ)⁻¹ := by
  induction m with
  | zero =>
    have h : simplexSet 0 = univ :=
      eq_univ_of_forall fun x => (mem_simplexSet_iff_forall x).mpr ⟨fun i => i.elim0, by simp⟩
    rw [h]
    rw [MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  | succ m ih =>
    have hfin : IntegrableOn (fun _ : Fin (m + 1) → ℝ => (1 : ℝ)) (simplexSet (m + 1)) :=
      integrableOn_const (isCompact_simplexSet _).measure_lt_top.ne
    have h := integral_simplex_peel hfin
    simp only [setIntegral_const, smul_eq_mul, mul_one] at h
    rw [Measure.real, Measure.real] at h
    rw [h, ih]
    have hI : ∫ t in (0 : ℝ)..1, (1 - t) ^ m * ((m.factorial : ℕ) : ℝ)⁻¹ =
        ((m + 1 : ℕ) : ℝ)⁻¹ * ((m.factorial : ℕ) : ℝ)⁻¹ := by
      rw [intervalIntegral.integral_mul_const]
      congr 1
      have := intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ m) (a := 0) (b := 1)
        (1 : ℝ)
      simp only [sub_zero, sub_self] at this
      rw [this, integral_pow]
      push_cast
      field_simp
      ring
    rw [hI, Nat.factorial_succ]
    push_cast
    rw [mul_inv]

/-- **`vol(Δ₂) = 1/2`.** -/
theorem faceId_volume_simplexSet_two : (volume (simplexSet 2)).toReal = 1 / 2 := by
  rw [faceId_volume_simplexSet]
  norm_num [Nat.factorial]

/-- **A beta-type integral**: `∫₀¹ ρᵏ (ρa + (1 - ρ)b)^{-(k+2)} dρ = 1/((k+1) a^{k+1} b)`. -/
theorem faceId_integral_beta (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ ρ in (0 : ℝ)..1, ρ ^ k * ((ρ * a + (1 - ρ) * b) ^ (k + 2))⁻¹ =
      (((k + 1 : ℕ) : ℝ) * a ^ (k + 1) * b)⁻¹ := by
  set L : ℝ → ℝ := fun ρ => ρ * a + (1 - ρ) * b with hL
  have hLpos : ∀ ρ ∈ uIcc (0 : ℝ) 1, 0 < L ρ := by
    intro ρ hρ
    rw [uIcc_of_le zero_le_one] at hρ
    simp only [hL]
    rcases eq_or_lt_of_le hρ.1 with h0 | h0
    · rw [← h0]; simp [hb]
    · nlinarith [hρ.2]
  set F : ℝ → ℝ := fun ρ => ρ ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * b * L ρ ^ (k + 1)) with hF
  have hderiv : ∀ ρ ∈ uIcc (0 : ℝ) 1,
      HasDerivAt F (ρ ^ k * ((L ρ) ^ (k + 2))⁻¹) ρ := by
    intro ρ hρ
    have hL0 := (hLpos ρ hρ).ne'
    have hLd : HasDerivAt (fun x => b + (a - b) * x) ((a - b) * 1) ρ :=
      ((hasDerivAt_id ρ).const_mul (a - b)).const_add b
    have hLe : L = fun x => b + (a - b) * x := by funext x; simp only [hL]; ring
    have hD := (hLd.pow (k + 1)).const_mul ((((k + 1 : ℕ) : ℝ)) * b)
    have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hne : (((k + 1 : ℕ) : ℝ)) * b * (b + (a - b) * ρ) ^ (k + 1) ≠ 0 := by
      have : b + (a - b) * ρ = L ρ := by rw [hLe]
      rw [this]; positivity
    have h1 := (hasDerivAt_pow (k + 1) ρ).div hD hne
    have hFe : F = fun x => x ^ (k + 1) /
        ((((k + 1 : ℕ) : ℝ)) * b * (b + (a - b) * x) ^ (k + 1)) := by
      funext x; simp only [hF, hLe]
    rw [hFe]
    convert h1 using 1
    have hLr : L ρ = b + (a - b) * ρ := by rw [hLe]
    rw [hLr] at hL0 ⊢
    simp only [Nat.add_sub_cancel, Pi.pow_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun ρ => ρ ^ k * ((L ρ) ^ (k + 2))⁻¹) (uIcc (0 : ℝ) 1) := by
    refine (continuousOn_pow k).mul (ContinuousOn.inv₀ ?_ fun ρ hρ => (pow_pos (hLpos ρ hρ) _).ne')
    exact (Continuous.continuousOn (by simp only [hL]; fun_prop)).pow _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [hF, hL]
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  simp
  ring

end QED.GradedProof.RPi4

end
