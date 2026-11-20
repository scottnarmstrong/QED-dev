/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VWard
public import QED.GradedProof.RPi4FaceIdLapF
public import QED.Algebra.Contraction

/-!
# (R-Π₄) step L6d3: the Dirac identities of the faces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. With
`kV ρ σ = faceIdKV · η_ρσ` (`faceId_kV_eq`) and the mostly-plus contractions
`γ^a γ^ν γ_a = 2γ^ν`, `γ^a γ_a = -4`:

* **vertex faces of `VB`**: the half loop-`1` (resp. loop-`0`) Laplacian of the class numerator is
  `2 faceIdKV · Tr[γ^μ S(ℓ₀) γ^ν S(k + ℓ₀)]` (`faceId_lapF_vNum_VB_one`), resp.
  `2 faceIdKV · Tr[γ^μ S(ℓ₁ - k) γ^ν S(ℓ₁)]` (`faceId_lapF_vNum_VB_zero`): the gauge counterterm
  vertex `γ^ν` (resp. `γ^μ`);
* **self-energy faces of `VA`, `VC`**: at the midpoint `ℓ₁ = y/2` of the face simplex (the
  average of a numerator affine in `ℓ₁`, `faceId_eval_avg_seT_mid`), the class numerator is
  `faceIdKV` times the one-loop numerator with the insertion `-(y̸ + 4m) = -fermionCtMatrix 1 4 m y`
  (`faceId_vNum_VA_half`, `y = ℓ₀`; `faceId_vNum_VC_half`, `y = k + ℓ₀`).

The constants were checked numerically on the Lean gamma matrices first
(deviation `1e-14`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.Dirac

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Gamma-matrix contractions -/

theorem faceId_gammaLower_eq_smul (a : Fin 4) :
    gammaLower a = ((Minkowski.metric a a : ℝ) : ℂ) • gamma a := by
  fin_cases a <;> simp [gammaLower, Minkowski.metric]

theorem faceId_metric_sq (a : Fin 4) :
    ((Minkowski.metric a a : ℝ) : ℂ) * ((Minkowski.metric a a : ℝ) : ℂ) = 1 := by
  fin_cases a <;> simp [Minkowski.metric]

theorem faceId_slash_single (a : Fin 4) (c : ℝ) :
    slash (Pi.single a c) = (c : ℂ) • gammaLower a := by
  fin_cases a <;>
    simp [slash, gammaLower, Minkowski.lower, Minkowski.metric, Pi.single_apply]

theorem faceId_gamma_eq_slash (a : Fin 4) :
    gamma a = slash (Pi.single a (Minkowski.metric a a)) := by
  rw [faceId_slash_single, faceId_gammaLower_eq_smul, smul_smul, faceId_metric_sq, one_smul]

theorem faceId_contract_gamma (ν : Fin 4) :
    ∑ a, gamma a * gamma ν * gammaLower a = (2 : ℂ) • gamma ν := by
  rw [faceId_gamma_eq_slash ν]
  exact contract_slash _

/-- `η_aa Tr[P γ^a B γ^a R] = Tr[P γ^a B γ_a R]`. -/
theorem faceId_metric_trace_gamma (P B R : Mat) (a : Fin 4) :
    ((Minkowski.metric a a : ℝ) : ℂ) * (P * gamma a * B * gamma a * R).trace =
      (P * (gamma a * B * gammaLower a) * R).trace := by
  rw [faceId_gammaLower_eq_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]

/-- `η_aa Tr[P γ_a B γ_a R] = Tr[P γ^a B γ_a R]`. -/
theorem faceId_metric_trace_gammaLower (P B R : Mat) (a : Fin 4) :
    ((Minkowski.metric a a : ℝ) : ℂ) * (P * gammaLower a * B * gammaLower a * R).trace =
      (P * (gamma a * B * gammaLower a) * R).trace := by
  rw [faceId_gammaLower_eq_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  linear_combination (((Minkowski.metric a a : ℝ) : ℂ) *
    (P * (gamma a * (B * (gamma a * R)))).trace) * faceId_metric_sq a

/-- The second difference of a trace with two factors shifted by `∓ s`. -/
theorem faceId_trace_second (A B C X Y s : Mat) :
    (A * (X - s) * B * (Y - s) * C).trace + (A * (X + s) * B * (Y + s) * C).trace -
      2 * (A * X * B * Y * C).trace = 2 * (A * s * B * s * C).trace := by
  have h : A * (X - s) * B * (Y - s) * C + A * (X + s) * B * (Y + s) * C =
      A * X * B * Y * C + A * X * B * Y * C + (A * s * B * s * C + A * s * B * s * C) := by
    noncomm_ring
  have h2 := congrArg Matrix.trace h
  simp only [Matrix.trace_add] at h2
  linear_combination h2

/-- `Σ_a η_aa Tr[P (γ_a γ^ν γ_a) R] = 2 Tr[P γ^ν R]`. -/
theorem faceId_fold_lower (P R : Mat) (ν : Fin 4) :
    ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) *
      (P * (gammaLower a * gamma ν * gammaLower a) * R).trace = 2 * (P * gamma ν * R).trace := by
  have h : ∀ a, ((Minkowski.metric a a : ℝ) : ℂ) *
      (P * (gammaLower a * gamma ν * gammaLower a) * R).trace =
      (P * (gamma a * gamma ν * gammaLower a) * R).trace := fun a => by
    have := faceId_metric_trace_gammaLower P (gamma ν) R a
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  simp only [h, ← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, faceId_contract_gamma,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- `Σ_a η_aa Tr[P (γ^a γ^ν γ^a) R] = 2 Tr[P γ^ν R]`. -/
theorem faceId_fold_upper (P R : Mat) (ν : Fin 4) :
    ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) *
      (P * (gamma a * gamma ν * gamma a) * R).trace = 2 * (P * gamma ν * R).trace := by
  have h : ∀ a, ((Minkowski.metric a a : ℝ) : ℂ) *
      (P * (gamma a * gamma ν * gamma a) * R).trace =
      (P * (gamma a * gamma ν * gammaLower a) * R).trace := fun a => by
    have := faceId_metric_trace_gamma P (gamma ν) R a
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  simp only [h, ← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, faceId_contract_gamma,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- `Σ_a η_aa Tr[P (γ^a X γ^a) R] = Tr[P (γ^a X γ_a) R]`, summed. -/
theorem faceId_fold_upper_gen (P X R : Mat) :
    ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) * (P * (gamma a * X * gamma a) * R).trace =
      (P * (∑ a, gamma a * X * gammaLower a) * R).trace := by
  have h : ∀ a, ((Minkowski.metric a a : ℝ) : ℂ) * (P * (gamma a * X * gamma a) * R).trace =
      (P * (gamma a * X * gammaLower a) * R).trace := fun a => by
    have := faceId_metric_trace_gamma P X R a
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  simp only [h, ← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum]

/-! ### The photon constant -/

/-- The scalar of the class photon numerator: `kV ρ σ = faceIdKV · η_ρσ`. -/
noncomputable def faceIdKV (e mγ Λ : ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ((I * e) ^ 4 * (1 / I) ^ 5) * ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ)

theorem faceId_kV_eq (e mγ Λ : ℝ) (ρ σ : Fin 4) :
    kV e mγ Λ ρ σ = faceIdKV e mγ Λ * ((Minkowski.metric ρ σ : ℝ) : ℂ) := by
  simp only [kV, faceIdKV, QED.TwoLoop.CountertermLimit.pvPhotonNum]
  push_cast
  ring

/-- The photon double sum is diagonal. -/
theorem faceId_sum_kV (e mγ Λ : ℝ) (f : Fin 4 → Fin 4 → ℂ) :
    ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * f ρ σ =
      faceIdKV e mγ Λ * ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) * f σ σ := by
  simp only [faceId_kV_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_eq_single ρ]
  · ring
  · intro σ _ hσ
    simp [Minkowski.metric, Ne.symm hσ]
  · simp

theorem faceId_eN_add (m : ℝ) (p u : Fin 4 → ℝ) :
    electronNumerator m (p + u) = electronNumerator m p - slash u := by
  simp only [electronNumerator, slash_add]
  abel

theorem faceId_eN_sub (m : ℝ) (p u : Fin 4 → ℝ) :
    electronNumerator m (p - u) = electronNumerator m p + slash u := by
  rw [sub_eq_add_neg, faceId_eN_add, show slash (-u) = -slash u by
    rw [show -u = (-1 : ℝ) • u by simp, slash_smul]; simp]
  abel

/-! ### The vertex faces of `VB` -/

section VB

variable (e mγ Λ m : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)

/-- The class numerator of `VB` with the photon sum made diagonal. -/
theorem faceId_vNum_VB (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν = faceIdKV e mγ Λ * ∑ σ,
      ((Minkowski.metric σ σ : ℝ) : ℂ) * (gamma μ * electronNumerator m (ℓ 0) * gamma σ *
        electronNumerator m (ℓ 1 - k) * gamma ν * electronNumerator m (ℓ 1) * gamma σ *
        electronNumerator m (k + ℓ 0)).trace := by
  simp only [vNum, vT, fm_VB]
  rw [faceId_sum_kV]
  rfl

/-- **The vertex identity of `VB` at loop `1`**: the half loop-`1` Laplacian of the class
numerator is `2 faceIdKV` times the one-loop numerator `Tr[γ^μ S(ℓ₀) γ^ν S(k + ℓ₀)]`. -/
theorem faceId_lapF_vNum_VB_one (ℓ : Fin 2 → Fin 4 → ℝ) :
    faceIdLapF 1 (fun ℓ => vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν) ℓ =
      2 * faceIdKV e mγ Λ * (gamma μ * electronNumerator m (ℓ 0) * gamma ν *
        electronNumerator m (k + ℓ 0)).trace := by
  set S₀ := electronNumerator m (ℓ 0)
  set S₃ := electronNumerator m (k + ℓ 0)
  set X := electronNumerator m (ℓ 1 - k)
  set Y := electronNumerator m (ℓ 1)
  have key : ∀ a σ : Fin 4,
      (gamma μ * S₀ * gamma σ * electronNumerator m ((ℓ + faceIdE 1 a) 1 - k) * gamma ν *
        electronNumerator m ((ℓ + faceIdE 1 a) 1) * gamma σ * S₃).trace +
      (gamma μ * S₀ * gamma σ * electronNumerator m ((ℓ - faceIdE 1 a) 1 - k) * gamma ν *
        electronNumerator m ((ℓ - faceIdE 1 a) 1) * gamma σ * S₃).trace -
      2 * (gamma μ * S₀ * gamma σ * X * gamma ν * Y * gamma σ * S₃).trace =
      2 * ((gamma μ * S₀ * gamma σ) * (gammaLower a * gamma ν * gammaLower a) *
        (gamma σ * S₃)).trace := by
    intro a σ
    have hs : slash (Pi.single a (1 : ℝ)) = gammaLower a := by
      rw [faceId_slash_single]; simp
    have e1 : electronNumerator m (ℓ 1 + Pi.single a 1 - k) = X - gammaLower a := by
      rw [show ℓ 1 + Pi.single a 1 - k = (ℓ 1 - k) + Pi.single a 1 by abel, faceId_eN_add, hs]
    have e2 : electronNumerator m (ℓ 1 + Pi.single a 1) = Y - gammaLower a := by
      rw [faceId_eN_add, hs]
    have e3 : electronNumerator m (ℓ 1 - Pi.single a 1 - k) = X + gammaLower a := by
      rw [show ℓ 1 - Pi.single a 1 - k = (ℓ 1 - k) - Pi.single a 1 by abel, faceId_eN_sub, hs]
    have e4 : electronNumerator m (ℓ 1 - Pi.single a 1) = Y + gammaLower a := by
      rw [faceId_eN_sub, hs]
    rw [(faceId_add_E_one ℓ a).2, (faceId_sub_E_one ℓ a).2, e1, e2, e3, e4]
    have h := faceId_trace_second (gamma μ * S₀ * gamma σ) (gamma ν) (gamma σ * S₃) X Y
      (gammaLower a)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have hF : ∀ a, vNum e mγ Λ aVB baseVB cVB m k (ℓ + faceIdE 1 a) μ ν +
      vNum e mγ Λ aVB baseVB cVB m k (ℓ - faceIdE 1 a) μ ν -
      2 * vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν = faceIdKV e mγ Λ * ∑ σ,
        ((Minkowski.metric σ σ : ℝ) : ℂ) * (2 * ((gamma μ * S₀ * gamma σ) *
          (gammaLower a * gamma ν * gammaLower a) * (gamma σ * S₃)).trace) := by
    intro a
    rw [faceId_vNum_VB, faceId_vNum_VB, faceId_vNum_VB, (faceId_add_E_one ℓ a).1,
      (faceId_sub_E_one ℓ a).1]
    simp only [← key, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  simp only [faceIdLapF, hF]
  have hσ : ∀ σ : Fin 4, ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) *
      ((gamma μ * S₀ * gamma σ) * (gammaLower a * gamma ν * gammaLower a) *
        (gamma σ * S₃)).trace = 2 * (gamma μ * S₀ * (gamma σ * gamma ν * gamma σ) * S₃).trace := by
    intro σ
    rw [faceId_fold_lower]
    simp only [Matrix.mul_assoc]
  have hsum : ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) * (faceIdKV e mγ Λ * ∑ σ,
      ((Minkowski.metric σ σ : ℝ) : ℂ) * (2 * ((gamma μ * S₀ * gamma σ) *
        (gammaLower a * gamma ν * gammaLower a) * (gamma σ * S₃)).trace)) =
      2 * faceIdKV e mγ Λ * ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) * ∑ a,
        ((Minkowski.metric a a : ℝ) : ℂ) * ((gamma μ * S₀ * gamma σ) *
          (gammaLower a * gamma ν * gammaLower a) * (gamma σ * S₃)).trace := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hsum]
  simp only [hσ]
  have h2 := faceId_fold_upper (gamma μ * S₀) S₃ ν
  rw [show ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) *
      (2 * (gamma μ * S₀ * (gamma σ * gamma ν * gamma σ) * S₃).trace) =
      2 * ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) *
        (gamma μ * S₀ * (gamma σ * gamma ν * gamma σ) * S₃).trace by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by ring, h2]
  ring

/-- **The vertex identity of `VB` at loop `0`**: the half loop-`0` Laplacian of the class
numerator is `2 faceIdKV` times the one-loop numerator `Tr[γ^μ S(ℓ₁ - k) γ^ν S(ℓ₁)]`. -/
theorem faceId_lapF_vNum_VB_zero (ℓ : Fin 2 → Fin 4 → ℝ) :
    faceIdLapF 0 (fun ℓ => vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν) ℓ =
      2 * faceIdKV e mγ Λ * (gamma μ * electronNumerator m (ℓ 1 - k) * gamma ν *
        electronNumerator m (ℓ 1)).trace := by
  set S₀ := electronNumerator m (ℓ 0)
  set S₃ := electronNumerator m (k + ℓ 0)
  set X := electronNumerator m (ℓ 1 - k)
  set Y := electronNumerator m (ℓ 1)
  have key : ∀ a σ : Fin 4,
      (gamma μ * electronNumerator m ((ℓ + faceIdE 0 a) 0) * gamma σ * X * gamma ν * Y *
        gamma σ * electronNumerator m (k + (ℓ + faceIdE 0 a) 0)).trace +
      (gamma μ * electronNumerator m ((ℓ - faceIdE 0 a) 0) * gamma σ * X * gamma ν * Y *
        gamma σ * electronNumerator m (k + (ℓ - faceIdE 0 a) 0)).trace -
      2 * (gamma μ * S₀ * gamma σ * X * gamma ν * Y * gamma σ * S₃).trace =
      2 * ((1 : Mat) * (gammaLower a * gamma μ * gammaLower a) *
        (gamma σ * X * gamma ν * Y * gamma σ)).trace := by
    intro a σ
    have hs : slash (Pi.single a (1 : ℝ)) = gammaLower a := by
      rw [faceId_slash_single]; simp
    have e1 : electronNumerator m (ℓ 0 + Pi.single a 1) = S₀ - gammaLower a := by
      rw [faceId_eN_add, hs]
    have e2 : electronNumerator m (k + (ℓ 0 + Pi.single a 1)) = S₃ - gammaLower a := by
      rw [← add_assoc, faceId_eN_add, hs]
    have e3 : electronNumerator m (ℓ 0 - Pi.single a 1) = S₀ + gammaLower a := by
      rw [faceId_eN_sub, hs]
    have e4 : electronNumerator m (k + (ℓ 0 - Pi.single a 1)) = S₃ + gammaLower a := by
      rw [← add_sub_assoc, faceId_eN_sub, hs]
    rw [(faceId_add_E_zero ℓ a).1, (faceId_sub_E_zero ℓ a).1, e1, e2, e3, e4]
    have h := faceId_trace_second (gamma μ) (gamma σ * X * gamma ν * Y * gamma σ) 1 S₀ S₃
      (gammaLower a)
    have hc : (gamma μ * gammaLower a * (gamma σ * X * gamma ν * Y * gamma σ) *
        gammaLower a * 1).trace = ((1 : Mat) * (gammaLower a * gamma μ * gammaLower a) *
          (gamma σ * X * gamma ν * Y * gamma σ)).trace := by
      rw [Matrix.mul_one, Matrix.trace_mul_comm _ (gammaLower a)]
      simp only [Matrix.mul_assoc, Matrix.one_mul]
    rw [← hc]
    simp only [Matrix.mul_assoc, Matrix.mul_one] at h ⊢
    exact h
  have hF : ∀ a, vNum e mγ Λ aVB baseVB cVB m k (ℓ + faceIdE 0 a) μ ν +
      vNum e mγ Λ aVB baseVB cVB m k (ℓ - faceIdE 0 a) μ ν -
      2 * vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν = faceIdKV e mγ Λ * ∑ σ,
        ((Minkowski.metric σ σ : ℝ) : ℂ) * (2 * ((1 : Mat) *
          (gammaLower a * gamma μ * gammaLower a) *
            (gamma σ * X * gamma ν * Y * gamma σ)).trace) := by
    intro a
    rw [faceId_vNum_VB, faceId_vNum_VB, faceId_vNum_VB, (faceId_add_E_zero ℓ a).2,
      (faceId_sub_E_zero ℓ a).2]
    simp only [← key, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  simp only [faceIdLapF, hF]
  have hσ : ∀ σ : Fin 4, ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) *
      ((1 : Mat) * (gammaLower a * gamma μ * gammaLower a) *
        (gamma σ * X * gamma ν * Y * gamma σ)).trace =
      2 * ((1 : Mat) * (gamma σ * gamma μ * gamma σ) * (X * gamma ν * Y)).trace := by
    intro σ
    rw [faceId_fold_lower, Matrix.one_mul, Matrix.one_mul,
      show gamma μ * (gamma σ * X * gamma ν * Y * gamma σ) =
        (gamma μ * (gamma σ * X * gamma ν * Y)) * gamma σ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : ∑ a, ((Minkowski.metric a a : ℝ) : ℂ) * (faceIdKV e mγ Λ * ∑ σ,
      ((Minkowski.metric σ σ : ℝ) : ℂ) * (2 * ((1 : Mat) *
        (gammaLower a * gamma μ * gammaLower a) * (gamma σ * X * gamma ν * Y * gamma σ)).trace)) =
      2 * faceIdKV e mγ Λ * ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) * ∑ a,
        ((Minkowski.metric a a : ℝ) : ℂ) * ((1 : Mat) *
          (gammaLower a * gamma μ * gammaLower a) *
            (gamma σ * X * gamma ν * Y * gamma σ)).trace := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hsum]
  simp only [hσ]
  have h2 := faceId_fold_upper (1 : Mat) (X * gamma ν * Y) μ
  rw [show ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) *
      (2 * ((1 : Mat) * (gamma σ * gamma μ * gamma σ) * (X * gamma ν * Y)).trace) =
      2 * ∑ σ, ((Minkowski.metric σ σ : ℝ) : ℂ) *
        ((1 : Mat) * (gamma σ * gamma μ * gamma σ) * (X * gamma ν * Y)).trace by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by ring, h2]
  simp only [Matrix.one_mul, Matrix.mul_assoc]
  ring

end VB

/-! ### The self-energy faces of `VA` and `VC` -/

section SE

open QED.TwoLoop.Insertion (fermionCtMatrix)

variable (e mγ Λ m : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)

/-- **The self-energy contraction at the midpoint**: `γ^σ S(y/2) γ_σ = -(y̸ + 4m)`. -/
theorem faceId_contract_eN_half (y : Fin 4 → ℝ) :
    ∑ σ, gamma σ * electronNumerator m ((1 / 2 : ℝ) • y) * gammaLower σ =
      -fermionCtMatrix 1 4 m y := by
  have h1 : ∑ σ, gamma σ * ((m : ℂ) • (1 : Mat)) * gammaLower σ = (m : ℂ) • ((-4 : ℂ) • 1) := by
    rw [← contract_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Finset.smul_sum]
  have h2 := contract_slash ((1 / 2 : ℝ) • y)
  simp only [electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, h1, h2]
  simp only [fermionCtMatrix, slash_smul, smul_smul]
  push_cast
  ext i j
  simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- **The self-energy identity of `VA`**: at the loop-`1` midpoint `ℓ₁ = ℓ₀/2` the class
numerator is `faceIdKV` times the one-loop numerator with the insertion `-(ℓ̸₀ + 4m)`. -/
theorem faceId_vNum_VA_half (ℓ₀ : Fin 4 → ℝ) :
    vNum e mγ Λ aVA baseVA cVA m k ![ℓ₀, (1 / 2 : ℝ) • ℓ₀] μ ν =
      faceIdKV e mγ Λ * (gamma μ * electronNumerator m ℓ₀ * (-fermionCtMatrix 1 4 m ℓ₀) *
        electronNumerator m ℓ₀ * gamma ν * electronNumerator m (k + ℓ₀)).trace := by
  simp only [vNum, vT, fm_VA]
  rw [faceId_sum_kV]
  congr 1
  have h := faceId_fold_upper_gen (gamma μ * electronNumerator m ℓ₀)
    (electronNumerator m ((1 / 2 : ℝ) • ℓ₀))
    (electronNumerator m ℓ₀ * gamma ν * electronNumerator m (k + ℓ₀))
  rw [faceId_contract_eN_half] at h
  simp only [aVA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  simp only [Matrix.mul_assoc] at h ⊢
  exact h

/-- **The self-energy identity of `VC`**: at the loop-`1` midpoint `ℓ₁ = (k + ℓ₀)/2` the class
numerator is `faceIdKV` times the one-loop numerator with the insertion `-(y̸ + 4m)`,
`y = k + ℓ₀`. -/
theorem faceId_vNum_VC_half (ℓ₀ : Fin 4 → ℝ) :
    vNum e mγ Λ aVC baseVC cVC m k ![ℓ₀, (1 / 2 : ℝ) • (k + ℓ₀)] μ ν =
      faceIdKV e mγ Λ * (gamma μ * electronNumerator m ℓ₀ * gamma ν *
        electronNumerator m (k + ℓ₀) * (-fermionCtMatrix 1 4 m (k + ℓ₀)) *
        electronNumerator m (k + ℓ₀)).trace := by
  simp only [vNum, vT, fm_VC]
  rw [faceId_sum_kV]
  congr 1
  have h := faceId_fold_upper_gen
    (gamma μ * electronNumerator m ℓ₀ * gamma ν * electronNumerator m (k + ℓ₀))
    (electronNumerator m ((1 / 2 : ℝ) • (k + ℓ₀))) (electronNumerator m (k + ℓ₀))
  rw [faceId_contract_eN_half] at h
  simp only [aVC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  simp only [Matrix.mul_assoc] at h ⊢
  exact h

end SE

end QED.GradedProof.RPi4

end
