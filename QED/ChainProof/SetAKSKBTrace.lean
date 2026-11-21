/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdDirac

/-!
# Set (a), stage B1: the class numerators as one-loop numerators with an insertion

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient: the model's two-loop
vacuum polarization is the Källén–Sabry function), stage B (the nested one-loop form of the
class densities). With `kV ρ σ = faceIdKV · η_ρσ` and the mostly-plus contractions
`γ^σ γ_σ = -4`, `γ^σ a̸ γ_σ = 2a̸`, `γ^σ a̸ b̸ γ_σ = 4 a·b`, `γ^σ a̸ b̸ c̸ γ_σ = 2 c̸ b̸ a̸`, the
photon indices of the three class numerators contract, for **every** pair of loop momenta, to a
one-loop numerator with an inner insertion:

* `ksB_contract_eN`: `γ^σ S(y) γ_σ = -(2y̸ + 4m)` (the inner self-energy numerator);
* `ksB_contract_vertex`: `γ^σ S(a) γ^ν S(b) γ_σ = 2m² γ^ν - 4m (a^ν + b^ν) + 2 b̸ γ^ν a̸`
  (the inner vertex numerator);
* `ksB_vNum_VA`, `ksB_vNum_VC`: the self-energy classes,
  `vNum_VA = faceIdKV · Tr[γ^μ S(ℓ₀) (-(2ℓ̸₁ + 4m)) S(ℓ₀) γ^ν S(k + ℓ₀)]`, and the same with the
  insertion on `k + ℓ₀` for `VC`;
* `ksB_vNum_VB`: the vertex class,
  `vNum_VB = faceIdKV · Tr[γ^μ S(ℓ₀) Γ^ν(ℓ₁ - k, ℓ₁) S(k + ℓ₀)]`.

These generalize the midpoint identities `faceId_vNum_VA_half`, `faceId_vNum_VC_half` of
`QED.GradedProof.RPi4FaceIdDirac` (`ℓ₁ = y/2`). The constants were checked numerically on the
Lean gamma matrices first (deviation `7e-15`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Dirac
open QED.TwoLoop.Insertion (fermionCtMatrix)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

variable (e mγ Λ m : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)

/-- **The inner self-energy numerator**: `γ^σ S(y) γ_σ = -(2y̸ + 4m)`. -/
theorem ksB_contract_eN (y : Fin 4 → ℝ) :
    ∑ σ, gamma σ * electronNumerator m y * gammaLower σ = -fermionCtMatrix 2 4 m y := by
  have h1 : ∑ σ, gamma σ * ((m : ℂ) • (1 : Mat)) * gammaLower σ = (m : ℂ) • ((-4 : ℂ) • 1) := by
    rw [← contract_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Finset.smul_sum]
  have h2 := contract_slash y
  simp only [electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, h1, h2]
  simp only [fermionCtMatrix]
  push_cast
  ext i j
  simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The inner vertex numerator `2m² γ^ν - 4m (a^ν + b^ν) + 2 b̸ γ^ν a̸`. -/
noncomputable def ksBVertexIns (m : ℝ) (a b : Fin 4 → ℝ) (ν : Fin 4) : Mat :=
  (2 * (m : ℂ) ^ 2) • gamma ν - ((4 * m * (a ν + b ν) : ℝ) : ℂ) • (1 : Mat) +
    (2 : ℂ) • (slash b * gamma ν * slash a)

theorem ksB_gamma_eq_slash : gamma ν = slash (Pi.single ν (Minkowski.metric ν ν)) :=
  faceId_gamma_eq_slash ν

theorem ksB_dot_single (a : Fin 4 → ℝ) :
    Minkowski.dot a (Pi.single ν (Minkowski.metric ν ν)) = a ν := by
  fin_cases ν <;> simp [Minkowski.dot, Minkowski.metric, Pi.single_apply]

theorem ksB_single_dot (a : Fin 4 → ℝ) :
    Minkowski.dot (Pi.single ν (Minkowski.metric ν ν)) a = a ν := by
  fin_cases ν <;> simp [Minkowski.dot, Minkowski.metric, Pi.single_apply]

/-- **The inner vertex numerator**: `γ^σ S(a) γ^ν S(b) γ_σ = Γ^ν(a, b)`. -/
theorem ksB_contract_vertex (a b : Fin 4 → ℝ) :
    ∑ σ, gamma σ * electronNumerator m a * gamma ν * electronNumerator m b * gammaLower σ =
      ksBVertexIns m a b ν := by
  set g : Fin 4 → ℝ := Pi.single ν (Minkowski.metric ν ν) with hg
  have hγ : gamma ν = slash g := ksB_gamma_eq_slash ν
  have e1 : ∀ σ, gamma σ * electronNumerator m a * gamma ν * electronNumerator m b *
      gammaLower σ = ((m : ℂ) ^ 2) • (gamma σ * slash g * gammaLower σ) -
        (m : ℂ) • (gamma σ * slash a * slash g * gammaLower σ) -
        (m : ℂ) • (gamma σ * slash g * slash b * gammaLower σ) +
        gamma σ * slash a * slash g * slash b * gammaLower σ := fun σ => by
    simp only [electronNumerator, hγ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
    module
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    contract_slash, contract_slash_slash, contract_slash_slash_slash]
  rw [hg, ksB_dot_single, ksB_single_dot, ← hg, ksBVertexIns, hγ]
  push_cast
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> ring

/-- **The class `VA` as a one-loop numerator with the self-energy insertion on `ℓ₀`.** -/
theorem ksB_vNum_VA (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e mγ Λ aVA baseVA cVA m k ℓ μ ν =
      faceIdKV e mγ Λ * (gamma μ * electronNumerator m (ℓ 0) * (-fermionCtMatrix 2 4 m (ℓ 1)) *
        electronNumerator m (ℓ 0) * gamma ν * electronNumerator m (k + ℓ 0)).trace := by
  simp only [vNum, vT, fm_VA]
  rw [faceId_sum_kV]
  congr 1
  have h := faceId_fold_upper_gen (gamma μ * electronNumerator m (ℓ 0))
    (electronNumerator m (ℓ 1))
    (electronNumerator m (ℓ 0) * gamma ν * electronNumerator m (k + ℓ 0))
  rw [ksB_contract_eN] at h
  simp only [aVA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  simp only [Matrix.mul_assoc] at h ⊢
  exact h

/-- **The class `VC` as a one-loop numerator with the self-energy insertion on `k + ℓ₀`.** -/
theorem ksB_vNum_VC (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e mγ Λ aVC baseVC cVC m k ℓ μ ν =
      faceIdKV e mγ Λ * (gamma μ * electronNumerator m (ℓ 0) * gamma ν *
        electronNumerator m (k + ℓ 0) * (-fermionCtMatrix 2 4 m (ℓ 1)) *
        electronNumerator m (k + ℓ 0)).trace := by
  simp only [vNum, vT, fm_VC]
  rw [faceId_sum_kV]
  congr 1
  have h := faceId_fold_upper_gen
    (gamma μ * electronNumerator m (ℓ 0) * gamma ν * electronNumerator m (k + ℓ 0))
    (electronNumerator m (ℓ 1)) (electronNumerator m (k + ℓ 0))
  rw [ksB_contract_eN] at h
  simp only [aVC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  simp only [Matrix.mul_assoc] at h ⊢
  exact h

/-- **The class `VB` as a one-loop numerator with the vertex insertion.** -/
theorem ksB_vNum_VB (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e mγ Λ aVB baseVB cVB m k ℓ μ ν =
      faceIdKV e mγ Λ * (gamma μ * electronNumerator m (ℓ 0) * ksBVertexIns m (ℓ 1 - k) (ℓ 1) ν *
        electronNumerator m (k + ℓ 0)).trace := by
  rw [faceId_vNum_VB, ← ksB_contract_vertex]
  congr 1
  have h := faceId_fold_upper_gen (gamma μ * electronNumerator m (ℓ 0))
    (electronNumerator m (ℓ 1 - k) * gamma ν * electronNumerator m (ℓ 1))
    (electronNumerator m (k + ℓ 0))
  simp only [Matrix.mul_assoc] at h ⊢
  rw [h]

end QED.ChainProof.SetAKS

end
