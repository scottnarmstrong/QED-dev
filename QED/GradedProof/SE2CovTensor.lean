/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2SEChain
public import QED.TwoLoop.LimitCovarianceLorentz

/-!
# Spinor covariance of self-energy chains

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L2. For a spinor lift `(S, S')` of `L`
(`QED.TwoLoop.LimitCovariance.IsSpinLift`):

* `TensorCov L D' D`: the two-index photon factor `D'` transforms into `D`,
  `∑_{νρ} D'_{νρ} L^ν_b L^ρ_a = D_{ba}`; it holds for `g_{νρ}` (`tensorCov_metric`) and for
  `(Lk)_ν (Lk)_ρ` against `k_ν k_ρ` (`tensorCov_lower`), hence for the photon numerators
  (`tensorCov_pvPhotonNum`, `tensorCov_photonNum`).
* `mul_seChain_mul`: `S seChain(A, D') S' = seChain(S A S', D)` for `TensorCov L D' D`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.SE2

open QED.TwoLoop.LimitCovariance QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}

/-- The photon factor `D'` transforms into `D` under `L`. -/
def TensorCov (L : Matrix (Fin 4) (Fin 4) ℝ) (D' D : Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ b a, ∑ ν, ∑ ρ, D' ν ρ * (((L ν b : ℝ) : ℂ) * ((L ρ a : ℝ) : ℂ)) = D b a

theorem TensorCov.add {D₁' D₁ D₂' D₂ : Fin 4 → Fin 4 → ℂ} (h₁ : TensorCov L D₁' D₁)
    (h₂ : TensorCov L D₂' D₂) : TensorCov L (fun ν ρ => D₁' ν ρ + D₂' ν ρ)
      (fun ν ρ => D₁ ν ρ + D₂ ν ρ) := fun b a => by
  dsimp only
  rw [← h₁ b a, ← h₂ b a, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by rw [← Finset.sum_add_distrib]; simp only [add_mul]

theorem TensorCov.const_mul (c : ℂ) {D' D : Fin 4 → Fin 4 → ℂ} (h : TensorCov L D' D) :
    TensorCov L (fun ν ρ => c * D' ν ρ) (fun ν ρ => c * D ν ρ) := fun b a => by
  dsimp only
  rw [← h b a, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]; simp only [mul_assoc]

theorem tensorCov_metric (h : IsSpinLift L S S') :
    TensorCov L (fun ν ρ => ((Minkowski.metric ν ρ : ℝ) : ℂ))
      (fun ν ρ => ((Minkowski.metric ν ρ : ℝ) : ℂ)) := fun b a => by
  dsimp only
  have hr := h.lorentz_right b a
  have hc : ((∑ ν, ∑ ρ, L ν b * L ρ a * Minkowski.metric ν ρ : ℝ) : ℂ) =
      ((Minkowski.metric b a : ℝ) : ℂ) := by rw [hr]
  rw [← hc]
  push_cast
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensorCov_lower (h : IsSpinLift L S S') (k : Fin 4 → ℝ) :
    TensorCov L (fun ν ρ => ((Minkowski.lower (L *ᵥ k) ν : ℝ) : ℂ) *
        ((Minkowski.lower (L *ᵥ k) ρ : ℝ) : ℂ))
      (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) :=
  fun b a => by
  dsimp only
  have hb := h.lower_mulVec_contract k b
  have ha := h.lower_mulVec_contract k a
  rw [← hb, ← ha]
  push_cast
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The photon numerator of the Pauli–Villars pair, `(Λ² - m_γ²) g_{νρ}`, is invariant. -/
theorem tensorCov_pvPhotonNum (h : IsSpinLift L S S') (mγ Λ : ℝ) :
    TensorCov L (pvPhotonNum mγ Λ) (pvPhotonNum mγ Λ) := by
  have e : pvPhotonNum mγ Λ = fun ν ρ => ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) *
      ((Minkowski.metric ν ρ : ℝ) : ℂ) := by
    funext ν ρ
    simp only [pvPhotonNum]
    push_cast
    ring
  rw [e]
  exact (tensorCov_metric h).const_mul _

theorem photonNum_eq (δ₃ mγ Λ : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    photonNum δ₃ mγ Λ k ν ρ = (1 / I) * (-(I / 2)) * ((δ₃ * (Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) *
      (((Minkowski.dot k k : ℝ) : ℂ) * ((Minkowski.metric ν ρ : ℝ) : ℂ) -
        ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
  simp only [photonNum, pvPhotonNum, QED.TwoLoop.Insertion.photonCtFactor, Minkowski.lower,
    Fin.sum_univ_four, Minkowski.metric]
  fin_cases ν <;> fin_cases ρ <;> simp <;> ring

/-- The `δ₃`-inserted photon numerator `∝ k² g_{νρ} - k_ν k_ρ` transforms covariantly. -/
theorem tensorCov_photonNum (h : IsSpinLift L S S') (δ₃ mγ Λ : ℝ) (k : Fin 4 → ℝ) :
    TensorCov L (photonNum δ₃ mγ Λ (L *ᵥ k)) (photonNum δ₃ mγ Λ k) := by
  have e : ∀ k', photonNum δ₃ mγ Λ k' = fun ν ρ =>
      ((1 / I) * (-(I / 2)) * ((δ₃ * (Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((Minkowski.dot k' k' : ℝ) : ℂ)) * ((Minkowski.metric ν ρ : ℝ) : ℂ) +
      (-((1 / I) * (-(I / 2)) * ((δ₃ * (Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ))) *
        (((Minkowski.lower k' ν : ℝ) : ℂ) * ((Minkowski.lower k' ρ : ℝ) : ℂ)) := fun k' => by
    funext ν ρ
    rw [photonNum_eq]
    ring
  rw [e, e, h.dot_mulVec]
  exact ((tensorCov_metric h).const_mul _).add ((tensorCov_lower h k).const_mul _)

/-- **Covariance of the self-energy chain.** -/
theorem mul_seChain_mul (h : IsSpinLift L S S') (A : Matrix (Fin 4) (Fin 4) ℂ)
    {D' D : Fin 4 → Fin 4 → ℂ} (hD : TensorCov L D' D) :
    S * seChain A D' * S' = seChain (S * A * S') D := by
  have e1 : ∀ ν ρ, S * (Dirac.gamma ρ * A * Dirac.gamma ν) * S' = ∑ a, ∑ b,
      (((L ν b : ℝ) : ℂ) * ((L ρ a : ℝ) : ℂ)) • (Dirac.gamma a * (S * A * S') * Dirac.gamma b) := by
    intro ν ρ
    rw [h.mul_mul_mul, h.mul_mul_mul, h.mul_gamma_mul, h.mul_gamma_mul]
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Finset.sum_comm]
  unfold seChain
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, e1,
    Finset.smul_sum, smul_smul]
  rw [sum4_swap, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [← hD b a, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_smul]

/-- `S (m - (L u)̸) S' = m - u̸`, as a statement about `electronNumerator` at `L u`. -/
theorem mul_electronNumerator_mulVec (h : IsSpinLift L S S') (m : ℝ) (u : Fin 4 → ℝ) :
    S * electronNumerator m (L *ᵥ u) * S' = electronNumerator m u :=
  h.mul_electronNumerator_mul m u

end QED.GradedProof.SE2

end
