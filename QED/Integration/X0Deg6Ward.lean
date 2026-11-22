/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.X0Deg6Merge

/-!
# The Ward form and the scalar merge at a photon counterterm

Helper level for the Phase 5 Stage 3 goal (HS₀) (decision D-58), for the classes `D` (a
`photonCt` vertex on a photon line of the two-loop vertex). The counterterm factor is
`-(i/2) δ₃ (k·k g^{μν} - k^μ k^ν)`, with `k` the momentum of the two photon lines it joins.

* **The `g` part**: `k·k D_M(k)⁻¹ = 1 + (iε - M²) D_M(k)⁻¹` (`dot_mul_propDenom_inv`) merges `k·k`
  into one photon denominator.
* **The `k k` part**: contracted through the photon numerator `g_{ρμ}` with the `γ^ρ` of the
  gauge vertex at the other end, `k^μ` gives `k̸` (`sum_gamma_metric`). Between the two fermion
  propagators at that vertex, of momenta `k₁`, `k₂` with `k₁ - k₂ = ±k`, the Ward form
  `A(k₁) (k₁ - k₂)̸ A(k₂) = (D(k₁) + iε) A(k₂) - (D(k₂) + iε) A(k₁)` with `A = M - k̸`
  (`electronNumerator_slash_electronNumerator`) cancels one denominator and lowers the numerator
  degree of the pair by two. At a vertex next to an external fermion of momentum `k₀`, the
  one-sided forms `(k₀ - k₁)̸ A(k₁) = 2M A(k₁) - (D(k₁) + iε) - A(k₀) A(k₁)`
  (`slash_sub_mul_electronNumerator`) and its mirror image lower the degree by one.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0Deg6

open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator)

theorem slash_sub_eq (k₁ k₂ : Fin 4 → ℝ) :
    Dirac.slash (k₁ - k₂) = Dirac.slash k₁ - Dirac.slash k₂ := by
  simp only [Dirac.slash, Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Complex.ofReal_sub, sub_smul]

/-- `(k₁ - k₂)̸ = A(k₂) - A(k₁)`. -/
theorem slash_sub_eq_numerator (M : ℝ) (k₁ k₂ : Fin 4 → ℝ) :
    Dirac.slash (k₁ - k₂) = electronNumerator M k₂ - electronNumerator M k₁ := by
  rw [slash_sub_eq]
  simp only [electronNumerator]
  abel

/-- **The Ward form** `A(k₁) (k₁ - k₂)̸ A(k₂) = (D(k₁) + iε) A(k₂) - (D(k₂) + iε) A(k₁)`. -/
theorem electronNumerator_slash_electronNumerator (M ε : ℝ) (k₁ k₂ : Fin 4 → ℝ) :
    electronNumerator M k₁ * Dirac.slash (k₁ - k₂) * electronNumerator M k₂ =
      (propDenom M ε k₁ + (ε : ℂ) * I) • electronNumerator M k₂ -
        (propDenom M ε k₂ + (ε : ℂ) * I) • electronNumerator M k₁ := by
  rw [slash_sub_eq_numerator M, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    electronNumerator_mul_self M ε k₂, electronNumerator_mul_self M ε k₁]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  abel

/-- **The one-sided form at the outgoing end** `(k₀ - k₁)̸ A(k₁) =
2M A(k₁) - (D(k₁) + iε) - A(k₀) A(k₁)`. -/
theorem slash_sub_mul_electronNumerator (M ε : ℝ) (k₀ k₁ : Fin 4 → ℝ) :
    Dirac.slash (k₀ - k₁) * electronNumerator M k₁ =
      (2 * (M : ℂ)) • electronNumerator M k₁ -
        (propDenom M ε k₁ + (ε : ℂ) * I) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
          electronNumerator M k₀ * electronNumerator M k₁ := by
  rw [slash_sub_eq_numerator M, Matrix.sub_mul, electronNumerator_mul_self M ε k₁]

/-- **The one-sided form at the incoming end** `A(k₁) (k₁ - k₀)̸ =
A(k₁) A(k₀) - 2M A(k₁) + (D(k₁) + iε)`. -/
theorem electronNumerator_mul_slash_sub (M ε : ℝ) (k₀ k₁ : Fin 4 → ℝ) :
    electronNumerator M k₁ * Dirac.slash (k₁ - k₀) =
      electronNumerator M k₁ * electronNumerator M k₀ -
        (2 * (M : ℂ)) • electronNumerator M k₁ +
          (propDenom M ε k₁ + (ε : ℂ) * I) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [slash_sub_eq_numerator M, Matrix.mul_sub, electronNumerator_mul_self M ε k₁]
  abel

/-- **The scalar merge** `k·k D_M(k)⁻¹ = 1 + (iε - M²) D_M(k)⁻¹`. -/
theorem dot_mul_propDenom_inv (M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    ((Minkowski.dot k k : ℝ) : ℂ) * (propDenom M ε k)⁻¹ =
      1 + ((ε : ℂ) * I - (M : ℂ) ^ 2) * (propDenom M ε k)⁻¹ := by
  have hD := propDenom_ne_zero (M := M) hε k
  have h : ((Minkowski.dot k k : ℝ) : ℂ) = propDenom M ε k + ((ε : ℂ) * I - (M : ℂ) ^ 2) := by
    simp only [propDenom]
    push_cast
    ring
  rw [h, add_mul, mul_inv_cancel₀ hD]

/-- **The Lorentz contraction** `∑_{ρ,μ} γ^ρ g_{ρμ} k^μ = k̸`. -/
theorem sum_gamma_metric (k : Fin 4 → ℝ) (a b : Fin 4) :
    ∑ ρ, ∑ μ, ((Minkowski.metric ρ μ : ℝ) : ℂ) * (k μ : ℂ) * Dirac.gamma ρ a b =
      Dirac.slash k a b := by
  simp only [Dirac.slash, Minkowski.lower, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  push_cast
  rw [Finset.sum_mul]

end QED.GradedProof.X0Deg6

end
