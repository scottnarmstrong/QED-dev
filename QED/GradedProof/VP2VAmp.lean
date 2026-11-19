/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VBlock
public import QED.GradedProof.SE2ClassVAmp

/-!
# The two-loop classes `VA`, `VB`, `VC`: index sums and the integrand form

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2. Shared by the three
classes with one closed electron loop through the four `gauge` vertices of `gggg`:

* `sum_spinor_loop4`: the spinor sum around the loop is a trace;
* `sum_lor_ps4_1`, `sum_lor_ps4_2`, `sum_lor_ps4_3`: the Lorentz sum with the two external
  photon fields at vertex `0` and at vertex `1`, `2`, `3`;
* `v_term_eq`: the constant `(2π)⁻⁸ (ie)⁴ (1/i)⁵` times the photon propagator times the trace of
  the loop, at line momenta given by line data `base`, `pp`, is the term
  `K vD vH` of `QED/GradedProof/VP2VBlock.lean`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.GradedProof.SE2 (k_gggg fv4 ps4 sum_ps4)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

section Enum

variable {X M : Type*} [Fintype X] [DecidableEq X]

theorem prod_eq_of_four [CommMonoid M] {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d)
    (g : X → M) : ∏ x, g x = g a * g b * g c * g d := by
  have : (Finset.univ : Finset X) = {a, b, c, d} := by
    ext x
    simpa using hX x
  rw [this, Finset.prod_insert (by simp [hab, hac, had]), Finset.prod_insert (by simp [hbc, hbd]),
    Finset.prod_pair hcd]
  simp only [mul_assoc]

omit [DecidableEq X] in
theorem sum_eq_of_one [AddCommMonoid M] {a : X} (hX : ∀ x, x = a) (g : X → M) :
    ∑ x, g x = g a := by
  have : (Finset.univ : Finset X) = {a} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_singleton]

end Enum

/-- **The spinor sum around a closed loop through four vertices** is a trace. -/
theorem sum_spinor_loop4 {X : Type*} [Fintype X] [DecidableEq X] {x₁ x₂ x₃ x₄ : X}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄)
    (h34 : x₃ ≠ x₄) (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = x₄)
    (A₁ A₂ A₃ A₄ S₁ S₂ S₃ S₄ : Mat) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃) * S₃ (β x₃) (α x₄) * A₄ (α x₄) (β x₄) * S₄ (β x₄) (α x₁) =
      Matrix.trace (A₁ * S₁ * A₂ * S₂ * A₃ * S₃ * A₄ * S₄) := by
  have key : ∀ α β : X → Fin 4,
      A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃) * S₃ (β x₃) (α x₄) * A₄ (α x₄) (β x₄) * S₄ (β x₄) (α x₁) =
        ∑ a : Fin 4, ∑ b : Fin 4, (if α x₁ = a ∧ β x₄ = b then (1 : ℂ) else 0) *
          (1 * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
            A₃ (α x₃) (β x₃) * S₃ (β x₃) (α x₄) * A₄ (α x₄) (β x₄))) * S₄ b a := by
    intro α β
    simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [key]
  have e : ∀ (g : (X → Fin 4) → (X → Fin 4) → Fin 4 → Fin 4 → ℂ),
      ∑ α : X → Fin 4, ∑ β : X → Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, g α β a b =
        ∑ a, ∑ b, ∑ α, ∑ β, g α β a b := fun g => by
    have h1 : ∀ α, ∑ β : X → Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, g α β a b =
        ∑ a, ∑ b, ∑ β, g α β a b := fun α => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [e]
  simp only [← Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag,
    Matrix.mul_apply (M := A₁ * S₁ * A₂ * S₂ * A₃ * S₃ * A₄)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simpa using QED.TwoLoop.Insertion.sum_spinor_chain4 h12 h13 h14 h23 h24 h34 hX 1 A₁ A₂ A₃ A₄
    S₁ S₂ S₃ a b

/-! ### The Lorentz sums -/

theorem sum_lor_ps4_1 (μ ν : Fin 4) (G : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ lor : Wick.PhotonSlot k_gggg → Fin 4,
      (if lor (ps4 0) = μ ∧ lor (ps4 1) = ν then (1 : ℂ) else 0) *
        G (lor (ps4 0)) (lor (ps4 1)) (lor (ps4 2)) (lor (ps4 3)) =
      ∑ ρ, ∑ σ, G μ ν ρ σ := by
  rw [sum_ps4]
  simp only [Fintype.sum_prod_type, QED.GradedProof.SE2.ps4_eval]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_lor_ps4_2 (μ ν : Fin 4) (G : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ lor : Wick.PhotonSlot k_gggg → Fin 4,
      (if lor (ps4 0) = μ ∧ lor (ps4 2) = ν then (1 : ℂ) else 0) *
        G (lor (ps4 0)) (lor (ps4 1)) (lor (ps4 2)) (lor (ps4 3)) =
      ∑ ρ, ∑ σ, G μ ρ ν σ := by
  rw [sum_ps4]
  simp only [Fintype.sum_prod_type, QED.GradedProof.SE2.ps4_eval]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_lor_ps4_3 (μ ν : Fin 4) (G : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ lor : Wick.PhotonSlot k_gggg → Fin 4,
      (if lor (ps4 0) = μ ∧ lor (ps4 3) = ν then (1 : ℂ) else 0) *
        G (lor (ps4 0)) (lor (ps4 1)) (lor (ps4 2)) (lor (ps4 3)) =
      ∑ ρ, ∑ σ, G μ ρ σ ν := by
  rw [sum_ps4]
  simp only [Fintype.sum_prod_type, QED.GradedProof.SE2.ps4_eval]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ### The integrand form -/

/-- The constant of one term: `(2π)⁻⁸ (ie)⁴ (1/i)⁵` times the photon numerator. -/
noncomputable def kV (e mγ Λ : ℝ) (ρ σ : Fin 4) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ((I * e) ^ 4 * (1 / I) ^ 5) * pvPhotonNum mγ Λ ρ σ

/-- **One term of a class integrand** in the form `K vD vH`. -/
theorem v_term_eq (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (e mγ Λ M : ℝ) {ε : ℝ}
    (hε : ε ≠ 0) (A : Fin 4 → Mat) (ρ σ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ((I * e) ^ 4 * (1 / I) ^ 5) *
        (QED.OneLoop.photonPropagator mγ Λ ε (phm base pp ℓ) ρ σ *
          Matrix.trace (A 0 * QED.OneLoop.electronPropagator M ε (fm base pp 0 ℓ) * A 1 *
            QED.OneLoop.electronPropagator M ε (fm base pp 1 ℓ) * A 2 *
            QED.OneLoop.electronPropagator M ε (fm base pp 2 ℓ) * A 3 *
            QED.OneLoop.electronPropagator M ε (fm base pp 3 ℓ))) =
      kV e mγ Λ ρ σ * vD base pp mγ Λ ε ℓ * vH base pp A ε M ℓ := by
  rw [photonPropagator_eq_scalar _ _ hε]
  simp only [QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, kV, vD, vH, vT, Fin.prod_univ_four]
  ring

end QED.GradedProof.VP2

end
