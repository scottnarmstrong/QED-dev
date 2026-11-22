/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitQuartic

/-!
# Set (a), stage B3: the Gaussian contraction from the numerator function

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). The contraction `contractTwo A X = ∑ₐ_b Hₐ_b(X) Gₐ_b` (`G = η ⊗ A⁻¹`) of a numerator is
computed from its values only:

* `ksN_hessForm_of_poly`: if `P(ℓ + t δ) = c₀ + c₁ t + c₂ t² + c₃ t³ + c₄ t⁴` for all real `t`,
  the quadratic form `∑ Hₐ_b(ℓ) δₐ δ_b` is `c₂`;
* **`ksN_contractTwo_eq`**: for symmetric `A`, with `g = A⁻¹` and `H(δ)` the quadratic form at
  `ℓ`, `contractTwo A ℓ = ∑_μ η_μμ (g₀₀ H(e₀μ) + g₁₁ H(e₁μ) +
  g₀₁ (H(e₀μ + e₁μ) - H(e₀μ) - H(e₁μ)))`, `eₛμ` the unit loop momenta.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.Integration.TwoLoop.LoopQuartic
open QED.TwoLoop.PauliZeroExplicit.NumeratorCongr (hessForm hessForm_two_smul quartPart_two_smul)

/-- The unit loop momentum in the component `μ` of the loop `s`. -/
noncomputable def ksNE (s : Fin 2) (μ : Fin 4) : Fin 2 → Fin 4 → ℝ :=
  Pi.single s (Pi.single μ 1)

/-- **The quadratic form of a numerator from a polynomial expansion along a line.** -/
theorem ksN_hessForm_of_poly (Q : LoopQuartic) (ℓ δ : Fin 2 → Fin 4 → ℝ) (c₀ c₁ c₂ c₃ c₄ : ℂ)
    (h : ∀ t : ℝ, Q.eval (ℓ + t • δ) =
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4) :
    hessForm Q ℓ δ = c₂ := by
  have e1 : Q.eval (ℓ + δ) + Q.eval (ℓ - δ) =
      2 * (Q.eval ℓ + hessForm Q ℓ δ + Q.quartPart (loopComp δ)) := Q.eval_add_add_eval_sub ℓ δ
  have e2 : Q.eval (ℓ + (2 : ℝ) • δ) + Q.eval (ℓ - (2 : ℝ) • δ) =
      2 * (Q.eval ℓ + hessForm Q ℓ ((2 : ℝ) • δ) + Q.quartPart (loopComp ((2 : ℝ) • δ))) :=
    Q.eval_add_add_eval_sub ℓ _
  rw [hessForm_two_smul, quartPart_two_smul] at e2
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp only [zero_smul, add_zero, one_smul] at h0 h1
  rw [neg_smul, one_smul, ← sub_eq_add_neg] at hm1
  rw [neg_smul, ← sub_eq_add_neg] at hm2
  rw [h1, hm1, h0] at e1
  rw [h2, hm2, h0] at e2
  push_cast at e1 e2
  linear_combination (e2 - 16 * e1) / 24

theorem ksN_loopComp_ksNE (s : Fin 2) (μ : Fin 4) (a : LoopIndex) :
    loopComp (ksNE s μ) a = if a = (s, μ) then 1 else 0 := by
  obtain ⟨r, ν⟩ := a
  simp only [loopComp, ksNE, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem ksN_hessForm_ksNE (Q : LoopQuartic) (ℓ : Fin 2 → Fin 4 → ℝ) (s : Fin 2) (μ : Fin 4) :
    hessForm Q ℓ (ksNE s μ) = Q.hess (loopComp ℓ) (s, μ) (s, μ) := by
  simp only [hessForm, ksN_loopComp_ksNE, mul_ite, mul_one, mul_zero]
  simp

theorem ksN_hessForm_pair (Q : LoopQuartic) (ℓ : Fin 2 → Fin 4 → ℝ) (μ : Fin 4) :
    hessForm Q ℓ (ksNE 0 μ + ksNE 1 μ) =
      Q.hess (loopComp ℓ) (0, μ) (0, μ) + Q.hess (loopComp ℓ) (0, μ) (1, μ) +
        Q.hess (loopComp ℓ) (1, μ) (0, μ) + Q.hess (loopComp ℓ) (1, μ) (1, μ) := by
  simp only [hessForm, loopComp_add, Pi.add_apply, ksN_loopComp_ksNE, mul_add,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_add_distrib]
  ring

/-- **The Gaussian contraction from the quadratic forms along the unit loop momenta.** -/
theorem ksN_contractTwo_eq (Q : LoopQuartic) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.transpose = A)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Q.contractTwo A (loopComp ℓ) = ∑ μ, (Minkowski.metric μ μ : ℂ) *
      ((A⁻¹ 0 0 : ℂ) * hessForm Q ℓ (ksNE 0 μ) + (A⁻¹ 1 1 : ℂ) * hessForm Q ℓ (ksNE 1 μ) +
        (A⁻¹ 0 1 : ℂ) * (hessForm Q ℓ (ksNE 0 μ + ksNE 1 μ) - hessForm Q ℓ (ksNE 0 μ) -
          hessForm Q ℓ (ksNE 1 μ))) := by
  have hg : A⁻¹ 1 0 = A⁻¹ 0 1 := by
    have h := congrFun (congrFun (Matrix.transpose_nonsing_inv A) 0) 1
    rw [hA] at h
    simpa using h
  simp only [ksN_hessForm_ksNE, ksN_hessForm_pair]
  simp only [contractTwo, loopMetricInv, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hz : ∀ (s r : Fin 2), ∑ ν : Fin 4, Q.hess (loopComp ℓ) (s, μ) (r, ν) *
      ((Minkowski.metric μ ν * A⁻¹ s r : ℝ) : ℂ) =
      Q.hess (loopComp ℓ) (s, μ) (r, μ) * ((Minkowski.metric μ μ * A⁻¹ s r : ℝ) : ℂ) :=
    fun s r => Finset.sum_eq_single μ (fun ν _ hν => by
      simp [Minkowski.metric, Ne.symm hν]) (by simp)
  rw [hz, hz, hz, hz, hg]
  push_cast
  ring

end QED.ChainProof.SetAKS

end
