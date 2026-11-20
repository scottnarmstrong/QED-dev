/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2V
public import QED.TwoLoop.ClassLimitVP
public import QED.Algebra.ChargeConjugation

/-!
# A7 for the class `VP`: the numerators

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7 for the vacuum-polarization vertex class `VP` at zero photon momentum.

* `trSE_neg_swap`: charge conjugation reverses the loop trace,
  `Tr[γ^σ (M - u̸) γ^τ (M - v̸)] = Tr[γ^σ (M + v̸) γ^τ (M + u̸)]`.
* `mVP`: the change of loop momenta `ℓ ↦ (-ℓ₁, ℓ₁ - ℓ₀)` (determinant `-1`) from the class
  routing of `VP` to the Ward–Takahashi routing of the self-energy class `V` (`vData`).
* `sum_lower_vpNumer`, `sum_lower_vpNumer2`: contracting the external photon index of the
  numerator of `VP` at `p' = p` with `r` puts `r̸` between the two open-line numerators.
* `num_VP_lt`, `num_VP_three`: the contracted numerators of the four terms of `VP`
  (`QED.TwoLoop.Bridge.vpTermNumer`) are `e` times the one-slot numerators of the pieces of `V`
  with the insertion `(m - k̸) r̸ (m - k̸)` on the open line (`SEData.slotV`), at `mVP ℓ`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.ClassLimit

/-! ### Charge conjugation of the loop trace -/

theorem transpose_gamma_eq (μ : Fin 4) :
    (Dirac.gamma μ)ᵀ = -(Dirac.chargeConj * Dirac.gamma μ * Dirac.chargeConj) := by
  rw [Dirac.chargeConj_mul_gamma_mul_chargeConj, neg_neg]

theorem transpose_slash_eq (u : Fin 4 → ℝ) :
    (Dirac.slash u)ᵀ = -(Dirac.chargeConj * Dirac.slash u * Dirac.chargeConj) := by
  simp only [Dirac.slash, Matrix.transpose_sum, Matrix.transpose_smul, transpose_gamma_eq,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
    Finset.sum_neg_distrib]

theorem transpose_electronNumerator (M : ℝ) (u : Fin 4 → ℝ) :
    (electronNumerator M u)ᵀ =
      Dirac.chargeConj * electronNumerator M (-u) * Dirac.chargeConj := by
  simp only [electronNumerator, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, transpose_slash_eq, Dirac.slash_neg, sub_neg_eq_add, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Dirac.chargeConj_mul_self]

/-- **Charge conjugation reverses the loop trace.** -/
theorem trSE_neg_swap (M : ℝ) (u v : Fin 4 → ℝ) (σ τ : Fin 4) :
    trSE M u v σ τ = trSE M (-v) (-u) σ τ := by
  have hCC : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, Dirac.chargeConj * (Dirac.chargeConj * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, Dirac.chargeConj_mul_self, Matrix.one_mul]
  unfold trSE
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, transpose_gamma_eq, transpose_electronNumerator]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hCC]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Dirac.chargeConj_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-! ### The change of loop momenta -/

/-- The change of loop momenta `ℓ ↦ (-ℓ₁, ℓ₁ - ℓ₀)` from the class routing of `VP` to the
Ward–Takahashi routing of `V`. -/
def mVP : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; -1, 1]

theorem isUnit_det_mVP : IsUnit mVP.det := by simp [mVP, Matrix.det_fin_two]

theorem loopAff_mVP (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopAff mVP 0 ℓ 0 = -ℓ 1 ∧ loopAff mVP 0 ℓ 1 = ℓ 1 - ℓ 0 := by
  refine ⟨funext fun μ => ?_, funext fun μ => ?_⟩
  · simp [loopAff, mVP, Fin.sum_univ_two]
  · simp [loopAff, mVP, Fin.sum_univ_two]
    ring

/-! ### Contracting the external photon index -/

theorem sum_lower_mul_gamma (r : Fin 4 → ℝ) (A B : Matrix (Fin 4) (Fin 4) ℂ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (A * Dirac.gamma μ * B) α β =
      (A * Dirac.slash r * B) α β := by
  simp only [Dirac.slash, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem sum_lower_outerNum (Q : Params) (p k r : Fin 4 → ℝ) (α β l0 l2 : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * outerNum Q p (p - p) k μ l0 l2 α β =
      (Dirac.gamma l2 * (electronNumerator Q.m (p - k) * Dirac.slash r *
        electronNumerator Q.m (p - k)) * Dirac.gamma l0) α β := by
  have h := sum_lower_mul_gamma r (Dirac.gamma l2 * electronNumerator Q.m (p - k))
    (electronNumerator Q.m (p - k) * Dirac.gamma l0) α β
  simp only [Matrix.mul_assoc] at h ⊢
  simp only [outerNum, sub_self, add_zero, Matrix.mul_assoc]
  exact h

/-- Contracting a four-index sum of the outer factor of `VP` at `p' = p`. -/
theorem sum_lower_sum_outerNum (Q : Params) (p k r : Fin 4 → ℝ) (α β : Fin 4)
    (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
      ∑ l4 : Fin 4, outerNum Q p (p - p) k μ l0 l2 α β * w l0 l2 l3 l4 =
    ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4,
      (Dirac.gamma l2 * (electronNumerator Q.m (p - k) * Dirac.slash r *
        electronNumerator Q.m (p - k)) * Dirac.gamma l0) α β * w l0 l2 l3 l4 := by
  simp only [← sum_lower_outerNum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l0 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l2 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l3 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l4 _ => Finset.sum_congr rfl fun μ _ => ?_
  ring

/-! ### The numerators -/

theorem trSE_mVP (ℓ : Fin 2 → Fin 4 → ℝ) (σ τ : Fin 4) :
    trSE 0 (ℓ 1 - ℓ 0) (-ℓ 1 + (ℓ 1 - ℓ 0)) σ τ = loopTrace 0 (ℓ 0) (-ℓ 1) σ τ := by
  rw [trSE_neg_swap, show -(-ℓ 1 + (ℓ 1 - ℓ 0)) = ℓ 0 by abel,
    show -(ℓ 1 - ℓ 0) = ℓ 0 + -ℓ 1 by abel]
  rfl

theorem vK_eq (Q : Params) : vK Q = vpBubbleCoeff Q := rfl

theorem vpCoeff_eq (e : ℝ) : (I * e) ^ 5 * (1 / I) ^ 6 = e * ((I * e) ^ 4 * (1 / I) ^ 5) := by
  field_simp

/-- The open-line factor with the insertion `(m - k̸) r̸ (m - k̸)`. -/
noncomputable abbrev insVP (Q : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  electronNumerator Q.m (p - ℓ 0) * Dirac.slash r * electronNumerator Q.m (p - ℓ 0)

/-- **The contracted numerator of the terms `0, 1, 2` of `VP`.** -/
theorem num_VP_lt (Q : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ)
    {t : Fin 4} (ht : t ≠ 3) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * vpTermNumer Q (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ) =
      Q.e * ∑ l, cSlotV1 Q l (loopAff mVP 0 ℓ) *
        (aSlotV l * insVP Q p r (loopAff mVP 0 ℓ) * bSlotV l) α β := by
  obtain ⟨h0, h1⟩ := loopAff_mVP ℓ
  have e : ∀ μ, twoLoopNorm * vpTermNumer Q (fun _ => p) (fun _ => p) (fun _ => p - p)
      (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ = ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
        ∑ l4 : Fin 4, outerNum Q p (p - p) (-ℓ 1) μ l0 l2 α β *
          (twoLoopNorm * vpBubbleCoeff Q * (Q.e * ((I * Q.e) ^ 4 * (1 / I) ^ 5)) *
            (((Minkowski.metric l0 l3 * (Q.Λ ^ 2 - Q.mγ ^ 2) : ℝ) : ℂ) *
              ((Minkowski.metric l2 l4 * (Q.Λ ^ 2 - Q.mγ ^ 2) : ℝ) : ℂ)) *
            (loopTrace 0 (ℓ 0) (-ℓ 1) l3 l4 +
              ((Q.m ^ 2 : ℝ) : ℂ) * (Dirac.gamma l3 * Dirac.gamma l4).trace)) := by
    intro μ
    simp only [vpTermNumer, ht, ↓reduceIte, vpE0, vpE2, vpNumerator, vpNumer, vpNumer2,
      vpCoeff_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
      Finset.sum_congr rfl fun l3 _ => Finset.sum_congr rfl fun l4 _ => ?_
    ring
  simp only [e]
  rw [sum_lower_sum_outerNum]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
    Finset.sum_congr rfl fun l3 _ => Finset.sum_congr rfl fun l4 _ => ?_
  simp only [cSlotV1, gSlotV, aSlotV, bSlotV, insVP, h0, h1, trSE_mVP, vK_eq, vκ, vC]
  ring

/-- **The contracted numerator of term `3` of `VP`**, without its two denominators. -/
theorem num_VP_three (Q : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * -(vpBubbleCoeff Q *
      vpE2 Q (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ)) =
      Q.e * ∑ l, cSlotV2 Q l (loopAff mVP 0 ℓ) *
        (aSlotV l * insVP Q p r (loopAff mVP 0 ℓ) * bSlotV l) α β := by
  obtain ⟨h0, -⟩ := loopAff_mVP ℓ
  have e : ∀ μ, twoLoopNorm * -(vpBubbleCoeff Q *
      vpE2 Q (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
      ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
        ∑ l4 : Fin 4, outerNum Q p (p - p) (-ℓ 1) μ l0 l2 α β *
          (-(twoLoopNorm * vpBubbleCoeff Q * (Q.e * ((I * Q.e) ^ 4 * (1 / I) ^ 5))) *
            (((Minkowski.metric l0 l3 * (Q.Λ ^ 2 - Q.mγ ^ 2) : ℝ) : ℂ) *
              ((Minkowski.metric l2 l4 * (Q.Λ ^ 2 - Q.mγ ^ 2) : ℝ) : ℂ)) *
            (Dirac.gamma l3 * Dirac.gamma l4).trace) := by
    intro μ
    simp only [vpE2, vpNumer2, vpCoeff_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
      Finset.sum_congr rfl fun l3 _ => Finset.sum_congr rfl fun l4 _ => ?_
    ring
  simp only [e]
  rw [sum_lower_sum_outerNum]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
    Finset.sum_congr rfl fun l3 _ => Finset.sum_congr rfl fun l4 _ => ?_
  simp only [cSlotV2, gSlotV, aSlotV, bSlotV, insVP, h0, vK_eq, vκ, vC]
  ring

end QED.GradedProof.WI2

end
