/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphCross
public import QED.Algebra.ChargeConjugation
import Mathlib.Tactic.Ring

/-!
# Reversion of Dirac traces

Infrastructure for the corner class `C₋` (section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the
`S + C` link), whose numerator is the reverse of that of `C₊`. With the charge-conjugation matrix
`C = γ⁰γ²` (`QED.Dirac.chargeConj`, `C γ^μ C = -(γ^μ)ᵀ`, `C² = 1`), the reversion
`X ↦ X^R = C Xᵀ C` (`revM`)

* reverses products, `(XY)^R = Y^R X^R` (`revM_mul`), and keeps traces (`trace_revM`);
* changes the sign of the gamma matrices, `(γ^μ)^R = -γ^μ`, `(γ_μ)^R = -γ_μ`;
* acts on the planar subalgebra by `(s, a, b, c) ↦ (s, -a, -b, -c)` (`revM_toMat`, `revPl`), so
  it maps a planar Pauli family with data `(Q₀, Q₁, R)` to one with data
  `(Q₀^R, Q₁^R, -(R^R)‾)` (`planarPauli_revM`).

The second-order jets of reversed planar functions follow coordinatewise (`hasPJ_rev`,
`hasPJ_revR`).
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitSCGraph

open QED.Dirac QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitLGraphTrace.Pl

/-- The identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The reversion of matrices -/

/-- **The reversion** `X^R = C Xᵀ C`. -/
noncomputable def revM (X : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  chargeConj * Xᵀ * chargeConj

section Rev

variable (X Y : Matrix (Fin 4) (Fin 4) ℂ)

theorem revM_mul : revM (X * Y) = revM Y * revM X := by
  unfold revM
  rw [Matrix.transpose_mul]
  calc chargeConj * (Yᵀ * Xᵀ) * chargeConj
      = chargeConj * Yᵀ * 𝟙 * Xᵀ * chargeConj := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [← chargeConj_mul_self]; simp only [Matrix.mul_assoc]

theorem revM_add : revM (X + Y) = revM X + revM Y := by
  simp only [revM, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem revM_smul (c : ℂ) : revM (c • X) = c • revM X := by
  simp only [revM, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem revM_neg : revM (-X) = -revM X := by
  simp only [revM, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem revM_one : revM 𝟙 = 𝟙 := by
  simp only [revM, Matrix.transpose_one, Matrix.mul_one, chargeConj_mul_self]

theorem revM_sum (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : revM (∑ i, X i) = ∑ i, revM (X i) := by
  simp only [revM, Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul]

theorem trace_revM : trace (revM X) = trace X := by
  unfold revM
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, chargeConj_mul_self, Matrix.one_mul,
    Matrix.trace_transpose]

theorem revM_gamma (μ : Fin 4) : revM (gamma μ) = -gamma μ := by
  have h := chargeConj_mul_gamma_mul_chargeConj μ
  unfold revM
  rw [← neg_neg (gamma μ)ᵀ, ← h]
  simp only [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, chargeConj_mul_self,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, chargeConj_mul_self, Matrix.mul_one]

theorem revM_gammaLower (μ : Fin 4) : revM (gammaLower μ) = -gammaLower μ := by
  rw [gammaLower_eq_metric_smul, revM_smul, revM_gamma, smul_neg]

theorem revM_revM : revM (revM X) = X := by
  unfold revM
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hC : chargeConjᵀ = -chargeConj := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [chargeConj_apply, ccIdx, ccSign]
  rw [hC]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, chargeConj_mul_self,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, chargeConj_mul_self, Matrix.mul_one]

end Rev

/-! ### The planar subalgebra -/

/-- The reversion on the planar subalgebra: `(s, a, b, c) ↦ (s, -a, -b, -c)`. -/
def revPl (x : Pl) : Pl := ⟨x.s, -x.a, -x.b, -x.c⟩

/-- The datum `-(R^R)‾` of a reversed Pauli family: `(s, a, b, c) ↦ (-s, -a, -b, c)`. -/
def revR (x : Pl) : Pl := ⟨-x.s, -x.a, -x.b, x.c⟩

theorem revM_toMat (x : Pl) : revM (toMat x) = toMat (revPl x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [revM, toMat, revPl, chargeConj_apply, ccIdx, ccSign, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- **Reversed planar Pauli families.** -/
theorem planarPauli_revM {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R) :
    PlanarPauli (fun μ => revM (P μ)) (revPl Q₀) (revPl Q₁) (revR R) := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  have e : ∀ i : Fin 4, i = 2 ∨ i = 3 → revM (toMat R * gamma i) = toMat (revR R) * gamma i := by
    intro i hi
    have hb : revR R = -bar (revPl R) := by ext <;> simp [revR, revPl, bar]
    rw [revM_mul, revM_gamma, revM_toMat, hb, toMat_neg, Matrix.neg_mul, Matrix.neg_mul]
    rcases hi with rfl | rfl
    · rw [gamma_two_mul_toMat]
    · rw [gamma_three_mul_toMat]
  exact ⟨by simp only [h0, revM_toMat], by simp only [h1, revM_toMat],
    by simp only [h2]; exact e 2 (Or.inl rfl), by simp only [h3]; exact e 3 (Or.inr rfl)⟩

/-! ### Jets -/

/-- The reversion of a jet. -/
def pjRev (x : PJ) : PJ := ⟨revPl x.j0, revPl x.j1, revPl x.j2⟩

/-- The datum `-(R^R)‾` of a jet. -/
def pjRevR (x : PJ) : PJ := ⟨revR x.j0, revR x.j1, revR x.j2⟩

theorem hasPJ_rev {X : ℝ → Pl} {x : PJ} (h : HasPJ X x) :
    HasPJ (fun u => revPl (X u)) (pjRev x) := by
  obtain ⟨hs, ha, hb, hc⟩ := h
  exact ⟨hs, ha.neg, hb.neg, hc.neg⟩

theorem hasPJ_revR {X : ℝ → Pl} {x : PJ} (h : HasPJ X x) :
    HasPJ (fun u => revR (X u)) (pjRevR x) := by
  obtain ⟨hs, ha, hb, hc⟩ := h
  exact ⟨hs.neg, ha.neg, hb.neg, hc⟩

end QED.TwoLoop.UnitSCGraph

end
