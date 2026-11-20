/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdLoop1

/-!
# (R-Π₄) step L6d3: the face value depends only on the numerator function

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The face value
`faceIdVal n S Q` of a sorted piece is built from `Q.evalC`, the quadratic contraction `cTwoG` and
the quartic contractions `cFourG`, `cFourX` of the quartic `Q`, at real points and with symmetric
matrices. Such contractions depend on `Q` only through the numerator function `Q.eval`
(polarization, as `QED.TwoLoop.PauliZeroExplicit.NumeratorCongr` for `A⁻¹`, here for any symmetric
matrix, singular ones such as `eS 1` included). Hence any representative of the numerator may be
used to compute a face value, for instance one of the explicit form of the Dirac trace.

* `faceIdC2`, `faceIdC4` (contractions with any matrix on `LoopIndex`);
* `faceId_c2_congr`, `faceId_two_mul_c4`, **`faceId_c4_congr`** (symmetric matrices);
* `faceId_cTwoG_congr`, `faceId_cFourG_congr`, `faceId_cFourX_congr`;
* `faceId_se_congr`, `faceId_vtx_congr`, `faceId_se₂_congr`, `faceId_vtx₂_congr`;
* **`faceId_faceIdVal_congr`**: `Q.eval = Q'.eval → faceIdVal n S Q = faceIdVal n S Q'`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.TwoLoop.PauliZeroExplicit (sum_mul_eq_of_quadForm)
open QED.TwoLoop.PauliZeroExplicit.NumeratorCongr (hessForm hessForm_congr ofIndex
  loopComp_ofIndex hess_add_hess_neg sum_comm4)

/-- The quadratic contraction `∑ₐ_b Hₐ_b(X) Bₐ_b` with any matrix `B`. -/
noncomputable def faceIdC2 (Q : LoopQuartic) (B : Matrix LoopIndex LoopIndex ℝ)
    (X : LoopIndex → ℂ) : ℂ :=
  ∑ a, ∑ b, Q.hess X a b * (B a b : ℂ)

/-- The quartic pairing contraction `∑ Rₐ_bcd (Bₐ_b B_cd + Bₐ_c B_bd + Bₐ_d B_bc)`. -/
noncomputable def faceIdC4 (Q : LoopQuartic) (B : Matrix LoopIndex LoopIndex ℝ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (matPair B a b c d : ℂ)

variable {Q Q' : LoopQuartic}

/-- **The quadratic contraction at a real point is determined by the numerator function**, for a
symmetric matrix. -/
theorem faceId_c2_congr (h : Q.eval = Q'.eval) {B : Matrix LoopIndex LoopIndex ℝ}
    (hB : ∀ a b, B a b = B b a) (ℓ : Fin 2 → Fin 4 → ℝ) :
    faceIdC2 Q B (loopComp ℓ) = faceIdC2 Q' B (loopComp ℓ) := by
  unfold faceIdC2
  refine sum_mul_eq_of_quadForm (fun y => ?_) hB
  have := hessForm_congr h ℓ (ofIndex y)
  simpa only [hessForm, loopComp_ofIndex] using this

/-- The pairing contraction as a quadratic contraction of the symmetrized quartic coefficients. -/
theorem faceId_two_mul_c4 (Q : LoopQuartic) (B : Matrix LoopIndex LoopIndex ℝ) :
    2 * faceIdC4 Q B = ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d * ((B a b : ℝ) : ℂ)) *
      ((B c d : ℝ) : ℂ) := by
  have h := sum_mul_matPair_add Q.quart B B
  have h4 : ∀ a b c d, matPair (B + B) a b c d = 4 * matPair B a b c d := fun a b c d => by
    simp only [matPair, Matrix.add_apply]
    ring
  simp only [h4, ofReal_mul, ofReal_ofNat] at h
  have hl : ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (4 * (matPair B a b c d : ℂ)) =
      4 * faceIdC4 Q B := by
    simp only [faceIdC4, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hl] at h
  have hr : ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d * ((B a b : ℝ) : ℂ)) *
      ((B c d : ℝ) : ℂ) = ∑ a, ∑ b, ∑ c, ∑ d, (Q.quart a b c d +
        Q.quart a c b d + Q.quart a c d b + Q.quart c a b d + Q.quart c a d b + Q.quart c d a b) *
        (((B a b : ℝ) : ℂ) * ((B c d : ℝ) : ℂ)) := by
    simp only [Finset.sum_mul, LoopQuartic.quartSym]
    rw [sum_comm4]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hr]
  unfold faceIdC4 at h ⊢
  linear_combination h

/-- **The pairing contraction is determined by the numerator function**, for a symmetric
matrix. -/
theorem faceId_c4_congr (h : Q.eval = Q'.eval) {B : Matrix LoopIndex LoopIndex ℝ}
    (hB : ∀ a b, B a b = B b a) : faceIdC4 Q B = faceIdC4 Q' B := by
  have hX : ∀ y : LoopIndex → ℝ,
      ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d * ((B a b : ℝ) : ℂ)) *
          (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) =
        ∑ c, ∑ d, (∑ a, ∑ b, Q'.quartSym a b c d * ((B a b : ℝ) : ℂ)) *
          (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) := by
    intro y
    have key : ∀ R : LoopQuartic, 2 * ∑ c, ∑ d, (∑ a, ∑ b, R.quartSym a b c d *
        ((B a b : ℝ) : ℂ)) * (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) =
        faceIdC2 R B (loopComp (ofIndex y)) + faceIdC2 R B (loopComp (-ofIndex y)) -
          2 * faceIdC2 R B (loopComp 0) := by
      intro R
      have hneg : loopComp (-ofIndex y) = -loopComp (ofIndex y) := by
        funext a
        simp [loopComp]
      have h0 : loopComp (0 : Fin 2 → Fin 4 → ℝ) = 0 := by
        funext a
        simp [loopComp]
      rw [hneg, h0]
      simp only [faceIdC2, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      have e : ∀ a b, R.hess (loopComp (ofIndex y)) a b * ((B a b : ℝ) : ℂ) +
          R.hess (-loopComp (ofIndex y)) a b * ((B a b : ℝ) : ℂ) -
          2 * (R.hess 0 a b * ((B a b : ℝ) : ℂ)) =
          ∑ c, ∑ d, 2 * (R.quartSym a b c d * ((B a b : ℝ) : ℂ) *
            (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ))) := fun a b => by
        have := hess_add_hess_neg (Q := R) (loopComp (ofIndex y)) a b
        simp only [loopComp_ofIndex] at this ⊢
        rw [← add_mul, ← mul_assoc, ← sub_mul, this, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by ring
      simp only [e]
      rw [← sum_comm4]
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hQ := key Q
    have hQ' := key Q'
    rw [faceId_c2_congr h hB, faceId_c2_congr h hB (-ofIndex y),
      faceId_c2_congr h hB 0] at hQ
    linear_combination (hQ - hQ') / 2
  have := sum_mul_eq_of_quadForm hX hB
  have e1 := faceId_two_mul_c4 Q B
  have e2 := faceId_two_mul_c4 Q' B
  linear_combination (e1 - e2 + this) / 2

/-! ### The contractions of a face bracket -/

theorem faceId_gMet_symm {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : ∀ r s, G r s = G s r)
    (a b : LoopIndex) : gMet G a b = gMet G b a := by
  simp only [gMet, hG a.1 b.1, Minkowski.metric_symm a.2 b.2]

theorem faceId_cTwoG_congr (h : Q.eval = Q'.eval) {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r s, G r s = G s r) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cTwoG Q G (loopComp ℓ) = cTwoG Q' G (loopComp ℓ) :=
  faceId_c2_congr h (faceId_gMet_symm hG) ℓ

theorem faceId_cFourG_congr (h : Q.eval = Q'.eval) {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r s, G r s = G s r) : cFourG Q G = cFourG Q' G :=
  faceId_c4_congr h (faceId_gMet_symm hG)

theorem faceId_cFourX_congr (h : Q.eval = Q'.eval) {G E : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r s, G r s = G s r) (hE : ∀ r s, E r s = E s r) : cFourX Q G E = cFourX Q' G E := by
  have hGE : ∀ r s, (G + (1 : ℝ) • E) r s = (G + (1 : ℝ) • E) s r := fun r s => by
    simp [hG r s, hE r s]
  have e := cFourG_add_smul Q G E 1
  have e' := cFourG_add_smul Q' G E 1
  rw [faceId_cFourG_congr h hGE, faceId_cFourG_congr h hG, faceId_cFourG_congr h hE] at e
  simp only [ofReal_one, one_mul, one_pow] at e e'
  linear_combination e' - e

theorem faceId_faceG_symm (ρ a b c : ℝ) (r s : Fin 2) : faceG ρ a b c r s = faceG ρ a b c s r := by
  fin_cases r <;> fin_cases s <;> rfl

theorem faceId_eS_symm (t : Fin 2) (r s : Fin 2) : eS t r s = eS t s r := by
  simp only [eS]
  by_cases h1 : r = t <;> by_cases h2 : s = t <;> simp [h1, h2]

theorem faceId_evalC_faceX_congr (h : Q.eval = Q'.eval) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) :
    Q.evalC (faceX ρ a b c β₀ b₁) = Q'.evalC (faceX ρ a b c β₀ b₁) :=
  congrFun h _

theorem faceId_cTwoG_faceX_congr (h : Q.eval = Q'.eval) {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r s, G r s = G s r) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) :
    cTwoG Q G (faceX ρ a b c β₀ b₁) = cTwoG Q' G (faceX ρ a b c β₀ b₁) :=
  faceId_cTwoG_congr h hG _

/-! ### The brackets and the face value -/

theorem faceId_se_congr (h : Q.eval = Q'.eval) (n : ℕ) : FaceBr.se n Q = FaceBr.se n Q' := by
  simp only [FaceBr.se, faceId_evalC_faceX_congr h,
    faceId_cTwoG_faceX_congr h (faceId_faceG_symm _ _ _ _),
    faceId_cFourG_congr h (faceId_faceG_symm _ _ _ _)]

theorem faceId_vtx_congr (h : Q.eval = Q'.eval) (n : ℕ) : FaceBr.vtx n Q = FaceBr.vtx n Q' := by
  simp only [FaceBr.vtx, faceId_evalC_faceX_congr h,
    faceId_cTwoG_faceX_congr h (faceId_faceG_symm _ _ _ _),
    faceId_cTwoG_faceX_congr h (faceId_eS_symm 1),
    faceId_cFourG_congr h (faceId_faceG_symm _ _ _ _),
    faceId_cFourX_congr h (faceId_faceG_symm _ _ _ _) (faceId_eS_symm 1)]

theorem faceId_se₂_congr (h : Q.eval = Q'.eval) (n : ℕ) :
    FaceBr.se₂ n Q = FaceBr.se₂ n Q' := by
  simp only [FaceBr.se₂, faceId_evalC_faceX_congr h,
    faceId_cTwoG_faceX_congr h (faceId_faceG_symm _ _ _ _)]

theorem faceId_vtx₂_congr (h : Q.eval = Q'.eval) (n : ℕ) :
    FaceBr.vtx₂ n Q = FaceBr.vtx₂ n Q' := by
  simp only [FaceBr.vtx₂, faceId_evalC_faceX_congr h,
    faceId_cTwoG_faceX_congr h (faceId_faceG_symm _ _ _ _),
    faceId_cTwoG_faceX_congr h (faceId_eS_symm 1)]

/-- **The face value depends only on the numerator function.** -/
theorem faceId_faceIdVal_congr (h : Q.eval = Q'.eval) (n : ℕ) {p q : ℕ}
    (S : FaceShape (p + 1) q) : faceIdVal n S Q = faceIdVal n S Q' := by
  simp only [faceIdVal, faceId_se_congr h, faceId_vtx_congr h, faceId_se₂_congr h,
    faceId_vtx₂_congr h]

end QED.GradedProof.RPi4

end
