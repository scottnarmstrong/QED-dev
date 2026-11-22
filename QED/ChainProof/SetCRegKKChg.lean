/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKCov

/-!
# Set (c): moving a term of the longitudinal integrand to another class

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
After the Ward identities (`QED.ChainProof.SetCMain.dKUnit_int`, `dKUnit_ext`) the longitudinal
integrand of a main class `repB i` is a sum of terms `kkT` on the ten-line unit with some electron
lines deleted (`QED/ChainProof/SetCMainBKKTerm.lean`). A term with a deleted line of one class is
often a term of another class in a different loop routing. Here a term of class `i` at the loop
momenta `chgD M a ℓ` is compared with a term of class `i'` at `ℓ`, line by line along the same
line map: the integer vectors of the kept lines agree up to sign, the element momentum and the
electron momenta agree. The pointwise limits `kkLimX` are then equal (unimodular change of
loop momenta in the joint energy-first integral).

* `uVec`: the integer vector of a unit line after the change; `lineMomentum_unit_chgD`,
  `kK_chgD`, `kQ_chgD`, `elemMom_chgD`;
* **`kkDen_chgD`**, **`kkSpec_chgD`**: the denominators and the spectral factor;
* **`kNum_chgD`**: a numerator term, from the electron momenta and the element momentum;
* **`kkT_chgD`**, **`kkLimX_chgD`**: a term, and the pointwise limits;
* `kPermD_symm`, `ocW_eq`: the chain `ocW` written out, for the chain rearrangements.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCLink (mvReal)
open QED.TwoLoop.Enumeration
open QED.Integration.TwoLoop (lineDenom lineMomentum pvLines)

/-! ### The lines after a change of loop momenta -/

/-- The integer vector (loop, `p`, `q = p' - p` coefficients) of line `q` of the unit of
`repB i` after the change of loop momenta `chgD M a`. -/
def uVec (i : Fin 12) (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ) (q : Fin 10) :
    Fin 4 → ℤ :=
  classVecD (repBClass i) M a (pvLines (mLine (r := 2) (repBSlot i) q))

theorem lineMomentum_unit_chgD (i : Fin 12) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (a : Fin 2 → Fin 2 → ℤ) (p p' : Fin 4 → ℝ) (q : Fin 10) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
        (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p') q (chgD M a p (p' - p) ℓ) =
      mvReal ℓ p (p' - p) (uVec i M a q) := by
  rw [lineMomentum_unitM_one _ _ one_one_eq, lineMomentum_chgD]
  rfl

theorem lineMomentum_unit_eq (i : Fin 12) (p p' : Fin 4 → ℝ) (q : Fin 10)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
        (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p') q ℓ =
      mvReal ℓ p (p' - p) (uVec i 1 0 q) := by
  conv_lhs => rw [← chgD_one_zero p (p' - p) ℓ]
  exact lineMomentum_unit_chgD i 1 0 p p' q ℓ

theorem kK_chgD (i : Fin 12) (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ)
    (p p' : Fin 4 → ℝ) (j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kK (repBClass i) (repBSlot i) p p' j (chgD M a p (p' - p) ℓ) =
      mvReal ℓ p (p' - p) (uVec i M a (eIdx j)) :=
  lineMomentum_unit_chgD i M a p p' (eIdx j) ℓ

theorem kQ_chgD (i : Fin 12) (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ)
    (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kQ (repBClass i) (repBSlot i) p p' (chgD M a p (p' - p) ℓ) =
      mvReal ℓ p (p' - p) (uVec i M a 8) :=
  lineMomentum_unit_chgD i M a p p' 8 ℓ

theorem elemMom_chgD (i : Fin 12) (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ)
    (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemMom (repBClass i) (repBSlot i) p p' (chgD M a p (p' - p) ℓ) =
      mvReal ℓ p (p' - p) (uVec i M a 8) := by
  rw [elemMom_eq_kQ]
  exact kQ_chgD i M a p p' ℓ

theorem dot_neg_neg' (k : Fin 4 → ℝ) : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by
  simp only [Minkowski.dot, Pi.neg_apply, mul_neg, neg_mul, neg_neg]

theorem dot_mvReal_of {ℓ : Fin 2 → Fin 4 → ℝ} {p q : Fin 4 → ℝ} {v w : Fin 4 → ℤ}
    (h : v = w ∨ v = -w) :
    Minkowski.dot (mvReal ℓ p q v) (mvReal ℓ p q v) = Minkowski.dot (mvReal ℓ p q w)
      (mvReal ℓ p q w) := by
  rcases h with rfl | rfl
  · rfl
  · rw [map_neg, dot_neg_neg']

/-! ### The factors of a term -/

section Factors

variable {k : ℕ} (i i' : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ)
  (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ)

/-- **The denominators of a term after the change**: equal when the kept lines have the same
integer vectors up to sign (the masses are those of the same unit lines). -/
theorem kkDen_chgD (ι : Fin (k + 1) → Fin 10)
    (h : ∀ b, uVec i M a (ι b) = uVec i' 1 0 (ι b) ∨ uVec i M a (ι b) = -uVec i' 1 0 (ι b))
    (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkDen i R p p' ι ε (chgD M a p (p' - p) ℓ) = kkDen i' R p p' ι ε ℓ := by
  unfold kkDen
  refine Finset.prod_congr rfl fun b _ => ?_
  have e : ∀ (j : Fin 12) (ℓ' : Fin 2 → Fin 4 → ℝ),
      lineDenom (fun a => unitMMatrix (repBClass j) (repBSlot j) (![1, 1] : Fin 2 → ℝ) (ι a))
        (fun a => unitMMomenta (repBClass j) (repBSlot j) ![1, 1] p p' (ι a))
        (fun a => dkMasses R (ι a)) ε b ℓ' =
      lineDenom (unitMMatrix (repBClass j) (repBSlot j) (![1, 1] : Fin 2 → ℝ))
        (unitMMomenta (repBClass j) (repBSlot j) ![1, 1] p p') (dkMasses R) ε (ι b) ℓ' :=
    fun _ _ => rfl
  rw [e, e]
  unfold lineDenom
  rw [lineMomentum_unit_chgD, lineMomentum_unit_eq, dot_mvReal_of (h b)]

/-- **The spectral factor after the change**: equal when the element momenta agree up to
sign. -/
theorem kkSpec_chgD (h : uVec i M a 8 = uVec i' 1 0 8 ∨ uVec i M a 8 = -uVec i' 1 0 8)
    (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkSpec i p p' t ε x (chgD M a p (p' - p) ℓ) = kkSpec i' p p' t ε x ℓ := by
  unfold kkSpec
  have e : elemMom (repBClass i') (repBSlot i') p p' ℓ = mvReal ℓ p (p' - p) (uVec i' 1 0 8) := by
    rw [elemMom_eq_kQ]
    exact lineMomentum_unit_eq i' p p' 8 ℓ
  rw [elemMom_chgD, e, dot_mvReal_of h]

/-- **A term after the change**: the denominators, the spectral factor and the numerator. -/
theorem kkT_chgD (ι : Fin (k + 1) → Fin 10) (F F' : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (h : ∀ b, uVec i M a (ι b) = uVec i' 1 0 (ι b) ∨ uVec i M a (ι b) = -uVec i' 1 0 (ι b))
    (h8 : uVec i M a 8 = uVec i' 1 0 8 ∨ uVec i M a 8 = -uVec i' 1 0 8)
    (hF : ∀ ℓ, F (chgD M a p (p' - p) ℓ) = F' ℓ) (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT i R p p' t ι F ε x (chgD M a p (p' - p) ℓ) = kkT i' R p p' t ι F' ε x ℓ := by
  unfold kkT
  rw [hF, kkDen_chgD i i' R p p' M a ι h, kkSpec_chgD i i' p p' t M a h8]

end Factors

/-- **The pointwise limit is invariant under a unimodular change of loop momenta.** -/
theorem kkLimX_chgD {H H' : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : IsUnit M.det) (a : Fin 2 → Fin 2 → ℤ) (p q : Fin 4 → ℝ)
    (h : ∀ ε x ℓ, H' ε x ℓ = H ε x (chgD M a p q ℓ)) (x : ℝ) :
    kkLimX H' x = kkLimX H x := by
  unfold kkLimX
  congr 1
  funext ε
  exact QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp M hM _ fun ℓ => h ε x ℓ

/-! ### Numerator terms -/

/-- **A numerator term after the change**, from the element momentum and the momenta of the
electron lines in `K`. -/
theorem kNum_chgD (π : Equiv.Perm (Fin 5)) (c c' : Class5) (σ σ' : Fin 8) (m : ℝ)
    (p p' : Fin 4 → ℝ) (X Y : KSlot) (K : Finset (Fin 4)) (μ : Fin 4)
    (L L' : Fin 2 → Fin 4 → ℝ) (hQ : kQ c σ p p' L = kQ c' σ' p p' L')
    (hK : ∀ j ∈ K, kK c σ p p' j L = kK c' σ' p p' j L') :
    kNum π c σ m p p' X Y K μ L = kNum π c' σ' m p p' X Y K μ L' := by
  have hS : ∀ Z : KSlot, kSlotM c σ m p p' Z L = kSlotM c' σ' m p p' Z L' := fun Z => by
    cases Z <;> simp only [kSlotM, hQ]
  have hE : (fun j => kEK c σ m p p' K j L) = fun j => kEK c' σ' m p p' K j L' := by
    funext j
    unfold kEK
    split_ifs with hj
    · rw [hK j hj]
    · rfl
  unfold kNum
  rw [hS X, hS Y, hE]

/-! ### The chain written out -/

theorem kPermD_symm {i : Fin 12} {t k : Fin 5} (h : kPermD i k = t) : (kPermD i).symm t = k :=
  (Equiv.symm_apply_eq _).2 h.symm

theorem ocW_eq (π : Equiv.Perm (Fin 5)) (W : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ocW π W E = W (π.symm 4) * E 3 * W (π.symm 3) * E 2 * W (π.symm 2) * E 1 *
      W (π.symm 1) * E 0 * W (π.symm 0) :=
  rfl

end QED.ChainProof.SetCRegDisp

end
