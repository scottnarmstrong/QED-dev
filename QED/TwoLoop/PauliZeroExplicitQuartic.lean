/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitPiece
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The parametric integrand depends only on the numerator function

Part of the explicit form of the `q² → 0⁺` limit of obligation O2-22
(`docs/TWO-LOOP-DERIVATION.md`, section 5.4). A numerator of degree at most four in the loop
momenta enters the parametric representation through a coefficient tensor `Q : LoopQuartic`, and
coefficient tensors are not unique: only their symmetrizations are fixed by the function
`Q.eval`. This file proves that the parametric integrand nevertheless depends only on `Q.eval`
(`paramIntegrand_congr`, `paramNum_congr`), so that the numerator function determines the
integrand **pointwise** on the simplex, not only after integration.

* `sum_mul_eq_of_quadForm`: two coefficient matrices with the same quadratic form on real vectors
  have the same contraction with every symmetric matrix (polarization).
* `hessForm_congr`, `quartPart_congr`: from the even part
  `P(ℓ + δ) + P(ℓ - δ) = 2 (P(ℓ) + ∑ Hₐ_b(ℓ) δₐ δ_b + R(δ))` at `δ` and `2δ`, the quadratic form
  of `H(ℓ)` and the quartic part `R` are determined by `Q.eval`.
* `contractTwo_congr`, `contractFour_congr`: hence the two contractions of the parametric formula,
  for a symmetric `A`. For the pairing contraction the quadratic form `X ↦ ∑ₐ_b Hₐ_b(X) Gₐ_b` is
  used once more, through `∑ R Π(G) = ½ ∑ R^{sym}ₐ_bcd Gₐ_b G_cd` (`sum_mul_matPair_add`).

The canonical objects: `numQuartic F` (a quartic representing `F`, if there is one) and
`paramNumOf F α p M x`, the numerator `T₁ + T₂ V + T₃ V²` of the parametric integrand at `ε = 0`
of the numerator function `F`; `paramNumOf_eq` identifies it with `paramNum Q` for every
representing `Q`.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.PauliZeroExplicit

open QED.Integration.TwoLoop QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Polarization of quadratic forms -/

section Polarization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_quadForm_add (K : ι → ι → ℂ) (y z : ι → ℝ) :
    ∑ a, ∑ b, K a b * ((((y + z) a : ℝ) : ℂ) * (((y + z) b : ℝ) : ℂ)) =
      ∑ a, ∑ b, K a b * (((y a : ℝ) : ℂ) * ((y b : ℝ) : ℂ)) +
        ∑ a, ∑ b, K a b * (((z a : ℝ) : ℂ) * ((z b : ℝ) : ℂ)) +
        ∑ a, ∑ b, K a b * (((y a : ℝ) : ℂ) * ((z b : ℝ) : ℂ) +
          ((z a : ℝ) : ℂ) * ((y b : ℝ) : ℂ)) := by
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.add_apply, ofReal_add]
  ring

/-- A coefficient matrix whose quadratic form vanishes on real vectors is antisymmetric. -/
theorem add_swap_eq_zero_of_quadForm {K : ι → ι → ℂ}
    (h : ∀ y : ι → ℝ, ∑ a, ∑ b, K a b * (((y a : ℝ) : ℂ) * ((y b : ℝ) : ℂ)) = 0) (a b : ι) :
    K a b + K b a = 0 := by
  have h1 := sum_quadForm_add K (Pi.single a 1) (Pi.single b 1)
  rw [h, h, h, zero_add, zero_add] at h1
  have e : ∀ c d, K c d * ((((Pi.single a (1 : ℝ) : ι → ℝ) c : ℝ) : ℂ) *
      (((Pi.single b (1 : ℝ) : ι → ℝ) d : ℝ) : ℂ) +
      (((Pi.single b (1 : ℝ) : ι → ℝ) c : ℝ) : ℂ) * (((Pi.single a (1 : ℝ) : ι → ℝ) d : ℝ) : ℂ)) =
      (if c = a then (if d = b then K c d else 0) else 0) +
        (if c = b then (if d = a then K c d else 0) else 0) := fun c d => by
    simp only [Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  exact h1.symm

/-- **Polarization.** Two coefficient matrices with the same quadratic form on real vectors have
the same contraction with every symmetric real matrix. -/
theorem sum_mul_eq_of_quadForm {H H' : ι → ι → ℂ}
    (h : ∀ y : ι → ℝ, ∑ a, ∑ b, H a b * (((y a : ℝ) : ℂ) * ((y b : ℝ) : ℂ)) =
      ∑ a, ∑ b, H' a b * (((y a : ℝ) : ℂ) * ((y b : ℝ) : ℂ)))
    {G : Matrix ι ι ℝ} (hG : ∀ a b, G a b = G b a) :
    ∑ a, ∑ b, H a b * ((G a b : ℝ) : ℂ) = ∑ a, ∑ b, H' a b * ((G a b : ℝ) : ℂ) := by
  set K : ι → ι → ℂ := fun a b => H a b - H' a b with hK
  have hK0 : ∀ y : ι → ℝ, ∑ a, ∑ b, K a b * (((y a : ℝ) : ℂ) * ((y b : ℝ) : ℂ)) = 0 := by
    intro y
    simp only [hK, sub_mul, Finset.sum_sub_distrib, h y, sub_self]
  have hanti := add_swap_eq_zero_of_quadForm hK0
  have hsw : ∑ a, ∑ b, K a b * ((G a b : ℝ) : ℂ) = ∑ a, ∑ b, K b a * ((G a b : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hG]
  have h2 : 2 * ∑ a, ∑ b, K a b * ((G a b : ℝ) : ℂ) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hsw]
    simp only [← Finset.sum_add_distrib, ← add_mul, hanti, zero_mul, Finset.sum_const_zero]
  have h3 : ∑ a, ∑ b, K a b * ((G a b : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  simp only [hK, sub_mul, Finset.sum_sub_distrib] at h3
  exact sub_eq_zero.mp h3

end Polarization

/-! ### The quadratic and quartic forms of a numerator -/

namespace NumeratorCongr

open QED.Integration.TwoLoop.LoopQuartic

/-- The quadratic form `∑ₐ_b Hₐ_b(ℓ) δₐ δ_b` of the part of `P(ℓ + δ)` quadratic in `δ`. -/
noncomputable def hessForm (Q : LoopQuartic) (ℓ δ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ a, ∑ b, Q.hess (loopComp ℓ) a b * (loopComp δ a * loopComp δ b)

theorem loopComp_two_smul (δ : Fin 2 → Fin 4 → ℝ) (a : LoopIndex) :
    loopComp ((2 : ℝ) • δ) a = 2 * loopComp δ a := by
  simp [loopComp]

theorem hessForm_two_smul (Q : LoopQuartic) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ ((2 : ℝ) • δ) = 4 * hessForm Q ℓ δ := by
  simp only [hessForm, loopComp_two_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem quartPart_two_smul (Q : LoopQuartic) (δ : Fin 2 → Fin 4 → ℝ) :
    Q.quartPart (loopComp ((2 : ℝ) • δ)) = 16 * Q.quartPart (loopComp δ) := by
  simp only [quartPart, loopComp_two_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

variable {Q Q' : LoopQuartic}

theorem hessForm_add_quartPart_congr (h : Q.eval = Q'.eval) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ δ + Q.quartPart (loopComp δ) = hessForm Q' ℓ δ + Q'.quartPart (loopComp δ) := by
  have e1 := Q.eval_add_add_eval_sub ℓ δ
  have e2 := Q'.eval_add_add_eval_sub ℓ δ
  rw [h] at e1
  unfold hessForm
  linear_combination (e2 - e1) / 2

/-- **The quadratic form of `H(ℓ)` is determined by the numerator function.** -/
theorem hessForm_congr (h : Q.eval = Q'.eval) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ δ = hessForm Q' ℓ δ := by
  have e1 := hessForm_add_quartPart_congr h ℓ δ
  have e2 := hessForm_add_quartPart_congr h ℓ ((2 : ℝ) • δ)
  rw [hessForm_two_smul, hessForm_two_smul, quartPart_two_smul, quartPart_two_smul] at e2
  linear_combination (16 * e1 - e2) / 12

/-- **The quartic part is determined by the numerator function.** -/
theorem quartPart_congr (h : Q.eval = Q'.eval) (δ : Fin 2 → Fin 4 → ℝ) :
    Q.quartPart (loopComp δ) = Q'.quartPart (loopComp δ) := by
  have e1 := hessForm_add_quartPart_congr h 0 δ
  rw [hessForm_congr h 0 δ] at e1
  linear_combination e1

/-! ### The contractions -/

/-- `loopMetricInv A` is symmetric for symmetric `A`. -/
theorem loopMetricInv_symm {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A) (a b : LoopIndex) :
    loopMetricInv A a b = loopMetricInv A b a := by
  have hinv : (A⁻¹)ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hA]
  have h1 : A⁻¹ a.1 b.1 = A⁻¹ b.1 a.1 := by
    rw [← Matrix.transpose_apply (A⁻¹) b.1 a.1, hinv]
  have h2 : Minkowski.metric a.2 b.2 = Minkowski.metric b.2 a.2 := by
    simp only [Minkowski.metric]
    split_ifs <;> simp_all
  simp only [loopMetricInv, h1, h2]

/-- The real vector `y` as loop momenta. -/
def ofIndex (y : LoopIndex → ℝ) : Fin 2 → Fin 4 → ℝ := fun s μ => y (s, μ)

theorem loopComp_ofIndex (y : LoopIndex → ℝ) (a : LoopIndex) :
    loopComp (ofIndex y) a = ((y a : ℝ) : ℂ) := rfl

/-- **The contraction `∑ₐ_b Hₐ_b(X) Gₐ_b` at real `X` is determined by the numerator
function**, for symmetric `A`. -/
theorem contractTwo_congr (h : Q.eval = Q'.eval) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Q.contractTwo A (loopComp ℓ) = Q'.contractTwo A (loopComp ℓ) := by
  unfold contractTwo
  refine sum_mul_eq_of_quadForm (fun y => ?_) (loopMetricInv_symm hA)
  have := hessForm_congr h ℓ (ofIndex y)
  simpa only [hessForm, loopComp_ofIndex] using this

/-- The even part of the Hessian coefficients in `X`. -/
theorem hess_add_hess_neg (X : LoopIndex → ℂ) (a b : LoopIndex) :
    Q.hess X a b + Q.hess (-X) a b - 2 * Q.hess 0 a b =
      2 * ∑ c, ∑ d, Q.quartSym a b c d * (X c * X d) := by
  simp only [hess, Pi.neg_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib]
  ring

/-- Moving two outer summations inside two inner ones. -/
theorem sum_comm4 {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℂ) :
    ∑ c, ∑ d, ∑ a, ∑ b, F a b c d = ∑ a, ∑ b, ∑ c, ∑ d, F a b c d := by
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]

/-- The pairing sum as a quadratic contraction of the symmetrized quartic coefficients. -/
theorem two_mul_contractFour (A : Matrix (Fin 2) (Fin 2) ℝ) :
    2 * Q.contractFour A = ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d *
      ((loopMetricInv A a b : ℝ) : ℂ)) * ((loopMetricInv A c d : ℝ) : ℂ) := by
  have h := sum_mul_matPair_add Q.quart (loopMetricInv A) (loopMetricInv A)
  have h4 : ∀ a b c d, matPair (loopMetricInv A + loopMetricInv A) a b c d =
      4 * matPair (loopMetricInv A) a b c d := fun a b c d => by
    simp only [matPair, Matrix.add_apply]
    ring
  simp only [h4, ofReal_mul, ofReal_ofNat] at h
  have hl : ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d *
      (4 * (matPair (loopMetricInv A) a b c d : ℂ)) = 4 * Q.contractFour A := by
    simp only [contractFour, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hl] at h
  have hr : ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ)) *
      ((loopMetricInv A c d : ℝ) : ℂ) = ∑ a, ∑ b, ∑ c, ∑ d, (Q.quart a b c d +
        Q.quart a c b d + Q.quart a c d b + Q.quart c a b d + Q.quart c a d b + Q.quart c d a b) *
        (((loopMetricInv A a b : ℝ) : ℂ) * ((loopMetricInv A c d : ℝ) : ℂ)) := by
    simp only [Finset.sum_mul, quartSym]
    rw [sum_comm4]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hr]
  unfold contractFour at h ⊢
  linear_combination h

/-- **The pairing contraction is determined by the numerator function**, for symmetric `A`. -/
theorem contractFour_congr (h : Q.eval = Q'.eval) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : Aᵀ = A) : Q.contractFour A = Q'.contractFour A := by
  -- the quadratic form `X ↦ ∑ₐ_b Hₐ_b(X) Gₐ_b` agrees at real `X`
  have hX : ∀ y : LoopIndex → ℝ,
      ∑ c, ∑ d, (∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ)) *
          (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) =
        ∑ c, ∑ d, (∑ a, ∑ b, Q'.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ)) *
          (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) := by
    intro y
    have key : ∀ R : LoopQuartic, 2 * ∑ c, ∑ d, (∑ a, ∑ b, R.quartSym a b c d *
        ((loopMetricInv A a b : ℝ) : ℂ)) * (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) =
        R.contractTwo A (loopComp (ofIndex y)) + R.contractTwo A (loopComp (-ofIndex y)) -
          2 * R.contractTwo A (loopComp 0) := by
      intro R
      have hneg : loopComp (-ofIndex y) = -loopComp (ofIndex y) := by
        funext a
        simp [loopComp]
      have h0 : loopComp (0 : Fin 2 → Fin 4 → ℝ) = 0 := by
        funext a
        simp [loopComp]
      rw [hneg, h0]
      simp only [contractTwo, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      have e : ∀ a b, R.hess (loopComp (ofIndex y)) a b * ((loopMetricInv A a b : ℝ) : ℂ) +
          R.hess (-loopComp (ofIndex y)) a b * ((loopMetricInv A a b : ℝ) : ℂ) -
          2 * (R.hess 0 a b * ((loopMetricInv A a b : ℝ) : ℂ)) =
          ∑ c, ∑ d, 2 * (R.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ) *
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
    rw [contractTwo_congr h hA, contractTwo_congr h hA (-ofIndex y),
      contractTwo_congr h hA 0] at hQ
    linear_combination (hQ - hQ') / 2
  have := sum_mul_eq_of_quadForm hX (loopMetricInv_symm hA)
  have e1 := two_mul_contractFour (Q := Q) A
  have e2 := two_mul_contractFour (Q := Q') A
  linear_combination (e1 - e2 + this) / 2

end NumeratorCongr

/-! ### The parametric integrand -/

section Param

variable {m : ℕ} {Q Q' : LoopQuartic} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- **The parametric integrand depends only on the numerator function.** -/
theorem paramIntegrand_congr (h : Q.eval = Q'.eval) (ε : ℝ) (x : Fin m → ℝ) :
    ClassLimit.paramIntegrand Q α p M ε x = ClassLimit.paramIntegrand Q' α p M ε x := by
  simp only [ClassLimit.paramIntegrand, h,
    NumeratorCongr.contractTwo_congr h (symanzikMatrix_transpose α _),
    NumeratorCongr.contractFour_congr h (symanzikMatrix_transpose α _)]

/-- **The parametric numerator depends only on the numerator function.** -/
theorem paramNum_congr (h : Q.eval = Q'.eval) (x : Fin m → ℝ) :
    paramNum Q α p M x = paramNum Q' α p M x := by
  simp only [paramNum, ClassLimit.coeffOne, ClassLimit.coeffTwo, ClassLimit.coeffThree, h,
    NumeratorCongr.contractTwo_congr h (symanzikMatrix_transpose α _),
    NumeratorCongr.contractFour_congr h (symanzikMatrix_transpose α _)]

/-- `paramNum` is linear in the coefficients. -/
theorem paramNum_qsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (R : ι → LoopQuartic)
    (x : Fin m → ℝ) :
    paramNum (qsum s c R) α p M x = ∑ k ∈ s, c k * paramNum (R k) α p M x := by
  simp only [paramNum, ClassLimit.coeffOne, ClassLimit.coeffTwo, ClassLimit.coeffThree,
    LoopQuartic.eval, evalC_qsum, contractTwo_qsum, contractFour_qsum, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end Param

/-! ### The canonical numerator -/

open Classical in
/-- A quartic representing the numerator function `F`, if there is one (else `0`). -/
noncomputable def numQuartic (F : (Fin 2 → Fin 4 → ℝ) → ℂ) : LoopQuartic :=
  if h : ∃ Q : LoopQuartic, Q.eval = F then h.choose else ⟨0, 0, 0, 0, 0⟩

theorem eval_numQuartic {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : ∃ Q : LoopQuartic, Q.eval = F) :
    (numQuartic F).eval = F := by
  unfold numQuartic
  split_ifs
  exact h.choose_spec

/-- **The parametric numerator of a numerator function** `F`: the numerator `T₁ + T₂ V + T₃ V²`
of the parametric integrand at `ε = 0`, with `T₁ = (m-4)! U⁻² F(-S)`,
`T₂ = (m-5)!/2 U⁻² ∑ Hₐ_b(-S) Gₐ_b` and `T₃ = (m-6)!/4 U⁻² ∑ Rₐ_bcd Πₐ_bcd(G)` computed from any
quartic representing `F` (`paramNumOf_eq`). -/
noncomputable def paramNumOf {m : ℕ} (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ) : ℂ :=
  paramNum (numQuartic F) α p M x

theorem paramNumOf_eq {m : ℕ} {Q : LoopQuartic} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hQ : Q.eval = F)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (x : Fin m → ℝ) : paramNumOf F α p M x = paramNum Q α p M x :=
  paramNum_congr α p M ((eval_numQuartic ⟨Q, hQ⟩).trans hQ.symm) x

end QED.TwoLoop.PauliZeroExplicit

end
