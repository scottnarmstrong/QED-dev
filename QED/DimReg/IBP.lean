/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OrthantFTC
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Integration-by-parts and dimension-shift identities for Lee–Pomeransky integrals

Let `P` be a real polynomial in `N` variables, positive on the orthant, and write
`J(ν, d) = lpIntegral (eval · P) ν d`. For `α ∈ ℕᴺ` let `ν + α` be the shifted exponents
(`QED.DimReg.shiftExp`). Two families of linear relations hold wherever every integral in them
converges absolutely:

* **Dimension shift** (`QED.DimReg.lpIntegral_dimShift`): from
  `G ^ (-d / 2) = G · G ^ (-(d + 2) / 2)`,
  `J(ν, d) = ∑_{α} c_α(P) · J(ν + α, d + 2)`.
* **Integration by parts in `xᵢ`** (`QED.DimReg.lpIntegral_ibp`): from
  `∫ ∂ᵢ (xᵢ · x ^ (ν - 1) G ^ (-d / 2)) = 0`,
  `νᵢ · J(ν, d) = (d / 2) · ∑_{α} c_α(xᵢ ∂ᵢ P) · J(ν + α, d + 2)`.

Here `c_α(Q)` is the coefficient of `x ^ α` in `Q`, and the sums run over the supports. The
hypotheses are only the absolute convergence of the integrals that occur: the boundary terms
vanish automatically (`QED.DimReg.integral_posOrthant_eq_zero_of_hasDerivAt`).

Each relation is a finite linear combination `∑ₖ cₖ(d) · J(νₖ, d + 2 sₖ) = 0` with
coefficients polynomial in `d` (and in the seed `ν`) and in the coefficients of `P`. The forms
`QED.DimReg.lpIntegral_dimShift_rel` and `QED.DimReg.lpIntegral_ibp_rel` state them as the
vanishing of such a sum, the shape a certificate checker consumes.

## Main results

* `QED.DimReg.hasDerivAt_eval_update`: the partial derivative of a polynomial function.
* `QED.DimReg.lpIntegral_dimShift`, `QED.DimReg.lpIntegral_dimShift_rel`.
* `QED.DimReg.lpIntegral_ibp`, `QED.DimReg.lpIntegral_ibp_rel`.
-/

public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg

variable {N : ℕ}

/-- The exponents shifted by a multi-index: `(ν + α)ⱼ = νⱼ + αⱼ`. -/
@[expose] def shiftExp (ν : Fin N → ℂ) (α : Fin N →₀ ℕ) : Fin N → ℂ := fun j => ν j + (α j : ℂ)

/-- The partial derivative of a polynomial function in the coordinate `xᵢ`. -/
theorem hasDerivAt_eval_update (P : MvPolynomial (Fin N) ℝ) (x : Fin N → ℝ) (i : Fin N)
    (t : ℝ) :
    HasDerivAt (fun s => eval (Function.update x i s) P)
      (eval (Function.update x i t) (pderiv i P)) t := by
  induction P using MvPolynomial.induction_on generalizing t with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact (hp t).add (hq t)
  | mul_X p j hp =>
    have e1 : (fun s => eval (Function.update x i s) (p * X j)) =
        fun s => eval (Function.update x i s) p * Function.update x i s j := by
      funext s; simp
    have e2 : eval (Function.update x i t) (pderiv i (p * X j)) =
        eval (Function.update x i t) (pderiv i p) * Function.update x i t j +
          eval (Function.update x i t) p * (if j = i then 1 else 0) := by
      simp only [pderiv_mul, pderiv_X, Pi.single_apply, map_add, map_mul, eval_X]
      split_ifs <;> simp
    have h : HasDerivAt (fun s => Function.update x i s j) (if j = i then 1 else 0) t := by
      by_cases hj : j = i
      · subst hj; simpa using hasDerivAt_id' t
      · simpa [Function.update_of_ne hj, hj] using hasDerivAt_const t (x j)
    rw [e1, e2]
    exact (hp t).mul h

/-- Shifting exponents by `α` multiplies the integrand by `x ^ α`. -/
theorem lpIntegrand_shiftExp (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (α : Fin N →₀ ℕ) (e : ℂ)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) :
    lpIntegrand G (shiftExp ν α) e x = (∏ j, (x j : ℂ) ^ (α j)) * lpIntegrand G ν e x := by
  rw [mem_posOrthant] at hx
  have h : ∀ j, (x j : ℂ) ^ (shiftExp ν α j - 1) = (x j : ℂ) ^ (α j) * (x j : ℂ) ^ (ν j - 1) := by
    intro j
    rw [shiftExp, show ν j + (α j : ℂ) - 1 = ((α j : ℕ) : ℂ) + (ν j - 1) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr (hx j).ne'), cpow_natCast]
  simp only [lpIntegrand, h, Finset.prod_mul_distrib]
  ring

/-- `∑_α c_α(Q) · J-integrand(ν + α) = Q(x) · J-integrand(ν)` on the orthant. -/
theorem sum_coeff_mul_lpIntegrand (G : (Fin N → ℝ) → ℝ) (Q : MvPolynomial (Fin N) ℝ)
    (ν : Fin N → ℂ) (e : ℂ) {x : Fin N → ℝ} (hx : x ∈ posOrthant N) :
    ∑ α ∈ Q.support, (Q.coeff α : ℂ) * lpIntegrand G (shiftExp ν α) e x =
      (eval x Q : ℂ) * lpIntegrand G ν e x := by
  simp only [lpIntegrand_shiftExp G ν _ e hx, eval_eq', ofReal_sum, ofReal_mul, ofReal_prod,
    ofReal_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- The dimension shift, pointwise: `G ^ (-d / 2) = G · G ^ (-(d + 2) / 2)`. -/
theorem lpIntegrand_eq_mul_add_two (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (d : ℂ)
    {x : Fin N → ℝ} (hG : 0 < G x) :
    lpIntegrand G ν d x = (G x : ℂ) * lpIntegrand G ν (d + 2) x := by
  have hG0 : (G x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hG.ne'
  have h : (G x : ℂ) ^ (-((d + 2) / 2)) = (G x : ℂ) ^ (-(d / 2)) * (G x : ℂ)⁻¹ := by
    rw [show -((d + 2) / 2) = -(d / 2) + (-1) by ring, cpow_add _ _ hG0, cpow_neg_one]
  simp only [lpIntegrand, h]
  field_simp

/-- **Dimension shift.** If `P > 0` on the orthant and every `J(ν + α, d + 2)` converges, then
`J(ν, d) = ∑_{α ∈ supp P} c_α(P) · J(ν + α, d + 2)`. -/
theorem lpIntegral_dimShift {P : MvPolynomial (Fin N) ℝ}
    (hpos : ∀ x ∈ posOrthant N, 0 < eval x P) (ν : Fin N → ℂ) (d : ℂ)
    (hconv : ∀ α ∈ P.support, LPConvergent (fun x => eval x P) (shiftExp ν α) (d + 2)) :
    lpIntegral (fun x => eval x P) ν d =
      ∑ α ∈ P.support, (P.coeff α : ℂ) * lpIntegral (fun x => eval x P) (shiftExp ν α) (d + 2) := by
  unfold lpIntegral
  rw [setIntegral_congr_fun (measurableSet_posOrthant N) (fun x hx => by
    rw [lpIntegrand_eq_mul_add_two _ ν d (hpos x hx),
      ← sum_coeff_mul_lpIntegrand _ P ν (d + 2) hx])]
  rw [integral_finsetSum _ fun α hα => (hconv α hα).const_mul _]
  simp_rw [integral_const_mul]

/-- The derivative of the boundary function `xᵢ · x ^ (ν - 1) G ^ (-d / 2)` in `xᵢ`. -/
theorem hasDerivAt_lpIntegrand_update {P : MvPolynomial (Fin N) ℝ} (i : Fin N) (ν : Fin N → ℂ)
    (d : ℂ) {x : Fin N → ℝ} (hx : x ∈ posOrthant N) (hG : 0 < eval x P) :
    HasDerivAt
      (fun t => lpIntegrand (fun x => eval x P) (shiftExp ν (Finsupp.single i 1)) d
        (Function.update x i t))
      (ν i * lpIntegrand (fun x => eval x P) ν d x - d / 2 *
        ∑ α ∈ (X i * pderiv i P).support, ((X i * pderiv i P).coeff α : ℂ) *
          lpIntegrand (fun x => eval x P) (shiftExp ν α) (d + 2) x) (x i) := by
  have hx' := mem_posOrthant.mp hx
  set R : ℂ := ∏ j ∈ Finset.univ.erase i, (x j : ℂ) ^ (ν j - 1)
  set c : ℂ := -(d / 2)
  have hfun : (fun t => lpIntegrand (fun x => eval x P) (shiftExp ν (Finsupp.single i 1)) d
      (Function.update x i t)) =
      fun t : ℝ => ((t : ℂ) ^ (ν i) * R) * ((eval (Function.update x i t) P : ℝ) : ℂ) ^ c := by
    funext t
    simp only [lpIntegrand]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [shiftExp]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [shiftExp, Function.update_of_ne hji, Ne.symm hji]
  have hxi : (x i : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (hx' i)
  have hGs : ((eval x P : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hG
  have hA := (((hasDerivAt_id (x i : ℂ)).cpow_const (c := ν i) hxi).comp_ofReal).mul_const R
  have hin := (hasDerivAt_eval_update P x i (x i)).ofReal_comp
  rw [Function.update_eq_self] at hin
  have hB := (Complex.hasStrictDerivAt_cpow_const (c := c) (by simpa using hGs)).hasDerivAt.comp
    (x i) (h := fun t => ((eval (Function.update x i t) P : ℝ) : ℂ))
    (by simpa [Function.update_eq_self] using hin)
  rw [hfun]
  convert hA.mul hB using 1
  · rfl
  rw [sum_coeff_mul_lpIntegrand _ _ ν (d + 2) hx]
  have hxi0 : (x i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hx' i).ne'
  have hsplit : ∀ e : ℂ, lpIntegrand (fun x => eval x P) ν e x =
      (x i : ℂ) ^ (ν i - 1) * R * ((eval x P : ℝ) : ℂ) ^ (-(e / 2)) := by
    intro e
    simp only [lpIntegrand, R]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hpow : (x i : ℂ) ^ (ν i) = (x i : ℂ) ^ (ν i - 1) * x i := by
    have h := cpow_add (x := (x i : ℂ)) (ν i - 1) 1 hxi0
    rw [cpow_one, sub_add_cancel] at h
    exact h
  have hexp : c - 1 = -((d + 2) / 2) := by simp only [c]; ring
  simp only [hsplit, hpow, Function.comp, Function.update_eq_self, eval_mul, eval_X, id,
    ofReal_mul, hexp, c]
  ring

/-- **Integration by parts in `xᵢ`.** If `P > 0` on the orthant, `J(ν, d)` converges, and every
`J(ν + α, d + 2)` with `α ∈ supp (xᵢ ∂ᵢ P)` converges, then
`νᵢ · J(ν, d) = (d / 2) · ∑_α c_α(xᵢ ∂ᵢ P) · J(ν + α, d + 2)`. -/
theorem lpIntegral_ibp {P : MvPolynomial (Fin N) ℝ}
    (hpos : ∀ x ∈ posOrthant N, 0 < eval x P) (i : Fin N) (ν : Fin N → ℂ) (d : ℂ)
    (hconv : LPConvergent (fun x => eval x P) ν d)
    (hconvα : ∀ α ∈ (X i * pderiv i P).support,
      LPConvergent (fun x => eval x P) (shiftExp ν α) (d + 2)) :
    ν i * lpIntegral (fun x => eval x P) ν d =
      d / 2 * ∑ α ∈ (X i * pderiv i P).support, ((X i * pderiv i P).coeff α : ℂ) *
        lpIntegral (fun x => eval x P) (shiftExp ν α) (d + 2) := by
  set Q := X i * pderiv i P
  have hsum : IntegrableOn (fun x => ∑ α ∈ Q.support, (Q.coeff α : ℂ) *
      lpIntegrand (fun x => eval x P) (shiftExp ν α) (d + 2) x) (posOrthant N) :=
    integrable_finsetSum _ fun α hα => (hconvα α hα).const_mul _
  have h0 := integral_posOrthant_eq_zero_of_hasDerivAt i
    (φ := lpIntegrand (fun x => eval x P) (shiftExp ν (Finsupp.single i 1)) d)
    (fun x hx => hasDerivAt_lpIntegrand_update i ν d hx (hpos x hx))
    ((hconv.const_mul _).sub (hsum.const_mul _)) ?_
  · rw [integral_sub (hconv.const_mul _) (hsum.const_mul _), integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun α hα => (hconvα α hα).const_mul _,
      sub_eq_zero] at h0
    simp_rw [integral_const_mul] at h0
    exact h0
  · refine hconv.congr_fun (fun x hx => ?_) (measurableSet_posOrthant N)
    rw [lpIntegrand_shiftExp _ ν _ d hx]
    have hxi : (x i : ℂ) ≠ 0 := ofReal_ne_zero.mpr ((mem_posOrthant.mp hx) i).ne'
    have hprod : (∏ j, (x j : ℂ) ^ ((Finsupp.single i 1 : Fin N →₀ ℕ) j)) = x i := by
      rw [Finset.prod_eq_single i (fun j _ hj => by simp [Ne.symm hj])
        (by simp)]
      simp
    rw [hprod, Complex.real_smul, ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hxi, one_mul]

/-- The dimension shift as the vanishing of a linear combination of integrals. -/
theorem lpIntegral_dimShift_rel {P : MvPolynomial (Fin N) ℝ}
    (hpos : ∀ x ∈ posOrthant N, 0 < eval x P) (ν : Fin N → ℂ) (d : ℂ)
    (hconv : ∀ α ∈ P.support, LPConvergent (fun x => eval x P) (shiftExp ν α) (d + 2)) :
    lpIntegral (fun x => eval x P) ν d -
      ∑ α ∈ P.support, (P.coeff α : ℂ) * lpIntegral (fun x => eval x P) (shiftExp ν α) (d + 2)
      = 0 :=
  sub_eq_zero.mpr (lpIntegral_dimShift hpos ν d hconv)

/-- Integration by parts as the vanishing of a linear combination of integrals, with
coefficients `2 νᵢ` and `-d · c_α(xᵢ ∂ᵢ P)` polynomial in `d`. -/
theorem lpIntegral_ibp_rel {P : MvPolynomial (Fin N) ℝ}
    (hpos : ∀ x ∈ posOrthant N, 0 < eval x P) (i : Fin N) (ν : Fin N → ℂ) (d : ℂ)
    (hconv : LPConvergent (fun x => eval x P) ν d)
    (hconvα : ∀ α ∈ (X i * pderiv i P).support,
      LPConvergent (fun x => eval x P) (shiftExp ν α) (d + 2)) :
    2 * ν i * lpIntegral (fun x => eval x P) ν d +
      ∑ α ∈ (X i * pderiv i P).support, (-d * ((X i * pderiv i P).coeff α : ℂ)) *
        lpIntegral (fun x => eval x P) (shiftExp ν α) (d + 2) = 0 := by
  have h := lpIntegral_ibp hpos i ν d hconv hconvα
  simp only [neg_mul, mul_assoc, Finset.sum_neg_distrib, ← Finset.mul_sum] at h ⊢
  linear_combination 2 * h

end QED.DimReg
