/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.IBP
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Annihilator relations for Lee–Pomeransky integrals

Let `G > 0` on the orthant with partial derivatives `∂_b G`, and write
`J(ν, d) = ∫_{(0,∞)^N} x ^ (ν - 1) G ^ (-d / 2) dx`. A polynomial vector field `p = (p_b)_b`
and polynomials `q`, `r` with

  `Σ_b p_b ∂_b G = q G + r`

give, from `Σ_b ∫ ∂_b (x ^ (ν - 1) p_b G ^ (-d / 2)) = 0`, the linear relation
(`QED.DimReg.lpIntegral_annihilator`)

  `Σ_b Σ_{c x^α ∈ p_b} c (ν_b + α_b - 1) J(ν + α - e_b, d)
    - (d / 2) (Σ_{c x^γ ∈ q} c J(ν + γ, d) + Σ_{c x^γ ∈ r} c J(ν + γ, d + 2)) = 0`

wherever the integrals involved converge absolutely. With `r = 0` this is the relation of the
annihilator `Σ_b p_b ∂_b + (d / 2) q` of `G ^ (-d / 2)`; with `p_b = x_b`, `q = 0` it is the
integration-by-parts identity `QED.DimReg.lpIntegral_ibp`. Polynomials are given as explicit lists
of monomials `(c, α)` (`QED.DimReg.polyEval`), so that the hypotheses on a concrete family are
`ring` identities.

## Main results

* `QED.DimReg.hasDerivAt_lpIntegrand_coord`: the partial derivative of the integrand.
* `QED.DimReg.lpIntegral_annihilator`: the relation.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.DimReg

variable {N : ℕ}

/-! ### Monomial lists -/

/-- A polynomial as a list of monomials `c x ^ α`. -/
abbrev MonoList (N : ℕ) := List (ℤ × (Fin N → ℕ))

/-- The value of a monomial `x ^ α`. -/
noncomputable def monoEval (α : Fin N → ℕ) (x : Fin N → ℝ) : ℝ := ∏ k, x k ^ α k

/-- The value of a polynomial given as a monomial list. -/
noncomputable def polyEval (l : MonoList N) (x : Fin N → ℝ) : ℝ :=
  (l.map fun t => (t.1 : ℝ) * monoEval t.2 x).sum

/-- The exponents raised by `α`. -/
def natShift (ν : Fin N → ℂ) (α : Fin N → ℕ) : Fin N → ℂ := fun j => ν j + α j

/-- The exponents with `ν_b` lowered by one. -/
def lowerAt (ν : Fin N → ℂ) (b : Fin N) : Fin N → ℂ := fun j => ν j - if j = b then 1 else 0

/-! ### Pointwise identities -/

theorem lpIntegrand_split (G : (Fin N → ℝ) → ℝ) (μ : Fin N → ℂ) (e : ℂ) (b : Fin N)
    (x : Fin N → ℝ) : lpIntegrand G μ e x = (x b : ℂ) ^ (μ b - 1) *
      (∏ j ∈ Finset.univ.erase b, (x j : ℂ) ^ (μ j - 1)) * (G x : ℂ) ^ (-(e / 2)) := by
  rw [lpIntegrand, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]

theorem prod_erase_lowerAt (μ : Fin N → ℂ) (b : Fin N) (x : Fin N → ℝ) :
    ∏ j ∈ Finset.univ.erase b, (x j : ℂ) ^ (lowerAt μ b j - 1) =
      ∏ j ∈ Finset.univ.erase b, (x j : ℂ) ^ (μ j - 1) :=
  Finset.prod_congr rfl fun j hj => by simp [lowerAt, Finset.ne_of_mem_erase hj]

/-- Dividing by `x_b` lowers `ν_b` by one. -/
theorem inv_mul_lpIntegrand (G : (Fin N → ℝ) → ℝ) (μ : Fin N → ℂ) (e : ℂ) (b : Fin N)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) :
    (x b : ℂ)⁻¹ * lpIntegrand G μ e x = lpIntegrand G (lowerAt μ b) e x := by
  have hxb : (x b : ℂ) ≠ 0 := ofReal_ne_zero.mpr ((mem_posOrthant.mp hx) b).ne'
  rw [lpIntegrand_split G μ e b, lpIntegrand_split G (lowerAt μ b) e b, prod_erase_lowerAt]
  have h : (x b : ℂ) ^ (μ b - 1) = (x b : ℂ) ^ (lowerAt μ b b - 1) * x b := by
    have h := cpow_add (x := (x b : ℂ)) (lowerAt μ b b - 1) 1 hxb
    rw [cpow_one] at h
    rw [← h]
    congr 1
    simp [lowerAt]
  rw [h]
  field_simp

/-- Raising the exponents by `α` multiplies the integrand by `x ^ α`. -/
theorem lpIntegrand_natShift (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (α : Fin N → ℕ) (e : ℂ)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) :
    lpIntegrand G (natShift ν α) e x = (monoEval α x : ℂ) * lpIntegrand G ν e x := by
  rw [mem_posOrthant] at hx
  have h : ∀ j, (x j : ℂ) ^ (natShift ν α j - 1) = (x j : ℂ) ^ (α j) * (x j : ℂ) ^ (ν j - 1) := by
    intro j
    rw [natShift, show ν j + (α j : ℂ) - 1 = ((α j : ℕ) : ℂ) + (ν j - 1) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr (hx j).ne'), cpow_natCast]
  simp only [lpIntegrand, h, Finset.prod_mul_distrib, monoEval, ofReal_prod, ofReal_pow]
  ring

theorem list_sum_lpIntegrand (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (l : MonoList N) (e : ℂ)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) :
    (l.map fun t => (t.1 : ℂ) * lpIntegrand G (natShift ν t.2) e x).sum =
      (polyEval l x : ℂ) * lpIntegrand G ν e x := by
  induction l with
  | nil => simp [polyEval]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, polyEval, ofReal_add, ofReal_mul,
      ofReal_intCast, lpIntegrand_natShift G ν a.2 e hx]
    ring

/-- **The partial derivative of the integrand** in `x_b`. -/
theorem hasDerivAt_lpIntegrand_coord {G : (Fin N → ℝ) → ℝ} {G' : (Fin N → ℝ) → ℝ} (b : Fin N)
    (μ : Fin N → ℂ) (d : ℂ) {x : Fin N → ℝ} (hx : x ∈ posOrthant N) (hG : 0 < G x)
    (hd : HasDerivAt (fun t => G (Function.update x b t)) (G' x) (x b)) :
    HasDerivAt (fun t => lpIntegrand G μ d (Function.update x b t))
      ((μ b - 1) * lpIntegrand G (lowerAt μ b) d x - d / 2 * G' x * lpIntegrand G μ (d + 2) x)
      (x b) := by
  have hx' := mem_posOrthant.mp hx
  set R : ℂ := ∏ j ∈ Finset.univ.erase b, (x j : ℂ) ^ (μ j - 1)
  set c : ℂ := -(d / 2)
  have hfun : (fun t => lpIntegrand G μ d (Function.update x b t)) =
      fun t : ℝ => ((t : ℂ) ^ (μ b - 1) * R) * ((G (Function.update x b t) : ℝ) : ℂ) ^ c := by
    funext t
    rw [lpIntegrand_split G μ d b]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hxb : (x b : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (hx' b)
  have hGs : ((G x : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hG
  have hA := (((hasDerivAt_id (x b : ℂ)).cpow_const (c := μ b - 1) hxb).comp_ofReal).mul_const R
  have hin := hd.ofReal_comp
  have hB := (Complex.hasStrictDerivAt_cpow_const (c := c) (by simpa using hGs)).hasDerivAt.comp
    (x b) (h := fun t => ((G (Function.update x b t) : ℝ) : ℂ)) (by simpa using hin)
  rw [hfun]
  convert hA.mul hB using 1
  · rfl
  have hxb0 : (x b : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hx' b).ne'
  have hpow : (x b : ℂ) ^ (μ b - 1) = (x b : ℂ) ^ (μ b - 1 - 1) * x b := by
    have h := cpow_add (x := (x b : ℂ)) (μ b - 1 - 1) 1 hxb0
    rw [cpow_one, sub_add_cancel] at h
    exact h
  have hexp : c - 1 = -((d + 2) / 2) := by simp only [c]; ring
  have hlow : lowerAt μ b b - 1 = μ b - 1 - 1 := by simp [lowerAt]
  rw [lpIntegrand_split G (lowerAt μ b) d b, prod_erase_lowerAt, lpIntegrand_split G μ (d + 2) b,
    hlow]
  simp only [Function.comp, Function.update_eq_self, id, hexp, hpow, c, R]
  ring

/-! ### List sums -/

theorem hasDerivAt_list_sum {β : Type*} (l : List β) {f : β → ℝ → ℂ} {f' : β → ℂ} {t : ℝ}
    (h : ∀ a ∈ l, HasDerivAt (f a) (f' a) t) :
    HasDerivAt (fun s => (l.map fun a => f a s).sum) (l.map f').sum t := by
  induction l with
  | nil => simpa using hasDerivAt_const t (0 : ℂ)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem a hb))

theorem integrableOn_list_sum {β : Type*} (l : List β) {f : β → (Fin N → ℝ) → ℂ} {s : Set _}
    (h : ∀ a ∈ l, IntegrableOn (f a) s) : IntegrableOn (fun x => (l.map fun a => f a x).sum) s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem a hb))

theorem integral_list_sum {β : Type*} (l : List β) {f : β → (Fin N → ℝ) → ℂ} {s : Set _}
    (h : ∀ a ∈ l, IntegrableOn (f a) s) :
    ∫ x in s, (l.map fun a => f a x).sum = (l.map fun a => ∫ x in s, f a x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (h a List.mem_cons_self)
      (integrableOn_list_sum l fun b hb => h b (List.mem_cons_of_mem a hb)),
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem list_sum_map_sub {β : Type*} (l : List β) (f g : β → ℂ) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_map_mul_left {β : Type*} (l : List β) (f : β → ℂ) (c : ℂ) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ### The relation -/

variable {G : (Fin N → ℝ) → ℝ} {G' : Fin N → (Fin N → ℝ) → ℝ}

/-- The `x_b`-weighted pieces: `Σ_{c x^α ∈ l} c x ^ (ν + α - 1) G ^ (-e / 2)`. -/
noncomputable def lpSum (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (l : MonoList N) (e : ℂ)
    (x : Fin N → ℝ) : ℂ :=
  (l.map fun t => (t.1 : ℂ) * lpIntegrand G (natShift ν t.2) e x).sum

theorem integrableOn_lpSum {ν : Fin N → ℂ} {l : MonoList N} {e : ℂ}
    (h : ∀ t ∈ l, LPConvergent G (natShift ν t.2) e) :
    IntegrableOn (lpSum G ν l e) (posOrthant N) :=
  integrableOn_list_sum l fun t ht => (h t ht).const_mul _

theorem integral_lpSum {ν : Fin N → ℂ} {l : MonoList N} {e : ℂ}
    (h : ∀ t ∈ l, LPConvergent G (natShift ν t.2) e) :
    ∫ x in posOrthant N, lpSum G ν l e x =
      (l.map fun t => (t.1 : ℂ) * lpIntegral G (natShift ν t.2) e).sum := by
  unfold lpSum
  rw [integral_list_sum l fun t ht => (h t ht).const_mul _]
  simp_rw [integral_const_mul]
  rfl

/-- **Annihilator relation.** If `Σ_b p_b ∂_b G = q G + r` on the orthant, `p_b ∂_b G = e_b`, and
the integrals involved converge absolutely, then
`Σ_b Σ_{c x^α ∈ p_b} c (ν_b + α_b - 1) J(ν + α - e_b, d)
  - (d / 2) (Σ_{c x^γ ∈ q} c J(ν + γ, d) + Σ_{c x^γ ∈ r} c J(ν + γ, d + 2)) = 0`. -/
theorem lpIntegral_annihilator (hG : ∀ x ∈ posOrthant N, 0 < G x)
    (hG' : ∀ b, ∀ x ∈ posOrthant N,
      HasDerivAt (fun t => G (Function.update x b t)) (G' b x) (x b))
    (p : Fin N → MonoList N) (q r : MonoList N) (e : Fin N → MonoList N)
    (hsyz : ∀ x ∈ posOrthant N, ∑ b, polyEval (p b) x * G' b x = polyEval q x * G x + polyEval r x)
    (he : ∀ b, ∀ x ∈ posOrthant N, polyEval (p b) x * G' b x = polyEval (e b) x)
    (ν : Fin N → ℂ) (d : ℂ)
    (hp : ∀ b, ∀ t ∈ p b, LPConvergent G (lowerAt (natShift ν t.2) b) d)
    (hq : ∀ t ∈ q, LPConvergent G (natShift ν t.2) d)
    (hr : ∀ t ∈ r, LPConvergent G (natShift ν t.2) (d + 2))
    (hev : ∀ b, ∀ t ∈ e b, LPConvergent G (natShift ν t.2) (d + 2)) :
    ∑ b, ((p b).map fun t => (t.1 : ℂ) * (ν b + t.2 b - 1) *
        lpIntegral G (lowerAt (natShift ν t.2) b) d).sum -
      d / 2 * ((q.map fun t => (t.1 : ℂ) * lpIntegral G (natShift ν t.2) d).sum +
        (r.map fun t => (t.1 : ℂ) * lpIntegral G (natShift ν t.2) (d + 2)).sum) = 0 := by
  -- the lowered pieces
  let low : Fin N → (Fin N → ℝ) → ℂ := fun b x => ((p b).map fun t => (t.1 : ℂ) *
    (ν b + t.2 b - 1) * lpIntegrand G (lowerAt (natShift ν t.2) b) d x).sum
  have hlow : ∀ b, IntegrableOn (low b) (posOrthant N) := fun b =>
    integrableOn_list_sum _ fun t ht => (hp b t ht).const_mul _
  have hilow : ∀ b, ∫ x in posOrthant N, low b x = ((p b).map fun t => (t.1 : ℂ) *
      (ν b + t.2 b - 1) * lpIntegral G (lowerAt (natShift ν t.2) b) d).sum := fun b => by
    rw [integral_list_sum _ fun t ht => (hp b t ht).const_mul _]
    simp_rw [integral_const_mul]
    rfl
  -- each coordinate: `∫ (low b - (d / 2) lpSum (e b) (d + 2)) = 0`
  have hb : ∀ b, ∫ x in posOrthant N, (low b x - d / 2 * lpSum G ν (e b) (d + 2) x) = 0 := by
    intro b
    refine integral_posOrthant_eq_zero_of_hasDerivAt b (φ := lpSum G ν (p b) d) ?_
      ((hlow b).sub ((integrableOn_lpSum (hev b)).const_mul _)) ?_
    · intro x hx
      have h := hasDerivAt_list_sum (p b) (f := fun t s =>
        (t.1 : ℂ) * lpIntegrand G (natShift ν t.2) d (Function.update x b s)) fun t _ =>
        (hasDerivAt_lpIntegrand_coord b (natShift ν t.2) d hx (hG x hx) (hG' b x hx)).const_mul
          (t.1 : ℂ)
      refine h.congr_deriv ?_
      simp only [mul_sub, list_sum_map_sub]
      dsimp only [low, lpSum]
      congr 1
      · refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
        simp [natShift]; ring
      · rw [list_sum_lpIntegrand G ν _ _ hx, ← he b x hx]
        have := list_sum_lpIntegrand G ν (p b) (d + 2) hx
        rw [show ((p b).map fun t => (t.1 : ℂ) * (d / 2 * G' b x *
            lpIntegrand G (natShift ν t.2) (d + 2) x)) = (p b).map fun t => d / 2 * G' b x *
            ((t.1 : ℂ) * lpIntegrand G (natShift ν t.2) (d + 2) x) from
          List.map_congr_left fun t _ => by ring, list_sum_map_mul_left, this]
        push_cast
        ring
    · refine (integrableOn_list_sum (p b) fun t ht => (hp b t ht).const_mul (t.1 : ℂ)).congr_fun
        (fun x hx => ?_) (measurableSet_posOrthant N)
      simp only [lpSum, Complex.real_smul, ofReal_inv, ← list_sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      rw [← inv_mul_lpIntegrand G _ d b hx]
      ring
  -- the `d + 2` pieces combine by the syzygy
  have hsum : ∀ x ∈ posOrthant N, ∑ b, lpSum G ν (e b) (d + 2) x =
      lpSum G ν q d x + lpSum G ν r (d + 2) x := by
    intro x hx
    simp only [lpSum, list_sum_lpIntegrand G ν _ _ hx, ← Finset.sum_mul, ← ofReal_sum]
    rw [lpIntegrand_eq_mul_add_two G ν d (hG x hx), Finset.sum_congr rfl fun b _ =>
      (he b x hx).symm, hsyz x hx]
    push_cast
    ring
  have hE : ∑ b, ∫ x in posOrthant N, lpSum G ν (e b) (d + 2) x =
      (q.map fun t => (t.1 : ℂ) * lpIntegral G (natShift ν t.2) d).sum +
        (r.map fun t => (t.1 : ℂ) * lpIntegral G (natShift ν t.2) (d + 2)).sum := by
    rw [← integral_finsetSum _ fun b _ => integrableOn_lpSum (hev b),
      setIntegral_congr_fun (measurableSet_posOrthant N) hsum,
      integral_add (integrableOn_lpSum hq) (integrableOn_lpSum hr), integral_lpSum hq,
      integral_lpSum hr]
  have h0 : ∑ b, ∫ x in posOrthant N, (low b x - d / 2 * lpSum G ν (e b) (d + 2) x) = 0 :=
    Finset.sum_eq_zero fun b _ => hb b
  rw [Finset.sum_congr rfl fun b _ => integral_sub (hlow b)
    ((integrableOn_lpSum (hev b)).const_mul _)] at h0
  simp only [integral_const_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hE, hilow] at h0
  exact h0

end QED.DimReg
