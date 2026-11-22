/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.CubeCont
public import QED.DimReg.IBP
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Derivatives of a complex power of a positive polynomial

On a leaf of a sector decomposition the non-monomial part of the Lee–Pomeransky integrand is
`P̃(y) ^ (-a)`, with `P̃` a polynomial that is positive on the closed unit cube and `a = d / 2`
(a holomorphic function of the line parameter). Its iterated derivatives stay in the class of
finite sums

  `c(z) · Q(y) · P̃(y) ^ (-(a(z) + j))`

with `Q` a polynomial, `c` holomorphic and `j ∈ ℕ` (`QED.DimReg.PowTerm`): the derivative in `yᵢ` of
such a term is `c (∂ᵢQ) P̃ ^ (-(a + j)) + c · (-(a + j)) · Q (∂ᵢP̃) P̃ ^ (-(a + j + 1))`. Along a
word `w` of coordinates this gives the explicit family `QED.DimReg.powFamily P a w` with
`powFamily P a (w ++ [i]) = ∂ᵢ powFamily P a w`, jointly continuous and holomorphic in the
parameter: a `QED.DimReg.CubeDerivFamily` (`QED.DimReg.cubeDerivFamily_powFamily`), the input of
the cube continuation `QED.DimReg.cubeMellinCont`.

## Main results

* `QED.DimReg.powFamily_nil`: `powFamily P a [] z y = P(y) ^ (-a(z))`.
* `QED.DimReg.hasDerivAt_powFamily`: the derivative relation.
* `QED.DimReg.cubeDerivFamily_powFamily`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology MvPolynomial

namespace QED.DimReg

variable {N : ℕ}

/-- A term `c(z) · Q(y) · P(y) ^ (-(a(z) + j))`. -/
structure PowTerm (N : ℕ) where
  /-- The coefficient, a function of the parameter. -/
  c : ℂ → ℂ
  /-- The polynomial factor. -/
  Q : MvPolynomial (Fin N) ℝ
  /-- The extra power of `P` in the denominator. -/
  j : ℕ

namespace PowTerm

variable (P : MvPolynomial (Fin N) ℝ) (a : ℂ → ℂ)

/-- The value of a term. -/
noncomputable def eval (t : PowTerm N) (z : ℂ) (y : Fin N → ℝ) : ℂ :=
  t.c z * (MvPolynomial.eval y t.Q : ℂ) * ((MvPolynomial.eval y P : ℝ) : ℂ) ^ (-(a z + t.j))

/-- The derivative of a term in `yᵢ`, as two terms. -/
noncomputable def deriv (i : Fin N) (t : PowTerm N) : List (PowTerm N) :=
  [⟨t.c, pderiv i t.Q, t.j⟩, ⟨fun z => t.c z * (-(a z + t.j)), t.Q * pderiv i P, t.j + 1⟩]

end PowTerm

variable (P : MvPolynomial (Fin N) ℝ) (a : ℂ → ℂ)

/-- The terms of `∂_w P ^ (-a)` along a word `w` of coordinates. -/
noncomputable def powTerms (w : List (Fin N)) : List (PowTerm N) :=
  w.foldl (fun ts i => ts.flatMap (PowTerm.deriv P a i)) [⟨fun _ => 1, 1, 0⟩]

/-- The iterated derivative `∂_w (P ^ (-a))`, as an explicit sum of terms. -/
noncomputable def powFamily (w : List (Fin N)) (z : ℂ) (y : Fin N → ℝ) : ℂ :=
  ((powTerms P a w).map fun t => t.eval P a z y).sum

theorem powFamily_nil (z : ℂ) (y : Fin N → ℝ) :
    powFamily P a [] z y = ((MvPolynomial.eval y P : ℝ) : ℂ) ^ (-(a z)) := by
  simp [powFamily, powTerms, PowTerm.eval]

theorem powTerms_append (w : List (Fin N)) (i : Fin N) :
    powTerms P a (w ++ [i]) = (powTerms P a w).flatMap (PowTerm.deriv P a i) := by
  simp [powTerms, List.foldl_append]

variable {P a}

theorem PowTerm.hasDerivAt_eval (t : PowTerm N) (z : ℂ) {y : Fin N → ℝ} (i : Fin N)
    (hPy : 0 < MvPolynomial.eval y P) :
    HasDerivAt (fun s => t.eval P a z (Function.update y i s))
      (((t.deriv P a i).map fun u => u.eval P a z y).sum) (y i) := by
  have hQ := (hasDerivAt_eval_update t.Q y i (y i)).ofReal_comp
  have hP := hasDerivAt_eval_update P y i (y i)
  have hs : ((MvPolynomial.eval (Function.update y i (y i)) P : ℝ) : ℂ) ∈ slitPlane := by
    rw [Function.update_eq_self]; exact ofReal_mem_slitPlane.mpr hPy
  have hpow := (Complex.hasStrictDerivAt_cpow_const (c := -(a z + t.j)) hs).hasDerivAt.comp
    (y i) (hP.ofReal_comp)
  simp only [Function.update_eq_self] at hQ
  have hP0 : ((MvPolynomial.eval y P : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hPy.ne'
  simp only [Function.comp_def, Function.update_eq_self] at hpow
  have h := (hQ.const_mul (t.c z)).mul hpow
  refine h.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · simp only [PowTerm.deriv, PowTerm.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, map_mul]
    have he : -(a z + (t.j : ℂ)) - 1 = -(a z + ((t.j + 1 : ℕ) : ℂ)) := by push_cast; ring
    rw [he]
    simp only [Function.update_eq_self]
    push_cast
    ring
  · simp [PowTerm.eval]

theorem hasDerivAt_powFamily (w : List (Fin N)) (z : ℂ) {y : Fin N → ℝ} (i : Fin N)
    (hPy : 0 < MvPolynomial.eval y P) :
    HasDerivAt (fun s => powFamily P a w z (Function.update y i s))
      (powFamily P a (w ++ [i]) z y) (y i) := by
  unfold powFamily
  rw [powTerms_append]
  induction powTerms P a w with
  | nil => simpa using hasDerivAt_const (y i) (0 : ℂ)
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append]
    exact (t.hasDerivAt_eval z i hPy).add ih

theorem differentiable_c_powTerms (ha : Differentiable ℂ a) (w : List (Fin N)) :
    ∀ t ∈ powTerms P a w, Differentiable ℂ t.c := by
  induction w using List.reverseRecOn with
  | nil => simp [powTerms, differentiable_const]
  | append_singleton w i ih =>
    intro t ht
    rw [powTerms_append, List.mem_flatMap] at ht
    obtain ⟨u, hu, ht⟩ := ht
    simp only [PowTerm.deriv, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ih u hu
    · exact (ih u hu).mul ((ha.add (differentiable_const _)).neg)

theorem continuousOn_powFamily (ha : Differentiable ℂ a)
    (hP : ∀ y ∈ closedCube N, 0 < MvPolynomial.eval y P) (w : List (Fin N)) (U : Set ℂ) :
    ContinuousOn (fun p : ℂ × (Fin N → ℝ) => powFamily P a w p.1 p.2) (U ×ˢ closedCube N) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  unfold powFamily
  have key : ∀ ts : List (PowTerm N), (∀ t ∈ ts, Differentiable ℂ t.c) →
      ContinuousAt (fun p : ℂ × (Fin N → ℝ) => (ts.map fun t => t.eval P a p.1 p.2).sum) p := by
    intro ts
    induction ts with
    | nil => intro _; simpa using continuousAt_const
    | cons t ts ih =>
      intro hc
      simp only [List.map_cons, List.sum_cons]
      refine ContinuousAt.add ?_ (ih fun u hu => hc u (List.mem_cons_of_mem t hu))
      have h1 : ContinuousAt (fun p : ℂ × (Fin N → ℝ) => t.c p.1) p :=
        (hc t List.mem_cons_self).continuous.continuousAt.comp continuous_fst.continuousAt
      have h2 : ContinuousAt (fun p : ℂ × (Fin N → ℝ) => (MvPolynomial.eval p.2 t.Q : ℂ)) p :=
        (continuous_ofReal.comp ((MvPolynomial.continuous_eval t.Q).comp
          continuous_snd)).continuousAt
      have h3 : ContinuousAt (fun p : ℂ × (Fin N → ℝ) => ((MvPolynomial.eval p.2 P : ℝ) : ℂ))
          p := (continuous_ofReal.comp ((MvPolynomial.continuous_eval P).comp
            continuous_snd)).continuousAt
      have h4 : ContinuousAt (fun p : ℂ × (Fin N → ℝ) => -(a p.1 + t.j)) p :=
        ((ha.continuous.comp continuous_fst).add continuous_const).neg.continuousAt
      exact (h1.mul h2).mul (h3.cpow h4 (ofReal_mem_slitPlane.mpr (hP p.2 hp.2)))
  exact key _ (differentiable_c_powTerms (P := P) ha w)

theorem differentiable_powFamily (ha : Differentiable ℂ a) (w : List (Fin N))
    {y : Fin N → ℝ} (hPy : 0 < MvPolynomial.eval y P) :
    Differentiable ℂ (fun z => powFamily P a w z y) := by
  unfold powFamily
  have key : ∀ ts : List (PowTerm N), (∀ t ∈ ts, Differentiable ℂ t.c) →
      Differentiable ℂ (fun z => (ts.map fun t => t.eval P a z y).sum) := by
    intro ts
    induction ts with
    | nil => intro _; simp
    | cons t ts ih =>
      intro hc
      simp only [List.map_cons, List.sum_cons]
      refine Differentiable.add ?_ (ih fun u hu => hc u (List.mem_cons_of_mem t hu))
      refine ((hc t List.mem_cons_self).mul (differentiable_const _)).mul ?_
      exact ((ha.add (differentiable_const _)).neg).const_cpow
        (Or.inl (ofReal_ne_zero.mpr hPy.ne'))
  exact key _ (differentiable_c_powTerms (P := P) ha w)

theorem continuousOn_powFamily_slice (ha : Differentiable ℂ a)
    (hP : ∀ y ∈ closedCube N, 0 < MvPolynomial.eval y P) (w : List (Fin N)) (z : ℂ) :
    ContinuousOn (powFamily P a w z) (closedCube N) :=
  (continuousOn_powFamily ha hP w univ).comp (continuous_const.prodMk continuous_id).continuousOn
    fun _ hy => ⟨mem_univ z, hy⟩

/-- **The derivative family of `P ^ (-a)`.** For `P > 0` on the closed cube and `a` entire,
`powFamily P a` is a family of derivatives on every parameter set. -/
theorem cubeDerivFamily_powFamily (ha : Differentiable ℂ a)
    (hP : ∀ y ∈ closedCube N, 0 < MvPolynomial.eval y P) (U : Set ℂ) :
    CubeDerivFamily (powFamily P a) U where
  hasDerivAt w i z _ y hy _ := hasDerivAt_powFamily w z i (hP y hy)
  continuousOn w := continuousOn_powFamily ha hP w U
  differentiableOn w y hy := (differentiable_powFamily ha w (hP y hy)).differentiableOn

end QED.DimReg
