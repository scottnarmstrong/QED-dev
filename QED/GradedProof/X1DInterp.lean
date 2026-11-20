/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitPiece
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# (X₁) piece D: tensor Lagrange interpolation of polynomials in four-vectors

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. A function `F` of `L` four-vectors of total degree at most `n`
(`QED.TwoLoop.Bridge.IsLoopPoly L n F`) is determined by its values on the grid of the nodes
`k / (n + 1)` in each of the `4L` coordinates:

`F y = ∑_κ w_κ(y) F(y_κ)`, `w_κ(y) = ∏_v ℓ_{κ v}(y_v)`

with the one-variable Lagrange basis `ℓ_k` of `QED.TwoLoop.PauliZeroLimit.lbasis`
(`IsLoopPoly.eq_grid`). The weights are continuous (`continuous_gridWt`). Also: polynomials in
four-vectors are continuous (`IsLoopPoly.continuous`).

This is the multi-variable form of the one-parameter interpolation of
`QED/TwoLoop/PauliZeroLimitCore.lean`, used for continuity in the external momenta.
-/

@[expose] public section

open Complex Polynomial Filter Topology
open QED.TwoLoop.PauliZeroLimit (node lbasis node_injOn)
open QED.TwoLoop.Bridge (IsLoopPoly)

namespace QED.GradedProof.X1D

variable {L n : ℕ}

/-- The grid points: coordinate `(s, μ)` at the node `κ (s, μ)`. -/
noncomputable def gridPt (n : ℕ) (κ : Fin L × Fin 4 → Fin (n + 1)) : Fin L → Fin 4 → ℝ :=
  fun s μ => node n (κ (s, μ))

/-- The tensor Lagrange weight `w_κ(y) = ∏_v ℓ_{κ v}(y_v)`. -/
noncomputable def gridWt (n : ℕ) (κ : Fin L × Fin 4 → Fin (n + 1)) (y : Fin L → Fin 4 → ℝ) : ℂ :=
  ∏ v, (lbasis n (κ v)).eval ((y v.1 v.2 : ℝ) : ℂ)

/-- **One-variable exactness on monomials**: `∑ₖ tₖᵃ ℓₖ(u) = uᵃ` for `a ≤ n`. -/
theorem sum_node_pow_mul_lbasis {a : ℕ} (ha : a ≤ n) (u : ℂ) :
    ∑ k : Fin (n + 1), ((node n k : ℝ) : ℂ) ^ a * (lbasis n k).eval u = u ^ a := by
  have hdeg : ((X : ℂ[X]) ^ a).degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin, degree_X_pow]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le ha)
  have h := Lagrange.eq_interpolate_of_eval_eq (s := Finset.univ)
    (v := fun k : Fin (n + 1) => ((node n k : ℝ) : ℂ))
    (r := fun k => ((node n k : ℝ) : ℂ) ^ a) (node_injOn n) hdeg (fun k _ => by simp)
  have e := congrArg (Polynomial.eval u) h
  simp only [eval_pow, eval_X, Lagrange.interpolate_apply, eval_finsetSum, eval_mul,
    eval_C] at e
  rw [e]
  rfl

/-- **Tensor interpolation of a polynomial in four-vectors** on the grid of the nodes. -/
theorem IsLoopPoly.eq_grid {F : (Fin L → Fin 4 → ℝ) → ℂ} (hF : IsLoopPoly L n F)
    (y : Fin L → Fin 4 → ℝ) :
    F y = ∑ κ : Fin L × Fin 4 → Fin (n + 1), gridWt n κ y * F (gridPt n κ) := by
  classical
  obtain ⟨Q, hQ, hFQ⟩ := hF
  simp only [hFQ, MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdv : ∀ v, d v ≤ n := fun v => by
    refine le_trans ?_ ((MvPolynomial.le_totalDegree hd).trans hQ)
    by_cases hv : v ∈ d.support
    · exact Finset.single_le_sum (f := fun x => d x) (fun _ _ => Nat.zero_le _) hv
    · rw [Finsupp.notMem_support_iff.mp hv]
      exact Nat.zero_le _
  have e : ∀ κ : Fin L × Fin 4 → Fin (n + 1), gridWt n κ y *
      (Q.coeff d * ∏ v, ((gridPt n κ v.1 v.2 : ℝ) : ℂ) ^ d v) =
      Q.coeff d * ∏ v, (((node n (κ v) : ℝ) : ℂ) ^ d v *
        (lbasis n (κ v)).eval ((y v.1 v.2 : ℝ) : ℂ)) := fun κ => by
    simp only [gridWt, gridPt, Finset.prod_mul_distrib]
    ring
  simp only [e, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun v (k : Fin (n + 1)) => ((node n k : ℝ) : ℂ) ^ d v *
    (lbasis n k).eval ((y v.1 v.2 : ℝ) : ℂ))]
  exact Finset.prod_congr rfl fun v _ => (sum_node_pow_mul_lbasis (hdv v) _).symm

/-- The tensor weights are continuous in `y`. -/
theorem continuous_gridWt (n : ℕ) (κ : Fin L × Fin 4 → Fin (n + 1)) :
    Continuous (gridWt n κ) := by
  unfold gridWt
  refine continuous_finsetProd _ fun v _ => ?_
  exact (Polynomial.continuous _).comp
    (continuous_ofReal.comp ((continuous_apply v.2).comp (continuous_apply v.1)))

/-- **Polynomials in four-vectors are continuous.** -/
theorem IsLoopPoly.continuous {F : (Fin L → Fin 4 → ℝ) → ℂ} (hF : IsLoopPoly L n F) :
    Continuous F := by
  obtain ⟨Q, -, hFQ⟩ := hF
  rw [show F = fun y => MvPolynomial.eval (fun x => ((y x.1 x.2 : ℝ) : ℂ)) Q from funext hFQ]
  exact (MvPolynomial.continuous_eval Q).comp
    (continuous_pi fun x => continuous_ofReal.comp
      ((continuous_apply x.2).comp (continuous_apply x.1)))

end QED.GradedProof.X1D

end
