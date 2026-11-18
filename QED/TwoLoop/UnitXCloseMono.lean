/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity

/-!
# Real monomials and Newton-polytope lower bounds

Helper lemmas for the domination of the crossed-ladder integrand
(`QED/TwoLoop/UnitXCloseBound.lean`). For `z ∈ (0, ∞)ⁿ` and `v ∈ ℝⁿ` write
`mono z v = ∏ₖ zₖ ^ vₖ` (real powers). Then:

* `mono_add`, `mono_smul`, `mono_natCast`: the exponent arithmetic;
* `mono_le_of_le_one`: for `z ∈ (0, 1]ⁿ` the map `v ↦ mono z v` is antitone;
* `mono_sum_smul_le`: **the Newton-polytope bound**. If `mono z vⱼ ≤ S` for each `j` and
  `θ` is a probability vector, then `mono z (∑ⱼ θⱼ vⱼ) ≤ S`. Applied to the monomials `vⱼ` of a
  polynomial `S` with positive coefficients, it bounds `S` below by `mono z p` for every point `p`
  of the convex hull of its exponents.
-/

@[expose] public section

open scoped BigOperators

namespace QED.TwoLoop.UnitXClose

variable {n : ℕ}

/-- The real monomial `∏ₖ zₖ ^ vₖ`. -/
noncomputable def mono (z v : Fin n → ℝ) : ℝ := ∏ k, z k ^ v k

theorem mono_pos {z : Fin n → ℝ} (hz : ∀ k, 0 < z k) (v : Fin n → ℝ) : 0 < mono z v :=
  Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hz k) _

theorem mono_add {z : Fin n → ℝ} (hz : ∀ k, 0 < z k) (v w : Fin n → ℝ) :
    mono z (v + w) = mono z v * mono z w := by
  unfold mono
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Real.rpow_add (hz k) _ _

theorem mono_smul {z : Fin n → ℝ} (hz : ∀ k, 0 < z k) (t : ℝ) (v : Fin n → ℝ) :
    mono z (t • v) = mono z v ^ t := by
  unfold mono
  rw [← Real.finsetProd_rpow _ _ fun k _ => (Real.rpow_pos_of_pos (hz k) _).le]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, ← Real.rpow_mul (hz k).le, mul_comm]

theorem mono_natCast (z : Fin n → ℝ) (m : Fin n → ℕ) :
    mono z (fun k => (m k : ℝ)) = ∏ k, z k ^ m k := by
  unfold mono
  exact Finset.prod_congr rfl fun k _ => Real.rpow_natCast _ _

theorem mono_sum {r : ℕ} {z : Fin n → ℝ} (hz : ∀ k, 0 < z k) (vs : Fin r → Fin n → ℝ) :
    mono z (∑ j, vs j) = ∏ j, mono z (vs j) := by
  unfold mono
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.sum_apply, Real.rpow_sum_of_pos (hz k)]

/-- On `(0, 1]ⁿ`, `v ↦ mono z v` is antitone. -/
theorem mono_le_of_le_one {z : Fin n → ℝ} (hz : ∀ k, 0 < z k) (hz1 : ∀ k, z k ≤ 1)
    {v w : Fin n → ℝ} (h : ∀ k, w k ≤ v k) : mono z v ≤ mono z w :=
  Finset.prod_le_prod₀ (fun k _ => (Real.rpow_pos_of_pos (hz k) _).le)
    fun k _ => Real.rpow_le_rpow_of_exponent_ge (hz k) (hz1 k) (h k)

/-- **The Newton-polytope bound**: if `mono z vⱼ ≤ S` for every `j` and `θ` is a probability
vector, then `mono z (∑ⱼ θⱼ vⱼ) ≤ S`. -/
theorem mono_sum_smul_le {r : ℕ} {z : Fin n → ℝ} (hz : ∀ k, 0 < z k) (vs : Fin r → Fin n → ℝ)
    (θ : Fin r → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hθ1 : ∑ j, θ j = 1) {S : ℝ}
    (h : ∀ j, mono z (vs j) ≤ S) : mono z (∑ j, θ j • vs j) ≤ S := by
  rw [mono_sum hz]
  simp only [mono_smul hz]
  have hS : 0 < S := by
    by_cases hr : r = 0
    · subst hr
      simp at hθ1
    · exact (mono_pos hz _).trans_le (h ⟨0, Nat.pos_of_ne_zero hr⟩)
  calc ∏ j, mono z (vs j) ^ θ j ≤ ∏ j, S ^ θ j :=
        Finset.prod_le_prod₀ (fun j _ => (Real.rpow_pos_of_pos (mono_pos hz _) _).le)
          fun j _ => Real.rpow_le_rpow (mono_pos hz _).le (h j) (hθ j)
    _ = S := by rw [← Real.rpow_sum_of_pos hS, hθ1, Real.rpow_one]

end QED.TwoLoop.UnitXClose

end
