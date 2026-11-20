/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Merge
public import QED.GradedProof.RPi4PhotonMass
public import QED.GradedProof.RPi4LightVP

/-!
# (R-Π₄) step L6b′: collapsing a pair of parallel photon lines

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6b′ (heavy photon
pair). In every piece of the vacuum-polarization classes the two photon lines (masses `a`, `b`)
have the same row and the same external momentum: the data are those of one line `i`, doubled
(`QED.GradedProof.WI2.dbl`). Splitting the parameter `zᵢ` of the merged line into
`(τ, zᵢ - τ)` (`QED.Integration.SimplexMerge.splitAt`) leaves `U`, `A`, the shift unchanged, and
`V` is affine in the squared masses, so the integrand depends on `τ` only through
`τ a² + (zᵢ - τ) b²`. The pair formula `QED.GradedProof.RPi4.integral_comp_pair` then turns the
`τ`-integral into an integral over the squared mass `u ∈ [a², b²]` of one photon line.

* `paramAtV n Q α p z v`: the parametric integrand at the Feynman point `z` with the number `v`
  in place of `V - iε`; `paramAt_zero`.
* `symanzikV_pair`: `V` at the split point with masses `(a, b)` on the doubled line is
  `V₀ + τ a² + (zᵢ - τ) b²`, `V₀` the merged value at photon mass `0`; `paramAt_pair`.
* `symanzikV_update_sqrt`, `paramAtV_sqrt`: `V₀ + zᵢ u` is the merged value at photon mass `√u`.
* `integral_paramIntegrand_pair` (**photon collapse**):
  `∫_{Δₘ₊₁} paramIntegrand(a, b) = ∫_{Δₘ} (zᵢ/(b² - a²)) ∫_{a²}^{b²} paramAtV(V₀ + zᵢ u) du`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.GradedProof.WI2 (dbl paramAt ehat symanzikU_dbl symanzikMatrix_dbl loopShift_dbl
  symanzikV_dbl)
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)

variable {m : ℕ}

/-- **The parametric integrand at the Feynman point `z` with the value `v`** in place of
`V - iε`: `U(z)⁻² Ê_n[Q](A(z), -S(z), v)`. -/
noncomputable def paramAtV (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) (v : ℝ) : ℂ :=
  ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
    ehat n Q (symanzikMatrix α z) (loopComp (-loopShift α p z)) (v : ℂ)

theorem paramAt_zero (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M z : Fin (m + 1) → ℝ) :
    paramAt n Q α p M 0 z = paramAtV n Q α p z (symanzikV α p M z) := by
  simp [paramAt, paramAtV]

/-- **`V` at a split photon pair**: masses `(a, b)` on the two halves `(τ, zᵢ - τ)` of the
doubled line `i` (`a` the mass of line `i`). -/
theorem symanzikV_pair (i : Fin (m + 1)) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (b : ℝ) (z : Fin (m + 1) → ℝ)
    (τ : ℝ) :
    symanzikV (dbl i α) (dbl i p) (Fin.snoc M b) (splitAt i z τ) =
      symanzikV α p (Function.update M i 0) z + (τ * M i ^ 2 + (z i - τ) * b ^ 2) := by
  have h1 := symanzikV_sub_mass (dbl i α) (dbl i p) (Fin.snoc M b)
    (dbl i (Function.update M i 0)) (splitAt i z τ)
  rw [symanzikV_dbl] at h1
  rw [← sub_eq_iff_eq_add', h1, Fin.sum_univ_castSucc]
  simp only [splitAt_castSucc, splitAt_last, dbl, Fin.snoc_castSucc, Fin.snoc_last,
    Function.update_self]
  rw [Finset.sum_eq_single i]
  · simp only [Function.update_self]
    ring
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · simp

theorem paramAt_pair (n : ℕ) (Q : LoopQuartic) (i : Fin (m + 1))
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (b : ℝ)
    (z : Fin (m + 1) → ℝ) (τ : ℝ) :
    paramAt n Q (dbl i α) (dbl i p) (Fin.snoc M b) 0 (splitAt i z τ) =
      paramAtV n Q α p z
        (symanzikV α p (Function.update M i 0) z + (τ * M i ^ 2 + (z i - τ) * b ^ 2)) := by
  rw [paramAt_zero, symanzikV_pair]
  simp only [paramAtV, symanzikU_dbl, symanzikMatrix_dbl, loopShift_dbl]

/-- `V₀ + zᵢ u` is the value of `V` with the mass `√u` on line `i`. -/
theorem symanzikV_update_sqrt (i : Fin (m + 1)) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M z : Fin (m + 1) → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    symanzikV α p (Function.update M i (√u)) z =
      symanzikV α p (Function.update M i 0) z + z i * u := by
  have h := symanzikV_sub_mass α p (Function.update M i (√u)) (Function.update M i 0) z
  rw [← sub_eq_iff_eq_add', h, Finset.sum_eq_single i]
  · simp [Real.sq_sqrt hu]
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · simp

theorem paramAtV_sqrt (n : ℕ) (Q : LoopQuartic) (i : Fin (m + 1))
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M z : Fin (m + 1) → ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    paramAtV n Q α p z (symanzikV α p (Function.update M i 0) z + z i * u) =
      paramAt n Q α p (Function.update M i (√u)) 0 z := by
  rw [paramAt_zero, symanzikV_update_sqrt i α p M z hu]

/-- **Photon collapse.** For a line `i` doubled with masses `(a, b) = (Mᵢ, b)`, `a² ≠ b²`, and an
integrable integrand: `∫_{Δₘ₊₁} paramIntegrand = ∫_{Δₘ} (zᵢ/(b² - a²)) ∫_{a²}^{b²} paramAtV(V₀ +
zᵢ u) du`, with `V₀` the merged `V` at photon mass `0`. -/
theorem integral_paramIntegrand_pair (hm : 0 < m) (Q : LoopQuartic) (i : Fin (m + 1))
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {b : ℝ}
    (hab : M i ^ 2 ≠ b ^ 2)
    (hI : IntegrableOn (paramIntegrand Q (dbl i α) (dbl i p) (Fin.snoc M b) 0)
      (simplexSet (m + 1))) :
    ∫ x in simplexSet (m + 1), paramIntegrand Q (dbl i α) (dbl i p) (Fin.snoc M b) 0 x =
      ∫ y in simplexSet m, (simplexPoint y i / (b ^ 2 - M i ^ 2)) •
        ∫ u in M i ^ 2..b ^ 2, paramAtV (m + 1) Q α p (simplexPoint y)
          (symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u) := by
  obtain ⟨-, h2⟩ := integral_simplex_splitAt hm i
    (f := paramAt (m + 1) Q (dbl i α) (dbl i p) (Fin.snoc M b) 0) hI
  refine h2.trans (setIntegral_congr_fun (measurableSet_simplexSet m) fun y _ => ?_)
  simp only [paramAt_pair]
  exact integral_comp_pair (fun w => paramAtV (m + 1) Q α p (simplexPoint y)
    (symanzikV α p (Function.update M i 0) (simplexPoint y) + w)) hab (simplexPoint y i)

end QED.GradedProof.RPi4

end
