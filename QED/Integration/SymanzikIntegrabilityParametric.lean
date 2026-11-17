/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrability
public import QED.Integration.TwoLoopParametric

/-!
# The scalar two-loop parametric representation without integrability hypotheses

Corollaries of `QED/Integration/TwoLoopParametric.lean` in which the integrability hypotheses on
the first Symanzik polynomial `U` are discharged by `QED/Integration/SymanzikIntegrability.lean`:

* `integral_prod_lineDenom_eq_of_span` (sub-step (a)): the hypothesis that `U^{-1/2}` is
  integrable on the simplex is dropped; two independent `αᵢ` suffice.
* `jointEnergyFirstIntegral_prod_inv_lineDenom_of_noSubdivergence`: the full parametric
  representation for `N = m + 1 ≥ 5` lines whose loop coefficients satisfy the no-subdivergence
  criterion `NoSubdivergence α` (every line has at least three lines not parallel to it); the
  criterion implies both `hspan` and the integrability of `U⁻²`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **Sub-step (a) without the integrability hypothesis.** For `N = m + 1 ≥ 2` propagators,
`ε > 0` and two independent `αᵢ`, the energy integrand `∏ᵢ Dᵢ(t, v)⁻¹` is integrable and
`∫_{ℝ²} ∏ᵢ Dᵢ⁻¹ dt = m! ∫_Δ -(π/(N-1)) U^{-1/2} w^{1-N} dx`. -/
theorem integral_prod_lineDenom_eq_of_span (hm : 0 < m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun t : Fin 2 → ℝ => ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ t : Fin 2 → ℝ, ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, energyValue α p M ε x v :=
  integral_prod_lineDenom_eq α p M hm hε hspan
    (integrableOn_inv_sqrt_symanzikU_of_span α hm hspan) v

/-- **The scalar two-loop parametric representation under the no-subdivergence criterion.**
For `N = m + 1 ≥ 5` propagators with line momenta `kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ`, masses `Mᵢ`,
`ε > 0`, and loop coefficients such that every line has at least three lines not parallel to it
(`NoSubdivergence α`: no one-loop subintegration with at most two lines): both stages of the
joint energy-first integral of `∏ᵢ Dᵢ⁻¹`, `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, are integrable, and
`jointEnergyFirstIntegral 2 (∏ᵢ Dᵢ⁻¹) = -π⁴ (N-5)! ∫_Δ U⁻² (V - iε)^{4-N} dx`. -/
theorem jointEnergyFirstIntegral_prod_inv_lineDenom_of_noSubdivergence (hm : 4 ≤ m)
    (hε : 0 < ε) (hcrit : NoSubdivergence α) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ((m - 4).factorial : ℂ) *
        ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ :=
  jointEnergyFirstIntegral_prod_inv_lineDenom α p M hm hε hcrit.span
    (integrableOn_inv_sq_symanzikU_of_criterion α hcrit)

end QED.Integration.TwoLoop

end
