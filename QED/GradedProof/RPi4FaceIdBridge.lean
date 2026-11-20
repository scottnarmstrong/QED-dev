/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPad
public import QED.GradedProof.RPi4FaceIdKinds
public import QED.TwoLoop.UnitSCCtAssembly

/-!
# (R-Π₄) step L6d3: one-loop limits as reduced one-loop functionals

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The limit of a
one-loop integrand through product data is `(auxLimit m₀)⁻¹ pvOf(…)` of the padded data
(`tendsto_kinds`, `faceId_tendsto_kinds_cubic`). With `auxLimit m₀ = iπ²/(2m₀²)` and
`faceId_integral_pad`, this value is `iπ²` times the reduced one-loop functional
`∫_Δ faceIdRedBr` of the one-loop lines, the functional in which the face values of the two-loop
pieces are expressed (`FaceShape.faceIdRedVal`).

* **`faceId_pvOf_pad`**: `(auxLimit m₀)⁻¹ · pvOf N (padded data) = iπ² ∫_Δ faceIdRedBr`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- **The one-loop value of padded data as a reduced one-loop functional**: for `r + 4` one-loop
lines, a numerator of loop-1 degree at most one (cubic for `r = 0`) and `V̂ ≥ c > 0` on the
one-loop simplex, `(auxLimit m₀)⁻¹ pvOf N = iπ² ∫_Δ faceIdRedBr (r + 4) Q (-P₀, 0) V̂`. -/
theorem faceId_pvOf_pad {r : ℕ} {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q)
    (hq : r = 0 → Q.quart = 0) (pR : Fin (r + 3 + 1) → Fin 4 → ℝ) (MR : Fin (r + 3 + 1) → ℝ)
    {m₀ c : ℝ} (hc : 0 < c) (hm₀ : 0 < m₀)
    (hV : ∀ w ∈ simplexSet (r + 3), c ≤ faceIdVR pR MR (simplexPoint w))
    {N : (Fin 2 → Fin 4 → ℝ) → ℂ} (hQN : Q.eval = N)
    (hint : IntegrableOn (QED.TwoLoop.ClassLimit.paramIntegrand Q (faceIdPadα (r + 3))
      (faceIdPadP pR) (faceIdPadM MR m₀) 0) (simplexSet (r + 3 + 1 + 2))) :
    (auxLimit m₀)⁻¹ * pvOf N (faceIdPadα (r + 3)) (faceIdPadP pR) (faceIdPadM MR m₀) =
      I * (π : ℂ) ^ 2 * ∫ w in simplexSet (r + 3), faceIdRedBr (r + 3 + 1) Q
        (faceIdX0 (faceIdP0 pR (simplexPoint w))) (faceIdVR pR MR (simplexPoint w)) := by
  rw [pvOf_eq hQN, QED.TwoLoop.UnitSCCt.auxLimit_eq hm₀]
  have h := faceId_integral_pad pR MR m₀ hQ hq hc hm₀ hV hint
  simp only [← faceId_paramIntegrand_eq_pf] at h
  rw [h]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hm : (m₀ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm₀.ne'
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

end QED.GradedProof.RPi4

end
