/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayBPiece
public import QED.TwoLoop.MassScalingBasic

/-!
# (R-Π₄) step L10, T2.UV: the dilation of the collapsed integrand

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the rate input
(B) of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`). Along the ray `k'(s) = √s (1, 0, 1, 1)`
the momenta are `r • p` with `r = √s`. Writing the masses as `r • (M / r)`, the photon mass as
`r² (u / r²)` and the numerator as `ℓ ↦ a Q(ℓ / r)` turns the collapsed integrand at `k'(s)`
into `a r^{-2(n-3)}` times the integrand at bounded momenta, masses `M / r` and photon mass
`u / r²` (exact, pointwise in the Feynman parameters):

* `faceIdRayB_loopComp_shift`, `faceIdRayB_cOneAt_dilateQ`, `faceIdRayB_cTwoAt_dilateQ`,
  `faceIdRayB_cThreeAt_dilateQ`: the three coefficients;
* `faceIdRayB_paramAtV_dilateQ`, **`faceIdRayB_pieceF_dilateQ`**.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.MassScaling

section Dilate

variable {m : ℕ} (n : ℕ) (Q : LoopQuartic) (a : ℂ) {r : ℝ} (hr : r ≠ 0)
  (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ)

include hr

theorem faceIdRayB_loopComp_shift :
    (fun i => ((r⁻¹ : ℝ) : ℂ) * loopComp (-loopShift α (r • p) z) i) =
      loopComp (-loopShift α p z) := by
  have e : r⁻¹ • -loopShift α (r • p) z = -loopShift α p z := by
    rw [loopShift_smul, smul_neg, smul_smul, inv_mul_cancel₀ hr, one_smul]
  rw [← e]
  funext i
  simp [loopComp]

/-- The first coefficient of `ℓ ↦ a Q(ℓ/r)` at the momenta `r p` is `a` times that of `Q`. -/
theorem faceIdRayB_cOneAt_dilateQ :
    cOneAt n (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) z = a * cOneAt n Q α p z := by
  simp only [cOneAt, evalC_dilateQ, faceIdRayB_loopComp_shift hr]
  ring

/-- The second coefficient of `ℓ ↦ a Q(ℓ/r)` at the momenta `r p` is `a r⁻²` times that of
`Q`. -/
theorem faceIdRayB_cTwoAt_dilateQ :
    cTwoAt n (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) z =
      a * ((r⁻¹ : ℝ) : ℂ) ^ 2 * cTwoAt n Q α p z := by
  simp only [cTwoAt, contractTwo_dilateQ, faceIdRayB_loopComp_shift hr]
  ring

omit hr in
/-- The third coefficient of `ℓ ↦ a Q(ℓ/r)` is `a r⁻⁴` times that of `Q`. -/
theorem faceIdRayB_cThreeAt_dilateQ :
    cThreeAt n (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α z = a * ((r⁻¹ : ℝ) : ℂ) ^ 4 * cThreeAt n Q α z := by
  simp only [cThreeAt, contractFour_dilateQ]
  ring

/-- **The parametric integrand under the dilation**: at the momenta `r p` and the argument
`r² v`, the numerator `ℓ ↦ a Q(ℓ/r)` gives `a r^{-2(n-3)}` times the integrand of `Q`. -/
theorem faceIdRayB_paramAtV_dilateQ (hn : 5 ≤ n) (v : ℝ) :
    paramAtV n (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) z (r ^ 2 * v) =
      a * ((r⁻¹ : ℝ) : ℂ) ^ (2 * (n - 3)) * paramAtV n Q α p z v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [paramAtV_eq, paramAtV_eq, faceIdRayB_cOneAt_dilateQ (k + 5) Q a hr,
    faceIdRayB_cTwoAt_dilateQ (k + 5) Q a hr, faceIdRayB_cThreeAt_dilateQ]
  have e3 : k + 5 - 3 = k + 2 := by omega
  have e4 : k + 5 - 4 = k + 1 := by omega
  have e5 : k + 5 - 5 = k := by omega
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  simp only [e3, e4, e5]
  push_cast
  simp only [mul_pow, mul_inv, inv_pow, ← pow_mul]
  have h2 : ∀ j : ℕ, ((r : ℂ) ^ (2 * j))⁻¹ = ((r : ℂ)⁻¹) ^ (2 * j) := fun j => by
    rw [inv_pow]
  simp only [h2]
  have e6 : 2 * (k + 2) = 2 * (k + 1) + 2 := by ring
  have e7 : 2 * (k + 1) = 2 * k + 2 := by ring
  rw [e6, e7]
  ring

omit hr in
/-- The second Symanzik function is homogeneous of degree `2` in the momenta and masses. -/
theorem faceIdRayB_symanzikV_smul (M : Fin (m + 1) → ℝ) (t : ℝ) :
    symanzikV α (t • p) (t • M) z = t ^ 2 * symanzikV α p M z :=
  symanzikV_smul α p M z t

/-- **The collapsed integrand under the dilation**: at momenta `r p`, masses `r M` and photon
mass `r² u`, the numerator `ℓ ↦ a Q(ℓ/r)` gives `a r^{-2(n-3)}` times the integrand of `Q` at
`p`, `M`, `u`. -/
theorem faceIdRayB_pieceF_dilateQ (hn : 5 ≤ n) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1))
    (u : ℝ) :
    pieceF n (dilateQ a ((r⁻¹ : ℝ) : ℂ) Q) α (r • p) (r • M) γ (r ^ 2 * u) z =
      a * ((r⁻¹ : ℝ) : ℂ) ^ (2 * (n - 3)) * pieceF n Q α p M γ u z := by
  simp only [pieceF]
  rw [faceIdRayB_symanzikV_smul α p z M r]
  have e : r ^ 2 * symanzikV α p M z + z γ * (r ^ 2 * u) =
      r ^ 2 * (symanzikV α p M z + z γ * u) := by ring
  rw [e, faceIdRayB_paramAtV_dilateQ n Q a hr α p z hn]
  ring

end Dilate

end QED.GradedProof.RPi4

end
