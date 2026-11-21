/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW5
public import QED.GradedProof.RPi4Pos

/-!
# (R-Π₄) step L10, B-inc: the pointwise derivative and `V(0) ≥ 0`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. In the scaled frame a piece is `pieceF n Q α pp (σ^{-1/2} M) γ (u/σ)`.
At a fixed Feynman point its `σ`-derivative is `σ⁻¹ (pieceFd n - pieceFw (n + 1))`, since
`v(σ) = V(0) + σ⁻¹ (∑ zᵢ Mᵢ² + z_γ u)` and `∂_v paramAtV n = -paramAtV (n + 1)`. The two terms
are dominated by the absolute bracket when `V(0) ≥ 0`, which P0 gives for spacelike momenta:

* `faceIdRayD_symanzikV_zero_nonneg`: `V(0) ≥ 0` at a spacelike momentum (`Minkowski.dot k k ≥ 0`);
* `faceIdRayD_hasDerivAt_paramAtV`: `∂_v paramAtV n = -paramAtV (n + 1)` (`n ≥ 6`, `v ≠ 0`);
* **`faceIdRayD_hasDerivAt_pieceF`**: the pointwise `σ`-derivative of the scaled integrand.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

/-- **`V(0) ≥ 0` at a spacelike momentum** (P0 at the masses `1` on the fermion lines and
`V(M) = V(0) + ∑ zᵢ Mᵢ²`). -/
theorem faceIdRayD_symanzikV_zero_nonneg (base : Fin 5 → Fin 2 → ℤ) (a : Fin 5 → ℝ)
    (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + a j| + |∑ s, (base j s : ℝ) * y₂ s + a j|
      ≤ if j = 4 then 0 else 1)
    {n : ℕ} (sh : Fin (n + 1) → Fin 5) {k : Fin 4 → ℝ} (hk : 0 ≤ Minkowski.dot k k)
    {z : Fin (n + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU (castLoopMatrix fun i => base (sh i)) z ≠ 0) :
    0 ≤ symanzikV (castLoopMatrix fun i => base (sh i)) (fun i => a (sh i) • k) 0 z := by
  set Ms : Fin (n + 1) → ℝ := fun i => if sh i = 4 then 0 else 1 with hMs
  have h := symanzikV_vp_ge_fermion base a y₁ y₂ hflow sh Ms one_pos
    (fun i hi => by simp [hMs, hi]) (k := k) (by nlinarith) hz hU
  have hmin : min 1 (1 + Minkowski.dot k k / (2 * 1) ^ 2) = 1 :=
    min_eq_left (le_add_of_nonneg_right (by positivity))
  rw [hmin, faceIdRayD_symanzikV_eq] at h
  simp only [one_pow, mul_one, one_mul] at h
  have e : ∑ i, z i * Ms i ^ 2 = ∑ i ∈ Finset.univ.filter (fun i => sh i ≠ 4), z i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : sh i = 4 <;> simp [hMs, hi]
  rw [e] at h
  linarith

/-- **`∂_v paramAtV n = -paramAtV (n + 1)`** (`n ≥ 6`, `v ≠ 0`). -/
theorem faceIdRayD_hasDerivAt_paramAtV {m n : ℕ} (hn : 6 ≤ n) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ)
    {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun w : ℝ => paramAtV n Q α p z w) (-paramAtV (n + 1) Q α p z v) v := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  have h := ((QED.GradedProof.WI2.hasDerivAt_ehat j Q (symanzikMatrix α z)
    (loopComp (-loopShift α p z)) (W := (v : ℂ)) (ofReal_ne_zero.2 hv)).comp_ofReal).const_mul
    (((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹)
  simp only [mul_neg] at h
  exact h

/-- `V` at the scaled masses `τ^{-1/2} M` and photon mass `u/τ`:
`V(0) + τ⁻¹ (∑ zᵢ Mᵢ² + z_γ u)`. -/
theorem faceIdRayD_v_scaled {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ)
    (z : Fin (m + 1) → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    symanzikV α pp ((Real.sqrt τ)⁻¹ • Ms) z + z γ * (u / τ) =
      symanzikV α pp 0 z + τ⁻¹ * (∑ i, z i * Ms i ^ 2 + z γ * u) := by
  rw [faceIdRayD_symanzikV_eq]
  have e : ∀ i, z i * ((Real.sqrt τ)⁻¹ • Ms) i ^ 2 = τ⁻¹ * (z i * Ms i ^ 2) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt hτ.le]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

/-- **The pointwise `σ`-derivative of the scaled collapsed integrand**: at a Feynman point `z`
with `v(σ) ≠ 0`, `∂_σ pieceF n Q α pp (σ^{-1/2} M) γ (u/σ) z = σ⁻¹ (pieceFd n - pieceFw (n + 1))`
at the same data. -/
theorem faceIdRayD_hasDerivAt_pieceF {m n : ℕ} (hn : 6 ≤ n) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hv : symanzikV α pp ((Real.sqrt σ)⁻¹ • Ms) z + z γ * (u / σ) ≠ 0) :
    HasDerivAt (fun τ => pieceF n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z)
      (((σ⁻¹ : ℝ) : ℂ) * (pieceFd n Q α pp ((Real.sqrt σ)⁻¹ • Ms) γ (u / σ) z -
        pieceFw (n + 1) Q α pp ((Real.sqrt σ)⁻¹ • Ms) γ (u / σ) z)) σ := by
  set B := symanzikV α pp 0 z
  set c := ∑ i, z i * Ms i ^ 2 + z γ * u
  have hg : HasDerivAt (fun τ : ℝ => B + τ⁻¹ * c) (c * -(σ ^ 2)⁻¹) σ := by
    have := ((hasDerivAt_inv hσ.ne').mul_const c).const_add B
    simpa [mul_comm] using this
  have hvσ := faceIdRayD_v_scaled α pp Ms γ u z hσ
  rw [hvσ] at hv
  have hP := faceIdRayD_hasDerivAt_paramAtV hn Q α pp z hv
  have hc := (hP.scomp σ hg).const_mul (z γ : ℂ)
  have hev : (fun τ => pieceF n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z) =ᶠ[nhds σ]
      fun τ => (z γ : ℂ) * ((fun w : ℝ => paramAtV n Q α pp z w) ∘ fun τ => B + τ⁻¹ * c) τ := by
    filter_upwards [lt_mem_nhds hσ] with τ hτ
    simp only [pieceF, Function.comp, faceIdRayD_v_scaled α pp Ms γ u z hτ]
    rfl
  refine (hc.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [faceIdRayD_pieceFd_eq, pieceFw, pieceF, hvσ]
  simp only [c, real_smul]
  push_cast
  ring

end QED.GradedProof.RPi4

end
