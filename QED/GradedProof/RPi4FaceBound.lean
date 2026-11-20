/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceCoeff

/-!
# (R-Π₄) step L6d1: the parametric integrand on the face of a logarithmic subgraph

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. Let `ρ` be the
parameter weight of a subgraph block (a chain together with the photon) of a theta graph, small
compared with the weight `≥ 1/2` of the remaining chain. Then `U ≥ ρ / 2`, the entries of `A⁻¹`
other than the one of the subgraph loop are at most `2`, and that one is at most `2 / ρ`.
Hence the sharp per-point bounds (R12.8 of the worker notes):

* `norm_paramAtV_le_face_se`: for a numerator of degree at most one along the subgraph loop (a
  self-energy face) the three terms of the integrand are at most `ρ⁻²` times constants;
* `norm_paramAtV_le_face_vtx`: for degree at most two (a vertex face) the last two terms carry
  one more factor `ρ⁻¹`;
* `face_hyps_one`, `face_hyps_two`: the hypotheses on the two faces of a theta graph
  (subgraph loop `1`: the chains `(0, 1)` and `(1, -1)`; subgraph loop `0`: the chains `(1, 0)`
  and `(1, -1)`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ}

section Generic

variable (n : ℕ) {Q : LoopQuartic} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (z : Fin (m + 1) → ℝ)

theorem norm_paramAtV_le_of_coeff {v a b c : ℝ} (hv : 0 < v) (h1 : ‖cOneAt n Q α p z‖ ≤ a)
    (h2 : ‖cTwoAt n Q α p z‖ ≤ b) (h3 : ‖cThreeAt n Q α z‖ ≤ c) :
    ‖paramAtV n Q α p z v‖ ≤ a * (v ^ (n - 3))⁻¹ + b * (v ^ (n - 4))⁻¹ + c * (v ^ (n - 5))⁻¹ := by
  have key : ∀ (w : ℂ) (B : ℝ) (k : ℕ), ‖w‖ ≤ B → ‖w * ((v : ℂ) ^ k)⁻¹‖ ≤ B * (v ^ k)⁻¹ :=
    fun w B k hw => by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv.le]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
  rw [paramAtV_eq]
  exact (norm_add₃_le).trans (add_le_add (add_le_add (key _ _ _ h1) (key _ _ _ h2))
    (key _ _ _ h3))

theorem invU_sq_le_face {B U ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ) (hU : ρ / 2 ≤ U) :
    B / U ^ 2 ≤ 4 / ρ ^ 2 * B := by
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  rw [div_le_iff₀ (by positivity)]
  have : ρ ^ 2 ≤ 4 * U ^ 2 := by nlinarith
  calc B = B * ρ ^ 2 / ρ ^ 2 := by field_simp
    _ ≤ B * (4 * U ^ 2) / ρ ^ 2 := by gcongr
    _ = _ := by ring

variable {s : Fin 2} {K ρ v : ℝ} (hK : 0 ≤ K) (hX : ∀ a, ‖loopComp (-loopShift α p z) a‖ ≤ K)
  (hρ : 0 < ρ) (hU : ρ / 2 ≤ symanzikU α z)
  (hg₀ : ∀ r t, (r, t) ≠ (s, s) → |(symanzikMatrix α z)⁻¹ r t| ≤ 2) (hv : 0 < v)

include hK hX hρ hU hg₀ hv

/-- **The self-energy face**: a numerator of degree at most one along the subgraph loop. -/
theorem norm_paramAtV_le_face_se (hQ : LoopDegLe s 1 Q) :
    ‖paramAtV n Q α p z v‖ ≤ 4 / ρ ^ 2 *
      ((n - 4).factorial * (lqNorm Q * (1 + K) ^ 4) * (v ^ (n - 3))⁻¹ +
        (n - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * 2) * (v ^ (n - 4))⁻¹ +
        (n - 6).factorial / 4 * (lqQuart Q * (3 * 2 ^ 2)) * (v ^ (n - 5))⁻¹) := by
  have hU0 : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hU
  have h1 := norm_cOneAt_le n (Q := Q) α p z hK hX hU0
  have h2 := norm_cTwoAt_le_deg n α p z hK hX hU0 hQ zero_le_two hg₀
  have h3 := norm_cThreeAt_le_deg_one n α z hU0 hQ zero_le_two hg₀
  have b1 : 0 ≤ (n - 4).factorial * (lqNorm Q * (1 + K) ^ 4) :=
    mul_nonneg (by positivity) (mul_nonneg (lqNorm_nonneg Q) (by positivity))
  have b2 : 0 ≤ (n - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * 2) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (lqHess_nonneg Q) (by positivity))
      zero_le_two)
  have b3 : 0 ≤ (n - 6).factorial / 4 * (lqQuart Q * (3 * 2 ^ 2)) :=
    mul_nonneg (by positivity) (mul_nonneg (lqQuart_nonneg Q) (by positivity))
  refine (norm_paramAtV_le_of_coeff n α p z hv (h1.trans (invU_sq_le_face b1 hρ hU))
    (h2.trans (invU_sq_le_face b2 hρ hU)) (h3.trans (invU_sq_le_face b3 hρ hU))).trans
    (le_of_eq ?_)
  ring

/-- **The vertex face**: a numerator of degree at most two along the subgraph loop. -/
theorem norm_paramAtV_le_face_vtx (hQ : LoopDegLe s 2 Q)
    (hg : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ 2 / ρ) :
    ‖paramAtV n Q α p z v‖ ≤ 4 / ρ ^ 2 *
      ((n - 4).factorial * (lqNorm Q * (1 + K) ^ 4) * (v ^ (n - 3))⁻¹ +
        (n - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * (2 / ρ)) * (v ^ (n - 4))⁻¹ +
        (n - 6).factorial / 4 * (lqQuart Q * (3 * (2 * (2 / ρ)))) * (v ^ (n - 5))⁻¹) := by
  have hU0 : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hU
  have h1 := norm_cOneAt_le n (Q := Q) α p z hK hX hU0
  have h2 := norm_cTwoAt_le n (Q := Q) α p z hK hX hU0 hg
  have h3 := norm_cThreeAt_le_deg_two n α z hU0 hQ zero_le_two hg hg₀
  have b1 : 0 ≤ (n - 4).factorial * (lqNorm Q * (1 + K) ^ 4) :=
    mul_nonneg (by positivity) (mul_nonneg (lqNorm_nonneg Q) (by positivity))
  have b2 : 0 ≤ (n - 5).factorial / 2 * (lqHess Q * (1 + (K + K ^ 2)) * (2 / ρ)) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (lqHess_nonneg Q) (by positivity))
      (by positivity))
  have b3 : 0 ≤ (n - 6).factorial / 4 * (lqQuart Q * (3 * (2 * (2 / ρ)))) :=
    mul_nonneg (by positivity) (mul_nonneg (lqQuart_nonneg Q) (by positivity))
  refine (norm_paramAtV_le_of_coeff n α p z hv (h1.trans (invU_sq_le_face b1 hρ hU))
    (h2.trans (invU_sq_le_face b2 hρ hU)) (h3.trans (invU_sq_le_face b3 hρ hU))).trans
    (le_of_eq ?_)
  ring

end Generic

section Theta

variable (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
  (hα : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1]) (hz : ∀ i, 0 ≤ z i)
  (hT : chainZ α z ![1, 0] + chainZ α z ![0, 1] + chainZ α z ![1, -1] ≤ 1)

include hα hz hT

/-- **The face of the subgraph loop `1`** (block `ρ = Z₂ + Z₃`, remaining chain `Z₁ ≥ 1/2`). -/
theorem face_hyps_one (hρ : 0 < chainZ α z ![0, 1] + chainZ α z ![1, -1])
    (hZ : 1 / 2 ≤ chainZ α z ![1, 0]) :
    (chainZ α z ![0, 1] + chainZ α z ![1, -1]) / 2 ≤ symanzikU α z ∧
      (∀ r t, (r, t) ≠ (1, 1) → |(symanzikMatrix α z)⁻¹ r t| ≤ 2) ∧
      ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ 2 / (chainZ α z ![0, 1] + chainZ α z ![1, -1]) := by
  set ρ := chainZ α z ![0, 1] + chainZ α z ![1, -1] with hρdef
  have h2 := chainZ_nonneg α hz ![0, 1]
  have h3 := chainZ_nonneg α hz ![1, -1]
  have hUc := symanzikU_chain α z hα
  have hUρ : ρ / 2 ≤ symanzikU α z := by
    rw [hUc]; nlinarith
  have hU : symanzikU α z ≠ 0 := (lt_of_lt_of_le (by positivity) hUρ).ne'
  have hU0 : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hUρ
  refine ⟨hUρ, fun r t hrt => ?_, fun r t => ?_⟩
  · refine (abs_inv_le_chain_one α hα hz hU (by linarith) r t hrt).trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  · refine (abs_inv_le_chain α hα hz hU r t).trans ?_
    rw [div_le_div_iff₀ hU0 (by positivity)]
    nlinarith

/-- **The face of the subgraph loop `0`** (block `ρ = Z₁ + Z₃`, remaining chain `Z₂ ≥ 1/2`). -/
theorem face_hyps_two (hρ : 0 < chainZ α z ![1, 0] + chainZ α z ![1, -1])
    (hZ : 1 / 2 ≤ chainZ α z ![0, 1]) :
    (chainZ α z ![1, 0] + chainZ α z ![1, -1]) / 2 ≤ symanzikU α z ∧
      (∀ r t, (r, t) ≠ (0, 0) → |(symanzikMatrix α z)⁻¹ r t| ≤ 2) ∧
      ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ 2 / (chainZ α z ![1, 0] + chainZ α z ![1, -1]) := by
  set ρ := chainZ α z ![1, 0] + chainZ α z ![1, -1] with hρdef
  have h1 := chainZ_nonneg α hz ![1, 0]
  have h3 := chainZ_nonneg α hz ![1, -1]
  have hUc := symanzikU_chain α z hα
  have hUρ : ρ / 2 ≤ symanzikU α z := by
    rw [hUc]; nlinarith
  have hU : symanzikU α z ≠ 0 := (lt_of_lt_of_le (by positivity) hUρ).ne'
  have hU0 : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hUρ
  refine ⟨hUρ, fun r t hrt => ?_, fun r t => ?_⟩
  · refine (abs_inv_le_chain_two α hα hz hU (by linarith) r t hrt).trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  · refine (abs_inv_le_chain α hα hz hU r t).trans ?_
    rw [div_le_div_iff₀ hU0 (by positivity)]
    nlinarith

end Theta

end QED.GradedProof.RPi4

end
