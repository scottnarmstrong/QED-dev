/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRateNull

/-!
# (R-Π₄) step L10, T2.UV: the ray face rate by interpolation

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV, the
inputs `QED.GradedProof.RPi4.FaceIdRateRay` of `QED.GradedProof.RPi4.faceIdRate_cfg4_of_ray`).
The sharp scaling `C s (s/u)^η` of `FaceIdRateRay` follows from two cruder bounds along the ray
`k'(s) = tiltVec √s s`, for `u ≥ s ≥ 1`:

* a **size bound with a gain**: `‖u G(u, k'(s))‖ ≤ A s^{1-δ}` for some `δ > 0` (the
  Pauli–Villars block suppresses the class densities when all masses are below `√s`);
* a **rate with a polynomial constant**: `‖u G(u, k'(s)) - L(s)‖ ≤ B s^p u^{-1/2}` (the
  heavy-photon rate of `heavyRate_vDens_*` with its constant tracked polynomially in `s`).

For `u ≤ s^{4p}` the first bound is below `s (s/u)^η` once `η (4p - 1) ≤ δ`; for `u ≥ s^{4p}` the
second is, once `η ≤ 1/4`.

* `faceIdRay_rpow_mono`; **`faceIdRay_of_size_rate`**.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

/-- `s^a ≤ s^b` for `1 ≤ s`, `a ≤ b`. -/
theorem faceIdRay_rpow_mono {s a b : ℝ} (hs : 1 ≤ s) (hab : a ≤ b) : s ^ a ≤ s ^ b :=
  Real.rpow_le_rpow_of_exponent_le hs hab

/-- **The ray face rate from a size bound with a gain and a rate with a polynomial constant.** -/
theorem faceIdRay_of_size_rate {G : ℝ → (Fin 4 → ℝ) → ℂ} {L : ℝ → ℂ} {A B δ p : ℝ}
    (hδ : 0 < δ) (hp : 1 ≤ p)
    (hA : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ A * s ^ (1 - δ))
    (hB : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, s ≤ u →
      ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ B * s ^ p * u ^ (-(1 / 2) : ℝ)) :
    FaceIdRateRay G := by
  set η : ℝ := min (1 / 4) (δ / (4 * p - 1)) with hη_def
  have hp1 : 0 < 4 * p - 1 := by linarith
  have hη : 0 < η := lt_min (by norm_num) (div_pos hδ hp1)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηδ : η * (4 * p - 1) ≤ δ := by
    have := min_le_right (1 / 4 : ℝ) (δ / (4 * p - 1))
    rw [← hη_def, le_div_iff₀ hp1] at this
    exact this
  refine ⟨max (2 * |A|) |B|, η, hη, L, fun s hs u hsu => ?_⟩
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hsu
  have hu1 : 1 ≤ u := hs.trans hsu
  -- the limit inherits the size bound
  have hL : ‖L s‖ ≤ A * s ^ (1 - δ) := by
    have ht : Tendsto (fun u : ℝ => (u : ℂ) * G u (tiltVec (Real.sqrt s) s)) atTop (𝓝 (L s)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun u : ℝ => B * s ^ p * u ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
          (B * s ^ p)
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
      filter_upwards [eventually_ge_atTop s] with v hv using hB s hs v hv
    exact le_of_tendsto ht.norm (by
      filter_upwards [eventually_ge_atTop s] with v hv using hA s hs v hv)
  have hX : s * (s / u) ^ η = s ^ (1 + η) * u ^ (-η) := by
    rw [Real.div_rpow hs0.le hu0.le, Real.rpow_neg hu0.le, Real.rpow_add hs0, Real.rpow_one,
      div_eq_mul_inv]
    ring
  have hX0 : 0 ≤ s * (s / u) ^ η := mul_nonneg hs0.le (Real.rpow_nonneg (div_pos hs0 hu0).le _)
  rw [mul_assoc]
  rcases le_or_gt u (s ^ (4 * p)) with hu | hu
  · -- small `u`: the size bound
    have h1 : ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s‖ ≤ 2 * |A| * s ^ (1 - δ) := by
      have := (norm_sub_le _ _).trans (add_le_add (hA s hs u hsu) hL)
      have hA' : A * s ^ (1 - δ) ≤ |A| * s ^ (1 - δ) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hs0.le _)
      linarith
    have h2 : s ^ (1 - δ) ≤ s * (s / u) ^ η := by
      rw [hX]
      have hu' : (s ^ (4 * p)) ^ (-η) ≤ u ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos hu0 hu (by linarith)
      rw [← Real.rpow_mul hs0.le] at hu'
      calc s ^ (1 - δ) ≤ s ^ (1 + η + 4 * p * -η) :=
            faceIdRay_rpow_mono hs (by nlinarith)
        _ = s ^ (1 + η) * s ^ (4 * p * -η) := Real.rpow_add hs0 _ _
        _ ≤ s ^ (1 + η) * u ^ (-η) :=
            mul_le_mul_of_nonneg_left hu' (Real.rpow_nonneg hs0.le _)
    calc _ ≤ 2 * |A| * s ^ (1 - δ) := h1
      _ ≤ 2 * |A| * (s * (s / u) ^ η) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max (2 * |A|) |B| * (s * (s / u) ^ η) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
  · -- large `u`: the rate
    have h2 : s ^ p * u ^ (-(1 / 2) : ℝ) ≤ s * (s / u) ^ η := by
      rw [hX]
      have hsplit : u ^ (-(1 / 2) : ℝ) = u ^ (-η) * u ^ (-(1 / 2 - η)) := by
        rw [← Real.rpow_add hu0]; ring_nf
      have hu' : u ^ (-(1 / 2 - η)) ≤ (s ^ (4 * p)) ^ (-(1 / 2 - η)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hs0 _) hu.le (by linarith)
      rw [← Real.rpow_mul hs0.le] at hu'
      have hsp : s ^ p * s ^ (4 * p * -(1 / 2 - η)) ≤ s ^ (1 + η) := by
        rw [← Real.rpow_add hs0]
        exact faceIdRay_rpow_mono hs (by nlinarith)
      have hue : 0 ≤ u ^ (-η) := Real.rpow_nonneg hu0.le _
      calc s ^ p * u ^ (-(1 / 2) : ℝ) = s ^ p * u ^ (-(1 / 2 - η)) * u ^ (-η) := by
            rw [hsplit]; ring
        _ ≤ s ^ p * s ^ (4 * p * -(1 / 2 - η)) * u ^ (-η) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hu' (Real.rpow_nonneg hs0.le _)) hue
        _ ≤ s ^ (1 + η) * u ^ (-η) := mul_le_mul_of_nonneg_right hsp hue
    have hB' := hB s hs u hsu
    have h3 : B * s ^ p * u ^ (-(1 / 2) : ℝ) ≤ |B| * (s ^ p * u ^ (-(1 / 2) : ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _)
        (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hu0.le _))
    calc _ ≤ |B| * (s ^ p * u ^ (-(1 / 2) : ℝ)) := hB'.trans h3
      _ ≤ |B| * (s * (s / u) ^ η) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ ≤ max (2 * |A|) |B| * (s * (s / u) ^ η) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hX0

end QED.GradedProof.RPi4

end
