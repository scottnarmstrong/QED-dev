/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajDPCov
public import QED.GradedProof.RPi4FaceIdRayA
public import QED.GradedProof.RPi4FaceIdRayBRay

/-!
# (R-Π₄) step L10, `MajDRay`: the ray half from a gain bound and the rate (B)

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The ray half
`QED.GradedProof.RPi4.MajDRayRay` of a heavy-photon density `G`, `‖u G(u, k'(s))‖ ≤ C s` for all
`s, u ≥ 1` along `k'(s) = tiltVec √s s`, follows from two bounds:

* the size bound with a gain in `s` and a power loss in `u`, **for all `u ≥ 1`**
  (`MajDRayPow`): some `δ > 0` such that for every `a > 0`,
  `‖u G(u, k'(s))‖ ≤ A_a s^{1-δ} u^a`;
* the rate (B) `‖u G(u, k'(s)) - L(s)‖ ≤ B s^p u^{-1/2}` for `u ≥ s`
  (`QED.GradedProof.RPi4.FaceIdRayRateB`).

With `a = δ/(2p)` the loss is harmless for `u ≤ s^{2p}`; above, (B) at `u₀ = s^{2p}` bounds
`‖L(s)‖ ≤ A s + B`, and (B) at `u` gives `‖u G‖ ≤ ‖L(s)‖ + B`. The pointwise majorant route of
input (A) (`W ≥ c + sB` for every `u ≥ 1`, `u z_γ/W ≤ (u z_γ)^a W^{-a}`, the flow gain
`QED.GradedProof.RPi4.faceIdRayA_gain_le`) does not use `u ≥ s`, so `MajDRayPow` is the common
strengthening of `QED.GradedProof.RPi4.FaceIdRayAPow` that serves both (A) and `MajDRay`
(`MajDRayPow.faceIdRayAPow`).

* `MajDRayPow`, `MajDRayPow.zero`, `.add`, `.const_mul`, `.congr`, `.faceIdRayAPow`;
* **`majDRayRay_of_pow_rateB`**: `MajDRayPow G` and `FaceIdRayRateB G` give `MajDRayRay G`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.TwoLoop.LimitCovariance

/-- **The size bound with a gain, for every `u ≥ 1`**: some `δ > 0` such that for every
`a > 0`, `‖u G(u, k'(s))‖ ≤ A s^{1-δ} u^a` for `s, u ≥ 1`. -/
def MajDRayPow (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → ∃ A : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ A * s ^ (1 - δ) * u ^ a

namespace MajDRayPow

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

/-- `MajDRayPow` restricts to input (A) with a power loss. -/
theorem faceIdRayAPow (h : MajDRayPow G) : FaceIdRayAPow G := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := h a ha
  exact ⟨A, fun s hs u hu => hA s hs u (hs.trans hu)⟩

theorem zero : MajDRayPow fun _ _ => 0 :=
  ⟨1, one_pos, fun _ _ => ⟨0, fun _ _ _ _ => by simp⟩⟩

theorem add (hG : MajDRayPow G) (hH : MajDRayPow H) :
    MajDRayPow fun u k => G u k + H u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  obtain ⟨δ', hδ', hH⟩ := hH
  refine ⟨min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  obtain ⟨A', hA'⟩ := hH a ha
  refine ⟨|A| + |A'|, fun s hs u hu => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  have hua : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le a
  have h1 : s ^ (1 - δ) ≤ s ^ (1 - min δ δ') :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith [min_le_left δ δ'])
  have h2 : s ^ (1 - δ') ≤ s ^ (1 - min δ δ') :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith [min_le_right δ δ'])
  have g1 : A * s ^ (1 - δ) * u ^ a ≤ |A| * s ^ (1 - min δ δ') * u ^ a :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self A) h1
      (Real.rpow_nonneg (by linarith) _) (abs_nonneg A)) hua
  have g2 : A' * s ^ (1 - δ') * u ^ a ≤ |A'| * s ^ (1 - min δ δ') * u ^ a :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self A') h2
      (Real.rpow_nonneg (by linarith) _) (abs_nonneg A')) hua
  rw [mul_add]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ |A| * s ^ (1 - min δ δ') * u ^ a + |A'| * s ^ (1 - min δ δ') * u ^ a := by
        linarith [hA s hs u hu, hA' s hs u hu]
    _ = _ := by ring

theorem const_mul (hG : MajDRayPow G) (r : ℂ) : MajDRayPow fun u k => r * G u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  refine ⟨‖r‖ * A, fun s hs u hu => ?_⟩
  have e : (u : ℂ) * (r * G u (tiltVec (Real.sqrt s) s)) =
      r * ((u : ℂ) * G u (tiltVec (Real.sqrt s) s)) := by ring
  rw [e, norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hA s hs u hu).trans (le_of_eq (by ring))) (norm_nonneg _)

theorem congr (hG : MajDRayPow G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) :
    MajDRayPow H := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  exact ⟨A, fun s hs u hu => by rw [← e s hs u hu]; exact hA s hs u hu⟩

end MajDRayPow

/-- **The ray half of `MajDRay` from the gain bound and the rate (B).** -/
theorem majDRayRay_of_pow_rateB {G : ℝ → (Fin 4 → ℝ) → ℂ} (hA : MajDRayPow G)
    (hB : FaceIdRayRateB G) : MajDRayRay G := by
  obtain ⟨δ, hδ, hA⟩ := hA
  obtain ⟨B, p, hp, L, hL⟩ := hB
  have hp0 : 0 < p := one_pos.trans_le hp
  obtain ⟨A, hA⟩ := hA (δ / (2 * p)) (by positivity)
  set K : ℝ := |A| with hK
  refine ⟨K + 2 * |B|, fun s hs u hu => ?_⟩
  have hs0 : 0 < s := one_pos.trans_le hs
  have hu0 : 0 < u := one_pos.trans_le hu
  set u₀ : ℝ := s ^ (2 * p) with hu₀
  have hu₀0 : 0 < u₀ := Real.rpow_pos_of_pos hs0 _
  have hsu₀ : s ≤ u₀ := by
    calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
      _ ≤ u₀ := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  -- below `u₀`: the power loss is absorbed by the gain
  have hlow : ∀ v : ℝ, 1 ≤ v → v ≤ u₀ →
      ‖(v : ℂ) * G v (tiltVec (Real.sqrt s) s)‖ ≤ K * s := fun v hv hvu => by
    have hv0 : 0 < v := one_pos.trans_le hv
    have h3 : v ^ (δ / (2 * p)) ≤ s ^ δ := by
      calc v ^ (δ / (2 * p)) ≤ u₀ ^ (δ / (2 * p)) :=
            Real.rpow_le_rpow hv0.le hvu (by positivity)
        _ = s ^ δ := by
            rw [hu₀, ← Real.rpow_mul hs0.le]
            congr 1
            field_simp
    have h4 : s ^ (1 - δ) * s ^ δ = s := by
      rw [← Real.rpow_add hs0]; simp
    calc _ ≤ A * s ^ (1 - δ) * v ^ (δ / (2 * p)) := hA s hs v hv
      _ ≤ K * s ^ (1 - δ) * v ^ (δ / (2 * p)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A)
            (Real.rpow_nonneg hs0.le _)) (Real.rpow_nonneg hv0.le _)
      _ ≤ K * s ^ (1 - δ) * s ^ δ :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg A) (Real.rpow_nonneg hs0.le _))
      _ = K * s := by rw [mul_assoc, h4]
  have hK0 : 0 ≤ K := abs_nonneg A
  have hB0 : 0 ≤ |B| := abs_nonneg B
  by_cases hcase : u ≤ u₀
  · calc _ ≤ K * s := hlow u hu hcase
      _ ≤ (K + 2 * |B|) * s := by nlinarith
  · rw [not_le] at hcase
    -- `s^p u^{-1/2} ≤ 1` for `u ≥ u₀ = s^{2p}`
    have hpow : ∀ v : ℝ, u₀ ≤ v → s ^ p * v ^ (-(1 / 2) : ℝ) ≤ 1 := fun v hv => by
      have hv0 : 0 < v := hu₀0.trans_le hv
      have e1 : u₀ ^ (-(1 / 2) : ℝ) = (s ^ p)⁻¹ := by
        rw [hu₀, ← Real.rpow_mul hs0.le, ← Real.rpow_neg hs0.le]
        congr 1; ring
      have h1 : v ^ (-(1 / 2) : ℝ) ≤ u₀ ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hu₀0 hv (by norm_num)
      have hsp : 0 < s ^ p := Real.rpow_pos_of_pos hs0 p
      rw [e1] at h1
      calc s ^ p * v ^ (-(1 / 2) : ℝ) ≤ s ^ p * (s ^ p)⁻¹ :=
            mul_le_mul_of_nonneg_left h1 hsp.le
        _ = 1 := mul_inv_cancel₀ hsp.ne'
    have hBv : ∀ v : ℝ, u₀ ≤ v →
        ‖(v : ℂ) * G v (tiltVec (Real.sqrt s) s) - L s‖ ≤ |B| := fun v hv => by
      have hv0 : 0 < v := hu₀0.trans_le hv
      calc _ ≤ B * s ^ p * v ^ (-(1 / 2) : ℝ) := hL s hs v (hsu₀.trans hv)
        _ ≤ |B| * s ^ p * v ^ (-(1 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B)
              (Real.rpow_nonneg hs0.le _)) (Real.rpow_nonneg hv0.le _)
        _ = |B| * (s ^ p * v ^ (-(1 / 2) : ℝ)) := by ring
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left (hpow v hv) hB0
        _ = |B| := mul_one _
    have hL0 : ‖L s‖ ≤ K * s + |B| := by
      have h1 := hlow u₀ (hs.trans hsu₀) le_rfl
      have h2 := hBv u₀ le_rfl
      have e : L s = (u₀ : ℂ) * G u₀ (tiltVec (Real.sqrt s) s) -
          ((u₀ : ℂ) * G u₀ (tiltVec (Real.sqrt s) s) - L s) := by ring
      rw [e]
      exact (norm_sub_le _ _).trans (by linarith)
    have e : (u : ℂ) * G u (tiltVec (Real.sqrt s) s) =
        ((u : ℂ) * G u (tiltVec (Real.sqrt s) s) - L s) + L s := by ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ |B| + (K * s + |B|) := add_le_add (hBv u hcase.le) hL0
      _ ≤ (K + 2 * |B|) * s := by nlinarith

end QED.GradedProof.RPi4

end
