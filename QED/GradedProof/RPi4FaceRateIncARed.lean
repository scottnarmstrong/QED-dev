/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncPcs
public import QED.GradedProof.RPi4MajDInc
public import QED.GradedProof.RPi4MajDPNull

/-!
# (R-Π₄) step L10: (A) for increments at every photon mass, and `MajDRayInc`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10.
`FaceRateIncAQPow` is `QED.GradedProof.RPi4.FaceRateIncAPow` for all `u ≥ 1` (not only
`u ≥ s`). Together with the increment rate (B) `QED.GradedProof.RPi4.FaceRateIncB` it gives the
increment bound `QED.GradedProof.RPi4.MajDRayInc` of a density: below `u₀ = s^{2p}` the power
loss `u^a` is absorbed by the gain `s^{-δ}`, above `u₀` the rate (B) applies, and the increment
of the limit `L` is read off at `u₀`.

* `FaceRateIncAQPow`, `.faceRateIncAPow`, `.zero`, `.add`, `.const_mul`, `faceRateIncLin_aqPow`;
* **`majDRayInc_of_incPow_rateB`**;
* `faceRateIncAQ_pieceP_two_three`, `FaceRateIncAQPiecesAB`, `faceRateIncPieces_aq_of_AB`;
* **`faceRateIncAQ_majDRayInc_vDens`**: `MajDRayInc` of a class density from (A) for increments
  at every photon mass and (B) for increments of its merged pieces.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- **(A) for increments with a power loss, for all `u ≥ 1`**: some `δ > 0` such that for
every `a > 0`, `‖u (G(u, k'(s)) - G(u, k'(s')))‖ ≤ A s^{1-δ} u^a (s - s')/s'` for
`1 ≤ s' ≤ s ≤ 2s'`, `u ≥ 1`. -/
def FaceRateIncAQPow (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → ∃ A : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
    ∀ u : ℝ, 1 ≤ u →
      ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))‖ ≤
        A * s ^ (1 - δ) * u ^ a * ((s - s') / s')

namespace FaceRateIncAQPow

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem faceRateIncAPow (h : FaceRateIncAQPow G) : FaceRateIncAPow G := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := h a ha
  exact ⟨A, fun s s' hs' hss hs2 u hsu => hA s s' hs' hss hs2 u ((hs'.trans hss).trans hsu)⟩

theorem zero : FaceRateIncAQPow fun _ _ => 0 :=
  ⟨1, one_pos, fun _ _ => ⟨0, fun _ _ _ _ _ u _ => by simp⟩⟩

theorem add (hG : FaceRateIncAQPow G) (hH : FaceRateIncAQPow H) :
    FaceRateIncAQPow fun u k => G u k + H u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  obtain ⟨δ', hδ', hH⟩ := hH
  refine ⟨min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  obtain ⟨A', hA'⟩ := hH a ha
  refine ⟨|A| + |A'|, fun s s' hs' hss hs2 u hu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  have hε : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  have hua : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le _
  have m1 : s ^ (1 - δ) ≤ s ^ (1 - min δ δ') :=
    faceIdRay_rpow_mono hs (by linarith [min_le_left δ δ'])
  have m2 : s ^ (1 - δ') ≤ s ^ (1 - min δ δ') :=
    faceIdRay_rpow_mono hs (by linarith [min_le_right δ δ'])
  have b : ∀ {C δ₀ : ℝ}, s ^ (1 - δ₀) ≤ s ^ (1 - min δ δ') →
      C * s ^ (1 - δ₀) * u ^ a * ((s - s') / s') ≤
        |C| * s ^ (1 - min δ δ') * u ^ a * ((s - s') / s') := fun {C δ₀} hm =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hm
      (Real.rpow_nonneg hs0.le _) (abs_nonneg _)) hua) hε
  have e : (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) + H u (tiltVec (Real.sqrt s) s) -
      (G u (tiltVec (Real.sqrt s') s') + H u (tiltVec (Real.sqrt s') s'))) =
      (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) +
        (u : ℂ) * (H u (tiltVec (Real.sqrt s) s) - H u (tiltVec (Real.sqrt s') s')) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add ((hA s s' hs' hss hs2 u hu).trans (b m1))
    ((hA' s s' hs' hss hs2 u hu).trans (b m2))).trans (le_of_eq ?_))
  ring

theorem const_mul (hG : FaceRateIncAQPow G) (r : ℂ) :
    FaceRateIncAQPow fun u k => r * G u k := by
  obtain ⟨δ, hδ, hG⟩ := hG
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨A, hA⟩ := hG a ha
  refine ⟨‖r‖ * A, fun s s' hs' hss hs2 u hu => ?_⟩
  have e : (u : ℂ) * (r * G u (tiltVec (Real.sqrt s) s) - r * G u (tiltVec (Real.sqrt s') s')) =
      r * ((u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))) := by
    ring
  rw [e, norm_mul]
  calc ‖r‖ * ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))‖
      ≤ ‖r‖ * (A * s ^ (1 - δ) * u ^ a * ((s - s') / s')) :=
        mul_le_mul_of_nonneg_left (hA s s' hs' hss hs2 u hu) (norm_nonneg _)
    _ = _ := by ring

end FaceRateIncAQPow

theorem faceRateIncLin_aqPow : FaceRateIncLin FaceRateIncAQPow :=
  ⟨FaceRateIncAQPow.zero, fun hG hH => hG.add hH, fun r hG => hG.const_mul r⟩

/-- **`MajDRayInc` from (A) for increments at every photon mass and (B) for increments.** -/
theorem majDRayInc_of_incPow_rateB {G : ℝ → (Fin 4 → ℝ) → ℂ} (hA : FaceRateIncAQPow G)
    (hB : FaceRateIncB G) : MajDRayInc G := by
  obtain ⟨δ, hδ, hA⟩ := hA
  obtain ⟨B, p, hp, L, hL⟩ := hB
  have hp0 : 0 < p := one_pos.trans_le hp
  obtain ⟨A, hA⟩ := hA (δ / (2 * p)) (by positivity)
  set K : ℝ := |A| with hK
  have hK0 : 0 ≤ K := abs_nonneg A
  have hB0 : 0 ≤ |B| := abs_nonneg B
  refine ⟨2 * (K + 2 * |B|), fun s s' hs' hss hs2 u hu => ?_⟩
  have hs : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := one_pos.trans_le hs
  have hs'0 : 0 < s' := one_pos.trans_le hs'
  set ε : ℝ := (s - s') / s' with hε_def
  have hε : 0 ≤ ε := div_nonneg (by linarith) hs'0.le
  have hsε : s * ε ≤ 2 * (s - s') := by
    rw [hε_def, mul_div_assoc', div_le_iff₀ hs'0]
    nlinarith
  set u₀ : ℝ := s ^ (2 * p) with hu₀
  have hu₀0 : 0 < u₀ := Real.rpow_pos_of_pos hs0 _
  have hsu₀ : s ≤ u₀ := by
    calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
      _ ≤ u₀ := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  set Δ : ℝ → ℂ := fun v =>
    (v : ℂ) * (G v (tiltVec (Real.sqrt s) s) - G v (tiltVec (Real.sqrt s') s')) with hΔ
  -- below `u₀`: the power loss is absorbed by the gain
  have hlow : ∀ v : ℝ, 1 ≤ v → v ≤ u₀ → ‖Δ v‖ ≤ K * s * ε := fun v hv hvu => by
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
    calc ‖Δ v‖ ≤ A * s ^ (1 - δ) * v ^ (δ / (2 * p)) * ε := hA s s' hs' hss hs2 v hv
      _ ≤ K * s ^ (1 - δ) * v ^ (δ / (2 * p)) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_abs_self A) (Real.rpow_nonneg hs0.le _)) (Real.rpow_nonneg hv0.le _)) hε
      _ ≤ K * s ^ (1 - δ) * s ^ δ * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3
            (mul_nonneg hK0 (Real.rpow_nonneg hs0.le _))) hε
      _ = K * s * ε := by rw [mul_assoc K, h4]
  -- above `u₀`: the rate (B)
  have hpow : ∀ v : ℝ, u₀ ≤ v → s ^ p * v ^ (-(1 / 2) : ℝ) ≤ 1 := fun v hv => by
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
  have hBv : ∀ v : ℝ, u₀ ≤ v → ‖Δ v - (L s - L s')‖ ≤ |B| * ε := fun v hv => by
    have hv0 : 0 < v := hu₀0.trans_le hv
    calc _ ≤ B * s ^ p * v ^ (-(1 / 2) : ℝ) * ε := hL s s' hs' hss hs2 v (hsu₀.trans hv)
      _ ≤ |B| * s ^ p * v ^ (-(1 / 2) : ℝ) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_abs_self B) (Real.rpow_nonneg hs0.le _)) (Real.rpow_nonneg hv0.le _)) hε
      _ = |B| * (s ^ p * v ^ (-(1 / 2) : ℝ)) * ε := by ring
      _ ≤ |B| * 1 * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow v hv) hB0) hε
      _ = |B| * ε := by ring
  have hfin : ‖Δ u‖ ≤ (K + 2 * |B|) * (s * ε) := by
    by_cases hcase : u ≤ u₀
    · have := hlow u hu hcase
      nlinarith [mul_nonneg hB0 (mul_nonneg hs0.le hε)]
    · rw [not_le] at hcase
      have hL0 : ‖L s - L s'‖ ≤ K * s * ε + |B| * ε := by
        have h1 := hBv u₀ le_rfl
        have h2 := hlow u₀ (hs.trans hsu₀) le_rfl
        calc ‖L s - L s'‖ = ‖Δ u₀ - (Δ u₀ - (L s - L s'))‖ := by ring_nf
          _ ≤ ‖Δ u₀‖ + ‖Δ u₀ - (L s - L s')‖ := norm_sub_le _ _
          _ ≤ _ := add_le_add h2 h1
      have h3 := hBv u hcase.le
      have h4 : ‖Δ u‖ ≤ ‖Δ u - (L s - L s')‖ + ‖L s - L s'‖ := by
        calc ‖Δ u‖ = ‖(Δ u - (L s - L s')) + (L s - L s')‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have hε1 : |B| * ε ≤ |B| * (s * ε) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hε hs) hB0
      nlinarith
  have hc : 0 ≤ K + 2 * |B| := by positivity
  calc ‖Δ u‖ ≤ (K + 2 * |B|) * (s * ε) := hfin
    _ ≤ (K + 2 * |B|) * (2 * (s - s')) := mul_le_mul_of_nonneg_left hsε hc
    _ = 2 * (K + 2 * |B|) * (s - s') := by ring

/-! ### Class densities -/

section Pad

variable (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ)

/-- **The padded piece at `(2, 3)` has (A) for increments**: it vanishes. -/
theorem faceRateIncAQ_pieceP_two_three (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) (M X Y : ℝ) :
    FaceRateIncAQPow (majDPieceP base c (vNumE4 e 0 1 A) M X Y 2 3) := by
  have h4 : ∀ k, vNumE4 e 0 1 A k 2 3 = 0 :=
    majDP_E4_two_three _ (vNumE4_cov e A base c hA hcov) fun _ => rfl
  have h0 : majDPieceP base c (vNumE4 e 0 1 A) M X Y 2 3 = fun _ _ => 0 :=
    funext₂ fun u k => majDPieceP_two_three base c _ h4 M X Y u k
  rw [h0]
  exact FaceRateIncAQPow.zero

/-- (A) for increments at every photon mass of the merged pieces `A_{ij}` and `B_i` at
`(2, 3)`, masses `≥ m₀`. -/
def FaceRateIncAQPiecesAB (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j →
      FaceRateIncAQPow (majDPieceA base c (vNum e 0 1 A base c) M X Y 2 3 i j)) ∧
      ∀ i : Fin 4, FaceRateIncAQPow (majDPieceB base c (vNum e 0 1 A base c) M X Y 2 3 i)

/-- **`FaceRateIncPieces … FaceRateIncAQPow` from the pieces `A_{ij}`, `B_i`.** -/
theorem faceRateIncPieces_aq_of_AB (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) {m₀ : ℝ}
    (h : FaceRateIncAQPiecesAB A base c e m₀) :
    FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) 2 3 FaceRateIncAQPow m₀ :=
  fun M X Y hM hX hY => ⟨(h M X Y hM hX hY).1, (h M X Y hM hX hY).2,
    faceRateIncAQ_pieceP_two_three A base c e hA hcov M X Y⟩

end Pad

/-- **`MajDRayInc` of a class density** from (A) for increments at every photon mass and (B)
for increments of its merged pieces. -/
theorem faceRateIncAQ_majDRayInc_vDens
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ) (μ ν : Fin 4) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA : FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν FaceRateIncAQPow
      m₀)
    (hB : FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν FaceRateIncB m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRayInc fun u k => vDens A base c Φ e m₀ u k μ ν :=
  majDRayInc_of_incPow_rateB
    (faceRateInc_vDens_of_pieces faceRateIncLin_aqPow A base c e μ ν hm₀ hA Φ hmass)
    (faceRateInc_vDens_of_pieces faceRateIncLin_b A base c e μ ν hm₀ hB Φ hmass)

end QED.GradedProof.RPi4

end
