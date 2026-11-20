/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPL

/-!
# (R-Π₄) step L6d3: the half Laplacian as a one-loop representative

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The vertex face
wrappers (`faceId_face1_vtx_four`, `faceId_face0_vtx_four`) ask for a quartic `P` without
quartic part, of loop-`1` degree `≤ 1`, with `P(ℓ) = N(ℓ₀)`, where `N` is the half Laplacian of
the piece numerator on the slice. For a numerator `Q` of degree `≤ 2` along the face loop, the
quartic `faceIdLap Q` (resp. `faceIdLap (swapQ Q)`) is such a `P`: it has degree `0` along
loop `1` (`faceId_loopDegLe_faceIdLap`), so its value depends on `ℓ₀` only
(`faceId_eval_slice_of_deg0`). So the vertex wrappers apply with `N` the slice Laplacian itself
and no Dirac algebra (`faceId_lap_rep`, `faceId_lap_rep0`); the Dirac identities of
`RPi4FaceIdDirac` then rewrite `N` pointwise.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

/-- **The half loop-`1` Laplacian of a numerator of loop-`1` degree `≤ 2` has loop-`1` degree
`0`.** -/
theorem faceId_loopDegLe_faceIdLap {Q : LoopQuartic} (hQ : LoopDegLe 1 2 Q) :
    LoopDegLe 1 0 (faceIdLap Q) where
  lin c hc := by
    simp only [faceIdLap]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
    by_cases hab : loopInd 1 a + loopInd 1 b ≤ 1
    · simp [gMet_eS_eq_zero hab]
    · have ha := loopInd_le_one 1 a
      have hb := loopInd_le_one 1 b
      rw [hQ.cub a b c (by omega), hQ.cub a c b (by omega), hQ.cub c a b (by omega)]
      simp
  quad c d hcd := by
    simp only [faceIdLap]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
    by_cases hab : loopInd 1 a + loopInd 1 b ≤ 1
    · simp [gMet_eS_eq_zero hab]
    · have ha := loopInd_le_one 1 a
      have hb := loopInd_le_one 1 b
      simp only [LoopQuartic.quartSym]
      rw [hQ.quart a b c d (by omega), hQ.quart a c b d (by omega), hQ.quart a c d b (by omega),
        hQ.quart c a b d (by omega), hQ.quart c a d b (by omega), hQ.quart c d a b (by omega)]
      simp
  cub _ _ _ _ := rfl
  quart _ _ _ _ _ := rfl

/-- **A quartic of loop-`1` degree `0` depends on `ℓ₀` only.** -/
theorem faceId_eval_slice_of_deg0 {P : LoopQuartic} (h : LoopDegLe 1 0 P)
    (ℓ : Fin 2 → Fin 4 → ℝ) : P.eval ℓ = P.eval ![ℓ 0, 0] := by
  have key : ∀ a : LoopIndex, loopInd 1 a = 0 → loopComp ℓ a = loopComp ![ℓ 0, 0] a := by
    rintro ⟨s, ν⟩ ha
    have hs : s = 0 := by
      by_contra hs
      have : s = 1 := by omega
      simp [loopInd, this] at ha
    subst hs
    simp [loopComp]
  have hz : ∀ a : LoopIndex, 0 < loopInd 1 a ∨ loopInd 1 a = 0 := fun a => by omega
  simp only [LoopQuartic.eval, LoopQuartic.evalC]
  congr 1
  congr 1
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rcases hz a with ha | ha
    · simp [h.lin a ha]
    · rw [key a ha]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases hz a with ha | ha
    · simp [h.quad a b (by omega)]
    rcases hz b with hb | hb
    · simp [h.quad a b (by omega)]
    rw [key a ha, key b hb]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    by_cases h0 : loopInd 1 a = 0 ∧ loopInd 1 b = 0 ∧ loopInd 1 c = 0
    · rw [key a h0.1, key b h0.2.1, key c h0.2.2]
    · simp [h.cub a b c (by omega)]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h0 : loopInd 1 a = 0 ∧ loopInd 1 b = 0 ∧ loopInd 1 c = 0 ∧ loopInd 1 d = 0
    · rw [key a h0.1, key b h0.2.1, key c h0.2.2.1, key d h0.2.2.2]
    · simp [h.quart a b c d (by omega)]

/-- **The loop-`1` vertex representative**: for `LoopDegLe 1 2 Q`, `faceIdLap Q` has no quartic
part, loop-`1` degree `≤ 1`, and value the slice Laplacian `faceIdLapF 1 Q.eval (ℓ₀, 0)`. -/
theorem faceId_lap_rep {Q : LoopQuartic} (hQ : LoopDegLe 1 2 Q) :
    (faceIdLap Q).quart = 0 ∧ LoopDegLe 1 1 (faceIdLap Q) ∧
      ∀ ℓ, (faceIdLap Q).eval ℓ = faceIdLapF 1 Q.eval ![ℓ 0, 0] := by
  refine ⟨rfl, (faceId_loopDegLe_faceIdLap hQ).mono (by norm_num), fun ℓ => ?_⟩
  rw [faceId_eval_slice_of_deg0 (faceId_loopDegLe_faceIdLap hQ), faceId_eval_faceIdLap hQ]

/-- **The loop-`0` vertex representative**: for `LoopDegLe 0 2 Q`, `faceIdLap (swapQ Q)` has no
quartic part, loop-`1` degree `≤ 1`, and value the slice Laplacian `faceIdLapF 0 Q.eval (0, ℓ₀)`. -/
theorem faceId_lap_rep0 {Q : LoopQuartic} (hQ : LoopDegLe 0 2 Q) :
    (faceIdLap (swapQ Q)).quart = 0 ∧ LoopDegLe 1 1 (faceIdLap (swapQ Q)) ∧
      ∀ ℓ, (faceIdLap (swapQ Q)).eval ℓ = faceIdLapF 0 Q.eval ![0, ℓ 0] := by
  have h1 := loopDegLe_swapQ hQ
  refine ⟨rfl, (faceId_loopDegLe_faceIdLap h1).mono (by norm_num), fun ℓ => ?_⟩
  rw [faceId_eval_slice_of_deg0 (faceId_loopDegLe_faceIdLap h1), faceId_eval_faceIdLap_swapQ hQ]
  congr 1
  funext i
  fin_cases i <;> rfl

end QED.GradedProof.RPi4

end
