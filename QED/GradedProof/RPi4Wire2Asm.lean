/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Wire2DRay
public import QED.GradedProof.RPi4FaceRateIncARed
public import QED.GradedProof.RPi4FaceRateIncBPcs
public import QED.GradedProof.RPi4MajLipCfg
public import QED.GradedProof.RPi4MajLIncClass

/-!
# (R-Π₄) wiring: the frozen conclusion from the increment inputs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). With `WireDRayGen` and
`WireFaceRateGen` proved (`QED.GradedProof.RPi4.wire2_wireDRayGen`,
`QED.GradedProof.RPi4.wire2_wireFaceRateGen`), the frozen conclusion needs only the
scale-Lipschitz bound `MajLimLip4` of the photon limit. That bound follows from
`QED.GradedProof.RPi4.majLip_limLip4_of_ins`, whose inputs `MajFaceRate` at `decCfg 1 4`,
`MajDRay` and `MajLRayInc` of the classes are proved; what remains are the increment forms
(A) and (B) of the merged pieces at the dilated configurations `decDil l (decCfg 1 4)`, `l ≥ 1`:
(A) gives with (B) both `MajDRayInc` (`QED.GradedProof.RPi4.majDRayInc_of_incPow_rateB`) and,
with the value face rate, `MajFaceRateInc`.

* **`vacuumPolarizationPart_two_lepton_limit_of_limLip4`**: the frozen conclusion from
  `MajLimLip4` alone;
* `wire2_decDil_mass`, `wire2_majFaceRateInc_of_pieces`, `wire2_majLipIns_of_pieces`,
  **`wire2_limLip4_of_pieces`**;
* **`vacuumPolarizationPart_two_lepton_limit_of_incPieces`**: the frozen conclusion from (A)
  and (B) for increments of the merged pieces of the three classes at `decDil l (decCfg 1 4)`.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **(R-Π₄), conditional on `MajLimLip4` alone**: the frozen conclusion from the
scale-Lipschitz bound of the photon limit; every other input is proved. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_limLip4 {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hL4 : MajLimLip4 P₀.e) :
    ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
      ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
        1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
        ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
          (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
          (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
        ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
          (∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
            IsRenormalizedThrough
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2) ∧
          ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
            IsRenormalizedThrough
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2 →
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 :=
  vacuumPolarizationPart_two_lepton_limit_of_gen P₀ mH he hm hmH (wire2_wireDRayGen P₀.e)
    (wire2_wireFaceRateGen P₀ he) hL4

/-- The flavours of `decDil l (decCfg 1 4)`, `l ≥ 1`, have masses at least `l`. -/
theorem wire2_decDil_mass {l : ℝ} (hl : 1 ≤ l) : ∀ g, l ≤ (decDil l (decCfg 1 4)).mass g := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  intro g
  simpa using majLip_decDil_mass_ge (zero_le_one.trans hl) hmass g

/-- (A) for increments at every photon mass gives (A) for increments, piece by piece. -/
theorem wire2_aPow_of_aq {base : Fin 5 → Fin 2 → ℤ} {c : Fin 5 → ℝ}
    {Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {l : ℝ}
    (h : FaceRateIncPieces base c Num E4 2 3 FaceRateIncAQPow l) :
    FaceRateIncPieces base c Num E4 2 3 FaceRateIncAPow l := fun M X Y hM hX hY =>
  ⟨fun i j hij => ((h M X Y hM hX hY).1 i j hij).faceRateIncAPow,
    fun i => ((h M X Y hM hX hY).2.1 i).faceRateIncAPow, (h M X Y hM hX hY).2.2.faceRateIncAPow⟩

section Inc

variable (P : Params) (he : P.e ≠ 0)

include he

/-- **`MajFaceRateInc` at `decDil l (decCfg 1 4)`** from (A) and (B) for increments of the
merged pieces (the value face rate is proved). -/
theorem wire2_majFaceRateInc_of_pieces {l : ℝ} (hl : 1 ≤ l)
    (hAa : FaceRateIncPieces baseVA cVA (vNum P.e 0 1 aVA baseVA cVA) (vNumE4 P.e 0 1 aVA) 2 3
      FaceRateIncAPow l)
    (hBa : FaceRateIncPieces baseVB cVB (vNum P.e 0 1 aVB baseVB cVB) (vNumE4 P.e 0 1 aVB) 2 3
      FaceRateIncAPow l)
    (hCa : FaceRateIncPieces baseVC cVC (vNum P.e 0 1 aVC baseVC cVC) (vNumE4 P.e 0 1 aVC) 2 3
      FaceRateIncAPow l)
    (hAb : FaceRateIncPieces baseVA cVA (vNum P.e 0 1 aVA baseVA cVA) (vNumE4 P.e 0 1 aVA) 2 3
      FaceRateIncB l)
    (hBb : FaceRateIncPieces baseVB cVB (vNum P.e 0 1 aVB baseVB cVB) (vNumE4 P.e 0 1 aVB) 2 3
      FaceRateIncB l)
    (hCb : FaceRateIncPieces baseVC cVC (vNum P.e 0 1 aVC baseVC cVC) (vNumE4 P.e 0 1 aVC) 2 3
      FaceRateIncB l) :
    MajFaceRateInc (decDil l (decCfg 1 4)) (fun _ => 0) P.e l := by
  have hl0 : 0 < l := one_pos.trans_le hl
  have hm := wire2_decDil_mass hl
  exact faceRateInc_decDil_of_pieces P he hl (wire2_faceIdRateRay_VA _ hl0 hm P.e)
    (wire2_faceIdRateRay_VB _ hl0 hm P.e) (wire2_faceIdRateRay_VC _ hl0 hm P.e)
    hAa hBa hCa hAb hBb hCb

/-- **`MajLipIns` at `decDil l (decCfg 1 4)`** from (A) for increments at every photon mass and
(B) for increments of the merged pieces `A_{ij}`, `B_i` of the three classes. -/
theorem wire2_majLipIns_of_pieces {l : ℝ} (hl : 1 ≤ l)
    (hA : FaceRateIncAQPiecesAB aVA baseVA cVA P.e l)
    (hB : FaceRateIncAQPiecesAB aVB baseVB cVB P.e l)
    (hC : FaceRateIncAQPiecesAB aVC baseVC cVC P.e l)
    (hA' : FaceRateIncBPiecesAB aVA baseVA cVA P.e l)
    (hB' : FaceRateIncBPiecesAB aVB baseVB cVB P.e l)
    (hC' : FaceRateIncBPiecesAB aVC baseVC cVC P.e l) :
    MajLipIns (decDil l (decCfg 1 4)) (fun _ => 0) P.e l := by
  have hl0 : 0 < l := one_pos.trans_le hl
  have hm := wire2_decDil_mass hl
  have qA := faceRateIncPieces_aq_of_AB _ _ _ P.e (isOddG_aVA · · · ·)
    (tcov_vNumA P.e 0 1 baseVA cVA) hA
  have qB := faceRateIncPieces_aq_of_AB _ _ _ P.e (isOddG_aVB · · · ·)
    (tcov_vNumB P.e 0 1 baseVB cVB) hB
  have qC := faceRateIncPieces_aq_of_AB _ _ _ P.e (isOddG_aVC · · · ·)
    (tcov_vNumC P.e 0 1 baseVC cVC) hC
  have bA := faceRateIncPieces_b_VA P.e hA'
  have bB := faceRateIncPieces_b_VB P.e hB'
  have bC := faceRateIncPieces_b_VC P.e hC'
  obtain ⟨lA, lB, lC⟩ := majLInc_decDil P.e hl
  exact ⟨wire2_majDRay_VA _ hl0 hm P.e, wire2_majDRay_VB _ hl0 hm P.e,
    wire2_majDRay_VC _ hl0 hm P.e, lA, lB, lC,
    faceRateIncAQ_majDRayInc_vDens _ _ _ P.e 2 3 hl0 qA bA _ hm,
    faceRateIncAQ_majDRayInc_vDens _ _ _ P.e 2 3 hl0 qB bB _ hm,
    faceRateIncAQ_majDRayInc_vDens _ _ _ P.e 2 3 hl0 qC bC _ hm,
    wire2_majFaceRateInc_of_pieces P he hl (wire2_aPow_of_aq qA) (wire2_aPow_of_aq qB)
      (wire2_aPow_of_aq qC) bA bB bC⟩

/-- **`MajLimLip4`** from (A) and (B) for increments of the merged pieces of the three classes
at every `decDil l (decCfg 1 4)`, `l ≥ 1`. -/
theorem wire2_limLip4_of_pieces
    (hA : ∀ l : ℝ, 1 ≤ l → FaceRateIncAQPiecesAB aVA baseVA cVA P.e l ∧
      FaceRateIncAQPiecesAB aVB baseVB cVB P.e l ∧ FaceRateIncAQPiecesAB aVC baseVC cVC P.e l)
    (hB : ∀ l : ℝ, 1 ≤ l → FaceRateIncBPiecesAB aVA baseVA cVA P.e l ∧
      FaceRateIncBPiecesAB aVB baseVB cVB P.e l ∧ FaceRateIncBPiecesAB aVC baseVC cVC P.e l) :
    MajLimLip4 P.e :=
  majLip_limLip4_of_ins P he (faceIdRayAQ_majFaceRate_cfg4 P he) fun l hl =>
    wire2_majLipIns_of_pieces P he hl (hA l hl).1 (hA l hl).2.1 (hA l hl).2.2 (hB l hl).1
      (hB l hl).2.1 (hB l hl).2.2

end Inc

/-- **(R-Π₄), conditional on the increment inputs of the merged pieces**: (A) for increments at
every photon mass and (B) for increments of the pieces `A_{ij}`, `B_i` of the classes `VA`,
`VB`, `VC` at every `decDil l (decCfg 1 4)`, `l ≥ 1`, masses at least `l`. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_incPieces {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hA : ∀ l : ℝ, 1 ≤ l → FaceRateIncAQPiecesAB aVA baseVA cVA P₀.e l ∧
      FaceRateIncAQPiecesAB aVB baseVB cVB P₀.e l ∧ FaceRateIncAQPiecesAB aVC baseVC cVC P₀.e l)
    (hB : ∀ l : ℝ, 1 ≤ l → FaceRateIncBPiecesAB aVA baseVA cVA P₀.e l ∧
      FaceRateIncBPiecesAB aVB baseVB cVB P₀.e l ∧ FaceRateIncBPiecesAB aVC baseVC cVC P₀.e l) :
    ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
      ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
        1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
        ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
          (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
          (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
        ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
          (∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
            IsRenormalizedThrough
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2) ∧
          ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
            IsRenormalizedThrough
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2 →
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 :=
  vacuumPolarizationPart_two_lepton_limit_of_limLip4 P₀ mH he hm hmH
    (wire2_limLip4_of_pieces P₀ he hA hB)

end QED.GradedProof.RPi4

end
