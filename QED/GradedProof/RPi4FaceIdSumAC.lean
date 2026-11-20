/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdTriF
public import QED.GradedProof.RPi4FaceIdPcVA
public import QED.GradedProof.RPi4FaceIdPcVC

/-!
# (R-Π₄) step L6d3: the merged pieces of `VA` and `VC` at the face

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For the classes
`VA` and `VC` (face at loop `1`, the loop-`0` vertex face vanishing since the numerator is affine
in `ℓ₁`), the face integral `faceIdTriPsi` of the fifteen pieces at `ε > 0` is the energy-first
integral of the three-flavour combination `faceIdTriF` of the self-energy face integrand, plus
`iε` times the integral of the padded defect:

* `faceId_isLoopPoly_congr`;
* `faceId_propDenom_Y0`: `p² + Y² = (p² - iε) + Y² + iε`;
* **`faceId_triPsi_VA`**, **`faceId_triPsi_VC`**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

theorem faceId_propDenom_Y0 (Y ε : ℝ) (p : Fin 4 → ℝ) :
    propDenom Y 0 p = propDenom 0 ε p + (Y : ℂ) ^ 2 + ε * I := by
  simp only [propDenom]
  push_cast
  ring

theorem faceId_isLoopPoly_congr {n : ℕ} {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : IsLoopPoly 2 n F) (e : ∀ ℓ, F ℓ = G ℓ) : IsLoopPoly 2 n G :=
  funext e ▸ h

variable (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ) (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (k : Fin 4 → ℝ) (μ ν : Fin 4) {ε : ℝ} (hε : 0 < ε)
  (hL : ∀ m ℓ, faceIdLapF 1 (fun ℓ => Num m k ℓ μ ν) ℓ = 0)
  (hN : ∀ m ℓ, Num m k ℓ μ ν = E0 ℓ + (m : ℂ) ^ 2 * E2 ℓ + ((m : ℂ) ^ 2) ^ 2 * E4 k μ ν)
  (hP : ∀ m, IsLoopPoly 2 4 fun ℓ => Num m k ℓ μ ν) (hP2 : IsLoopPoly 2 2 E2)
  {M X Y : ℝ} (h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0) (h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0)
  (h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0)
include hε hL hN hP hP2 h01 h02 h12

/-- **The merged pieces of `VA` at the face.** -/
theorem faceId_triPsi_VA :
    faceIdTriPsi baseVA cVA Num E4 M X Y 0 k μ ν ε =
      QED.OneLoop.energyFirstIntegral (faceIdTriF (faceIdRB baseVA ![1, 0]) cVA ε k
        (fun m x => Num m k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν) M X Y) +
      ε * I * QED.OneLoop.energyFirstIntegral (faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k
        (fun _ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν) Y) ∧
    EF (faceIdTriF (faceIdRB baseVA ![1, 0]) cVA ε k
        (fun m x => Num m k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν) M X Y) := by
  set b := faceIdRB baseVA ![1, 0]
  set mid : (Fin 4 → ℝ) → Fin 2 → Fin 4 → ℝ := fun x => ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)]
  have hm : ∀ {n} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}, IsLoopPoly 2 n F →
      IsLoopPoly 2 n fun ℓ => F (mid (ℓ 0)) := fun hF => faceId_isLoopPoly_mid hF 0 k
  have hV0 : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => faceIdV cVA ε k (ℓ 0) 0 := by
    refine faceId_isLoopPoly_congr ((isLoopAffine_zk k false).isLoopPoly_propDenom 0 ε)
      fun ℓ => ?_
    simp [faceIdV, zk, cVA]
  have eA : ∀ i j, i ≤ j → EF (faceIdFA b cVA ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k (mid x) μ ν) M X Y i j) := fun i j hij =>
    faceId_efA_VA hε k M X Y _ ((hm (hP M)).const_mul _) i j hij
  have eB : ∀ i, EF (faceIdFB b cVA ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (Num X k (mid x) μ ν - Num M k (mid x) μ ν)) X Y i) := fun i => by
    refine faceId_efB_VA hε k X Y _ ?_ i
    refine faceId_isLoopPoly_congr (((hm hP2).const_mul
      (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2))).add
      (IsLoopPoly.const (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((((X : ℂ) ^ 2) ^ 2 - ((M : ℂ) ^ 2) ^ 2) * E4 k μ ν)))) fun ℓ => ?_
    simp only [hN]
    ring
  have eP : EF (faceIdFP b cVA ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * (faceIdV cVA ε k x 0 + (Y : ℂ) ^ 2 + ε * I)) Y) :=
    faceId_efP_VA hε k Y _ ((hV0.add (IsLoopPoly.const _)).add (IsLoopPoly.const _)
      |>.const_mul _)
  have eP0 : EF (faceIdFP b cVA ε k
      (fun _ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν) Y) :=
    faceId_efP_VA hε k Y _ ((IsLoopPoly.const (n := 0) _).mono (by norm_num))
  obtain ⟨hs, hE⟩ := faceId_efi_sum_pieces _ _ _ eA eB eP
  have hpt := fun x => faceId_pieces_eq_triF b (by decide) cVA hε.ne' k
    (fun m x => Num m k (mid x) μ ν) (fun x => E0 (mid x)) (fun x => E2 (mid x)) (E4 k μ ν)
    (fun m x => hN m (mid x)) h01 h02 h12 x
  have hT : EF (faceIdTriF b cVA ε k (fun m x => Num m k (mid x) μ ν) M X Y) :=
    (hE.add (eP0.const_mul (-(ε * I)))).congr fun x => by rw [hpt x]; ring
  refine ⟨?_, hT⟩
  have hPsi : faceIdTriPsi baseVA cVA Num E4 M X Y 0 k μ ν ε =
      (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then QED.OneLoop.energyFirstIntegral
        (faceIdFA b cVA ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k (mid x) μ ν) M X Y i j) else 0) +
      ∑ i : Fin 4, QED.OneLoop.energyFirstIntegral (faceIdFB b cVA ε k (fun x =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k (mid x) μ ν - Num M k (mid x) μ ν)) X Y i) +
      QED.OneLoop.energyFirstIntegral (faceIdFP b cVA ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * (faceIdV cVA ε k x 0 + (Y : ℂ) ^ 2 + ε * I))
        Y) := by
    simp only [faceIdTriPsi]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hij
        · exact faceId_psiA_VA Num k μ ν M X Y ε hL i j hij
        · rfl
      · exact Finset.sum_congr rfl fun i _ => faceId_psiB_VA Num k μ ν M X Y ε hL i
    · rw [faceId_psiP_VA]
      congr 1
      funext x
      simp only [faceIdFP, faceId_propDenom_Y0 Y ε, faceIdV, cVA]
      simp only [Fin.castSucc_zero, Matrix.cons_val_zero, zero_smul, zero_add]
      ring
  rw [hPsi, hs, ← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    ← efi_add hT (eP0.const_mul _)]
  congr 1
  funext x
  exact hpt x

/-- **The merged pieces of `VC` at the face.** -/
theorem faceId_triPsi_VC :
    faceIdTriPsi baseVC cVC Num E4 M X Y 1 k μ ν ε =
      QED.OneLoop.energyFirstIntegral (faceIdTriF (faceIdRB baseVC ![1, 0]) cVC ε k
        (fun m x => Num m k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν) M X Y) +
      ε * I * QED.OneLoop.energyFirstIntegral (faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k
        (fun _ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν) Y) ∧
    EF (faceIdTriF (faceIdRB baseVC ![1, 0]) cVC ε k
        (fun m x => Num m k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν) M X Y) := by
  set b := faceIdRB baseVC ![1, 0]
  set mid : (Fin 4 → ℝ) → Fin 2 → Fin 4 → ℝ := fun x => ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)]
  have hm : ∀ {n} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}, IsLoopPoly 2 n F →
      IsLoopPoly 2 n fun ℓ => F (mid (ℓ 0)) := fun hF => faceId_isLoopPoly_mid hF 1 k
  have hV0 : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => faceIdV cVC ε k (ℓ 0) 0 := by
    refine faceId_isLoopPoly_congr ((isLoopAffine_zk k false).isLoopPoly_propDenom 0 ε)
      fun ℓ => ?_
    simp [faceIdV, zk, cVC]
  have eA : ∀ i j, i ≤ j → EF (faceIdFA b cVC ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k (mid x) μ ν) M X Y i j) := fun i j hij =>
    faceId_efA_VC hε k M X Y _ ((hm (hP M)).const_mul _) i j hij
  have eB : ∀ i, EF (faceIdFB b cVC ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (Num X k (mid x) μ ν - Num M k (mid x) μ ν)) X Y i) := fun i => by
    refine faceId_efB_VC hε k X Y _ ?_ i
    refine faceId_isLoopPoly_congr (((hm hP2).const_mul
      (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2))).add
      (IsLoopPoly.const (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((((X : ℂ) ^ 2) ^ 2 - ((M : ℂ) ^ 2) ^ 2) * E4 k μ ν)))) fun ℓ => ?_
    simp only [hN]
    ring
  have eP : EF (faceIdFP b cVC ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * (faceIdV cVC ε k x 0 + (Y : ℂ) ^ 2 + ε * I)) Y) :=
    faceId_efP_VC hε k Y _ ((hV0.add (IsLoopPoly.const _)).add (IsLoopPoly.const _)
      |>.const_mul _)
  have eP0 : EF (faceIdFP b cVC ε k
      (fun _ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν) Y) :=
    faceId_efP_VC hε k Y _ ((IsLoopPoly.const (n := 0) _).mono (by norm_num))
  obtain ⟨hs, hE⟩ := faceId_efi_sum_pieces _ _ _ eA eB eP
  have hpt := fun x => faceId_pieces_eq_triF b (by decide) cVC hε.ne' k
    (fun m x => Num m k (mid x) μ ν) (fun x => E0 (mid x)) (fun x => E2 (mid x)) (E4 k μ ν)
    (fun m x => hN m (mid x)) h01 h02 h12 x
  have hT : EF (faceIdTriF b cVC ε k (fun m x => Num m k (mid x) μ ν) M X Y) :=
    (hE.add (eP0.const_mul (-(ε * I)))).congr fun x => by rw [hpt x]; ring
  refine ⟨?_, hT⟩
  have hPsi : faceIdTriPsi baseVC cVC Num E4 M X Y 1 k μ ν ε =
      (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then QED.OneLoop.energyFirstIntegral
        (faceIdFA b cVC ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k (mid x) μ ν) M X Y i j) else 0) +
      ∑ i : Fin 4, QED.OneLoop.energyFirstIntegral (faceIdFB b cVC ε k (fun x =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k (mid x) μ ν - Num M k (mid x) μ ν)) X Y i) +
      QED.OneLoop.energyFirstIntegral (faceIdFP b cVC ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν * (faceIdV cVC ε k x 0 + (Y : ℂ) ^ 2 + ε * I))
        Y) := by
    simp only [faceIdTriPsi]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hij
        · exact faceId_psiA_VC Num k μ ν M X Y ε hL i j hij
        · rfl
      · exact Finset.sum_congr rfl fun i _ => faceId_psiB_VC Num k μ ν M X Y ε hL i
    · rw [faceId_psiP_VC]
      congr 1
      funext x
      simp only [faceIdFP, faceId_propDenom_Y0 Y ε, faceIdV, cVC]
      simp only [Fin.castSucc_zero, Matrix.cons_val_zero, zero_smul, zero_add]
      ring
  rw [hPsi, hs, ← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    ← efi_add hT (eP0.const_mul _)]
  congr 1
  funext x
  exact hpt x

end QED.GradedProof.RPi4

end
