/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdSumAC
public import QED.GradedProof.RPi4FaceIdPcVB

/-!
# (R-Π₄) step L6d3: the merged pieces of `VB` at the two faces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For the class
`VB` both faces are vertex faces (three lines of each loop): the face integrands carry half the
Laplacian of the numerator, which is `A₀ + m² A₂` (the `m⁴` term is constant), and the padded
piece vanishes. The face integral `faceIdTriPsi` of the fifteen pieces at `ε > 0` is the sum over
the two faces of the energy-first integrals of the three-flavour combinations `faceIdTriF`:

* `faceId_pieces_eq_triF0`: the pointwise identity without the `m⁴` term;
* `faceId_efi_sum_pieces2`: the energy-first integral of the pieces of one face;
* **`faceId_triPsi_VB`**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-- **The pieces of a face are the three-flavour combination**, numerator `E₀ + m² E₂`. -/
theorem faceId_pieces_eq_triF0 (b : Fin 4 → Bool) (c : Fin 5 → ℝ) {ε : ℝ} (hε : ε ≠ 0)
    (k : Fin 4 → ℝ) (N : ℝ → (Fin 4 → ℝ) → ℂ) (E0 E2 : (Fin 4 → ℝ) → ℂ)
    (hN : ∀ m x, N m x = E0 x + (m : ℂ) ^ 2 * E2 x) {M X Y : ℝ}
    (h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0) (h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0)
    (h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0) (x : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then faceIdFA b c ε k (fun x =>
        ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * N M x) M X Y i j x
      else 0) +
      ∑ i : Fin 4, faceIdFB b c ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (N X x - N M x))
        X Y i x =
    faceIdTriF b c ε k N M X Y x := by
  have T := faceId_tri_g b (faceIdV c ε k x) (E0 x) (E2 x) 0 ((M : ℂ) ^ 2) ((X : ℂ) ^ 2)
    ((Y : ℂ) ^ 2) h01 h02 h12 (faceId_V_add_ne hε k x M) (faceId_V_add_ne hε k x X)
    (faceId_V_add_ne hε k x Y)
  have hA : ((triA M X Y : ℝ) : ℂ) = ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]
    push_cast
    ring
  have hB : ((triB M X Y : ℝ) : ℂ) = ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]
    push_cast
    ring
  have hS : ∀ i j : Fin 4, (if i ≤ j then faceIdFA b c ε k (fun x =>
        ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * N M x) M X Y i j x
      else 0) = if i ≤ j then ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (E0 x + (M : ℂ) ^ 2 * E2 x + ((M : ℂ) ^ 2) ^ 2 * 0) *
          ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l)
            (if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
          faceIdW (b i) (faceIdV c ε k x i) ((X : ℂ) ^ 2) *
          faceIdW (b j) (faceIdV c ε k x j) ((Y : ℂ) ^ 2)) else 0 := fun i j => by
    split_ifs
    · simp only [faceIdFA, hN]
      ring
    · rfl
  have hB' : ∀ i : Fin 4, faceIdFB b c ε k
      (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (N X x - N M x)) X Y i x =
      -(((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
        (E2 x + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * 0) *
        ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l)
          (if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
          faceIdW (b i) (faceIdV c ε k x i) ((Y : ℂ) ^ 2)) := fun i => by
    simp only [faceIdFB, hN]
    ring
  simp only [hS, hB']
  simp only [faceIdTriF, hN, hA, hB]
  linear_combination -T

/-- The energy-first integral of the pieces of one face, all integrable (no padded piece). -/
theorem faceId_efi_sum_pieces2 (FA : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (FB : Fin 4 → (Fin 4 → ℝ) → ℂ) (hA : ∀ i j, i ≤ j → EF (FA i j)) (hB : ∀ i, EF (FB i)) :
    (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then QED.OneLoop.energyFirstIntegral (FA i j) else 0) +
        ∑ i : Fin 4, QED.OneLoop.energyFirstIntegral (FB i) =
      QED.OneLoop.energyFirstIntegral fun x =>
        (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then FA i j x else 0) + ∑ i : Fin 4, FB i x := by
  obtain ⟨h, -⟩ := faceId_efi_sum_pieces FA FB (fun _ => 0) hA hB EF.zero
  rw [faceId_efi_zero, add_zero] at h
  simpa only [add_zero] using h

section VB

variable (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) (μ ν : Fin 4) {ε : ℝ} (hε : 0 < ε)
  (A0 A2 B0 B2 : (Fin 4 → ℝ) → ℂ)
  (hA : ∀ m x, 2⁻¹ * faceIdLapF 1 (fun ℓ => Num m k ℓ μ ν) ![x, 0] = A0 x + (m : ℂ) ^ 2 * A2 x)
  (hB : ∀ m x, 2⁻¹ * faceIdLapF 0 (fun ℓ => Num m k ℓ μ ν) ![0, x] = B0 x + (m : ℂ) ^ 2 * B2 x)
  (hA0 : IsLoopPoly 2 2 fun ℓ => A0 (ℓ 0)) (hA2 : IsLoopPoly 2 0 fun ℓ => A2 (ℓ 0))
  (hB0 : IsLoopPoly 2 2 fun ℓ => B0 (ℓ 0)) (hB2 : IsLoopPoly 2 0 fun ℓ => B2 (ℓ 0))
  {M X Y : ℝ} (h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0) (h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0)
  (h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0)
include hε hA hB hA0 hA2 hB0 hB2 h01 h02 h12

/-- **The merged pieces of `VB` at the two faces.** -/
theorem faceId_triPsi_VB :
    faceIdTriPsi baseVB cVB Num E4 M X Y 0 k μ ν ε =
      QED.OneLoop.energyFirstIntegral (faceIdTriF (faceIdRB baseVB ![1, 0]) cVB ε k
        (fun m x => A0 x + (m : ℂ) ^ 2 * A2 x) M X Y) +
      QED.OneLoop.energyFirstIntegral (faceIdTriF (faceIdRB baseVB ![0, 1]) cVB ε k
        (fun m x => B0 x + (m : ℂ) ^ 2 * B2 x) M X Y) ∧
    EF (faceIdTriF (faceIdRB baseVB ![1, 0]) cVB ε k
        (fun m x => A0 x + (m : ℂ) ^ 2 * A2 x) M X Y) ∧
    EF (faceIdTriF (faceIdRB baseVB ![0, 1]) cVB ε k
        (fun m x => B0 x + (m : ℂ) ^ 2 * B2 x) M X Y) := by
  set NA : ℝ → (Fin 4 → ℝ) → ℂ := fun m x => A0 x + (m : ℂ) ^ 2 * A2 x
  set NB : ℝ → (Fin 4 → ℝ) → ℂ := fun m x => B0 x + (m : ℂ) ^ 2 * B2 x
  have pA : ∀ m, IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => NA m (ℓ 0) := fun m =>
    hA0.add ((hA2.const_mul _).mono (by norm_num))
  have pB : ∀ m, IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => NB m (ℓ 0) := fun m =>
    hB0.add ((hB2.const_mul _).mono (by norm_num))
  have qA : IsLoopPoly 2 0 fun ℓ : Fin 2 → Fin 4 → ℝ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (NA X
      (ℓ 0) - NA M (ℓ 0)) :=
    faceId_isLoopPoly_congr (hA2.const_mul (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 -
        (M : ℂ) ^ 2)))
      fun ℓ => by simp only [NA]; ring
  have qB : IsLoopPoly 2 0 fun ℓ : Fin 2 → Fin 4 → ℝ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (NB X
      (ℓ 0) - NB M (ℓ 0)) :=
    faceId_isLoopPoly_congr (hB2.const_mul (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 -
        (M : ℂ) ^ 2)))
      fun ℓ => by simp only [NB]; ring
  have eA1 : ∀ i j, i ≤ j → EF (faceIdFA (faceIdRB baseVB ![1, 0]) cVB ε k (fun x =>
      ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NA M x) M X Y i j) :=
    fun i j hij => faceId_efA_VB1 hε k M X Y _ ((pA M).const_mul _) i j hij
  have eA0 : ∀ i j, i ≤ j → EF (faceIdFA (faceIdRB baseVB ![0, 1]) cVB ε k (fun x =>
      ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NB M x) M X Y i j) :=
    fun i j hij => faceId_efA_VB0 hε k M X Y _ ((pB M).const_mul _) i j hij
  have eB1 : ∀ i, EF (faceIdFB (faceIdRB baseVB ![1, 0]) cVB ε k (fun x => -((Y : ℂ) ^ 2 -
      (M : ℂ) ^ 2) * (NA X x - NA M x)) X Y i) :=
    fun i => faceId_efB_VB1 hε k X Y _ qA i
  have eB0 : ∀ i, EF (faceIdFB (faceIdRB baseVB ![0, 1]) cVB ε k (fun x => -((Y : ℂ) ^ 2 -
      (M : ℂ) ^ 2) * (NB X x - NB M x)) X Y i) :=
    fun i => faceId_efB_VB0 hε k X Y _ qB i
  have s1 := faceId_efi_sum_pieces2 _ _ eA1 eB1
  have s0 := faceId_efi_sum_pieces2 _ _ eA0 eB0
  have p1 := fun x => faceId_pieces_eq_triF0 (faceIdRB baseVB ![1, 0]) cVB hε.ne' k NA A0 A2
      (fun _ _ => rfl)
    h01 h02 h12 x
  have p0 := fun x => faceId_pieces_eq_triF0 (faceIdRB baseVB ![0, 1]) cVB hε.ne' k NB B0 B2
      (fun _ _ => rfl)
    h01 h02 h12 x
  have EA : ∀ i, EF fun x => ∑ j : Fin 4, if i ≤ j then
      faceIdFA (faceIdRB baseVB ![1, 0]) cVB ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NA M x) M X Y i j x else 0 := fun i =>
    EF.sum _ fun j _ => by
      by_cases h : i ≤ j
      · simpa [h] using eA1 i j h
      · simpa [h] using (EF.zero : EF fun _ => (0 : ℂ))
  have EA' : ∀ i, EF fun x => ∑ j : Fin 4, if i ≤ j then
      faceIdFA (faceIdRB baseVB ![0, 1]) cVB ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NB M x) M X Y i j x else 0 := fun i =>
    EF.sum _ fun j _ => by
      by_cases h : i ≤ j
      · simpa [h] using eA0 i j h
      · simpa [h] using (EF.zero : EF fun _ => (0 : ℂ))
  have T1 : EF (faceIdTriF (faceIdRB baseVB ![1, 0]) cVB ε k NA M X Y) :=
    ((EF.sum _ fun i _ => EA i).add (EF.sum _ fun i _ => eB1 i)).congr p1
  have T0 : EF (faceIdTriF (faceIdRB baseVB ![0, 1]) cVB ε k NB M X Y) :=
    ((EF.sum _ fun i _ => EA' i).add (EF.sum _ fun i _ => eB0 i)).congr p0
  refine ⟨?_, T1, T0⟩
  have hL1 : ∀ m x, 2⁻¹ * faceIdLapF 1 (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 -
      (M : ℂ) ^ 2) * Num m k ℓ μ ν) ![x, 0] = ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 -
          (M : ℂ) ^ 2) * NA m x :=
    fun m x => by rw [faceId_lapF_const_mul, mul_left_comm, hA]
  have hL0 : ∀ m x, 2⁻¹ * faceIdLapF 0 (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 -
      (M : ℂ) ^ 2) * Num m k ℓ μ ν) ![0, x] = ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 -
          (M : ℂ) ^ 2) * NB m x :=
    fun m x => by rw [faceId_lapF_const_mul, mul_left_comm, hB]
  have hM1 : ∀ x, 2⁻¹ * faceIdLapF 1 (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (Num X k ℓ μ ν - Num M k ℓ μ ν)) ![x, 0] =
      -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (NA X x - NA M x) := fun x => by
    rw [faceId_lapF_const_mul, faceId_lapF_sub, mul_left_comm, mul_sub, hA, hA]
  have hM0 : ∀ x, 2⁻¹ * faceIdLapF 0 (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (Num X k ℓ μ ν - Num M k ℓ μ ν)) ![0, x] =
      -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (NB X x - NB M x) := fun x => by
    rw [faceId_lapF_const_mul, faceId_lapF_sub, mul_left_comm, mul_sub, hB, hB]
  have hPsi : faceIdTriPsi baseVB cVB Num E4 M X Y 0 k μ ν ε =
      ((∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then QED.OneLoop.energyFirstIntegral
        (faceIdFA (faceIdRB baseVB ![1, 0]) cVB ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
            ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NA M x) M X Y i j) else 0) +
      ∑ i : Fin 4, QED.OneLoop.energyFirstIntegral
        (faceIdFB (faceIdRB baseVB ![1, 0]) cVB ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
            (NA X x - NA M x)) X Y i)) +
      ((∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then QED.OneLoop.energyFirstIntegral
        (faceIdFA (faceIdRB baseVB ![0, 1]) cVB ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
            ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NB M x) M X Y i j) else 0) +
      ∑ i : Fin 4, QED.OneLoop.energyFirstIntegral
        (faceIdFB (faceIdRB baseVB ![0, 1]) cVB ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
            (NB X x - NB M x)) X Y i)) := by
    simp only [faceIdTriPsi, faceId_psiP_VB, add_zero]
    have eA : ∀ i j : Fin 4, (if i ≤ j then faceIdPsi baseVB cVB (shA i j)
        (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ μ ν)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] 0 k ε
        else 0) =
        (if i ≤ j then QED.OneLoop.energyFirstIntegral
          (faceIdFA (faceIdRB baseVB ![1, 0]) cVB ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
              ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NA M x) M X Y i j) else 0) +
        (if i ≤ j then QED.OneLoop.energyFirstIntegral
          (faceIdFA (faceIdRB baseVB ![0, 1]) cVB ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
              ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * NB M x) M X Y i j) else 0) := fun i j => by
      split_ifs with hij
      · rw [faceId_psiA_VB Num k μ ν M X Y ε i j hij]
        congr 1 <;> congr 1 <;> funext x <;> simp only [faceIdFA]
        · rw [← hL1 M x]
        · rw [← hL0 M x]
      · simp
    have eB : ∀ i : Fin 4, faceIdPsi baseVB cVB (shB i)
        (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] 0 k ε =
        QED.OneLoop.energyFirstIntegral
          (faceIdFB (faceIdRB baseVB ![1, 0]) cVB ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
              (NA X x - NA M x)) X Y i) +
        QED.OneLoop.energyFirstIntegral
          (faceIdFB (faceIdRB baseVB ![0, 1]) cVB ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
              (NB X x - NB M x)) X Y i) := fun i => by
      rw [faceId_psiB_VB Num k μ ν M X Y ε i]
      congr 1 <;> congr 1 <;> funext x <;> simp only [faceIdFB]
      · rw [← hM1 x]
      · rw [← hM0 x]
    simp only [eA, eB, Finset.sum_add_distrib]
    ring
  rw [hPsi, s1, s0]
  congr 1 <;> congr 1 <;> funext x
  · exact p1 x
  · exact p0 x

end VB

end QED.GradedProof.RPi4

end
