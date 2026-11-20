/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdEFs

/-!
# (R-Π₄) step L6d3: the three-flavour face integrand and the sum of the pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.

* `faceIdTriF`: the three-flavour combination `H(M) + a H(X) + b H(Y)` of a face integrand
  `H(m) = N(m) ∏_rest (p_l² + m² - iε)⁻¹` (Pauli–Villars coefficients `triA`, `triB`);
* **`faceId_pieces_eq_triF`**: for a numerator `N(m) = E₀ + m² E₂ + m⁴ E₄`, the sum of the face
  integrands of the fifteen pieces (`faceIdFA`, `faceIdFB`, `faceIdFP` with the numerators of
  `faceIdTriPsi`) is `faceIdTriF` plus the defect of the padded piece, `iε` times its integrand
  at the numerator `(X² - M²)(Y² - M²) E₄` (from `faceId_tri_g`: the padded numerator carries
  `p₀² + Y²` where the line factor has `p₀² + Y² - iε`);
* `faceId_V_add_ne`, `faceId_isLoopPoly_mid`: substitution of the face midpoint `(x, (x + β k)/2)`;
* `faceId_efi_sum`, `faceId_efi_sum_pieces`: the energy-first integral of the sum of the pieces.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-- **The three-flavour combination of a face integrand.** -/
noncomputable def faceIdTriF (b : Fin 4 → Bool) (c : Fin 5 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ)
    (N : ℝ → (Fin 4 → ℝ) → ℂ) (M X Y : ℝ) (x : Fin 4 → ℝ) : ℂ :=
  N M x * (∏ l, faceIdG (b l) (faceIdV c ε k x l) ((M : ℂ) ^ 2)) +
    ((triA M X Y : ℝ) : ℂ) * (N X x * ∏ l, faceIdG (b l) (faceIdV c ε k x l) ((X : ℂ) ^ 2)) +
    ((triB M X Y : ℝ) : ℂ) * (N Y x * ∏ l, faceIdG (b l) (faceIdV c ε k x l) ((Y : ℂ) ^ 2))

theorem faceId_efi_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, EF (F i)) :
    QED.OneLoop.energyFirstIntegral (fun x => ∑ i ∈ s, F i x) =
      ∑ i ∈ s, QED.OneLoop.energyFirstIntegral (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QED.OneLoop.energyFirstIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [efi_add (h a (Finset.mem_insert_self a s))
      (EF.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem faceId_isLoopPoly_mid {n : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : IsLoopPoly 2 n F)
    (β : ℝ) (k : Fin 4 → ℝ) :
    IsLoopPoly 2 n fun ℓ => F ![ℓ 0, (1 / 2 : ℝ) • (ℓ 0 + β • k)] := by
  refine hF.comp (g := fun ℓ => ![ℓ 0, (1 / 2 : ℝ) • (ℓ 0 + β • k)]) fun s ν => ?_
  fin_cases s
  · simpa using IsLoopPoly.coord (L := 2) (n := 1) 0 ν le_rfl
  · have h : (fun ℓ : Fin 2 → Fin 4 → ℝ =>
        (((![ℓ 0, (1 / 2 : ℝ) • (ℓ 0 + β • k)] : Fin 2 → Fin 4 → ℝ) 1 ν : ℝ) : ℂ)) =
        fun ℓ => (1 / 2 : ℂ) * ((ℓ 0 ν : ℝ) : ℂ) + ((1 / 2 * (β * k ν) : ℝ) : ℂ) := by
      funext ℓ
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul]
      push_cast
      ring
    simp only [Fin.mk_one, Fin.isValue]
    rw [h]
    exact ((IsLoopPoly.coord 0 ν le_rfl).const_mul _).add (IsLoopPoly.const _)

/-- **The energy-first integral of the fifteen pieces** in the uniform form, all integrable. -/
theorem faceId_efi_sum_pieces (FA : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (FB : Fin 4 → (Fin 4 → ℝ) → ℂ) (FP : (Fin 4 → ℝ) → ℂ)
    (hA : ∀ i j, i ≤ j → EF (FA i j)) (hB : ∀ i, EF (FB i)) (hP : EF FP) :
    ((∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then QED.OneLoop.energyFirstIntegral (FA i j) else 0) +
        ∑ i : Fin 4, QED.OneLoop.energyFirstIntegral (FB i) +
        QED.OneLoop.energyFirstIntegral FP =
      QED.OneLoop.energyFirstIntegral fun x =>
        (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then FA i j x else 0) + ∑ i : Fin 4, FB i x +
          FP x) ∧
    EF fun x => (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then FA i j x else 0) +
      ∑ i : Fin 4, FB i x + FP x := by
  have eA : ∀ i j, EF fun x => if i ≤ j then FA i j x else 0 := fun i j => by
    by_cases h : i ≤ j
    · simpa [h] using hA i j h
    · simpa [h] using (EF.zero : EF fun _ => (0 : ℂ))
  have eAs : ∀ i, EF fun x => ∑ j : Fin 4, if i ≤ j then FA i j x else 0 := fun i =>
    EF.sum _ fun j _ => eA i j
  have eAA : EF fun x => ∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then FA i j x else 0 :=
    EF.sum _ fun i _ => eAs i
  have eBB : EF fun x => ∑ i : Fin 4, FB i x := EF.sum _ fun i _ => hB i
  refine ⟨?_, (eAA.add eBB).add hP⟩
  rw [efi_add (eAA.add eBB) hP, efi_add eAA eBB,
    faceId_efi_sum _ fun i _ => eAs i,
    faceId_efi_sum _ fun i _ => hB i]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [faceId_efi_sum _ fun j _ => eA i j]
  exact Finset.sum_congr rfl fun j _ => (faceId_efi_ite _ _).symm

theorem faceId_V_add_ne {c : Fin 5 → ℝ} {ε : ℝ} (hε : ε ≠ 0) (k x : Fin 4 → ℝ) (m : ℝ)
    (l : Fin 4) : faceIdV c ε k x l + (m : ℂ) ^ 2 ≠ 0 := by
  rw [faceIdV, ← VP2.propDenom_eq_add]
  exact propDenom_ne_zero hε _

/-- **The fifteen pieces of a face are the three-flavour combination** (pointwise, `ε ≠ 0`). -/
theorem faceId_pieces_eq_triF (b : Fin 4 → Bool) (hb0 : b 0 = true) (c : Fin 5 → ℝ) {ε : ℝ}
    (hε : ε ≠ 0) (k : Fin 4 → ℝ) (N : ℝ → (Fin 4 → ℝ) → ℂ) (E0 E2 : (Fin 4 → ℝ) → ℂ) (E4 : ℂ)
    (hN : ∀ m x, N m x = E0 x + (m : ℂ) ^ 2 * E2 x + ((m : ℂ) ^ 2) ^ 2 * E4) {M X Y : ℝ}
    (h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0) (h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0)
    (h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0) (x : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then faceIdFA b c ε k (fun x =>
        ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * N M x) M X Y i j x
      else 0) +
      ∑ i : Fin 4, faceIdFB b c ε k (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (N X x - N M x))
        X Y i x +
      faceIdFP b c ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 *
        (faceIdV c ε k x 0 + (Y : ℂ) ^ 2 + ε * I)) Y x =
    faceIdTriF b c ε k N M X Y x + ε * I * faceIdFP b c ε k
      (fun _ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4) Y x := by
  have T := faceId_tri_g b (faceIdV c ε k x) (E0 x) (E2 x) E4 ((M : ℂ) ^ 2) ((X : ℂ) ^ 2)
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
        (E0 x + (M : ℂ) ^ 2 * E2 x + ((M : ℂ) ^ 2) ^ 2 * E4) *
          ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l)
            (if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
          faceIdW (b i) (faceIdV c ε k x i) ((X : ℂ) ^ 2) *
          faceIdW (b j) (faceIdV c ε k x j) ((Y : ℂ) ^ 2)) else 0 := fun i j => by
    split_ifs
    simp only [faceIdFA, hN]
    ring
  have hB' : ∀ i : Fin 4, faceIdFB b c ε k
      (fun x => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (N X x - N M x)) X Y i x =
      -(((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
        (E2 x + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4) *
        ((∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l)
          (if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)) *
          faceIdW (b i) (faceIdV c ε k x i) ((Y : ℂ) ^ 2)) := fun i => by
    simp only [faceIdFB, hN]
    ring
  simp only [hS, hB']
  have hW := faceId_V_add_ne (c := c) hε k x Y 0
  have hP : faceIdFP b c ε k (fun x => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 * (faceIdV c ε k x 0 + (Y : ℂ) ^ 2 + ε * I)) Y x =
      ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 *
        ∏ l : Fin 4, faceIdG (b l) (faceIdV c ε k x l) ((Y : ℂ) ^ 2) +
      ε * I * faceIdFP b c ε k
        (fun _ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4) Y x := by
    simp only [faceIdFP, hb0, faceIdW, ite_true]
    field_simp
  rw [hP, ← add_assoc, ← T]
  simp only [faceIdTriF, hN, hA, hB]

end QED.GradedProof.RPi4

end
