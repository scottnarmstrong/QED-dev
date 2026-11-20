/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdTri
public import QED.GradedProof.RPi4FaceIdDDG

/-!
# (R-Π₄) step L6d3: the face integrals of a piece as energy-first integrals

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The face
integrals `faceIdPsi` of a merged piece are, for each face kind (decided by the integer cards),
one energy-first integral whose rest product runs over all lines with an `if` on the integer row:

* `faceId_prod_filter10`, `faceId_prod_filter01`: the real-row filter as an integer-row `if`;
* `faceId_psi_se`, `faceId_psi_vtx1`, `faceId_psi_vtx0`, `faceId_psi_zero`: the four kinds;
* `faceId_efi_zero_mul`, `faceId_efi_ite`, `faceId_efi_zero`: elementary energy-first integrals;
* `faceIdRB` (the rest lines of a face among the fermion lines) and evaluation helpers;
* `faceIdV`: the massless line denominator `p·p - iε` at the momentum `c_l k + x`, and
  `faceId_inv_propDenom_eq_G`: `(propDenom m ε p)⁻¹ = faceIdG true (p·p - iε) m²`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-- The massless denominator of the fermion line `l` of a face at loop momentum `x`. -/
noncomputable def faceIdV (c : Fin 5 → ℝ) (ε : ℝ) (k x : Fin 4 → ℝ) (l : Fin 4) : ℂ :=
  propDenom 0 ε (c l.castSucc • k + x)

theorem faceId_inv_propDenom_eq_G (m ε : ℝ) (p : Fin 4 → ℝ) :
    (propDenom m ε p)⁻¹ = faceIdG true (propDenom 0 ε p) ((m : ℂ) ^ 2) := by
  rw [VP2.propDenom_eq_add]
  rfl


theorem faceId_prod_filter10 {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (sh : Fin (m + 2) → Fin 5)
    (f : Fin (m + 1) → ℂ) :
    ∏ l ∈ Finset.univ.filter (fun l =>
        castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, 0]), f l =
      ∏ l, if base (sh l.castSucc) = ![1, 0] then f l else 1 := by
  rw [Finset.prod_filter]
  exact Finset.prod_congr rfl fun l _ => by simp only [castLoopMatrix_eq_row10_iff]

theorem faceId_prod_filter01 {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (sh : Fin (m + 2) → Fin 5)
    (f : Fin (m + 1) → ℂ) :
    ∏ l ∈ Finset.univ.filter (fun l =>
        castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![0, 1]), f l =
      ∏ l, if base (sh l.castSucc) = ![0, 1] then f l else 1 := by
  rw [Finset.prod_filter]
  exact Finset.prod_congr rfl fun l _ => by simp only [castLoopMatrix_eq_row01_iff]

theorem faceId_efi_zero_mul (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun x => 0 * F x) = 0 := by
  simp [QED.OneLoop.energyFirstIntegral]

theorem faceId_efi_mul_zero (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun x => F x * 0) = 0 := by
  simp [QED.OneLoop.energyFirstIntegral]

theorem faceId_efi_ite (p : Prop) [Decidable p] (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun x => if p then F x else 0) =
      if p then QED.OneLoop.energyFirstIntegral F else 0 := by
  split_ifs <;> simp [QED.OneLoop.energyFirstIntegral]

theorem faceId_efi_zero : QED.OneLoop.energyFirstIntegral (fun _ => (0 : ℂ)) = 0 := by
  simp [QED.OneLoop.energyFirstIntegral]

/-- The rest lines of a face of row `r` among the four fermion lines. -/
def faceIdRB (base : Fin 5 → Fin 2 → ℤ) (r : Fin 2 → ℤ) (l : Fin 4) : Bool :=
  decide (base l.castSucc = r)

theorem faceId_G_false (V s : ℂ) : faceIdG false V s = 1 := rfl

theorem faceId_W_false (V s : ℂ) : faceIdW false V s = 0 := rfl

theorem faceId_W_true (V s : ℂ) : faceIdW true V s = faceIdG true V s := rfl

theorem faceId_shA_castSucc (i j : Fin 4) (l : Fin 7) :
    shA i j l.castSucc = ![(0 : Fin 4).castSucc, (1 : Fin 4).castSucc, (2 : Fin 4).castSucc,
      (3 : Fin 4).castSucc, i.castSucc, j.castSucc, Fin.last 4] l := by
  fin_cases l <;> rfl

theorem faceId_shB_castSucc (i : Fin 4) (l : Fin 6) :
    shB i l.castSucc = ![(0 : Fin 4).castSucc, (1 : Fin 4).castSucc, (2 : Fin 4).castSucc,
      (3 : Fin 4).castSucc, i.castSucc, Fin.last 4] l := by
  fin_cases l <;> rfl

theorem faceId_c_castSucc (c : Fin 5 → ℝ) (l : Fin 4) :
    c l.castSucc = ![c 0, c 1, c 2, c 3] l := by
  fin_cases l <;> rfl

section Kinds

variable {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (sh : Fin (m + 2) → Fin 5)
  (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (Ms : Fin (m + 1) → ℝ) (β : ℝ) (k : Fin 4 → ℝ) (ε : ℝ)

/-- **A self-energy face at loop `1`.** -/
theorem faceId_psi_se (h1 : faceIdCard base sh ![1, 0] = 2)
    (h0 : faceIdCard base sh ![0, 1] ≠ 3) :
    faceIdPsi base c sh N Ms β k ε = QED.OneLoop.energyFirstIntegral fun x =>
      N ![x, (1 / 2 : ℝ) • (x + β • k)] * ∏ l : Fin (m + 1),
        if base (sh l.castSucc) = ![1, 0] then (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹
        else 1 := by
  simp only [faceIdPsi, faceIdPsi1, faceIdPsi0, h1, h0, ite_true, ite_false, add_zero,
    faceId_prod_filter10]

/-- **A vertex face at loop `1`.** -/
theorem faceId_psi_vtx1 (h1 : faceIdCard base sh ![1, 0] = 3)
    (h0 : faceIdCard base sh ![0, 1] ≠ 3) :
    faceIdPsi base c sh N Ms β k ε = QED.OneLoop.energyFirstIntegral fun x =>
      2⁻¹ * faceIdLapF 1 N ![x, 0] * ∏ l : Fin (m + 1),
        if base (sh l.castSucc) = ![1, 0] then (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹
        else 1 := by
  simp only [faceIdPsi, faceIdPsi1, faceIdPsi0, h1, h0, ite_true, ite_false, add_zero,
    faceId_prod_filter10, show (3 : ℕ) ≠ 2 by norm_num]
  rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  simp only [mul_assoc]

/-- **A vertex face at loop `0`.** -/
theorem faceId_psi_vtx0 (h2 : faceIdCard base sh ![1, 0] ≠ 2)
    (h3 : faceIdCard base sh ![1, 0] ≠ 3) (h0 : faceIdCard base sh ![0, 1] = 3) :
    faceIdPsi base c sh N Ms β k ε = QED.OneLoop.energyFirstIntegral fun x =>
      2⁻¹ * faceIdLapF 0 N ![0, x] * ∏ l : Fin (m + 1),
        if base (sh l.castSucc) = ![0, 1] then (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹
        else 1 := by
  simp only [faceIdPsi, faceIdPsi1, faceIdPsi0, h2, h3, h0, ite_true, ite_false, zero_add,
    faceId_prod_filter01]
  rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  simp only [mul_assoc]

/-- **No face.** -/
theorem faceId_psi_zero (h2 : faceIdCard base sh ![1, 0] ≠ 2)
    (h3 : faceIdCard base sh ![1, 0] ≠ 3) (h0 : faceIdCard base sh ![0, 1] ≠ 3) :
    faceIdPsi base c sh N Ms β k ε = 0 := by
  simp only [faceIdPsi, faceIdPsi1, faceIdPsi0, h2, h3, h0, ite_false, add_zero]

end Kinds

end QED.GradedProof.RPi4

end
