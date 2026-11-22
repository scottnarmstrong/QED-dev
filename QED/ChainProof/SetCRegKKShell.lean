/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKPinch
public import QED.TwoLoop.PauliZeroLimitCurve

/-!
# Set (c): the terms of the longitudinal integrand that vanish on shell

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
A Ward identity at an end vertex of the chain (`QED.ChainProof.SetCMain.kOpen_ward_out`,
`kOpen_ward_in`) leaves the matrix `2m - A(p')` next to the outgoing spinor, or `A(p) - 2m` next
to the incoming one, `A(k) = m - k̸`. The Pauli weights contract a vertex matrix `V` as
`tr(A(p') V A(p) Γ)`, and `A(p') (2m - A(p')) = (p'·p' + m²) = 0`,
`(A(p) - 2m) A(p) = -(p·p + m²) = 0` on shell. So every such term has zero Pauli-weighted sum,
pointwise in the loop momenta: the terms `0A`, `6A`, `10A` of the classes with the Ward
identities at both ends, and the end terms of the second Ward step.

* `electronNumerator_mul_out`, `inn_mul_electronNumerator`: the on-shell products;
* **`pauliWt_sum_out_mul`**, **`pauliWt_sum_mul_inn`**: `∑ᵢⱼ w_{μij} ((2m - A(p')) B)ᵢⱼ = 0`,
  `∑ᵢⱼ w_{μij} (B (A(p) - 2m))ᵢⱼ = 0`;
* `kOpen_eq_X_mul`, `kOpen_eq_Y_mul`, `kOpen_eq_mul_X`, `kOpen_eq_mul_Y`: an end vertex of the
  chain factors out;
* **`pauliWt_sum_kNum_out`**, **`pauliWt_sum_kNum_inn`**, `pauliWt_sum_kNum_Y_out`,
  `pauliWt_sum_kNum_X_inn`: the numerator terms with an on-shell end vertex.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params)
open QED.Dirac (gamma slash gammaLower)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit (pauliWt trace_mul_mul_eq_sum)
open QED.TwoLoop.Bridge (electronNumerator)

/-! ### The on-shell products -/

theorem electronNumerator_mul_self' (m : ℝ) (k : Fin 4 → ℝ) :
    electronNumerator m k * electronNumerator m k =
      (2 * (m : ℂ)) • electronNumerator m k -
        ((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hs := QED.Dirac.slash_mul_slash k
  simp only [electronNumerator, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs]
  push_cast
  module

/-- `A(p') (2m - A(p')) = 0` on shell. -/
theorem electronNumerator_mul_out {m : ℝ} {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) :
    electronNumerator m p' * ((2 * (m : ℂ)) • 1 - electronNumerator m p') = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, electronNumerator_mul_self', hp']
  simp

/-- `(A(p) - 2m) A(p) = 0` on shell. -/
theorem inn_mul_electronNumerator {m : ℝ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) :
    (electronNumerator m p - (2 * (m : ℂ)) • 1) * electronNumerator m p = 0 := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, electronNumerator_mul_self', hp]
  simp

/-! ### The Pauli-weighted sums -/

theorem pauliWt_sum_eq (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (V : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * V i j =
      (m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) *
          trace (electronNumerator m p' * V * (electronNumerator m p * gammaLower μ)) +
        ((Minkowski.dot (p' - p) (p' - p) : ℂ) - 2 * (m : ℂ) ^ 2) *
          ((Minkowski.lower (p' + p) μ : ℝ) : ℂ) *
          trace (electronNumerator m p' * V * electronNumerator m p) := by
  rw [trace_mul_mul_eq_sum, trace_mul_mul_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pauliWt, Matrix.mul_assoc]
  ring

/-- **A vertex matrix starting with `2m - A(p')` has zero Pauli-weighted sum** on shell. -/
theorem pauliWt_sum_out_mul {m : ℝ} {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (p : Fin 4 → ℝ) (μ : Fin 4) (B : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * (((2 * (m : ℂ)) • 1 - electronNumerator m p') * B) i j =
      0 := by
  rw [pauliWt_sum_eq]
  simp only [← Matrix.mul_assoc, electronNumerator_mul_out hp', Matrix.zero_mul,
    Matrix.trace_zero, mul_zero, add_zero]

/-- **A vertex matrix ending with `A(p) - 2m` has zero Pauli-weighted sum** on shell. -/
theorem pauliWt_sum_mul_inn {m : ℝ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2)
    (p' : Fin 4 → ℝ) (μ : Fin 4) (B : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * (B * (electronNumerator m p - (2 * (m : ℂ)) • 1)) i j =
      0 := by
  rw [pauliWt_sum_eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (electronNumerator m p - (2 * (m : ℂ)) • 1), inn_mul_electronNumerator hp]
  simp

/-! ### An end vertex factors out of the chain -/

section Ends

variable {π : Equiv.Perm (Fin 5)} (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ)
  (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

theorem kOpen_eq_X_mul (hπ : π 1 = 4) : ∃ B, kOpen π μ X Y E = X * B := by
  have h : π.symm 4 = 1 := (Equiv.symm_apply_eq _).2 hπ.symm
  refine ⟨∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (E 3 * ![gamma μ, X, Y, gamma z, gamma z]
    (π.symm 3) * E 2 * ![gamma μ, X, Y, gamma z, gamma z] (π.symm 2) * E 1 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 1) * E 0 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 0)), ?_⟩
  simp only [kOpen, ocW_eq, h, Finset.mul_sum, Matrix.mul_smul, Matrix.mul_assoc]
  rfl

theorem kOpen_eq_Y_mul (hπ : π 2 = 4) : ∃ B, kOpen π μ X Y E = Y * B := by
  have h : π.symm 4 = 2 := (Equiv.symm_apply_eq _).2 hπ.symm
  refine ⟨∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (E 3 * ![gamma μ, X, Y, gamma z, gamma z]
    (π.symm 3) * E 2 * ![gamma μ, X, Y, gamma z, gamma z] (π.symm 2) * E 1 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 1) * E 0 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 0)), ?_⟩
  simp only [kOpen, ocW_eq, h, Finset.mul_sum, Matrix.mul_smul, Matrix.mul_assoc]
  rfl

theorem kOpen_eq_mul_X (hπ : π 1 = 0) : ∃ B, kOpen π μ X Y E = B * X := by
  have h : π.symm 0 = 1 := (Equiv.symm_apply_eq _).2 hπ.symm
  refine ⟨∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (![gamma μ, X, Y, gamma z, gamma z]
    (π.symm 4) * E 3 * ![gamma μ, X, Y, gamma z, gamma z] (π.symm 3) * E 2 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 2) * E 1 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 1) * E 0), ?_⟩
  simp only [kOpen, ocW_eq, h, Finset.sum_mul, Matrix.smul_mul]
  rfl

theorem kOpen_eq_mul_Y (hπ : π 2 = 0) : ∃ B, kOpen π μ X Y E = B * Y := by
  have h : π.symm 0 = 2 := (Equiv.symm_apply_eq _).2 hπ.symm
  refine ⟨∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (![gamma μ, X, Y, gamma z, gamma z]
    (π.symm 4) * E 3 * ![gamma μ, X, Y, gamma z, gamma z] (π.symm 3) * E 2 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 2) * E 1 *
    ![gamma μ, X, Y, gamma z, gamma z] (π.symm 1) * E 0), ?_⟩
  simp only [kOpen, ocW_eq, h, Finset.sum_mul, Matrix.smul_mul]
  rfl

end Ends

/-! ### The numerator terms with an on-shell end vertex -/

section Terms

variable {π : Equiv.Perm (Fin 5)} (c : Class5) (σ : Fin 8) {m : ℝ} {p p' : Fin 4 → ℝ}
  (K : Finset (Fin 4)) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ)

/-- **The term with `2m - A(p')` at the Ward vertex `π 1 = 4`** has zero Pauli-weighted sum. -/
theorem pauliWt_sum_kNum_out (hπ : π 1 = 4) (hp' : Minkowski.dot p' p' = -m ^ 2) (Y : KSlot) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * kNum π c σ m p p' .out Y K μ ℓ i j = 0 := by
  obtain ⟨B, hB⟩ := kOpen_eq_X_mul μ (kSlotM c σ m p p' .out ℓ) (kSlotM c σ m p p' Y ℓ)
    (fun j => kEK c σ m p p' K j ℓ) hπ
  rw [kNum, hB]
  exact pauliWt_sum_out_mul hp' p μ B

/-- **The term with `A(p) - 2m` at the other end `π 2 = 0`** has zero Pauli-weighted sum. -/
theorem pauliWt_sum_kNum_inn (hπ : π 2 = 0) (hp : Minkowski.dot p p = -m ^ 2) (X : KSlot) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * kNum π c σ m p p' X .inn K μ ℓ i j = 0 := by
  obtain ⟨B, hB⟩ := kOpen_eq_mul_Y μ (kSlotM c σ m p p' X ℓ) (kSlotM c σ m p p' .inn ℓ)
    (fun j => kEK c σ m p p' K j ℓ) hπ
  rw [kNum, hB]
  exact pauliWt_sum_mul_inn hp p' μ B

/-- The term with `2m - A(p')` at the other end `π 2 = 4` has zero Pauli-weighted sum. -/
theorem pauliWt_sum_kNum_Y_out (hπ : π 2 = 4) (hp' : Minkowski.dot p' p' = -m ^ 2) (X : KSlot) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * kNum π c σ m p p' X .out K μ ℓ i j = 0 := by
  obtain ⟨B, hB⟩ := kOpen_eq_Y_mul μ (kSlotM c σ m p p' X ℓ) (kSlotM c σ m p p' .out ℓ)
    (fun j => kEK c σ m p p' K j ℓ) hπ
  rw [kNum, hB]
  exact pauliWt_sum_out_mul hp' p μ B

/-- The term with `A(p) - 2m` at the Ward vertex `π 1 = 0` has zero Pauli-weighted sum. -/
theorem pauliWt_sum_kNum_X_inn (hπ : π 1 = 0) (hp : Minkowski.dot p p = -m ^ 2) (Y : KSlot) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * kNum π c σ m p p' .inn Y K μ ℓ i j = 0 := by
  obtain ⟨B, hB⟩ := kOpen_eq_mul_X μ (kSlotM c σ m p p' .inn ℓ) (kSlotM c σ m p p' Y ℓ)
    (fun j => kEK c σ m p p' K j ℓ) hπ
  rw [kNum, hB]
  exact pauliWt_sum_mul_inn hp p' μ B

end Terms

end QED.ChainProof.SetCRegDisp

end
