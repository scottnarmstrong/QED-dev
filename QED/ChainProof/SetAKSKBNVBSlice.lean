/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNVBAlg
public import QED.ChainProof.SetAKSKBNHom
public import QED.ChainProof.SetAKSKBPiece

/-!
# Set (a), stage B3: the `VB` integrand at a normalized inner vertex point

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). The class `VB` has the five lines `ℓ₀` (weight `a`), `ℓ₁ - k` (`x₁`), `ℓ₁` (`x₂`),
`k + ℓ₀` (`b`), `ℓ₀ - ℓ₁ + k` (the photon, `x₃`); the inner vertex is the triple `(x₁, x₂, x₃)`.
At a normalized inner point (`x₁ + x₂ + x₃ = 1`) the Symanzik data are `U = a + b + τ`,
`τ = x₃(1 - x₃)`, `A⁻¹ = U⁻¹ [[1, x₃], [x₃, a + b + x₃]]`, the loop shift `(-σ₀ k, σ₁ k)` and
`W = V + x₃u` the outer one-loop `D` with the inner vertex as a line of weight `τ`, momentum
`ℓ₀ + βk` (`β = x₂/(1 - x₃)`) and `m_v² + β²s = ((1 - x₃)M² + x₃u + x₂(1 - x₂)s)/τ`. So:

* **`ksN_slice_VB`**: `pieceF₅(a, x₁, x₂, b, x₃) = x₃ · K ksNGB M u x k (a, b, τ)` for every
  numerator with values `K ksNTB` and vanishing quartic contraction, where
* `ksNGB M u x k y = k²k³ [(y₂/τ) S⁻² (e/D² + (h₀₀ + 2x₃h₀₁ + x₃²h₁₁)/(2SD)) + S⁻² h₁₁/(2D)]`,
  `S = y₀ + y₁ + y₂`, `σ₀ = (y₁ + βy₂)/S`, `σ₁ = ((1 - x₂)y₀ + x₁y₁ + γy₂)/S` (`γ = x₁/(1 - x₃)`),
  `D = (y₀ + y₁)M² + y₁s + y₂(m_v² + β²s) - (y₁ + βy₂)²s/S`, with the moments `e`, `h` of
  `SetAKSKBNVBAlg`, is the outer one-loop integrand, homogeneous of degree `-3`
  (`ksN_ksNGB_smul`).

(Checked exactly with sympy, `setAKS10/n1_vb.py`, and numerically against `setAKS4/outerVB.py`,
`setAKS10/n2_vbnum.py`.)
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.GradedProof.WI2 (ehat)

/-- The moment `e` of the `VB` entry (`k²k³` removed). -/
noncomputable def ksNeB (M σ₀ σ₁ : ℝ) : ℝ :=
  16 * M ^ 2 * (σ₀ ^ 2 + 4 * σ₀ * σ₁ - 3 * σ₀ + σ₁ ^ 2 - 3 * σ₁ + 1)

/-- The moment `h₀₀` of the `VB` entry. -/
noncomputable def ksNh00 (σ₁ : ℝ) : ℝ := 32 * σ₁ * (σ₁ - 1)

/-- The moment `h₀₁` of the `VB` entry. -/
noncomputable def ksNh01 (σ₀ σ₁ : ℝ) : ℝ := 16 * (2 * σ₀ * σ₁ - σ₀ - σ₁)

/-- The moment `h₁₁` of the `VB` entry. -/
noncomputable def ksNh11 (σ₀ : ℝ) : ℝ := 32 * σ₀ * (σ₀ - 1)

/-- The shift fraction `σ₀` of the outer loop. -/
noncomputable def ksNSigB0 (x y : Fin 3 → ℝ) : ℝ :=
  (y 1 + x 1 / (1 - x 2) * y 2) / (y 0 + y 1 + y 2)

/-- The shift fraction `σ₁` of the inner loop. -/
noncomputable def ksNSigB1 (x y : Fin 3 → ℝ) : ℝ :=
  ((1 - x 1) * y 0 + x 0 * y 1 + x 0 / (1 - x 2) * y 2) / (y 0 + y 1 + y 2)

/-- The squared mass `m_v² + β²s` of the inner vertex as an outer line. -/
noncomputable def ksNEB (M u : ℝ) (x : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  ((1 - x 2) * M ^ 2 + x 2 * u + x 1 * (1 - x 1) * s) / (x 2 * (1 - x 2))

/-- The outer one-loop denominator `D` of `VB`. -/
noncomputable def ksNDB (M u : ℝ) (x : Fin 3 → ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (y 0 + y 1) * M ^ 2 + y 1 * Minkowski.dot k k + y 2 * ksNEB M u x (Minkowski.dot k k) -
    (y 1 + x 1 / (1 - x 2) * y 2) ^ 2 * Minkowski.dot k k / (y 0 + y 1 + y 2)

/-- **The outer one-loop integrand of `VB`** (`K` and the flavour weight removed): lines `ℓ₀`
(`y₀`), `k + ℓ₀` (`y₁`), the inner vertex (`y₂`), at the inner point `x`. -/
noncomputable def ksNGB (M u : ℝ) (x : Fin 3 → ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  k 2 * k 3 * (y 2 * (x 2 * (1 - x 2))⁻¹ * (((y 0 + y 1 + y 2) ^ 2)⁻¹ *
      (ksNeB M (ksNSigB0 x y) (ksNSigB1 x y) / ksNDB M u x k y ^ 2 +
        (ksNh00 (ksNSigB1 x y) + 2 * x 2 * ksNh01 (ksNSigB0 x y) (ksNSigB1 x y) +
          x 2 ^ 2 * ksNh11 (ksNSigB0 x y)) / (2 * (y 0 + y 1 + y 2) * ksNDB M u x k y))) +
    ((y 0 + y 1 + y 2) ^ 2)⁻¹ * ksNh11 (ksNSigB0 x y) / (2 * ksNDB M u x k y))

section Hom

variable (M u : ℝ) (x : Fin 3 → ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) {t : ℝ} (ht : 0 < t)
include ht

theorem ksN_ksNSigB0_smul : ksNSigB0 x (t • y) = ksNSigB0 x y := by
  simp only [ksNSigB0, Pi.smul_apply, smul_eq_mul]
  rw [show t * y 1 + x 1 / (1 - x 2) * (t * y 2) = t * (y 1 + x 1 / (1 - x 2) * y 2) by ring,
    show t * y 0 + t * y 1 + t * y 2 = t * (y 0 + y 1 + y 2) by ring,
    mul_div_mul_left _ _ ht.ne']

theorem ksN_ksNSigB1_smul : ksNSigB1 x (t • y) = ksNSigB1 x y := by
  simp only [ksNSigB1, Pi.smul_apply, smul_eq_mul]
  rw [show (1 - x 1) * (t * y 0) + x 0 * (t * y 1) + x 0 / (1 - x 2) * (t * y 2) =
      t * ((1 - x 1) * y 0 + x 0 * y 1 + x 0 / (1 - x 2) * y 2) by ring,
    show t * y 0 + t * y 1 + t * y 2 = t * (y 0 + y 1 + y 2) by ring,
    mul_div_mul_left _ _ ht.ne']

theorem ksN_ksNDB_smul (hy : ∀ i, 0 < y i) : ksNDB M u x k (t • y) = t * ksNDB M u x k y := by
  have hS : 0 < y 0 + y 1 + y 2 := by linarith [hy 0, hy 1, hy 2]
  simp only [ksNDB, Pi.smul_apply, smul_eq_mul]
  generalize x 1 / (1 - x 2) = β
  generalize ksNEB M u x (Minkowski.dot k k) = E
  field_simp

/-- **The outer integrand is homogeneous of degree `-3`.** -/
theorem ksN_ksNGB_smul (hy : ∀ i, 0 < y i) :
    ksNGB M u x k (t • y) = (t ^ 3)⁻¹ * ksNGB M u x k y := by
  have hS : 0 < y 0 + y 1 + y 2 := by linarith [hy 0, hy 1, hy 2]
  have hSt : (t • y) 0 + (t • y) 1 + (t • y) 2 = t * (y 0 + y 1 + y 2) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [ksNGB]
  rw [ksN_ksNSigB0_smul x y ht, ksN_ksNSigB1_smul x y ht, ksN_ksNDB_smul M u x k y ht hy, hSt]
  have hy2 : (t • y) 2 = t * y 2 := rfl
  rw [hy2]
  generalize ksNeB M (ksNSigB0 x y) (ksNSigB1 x y) = e
  generalize ksNh00 (ksNSigB1 x y) = h0
  generalize ksNh01 (ksNSigB0 x y) (ksNSigB1 x y) = h1
  generalize ksNh11 (ksNSigB0 x y) = h2
  generalize (x 2 * (1 - x 2))⁻¹ = c
  generalize ksNDB M u x k y = D
  by_cases hD : D = 0
  · simp [hD]
  · field_simp

end Hom

/-! ### The Symanzik data of `VB` -/

section Slice

variable (k : Fin 4 → ℝ) (z : Fin 5 → ℝ)

theorem ksN_symanzikMatrix_B :
    symanzikMatrix (castLoopMatrix baseVB) z =
      !![z 0 + z 3 + z 4, -z 4; -z 4, z 1 + z 2 + z 4] := by
  ext s t
  fin_cases s <;> fin_cases t <;>
    simp [symanzikMatrix, castLoopMatrix, baseVB, Fin.sum_univ_five]

theorem ksN_symanzikU_B :
    symanzikU (castLoopMatrix baseVB) z = (z 0 + z 3 + z 4) * (z 1 + z 2 + z 4) - z 4 ^ 2 := by
  rw [symanzikU, ksN_symanzikMatrix_B, Matrix.det_fin_two_of]
  ring

theorem ksN_inv_B :
    (symanzikMatrix (castLoopMatrix baseVB) z)⁻¹ =
      (symanzikU (castLoopMatrix baseVB) z)⁻¹ •
        !![z 1 + z 2 + z 4, z 4; z 4, z 0 + z 3 + z 4] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, symanzikU, Ring.inverse_eq_inv']
  rw [ksN_symanzikMatrix_B]
  congr 1
  ext s t
  fin_cases s <;> fin_cases t <;> simp

theorem ksN_symanzikVector_B :
    symanzikVector (castLoopMatrix baseVB) (fun l => cVB l • k) z =
      ![(z 3 + z 4) • k, -(z 1 + z 4) • k] := by
  funext s μ
  fin_cases s <;>
    simp [symanzikVector, Fin.sum_univ_five, castLoopMatrix, baseVB, cVB] <;> ring

theorem ksN_loopShift_B :
    loopShift (castLoopMatrix baseVB) (fun l => cVB l • k) z =
      ![((symanzikU (castLoopMatrix baseVB) z)⁻¹ *
          ((z 1 + z 2 + z 4) * (z 3 + z 4) - z 4 * (z 1 + z 4))) • k,
        ((symanzikU (castLoopMatrix baseVB) z)⁻¹ *
          (z 4 * (z 3 + z 4) - (z 0 + z 3 + z 4) * (z 1 + z 4))) • k] := by
  funext s μ
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply, ksN_inv_B]
  fin_cases s <;>
    simp [Fin.sum_univ_two, Fin.sum_univ_five, castLoopMatrix, baseVB, cVB] <;> ring

theorem ksN_symanzikV_B (M : ℝ) :
    symanzikV (castLoopMatrix baseVB) (fun l => cVB l • k) (ksBM5 fun _ => M) z =
      (z 0 + z 1 + z 2 + z 3) * M ^ 2 + (z 1 + z 3 + z 4) * Minkowski.dot k k -
        (symanzikU (castLoopMatrix baseVB) z)⁻¹ * ((z 1 + z 2 + z 4) * (z 3 + z 4) ^ 2 -
          2 * z 4 * (z 3 + z 4) * (z 1 + z 4) + (z 0 + z 3 + z 4) * (z 1 + z 4) ^ 2) *
          Minkowski.dot k k := by
  rw [symanzikV, ksN_symanzikVector_B, ksN_inv_B]
  simp [Fin.sum_univ_two, Fin.sum_univ_five, ksBM5, cVB, ksN_dot_smul_smul]
  ring

/-- **The `VB` integrand at a normalized inner point** is `x₃` times the outer one-loop
integrand at `(a, b, x₃(1 - x₃))`. -/
theorem ksN_slice_VB {Q : LoopQuartic} {K : ℂ} {M : ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTB M (ℓ 0) (ℓ 1) k : ℂ))
    (hC4 : ∀ A, Q.contractFour A = 0) (u : ℝ) {x₁ x₃ a b : ℝ} (h1 : 0 < x₁) (h3 : 0 < x₃)
    (h2 : 0 < 1 - x₁ - x₃) (ha : 0 < a) (hb : 0 < b) :
    pieceF 5 Q (castLoopMatrix baseVB) (fun l => cVB l • k) (ksBM5 fun _ => M) (Fin.last 4) u
        ![a, x₁, 1 - x₁ - x₃, b, x₃] =
      (x₃ : ℂ) * (K * (ksNGB M u ![x₁, 1 - x₁ - x₃, x₃] k ![a, b, x₃ * (1 - x₃)] : ℂ)) := by
  have hξ : 0 < 1 - x₃ := by linarith
  have hτ : 0 < x₃ * (1 - x₃) := mul_pos h3 hξ
  set z : Fin 5 → ℝ := ![a, x₁, 1 - x₁ - x₃, b, x₃] with hz
  have z0 : z 0 = a := rfl
  have z1 : z 1 = x₁ := rfl
  have z2 : z 2 = 1 - x₁ - x₃ := rfl
  have z3 : z 3 = b := rfl
  have z4 : z 4 = x₃ := rfl
  have hU0 : 0 < a + b + x₃ * (1 - x₃) := by positivity
  have hU : symanzikU (castLoopMatrix baseVB) z = a + b + x₃ * (1 - x₃) := by
    rw [ksN_symanzikU_B, z0, z1, z2, z3, z4]
    ring
  have hinv := ksN_inv_B z
  rw [hU, z0, z1, z2, z3, z4] at hinv
  have h00 : (symanzikMatrix (castLoopMatrix baseVB) z)⁻¹ 0 0 = (a + b + x₃ * (1 - x₃))⁻¹ := by
    rw [hinv]; simp; ring
  have h01 : (symanzikMatrix (castLoopMatrix baseVB) z)⁻¹ 0 1 =
      (a + b + x₃ * (1 - x₃))⁻¹ * x₃ := by
    rw [hinv]; simp
  have h11 : (symanzikMatrix (castLoopMatrix baseVB) z)⁻¹ 1 1 =
      1 + x₃ ^ 2 * (a + b + x₃ * (1 - x₃))⁻¹ := by
    rw [hinv]; simp
    field_simp
    ring
  set y : Fin 3 → ℝ := ![a, b, x₃ * (1 - x₃)] with hy
  set xv : Fin 3 → ℝ := ![x₁, 1 - x₁ - x₃, x₃] with hxv
  set σ₀ := ksNSigB0 xv y with hσ₀
  set σ₁ := ksNSigB1 xv y with hσ₁
  have hσ₀' : σ₀ = (a + b + x₃ * (1 - x₃))⁻¹ * (b + (1 - x₁ - x₃) * x₃) := by
    simp only [hσ₀, ksNSigB0, hy, hxv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
  have hσ₁' : σ₁ = (a + b + x₃ * (1 - x₃))⁻¹ * ((x₁ + x₃) * a + x₁ * b + x₁ * x₃) := by
    simp only [hσ₁, ksNSigB1, hy, hxv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hS : -loopShift (castLoopMatrix baseVB) (fun l => cVB l • k) z = ![-σ₀ • k, σ₁ • k] := by
    rw [ksN_loopShift_B, hU, z0, z1, z2, z3, z4, hσ₀', hσ₁']
    funext s μ
    fin_cases s
    · simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero]
      ring
    · simp only [Pi.neg_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      ring
  have hE : Q.evalC (loopComp (-loopShift (castLoopMatrix baseVB) (fun l => cVB l • k) z)) =
      K * ((k 2 * k 3 * ksNeB M σ₀ σ₁ : ℝ) : ℂ) := by
    rw [hS]
    have := congrFun hQ ![-σ₀ • k, σ₁ • k]
    simp only [LoopQuartic.eval] at this
    rw [this]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ksN_ksNTB_shift, ksNeB]
  have hC : Q.contractTwo (symanzikMatrix (castLoopMatrix baseVB) z)
      (loopComp (-loopShift (castLoopMatrix baseVB) (fun l => cVB l • k) z)) =
      K * ((k 2 * k 3 * ((a + b + x₃ * (1 - x₃))⁻¹ * ksNh00 σ₁ +
        2 * ((a + b + x₃ * (1 - x₃))⁻¹ * x₃) * ksNh01 σ₀ σ₁ +
        (1 + x₃ ^ 2 * (a + b + x₃ * (1 - x₃))⁻¹) * ksNh11 σ₀) : ℝ) : ℂ) := by
    rw [hS]
    exact ksN_contractTwo_ksNTB hQ (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose _ _)
      h00 h01 h11
  have hV := ksN_symanzikV_B k z M
  rw [hU, z0, z1, z2, z3, z4] at hV
  set W := (a + x₁ + (1 - x₁ - x₃) + b) * M ^ 2 + (x₁ + b + x₃) * Minkowski.dot k k -
    (a + b + x₃ * (1 - x₃))⁻¹ * ((x₁ + (1 - x₁ - x₃) + x₃) * (b + x₃) ^ 2 -
      2 * x₃ * (b + x₃) * (x₁ + x₃) + (a + b + x₃) * (x₁ + x₃) ^ 2) * Minkowski.dot k k +
    x₃ * u with hW
  have hD : ksNDB M u xv k y = W := by
    simp only [ksNDB, ksNEB, hy, hxv, hW, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hG : ksNGB M u xv k y = k 2 * k 3 *
      (((a + b + x₃ * (1 - x₃)) ^ 2)⁻¹ * (ksNeB M σ₀ σ₁ / W ^ 2 +
        (ksNh00 σ₁ + 2 * x₃ * ksNh01 σ₀ σ₁ + x₃ ^ 2 * ksNh11 σ₀) /
          (2 * (a + b + x₃ * (1 - x₃)) * W)) +
      ((a + b + x₃ * (1 - x₃)) ^ 2)⁻¹ * ksNh11 σ₀ / (2 * W)) := by
    have hy2 : y 2 * (x₃ * (1 - x₃))⁻¹ = 1 := mul_inv_cancel₀ hτ.ne'
    have hSy : y 0 + y 1 + y 2 = a + b + x₃ * (1 - x₃) := rfl
    have hx2 : xv 2 = x₃ := rfl
    simp only [ksNGB, ← hσ₀, ← hσ₁, hD, hy2, hSy, hx2, one_mul]
  have hzγ : z (Fin.last 4) = x₃ := rfl
  rw [hG]
  simp only [pieceF, paramAtV, ehat, hE, hC, hC4, hU, hzγ]
  have hVW : symanzikV (castLoopMatrix baseVB) (fun l => cVB l • k) (ksBM5 fun _ => M) z +
      x₃ * u = W := by rw [hV]
  rw [hVW]
  simp only [show (5 - 4).factorial = 1 from rfl, show (5 - 5).factorial = 1 from rfl,
    show 5 - 3 = 2 from rfl, show 5 - 4 = 1 from rfl, show 5 - 5 = 0 from rfl]
  by_cases hW0 : W = 0
  · simp [hW0]
  · have hW' : (W : ℂ) ≠ 0 := ofReal_ne_zero.2 hW0
    generalize a + b + x₃ * (1 - x₃) = U at hU0 ⊢
    have hU' : (U : ℂ) ≠ 0 := ofReal_ne_zero.2 hU0.ne'
    push_cast
    field_simp
    ring

end Slice

end QED.ChainProof.SetAKS

end
