/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNAlg
public import QED.ChainProof.SetAKSKBNHom

/-!
# Set (a), stage B3: the merged `VA` integrand at the Cheng–Wu slice

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). The class `VA` with its two equal lines `ℓ₀` merged has the four lines `ℓ₀` (weight
`z₀`), `ℓ₁` (the inner fermion), `k + ℓ₀`, `ℓ₀ - ℓ₁` (the photon): rows `ksNBaseA`, shifts
`(0, 0, k, 0)`, masses `(M, M, M, 0)`. At the Cheng–Wu slice `z = (a, x, b, 1 - x)` (inner pair on
the simplex) the Symanzik data are `U = a + b + xξ` (`ξ = 1 - x`),
`A⁻¹ = U⁻¹ [[1, ξ], [ξ, a + b + ξ]]`, the loop shift `(σ k, ξ σ k)` with `σ = b/U`, and
`W = V + ξu` is the outer one-loop `V` with the inner loop as a line of weight `xξ` and mass
`m_x² = M²/ξ + u/x`. So:

* **`ksN_slice_VA`**: `z₀ pieceF₅(z) = ξ · K ksNGA M u x k (a, b, xξ)` for every numerator with
  values `K ksNTA` and vanishing quartic contraction, where
* `ksNGA M u x k y = k²k³ y₀ [S⁻² a₀(σ)/D² + 2 S⁻³ a₁(σ)/D]`, `S = y₀ + y₁ + y₂`, `σ = y₁/S`,
  `D = y₁(S - y₁)s/S + (y₀ + y₁)M² + y₂ m_x²` (`s = k·k`) is the outer one-loop integrand,
  homogeneous of degree `-3` (`ksN_ksNGA_smul`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4
open QED.GradedProof.WI2 (ehat)

/-- The loop rows of the merged `VA` data: `ℓ₀`, `ℓ₁`, `ℓ₀`, `ℓ₀ - ℓ₁`. -/
def ksNBaseA : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![1, 0], ![1, -1]]

/-- The line shifts of the merged `VA` data: `k` on line `2`. -/
def ksNppA (k : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := ![0, 0, k, 0]

/-- The masses of the merged `VA` data. -/
def ksNMA (M : ℝ) : Fin 4 → ℝ := ![M, M, M, 0]

/-- **The outer one-loop integrand of `VA`** (`K` and the flavour weight removed): lines `ℓ₀`
(merged, `y₀`), `k + ℓ₀` (`y₁`), the inner loop (`y₂`). -/
noncomputable def ksNGA (M u x : ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  k 2 * k 3 * y 0 *
    (((y 0 + y 1 + y 2) ^ 2)⁻¹ * (16 * (y 1 / (y 0 + y 1 + y 2)) * (1 - y 1 / (y 0 + y 1 + y 2)) *
        (4 * M ^ 2 - (1 - x) * M ^ 2 +
          (1 - x) * (y 1 / (y 0 + y 1 + y 2)) ^ 2 * Minkowski.dot k k)) /
      (y 1 * (y 0 + y 2) * Minkowski.dot k k / (y 0 + y 1 + y 2) + (y 0 + y 1) * M ^ 2 +
        y 2 * (M ^ 2 / (1 - x) + u / x)) ^ 2 +
     2 * ((y 0 + y 1 + y 2) ^ 3)⁻¹ *
        (-8 * (1 - x) * (y 1 / (y 0 + y 1 + y 2)) * (4 * (y 1 / (y 0 + y 1 + y 2)) - 3)) /
      (y 1 * (y 0 + y 2) * Minkowski.dot k k / (y 0 + y 1 + y 2) + (y 0 + y 1) * M ^ 2 +
        y 2 * (M ^ 2 / (1 - x) + u / x)))

/-- **The outer integrand is homogeneous of degree `-3`.** -/
theorem ksN_ksNGA_smul (M u x : ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) (hy : ∀ i, 0 < y i)
    {t : ℝ} (ht : 0 < t) : ksNGA M u x k (t • y) = (t ^ 3)⁻¹ * ksNGA M u x k y := by
  have hS : 0 < y 0 + y 1 + y 2 := by linarith [hy 0, hy 1, hy 2]
  set D := y 1 * (y 0 + y 2) * Minkowski.dot k k / (y 0 + y 1 + y 2) + (y 0 + y 1) * M ^ 2 +
    y 2 * (M ^ 2 / (1 - x) + u / x) with hD
  have hDt : t * y 1 * (t * y 0 + t * y 2) * Minkowski.dot k k / (t * y 0 + t * y 1 + t * y 2) +
      (t * y 0 + t * y 1) * M ^ 2 + t * y 2 * (M ^ 2 / (1 - x) + u / x) = t * D := by
    rw [hD]
    field_simp
  have hσ : t * y 1 / (t * y 0 + t * y 1 + t * y 2) = y 1 / (y 0 + y 1 + y 2) := by
    field_simp
  have hSt : t * y 0 + t * y 1 + t * y 2 = t * (y 0 + y 1 + y 2) := by ring
  simp only [ksNGA, Pi.smul_apply, smul_eq_mul]
  rw [hDt, hσ, hSt]
  rw [← hD]
  by_cases h0 : D = 0
  · simp [h0]
  · field_simp

section Slice

variable (k : Fin 4 → ℝ) (z : Fin 4 → ℝ)

/-- The Symanzik matrix of the merged `VA` data. -/
theorem ksN_symanzikMatrix_A :
    symanzikMatrix (castLoopMatrix ksNBaseA) z = !![z 0 + z 2 + z 3, -z 3; -z 3, z 1 + z 3] := by
  ext s t
  fin_cases s <;> fin_cases t <;> simp [symanzikMatrix, castLoopMatrix, ksNBaseA, Fin.sum_univ_four]

theorem ksN_symanzikU_A :
    symanzikU (castLoopMatrix ksNBaseA) z = (z 0 + z 2 + z 3) * (z 1 + z 3) - z 3 ^ 2 := by
  rw [symanzikU, ksN_symanzikMatrix_A, Matrix.det_fin_two_of]
  ring

theorem ksN_inv_A :
    (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ =
      (symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ • !![z 1 + z 3, z 3; z 3, z 0 + z 2 + z 3] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, symanzikU, Ring.inverse_eq_inv']
  rw [ksN_symanzikMatrix_A]
  congr 1
  ext s t
  fin_cases s <;> fin_cases t <;> simp

theorem ksN_loopShift_A :
    loopShift (castLoopMatrix ksNBaseA) (ksNppA k) z =
      ![((symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ * (z 1 + z 3) * z 2) • k,
        ((symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ * z 3 * z 2) • k] := by
  funext s μ
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply, ksN_inv_A]
  fin_cases s <;>
    simp [Fin.sum_univ_two, Fin.sum_univ_four, castLoopMatrix, ksNBaseA, ksNppA] <;> ring

theorem ksN_symanzikV_A (M : ℝ) :
    symanzikV (castLoopMatrix ksNBaseA) (ksNppA k) (ksNMA M) z =
      (z 0 + z 1 + z 2) * M ^ 2 + z 2 * Minkowski.dot k k -
        (symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ * (z 1 + z 3) * z 2 ^ 2 *
          Minkowski.dot k k := by
  have hB : symanzikVector (castLoopMatrix ksNBaseA) (ksNppA k) z = ![z 2 • k, 0] := by
    funext s μ
    fin_cases s <;> simp [symanzikVector, Fin.sum_univ_four, castLoopMatrix, ksNBaseA, ksNppA]
  rw [symanzikV, hB, ksN_inv_A]
  simp [Fin.sum_univ_two, Fin.sum_univ_four, ksNMA, ksNppA, Minkowski.dot]
  ring

/-- **The merged `VA` integrand at the Cheng–Wu slice** is `ξ` times the outer one-loop
integrand at `(a, b, xξ)`. -/
theorem ksN_slice_VA {Q : LoopQuartic} {K : ℂ} {M : ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTA M (ℓ 0) (ℓ 1) k : ℂ))
    (hC4 : ∀ A, Q.contractFour A = 0) (u : ℝ) {x a b : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    (a : ℂ) * pieceF 5 Q (castLoopMatrix ksNBaseA) (ksNppA k) (ksNMA M) 3 u ![a, x, b, 1 - x] =
      ((1 - x : ℝ) : ℂ) * (K * (ksNGA M u x k ![a, b, x * (1 - x)] : ℂ)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hξ : 0 < 1 - x := by linarith
  set z : Fin 4 → ℝ := ![a, x, b, 1 - x] with hz
  set U := a + b + x * (1 - x) with hUdef
  have hU0 : 0 < U := by positivity
  have hU : symanzikU (castLoopMatrix ksNBaseA) z = U := by
    rw [ksN_symanzikU_A]
    simp [hz, hUdef]
    ring
  have hinv := ksN_inv_A z
  rw [hU] at hinv
  have h00 : (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ 0 0 = U⁻¹ := by
    rw [hinv]; simp [hz]
  have h01 : (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ 0 1 = (1 - x) * U⁻¹ := by
    rw [hinv]; simp [hz]; ring
  have h11 : (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ 1 1 = (a + b + (1 - x)) * U⁻¹ := by
    rw [hinv]; simp [hz]; ring
  set σ := U⁻¹ * b with hσ
  have hS : -loopShift (castLoopMatrix ksNBaseA) (ksNppA k) z = ![-σ • k, -((1 - x) * σ) • k] := by
    have z2 : z 2 = b := rfl
    have z3 : z 3 = 1 - x := rfl
    have z1 : z 1 = x := rfl
    rw [ksN_loopShift_A, hU, z1, z2, z3]
    funext s μ
    fin_cases s
    · simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hσ]
      ring
    · simp only [Pi.neg_apply, Fin.mk_one, Matrix.cons_val_one]
      simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      rw [hσ]
      ring
  have hE : Q.evalC (loopComp (-loopShift (castLoopMatrix ksNBaseA) (ksNppA k) z)) =
      K * ((k 2 * k 3 * (16 * σ * (1 - σ) * (4 * M ^ 2 - (1 - x) * M ^ 2 +
        (1 - x) * σ ^ 2 * Minkowski.dot k k)) : ℝ) : ℂ) := by
    rw [hS]
    have := congrFun hQ ![-σ • k, -((1 - x) * σ) • k]
    simp only [LoopQuartic.eval] at this
    rw [this]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ksN_ksNTA_shift]
  have hC : Q.contractTwo (symanzikMatrix (castLoopMatrix ksNBaseA) z)
      (loopComp (-loopShift (castLoopMatrix ksNBaseA) (ksNppA k) z)) =
      K * ((4 * k 2 * k 3 * (-8 * (1 - x) * σ * (4 * σ - 3)) * U⁻¹ : ℝ) : ℂ) := by
    rw [hS]
    exact ksN_contractTwo_ksNTA hQ (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose _ _)
      h00 h01 h11
  have hV := ksN_symanzikV_A k z M
  rw [hU] at hV
  set W := (a + x + b) * M ^ 2 + b * Minkowski.dot k k -
    U⁻¹ * (x + (1 - x)) * b ^ 2 * Minkowski.dot k k + (1 - x) * u with hW
  have hG : ksNGA M u x k ![a, b, x * (1 - x)] = k 2 * k 3 * a *
      ((U ^ 2)⁻¹ * (16 * σ * (1 - σ) * (4 * M ^ 2 - (1 - x) * M ^ 2 +
        (1 - x) * σ ^ 2 * Minkowski.dot k k)) / W ^ 2 +
       2 * (U ^ 3)⁻¹ * (-8 * (1 - x) * σ * (4 * σ - 3)) / W) := by
    have hbU : b / (a + b + x * (1 - x)) = σ := by rw [hσ, ← hUdef, div_eq_inv_mul]
    have hD : b * (a + x * (1 - x)) * Minkowski.dot k k / (a + b + x * (1 - x)) +
        (a + b) * M ^ 2 + x * (1 - x) * (M ^ 2 / (1 - x) + u / x) = W := by
      rw [hW, ← hUdef]
      field_simp
      ring
    simp only [ksNGA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ← hUdef] at hbU hD ⊢
    rw [hbU, hD]
  have hzγ : z 3 = 1 - x := rfl
  have hz0 : z 0 = a := rfl
  rw [hG]
  simp only [pieceF, paramAtV, ehat, hE, hC, hC4, hU, hV, hzγ]
  have hVW : (z 0 + z 1 + z 2) * M ^ 2 + z 2 * Minkowski.dot k k -
      U⁻¹ * (z 1 + (1 - x)) * z 2 ^ 2 * Minkowski.dot k k + (1 - x) * u = W := rfl
  rw [hVW]
  simp only [show (5 - 4).factorial = 1 from rfl, show (5 - 5).factorial = 1 from rfl,
    show 5 - 3 = 2 from rfl, show 5 - 4 = 1 from rfl,
    show 5 - 5 = 0 from rfl]
  by_cases hW0 : W = 0
  · simp [hW0]
  · have hU' : (U : ℂ) ≠ 0 := ofReal_ne_zero.2 hU0.ne'
    have hW' : (W : ℂ) ≠ 0 := ofReal_ne_zero.2 hW0
    push_cast
    field_simp
    ring

end Slice

end QED.ChainProof.SetAKS

end
