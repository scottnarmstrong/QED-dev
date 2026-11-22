/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBZero
public import QED.ChainProof.SetCRegDispCt01
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The mass part at zero momentum transfer as a derivative in the photon variable

Helper level for `QED.ChainProof.SetCRegDisp.CBLoBEq` (set (c), layer 5). Both sides of the
mass-part identity are integrals of a derivative in the radial photon variable `K`:

* `integral_comb_zero_deriv`: the zero-transfer combination `∫ (undKern - 2m² dblKern)` of the
  Pauli values is `∫₀¹ 6 y (K g)'(K) dy` at `K = y² m²/(1-y)`, `g = phf Ms`
  (`hasDerivAt_mul_phf`);
* `vpInsertW_eq_deriv`: the target kernel is `vpInsertW c a b = ∫₀¹ x (K R)'(K) dx` at
  `K = x²/(1-x)`, `R(K) = K² (1/(K+a) - 1/(K+b))²/(K+c)` (`hasDerivAt_wKerK`).

The remaining matching replaces `g` (a product of simple photon poles) by `R` (squared poles and a
`K²` numerator, from the regulated photon pair and the `k²` absorption).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ChainProof.CtLoB

open QED.ChainProof.SetCRegDisp

theorem hasDerivAt_phf {n : ℕ} (Ms : Fin n → ℝ) {K : ℝ} (hK : ∀ i, K + Ms i ^ 2 ≠ 0) :
    HasDerivAt (phf Ms) (-(phf Ms K * ∑ i, (K + Ms i ^ 2)⁻¹)) K := by
  induction n with
  | zero =>
    have he : phf Ms = fun _ => 1 := by funext K; simp [phf]
    rw [he]
    simpa using hasDerivAt_const K (1 : ℝ)
  | succ n ih =>
    have ht := ih (Fin.tail Ms) fun i => hK i.succ
    have h0 : HasDerivAt (fun K => (K + Ms 0 ^ 2)⁻¹) (-((K + Ms 0 ^ 2) ^ 2)⁻¹) K := by
      convert ((hasDerivAt_id' K).add_const (Ms 0 ^ 2)).inv (hK 0) using 1
      ring
    have he : phf Ms = fun K => (K + Ms 0 ^ 2)⁻¹ * phf (Fin.tail Ms) K := by
      funext K
      rw [phf, phf, Fin.prod_univ_succ]
      rfl
    rw [he]
    convert h0.mul ht using 1
    simp only [phf, Fin.sum_univ_succ, Fin.tail]
    have := hK 0
    field_simp
    ring

theorem hasDerivAt_mul_phf {n : ℕ} (Ms : Fin n → ℝ) {K : ℝ} (hK : ∀ i, K + Ms i ^ 2 ≠ 0) :
    HasDerivAt (fun K => K * phf Ms K)
      (phf Ms K - K * phf Ms K * ∑ i, (K + Ms i ^ 2)⁻¹) K := by
  convert (hasDerivAt_id' K).mul (hasDerivAt_phf Ms hK) using 1
  ring

theorem hasDerivAt_wKerK {a b c K : ℝ} (ha : K + a ≠ 0) (hb : K + b ≠ 0) (hc : K + c ≠ 0) :
    HasDerivAt (fun K => K ^ 3 * (1 / (K + a) - 1 / (K + b)) ^ 2 / (K + c))
      (wKerK c a b K) K := by
  have hA : HasDerivAt (fun K => 1 / (K + a)) (-1 / (K + a) ^ 2) K := by
    convert ((hasDerivAt_id' K).add_const a).inv ha using 1
    funext K; simp
  have hB : HasDerivAt (fun K => 1 / (K + b)) (-1 / (K + b) ^ 2) K := by
    convert ((hasDerivAt_id' K).add_const b).inv hb using 1
    funext K; simp
  have hC : HasDerivAt (fun K => K + c) 1 K := (hasDerivAt_id' K).add_const c
  convert (((hasDerivAt_pow 3 K).mul ((hA.sub hB).pow 2)).div hC hc) using 1
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold wKerK
  field_simp
  ring

theorem radKY_nonneg (m : ℝ) {y : ℝ} (hy : y ≤ 1) : 0 ≤ radKY m y :=
  div_nonneg (by positivity) (by linarith)

/-- **The zero-transfer combination as a derivative.** -/
theorem integral_comb_zero_deriv {m : ℝ} (hm : 0 < m) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, 0 < Ms i) (d : Fin 2) :
    ∫ z, (undKern m 0 Ms z - 2 * m ^ 2 * dblKern m 0 Ms d z) ∂QED.Integration.feynmanMeasure =
      ∫ y in (0 : ℝ)..1, 6 * y * deriv (fun K => K * phf Ms K) (radKY m y) := by
  rw [integral_comb_zero hm hMs d]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le zero_le_one] at hy
  have hK : ∀ i, radKY m y + Ms i ^ 2 ≠ 0 := fun i =>
    (add_pos_of_nonneg_of_pos (radKY_nonneg m hy.2) (pow_pos (hMs i) 2)).ne'
  rw [(hasDerivAt_mul_phf Ms hK).deriv]

/-- **The target kernel as a derivative.** -/
theorem vpInsertW_eq_deriv {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    vpInsertW c a b = ∫ x in (0 : ℝ)..1,
      x * deriv (fun K => K ^ 3 * (1 / (K + a) - 1 / (K + b)) ^ 2 / (K + c)) (x ^ 2 / (1 - x)) := by
  unfold vpInsertW wKer
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hK : 0 ≤ x ^ 2 / (1 - x) := div_nonneg (by positivity) (by linarith [hx.2])
  rw [(hasDerivAt_wKerK (by linarith) (by linarith) (by linarith)).deriv]

end QED.ChainProof.CtLoB

end
