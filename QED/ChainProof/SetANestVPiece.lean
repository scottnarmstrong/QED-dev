/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestVShell
public import QED.Integration.TwoLoopRefinedBoundCubic
import Mathlib.Algebra.Order.Star.Real

/-!
# The spatial integral of a two-loop energy integral, polynomially in the external momentum

Helper level for the set (a) headline (HA₆), obligation (N), step NL for `VA`, `VB`, `VC`.
For a two-loop integrand `P(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹` with `N = m + 1` lines, Minkowski denominators at
`ε > 0` and line momenta `αᵢ·ℓ + cᵢ k`, the energy integral `J(k, v) = ∫ dt (⋯)` at spatial
loop momenta `v` satisfies

`∫ d⁶v |J(k, v)| ≤ C (1 + Σ_μ k_μ²)⁴`,

with `C` independent of `k`, under the numerator-aware criterion and the **additive** pointwise
bound `‖P_k(ℓ)‖ ≤ C_b w_E(A) (1 + Σ_μ k_μ² + ℓᵀAℓ)²` on the numerators. This is the analytic
core of the Fubini condition of the nested form (`QED.ChainProof.SetANestV.InnerBound`, here in
its integrated form).

The proof follows `QED.Integration.TwoLoop.integrable_numEnergyValueQuartic_of_refined`: at a
Feynman parameter `x` the energy-integrated integrand is three terms
`f_j(v) U^{-1/2} ((v + σ)ᵀA(v + σ) + V - iε)^{-n_j}`. The three numerators are bounded by
`b + (v + σ)ᵀA(v + σ)` to the powers `2, 2, 0` (or `2, 1, 0` for a cubic), with
`b = 1 + Σ k² + 2 Σᵢ |pᵢ|²`, through the shift bounds `loopNorm_shift_le` and the rescaling
`A ↦ A/(1 + Σ k²)` of the finite-difference bounds (`norm_energyContractTwo_le_add`, …). The
shell bound `QED.ChainProof.SetANestV.integral_quadForm_shell_le` then gives
`(1 + Σ k²)^{j+2}` in place of the `(K + 1)^n` of the uniform comparison.

* `qf_inv_mulVec`, `qf_shift_le`, `loopNorm_shift_le`: the shift bounds;
* `loopNorm_smul_matrix`, `norm_energyContractTwo_le_add`, `norm_energyContractTwo_le_add_cubic`,
  `norm_energyContractFour_le_add`: the contractions under the additive bound;
* `integral_norm_term_le`, **`integral_norm_numEnergyValueQuartic_le`**: the bound at a Feynman
  parameter;
* **`integral_norm_energyIntegral_le`**: the bound on `∫ d⁶v |J(k, v)|`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Matrix
open scoped Real

namespace QED.ChainProof.SetANestV

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.Spatial (quadForm)

/-! ### The shift bounds -/

theorem qf_inv_mulVec {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (β : Fin 2 → ℝ) :
    (A⁻¹ *ᵥ β) ⬝ᵥ A *ᵥ (A⁻¹ *ᵥ β) = β ⬝ᵥ A⁻¹ *ᵥ β := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, dotProduct_comm]

section Shift

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}

theorem qf_shift_le (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hPD : (symanzikMatrix α z).PosDef) (q : Fin (m + 1) → ℝ) :
    ((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) ⬝ᵥ symanzikMatrix α z *ᵥ
      ((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) ≤ ∑ i, q i ^ 2 := by
  rw [qf_inv_mulVec hPD]
  have h0 := remainder_nonneg α hz hPD.det_pos.ne' q
  unfold remainder at h0
  have hzle : ∀ i, z i ≤ 1 := fun i => by
    rw [← hz1]
    exact Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  have hle : ∑ i, z i * q i ^ 2 ≤ ∑ i, q i ^ 2 :=
    Finset.sum_le_sum fun i _ => by nlinarith [hz i, hzle i, sq_nonneg (q i)]
  linarith

/-- **The shift bound**: at the energy shift `-τ`, the loop norm is at most
`2 (v + σ)ᵀA(v + σ) + 2 Σᵢ |pᵢ|²`. -/
theorem loopNorm_shift_le (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hPD : (symanzikMatrix α z).PosDef) (p : Fin (m + 1) → Fin 4 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    loopNorm (symanzikMatrix α z) (loopMomenta (-energyShift α p z) v) ≤
      2 * quadForm (symanzikMatrix α z) (v + spatialShift α p z) + 2 * ∑ i, ∑ μ, p i μ ^ 2 := by
  set A := symanzikMatrix α z with hA
  have hτ : energyShift α p z ⬝ᵥ A *ᵥ energyShift α p z ≤ ∑ i, p i 0 ^ 2 :=
    qf_shift_le α hz hz1 hPD _
  have hσ : ∀ c : Fin 3, (fun s => spatialShift α p z s c) ⬝ᵥ A *ᵥ
      (fun s => spatialShift α p z s c) ≤ ∑ i, p i c.succ ^ 2 := fun c =>
    qf_shift_le α hz hz1 hPD _
  have hsplit : v = (v + spatialShift α p z) + -spatialShift α p z := by abel
  have hv := quadForm_add_le hPD (v + spatialShift α p z) (-spatialShift α p z)
  rw [← hsplit] at hv
  have hneg : quadForm A (-spatialShift α p z) ≤ ∑ c : Fin 3, ∑ i, p i c.succ ^ 2 := by
    rw [quadForm_eq_sum_dotProduct]
    refine Finset.sum_le_sum fun c _ => ?_
    have e : (fun s => (-spatialShift α p z) s c) = -(fun s => spatialShift α p z s c) := by
      funext s; simp
    rw [e, qf_neg]
    exact hσ c
  rw [loopNorm_loopMomenta, qf_neg]
  have htot : ∑ i, ∑ μ, p i μ ^ 2 = ∑ i, p i 0 ^ 2 + ∑ c : Fin 3, ∑ i, p i c.succ ^ 2 := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_succ _
  have h0 : 0 ≤ ∑ i, p i 0 ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [htot]
  linarith

end Shift

/-! ### The contractions under the additive bound -/

theorem loopNorm_smul_matrix (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopNorm (c • A) ℓ = c * loopNorm A ℓ := by
  unfold loopNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [dotProduct_mulVec_fin_two, Matrix.smul_apply, smul_eq_mul]
  ring

theorem inv_smul_inv_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) {t : ℝ} (ht : 0 < t) :
    ((t⁻¹ • A)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) = t • A⁻¹ := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  refine inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, mul_inv_cancel₀ ht.ne', one_smul, nonsing_inv_mul _ hdet]

/-- The additive bound at `A` is a bound at the rescaled matrix `A/(1 + S)`. -/
theorem norm_eval_le_rescaled (P : LoopQuartic) {A : Matrix (Fin 2) (Fin 2) ℝ} {K S : ℝ}
    (hS : 0 ≤ S) (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + S + loopNorm A ℓ) ^ 2)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.eval ℓ‖ ≤ (K * (1 + S) ^ 2) * (1 + loopNorm ((1 + S)⁻¹ • A) ℓ) ^ 2 := by
  have ht : 0 < 1 + S := by linarith
  refine (hP ℓ).trans_eq ?_
  rw [loopNorm_smul_matrix]
  field_simp

section Contract

variable (P : LoopQuartic) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) {K S : ℝ}
  (hK : 0 ≤ K) (hS : 0 ≤ S) (hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ K * (1 + S + loopNorm A ℓ) ^ 2)
include hA hK hS hP

/-- **The quadratic energy contraction under the additive bound.** -/
theorem norm_energyContractTwo_le_add (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.energyContractTwo A (loopComp ℓ)‖ ≤ 6 * 34 ^ 2 * K * (1 + S + loopNorm A ℓ) ^ 2 := by
  have ht : 0 < 1 + S := by linarith
  have hA' : ((1 + S)⁻¹ • A).PosDef := hA.smul (inv_pos.mpr ht)
  have h := norm_energyContractTwo_le_of_bound P hA' (by positivity)
    (norm_eval_le_rescaled P hS hP) ℓ
  have he : P.energyContractTwo ((1 + S)⁻¹ • A) (loopComp ℓ) =
      ((1 + S : ℝ) : ℂ) * P.energyContractTwo A (loopComp ℓ) := by
    unfold LoopQuartic.energyContractTwo
    rw [inv_smul_inv_eq hA ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [he, norm_mul, norm_real, Real.norm_of_nonneg ht.le, loopNorm_smul_matrix] at h
  have e : 6 * 34 ^ 2 * (K * (1 + S) ^ 2) * (1 + (1 + S)⁻¹ * loopNorm A ℓ) ^ 2 =
      6 * 34 ^ 2 * K * (1 + S + loopNorm A ℓ) ^ 2 := by
    field_simp
  rw [e] at h
  exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith)).trans h

/-- **The quadratic energy contraction of a cubic under the additive bound.** -/
theorem norm_energyContractTwo_le_add_cubic (hq : P.quart = 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.energyContractTwo A (loopComp ℓ)‖ ≤ 5 * (6 * 34 ^ 2 * K) * (1 + S + loopNorm A ℓ) := by
  have ht : 0 < 1 + S := by linarith
  have hA' : ((1 + S)⁻¹ • A).PosDef := hA.smul (inv_pos.mpr ht)
  have h := norm_energyContractTwo_le_of_bound_cubic P hq hA' (by positivity)
    (norm_eval_le_rescaled P hS hP) ℓ
  have he : P.energyContractTwo ((1 + S)⁻¹ • A) (loopComp ℓ) =
      ((1 + S : ℝ) : ℂ) * P.energyContractTwo A (loopComp ℓ) := by
    unfold LoopQuartic.energyContractTwo
    rw [inv_smul_inv_eq hA ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [he, norm_mul, norm_real, Real.norm_of_nonneg ht.le, loopNorm_smul_matrix] at h
  have e : 5 * (6 * 34 ^ 2 * (K * (1 + S) ^ 2)) * (1 + (1 + S)⁻¹ * loopNorm A ℓ) =
      (1 + S) * (5 * (6 * 34 ^ 2 * K) * (1 + S + loopNorm A ℓ)) := by
    field_simp
  rw [e] at h
  exact le_of_mul_le_mul_left h ht

/-- **The quartic energy contraction under the additive bound.** -/
theorem norm_energyContractFour_le_add : ‖P.energyContractFour A‖ ≤ 5 * 33 ^ 2 * K := by
  have ht : 0 < 1 + S := by linarith
  have hA' : ((1 + S)⁻¹ • A).PosDef := hA.smul (inv_pos.mpr ht)
  have h := norm_energyContractFour_le_of_bound P hA' (by positivity)
    (norm_eval_le_rescaled P hS hP)
  have he : P.energyContractFour ((1 + S)⁻¹ • A) =
      (((1 + S) ^ 2 : ℝ) : ℂ) * P.energyContractFour A := by
    unfold LoopQuartic.energyContractFour
    rw [inv_smul_inv_eq hA ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [matPair, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [he, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)] at h
  have e : 5 * 33 ^ 2 * (K * (1 + S) ^ 2) = (1 + S) ^ 2 * (5 * 33 ^ 2 * K) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h (by positivity)

end Contract

/-! ### The bound at a Feynman parameter -/

/-- The coefficient of the bound at a Feynman parameter. -/
noncomputable def numConst (m : ℕ) (Cb b K ε : ℝ) : ℝ :=
  ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * (4 * Cb) * shellConst b K ε 2 m +
    ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (4 * (5 * (6 * 34 ^ 2 * Cb))) *
      (shellConst b K ε 2 (m - 1) + shellConst b K ε 1 (m - 1)) +
    ‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ * (5 * 33 ^ 2 * Cb) *
      shellConst b K ε 0 (m - 2)

theorem shellConst_nonneg {b K ε : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hε : 0 < ε) (j n : ℕ) :
    0 ≤ shellConst b K ε j n := by
  unfold shellConst
  have : 0 ≤ b + 2 * K + 1 := by linarith
  positivity

section AtPoint

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **One term at an interior point**: a continuous numerator bounded by
`C_f w_E(A) (b + (v + σ)ᵀA(v + σ))^j` against `c U^{-1/2} ((v + σ)ᵀA(v + σ) + V - iε)^{-n}`. -/
theorem integral_norm_term_le (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) (E : Finset (Fin (m + 1))) {b K : ℝ}
    (hb : 1 ≤ b) (hV : |symanzikV α p M (simplexPoint x)| ≤ K) {j n : ℕ} (hjn : j + 4 ≤ n)
    {f : (Fin 2 → Fin 3 → ℝ) → ℂ} (hf : Continuous f) {Cf : ℝ}
    (hbd : ∀ v, ‖f v‖ ≤ Cf * lineWeight α E (symanzikMatrix α (simplexPoint x)) *
      (b + quadForm (symanzikMatrix α (simplexPoint x))
        (v + spatialShift α p (simplexPoint x))) ^ j)
    (c : ℂ) :
    Integrable (fun v => f v * (c * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        ((((quadForm (symanzikMatrix α (simplexPoint x))
          (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹)) ∧
      ∫ v, ‖f v * (c * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        ((((quadForm (symanzikMatrix α (simplexPoint x))
          (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹)‖ ≤
        ‖c‖ * Cf * shellConst b K ε j n * refinedWeight 2 E α (simplexPoint x) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  set V := symanzikV α p M (simplexPoint x) with hVdef
  set lw := lineWeight α E A with hlw
  have hAdet : A.det = U := rfl
  have hG := integral_quadForm_shell_le hPD hb hV hε hjn σ hf.aestronglyMeasurable
    (C := Cf * lw) hbd
  have hfun : ∀ v, f v * (c * ((Real.sqrt U : ℝ) : ℂ)⁻¹ *
      ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹) =
      c * ((Real.sqrt U : ℝ) : ℂ)⁻¹ *
        (f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹) :=
    fun v => by ring
  simp only [hfun]
  refine ⟨hG.1.const_mul _, ?_⟩
  simp only [norm_mul (c * _)]
  rw [integral_const_mul]
  have hRW := refinedWeight_eq_mul α E hPD
  have hc : ‖c * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ = ‖c‖ * (Real.sqrt U)⁻¹ := by
    rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [hc, ← hRW]
  calc ‖c‖ * (Real.sqrt U)⁻¹ * ∫ v, ‖f v *
        ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖
      ≤ ‖c‖ * (Real.sqrt U)⁻¹ * (Cf * lw * (shellConst b K ε j n * (Real.sqrt A.det ^ 3)⁻¹)) :=
        mul_le_mul_of_nonneg_left hG.2 (by positivity)
    _ = _ := by rw [hAdet]; ring

/-- **The bound at an interior Feynman parameter.** Under the additive bound
`‖P(ℓ)‖ ≤ C_b w_E(A) (1 + S + ℓᵀAℓ)²` for all positive definite `A`, with
`b ≥ 1 + S + 2 Σᵢ |pᵢ|²` and `K ≥ Σᵢ (Mᵢ² + |pᵢ|²)`, the energy-integrated integrand is
integrable in the spatial momenta, with absolute integral at most a constant (depending only on
`m`) times `C_b` times shell constants times `refinedWeight 2 E α`. -/
theorem integral_norm_numEnergyValueQuartic_le (P : LoopQuartic)
    (hdeg : 7 ≤ m ∨ (6 ≤ m ∧ P.quart = 0)) (hε : 0 < ε) {x : Fin m → ℝ}
    (hxS : x ∈ simplexSet m) (hPD : (symanzikMatrix α (simplexPoint x)).PosDef)
    (E : Finset (Fin (m + 1))) {Cb S b K : ℝ} (hCb : 0 ≤ Cb) (hS : 0 ≤ S)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖P.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + S + loopNorm A ℓ) ^ 2)
    (hb : 1 + S + 2 * ∑ i, ∑ μ, p i μ ^ 2 ≤ b) (hK : ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) ≤ K) :
    Integrable (fun v => numEnergyValueQuartic P α p M ε x v) ∧
      ∫ v, ‖numEnergyValueQuartic P α p M ε x v‖ ≤
        numConst m Cb b K ε * refinedWeight 2 E α (simplexPoint x) := by
  have hm6 : 6 ≤ m := by omega
  set z := simplexPoint x with hzdef
  set A := symanzikMatrix α z with hAdef
  set τ := energyShift α p z with hτdef
  set σ := spatialShift α p z with hσdef
  set lw := lineWeight α E A with hlw
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  have hdet : symanzikU α z ≠ 0 := hPD.det_pos.ne'
  have hV : |symanzikV α p M z| ≤ K := (abs_symanzikV_le α p M hz.1 hz.2 hdet).trans hK
  have hp0 : 0 ≤ ∑ i, ∑ μ, p i μ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb1 : 1 ≤ b := by linarith
  have hlw0 : 0 ≤ lw := lineWeight_nonneg α E A
  have hK0 : 0 ≤ Cb * lw := mul_nonneg hCb hlw0
  have hP : ∀ ℓ, ‖P.eval ℓ‖ ≤ Cb * lw * (1 + S + loopNorm A ℓ) ^ 2 := hB A hPD
  -- the size of the shifted loop momenta
  have hL : ∀ v, 1 + S + loopNorm A (loopMomenta (-τ) v) ≤ 2 * (b + quadForm A (v + σ)) :=
    fun v => by
      have h := loopNorm_shift_le α hz.1 hz.2 hPD p v
      have hq := QED.Integration.TwoLoop.quadForm_nonneg hPD (v + σ)
      linarith
  have hL0 : ∀ v, 0 ≤ 1 + S + loopNorm A (loopMomenta (-τ) v) := fun v => by
    linarith [loopNorm_nonneg hPD (loopMomenta (-τ) v)]
  have hcont0 : Continuous fun v : Fin 2 → Fin 3 → ℝ => loopMomenta (-τ) v :=
    continuous_loopMomenta.comp (continuous_const.prodMk continuous_id)
  -- the first term
  have h1 := integral_norm_term_le α p M hε hPD E hb1 hV (j := 2) (n := m) (by omega)
    (f := fun v => P.eval (loopMomenta (-τ) v)) (P.continuous_eval.comp hcont0) (Cf := 4 * Cb)
    (fun v => by
      refine (hP _).trans ?_
      have h2 := pow_le_pow_left₀ (hL0 v) (hL v) 2
      calc Cb * lw * (1 + S + loopNorm A (loopMomenta (-τ) v)) ^ 2
          ≤ Cb * lw * (2 * (b + quadForm A (v + σ))) ^ 2 := mul_le_mul_of_nonneg_left h2 hK0
        _ = 4 * Cb * lw * (b + quadForm A (v + σ)) ^ 2 := by ring)
    (-(π / (((m + 1 : ℕ) : ℂ) - 1)))
  -- the second term
  have hcont2 : Continuous fun v => P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) :=
    (P.continuous_energyContractTwo A).comp (continuous_loopComp.comp hcont0)
  have h2 : Integrable (fun v => P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
        energyValueTwo α p M ε x v) ∧
      ∫ v, ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
        energyValueTwo α p M ε x v‖ ≤
        ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (4 * (5 * (6 * 34 ^ 2 * Cb))) *
          (shellConst b K ε 2 (m - 1) + shellConst b K ε 1 (m - 1)) *
          refinedWeight 2 E α z := by
    simp only [energyValueTwo_eq]
    have hc0 : 0 ≤ ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (4 * (5 * (6 * 34 ^ 2 * Cb))) :=
      by positivity
    have hR : 0 ≤ refinedWeight 2 E α z := by
      rw [refinedWeight_eq_lineWeight]
      have := hPD.det_pos
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg this.le _)) hlw0
    have hK0' : 0 ≤ K := (abs_nonneg _).trans hV
    have hs1 : 0 ≤ shellConst b K ε 1 (m - 1) := shellConst_nonneg (by linarith) hK0' hε _ _
    have hs2 : 0 ≤ shellConst b K ε 2 (m - 1) := shellConst_nonneg (by linarith) hK0' hε _ _
    rcases hdeg with h7 | ⟨_, hq⟩
    · have h := integral_norm_term_le α p M hε hPD E hb1 hV (j := 2) (n := m - 1) (by omega)
        hcont2 (Cf := 4 * (5 * (6 * 34 ^ 2 * Cb)))
        (fun v => by
          refine (norm_energyContractTwo_le_add P hPD hK0 hS hP _).trans ?_
          have h2 := pow_le_pow_left₀ (hL0 v) (hL v) 2
          have hq := QED.Integration.TwoLoop.quadForm_nonneg hPD (v + σ)
          calc 6 * 34 ^ 2 * (Cb * lw) * (1 + S + loopNorm A (loopMomenta (-τ) v)) ^ 2
              ≤ 6 * 34 ^ 2 * (Cb * lw) * (2 * (b + quadForm A (v + σ))) ^ 2 :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ ≤ 4 * (5 * (6 * 34 ^ 2 * Cb)) * lw * (b + quadForm A (v + σ)) ^ 2 := by
                nlinarith [mul_nonneg hK0 (sq_nonneg (b + quadForm A (v + σ)))])
        ((π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1))))
      refine ⟨h.1, h.2.trans ?_⟩
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hs1 :
        shellConst b K ε 2 (m - 1) ≤ _) hc0
      exact mul_le_mul_of_nonneg_right (by linarith) hR
    · have h := integral_norm_term_le α p M hε hPD E hb1 hV (j := 1) (n := m - 1) (by omega)
        hcont2 (Cf := 4 * (5 * (6 * 34 ^ 2 * Cb)))
        (fun v => by
          refine (norm_energyContractTwo_le_add_cubic P hPD hK0 hS hP hq _).trans ?_
          have hq' := QED.Integration.TwoLoop.quadForm_nonneg hPD (v + σ)
          calc 5 * (6 * 34 ^ 2 * (Cb * lw)) * (1 + S + loopNorm A (loopMomenta (-τ) v))
              ≤ 5 * (6 * 34 ^ 2 * (Cb * lw)) * (2 * (b + quadForm A (v + σ))) :=
                mul_le_mul_of_nonneg_left (hL v) (by positivity)
            _ ≤ 4 * (5 * (6 * 34 ^ 2 * Cb)) * lw * (b + quadForm A (v + σ)) ^ 1 := by
                nlinarith [mul_nonneg hK0 (by linarith : 0 ≤ b + quadForm A (v + σ))])
        ((π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1))))
      refine ⟨h.1, h.2.trans ?_⟩
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hs2 :
        shellConst b K ε 1 (m - 1) ≤ _) hc0
      exact mul_le_mul_of_nonneg_right (by linarith) hR
  -- the third term
  have h3 := integral_norm_term_le α p M hε hPD E hb1 hV (j := 0) (n := m - 2) (by omega)
    (f := fun _ => P.energyContractFour A) continuous_const (Cf := 5 * 33 ^ 2 * Cb)
    (fun v => by
      refine (norm_energyContractFour_le_add P hPD hK0 hS hP).trans_eq ?_
      ring)
    (-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2)))))
  simp only [← energyValue_eq] at h1
  simp only [← energyValueFour_eq] at h3
  have hsum : (fun v => numEnergyValueQuartic P α p M ε x v) = fun v =>
      P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v +
        P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) * energyValueTwo α p M ε x v +
        P.energyContractFour A * energyValueFour α p M ε x v := rfl
  rw [hsum]
  refine ⟨(h1.1.add h2.1).add h3.1, ?_⟩
  calc ∫ v, ‖P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v +
        P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) * energyValueTwo α p M ε x v +
        P.energyContractFour A * energyValueFour α p M ε x v‖
      ≤ ∫ v, (‖P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v‖ +
        ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) * energyValueTwo α p M ε x v‖ +
        ‖P.energyContractFour A * energyValueFour α p M ε x v‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          ((h1.1.norm.add h2.1.norm).add h3.1.norm) (Eventually.of_forall fun v => ?_)
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (∫ v, ‖P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v‖) +
        (∫ v, ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
          energyValueTwo α p M ε x v‖) +
        ∫ v, ‖P.energyContractFour A * energyValueFour α p M ε x v‖ := by
        rw [integral_add, integral_add]
        exacts [h1.1.norm, h2.1.norm, h1.1.norm.add h2.1.norm, h3.1.norm]
    _ ≤ _ := by
        have := add_le_add (add_le_add h1.2 h2.2) h3.2
        refine this.trans_eq ?_
        unfold numConst
        ring

end AtPoint

/-! ### The bound on the spatial integral of the energy integral -/

theorem shellConst_le {b K B t ε : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hB : 0 ≤ B) (ht : 1 ≤ t)
    (hε : 0 < ε) (hbB : b ≤ B * t) (hKB : K ≤ B * t) {j : ℕ} (hj : j ≤ 2) (n : ℕ) :
    shellConst b K ε j n ≤ shellConst B B ε j n * t ^ 4 := by
  unfold shellConst
  have ht0 : 0 ≤ t := by linarith
  have h1 : b + 2 * K + 1 ≤ (B + 2 * B + 1) * t := by nlinarith
  have h1' : (b + 2 * K + 1) ^ (j + 2) ≤ (B + 2 * B + 1) ^ (j + 2) * t ^ 4 := by
    calc (b + 2 * K + 1) ^ (j + 2) ≤ ((B + 2 * B + 1) * t) ^ (j + 2) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = (B + 2 * B + 1) ^ (j + 2) * t ^ (j + 2) := mul_pow _ _ _
      _ ≤ (B + 2 * B + 1) ^ (j + 2) * t ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (by positivity)
  have h2 : b ^ j ≤ B ^ j * t ^ 4 := by
    calc b ^ j ≤ (B * t) ^ j := pow_le_pow_left₀ hb hbB _
      _ = B ^ j * t ^ j := mul_pow _ _ _
      _ ≤ B ^ j * t ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega))
          (by positivity)
  have e1 : 0 ≤ (ε ^ (n - 2))⁻¹ * (π / (2 * ε)) := by positivity
  have e2 : (0 : ℝ) ≤ 2 ^ n * (1 / 2) := by positivity
  have := add_le_add (mul_le_mul_of_nonneg_right h1' e1) (mul_le_mul_of_nonneg_left h2 e2)
  have hπ : (0 : ℝ) ≤ π ^ 3 := by positivity
  calc π ^ 3 * ((b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ * (π / (2 * ε)) +
        2 ^ n * b ^ j * (1 / 2))
      = π ^ 3 * ((b + 2 * K + 1) ^ (j + 2) * ((ε ^ (n - 2))⁻¹ * (π / (2 * ε))) +
        2 ^ n * (1 / 2) * b ^ j) := by ring
    _ ≤ π ^ 3 * ((B + 2 * B + 1) ^ (j + 2) * t ^ 4 * ((ε ^ (n - 2))⁻¹ * (π / (2 * ε))) +
        2 ^ n * (1 / 2) * (B ^ j * t ^ 4)) := mul_le_mul_of_nonneg_left this hπ
    _ = _ := by ring

theorem numConst_le {m : ℕ} {Cb b K B t ε : ℝ} (hCb : 0 ≤ Cb) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (ht : 1 ≤ t) (hε : 0 < ε) (hbB : b ≤ B * t) (hKB : K ≤ B * t) :
    numConst m Cb b K ε ≤ numConst m Cb B B ε * t ^ 4 := by
  have s := fun (j : ℕ) (hj : j ≤ 2) (n : ℕ) => shellConst_le hb hK hB ht hε hbB hKB hj n
  have a1 : 0 ≤ ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * (4 * Cb) := by positivity
  have a2 : 0 ≤ ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (4 * (5 * (6 * 34 ^ 2 * Cb))) := by
    positivity
  have a3 : 0 ≤ ‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ * (5 * 33 ^ 2 * Cb) := by
    positivity
  unfold numConst
  have := add_le_add (add_le_add (mul_le_mul_of_nonneg_left (s 2 le_rfl m) a1)
    (mul_le_mul_of_nonneg_left (add_le_add (s 2 le_rfl (m - 1)) (s 1 (by norm_num) (m - 1))) a2))
    (mul_le_mul_of_nonneg_left (s 0 (by norm_num) (m - 2)) a3)
  exact this.trans_eq (by ring)

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (E : Finset (Fin (m + 1))) (c : Fin (m + 1) → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **The spatial integral of the energy integral, polynomially in the external momentum.** For
`N = m + 1` lines with momenta `αᵢ·ℓ + cᵢ k`, `ε > 0`, the numerator-aware criterion, numerators
`P_k` of degree at most four (`N ≥ 8`) or three (`N ≥ 7`) with the additive bound
`‖P_k(ℓ)‖ ≤ C_b w_E(A) (1 + Σ_μ k_μ² + ℓᵀAℓ)²`: both stages are integrable and
`∫ d⁶v |∫ dt P_k ∏ Dᵢ⁻¹| ≤ C (1 + Σ_μ k_μ²)⁴` with `C` independent of `k`. -/
theorem integral_norm_energyIntegral_le (hcrit : NoSubdivergenceRefined 2 E α) (hε : 0 < ε)
    (P : (Fin 4 → ℝ) → LoopQuartic) (hdeg : 7 ≤ m ∨ (6 ≤ m ∧ ∀ k, (P k).quart = 0)) {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hB : ∀ k (A : Matrix (Fin 2) (Fin 2) ℝ), A.PosDef → ∀ ℓ,
      ‖(P k).eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + ∑ μ, k μ ^ 2 + loopNorm A ℓ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Fin 4 → ℝ,
      (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ => (P k).eval (loopMomenta t v) *
        ∏ i, (lineDenom α (fun i => c i • k) M ε i (loopMomenta t v))⁻¹) ∧
      Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, (P k).eval (loopMomenta t v) *
        ∏ i, (lineDenom α (fun i => c i • k) M ε i (loopMomenta t v))⁻¹) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, (P k).eval (loopMomenta t v) *
        ∏ i, (lineDenom α (fun i => c i • k) M ε i (loopMomenta t v))⁻¹‖ ≤
        C * (1 + ∑ μ, k μ ^ 2) ^ 4 := by
  have hm6 : 6 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  have hW0 : 0 ≤ ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x) := by
    refine integral_nonneg fun x => ?_
    rw [refinedWeight_eq_lineWeight]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (lineWeight_nonneg _ _ _)
  set B : ℝ := 1 + 2 * ∑ i, c i ^ 2 + ∑ i, M i ^ 2 with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(m.factorial : ℝ) * numConst m Cb B B ε *
    ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x), ?_, fun k => ?_⟩
  · have : 0 ≤ numConst m Cb B B ε := by
      unfold numConst
      have hs := fun j n => shellConst_nonneg (j := j) (n := n) hB0 hB0 hε
      have := hs 2 m; have := hs 2 (m - 1); have := hs 1 (m - 1); have := hs 0 (m - 2)
      positivity
    positivity
  set p : Fin (m + 1) → Fin 4 → ℝ := fun i => c i • k with hp
  set S := ∑ μ, k μ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpp : ∑ i, ∑ μ, p i μ ^ 2 = (∑ i, c i ^ 2) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [hp]
    ring
  have hRB : RefinedBound α E 4 (P k).eval := by
    refine ⟨Cb * (1 + S) ^ 2, by positivity, fun A hA ℓ => (hB k A hA ℓ).trans ?_⟩
    have hL := loopNorm_nonneg hA ℓ
    have hlw := lineWeight_nonneg α E A
    have e : Real.sqrt (1 + loopNorm A ℓ) ^ 4 = (1 + loopNorm A ℓ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
    rw [e]
    have h1 : 1 + S + loopNorm A ℓ ≤ (1 + S) * (1 + loopNorm A ℓ) := by nlinarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 2
    calc Cb * lineWeight α E A * (1 + S + loopNorm A ℓ) ^ 2
        ≤ Cb * lineWeight α E A * ((1 + S) * (1 + loopNorm A ℓ)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cb * (1 + S) ^ 2 * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2 := by ring
  have hE := fun v => integrable_eval_mul_paramDenom_prod_of_refined (P k) α p M (by omega) hε
    hspan hRB hW v
  have hA' := fun v => integral_loopQuartic_mul_prod_lineDenom_eq_of_integrable (P k) α p M
    (by omega) hε hspan v (hE v)
  have hSint : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      numEnergyValueQuartic (P k) α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume) := by
    rcases hdeg with h7 | ⟨_, hq⟩
    · exact integrable_numEnergyValueQuartic_of_refined (P k) α p M h7 hε hspan hRB hW
    · exact integrable_numEnergyValueQuartic_of_cubic (P k) α p M (hq k) hm6 hε hspan hRB hW
  have hJ : (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, (P k).eval (loopMomenta t v) *
      ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) = fun v =>
      (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic (P k) α p M ε x v :=
    funext fun v => (hA' v).2
  refine ⟨fun v => (hA' v).1, ?_, ?_⟩
  · rw [hJ]
    exact hSint.integral_prod_right.const_mul _
  have hJ' : ∀ v : Fin 2 → Fin 3 → ℝ, (∫ t : Fin 2 → ℝ, (P k).eval (loopMomenta t v) *
      ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) =
      (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic (P k) α p M ε x v :=
    fun v => (hA' v).2
  simp only [hJ']
  set b := 1 + S + 2 * ∑ i, ∑ μ, p i μ ^ 2 with hbdef
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) with hKdef
  have hdeg' : 7 ≤ m ∨ (6 ≤ m ∧ (P k).quart = 0) := hdeg.imp id fun h => ⟨h.1, h.2 k⟩
  have hc0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM0 : 0 ≤ ∑ i, M i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK' : K = ∑ i, M i ^ 2 + (∑ i, c i ^ 2) * S := by
    rw [hKdef, Finset.sum_add_distrib, hpp]
  have hb0 : 0 ≤ b := by rw [hbdef, hpp]; positivity
  have hK0 : 0 ≤ K := by rw [hK']; positivity
  have hbB : b ≤ B * (1 + S) := by rw [hbdef, hpp, hBdef]; nlinarith [mul_nonneg hM0 hS]
  have hKB : K ≤ B * (1 + S) := by
    rw [hK', hBdef]; nlinarith [mul_nonneg hM0 hS, mul_nonneg hc0 hS]
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ∫ v, ‖numEnergyValueQuartic (P k) α p M ε x v‖ ≤
        numConst m Cb b K ε * refinedWeight 2 E α (simplexPoint x) := by
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact (integral_norm_numEnergyValueQuartic_le α p M (P k) hdeg' hε hxS hPD E hCb hS (hB k)
      le_rfl le_rfl).2
  have hnc := numConst_le (m := m) hCb hb0 hK0 hB0 (by linarith : (1 : ℝ) ≤ 1 + S) hε hbB hKB
  calc ∫ v, ‖(m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic (P k) α p M ε x v‖
      = (m.factorial : ℝ) * ∫ v, ‖∫ x in simplexSet m, numEnergyValueQuartic (P k) α p M ε x v‖ :=
        by simp only [norm_mul, Complex.norm_natCast]; rw [integral_const_mul]
    _ ≤ (m.factorial : ℝ) * ∫ v, ∫ x in simplexSet m, ‖numEnergyValueQuartic (P k) α p M ε x v‖ :=
        by
        refine mul_le_mul_of_nonneg_left (integral_mono hSint.integral_prod_right.norm
          hSint.norm.integral_prod_right fun v => norm_integral_le_integral_norm _) (by positivity)
    _ = (m.factorial : ℝ) * ∫ x in simplexSet m, ∫ v, ‖numEnergyValueQuartic (P k) α p M ε x v‖ :=
        by rw [integral_integral_swap (f := fun x v => ‖numEnergyValueQuartic (P k) α p M ε x v‖)
          hSint.norm]
    _ ≤ (m.factorial : ℝ) * ∫ x in simplexSet m,
          numConst m Cb b K ε * refinedWeight 2 E α (simplexPoint x) :=
        mul_le_mul_of_nonneg_left (integral_mono_ae hSint.norm.integral_prod_left
          (hW.const_mul _) hpt) (by positivity)
    _ = (m.factorial : ℝ) * numConst m Cb b K ε *
          ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x) := by
        rw [integral_const_mul]; ring
    _ ≤ (m.factorial : ℝ) * (numConst m Cb B B ε * (1 + S) ^ 4) *
          ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x) := by
        gcongr
    _ = _ := by ring

end QED.ChainProof.SetANestV

end
