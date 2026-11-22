/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametric
public import QED.Frozen.Algebra.Dot
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import QED.Algebra.Minkowski

/-!
# The two-loop Wick rotation at a Feynman-parameter point (pilot P2, first step)

At a fixed point of the Feynman simplex, a two-loop integrand with `N` combined propagators is
`(ℓᵀ A ℓ + V - iε)^{-N}`, where `A` is the `2 × 2` Symanzik matrix,
`ℓᵀ A ℓ = Σ_{s,t} A_{st} ℓ_s·ℓ_t` with the mostly-plus Minkowski product, and `V` the second
Symanzik function divided by `U`.
The dimensionally regularized side writes the Euclidean value of the same object as

  `∫ dᵈℓ₁ dᵈℓ₂ / π^d (ℓ_Eᵀ A ℓ_E + V)^{-N} = Γ(N - d)/Γ(N) · (det A)^{-d/2} · V^{d-N}`

(`euclidVacuumTwo`; this is the point integrand of the projective Feynman representation
`Γ(N - Ld/2) U^{N-(L+1)d/2} F^{Ld/2-N}` at `L = 2`, `F = U V`).

This module proves that the model's joint energy-first integral
(`QED.TwoLoop.jointEnergyFirstIntegral`, decision D-37.5) of `(ℓᵀ A ℓ + V - iε)^{-N}` is, for
every `ε > 0` and `N ≥ 5`,
`-π⁴ (N-1)⁻¹(N-2)⁻¹(N-3)⁻¹(N-4)⁻¹ (det A)^{-2} (V - iε)^{4-N}` with both stages integrable
(`jointEnergyFirstIntegral_wickKernelTwo`), and that as `ε → 0⁺` it tends to
`(i π²)² · euclidVacuumTwo (det A) V N 4` (`tendsto_jointEnergyFirstIntegral_wickKernelTwo`).
So at two loops the Wick factor `(i π^{d/2})^L` and the sign are theorems at `d = 4`, pointwise
in the Feynman parameters (the even-`L` case: no half-integer branch). The energy integral is
`QED.Integration.TwoLoop.integral_inv_neg_quadratic_add_pow`, the spatial one
`QED.Integration.TwoLoop.integral_inv_quadForm_shifted_add_pow`; this is the pointwise core of
`QED.Integration.TwoLoop.jointEnergyFirstIntegral_prod_inv_lineDenom`.

Scope: the link from `euclidVacuumTwo` to the Lee–Pomeransky integrals of `QED.DimReg`
(`QED.DimReg.FeynmanFamily.integral`) needs the orthant ↔ simplex equivalence, which is not
proved here (P2 design memo, file `TwoLoopBridgeLP`).

## Main statements

* `QED.DimReg.TwoLoopBridge.jointEnergyFirstIntegral_wickKernelTwo`: the exact value at `ε > 0`,
  with `integrable_wickKernelTwo_time`, `integrable_wickKernelTwo_space`.
* `QED.DimReg.TwoLoopBridge.tendsto_jointEnergyFirstIntegral_wickKernelTwo`: the limit.
* `QED.DimReg.TwoLoopBridge.euclidVacuumTwo_four`: the Euclidean value at `d = 4`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Matrix
open QED.Integration.TwoLoop
open QED.Integration.Spatial (quadForm quadForm_eq_sum)
open scoped Real

namespace QED.DimReg.TwoLoopBridge

/-- The Minkowski quadratic form `ℓᵀ A ℓ = Σ_{s,t} A_{st} ℓ_s·ℓ_t` of two loop momenta. -/
noncomputable def minkQuad (A : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℝ :=
  ∑ s, ∑ t, A s t * Minkowski.dot (ℓ s) (ℓ t)

/-- The two-loop point kernel `(ℓᵀ A ℓ + V - iε)^{-n}` of the joint energy-first prescription. -/
noncomputable def wickKernelTwo (A : Matrix (Fin 2) (Fin 2) ℝ) (V ε : ℝ) (n : ℕ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((((minkQuad A ℓ + V : ℝ) : ℂ) - ε * I)) ^ n)⁻¹

/-- The Euclidean two-loop point value of the dimensionally regularized side,
`Γ(n - d)/Γ(n) (det A)^{-d/2} V^{d-n}`. -/
noncomputable def euclidVacuumTwo (detA V : ℝ) (n : ℕ) (d : ℂ) : ℂ :=
  Gamma (n - d) / Gamma n * (detA : ℂ) ^ (-(d / 2)) * (V : ℂ) ^ (d - n)

theorem dot_cons_cons (a b : ℝ) (x y : Fin 3 → ℝ) :
    Minkowski.dot (Fin.cons a x : Fin 4 → ℝ) (Fin.cons b y) = -(a * b) + ∑ k, x k * y k := by
  rw [Minkowski.dot_eq, Fin.sum_univ_three]
  change -(a * b) + x 0 * y 0 + x 1 * y 1 + x 2 * y 2 = _
  ring

theorem minkQuad_cons (A : Matrix (Fin 2) (Fin 2) ℝ) (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    minkQuad A (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) = -(t ⬝ᵥ A *ᵥ t) + quadForm A v := by
  simp only [minkQuad, dot_cons_cons, quadForm_eq_sum, dotProduct, mulVec, Fin.sum_univ_two,
    Fin.sum_univ_three]
  ring

theorem wickKernelTwo_cons (A : Matrix (Fin 2) (Fin 2) ℝ) (V ε : ℝ) (n : ℕ) (t : Fin 2 → ℝ)
    (v : Fin 2 → Fin 3 → ℝ) :
    wickKernelTwo A V ε n (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      ((-((t ⬝ᵥ A *ᵥ t : ℝ) : ℂ) + (((quadForm A v : ℝ) : ℂ) + ((V : ℂ) - ε * I))) ^ n)⁻¹ := by
  rw [wickKernelTwo, minkQuad_cons]
  push_cast
  ring_nf

theorem im_spatial_w (A : Matrix (Fin 2) (Fin 2) ℝ) (V ε : ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    (((quadForm A v : ℝ) : ℂ) + ((V : ℂ) - ε * I)).im = -ε := by
  simp

/-- The energy stage is integrable at every `ε > 0`. -/
theorem integrable_wickKernelTwo_time {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (V : ℝ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable fun t : Fin 2 → ℝ =>
      wickKernelTwo A V ε n (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) := by
  simp_rw [wickKernelTwo_cons]
  exact integrable_inv_neg_quadratic_add_pow hA (by rw [im_spatial_w]; linarith) hn

theorem integral_wickKernelTwo_time {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (V : ℝ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) (v : Fin 2 → Fin 3 → ℝ) :
    ∫ t : Fin 2 → ℝ, wickKernelTwo A V ε n (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      -(π / ((n : ℂ) - 1)) * ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ *
        (((((quadForm A v : ℝ) : ℂ) + ((V : ℂ) - ε * I)) ^ (n - 1))⁻¹) := by
  simp_rw [wickKernelTwo_cons]
  exact integral_inv_neg_quadratic_add_pow hA (by rw [im_spatial_w]; linarith) hn

theorem im_V_sub (V ε : ℝ) : ((V : ℂ) - ε * I).im = -ε := by simp

/-- The spatial stage is integrable at every `ε > 0`, for `n ≥ 5`. -/
theorem integrable_wickKernelTwo_space {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (V : ℝ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 5 ≤ n) :
    Integrable fun v : Fin 2 → Fin 3 → ℝ =>
      ∫ t : Fin 2 → ℝ, wickKernelTwo A V ε n (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) := by
  simp_rw [integral_wickKernelTwo_time hA V hε (by omega : 2 ≤ n)]
  have h := integrable_inv_quadForm_shifted_add_pow hA (w := (V : ℂ) - ε * I)
    (by rw [im_V_sub]; linarith) (k := n - 1) (by omega) 0
  simp only [add_zero] at h
  exact h.const_mul _

/-- **The joint energy-first integral of the two-loop point kernel**, exactly, at `ε > 0`. -/
theorem jointEnergyFirstIntegral_wickKernelTwo {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (V : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (wickKernelTwo A V ε (k + 5)) =
      -((π : ℂ) ^ 4 * (((k : ℂ) + 4) * ((k : ℂ) + 3) * ((k : ℂ) + 2) * ((k : ℂ) + 1))⁻¹ *
        ((A.det ^ 2 : ℝ) : ℂ)⁻¹ * ((((V : ℂ) - ε * I)) ^ (k + 1))⁻¹) := by
  have hdet : 0 < A.det := hA.det_pos
  have hs : 0 < Real.sqrt A.det := Real.sqrt_pos.mpr hdet
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  simp_rw [integral_wickKernelTwo_time hA V hε (by omega : 2 ≤ k + 5)]
  rw [integral_const_mul, show k + 5 - 1 = k + 4 by omega]
  have h := integral_inv_quadForm_shifted_add_pow hA (w := (V : ℂ) - ε * I)
    (by rw [im_V_sub]; linarith) (k := k + 4) (by omega) 0
  simp only [add_zero] at h
  rw [h, show k + 4 - 3 = k + 1 by omega]
  have hsq : Real.sqrt A.det ^ 4 = A.det ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hdet.le]
  have hs' : ((Real.sqrt A.det : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hd2 : ((A.det ^ 2 : ℝ) : ℂ) = ((Real.sqrt A.det : ℝ) : ℂ) ^ 4 := by
    rw [← hsq]; push_cast; ring
  have hw : (V : ℂ) - ε * I ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  rw [hd2]
  push_cast
  have h1 : (k : ℂ) + 5 - 1 = (k : ℂ) + 4 := by ring
  have h2 : (k : ℂ) + 4 - 1 = (k : ℂ) + 3 := by ring
  have h3 : (k : ℂ) + 4 - 2 = (k : ℂ) + 2 := by ring
  have h4 : (k : ℂ) + 4 - 3 = (k : ℂ) + 1 := by ring
  rw [h1, h2, h3, h4]
  have k1 : (k : ℂ) + 1 ≠ 0 := by norm_cast
  have k2 : (k : ℂ) + 2 ≠ 0 := by norm_cast
  have k3 : (k : ℂ) + 3 ≠ 0 := by norm_cast
  have k4 : (k : ℂ) + 4 ≠ 0 := by norm_cast
  field_simp

/-- The Euclidean value at `d = 4`: `Γ(N - 4)/Γ(N) (det A)^{-2} V^{4-N}` for `N = k + 5`. -/
theorem euclidVacuumTwo_four {detA V : ℝ} (hd : 0 < detA) (hV : 0 < V) (k : ℕ) :
    euclidVacuumTwo detA V (k + 5) 4 =
      (((k : ℂ) + 4) * ((k : ℂ) + 3) * ((k : ℂ) + 2) * ((k : ℂ) + 1))⁻¹ *
        ((detA ^ 2 : ℝ) : ℂ)⁻¹ * ((V : ℂ) ^ (k + 1))⁻¹ := by
  have hd' : (detA : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
  have hV' : (V : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV.ne'
  have g1 : Gamma (((k + 5 : ℕ) : ℂ) - 4) = k.factorial := by
    rw [show ((k + 5 : ℕ) : ℂ) - 4 = (k : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have g2 : Gamma ((k + 5 : ℕ) : ℂ) = (k + 4).factorial := by
    rw [show ((k + 5 : ℕ) : ℂ) = ((k + 4 : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  have c1 : (detA : ℂ) ^ (-((4 : ℂ) / 2)) = ((detA : ℂ) ^ 2)⁻¹ := by
    rw [show -((4 : ℂ) / 2) = -((2 : ℕ) : ℂ) by norm_num, cpow_neg, cpow_natCast]
  have c2 : (V : ℂ) ^ ((4 : ℂ) - ((k + 5 : ℕ) : ℂ)) = ((V : ℂ) ^ (k + 1))⁻¹ := by
    rw [show (4 : ℂ) - ((k + 5 : ℕ) : ℂ) = -((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]
  rw [euclidVacuumTwo, g1, g2, c1, c2]
  have hf : ((k + 4).factorial : ℂ) =
      ((k : ℂ) + 4) * ((k : ℂ) + 3) * ((k : ℂ) + 2) * ((k : ℂ) + 1) * k.factorial := by
    simp only [Nat.factorial_succ]
    push_cast
    ring
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [hf]
  push_cast
  field_simp

/-- **The two-loop Wick rotation at a Feynman-parameter point, as a theorem.** For a positive
definite `A`, `V > 0` and `N = k + 5 ≥ 5`, the model's joint energy-first integral of
`(ℓᵀ A ℓ + V - iε)^{-N}` tends, as `ε → 0⁺`, to `(i π²)²` times the Euclidean value
`Γ(N - 4)/Γ(N) (det A)^{-2} V^{4-N}` of the dimensionally regularized side at `d = 4`. -/
theorem tendsto_jointEnergyFirstIntegral_wickKernelTwo {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {V : ℝ} (hV : 0 < V) (k : ℕ) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (wickKernelTwo A V ε (k + 5)))
      (𝓝[>] 0) (𝓝 ((I * (π : ℂ) ^ 2) ^ 2 * euclidVacuumTwo A.det V (k + 5) 4)) := by
  have hV' : (V : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV.ne'
  have hc : Tendsto (fun ε : ℝ => (((V : ℂ) - ε * I) ^ (k + 1))⁻¹) (𝓝[>] 0)
      (𝓝 (((V : ℂ) ^ (k + 1))⁻¹)) := by
    have h0 : Tendsto (fun ε : ℝ => (V : ℂ) - ε * I) (𝓝 0) (𝓝 (V : ℂ)) := by
      have : Continuous fun ε : ℝ => (V : ℂ) - ε * I := by fun_prop
      simpa using this.tendsto 0
    exact ((h0.pow (k + 1)).inv₀ (pow_ne_zero _ hV')).mono_left nhdsWithin_le_nhds
  have h := (hc.const_mul ((π : ℂ) ^ 4 *
    (((k : ℂ) + 4) * ((k : ℂ) + 3) * ((k : ℂ) + 2) * ((k : ℂ) + 1))⁻¹ *
      ((A.det ^ 2 : ℝ) : ℂ)⁻¹)).neg
  rw [euclidVacuumTwo_four hA.det_pos hV]
  have e : (I * (π : ℂ) ^ 2) ^ 2 *
      ((((k : ℂ) + 4) * ((k : ℂ) + 3) * ((k : ℂ) + 2) * ((k : ℂ) + 1))⁻¹ *
        ((A.det ^ 2 : ℝ) : ℂ)⁻¹ * ((V : ℂ) ^ (k + 1))⁻¹) =
      -((π : ℂ) ^ 4 * (((k : ℂ) + 4) * ((k : ℂ) + 3) * ((k : ℂ) + 2) * ((k : ℂ) + 1))⁻¹ *
        ((A.det ^ 2 : ℝ) : ℂ)⁻¹ * ((V : ℂ) ^ (k + 1))⁻¹) := by
    rw [mul_pow, I_sq]; ring
  rw [e]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [jointEnergyFirstIntegral_wickKernelTwo hA V hε k]

end QED.DimReg.TwoLoopBridge

end
