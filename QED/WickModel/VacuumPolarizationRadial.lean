/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationAlgebra
public import QED.Integration.SpatialIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pauli–Villars-summed spatial integrals of the vacuum polarization

At `ε = 0`, after the loop-energy integral, the translation of the spatial momentum and the
symmetrization `w⃗ ↦ -w⃗`, the vacuum polarization at fixed Feynman parameter reduces to two
Pauli–Villars-summed integrals over `w⃗ ∈ ℝ³`, with `W_f = |w⃗|² + D_f`, `∑ c_f = 0` and
`∑ c_f D_f = 0`:

* `integral_radialSum`: `∫ ∑_f c_f W_f^{-3/2} d³w = -2π ∑_f c_f log D_f`, from the paired
  logarithmic integral of `QED.Integration`.
* `integral_radialPiece_eq_zero`: `∫ ∑_f c_f W_f^{-3/2} (ŵ^μ ŵ^ν - h^{μν} W_f) d³w = 0`, with
  `ŵ = (0, w⃗)` and `h^{μν}` the spatial projector. This is the covariance of the energy-first
  prescription after the Pauli–Villars sum: the time components vanish identically, the
  off-diagonal spatial ones by parity, and the diagonal ones because, after averaging over the
  three axes, the radial integrand is the derivative `-(d/dr)(r³ ∑_f c_f (r² + D_f)^{-1/2})`,
  whose boundary terms vanish thanks to both Pauli–Villars conditions.

The declarations here are internal helpers of packet 6b, not source-facing definitions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QED.WickModel

namespace VacuumPolarizationLimit

open QED.Integration

/-- The spatial projector `h^{μν} = δ^μ_0 δ^ν_0 + g^{μν}`. -/
noncomputable def hproj (μ ν : Fin 4) : ℝ := e0 μ * e0 ν + Minkowski.metric μ ν

/-- The Pauli–Villars sum `∑_f c_f (|w|² + D_f)^{-3/2}`. -/
noncomputable def radialSum (c D : Fin 3 → ℝ) (w : Fin 3 → ℝ) : ℝ :=
  ∑ f, c f * (∑ i, w i ^ 2 + D f) ^ (-(3 / 2 : ℝ))

/-- The Pauli–Villars sum `∑_f c_f (|w|² + D_f)^{-3/2} (ŵ^μ ŵ^ν - h^{μν} (|w|² + D_f))`. -/
noncomputable def radialPiece (c D : Fin 3 → ℝ) (μ ν : Fin 4) (w : Fin 3 → ℝ) : ℝ :=
  ∑ f, c f * ((∑ i, w i ^ 2 + D f) ^ (-(3 / 2 : ℝ)) *
    ((Fin.cons 0 w : Fin 4 → ℝ) μ * (Fin.cons 0 w : Fin 4 → ℝ) ν
      - hproj μ ν * (∑ i, w i ^ 2 + D f)))

/-! ### The logarithmic integral -/

/-- With `∑ c_f = 0`, the sum is a combination of Pauli–Villars pairs. -/
theorem radialSum_eq {c D : Fin 3 → ℝ} (hc : ∑ f, c f = 0) (w : Fin 3 → ℝ) :
    radialSum c D w = c 1 * ((∑ i, w i ^ 2 + D 1) ^ (-(3 / 2 : ℝ))
        - (∑ i, w i ^ 2 + D 0) ^ (-(3 / 2 : ℝ)))
      + c 2 * ((∑ i, w i ^ 2 + D 2) ^ (-(3 / 2 : ℝ)) - (∑ i, w i ^ 2 + D 0) ^ (-(3 / 2 : ℝ))) := by
  rw [Fin.sum_univ_three] at hc
  simp only [radialSum, Fin.sum_univ_three]
  linear_combination ((w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 + D 0) ^ (-(3 / 2 : ℝ))) * hc

/-- `∑_f c_f (|w|² + D_f)^{-3/2}` is integrable when `∑ c_f = 0`. -/
theorem integrable_radialSum {c D : Fin 3 → ℝ} (hD : ∀ f, 0 < D f) (hc : ∑ f, c f = 0) :
    Integrable (radialSum c D) := by
  have h := ((integrable_sum_sq_add_rpow_neg_three_halves_sub (hD 1) (hD 0)).const_mul (c 1)).add
    ((integrable_sum_sq_add_rpow_neg_three_halves_sub (hD 2) (hD 0)).const_mul (c 2))
  exact h.congr (Eventually.of_forall fun w => (radialSum_eq hc w).symm)

/-- **The logarithmic integral**: `∫ ∑_f c_f (|w|² + D_f)^{-3/2} d³w = -2π ∑_f c_f log D_f`
when `∑ c_f = 0`. -/
theorem integral_radialSum {c D : Fin 3 → ℝ} (hD : ∀ f, 0 < D f) (hc : ∑ f, c f = 0) :
    ∫ w, radialSum c D w = -(2 * π * ∑ f, c f * Real.log (D f)) := by
  have i1 := integrable_sum_sq_add_rpow_neg_three_halves_sub (hD 1) (hD 0)
  have i2 := integrable_sum_sq_add_rpow_neg_three_halves_sub (hD 2) (hD 0)
  rw [integral_congr_ae (Eventually.of_forall fun w => radialSum_eq hc w),
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_sum_sq_add_rpow_neg_three_halves_sub (hD 1) (hD 0),
    integral_sum_sq_add_rpow_neg_three_halves_sub (hD 2) (hD 0),
    Real.log_div (hD 0).ne' (hD 1).ne', Real.log_div (hD 0).ne' (hD 2).ne']
  rw [Fin.sum_univ_three] at hc ⊢
  linear_combination (2 * π * Real.log (D 0)) * hc

/-! ### The covariance integral -/

/-- The integral is invariant under the transposition of two coordinates. -/
theorem integral_comp_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin 3 → ℝ) → E) (i j : Fin 3) :
    ∫ v : Fin 3 → ℝ, F (fun l => v (Equiv.swap i j l)) = ∫ v, F v := by
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
    MeasurableEquiv.arrowCongr' (Equiv.swap i j) (MeasurableEquiv.refl ℝ)
  have hmp : MeasurePreserving e :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  exact hmp.integral_comp' F

/-- The diagonal spatial components. -/
theorem radialPiece_succ_succ (c D : Fin 3 → ℝ) (i : Fin 3) (w : Fin 3 → ℝ) :
    radialPiece c D i.succ i.succ w = ∑ f, c f * ((∑ l, w l ^ 2 + D f) ^ (-(3 / 2 : ℝ)) *
      (w i ^ 2 - (∑ l, w l ^ 2 + D f))) := by
  have hh : hproj i.succ i.succ = 1 := by
    simp [hproj, e0, Minkowski.metric, Fin.succ_ne_zero]
  simp only [radialPiece, Fin.cons_succ, hh, one_mul, sq]

/-- The off-diagonal spatial components. -/
theorem radialPiece_succ_succ_of_ne (c D : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j)
    (w : Fin 3 → ℝ) :
    radialPiece c D i.succ j.succ w
      = (w i * w j) • (∑ f, c f * (∑ l, w l ^ 2 + D f) ^ (-(3 / 2 : ℝ))) := by
  have hh : hproj i.succ j.succ = 0 := by
    simp [hproj, e0, Minkowski.metric, Fin.succ_inj, hij]
  simp only [radialPiece, Fin.cons_succ, hh, zero_mul, sub_zero, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- The time components vanish identically. -/
theorem radialPiece_zero_left (c D : Fin 3 → ℝ) (ν : Fin 4) (w : Fin 3 → ℝ) :
    radialPiece c D 0 ν w = 0 := by
  have hh : hproj 0 ν = 0 := by
    refine Fin.cases ?_ (fun j => ?_) ν
    · simp [hproj, e0, Minkowski.metric]
    · simp [hproj, e0, Minkowski.metric, (Fin.succ_ne_zero j).symm]
  simp [radialPiece, hh]

/-- The time components vanish identically. -/
theorem radialPiece_zero_right (c D : Fin 3 → ℝ) (μ : Fin 4) (w : Fin 3 → ℝ) :
    radialPiece c D μ 0 w = 0 := by
  have hh : hproj μ 0 = 0 := by
    refine Fin.cases ?_ (fun j => ?_) μ
    · simp [hproj, e0, Minkowski.metric]
    · simp [hproj, e0, Minkowski.metric, Fin.succ_ne_zero j]
  simp [radialPiece, hh]

/-- `X^{-1/2} = X^{-3/2} X` for `X > 0`. -/
theorem rpow_neg_half_eq {X : ℝ} (hX : 0 < X) :
    X ^ (-(1 / 2 : ℝ)) = X ^ (-(3 / 2 : ℝ)) * X := by
  rw [show -(1 / 2 : ℝ) = -(3 / 2) + 1 by norm_num, Real.rpow_add hX, Real.rpow_one]

/-- The radial profile `Ψ(ρ) = ∑_f c_f (ρ + D_f)^{-3/2} (ρ - 3 (ρ + D_f))` of the sum of the three
diagonal components. -/
noncomputable def radialPsi (c D : Fin 3 → ℝ) (ρ : ℝ) : ℝ :=
  ∑ f, c f * ((ρ + D f) ^ (-(3 / 2 : ℝ)) * (ρ - 3 * (ρ + D f)))

/-- An antiderivative of `r² Ψ(r²)`: `-r³ ∑_f c_f (r² + D_f)^{-1/2}`. -/
theorem hasDerivAt_radialPsi {c D : Fin 3 → ℝ} (hD : ∀ f, 0 < D f) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(r ^ 3 * ∑ f, c f * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ))))
      (r ^ 2 * radialPsi c D (r ^ 2)) r := by
  have hX : ∀ f, 0 < r ^ 2 + D f := fun f => add_pos_of_nonneg_of_pos (sq_nonneg r) (hD f)
  have hd : ∀ f, HasDerivAt (fun r : ℝ => (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)))
      (2 * r * (-(1 / 2 : ℝ)) * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ) - 1)) r := fun f => by
    have h := ((hasDerivAt_pow 2 r).add_const (D f)).rpow_const (p := -(1 / 2 : ℝ))
      (Or.inl (hX f).ne')
    simpa using h
  have hsum : HasDerivAt (fun r : ℝ => ∑ f, c f * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)))
      (∑ f, c f * (2 * r * (-(1 / 2 : ℝ)) * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ) - 1))) r :=
    HasDerivAt.fun_sum fun f _ => (hd f).const_mul (c f)
  have h := ((hasDerivAt_pow 3 r).mul hsum).neg
  refine h.congr_deriv ?_
  have e1 : ∀ f, (r ^ 2 + D f) ^ (-(1 / 2 : ℝ) - 1) = (r ^ 2 + D f) ^ (-(3 / 2 : ℝ)) := fun f => by
    norm_num
  simp only [e1, rpow_neg_half_eq (hX _), radialPsi, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

/-- For `r > 0` and `D > 0`, `0 ≤ r³ (r² + D)^{-1/2} - r² + D/2 ≤ (3/8) D² / r²`. -/
theorem rpow_neg_half_expansion_bound {r D : ℝ} (hr : 0 < r) (hD : 0 < D) :
    0 ≤ r ^ 3 * (r ^ 2 + D) ^ (-(1 / 2 : ℝ)) - r ^ 2 + D / 2 ∧
      r ^ 3 * (r ^ 2 + D) ^ (-(1 / 2 : ℝ)) - r ^ 2 + D / 2 ≤ 3 / 8 * D ^ 2 / r ^ 2 := by
  have hX : 0 < r ^ 2 + D := by positivity
  set S := √(r ^ 2 + D) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 hX
  have hS2 : S ^ 2 = r ^ 2 + D := Real.sq_sqrt hX.le
  have hSr : r ≤ S := by nlinarith
  have hrp : (r ^ 2 + D) ^ (-(1 / 2 : ℝ)) = S⁻¹ := by
    rw [Real.rpow_neg hX.le, hS, Real.sqrt_eq_rpow]
  rw [hrp]
  have key : (r ^ 3 * S⁻¹ - r ^ 2 + D / 2) * (2 * S) = (S - r) ^ 2 * (S + 2 * r) := by
    field_simp
    linear_combination (-S) * hS2
  have hE : r ^ 3 * S⁻¹ - r ^ 2 + D / 2 = (S - r) ^ 2 * (S + 2 * r) / (2 * S) := by
    rw [← key]
    field_simp
  rw [hE]
  constructor
  · positivity
  · have h1 : (S - r) * (S + r) = D := by linear_combination hS2
    have h2 : (S - r) * (2 * r) ≤ D := by nlinarith
    have h3 : S - r ≤ D / (2 * r) := by rw [le_div_iff₀ (by positivity)]; exact h2
    have h4 : (S - r) ^ 2 ≤ (D / (2 * r)) ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
    have h5 : (S + 2 * r) / (2 * S) ≤ 3 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc (S - r) ^ 2 * (S + 2 * r) / (2 * S) = (S - r) ^ 2 * ((S + 2 * r) / (2 * S)) := by ring
      _ ≤ (D / (2 * r)) ^ 2 * (3 / 2) := by gcongr
      _ = 3 / 8 * D ^ 2 / r ^ 2 := by field_simp; ring

/-- **The boundary term vanishes at infinity**: `r³ ∑_f c_f (r² + D_f)^{-1/2} → 0` when
`∑ c_f = 0` and `∑ c_f D_f = 0`. -/
theorem tendsto_radialPsi_antideriv {c D : Fin 3 → ℝ} (hD : ∀ f, 0 < D f)
    (hc : ∑ f, c f = 0) (hcD : ∑ f, c f * D f = 0) :
    Tendsto (fun r : ℝ => -(r ^ 3 * ∑ f, c f * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)))) atTop (𝓝 0) := by
  set C : ℝ := ∑ f, |c f| * (3 / 8 * D f ^ 2)
  have hlim : Tendsto (fun r : ℝ => C / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hrw : -(r ^ 3 * ∑ f, c f * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)))
      = -∑ f, c f * (r ^ 3 * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)) - r ^ 2 + D f / 2) := by
    have e : ∑ f, c f * (r ^ 3 * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)) - r ^ 2 + D f / 2)
        = r ^ 3 * ∑ f, c f * (r ^ 2 + D f) ^ (-(1 / 2 : ℝ)) - r ^ 2 * ∑ f, c f
          + (∑ f, c f * D f) / 2 := by
      simp only [Fin.sum_univ_three]
      ring
    rw [e, hc, hcD]
    ring
  rw [hrw, norm_neg, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hC : C / r ^ 2 = ∑ f, |c f| * (3 / 8 * D f ^ 2 / r ^ 2) := by
    simp only [C, Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  rw [hC]
  refine Finset.sum_le_sum fun f _ => ?_
  have hb := rpow_neg_half_expansion_bound hr (hD f)
  rw [abs_mul, abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)

/-- `∫₀^∞ r² Ψ(r²) dr = 0`. -/
theorem integral_Ioi_radialPsi {c D : Fin 3 → ℝ} (hD : ∀ f, 0 < D f) (hc : ∑ f, c f = 0)
    (hcD : ∑ f, c f * D f = 0)
    (hint : IntegrableOn (fun r : ℝ => r ^ 2 * radialPsi c D (r ^ 2)) (Ioi 0)) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * radialPsi c D (r ^ 2) = 0 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ => hasDerivAt_radialPsi hD r) hint
    (tendsto_radialPsi_antideriv hD hc hcD)]
  simp

/-- **The covariance integral vanishes**: `∫ ∑_f c_f W_f^{-3/2} (ŵ^μ ŵ^ν - h^{μν} W_f) d³w = 0`
when `∑ c_f = 0`, `∑ c_f D_f = 0`, and the three diagonal components are integrable. -/
theorem integral_radialPiece_eq_zero {c D : Fin 3 → ℝ} (hD : ∀ f, 0 < D f)
    (hc : ∑ f, c f = 0) (hcD : ∑ f, c f * D f = 0)
    (hdiag : ∀ i : Fin 3, Integrable (radialPiece c D i.succ i.succ)) (μ ν : Fin 4) :
    ∫ w, radialPiece c D μ ν w = 0 := by
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [radialPiece_zero_left]
  refine Fin.cases ?_ (fun j => ?_) ν
  · simp [radialPiece_zero_right]
  by_cases hij : i = j
  swap
  · simp_rw [radialPiece_succ_succ_of_ne c D hij]
    exact integral_coord_mul_coord_smul_radial
      (fun ρ => ∑ f, c f * (ρ + D f) ^ (-(3 / 2 : ℝ))) hij
  subst hij
  -- all diagonal components have the same integral
  have hsame : ∀ a b : Fin 3,
      ∫ w, radialPiece c D a.succ a.succ w = ∫ w, radialPiece c D b.succ b.succ w := by
    intro a b
    rw [← integral_comp_swap (fun w => radialPiece c D a.succ a.succ w) a b]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [radialPiece_succ_succ, Equiv.swap_apply_left]
    have hs : ∑ l, w (Equiv.swap a b l) ^ 2 = ∑ l, w l ^ 2 :=
      Equiv.sum_comp (Equiv.swap a b) (fun l => w l ^ 2)
    rw [hs]
  -- their sum is radial
  have hsum : ∀ w, radialPiece c D (0 : Fin 3).succ (0 : Fin 3).succ w
      + radialPiece c D (1 : Fin 3).succ (1 : Fin 3).succ w
      + radialPiece c D (2 : Fin 3).succ (2 : Fin 3).succ w = radialPsi c D (∑ l, w l ^ 2) := by
    intro w
    simp only [radialPiece_succ_succ, radialPsi, Fin.sum_univ_three]
    ring
  have hint : Integrable fun w : Fin 3 → ℝ => radialPsi c D (∑ l, w l ^ 2) :=
    (((hdiag 0).add (hdiag 1)).add (hdiag 2)).congr (Eventually.of_forall hsum)
  have hrad : ∫ w : Fin 3 → ℝ, radialPsi c D (∑ l, w l ^ 2) = 0 := by
    rw [integral_comp_sum_sq]
    have hI := (integrable_comp_sum_sq_iff (radialPsi c D)).1 hint
    simp only [smul_eq_mul] at hI ⊢
    rw [integral_Ioi_radialPsi hD hc hcD hI, mul_zero]
  have e := integral_congr_ae (μ := volume)
    (f := fun w => radialPiece c D (0 : Fin 3).succ (0 : Fin 3).succ w
      + radialPiece c D (1 : Fin 3).succ (1 : Fin 3).succ w
      + radialPiece c D (2 : Fin 3).succ (2 : Fin 3).succ w)
    (g := fun w : Fin 3 → ℝ => radialPsi c D (∑ l, w l ^ 2)) (Eventually.of_forall hsum)
  have h3 : ∫ w : Fin 3 → ℝ, radialPsi c D (∑ l, w l ^ 2)
      = 3 * ∫ w, radialPiece c D i.succ i.succ w := by
    rw [← e, integral_add (f := fun w => radialPiece c D (0 : Fin 3).succ (0 : Fin 3).succ w
      + radialPiece c D (1 : Fin 3).succ (1 : Fin 3).succ w) ((hdiag 0).add (hdiag 1)) (hdiag 2),
      integral_add (hdiag 0) (hdiag 1),
      hsame 0 i, hsame 1 i, hsame 2 i]
    ring
  rw [hrad] at h3
  linarith

end VacuumPolarizationLimit

end QED.WickModel

end
