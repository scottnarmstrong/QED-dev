/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopBridgeTraceX
public import QED.TwoLoop.UnitXCloseLimit
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The crossed-ladder bridge, first step: the `d`-dimensional merged integrand

The X unit of the model is the four-dimensional integral
`∫_{Δ₄} crossedZero = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)` of the massless merged
integrand `crossedTerm 0 0 = z_M [Ψ₁(z_M/2)/(2U⁶E²) - Ψ₂(z_M/2)/(2U⁵E)]`
(`QED.TwoLoop.UnitXClose.crossedZero`, `QED.TwoLoop.UnitXGraph.crossedTerm`), in the group
variables `(z_A, z_M, z_c, z_a, z_b)` of the crossed ladder, `U = gXU`, `E = gXE = Ẽ/U`.

On the dimensionally regularized side the photons are massless and there is no Pauli–Villars
pair, so the crossed ladder has six lines `(z_A, t, z_M - t, z_c, z_a, z_b)`, all of index `1`.
With the projected numerator in the scheme of `QED/DimReg/TwoLoopBridgeTraceX.lean`
(`T₁ᵈ ∝ Ψ₁ᵈ`, `T₂ᵈ ∝ Ψ₂ᵈ`, `T₃ᵈ = 0`), the parametric formula with numerators
(`QED/DimReg/TwoLoopBridgeSchwingerNum.lean`: degree `0` with `Γ(a)`, one contraction with
`Γ(a - 1)`, `a = 6 - d`) gives the integrand
`U^(-d/2) (Γ(6 - d) E^(d-6) Ψ₁ᵈ/U⁴ - Γ(5 - d) E^(d-5) Ψ₂ᵈ/U³) / 2`
on the six-line simplex (the relative weight `-1` of the two terms is `½ · (-1024)/512`, from the
normalizations `512`, `-1024` of `c₂[T₁ᵈ]`, `c₂[T₂ᵈ]` and the factor `½` of a contraction).
Its overall constant (`π`, `Γ`, coupling and measure factors) is not fixed here.

* `psiT1d_affine`, `psiT2d_affine`: `Ψ₁ᵈ`, `Ψ₂ᵈ` are affine in the slot data `bₖ`, which are
  affine in the split `t`; so the split integrates to `z_M` times the midpoint value in every
  dimension (`integral_gPsi1d`, `integral_gPsi2d`), as at `d = 4`
  (`QED.TwoLoop.UnitXGraph.gPsi1_affine`).
* `xTermD`: the merged `d`-dimensional integrand on `Δ₄`.
* `xTermD_four`: **at `d = 4` it is the model's massless integrand**,
  `xTermD 4 = crossedTerm 0 0`, wherever `U, E ≠ 0`.

The remaining steps of the X bridge (domination of `xTermD d` uniformly for `d` near `4`, and the
identification of `∫_{Δ₄} xTermD d` with the combination of `FeynmanFamily` values of the
crossed family) are not in this file.
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.DimReg.TwoLoopBridgeX

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose QED.DimReg.TwoLoopBridgeTrace

/-! ### Affinity in the split -/

theorem psiT1d_affine (d a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 u t : ℂ) :
    psiT1d d a0 a1 a2 a3 (b0 + t * d0) (b1 + t * d1) (b2 + t * d2) (b3 + t * d3) u =
      psiT1d d a0 a1 a2 a3 b0 b1 b2 b3 u +
        t * (psiT1d d a0 a1 a2 a3 (b0 + d0) (b1 + d1) (b2 + d2) (b3 + d3) u -
          psiT1d d a0 a1 a2 a3 b0 b1 b2 b3 u) := by
  simp only [psiT1d]; ring

theorem psiT2d_affine (d a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 c01 c02 c03 c12 c13 c23 u t : ℂ) :
    psiT2d d a0 a1 a2 a3 (b0 + t * d0) (b1 + t * d1) (b2 + t * d2) (b3 + t * d3) c01 c02 c03
        c12 c13 c23 u =
      psiT2d d a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u +
        t * (psiT2d d a0 a1 a2 a3 (b0 + d0) (b1 + d1) (b2 + d2) (b3 + d3) c01 c02 c03 c12 c13
          c23 u - psiT2d d a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u) := by
  simp only [psiT2d]; ring

/-- `Ψ₁ᵈ` in the group sums and the split `t` (the `d`-dimensional `gPsi1`). -/
noncomputable def gPsi1d (d : ℂ) (A t M c a b : ℝ) : ℂ :=
  psiT1d d (gXan A M c a b 0) (gXan A M c a b 1) (gXan A M c a b 2) (gXan A M c a b 3)
    (gXbn A t M c a b 0) (gXbn A t M c a b 1) (gXbn A t M c a b 2) (gXbn A t M c a b 3)
    (gXU A M c a b)

/-- `Ψ₂ᵈ` in the group sums and the split `t` (the `d`-dimensional `gPsi2`). -/
noncomputable def gPsi2d (d : ℂ) (A t M c a b : ℝ) : ℂ :=
  psiT2d d (gXan A M c a b 0) (gXan A M c a b 1) (gXan A M c a b 2) (gXan A M c a b 3)
    (gXbn A t M c a b 0) (gXbn A t M c a b 1) (gXbn A t M c a b 2) (gXbn A t M c a b 3)
    (A + a) (A + a) (-M) (A + c + a + b) (c + b) (c + b) (gXU A M c a b)

theorem gPsi1d_four (A t M c a b : ℝ) : gPsi1d 4 A t M c a b = (gPsi1 A t M c a b : ℂ) :=
  psiT1d_four _ _ _ _ _ _ _ _ _

theorem gPsi2d_four (A t M c a b : ℝ) : gPsi2d 4 A t M c a b = (gPsi2 A t M c a b : ℂ) := by
  rw [gPsi2d, gPsi2, ← psiT2d_four]
  push_cast
  rfl

theorem gXbn_affine_ofReal (A t M c a b : ℝ) (k : Fin 4) :
    (gXbn A t M c a b k : ℂ) =
      gXbn A 0 M c a b k + t * (gXbn A 1 M c a b k - gXbn A 0 M c a b k) := by
  rw [gXbn_affine A t M c a b k]
  push_cast
  ring

/-- `Ψ₁ᵈ` is affine in the split. -/
theorem gPsi1d_affine (d : ℂ) (A t M c a b : ℝ) :
    gPsi1d d A t M c a b =
      gPsi1d d A 0 M c a b + t * (gPsi1d d A 1 M c a b - gPsi1d d A 0 M c a b) := by
  unfold gPsi1d
  rw [gXbn_affine_ofReal A t M c a b 0, gXbn_affine_ofReal A t M c a b 1,
    gXbn_affine_ofReal A t M c a b 2, gXbn_affine_ofReal A t M c a b 3, psiT1d_affine]
  simp only [add_sub_cancel]

/-- `Ψ₂ᵈ` is affine in the split. -/
theorem gPsi2d_affine (d : ℂ) (A t M c a b : ℝ) :
    gPsi2d d A t M c a b =
      gPsi2d d A 0 M c a b + t * (gPsi2d d A 1 M c a b - gPsi2d d A 0 M c a b) := by
  unfold gPsi2d
  rw [gXbn_affine_ofReal A t M c a b 0, gXbn_affine_ofReal A t M c a b 1,
    gXbn_affine_ofReal A t M c a b 2, gXbn_affine_ofReal A t M c a b 3, psiT2d_affine]
  simp only [add_sub_cancel]

/-- The integral of a complex affine function of `t` is the length times the midpoint value. -/
theorem integral_affine_eq_mid {f : ℝ → ℂ} (p q : ℂ) (hf : ∀ t : ℝ, f t = p + t * q) (M : ℝ) :
    ∫ t in (0 : ℝ)..M, f t = M * f (M / 2) := by
  have hi : IntervalIntegrable (fun t : ℝ => (t : ℂ) * q) volume 0 M :=
    ((continuous_ofReal.mul continuous_const)).intervalIntegrable 0 M
  rw [intervalIntegral.integral_congr (g := fun t => p + t * q) fun t _ => hf t,
    intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, integral_id, hf]
  simp only [real_smul, sub_zero]
  push_cast
  ring

/-- **The split in `d` dimensions (`Ψ₁ᵈ`)**: `∫₀^{z_M} Ψ₁ᵈ dt = z_M Ψ₁ᵈ(z_M/2)`. -/
theorem integral_gPsi1d (d : ℂ) (A M c a b : ℝ) :
    ∫ t in (0 : ℝ)..M, gPsi1d d A t M c a b = M * gPsi1d d A (M / 2) M c a b :=
  integral_affine_eq_mid _ _ (fun t => gPsi1d_affine d A t M c a b) M

/-- **The split in `d` dimensions (`Ψ₂ᵈ`)**: `∫₀^{z_M} Ψ₂ᵈ dt = z_M Ψ₂ᵈ(z_M/2)`. -/
theorem integral_gPsi2d (d : ℂ) (A M c a b : ℝ) :
    ∫ t in (0 : ℝ)..M, gPsi2d d A t M c a b = M * gPsi2d d A (M / 2) M c a b :=
  integral_affine_eq_mid _ _ (fun t => gPsi2d_affine d A t M c a b) M

/-! ### The merged integrand -/

/-- **The `d`-dimensional merged crossed-ladder integrand** on `Δ₄`, groups
`(z_A, z_M, z_c, z_a, z_b)`:
`z_M U^(-d/2) (Γ(6 - d) E^(d-6) Ψ₁ᵈ(z_M/2)/U⁴ - Γ(5 - d) E^(d-5) Ψ₂ᵈ(z_M/2)/U³) / 2`. -/
noncomputable def xTermD (d : ℂ) (A M c a b : ℝ) : ℂ :=
  M * (gXU A M c a b : ℂ) ^ (-(d / 2)) *
    (Gamma (6 - d) / 2 * (gXE A M c a b : ℂ) ^ (d - 6) * gPsi1d d A (M / 2) M c a b /
        (gXU A M c a b : ℂ) ^ 4 -
      Gamma (5 - d) / 2 * (gXE A M c a b : ℂ) ^ (d - 5) * gPsi2d d A (M / 2) M c a b /
        (gXU A M c a b : ℂ) ^ 3)

/-- **At `d = 4` the `d`-dimensional integrand is the model's massless integrand**:
`xTermD 4 = crossedTerm 0 0` wherever `U ≠ 0`, `E ≠ 0`. -/
theorem xTermD_four {A M c a b : ℝ} (hU : gXU A M c a b ≠ 0) (hE : gXE A M c a b ≠ 0) :
    xTermD 4 A M c a b = (crossedTerm 0 0 A M c a b : ℂ) := by
  have hU' : (gXU A M c a b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hU
  have hE' : (gXE A M c a b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hE
  have h1 : -((4 : ℂ) / 2) = -((2 : ℕ) : ℂ) := by norm_num
  have h2 : (4 : ℂ) - 6 = -((2 : ℕ) : ℂ) := by norm_num
  have h3 : (4 : ℂ) - 5 = -((1 : ℕ) : ℂ) := by norm_num
  have g2 : Gamma (6 - 4) = 1 := by
    rw [show (6 : ℂ) - 4 = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one, mul_one]
  have g1 : Gamma (5 - 4) = 1 := by rw [show (5 : ℂ) - 4 = 1 by norm_num, Gamma_one]
  rw [xTermD, h1, h2, h3, g2, g1, cpow_neg, cpow_neg, cpow_neg, cpow_natCast, cpow_natCast,
    cpow_natCast, gPsi1d_four, gPsi2d_four, crossedTerm]
  generalize gPsi1 A (M / 2) M c a b = ψ₁
  generalize gPsi2 A (M / 2) M c a b = ψ₂
  push_cast
  simp only [pow_one, ← inv_pow]
  field_simp
  have hEE : (gXE A M c a b : ℂ) ^ 2 * (gXE A M c a b : ℂ)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hE', one_pow]
  linear_combination (-((M : ℂ) * ψ₁ - (M : ℂ) * (gXU A M c a b : ℂ) * (gXE A M c a b : ℂ) * ψ₂)) *
    hEE

end QED.DimReg.TwoLoopBridgeX
