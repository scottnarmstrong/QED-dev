/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The antiderivative of the `z_a`-integration of the crossed ladder

Step 1 of section 4.2 of `docs/TWO-LOOP-UNITS.md`. In the hierarchical variables the massless
integrand is, at fixed `(z₂, z₃, z_A)`, a rational function of `U = b + w` with poles only at
`U = 0` (order `4`) and at `Ẽ = Y² U + b² = 0` (order `2`):
`T(0, 0) = α₁/U + α₂/U² + α₃/U³ + α₄/U⁴ + β₂/Ẽ² - α₁ Y²/Ẽ`
(the residues at `U = 0` and at `Ẽ = 0` cancel, which is the convergence at `z_a → ∞`).
This file gives the antiderivative in this generic shape:

* `outerPrim`: `-α₂/U - α₃/(2U²) - α₄/(3U³) - β₂/(Y² Ẽ) + α₁ log (Y² U/Ẽ)`;
* `hasDerivAt_outerPrim`: its derivative in `U` is the partial-fraction form `outerPF`;
* `tendsto_outerPrim_atTop`: it tends to `0` as `U → ∞`.
-/

@[expose] public section

open Real Filter Topology

namespace QED.TwoLoop.UnitXClose

/-- The partial-fraction form `α₁/U + α₂/U² + α₃/U³ + α₄/U⁴ + β₂/Ẽ² - α₁/Ẽ`, `Ẽ = Y² U + b²`. -/
noncomputable def outerPF (Y b α₁ α₂ α₃ α₄ β₂ U : ℝ) : ℝ :=
  α₁ / U + α₂ / U ^ 2 + α₃ / U ^ 3 + α₄ / U ^ 4 + β₂ / (Y ^ 2 * U + b ^ 2) ^ 2 -
    α₁ * Y ^ 2 / (Y ^ 2 * U + b ^ 2)

/-- Its antiderivative, normalized to vanish at `U = ∞`. -/
noncomputable def outerPrim (Y b α₁ α₂ α₃ α₄ β₂ U : ℝ) : ℝ :=
  -α₂ / U - α₃ / (2 * U ^ 2) - α₄ / (3 * U ^ 3) - β₂ / (Y ^ 2 * (Y ^ 2 * U + b ^ 2)) +
    α₁ * log (Y ^ 2 * U / (Y ^ 2 * U + b ^ 2))

theorem hasDerivAt_outerPrim {Y b α₁ α₂ α₃ α₄ β₂ U : ℝ} (hY : 0 < Y) (hb : 0 < b) (hU : 0 < U) :
    HasDerivAt (outerPrim Y b α₁ α₂ α₃ α₄ β₂) (outerPF Y b α₁ α₂ α₃ α₄ β₂ U) U := by
  have hE : 0 < Y ^ 2 * U + b ^ 2 := by positivity
  have hq : 0 < Y ^ 2 * U / (Y ^ 2 * U + b ^ 2) := by positivity
  have h1 : HasDerivAt (fun U : ℝ => Y ^ 2 * U / (Y ^ 2 * U + b ^ 2))
      ((Y ^ 2 * (Y ^ 2 * U + b ^ 2) - Y ^ 2 * U * Y ^ 2) / (Y ^ 2 * U + b ^ 2) ^ 2) U := by
    have := ((hasDerivAt_id' U).const_mul (Y ^ 2)).div
      (((hasDerivAt_id' U).const_mul (Y ^ 2)).add_const (b ^ 2)) hE.ne'
    convert this using 1
    simp
  have hl := h1.log hq.ne'
  have hU1 : HasDerivAt (fun U : ℝ => -α₂ / U) (α₂ / U ^ 2) U := by
    have := (hasDerivAt_inv hU.ne').const_mul (-α₂)
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have hU2 : HasDerivAt (fun U : ℝ => α₃ / (2 * U ^ 2)) (-(α₃ / U ^ 3)) U := by
    have := ((hasDerivAt_pow 2 U).const_mul 2).inv (by positivity) |>.const_mul α₃
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp; ring
  have hU3 : HasDerivAt (fun U : ℝ => α₄ / (3 * U ^ 3)) (-(α₄ / U ^ 4)) U := by
    have := ((hasDerivAt_pow 3 U).const_mul 3).inv (by positivity) |>.const_mul α₄
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp; ring
  have hE1 : HasDerivAt (fun U : ℝ => β₂ / (Y ^ 2 * (Y ^ 2 * U + b ^ 2)))
      (-(β₂ / (Y ^ 2 * U + b ^ 2) ^ 2)) U := by
    have := ((((hasDerivAt_id' U).const_mul (Y ^ 2)).add_const (b ^ 2)).const_mul (Y ^ 2)).inv
      (by positivity : Y ^ 2 * (Y ^ 2 * U + b ^ 2) ≠ 0) |>.const_mul β₂
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have := (((hU1.sub hU2).sub hU3).sub hE1).add (hl.const_mul α₁)
  convert this using 1
  · funext x; simp only [outerPrim, Pi.add_apply, Pi.sub_apply]
  · simp only [outerPF]
    field_simp
    ring

theorem tendsto_outerPrim_atTop {Y b α₁ α₂ α₃ α₄ β₂ : ℝ} (hY : 0 < Y) :
    Tendsto (outerPrim Y b α₁ α₂ α₃ α₄ β₂) atTop (𝓝 0) := by
  have hinv : Tendsto (fun U : ℝ => U⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hE : Tendsto (fun U : ℝ => Y ^ 2 * U + b ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by positivity))
  have hq : Tendsto (fun U : ℝ => Y ^ 2 * U / (Y ^ 2 * U + b ^ 2)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun U : ℝ => 1 - b ^ 2 * (Y ^ 2 * U + b ^ 2)⁻¹) atTop (𝓝 (1 - b ^ 2 * 0)) :=
      tendsto_const_nhds.sub (hE.inv_tendsto_atTop.const_mul _)
    rw [mul_zero, sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with U hU
    have : 0 < Y ^ 2 * U + b ^ 2 := by positivity
    field_simp
    ring
  have hlog : Tendsto (fun U : ℝ => log (Y ^ 2 * U / (Y ^ 2 * U + b ^ 2))) atTop (𝓝 0) := by
    have h := (continuousAt_log one_ne_zero).tendsto.comp hq
    rw [log_one] at h
    exact h
  have t1 : Tendsto (fun U : ℝ => -α₂ / U) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul (-α₂)
  have t2 : Tendsto (fun U : ℝ => α₃ / (2 * U ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop two_pos)
  have t3 : Tendsto (fun U : ℝ => α₄ / (3 * U ^ 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop three_ne_zero).const_mul_atTop three_pos)
  have t4 : Tendsto (fun U : ℝ => β₂ / (Y ^ 2 * (Y ^ 2 * U + b ^ 2))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hE.const_mul_atTop (by positivity))
  have := (((t1.sub t2).sub t3).sub t4).add (hlog.const_mul α₁)
  simp only [sub_zero, mul_zero, add_zero] at this
  exact this

end QED.TwoLoop.UnitXClose

end
