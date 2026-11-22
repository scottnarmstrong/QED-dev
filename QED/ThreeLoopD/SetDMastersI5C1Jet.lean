/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5RemTaylor
public import QED.ThreeLoopD.SetDMastersI13R1

/-!
# Set (d), master `I₅`: the first Taylor coefficients of the integrands of `Rem`

With `Kₖ(t)` the Taylor coefficients of the kernel in `ε` (`QED.ThreeLoopD.i5KerC`), `λ = log t`
and `β₁` the first bubble coefficient (`QED.ThreeLoopD.i13Be1r`), the Cauchy product of the
jets of `t ^ (1 - ε)`, `b_ε(t)` and `K_ε(t)` gives

  `D¹ (t ^ (1 - ε) b_ε K_ε)(t) = t ((-λ + β₁) K₀(t) + K₁(t))`
  (`QED.ThreeLoopD.i5Dsl_remInt1_one`).

The subtraction `α₀ dslope N 0` has the jet of `α₀` times the shifted jet of `N`
(`QED.ThreeLoopD.I13Jet.dslope`); with `G'(0) = 0`, `G''(0)/2 = -π²/6`,

  `D¹ (α₀ dslope N 0)(t) = (-5λ²/2 - 2λ + 8 + π²/6) / t`
  (`QED.ThreeLoopD.i5Dsl_asymH_one`).

## Main results

* `QED.ThreeLoopD.i13Jet_i5Ker`, `QED.ThreeLoopD.I13Jet.dslope`.
* `QED.ThreeLoopD.i5Dsl_remInt1_one`, `QED.ThreeLoopD.i5Dsl_asymH_one`,
  `QED.ThreeLoopD.i5Dsl_remInt2_one`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-! ### The jet of the kernel -/

theorem i5Jet_dsl {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) (k : ℕ) : i13Dsl f k 0 = a k := by
  obtain ⟨-, -, -, h⟩ := hf
  exact h k

/-- The Taylor coefficients of the kernel `ε ↦ K_ε(t)` at `ε = 0`. -/
noncomputable def i5KerC (t : ℝ) (k : ℕ) : ℂ := i13Dsl (fun ε => i5Ker ε t) k 0

theorem i5KerC_zero (t : ℝ) : i5KerC t 0 = i5Ker 0 t := rfl

theorem i13Jet_i5Ker {t : ℝ} (ht : 0 < t) : I13Jet (fun ε => i5Ker ε t) (i5KerC t) :=
  I13Jet.of_differentiableOn (R := 1 / 4) (by norm_num) fun ε hε => by
    rw [mem_ball, dist_zero_right] at hε
    exact (differentiableAt_i5Ker hε ht).differentiableWithinAt

/-! ### The integrand on `(0, 1)` -/

/-- The coefficients of `t ^ (1 - ε) b_ε(t) K_ε(t)`. -/
noncomputable def i5R1C (t : ℝ) : ℕ → ℂ :=
  i13Cauchy (i13Cauchy (i13TpC t 1 (-1)) (i13BubC t)) (i5KerC t)

theorem i13Jet_i5RemInt1 {t : ℝ} (ht : 0 < t) : I13Jet (i5RemInt1 t) (i5R1C t) :=
  (((i13Jet_tpow ht (fun ε => 1 - ε) 1 (-1) fun ε => by ring).mul'
    (i13Jet_bub ht.le)).mul' (i13Jet_i5Ker ht)).congr (funext fun ε => by
      unfold i5RemInt1; ring)

/-- **The first coefficient on `(0, 1)`**: `t ((-λ + β₁) K₀ + K₁)`. -/
theorem i5Dsl_remInt1_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (i5RemInt1 t) 1 0 =
      t * ((-(Real.log t : ℂ) + i13Be1r t) * i5Ker 0 t + i5KerC t 1) := by
  rw [i5Jet_dsl (i13Jet_i5RemInt1 ht) 1]
  simp only [i5R1C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_one ht, cpow_one]
  norm_num [i13BubC_zero, i5KerC_zero]
  ring

/-! ### The subtraction -/

theorem i13Dsl_dslope (f : ℂ → ℂ) : ∀ k, i13Dsl (dslope f 0) k = i13Dsl f (k + 1)
  | 0 => rfl
  | k + 1 => by rw [i13Dsl_succ, i13Dsl_dslope f k, ← i13Dsl_succ]

/-- **The jet of a slope**: the coefficients shift by one. -/
theorem I13Jet.dslope {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) :
    I13Jet (dslope f 0) fun k => a (k + 1) := by
  obtain ⟨R, hR, hd, hk⟩ := hf
  exact ⟨R, hR, (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).2 hd,
    fun k => by rw [i13Dsl_dslope, hk]⟩

/-- The coefficients of `N(t, ε) = t ^ (-1 - 2ε) / (1 - 2ε) - G t ^ (-1 - 3ε)`. -/
noncomputable def i5NC (t : ℝ) (k : ℕ) : ℂ :=
  i13Cauchy (i13TpC t (-1) (-2)) (fun k => 2 ^ k) k - i13Cauchy i13GC (i13TpC t (-1) (-3)) k

theorem i13Jet_i5AsymN {t : ℝ} (ht : 0 < t) : I13Jet (i5AsymN t) (i5NC t) :=
  (((i13Jet_tpow ht (fun ε => -1 - 2 * ε) (-1) (-2) fun ε => by ring).mul'
    (i13Jet_geom 2)).sub (i13Jet_G.mul'
      (i13Jet_tpow ht (fun ε => -1 - 3 * ε) (-1) (-3) fun ε => by ring))).congr
    (funext fun ε => by unfold i5AsymN; ring)

theorem i13Jet_i5AsymH {t : ℝ} (ht : 0 < t) :
    I13Jet (fun ε => i5AsymH ε t) (i13Cauchy i13A0C fun k => i5NC t (k + 1)) :=
  (i13Jet_Al0.mul' (i13Jet_i5AsymN ht).dslope).congr (funext fun _ => rfl)

/-- **The first coefficient of the subtraction**: `(-5λ²/2 - 2λ + 8 + π²/6) / t`. -/
theorem i5Dsl_asymH_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (fun ε => i5AsymH ε t) 1 0 =
      (-5 / 2 * (Real.log t : ℂ) ^ 2 - 2 * (Real.log t : ℂ) + 8 + (Real.pi : ℂ) ^ 2 / 6) / t := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have g2 : i13GC 2 = -1 / 6 * (Real.pi : ℂ) ^ 2 := i13GC_eq 2 (by norm_num)
  rw [i5Jet_dsl (i13Jet_i5AsymH ht) 1]
  simp only [i5NC, i13A0C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    cpow_neg_one]
  norm_num [Nat.factorial, i13GC_zero, i13GC_one, g2]
  field_simp
  ring

/-- **The first coefficient on `(1, ∞)`**. -/
theorem i5Dsl_remInt2_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (i5RemInt2 t) 1 0 =
      t * ((-(Real.log t : ℂ) + i13Be1r t) * i5Ker 0 t + i5KerC t 1) -
        (-5 / 2 * (Real.log t : ℂ) ^ 2 - 2 * (Real.log t : ℂ) + 8 + (Real.pi : ℂ) ^ 2 / 6) / t := by
  have J : I13Jet (i5RemInt2 t) fun k =>
      i5R1C t k - i13Cauchy i13A0C (fun k => i5NC t (k + 1)) k :=
    ((i13Jet_i5RemInt1 ht).sub (i13Jet_i5AsymH ht)).congr (funext fun _ => rfl)
  rw [i5Jet_dsl J 1, ← i5Jet_dsl (i13Jet_i5RemInt1 ht) 1, ← i5Jet_dsl (i13Jet_i5AsymH ht) 1,
    i5Dsl_remInt1_one ht, i5Dsl_asymH_one ht]

end QED.ThreeLoopD
