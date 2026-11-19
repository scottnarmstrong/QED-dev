/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKOneLoop

/-!
# Set (c), Stage K: the simple-pole Stieltjes atoms of the two placements

Helper level (no frozen statement). In both placements of a unit with one photon of mass² `t`, a
term with a simple pole in the massive line's mass function is already a Stieltjes transform in
BLP's variable, with the line's own Feynman parameter as `x`:

* **inner** (`M_t(Y) = (1-Y)(Q(Y) + t)`): `∫₀¹ f(Y)/M_t(Y) dY = ∫₀¹ (f(x)/x²) Q/(Q+t) dx`
  (`integral_div_massIn`), since `(1-x) Q(x) = x²`;
* **outer** (`h_t(x) = ((1-x)/x)(Q(x) + t)`): `∫₀¹ f(x)/h_t(x) dx = ∫₀¹ (f(x)/x) · Q/(Q+t) dx`
  (`integral_div_massOut`).

These are the atoms of the fibre route (section 1 (iii) of the plan); the double poles and the
logarithms are reduced to them by integration by parts in the node variable.
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- Pointwise inner atom: `1/M_t(Y) = (1/Y²) · Q(Y)/(Q(Y) + t)` for `0 < Y < 1`, `t ≥ 0`. -/
theorem inv_ladderInnerMass_sqrt_eq {t Y : ℝ} (ht : 0 ≤ t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    1 / ladderInnerMass 1 (√t) Y = 1 / Y ^ 2 * (setCKQ Y / (setCKQ Y + t)) := by
  have h1 : (1 - Y) ≠ 0 := by linarith [hY.2]
  have hQ : 0 < setCKQ Y := div_pos (pow_pos hY.1 2) (by linarith [hY.2])
  rw [ladderInnerMass_sqrt_eq ht hY.2]
  have : setCKQ Y + t ≠ 0 := by linarith
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hM : Y ^ 2 + (1 - Y) * t ≠ 0 := by
    have : 0 ≤ (1 - Y) * t := mul_nonneg (by linarith [hY.2]) ht
    positivity
  unfold setCKQ at *
  field_simp

/-- Pointwise outer atom: `1/h_t(x) = (1/x) · Q(x)/(Q(x) + t)` for `0 < x < 1`, `t ≥ 0`. -/
theorem inv_ladderInnerMass_sqrt_div_eq {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 / (ladderInnerMass 1 (√t) x / x) = 1 / x * (setCKQ x / (setCKQ x + t)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : (1 - x) ≠ 0 := by linarith [hx.2]
  have hQ : 0 < setCKQ x := div_pos (pow_pos hx.1 2) (by linarith [hx.2])
  rw [ladderInnerMass_sqrt_div_eq ht hx]
  have : setCKQ x + t ≠ 0 := by linarith
  unfold setCKQ at *
  field_simp

/-- **The inner simple-pole atom**: `∫₀¹ f(Y)/M_t(Y) dY = ∫₀¹ (f(x)/x²) Q/(Q+t) dx`. -/
theorem integral_div_massIn (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ Y in (0 : ℝ)..1, f Y / ladderInnerMass 1 (√t) Y =
      setCKStieltjes (fun x => f x / x ^ 2) t := by
  unfold setCKStieltjes
  refine intervalIntegral.integral_congr_ae ((Measure.ae_ne volume 1).mono fun Y h1 hY => ?_)
  rw [uIoc_of_le zero_le_one] at hY
  have h := inv_ladderInnerMass_sqrt_eq ht ⟨hY.1, lt_of_le_of_ne hY.2 h1⟩
  rw [div_eq_mul_one_div, h]
  ring

/-- **The outer simple-pole atom**: `∫₀¹ f(x)/h_t(x) dx = ∫₀¹ (f(x)/x) Q/(Q+t) dx`. -/
theorem integral_div_massOut (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in (0 : ℝ)..1, f x / (ladderInnerMass 1 (√t) x / x) =
      setCKStieltjes (fun x => f x / x) t := by
  unfold setCKStieltjes
  refine intervalIntegral.integral_congr_ae ((Measure.ae_ne volume 1).mono fun x h1 hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  have h := inv_ladderInnerMass_sqrt_div_eq ht ⟨hx.1, lt_of_le_of_ne hx.2 h1⟩
  rw [div_eq_mul_one_div, h]
  ring

/-- **The double-pole atom** (one integration by parts in the node variable): for `g` with a
derivative `g'` on `[0, 1]`,
`∫₀¹ g(x) x(2-x)/M_t(x)² dx = g(0)/t + ∫₀¹ (g'(x)(1-x)/x²) Q/(Q+t) dx`, `M_t(x) = x² + (1-x) t`.
The weight `x(2-x)/M_t²` is `d/dx [-(1-x)/M_t] = d/dx [-1/(Q+t)]`; the boundary term `g(0)/t` is a
point mass at `Q = 0` and must vanish (or cancel) in a Stieltjes identity. In the inner placement
`1/M_t(Y)² = (1/(Y(2-Y))) · Y(2-Y)/M_t²`; in the outer one `1/h_t(x)² = (x/(2-x)) · x(2-x)/M_t²`. -/
theorem integral_mul_div_massIn_sq {g g' : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hg : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' volume 0 1) :
    ∫ x in (0 : ℝ)..1, g x * (x * (2 - x)) / ladderInnerMass 1 (√t) x ^ 2 =
      g 0 / t + setCKStieltjes (fun x => g' x * (1 - x) / x ^ 2) t := by
  have hD : ∀ x : ℝ, ladderInnerMass 1 (√t) x = x ^ 2 + (1 - x) * t := fun x => by
    unfold ladderInnerMass
    rw [sq_sqrt ht.le]
    ring
  have hDpos : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < x ^ 2 + (1 - x) * t := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h
      norm_num
    · have : 0 < (1 - x) * t := mul_pos (by linarith) ht
      positivity
  set v : ℝ → ℝ := fun x => -(1 - x) / (x ^ 2 + (1 - x) * t) with hv
  have hv' : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt v (x * (2 - x) / (x ^ 2 + (1 - x) * t) ^ 2) x := fun x hx => by
    have hd := hDpos x hx
    have h1 : HasDerivAt (fun y : ℝ => -(1 - y)) (- -1) x :=
      ((hasDerivAt_id' x).const_sub (1 : ℝ)).neg
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 + (1 - x) * t) (2 * x - t) x := by
      have := ((hasDerivAt_pow 2 x).add (((hasDerivAt_id' x).const_sub 1).mul_const t))
      convert this using 1
      norm_num
      ring
    convert h1.div h2 hd.ne' using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun x => x * (2 - x) / (x ^ 2 + (1 - x) * t) ^ 2) (uIcc 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (pow_pos (hDpos x hx) 2).ne'
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hv' hg'
    hcont.intervalIntegrable
  have e1 : ∫ x in (0 : ℝ)..1, g x * (x * (2 - x)) / ladderInnerMass 1 (√t) x ^ 2 =
      ∫ x in (0 : ℝ)..1, g x * (x * (2 - x) / (x ^ 2 + (1 - x) * t) ^ 2) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hD]
    ring
  have e2 : ∫ x in (0 : ℝ)..1, g' x * v x =
      -∫ x in (0 : ℝ)..1, g' x * (1 - x) / ladderInnerMass 1 (√t) x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hv, hD]
    ring
  rw [e1, ibp, e2, integral_div_massIn (fun x => g' x * (1 - x)) ht.le]
  simp only [hv]
  norm_num
  field_simp

end QED.ChainProof.SetCK

end
