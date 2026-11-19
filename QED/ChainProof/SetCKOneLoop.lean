/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLLinkCt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the Euclidean map `Q(x) = x²/(1-x)` and the one-loop Stieltjes form

Helper level (no frozen statement). Stage K of the set (c) kernel derivation proves the
**Stieltjes identity** `A_(c)(t) = ∫₀¹ λ⁽⁴⁾(x) Q(x)/(Q(x) + t) dx` for the two-loop vertex with one
photon of mass² `t`, where `Q(x) = x²/(1-x)` is Balzani–Laporta–Passera's map between their
space-like variable `x` and the photon virtuality. This file fixes the two objects every later
file uses and proves the one-loop instance of the identity.

* `setCKQ x = x²/(1-x)` and the **Stieltjes transform** `setCKStieltjes ρ t = ∫₀¹ ρ(x) Q/(Q+t)`.
* **The one-loop identity** (`oneLoopF2_sqrt_eq_setCKStieltjes`):
  `F₂⁽²⁾(√t) = ∫₀¹ (1-x) Q(x)/(Q(x)+t) dx` for `t > 0`, i.e. the one-loop kernel is
  `κ⁽²⁾(x) = 1 - x` and the electron Feynman parameter is BLP's `x`.
* **The two fibre factorizations** of the massive line (section 1 (iii) of the plan): the inner
  mass `M_t(Y) = Y² + (1-Y) t = (1-Y)(Q(Y) + t)` (`ladderInnerMass_sqrt_eq`) and the outer
  `h_t(x) = (x² + (1-x) t)/x = ((1-x)/x)(Q(x) + t)` (`ladderInnerMass_sqrt_div_eq`). In both
  placements the photon mass² enters linearly with the node `Q` of the line's own parameter.
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- BLP's map `Q(x) = x²/(1-x)` from the space-like variable `x ∈ (0,1)` to the Euclidean
virtuality `Q ∈ (0, ∞)` (`m = 1`). -/
noncomputable def setCKQ (x : ℝ) : ℝ := x ^ 2 / (1 - x)

/-- **The Stieltjes transform** `∫₀¹ ρ(x) Q(x)/(Q(x) + t) dx` of a space-like kernel `ρ`. -/
noncomputable def setCKStieltjes (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ρ x * (setCKQ x / (setCKQ x + t))

theorem setCKQ_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ setCKQ x :=
  div_nonneg (sq_nonneg x) (by linarith [hx.2])

/-- The kernel `Q/(Q+t)` in the original variables: `Q(x)/(Q(x)+t) = x²/(x² + (1-x) t)`
for `x < 1` (both sides vanish when `x² + (1-x) t = 0`). -/
theorem setCKQ_div_eq {x t : ℝ} (hx : x < 1) :
    setCKQ x / (setCKQ x + t) = x ^ 2 / (x ^ 2 + (1 - x) * t) := by
  have h1 : (1 - x) ≠ 0 := by linarith
  unfold setCKQ
  rw [div_add' _ _ _ h1, div_div_div_cancel_right₀ h1]
  ring_nf

/-- **The inner fibre factorization**: `M_t(Y) = Y² + (1-Y) t = (1-Y)(Q(Y) + t)` for `Y < 1`. -/
theorem ladderInnerMass_sqrt_eq {t Y : ℝ} (ht : 0 ≤ t) (hY : Y < 1) :
    ladderInnerMass 1 (√t) Y = (1 - Y) * (setCKQ Y + t) := by
  have h1 : (1 - Y) ≠ 0 := by linarith
  unfold ladderInnerMass setCKQ
  rw [sq_sqrt ht]
  field_simp

/-- **The outer fibre factorization**: `h_t(x) = (x² + (1-x) t)/x = ((1-x)/x)(Q(x) + t)` for
`0 < x < 1`. -/
theorem ladderInnerMass_sqrt_div_eq {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ladderInnerMass 1 (√t) x / x = (1 - x) / x * (setCKQ x + t) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : (1 - x) ≠ 0 := by linarith [hx.2]
  unfold ladderInnerMass setCKQ
  rw [sq_sqrt ht]
  field_simp

/-- Pointwise form of the one-loop identity on `[0, 1]`. -/
theorem oneLoopF2_integrand_eq {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Icc (0 : ℝ) 1) :
    Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 (√t) Y =
      (1 - Y) * (setCKQ Y / (setCKQ Y + t)) := by
  rcases eq_or_lt_of_le hY.2 with h | h
  · subst h
    simp
  · rw [setCKQ_div_eq h]
    unfold ladderInnerMass
    rw [sq_sqrt ht.le]
    field_simp

/-- **The one-loop Stieltjes identity**: `F₂⁽²⁾(√t) = ∫₀¹ (1-x) Q(x)/(Q(x)+t) dx` for `t > 0`
(`κ⁽²⁾ = 1 - x`). -/
theorem oneLoopF2_sqrt_eq_setCKStieltjes {t : ℝ} (ht : 0 < t) :
    oneLoopF2 1 (√t) = setCKStieltjes (fun x => 1 - x) t := by
  unfold oneLoopF2 setCKStieltjes
  refine intervalIntegral.integral_congr fun Y hY => ?_
  rw [uIcc_of_le zero_le_one] at hY
  exact oneLoopF2_integrand_eq ht hY

end QED.ChainProof.SetCK

end
