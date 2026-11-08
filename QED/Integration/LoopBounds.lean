/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary bounds for regulated loop integrands

Uniform estimates used to justify Fubini swaps and dominated convergence for the one-loop
vertex under the energy-first prescription M1 (`docs/REGULARIZATION.md`, decision D-5).

## Main statements

* `QED.Integration.exists_mul_one_add_sq_le_norm`: a shifted Minkowski denominator
  `-(t + a)² + W - iε` with `ε > 0` is bounded below by `c (1 + t²)`, uniformly for bounded
  shifts `a` and bounded-above mass terms `W`.
* `QED.Integration.exists_mul_one_add_norm_sq_le`: the shifted spatial square
  `Σ (v k + b k)² + D` is bounded below by `c (1 + ‖v‖)²`, uniformly for bounded shifts `b`
  and mass terms `D ≥ D₀ > 0`.
* `QED.Integration.norm_finCons_le`: `‖Fin.cons t v‖ ≤ |t| + ‖v‖` for the sup norm.
-/

@[expose] public section

open Complex

namespace QED.Integration

/-- A shifted Minkowski denominator with a fixed `-iε`, `ε > 0`, grows like `1 + t²`,
uniformly for shifts `|a| ≤ A` and mass terms `W' ≤ W`. -/
theorem exists_mul_one_add_sq_le_norm {ε : ℝ} (hε : 0 < ε) (A W : ℝ) :
    ∃ c > 0, ∀ t a W' : ℝ, |a| ≤ A → W' ≤ W →
      c * (1 + t ^ 2) ≤ ‖-((t : ℂ) + a) ^ 2 + W' - ε * I‖ := by
  set R : ℝ := A ^ 2 + |W| with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨ε / (1 + 4 * (R + ε)), by positivity, fun t a W' ha hW' => ?_⟩
  have hZ : -((t : ℂ) + a) ^ 2 + W' - ε * I = ((-(t + a) ^ 2 + W' : ℝ) : ℂ) - (ε : ℂ) * I := by
    push_cast; ring
  rw [hZ]
  set Z : ℂ := ((-(t + a) ^ 2 + W' : ℝ) : ℂ) - (ε : ℂ) * I
  have him : Z.im = -ε := by
    simp only [Z, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hre : Z.re = -(t + a) ^ 2 + W' := by
    simp only [Z, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have h1 : ε ≤ ‖Z‖ := by
    have := Complex.abs_im_le_norm Z
    rw [him, abs_neg, abs_of_pos hε] at this
    exact this
  have h2 : (t + a) ^ 2 - W' ≤ ‖Z‖ := by
    have := Complex.abs_re_le_norm Z
    rw [hre] at this
    linarith [neg_abs_le (-(t + a) ^ 2 + W')]
  have ha2 : a ^ 2 ≤ A ^ 2 := by
    have := sq_abs a
    nlinarith [abs_nonneg a]
  have hW2 : W' ≤ |W| := hW'.trans (le_abs_self W)
  have hsq : t ^ 2 / 2 - a ^ 2 ≤ (t + a) ^ 2 := by nlinarith [sq_nonneg (t + 2 * a)]
  have hc : ε / (1 + 4 * (R + ε)) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hc' : ε / (1 + 4 * (R + ε)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases le_or_gt (t ^ 2) (4 * (R + ε)) with ht | ht
  · calc ε / (1 + 4 * (R + ε)) * (1 + t ^ 2) ≤ ε / (1 + 4 * (R + ε)) * (1 + 4 * (R + ε)) := by
          gcongr
      _ = ε := by field_simp
      _ ≤ ‖Z‖ := h1
  · have hlow : t ^ 2 / 4 + ε ≤ ‖Z‖ := by nlinarith
    calc ε / (1 + 4 * (R + ε)) * (1 + t ^ 2)
        = ε / (1 + 4 * (R + ε)) + ε / (1 + 4 * (R + ε)) * t ^ 2 := by ring
      _ ≤ ε + 1 / 4 * t ^ 2 := by gcongr
      _ ≤ ‖Z‖ := by linarith

/-- The shifted spatial square is coercive: `c (1 + ‖v‖)² ≤ Σ (v k + b k)² + D`, uniformly
for shifts `‖b‖ ≤ B` and mass terms `D ≥ D₀ > 0`. -/
theorem exists_mul_one_add_norm_sq_le {n : ℕ} (B : ℝ) {D₀ : ℝ} (hD₀ : 0 < D₀) :
    ∃ c > 0, ∀ (v b : Fin n → ℝ) (D : ℝ), ‖b‖ ≤ B → D₀ ≤ D →
      c * (1 + ‖v‖) ^ 2 ≤ ∑ k, (v k + b k) ^ 2 + D := by
  set B' : ℝ := |B|
  have hB' : 0 ≤ B' := abs_nonneg B
  refine ⟨min (1 / 2) (D₀ / (2 * (1 + B') ^ 2)), by positivity, fun v b D hb hD => ?_⟩
  set S : ℝ := ∑ k, (v k + b k) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hv : ‖v‖ ≤ Real.sqrt S + B' := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
    have hk : (v k + b k) ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun k => (v k + b k) ^ 2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ k)
    have h1 : |v k + b k| ≤ Real.sqrt S := Real.abs_le_sqrt hk
    have h2 : |b k| ≤ B' := ((norm_le_pi_norm b k).trans hb).trans (le_abs_self B)
    rw [Real.norm_eq_abs]
    calc |v k| = |(v k + b k) - b k| := by ring_nf
      _ ≤ |v k + b k| + |b k| := abs_sub _ _
      _ ≤ Real.sqrt S + B' := add_le_add h1 h2
  have hsqrt : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have hsq : (1 + ‖v‖) ^ 2 ≤ 2 * (1 + B') ^ 2 + 2 * S := by
    have h0 : 0 ≤ 1 + ‖v‖ := by positivity
    have := pow_le_pow_left₀ h0 (by linarith : 1 + ‖v‖ ≤ 1 + B' + Real.sqrt S) 2
    nlinarith [sq_nonneg (1 + B' - Real.sqrt S)]
  have hc1 : min (1 / 2) (D₀ / (2 * (1 + B') ^ 2)) * (2 * S) ≤ S := by
    have := min_le_left (1 / 2 : ℝ) (D₀ / (2 * (1 + B') ^ 2))
    nlinarith
  have hc2 : min (1 / 2) (D₀ / (2 * (1 + B') ^ 2)) * (2 * (1 + B') ^ 2) ≤ D₀ := by
    have := min_le_right (1 / 2 : ℝ) (D₀ / (2 * (1 + B') ^ 2))
    calc min (1 / 2) (D₀ / (2 * (1 + B') ^ 2)) * (2 * (1 + B') ^ 2)
        ≤ D₀ / (2 * (1 + B') ^ 2) * (2 * (1 + B') ^ 2) := by gcongr
      _ = D₀ := by field_simp
  calc min (1 / 2) (D₀ / (2 * (1 + B') ^ 2)) * (1 + ‖v‖) ^ 2
      ≤ min (1 / 2) (D₀ / (2 * (1 + B') ^ 2)) * (2 * (1 + B') ^ 2 + 2 * S) := by gcongr
    _ ≤ S + D := by nlinarith

/-- The sup norm of `Fin.cons t v` is at most `|t| + ‖v‖`. -/
theorem norm_finCons_le {n : ℕ} (t : ℝ) (v : Fin n → ℝ) :
    ‖(Fin.cons t v : Fin (n + 1) → ℝ)‖ ≤ |t| + ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [Fin.cons_zero, Real.norm_eq_abs]
    linarith [norm_nonneg v]
  · simp only [Fin.cons_succ]
    linarith [norm_le_pi_norm v k, abs_nonneg t]

end QED.Integration

end
