/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Set (d), master `I₃`: positivity of the `c`-derivative numerator

With `f(z) = z log z`, `w = u + v + u v` and `1 + w = (1 + u)(1 + v)`, the numerator

  `N(u, v) = f(1 + u + v) + f(w) - f(u) - f(v) - f(1 + w)`

governs the derivative of the `e₃`-integrated master integrand with respect to `c = x (1 - x)`.
It vanishes on the axes, and `∂ᵤ ∂ᵥ N = 1/(1 + u + v) + 1/w - log (1 + 1/w) > 0`, so `N ≥ 0` on
the closed quadrant. In the proof, `∂ᵥ N` vanishes at `u = 0` and increases in `u`, and then
`N` increases in `v` from `N(u, 0) = 0`.

## Main results

* `QED.ThreeLoopD.i3XN_nonneg`: `0 ≤ N(u, v)` for `0 < u`, `0 ≤ v`.
-/

@[expose] public section

open Real Set

namespace QED.ThreeLoopD

/-- `N(u, v) = f(1 + u + v) + f(w) - f(u) - f(v) - f(1 + w)`, `f(z) = z log z`,
`w = u + v + u v`. -/
noncomputable def i3XN (u v : ℝ) : ℝ :=
  (1 + u + v) * log (1 + u + v) + (u + v + u * v) * log (u + v + u * v) - u * log u -
    v * log v - (1 + u + v + u * v) * log (1 + u + v + u * v)

/-- `∂ᵥ N`, extended to `u = 0`. -/
noncomputable def i3XNv (u v : ℝ) : ℝ :=
  log (1 + u + v) + (1 + u) * (log (u + v + u * v) - log (1 + u + v + u * v)) - log v

theorem i3XNv_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) : 0 ≤ i3XNv u v := by
  have hw : ∀ s ∈ Ici (0 : ℝ), 0 < s + v + s * v := fun s (hs : 0 ≤ s) => by positivity
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun s => i3XNv s v)
      (1 / (1 + s + v) + 1 / (s + v + s * v) + (log (s + v + s * v) -
        log (1 + s + v + s * v))) s := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := hs
    have h1 : 0 < 1 + s + v := by positivity
    have h2 := hw s hs
    have h3 : 0 < 1 + s + v + s * v := by positivity
    have e1 : HasDerivAt (fun s => 1 + s + v) 1 s :=
      ((hasDerivAt_id' s).const_add 1).add_const v
    have e2 : HasDerivAt (fun s => s + v + s * v) (1 + v) s :=
      (((hasDerivAt_id' s).add_const v).add ((hasDerivAt_id' s).mul_const v)).congr_deriv
        (by ring)
    have e3 : HasDerivAt (fun s => 1 + s + v + s * v) (1 + v) s :=
      ((((hasDerivAt_id' s).const_add 1).add_const v).add
        ((hasDerivAt_id' s).mul_const v)).congr_deriv (by ring)
    have := ((e1.log h1.ne').add (((hasDerivAt_id' s).const_add 1).mul
      ((e2.log h2.ne').sub (e3.log h3.ne')))).sub_const (log v)
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hmono : MonotoneOn (fun s => i3XNv s v) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt) ?_
    intro s hs
    have hs' : s ∈ Ici (0 : ℝ) := interior_subset hs
    have h2 := hw s hs'
    have hs0 : (0 : ℝ) ≤ s := hs'
    have h1 : 0 < 1 + s + v := by positivity
    have hl : -(1 / (s + v + s * v)) ≤ log (s + v + s * v) - log (1 + s + v + s * v) := by
      rw [← log_div h2.ne' (by positivity)]
      have := one_sub_inv_le_log_of_pos (x := (s + v + s * v) / (1 + s + v + s * v))
        (by positivity)
      refine le_trans (le_of_eq ?_) this
      field_simp
      ring
    have : 0 ≤ 1 / (1 + s + v) := by positivity
    linarith
  have h0 : i3XNv 0 v = 0 := by
    simp only [i3XNv]
    rw [show (1 : ℝ) + 0 + v + 0 * v = 1 + v by ring, show (0 : ℝ) + v + 0 * v = v by ring,
      show (1 : ℝ) + 0 + v = 1 + v by ring]
    ring
  have := hmono (show (0 : ℝ) ∈ Ici 0 from le_refl _) (show u ∈ Ici (0 : ℝ) from hu) hu
  simpa [h0] using this

theorem i3XN_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) : 0 ≤ i3XN u v := by
  have hcont : ContinuousOn (fun t => i3XN u t) (Ici 0) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have h1 : 0 < 1 + u + t := by positivity
    have h3 : 0 < 1 + u + t + u * t := by positivity
    have hm : Continuous fun t : ℝ => t * log t := continuous_mul_log
    have hc1 : ContinuousAt (fun t => (1 + u + t) * log (1 + u + t)) t :=
      ((continuous_const.add continuous_id).continuousAt).mul
        ((continuous_const.add continuous_id).continuousAt.log h1.ne')
    have hc2 : ContinuousAt (fun t => (u + t + u * t) * log (u + t + u * t)) t :=
      (hm.comp ((continuous_const.add continuous_id).add
        (continuous_const.mul continuous_id))).continuousAt
    have hc4 : ContinuousAt (fun t => (1 + u + t + u * t) * log (1 + u + t + u * t)) t :=
      ((((continuous_const.add continuous_id).add
        (continuous_const.mul continuous_id))).continuousAt).mul
        ((((continuous_const.add continuous_id).add
        (continuous_const.mul continuous_id))).continuousAt.log h3.ne')
    exact ((((hc1.add hc2).sub continuousAt_const).sub (hm.continuousAt)).sub
      hc4).continuousWithinAt
  have hd : ∀ t ∈ interior (Ici (0 : ℝ)), HasDerivWithinAt (fun t => i3XN u t) (i3XNv u t)
      (interior (Ici 0)) t := by
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 : 0 < 1 + u + t := by positivity
    have h2 : 0 < u + t + u * t := by positivity
    have h3 : 0 < 1 + u + t + u * t := by positivity
    have e1 : HasDerivAt (fun t => 1 + u + t) 1 t := (hasDerivAt_id' t).const_add (1 + u)
    have e2 : HasDerivAt (fun t => u + t + u * t) (1 + u) t :=
      (((hasDerivAt_id' t).const_add u).add ((hasDerivAt_id' t).const_mul u)).congr_deriv
        (by ring)
    have e3 : HasDerivAt (fun t => 1 + u + t + u * t) (1 + u) t :=
      (((hasDerivAt_id' t).const_add (1 + u)).add ((hasDerivAt_id' t).const_mul u)).congr_deriv
        (by ring)
    have f1 := (hasDerivAt_mul_log h1.ne').comp t e1
    have f2 := (hasDerivAt_mul_log h2.ne').comp t e2
    have f3 := (hasDerivAt_mul_log ht0.ne')
    have f4 := (hasDerivAt_mul_log h3.ne').comp t e3
    have := (((f1.add f2).sub_const (u * log u)).sub f3).sub f4
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [i3XNv]
    ring
  have hmono : MonotoneOn (fun t => i3XN u t) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont hd fun t ht => by
      rw [interior_Ici] at ht
      exact i3XNv_nonneg hu.le ht
  have h0 : i3XN u 0 = 0 := by
    simp only [i3XN]
    rw [show (1 : ℝ) + u + 0 + u * 0 = 1 + u + 0 by ring, show u + 0 + u * 0 = u by ring]
    simp
  have := hmono (show (0 : ℝ) ∈ Ici 0 from le_refl _) (show v ∈ Ici (0 : ℝ) from hv) hv
  simpa [h0] using this

end QED.ThreeLoopD
