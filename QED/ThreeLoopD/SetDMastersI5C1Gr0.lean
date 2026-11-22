/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1At0
public import QED.ThreeLoopD.SetDMastersI5C1Der
public import QED.ThreeLoopD.SetDMastersI5C1Kx

/-!
# Set (d), master `I₅`: the limit of the primitive at `x = 0⁺`

As a polynomial in `log x`, the primitive is `P = R₀ + log x · A₁ + log² x · A₂`
(`QED.ThreeLoopD.i5C1E_PB_eq0`), where `R₀` (in parts `QED.ThreeLoopD.i5C1E_R0a`, ...), `A₁`,
`A₂` are polynomials in the other atoms. `R₀` tends to `QED.ThreeLoopD.i5C1E_V0` by the atom
limits of `QED.ThreeLoopD.SetDMastersI5C1At0`; `A₁`, `A₂` are differentiable at `0` and vanish
there, so `log x · A₁ → 0` and `log² x · A₂ → 0`.

## Main results

* `QED.ThreeLoopD.i5C1E_PB_eq0`, `QED.ThreeLoopD.tendsto_i5C1PB_zero`.
-/

@[expose] public section

open Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- Part `a` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0a (ξ x : ℝ) : ℝ :=
  (-1 / 3) * (π * π * log (ξ * x + (1 - ξ))) + 1 * (π * π * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (1 / 2) * (π * π * log (ξ * x + (1 - ξ) ^ 2)) + (-1 / 3) * (log (ξ * x + (1 - ξ)) *
      log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + (19 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 - ξ)) + (7 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 - ξ - x)) + (5 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 + ξ)) + (15 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 - x)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-3 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2)) + (-3) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log ξ) + (-1 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + (-11) * (log (ξ * x + (1 - ξ)) *
      log (1 - ξ) * log (1 - ξ - x)) + (-14) * (log (ξ * x + (1 - ξ)) * log (1 - ξ) *
      log (1 + ξ)) + 1 * (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log (1 - x)) + (-12) *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 5 *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log ξ) + 4 * (log (ξ * x + (1 - ξ)) * log (1 - ξ)) +
      (-2) * (log (ξ * x + (1 - ξ)) * log (1 - ξ - x) * log (1 + ξ)) + (-1) *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ - x) * log (1 - x))

/-- The limit of `i5C1E_R0a`. -/
noncomputable def i5C1E_V0a (ξ : ℝ) : ℝ :=
  (-1 / 3) * (π * π * (log (1 - ξ))) + 1 * (π * π * (2 * log (1 - ξ))) + (1 / 2) *
      (π * π * (2 * log (1 - ξ))) + (-1 / 3) * ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) +
      (19 / 2) * ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (7 / 2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (5 / 2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 + ξ))) + (15 / 2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (0)) + 1 * ((log (1 - ξ)) * (log (1 - ξ)) *
      (2 * log (1 - ξ))) + (-3 / 2) * ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + (-3) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log ξ)) + (-1 / 2) * ((log (1 - ξ)) * (log (1 - ξ))) +
      (-11) * ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (-14) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 + ξ))) + 1 * ((log (1 - ξ)) * (log (1 - ξ)) * (0)) +
      (-12) * ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + 5 *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log ξ)) + 4 * ((log (1 - ξ)) * (log (1 - ξ))) + (-2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 + ξ))) + (-1) * ((log (1 - ξ)) * (log (1 - ξ)) * (0))

theorem i5C1E_tR0a {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0a ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0a ξ)) := by
  have cπ : Tendsto (fun _ : ℝ => π) (𝓝[>] 0) (𝓝 π) := tendsto_const_nhds
  have t1 := i5C1E_t0_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[>] 0) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have t3 := i5C1E_t0_3 hξ
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[>] 0) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_t0_5 hξ
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have h := ((((((((((((((((((((((cπ.mul cπ).mul t1).const_mul (-1 / 3)).add
      (((cπ.mul cπ).mul t6).const_mul 1)).add (((cπ.mul cπ).mul t7).const_mul (1 / 2))).add
      (((t1.mul t1).mul t1).const_mul (-1 / 3))).add (((t1.mul t1).mul c2).const_mul (19 / 2))).add
      (((t1.mul t1).mul t3).const_mul (7 / 2))).add (((t1.mul t1).mul c4).const_mul (5 / 2))).add
      (((t1.mul t1).mul t5).const_mul (15 / 2))).add (((t1.mul t1).mul t6).const_mul 1)).add
      (((t1.mul t1).mul t7).const_mul (-3 / 2))).add (((t1.mul t1).mul c8).const_mul (-3))).add
      ((t1.mul t1).const_mul (-1 / 2))).add (((t1.mul c2).mul t3).const_mul (-11))).add
      (((t1.mul c2).mul c4).const_mul (-14))).add (((t1.mul c2).mul t5).const_mul 1)).add
      (((t1.mul c2).mul t6).const_mul (-12))).add (((t1.mul c2).mul c8).const_mul 5)).add
      ((t1.mul c2).const_mul 4)).add (((t1.mul t3).mul c4).const_mul (-2))).add
      (((t1.mul t3).mul t5).const_mul (-1)))
  exact h

/-- Part `b` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0b (ξ x : ℝ) : ℝ :=
  (-6) * (log (ξ * x + (1 - ξ)) * log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2)) + 3 *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ - x) * log ξ) + (-1) * (log (ξ * x + (1 - ξ)) *
      log (1 + ξ) * log (1 + ξ)) + (-5) * (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log (1 - x)) +
      (-1) * (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log (ξ * x + (1 - ξ) ^ 2)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log ξ) + (-3 / 2) * (log (ξ * x + (1 - ξ)) *
      log (1 - x) * log (1 - x)) + (-6) * (log (ξ * x + (1 - ξ)) * log (1 - x) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 * (log (ξ * x + (1 - ξ)) * log (1 - x)) + 4 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (-2) * (log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ) + 1 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + 3 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + (-1 / 2) *
      (log (ξ * x + (1 - ξ)) * log ξ * log ξ) + (-1) * (log (ξ * x + (1 - ξ)) * log ξ) + 2 *
      (log (ξ * x + (1 - ξ)) * Li₂ (x)) + (-3) * (log (ξ * x + (1 - ξ)) * Li₂ (x / (1 - ξ))) +
      (-1) * (log (ξ * x + (1 - ξ)) * Li₂ (ξ / (1 - x))) + 4 * (log (ξ * x + (1 - ξ)) *
      Li₂ (-(ξ * x / (1 - ξ))))

/-- The limit of `i5C1E_R0b`. -/
noncomputable def i5C1E_V0b (ξ : ℝ) : ℝ :=
  (-6) * ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + 1 *
      ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + 3 * ((log (1 - ξ)) * (log (1 - ξ)) *
      (log ξ)) + (-1) * ((log (1 - ξ)) * (log (1 + ξ)) * (log (1 + ξ))) + (-5) *
      ((log (1 - ξ)) * (log (1 + ξ)) * (0)) + (-1) * ((log (1 - ξ)) * (log (1 + ξ)) *
      (2 * log (1 - ξ))) + 1 * ((log (1 - ξ)) * (log (1 + ξ)) * (log ξ)) + (-3 / 2) *
      ((log (1 - ξ)) * (0) * (0)) + (-6) * ((log (1 - ξ)) * (0) * (2 * log (1 - ξ))) + 1 *
      ((log (1 - ξ)) * (0)) + 4 * ((log (1 - ξ)) * (2 * log (1 - ξ)) * (2 * log (1 - ξ))) + (-2) *
      ((log (1 - ξ)) * (2 * log (1 - ξ)) * (log ξ)) + 1 * ((log (1 - ξ)) * (2 * log (1 - ξ)) *
      (2 * log (1 - ξ))) + 3 * ((log (1 - ξ)) * (2 * log (1 - ξ)) * (log ξ)) + (-1 / 2) *
      ((log (1 - ξ)) * (log ξ) * (log ξ)) + (-1) * ((log (1 - ξ)) * (log ξ)) + 2 *
      ((log (1 - ξ)) * (0)) + (-3) * ((log (1 - ξ)) * (0)) + (-1) * ((log (1 - ξ)) * (Li₂ ξ)) + 4 *
      ((log (1 - ξ)) * (0))

theorem i5C1E_tR0b {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0b ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0b ξ)) := by
  have t1 := i5C1E_t0_1 hξ
  have t3 := i5C1E_t0_3 hξ
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[>] 0) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_t0_5 hξ
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_t0_9 hξ
  have t10 := i5C1E_t0_10 hξ
  have t11 := i5C1E_t0_11 hξ
  have t13 := i5C1E_t0_13 hξ
  have h := ((((((((((((((((((((((t1.mul t3).mul t6).const_mul (-6)).add
      (((t1.mul t3).mul t7).const_mul 1)).add (((t1.mul t3).mul c8).const_mul 3)).add
      (((t1.mul c4).mul c4).const_mul (-1))).add (((t1.mul c4).mul t5).const_mul (-5))).add
      (((t1.mul c4).mul t7).const_mul (-1))).add (((t1.mul c4).mul c8).const_mul 1)).add
      (((t1.mul t5).mul t5).const_mul (-3 / 2))).add (((t1.mul t5).mul t6).const_mul (-6))).add
      ((t1.mul t5).const_mul 1)).add (((t1.mul t6).mul t6).const_mul 4)).add
      (((t1.mul t6).mul c8).const_mul (-2))).add (((t1.mul t7).mul t7).const_mul 1)).add
      (((t1.mul t7).mul c8).const_mul 3)).add (((t1.mul c8).mul c8).const_mul (-1 / 2))).add
      ((t1.mul c8).const_mul (-1))).add ((t1.mul t9).const_mul 2)).add
      ((t1.mul t10).const_mul (-3))).add ((t1.mul t11).const_mul (-1))).add
      ((t1.mul t13).const_mul 4))
  exact h

/-- Part `c` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0c (ξ x : ℝ) : ℝ :=
  (-2) * (log (ξ * x + (1 - ξ)) * Li₂ (x / (ξ * x + (1 - ξ)))) + 1 *
      (log (ξ * x + (1 - ξ)) * Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) + 2 *
      (log (ξ * x + (1 - ξ)) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + (39 / 2) *
      (log (1 - ξ) * log (1 - ξ) * log (1 - ξ - x)) + (-3 / 2) * (log (1 - ξ) * log (1 - ξ) *
      log (1 - x)) + 7 * (log (1 - ξ) * log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-5 / 2) *
      (log (1 - ξ) * log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2)) + 13 *
      (log (1 - ξ) * log (1 - ξ - x) * log (1 + ξ)) + 2 * (log (1 - ξ) * log (1 - ξ - x) *
      log (1 - x)) + (-6) * (log (1 - ξ) * log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (-1) * (log (1 - ξ) * log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2)) + (-2) *
      (log (1 - ξ) * log (1 - ξ - x) * log ξ) + 3 * (log (1 - ξ) * log (1 + ξ) * log (1 - x)) + 1 *
      (log (1 - ξ) * log (1 - x) * log (1 - x)) + (-2) * (log (1 - ξ) * log (1 - x) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-1) * (log (1 - ξ) * log (1 - x) * log ξ) + 2 *
      (log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 *
      (log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + (-1) *
      (log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + 4 * (log (1 - ξ) * Li₂ (x))

/-- The limit of `i5C1E_R0c`. -/
noncomputable def i5C1E_V0c (ξ : ℝ) : ℝ :=
  (-2) * ((log (1 - ξ)) * (0)) + 1 * ((log (1 - ξ)) * (Li₂ ξ)) + 2 * ((log (1 - ξ)) * (Li₂ ξ)) +
      (39 / 2) * ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 - ξ))) + (-3 / 2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (0)) + 7 * ((log (1 - ξ)) * (log (1 - ξ)) *
      (2 * log (1 - ξ))) + (-5 / 2) * ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + 13 *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log (1 + ξ))) + 2 * ((log (1 - ξ)) * (log (1 - ξ)) * (0)) +
      (-6) * ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + (-1) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (2 * log (1 - ξ))) + (-2) *
      ((log (1 - ξ)) * (log (1 - ξ)) * (log ξ)) + 3 * ((log (1 - ξ)) * (log (1 + ξ)) * (0)) + 1 *
      ((log (1 - ξ)) * (0) * (0)) + (-2) * ((log (1 - ξ)) * (0) * (2 * log (1 - ξ))) + (-1) *
      ((log (1 - ξ)) * (0) * (log ξ)) + 2 * ((log (1 - ξ)) * (2 * log (1 - ξ)) *
      (2 * log (1 - ξ))) + 3 * ((log (1 - ξ)) * (2 * log (1 - ξ)) * (2 * log (1 - ξ))) + (-1) *
      ((log (1 - ξ)) * (2 * log (1 - ξ)) * (log ξ)) + 4 * ((log (1 - ξ)) * (0))

theorem i5C1E_tR0c {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0c ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0c ξ)) := by
  have t1 := i5C1E_t0_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[>] 0) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have t3 := i5C1E_t0_3 hξ
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[>] 0) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_t0_5 hξ
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_t0_9 hξ
  have t14 := i5C1E_t0_14 hξ
  have t16 := i5C1E_t0_16 hξ
  have t19 := i5C1E_t0_19 hξ
  have h := (((((((((((((((((((((t1.mul t14).const_mul (-2)).add ((t1.mul t16).const_mul 1)).add
      ((t1.mul t19).const_mul 2)).add (((c2.mul c2).mul t3).const_mul (39 / 2))).add
      (((c2.mul c2).mul t5).const_mul (-3 / 2))).add (((c2.mul c2).mul t6).const_mul 7)).add
      (((c2.mul c2).mul t7).const_mul (-5 / 2))).add (((c2.mul t3).mul c4).const_mul 13)).add
      (((c2.mul t3).mul t5).const_mul 2)).add (((c2.mul t3).mul t6).const_mul (-6))).add
      (((c2.mul t3).mul t7).const_mul (-1))).add (((c2.mul t3).mul c8).const_mul (-2))).add
      (((c2.mul c4).mul t5).const_mul 3)).add (((c2.mul t5).mul t5).const_mul 1)).add
      (((c2.mul t5).mul t6).const_mul (-2))).add (((c2.mul t5).mul c8).const_mul (-1))).add
      (((c2.mul t6).mul t6).const_mul 2)).add (((c2.mul t7).mul t7).const_mul 3)).add
      (((c2.mul t7).mul c8).const_mul (-1))).add ((c2.mul t9).const_mul 4))
  exact h

/-- Part `d` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0d (ξ x : ℝ) : ℝ :=
  (-25) * (log (1 - ξ) * Li₂ (x / (1 - ξ))) + (-3) * (log (1 - ξ) * Li₂ (ξ / (1 - x))) + 3 *
      (log (1 - ξ) * Li₂ (ξ * (1 - x))) + (-9) * (log (1 - ξ) * Li₂ (-(ξ * x / (1 - ξ)))) + (-4) *
      (log (1 - ξ) * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-1) * (log (1 - ξ) *
      Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) + 12 * (log (1 - ξ) * Li₂ ((1 + ξ) *
      x / (ξ * x + (1 - ξ)))) + 4 * (log (1 - ξ) * Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) + (-3) *
      (log (1 - ξ) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 4 *
      (log (1 - ξ) * Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + 1 *
      (log (1 - ξ - x) * log (1 + ξ) * log (1 + ξ)) + 2 * (log (1 - ξ - x) * log (1 + ξ) *
      log (1 - x)) + 1 * (log (1 - ξ - x) * log (1 + ξ) * log (ξ * x + (1 - ξ) ^ 2)) + (-2) *
      (log (1 - ξ - x) * log (1 + ξ) * log ξ) + 3 * (log (1 - ξ - x) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 *
      (log (1 - ξ - x) * Li₂ (x)) + 1 * (log (1 - ξ - x) * Li₂ (ξ * (1 - x))) + 1 *
      (log (1 - ξ - x) * Li₂ (-(ξ * x / (1 - ξ)))) + (-2) * (log (1 - ξ - x) *
      Li₂ (x / (ξ * x + (1 - ξ)))) + 1 * (log (1 - ξ - x) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))))

/-- The limit of `i5C1E_R0d`. -/
noncomputable def i5C1E_V0d (ξ : ℝ) : ℝ :=
  (-25) * ((log (1 - ξ)) * (0)) + (-3) * ((log (1 - ξ)) * (Li₂ ξ)) + 3 *
      ((log (1 - ξ)) * (Li₂ ξ)) + (-9) * ((log (1 - ξ)) * (0)) + (-4) * ((log (1 - ξ)) * (0)) +
      (-1) * ((log (1 - ξ)) * (Li₂ ξ)) + 12 * ((log (1 - ξ)) * (0)) + 4 * ((log (1 - ξ)) * (0)) +
      (-3) * ((log (1 - ξ)) * (Li₂ ξ)) + 4 * ((log (1 - ξ)) * (Li₂ (-ξ))) + 1 *
      ((log (1 - ξ)) * (log (1 + ξ)) * (log (1 + ξ))) + 2 * ((log (1 - ξ)) * (log (1 + ξ)) * (0)) +
      1 * ((log (1 - ξ)) * (log (1 + ξ)) * (2 * log (1 - ξ))) + (-2) *
      ((log (1 - ξ)) * (log (1 + ξ)) * (log ξ)) + 3 * ((log (1 - ξ)) * (2 * log (1 - ξ)) *
      (2 * log (1 - ξ))) + 2 * ((log (1 - ξ)) * (0)) + 1 * ((log (1 - ξ)) * (Li₂ ξ)) + 1 *
      ((log (1 - ξ)) * (0)) + (-2) * ((log (1 - ξ)) * (0)) + 1 * ((log (1 - ξ)) * (Li₂ ξ))

theorem i5C1E_tR0d {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0d ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0d ξ)) := by
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[>] 0) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have t3 := i5C1E_t0_3 hξ
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[>] 0) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_t0_5 hξ
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_t0_9 hξ
  have t10 := i5C1E_t0_10 hξ
  have t11 := i5C1E_t0_11 hξ
  have t12 := i5C1E_t0_12 hξ
  have t13 := i5C1E_t0_13 hξ
  have t14 := i5C1E_t0_14 hξ
  have t15 := i5C1E_t0_15 hξ
  have t16 := i5C1E_t0_16 hξ
  have t17 := i5C1E_t0_17 hξ
  have t18 := i5C1E_t0_18 hξ
  have t19 := i5C1E_t0_19 hξ
  have t21 := i5C1E_t0_21 hξ
  have h := (((((((((((((((((((((c2.mul t10).const_mul (-25)).add
      ((c2.mul t11).const_mul (-3))).add ((c2.mul t12).const_mul 3)).add
      ((c2.mul t13).const_mul (-9))).add ((c2.mul t15).const_mul (-4))).add
      ((c2.mul t16).const_mul (-1))).add ((c2.mul t17).const_mul 12)).add
      ((c2.mul t18).const_mul 4)).add ((c2.mul t19).const_mul (-3))).add
      ((c2.mul t21).const_mul 4)).add (((t3.mul c4).mul c4).const_mul 1)).add
      (((t3.mul c4).mul t5).const_mul 2)).add (((t3.mul c4).mul t7).const_mul 1)).add
      (((t3.mul c4).mul c8).const_mul (-2))).add (((t3.mul t6).mul t6).const_mul 3)).add
      ((t3.mul t9).const_mul 2)).add ((t3.mul t12).const_mul 1)).add
      ((t3.mul t13).const_mul 1)).add ((t3.mul t14).const_mul (-2))).add ((t3.mul t19).const_mul 1))
  exact h

/-- Part `e` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0e (ξ x : ℝ) : ℝ :=
  (3 / 2) * (log (1 + ξ) * log (1 + ξ) * log (1 - x)) + 1 * (log (1 + ξ) * log (1 - x) *
      log (1 - x)) + (-1) * (log (1 + ξ) * log (1 - x) * log ξ) + 2 *
      (log (1 + ξ) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + (-3) * (log (1 + ξ) *
      Li₂ (x / (1 - ξ))) + (-1) * (log (1 + ξ) * Li₂ (ξ / (1 - x))) + (-1) *
      (log (1 + ξ) * Li₂ (ξ * (1 - x))) + 3 * (log (1 + ξ) * Li₂ (-(ξ * x / (1 - ξ)))) + 1 *
      (log (1 + ξ) * Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) + 1 * (log (1 + ξ) *
      Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 1 * (log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-2) * (log (1 - x) * Li₂ (x)) + (-3) *
      (log (1 - x) * Li₂ (x / (1 - ξ))) + (-1) * (log (1 - x) * Li₂ (-(ξ * x / (1 - ξ)))) + 2 *
      (log (1 - x) * Li₂ (x / (ξ * x + (1 - ξ)))) + (-1) * (log (1 - x) *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + 3 * (log (1 - x) * Li₂ ((1 + ξ) *
      x / (ξ * x + (1 - ξ)))) + (-2) * (log (1 - x) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 1 *
      (log (1 - x) * Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + (-5 / 3) *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2))

/-- The limit of `i5C1E_R0e`. -/
noncomputable def i5C1E_V0e (ξ : ℝ) : ℝ :=
  (3 / 2) * ((log (1 + ξ)) * (log (1 + ξ)) * (0)) + 1 * ((log (1 + ξ)) * (0) * (0)) + (-1) *
      ((log (1 + ξ)) * (0) * (log ξ)) + 2 * ((log (1 + ξ)) * (2 * log (1 - ξ)) * (log ξ)) + (-3) *
      ((log (1 + ξ)) * (0)) + (-1) * ((log (1 + ξ)) * (Li₂ ξ)) + (-1) * ((log (1 + ξ)) * (Li₂ ξ)) +
      3 * ((log (1 + ξ)) * (0)) + 1 * ((log (1 + ξ)) * (Li₂ ξ)) + 1 * ((log (1 + ξ)) * (Li₂ ξ)) +
      1 * ((0) * (2 * log (1 - ξ)) * (2 * log (1 - ξ))) + (-2) * ((0) * (0)) + (-3) * ((0) * (0)) +
      (-1) * ((0) * (0)) + 2 * ((0) * (0)) + (-1) * ((0) * (0)) + 3 * ((0) * (0)) + (-2) *
      ((0) * (Li₂ ξ)) + 1 * ((0) * (Li₂ (-ξ))) + (-5 / 3) * ((2 * log (1 - ξ)) *
      (2 * log (1 - ξ)) * (2 * log (1 - ξ)))

theorem i5C1E_tR0e {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0e ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0e ξ)) := by
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[>] 0) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_t0_5 hξ
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_t0_9 hξ
  have t10 := i5C1E_t0_10 hξ
  have t11 := i5C1E_t0_11 hξ
  have t12 := i5C1E_t0_12 hξ
  have t13 := i5C1E_t0_13 hξ
  have t14 := i5C1E_t0_14 hξ
  have t15 := i5C1E_t0_15 hξ
  have t16 := i5C1E_t0_16 hξ
  have t17 := i5C1E_t0_17 hξ
  have t19 := i5C1E_t0_19 hξ
  have t21 := i5C1E_t0_21 hξ
  have h := ((((((((((((((((((((((c4.mul c4).mul t5).const_mul (3 / 2)).add
      (((c4.mul t5).mul t5).const_mul 1)).add (((c4.mul t5).mul c8).const_mul (-1))).add
      (((c4.mul t7).mul c8).const_mul 2)).add ((c4.mul t10).const_mul (-3))).add
      ((c4.mul t11).const_mul (-1))).add ((c4.mul t12).const_mul (-1))).add
      ((c4.mul t13).const_mul 3)).add ((c4.mul t16).const_mul 1)).add
      ((c4.mul t19).const_mul 1)).add (((t5.mul t6).mul t6).const_mul 1)).add
      ((t5.mul t9).const_mul (-2))).add ((t5.mul t10).const_mul (-3))).add
      ((t5.mul t13).const_mul (-1))).add ((t5.mul t14).const_mul 2)).add
      ((t5.mul t15).const_mul (-1))).add ((t5.mul t17).const_mul 3)).add
      ((t5.mul t19).const_mul (-2))).add ((t5.mul t21).const_mul 1)).add
      (((t6.mul t6).mul t6).const_mul (-5 / 3)))
  exact h

/-- Part `f` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0f (ξ x : ℝ) : ℝ :=
  1 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) +
      (-2) * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) *
      log (ξ * x + (1 - ξ) ^ 2)) + (-4) * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x)) + 8 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x / (1 - ξ))) + 2 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      Li₂ (ξ / (1 - x))) + (-4) * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (ξ * (1 - x))) + 8 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (-(ξ * x / (1 - ξ)))) + 2 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x / (ξ * x + (1 - ξ)))) + (-2) *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) + 2 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + (-1) *
      (log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + (-2) *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (x)) + 2 * (log (ξ * x + (1 - ξ) ^ 2) *
      Li₂ (-(ξ * x / (1 - ξ)))) + 2 * (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (x / (ξ * x + (1 - ξ)))) +
      1 * (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-2) *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + 3 *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) + (-1) *
      (log (ξ * x + (1 - ξ) ^ 2) * Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + 3 *
      (log ξ * Li₂ (x / (1 - ξ))) + (-3) * (log ξ * Li₂ (-(ξ * x / (1 - ξ))))

/-- The limit of `i5C1E_R0f`. -/
noncomputable def i5C1E_V0f (ξ : ℝ) : ℝ :=
  1 * ((2 * log (1 - ξ)) * (2 * log (1 - ξ)) * (2 * log (1 - ξ))) + (-2) *
      ((2 * log (1 - ξ)) * (2 * log (1 - ξ)) * (2 * log (1 - ξ))) + (-4) *
      ((2 * log (1 - ξ)) * (0)) + 8 * ((2 * log (1 - ξ)) * (0)) + 2 *
      ((2 * log (1 - ξ)) * (Li₂ ξ)) + (-4) * ((2 * log (1 - ξ)) * (Li₂ ξ)) + 8 *
      ((2 * log (1 - ξ)) * (0)) + 2 * ((2 * log (1 - ξ)) * (0)) + (-2) *
      ((2 * log (1 - ξ)) * (0)) + 2 * ((2 * log (1 - ξ)) * (Li₂ ξ)) + (-1) *
      ((2 * log (1 - ξ)) * (2 * log (1 - ξ)) * (log ξ)) + (-2) * ((2 * log (1 - ξ)) * (0)) + 2 *
      ((2 * log (1 - ξ)) * (0)) + 2 * ((2 * log (1 - ξ)) * (0)) + 1 * ((2 * log (1 - ξ)) * (0)) +
      (-2) * ((2 * log (1 - ξ)) * (Li₂ ξ)) + 3 * ((2 * log (1 - ξ)) * (Li₂ (-ξ))) + (-1) *
      ((2 * log (1 - ξ)) * (Li₂ (-ξ))) + 3 * ((log ξ) * (0)) + (-3) * ((log ξ) * (0))

theorem i5C1E_tR0f {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0f ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0f ξ)) := by
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t9 := i5C1E_t0_9 hξ
  have t10 := i5C1E_t0_10 hξ
  have t11 := i5C1E_t0_11 hξ
  have t12 := i5C1E_t0_12 hξ
  have t13 := i5C1E_t0_13 hξ
  have t14 := i5C1E_t0_14 hξ
  have t15 := i5C1E_t0_15 hξ
  have t18 := i5C1E_t0_18 hξ
  have t19 := i5C1E_t0_19 hξ
  have t20 := i5C1E_t0_20 hξ
  have t21 := i5C1E_t0_21 hξ
  have h := ((((((((((((((((((((((t6.mul t6).mul t7).const_mul 1).add
      (((t6.mul t7).mul t7).const_mul (-2))).add ((t6.mul t9).const_mul (-4))).add
      ((t6.mul t10).const_mul 8)).add ((t6.mul t11).const_mul 2)).add
      ((t6.mul t12).const_mul (-4))).add ((t6.mul t13).const_mul 8)).add
      ((t6.mul t14).const_mul 2)).add ((t6.mul t18).const_mul (-2))).add
      ((t6.mul t19).const_mul 2)).add (((t7.mul t7).mul c8).const_mul (-1))).add
      ((t7.mul t9).const_mul (-2))).add ((t7.mul t13).const_mul 2)).add
      ((t7.mul t14).const_mul 2)).add ((t7.mul t15).const_mul 1)).add
      ((t7.mul t19).const_mul (-2))).add ((t7.mul t20).const_mul 3)).add
      ((t7.mul t21).const_mul (-1))).add ((c8.mul t10).const_mul 3)).add
      ((c8.mul t13).const_mul (-3)))
  exact h

/-- Part `g` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0g (ξ x : ℝ) : ℝ :=
  1 * (log ξ * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) + (-3) * (log ξ *
      Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) + (-1) * (log ξ * Li₂ (-(ξ *
      (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) + 1 * Li₂ (ξ * (1 - x)) + (-3) *
      Li₂ (-(ξ * x / (1 - ξ))) + (-1) * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) + (-8) *
      Li₃ ((1 - x)) + (-9) * Li₃ (x / (1 - ξ)) + 4 * Li₃ (ξ / (1 - x)) + 3 * Li₃ (ξ * (1 - x)) +
      (-18) * Li₃ (-(ξ * x / (1 - ξ))) + (-1) * Li₃ ((ξ * x + (1 - ξ))) + 1 *
      Li₃ ((1 - ξ - x) / (1 - x)) + (-6) * Li₃ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) + 3 *
      Li₃ ((1 - ξ - x) / (1 - ξ)) + 1 * Li₃ (ξ * (1 - ξ - x) / (1 - ξ)) + 3 *
      Li₃ ((1 + ξ) * x / (ξ * x + (1 - ξ))) + 4 * Li₃ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) + (-3) *
      Li₃ ((1 - ξ - x) / (ξ * x + (1 - ξ))) + 6 * Li₃ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))

/-- The limit of `i5C1E_R0g`. -/
noncomputable def i5C1E_V0g (ξ : ℝ) : ℝ :=
  1 * ((log ξ) * (0)) + (-3) * ((log ξ) * (0)) + (-1) * ((log ξ) * (Li₂ (-ξ))) + 1 * (Li₂ ξ) +
      (-3) * (0) + (-1) * (Li₂ ξ) + (-8) * (zeta3) + (-9) * (0) + 4 * (Li₃ ξ) + 3 * (Li₃ ξ) +
      (-18) * (0) + (-1) * (Li₃ (1 - ξ)) + 1 * (Li₃ (1 - ξ)) + (-6) * (0) + 3 * (zeta3) + 1 *
      (Li₃ ξ) + 3 * (0) + 4 * (Li₃ ξ) + (-3) * (zeta3) + 6 * (Li₃ (-ξ))

theorem i5C1E_tR0g {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0g ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0g ξ)) := by
  have c8 : Tendsto (fun _ : ℝ => log ξ) (𝓝[>] 0) (𝓝 (log ξ)) :=
    tendsto_const_nhds
  have t12 := i5C1E_t0_12 hξ
  have t13 := i5C1E_t0_13 hξ
  have t15 := i5C1E_t0_15 hξ
  have t17 := i5C1E_t0_17 hξ
  have t19 := i5C1E_t0_19 hξ
  have t21 := i5C1E_t0_21 hξ
  have t22 := i5C1E_t0_22 hξ
  have t23 := i5C1E_t0_23 hξ
  have t24 := i5C1E_t0_24 hξ
  have t25 := i5C1E_t0_25 hξ
  have t26 := i5C1E_t0_26 hξ
  have t27 := i5C1E_t0_27 hξ
  have t28 := i5C1E_t0_28 hξ
  have t29 := i5C1E_t0_29 hξ
  have t30 := i5C1E_t0_30 hξ
  have t31 := i5C1E_t0_31 hξ
  have t32 := i5C1E_t0_32 hξ
  have t33 := i5C1E_t0_33 hξ
  have t34 := i5C1E_t0_34 hξ
  have t35 := i5C1E_t0_35 hξ
  have h := (((((((((((((((((((((c8.mul t15).const_mul 1).add ((c8.mul t17).const_mul (-3))).add
      ((c8.mul t21).const_mul (-1))).add (t12.const_mul 1)).add (t13.const_mul (-3))).add
      (t19.const_mul (-1))).add (t22.const_mul (-8))).add (t23.const_mul (-9))).add
      (t24.const_mul 4)).add (t25.const_mul 3)).add (t26.const_mul (-18))).add
      (t27.const_mul (-1))).add (t28.const_mul 1)).add (t29.const_mul (-6))).add
      (t30.const_mul 3)).add (t31.const_mul 1)).add (t32.const_mul 3)).add (t33.const_mul 4)).add
      (t34.const_mul (-3))).add (t35.const_mul 6))
  exact h

/-- Part `h` of the regular part of the primitive at `x = 0`. -/
noncomputable def i5C1E_R0h (ξ x : ℝ) : ℝ :=
  6 * Li₃ ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) + (-3) * Li₃ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) +
      (-3) * Li₃ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) + (-2) *
      Li₃ ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) + (-15) *
      Li₃ (ξ * x / (ξ * x + (1 - ξ))) + 3 * Li₃ (ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))) + (-1) *
      Li₃ (ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ))) + (-6) * Li₃ (ξ *
      x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * Li₃ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) + (-1) *
      Li₃ ((1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x))) + 6 * Li₃ (ξ * x *
      (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) + (-2) * Li₃ (ξ *
      (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) + 6 * Li₃ (x *
      (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 6 * Li₃ (-(ξ * x *
      (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) + 2 * Li₃ ((1 - ξ) ^ 2 *
      (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 * Li₃ ((1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x +
      (1 - ξ))) + (-2) * Li₃ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) *
      (1 - x))) + 2 * Li₃ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2))

/-- The limit of `i5C1E_R0h`. -/
noncomputable def i5C1E_V0h (ξ : ℝ) : ℝ :=
  6 * (zeta3) + (-3) * (Li₃ (1 - ξ)) + (-3) * (Li₃ (1 - ξ)) + (-2) * (zeta3) + (-15) * (0) + 3 *
      (Li₃ (ξ / (1 + ξ))) + (-1) * (Li₃ (ξ ^ 2)) + (-6) * (0) + 2 * (zeta3) + (-1) *
      (Li₃ (1 / (1 + ξ))) + 6 * (0) + (-2) * (Li₃ (ξ / (1 + ξ))) + 6 * (0) + 6 * (0) + 2 *
      (zeta3) + 1 * (Li₃ (1 - ξ ^ 2)) + (-2) * (Li₃ ξ) + 2 * (Li₃ (1 - ξ))

theorem i5C1E_tR0h {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_R0h ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0h ξ)) := by
  have t36 := i5C1E_t0_36 hξ
  have t37 := i5C1E_t0_37 hξ
  have t38 := i5C1E_t0_38 hξ
  have t39 := i5C1E_t0_39 hξ
  have t40 := i5C1E_t0_40 hξ
  have t41 := i5C1E_t0_41 hξ
  have t42 := i5C1E_t0_42 hξ
  have t43 := i5C1E_t0_43 hξ
  have t44 := i5C1E_t0_44 hξ
  have t45 := i5C1E_t0_45 hξ
  have t46 := i5C1E_t0_46 hξ
  have t47 := i5C1E_t0_47 hξ
  have t48 := i5C1E_t0_48 hξ
  have t49 := i5C1E_t0_49 hξ
  have t50 := i5C1E_t0_50 hξ
  have t51 := i5C1E_t0_51 hξ
  have t52 := i5C1E_t0_52 hξ
  have t53 := i5C1E_t0_53 hξ
  have h := ((((((((((((((((((t36.const_mul 6).add (t37.const_mul (-3))).add
      (t38.const_mul (-3))).add (t39.const_mul (-2))).add (t40.const_mul (-15))).add
      (t41.const_mul 3)).add (t42.const_mul (-1))).add (t43.const_mul (-6))).add
      (t44.const_mul 2)).add (t45.const_mul (-1))).add (t46.const_mul 6)).add
      (t47.const_mul (-2))).add (t48.const_mul 6)).add (t49.const_mul 6)).add
      (t50.const_mul 2)).add (t51.const_mul 1)).add (t52.const_mul (-2))).add (t53.const_mul 2))
  exact h

/-- The limit of the primitive at `x = 0`. -/
noncomputable def i5C1E_V0 (ξ : ℝ) : ℝ :=
  i5C1E_V0a ξ + i5C1E_V0b ξ + i5C1E_V0c ξ + i5C1E_V0d ξ + i5C1E_V0e ξ + i5C1E_V0f ξ + i5C1E_V0g ξ +
      i5C1E_V0h ξ

/-- The coefficient of `log x ^ 1` in the primitive. -/
noncomputable def i5C1E_A1 (ξ x : ℝ) : ℝ :=
  (-9 / 2) * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + 9 *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ - x)) + 6 * (log (ξ * x + (1 - ξ)) * log (1 + ξ)) +
      (-6) * (log (ξ * x + (1 - ξ)) * log (1 - x)) + (-3) * log (ξ * x + (1 - ξ)) + (25 / 2) *
      (log (1 - ξ) * log (1 - ξ)) + (-9) * (log (1 - ξ) * log (1 - ξ - x)) + 10 *
      (log (1 - ξ) * log (1 - x)) + (-4) * (log (1 - ξ) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-4) *
      (log (1 - ξ) * log (ξ * x + (1 - ξ) ^ 2)) + 3 * log (1 - ξ) + (-6) *
      (log (1 - ξ - x) * log (1 + ξ)) + (-2) * (log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + 6 * Li₂ (x / (1 - ξ)) + 3 *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) + (-6) * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) + 3 *
      Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) + (-3) * Li₂ (-(ξ *
      (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))

theorem i5C1E_tA1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_A1 ξ) (𝓝[>] 0) (𝓝 ((-9 / 2) * ((log (1 - ξ)) * (log (1 - ξ))) + 9 *
        ((log (1 - ξ)) * (log (1 - ξ))) + 6 * ((log (1 - ξ)) * (log (1 + ξ))) + (-6) *
        ((log (1 - ξ)) * (0)) + (-3) * (log (1 - ξ)) + (25 / 2) * ((log (1 - ξ)) * (log (1 - ξ))) +
        (-9) * ((log (1 - ξ)) * (log (1 - ξ))) + 10 * ((log (1 - ξ)) * (0)) + (-4) *
        ((log (1 - ξ)) * (2 * log (1 - ξ))) + (-4) * ((log (1 - ξ)) * (2 * log (1 - ξ))) + 3 *
        (log (1 - ξ)) + (-6) * ((log (1 - ξ)) * (log (1 + ξ))) + (-2) * ((0) * (2 * log (1 - ξ))) +
        2 * ((2 * log (1 - ξ)) * (2 * log (1 - ξ))) + 6 * (0) + 3 * (0) + (-6) * (0) + 3 *
        (Li₂ (-ξ)) + (-3) * (Li₂ (-ξ)))) := by
  have t1 := i5C1E_t0_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[>] 0) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have t3 := i5C1E_t0_3 hξ
  have c4 : Tendsto (fun _ : ℝ => log (1 + ξ)) (𝓝[>] 0) (𝓝 (log (1 + ξ))) :=
    tendsto_const_nhds
  have t5 := i5C1E_t0_5 hξ
  have t6 := i5C1E_t0_6 hξ
  have t7 := i5C1E_t0_7 hξ
  have t10 := i5C1E_t0_10 hξ
  have t15 := i5C1E_t0_15 hξ
  have t17 := i5C1E_t0_17 hξ
  have t20 := i5C1E_t0_20 hξ
  have t21 := i5C1E_t0_21 hξ
  have h := ((((((((((((((((((((t1.mul t1).const_mul (-9 / 2)).add ((t1.mul t3).const_mul 9)).add
      ((t1.mul c4).const_mul 6)).add ((t1.mul t5).const_mul (-6))).add (t1.const_mul (-3))).add
      ((c2.mul c2).const_mul (25 / 2))).add ((c2.mul t3).const_mul (-9))).add
      ((c2.mul t5).const_mul 10)).add ((c2.mul t6).const_mul (-4))).add
      ((c2.mul t7).const_mul (-4))).add (c2.const_mul 3)).add ((t3.mul c4).const_mul (-6))).add
      ((t5.mul t6).const_mul (-2))).add ((t6.mul t7).const_mul 2)).add (t10.const_mul 6)).add
      (t15.const_mul 3)).add (t17.const_mul (-6))).add (t20.const_mul 3)).add (t21.const_mul (-3)))
  exact h

theorem i5C1E_dA1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (i5C1E_A1 ξ) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have d1 : DifferentiableAt ℝ (fun x => log (ξ * x + (1 - ξ))) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have dc2 : DifferentiableAt ℝ (fun _ : ℝ => log (1 - ξ)) 0 :=
    differentiableAt_const _
  have d3 : DifferentiableAt ℝ (fun x => log (1 - ξ - x)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have dc4 : DifferentiableAt ℝ (fun _ : ℝ => log (1 + ξ)) 0 :=
    differentiableAt_const _
  have d5 : DifferentiableAt ℝ (fun x => log (1 - x)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have d6 : DifferentiableAt ℝ (fun x => log (ξ * x ^ 2 + (1 - ξ) ^ 2)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have d7 : DifferentiableAt ℝ (fun x => log (ξ * x + (1 - ξ) ^ 2)) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have d10 := i5C1E_d0_10 hξ
  have d15 := i5C1E_d0_15 hξ
  have d17 := i5C1E_d0_17 hξ
  have d20 := i5C1E_d0_20 hξ
  have d21 := i5C1E_d0_21 hξ
  have h := ((((((((((((((((((((d1.mul d1).const_mul (-9 / 2)).add ((d1.mul d3).const_mul 9)).add
      ((d1.mul dc4).const_mul 6)).add ((d1.mul d5).const_mul (-6))).add (d1.const_mul (-3))).add
      ((dc2.mul dc2).const_mul (25 / 2))).add ((dc2.mul d3).const_mul (-9))).add
      ((dc2.mul d5).const_mul 10)).add ((dc2.mul d6).const_mul (-4))).add
      ((dc2.mul d7).const_mul (-4))).add (dc2.const_mul 3)).add ((d3.mul dc4).const_mul (-6))).add
      ((d5.mul d6).const_mul (-2))).add ((d6.mul d7).const_mul 2)).add (d10.const_mul 6)).add
      (d15.const_mul 3)).add (d17.const_mul (-6))).add (d20.const_mul 3)).add (d21.const_mul (-3)))
  exact h

theorem i5C1E_zA1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : i5C1E_A1 ξ 0 = 0 := by
  have h1 := (i5C1E_dA1 hξ).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  rw [tendsto_nhds_unique h1 (i5C1E_tA1 hξ)]
  ring

/-- The coefficient of `log x ^ 2` in the primitive. -/
noncomputable def i5C1E_A2 (ξ x : ℝ) : ℝ :=
  3 * log (ξ * x + (1 - ξ)) + (-3) * log (1 - ξ)

theorem i5C1E_tA2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1E_A2 ξ) (𝓝[>] 0) (𝓝 (3 * (log (1 - ξ)) + (-3) * (log (1 - ξ)))) := by
  have t1 := i5C1E_t0_1 hξ
  have c2 : Tendsto (fun _ : ℝ => log (1 - ξ)) (𝓝[>] 0) (𝓝 (log (1 - ξ))) :=
    tendsto_const_nhds
  have h := ((t1.const_mul 3).add (c2.const_mul (-3)))
  exact h

theorem i5C1E_dA2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (i5C1E_A2 ξ) 0 := by
  have h0 := hξ.1
  have h1 := hξ.2
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have d1 : DifferentiableAt ℝ (fun x => log (ξ * x + (1 - ξ))) 0 := by
    fun_prop (disch := first | positivity | (simp only [sub_sub_cancel]; positivity))
  have dc2 : DifferentiableAt ℝ (fun _ : ℝ => log (1 - ξ)) 0 :=
    differentiableAt_const _
  have h := ((d1.const_mul 3).add (dc2.const_mul (-3)))
  exact h

theorem i5C1E_zA2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : i5C1E_A2 ξ 0 = 0 := by
  have h1 := (i5C1E_dA2 hξ).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  rw [tendsto_nhds_unique h1 (i5C1E_tA2 hξ)]
  ring

theorem i5C1E_PB_eq0 (ξ x : ℝ) :
    i5C1PB ξ x = i5C1E_R0a ξ x + i5C1E_R0b ξ x + i5C1E_R0c ξ x + i5C1E_R0d ξ x + i5C1E_R0e ξ x +
        i5C1E_R0f ξ x + i5C1E_R0g ξ x + i5C1E_R0h ξ x + log x * i5C1E_A1 ξ x + log x ^ 2 *
        i5C1E_A2 ξ x := by
  simp only [i5C1PB, i5C1Q0, i5C1Q1, i5C1Q2, i5C1Q3, i5C1Q4, i5C1Q5, i5C1Q6, i5C1Q7, i5C1Q8,
      i5C1Q9, i5C1Q10, i5C1Q11, i5C1Q12, i5C1Q13, i5C1Q14, i5C1Q15, i5C1Q16, i5C1Q17, i5C1Q18,
      i5C1Q19, i5C1Q20, i5C1Q21, i5C1Q22, i5C1Q23, i5C1Q24, i5C1Q25, i5C1Q26, i5C1Q27, i5C1Q28,
      i5C1Q29, i5C1Q30, i5C1Q31, i5C1Q32, i5C1Q33, i5C1Q34, i5C1Q35, i5C1Q36, i5C1Q37, i5C1Q38,
      i5C1Q39, i5C1Q40, i5C1Q41, i5C1E_R0a, i5C1E_R0b, i5C1E_R0c, i5C1E_R0d, i5C1E_R0e, i5C1E_R0f,
      i5C1E_R0g, i5C1E_R0h, i5C1E_A1, i5C1E_A2]
  ring

/-- **The limit of the primitive at `x = 0⁺`.** -/
theorem tendsto_i5C1PB_zero {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i5C1PB ξ) (𝓝[>] 0) (𝓝 (i5C1E_V0 ξ)) := by
  have hA1 := i5C1_tendsto_log_pow_mul 1 (i5C1E_dA1 hξ) (i5C1E_zA1 hξ)
  have hA2 := i5C1_tendsto_log_pow_mul 2 (i5C1E_dA2 hξ) (i5C1E_zA2 hξ)
  simp only [pow_one] at hA1
  have h := ((((((((((i5C1E_tR0a hξ).add (i5C1E_tR0b hξ)).add (i5C1E_tR0c hξ)).add
      (i5C1E_tR0d hξ)).add (i5C1E_tR0e hξ)).add (i5C1E_tR0f hξ)).add (i5C1E_tR0g hξ)).add
      (i5C1E_tR0h hξ))).add hA1).add hA2
  rw [add_zero, add_zero] at h
  exact h.congr fun x => (i5C1E_PB_eq0 ξ x).symm

end QED.ThreeLoopD
