/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ConstBounds

/-!
# The set (c) constant and its enclosure

Helper-level definition for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md` (the
second-order vacuum-polarization insertion into the photon lines of the fourth-order vertex
graphs, 12 diagrams). It is **not** frozen.

The closed form is Barbieri–Remiddi, CERN preprint TH.1801 (1974), Phys. Lett. B 49 (1974) 468,
eq. (3), with `ζ(2) = π²/6`:
`A_(c) = 227/72 + 31/9 ζ(2) - 8 ζ(2) ln 2 - 35/8 ζ(3) + 2 ζ(2)²
  = -0.150 172 282 099 798 375 213…`.

This module only *defines* the closed-form expression and encloses it. It does not claim that
the expression equals any Feynman-diagram quantity.

## Main statements

* `QED.Chain.aSetC`: the closed form.
* `QED.Chain.aSetC_bounds_fine`: `-0.1501722820997984 < aSetC < -0.1501722820997983`.
* `QED.Chain.aSetC_bounds`: `-0.15017228210 < aSetC < -0.15017228209` (width `10⁻¹¹`).
-/

@[expose] public section

open Real QED.Polylog

namespace QED.Chain

/-- The sixth-order set (c) constant (Barbieri–Remiddi 1974, eq. (3)), with `ζ(2) = π²/6`. -/
noncomputable def aSetC : ℝ :=
  227 / 72 + 31 / 9 * (π ^ 2 / 6) - 8 * (π ^ 2 / 6) * log 2 - 35 / 8 * zeta3 +
    2 * (π ^ 2 / 6) ^ 2

/-- `-0.1501722820997984 < A_(c) < -0.1501722820997983`
(true value `-0.15017228209979837521…`). -/
theorem aSetC_bounds_fine : -0.1501722820997984 < aSetC ∧ aSetC < -0.1501722820997983 := by
  have hp := pi_sq_bounds
  have hl := log_two_bounds
  have hz : (1.202056903159594284 : ℝ) ≤ zeta3 ∧ zeta3 ≤ 1.202056903159594286 :=
    ⟨zeta3_gt_d18.le, zeta3_lt_d18.le⟩
  have hpl := mul_bounds (by norm_num) (by norm_num) hp hl
  have hp4 := mul_bounds (by norm_num) (by norm_num) hp hp
  have e : aSetC = 227 / 72 + 31 / 54 * π ^ 2 - 4 / 3 * (π ^ 2 * log 2) - 35 / 8 * zeta3 +
      1 / 18 * (π ^ 2 * π ^ 2) := by
    unfold aSetC; ring
  rw [e]
  norm_num at hp hpl hp4 ⊢
  constructor <;> linarith [hp.1, hp.2, hz.1, hz.2, hpl.1, hpl.2, hp4.1, hp4.2]

/-- **The set (c) constant to eleven decimals**: `-0.15017228210 < A_(c) < -0.15017228209`. -/
theorem aSetC_bounds : -0.15017228210 < aSetC ∧ aSetC < -0.15017228209 := by
  have h := aSetC_bounds_fine
  constructor <;> linarith [h.1, h.2]

end QED.Chain
