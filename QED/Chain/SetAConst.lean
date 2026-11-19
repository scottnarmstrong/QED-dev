/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ConstBounds

/-!
# The set (a) constant and its enclosure

Helper-level definition for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md` (the
fourth-order vacuum-polarization insertion, 3 diagrams). It is **not** frozen.

The closed form is Kaptari–Lashkevich–Solovtsova, Phys. Rev. D 112 (2025) 073008,
arXiv:2508.05119v1, eq. (16) (the equal-mass value `A₂,L⁽⁶⁾(1)`, first obtained by
Mignaco–Remiddi, Nuovo Cim. A 60 (1969) 519):
`A_(a) = 673/108 - 41π²/81 - 7π⁴/270 - (4/9)π² ln 2 - (4/9)π² ln²2 + (4/9) ln⁴2
  + (32/3) Li₄(1/2) + (13/18) ζ(3) = 0.052 870 652 475 767 000 9…`.

## Main statements

* `QED.Chain.aSetA`: the closed form.
* `QED.Chain.aSetA_bounds_fine`: `0.0528706524757669 < aSetA < 0.0528706524757671`.
* `QED.Chain.aSetA_bounds`: `0.05287065247 < aSetA < 0.05287065248` (width `10⁻¹¹`).
-/

@[expose] public section

open Real QED.Polylog

namespace QED.Chain

/-- The sixth-order set (a) constant (Kaptari et al. 2025, eq. (16)). -/
noncomputable def aSetA : ℝ :=
  673 / 108 - 41 / 81 * π ^ 2 - 7 / 270 * π ^ 4 - 4 / 9 * π ^ 2 * log 2 -
    4 / 9 * π ^ 2 * log 2 ^ 2 + 4 / 9 * log 2 ^ 4 + 32 / 3 * Li 4 (1 / 2) + 13 / 18 * zeta3

/-- `0.0528706524757669 < A_(a) < 0.0528706524757671` (true value `0.05287065247576700093…`). -/
theorem aSetA_bounds_fine : 0.0528706524757669 < aSetA ∧ aSetA < 0.0528706524757671 := by
  have hp := pi_sq_bounds
  have hl := log_two_bounds
  have hz : (1.202056903159594284 : ℝ) ≤ zeta3 ∧ zeta3 ≤ 1.202056903159594286 :=
    ⟨zeta3_gt_d18.le, zeta3_lt_d18.le⟩
  have hal := Li_four_one_half_gt
  have hah := Li_four_one_half_lt
  have hpl := mul_bounds (by norm_num) (by norm_num) hp hl
  have hl2 := mul_bounds (by norm_num) (by norm_num) hl hl
  have hpl2 := mul_bounds (by norm_num) (by norm_num) hp hl2
  have hl4 := mul_bounds (by norm_num) (by norm_num) hl2 hl2
  have hp4 := mul_bounds (by norm_num) (by norm_num) hp hp
  have e : aSetA = 673 / 108 - 41 / 81 * π ^ 2 - 7 / 270 * (π ^ 2 * π ^ 2) -
      4 / 9 * (π ^ 2 * log 2) - 4 / 9 * (π ^ 2 * (log 2 * log 2)) +
      4 / 9 * (log 2 * log 2 * (log 2 * log 2)) + 32 / 3 * Li 4 (1 / 2) + 13 / 18 * zeta3 := by
    unfold aSetA; ring
  rw [e]
  norm_num at hp hpl hpl2 hl4 hp4 ⊢
  constructor <;>
    linarith [hp.1, hp.2, hz.1, hz.2, hpl.1, hpl.2, hpl2.1, hpl2.2, hl4.1, hl4.2, hp4.1, hp4.2]

/-- **The set (a) constant to eleven decimals**: `0.05287065247 < A_(a) < 0.05287065248`. -/
theorem aSetA_bounds : 0.05287065247 < aSetA ∧ aSetA < 0.05287065248 := by
  have h := aSetA_bounds_fine
  constructor <;> linarith [h.1, h.2]

end QED.Chain
