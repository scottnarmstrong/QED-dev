/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornIn
public import QED.ChainProof.SetCKPairS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the boundary term on the second branch

Helper level (no frozen statement). In the inner-massive corner unit the boundary term
`δ/(M + w₀)` of `cornerGm_add_log_eq` vanishes on the first branch `x(1-y₃) ≤ 1-Y`
(`cornInDel_of_branch1`, `betaG_of_branch1`). On the second branch `x(1-y₃) ≥ 1-Y` the threshold
is `w₀ = e x²/(1-x)`, `e = y₃(Y-y₃)` (`cornInW0_of_branch2`), and

`δ = φ(x) w₀'(x)`, `w₀' = e x(2-x)/(1-x)²` (`cornInDel_of_branch2`),

with the rational function (generated in exact arithmetic, scratch `g2/mkPhi.py`)

`φ = (x-1)² (1 - Y - x(1-y₃)) P(x)/(4x² y₃ (y₃-Y)³ (x-2))` (`cornInPhi`, `P` a cubic in `x`),

which vanishes at both ends `x* = (1-Y)/(1-y₃)` and `x = 1` of the branch. Its derivative is
`φ' = (x-1) N(x)/(2x³ y₃ (y₃-Y)³ (x-2)²)` (`cornInDPhi`, `hasDerivAt_cornInPhi`).
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The cubic factor `P` of `φ`, as coefficients in `x` (used through `hpoly`). -/
noncomputable def cornInPl (Y y3 : ℝ) : List ℝ :=
  [-2*(-Y^3 + Y^2*y3 + 2*Y^2 - Y - 2*y3 + 1), -2*Y^3 - 2*Y^2*y3 + 6*Y^2 + 4*Y*y3^2 - 3*Y -
    6*y3 + 3, 4*Y^2*y3 - 2*Y^2 - 2*Y*y3^2 - 4*Y*y3 + 2*Y - 2*y3^3 + 4*y3^2 + y3 - 1, 2*y3*(-Y +
    y3)*(y3 - 1)]

/-- The numerator `N` of `φ′`, as coefficients in `x` (used through `hpoly`). -/
noncomputable def cornInNl (Y y3 : ℝ) : List ℝ :=
  [-4*(Y - 1)*(-Y^3 + Y^2*y3 + 2*Y^2 - Y - 2*y3 + 1), -5*Y^4 - Y^3*y3 + 19*Y^3 + 6*Y^2*y3^2 +
    Y^2*y3 - 22*Y^2 - 4*Y*y3^2 - 14*Y*y3 + 14*Y - 4*y3^2 + 18*y3 - 8, -(Y - 1)*(-Y^3 + Y^2*y3 +
    2*Y^2 - Y - 2*y3 + 1), 9*Y^3*y3 - 6*Y^3 + 6*Y^2*y3^2 - 32*Y^2*y3 + 17*Y^2 - 13*Y*y3^3 +
    13*Y*y3^2 + 20*Y*y3 - 11*Y - 2*y3^4 + 11*y3^3 - 2*y3^2 - 17*y3 + 7, -3*Y^3*y3 + 2*Y^3 -
    18*Y^2*y3^2 + 32*Y^2*y3 - 11*Y^2 + 11*Y*y3^3 + 9*Y*y3^2 - 32*Y*y3 + 9*Y + 10*y3^4 - 33*y3^3
    + 18*y3^2 + 11*y3 - 5, -(y3 - 1)*(-6*Y^2*y3 + 2*Y^2 - 5*Y*y3^2 + 15*Y*y3 - 2*Y + 11*y3^3 -
    15*y3^2 - y3 + 1), 3*y3*(-Y + y3)*(y3 - 1)^2]

/-- **The function `φ`**: the boundary term on the second branch is `φ · w₀′`. -/
noncomputable def cornInPhi (Y y3 x : ℝ) : ℝ :=
  (x - 1) ^ 2 * (1 - Y - x * (1 - y3)) * hpoly (cornInPl Y y3) x /
    (4 * x ^ 2 * y3 * (y3 - Y) ^ 3 * (x - 2))

/-- The derivative `φ′` of `cornInPhi` in `x`. -/
noncomputable def cornInDPhi (Y y3 x : ℝ) : ℝ :=
  (x - 1) * hpoly (cornInNl Y y3) x / (2 * x ^ 3 * y3 * (y3 - Y) ^ 3 * (x - 2) ^ 2)

/-- The branch point `x* = (1 − Y)/(1 − y₃)`. -/
noncomputable def cornInXs (Y y3 : ℝ) : ℝ := (1 - Y) / (1 - y3)

theorem hasDerivAt_cornInPhi {Y y3 x : ℝ} (hx : x ≠ 0) (hx2 : x ≠ 2) (h3 : y3 ≠ 0)
    (h34 : y3 - Y ≠ 0) : HasDerivAt (cornInPhi Y y3) (cornInDPhi Y y3 x) x := by
  have hn : HasDerivAt (fun x => (x - 1) ^ 2 * (1 - Y - x * (1 - y3)) * hpoly (cornInPl Y y3) x)
      (2 * (x - 1) * (1 - Y - x * (1 - y3)) * hpoly (cornInPl Y y3) x +
        (x - 1) ^ 2 * (-(1 - y3)) * hpoly (cornInPl Y y3) x +
        (x - 1) ^ 2 * (1 - Y - x * (1 - y3)) * hpolyD (cornInPl Y y3) x) x := by
    have h1 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (x - 1)) x := by
      exact (((hasDerivAt_id' x).sub_const 1).pow 2).congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun x : ℝ => 1 - Y - x * (1 - y3)) (-(1 - y3)) x := by
      exact ((hasDerivAt_const x (1 - Y)).sub ((hasDerivAt_id' x).mul_const (1 - y3))).congr_deriv
        (by ring)
    have := (h1.mul h2).mul (hasDerivAt_hpoly (cornInPl Y y3) x)
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hd : HasDerivAt (fun x : ℝ => 4 * x ^ 2 * y3 * (y3 - Y) ^ 3 * (x - 2))
      (8 * x * y3 * (y3 - Y) ^ 3 * (x - 2) + 4 * x ^ 2 * y3 * (y3 - Y) ^ 3) x := by
    have h1 : HasDerivAt (fun x : ℝ => 4 * x ^ 2 * y3 * (y3 - Y) ^ 3) (8 * x * y3 * (y3 - Y) ^ 3)
        x := by
      have := (((hasDerivAt_pow 2 x).const_mul 4).mul_const y3).mul_const ((y3 - Y) ^ 3)
      refine this.congr_deriv ?_
      push_cast
      ring
    have := h1.mul ((hasDerivAt_id' x).sub_const 2)
    refine this.congr_deriv ?_
    ring
  have hne : 4 * x ^ 2 * y3 * (y3 - Y) ^ 3 * (x - 2) ≠ 0 := by
    have : x - 2 ≠ 0 := sub_ne_zero.2 hx2
    positivity
  refine (hn.div hd hne).congr_deriv ?_
  have : x - 2 ≠ 0 := sub_ne_zero.2 hx2
  simp only [cornInDPhi, cornInPl, cornInNl, hpoly, hpolyD]
  field_simp
  ring

theorem cornInPhi_xs (Y y3 : ℝ) (h3 : y3 ≠ 1) : cornInPhi Y y3 (cornInXs Y y3) = 0 := by
  have : 1 - y3 ≠ 0 := sub_ne_zero.2 (Ne.symm h3)
  have e : 1 - Y - cornInXs Y y3 * (1 - y3) = 0 := by
    unfold cornInXs
    field_simp
    ring
  simp [cornInPhi, e]

theorem cornInPhi_one (Y y3 : ℝ) : cornInPhi Y y3 1 = 0 := by
  simp [cornInPhi]

/-- On the first branch `x(1 − y₃) ≤ 1 − Y`, `β` is the corner value. -/
theorem betaG_of_branch1 {Y y3 x : ℝ} (h3 : 0 < y3) (hx : x < 1)
    (hb : x * (1 - y3) ≤ 1 - Y) :
    betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = cornerG y3 (Y - y3) := by
  unfold betaG cornerG
  refine max_eq_left ?_
  have h1 : 0 < 1 - x := by linarith
  rw [div_le_iff₀ h1]
  have : 0 < y3 := h3
  nlinarith [mul_pos h3 h1]

/-- On the second branch `1 − Y ≤ x(1 − y₃)`, `β = y₃(Y − y₃)x/(1 − x)`. -/
theorem betaG_of_branch2 {Y y3 x : ℝ} (h3 : 0 < y3) (hx : x < 1)
    (hb : 1 - Y ≤ x * (1 - y3)) :
    betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = y3 * (Y - y3) * x / (1 - x) := by
  unfold betaG cornerG
  refine max_eq_right ?_
  have h1 : 0 < 1 - x := by linarith
  rw [le_div_iff₀ h1]
  nlinarith [mul_pos h3 h1]

theorem cornInW0_of_branch2 {Y y3 x : ℝ} (h3 : 0 < y3) (hx : x < 1)
    (hb : 1 - Y ≤ x * (1 - y3)) : cornInW0 Y y3 x = y3 * (Y - y3) * x ^ 2 / (1 - x) := by
  rw [cornInW0, betaG_of_branch2 h3 hx hb]
  ring

/-- **The boundary term on the second branch** is `φ · w₀′`. -/
theorem cornInDel_of_branch2 {Y y3 x : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hb : 1 - Y ≤ x * (1 - y3)) :
    cornInDel Y y3 x = cornInPhi Y y3 x * (y3 * (Y - y3) * x * (2 - x) / (1 - x) ^ 2) := by
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : x - 2 ≠ 0 := by linarith [hx.2]
  have hx0 := hx.1.ne'
  have h30 := h3.ne'
  have h4 : y3 - Y ≠ 0 := by linarith
  have h4' : Y - y3 ≠ 0 := by linarith
  unfold cornInDel cornInDelta
  rw [cornInW0_of_branch2 h3 hx.2 hb]
  simp only [cornInPhi, cornInPl, hpoly, cornerA0, cornerA1, cornerA2, cornerG, cornerQ,
    QED.TwoLoop.UnitSCReduce.cornerP1]
  field_simp
  ring

end QED.ChainProof.SetCK

end
