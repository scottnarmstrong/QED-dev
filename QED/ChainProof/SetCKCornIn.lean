/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInW
public import QED.ChainProof.SetCKLPair
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the corner unit with a massive inner photon

Helper level (no frozen statement). Group G2 of the set (c) kernel plan is the corner unit `C`
with the photon of mass² `t > 0` inside the vertex subgraph and the outer photon massless,
`C(t, 0)`. It is infrared finite by itself. From eq. (6.3) of `docs/TWO-LOOP-UNITS.md` at
infinite Pauli–Villars mass (`G_C = E_C - e₀ = cornerGm`, checked against the parametric engine),
with `Y = y₃ + y₄`, `M = M_t(Y) = Y² + (1-Y) t` and the counterterm `δ₁(t) F₂(0)`, `F₂(0) = 1/2`,

`C(t, 0) = 2 ∫₀¹ dY [∫₀^Y dy₃ ∫₀¹ dx cornerGm 0 (√t) y₃ (Y-y₃) x
  - (Y/2) ((Y² + 2Y - 2)/(2M) - (log M)/2)]` (`cornIn`).

Numerically (scratch `stageK/g2`) `cornIn 1 = 0.2738769552533539609` and
`cornIn 4 = 0.098856526607211374534` (the regulated unit at outer photon mass² `10⁻⁴⁰`).

In the unit, `h = x` and the `b`-threshold is `w₀ = β(x) x` (`cornInW0`), with the two branches
`β = g = y₃(1-Y)` for `x ≤ x* = (1-Y)/(1-y₃)` and `β = e x/(1-x)`, `e = y₃ y₄`, above.

* **`cornerGm_add_log_eq`**: the `w`-representation of `SetCKCornInW` in the unit:
  `cornerGm + ((1-x)/2) log M = ∫₀^∞ K(w)/(M + w) dw + δ/(M + w₀)`;
* **`cornInDel_of_branch1`**: the boundary term `δ` vanishes on the first branch
  (`a₀ g² + a₁ g + a₂ = 0`), so only the second branch carries one.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The `Y`-integrand of the inner-massive corner unit (with its counterterm). -/
noncomputable def cornInIntegrand (t Y : ℝ) : ℝ :=
  (∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, cornerGm 0 (√t) y3 (Y - y3) x) -
    Y / 2 * ((Y ^ 2 + 2 * Y - 2) / (2 * massIn t Y) - log (massIn t Y) / 2)

/-- **The inner-massive corner unit** `C(t, 0)`. -/
noncomputable def cornIn (t : ℝ) : ℝ := 2 * ∫ Y in (0 : ℝ)..1, cornInIntegrand t Y

/-- **The Stieltjes identity for G2** for a candidate density `ρ`. -/
def IsCornInDensity (ρ : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 < t → cornIn t = setCKStieltjes ρ t

/-- The `b`-threshold times `h = x`: `w₀ = β(x) x`. -/
noncomputable def cornInW0 (Y y3 x : ℝ) : ℝ := betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x * x

/-- The `w`-weight of the unit at `(Y, y₃, x)`. -/
noncomputable def cornInKw (Y y3 x w : ℝ) : ℝ :=
  cornInK (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3)) (cornerC0 x) (cornerC1 x y3 (Y - y3))
    (cornerC2 x y3 (Y - y3)) (cornerC3 x y3 (Y - y3)) x (cornInW0 Y y3 x) w

/-- The boundary term of the unit at `(Y, y₃, x)`. -/
noncomputable def cornInDel (Y y3 x : ℝ) : ℝ :=
  cornInDelta (cornerA0 x y3 (Y - y3)) (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3)) x
    (cornInW0 Y y3 x)

theorem cornerMass_zero_sqrt {t : ℝ} (ht : 0 ≤ t) (Y y3 : ℝ) :
    cornerMass 0 (√t) y3 (Y - y3) = massIn t Y := by
  unfold cornerMass massIn ladderInnerMass
  rw [sq_sqrt ht]
  ring

theorem cornerG_pos {Y y3 : ℝ} (hY : Y < 1) (h3 : 0 < y3) : 0 < cornerG y3 (Y - y3) := by
  unfold cornerG
  have : 0 < 1 - y3 - (Y - y3) := by linarith
  positivity

theorem cornInW0_pos {Y y3 x : ℝ} (hY : Y < 1) (h3 : 0 < y3) (hx : 0 < x) :
    0 < cornInW0 Y y3 x :=
  mul_pos (betaG_pos (cornerG_pos hY h3)) hx

/-- **The `w`-representation of the corner integrand** in the inner-massive unit. -/
theorem cornerGm_add_log_eq {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : 0 < y3) (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerGm 0 (√t) y3 (Y - y3) x + (1 - x) / 2 * log (massIn t Y) =
      (∫ w in Ioi 0, cornInKw Y y3 x w / (massIn t Y + w)) +
        cornInDel Y y3 x / (massIn t Y + cornInW0 Y y3 x) := by
  have hM := massIn_pos ht ⟨hY.1.le, hY.2.le⟩
  have hβ := betaG_pos (e := y3 * (Y - y3)) (x := x) (cornerG_pos hY.2 h3)
  have key := cForm_add_log_eq (a₀ := cornerA0 x y3 (Y - y3)) (a₁ := cornerA1 x y3 (Y - y3))
    (a₂ := cornerA2 x y3 (Y - y3)) (c₀ := cornerC0 x) (c₁ := cornerC1 x y3 (Y - y3))
    (c₂ := cornerC2 x y3 (Y - y3)) (c₃ := cornerC3 x y3 (Y - y3)) hM hβ hx.1
  have hc0 : cornerC0 x / x = (1 - x) / 2 := by
    unfold cornerC0
    field_simp [hx.1.ne']
  rw [hc0] at key
  unfold cornerGm
  rw [ladderInnerMass_zero_div hx.1.ne', cornerMass_zero_sqrt ht.le]
  exact key

/-- On the first branch the boundary term vanishes: `a₀ g² + a₁ g + a₂ = 0`. -/
theorem cornInDel_of_branch1 {Y y3 x : ℝ} (hY : Y < 1) (h3 : 0 < y3) (hx : 0 < x)
    (hb : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = cornerG y3 (Y - y3)) :
    cornInDel Y y3 x = 0 := by
  have hg := cornerG_pos hY h3
  unfold cornInDel cornInDelta cornInW0
  rw [hb]
  unfold cornerA0 cornerA1 cornerA2
  have := hg.ne'
  have := hx.ne'
  field_simp
  ring

end QED.ChainProof.SetCK

end
