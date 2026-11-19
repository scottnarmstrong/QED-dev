/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossMirror
public import QED.ChainProof.SetCKCrossT
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G3: the `b`-integration of the crossed integrand at two masses

Helper level (no frozen statement). The link from the merged crossed integrand
`crossedTerm μ_a μ_b` (`QED/TwoLoop/UnitXGraphReduce.lean`) to the closed form `crossTGm` of
`QED/ChainProof/SetCKCrossT.lean`, the analogue of `QED.TwoLoop.UnitSCLimit.cornerAX_eq` and
`hasIoiInt_cornerAX_sub` for the corner. In the frame `y₃ + y₄ + z_b = 1`
(`z₂ = y₃`, `z₃ = y₄`), with `b = z_A + g`, `w = z_a + e = b(1-x)/x`, `g = y₃(1-Y)`, `e = y₃ y₄`:

* `crossedTerm_subst`: **the splitting identity (2.1) for the crossed graph at two photon
  masses**: the integrand times the Jacobian `b/x²` (`crossAX`) is
  `(a₁/b + a₂/b²)/D² + (c₁/b + c₂/b² + c₃/b³)/D`,
  `D = Y² + (1-Y) μ_b - μ_a e + b (x² + (1-x) μ_a)/x`, with the mass-independent coefficients
  `crossTA1, crossTA2, crossTC1, crossTC2, crossTC3`;
* `crossAX_eq`: the same as a combination of the masters `masterK5, K6, K2, K3, K7`;
* `hasIoiInt_crossAX`: **the `b`-integration**: for `M = cornerMass la lb y₃ y₄ > 0` and
  `h = (x² + (1-x) la²)/x > 0`, `z ↦ crossAX(z + β(x))` is integrable on `(0, ∞)` with integral
  `crossTGm la lb y₃ y₄ x`.

The identity of `crossedTerm_subst` was checked first in exact rational arithmetic at random
points with both masses nonzero (scratch `stageK/mir/m2.py`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The crossed integrand times the Jacobian** `b/x²` of `w = b(1-x)/x`, in the frame
`y₃ + y₄ + z_b = 1`, at photon masses² `μ_a` (outer) and `μ_b` (inner). -/
noncomputable def crossAX (μa μb y3 y4 x b : ℝ) : ℝ :=
  crossedTerm μa μb (b - cornerG y3 y4) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) *
    (b / x ^ 2)

/-- **The splitting identity for the crossed graph at two photon masses.** -/
theorem crossedTerm_subst {μa μb y3 y4 b x : ℝ} (hb : 0 < b) (hx : x ∈ Ioo (0 : ℝ) 1) :
    crossAX μa μb y3 y4 x b =
      (crossTA1 x y3 y4 / b + crossTA2 x y3 y4 / b ^ 2) /
          ((y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
            b * ((x ^ 2 + (1 - x) * μa) / x)) ^ 2 +
        (crossTC1 x y3 y4 / b + crossTC2 x y3 y4 / b ^ 2 + crossTC3 x y3 y4 / b ^ 3) /
          ((y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
            b * ((x ^ 2 + (1 - x) * μa) / x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hb0 := hb.ne'
  have hx0' := hx0.ne'
  have hU : gXU (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) =
      b / x := by
    rw [gXU_frame]; field_simp; ring
  have hU0 : gXU (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) ≠ 0 := by
    rw [hU]; positivity
  have hV : gXE (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) +
      μa * (b * (1 - x) / x - y3 * y4) + μb * (1 - y3 - y4) =
      (y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
        b * ((x ^ 2 + (1 - x) * μa) / x) := by
    rw [gXE_frame hU0]
    have hbx : b - y3 * (1 - y3 - y4) + y3 * (1 - y3 - y4) +
        (b * (1 - x) / x - y3 * y4 + y3 * y4) = b / x := by field_simp; ring
    rw [hbx]
    field_simp
    ring
  unfold crossAX crossedTerm
  rw [show cornerG y3 y4 = y3 * (1 - y3 - y4) from rfl, hV, hU]
  simp only [gPsi1, gPsi2, psiT1h, psiT2h, gXan, gXbn, hU, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, crossTA1, crossTN1, crossTA2, crossTPa, crossTC1, crossTC2, crossTN2,
    crossTC3, crossTP3]
  field_simp
  ring

/-- **The crossed integrand in the variables `(b, x)`** as a combination of the masters. -/
theorem crossAX_eq {la lb y3 y4 x b : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hb : 0 < b)
    (hD : 0 < cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x)) :
    crossAX (la ^ 2) (lb ^ 2) y3 y4 x b =
      crossTA1 x y3 y4 * masterK5 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        crossTA2 x y3 y4 * masterK6 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        crossTC1 x y3 y4 * masterK2 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        crossTC2 x y3 y4 * masterK3 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        crossTC3 x y3 y4 * masterK7 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b := by
  have eD : (y3 + y4) ^ 2 + (1 - (y3 + y4)) * lb ^ 2 - la ^ 2 * (y3 * y4) +
      b * ((x ^ 2 + (1 - x) * la ^ 2) / x) =
      cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x) := by
    unfold cornerMass ladderInnerMass; ring
  rw [crossedTerm_subst hb hx, eD]
  unfold masterK2 masterK3 masterK5 masterK6 masterK7
  have := hD.ne'
  have := hb.ne'
  field_simp
  ring

/-- **The `b`-integration of the crossed integrand**: for `(y₃, y₄)` in the open triangle,
`0 < x < 1`, `h > 0` and `M > 0`, the integrand at `b = z + β(x)` is integrable on `z > 0` with
integral `crossTGm la lb y₃ y₄ x`. -/
theorem hasIoiInt_crossAX {la lb y3 y4 x : ℝ} (h3 : 0 < y3) (hY : y3 + y4 < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hh : 0 < ladderInnerMass 1 la x / x)
    (hM : 0 < cornerMass la lb y3 y4) :
    HasIoiInt (fun z => crossAX (la ^ 2) (lb ^ 2) y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x))
      (crossTGm la lb y3 y4 x) := by
  have hg : 0 < cornerG y3 y4 := by
    unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
    positivity
  have hβ := betaG_pos (e := y3 * y4) (x := x) hg
  set M := cornerMass la lb y3 y4 with hMdef
  set h := ladderInnerMass 1 la x / x with hhdef
  set β := betaG (cornerG y3 y4) (y3 * y4) x with hβdef
  have I := (((((hasIoiInt_master5 hM hh hβ).const_mul (crossTA1 x y3 y4)).add
    ((hasIoiInt_master6 hM hh hβ).const_mul (crossTA2 x y3 y4))).add
    ((hasIoiInt_master2 hM hh hβ).const_mul (crossTC1 x y3 y4))).add
    ((hasIoiInt_master3 hM hh hβ).const_mul (crossTC2 x y3 y4))).add
    ((hasIoiInt_master7 hM hh hβ).const_mul (crossTC3 x y3 y4))
  refine I.congr (fun z hz => ?_) ?_
  · have hb : 0 < z + β := by simp only [mem_Ioi] at hz; linarith
    rw [crossAX_eq hx hb (by positivity)]
  · simp only [crossTGm, cForm]
    rw [← hMdef, ← hhdef, ← hβdef]
    ring

end QED.ChainProof.SetCK

end
