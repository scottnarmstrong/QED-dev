/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN

/-!
# The constant `ζ(5)`

`zeta5 = ∑_{n ≥ 1} 1 / n ^ 5`, as a real number, mirroring `QED.Polylog.zeta3`.

## Main results

* `QED.Polylog.hasSum_zeta5`: the defining series converges to `zeta5`.
* `QED.Polylog.riemannZeta_five`, `QED.Polylog.riemannZeta_five_re`: `riemannZeta 5 = zeta5`.
* `QED.Polylog.Li_five_one`: `Li 5 1 = zeta5`.
* `QED.Polylog.zeta5_pos`: `0 < zeta5`.
-/

@[expose] public section

namespace QED.Polylog

/-- The value `ζ(5) = ∑_{n ≥ 1} 1 / n ^ 5`, as a real number. -/
noncomputable def zeta5 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5

/-- The series defining `zeta5` converges. -/
theorem hasSum_zeta5 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 5) zeta5 :=
  (summable_one_div_add_one_pow (by norm_num)).hasSum

/-- `Li 5 1 = zeta5`. -/
theorem Li_five_one : Li 5 1 = zeta5 := Li_at_one 5

/-- `zeta5` is the value of the Riemann zeta function at `5`. -/
theorem riemannZeta_five : riemannZeta 5 = (zeta5 : ℂ) := by
  have h := riemannZeta_natCast_eq_Li_one (k := 5) (by norm_num)
  rw [Li_five_one] at h
  exact_mod_cast h

/-- `zeta5` is the real part of `riemannZeta 5`. -/
theorem riemannZeta_five_re : (riemannZeta 5).re = zeta5 := by
  rw [riemannZeta_five, Complex.ofReal_re]

/-- `zeta5` is positive. -/
theorem zeta5_pos : 0 < zeta5 := by
  refine lt_of_lt_of_le ?_ (sum_le_hasSum (Finset.range 1) (fun n _ => by positivity) hasSum_zeta5)
  norm_num

end QED.Polylog
