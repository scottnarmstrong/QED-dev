/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: dilogarithm antiderivative tools

Helper level (no frozen statement). Shared by the closed forms of `ρ_C` and `ρ_X`. An integrand
`log(1 - w(u)) w'(u)/w(u)` (for linear `w`, this is `log|ℓ(u)/ℓ(u₀)|/p(u)` with `w = 1 - ℓ/ℓ(u₀)`,
`p` the linear factor vanishing at `u₀`) has the formal antiderivative `-Li₂(w)`. Lean's `Li₂` has
a usable derivative only on `(-1, 1)` (`hasDerivAt_Li₂`), so three forms are provided, each with
its argument in `(-1, 1)`:

* **`li2_hasDerivAt_neg`**: `|w| < 1`: `-Li₂(w)`;
* **`li2_hasDerivAt_inv`**: `w > 1`: `Li₂(1/w) + log² w/2` (inversion), derivative
  `log(w - 1) w'/w`;
* **`li2_hasDerivAt_landen`**: `w < 0`: `Li₂(w/(w - 1)) + log²(1 - w)/2` (Landen).
-/

@[expose] public section

open Real

namespace QED.ChainProof.SetCK

open QED.Polylog

variable {w : ℝ → ℝ} {w' u : ℝ}

/-- The direct form: `(-Li₂ ∘ w)' = log(1 - w) w'/w` for `0 < |w| < 1`. -/
theorem li2_hasDerivAt_neg (hw : HasDerivAt w w' u) (h1 : |w u| < 1) (h0 : w u ≠ 0) :
    HasDerivAt (fun v => -Li₂ (w v)) (log (1 - w u) * (w' / w u)) u := by
  have h := ((hasDerivAt_Li₂ h1 h0).comp u hw).neg
  refine h.congr_deriv ?_
  ring

/-- The inversion form, for `w > 1`: `(Li₂(1/w) + log² w/2)' = log(w - 1) w'/w`. -/
theorem li2_hasDerivAt_inv (hw : HasDerivAt w w' u) (h1 : 1 < w u) :
    HasDerivAt (fun v => Li₂ (1 / w v) + log (w v) ^ 2 / 2) (log (w u - 1) * (w' / w u)) u := by
  have hw0 : w u ≠ 0 := by positivity
  have hinv : HasDerivAt (fun v => 1 / w v) (-w' / w u ^ 2) u := by
    refine ((hasDerivAt_const u (1 : ℝ)).div hw hw0).congr_deriv ?_
    ring
  have ha : |1 / w u| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    exact h1
  have h := ((hasDerivAt_Li₂ ha (by positivity)).comp u hinv).add
    (((hw.log hw0).pow 2).div_const 2)
  refine h.congr_deriv ?_
  have e : 1 - 1 / w u = (w u - 1) / w u := by field_simp
  rw [e, log_div (by linarith) hw0]
  field_simp
  ring

/-- The Landen form, for `w < 0`: `(Li₂(w/(w - 1)) + log²(1 - w)/2)' = log(1 - w) w'/w`. -/
theorem li2_hasDerivAt_landen (hw : HasDerivAt w w' u) (h0 : w u < 0) :
    HasDerivAt (fun v => Li₂ (w v / (w v - 1)) + log (1 - w v) ^ 2 / 2)
      (log (1 - w u) * (w' / w u)) u := by
  have hw1 : w u - 1 ≠ 0 := by linarith
  have hz : HasDerivAt (fun v => w v / (w v - 1)) (-w' / (w u - 1) ^ 2) u := by
    refine (hw.div (hw.sub_const 1) hw1).congr_deriv ?_
    field_simp
    ring
  have hzpos : 0 < w u / (w u - 1) := div_pos_of_neg_of_neg h0 (by linarith)
  have ha : |w u / (w u - 1)| < 1 := by
    rw [abs_of_pos hzpos, div_lt_one_of_neg (by linarith)]
    linarith
  have h1w : HasDerivAt (fun v => 1 - w v) (-w') u := hw.const_sub 1
  have h := ((hasDerivAt_Li₂ ha hzpos.ne').comp u hz).add
    (((h1w.log (by linarith)).pow 2).div_const 2)
  refine h.congr_deriv ?_
  have h1 : 1 - w u ≠ 0 := by linarith
  have e : 1 - w u / (w u - 1) = (1 - w u)⁻¹ := by
    field_simp
    ring
  have hw0 : w u ≠ 0 := h0.ne
  rw [e, log_inv]
  field_simp
  ring

end QED.ChainProof.SetCK

end
