/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R4Q

/-!
# Set (d), master `I₁₃`: the primitive `Ψ₄` and `p₄` in the variable `ξ`

`Ψ₄ = (N₀ + ξ N₁ + ξ² N₂ + ξ³ N₃ + ξ⁴ N₄)/ξ² + W` (`QED.ThreeLoopD.i13Psi4`), assembled from the
parts of `QED.ThreeLoopD.SetDMastersI13R4P` and `QED.ThreeLoopD.SetDMastersI13R4Q`, with its
derivative `QED.ThreeLoopD.i13Psi4D`, and `p₄` as a function of `ξ`
(`QED.ThreeLoopD.i13P4_eq`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i13Psi4`, `QED.ThreeLoopD.i13P4_eq`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### `Ψ₄` and its derivative -/

/-- The primitive `Ψ₄` of `p₄ dt/dξ`, as a function of `ξ`. -/
noncomputable def i13Psi4 (x : ℝ) : ℝ :=
  (i13Psi4N0 x + x * i13Psi4N1 x + x ^ 2 * i13Psi4N2 x + x ^ 3 * i13Psi4N3 x +
    x ^ 4 * i13Psi4N4 x) / x ^ 2 + i13Psi4W x

/-- The derivative of `Ψ₄`. -/
noncomputable def i13Psi4D (x : ℝ) : ℝ :=
  ((i13Psi4dN0 x + (i13Psi4N1 x + x * i13Psi4dN1 x) +
      (2 * x * i13Psi4N2 x + x ^ 2 * i13Psi4dN2 x) +
      (3 * x ^ 2 * i13Psi4N3 x + x ^ 3 * i13Psi4dN3 x) +
      (4 * x ^ 3 * i13Psi4N4 x + x ^ 4 * i13Psi4dN4 x)) * x ^ 2 -
    (i13Psi4N0 x + x * i13Psi4N1 x + x ^ 2 * i13Psi4N2 x + x ^ 3 * i13Psi4N3 x +
      x ^ 4 * i13Psi4N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i13Psi4dW x

theorem hasDerivAt_i13Psi4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi4 (i13Psi4D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i13Psi4N0 hx).add (X.mul (hasDerivAt_i13Psi4N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i13Psi4N2 hx))).add ((X.pow 3).mul (hasDerivAt_i13Psi4N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i13Psi4N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i13Psi4W hx)
  unfold i13Psi4
  refine e.congr_deriv ?_
  unfold i13Psi4D
  simp only [Pi.pow_apply]
  norm_num

/-- `p₄` in the variable `ξ`. -/
noncomputable def i13P4x (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * ((1 + x) / (1 - x) * (i13PB4 x - i13P4c)) +
    2 * (2 + Real.log x * (1 + x) / (1 - x)) * i13Be3x x + i13Be2x x ^ 2 -
    (2 * Real.log (1 - x) - Real.log x) *
      (2 * i13Be3x x + 2 * (2 + Real.log x * (1 + x) / (1 - x)) * i13Be2x x) +
    (2 * Real.log (1 - x) - Real.log x) ^ 2 *
      (i13Be2x x + (2 + Real.log x * (1 + x) / (1 - x)) ^ 2 / 2) -
    (2 * Real.log (1 - x) - Real.log x) ^ 3 * (2 + Real.log x * (1 + x) / (1 - x)) / 3 +
    (2 * Real.log (1 - x) - Real.log x) ^ 4 / 24)

theorem i13P4_eq {t : ℝ} (ht : 0 < t) : i13P4 t = i13P4x (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i13_log_eq_xi ht).symm
  unfold i13P4 i13P4x i13Be4r i13Be1r
  rw [i13Be2r_eq, i13Be3r_eq, hT, hlog]

end QED.ThreeLoopD
