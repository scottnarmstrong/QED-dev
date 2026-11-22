/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R4N

/-!
# Set (d), master `I₁₃`: the primitive `F₄` of `p₄`

`F₄(t) = Ψ₄(ξ(t))` (`QED.ThreeLoopD.i13F4`) is a primitive of `p₄` on `(0, ∞)`
(`QED.ThreeLoopD.hasDerivAt_i13F4`). The check `Ψ₄'(ξ) ξ'(t) = p₄(t)`
(`QED.ThreeLoopD.i13Psi4D_mul`) inserts the Lyndon forms of the parts of `Ψ₄` and of `ξ p₄`
(`QED.ThreeLoopD.SetDMastersI13R4N`), after which it is an identity of polynomials in `ξ` and the
Lyndon basis functions.

## Main results

* `QED.ThreeLoopD.i13Psi4D_mul`, `QED.ThreeLoopD.hasDerivAt_i13F4`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- **`Ψ₄'(ξ) ξ' = p₄`**, in terms of `ξ`. -/
theorem i13Psi4D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i13Psi4D x * (-x ^ 2 / (1 - x ^ 2)) = i13P4x x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hq : x * (1 - x) * (1 + x) ≠ 0 := mul_ne_zero (mul_ne_zero h0 h1) h2
  have eN0 := i13Psi4N0_eq hx
  have eD0 : i13Psi4dN0 x = (i13Q4B0a_0 x + i13Q4B0a_1 x + i13Q4B0b_0 x + i13Q4B0b_1 x +
      i13Q4B0c_0 x + i13Q4B0c_1 x) / (x * (1 - x) * (1 + x)) := by
    refine eq_div_of_mul_eq hq ?_
    unfold i13Psi4dN0
    linear_combination i13Psi4dN0a_eq hx + i13Psi4dN0b_eq hx + i13Psi4dN0c_eq hx
  have eN1 := i13Psi4N1_eq hx
  have eD1 : i13Psi4dN1 x = (i13Q4B1a_0 x + i13Q4B1a_1 x + i13Q4B1b_0 x + i13Q4B1b_1 x +
      i13Q4B1c_0 x) / (x * (1 - x) * (1 + x)) := by
    refine eq_div_of_mul_eq hq ?_
    unfold i13Psi4dN1
    linear_combination i13Psi4dN1a_eq hx + i13Psi4dN1b_eq hx + i13Psi4dN1c_eq hx
  have eN2 := i13Psi4N2_eq hx
  have eD2 : i13Psi4dN2 x = (i13Q4B2a_0 x + i13Q4B2a_1 x + i13Q4B2a_2 x + i13Q4B2b_0 x +
      i13Q4B2b_1 x) / (x * (1 - x) * (1 + x)) := by
    refine eq_div_of_mul_eq hq ?_
    unfold i13Psi4dN2
    linear_combination i13Psi4dN2a_eq hx + i13Psi4dN2b_eq hx
  have eN3 := i13Psi4N3_eq hx
  have eD3 : i13Psi4dN3 x = (i13Q4B3a_0 x + i13Q4B3a_1 x + i13Q4B3b_0 x + i13Q4B3b_1 x +
      i13Q4B3c_0 x) / (x * (1 - x) * (1 + x)) := by
    refine eq_div_of_mul_eq hq ?_
    unfold i13Psi4dN3
    linear_combination i13Psi4dN3a_eq hx + i13Psi4dN3b_eq hx + i13Psi4dN3c_eq hx
  have eN4 := i13Psi4N4_eq hx
  have eD4 : i13Psi4dN4 x = (i13Q4B4a_0 x + i13Q4B4a_1 x + i13Q4B4b_0 x + i13Q4B4b_1 x +
      i13Q4B4c_0 x + i13Q4B4c_1 x) / (x * (1 - x) * (1 + x)) := by
    refine eq_div_of_mul_eq hq ?_
    unfold i13Psi4dN4
    linear_combination i13Psi4dN4a_eq hx + i13Psi4dN4b_eq hx + i13Psi4dN4c_eq hx
  have eW : i13Psi4dW x = (i13Q4Ca_0 x + i13Q4Ca_1 x + i13Q4Ca_2 x + i13Q4Cb_0 x +
      i13Q4Cb_1 x + i13Q4Cb_2 x) / (x * (1 - x) * (1 + x)) := by
    refine eq_div_of_mul_eq hq ?_
    unfold i13Psi4dW
    linear_combination i13Psi4dWa_eq hx + i13Psi4dWb_eq hx
  have eE : i13P4x x = (i13Q4E0 x + i13Q4E1 x + i13Q4E2 x + i13Q4E3 x + i13Q4E4 x +
      i13Q4E5 x) / x :=
    eq_div_of_mul_eq h0 (by rw [mul_comm]; exact i13P4x_eq hx)
  unfold i13Psi4D
  rw [eN0, eN1, eN2, eN3, eN4, eD0, eD1, eD2, eD3, eD4, eW, eE]
  field_simp
  unfold i13Q4A0_0 i13Q4A0_1 i13Q4A0_2 i13Q4B0a_0 i13Q4B0a_1 i13Q4B0b_0 i13Q4B0b_1 i13Q4B0c_0
    i13Q4B0c_1 i13Q4A1_0 i13Q4A1_1 i13Q4B1a_0 i13Q4B1a_1 i13Q4B1b_0 i13Q4B1b_1 i13Q4B1c_0 i13Q4A2_0
    i13Q4A2_1 i13Q4B2a_0 i13Q4B2a_1 i13Q4B2a_2 i13Q4B2b_0 i13Q4B2b_1 i13Q4A3_0 i13Q4A3_1 i13Q4B3a_0
    i13Q4B3a_1 i13Q4B3b_0 i13Q4B3b_1 i13Q4B3c_0 i13Q4A4_0 i13Q4A4_1 i13Q4B4a_0 i13Q4B4a_1 i13Q4B4b_0
    i13Q4B4b_1 i13Q4B4c_0 i13Q4B4c_1 i13Q4Ca_0 i13Q4Ca_1 i13Q4Ca_2 i13Q4Cb_0 i13Q4Cb_1 i13Q4Cb_2
    i13Q4E0 i13Q4E1 i13Q4E2 i13Q4E3 i13Q4E4 i13Q4E5
  ring

/-! ### The primitive `F₄` -/

/-- `F₄(t) = Ψ₄(ξ(t))`. -/
noncomputable def i13F4 (t : ℝ) : ℝ := i13Psi4 (i13Xi t)

theorem hasDerivAt_i13F4 {t : ℝ} (ht : 0 < t) : HasDerivAt i13F4 (i13P4 t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have e := (hasDerivAt_i13Psi4 ⟨hx0, hx1⟩).comp t (hasDerivAt_i13Xi ht)
  rw [i13Psi4D_mul ⟨hx0, hx1⟩, ← i13P4_eq ht] at e
  exact e

end QED.ThreeLoopD
