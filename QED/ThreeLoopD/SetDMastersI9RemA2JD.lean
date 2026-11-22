/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2Th
public import QED.Polylog.HPLLowWeight
public import QED.Polylog.HPLShuffle

/-!
# Set (d), master `I₉`: an antiderivative of the one-dimensional `A₂'` integrand

`QED.ThreeLoopD.integrableOn_and_integral_i9A2j` reduces the `Dens'` part of `∫ F₂` to
`∫₀¹ j`. In the variable `x = 1 - p` the integrand `j(1 - x)` is a combination of harmonic
polylogarithms `H(w; x)` over `{0, 1}` with rational coefficients having poles at `x = 0` of
order up to three, and it has the antiderivative

  `Ψ = A + B/x + C/x²`,

`A`, `B`, `C` explicit constant-coefficient combinations of `H(w; x)` of weight at most four.
The check `Ψ' = j(1 - x)` reduces every word to the products of `log x`, `log (1 - x)`,
`Li₂ x`, `Li₃ x`, `H(0, 1, 1)`, `H(0, 0, 1, 1)` and `H(0, 1, 1, 1)` (the weight-four words by
shuffle products, `QED.ThreeLoopD.hpl_w0110` and its companions).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i9A2Psi`: `Ψ'(x) = j(1 - x)` on `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part `A` of the antiderivative. -/
noncomputable def i9A2PsiA (x : ℝ) : ℝ :=
  (-π ^ 2) * hpl [zero] x +
    (-π ^ 2) * hpl [one] x +
    (27 - 2 * π ^ 2) * hpl [zero, one] x +
    (27 - 2 * π ^ 2) * hpl [one, one] x +
    (-12) * hpl [zero, zero, one] x +
    (-18) * hpl [zero, one, zero] x +
    (21) * hpl [zero, one, one] x +
    (-12) * hpl [one, zero, one] x +
    (-18) * hpl [one, one, zero] x +
    (21) * hpl [one, one, one] x +
    (12) * hpl [zero, zero, one, one] x +
    (-6) * hpl [zero, one, zero, one] x +
    (-18) * hpl [zero, one, one, zero] x +
    (12) * hpl [zero, one, one, one] x +
    (12) * hpl [one, zero, one, one] x +
    (-6) * hpl [one, one, zero, one] x +
    (-18) * hpl [one, one, one, zero] x +
    (12) * hpl [one, one, one, one] x

/-- The part `B` of the antiderivative. -/
noncomputable def i9A2PsiB (x : ℝ) : ℝ :=
  (2 * π ^ 2) * hpl [one] x +
    (3 * π ^ 2) * hpl [zero, one] x +
    (π ^ 2) * hpl [one, zero] x +
    (-27 + 4 * π ^ 2) * hpl [one, one] x +
    (-12) * hpl [zero, one, one] x +
    (6) * hpl [one, zero, one] x +
    (18) * hpl [one, one, zero] x +
    (-12) * hpl [one, one, one] x +
    (-24) * hpl [zero, zero, one, one] x +
    (24) * hpl [zero, one, one, zero] x +
    (-36) * hpl [zero, one, one, one] x +
    (12) * hpl [one, zero, zero, one] x +
    (12) * hpl [one, zero, one, zero] x +
    (-12) * hpl [one, zero, one, one] x +
    (12) * hpl [one, one, zero, one] x +
    (36) * hpl [one, one, one, zero] x +
    (-24) * hpl [one, one, one, one] x

/-- The part `C` of the antiderivative. -/
noncomputable def i9A2PsiC (x : ℝ) : ℝ :=
  (-9) * hpl [one, one, one] x +
    (-12) * hpl [one, zero, one, one] x +
    (-18) * hpl [one, one, zero, one] x +
    (-18) * hpl [one, one, one, zero] x +
    (12) * hpl [one, one, one, one] x

theorem hasDerivAt_i9A2PsiA {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9A2PsiA ((-π ^ 2) * (zero.kernel x * hpl [] x) +
      (-π ^ 2) * (one.kernel x * hpl [] x) +
      (27 - 2 * π ^ 2) * (zero.kernel x * hpl [one] x) +
      (27 - 2 * π ^ 2) * (one.kernel x * hpl [one] x) +
      (-12) * (zero.kernel x * hpl [zero, one] x) +
      (-18) * (zero.kernel x * hpl [one, zero] x) +
      (21) * (zero.kernel x * hpl [one, one] x) +
      (-12) * (one.kernel x * hpl [zero, one] x) +
      (-18) * (one.kernel x * hpl [one, zero] x) +
      (21) * (one.kernel x * hpl [one, one] x) +
      (12) * (zero.kernel x * hpl [zero, one, one] x) +
      (-6) * (zero.kernel x * hpl [one, zero, one] x) +
      (-18) * (zero.kernel x * hpl [one, one, zero] x) +
      (12) * (zero.kernel x * hpl [one, one, one] x) +
      (12) * (one.kernel x * hpl [zero, one, one] x) +
      (-6) * (one.kernel x * hpl [one, zero, one] x) +
      (-18) * (one.kernel x * hpl [one, one, zero] x) +
      (12) * (one.kernel x * hpl [one, one, one] x)) x := by
  unfold i9A2PsiA
  exact ((((((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (27 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (27 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (21))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (21))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (12))

theorem hasDerivAt_i9A2PsiB {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9A2PsiB ((2 * π ^ 2) * (one.kernel x * hpl [] x) +
      (3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
      (π ^ 2) * (one.kernel x * hpl [zero] x) +
      (-27 + 4 * π ^ 2) * (one.kernel x * hpl [one] x) +
      (-12) * (zero.kernel x * hpl [one, one] x) +
      (6) * (one.kernel x * hpl [zero, one] x) +
      (18) * (one.kernel x * hpl [one, zero] x) +
      (-12) * (one.kernel x * hpl [one, one] x) +
      (-24) * (zero.kernel x * hpl [zero, one, one] x) +
      (24) * (zero.kernel x * hpl [one, one, zero] x) +
      (-36) * (zero.kernel x * hpl [one, one, one] x) +
      (12) * (one.kernel x * hpl [zero, zero, one] x) +
      (12) * (one.kernel x * hpl [zero, one, zero] x) +
      (-12) * (one.kernel x * hpl [zero, one, one] x) +
      (12) * (one.kernel x * hpl [one, zero, one] x) +
      (36) * (one.kernel x * hpl [one, one, zero] x) +
      (-24) * (one.kernel x * hpl [one, one, one] x)) x := by
  unfold i9A2PsiB
  exact (((((((((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (π ^ 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-27 + 4 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (-24))

theorem hasDerivAt_i9A2PsiC {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9A2PsiC ((-9) * (one.kernel x * hpl [one, one] x) +
      (-12) * (one.kernel x * hpl [zero, one, one] x) +
      (-18) * (one.kernel x * hpl [one, zero, one] x) +
      (-18) * (one.kernel x * hpl [one, one, zero] x) +
      (12) * (one.kernel x * hpl [one, one, one] x)) x := by
  unfold i9A2PsiC
  exact (((((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-9)).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (12))

/-! ### Shuffle reductions of the weight-four words -/

section Words

variable {x : ℝ}

theorem hpl_w0101 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero, one] x =
      hpl [zero, one] x ^ 2 / 2 - 2 * hpl [zero, zero, one, one] x := by
  have h := hpl_mul_hpl [zero, one] [zero, one] hx
  simp [shuffle_cons_cons] at h
  linear_combination -(h / 2)

theorem hpl_w0110 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, one, zero] x =
      hpl [zero] x * hpl [zero, one, one] x - hpl [zero, one] x ^ 2 / 2 := by
  have h1 := hpl_mul_hpl [zero] [zero, one, one] hx
  have h2 := hpl_mul_hpl [zero, one] [zero, one] hx
  simp [shuffle_cons_cons] at h1 h2
  linear_combination -(h1 - h2 / 2)

theorem hpl_w1001 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, zero, one] x =
      hpl [one] x * hpl [one, zero, zero] x - hpl [one, zero] x ^ 2 / 2 := by
  have h1 := hpl_mul_hpl [one] [one, zero, zero] hx
  have h2 := hpl_mul_hpl [one, zero] [one, zero] hx
  simp [shuffle_cons_cons] at h1 h2
  linear_combination -(h1 - h2 / 2)

theorem hpl_w1010 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, one, zero] x =
      -2 * (hpl [zero] x * hpl [zero, one, one] x) + hpl [zero, one] x ^ 2 / 2 +
        hpl [zero, one, zero] x * hpl [one] x + 2 * hpl [zero, zero, one, one] x := by
  have h1 := hpl_mul_hpl [zero] [zero, one, one] hx
  have h2 := hpl_mul_hpl [zero, one] [zero, one] hx
  have h3 := hpl_mul_hpl [zero, one, zero] [one] hx
  simp [shuffle_cons_cons] at h1 h2 h3
  linear_combination -(-2 * h1 + h2 / 2 + h3)

theorem hpl_w1011 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, one, one] x =
      hpl [zero, one, one] x * hpl [one] x - 3 * hpl [zero, one, one, one] x := by
  have h := hpl_mul_hpl [zero, one, one] [one] hx
  simp [shuffle_cons_cons] at h
  linear_combination -(h)

theorem hpl_w1101 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, zero, one] x =
      hpl [one] x * hpl [one, zero, one] x - hpl [zero, one] x * hpl [one, one] x +
        3 * hpl [zero, one, one, one] x := by
  have h1 := hpl_mul_hpl [one] [one, zero, one] hx
  have h2 := hpl_mul_hpl [zero, one] [one, one] hx
  simp [shuffle_cons_cons] at h1 h2
  linear_combination -(h1 - h2)

theorem hpl_w1110 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, one, zero] x =
      hpl [zero] x * hpl [one, one, one] x - hpl [one] x * hpl [one, zero, one] x / 2 -
        hpl [zero, one, one, one] x := by
  have h1 := hpl_mul_hpl [zero] [one, one, one] hx
  have h2 := hpl_mul_hpl [one] [one, zero, one] hx
  simp [shuffle_cons_cons] at h1 h2
  linear_combination -(h1 - h2 / 2)

theorem hpl_w1111 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, one, one] x = hpl [one] x * hpl [one, one, one] x / 4 := by
  have h := hpl_mul_hpl [one] [one, one, one] hx
  simp [shuffle_cons_cons] at h
  linear_combination -(h / 4)

end Words


/-! ### The antiderivative -/

/-- **The antiderivative** `Ψ = A + B/x + C/x²` of `x ↦ j(1 - x)`. -/
noncomputable def i9A2Psi (x : ℝ) : ℝ := i9A2PsiA x + i9A2PsiB x / x + i9A2PsiC x / x ^ 2

/-- `logOneSubSqPrim x = 2 H(0, 1, 1; x) - 2 ζ(3)`. -/
theorem logOneSubSqPrim_eq_hpl {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    logOneSubSqPrim x = 2 * hpl [zero, one, one] x - 2 * zeta3 := by
  have h := eq_hpl_cons_of_hasDerivAt (a := zero) (w := [one, one]) (by decide)
    (F := fun y => (logOneSubSqPrim y + 2 * zeta3) / 2) (fun y hy => by
      have := ((hasDerivAt_logOneSubSqPrim hy).add_const (2 * zeta3)).div_const 2
      convert this using 1
      rw [kernel_zero, hpl_one_one hy]
      field_simp) (by
      have := (tendsto_logOneSubSqPrim_zero.add_const (2 * zeta3)).div_const 2
      convert this using 2
      ring) x hx
  rw [h]
  ring

/-- **`Ψ' (x) = j(1 - x)`** on `(0, 1)`. -/
theorem hasDerivAt_i9A2Psi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9A2Psi (i9A2j (1 - x)) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.2 hx.2.ne'
  have h := ((hasDerivAt_i9A2PsiA hx).add ((hasDerivAt_i9A2PsiB hx).div (hasDerivAt_id' x)
    hx0)).add ((hasDerivAt_i9A2PsiC hx).div ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx0))
  convert h using 1
  · funext y
    simp only [i9A2Psi, Pi.add_apply, Pi.div_apply, Pi.pow_apply]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  simp only [i9A2PsiB, i9A2PsiC, kernel_zero, kernel_one, hpl_nil, hpl_w0110 hx,
    hpl_w1001 hx, hpl_w1010 hx, hpl_w1011 hx, hpl_w1101 hx, hpl_w1110 hx, hpl_w1111 hx]
  simp only [hpl_one_zero_zero hx, hpl_one_zero_one hx, hpl_one_one_zero hx,
    hpl_one_one_one hx, hpl_zero_one_zero hx, hpl_zero_zero_one hx]
  simp only [hpl_one_zero hx, hpl_one_one hx, hpl_zero_one hx, hpl_one hx,
    hpl_zero, Li_two, Li_three]
  unfold i9A2j i9A1K i9A1g i9A2h i9A2Kb i9A2AL i9A2BL i9A2A2 i9A2B2
  simp only [sub_sub_cancel]
  rw [logOneSubSqPrim_eq_hpl hx]
  field_simp
  ring

end QED.ThreeLoopD
