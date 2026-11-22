/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
import QED.Polylog.Deriv
import QED.Polylog.LiCalculus
import QED.Polylog.LiN

/-!
# Set (d), master `I₁₂`: an antiderivative of the `u`-integrand of `T''`

With `a = log u`, `b = log (1 - u)`, `c = log (1 + u)`, `ℓ = log 2` and the four arguments

  `2u/(1+u)`, `(1-u)/(1+u)`, `1/(1+u)`, `(1+u)/2`   (all in `(0, 1)` for `u ∈ (0, 1)`),

the `u`-integrand of `(T_A''(0) + T_B''(0)) / 4` is the weight-three function
`QED.ThreeLoopD.i12T2Q` (logarithms, `Li₂` and `Li₃` of the first two arguments). The function
`QED.ThreeLoopD.i12T2G`, found by an ansatz over rational multiples of products of these
logarithms and polylogarithms, is an antiderivative on `(0, 1)`. All polylogarithm and logarithm
values are treated as independent atoms in the derivative check, so no functional equation is
needed.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12T2G`.
-/

@[expose] public section

open Real QED.Polylog Set

namespace QED.ThreeLoopD

/-- The `u`-integrand of `(T_A''(0) + T_B''(0)) / 4`. -/
noncomputable def i12T2Q (u : ℝ) : ℝ :=
    log u ^ 3 - 6 * log u ^ 2 * log (1 - u) + 6 * log u ^ 2 * log (1 + u) + 3 * log u ^ 2 * log 2 +
    9 * log u ^ 2 / 2 + 6 * log u * log (1 - u) * log (1 + u) - 12 * log u * log (1 - u) *
    log 2 - 9 * log u * log (1 + u) ^ 2 + 12 * log u * log (1 + u) * log 2 - 9 *
    log u * log (1 + u) + 3 * log u * log 2 ^ 2 + 9 * log u * log 2 + log u * π ^ 2 - 6 *
    log u * Li₂ (2 * u / (1 + u)) - 6 * log u * Li₂ ((1 - u) / (1 + u)) - 6 * log u * u / (1 - u) +
    6 * Li₃ (2 * u / (1 + u)) + 6 * Li₃ ((1 - u) / (1 + u)) + log (1 - u) ^ 3 + 9 *
    log (1 - u) ^ 2 / 2 - 3 * log (1 - u) * log (1 + u) ^ 2 + 6 * log (1 - u) *
    log (1 + u) * log 2 - 9 * log (1 - u) * log (1 + u) - 6 * log (1 - u) * log 2 ^ 2 +
    3 * log (1 - u) / 2 - 3 * log (1 - u) / (2 * u) + 4 * log (1 + u) ^ 3 - 9 *
    log (1 + u) ^ 2 * log 2 + 9 * log (1 + u) ^ 2 + 6 * log (1 + u) * log 2 ^ 2 - 9 * log (1 + u) *
    log 2 + 6 * log (1 + u) * Li₂ (2 * u / (1 + u)) + 6 * log (1 + u) *
    Li₂ ((1 - u) / (1 + u)) + 6 * log (1 + u) * u / (1 - u) + 9 * log (1 + u) / 2 +
    3 * log (1 + u) / (2 * u) + log 2 ^ 3 + 9 * log 2 ^ 2 / 2 + log 2 * π ^ 2 - 6 *
    log 2 * Li₂ (2 * u / (1 + u)) - 6 * log 2 * Li₂ ((1 - u) / (1 + u)) - 6 * log 2 * u / (1 - u) +
    12 * zeta3 + 9 * Li₂ (2 * u / (1 + u)) + 9 * Li₂ ((1 - u) / (1 + u)) - 12

/-- An antiderivative of `QED.ThreeLoopD.i12T2Q` on `(0, 1)`. -/
noncomputable def i12T2G (u : ℝ) : ℝ :=
    (u * (2 * log 2 ^ 3 + 3 * log 2 ^ 2 + 2 * log 2 * π ^ 2 + 12 * log 2 - 2 * π ^ 2 + 24 * zeta3 -
    36) / 2) - 6 * Li₃ ((1 + u) / 2) + 6 * Li₃ (1 / (1 + u)) + (6 * (u -
    1)) * Li₃ ((1 - u) / (1 + u)) + (6 * u) * Li₃ (2 * u / (1 + u)) + 9 / 2 * Li₂ ((1 + u) / 2) +
    9 * Li₂ (1 / (1 + u)) + (-3 * (2 * log 2 - 3) * (u + 1)) * Li₂ ((1 - u) / (1 + u)) +
    (-6 * log 2 * u - 6 * log 2 + 9 * u + 39 / 2) * Li₂ (2 * u / (1 + u)) + (6 * log 2 ^ 2 * u + 6 *
    log 2 ^ 2 - 9 * log 2 * u - 27 * log 2 / 2 - 3 * u / 2 - 3 / 2) * log (1 + u) +
    6 * log (1 + u) * Li₂ ((1 + u) / 2) + 6 * log (1 + u) * Li₂ (1 / (1 + u)) + (6 * (u - 1)) *
    log (1 + u) * Li₂ ((1 - u) / (1 + u)) + (6 * u) * log (1 + u) * Li₂ (2 * u / (1 + u)) +
    (-9 * log 2 * u - 6 * log 2 + 9 * u + 75 / 4) * log (1 + u) ^ 2 + (4 * u) *
    log (1 + u) ^ 3 + (-6 * log 2 ^ 2 * u - 6 * log 2 ^ 2 + 6 * log 2 * u + 18 * log 2 + 3 * u / 2 -
    3 / 2) * log (1 - u) + (6 * log 2 * u + 6 * log 2 - 9 * u - 15) * log (1 - u) *
    log (1 + u) + (-3 * (u - 1)) * log (1 - u) * log (1 + u) ^ 2 + (3 * (u - 1) / 2) *
    log (1 - u) ^ 2 + (u - 1) * log (1 - u) ^ 3 + (u * (3 * log 2 ^ 2 + 3 * log 2 + π ^ 2 +
    6)) * log u + (-6 * u) * log u * Li₂ ((1 - u) / (1 + u)) + (-6 * u) *
    log u * Li₂ (2 * u / (1 + u)) + (12 * log 2 * u + 6 * log 2 - 9 * u - 18) *
    log u * log (1 + u) + (-9 * u) * log u * log (1 + u) ^ 2 + (-12 * log 2 * u - 6 * log 2 +
    6 * u + 18) * log u * log (1 - u) + (6 * u) * log u * log (1 - u) * log (1 + u) + (3 * u * (2 *
    log 2 + 1) / 2) * log u ^ 2 + (6 * u) * log u ^ 2 * log (1 + u) + (-6 * u) *
    log u ^ 2 * log (1 - u) + u * log u ^ 3

theorem hasDerivAt_i12T2G {u : ℝ} (hu' : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12T2G (i12T2Q u) u := by
  obtain ⟨hu0, hu1⟩ := hu'
  have h1m : 0 < 1 - u := by linarith
  have h1p : 0 < 1 + u := by linarith
  have hu : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id' u
  have ha : HasDerivAt (fun x : ℝ => log x) u⁻¹ u := hasDerivAt_log hu0.ne'
  have hb : HasDerivAt (fun x : ℝ => log (1 - x)) (-1 / (1 - u)) u :=
    ((hasDerivAt_id' u).const_sub 1).log h1m.ne'
  have hc : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u :=
    ((hasDerivAt_id' u).const_add 1).log h1p.ne'
  have hfF : HasDerivAt (fun x : ℝ => 2 * x / (1 + x)) (2 / (1 + u) ^ 2) u := by
    refine (((hasDerivAt_id' u).const_mul 2).div ((hasDerivAt_id' u).const_add 1)
      h1p.ne').congr_deriv ?_
    field_simp
    ring
  have hfG : HasDerivAt (fun x : ℝ => (1 - x) / (1 + x)) (-2 / (1 + u) ^ 2) u := by
    refine (((hasDerivAt_id' u).const_sub 1).div ((hasDerivAt_id' u).const_add 1)
      h1p.ne').congr_deriv ?_
    field_simp
    ring
  have hfI : HasDerivAt (fun x : ℝ => 1 / (1 + x)) (-1 / (1 + u) ^ 2) u := by
    have := ((hasDerivAt_id' u).const_add 1).inv h1p.ne'
    simp only [one_div]
    refine this.congr_deriv ?_
    field_simp
  have hfP : HasDerivAt (fun x : ℝ => (1 + x) / 2) (1 / 2) u := by
    simpa using ((hasDerivAt_id' u).const_add 1).div_const 2
  have mF : 0 < 2 * u / (1 + u) ∧ 2 * u / (1 + u) < 1 :=
    ⟨by positivity, (div_lt_one h1p).2 (by linarith)⟩
  have mG : 0 < (1 - u) / (1 + u) ∧ (1 - u) / (1 + u) < 1 :=
    ⟨by positivity, (div_lt_one h1p).2 (by linarith)⟩
  have mI : 0 < 1 / (1 + u) ∧ 1 / (1 + u) < 1 :=
    ⟨by positivity, (div_lt_one h1p).2 (by linarith)⟩
  have mP : 0 < (1 + u) / 2 ∧ (1 + u) / 2 < 1 := ⟨by positivity, by linarith⟩
  have aF : |2 * u / (1 + u)| < 1 := by rw [abs_of_pos mF.1]; exact mF.2
  have aG : |(1 - u) / (1 + u)| < 1 := by rw [abs_of_pos mG.1]; exact mG.2
  have aI : |1 / (1 + u)| < 1 := by rw [abs_of_pos mI.1]; exact mI.2
  have aP : |(1 + u) / 2| < 1 := by rw [abs_of_pos mP.1]; exact mP.2
  have dF : 2 / (1 + u) ^ 2 / (2 * u / (1 + u)) = 1 / (u * (1 + u)) := by field_simp
  have dG : -2 / (1 + u) ^ 2 / ((1 - u) / (1 + u)) = -2 / ((1 - u) * (1 + u)) := by
    field_simp
  have dI : -1 / (1 + u) ^ 2 / (1 / (1 + u)) = -1 / (1 + u) := by field_simp
  have dP : 1 / 2 / ((1 + u) / 2) = 1 / (1 + u) := by field_simp
  have lF : log (1 - 2 * u / (1 + u)) = log (1 - u) - log (1 + u) := by
    rw [show 1 - 2 * u / (1 + u) = (1 - u) / (1 + u) by field_simp; ring]
    exact log_div h1m.ne' h1p.ne'
  have lG : log (1 - (1 - u) / (1 + u)) = log 2 + log u - log (1 + u) := by
    rw [show 1 - (1 - u) / (1 + u) = 2 * u / (1 + u) by field_simp; ring,
      log_div (by positivity) h1p.ne', log_mul (by norm_num) hu0.ne']
  have lI : log (1 - 1 / (1 + u)) = log u - log (1 + u) := by
    rw [show 1 - 1 / (1 + u) = u / (1 + u) by field_simp; ring]
    exact log_div hu0.ne' h1p.ne'
  have lP : log (1 - (1 + u) / 2) = log (1 - u) - log 2 := by
    rw [show 1 - (1 + u) / 2 = (1 - u) / 2 by ring]
    exact log_div h1m.ne' (by norm_num)
  have hF2 := hasDerivAt_Li_two_of hfF aF mF.1.ne' dF lF
  have hG2 := hasDerivAt_Li_two_of hfG aG mG.1.ne' dG lG
  have hI2 := hasDerivAt_Li_two_of hfI aI mI.1.ne' dI lI
  have hP2 := hasDerivAt_Li_two_of hfP aP mP.1.ne' dP lP
  have hF3 := hasDerivAt_Li_three_of hfF aF mF.1.ne' dF rfl
  have hG3 := hasDerivAt_Li_three_of hfG aG mG.1.ne' dG rfl
  have hI3 := hasDerivAt_Li_three_of hfI aI mI.1.ne' dI rfl
  have hP3 := hasDerivAt_Li_three_of hfP aP mP.1.ne' dP rfl
  simp only [Li_two, Li_three] at hF2 hG2 hI2 hP2 hF3 hG3 hI3 hP3
  have h := (((((((((((((((((((((((((((((((((((((((((((((((hu.mul ha).mul ha).mul ha).add
      ((((hu.mul ha).mul ha).mul hb).const_mul (-6))).add
      ((((hu.mul ha).mul ha).mul hc).const_mul (6))).add
      (((hu.mul ha).mul ha).const_mul (3*log 2 + 3/2))).add
      ((((hu.mul ha).mul hb).mul hc).const_mul (6))).add
      (((hu.mul ha).mul hb).const_mul (6 - 12*log 2))).add
      ((((hu.mul ha).mul hc).mul hc).const_mul (-9))).add
      (((hu.mul ha).mul hc).const_mul (12*log 2 - 9))).add
      (((hu.mul ha).mul hF2).const_mul (-6))).add
      (((hu.mul ha).mul hG2).const_mul (-6))).add
      ((hu.mul ha).const_mul (3*log 2 ^ 2 + 3*log 2 + π ^ 2 + 6))).add
      (((hu.mul hb).mul hb).mul hb)).add
      (((hu.mul hb).mul hb).const_mul (3/2))).add
      ((((hu.mul hb).mul hc).mul hc).const_mul (-3))).add
      (((hu.mul hb).mul hc).const_mul (6*log 2 - 9))).add
      ((hu.mul hb).const_mul (-6*log 2 ^ 2 + 6*log 2 + 3/2))).add
      ((((hu.mul hc).mul hc).mul hc).const_mul (4))).add
      (((hu.mul hc).mul hc).const_mul (9 - 9*log 2))).add
      (((hu.mul hc).mul hF2).const_mul (6))).add
      (((hu.mul hc).mul hG2).const_mul (6))).add
      ((hu.mul hc).const_mul (6*log 2 ^ 2 - 9*log 2 - 3/2))).add
      ((hu.mul hF2).const_mul (9 - 6*log 2))).add
      ((hu.mul hG2).const_mul (9 - 6*log 2))).add
      ((hu.mul hF3).const_mul (6))).add
      ((hu.mul hG3).const_mul (6))).add
      (hu.const_mul (log 2 ^ 3 + 3*log 2 ^ 2/2 + log 2*π ^ 2 + 6*log 2 - π ^ 2 + 12*zeta3 -
        18))).add
      ((ha.mul hb).const_mul (18 - 6*log 2))).add
      ((ha.mul hc).const_mul (6*log 2 - 18))).add
      (((hb.mul hb).mul hb).const_mul (-1))).add
      ((hb.mul hb).const_mul (-3/2))).add
      (((hb.mul hc).mul hc).const_mul (3))).add
      ((hb.mul hc).const_mul (6*log 2 - 15))).add
      (hb.const_mul (-6*log 2 ^ 2 + 18*log 2 - 3/2))).add
      ((hc.mul hc).const_mul (75/4 - 6*log 2))).add
      ((hc.mul hG2).const_mul (-6))).add
      ((hc.mul hI2).const_mul (6))).add
      ((hc.mul hP2).const_mul (6))).add
      (hc.const_mul (6*log 2 ^ 2 - 27*log 2/2 - 3/2))).add
      (hF2.const_mul (39/2 - 6*log 2))).add
      (hG2.const_mul (9 - 6*log 2))).add
      (hI2.const_mul (9))).add
      (hP2.const_mul (9/2))).add
      (hG3.const_mul (-6))).add
      (hI3.const_mul (6))).add
      (hP3.const_mul (-6)))
  convert h using 1
  · funext x
    simp only [i12T2G, Pi.mul_apply, Pi.add_apply]
    ring
  simp only [i12T2Q, Pi.mul_apply]
  generalize log u = a
  generalize log (1 - u) = b
  generalize log (1 + u) = c
  generalize log 2 = l2
  generalize Li₂ (2 * u / (1 + u)) = F2
  generalize Li₂ ((1 - u) / (1 + u)) = G2
  generalize Li₂ (1 / (1 + u)) = I2
  generalize Li₂ ((1 + u) / 2) = P2
  have := h1m.ne'
  field_simp
  ring

end QED.ThreeLoopD
