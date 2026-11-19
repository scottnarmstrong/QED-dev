/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairDisp

/-!
# Set (c), Stage K: a pointwise bound on the discontinuity of the pair integrand

Helper level (no frozen statement). For `x ∈ (0, 1)` and `v > 0`,

`|σ_x(v)| (1 - x)(1 + v) ≤ 3 (1 + log(1 + p/v))`, `p = x/(1 - x)` (`abs_dispSig_le`).

The rational parts are bounded region by region (`v ≤ x`, `x < v ≤ p`, `v > p`) in the variables
`y = p`, `a ≥ 0` (`pairBdP1`–`pairBdP5`), where after clearing denominators every bound is a
polynomial with nonnegative coefficients. For `v > p` the decay comes from the Taylor bound
`|log(1 + r) - r + r²/2| ≤ r³/3` (`abs_log_taylor_le`).
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set

section

variable {x v y a r : ℝ}

theorem pairBdP1 (hy : 0 < y) (ha : 0 ≤ a)
    (hx : x = y / (1 + y)) (hv : v = y/((a + 1)*(y + 1))) :
    |-(pairAl x (-v))| *
      ((1 - x) * (1 + v)) ≤ 2 := by
  have h1 : (1 : ℝ) + y ≠ 0 := by positivity
  have h2 : (1 : ℝ) + a ≠ 0 := by positivity
  have h3 : y + 1 ≠ 0 := by positivity
  have h4 : a + 1 ≠ 0 := by positivity
  have hd : 0 < 12*(a + 1)^3*(y + 1)^4*(a*y + a + y + 2)^2 := by positivity
  have hpos : 0 ≤ (1 - x) * (1 + v) := by
    have : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have : 0 ≤ v := by rw [hv]; positivity
    nlinarith
  have e : (-(pairAl x (-v))) * ((1 - x) * (1 + v)) =
      (
        3*a^5*y^6 + 27*a^5*y^5 + 114*a^5*y^4 + 213*a^5*y^3 + 153*a^5*y^2 + 6*a^5*y -
        24*a^5 + 16*a^4*y^6 + 155*a^4*y^5 + 692*a^4*y^4 + 1376*a^4*y^3 + 1067*a^4*y^2 +
        104*a^4*y - 140*a^4 + 32*a^3*y^6 + 343*a^3*y^5 + 1645*a^3*y^4 + 3527*a^3*y^3 +
        2941*a^3*y^2 + 412*a^3*y - 318*a^3 + 30*a^2*y^6 + 364*a^2*y^5 + 1907*a^2*y^4 +
        4454*a^2*y^3 + 4017*a^2*y^2 + 678*a^2*y - 350*a^2 + 13*a*y^6 + 184*a*y^5 +
        1073*a*y^4 + 2757*a*y^3 + 2712*a*y^2 + 509*a*y - 186*a + 2*y^6 + 35*y^5 +
        233*y^4 + 666*y^3 + 721*y^2 + 145*y - 38) /
        (12*(a + 1)^3*(y + 1)^4*(a*y + a + y + 2)^2) := by
    unfold pairAl
    have hden : x - -v + -v * x = y*(a*y + a + y + 2)/((a + 1)*(y + 1)^2) := by
      subst hx hv; field_simp; ring
    rw [hden]
    subst hx hv
    field_simp
    ring
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_le, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor
  · have : 0 ≤ (
        3*a^5*y^6 + 27*a^5*y^5 + 114*a^5*y^4 + 213*a^5*y^3 + 153*a^5*y^2 + 6*a^5*y -
        24*a^5 + 16*a^4*y^6 + 155*a^4*y^5 + 692*a^4*y^4 + 1376*a^4*y^3 + 1067*a^4*y^2 +
        104*a^4*y - 140*a^4 + 32*a^3*y^6 + 343*a^3*y^5 + 1645*a^3*y^4 + 3527*a^3*y^3 +
        2941*a^3*y^2 + 412*a^3*y - 318*a^3 + 30*a^2*y^6 + 364*a^2*y^5 + 1907*a^2*y^4 +
        4454*a^2*y^3 + 4017*a^2*y^2 + 678*a^2*y - 350*a^2 + 13*a*y^6 + 184*a*y^5 +
        1073*a*y^4 + 2757*a*y^3 + 2712*a*y^2 + 509*a*y - 186*a + 2*y^6 + 35*y^5 +
        233*y^4 + 666*y^3 + 721*y^2 + 145*y - 38) +
        2 * (12*(a + 1)^3*(y + 1)^4*(a*y + a + y + 2)^2) := by
      ring_nf; positivity
    linarith
  · have : 0 ≤ 2 * (12*(a + 1)^3*(y + 1)^4*(a*y + a + y + 2)^2) -
        (
        3*a^5*y^6 + 27*a^5*y^5 + 114*a^5*y^4 + 213*a^5*y^3 + 153*a^5*y^2 + 6*a^5*y -
        24*a^5 + 16*a^4*y^6 + 155*a^4*y^5 + 692*a^4*y^4 + 1376*a^4*y^3 + 1067*a^4*y^2 +
        104*a^4*y - 140*a^4 + 32*a^3*y^6 + 343*a^3*y^5 + 1645*a^3*y^4 + 3527*a^3*y^3 +
        2941*a^3*y^2 + 412*a^3*y - 318*a^3 + 30*a^2*y^6 + 364*a^2*y^5 + 1907*a^2*y^4 +
        4454*a^2*y^3 + 4017*a^2*y^2 + 678*a^2*y - 350*a^2 + 13*a*y^6 + 184*a*y^5 +
        1073*a*y^4 + 2757*a*y^3 + 2712*a*y^2 + 509*a*y - 186*a + 2*y^6 + 35*y^5 +
        233*y^4 + 666*y^3 + 721*y^2 + 145*y - 38) := by
      ring_nf; positivity
    linarith

theorem pairBdP2 (hy : 0 < y) (ha : 0 ≤ a)
    (hx : x = y / (1 + y)) (hv : v = y^2/((a + 1)*(y + 1)) + y/(y + 1)) :
    |-(pairAl x (-v) + pairBe x (-v))| *
      ((1 - x) * (1 + v)) ≤ 2 := by
  have h1 : (1 : ℝ) + y ≠ 0 := by positivity
  have h2 : (1 : ℝ) + a ≠ 0 := by positivity
  have h3 : y + 1 ≠ 0 := by positivity
  have h4 : a + 1 ≠ 0 := by positivity
  have hd : 0 < 12*(a + 1)*(y + 1)^4*(a + y + 1)^2*(a*y + 2*a + 2*y + 2)^2 := by positivity
  have hpos : 0 ≤ (1 - x) * (1 + v) := by
    have : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have : 0 ≤ v := by rw [hv]; positivity
    nlinarith
  have e : (-(pairAl x (-v) + pairBe x (-v))) * ((1 - x) * (1 + v)) =
      (
        2*a^5*y^6 + 35*a^5*y^5 + 233*a^5*y^4 + 666*a^5*y^3 + 721*a^5*y^2 + 145*a^5*y -
        38*a^5 + a^4*y^7 + 71*a^4*y^6 + 733*a^4*y^5 + 3070*a^4*y^4 + 5665*a^4*y^3 +
        4111*a^4*y^2 + 645*a^4*y - 190*a^4 + 26*a^3*y^7 + 644*a^3*y^6 + 4399*a^3*y^5 +
        12674*a^3*y^4 + 16561*a^3*y^3 + 9178*a^3*y^2 + 1130*a^3*y - 380*a^3 +
        155*a^2*y^7 + 2272*a^2*y^6 + 10694*a^2*y^5 + 22190*a^2*y^4 + 22341*a^2*y^3 +
        10078*a^2*y^2 + 970*a^2*y - 380*a^2 + 352*a*y^7 + 3332*a*y^6 + 10990*a*y^5 +
        17473*a*y^4 + 14329*a*y^3 + 5461*a*y^2 + 405*a*y - 190*a + 276*y^7 +
        1635*y^6 + 3997*y^5 + 5120*y^4 + 3550*y^3 + 1171*y^2 + 65*y - 38) /
        (12*(a + 1)*(y + 1)^4*(a + y + 1)^2*(a*y + 2*a + 2*y + 2)^2) := by
    unfold pairAl pairBe
    have hden : x - -v + -v * x = y*(a*y + 2*a + 2*y + 2)/((a + 1)*(y + 1)^2) := by
      subst hx hv; field_simp; ring
    rw [hden]
    subst hx hv
    field_simp
    ring
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_le, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor
  · have : 0 ≤ (
        2*a^5*y^6 + 35*a^5*y^5 + 233*a^5*y^4 + 666*a^5*y^3 + 721*a^5*y^2 + 145*a^5*y -
        38*a^5 + a^4*y^7 + 71*a^4*y^6 + 733*a^4*y^5 + 3070*a^4*y^4 + 5665*a^4*y^3 +
        4111*a^4*y^2 + 645*a^4*y - 190*a^4 + 26*a^3*y^7 + 644*a^3*y^6 + 4399*a^3*y^5 +
        12674*a^3*y^4 + 16561*a^3*y^3 + 9178*a^3*y^2 + 1130*a^3*y - 380*a^3 +
        155*a^2*y^7 + 2272*a^2*y^6 + 10694*a^2*y^5 + 22190*a^2*y^4 + 22341*a^2*y^3 +
        10078*a^2*y^2 + 970*a^2*y - 380*a^2 + 352*a*y^7 + 3332*a*y^6 + 10990*a*y^5 +
        17473*a*y^4 + 14329*a*y^3 + 5461*a*y^2 + 405*a*y - 190*a + 276*y^7 +
        1635*y^6 + 3997*y^5 + 5120*y^4 + 3550*y^3 + 1171*y^2 + 65*y - 38) +
        2 * (12*(a + 1)*(y + 1)^4*(a + y + 1)^2*(a*y + 2*a + 2*y + 2)^2) := by
      ring_nf; positivity
    linarith
  · have : 0 ≤ 2 * (12*(a + 1)*(y + 1)^4*(a + y + 1)^2*(a*y + 2*a + 2*y + 2)^2) -
        (
        2*a^5*y^6 + 35*a^5*y^5 + 233*a^5*y^4 + 666*a^5*y^3 + 721*a^5*y^2 + 145*a^5*y -
        38*a^5 + a^4*y^7 + 71*a^4*y^6 + 733*a^4*y^5 + 3070*a^4*y^4 + 5665*a^4*y^3 +
        4111*a^4*y^2 + 645*a^4*y - 190*a^4 + 26*a^3*y^7 + 644*a^3*y^6 + 4399*a^3*y^5 +
        12674*a^3*y^4 + 16561*a^3*y^3 + 9178*a^3*y^2 + 1130*a^3*y - 380*a^3 +
        155*a^2*y^7 + 2272*a^2*y^6 + 10694*a^2*y^5 + 22190*a^2*y^4 + 22341*a^2*y^3 +
        10078*a^2*y^2 + 970*a^2*y - 380*a^2 + 352*a*y^7 + 3332*a*y^6 + 10990*a*y^5 +
        17473*a*y^4 + 14329*a*y^3 + 5461*a*y^2 + 405*a*y - 190*a + 276*y^7 +
        1635*y^6 + 3997*y^5 + 5120*y^4 + 3550*y^3 + 1171*y^2 + 65*y - 38) := by
      ring_nf; positivity
    linarith

theorem pairBdP3 (hy : 0 < y) (ha : 0 ≤ a)
    (hx : x = y / (1 + y)) (hv : v = y*(a + 1)) :
    |-(pairAl x (-v) + pairBe x (-v) +
      pairGa x (-v) * (x / (1 - x) / v - (x / (1 - x) / v) ^ 2 / 2))| *
      ((1 - x) * (1 + v)) ≤ 2 := by
  have h1 : (1 : ℝ) + y ≠ 0 := by positivity
  have h2 : (1 : ℝ) + a ≠ 0 := by positivity
  have h3 : y + 1 ≠ 0 := by positivity
  have h4 : a + 1 ≠ 0 := by positivity
  have hd : 0 < 12*(a + 1)^2*(a + 2)^2*(y + 1)^4 := by positivity
  have hpos : 0 ≤ (1 - x) * (1 + v) := by
    have : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have : 0 ≤ v := by rw [hv]; positivity
    nlinarith
  have e : (-(pairAl x (-v) + pairBe x (-v) +
      pairGa x (-v) * (x / (1 - x) / v - (x / (1 - x) / v) ^ 2 / 2))) * ((1 - x) * (1 + v)) =
      (
        5*a^4*y^3 + 5*a^4*y^2 + 58*a^3*y^3 + 54*a^3*y^2 + 3*a^3*y + 193*a^2*y^3 +
        201*a^2*y^2 + 34*a^2*y - 2*a^2 + 248*a*y^3 + 319*a*y^2 + 82*a*y - 8*a +
        108*y^3 + 183*y^2 + 61*y - 14) /
        (12*(a + 1)^2*(a + 2)^2*(y + 1)^4) := by
    unfold pairAl pairBe pairGa
    have hden : x - -v + -v * x = y*(a + 2)/(y + 1) := by
      subst hx hv; field_simp; ring
    rw [hden]
    subst hx hv
    field_simp
    ring
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_le, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor
  · have : 0 ≤ (
        5*a^4*y^3 + 5*a^4*y^2 + 58*a^3*y^3 + 54*a^3*y^2 + 3*a^3*y + 193*a^2*y^3 +
        201*a^2*y^2 + 34*a^2*y - 2*a^2 + 248*a*y^3 + 319*a*y^2 + 82*a*y - 8*a +
        108*y^3 + 183*y^2 + 61*y - 14) +
        2 * (12*(a + 1)^2*(a + 2)^2*(y + 1)^4) := by
      ring_nf; positivity
    linarith
  · have : 0 ≤ 2 * (12*(a + 1)^2*(a + 2)^2*(y + 1)^4) -
        (
        5*a^4*y^3 + 5*a^4*y^2 + 58*a^3*y^3 + 54*a^3*y^2 + 3*a^3*y + 193*a^2*y^3 +
        201*a^2*y^2 + 34*a^2*y - 2*a^2 + 248*a*y^3 + 319*a*y^2 + 82*a*y - 8*a +
        108*y^3 + 183*y^2 + 61*y - 14) := by
      ring_nf; positivity
    linarith

theorem pairBdP4 (hy : 0 < y) (ha : 0 ≤ a)
    (hx : x = y / (1 + y)) (hv : v = y/(a + 1)) :
    |-(pairGa x (-v))| *
      ((1 - x) * (1 + v)) ≤ 3 := by
  have h1 : (1 : ℝ) + y ≠ 0 := by positivity
  have h2 : (1 : ℝ) + a ≠ 0 := by positivity
  have h3 : y + 1 ≠ 0 := by positivity
  have h4 : a + 1 ≠ 0 := by positivity
  have hd : 0 < 2*(a + 1)^2*(y + 1)^4 := by positivity
  have hpos : 0 ≤ (1 - x) * (1 + v) := by
    have : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have : 0 ≤ v := by rw [hv]; positivity
    nlinarith
  have e : (-(pairGa x (-v))) * ((1 - x) * (1 + v)) =
      (
        -5*a^2*y^2 - 6*a^2*y + 2*a^2 - 5*a*y^3 - 25*a*y^2 - 19*a*y + 4*a - 14*y^3 -
        29*y^2 - 13*y + 2) /
        (2*(a + 1)^2*(y + 1)^4) := by
    unfold pairGa
    subst hx hv
    field_simp
    ring
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_le, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor
  · have : 0 ≤ (
        -5*a^2*y^2 - 6*a^2*y + 2*a^2 - 5*a*y^3 - 25*a*y^2 - 19*a*y + 4*a - 14*y^3 -
        29*y^2 - 13*y + 2) +
        3 * (2*(a + 1)^2*(y + 1)^4) := by
      ring_nf; positivity
    linarith
  · have : 0 ≤ 3 * (2*(a + 1)^2*(y + 1)^4) -
        (
        -5*a^2*y^2 - 6*a^2*y + 2*a^2 - 5*a*y^3 - 25*a*y^2 - 19*a*y + 4*a - 14*y^3 -
        29*y^2 - 13*y + 2) := by
      ring_nf; positivity
    linarith

theorem pairBdP5 (hy : 0 < y) (ha : 0 ≤ a)
    (hx : x = y / (1 + y)) (hv : v = y*(a + 1)) :
    |-(pairGa x (-v) * (x / (1 - x) / v) ^ 3 / 3)| *
      ((1 - x) * (1 + v)) ≤ 1 := by
  have h1 : (1 : ℝ) + y ≠ 0 := by positivity
  have h2 : (1 : ℝ) + a ≠ 0 := by positivity
  have h3 : y + 1 ≠ 0 := by positivity
  have h4 : a + 1 ≠ 0 := by positivity
  have hd : 0 < 6*(a + 1)^3*(y + 1)^4 := by positivity
  have hpos : 0 ≤ (1 - x) * (1 + v) := by
    have : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have : 0 ≤ v := by rw [hv]; positivity
    nlinarith
  have e : (-(pairGa x (-v) * (x / (1 - x) / v) ^ 3 / 3)) * ((1 - x) * (1 + v)) =
      (
        -9*a^2*y^3 - 9*a^2*y^2 - 23*a*y^3 - 33*a*y^2 - 7*a*y - 14*y^3 - 29*y^2 -
        13*y + 2) /
        (6*(a + 1)^3*(y + 1)^4) := by
    unfold pairGa
    subst hx hv
    field_simp
    ring
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_le, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor
  · have : 0 ≤ (
        -9*a^2*y^3 - 9*a^2*y^2 - 23*a*y^3 - 33*a*y^2 - 7*a*y - 14*y^3 - 29*y^2 -
        13*y + 2) +
        1 * (6*(a + 1)^3*(y + 1)^4) := by
      ring_nf; positivity
    linarith
  · have : 0 ≤ 1 * (6*(a + 1)^3*(y + 1)^4) -
        (
        -9*a^2*y^3 - 9*a^2*y^2 - 23*a*y^3 - 33*a*y^2 - 7*a*y - 14*y^3 - 29*y^2 -
        13*y + 2) := by
      ring_nf; positivity
    linarith

/-- The second-order Taylor bound for `log (1 + r)`, `r ≥ 0`. -/
theorem abs_log_taylor_le (hr : 0 ≤ r) : |log (1 + r) - (r - r ^ 2 / 2)| ≤ r ^ 3 / 3 := by
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  have hc1 : ContinuousOn (fun r : ℝ => log (1 + r) - (r - r ^ 2 / 2)) (Ici 0) := by
    refine ContinuousOn.sub (ContinuousOn.log (by fun_prop) fun r hr => ?_) (by fun_prop)
    have : (0 : ℝ) ≤ r := hr; positivity
  have hm1 : MonotoneOn (fun r : ℝ => log (1 + r) - (r - r ^ 2 / 2)) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun r => 1 / (1 + r) - (1 - r))
      (convex_Ici 0) hc1 (fun r hr => ?_) (fun r hr => ?_)
    · rw [hint] at hr ⊢
      have h1 : (1 : ℝ) + r ≠ 0 := by have : (0 : ℝ) < r := hr; positivity
      have := ((hasDerivAt_id r).const_add 1).log h1
      refine (this.sub ((hasDerivAt_id r).sub ((hasDerivAt_pow 2 r).div_const 2))).congr_deriv
        ?_ |>.hasDerivWithinAt
      simp only [id]; push_cast; ring
    · rw [hint] at hr
      have : (0 : ℝ) < r := hr
      rw [show 1 / (1 + r) - (1 - r) = r ^ 2 / (1 + r) by field_simp; ring]
      positivity
  have hc2 : ContinuousOn (fun r : ℝ => r - r ^ 2 / 2 + r ^ 3 / 3 - log (1 + r)) (Ici 0) := by
    refine ContinuousOn.sub (by fun_prop) (ContinuousOn.log (by fun_prop) fun r hr => ?_)
    have : (0 : ℝ) ≤ r := hr; positivity
  have hm2 : MonotoneOn (fun r : ℝ => r - r ^ 2 / 2 + r ^ 3 / 3 - log (1 + r)) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun r => 1 - r + r ^ 2 - 1 / (1 + r))
      (convex_Ici 0) hc2 (fun r hr => ?_) (fun r hr => ?_)
    · rw [hint] at hr ⊢
      have h1 : (1 : ℝ) + r ≠ 0 := by have : (0 : ℝ) < r := hr; positivity
      have := ((hasDerivAt_id r).const_add 1).log h1
      refine ((((hasDerivAt_id r).sub ((hasDerivAt_pow 2 r).div_const 2)).add
        ((hasDerivAt_pow 3 r).div_const 3)).sub this).congr_deriv ?_ |>.hasDerivWithinAt
      simp only [id]; push_cast; ring
    · rw [hint] at hr
      have : (0 : ℝ) < r := hr
      rw [show 1 - r + r ^ 2 - 1 / (1 + r) = r ^ 3 / (1 + r) by field_simp; ring]
      positivity
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := le_refl 0
  have e1 := hm1 h0 hr hr
  have e2 := hm2 h0 hr hr
  simp only [add_zero, log_one] at e1 e2
  rw [abs_le]
  constructor <;> nlinarith

/-- **The pointwise bound on `σ_x(v)`.** -/
theorem abs_dispSig_le (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    |dispSig x v| * ((1 - x) * (1 + v)) ≤ 3 * (1 + log (1 + x / (1 - x) / v)) := by
  have hx0 := hx.1
  have h1 : 0 < 1 - x := by linarith [hx.2]
  set p := x / (1 - x) with hp
  have hp0 : 0 < p := by positivity
  have hxp : x ≤ p := by rw [hp, le_div_iff₀ h1]; nlinarith
  have hM : 0 < (1 - x) * (1 + v) := by positivity
  have hpx : x = p / (1 + p) := by rw [hp]; field_simp; ring
  have hpne : p ≠ 0 := hp0.ne'
  have hp1 : p + 1 ≠ 0 := by positivity
  have hp1' : 1 + p ≠ 0 := by positivity
  have hq : p ^ 2 / (p + 1) = p - x := by rw [hpx]; field_simp; ring
  have hq2 : p / (p + 1) = x := by rw [hpx, add_comm]
  set L := log (1 + p / v) with hL
  have hpv : 0 < p / v := by positivity
  have hL0 : 0 ≤ L := log_nonneg (by linarith)
  have hG : v ≤ p → |-(pairGa x (-v))| * ((1 - x) * (1 + v)) ≤ 3 := fun hvp =>
    pairBdP4 (x := x) (v := v) (y := p) (a := p / v - 1) hp0
      (by rw [sub_nonneg, le_div_iff₀ hv]; linarith) hpx (by field_simp; try ring)
  rcases le_or_gt v x with hvx | hvx
  · have hs : dispSig x v = -(pairAl x (-v)) + -(pairGa x (-v)) * L := by
      unfold dispSig; simp only [not_lt.2 hvx, ↓reduceIte, ← hp, ← hL]; ring
    have hA := pairBdP1 (x := x) (v := v) (y := p) (a := x / v - 1) hp0
      (by rw [sub_nonneg, le_div_iff₀ hv]; linarith) hpx
      (by rw [sub_add_cancel, mul_comm, ← div_div, hq2]; field_simp)
    have hG' := mul_le_mul_of_nonneg_right (hG (hvx.trans hxp)) hL0
    rw [hs]
    calc |-(pairAl x (-v)) + -(pairGa x (-v)) * L| * ((1 - x) * (1 + v))
        ≤ (|-(pairAl x (-v))| + |-(pairGa x (-v))| * L) * ((1 - x) * (1 + v)) := by
          gcongr
          exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hL0])
      _ ≤ 2 + 3 * L := by nlinarith [hA, hG']
      _ ≤ 3 * (1 + L) := by linarith
  rcases le_or_gt v p with hvp | hvp
  · have hs : dispSig x v = -(pairAl x (-v) + pairBe x (-v)) + -(pairGa x (-v)) * L := by
      unfold dispSig; simp only [hvx, ↓reduceIte, ← hp, ← hL]; ring
    have hpx' : 0 < p - x := by
      rw [hp, sub_pos, lt_div_iff₀ h1]; nlinarith
    have hA := pairBdP2 (x := x) (v := v) (y := p) (a := (p - x) / (v - x) - 1) hp0
      (by rw [sub_nonneg, le_div_iff₀ (by linarith)]; linarith) hpx
      (by have : v - x ≠ 0 := by linarith
          have : p - x ≠ 0 := hpx'.ne'
          rw [sub_add_cancel, mul_comm, ← div_div, hq, hq2]
          field_simp; try ring)
    have hG' := mul_le_mul_of_nonneg_right (hG hvp) hL0
    rw [hs]
    calc |-(pairAl x (-v) + pairBe x (-v)) + -(pairGa x (-v)) * L| * ((1 - x) * (1 + v))
        ≤ (|-(pairAl x (-v) + pairBe x (-v))| + |-(pairGa x (-v))| * L) *
            ((1 - x) * (1 + v)) := by
          gcongr
          exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hL0])
      _ ≤ 2 + 3 * L := by nlinarith [hA, hG']
      _ ≤ 3 * (1 + L) := by linarith
  · set rr := p / v with hrr
    have hr0 : 0 ≤ rr := by positivity
    have hs : dispSig x v = -(pairAl x (-v) + pairBe x (-v) + pairGa x (-v) * (rr - rr ^ 2 / 2)) +
        -(pairGa x (-v)) * (L - (rr - rr ^ 2 / 2)) := by
      unfold dispSig; simp only [hvx, ↓reduceIte, ← hp, ← hL, ← hrr]; ring
    have hA := pairBdP3 (x := x) (v := v) (y := p) (a := v / p - 1) hp0
      (by rw [sub_nonneg, le_div_iff₀ hp0]; linarith) hpx
      (by rw [sub_add_cancel, mul_div_assoc', mul_div_cancel_left₀ _ hp0.ne'])
    have hB := pairBdP5 (x := x) (v := v) (y := p) (a := v / p - 1) hp0
      (by rw [sub_nonneg, le_div_iff₀ hp0]; linarith) hpx
      (by rw [sub_add_cancel, mul_div_assoc', mul_div_cancel_left₀ _ hp0.ne'])
    rw [← hp, ← hrr] at hA hB
    have hT := abs_log_taylor_le hr0
    rw [← hL] at hT
    have hB' : |-(pairGa x (-v)) * (L - (rr - rr ^ 2 / 2))| ≤
        |-(pairGa x (-v) * rr ^ 3 / 3)| := by
      rw [abs_mul, show -(pairGa x (-v) * rr ^ 3 / 3) = -(pairGa x (-v)) * (rr ^ 3 / 3) by ring,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ rr ^ 3 / 3)]
      gcongr
    rw [hs]
    calc _ ≤ (|-(pairAl x (-v) + pairBe x (-v) + pairGa x (-v) * (rr - rr ^ 2 / 2))| +
            |-(pairGa x (-v) * rr ^ 3 / 3)|) * ((1 - x) * (1 + v)) := by
          gcongr
          exact (abs_add_le _ _).trans (by gcongr)
      _ ≤ 3 := by linarith [hA, hB]
      _ ≤ 3 * (1 + L) := by linarith

end

end QED.ChainProof.SetCK
