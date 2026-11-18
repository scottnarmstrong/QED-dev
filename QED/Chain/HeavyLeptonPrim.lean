/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyLeptonParam
public import QED.Polylog.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-lepton bubble: an antiderivative in the variable `w`

Helper analysis for obligation O3-M3 of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

In the variable `w` of `QED/Chain/HeavyLeptonParam.lean` (`x = (1-w²)/(1+yw)`), the heavy-lepton
integrand times the Jacobian is `(1 - phi y w) piHatP (pOf y w) jac y w = R₀ + R₁ ell`
(`integrandW_eq`), with rational `R₀, R₁` and `ell = log(y+w) - log w - log(1+yw)`. It has the
antiderivative (generated with sympy and checked to 60 digits with mpmath; script
`scripts/numerics/chain/heavy_lepton.py`)

`hlPrim = Q₀ + c (log(1+yw) - log(y+w)) + Q₁ ell + a (K₁ + K₋₁) + b K_y`,

with `a = (y²-5)/(2y³)`, `b = 2/y⁴`, `c = (y²-9)/(3y²)`, rational `Q₀, Q₁`, and the dilogarithm
blocks `K₁' = ell/(1-w)`, `K₋₁' = ell/(1+w)`, `K_y' = y ell/(1+yw)`. Every `Li₂` argument
stays in `(-1, 1)` for `w ∈ (0,1)`, `y ∈ (0,1)`.

## Main statements

* `integrandW_eq`: the integrand in `w` is `R₀ + R₁ ell`.
* `hasDerivAt_hlPrim`: `hlPrim y` is an antiderivative of `R₀ + R₁ ell` on `(0,1)`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain.HeavyLepton

/-! ### Rational pieces -/

/-- The rational part `Q₀` of the antiderivative. -/
noncomputable def hlQ0 (y w : ℝ) : ℝ :=
  (((5 * y ^ 2 - 11) * (5 * y ^ 2 - 9)) +
    (2 * y * (19 * y ^ 4 - 58 * y ^ 2 + 99)) * w +
    (-29 * y ^ 4 + 283 * y ^ 2 - 99) * w ^ 2 +
    (-2 * y * (26 * y ^ 4 - 124 * y ^ 2 + 99)) * w ^ 3 +
    (3 * y ^ 2 * (21 * y ^ 2 - 53)) * w ^ 4 +
    (2 * y ^ 3 * (19 * y ^ 2 - 30)) * w ^ 5 +
    (13 * y ^ 4) * w ^ 6) /
    (36 * y ^ 4 * (1 - w ^ 2) * (1 + y * w) ^ 2)

/-- The coefficient `Q₁` of `ell` in the antiderivative (`Q₁(0) = 0`). -/
noncomputable def hlQ1 (y w : ℝ) : ℝ :=
  ((-6 * (y ^ 2 - 3)) * w +
    (y * (y ^ 4 - 12 * y ^ 2 + 42)) * w ^ 2 +
    (-2 * (2 * y ^ 4 - 18 * y ^ 2 + 13)) * w ^ 3 +
    (-y * (2 * y ^ 4 - 19 * y ^ 2 + 64)) * w ^ 4 +
    (2 * (y ^ 4 - 27 * y ^ 2 + 2)) * w ^ 5 +
    (y * (y ^ 4 - 22 * y ^ 2 + 6)) * w ^ 6 +
    (-2 * y ^ 4) * w ^ 7 +
    (-y ^ 3) * w ^ 8) /
    (6 * y ^ 3 * (1 - w ^ 2) ^ 2 * (1 + y * w) ^ 2)

/-- `Q₀'`. -/
noncomputable def hlQ0d (y w : ℝ) : ℝ :=
  ((-6 * y * (y ^ 2 - 7)) +
    (-19 * y ^ 4 + 54 * y ^ 2 + 84) * w +
    (-3 * y * (3 * y ^ 2 - 38)) * w ^ 2 +
    (31 * y ^ 4 + 76 * y ^ 2 - 120) * w ^ 3 +
    (5 * y * (31 * y ^ 2 - 30)) * w ^ 4 +
    (31 * y ^ 4 + 10 * y ^ 2 + 60) * w ^ 5 +
    (-y * (31 * y ^ 2 - 90)) * w ^ 6 +
    (-y ^ 2 * (19 * y ^ 2 - 4)) * w ^ 7 +
    (-13 * y ^ 3) * w ^ 8) /
    (18 * y ^ 2 * (1 - w ^ 2) ^ 2 * (1 + y * w) ^ 3)

/-- `Q₁'`. -/
noncomputable def hlQ1d (y w : ℝ) : ℝ :=
  ((-3 * (y ^ 2 - 3)) +
    (y * (y ^ 4 - 9 * y ^ 2 + 33)) * w +
    (-3 * (2 * y ^ 4 - 15 * y ^ 2 + 4)) * w ^ 2 +
    (-y * (5 * y ^ 4 - 29 * y ^ 2 + 54)) * w ^ 3 +
    (-2 * y ^ 4 - 97 * y ^ 2 - 3) * w ^ 4 +
    (-3 * y * (31 * y ^ 2 + 5)) * w ^ 5 +
    (-(3 * y ^ 2 + 2) * (11 * y ^ 2 + 1)) * w ^ 6 +
    (-y * (y ^ 2 + 1) * (5 * y ^ 2 + 4)) * w ^ 7 +
    (y ^ 3 * (y ^ 2 + 2)) * w ^ 9 +
    (y ^ 4) * w ^ 10) /
    (3 * y ^ 3 * (1 - w ^ 2) ^ 3 * (1 + y * w) ^ 3)

/-- The rational part `R₀` of the `w`-integrand `R₀ + R₁ ell`. -/
noncomputable def hlR0 (y w : ℝ) : ℝ :=
  ((-5 * y ^ 4) * w +
    (-3 * y ^ 3) * w ^ 2 +
    (y ^ 2 * (17 * y ^ 2 + 38)) * w ^ 3 +
    (5 * y * (17 * y ^ 2 + 12)) * w ^ 4 +
    (17 * y ^ 4 + 104 * y ^ 2 + 24) * w ^ 5 +
    (y * (19 * y ^ 2 + 36)) * w ^ 6 +
    (-y ^ 2 * (5 * y ^ 2 - 2)) * w ^ 7 +
    (-5 * y ^ 3) * w ^ 8) /
    (9 * y ^ 2 * (1 - w ^ 2) ^ 2 * (1 + y * w) ^ 3)

/-- The coefficient `R₁` of `ell` in the `w`-integrand. -/
noncomputable def hlR1 (y w : ℝ) : ℝ :=
  ((y ^ 5) * w +
    (3 * y ^ 4) * w ^ 2 +
    (-2 * y ^ 3 * (y ^ 2 + 2)) * w ^ 3 +
    (-2 * y ^ 2 * (10 * y ^ 2 + 11)) * w ^ 4 +
    (-6 * y * (y ^ 4 + 9 * y ^ 2 + 4)) * w ^ 5 +
    (-4 * (y ^ 2 + 2) * (6 * y ^ 2 + 1)) * w ^ 6 +
    (-2 * y * (y ^ 4 + 12 * y ^ 2 + 8)) * w ^ 7 +
    (-6 * y ^ 2) * w ^ 8 +
    (y ^ 3 * (y ^ 2 + 2)) * w ^ 9 +
    (y ^ 4) * w ^ 10) /
    (3 * y ^ 3 * (1 - w ^ 2) ^ 3 * (1 + y * w) ^ 3)

/-- The regular part `B = Q₀ + Q₁(u + u²/2 + u³/3 + u⁴/4)` of the antiderivative at `w = 1`,
with `u = y(1-w²)/(y+w)`. -/
noncomputable def hlB (y w : ℝ) : ℝ :=
  ((2 * y ^ 4 * (5 * y ^ 2 - 11) * (5 * y ^ 2 - 9)) +
    (2 * y ^ 3 * (38 * y ^ 6 - 91 * y ^ 4 + 23 * y ^ 2 + 396)) * w +
    (y ^ 2 * (25 * y ^ 8 - 4 * y ^ 6 + 476 * y ^ 4 + 1320 * y ^ 2 + 1188)) * w ^ 2 +
    (-2 * y * (38 * y ^ 8 - 476 * y ^ 6 - 795 * y ^ 4 - 1166 * y ^ 2 - 396)) * w ^ 3 +
    (-48 * y ^ 10 + 291 * y ^ 8 + 1020 * y ^ 6 + 2234 * y ^ 4 + 1600 * y ^ 2 + 198) * w ^ 4 +
    (2 * y * (9 * y ^ 8 - 236 * y ^ 6 + 653 * y ^ 4 + 646 * y ^ 2 + 198)) * w ^ 5 +
    (2 * y ^ 2 * (18 * y ^ 8 - 214 * y ^ 6 + 159 * y ^ 4 + 272 * y ^ 2 + 135)) * w ^ 6 +
    (-2 * y ^ 3 * (17 * y ^ 6 - 164 * y ^ 4 - 3 * y ^ 2 - 36)) * w ^ 7 +
    (-2 * y ^ 4 * (8 * y ^ 6 - 115 * y ^ 4 + 54 * y ^ 2 + 3)) * w ^ 8 +
    (2 * y ^ 7 * (11 * y ^ 2 - 51)) * w ^ 9 +
    (3 * y ^ 6 * (y ^ 4 - 16 * y ^ 2 + 4)) * w ^ 10 +
    (-2 * y ^ 7 * (3 * y ^ 2 - 2)) * w ^ 11 +
    (-3 * y ^ 8) * w ^ 12) /
    (72 * y ^ 4 * (1 + y * w) ^ 2 * (y + w) ^ 4)

/-- `U = Q₁ u⁴`, regular at `w = 1`. -/
noncomputable def hlU (y w : ℝ) : ℝ :=
  ((-6 * y * (y ^ 2 - 3)) * w +
    (y ^ 2 * (y ^ 4 - 12 * y ^ 2 + 42)) * w ^ 2 +
    (-2 * y * (2 * y ^ 4 - 24 * y ^ 2 + 31)) * w ^ 3 +
    (-y ^ 2 * (4 * y ^ 4 - 43 * y ^ 2 + 148)) * w ^ 4 +
    (2 * y * (5 * y ^ 4 - 66 * y ^ 2 + 37)) * w ^ 5 +
    (2 * y ^ 2 * (3 * y ^ 4 - 36 * y ^ 2 + 88)) * w ^ 6 +
    (-2 * y * (5 * y ^ 4 - 72 * y ^ 2 + 17)) * w ^ 7 +
    (-2 * y ^ 2 * (2 * y ^ 4 - 31 * y ^ 2 + 38)) * w ^ 8 +
    (2 * y * (3 * y ^ 4 - 27 * y ^ 2 + 2)) * w ^ 9 +
    (y ^ 2 * (y ^ 4 - 20 * y ^ 2 + 6)) * w ^ 10 +
    (-2 * y ^ 5) * w ^ 11 +
    (-y ^ 4) * w ^ 12) /
    (6 * (1 + y * w) ^ 2 * (y + w) ^ 4)

/-! ### Derivatives of the rational pieces -/

/-- The derivative of a polynomial of degree at most `12`. -/
theorem hasDerivAt_poly12 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ x : ℝ) :
    HasDerivAt (fun w => a₀ + a₁ * w + a₂ * w ^ 2 + a₃ * w ^ 3 + a₄ * w ^ 4 + a₅ * w ^ 5 +
      a₆ * w ^ 6 + a₇ * w ^ 7 + a₈ * w ^ 8 + a₉ * w ^ 9 + a₁₀ * w ^ 10 + a₁₁ * w ^ 11 +
      a₁₂ * w ^ 12)
      (a₁ + 2 * a₂ * x + 3 * a₃ * x ^ 2 + 4 * a₄ * x ^ 3 + 5 * a₅ * x ^ 4 + 6 * a₆ * x ^ 5 +
        7 * a₇ * x ^ 6 + 8 * a₈ * x ^ 7 + 9 * a₉ * x ^ 8 + 10 * a₁₀ * x ^ 9 +
        11 * a₁₁ * x ^ 10 + 12 * a₁₂ * x ^ 11) x := by
  have h := ((((((((((((hasDerivAt_const x a₀).add ((hasDerivAt_id' x).const_mul a₁)).add
    ((hasDerivAt_pow 2 x).const_mul a₂)).add ((hasDerivAt_pow 3 x).const_mul a₃)).add
    ((hasDerivAt_pow 4 x).const_mul a₄)).add ((hasDerivAt_pow 5 x).const_mul a₅)).add
    ((hasDerivAt_pow 6 x).const_mul a₆)).add ((hasDerivAt_pow 7 x).const_mul a₇)).add
    ((hasDerivAt_pow 8 x).const_mul a₈)).add ((hasDerivAt_pow 9 x).const_mul a₉)).add
    ((hasDerivAt_pow 10 x).const_mul a₁₀)).add ((hasDerivAt_pow 11 x).const_mul a₁₁)).add
    ((hasDerivAt_pow 12 x).const_mul a₁₂)
  convert h using 1
  push_cast
  ring

theorem hasDerivAt_one_sub_sq (w : ℝ) : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-(2 * w)) w := by
  simpa using (hasDerivAt_pow 2 w).const_sub 1

theorem hasDerivAt_one_add_mul (y w : ℝ) : HasDerivAt (fun w : ℝ => 1 + y * w) y w := by
  simpa using ((hasDerivAt_id' w).const_mul y).const_add 1

theorem hasDerivAt_add_left (y w : ℝ) : HasDerivAt (fun w : ℝ => y + w) 1 w := by
  simpa using (hasDerivAt_id' w).const_add y

theorem hasDerivAt_hlQ0 {y w : ℝ} (hy : y ≠ 0) (h1 : 1 - w ^ 2 ≠ 0) (h2 : 1 + y * w ≠ 0) :
    HasDerivAt (hlQ0 y) (hlQ0d y w) w := by
  have hN := hasDerivAt_poly12 ((5 * y ^ 2 - 11) * (5 * y ^ 2 - 9))
    (2 * y * (19 * y ^ 4 - 58 * y ^ 2 + 99)) (-29 * y ^ 4 + 283 * y ^ 2 - 99)
    (-2 * y * (26 * y ^ 4 - 124 * y ^ 2 + 99)) (3 * y ^ 2 * (21 * y ^ 2 - 53))
    (2 * y ^ 3 * (19 * y ^ 2 - 30)) (13 * y ^ 4) 0 0 0 0 0 0 w
  have hD := ((hasDerivAt_one_sub_sq w).const_mul (36 * y ^ 4)).mul
    ((hasDerivAt_one_add_mul y w).fun_pow 2)
  have hne : 36 * y ^ 4 * (1 - w ^ 2) * (1 + y * w) ^ 2 ≠ 0 := by
    have := pow_ne_zero 4 hy
    have := pow_ne_zero 2 h2
    positivity
  have hTd : 18 * y ^ 2 * (1 - w ^ 2) ^ 2 * (1 + y * w) ^ 3 ≠ 0 := by
    have := pow_ne_zero 2 hy
    have := pow_ne_zero 2 h1
    have := pow_ne_zero 3 h2
    positivity
  refine ((hN.div hD hne).congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun v => ?_)
  · simp only [Pi.mul_apply]
    unfold hlQ0d
    rw [div_eq_div_iff (pow_ne_zero 2 hne) hTd]
    push_cast
    ring
  · simp only [hlQ0, Pi.div_apply, Pi.mul_apply]
    ring

theorem hasDerivAt_hlQ1 {y w : ℝ} (hy : y ≠ 0) (h1 : 1 - w ^ 2 ≠ 0) (h2 : 1 + y * w ≠ 0) :
    HasDerivAt (hlQ1 y) (hlQ1d y w) w := by
  have hN := hasDerivAt_poly12 0 (-6 * (y ^ 2 - 3)) (y * (y ^ 4 - 12 * y ^ 2 + 42))
    (-2 * (2 * y ^ 4 - 18 * y ^ 2 + 13)) (-y * (2 * y ^ 4 - 19 * y ^ 2 + 64))
    (2 * (y ^ 4 - 27 * y ^ 2 + 2)) (y * (y ^ 4 - 22 * y ^ 2 + 6)) (-2 * y ^ 4) (-y ^ 3) 0 0 0 0 w
  have hD := (((hasDerivAt_one_sub_sq w).fun_pow 2).const_mul (6 * y ^ 3)).mul
    ((hasDerivAt_one_add_mul y w).fun_pow 2)
  have hne : 6 * y ^ 3 * (1 - w ^ 2) ^ 2 * (1 + y * w) ^ 2 ≠ 0 := by
    have := pow_ne_zero 3 hy
    have := pow_ne_zero 2 h1
    have := pow_ne_zero 2 h2
    positivity
  have hTd : 3 * y ^ 3 * (1 - w ^ 2) ^ 3 * (1 + y * w) ^ 3 ≠ 0 := by
    have := pow_ne_zero 3 hy
    have := pow_ne_zero 3 h1
    have := pow_ne_zero 3 h2
    positivity
  refine ((hN.div hD hne).congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun v => ?_)
  · simp only [Pi.mul_apply]
    unfold hlQ1d
    rw [div_eq_div_iff (pow_ne_zero 2 hne) hTd]
    push_cast
    ring
  · simp only [hlQ1, Pi.div_apply, Pi.mul_apply]
    ring

/-- The `ell`-coefficient identity: `Q₁' + a/(1-w) + a/(1+w) + b y/(1+yw) = R₁`. -/
theorem hlQ1d_add_eq {y w : ℝ} (hy : y ≠ 0) (h1 : 1 - w ≠ 0) (h2 : 1 + w ≠ 0)
    (h3 : 1 + y * w ≠ 0) :
    hlQ1d y w + (y ^ 2 - 5) / (2 * y ^ 3) * (1 / (1 - w) + 1 / (1 + w)) +
      2 / y ^ 4 * (y / (1 + y * w)) = hlR1 y w := by
  have h12 : 1 - w ^ 2 ≠ 0 := by
    rw [show 1 - w ^ 2 = (1 - w) * (1 + w) by ring]
    exact mul_ne_zero h1 h2
  unfold hlQ1d hlR1
  field_simp
  ring

/-- The rational identity: `Q₀' + c (y/(1+yw) - 1/(y+w)) + Q₁ ell' = R₀`. -/
theorem hlQ0d_add_eq {y w : ℝ} (hy : y ≠ 0) (hw : w ≠ 0) (h1 : 1 - w ≠ 0) (h2 : 1 + w ≠ 0)
    (h3 : 1 + y * w ≠ 0) (h4 : y + w ≠ 0) :
    hlQ0d y w + (y ^ 2 - 9) / (3 * y ^ 2) * (y / (1 + y * w) - 1 / (y + w)) +
      hlQ1 y w * (1 / (y + w) - 1 / w - y / (1 + y * w)) = hlR0 y w := by
  have h12 : 1 - w ^ 2 ≠ 0 := by
    rw [show 1 - w ^ 2 = (1 - w) * (1 + w) by ring]
    exact mul_ne_zero h1 h2
  unfold hlQ0d hlQ1 hlR0
  field_simp
  ring

/-! ### The integrand in `w` -/

/-- **The integrand in `w`.** `(1 - phi y w) piHatP (pOf y w) jac y w = R₀ + R₁ ell`. -/
theorem integrandW_eq {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    (1 - phi y w) * piHatP (pOf y w) * jac y w = hlR0 y w + hlR1 y w * ell y w := by
  obtain ⟨h0, h1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have hs : 0 < 1 - w ^ 2 := by nlinarith
  unfold piHatP
  rw [log_one_add_pOf_sub hy ⟨h0, h1⟩]
  generalize ell y w = L
  unfold phi pOf jac hlR0 hlR1
  field_simp
  ring

/-! ### The logarithmic and dilogarithmic blocks -/

theorem hasDerivAt_ell {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    HasDerivAt (ell y) (1 / (y + w) - 1 / w - y / (1 + y * w)) w := by
  have h := (((hasDerivAt_add_left y w).log (by positivity)).sub
    ((hasDerivAt_id' w).log hw.ne')).sub ((hasDerivAt_one_add_mul y w).log (by positivity))
  exact h

/-- `Li₂ ∘ g` has derivative `-log(1 - g)/g · g'` where `0 < |g| < 1`. -/
theorem hasDerivAt_Li₂_comp {g : ℝ → ℝ} {g' w : ℝ} (hg : HasDerivAt g g' w) (h1 : |g w| < 1)
    (h0 : g w ≠ 0) : HasDerivAt (fun v => Li₂ (g v)) (-log (1 - g w) / g w * g') w :=
  (hasDerivAt_Li₂ h1 h0).comp w hg

/-- `K₁ = Li₂((1-w)/(1+y)) - Li₂(y(1-w)/(1+y)) - Li₂(1-w)`, with `K₁' = ell/(1-w)`. -/
noncomputable def hlK1 (y w : ℝ) : ℝ :=
  Li₂ ((1 - w) / (1 + y)) - Li₂ (y * (1 - w) / (1 + y)) - Li₂ (1 - w)

/-- `K₋₁ = Li₂((1-y)/(1+w)) - log w log(1+w) - 2 Li₂(-w) - Li₂((1-y)w/(1+w)) + Li₂(-yw)`, with
`K₋₁' = ell/(1+w)`. -/
noncomputable def hlKm1 (y w : ℝ) : ℝ :=
  Li₂ ((1 - y) / (1 + w)) - log w * log (1 + w) - 2 * Li₂ (-w) - Li₂ ((1 - y) * w / (1 + w)) +
    Li₂ (-(y * w))

/-- `K_y = Li₂((1-y²)/(1+yw)) - log y log(1+yw) - log w log(1+yw) - Li₂(-yw)`, with
`K_y' = y ell/(1+yw)`. -/
noncomputable def hlKy (y w : ℝ) : ℝ :=
  Li₂ ((1 - y ^ 2) / (1 + y * w)) - log y * log (1 + y * w) - log w * log (1 + y * w) -
    Li₂ (-(y * w))

theorem abs_lt_one_of_mem {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : |t| < 1 := by
  rw [abs_of_pos h0]
  exact h1

theorem abs_neg_lt_one_of_mem {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : |-t| < 1 := by
  rw [abs_neg, abs_of_pos h0]
  exact h1

theorem hasDerivAt_hlK1 {y w : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hlK1 y) (ell y w / (1 - w)) w := by
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hw0, hw1⟩ := hw
  have hyp : 0 < 1 + y := by linarith
  have hsw : 0 < 1 - w := by linarith
  have hg1 : HasDerivAt (fun v => (1 - v) / (1 + y)) (-1 / (1 + y)) w :=
    ((hasDerivAt_id' w).const_sub 1).div_const (1 + y)
  have hg2 : HasDerivAt (fun v => y * (1 - v) / (1 + y)) (y * -1 / (1 + y)) w :=
    (((hasDerivAt_id' w).const_sub 1).const_mul y).div_const (1 + y)
  have hg3 : HasDerivAt (fun v : ℝ => 1 - v) (-1) w := (hasDerivAt_id' w).const_sub 1
  have m1 : 0 < (1 - w) / (1 + y) ∧ (1 - w) / (1 + y) < 1 :=
    ⟨by positivity, by rw [div_lt_one hyp]; linarith⟩
  have m2 : 0 < y * (1 - w) / (1 + y) ∧ y * (1 - w) / (1 + y) < 1 :=
    ⟨by positivity, by rw [div_lt_one hyp]; nlinarith⟩
  have h := ((hasDerivAt_Li₂_comp hg1 (abs_lt_one_of_mem m1.1 m1.2) m1.1.ne').sub
    (hasDerivAt_Li₂_comp hg2 (abs_lt_one_of_mem m2.1 m2.2) m2.1.ne')).sub
    (hasDerivAt_Li₂_comp hg3 (abs_lt_one_of_mem hsw (by linarith)) hsw.ne')
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => rfl)
  have l1 : log (1 - (1 - w) / (1 + y)) = log (y + w) - log (1 + y) := by
    rw [show 1 - (1 - w) / (1 + y) = (y + w) / (1 + y) by field_simp; ring,
      log_div (by positivity) hyp.ne']
  have l2 : log (1 - y * (1 - w) / (1 + y)) = log (1 + y * w) - log (1 + y) := by
    rw [show 1 - y * (1 - w) / (1 + y) = (1 + y * w) / (1 + y) by field_simp; ring,
      log_div (by positivity) hyp.ne']
  have l3 : log (1 - (1 - w)) = log w := by rw [sub_sub_cancel]
  rw [l1, l2, l3]
  unfold ell
  field_simp
  ring

theorem hasDerivAt_hlKm1 {y w : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hlKm1 y) (ell y w / (1 + w)) w := by
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hw0, hw1⟩ := hw
  have hwp : 0 < 1 + w := by linarith
  have hsy : 0 < 1 - y := by linarith
  have hpw : HasDerivAt (fun v : ℝ => 1 + v) 1 w := by
    simpa using (hasDerivAt_id' w).const_add 1
  have hg1 : HasDerivAt (fun v => (1 - y) / (1 + v)) ((0 * (1 + w) - (1 - y) * 1) / (1 + w) ^ 2)
      w := (hasDerivAt_const w (1 - y)).div hpw hwp.ne'
  have hg2 : HasDerivAt (fun v : ℝ => -v) (-1) w := (hasDerivAt_id' w).neg
  have hg3 : HasDerivAt (fun v => (1 - y) * v / (1 + v))
      (((1 - y) * 1 * (1 + w) - (1 - y) * w * 1) / (1 + w) ^ 2) w :=
    ((hasDerivAt_id' w).const_mul (1 - y)).div hpw hwp.ne'
  have hg4 : HasDerivAt (fun v => -(y * v)) (-(y * 1)) w := ((hasDerivAt_id' w).const_mul y).neg
  have m1 : 0 < (1 - y) / (1 + w) ∧ (1 - y) / (1 + w) < 1 :=
    ⟨by positivity, by rw [div_lt_one hwp]; linarith⟩
  have m3 : 0 < (1 - y) * w / (1 + w) ∧ (1 - y) * w / (1 + w) < 1 :=
    ⟨by positivity, by rw [div_lt_one hwp]; nlinarith⟩
  have m4 : 0 < y * w ∧ y * w < 1 := ⟨by positivity, by nlinarith⟩
  have hL := ((hasDerivAt_id' w).log hw0.ne').mul (hpw.log hwp.ne')
  have h := (((((hasDerivAt_Li₂_comp hg1 (abs_lt_one_of_mem m1.1 m1.2) m1.1.ne').sub hL).sub
    ((hasDerivAt_Li₂_comp hg2 (abs_neg_lt_one_of_mem hw0 hw1) (neg_ne_zero.2 hw0.ne')).const_mul
      2)).sub (hasDerivAt_Li₂_comp hg3 (abs_lt_one_of_mem m3.1 m3.2) m3.1.ne')).add
    (hasDerivAt_Li₂_comp hg4 (abs_neg_lt_one_of_mem m4.1 m4.2) (neg_ne_zero.2 m4.1.ne')))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  · have l1 : log (1 - (1 - y) / (1 + w)) = log (y + w) - log (1 + w) := by
      rw [show 1 - (1 - y) / (1 + w) = (y + w) / (1 + w) by field_simp; ring,
        log_div (by positivity) hwp.ne']
    have l2 : log (1 - -w) = log (1 + w) := by rw [sub_neg_eq_add]
    have l3 : log (1 - (1 - y) * w / (1 + w)) = log (1 + y * w) - log (1 + w) := by
      rw [show 1 - (1 - y) * w / (1 + w) = (1 + y * w) / (1 + w) by field_simp; ring,
        log_div (by positivity) hwp.ne']
    have l4 : log (1 - -(y * w)) = log (1 + y * w) := by rw [sub_neg_eq_add]
    rw [l1, l2, l3, l4]
    unfold ell
    field_simp
    ring
  · simp only [hlKm1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]

theorem hasDerivAt_hlKy {y w : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hlKy y) (y * ell y w / (1 + y * w)) w := by
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hw0, hw1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have hb := hasDerivAt_one_add_mul y w
  have hg1 : HasDerivAt (fun v => (1 - y ^ 2) / (1 + y * v))
      ((0 * (1 + y * w) - (1 - y ^ 2) * y) / (1 + y * w) ^ 2) w :=
    (hasDerivAt_const w (1 - y ^ 2)).div hb hd.ne'
  have hg4 : HasDerivAt (fun v => -(y * v)) (-(y * 1)) w := ((hasDerivAt_id' w).const_mul y).neg
  have m1 : 0 < (1 - y ^ 2) / (1 + y * w) ∧ (1 - y ^ 2) / (1 + y * w) < 1 :=
    ⟨div_pos hy2 hd, by rw [div_lt_one hd]; nlinarith⟩
  have m4 : 0 < y * w ∧ y * w < 1 := ⟨by positivity, by nlinarith⟩
  have h := (((hasDerivAt_Li₂_comp hg1 (abs_lt_one_of_mem m1.1 m1.2) m1.1.ne').sub
    ((hb.log hd.ne').const_mul (log y))).sub (((hasDerivAt_id' w).log hw0.ne').mul
      (hb.log hd.ne'))).sub
    (hasDerivAt_Li₂_comp hg4 (abs_neg_lt_one_of_mem m4.1 m4.2) (neg_ne_zero.2 m4.1.ne'))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  · have l1 : log (1 - (1 - y ^ 2) / (1 + y * w)) = log y + log (y + w) - log (1 + y * w) := by
      rw [show 1 - (1 - y ^ 2) / (1 + y * w) = y * (y + w) / (1 + y * w) by field_simp; ring,
        log_div (by positivity) hd.ne', log_mul hy0.ne' (by positivity)]
    have l4 : log (1 - -(y * w)) = log (1 + y * w) := by rw [sub_neg_eq_add]
    rw [l1, l4]
    unfold ell
    field_simp
    ring
  · simp only [hlKy, Pi.sub_apply, Pi.mul_apply]

/-! ### The antiderivative -/

/-- **The antiderivative in `w`**:
`Q₀ + c (log(1+yw) - log(y+w)) + Q₁ ell + a (K₁ + K₋₁) + b K_y` with `a = (y²-5)/(2y³)`,
`b = 2/y⁴`, `c = (y²-9)/(3y²)`. -/
noncomputable def hlPrim (y w : ℝ) : ℝ :=
  hlQ0 y w + (y ^ 2 - 9) / (3 * y ^ 2) * (log (1 + y * w) - log (y + w)) + hlQ1 y w * ell y w +
    (y ^ 2 - 5) / (2 * y ^ 3) * (hlK1 y w + hlKm1 y w) + 2 / y ^ 4 * hlKy y w

/-- **The antiderivative.** For `y, w ∈ (0,1)`, `hlPrim y` has derivative `R₀ + R₁ ell` at `w`. -/
theorem hasDerivAt_hlPrim {y w : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hlPrim y) (hlR0 y w + hlR1 y w * ell y w) w := by
  have hy0 := hy.1
  obtain ⟨hw0, hw1⟩ := hw
  have h1 : 1 - w ≠ 0 := by linarith
  have h2 : 1 + w ≠ 0 := by linarith
  have h3 : 0 < 1 + y * w := by positivity
  have h4 : 0 < y + w := by positivity
  have h12 : 1 - w ^ 2 ≠ 0 := by nlinarith
  have h := ((((hasDerivAt_hlQ0 hy0.ne' h12 h3.ne').add
    ((((hasDerivAt_one_add_mul y w).log h3.ne').sub
      ((hasDerivAt_add_left y w).log h4.ne')).const_mul ((y ^ 2 - 9) / (3 * y ^ 2)))).add
    ((hasDerivAt_hlQ1 hy0.ne' h12 h3.ne').mul (hasDerivAt_ell hy0 hw0))).add
    (((hasDerivAt_hlK1 hy ⟨hw0, hw1⟩).add (hasDerivAt_hlKm1 hy ⟨hw0, hw1⟩)).const_mul
      ((y ^ 2 - 5) / (2 * y ^ 3)))).add
    ((hasDerivAt_hlKy hy ⟨hw0, hw1⟩).const_mul (2 / y ^ 4))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  · linear_combination ell y w * hlQ1d_add_eq hy0.ne' h1 h2 h3.ne' +
      hlQ0d_add_eq hy0.ne' hw0.ne' h1 h2 h3.ne' h4.ne'
  · simp only [hlPrim, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]

end QED.Chain.HeavyLepton
