/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighDeriv

/-!
# Set (d), master `I₁₂`: the pointwise `ε`-derivatives of the five remainder integrands

At each interior point every integrand of `QED.ThreeLoopD.i12Rest` is a finite sum of terms
`C e^{λε}` and `C ε e^{λε}` with real `C`, `λ` (each power `x ^ (α + βε)` of a positive real is
`x ^ α e^{βε log x}`, and `Φ₀`, `Φ₁` are sums of such powers). Hence the `n`-th derivative at
`ε = 0` is the sum of the `C λⁿ` and `C n λⁿ⁻¹`: four terms for `T_A`, `T_B` (plus one), six for
`R₁`, ten for each of `R_A`, `R_B`, all polynomials in logarithms of the integration variables.

For instance, for `T_A`, with `X = uθ`, `Y = (1 - u)/2`, `B = 2 log θ - 2 log 2 + log(u(1 - u))`
and `λ(x) = B - 3 log x`, the `n`-th derivative is
`(2/θ) [(X + Y)²/(XY) λ(X + Y)ⁿ - (X/Y) λ(X)ⁿ - (Y/X) λ(Y)ⁿ - 2 λ(Y)ⁿ + 3n λ(Y)ⁿ⁻¹]`.

Together with `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_integrals` this gives every Taylor
coefficient of the remainder as five explicit integrals
(`QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_explicit`); in particular `r₃`, `r₄` (`n = 2, 3`).

## Main results

* `QED.ThreeLoopD.iteratedDeriv_i12TAIg`, `QED.ThreeLoopD.iteratedDeriv_i12TBIg`,
  `QED.ThreeLoopD.iteratedDeriv_i12R1Ig`, `QED.ThreeLoopD.iteratedDeriv_i12RA3Ig`,
  `QED.ThreeLoopD.iteratedDeriv_i12RB3Ig` (pointwise formulas).
* `QED.ThreeLoopD.iteratedDeriv_i12TA_eq_integral` and its four siblings.
* `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_explicit`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

theorem i12_cpow_lin {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = exp (Real.log x * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]

theorem i12_cpow_two_mul_sub_one {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ (2 * ε - 1) = exp (((2 * Real.log x : ℝ) : ℂ) * ε) / x := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_sub _ _ hx', cpow_one, i12_cpow_lin hx]
  push_cast; ring_nf

theorem i12_cpow_two_sub_three_mul {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ (2 - 3 * ε) = (x : ℂ) ^ 2 * exp (((-3 * Real.log x : ℝ) : ℂ) * ε) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_sub _ _ hx', i12_cpow_lin hx, i12_cpow_lin hx (3 * ε), div_eq_mul_inv, ← exp_neg]
  congr 1
  · rw [← i12_cpow_lin hx]; norm_cast
  · push_cast; ring_nf

theorem i12_cpow_neg_three_mul {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ (-3 * ε) = exp (((-3 * Real.log x : ℝ) : ℂ) * ε) := by
  rw [i12_cpow_lin hx]; push_cast; ring_nf

theorem i12_cpow_self {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ ε = exp ((Real.log x : ℂ) * ε) := i12_cpow_lin hx ε

theorem i12_cpow_neg_self {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ (-ε) = exp (((-Real.log x : ℝ) : ℂ) * ε) := by
  rw [i12_cpow_lin hx]; push_cast; ring_nf

theorem i12_cpow_one_sub_three_mul {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ (1 - 3 * ε) = (x : ℂ) * exp (((-3 * Real.log x : ℝ) : ℂ) * ε) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_sub _ _ hx', cpow_one, i12_cpow_lin hx (3 * ε), div_eq_mul_inv, ← exp_neg]
  congr 1
  push_cast; ring_nf

theorem i12_cpow_sub_one {x : ℝ} (hx : 0 < x) (ε : ℂ) :
    (x : ℂ) ^ (ε - 1) = exp ((Real.log x : ℂ) * ε) / x := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_sub _ _ hx', cpow_one, i12_cpow_lin hx]

theorem i12_exp_add_mul (A B : ℝ) (ε : ℂ) :
    exp (((A + B : ℝ) : ℂ) * ε) = exp ((A : ℂ) * ε) * exp ((B : ℂ) * ε) := by
  rw [← exp_add]; push_cast; ring_nf

theorem i12_iteratedDeriv_exp_zero (C L : ℂ) (n : ℕ) :
    iteratedDeriv n (fun ε => C * exp (L * ε)) 0 = C * L ^ n := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]; simp

theorem i12_iteratedDeriv_mul_exp_zero (C L : ℂ) (n : ℕ) :
    iteratedDeriv n (fun ε => C * (ε * exp (L * ε))) 0 = C * (n * L ^ (n - 1)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul (f := fun ε => ε) contDiffAt_id
    (by fun_prop)]
  rcases n with _ | n
  · simp
  rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [iteratedDeriv_fun_id_zero, hi])
    (fun h => by simp at h)]
  simp [iteratedDeriv_fun_id_zero, iteratedDeriv_cexp_const_mul]

/-- The pointwise `n`-th `ε`-derivative at `0` of the integrand of `T_A`. With `X = uθ`,
`Y = (1 - u)/2`, `B = 2 log θ - 2 log 2 + log(u(1 - u))`, `λ(x) = B - 3 log x`:
`(2/θ) [(X + Y)²/(XY) λ(X + Y)ⁿ - (X/Y) λ(X)ⁿ - (Y/X) λ(Y)ⁿ - 2 λ(Y)ⁿ + 3n λ(Y)ⁿ⁻¹]`. -/
noncomputable def i12TAd (n : ℕ) (θ u : ℝ) : ℝ :=
  let X := u * θ
  let Y := (1 - u) * (1 / 2)
  let B := 2 * Real.log θ + 2 * Real.log (1 / 2) + Real.log (u * (1 - u))
  ((X + Y) ^ 2 / (X * Y) * (B + -3 * Real.log (X + Y)) ^ n -
    X / Y * (B + -3 * Real.log X) ^ n - Y / X * (B + -3 * Real.log Y) ^ n -
    2 * (B + -3 * Real.log Y) ^ n + 3 * n * (B + -3 * Real.log Y) ^ (n - 1)) / (θ * (1 / 2))

theorem iteratedDeriv_i12TAIg {z : ℝ × ℝ} (hz : z ∈ i12Sq) (n : ℕ) :
    iteratedDeriv n (fun ε => i12TAIg ε z) 0 = i12TAd n z.1 z.2 := by
  obtain ⟨θ, u⟩ := z
  obtain ⟨⟨hθ0, hθ1⟩, ⟨hu0, hu1⟩⟩ := hz
  simp only at hθ0 hθ1 hu0 hu1
  have hX : 0 < u * θ := mul_pos hu0 hθ0
  have hY : 0 < (1 - u) * (1 / 2 : ℝ) := by nlinarith
  have hw : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hh : 0 < (1 / 2 : ℝ) := by norm_num
  have hS : 0 < u * θ + (1 - u) * (1 / 2 : ℝ) := by linarith
  set B := 2 * Real.log θ + 2 * Real.log (1 / 2) + Real.log (u * (1 - u)) with hB
  have hfun : (fun ε => i12TAIg ε (θ, u)) = fun ε =>
      ((u * θ + (1 - u) * (1 / 2)) ^ 2 / (u * θ * ((1 - u) * (1 / 2))) / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log (u * θ + (1 - u) * (1 / 2)) : ℝ) : ℂ) * ε) +
        (-(u * θ / ((1 - u) * (1 / 2))) / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log (u * θ) : ℝ) : ℂ) * ε) +
        (-((1 - u) * (1 / 2) / (u * θ)) / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log ((1 - u) * (1 / 2)) : ℝ) : ℂ) * ε) +
        (-2 / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log ((1 - u) * (1 / 2)) : ℝ) : ℂ) * ε) +
        (3 / (θ * (1 / 2)) : ℝ) *
          (ε * exp (((B + -3 * Real.log ((1 - u) * (1 / 2)) : ℝ) : ℂ) * ε)) := by
    funext ε
    simp only [i12TAIg, i12GA, i12GA0, i12Phi0, i12H_zero]
    simp only [zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
    rw [i12_cpow_two_mul_sub_one hθ0, i12_cpow_two_mul_sub_one hh, i12_cpow_self hw,
      i12_cpow_two_sub_three_mul hS, i12_cpow_two_sub_three_mul hX,
      i12_cpow_two_sub_three_mul hY, i12_cpow_neg_three_mul hY]
    simp only [hB, i12_exp_add_mul]
    have hX' : ((u * θ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
    have hY' : (((1 - u) * (1 / 2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
    have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ0.ne'
    push_cast at hX' hY' ⊢
    field_simp
    ring
  rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_mul_exp_zero, i12TAd, hB]
  push_cast
  ring

/-- The pointwise `n`-th `ε`-derivative at `0` of the integrand of `T_B`. With `X = u`,
`Y = (1 - u)θ/2`, `B = 2 log θ - 2 log 2 + log(u(1 - u))`, `λ(x) = B - 3 log x`:
`(2/θ) [(X + Y)²/(XY) λ(X + Y)ⁿ - (X/Y) λ(X)ⁿ - (Y/X) λ(Y)ⁿ - 2 λ(X)ⁿ + 3n λ(X)ⁿ⁻¹]`. -/
noncomputable def i12TBd (n : ℕ) (θ u : ℝ) : ℝ :=
  let X := u
  let Y := (1 - u) * θ * (1 / 2)
  let B := 2 * Real.log θ + 2 * Real.log (1 / 2) + Real.log (u * (1 - u))
  ((X + Y) ^ 2 / (X * Y) * (B + -3 * Real.log (X + Y)) ^ n -
    X / Y * (B + -3 * Real.log X) ^ n - Y / X * (B + -3 * Real.log Y) ^ n -
    2 * (B + -3 * Real.log X) ^ n + 3 * n * (B + -3 * Real.log X) ^ (n - 1)) / (θ * (1 / 2))

theorem iteratedDeriv_i12TBIg {z : ℝ × ℝ} (hz : z ∈ i12Sq) (n : ℕ) :
    iteratedDeriv n (fun ε => i12TBIg ε z) 0 = i12TBd n z.1 z.2 := by
  obtain ⟨θ, u⟩ := z
  obtain ⟨⟨hθ0, hθ1⟩, ⟨hu0, hu1⟩⟩ := hz
  simp only at hθ0 hθ1 hu0 hu1
  have hX : 0 < u := hu0
  have hY : 0 < (1 - u) * θ * (1 / 2 : ℝ) := by
    have := mul_pos (sub_pos.mpr hu1) hθ0; linarith
  have hw : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hh : 0 < (1 / 2 : ℝ) := by norm_num
  have hS : 0 < u + (1 - u) * θ * (1 / 2 : ℝ) := by linarith
  set B := 2 * Real.log θ + 2 * Real.log (1 / 2) + Real.log (u * (1 - u)) with hB
  have hfun : (fun ε => i12TBIg ε (θ, u)) = fun ε =>
      ((u + (1 - u) * θ * (1 / 2)) ^ 2 / (u * ((1 - u) * θ * (1 / 2))) / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log (u + (1 - u) * θ * (1 / 2)) : ℝ) : ℂ) * ε) +
        (-(u / ((1 - u) * θ * (1 / 2))) / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log u : ℝ) : ℂ) * ε) +
        (-((1 - u) * θ * (1 / 2) / u) / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log ((1 - u) * θ * (1 / 2)) : ℝ) : ℂ) * ε) +
        (-2 / (θ * (1 / 2)) : ℝ) *
          exp (((B + -3 * Real.log u : ℝ) : ℂ) * ε) +
        (3 / (θ * (1 / 2)) : ℝ) *
          (ε * exp (((B + -3 * Real.log u : ℝ) : ℂ) * ε)) := by
    funext ε
    simp only [i12TBIg, i12GB, i12GB0, i12Phi0, i12H_zero]
    simp only [zero_mul, i12H_zero, sub_zero, ofReal_one, one_cpow, mul_one]
    rw [i12_cpow_two_mul_sub_one hθ0, i12_cpow_two_mul_sub_one hh, i12_cpow_self hw,
      i12_cpow_two_sub_three_mul hS, i12_cpow_two_sub_three_mul hX,
      i12_cpow_two_sub_three_mul hY, i12_cpow_neg_three_mul hX]
    simp only [hB, i12_exp_add_mul]
    have hX' : ((u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
    have hY' : (((1 - u) * θ * (1 / 2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
    have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ0.ne'
    push_cast at hX' hY' ⊢
    field_simp
    ring
  rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_mul_exp_zero, i12TBd, hB]
  push_cast
  ring

/-- The pointwise `n`-th `ε`-derivative at `0` of the integrand of `R_A`: ten terms
`C λⁿ` or `C n λⁿ⁻¹`, one for each exponential `C e^{λε}` or `C ε e^{λε}` of the integrand
(`X = uθ`, `Y = (1 - u) h(ρ)`, `Y₀ = (1 - u) h(0)`). -/
noncomputable def i12RA3Dn (n : ℕ) (ρ θ u : ℝ) : ℝ :=
  ((u * θ + (1 - u) * i12H ρ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ)) *
      (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) +
      -Real.log (1 - ρ * θ) + -3 * Real.log (u * θ + (1 - u) * i12H ρ)) ^ n +
    (-(u * θ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ)) * (Real.log ρ + 2 *
        Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) + -Real.log (1 - ρ * θ) + -3 *
        Real.log (u * θ)) ^ n +
    (-((1 - u) * i12H ρ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ)) * (Real.log ρ +
        2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) + -Real.log (1 - ρ * θ) +
        -3 * Real.log ((1 - u) * i12H ρ)) ^ n +
    (-(u * θ + (1 - u) * i12H 0) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ)) *
        (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 *
        Real.log (u * θ + (1 - u) * i12H 0)) ^ n +
    ((u * θ) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 *
        Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log (u * θ)) ^ n +
    (((1 - u) * i12H 0) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ)) * (Real.log ρ +
        2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log ((1 - u) *
        i12H 0)) ^ n +
    (-2 / (i12H ρ) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H ρ) + -3 * Real.log ((1 - u) * i12H ρ)) ^ n +
    (3 / (i12H ρ) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H ρ) + -3 * Real.log ((1 - u) * i12H ρ)) ^ (n - 1)) +
    (2 / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log ((1 - u) * i12H 0)) ^ n +
    (-3 / (i12H 0) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log ((1 - u) * i12H 0)) ^ (n - 1))

theorem iteratedDeriv_i12RA3Ig {z : ℝ × ℝ × ℝ} (hz : z ∈ i12Cube) (n : ℕ) :
    iteratedDeriv n (fun ε => i12RA3Ig ε z) 0 = i12RA3Dn n z.1 z.2.1 z.2.2 := by
  obtain ⟨ρ, θ, u⟩ := z
  obtain ⟨⟨hρ0, hρ1⟩, ⟨hθ0, hθ1⟩, ⟨hu0, hu1⟩⟩ := hz
  simp only at hρ0 hρ1 hθ0 hθ1 hu0 hu1
  have hh : 0 < i12H ρ := i12H_pos (by linarith)
  have hh0 : 0 < i12H 0 := i12H_pos (by norm_num)
  have hw : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hX : 0 < u * θ := mul_pos hu0 hθ0
  have hY1 : 0 < (1 - u) * i12H ρ := mul_pos (by linarith) hh
  have hY0 : 0 < (1 - u) * i12H 0 := mul_pos (by linarith) hh0
  have hS1 : 0 < u * θ + (1 - u) * i12H ρ := by linarith
  have hS0 : 0 < u * θ + (1 - u) * i12H 0 := by linarith
  have hρθ : 0 < 1 - ρ * θ := by nlinarith
  have hX' : ((u * θ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY1' : (((1 - u) * i12H ρ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY1.ne'
  have hY0' : (((1 - u) * i12H 0 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY0.ne'
  have hh' : ((i12H ρ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  have hh0' : ((i12H 0 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh0.ne'
  have hρ' : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ0.ne'
  have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ0.ne'
  have hfun : (fun ε => i12RA3Ig ε (ρ, θ, u)) = fun ε =>
      (((u * θ + (1 - u) * i12H ρ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ *
          θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
          Real.log (i12H ρ) + -Real.log (1 - ρ * θ) + -3 * Real.log (u * θ + (1 - u) *
          i12H ρ) : ℝ) : ℂ) * ε) +
        ((-(u * θ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ) : ℝ) : ℂ) *
            exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) +
            -Real.log (1 - ρ * θ) + -3 * Real.log (u * θ) : ℝ) : ℂ) * ε) +
        ((-((1 - u) * i12H ρ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ) : ℝ) : ℂ) *
            exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) +
            -Real.log (1 - ρ * θ) + -3 * Real.log ((1 - u) * i12H ρ) : ℝ) : ℂ) * ε) +
        ((-(u * θ + (1 - u) * i12H 0) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ *
            θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
            Real.log (i12H 0) + -3 * Real.log (u * θ + (1 - u) * i12H 0) : ℝ) : ℂ) * ε) +
        (((u * θ) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ) : ℝ) : ℂ) *
            exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) +
            -3 * Real.log (u * θ) : ℝ) : ℂ) * ε) +
        ((((1 - u) * i12H 0) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ) : ℝ) : ℂ) *
            exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) +
            -3 * Real.log ((1 - u) * i12H 0) : ℝ) : ℂ) * ε) +
        ((-2 / (i12H ρ) / (ρ * θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u *
            (1 - u)) + 2 * Real.log (i12H ρ) + -3 * Real.log ((1 - u) * i12H ρ) : ℝ) : ℂ) * ε) +
        ((3 / (i12H ρ) / (ρ * θ) : ℝ) : ℂ) * (ε * exp (((Real.log ρ + 2 * Real.log θ +
            Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) + -3 * Real.log ((1 - u) *
            i12H ρ) : ℝ) : ℂ) * ε)) +
        ((2 / (i12H 0) / (ρ * θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u *
            (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log ((1 - u) * i12H 0) : ℝ) : ℂ) * ε) +
        ((-3 / (i12H 0) / (ρ * θ) : ℝ) : ℂ) * (ε * exp (((Real.log ρ + 2 * Real.log θ +
            Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log ((1 - u) *
            i12H 0) : ℝ) : ℂ) * ε)) := by
    funext ε
    simp only [i12RA3Ig, i12SecWt, i12GA, i12GA0, i12Phi0]
    simp only [zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
    rw [i12_cpow_sub_one hρ0, i12_cpow_two_mul_sub_one hθ0, i12_cpow_two_mul_sub_one hh,
        i12_cpow_two_mul_sub_one hh0, i12_cpow_neg_self hρθ, i12_cpow_self hw,
        i12_cpow_two_sub_three_mul hS1, i12_cpow_two_sub_three_mul hS0,
        i12_cpow_two_sub_three_mul hX, i12_cpow_two_sub_three_mul hY1,
        i12_cpow_two_sub_three_mul hY0, i12_cpow_neg_three_mul hY1, i12_cpow_neg_three_mul hY0]
    simp only [i12_exp_add_mul]
    push_cast at hX' hY1' hY0' hh' hh0' ⊢
    field_simp
    ring
  rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
        i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
        i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_mul_exp_zero, i12_iteratedDeriv_exp_zero,
        i12_iteratedDeriv_mul_exp_zero, i12RA3Dn]
  push_cast
  ring

/-- The pointwise `n`-th `ε`-derivative at `0` of the integrand of `R_B`: ten terms
`C λⁿ` or `C n λⁿ⁻¹`, one for each exponential `C e^{λε}` or `C ε e^{λε}` of the integrand
(`X = u`, `Y = (1 - u) θ h(ρθ)`, `Y₀ = (1 - u) θ h(0)`). -/
noncomputable def i12RB3Dn (n : ℕ) (ρ θ u : ℝ) : ℝ :=
  ((u + (1 - u) * θ * i12H (ρ * θ)) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) /
      (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ *
      θ)) + -Real.log (1 - ρ) + -3 * Real.log (u + (1 - u) * θ * i12H (ρ * θ))) ^ n +
    (-(u) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) / (ρ * θ)) * (Real.log ρ + 2 *
        Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) +
        -3 * Real.log (u)) ^ n +
    (-((1 - u) * θ * i12H (ρ * θ)) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) /
        (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ *
        θ)) + -Real.log (1 - ρ) + -3 * Real.log ((1 - u) * θ * i12H (ρ * θ))) ^ n +
    (-(u + (1 - u) * θ * i12H 0) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ)) *
        (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 *
        Real.log (u + (1 - u) * θ * i12H 0)) ^ n +
    ((u) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ +
        Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log (u)) ^ n +
    (((1 - u) * θ * i12H 0) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ)) *
        (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 *
        Real.log ((1 - u) * θ * i12H 0)) ^ n +
    (-2 / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -Real.log (1 - ρ) + -3 * Real.log (u)) ^ n +
    (3 / (i12H 0) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -Real.log (1 - ρ) + -3 * Real.log (u)) ^ (n - 1)) +
    (2 / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log (u)) ^ n +
    (-3 / (i12H 0) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log (u)) ^ (n - 1))

theorem iteratedDeriv_i12RB3Ig {z : ℝ × ℝ × ℝ} (hz : z ∈ i12Cube) (n : ℕ) :
    iteratedDeriv n (fun ε => i12RB3Ig ε z) 0 = i12RB3Dn n z.1 z.2.1 z.2.2 := by
  obtain ⟨ρ, θ, u⟩ := z
  obtain ⟨⟨hρ0, hρ1⟩, ⟨hθ0, hθ1⟩, ⟨hu0, hu1⟩⟩ := hz
  simp only at hρ0 hρ1 hθ0 hθ1 hu0 hu1
  have hh : 0 < i12H (ρ * θ) := i12H_pos (by nlinarith)
  have hh0 : 0 < i12H 0 := i12H_pos (by norm_num)
  have hw : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hX : 0 < u := hu0
  have hY1 : 0 < (1 - u) * θ * i12H (ρ * θ) := mul_pos (mul_pos (by linarith) hθ0) hh
  have hY0 : 0 < (1 - u) * θ * i12H 0 := mul_pos (mul_pos (by linarith) hθ0) hh0
  have hS1 : 0 < u + (1 - u) * θ * i12H (ρ * θ) := by linarith
  have hS0 : 0 < u + (1 - u) * θ * i12H 0 := by linarith
  have hρ1' : 0 < 1 - ρ := by linarith
  have hX' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY1' : (((1 - u) * θ * i12H (ρ * θ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY1.ne'
  have hY0' : (((1 - u) * θ * i12H 0 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY0.ne'
  have hh' : ((i12H (ρ * θ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  have hh0' : ((i12H 0 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh0.ne'
  have hρ' : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ0.ne'
  have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ0.ne'
  have hfun : (fun ε => i12RB3Ig ε (ρ, θ, u)) = fun ε =>
      (((u + (1 - u) * θ * i12H (ρ * θ)) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ *
          θ)) / (ρ * θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) +
          2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) + -3 * Real.log (u + (1 - u) * θ *
          i12H (ρ * θ)) : ℝ) : ℂ) * ε) +
        ((-(u) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) / (ρ * θ) : ℝ) : ℂ) *
            exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ *
            θ)) + -Real.log (1 - ρ) + -3 * Real.log (u) : ℝ) : ℂ) * ε) +
        ((-((1 - u) * θ * i12H (ρ * θ)) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ *
            θ)) / (ρ * θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u *
            (1 - u)) + 2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) + -3 * Real.log ((1 - u) *
            θ * i12H (ρ * θ)) : ℝ) : ℂ) * ε) +
        ((-(u + (1 - u) * θ * i12H 0) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ *
            θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
            Real.log (i12H 0) + -3 * Real.log (u + (1 - u) * θ * i12H 0) : ℝ) : ℂ) * ε) +
        (((u) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ) : ℝ) : ℂ) *
            exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) +
            -3 * Real.log (u) : ℝ) : ℂ) * ε) +
        ((((1 - u) * θ * i12H 0) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ *
            θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
            Real.log (i12H 0) + -3 * Real.log ((1 - u) * θ * i12H 0) : ℝ) : ℂ) * ε) +
        ((-2 / (i12H 0) / (ρ * θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u *
            (1 - u)) + 2 * Real.log (i12H 0) + -Real.log (1 - ρ) + -3 * Real.log (u) : ℝ) : ℂ) *
            ε) +
        ((3 / (i12H 0) / (ρ * θ) : ℝ) : ℂ) * (ε * exp (((Real.log ρ + 2 * Real.log θ +
            Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -Real.log (1 - ρ) + -3 *
            Real.log (u) : ℝ) : ℂ) * ε)) +
        ((2 / (i12H 0) / (ρ * θ) : ℝ) : ℂ) * exp (((Real.log ρ + 2 * Real.log θ + Real.log (u *
            (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log (u) : ℝ) : ℂ) * ε) +
        ((-3 / (i12H 0) / (ρ * θ) : ℝ) : ℂ) * (ε * exp (((Real.log ρ + 2 * Real.log θ +
            Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log (u) : ℝ) : ℂ) * ε)) := by
    funext ε
    simp only [i12RB3Ig, i12SecWt, i12GB, i12GB0, i12Phi0]
    simp only [zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
    rw [i12_cpow_sub_one hρ0, i12_cpow_two_mul_sub_one hθ0, i12_cpow_two_mul_sub_one hh,
        i12_cpow_two_mul_sub_one hh0, i12_cpow_neg_self hρ1', i12_cpow_self hw,
        i12_cpow_two_sub_three_mul hS1, i12_cpow_two_sub_three_mul hS0,
        i12_cpow_two_sub_three_mul hX, i12_cpow_two_sub_three_mul hY1,
        i12_cpow_two_sub_three_mul hY0, i12_cpow_neg_three_mul hX]
    simp only [i12_exp_add_mul]
    push_cast at hX' hY1' hY0' hh' hh0' ⊢
    field_simp
    ring
  rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
        i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
        i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_mul_exp_zero, i12_iteratedDeriv_exp_zero,
        i12_iteratedDeriv_mul_exp_zero, i12RB3Dn]
  push_cast
  ring

/-- **The `n`-th derivative of `T_A` at `0` as an explicit integral.** -/
theorem iteratedDeriv_i12TA_eq_integral (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (i12TAd n z.1 z.2 : ℂ)) (volume.restrict i12Sq) ∧
      iteratedDeriv n i12TA 0 = ∫ z in i12Sq, (i12TAd n z.1 z.2 : ℂ) := by
  obtain ⟨hI, hE⟩ := iteratedDeriv_i12TA_eq n
  refine ⟨hI.congr (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz =>
    iteratedDeriv_i12TAIg hz n), hE.trans (setIntegral_congr_fun i12_measurableSet2
      fun z hz => iteratedDeriv_i12TAIg hz n)⟩

/-- **The `n`-th derivative of `T_B` at `0` as an explicit integral.** -/
theorem iteratedDeriv_i12TB_eq_integral (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (i12TBd n z.1 z.2 : ℂ)) (volume.restrict i12Sq) ∧
      iteratedDeriv n i12TB 0 = ∫ z in i12Sq, (i12TBd n z.1 z.2 : ℂ) := by
  obtain ⟨hI, hE⟩ := iteratedDeriv_i12TB_eq n
  refine ⟨hI.congr (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz =>
    iteratedDeriv_i12TBIg hz n), hE.trans (setIntegral_congr_fun i12_measurableSet2
      fun z hz => iteratedDeriv_i12TBIg hz n)⟩

/-- The pointwise `n`-th `ε`-derivative at `0` of the integrand of `R₁`. With `c = y(1 - y)`,
`X = ut`, `Y = (1 - u)c`, `S = X + Y`, `N = S - XY`, `B = 2 log(ct) - log(1 - t) + log(u(1 - u))`,
`λ(x) = B - 3 log x`: `(1/(ct)) [N²/(XY) λ(N)ⁿ - S²/(XY) λ(S)ⁿ + X (2 λ(X)ⁿ - 3n λ(X)ⁿ⁻¹)
+ Y (2 λ(Y)ⁿ - 3n λ(Y)ⁿ⁻¹)]`. -/
noncomputable def i12R1Dn (n : ℕ) (y t u : ℝ) : ℝ :=
  let c := y * (1 - y)
  let X := u * t
  let Y := (1 - u) * c
  let B := 2 * Real.log (c * t) + -Real.log (1 - t) + Real.log (u * (1 - u))
  ((X + Y - X * Y) ^ 2 / (X * Y) * (B + -3 * Real.log (X + Y - X * Y)) ^ n -
    (X + Y) ^ 2 / (X * Y) * (B + -3 * Real.log (X + Y)) ^ n +
    X * (2 * (B + -3 * Real.log X) ^ n - 3 * n * (B + -3 * Real.log X) ^ (n - 1)) +
    Y * (2 * (B + -3 * Real.log Y) ^ n - 3 * n * (B + -3 * Real.log Y) ^ (n - 1))) / (c * t)

theorem iteratedDeriv_i12R1Ig {z : ℝ × ℝ × ℝ} (hz : z ∈ i12Cube) (n : ℕ) :
    iteratedDeriv n (fun ε => i12R1Ig ε z) 0 = i12R1Dn n z.1 z.2.1 z.2.2 := by
  obtain ⟨y, t, u⟩ := z
  obtain ⟨⟨hy0, hy1⟩, ⟨ht0, ht1⟩, ⟨hu0, hu1⟩⟩ := hz
  simp only at hy0 hy1 ht0 ht1 hu0 hu1
  have hc : 0 < y * (1 - y) := mul_pos hy0 (by linarith)
  have hct : 0 < y * (1 - y) * t := mul_pos hc ht0
  have h1t : 0 < 1 - t := by linarith
  have hw : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hX : 0 < u * t := mul_pos hu0 ht0
  have hY : 0 < (1 - u) * (y * (1 - y)) := mul_pos (by linarith) hc
  have hX1 : u * t < 1 := by nlinarith
  have hS : 0 < u * t + (1 - u) * (y * (1 - y)) := by linarith
  have hN : 0 < u * t + (1 - u) * (y * (1 - y)) - u * t * ((1 - u) * (y * (1 - y))) := by
    nlinarith
  set B := 2 * Real.log (y * (1 - y) * t) + -Real.log (1 - t) + Real.log (u * (1 - u))
    with hB
  set X := u * t with hXd
  set Y := (1 - u) * (y * (1 - y)) with hYd
  set c := y * (1 - y) with hcd
  have hfun : (fun ε => i12R1Ig ε (y, t, u)) = fun ε =>
      ((X + Y - X * Y) ^ 2 / (X * Y) / (c * t) : ℝ) *
          exp (((B + -3 * Real.log (X + Y - X * Y) : ℝ) : ℂ) * ε) +
        (-((X + Y) ^ 2 / (X * Y)) / (c * t) : ℝ) *
          exp (((B + -3 * Real.log (X + Y) : ℝ) : ℂ) * ε) +
        (2 * X / (c * t) : ℝ) * exp (((B + -3 * Real.log X : ℝ) : ℂ) * ε) +
        (-3 * X / (c * t) : ℝ) * (ε * exp (((B + -3 * Real.log X : ℝ) : ℂ) * ε)) +
        (2 * Y / (c * t) : ℝ) * exp (((B + -3 * Real.log Y : ℝ) : ℂ) * ε) +
        (-3 * Y / (c * t) : ℝ) * (ε * exp (((B + -3 * Real.log Y : ℝ) : ℂ) * ε)) := by
    funext ε
    simp only [i12R1Ig, i12Wt, i12Phi1]
    simp only [← hcd]
    simp only [← hYd, ← hXd]
    rw [i12_cpow_two_mul_sub_one hct, i12_cpow_neg_self h1t, i12_cpow_self hw,
      i12_cpow_two_sub_three_mul hN, i12_cpow_two_sub_three_mul hS,
      i12_cpow_one_sub_three_mul hX, i12_cpow_one_sub_three_mul hY]
    simp only [hB, i12_exp_add_mul]
    have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
    have hY' : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
    have hct' : ((c * t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hct.ne'
    push_cast at hX' hY' hct' ⊢
    field_simp
    ring
  rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
    i12_iteratedDeriv_mul_exp_zero, i12_iteratedDeriv_exp_zero,
    i12_iteratedDeriv_mul_exp_zero, i12R1Dn, hB]
  dsimp only
  simp only [← hcd]
  simp only [← hYd, ← hXd]
  have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY' : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  push_cast
  field_simp
  ring

/-- **The `n`-th derivative of `R1` at `0` as an explicit integral.** -/
theorem iteratedDeriv_i12R1_eq_integral (n : ℕ) :
    Integrable (fun z : ℝ × ℝ × ℝ => (i12R1Dn n z.1 z.2.1 z.2.2 : ℂ)) (volume.restrict i12Cube) ∧
      iteratedDeriv n i12R1 0 = ∫ z in i12Cube, (i12R1Dn n z.1 z.2.1 z.2.2 : ℂ) := by
  obtain ⟨hI, hE⟩ := iteratedDeriv_i12R1_eq n
  refine ⟨hI.congr (ae_restrict_of_forall_mem i12_measurableSet3 fun z hz =>
    iteratedDeriv_i12R1Ig hz n), hE.trans (setIntegral_congr_fun i12_measurableSet3
      fun z hz => iteratedDeriv_i12R1Ig hz n)⟩

/-- **The `n`-th derivative of `RA3` at `0` as an explicit integral.** -/
theorem iteratedDeriv_i12RA3_eq_integral (n : ℕ) :
    Integrable (fun z : ℝ × ℝ × ℝ => (i12RA3Dn n z.1 z.2.1 z.2.2 : ℂ)) (volume.restrict i12Cube) ∧
      iteratedDeriv n i12RA3 0 = ∫ z in i12Cube, (i12RA3Dn n z.1 z.2.1 z.2.2 : ℂ) := by
  obtain ⟨hI, hE⟩ := iteratedDeriv_i12RA3_eq n
  refine ⟨hI.congr (ae_restrict_of_forall_mem i12_measurableSet3 fun z hz =>
    iteratedDeriv_i12RA3Ig hz n), hE.trans (setIntegral_congr_fun i12_measurableSet3
      fun z hz => iteratedDeriv_i12RA3Ig hz n)⟩

/-- **The `n`-th derivative of `RB3` at `0` as an explicit integral.** -/
theorem iteratedDeriv_i12RB3_eq_integral (n : ℕ) :
    Integrable (fun z : ℝ × ℝ × ℝ => (i12RB3Dn n z.1 z.2.1 z.2.2 : ℂ)) (volume.restrict i12Cube) ∧
      iteratedDeriv n i12RB3 0 = ∫ z in i12Cube, (i12RB3Dn n z.1 z.2.1 z.2.2 : ℂ) := by
  obtain ⟨hI, hE⟩ := iteratedDeriv_i12RB3_eq n
  refine ⟨hI.congr (ae_restrict_of_forall_mem i12_measurableSet3 fun z hz =>
    iteratedDeriv_i12RB3Ig hz n), hE.trans (setIntegral_congr_fun i12_measurableSet3
      fun z hz => iteratedDeriv_i12RB3Ig hz n)⟩

/-- **Every Taylor coefficient of the remainder as five explicit integrals**:
`i12Rest⁽ⁿ⁺¹⁾(0) = (n + 1) (∫ D₁ⁿ + ∫ D_Aⁿ + ∫ D_Bⁿ) + ∫ T_Aⁿ⁺¹ + ∫ T_Bⁿ⁺¹`, with the
integrands polynomials of degree `n` (resp. `n + 1`) in logarithms of the integration
variables, with rational coefficients. -/
theorem iteratedDeriv_succ_i12Rest_eq_explicit (n : ℕ) :
    iteratedDeriv (n + 1) i12Rest 0 =
      (n + 1) * ((∫ z in i12Cube, (i12R1Dn n z.1 z.2.1 z.2.2 : ℂ)) +
        (∫ z in i12Cube, (i12RA3Dn n z.1 z.2.1 z.2.2 : ℂ)) +
        ∫ z in i12Cube, (i12RB3Dn n z.1 z.2.1 z.2.2 : ℂ)) +
      (∫ z in i12Sq, (i12TAd (n + 1) z.1 z.2 : ℂ)) +
      ∫ z in i12Sq, (i12TBd (n + 1) z.1 z.2 : ℂ) := by
  rw [iteratedDeriv_succ_i12Rest, (iteratedDeriv_i12R1_eq_integral n).2,
    (iteratedDeriv_i12RA3_eq_integral n).2, (iteratedDeriv_i12RB3_eq_integral n).2,
    (iteratedDeriv_i12TA_eq_integral (n + 1)).2, (iteratedDeriv_i12TB_eq_integral (n + 1)).2]

end QED.ThreeLoopD
