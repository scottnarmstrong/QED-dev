/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15Analytic
public import QED.ThreeLoopD.SetDMastersI9RemTaylor
public import QED.ThreeLoopD.SetDMastersI15Gamma

/-!
# Set (d), master `I₁₅`: the Taylor coefficients of `K` to order `ε⁴` as real integrals

With `c = x(1 - x)`, `P = c (1 - u)² + u` and the logarithms `Lc, Lu, LP`, the integrand of
`QED.ThreeLoopD.i15K` is, at each point of the open square, a sum of three exponentials in `ε`:

  `c ^ (ε - 1) u ^ (ε - 1) Ψ = (c u)⁻¹ (P e ^ (ε b₁) - u e ^ (ε b₂) - c e ^ (-ε b₂))`,

`b₁ = Lc + Lu - 2 LP`, `b₂ = Lc - Lu`. The expansion
`e ^ t = Σ_{k < 5} tᵏ / k! + t⁵ E₅(t)` (`QED.ThreeLoopD.exp_eq_i15E5`, `E₅` entire) writes it as
`Σ_{k < 5} εᵏ Fₖ + ε⁵ G(ε)` with

  `Fₖ = (P b₁ᵏ - u b₂ᵏ - c (-b₂)ᵏ) / (k! c u)`  (`QED.ThreeLoopD.i15F`).

A Cauchy-type estimate by the maximum modulus principle
(`QED.ThreeLoopD.i15_taylor_bound`), against `QED.ThreeLoopD.norm_i15K_integrand_le` on the
circle `‖ε‖ = 1/25`, dominates every `Fₖ` and `G(ε)` by multiples of one integrable function.
Hence `K(ε) = Σ_{k < 5} εᵏ ∫ Fₖ + ε⁵ ∫ G(ε)` with `ε ↦ ∫ G(ε)` analytic at `0`.

## Main results

* `QED.ThreeLoopD.i15K_eq_taylor`: the decomposition for `‖ε‖ < 1/25`.
* `QED.ThreeLoopD.hasTruncLaurent_i15K_integrals`:
  `HasTruncLaurent i15K (fun ε => Σ_{k < 5} εᵏ ∫ Fₖ) 5`.
* `QED.ThreeLoopD.hasTruncLaurent_i15K_of_coeffs`: the target expansion of `K` from the values
  of `∫ F₁, …, ∫ F₄` (`∫ F₀ = -3/2` is `QED.ThreeLoopD.integral_i15F_zero`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric QED.DimReg Filter Topology

namespace QED.ThreeLoopD

/-! ### The entire function `E₅` -/

/-- `E₅(t) = ∫₀¹ (1 - s)⁴/24 e ^ (t s) ds`, so that `e ^ t = Σ_{k < 5} tᵏ/k! + t⁵ E₅(t)`. -/
noncomputable def i15E5 (t : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, (((1 - s) ^ 4 / 24 : ℝ) : ℂ) * cexp (t * s)

theorem exp_eq_i15E5 (t : ℂ) :
    cexp t = 1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 * i15E5 t := by
  have hG : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ =>
      (t ^ 4 * (((1 - s) ^ 4 / 24 : ℝ) : ℂ) + t ^ 3 * (((1 - s) ^ 3 / 6 : ℝ) : ℂ) +
        t ^ 2 * (((1 - s) ^ 2 / 2 : ℝ) : ℂ) + t * ((1 - s : ℝ) : ℂ) + 1) * cexp (t * s))
      (t ^ 5 * ((((1 - s) ^ 4 / 24 : ℝ) : ℂ) * cexp (t * s))) s := by
    intro s _
    have h4 : HasDerivAt (fun s : ℝ => (((1 - s) ^ 4 / 24 : ℝ) : ℂ))
        ((-((1 - s) ^ 3 / 6) : ℝ) : ℂ) s := by
      have := (((hasDerivAt_id s).const_sub 1).pow 4).div_const 24
      exact (this.congr_deriv (by simp; ring)).ofReal_comp
    have h3 : HasDerivAt (fun s : ℝ => (((1 - s) ^ 3 / 6 : ℝ) : ℂ))
        ((-((1 - s) ^ 2 / 2) : ℝ) : ℂ) s := by
      have := (((hasDerivAt_id s).const_sub 1).pow 3).div_const 6
      exact (this.congr_deriv (by simp; ring)).ofReal_comp
    have hq : HasDerivAt (fun s : ℝ => (((1 - s) ^ 2 / 2 : ℝ) : ℂ)) ((-(1 - s) : ℝ) : ℂ) s := by
      have := (((hasDerivAt_id s).const_sub 1).pow 2).div_const 2
      exact (this.congr_deriv (by simp; ring)).ofReal_comp
    have hl : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) s :=
      (((hasDerivAt_id s).const_sub 1).congr_deriv (by simp)).ofReal_comp
    have hs : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) ((1 : ℝ) : ℂ) s :=
      (hasDerivAt_id s).ofReal_comp
    have he := (hs.const_mul t).cexp
    convert (((((h4.const_mul (t ^ 4)).add (h3.const_mul (t ^ 3))).add
      (hq.const_mul (t ^ 2))).add (hl.const_mul t)).add_const 1).mul he using 1
    simp only [Pi.add_apply]
    push_cast
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_const_mul] at hint
  unfold i15E5
  rw [hint]
  push_cast
  simp
  ring

theorem differentiable_i15E5 : Differentiable ℂ i15E5 := by
  intro t₁
  have e : i15E5 = fun t =>
      ∫ s in Ioc (0 : ℝ) 1, (((1 - s) ^ 4 / 24 : ℝ) : ℂ) * cexp (t * s) := by
    funext t
    exact intervalIntegral.integral_of_le zero_le_one
  rw [e]
  refine differentiableAt_integral_of_holomorphic (z₁ := t₁) one_pos
    (b := fun _ => Real.exp (‖t₁‖ + 1)) (integrable_const _)
    (fun t _ => (by fun_prop : Continuous fun s : ℝ =>
      (((1 - s) ^ 4 / 24 : ℝ) : ℂ) * cexp (t * s)).aestronglyMeasurable) ?_
    (ae_of_all _ fun s => (by fun_prop : Differentiable ℂ fun t : ℂ =>
      (((1 - s) ^ 4 / 24 : ℝ) : ℂ) * cexp (t * s)).differentiableOn)
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs t ht => ?_
  rw [mem_ball, dist_eq_norm] at ht
  have ht' : ‖t‖ < ‖t₁‖ + 1 := by linarith [norm_sub_norm_le t t₁]
  have h0 : 0 ≤ 1 - s := by linarith [hs.2]
  have h1' : 1 - s ≤ 1 := by linarith [hs.1]
  have h1 : |(1 - s) ^ 4 / 24| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have : (1 - s) ^ 4 ≤ 1 := pow_le_one₀ h0 h1'
    linarith
  have h2 : ‖cexp (t * s)‖ ≤ Real.exp (‖t₁‖ + 1) := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    nlinarith [norm_nonneg t, hs.2]
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  calc _ ≤ 1 * Real.exp (‖t₁‖ + 1) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

attribute [fun_prop] differentiable_i15E5

@[fun_prop]
theorem measurable_i15E5 : Measurable i15E5 := differentiable_i15E5.continuous.measurable

/-! ### A Cauchy-type estimate by the maximum modulus principle -/

/-- If `Σ_{k < n} εᵏ Fₖ + εⁿ G(ε)` is bounded by `b` on the circle `‖ε‖ = ρ`, `G` entire, then
`‖Fₖ‖ ≤ 2ᵏ b / ρᵏ` and `‖G‖ ≤ 2ⁿ b / ρⁿ` on the closed disc. -/
theorem i15_taylor_bound (n : ℕ) :
    ∀ (F : ℕ → ℂ) (G : ℂ → ℂ), Differentiable ℂ G → ∀ {ρ b : ℝ}, 0 < ρ →
      (∀ ε : ℂ, ‖ε‖ = ρ → ‖(∑ k ∈ Finset.range n, ε ^ k * F k) + ε ^ n * G ε‖ ≤ b) →
      (∀ k < n, ‖F k‖ ≤ 2 ^ k * b / ρ ^ k) ∧
        ∀ ε : ℂ, ‖ε‖ ≤ ρ → ‖G ε‖ ≤ 2 ^ n * b / ρ ^ n := by
  induction n with
  | zero =>
    intro F G hG ρ b hρ hf
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun ε hε => ?_⟩
    simp only [pow_zero, one_mul, div_one]
    exact i9_norm_le_of_sphere hG hρ (fun ε hε => by simpa using hf ε hε) hε
  | succ n ih =>
    intro F G hG ρ b hρ hf
    set H : ℂ → ℂ := fun ε => (∑ k ∈ Finset.range n, ε ^ k * F (k + 1)) + ε ^ n * G ε with hH
    have hHd : Differentiable ℂ H := by
      rw [hH]
      refine Differentiable.add ?_ (by fun_prop)
      exact Differentiable.fun_sum fun k _ => by fun_prop
    have he : ∀ ε : ℂ, (∑ k ∈ Finset.range (n + 1), ε ^ k * F k) + ε ^ (n + 1) * G ε =
        F 0 + ε * H ε := fun ε => by
      rw [Finset.sum_range_succ', hH]
      simp only [pow_succ, pow_zero, one_mul]
      rw [mul_add, Finset.mul_sum]
      have : ∀ k ∈ Finset.range n, ε ^ k * ε * F (k + 1) = ε * (ε ^ k * F (k + 1)) :=
        fun k _ => by ring
      rw [Finset.sum_congr rfl this]
      ring
    have h0 : ‖F 0‖ ≤ b := by
      have := i9_norm_le_of_sphere (h := fun ε => F 0 + ε * H ε) (by fun_prop) hρ (M := b)
        (fun ε hε => by rw [← he]; exact hf ε hε) (ε := 0) (by simp; exact hρ.le)
      simpa using this
    have hHb : ∀ ε : ℂ, ‖ε‖ = ρ → ‖H ε‖ ≤ 2 * b / ρ := fun ε hε => by
      rw [le_div_iff₀ hρ, ← hε, ← norm_mul, mul_comm]
      have e : ε * H ε = (F 0 + ε * H ε) - F 0 := by ring
      rw [e, ← he]
      refine (norm_sub_le _ _).trans ?_
      linarith [hf ε hε]
    obtain ⟨ihF, ihG⟩ := ih (fun k => F (k + 1)) G hG hρ hHb
    refine ⟨fun k hk => ?_, fun ε hε => (ihG ε hε).trans (le_of_eq ?_)⟩
    · rcases k with _ | k
      · simpa using h0
      · refine (ihF k (by omega)).trans (le_of_eq ?_)
        field_simp
        ring
    · field_simp
      ring

/-! ### The pointwise Taylor coefficients -/

/-- `P = c (1 - u)² + u`. -/
noncomputable abbrev i15P (x u : ℝ) : ℝ := i9Poly x u 1

/-- `b₁ = log c + log u - 2 log P`. -/
noncomputable def i15B1 (x u : ℝ) : ℝ :=
  Real.log (x * (1 - x)) + Real.log u - 2 * Real.log (i15P x u)

/-- `b₂ = log c - log u`. -/
noncomputable def i15B2 (x u : ℝ) : ℝ := Real.log (x * (1 - x)) - Real.log u

/-- **The `k`-th Taylor coefficient** `Fₖ = (P b₁ᵏ - u b₂ᵏ - c (-b₂)ᵏ) / (k! c u)`. -/
noncomputable def i15F (k : ℕ) (z : ℝ × ℝ) : ℝ :=
  (i15P z.1 z.2 * i15B1 z.1 z.2 ^ k - z.2 * i15B2 z.1 z.2 ^ k -
      z.1 * (1 - z.1) * (-i15B2 z.1 z.2) ^ k) /
    (k.factorial * (z.1 * (1 - z.1) * z.2))

/-- **The quintic remainder** `G(ε) = (c u)⁻¹ Σⱼ βⱼ bⱼ⁵ E₅(ε bⱼ)`. -/
noncomputable def i15G (ε : ℂ) (z : ℝ × ℝ) : ℂ :=
  ((z.1 * (1 - z.1) * z.2 : ℝ) : ℂ)⁻¹ *
    ((i15P z.1 z.2 : ℂ) * (i15B1 z.1 z.2 : ℂ) ^ 5 * i15E5 (ε * i15B1 z.1 z.2) -
      (z.2 : ℂ) * (i15B2 z.1 z.2 : ℂ) ^ 5 * i15E5 (ε * i15B2 z.1 z.2) -
      ((z.1 * (1 - z.1) : ℝ) : ℂ) * (-(i15B2 z.1 z.2 : ℂ)) ^ 5 *
        i15E5 (ε * (-(i15B2 z.1 z.2 : ℂ))))

theorem i15_cpow_one_sub_two_mul {r : ℝ} (hr : 0 < r) (ε : ℂ) :
    (r : ℂ) ^ (1 - 2 * ε) = (r : ℂ) * cexp (ε * (-2 * (Real.log r : ℂ))) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le,
    show (Real.log r : ℂ) * (1 - 2 * ε) = (Real.log r : ℂ) + ε * (-2 * (Real.log r : ℂ)) by ring,
    Complex.exp_add, ← ofReal_exp, Real.exp_log hr]

theorem i15_P_pos {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < i15P x u :=
  add_pos_of_nonneg_of_pos (mul_nonneg (i9_c_pos hx).le (sq_nonneg _)) (by simpa using hu.1)

/-- **The pointwise expansion** of the integrand of `K`. -/
theorem i15K_integrand_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (ε : ℂ) :
    i15Wt ε x u * i15Psi ε x u =
      (∑ k ∈ Finset.range 5, ε ^ k * (i15F k (x, u) : ℂ)) + ε ^ 5 * i15G ε (x, u) := by
  have hc : 0 < x * (1 - x) := i9_c_pos hx
  have hu0 : 0 < u := hu.1
  have hP : 0 < i15P x u := i15_P_pos hx hu
  have hB1 : (i15B1 x u : ℂ) = (Real.log (x * (1 - x)) : ℂ) + (Real.log u : ℂ) +
      (-2 * (Real.log (i15P x u) : ℂ)) := by unfold i15B1; push_cast; ring
  have hB2 : (i15B2 x u : ℂ) = (Real.log (x * (1 - x)) : ℂ) + (Real.log u : ℂ) +
      (-2 * (Real.log u : ℂ)) := by unfold i15B2; push_cast; ring
  have hB3 : -(i15B2 x u : ℂ) = (Real.log (x * (1 - x)) : ℂ) + (Real.log u : ℂ) +
      (-2 * (Real.log (x * (1 - x)) : ℂ)) := by unfold i15B2; push_cast; ring
  have e1 := exp_eq_i15E5 (ε * (i15B1 x u : ℂ))
  have e2 := exp_eq_i15E5 (ε * (i15B2 x u : ℂ))
  have e3 := exp_eq_i15E5 (ε * -(i15B2 x u : ℂ))
  have hL : i15Wt ε x u * i15Psi ε x u = ((x * (1 - x) : ℝ) : ℂ)⁻¹ * (u : ℂ)⁻¹ *
      ((i15P x u : ℂ) * cexp (ε * (i15B1 x u : ℂ)) - (u : ℂ) * cexp (ε * (i15B2 x u : ℂ)) -
        ((x * (1 - x) : ℝ) : ℂ) * cexp (ε * -(i15B2 x u : ℂ))) := by
    unfold i15Wt i15Psi
    rw [i9_cpow_sub_one hc, i9_cpow_sub_one hu0, i15_cpow_one_sub_two_mul hP,
      i15_cpow_one_sub_two_mul hu0, i15_cpow_one_sub_two_mul hc, hB1, hB3, hB2]
    simp only [mul_add, Complex.exp_add]
    ring
  rw [hL, e1, e2, e3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, i15F, i15G, Nat.factorial_zero,
    Nat.factorial_succ]
  push_cast
  generalize (x : ℂ) * (1 - (x : ℂ)) = C
  ring

theorem i15K_integrand_eq' {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (ε : ℂ) :
    i15Wt ε z.1 z.2 * i15Psi ε z.1 z.2 =
      (∑ k ∈ Finset.range 5, ε ^ k * (i15F k z : ℂ)) + ε ^ 5 * i15G ε z := by
  obtain ⟨x, u⟩ := z
  exact i15K_integrand_eq hz.1 hz.2 ε

/-! ### Bounds and integrability -/

/-- The dominating function of `QED.ThreeLoopD.norm_i15K_integrand_le`. -/
noncomputable def i15Bound (z : ℝ × ℝ) : ℝ :=
  17 * ((z.1 * (1 - z.1)) ^ (-(4 / 5) : ℝ) * z.2 ^ (-(4 / 5) : ℝ))

theorem integrable_i15Bound :
    Integrable i15Bound (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [volume_restrict_prod2]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    (integrableOn_rpow_Ioo (by norm_num))).const_mul 17

theorem differentiable_i15G (z : ℝ × ℝ) : Differentiable ℂ fun ε => i15G ε z := by
  unfold i15G
  fun_prop

theorem measurable_i15G (ε : ℂ) : Measurable fun z => i15G ε z := by
  unfold i15G i15B1 i15B2 i15P i9Poly
  fun_prop

theorem measurable_i15F (k : ℕ) : Measurable (i15F k) := by
  unfold i15F i15B1 i15B2 i15P i9Poly
  fun_prop

/-- **Coefficient bounds**: `|Fₖ| ≤ 50ᵏ b` and `‖G(ε)‖ ≤ 50⁵ b` on `‖ε‖ ≤ 1/25`. -/
theorem i15K_coeff_bounds {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    (∀ k < 5, |i15F k z| ≤ 50 ^ k * i15Bound z) ∧
      ∀ ε : ℂ, ‖ε‖ ≤ 1 / 25 → ‖i15G ε z‖ ≤ 50 ^ 5 * i15Bound z := by
  obtain ⟨h1, h2⟩ := i15_taylor_bound 5 (fun k => (i15F k z : ℂ)) (fun ε => i15G ε z)
    (differentiable_i15G z) (ρ := 1 / 25) (b := i15Bound z) (by norm_num) (fun ε hε => by
      have hε' : ‖ε‖ < 1 / 20 := by rw [hε]; norm_num
      rw [← i15K_integrand_eq' hz ε]
      exact norm_i15K_integrand_le hε' hz.1 hz.2)
  refine ⟨fun k hk => ?_, fun ε hε => (h2 ε hε).trans (le_of_eq (by ring))⟩
  have := h1 k hk
  rw [norm_real, Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [div_pow, one_pow, div_div_eq_mul_div, div_one, show (50 : ℝ) = 2 * 25 by norm_num,
    mul_pow]
  ring

theorem i15_S_meas : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem integrable_i15F {k : ℕ} (hk : k < 5) :
    Integrable (fun z => (i15F k z : ℂ)) (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
  Integrable.mono' (integrable_i15Bound.const_mul (50 ^ k))
    ((measurable_i15F k).complex_ofReal.aestronglyMeasurable)
    (ae_restrict_of_forall_mem i15_S_meas fun z hz => by
      rw [norm_real, Real.norm_eq_abs]; exact (i15K_coeff_bounds hz).1 k hk)

theorem integrable_i15F_real {k : ℕ} (hk : k < 5) :
    Integrable (i15F k) (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
  Integrable.mono' (integrable_i15Bound.const_mul (50 ^ k))
    (measurable_i15F k).aestronglyMeasurable
    (ae_restrict_of_forall_mem i15_S_meas fun z hz => by
      rw [Real.norm_eq_abs]; exact (i15K_coeff_bounds hz).1 k hk)

/-! ### The expansion -/

/-- **`K(ε) = Σ_{k < 5} εᵏ ∫ Fₖ + ε⁵ ∫ G(ε)`** for `‖ε‖ < 1/25`. -/
theorem i15K_eq_taylor {ε : ℂ} (hε : ‖ε‖ < 1 / 25) :
    i15K ε = (∑ k ∈ Finset.range 5,
        ε ^ k * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F k z : ℝ) : ℂ)) +
      ε ^ 5 * ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15G ε z := by
  have hG : Integrable (fun z => i15G ε z) (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    Integrable.mono' (integrable_i15Bound.const_mul (50 ^ 5))
      ((measurable_i15G ε).aestronglyMeasurable)
      (ae_restrict_of_forall_mem i15_S_meas fun z hz => (i15K_coeff_bounds hz).2 ε hε.le)
  have hF : ∀ k ∈ Finset.range 5, Integrable (fun z => ε ^ k * (i15F k z : ℂ))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := fun k hk =>
    (integrable_i15F (Finset.mem_range.mp hk)).const_mul _
  unfold i15K
  rw [setIntegral_congr_fun i15_S_meas (fun z hz => i15K_integrand_eq' hz ε),
    integral_add (integrable_finsetSum _ hF) (hG.const_mul _), integral_finsetSum _ hF,
    integral_const_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_complex_ofReal]

/-- `ε ↦ ∫ G(ε)` is analytic at `0`. -/
theorem analyticAt_i15KR :
    AnalyticAt ℂ (fun ε => ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15G ε z) 0 := by
  have hd : ∀ ε₀ ∈ ball (0 : ℂ) (1 / 50), DifferentiableAt ℂ
      (fun ε => ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15G ε z) ε₀ := by
    intro ε₀ h0
    have hball : ∀ ε ∈ ball ε₀ (1 / 50), ‖ε‖ ≤ 1 / 25 := fun ε hε => by
      have := norm_sub_norm_le ε ε₀
      rw [mem_ball, dist_eq_norm] at hε
      rw [mem_ball, dist_zero_right] at h0
      linarith
    refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 50)
      (b := fun z => 50 ^ 5 * i15Bound z) (integrable_i15Bound.const_mul _)
      (fun ε _ => (measurable_i15G ε).aestronglyMeasurable) ?_
      (ae_of_all _ fun z => (differentiable_i15G z).differentiableOn)
    exact ae_restrict_of_forall_mem i15_S_meas fun z hz ε hε =>
      (i15K_coeff_bounds hz).2 ε (hball ε hε)
  exact DifferentiableOn.analyticAt (fun ε hε => (hd ε hε).differentiableWithinAt)
    (ball_mem_nhds 0 (by norm_num))

/-- **`K` to order `ε⁴`**, with the coefficients as real integrals. -/
theorem hasTruncLaurent_i15K_integrals :
    HasTruncLaurent i15K (fun ε => ∑ k ∈ Finset.range 5,
      ε ^ k * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F k z : ℝ) : ℂ)) 5 :=
  ⟨_, analyticAt_i15KR, eventually_nhdsWithin_of_eventually_nhds
    (eventually_of_mem (ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 25)) fun ε hε =>
      i15K_eq_taylor (by simpa using hε))⟩

/-! ### The constant term and the assembly -/

theorem i15F_zero {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i15F 0 z = z.2 - 2 := by
  have hc := i9_c_pos hz.1
  have hu := hz.2.1
  unfold i15F i15P i9Poly
  rw [div_eq_iff (by simp only [Nat.factorial_zero, Nat.cast_one, one_mul]; positivity)]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, one_mul]
  ring

/-- **`∫ F₀ = -3/2`.** -/
theorem integral_i15F_zero :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 0 z = -3 / 2 := by
  rw [setIntegral_congr_fun i15_S_meas (fun z hz => i15F_zero hz)]
  have h := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (ν := volume.restrict (Ioo (0 : ℝ) 1)) (fun _ : ℝ => (1 : ℝ)) (fun u : ℝ => u - 2)
  simp only [one_mul] at h
  rw [volume_restrict_prod2, h, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_sub
      intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp
  norm_num

/-- **The target expansion of `K` from the values of its Taylor integrals.** -/
theorem hasTruncLaurent_i15K_of_coeffs
    (h1 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 1 z = -33 / 4)
    (h2 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 2 z =
      35 / 12 * Real.pi ^ 2 + 4 * QED.Polylog.zeta3 - 251 / 8)
    (h3 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 3 z =
      -16 * Real.pi ^ 2 * Real.log 2 + 107 / 8 * Real.pi ^ 2 + 61 * QED.Polylog.zeta3 - 1665 / 16)
    (h4 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 4 z =
      384 * QED.Polylog.Li 4 (1 / 2) + 16 * Real.log 2 ^ 4
        + 32 * Real.pi ^ 2 * Real.log 2 ^ 2 - 72 * Real.pi ^ 2 * Real.log 2
        - 253 / 80 * Real.pi ^ 4 - 2 / 3 * Real.pi ^ 2 * QED.Polylog.zeta3
        + 2267 / 48 * Real.pi ^ 2 + 503 / 2 * QED.Polylog.zeta3 + 12 * QED.Polylog.zeta5
        - 10403 / 32) :
    HasTruncLaurent i15K i15KLaurent 5 := by
  obtain ⟨R, hR, hev⟩ := hasTruncLaurent_i15K_integrals
  refine ⟨R, hR, hev.mono fun ε hε => ?_⟩
  rw [hε]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, integral_i15F_zero, h1, h2, h3, h4]
  unfold i15KLaurent
  push_cast
  ring

end QED.ThreeLoopD
