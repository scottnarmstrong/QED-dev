/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8Ang
public import QED.ThreeLoopD.SetDMastersI13RemAnalytic

/-!
# Set (d), master `I₈`: `Rem` is holomorphic at `0`, with its Taylor coefficients as integrals

The two integrands of `QED.ThreeLoopD.i8Rem`,

  `h₁(t, ε) = t ^ (1 - ε) b_ε(t)² A_ε(t)` on `(0, 1)`,
  `h₂(t, ε) = h₁(t, ε) - Asym(ε, t)` on `(1, ∞)`,

are holomorphic in `ε` on `‖ε‖ < 1/5`. On `‖ε‖ ≤ 1/10`, `‖A_ε(t)‖ ≤ C/t`, so
`‖h₁‖ ≤ 4C t ^ (-1/10)` (`QED.ThreeLoopD.norm_i8RemInt1_le`); and from the large-`t` expansions of
the bubble (`QED.ThreeLoopD.norm_i13Bub_sub_asym_le`) and of the angular average
(`QED.ThreeLoopD.i8Ang_asym`), `‖h₂‖ ≤ K t ^ (3/10 - 2)` (`QED.ThreeLoopD.norm_i8RemInt2_le`):
with `u = t ^ (-ε)`, `X₁ = α₁ u + β₀`, `X₂ = α₂ u + β₁`, `S = α₀ u + X₁/t + X₂/t²`,
`Y = X₁ + X₂/t` and `E = A - 1/t + κ/t² = O(t⁻³)`,

  `h₂ = t u (b - S)(b + S) A + t u S² E + u (2 α₀ u X₂ + Y² - 2κ α₀ u Y - κ Y²/t)/t²`

(`QED.ThreeLoopD.i8RemInt2_eq`). `QED.ThreeLoopD.hasTruncLaurent_integral_i13Dsl` then gives

  `Rem(ε) = ∑_{k < 5} cₖ εᵏ + ε⁵ R(ε)`, `R` holomorphic at `0`,

where `cₖ` (`QED.ThreeLoopD.i8RemCoeff`) is the sum of the integrals over `(0, 1)` and `(1, ∞)`
of the `k`-th Taylor coefficients `Dᵏ hᵢ(t, ·)(0)` of the integrands
(`QED.ThreeLoopD.hasTruncLaurent_i8Rem_coeff`).

## Main results

* `QED.ThreeLoopD.norm_i8RemInt1_le`, `QED.ThreeLoopD.norm_i8RemInt2_le`.
* `QED.ThreeLoopD.hasTruncLaurent_i8Rem_coeff`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- The integrand `t ^ (1 - ε) b_ε(t)² A_ε(t)` of `Rem` on `(0, 1)`. -/
noncomputable def i8RemInt1 (t : ℝ) (ε : ℂ) : ℂ :=
  (t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2 * i8Ang ε t

/-- The subtracted integrand `t ^ (1 - ε) b_ε(t)² A_ε(t) - Asym(ε, t)` of `Rem` on `(1, ∞)`. -/
noncomputable def i8RemInt2 (t : ℝ) (ε : ℂ) : ℂ :=
  (t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2 * i8Ang ε t - i8Asym ε t

/-- **The Taylor coefficients of `Rem`**, as integrals of the pointwise Taylor coefficients. -/
noncomputable def i8RemCoeff (k : ℕ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) 1, i13Dsl (i8RemInt1 t) k 0) +
    ∫ t in Ioi (1 : ℝ), i13Dsl (i8RemInt2 t) k 0

/-! ### The algebraic decomposition -/

theorem norm_i8Kap_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) : ‖i8Kap ε‖ ≤ 2 := by
  unfold i8Kap
  have h : 1 ≤ ‖(2 : ℂ) - ε‖ := by
    have := norm_sub_norm_le (2 : ℂ) ε
    rw [Complex.norm_ofNat] at this
    linarith
  rw [norm_div, Complex.norm_ofNat, div_le_iff₀ (by linarith)]
  linarith

theorem differentiableAt_i8Kap {ε : ℂ} (hε : ‖ε‖ < 1 / 2) : DifferentiableAt ℂ i8Kap ε := by
  have h2 : (2 : ℂ) - ε ≠ 0 := by
    intro h; have := congr_arg re h; simp at this; linarith [re_le_norm ε]
  unfold i8Kap
  exact (differentiableAt_const _).div (by fun_prop) h2

/-- **The decomposition of the subtracted integrand** at large `t`. -/
theorem i8RemInt2_eq {t : ℝ} (ht : 0 < t) (ε : ℂ) :
    i8RemInt2 t ε = t * (t : ℂ) ^ (-ε) * (i13Bub ε t - i13BubAsym ε t) *
        (i13Bub ε t + i13BubAsym ε t) * i8Ang ε t +
      t * (t : ℂ) ^ (-ε) * i13BubAsym ε t ^ 2 * (i8Ang ε t - 1 / t + i8Kap ε / t ^ 2) +
      (t : ℂ) ^ (-ε) * (2 * i13Al0 ε * (t : ℂ) ^ (-ε) * (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) +
        (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε + (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / t) ^ 2 -
        2 * i8Kap ε * i13Al0 ε * (t : ℂ) ^ (-ε) *
          (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε + (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / t) -
        i8Kap ε * (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε +
          (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / t) ^ 2 / t) / t ^ 2 := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have c1 := i13_cpow_lin ht 1 1 ε
  have c3 := i13_cpow_lin ht 0 3 ε
  have c5 := i13_cpow_lin ht (-1) 3 ε
  have c6 := i13_cpow_lin ht (-1) 2 ε
  simp only [cpow_one, cpow_zero, cpow_neg_one, Nat.cast_one, Nat.cast_ofNat, one_mul,
    pow_one] at c1 c3 c5 c6
  unfold i8RemInt2 i8Asym i13BubAsym
  rw [show 1 - ε = 1 + -ε by ring, c1, show -3 * ε = 0 + 3 * -ε by ring, c3,
    show -1 - 3 * ε = -1 + 3 * -ε by ring, c5, show -1 - 2 * ε = -1 + 2 * -ε by ring, c6]
  field_simp
  ring

/-! ### The bounds -/

/-- **The bound on `(1, ∞)`**: `‖h₂(t, ε)‖ ≤ K t ^ (3/10 - 2)` for `‖ε‖ ≤ 1/10`, `t ≥ 1`. -/
theorem norm_i8RemInt2_le : ∃ K, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ∀ t : ℝ, 1 ≤ t →
    ‖i8RemInt2 t ε‖ ≤ K * t ^ ((3 : ℝ) / 10 - 2) := by
  obtain ⟨CE, hE⟩ := norm_i13Bub_sub_asym_le
  obtain ⟨C, hC⟩ := i13_coeff_bound
  obtain ⟨CN, hN⟩ := i8Nrm_bound
  have hCN : 0 ≤ CN := (norm_nonneg _).trans (hN 0 (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp)).1
  have hCE : 0 ≤ CE := by
    have h := (norm_nonneg _).trans (hE 0 (by simp) 1 le_rfl)
    rw [Real.one_rpow, mul_one] at h
    exact h
  refine ⟨CE * (CE + 10 * C) * CN + 400 * C ^ 2 * CN + 68 * C ^ 2, fun ε hε t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hε2 : ‖ε‖ < 1 / 2 := by linarith
  obtain ⟨a0, a1, a2, b0, b1⟩ := hC ε hε
  set p := t ^ ((1 : ℝ) / 10) with hp
  have hp1 : 1 ≤ p := Real.one_le_rpow ht (by norm_num)
  have hp0 : 0 ≤ p := by linarith
  have hU := i13_norm_cpow_neg_le' hε ht
  rw [← hp] at hU
  have hnt : ‖(t : ℂ)‖ = t := by rw [norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hit : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hit0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hpow : t ^ ((3 : ℝ) / 10 - 2) = p ^ 3 * (t ^ 2)⁻¹ := by
    have h3 : p ^ 3 = t ^ ((3 : ℝ) / 10) := by
      rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    rw [h3, Real.rpow_sub ht0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  rw [hpow, i8RemInt2_eq ht0]
  set u := (t : ℂ) ^ (-ε)
  set X1 := i13Al1 ε * u + i13Be0 ε
  set X2 := i13Al2 ε * u + i13Be1 ε
  set Y := X1 + X2 / t
  have hX1 : ‖X1‖ ≤ 2 * C * p := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [mul_le_mul a1 hU (norm_nonneg _) hC0]
  have hX2 : ‖X2‖ ≤ 2 * C * p := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [mul_le_mul a2 hU (norm_nonneg _) hC0]
  have hdiv : ∀ z : ℂ, ‖z / (t : ℂ)‖ ≤ ‖z‖ := fun z => by
    rw [norm_div, hnt, div_eq_mul_inv]
    exact mul_le_of_le_one_right (norm_nonneg _) hit
  have hdiv2 : ∀ z : ℂ, ‖z / (t : ℂ) ^ 2‖ ≤ ‖z‖ := fun z => by
    rw [norm_div, norm_pow, hnt, div_eq_mul_inv]
    exact mul_le_of_le_one_right (norm_nonneg _) (inv_le_one_of_one_le₀ ht2)
  have hY : ‖Y‖ ≤ 4 * C * p := by
    refine (norm_add_le _ _).trans ?_
    linarith [hdiv X2]
  have hA0 : ‖i13Al0 ε * u‖ ≤ C * p := by
    rw [norm_mul]; exact mul_le_mul a0 hU (norm_nonneg _) hC0
  have hS : ‖i13BubAsym ε t‖ ≤ 5 * C * p := by
    rw [show i13BubAsym ε t = i13Al0 ε * u + X1 / t + X2 / t ^ 2 from rfl]
    have := norm_add_le (i13Al0 ε * u + X1 / t) (X2 / t ^ 2)
    have := norm_add_le (i13Al0 ε * u) (X1 / t)
    linarith [hdiv X1, hdiv2 X2]
  have hbS : ‖i13Bub ε t - i13BubAsym ε t‖ ≤ CE * (p * (t ^ 3)⁻¹) := by
    have h := hE ε hε t ht
    have hpow1 : t ^ ((1 : ℝ) / 10 - 3) = p * (t ^ 3)⁻¹ := by
      rw [Real.rpow_sub ht0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        div_eq_mul_inv]
    rwa [hpow1] at h
  have ht3 : (t ^ 3)⁻¹ ≤ (t ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ ht (by norm_num))
  have ht2' : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht2
  have hAng := norm_i8Ang_le hN hε ht0
  have hK := norm_i8Kap_le hε
  have hEA : ‖i8Ang ε t - 1 / t + i8Kap ε / t ^ 2‖ ≤ 16 * CN * (t ^ 3)⁻¹ := by
    rw [i8Ang_asym hε2 ht0]
    have hEt := norm_i8AngE_le (by linarith [re_le_norm ε] : ε.re ≤ 1 / 2) ht0
    have : (1 : ℂ) / t - i8Kap ε / t ^ 2 + 16 * i8Nrm ε * i8AngE ε t / t ^ 2 - 1 / t +
        i8Kap ε / t ^ 2 = 16 * i8Nrm ε * i8AngE ε t / t ^ 2 := by ring
    rw [this, norm_div, norm_mul, norm_mul, norm_pow, hnt, Complex.norm_ofNat]
    calc 16 * ‖i8Nrm ε‖ * ‖i8AngE ε t‖ / t ^ 2 ≤ 16 * CN * t⁻¹ / t ^ 2 := by
          gcongr
          exact hN ε hε
      _ = 16 * CN * (t ^ 3)⁻¹ := by field_simp
  -- the three terms
  have hT1 : ‖(t : ℂ) * u * (i13Bub ε t - i13BubAsym ε t) * (i13Bub ε t + i13BubAsym ε t) *
      i8Ang ε t‖ ≤ CE * (CE + 10 * C) * CN * (p ^ 3 * (t ^ 2)⁻¹) := by
    have hbp : ‖i13Bub ε t + i13BubAsym ε t‖ ≤ (CE + 10 * C) * p := by
      have h1 : ‖i13Bub ε t + i13BubAsym ε t‖ ≤
          ‖i13Bub ε t - i13BubAsym ε t‖ + 2 * ‖i13BubAsym ε t‖ := by
        calc ‖i13Bub ε t + i13BubAsym ε t‖ =
              ‖(i13Bub ε t - i13BubAsym ε t) + 2 * i13BubAsym ε t‖ := by ring_nf
          _ ≤ _ := (norm_add_le _ _).trans (by rw [norm_mul]; simp)
      have h2 : CE * (p * (t ^ 3)⁻¹) ≤ CE * p := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hp0 (inv_le_one_of_one_le₀ (one_le_pow₀ ht))) hCE
      nlinarith
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hnt]
    calc t * ‖u‖ * ‖i13Bub ε t - i13BubAsym ε t‖ * ‖i13Bub ε t + i13BubAsym ε t‖ *
          ‖i8Ang ε t‖ ≤ t * p * (CE * (p * (t ^ 3)⁻¹)) * ((CE + 10 * C) * p) * (CN * t⁻¹) := by
          gcongr
      _ = CE * (CE + 10 * C) * CN * (p ^ 3 * (t ^ 3)⁻¹) := by field_simp
      _ ≤ CE * (CE + 10 * C) * CN * (p ^ 3 * (t ^ 2)⁻¹) := by gcongr
  have hT2 : ‖(t : ℂ) * u * i13BubAsym ε t ^ 2 * (i8Ang ε t - 1 / t + i8Kap ε / t ^ 2)‖ ≤
      400 * C ^ 2 * CN * (p ^ 3 * (t ^ 2)⁻¹) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hnt]
    calc t * ‖u‖ * ‖i13BubAsym ε t‖ ^ 2 * ‖i8Ang ε t - 1 / t + i8Kap ε / t ^ 2‖ ≤
          t * p * (5 * C * p) ^ 2 * (16 * CN * (t ^ 3)⁻¹) := by gcongr
      _ = 400 * C ^ 2 * CN * (p ^ 3 * (t ^ 2)⁻¹) := by field_simp; ring
  have hT3 : ‖u * (2 * i13Al0 ε * u * X2 + Y ^ 2 - 2 * i8Kap ε * i13Al0 ε * u * Y -
      i8Kap ε * Y ^ 2 / t) / t ^ 2‖ ≤ 68 * C ^ 2 * (p ^ 3 * (t ^ 2)⁻¹) := by
    have hp2 : p ≤ p ^ 2 := by nlinarith
    have hin : ‖2 * i13Al0 ε * u * X2 + Y ^ 2 - 2 * i8Kap ε * i13Al0 ε * u * Y -
        i8Kap ε * Y ^ 2 / t‖ ≤ 68 * C ^ 2 * p ^ 2 := by
      have e1 : ‖2 * i13Al0 ε * u * X2‖ ≤ 4 * (C ^ 2 * p ^ 2) := by
        rw [show 2 * i13Al0 ε * u * X2 = 2 * (i13Al0 ε * u) * X2 by ring, norm_mul, norm_mul,
          Complex.norm_ofNat]
        calc 2 * ‖i13Al0 ε * u‖ * ‖X2‖ ≤ 2 * (C * p) * (2 * C * p) := by gcongr
          _ = 4 * (C ^ 2 * p ^ 2) := by ring
      have e2 : ‖Y ^ 2‖ ≤ 16 * (C ^ 2 * p ^ 2) := by
        rw [norm_pow]
        calc ‖Y‖ ^ 2 ≤ (4 * C * p) ^ 2 := by gcongr
          _ = 16 * (C ^ 2 * p ^ 2) := by ring
      have e3 : ‖2 * i8Kap ε * i13Al0 ε * u * Y‖ ≤ 16 * (C ^ 2 * p ^ 2) := by
        rw [show 2 * i8Kap ε * i13Al0 ε * u * Y = 2 * i8Kap ε * (i13Al0 ε * u) * Y by ring,
          norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
        calc 2 * ‖i8Kap ε‖ * ‖i13Al0 ε * u‖ * ‖Y‖ ≤ 2 * 2 * (C * p) * (4 * C * p) := by gcongr
          _ = 16 * (C ^ 2 * p ^ 2) := by ring
      have e4 : ‖i8Kap ε * Y ^ 2 / t‖ ≤ 32 * (C ^ 2 * p ^ 2) := by
        refine (hdiv _).trans ?_
        rw [norm_mul, norm_pow]
        calc ‖i8Kap ε‖ * ‖Y‖ ^ 2 ≤ 2 * (4 * C * p) ^ 2 := by gcongr
          _ = 32 * (C ^ 2 * p ^ 2) := by ring
      have f1 := norm_sub_le (2 * i13Al0 ε * u * X2 + Y ^ 2 - 2 * i8Kap ε * i13Al0 ε * u * Y)
        (i8Kap ε * Y ^ 2 / t)
      have f2 := norm_sub_le (2 * i13Al0 ε * u * X2 + Y ^ 2) (2 * i8Kap ε * i13Al0 ε * u * Y)
      have f3 := norm_add_le (2 * i13Al0 ε * u * X2) (Y ^ 2)
      linarith
    rw [norm_div, norm_mul, norm_pow, hnt, div_eq_mul_inv]
    calc ‖u‖ * ‖2 * i13Al0 ε * u * X2 + Y ^ 2 - 2 * i8Kap ε * i13Al0 ε * u * Y -
          i8Kap ε * Y ^ 2 / t‖ * (t ^ 2)⁻¹ ≤ p * (68 * C ^ 2 * p ^ 2) * (t ^ 2)⁻¹ := by gcongr
      _ = 68 * C ^ 2 * (p ^ 3 * (t ^ 2)⁻¹) := by ring
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (by linarith [hT1, hT2, hT3]))

/-- **The bound on `(0, 1)`**: `‖h₁(t, ε)‖ ≤ 4 C t ^ (-1/10)`. -/
theorem norm_i8RemInt1_le {C : ℝ} (hC : ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ‖i8Nrm ε‖ ≤ C)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) :
    ‖i8RemInt1 t ε‖ ≤ 4 * C * t ^ (-(1 : ℝ) / 10) := by
  unfold i8RemInt1
  have hre : |ε.re| ≤ 1 / 10 := (abs_re_le_norm ε).trans hε
  have h1 : ‖(t : ℂ) ^ (1 - ε)‖ ≤ t ^ ((9 : ℝ) / 10) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht.1]
    exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by
      simp; linarith [le_abs_self ε.re])
  have h2 : ‖i13Bub ε t‖ ≤ 2 := by
    refine (norm_i13Bub_le ε ht.1.le).trans ?_
    calc (1 + t / 4) ^ ‖ε‖ ≤ (1 + t / 4) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by linarith)
      _ ≤ 2 := by rw [Real.rpow_one]; linarith [ht.2]
  have h3 := norm_i8Ang_le hC hε ht.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp))
  have he : t ^ ((9 : ℝ) / 10) * t⁻¹ = t ^ (-(1 : ℝ) / 10) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht.1]; norm_num
  rw [norm_mul, norm_mul, norm_pow]
  calc ‖(t : ℂ) ^ (1 - ε)‖ * ‖i13Bub ε t‖ ^ 2 * ‖i8Ang ε t‖ ≤
        t ^ ((9 : ℝ) / 10) * 2 ^ 2 * (C * t⁻¹) :=
        mul_le_mul (mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity)
          (Real.rpow_nonneg ht.1.le _)) h3 (norm_nonneg _)
          (mul_nonneg (Real.rpow_nonneg ht.1.le _) (by norm_num))
    _ = 4 * C * (t ^ ((9 : ℝ) / 10) * t⁻¹) := by ring
    _ = 4 * C * t ^ (-(1 : ℝ) / 10) := by rw [he]

/-! ### The expansion -/

theorem differentiableOn_i8RemInt1 {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (i8RemInt1 t) (ball 0 (1 / 5)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  intro ε hε
  rw [mem_ball, dist_zero_right] at hε
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold i8RemInt1
  exact ((Differentiable.const_cpow (by fun_prop) (Or.inl ht0)).differentiableAt.mul
    ((differentiable_i13Bub ht.le).differentiableAt.pow 2)).mul
    (differentiableAt_i8Ang (by linarith) ht)

theorem differentiableOn_i8RemInt2 {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (i8RemInt2 t) (ball 0 (1 / 5)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  intro ε hε
  have h1 := differentiableOn_i8RemInt1 ht ε hε
  rw [mem_ball, dist_zero_right] at hε
  obtain ⟨d0, d1, -, e0, -⟩ := differentiableAt_i13_coeffs (by linarith : ‖ε‖ < 1 / 2)
  have dk := differentiableAt_i8Kap (by linarith : ‖ε‖ < 1 / 2)
  have hc : ∀ f : ℂ → ℂ, DifferentiableAt ℂ f ε →
      DifferentiableAt ℂ (fun ε => (t : ℂ) ^ f ε) ε := fun f hf => hf.const_cpow (Or.inl ht0)
  have p2 := hc (fun ε => -3 * ε) (by fun_prop)
  have p4 := hc (fun ε => -1 - 3 * ε) (by fun_prop)
  have p5 := hc (fun ε => -1 - 2 * ε) (by fun_prop)
  have hA : DifferentiableAt ℂ (fun ε => i8Asym ε t) ε := by
    unfold i8Asym; fun_prop
  have h1' := h1.differentiableAt (isOpen_ball.mem_nhds (by
    rw [mem_ball, dist_zero_right]; exact hε))
  exact (h1'.sub hA).differentiableWithinAt

theorem measurable_i8RemInt1 (ε : ℂ) : Measurable fun t => i8RemInt1 t ε := by
  unfold i8RemInt1
  exact ((measurable_ofReal.pow_const _).mul ((measurable_i13Bub ε).pow_const 2)).mul
    (measurable_i8Ang ε)

theorem measurable_i8RemInt2 (ε : ℂ) : Measurable fun t => i8RemInt2 t ε := by
  have h1 := measurable_i8RemInt1 ε
  unfold i8RemInt1 at h1
  unfold i8RemInt2 i8Asym
  have hc : ∀ c : ℂ, Measurable fun t : ℝ => (t : ℂ) ^ c := fun c =>
    measurable_ofReal.pow_const c
  exact h1.sub (((measurable_const.mul (hc _)).add (measurable_const.mul (hc _))).add
    (measurable_const.mul (hc _)))

/-- **`Rem` to order `ε⁴`, with the coefficients as integrals**:
`Rem(ε) = ∑_{k < 5} cₖ εᵏ + ε⁵ R(ε)`, `R` holomorphic at `0`. -/
theorem hasTruncLaurent_i8Rem_coeff :
    HasTruncLaurent i8Rem (fun ε => ∑ k ∈ Finset.range 5, i8RemCoeff k * ε ^ k) 5 := by
  obtain ⟨K, hK⟩ := norm_i8RemInt2_le
  obtain ⟨CN, hN⟩ := i8Nrm_bound
  have H1 := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (h := i8RemInt1) (R := 1 / 5) (ρ := 1 / 10) (M := fun t => 4 * CN * t ^ (-(1 : ℝ) / 10))
    (by norm_num) (by norm_num) ((integrableOn_rpow_Ioo (by norm_num)).const_mul (4 * CN))
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => differentiableOn_i8RemInt1 ht.1)
    (fun ε _ => (measurable_i8RemInt1 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ε hε =>
      norm_i8RemInt1_le hN ht hε.le) 5
  have H2 := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioi (1 : ℝ)))
    (h := i8RemInt2) (R := 1 / 5) (ρ := 1 / 10) (M := fun t => K * t ^ ((3 : ℝ) / 10 - 2))
    (by norm_num) (by norm_num)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul K)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      differentiableOn_i8RemInt2 (zero_lt_one.trans ht))
    (fun ε _ => (measurable_i8RemInt2 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ε hε =>
      hK ε hε.le t (le_of_lt ht)) 5
  obtain ⟨R1, hR1, e1⟩ := H1
  obtain ⟨R2, hR2, e2⟩ := H2
  refine ⟨fun ε => R1 ε + R2 ε, hR1.add hR2, ?_⟩
  filter_upwards [e1, e2] with ε h1 h2
  rw [show i8Rem ε = (∫ t in Ioo (0 : ℝ) 1, i8RemInt1 t ε) +
    ∫ t in Ioi (1 : ℝ), i8RemInt2 t ε from rfl, h1, h2]
  unfold i8RemCoeff
  simp only [add_mul, Finset.sum_add_distrib]
  ring

end QED.ThreeLoopD
