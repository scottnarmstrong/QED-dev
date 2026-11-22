/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RemAsy2
public import QED.ThreeLoopD.SetDMastersI13RemTaylor

/-!
# Set (d), master `I₁₃`: `Rem` is holomorphic at `0`, with its Taylor coefficients as integrals

The two integrands of `QED.ThreeLoopD.i13Rem`,

  `h₁(t, ε) = t ^ (1 - ε) b_ε(t)²` on `(0, 1)`,  `h₂(t, ε) = t ^ (1 - ε) b_ε(t)² - Asym(ε, t)` on
  `(1, ∞)`,

are holomorphic in `ε` on `‖ε‖ < 1/5`. On `‖ε‖ ≤ 1/10`, `‖h₁‖ ≤ 4`, and, from the large-`t`
expansion `QED.ThreeLoopD.norm_i13Bub_sub_asym_le` of the bubble,
`‖h₂‖ ≤ K t ^ (3/10 - 2)` (`QED.ThreeLoopD.norm_i13RemInt2_le`): with `u = t ^ (-ε)`,
`X₁ = α₁ u + β₀`, `X₂ = α₂ u + β₁` and `S = α₀ u + X₁/t + X₂/t²`,

  `h₂ = t u (b - S)(b + S) + u (2 X₁ X₂ / t² + X₂² / t³)`.

`QED.ThreeLoopD.hasTruncLaurent_integral_i13Dsl` then gives

  `Rem(ε) = ∑_{k < 5} cₖ εᵏ + ε⁵ R(ε)`, `R` holomorphic at `0`,

where `cₖ` (`QED.ThreeLoopD.i13RemCoeff`) is the sum of the integrals over `(0, 1)` and `(1, ∞)`
of the `k`-th Taylor coefficients `Dᵏ hᵢ(t, ·)(0)` of the integrands
(`QED.ThreeLoopD.hasTruncLaurent_i13Rem_coeff`).

## Main results

* `QED.ThreeLoopD.norm_i13RemInt2_le`.
* `QED.ThreeLoopD.hasTruncLaurent_i13Rem_coeff`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- The integrand `t ^ (1 - ε) b_ε(t)²` of `Rem` on `(0, 1)`. -/
noncomputable def i13RemInt1 (t : ℝ) (ε : ℂ) : ℂ := (t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2

/-- The subtracted integrand `t ^ (1 - ε) b_ε(t)² - Asym(ε, t)` of `Rem` on `(1, ∞)`. -/
noncomputable def i13RemInt2 (t : ℝ) (ε : ℂ) : ℂ :=
  (t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2 - i13Asym ε t

/-- **The Taylor coefficients of `Rem`**, as integrals of the pointwise Taylor coefficients. -/
noncomputable def i13RemCoeff (k : ℕ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) 1, i13Dsl (i13RemInt1 t) k 0) +
    ∫ t in Ioi (1 : ℝ), i13Dsl (i13RemInt2 t) k 0

/-! ### Holomorphy and boundedness of the coefficients -/

theorem differentiableAt_i13G {ε : ℂ} (hε : ‖ε‖ < 1 / 2) : DifferentiableAt ℂ i13G ε := by
  have hre : |ε.re| < 1 / 2 := (abs_re_le_norm ε).trans_lt hε
  have hr1 : 0 < (1 - ε).re := by simp; linarith [le_abs_self ε.re]
  have hr2 : 0 < (1 - 2 * ε).re := by simp; linarith [le_abs_self ε.re]
  have hG : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Gamma s := fun s hs =>
    differentiableAt_Gamma _ fun m hm => by
      have := congr_arg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  unfold i13G
  exact (((hG _ hr1).comp ε (by fun_prop)).pow 2).div ((hG _ hr2).comp ε (by fun_prop))
    (Gamma_ne_zero_of_re_pos hr2)

theorem differentiableAt_i13_coeffs {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    DifferentiableAt ℂ i13Al0 ε ∧ DifferentiableAt ℂ i13Al1 ε ∧ DifferentiableAt ℂ i13Al2 ε ∧
      DifferentiableAt ℂ i13Be0 ε ∧ DifferentiableAt ℂ i13Be1 ε := by
  obtain ⟨h1, h2, -, h12, -⟩ := i13_eps_facts hε
  have hG := differentiableAt_i13G hε
  have he1 : ε - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  have he2 : ε - 2 ≠ 0 := fun h => h2 (by linear_combination -h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold i13Al0; exact hG.div (by fun_prop) h12
  · unfold i13Al1; exact hG.const_mul 2
  · unfold i13Al2; exact (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -2 * (1 + 2 * ε)) ε).mul hG
  · unfold i13Be0; exact (differentiableAt_const _).div (by fun_prop) he1
  · unfold i13Be1; exact (differentiableAt_const _).div (by fun_prop) (mul_ne_zero he1 he2)

theorem i13_coeff_bound : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 →
    ‖i13Al0 ε‖ ≤ C ∧ ‖i13Al1 ε‖ ≤ C ∧ ‖i13Al2 ε‖ ≤ C ∧ ‖i13Be0 ε‖ ≤ C ∧ ‖i13Be1 ε‖ ≤ C := by
  have hc : ∀ f : ℂ → ℂ, (∀ ε : ℂ, ‖ε‖ < 1 / 2 → DifferentiableAt ℂ f ε) →
      ∃ C, ∀ ε ∈ closedBall (0 : ℂ) (1 / 10), ‖f ε‖ ≤ C := fun f hf =>
    (isCompact_closedBall (0 : ℂ) (1 / 10)).exists_bound_of_continuousOn
      fun ε hε => (hf ε (by rw [mem_closedBall, dist_zero_right] at hε; linarith)).continuousAt
        |>.continuousWithinAt
  obtain ⟨C0, h0⟩ := hc _ fun ε hε => (differentiableAt_i13_coeffs hε).1
  obtain ⟨C1, h1⟩ := hc _ fun ε hε => (differentiableAt_i13_coeffs hε).2.1
  obtain ⟨C2, h2⟩ := hc _ fun ε hε => (differentiableAt_i13_coeffs hε).2.2.1
  obtain ⟨C3, h3⟩ := hc _ fun ε hε => (differentiableAt_i13_coeffs hε).2.2.2.1
  obtain ⟨C4, h4⟩ := hc _ fun ε hε => (differentiableAt_i13_coeffs hε).2.2.2.2
  refine ⟨max (max (max C0 C1) (max C2 C3)) C4, fun ε hε => ?_⟩
  have hm : ε ∈ closedBall (0 : ℂ) (1 / 10) := by rw [mem_closedBall, dist_zero_right]; exact hε
  refine ⟨(h0 ε hm).trans ?_, (h1 ε hm).trans ?_, (h2 ε hm).trans ?_, (h3 ε hm).trans ?_,
    (h4 ε hm).trans ?_⟩ <;> simp

/-! ### The bound on `(1, ∞)` -/

theorem i13_cpow_lin {t : ℝ} (ht : 0 < t) (k : ℂ) (n : ℕ) (ε : ℂ) :
    (t : ℂ) ^ (k + n * (-ε)) = (t : ℂ) ^ k * ((t : ℂ) ^ (-ε)) ^ n := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [cpow_add _ _ ht0, cpow_nat_mul]

/-- The algebraic decomposition `h₂ = t u (b - S)(b + S) + u (2 X₁ X₂/t² + X₂²/t³)`. -/
theorem i13RemInt2_eq {t : ℝ} (ht : 0 < t) (ε : ℂ) :
    i13RemInt2 t ε = t * (t : ℂ) ^ (-ε) * (i13Bub ε t - i13BubAsym ε t) *
        (i13Bub ε t + i13BubAsym ε t) +
      (t : ℂ) ^ (-ε) * (2 * (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) *
        (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / t ^ 2 +
        (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) ^ 2 / t ^ 3) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have c1 := i13_cpow_lin ht 1 1 ε
  have c2 := i13_cpow_lin ht 1 3 ε
  have c3 := i13_cpow_lin ht 0 3 ε
  have c4 := i13_cpow_lin ht 0 2 ε
  have c5 := i13_cpow_lin ht (-1) 3 ε
  have c6 := i13_cpow_lin ht (-1) 2 ε
  have c7 := i13_cpow_lin ht (-1) 1 ε
  simp only [cpow_one, cpow_zero, cpow_neg_one, Nat.cast_one, Nat.cast_ofNat, one_mul,
    pow_one] at c1 c2 c3 c4 c5 c6 c7
  unfold i13RemInt2 i13Asym i13BubAsym
  rw [show 1 - ε = 1 + -ε by ring, c1, show 1 - 3 * ε = 1 + 3 * -ε by ring, c2,
    show -3 * ε = 0 + 3 * -ε by ring, c3, show -2 * ε = 0 + 2 * -ε by ring, c4,
    show -1 - 3 * ε = -1 + 3 * -ε by ring, c5, show -1 - 2 * ε = -1 + 2 * -ε by ring, c6,
    show -1 - ε = -1 + -ε by ring, c7]
  field_simp
  ring

theorem i13_norm_cpow_neg_le' {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ (-ε)‖ ≤ t ^ ((1 : ℝ) / 10) := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le ht (by
    rw [neg_re]; linarith [abs_re_le_norm ε, neg_abs_le ε.re])

/-- **The bound on `(1, ∞)`**: `‖h₂(t, ε)‖ ≤ K t ^ (3/10 - 2)` for `‖ε‖ ≤ 1/10`, `t ≥ 1`. -/
theorem norm_i13RemInt2_le : ∃ K, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ∀ t : ℝ, 1 ≤ t →
    ‖i13RemInt2 t ε‖ ≤ K * t ^ ((3 : ℝ) / 10 - 2) := by
  obtain ⟨CE, hE⟩ := norm_i13Bub_sub_asym_le
  obtain ⟨C, hC⟩ := i13_coeff_bound
  refine ⟨CE * (CE + 10 * C) + 12 * C ^ 2, fun ε hε t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨a0, a1, a2, b0, b1⟩ := hC ε hε
  have hC0 : 0 ≤ C := (norm_nonneg _).trans a0
  set p := t ^ ((1 : ℝ) / 10) with hp
  have hp1 : 1 ≤ p := Real.one_le_rpow ht (by norm_num)
  have hU := i13_norm_cpow_neg_le' hε ht
  rw [← hp] at hU
  have hit : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hit0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  -- the pieces
  have hpow1 : t ^ ((1 : ℝ) / 10 - 3) = p * (t ^ 3)⁻¹ := by
    rw [Real.rpow_sub ht0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  have hpow2 : t ^ ((3 : ℝ) / 10 - 2) = p ^ 3 * (t ^ 2)⁻¹ := by
    have h3 : p ^ 3 = t ^ ((3 : ℝ) / 10) := by
      rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    rw [h3, Real.rpow_sub ht0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  have hbS : ‖i13Bub ε t - i13BubAsym ε t‖ ≤ CE * (p * (t ^ 3)⁻¹) := by
    rw [← hpow1]; exact hE ε hε t ht
  rw [hpow2]
  have hX1 : ‖i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε‖ ≤ 2 * C * p := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [mul_le_mul a1 hU (norm_nonneg _) hC0]
  have hX2 : ‖i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε‖ ≤ 2 * C * p := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [mul_le_mul a2 hU (norm_nonneg _) hC0]
  have hS : ‖i13BubAsym ε t‖ ≤ 5 * C * p := by
    unfold i13BubAsym
    have hA : ‖i13Al0 ε * (t : ℂ) ^ (-ε)‖ ≤ C * p := by
      rw [norm_mul]; exact mul_le_mul a0 hU (norm_nonneg _) hC0
    have hd1 : ‖(i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) / (t : ℂ)‖ ≤ 2 * C * p := by
      rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_eq_mul_inv]
      nlinarith [mul_le_mul hX1 hit (inv_nonneg.mpr ht0.le) (by positivity)]
    have hd2 : ‖(i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / (t : ℂ) ^ 2‖ ≤ 2 * C * p := by
      rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_eq_mul_inv]
      have : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      nlinarith [mul_le_mul hX2 this (inv_nonneg.mpr (by positivity)) (by positivity)]
    calc _ ≤ ‖i13Al0 ε * (t : ℂ) ^ (-ε)‖ +
          ‖(i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) / (t : ℂ)‖ +
          ‖(i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / (t : ℂ) ^ 2‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _) |>.trans
            (le_of_eq (by ring))
      _ ≤ _ := by linarith
  have hCE : 0 ≤ CE := by
    have h := (norm_nonneg _).trans hbS
    have : 0 < p * (t ^ 3)⁻¹ := by positivity
    by_contra hn
    push Not at hn
    nlinarith
  set e := CE * (p * (t ^ 3)⁻¹) with he
  have ht3 : (t ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht)
  have ht2 : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht)
  have hp0 : 0 ≤ p := by linarith
  have hep : e ≤ CE * p := by
    rw [he]; exact mul_le_mul_of_nonneg_left (by nlinarith) hCE
  have he0 : 0 ≤ e := by positivity
  have hT1 : ‖(t : ℂ) * (t : ℂ) ^ (-ε) * (i13Bub ε t - i13BubAsym ε t) *
      (i13Bub ε t + i13BubAsym ε t)‖ ≤ CE * (CE + 10 * C) * (p ^ 3 * (t ^ 2)⁻¹) := by
    have hbp : ‖i13Bub ε t + i13BubAsym ε t‖ ≤ e + 10 * C * p := by
      calc ‖i13Bub ε t + i13BubAsym ε t‖ =
            ‖(i13Bub ε t - i13BubAsym ε t) + 2 * i13BubAsym ε t‖ := by ring_nf
        _ ≤ ‖i13Bub ε t - i13BubAsym ε t‖ + 2 * ‖i13BubAsym ε t‖ :=
            (norm_add_le _ _).trans (by rw [norm_mul]; simp)
        _ ≤ e + 10 * C * p := by linarith
    calc _ ≤ t * p * e * (e + 10 * C * p) := by
          rw [norm_mul, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
          exact mul_le_mul (mul_le_mul (mul_le_mul le_rfl hU (norm_nonneg _) ht0.le) hbS
            (norm_nonneg _) (by positivity)) hbp (norm_nonneg _) (by positivity)
      _ = p ^ 2 * (CE * (t ^ 2)⁻¹) * (e + 10 * C * p) := by
          rw [he]; field_simp
      _ ≤ p ^ 2 * (CE * (t ^ 2)⁻¹) * (CE * p + 10 * C * p) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = CE * (CE + 10 * C) * (p ^ 3 * (t ^ 2)⁻¹) := by ring
  have hT2 : ‖(t : ℂ) ^ (-ε) * (2 * (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) *
      (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / t ^ 2 +
      (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) ^ 2 / t ^ 3)‖ ≤
      12 * C ^ 2 * (p ^ 3 * (t ^ 2)⁻¹) := by
    have hn2 : ‖(t : ℂ) ^ 2‖ = t ^ 2 := by
      rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hn3 : ‖(t : ℂ) ^ 3‖ = t ^ 3 := by
      rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hq : 0 ≤ 2 * C * p := by positivity
    have hA : ‖2 * (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) *
        (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / (t : ℂ) ^ 2‖ ≤
        2 * (2 * C * p) * (2 * C * p) * (t ^ 2)⁻¹ := by
      rw [norm_div, norm_mul, norm_mul, hn2, div_eq_mul_inv]
      simp only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul le_rfl hX1 (norm_nonneg _)
        (by norm_num)) hX2 (norm_nonneg _) (by positivity)) (by positivity)
    have hB : ‖(i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) ^ 2 / (t : ℂ) ^ 3‖ ≤
        (2 * C * p) ^ 2 * (t ^ 2)⁻¹ := by
      rw [norm_div, norm_pow, hn3, div_eq_mul_inv]
      have h1 : (t ^ 3)⁻¹ ≤ (t ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ ht (by norm_num))
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hX2 2) h1 (by positivity)
        (by positivity)
    rw [norm_mul]
    calc _ ≤ p * (2 * (2 * C * p) * (2 * C * p) * (t ^ 2)⁻¹ + (2 * C * p) ^ 2 * (t ^ 2)⁻¹) :=
          mul_le_mul hU ((norm_add_le _ _).trans (add_le_add hA hB)) (norm_nonneg _) hp0
      _ = 12 * C ^ 2 * (p ^ 3 * (t ^ 2)⁻¹) := by ring
  rw [i13RemInt2_eq ht0]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add hT1 hT2
  linarith

/-! ### The expansion -/

theorem differentiable_i13RemInt1 {t : ℝ} (ht : 0 < t) : Differentiable ℂ (i13RemInt1 t) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  unfold i13RemInt1
  exact (Differentiable.const_cpow (by fun_prop) (Or.inl ht0)).mul
    ((differentiable_i13Bub ht.le).pow 2)

theorem differentiableOn_i13RemInt2 {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (i13RemInt2 t) (ball 0 (1 / 5)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  intro ε hε
  rw [mem_ball, dist_zero_right] at hε
  obtain ⟨d0, d1, d2, e0, e1⟩ := differentiableAt_i13_coeffs (by linarith : ‖ε‖ < 1 / 2)
  have hc : ∀ f : ℂ → ℂ, DifferentiableAt ℂ f ε →
      DifferentiableAt ℂ (fun ε => (t : ℂ) ^ f ε) ε := fun f hf => hf.const_cpow (Or.inl ht0)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold i13RemInt2 i13Asym
  have p1 := hc (fun ε => 1 - 3 * ε) (by fun_prop)
  have p2 := hc (fun ε => -3 * ε) (by fun_prop)
  have p3 := hc (fun ε => -2 * ε) (by fun_prop)
  have p4 := hc (fun ε => -1 - 3 * ε) (by fun_prop)
  have p5 := hc (fun ε => -1 - 2 * ε) (by fun_prop)
  have p6 := hc (fun ε => -1 - ε) (by fun_prop)
  have hb := differentiable_i13RemInt1 ht ε
  unfold i13RemInt1 at hb
  fun_prop

theorem measurable_i13RemInt1 (ε : ℂ) : Measurable fun t => i13RemInt1 t ε := by
  unfold i13RemInt1
  exact (measurable_ofReal.pow_const _).mul ((measurable_i13Bub ε).pow_const 2)

theorem measurable_i13RemInt2 (ε : ℂ) : Measurable fun t => i13RemInt2 t ε := by
  unfold i13RemInt2 i13Asym
  have hc : ∀ c : ℂ, Measurable fun t : ℝ => (t : ℂ) ^ c := fun c =>
    measurable_ofReal.pow_const c
  exact (measurable_i13RemInt1 ε).sub (by
    refine (((((measurable_const.mul (hc _)).add (measurable_const.mul (hc _))).add
      (measurable_const.mul (hc _))).add (measurable_const.mul (hc _))).add
      (measurable_const.mul (hc _))).add (measurable_const.mul (hc _)))

theorem norm_i13RemInt1_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) :
    ‖i13RemInt1 t ε‖ ≤ 4 := by
  unfold i13RemInt1
  have hre : |ε.re| ≤ 1 / 10 := (abs_re_le_norm ε).trans hε
  have h1 : ‖(t : ℂ) ^ (1 - ε)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos ht.1]
    exact Real.rpow_le_one ht.1.le ht.2.le (by simp; linarith [le_abs_self ε.re])
  have h2 : ‖i13Bub ε t‖ ≤ 2 := by
    refine (norm_i13Bub_le ε ht.1.le).trans ?_
    calc (1 + t / 4) ^ ‖ε‖ ≤ (1 + t / 4) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by linarith)
      _ ≤ 2 := by rw [Real.rpow_one]; linarith [ht.2]
  rw [norm_mul, norm_pow]
  calc ‖(t : ℂ) ^ (1 - ε)‖ * ‖i13Bub ε t‖ ^ 2 ≤ 1 * 2 ^ 2 :=
        mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity) zero_le_one
    _ = 4 := by norm_num

/-- **`Rem` to order `ε⁴`, with the coefficients as integrals**:
`Rem(ε) = ∑_{k < 5} cₖ εᵏ + ε⁵ R(ε)`, `R` holomorphic at `0`. -/
theorem hasTruncLaurent_i13Rem_coeff :
    HasTruncLaurent i13Rem (fun ε => ∑ k ∈ Finset.range 5, i13RemCoeff k * ε ^ k) 5 := by
  obtain ⟨K, hK⟩ := norm_i13RemInt2_le
  have H1 := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (h := i13RemInt1) (R := 1 / 5) (ρ := 1 / 10) (M := fun _ => 4) (by norm_num) (by norm_num)
    (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      (differentiable_i13RemInt1 ht.1).differentiableOn)
    (fun ε _ => (measurable_i13RemInt1 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ε hε =>
      norm_i13RemInt1_le ht hε.le) 5
  have H2 := hasTruncLaurent_integral_i13Dsl (μ := volume.restrict (Ioi (1 : ℝ)))
    (h := i13RemInt2) (R := 1 / 5) (ρ := 1 / 10) (M := fun t => K * t ^ ((3 : ℝ) / 10 - 2))
    (by norm_num) (by norm_num)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul K)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      differentiableOn_i13RemInt2 (zero_lt_one.trans ht))
    (fun ε _ => (measurable_i13RemInt2 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ε hε =>
      hK ε hε.le t (le_of_lt ht)) 5
  obtain ⟨R1, hR1, e1⟩ := H1
  obtain ⟨R2, hR2, e2⟩ := H2
  refine ⟨fun ε => R1 ε + R2 ε, hR1.add hR2, ?_⟩
  filter_upwards [e1, e2] with ε h1 h2
  rw [show i13Rem ε = (∫ t in Ioo (0 : ℝ) 1, i13RemInt1 t ε) +
    ∫ t in Ioi (1 : ℝ), i13RemInt2 t ε from rfl, h1, h2]
  unfold i13RemCoeff
  simp only [add_mul, Finset.sum_add_distrib]
  ring

end QED.ThreeLoopD
