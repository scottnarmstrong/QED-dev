/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RemAsy1

/-!
# Set (d), master `I₁₃`: the large-`t` expansion of the bubble

With `u = t ^ (-ε)` and the coefficients `α₀, α₁, α₂, β₀, β₁` of
`QED.ThreeLoopD.SetDMastersI13Def`, the truncation

  `S_ε(t) = α₀ u + (α₁ u + β₀)/t + (α₂ u + β₁)/t²`  (`QED.ThreeLoopD.i13BubAsym`)

approximates the bubble to `O(t ^ (-3 + 1/10))`, uniformly in `‖ε‖ ≤ 1/10`, `t ≥ 1`
(`QED.ThreeLoopD.norm_i13Bub_sub_asym_le`). The error is the exact combination
`δ³ (τ ^ (-ε) M₁ - Q₃) + τ ^ (-ε) R_ψ` (`τ = t/4`, `δ = 4/t`) of the remainders of
`QED.ThreeLoopD.SetDMastersI13RemAsy1` (`QED.ThreeLoopD.i13Bub_sub_asym_eq`); the leading
coefficients are identified through `QED.ThreeLoopD.i13Lc_gamma`.

## Main results

* `QED.ThreeLoopD.i13Bub_sub_asym_eq`.
* `QED.ThreeLoopD.norm_i13Bub_sub_asym_le`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- The rational part `c₀` of `A₀`. -/
noncomputable def i13Cc0 (ε : ℂ) : ℂ := 1 / 2 / (1 - ε) + 1 / 4 / (2 - ε) + 3 / 16 / (3 - ε)

/-- The rational part `c₁` of `A₁`. -/
noncomputable def i13Cc1 (ε : ℂ) : ℂ := 1 / 2 - ε / 4 / (1 - ε) - 3 / 16 * ε / (2 - ε)

/-- The rational part `c₂` of `A₂`. -/
noncomputable def i13Cc2 (ε : ℂ) : ℂ := -ε / 4 - (1 + ε) / 8 + 3 / 32 * ε * (1 + ε) / (1 - ε)

theorem i13Lc_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    i13Lc0 ε = i13Cc0 ε + i13PsiInt (1 - ε - 0) ∧
      i13Lc1 ε = i13Cc1 ε - ε * i13PsiInt (1 - ε - 1) ∧
      i13Lc2 ε = i13Cc2 ε + ε * (ε + 1) / 2 * i13PsiInt (1 - ε - 2) := by
  obtain ⟨h1, h2, h3, -⟩ := i13_eps_facts hε
  unfold i13Lc0 i13Lc1 i13Lc2 i13FPhi i13Cc0 i13Cc1 i13Cc2
  rw [show 1 - ε - 0 = 1 - ε by ring, show 1 - ε - 1 = -ε by ring,
    show 1 - ε - 2 = -1 - ε by ring]
  refine ⟨?_, ?_, ?_⟩ <;> (field_simp; ring)

/-- The polynomial part `H` of the third-order remainder of `(1 + δ) ^ (-ε) Q(1 + δ)`. -/
noncomputable def i13Hb (ε : ℂ) (δ : ℝ) : ℂ :=
  (6 * δ ^ 2 * ε ^ 2 + 6 * δ ^ 2 * ε + 10 * δ * ε ^ 3 - 2 * δ * ε ^ 2 - 24 * δ * ε + 15 * ε ^ 4 -
    40 * ε ^ 3 - 27 * ε ^ 2 + 72 * ε + 12) / (32 * ((1 - ε) * (2 - ε) * (3 - ε)))

/-- The third-order remainder `M₁ = K B₃(-ε, δ) Q(1 + δ) + H` of `(1 + δ) ^ (-ε) Q(1 + δ)`. -/
noncomputable def i13M1 (ε : ℂ) (δ : ℝ) : ℂ :=
  (-ε) * (-ε - 1) * (-ε - 2) / 2 * i13Bin3 (-ε) δ * i13Qp ε δ (1 + δ) + i13Hb ε δ

/-- The `δ³` coefficient `Q₃` of `Q(δ)`. -/
noncomputable def i13Q3 (ε : ℂ) : ℂ := 3 / (8 * ((1 - ε) * (2 - ε) * (3 - ε)))

/-- The remainder `R_ψ` of the `ψ` part. -/
noncomputable def i13Rpsi (ε : ℂ) (δ : ℝ) : ℂ :=
  (∫ w in Ioo (0 : ℝ) 1, ((δ + w : ℝ) : ℂ) ^ (-ε) * ((w ^ 3 * i13Psi w : ℝ) : ℂ)) -
    (i13PsiInt (1 - ε - 0) - ε * δ * i13PsiInt (1 - ε - 1) +
      ε * (ε + 1) / 2 * δ ^ 2 * i13PsiInt (1 - ε - 2))

/-- **The large-`t` truncation** `S_ε(t) = α₀ u + (α₁ u + β₀)/t + (α₂ u + β₁)/t²`. -/
noncomputable def i13BubAsym (ε : ℂ) (t : ℝ) : ℂ :=
  i13Al0 ε * (t : ℂ) ^ (-ε) + (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) / t +
    (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / t ^ 2

theorem i13PhiP_bounds {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 ≤ i13PhiP w ∧ i13PhiP w ≤ i13Phi w := by
  have h := i13Phi_eq_P_add hw.1.ne'
  have := mul_nonneg (pow_nonneg hw.1.le 3) (i13Psi_nonneg hw)
  unfold i13PhiP
  constructor
  · nlinarith [hw.1]
  · linarith

/-- **The exact error of the truncation.** -/
theorem i13Bub_sub_asym_eq {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 0 < t) :
    i13Bub ε t - i13BubAsym ε t =
      ((4 / t : ℝ) : ℂ) ^ 3 * (((t / 4 : ℝ) : ℂ) ^ (-ε) * i13M1 ε (4 / t) - i13Q3 ε) +
        ((t / 4 : ℝ) : ℂ) ^ (-ε) * i13Rpsi ε (4 / t) := by
  have hε2 : ‖ε‖ < 1 / 2 := by linarith
  obtain ⟨h1, h2, h3, -⟩ := i13_eps_facts hε2
  set δ : ℝ := 4 / t with hδ
  have hδ0 : 0 < δ := by positivity
  -- `b = τ ^ (-ε) ∫ (δ + w) ^ (-ε) φ`
  have hb : i13Bub ε t = ((t / 4 : ℝ) : ℂ) ^ (-ε) *
      ((∫ w in Ioo (0 : ℝ) 1, ((δ + w : ℝ) : ℂ) ^ (-ε) * (i13PhiP w : ℂ)) +
        ∫ w in Ioo (0 : ℝ) 1, ((δ + w : ℝ) : ℂ) ^ (-ε) * ((w ^ 3 * i13Psi w : ℝ) : ℂ)) := by
    have iP := integrableOn_i13_shift_mul hε2.le hδ0 (g := i13PhiP) (by unfold i13PhiP; fun_prop)
      fun w hw => by
        rw [abs_of_nonneg (i13PhiP_bounds hw).1]; exact (i13PhiP_bounds hw).2
    have iψ := integrableOn_i13_shift_mul hε2.le hδ0 (g := fun w => w ^ 3 * i13Psi w)
      (by fun_prop) fun w hw => by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg hw.1.le 3) (i13Psi_nonneg hw))]
        have : w ^ 3 ≤ 1 := pow_le_one₀ hw.1.le hw.2.le
        nlinarith [i13Psi_nonneg hw, i13Psi_le hw]
    rw [← integral_add iP iψ, ← integral_const_mul, i13Bub_eq_w ε ht.le]
    refine setIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have hsplit : 1 + t * w / 4 = t / 4 * (δ + w) := by rw [hδ]; field_simp
    rw [hsplit, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (by linarith [hw.1]),
      i13Phi_eq_P_add hw.1.ne']
    unfold i13PhiP
    push_cast
    ring
  -- the pieces
  have hP := i13_integral_PhiP hε2 hδ0
  have hT := i13_cpow_taylor3 (-ε) hδ0.le
  have hXY : ((t / 4 : ℝ) : ℂ) ^ (-ε) * (δ : ℂ) ^ (-ε) = 1 := by
    rw [← mul_cpow_ofReal_nonneg (by positivity) hδ0.le,
      show ((t / 4 : ℝ) : ℂ) * (δ : ℂ) = 1 by
        rw [hδ]; push_cast; field_simp [ofReal_ne_zero.mpr ht.ne'], one_cpow]
  have hU : (t : ℂ) ^ (-ε) = ((t / 4 : ℝ) : ℂ) ^ (-ε) * (((4 : ℝ) : ℂ) ^ ε)⁻¹ := by
    rw [← cpow_neg, mul_comm, ← mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    · congr 2; push_cast; ring
  obtain ⟨g0, g1, g2⟩ := i13Lc_gamma hε2
  obtain ⟨l0, l1, l2⟩ := i13Lc_eq hε2
  have hX0 : ((t / 4 : ℝ) : ℂ) ^ (-ε) ≠ 0 := by
    intro h; rw [h, zero_mul] at hXY; exact zero_ne_one hXY
  have hY : (δ : ℂ) ^ (-ε) = (((t / 4 : ℝ) : ℂ) ^ (-ε))⁻¹ := eq_inv_of_mul_eq_one_right hXY
  have hF := i13_four_cpow_ne_zero ε
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have he1 : ε - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  have he2 : ε - 2 ≠ 0 := fun h => h2 (by linear_combination -h)
  rw [hb, hP, hT, hY]
  unfold i13BubAsym i13M1 i13Rpsi i13Q3 i13Hb
  rw [hU, ← g0, ← g1, ← g2, l0, l1, l2]
  unfold i13Be0 i13Be1 i13Cc0 i13Cc1 i13Cc2 i13Qp
  rw [hδ]
  generalize ((t / 4 : ℝ) : ℂ) ^ (-ε) = X at hX0 ⊢
  generalize ((4 : ℝ) : ℂ) ^ ε = F at hF ⊢
  generalize i13Bin3 (-ε) (4 / t) = B
  generalize i13PsiInt (1 - ε - 0) = Ψ₀
  generalize i13PsiInt (1 - ε - 1) = Ψ₁
  generalize i13PsiInt (1 - ε - 2) = Ψ₂
  push_cast
  field_simp
  ring

/-! ### The bound -/

theorem i13_exists_bound_of_continuous {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : 0 ≤ M) : ∃ C, ∀ x : Fin n → ℂ, (∀ i, ‖x i‖ ≤ M) → ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℂ) M).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨C, fun x hx => hC x (mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg hM).mpr hx))⟩

theorem i13_norm_inv_sub_le {c : ℝ} (hc : 1 ≤ c) {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 2) :
    ‖((c : ℂ) - ε)⁻¹‖ ≤ 2 := by
  have h : 1 / 2 ≤ ‖(c : ℂ) - ε‖ := by
    have := norm_sub_norm_le (c : ℂ) ε
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith
  rw [norm_inv]
  calc ‖(c : ℂ) - ε‖⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 2 := by norm_num

/-- `M₁` and `Q₃` are bounded on `‖ε‖ ≤ 1/10`, `0 < δ ≤ 4`. -/
theorem i13_bound_M1 : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ∀ δ : ℝ, 0 < δ → δ ≤ 4 →
    ‖i13M1 ε δ‖ ≤ C ∧ ‖i13Q3 ε‖ ≤ C := by
  set g : (Fin 6 → ℂ) → ℂ := fun x =>
    (-x 0) * (-x 0 - 1) * (-x 0 - 2) / 2 * x 1 *
      ((1 / 2 - x 2 / 4 + 3 / 16 * x 2 ^ 2) * (1 + x 2) * x 3 +
        (1 / 4 - 3 / 8 * x 2) * (1 + x 2) ^ 2 * x 4 + 3 / 16 * (1 + x 2) ^ 3 * x 5) +
    (6 * x 2 ^ 2 * x 0 ^ 2 + 6 * x 2 ^ 2 * x 0 + 10 * x 2 * x 0 ^ 3 - 2 * x 2 * x 0 ^ 2 -
      24 * x 2 * x 0 + 15 * x 0 ^ 4 - 40 * x 0 ^ 3 - 27 * x 0 ^ 2 + 72 * x 0 + 12) / 32 *
      (x 3 * x 4 * x 5) with hg
  set q : (Fin 6 → ℂ) → ℂ := fun x => 3 / 8 * (x 3 * x 4 * x 5) with hq
  obtain ⟨C₁, hC₁⟩ := i13_exists_bound_of_continuous (g := g) (by rw [hg]; fun_prop)
    (M := 4) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := i13_exists_bound_of_continuous (g := q) (by rw [hq]; fun_prop)
    (M := 4) (by norm_num)
  refine ⟨max C₁ C₂, fun ε hε δ hδ hδ4 => ?_⟩
  have hε2 : ‖ε‖ ≤ 1 / 2 := by linarith
  obtain ⟨h1, h2, h3, -⟩ := i13_eps_facts (by linarith : ‖ε‖ < 1 / 2)
  set x : Fin 6 → ℂ := ![ε, i13Bin3 (-ε) δ, (δ : ℂ), (1 - ε)⁻¹, (2 - ε)⁻¹, (3 - ε)⁻¹] with hx
  have hxb : ∀ i, ‖x i‖ ≤ 4 := by
    have a1 := i13_norm_inv_sub_le (c := 1) le_rfl hε2
    have a2 := i13_norm_inv_sub_le (c := 2) (by norm_num) hε2
    have a3 := i13_norm_inv_sub_le (c := 3) (by norm_num) hε2
    push_cast at a1 a2 a3
    have hB := norm_i13Bin3_le (c := -ε) (u := δ) (by
      rw [neg_re]; linarith [abs_re_le_norm ε, neg_abs_le ε.re]) hδ.le
    intro i
    fin_cases i <;> simp [x]
    · linarith
    · linarith
    · rw [abs_of_pos hδ]; exact hδ4
    all_goals (rw [← norm_inv]; linarith)
  have eM : i13M1 ε δ = g x := by
    simp only [hg, hx, i13M1, i13Hb, i13Qp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    push_cast
    field_simp
  have eQ : i13Q3 ε = q x := by
    simp only [hq, hx, i13Q3, Matrix.cons_val]
    field_simp
  rw [eM, eQ]
  exact ⟨(hC₁ x hxb).trans (le_max_left _ _), (hC₂ x hxb).trans (le_max_right _ _)⟩

theorem i13_norm_tau_cpow_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 1 ≤ t) :
    ‖((t / 4 : ℝ) : ℂ) ^ (-ε)‖ ≤ 2 * t ^ ((1 : ℝ) / 10) := by
  have hre : |ε.re| ≤ 1 / 10 := (abs_re_le_norm ε).trans hε
  rw [norm_cpow_eq_rpow_re_of_pos (by positivity), Real.div_rpow (by positivity) (by norm_num),
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num), mul_comm]
  have h1 : t ^ (-ε).re ≤ t ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le ht (by rw [neg_re]; linarith [neg_abs_le ε.re])
  have h2 : (4 : ℝ) ^ (-(-ε).re) ≤ 2 := by
    calc (4 : ℝ) ^ (-(-ε).re) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            rw [neg_re, neg_neg]; linarith [le_abs_self ε.re])
      _ = 2 := by
          rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  exact mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith) _) (by norm_num)

theorem i13CPhi_nonneg : 0 ≤ i13CPhi :=
  setIntegral_nonneg measurableSet_Ioo fun _ hw =>
    mul_nonneg (Real.rpow_nonneg hw.1.le _) (i13Phi_pos hw.2).le

/-- **The large-`t` expansion of the bubble**: `‖b_ε(t) - S_ε(t)‖ ≤ C t ^ (1/10 - 3)` for
`‖ε‖ ≤ 1/10`, `t ≥ 1`. -/
theorem norm_i13Bub_sub_asym_le : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ∀ t : ℝ, 1 ≤ t →
    ‖i13Bub ε t - i13BubAsym ε t‖ ≤ C * t ^ ((1 : ℝ) / 10 - 3) := by
  obtain ⟨C, hC⟩ := i13_bound_M1
  refine ⟨128 * (2 * C + i13CPhi), fun ε hε t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hδ : 0 < 4 / t := by positivity
  have hδ4 : 4 / t ≤ 4 := by rw [div_le_iff₀ ht0]; linarith
  obtain ⟨hM, hQ⟩ := hC ε hε (4 / t) hδ hδ4
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hQ
  have hR := norm_i13_integral_Psi_sub_le hε hδ
  have hX := i13_norm_tau_cpow_le hε ht
  have ht1 : 1 ≤ t ^ ((1 : ℝ) / 10) := Real.one_le_rpow ht (by norm_num)
  rw [i13Bub_sub_asym_eq hε ht0]
  have hd3 : ‖((4 / t : ℝ) : ℂ) ^ 3‖ = (4 / t) ^ 3 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hpow : (4 / t) ^ 3 * t ^ ((1 : ℝ) / 10) = 64 * t ^ ((1 : ℝ) / 10 - 3) := by
    rw [Real.rpow_sub ht0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    norm_num
  calc ‖((4 / t : ℝ) : ℂ) ^ 3 * (((t / 4 : ℝ) : ℂ) ^ (-ε) * i13M1 ε (4 / t) - i13Q3 ε) +
        ((t / 4 : ℝ) : ℂ) ^ (-ε) * i13Rpsi ε (4 / t)‖
      ≤ (4 / t) ^ 3 * (2 * t ^ ((1 : ℝ) / 10) * C + C) +
          2 * t ^ ((1 : ℝ) / 10) * ((4 / t) ^ 3 * i13CPhi) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, hd3]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ hQ))
            (by positivity)
          rw [norm_mul]
          exact mul_le_mul hX hM (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          exact mul_le_mul hX hR (norm_nonneg _) (by positivity)
    _ ≤ (4 / t) ^ 3 * t ^ ((1 : ℝ) / 10) * (2 * (2 * C + i13CPhi)) := by
        have := i13CPhi_nonneg
        have h4 : 0 ≤ (4 / t) ^ 3 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left ht1 (mul_nonneg h4 hC0)]
    _ = 128 * (2 * C + i13CPhi) * t ^ ((1 : ℝ) / 10 - 3) := by rw [hpow]; ring

end QED.ThreeLoopD
