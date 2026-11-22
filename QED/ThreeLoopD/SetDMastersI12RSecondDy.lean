/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondR1y
public import QED.ThreeLoopD.SetDMastersI12RSecondPair

/-!
# Set (d), master `I₁₂`: `R₁'(0) + B3bad` on `(0, 1/2)`

`R₁'(0) = ∫₀¹ i12R1F` (`QED.ThreeLoopD.deriv_i12R1_zero_eq`) with `i12R1F(1 - y) = i12R1F(y)`,
and `i12R1F y = K(c)/c + i12R1Elem y` (`c = y(1 - y)`, `QED.ThreeLoopD.i12R1F_eq`). The
substitution `x = 2y` turns `B3bad = ∫₀¹ i12B3bad` into
`∫₀^{1/2} (2K(y)/y - 2K(c)/c) dy`. Folding `∫₀¹ i12R1F` onto `(0, 1/2)`, the `K(c)/c` terms
cancel pointwise, so no separate integrability of `K(y)/y` or `K(c)/c` is needed:

  `R₁'(0) + B3bad = 2 ∫₀^{1/2} (i12R1Elem y + K(y)/y) dy`.

## Main results

* `QED.ThreeLoopD.deriv_i12R1_add_i12B3bad`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The elementary-plus-`E` part of `i12R1F` (after the pairing), `c = y(1 - y)`. -/
noncomputable def i12R1Elem (y : ℝ) : ℝ :=
  -(1 / 6) * log (y * (1 - y)) + 329 / 36 - π ^ 2 + (3 * log (y * (1 - y)) + 3 * π ^ 2 - 3 / 2 +
    3 * log (y * (1 - y)) ^ 2 + i12RE (y * (1 - y))) / (y * (1 - y))

theorem i12R1F_one_sub (y : ℝ) : i12R1F (1 - y) = i12R1F y := by
  simp only [i12R1F, show (1 - y) * (1 - (1 - y)) = y * (1 - y) by ring]

/-- **`R₁'(0) + B3bad` on `(0, 1/2)`**: the `K(c)/c` terms cancel pointwise, leaving
`2 ∫₀^{1/2} (i12R1Elem y + K(y)/y) dy`. -/
theorem deriv_i12R1_add_i12B3bad :
    IntervalIntegrable (fun y => i12R1Elem y + i12RK y / y) volume 0 (1 / 2) ∧
      deriv i12R1 0 + ((∫ x in Ioo (0 : ℝ) 1, i12B3bad x : ℝ) : ℂ) =
        ((2 * ∫ y in (0 : ℝ)..(1 / 2), (i12R1Elem y + i12RK y / y) : ℝ) : ℂ) := by
  obtain ⟨hF, hFv⟩ := deriv_i12R1_zero_eq
  obtain ⟨hbad, -⟩ := deriv_i12RA3_add_i12RBB3
  have hF01 : IntervalIntegrable i12R1F volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hF
  have hb01 : IntervalIntegrable i12B3bad volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hbad
  have hFa : IntervalIntegrable i12R1F volume 0 (1 / 2) :=
    hF01.mono_set (by rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
                      exact Icc_subset_Icc le_rfl (by norm_num))
  have hFb : IntervalIntegrable i12R1F volume (1 / 2) 1 :=
    hF01.mono_set (by rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
                      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hFr : IntervalIntegrable (fun y => i12R1F (1 - y)) volume 0 (1 / 2) := by
    have h := hFb.comp_sub_left 1
    norm_num at h
    exact h.symm
  have hbs : IntervalIntegrable (fun y => i12B3bad (2 * y)) volume 0 (1 / 2) := by
    have h := hb01.comp_mul_left (c := 2)
    norm_num at h
    exact h
  have hpt : ∀ y ∈ Ioo (0 : ℝ) (1 / 2), i12R1F y + i12R1F (1 - y) + 2 * i12B3bad (2 * y) =
      2 * (i12R1Elem y + i12RK y / y) := by
    intro y hy
    have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    have h1 : 0 < 1 - y := by linarith [hy.2]
    rw [i12R1F_one_sub, i12R1F_eq hy']
    simp only [i12B3bad, i12R1Elem, show 2 * y / 2 = y by ring,
      show 2 * y * (2 - 2 * y) / 4 = y * (1 - y) by ring]
    have := hy.1.ne'
    have := h1.ne'
    have : (2 : ℝ) - 2 * y ≠ 0 := by linarith [hy.2]
    field_simp
    ring
  have hsum : IntervalIntegrable (fun y => i12R1F y + i12R1F (1 - y) + 2 * i12B3bad (2 * y))
      volume 0 (1 / 2) := (hFa.add hFr).add (hbs.const_mul 2)
  have hE : IntervalIntegrable (fun y => i12R1Elem y + i12RK y / y) volume 0 (1 / 2) := by
    have h := hsum.const_mul (1 / 2)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at h ⊢
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [hpt y hy]
    ring
  refine ⟨hE, ?_⟩
  have hIoo : ∀ {f : ℝ → ℝ}, ∫ y in (0 : ℝ)..(1 / 2), f y = ∫ y in Ioo (0 : ℝ) (1 / 2), f y :=
    fun {f} => by rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hI : ∫ y in (0 : ℝ)..(1 / 2), (i12R1F y + i12R1F (1 - y) + 2 * i12B3bad (2 * y)) =
      2 * ∫ y in (0 : ℝ)..(1 / 2), (i12R1Elem y + i12RK y / y) := by
    rw [← intervalIntegral.integral_const_mul, hIoo, hIoo]
    exact setIntegral_congr_fun measurableSet_Ioo hpt
  have hFs : ∫ y in Ioo (0 : ℝ) 1, i12R1F y =
      (∫ y in (0 : ℝ)..(1 / 2), i12R1F y) + ∫ y in (0 : ℝ)..(1 / 2), i12R1F (1 - y) := by
    rw [intervalIntegral.integral_comp_sub_left i12R1F, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    norm_num
    exact (intervalIntegral.integral_add_adjacent_intervals hFa hFb).symm
  have hbs' : ∫ x in Ioo (0 : ℝ) 1, i12B3bad x = 2 * ∫ y in (0 : ℝ)..(1 / 2), i12B3bad (2 * y) := by
    rw [intervalIntegral.integral_comp_mul_left i12B3bad (by norm_num : (2 : ℝ) ≠ 0),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    norm_num
    ring
  rw [hFv, ← Complex.ofReal_add, hFs, hbs', ← hI, intervalIntegral.integral_add (hFa.add hFr)
    (hbs.const_mul 2), intervalIntegral.integral_add hFa hFr, intervalIntegral.integral_const_mul]

end QED.ThreeLoopD
