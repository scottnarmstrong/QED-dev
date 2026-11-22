/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondRA
public import QED.ThreeLoopD.SetDMastersI12RSecondRB
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Set (d), master `I₁₂`: `R_A'(0) + B₃` by the inversion pairing of `K`

`R_A'(0) = ∫₀¹ (m (2 Li₂ ρ + K(m)) - 2 K(2)) / ρ dρ` with `m = 4 / (2 - ρ)`
(`QED.ThreeLoopD.deriv_i12RA3_zero_eq`), and the third piece of `R_B'(0)` is
`B₃ = ∫₀¹ (m K(1/m) - m K(x(2 - x)/4) - 2 K(1/2) + 2 K(x/2)) / x dx`
(`QED.ThreeLoopD.deriv_i12RB3_zero_eq`, `m = 4/(2 - x)`). Pointwise in the common variable, the
pairing `K(m) + K(1/m) = -6 - 2π² - 3 log² m` (`QED.ThreeLoopD.i12RK_add_i12RK_inv`, at `m` and
at `2`) removes every value of `K` at arguments `≥ 1/2`:

  `R_A'(0) + B₃ = J + B₃ᵇ`,
  `J = ∫₀¹ (2 m Li₂ ρ - (6 + 2π²)(m - 2) - 3 m log² m + 6 log² 2) / ρ dρ`,
  `B₃ᵇ = ∫₀¹ (2 K(x/2) - m K(x(2 - x)/4)) / x dx`.

The integrand of `J` is integrable: it is `4 Li₂ ρ / ρ + 4 Li₂ ρ / (2 - ρ)` plus a bounded
function (with `L = log (1 - ρ/2)`, `|L| ≤ ρ`, the logarithmic part is
`(12 L log 2 - 6 L² - 3 ρ log² 2) / (ρ (1 - ρ/2))`); the integrand of `B₃ᵇ` is then integrable
as a difference.

## Main results

* `QED.ThreeLoopD.deriv_i12RA3_add_i12RBB3`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The integrand of `J`. -/
noncomputable def i12PairJ (ρ : ℝ) : ℝ :=
  (2 * (4 / (2 - ρ)) * Li₂ ρ - (6 + 2 * π ^ 2) * (4 / (2 - ρ) - 2) -
    3 * (4 / (2 - ρ)) * Real.log (4 / (2 - ρ)) ^ 2 + 6 * Real.log 2 ^ 2) / ρ

/-- The integrand of `B₃ᵇ`. -/
noncomputable def i12B3bad (x : ℝ) : ℝ :=
  (2 * i12RK (x / 2) - 4 / (2 - x) * i12RK (x * (2 - x) / 4)) / x

/-- The elementary part of the integrand of `J`. -/
noncomputable def i12PairJe (ρ : ℝ) : ℝ :=
  (-(6 + 2 * π ^ 2) * (4 / (2 - ρ) - 2) - 3 * (4 / (2 - ρ)) * Real.log (4 / (2 - ρ)) ^ 2 +
    6 * Real.log 2 ^ 2) / ρ

theorem abs_i12PairJe_le {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) : |i12PairJe ρ| ≤ 100 := by
  have h2 : 0 < 2 - ρ := by linarith [hρ.2]
  have hh : 0 < 1 - ρ / 2 := by linarith [hρ.2]
  set L := Real.log (1 - ρ / 2) with hL
  have hLb := abs_log_one_sub_half_le hρ
  have hlog : Real.log (4 / (2 - ρ)) = Real.log 2 - L := by
    rw [hL, ← Real.log_div (by norm_num) hh.ne']
    congr 1; field_simp; ring
  have e : i12PairJe ρ = -(6 + 2 * π ^ 2) * (2 / (2 - ρ)) +
      (12 * Real.log 2 * L - 6 * L ^ 2 - 3 * Real.log 2 ^ 2 * ρ) / (ρ * (1 - ρ / 2)) := by
    simp only [i12PairJe, hlog]
    field_simp [hρ.1.ne']
    ring
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hA : |-(6 + 2 * π ^ 2) * (2 / (2 - ρ))| ≤ 52 := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    have : 2 / (2 - ρ) ≤ 2 := by rw [div_le_iff₀ h2]; linarith [hρ.1, hρ.2]
    nlinarith [sq_nonneg π]
  have hB : |(12 * Real.log 2 * L - 6 * L ^ 2 - 3 * Real.log 2 ^ 2 * ρ) / (ρ * (1 - ρ / 2))| ≤
      42 := by
    have hd : 0 < ρ * (1 - ρ / 2) := mul_pos hρ.1 hh
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
    have hL2 : L ^ 2 ≤ ρ ^ 2 := by
      have := sq_abs L; nlinarith [abs_nonneg L, hρ.1]
    have hN : |12 * Real.log 2 * L - 6 * L ^ 2 - 3 * Real.log 2 ^ 2 * ρ| ≤
        12 * ρ + 6 * ρ ^ 2 + 3 * ρ := by
      have hm : |Real.log 2 * L| ≤ ρ := by
        rw [abs_mul, abs_of_pos hl20]; nlinarith [abs_nonneg L]
      have hm' := abs_le.1 hm
      have hq1 : Real.log 2 ^ 2 ≤ 1 := by nlinarith
      have hq : Real.log 2 ^ 2 * ρ ≤ ρ := by nlinarith [hρ.1]
      have hq0 : 0 ≤ Real.log 2 ^ 2 * ρ := mul_nonneg (sq_nonneg _) hρ.1.le
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg L, hρ.1, hρ.2]
    nlinarith [hρ.1, hρ.2]
  rw [e]
  exact (abs_add_le _ _).trans (by linarith)

theorem integrableOn_i12PairJ : IntegrableOn i12PairJ (Ioo 0 1) := by
  have hfin : volume (Ioo (0 : ℝ) 1) ≠ ⊤ := by simp
  have he : IntegrableOn i12PairJe (Ioo 0 1) :=
    Measure.integrableOn_of_bounded (M := 100) hfin
      (Measurable.aestronglyMeasurable (by unfold i12PairJe; fun_prop))
      (ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ => by
        rw [Real.norm_eq_abs]; exact abs_i12PairJe_le hρ)
  have hl : IntegrableOn (fun ρ => Li₂ ρ / ρ) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      intervalIntegrable_and_integral_Li₂_div.1
  have hc : ContinuousOn (fun ρ => Li₂ ρ / (2 - ρ)) (Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.div (continuousOn_Li₂.mono fun ρ hρ => ⟨?_, hρ.2.le⟩) (by fun_prop)
      fun ρ hρ => ?_
    · linarith [hρ.1]
    · linarith [hρ.2]
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [isFiniteMeasure_restrict]; exact hfin
  have hb : IntegrableOn (fun ρ => Li₂ ρ / (2 - ρ)) (Ioo 0 1) :=
    Integrable.of_bound (hc.aestronglyMeasurable measurableSet_Ioo) (π ^ 2 / 6)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ => by
        have h1 : 1 ≤ 2 - ρ := by linarith [hρ.2]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 - ρ)]
        exact (div_le_self (abs_nonneg _) h1).trans
          (abs_Li₂_le_of_mem ⟨by linarith [hρ.1], hρ.2.le⟩))
  refine (show IntegrableOn (fun ρ => 4 * (Li₂ ρ / ρ) + (4 * (Li₂ ρ / (2 - ρ)) + i12PairJe ρ))
    (Ioo 0 1) volume from (hl.const_mul 4).add ((hb.const_mul 4).add he)).congr_fun
    (fun ρ hρ => ?_) measurableSet_Ioo
  simp only [i12PairJ, i12PairJe]
  field_simp [hρ.1.ne', show (2 - ρ) ≠ 0 by linarith [hρ.2]]
  ring

/-- **`R_A'(0) + B₃ = J + B₃ᵇ`**, with both integrands integrable. -/
theorem deriv_i12RA3_add_i12RBB3 :
    IntegrableOn i12B3bad (Ioo 0 1) ∧
      deriv i12RA3 0 + ((∫ x in Ioo (0 : ℝ) 1, i12RBB3 x : ℝ) : ℂ) =
        (((∫ ρ in Ioo (0 : ℝ) 1, i12PairJ ρ) + ∫ x in Ioo (0 : ℝ) 1, i12B3bad x : ℝ) : ℂ) := by
  obtain ⟨hA, hAv⟩ := deriv_i12RA3_zero_eq
  obtain ⟨-, -, hB3, -⟩ := deriv_i12RB3_zero_eq
  have hJ := integrableOn_i12PairJ
  have hpt : ∀ x ∈ Ioo (0 : ℝ) 1,
      (1 / i12H x * (2 * Li₂ x + i12RK (1 / i12H x)) - 2 * i12RK 2) / x + i12RBB3 x -
        i12PairJ x = i12B3bad x := by
    intro x hx
    have h2 : (2 - x) ≠ 0 := by linarith [hx.2]
    have hm : 0 < 4 / (2 - x) := div_pos (by norm_num) (by linarith [hx.2])
    have hp := i12RK_add_i12RK_inv hm
    have hp2 := i12RK_add_i12RK_inv (show (0 : ℝ) < 2 by norm_num)
    have e1 : 1 / i12H x = 4 / (2 - x) := by unfold i12H; field_simp
    have e2 : 1 / (4 / (2 - x)) = (2 - x) / 4 := by field_simp
    rw [e2] at hp
    rw [show (1 : ℝ) / 2 = 1 / 2 from rfl] at hp2
    simp only [i12RBB3, i12PairJ, i12B3bad, e1]
    field_simp [hx.1.ne']
    linear_combination 4 * hp + (2 * x - 4) * hp2
  have hbad : IntegrableOn i12B3bad (Ioo 0 1) := ((hA.add hB3).sub hJ).congr_fun hpt
    measurableSet_Ioo
  refine ⟨hbad, ?_⟩
  rw [hAv, ← Complex.ofReal_add]
  congr 1
  rw [← integral_add hA hB3, ← integral_add hJ hbad]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have := hpt x hx
  linarith

end QED.ThreeLoopD
