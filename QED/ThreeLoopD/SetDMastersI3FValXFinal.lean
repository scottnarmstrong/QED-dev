/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FValXAlpha
public import QED.ThreeLoopD.SetDMastersI3FValXInt

/-!
# Set (d), master `I₃`: the last integral

After the `α`-integration, `i3FInt 0` is the integral over `t ∈ (0, 1)` of

  `g(t) = log ((1 - t)/t) (1 - 2t) / (t (1 - t)) · J(t)`,  `J = 2 (t A - (1 - t) B)/(2t - 1)`,

`A = Li₂(-(1 - t)/t)`, `B = Li₂(-t/(1 - t))` (`QED.ThreeLoopD.i3XJ`). By Landen's identity
`B = -Li₂ t - log² (1 - t)/2` and `A = -Li₂ (1 - t) - log² t/2`, so `g(t) = 2 (F(t) + F(1 - t))`
off `t = 1/2` with `F = QED.ThreeLoopD.i3XF`, and `∫₀¹ g = 4 ∫₀¹ F = 4 π⁴/30 = 2π⁴/15`.

## Main results

* `QED.ThreeLoopD.i3X_lintegral_final`: `∫₀¹ g = 2π⁴/15` (as a lower integral).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal
open QED.Polylog QED.TwoLoop.UnitXClose

namespace QED.ThreeLoopD

/-- The integrand of the last integration. -/
noncomputable def i3XG (t : ℝ) : ℝ := log ((1 - t) / t) * (1 - 2 * t) / (t * (1 - t)) * i3XJ t

theorem i3XG_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hd : t ≠ 1 / 2) :
    i3XG t = 2 * (i3XF t + i3XF (1 - t)) := by
  obtain ⟨h0, h1⟩ := ht
  have hy : 0 < 1 - t := by linarith
  have hdd : t - (1 - t) ≠ 0 := fun h => hd (by linarith)
  have hB := i3X_dilogI_landen ⟨h0, h1⟩
  have hA := i3X_dilogI_landen (x := 1 - t) ⟨hy, by linarith⟩
  rw [sub_sub_cancel] at hA
  have e1 : dilogI t = Li 2 t := dilogI_eq_Li₂ ⟨by linarith, h1⟩
  have e2 : dilogI (1 - t) = Li 2 (1 - t) := dilogI_eq_Li₂ ⟨by linarith, by linarith⟩
  simp only [i3XG, i3XJ, i3XF, sub_sub_cancel]
  rw [hA, hB, e1, e2, log_div hy.ne' h0.ne']
  field_simp
  ring

theorem i3XG_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hd : t ≠ 1 / 2) : 0 ≤ i3XG t := by
  obtain ⟨h0, h1⟩ := ht
  have hy : 0 < 1 - t := by linarith
  have hJ := i3XJ_nonneg ⟨h0, h1⟩ hd
  have hl : 0 ≤ log ((1 - t) / t) * (1 - 2 * t) := by
    rcases lt_or_gt_of_ne hd with h | h
    · have : 1 < (1 - t) / t := by rw [one_lt_div h0]; linarith
      exact mul_nonneg (log_pos this).le (by linarith)
    · have : (1 - t) / t < 1 := by rw [div_lt_one h0]; linarith
      exact mul_nonneg_of_nonpos_of_nonpos (log_nonpos (by positivity) this.le) (by linarith)
  unfold i3XG
  exact mul_nonneg (div_nonneg hl (by positivity)) hJ

/-- **The last integral**: `∫₀¹ g = 2π⁴/15`. -/
theorem i3X_lintegral_final :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (i3XG t) = ENNReal.ofReal (2 * π ^ 4 / 15) := by
  obtain ⟨hFi, hFv⟩ := i3X_integral_F
  set H : ℝ → ℝ := fun t => 2 * (i3XF t + i3XF (1 - t)) with hH
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 / 2 := by
    rw [ae_iff]; simp
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), i3XG t = H t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hne] with t ht hd
    exact i3XG_eq ht hd
  have hpos : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] H := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hne] with t ht hd
    have := i3XG_nonneg ht hd
    rw [i3XG_eq ht hd] at this
    exact this
  have hF1 : IntervalIntegrable (fun t => i3XF (1 - t)) volume 0 1 := by
    have := hFi.comp_sub_left 1
    simpa using this.symm
  have hHi : IntervalIntegrable H volume 0 1 := (hFi.add hF1).const_mul 2
  have hHo : IntegrableOn H (Ioo (0 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hHi).mono_set
      Ioo_subset_Ioc_self
  rw [lintegral_congr_ae (hae.mono fun t ht => by rw [ht]),
    ← ofReal_integral_eq_lintegral_ofReal hHo hpos]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hH,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hFi hF1,
    intervalIntegral.integral_comp_sub_left (fun t => i3XF t) 1]
  simp only [sub_self, sub_zero]
  rw [hFv]
  ring

end QED.ThreeLoopD
