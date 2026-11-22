/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Set (d), master `I₂`: the `ξ`-integral of the `ℱ`-part

With `k = ξ (1 - ξ)` and `λ = p² / (1 - p)`, `0 ≤ p < 1`,

  `∫₀¹ log (1 + λ k) / k dξ = log² (1 - p)`.

(For `p > 1/2` the dilogarithm form `-2 Li₂(p) - 2 Li₂(-p / (1 - p))` has an argument below `-1`,
so we argue directly.) Differentiating in `λ` gives `∫₀¹ dξ / (1 + λ k)`; since
`1 + λ k = (1 - p ξ)(1 - p + p ξ) / (1 - p)`, this is `-2 (1 - p) log (1 - p) / (p (2 - p))`,
and with `dλ / dp = p (2 - p) / (1 - p)²` the derivative in `p` is `-2 log (1 - p) / (1 - p)`,
the derivative of `log² (1 - p)`.

## Main results

* `QED.ThreeLoopD.i2P1FXi_value`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace QED.ThreeLoopD

/-- The `ξ`-integrand `log (1 + μ k) / k`, `k = ξ (1 - ξ)`. -/
noncomputable def i2P1FXiF (μ ξ : ℝ) : ℝ := log (1 + μ * (ξ * (1 - ξ))) / (ξ * (1 - ξ))

/-- Its `μ`-derivative, written as `k / (1 + μ k) / k`. -/
noncomputable def i2P1FXiF' (μ ξ : ℝ) : ℝ := ξ * (1 - ξ) / (1 + μ * (ξ * (1 - ξ))) / (ξ * (1 - ξ))

/-- The function `p ↦ ∫₀¹ log (1 + λ(p) k) / k`. -/
noncomputable def i2P1FXiG (μ : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..1, i2P1FXiF μ ξ

theorem i2P1FXi_k_mem {ξ : ℝ} (hξ : ξ ∈ Ι (0 : ℝ) 1) :
    0 < ξ * (1 - ξ) ∨ ξ * (1 - ξ) = 0 := by
  rw [uIoc_of_le zero_le_one] at hξ
  rcases eq_or_lt_of_le hξ.2 with h | h
  · right; rw [h]; ring
  · left; exact mul_pos hξ.1 (by linarith)

theorem i2P1FXi_k_le (ξ : ℝ) : ξ * (1 - ξ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ξ - 1 / 2)]

theorem i2P1FXi_one_add_pos {μ ξ : ℝ} (hμ : -2 < μ) (hξ : 0 ≤ ξ * (1 - ξ)) :
    1 / 2 ≤ 1 + μ * (ξ * (1 - ξ)) := by
  have := i2P1FXi_k_le ξ
  nlinarith

/-- `log (1 + μ k) / k` is integrable on `[0, 1]` for `μ ≥ 0` (it is bounded by `μ`). -/
theorem i2P1FXi_intervalIntegrable {μ₀ : ℝ} (hμ₀ : 0 ≤ μ₀) :
    IntervalIntegrable (i2P1FXiF μ₀) volume 0 1 := by
  have hmeasF : AEStronglyMeasurable (i2P1FXiF μ₀) (volume.restrict (Ι (0 : ℝ) 1)) :=
    (by unfold i2P1FXiF; fun_prop : Measurable (i2P1FXiF μ₀)).aestronglyMeasurable
  refine (intervalIntegrable_const (c := μ₀)).mono_fun hmeasF ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun ξ hξ => ?_
  simp only [i2P1FXiF, norm_div, Real.norm_eq_abs]
  rcases i2P1FXi_k_mem hξ with h | h
  · rw [abs_of_pos h, abs_of_nonneg (log_nonneg (by nlinarith)), abs_of_nonneg hμ₀,
      div_le_iff₀ h]
    have := log_le_sub_one_of_pos (show 0 < 1 + μ₀ * (ξ * (1 - ξ)) by nlinarith)
    linarith
  · rw [h]; simp [abs_nonneg]

/-- **The `μ`-derivative** of `∫₀¹ log (1 + μ k) / k` at `μ₀ ≥ 0`. -/
theorem i2P1FXi_hasDerivAt {μ₀ : ℝ} (hμ₀ : 0 ≤ μ₀) :
    HasDerivAt i2P1FXiG (∫ ξ in (0 : ℝ)..1, i2P1FXiF' μ₀ ξ) μ₀ := by
  have hk : ∀ ξ ∈ Ι (0 : ℝ) 1, 0 ≤ ξ * (1 - ξ) := fun ξ hξ =>
    (i2P1FXi_k_mem hξ).elim le_of_lt ge_of_eq
  have hmeasF : ∀ μ, AEStronglyMeasurable (i2P1FXiF μ) (volume.restrict (Ι (0 : ℝ) 1)) :=
    fun μ => (by unfold i2P1FXiF; fun_prop : Measurable (i2P1FXiF μ)).aestronglyMeasurable
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := i2P1FXiF) (F' := i2P1FXiF') (bound := fun _ => 2) (Ioi_mem_nhds (by linarith :
      (-2 : ℝ) < μ₀)) (Eventually.of_forall hmeasF) ?_
    (by unfold i2P1FXiF'; fun_prop : Measurable (i2P1FXiF' μ₀)).aestronglyMeasurable ?_
    intervalIntegrable_const ?_).2
  · exact i2P1FXi_intervalIntegrable hμ₀
  · refine Eventually.of_forall fun ξ hξ μ (hμ : -2 < μ) => ?_
    have h1 := i2P1FXi_one_add_pos hμ (hk ξ hξ)
    simp only [i2P1FXiF', Real.norm_eq_abs]
    rcases i2P1FXi_k_mem hξ with h | h
    · have h2 : 0 < 1 + μ * (ξ * (1 - ξ)) := by linarith
      rw [show ξ * (1 - ξ) / (1 + μ * (ξ * (1 - ξ))) / (ξ * (1 - ξ)) =
          1 / (1 + μ * (ξ * (1 - ξ))) by rw [div_right_comm, div_self h.ne'],
        abs_of_pos (by positivity),
        div_le_iff₀ h2]
      linarith
    · rw [h]; simp
  · refine Eventually.of_forall fun ξ hξ μ (hμ : -2 < μ) => ?_
    have h1 := i2P1FXi_one_add_pos hμ (hk ξ hξ)
    have := (((hasDerivAt_id μ).mul_const (ξ * (1 - ξ))).const_add 1).log (by
      simp only [id]; linarith) |>.div_const (ξ * (1 - ξ))
    refine this.congr_deriv ?_
    simp [i2P1FXiF']

/-- **The `μ`-derivative at `μ = λ(p)`**:
`∫₀¹ dξ / (1 + λ k) = -2 (1 - p) log (1 - p) / (p (2 - p))`,
via `1 + λ k = (1 - p ξ)(1 - p + p ξ) / (1 - p)`. -/
theorem i2P1FXi_deriv_value {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ ξ in (0 : ℝ)..1, i2P1FXiF' (p ^ 2 / (1 - p)) ξ =
      -2 * (1 - p) * log (1 - p) / (p * (2 - p)) := by
  obtain ⟨hp0, hp1⟩ := hp
  have h1p : 0 < 1 - p := by linarith
  have h2p : 0 < 2 - p := by linarith
  set c := (1 - p) / (p * (2 - p)) with hc
  set Φ : ℝ → ℝ := fun ξ => c * (log (1 - p + p * ξ) - log (1 - p * ξ)) with hΦ
  have hpos1 : ∀ ξ ∈ Icc (0 : ℝ) 1, 0 < 1 - p + p * ξ := fun ξ hξ => by nlinarith [hξ.1]
  have hpos2 : ∀ ξ ∈ Icc (0 : ℝ) 1, 0 < 1 - p * ξ := fun ξ hξ => by nlinarith [hξ.2]
  have hmeas : Measurable (i2P1FXiF' (p ^ 2 / (1 - p))) := by unfold i2P1FXiF'; fun_prop
  have hint : IntervalIntegrable (i2P1FXiF' (p ^ 2 / (1 - p))) volume 0 1 := by
    refine (intervalIntegrable_const (c := (2 : ℝ))).mono_fun hmeas.aestronglyMeasurable ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun ξ hξ => ?_
    have hk : 0 ≤ ξ * (1 - ξ) := (i2P1FXi_k_mem hξ).elim le_of_lt ge_of_eq
    have h1 := i2P1FXi_one_add_pos (show (-2 : ℝ) < p ^ 2 / (1 - p) by
      have : 0 ≤ p ^ 2 / (1 - p) := by positivity
      linarith) hk
    simp only [i2P1FXiF', Real.norm_eq_abs]
    rcases i2P1FXi_k_mem hξ with h | h
    · have h2 : 0 < 1 + p ^ 2 / (1 - p) * (ξ * (1 - ξ)) := by linarith
      rw [div_right_comm, div_self h.ne', abs_of_pos (by positivity), div_le_iff₀ h2]
      norm_num
      linarith
    · rw [h]; simp
  have hcont : ContinuousOn Φ (Icc 0 1) :=
    continuousOn_const.mul ((ContinuousOn.log (by fun_prop) fun ξ hξ => (hpos1 ξ hξ).ne').sub
      (ContinuousOn.log (by fun_prop) fun ξ hξ => (hpos2 ξ hξ).ne'))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont (fun ξ hξ => ?_) hint]
  · simp only [hΦ, hc, mul_zero, sub_zero, mul_one, log_one, sub_add_cancel]
    field_simp
    ring
  · have hξ' : ξ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hξ
    have hk : 0 < ξ * (1 - ξ) := mul_pos hξ.1 (by linarith [hξ.2])
    have e1 := hpos1 ξ hξ'
    have e2 := hpos2 ξ hξ'
    have hd := ((((hasDerivAt_id ξ).const_mul p).const_add (1 - p)).log e1.ne').sub
      ((((hasDerivAt_id ξ).const_mul p).const_sub 1).log e2.ne') |>.const_mul c
    refine hd.congr_deriv ?_
    simp only [id, hc, i2P1FXiF']
    rw [div_right_comm, div_self hk.ne', show 1 + p ^ 2 / (1 - p) * (ξ * (1 - ξ)) =
      (1 - p * ξ) * (1 - p + p * ξ) / (1 - p) by field_simp; ring]
    field_simp
    ring

/-- **The `p`-derivative**: `d/dp ∫₀¹ log (1 + λ(p) k) / k = -2 log (1 - p) / (1 - p)`. -/
theorem i2P1FXi_hasDerivAt_p {p : ℝ} (hp : p ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (fun p : ℝ => i2P1FXiG (p ^ 2 / (1 - p))) (-2 * log (1 - p) / (1 - p)) p := by
  obtain ⟨hp0, hp1⟩ := hp
  have h1p : 0 < 1 - p := by linarith
  have hl : HasDerivAt (fun p : ℝ => p ^ 2 / (1 - p)) (p * (2 - p) / (1 - p) ^ 2) p := by
    have := ((hasDerivAt_id p).pow 2).div ((hasDerivAt_id p).const_sub 1) h1p.ne'
    refine this.congr_deriv ?_
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have hc := (i2P1FXi_hasDerivAt (show 0 ≤ p ^ 2 / (1 - p) by positivity)).comp p hl
  refine hc.congr_deriv ?_
  rcases eq_or_lt_of_le hp0 with h | h
  · subst h
    simp
  · rw [i2P1FXi_deriv_value ⟨h, hp1⟩]
    have : 0 < 2 - p := by linarith
    field_simp

/-- **The `ξ`-identity**: `∫₀¹ log (1 + λ k) / k dξ = log² (1 - p)` for `λ = p² / (1 - p)`,
`0 ≤ p < 1`. -/
theorem i2P1FXi_value {p : ℝ} (hp : p ∈ Ico (0 : ℝ) 1) :
    ∫ ξ in (0 : ℝ)..1, log (1 + p ^ 2 / (1 - p) * (ξ * (1 - ξ))) / (ξ * (1 - ξ)) =
      log (1 - p) ^ 2 := by
  set f : ℝ → ℝ := fun x => i2P1FXiG (x ^ 2 / (1 - x)) - log (1 - x) ^ 2 with hf
  have hd : ∀ x ∈ Icc 0 p, HasDerivAt f 0 x := fun x hx => by
    have hx' : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1, hx.2.trans_lt hp.2⟩
    have h1x : 1 - x ≠ 0 := by linarith [hx'.2]
    have hlog := (((hasDerivAt_id x).const_sub 1).log h1x).pow 2
    refine ((i2P1FXi_hasDerivAt_p hx').sub hlog).congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring
  have := constant_of_has_deriv_right_zero (f := f) (a := 0) (b := p)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (Ico_subset_Icc_self hx)).hasDerivWithinAt) p ⟨hp.1, le_rfl⟩
  simp only [hf, i2P1FXiG, i2P1FXiF] at this
  simpa [sub_eq_iff_eq_add] using this

/-- **The `ξ`-identity as a lower integral** over `(0, 1)`. -/
theorem i2P1FXi_lint {p : ℝ} (hp : p ∈ Ico (0 : ℝ) 1) :
    ∫⁻ ξ in Ioo (0 : ℝ) 1, ENNReal.ofReal
        (log (1 + p ^ 2 / (1 - p) * (ξ * (1 - ξ))) / (ξ * (1 - ξ))) =
      ENNReal.ofReal (log (1 - p) ^ 2) := by
  have hμ : 0 ≤ p ^ 2 / (1 - p) := div_nonneg (sq_nonneg p) (by linarith [hp.2])
  have hi := i2P1FXi_intervalIntegrable hμ
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] i2P1FXiF (p ^ 2 / (1 - p)) := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun ξ hξ => ?_)
    have hk : 0 < ξ * (1 - ξ) := mul_pos hξ.1 (by linarith [hξ.2])
    exact div_nonneg (log_nonneg (by nlinarith)) hk.le
  rw [← i2P1FXi_value hp, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  exact (ofReal_integral_eq_lintegral_ofReal hi hnn).symm

end QED.ThreeLoopD
