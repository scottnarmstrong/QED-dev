/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Meromorphic continuation by partial integration, and uniqueness

Two pieces of the generic layer L1.

**Uniqueness.** Two functions meromorphic on `ℂ` that agree on a nonempty open set agree in a
punctured neighbourhood of every point, hence at every point where both are continuous
(`QED.DimReg.Meromorphic.eventuallyEq_nhdsNE_of_eqOn`, `QED.DimReg.Meromorphic.eq_of_eqOn`).
This is what makes "the" meromorphic continuation of a parametric integral well defined: any two
meromorphic functions that equal the integral on its (open, nonempty) region of convergence
agree off their poles.

**Continuation by partial integration.** For `f` continuous on `[0, 1]` the integral
`M f s = ∫₀¹ t ^ (s - 1) f(t) dt` (`QED.DimReg.mellinUnit`) is analytic in `re s > 0`. If `f` is
`C¹`, partial integration gives `s · M f s = f(1) - M f' (s + 1)`. Iterating `k` times defines
`QED.DimReg.mellinUnitCont k f`, which equals `M f` on `re s > 0`, is meromorphic on
`re s > -k`, and is analytic there off `s ∈ {0, -1, …, -(k - 1)}`. This is the one-variable step
of the continuation of a sector integral `∫_{(0,1]^N} x ^ (a - 1) f(x) dx`; applying it in each
coordinate (with the integrand depending analytically on the other exponents and on `d`) is the
general box continuation.

## Main results

* `QED.DimReg.Meromorphic.eventuallyEq_nhdsNE_of_eqOn`, `QED.DimReg.Meromorphic.eq_of_eqOn`.
* `QED.DimReg.analyticAt_mellinUnit`: analyticity for `re s > 0`.
* `QED.DimReg.mul_mellinUnit`: the partial-integration step.
* `QED.DimReg.mellinUnitCont_eq`, `QED.DimReg.meromorphicAt_mellinUnitCont`,
  `QED.DimReg.analyticAt_mellinUnitCont`: the continuation.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.DimReg

/-! ### Uniqueness of meromorphic continuation -/

/-- Two functions meromorphic on `ℂ` that agree on a nonempty open set agree in a punctured
neighbourhood of every point. -/
theorem Meromorphic.eventuallyEq_nhdsNE_of_eqOn {f g : ℂ → ℂ} (hf : Meromorphic f)
    (hg : Meromorphic g) {V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) (h : EqOn f g V)
    (y : ℂ) : f =ᶠ[𝓝[≠] y] g := by
  obtain ⟨x, hx⟩ := hne
  have hm : MeromorphicOn (f - g) univ := fun z _ => (hf z).sub (hg z)
  have hx0 : meromorphicOrderAt (f - g) x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hx)] with z hz
    simp [h hz]
  have hy := hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ (mem_univ x)
    (mem_univ y) hx0
  rw [meromorphicOrderAt_eq_top_iff] at hy
  filter_upwards [hy] with z hz
  exact sub_eq_zero.mp hz

/-- Two functions meromorphic on `ℂ` that agree on a nonempty open set agree at every point
where both are continuous. -/
theorem Meromorphic.eq_of_eqOn {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    {V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) (h : EqOn f g V) {y : ℂ}
    (hfy : ContinuousAt f y) (hgy : ContinuousAt g y) : f y = g y := by
  have he := Meromorphic.eventuallyEq_nhdsNE_of_eqOn hf hg hV hne h y
  have h1 : Tendsto f (𝓝[≠] y) (𝓝 (f y)) := hfy.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] y) (𝓝 (g y)) :=
    (hgy.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm
  exact tendsto_nhds_unique h1 h2

/-! ### The unit Mellin integral -/

/-- The unit Mellin integral `M f s = ∫₀¹ t ^ (s - 1) f(t) dt`. -/
noncomputable def mellinUnit (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * f t

theorem mellinUnit_eq_mellin (f : ℝ → ℂ) (s : ℂ) :
    mellinUnit f s = mellin ((Ioc (0 : ℝ) 1).indicator f) s := by
  rw [mellinUnit, mellin, intervalIntegral.integral_of_le zero_le_one,
    ← integral_indicator measurableSet_Ioc,
    ← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases h1 : t ∈ Ioc (0 : ℝ) 1
  · have h2 : t ∈ Ioi (0 : ℝ) := h1.1
    simp [indicator_of_mem h1, indicator_of_mem h2]
  · rw [indicator_of_notMem h1]
    by_cases h2 : t ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem h2, indicator_of_notMem h1]
    · rw [indicator_of_notMem h2]

/-- For `f` continuous, `M f` is analytic on `re s > 0`. -/
theorem analyticAt_mellinUnit {f : ℝ → ℂ} (hf : Continuous f) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (mellinUnit f) s := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hf.continuousOn
  have hd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (mellinUnit f) z := by
    intro z hz
    have hfun : mellinUnit f = mellin ((Ioc (0 : ℝ) 1).indicator f) :=
      funext (mellinUnit_eq_mellin f)
    rw [hfun]
    refine mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := 0) ?_ ?_ (by linarith)
      ?_ hz
    · have hint : IntegrableOn f (Ioc (0 : ℝ) 1) :=
        (hf.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      exact (hint.integrable_indicator measurableSet_Ioc).locallyIntegrable.locallyIntegrableOn _
    · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop 1] with t ht
      rw [indicator_of_notMem (fun h => by linarith [h.2])]
    · refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
      by_cases h : t ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem h]
        exact hC t ⟨h.1.le, h.2⟩
      · rw [indicator_of_notMem h, norm_zero]
        exact (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  exact DifferentiableOn.analyticAt (fun z hz => (hd z hz).differentiableWithinAt)
    (hopen.mem_nhds hs)

/-- **The partial-integration step.** For `f` of class `C¹` and `re s > 0`,
`s · M f s = f(1) - M f' (s + 1)`. -/
theorem mul_mellinUnit {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {s : ℂ} (hs : 0 < s.re) :
    s * mellinUnit f s = f 1 - mellinUnit (deriv f) (s + 1) := by
  obtain ⟨hdf, hcf⟩ := contDiff_one_iff_deriv.mp hf
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hv : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ s / s) ((t : ℂ) ^ (s - 1)) t := by
    intro t ht
    have ht0 : 0 < t := by simpa using ht.1
    have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := s)
      (ofReal_mem_slitPlane.mpr ht0)).comp_ofReal.div_const s
    simp only [id] at h
    convert h using 1
    field_simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (u' := deriv f) (v := fun t : ℝ => (t : ℂ) ^ s / s)
    (v' := fun t : ℝ => (t : ℂ) ^ (s - 1)) (a := 0) (b := 1)
    hdf.continuous.continuousOn
    ((continuous_ofReal_cpow_const hs).div_const s).continuousOn
    (fun t _ => (hdf t).hasDerivAt) hv (hcf.intervalIntegrable 0 1)
    (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have h0 : ((0 : ℝ) : ℂ) ^ s = 0 := by rw [ofReal_zero, zero_cpow hs0]
  rw [mellinUnit, mellinUnit, add_sub_cancel_right]
  simp only [ofReal_one, one_cpow, h0, zero_div, mul_zero, sub_zero] at hparts
  have e1 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * f t =
      ∫ t in (0 : ℝ)..1, f t * (t : ℂ) ^ (s - 1) := by
    congr 1; funext t; ring
  have e2 : ∫ t in (0 : ℝ)..1, deriv f t * ((t : ℂ) ^ s / s) =
      s⁻¹ * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ s * deriv f t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; field_simp
  rw [e1, hparts, e2]
  field_simp

/-- The `k`-fold partial-integration continuation of `M f`:
`Cont₀ f = M f` and `Cont_{k+1} f s = (f(1) - Cont_k f' (s + 1)) / s`. -/
noncomputable def mellinUnitCont : ℕ → (ℝ → ℂ) → ℂ → ℂ
  | 0, f, s => mellinUnit f s
  | k + 1, f, s => (f 1 - mellinUnitCont k (deriv f) (s + 1)) / s

/-- The continuation agrees with the integral on `re s > 0`. -/
theorem mellinUnitCont_eq (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ k f) {s : ℂ} (hs : 0 < s.re) :
    mellinUnitCont k f s = mellinUnit f s := by
  induction k generalizing f s with
  | zero => rfl
  | succ k ih =>
    have hf' : ContDiff ℝ k (deriv f) := by
      have := (contDiff_succ_iff_deriv (n := ((k : ℕ) : WithTop ℕ∞))).mp (by exact_mod_cast hf)
      exact this.2.2
    have hs1 : 0 < (s + 1).re := by simp; linarith
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast (show 1 ≤ k + 1 by omega))
    rw [mellinUnitCont, ih hf' hs1, ← mul_mellinUnit h1 hs, mul_div_cancel_left₀ _ hs0]

/-- The continuation is meromorphic on `re s > -k`. -/
theorem meromorphicAt_mellinUnitCont (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ k f) {s : ℂ}
    (hs : -(k : ℝ) < s.re) : MeromorphicAt (mellinUnitCont k f) s := by
  induction k generalizing f s with
  | zero =>
    exact (analyticAt_mellinUnit hf.continuous (by simpa using hs)).meromorphicAt
  | succ k ih =>
    have hf' : ContDiff ℝ k (deriv f) := by
      have := (contDiff_succ_iff_deriv (n := ((k : ℕ) : WithTop ℕ∞))).mp (by exact_mod_cast hf)
      exact this.2.2
    have hs1 : -(k : ℝ) < (s + 1).re := by simp; push_cast at hs; linarith
    have h1 : MeromorphicAt (fun z => mellinUnitCont k (deriv f) (z + 1)) s :=
      (ih hf' hs1).comp_analyticAt (g := fun z : ℂ => z + 1) (by fun_prop)
    exact ((MeromorphicAt.const _ _).sub h1).div (by fun_prop : AnalyticAt ℂ id s).meromorphicAt

/-- The continuation is analytic on `re s > -k` away from `s ∈ {0, -1, …, -(k - 1)}`. -/
theorem analyticAt_mellinUnitCont (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ k f) {s : ℂ}
    (hs : -(k : ℝ) < s.re) (hpole : ∀ j : ℕ, j < k → s ≠ -(j : ℂ)) :
    AnalyticAt ℂ (mellinUnitCont k f) s := by
  induction k generalizing f s with
  | zero => exact analyticAt_mellinUnit hf.continuous (by simpa using hs)
  | succ k ih =>
    have hf' : ContDiff ℝ k (deriv f) := by
      have := (contDiff_succ_iff_deriv (n := ((k : ℕ) : WithTop ℕ∞))).mp (by exact_mod_cast hf)
      exact this.2.2
    have hs1 : -(k : ℝ) < (s + 1).re := by simp; push_cast at hs; linarith
    have hpole1 : ∀ j : ℕ, j < k → s + 1 ≠ -(j : ℂ) := by
      intro j hj h
      exact hpole (j + 1) (by omega) (by push_cast; linear_combination h)
    have hs0 : s ≠ 0 := by simpa using hpole 0 (by omega)
    have hg : AnalyticAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
    have h1 : AnalyticAt ℂ (fun z => mellinUnitCont k (deriv f) (z + 1)) s :=
      AnalyticAt.comp (g := mellinUnitCont k (deriv f)) (ih hf' hs1 hpole1) hg
    exact (analyticAt_const.sub h1).div analyticAt_id hs0

end QED.DimReg
