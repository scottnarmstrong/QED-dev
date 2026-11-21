/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Analytic.Basic
public import QED.Polylog.Zeta5
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Taylor expansion of `log Γ(1 + z)` through `z⁵`

For `‖z‖ < 1` we prove the Weierstrass form
`Γ(1 + z) = exp(-γ z + ∑_{k ≥ 2} (-1) ^ k ζ(k) / k · z ^ k)`
(`QED.DimReg.Gamma_one_add_eq_exp_logGammaTail`), with `ζ(k) = ∑_{n ≥ 1} n ^ (-k)`
(`QED.DimReg.zetaNat`) and `γ = Real.eulerMascheroniConstant`.

**Proof.** Euler's limit `Γ(z) = lim n ^ z n! / (z (z + 1) ⋯ (z + n))` (Mathlib's
`Complex.GammaSeq_tendsto_Gamma`) gives `z Γ(z) = lim exp(z log n - ∑_{j ≤ n} log(1 + z / j))`
(`QED.DimReg.mul_GammaSeq_eq_exp`). We split the exponent as
`-z (H_n - log n) + ∑_{j ≤ n} (z / j - log(1 + z / j))`; the first term tends to `-γ z`
(Mathlib's `Real.tendsto_harmonic_sub_log`), and the second to `∑_k (-1) ^ k ζ(k) / k · z ^ k`,
by expanding each logarithm in its Taylor series and exchanging the two sums of the absolutely
summable double family `(-1) ^ m / (m + 2) · (z / (n + 1)) ^ (m + 2)`
(`QED.DimReg.hasSum_log_one_add`).

**Truncation.** With `ζ(2) = π² / 6` and `ζ(4) = π⁴ / 90` (Mathlib) and `ζ(3) = zeta3`,
`ζ(5) = zeta5` (by definition),
`Γ(1 + z) = exp(-γ z + π² / 12 z² - ζ₃ / 3 z³ + π⁴ / 360 z⁴ - ζ₅ / 5 z⁵ + z⁶ R(z))`
with `R = QED.DimReg.logGammaRem` analytic at `0` (`QED.DimReg.Gamma_one_add_eq_exp`,
`QED.DimReg.analyticAt_logGammaRem`). In a product of factors `Γ(1 + aᵢ ε) ^ nᵢ` with
`∑ nᵢ aᵢ = 0` the `γ` terms cancel. The exponential is truncated in the same way:
`exp w = 1 + w + w² / 2 + w³ E(w)` with `E = QED.DimReg.expRem3` analytic at `0`
(`QED.DimReg.exp_eq_expRem3`).

## Main results

* `QED.DimReg.Gamma_one_add_eq_exp_logGammaTail`: the full series.
* `QED.DimReg.Gamma_one_add_eq_exp`: the truncation through `z⁵`, with analytic remainder.
* `QED.DimReg.exp_eq_expRem3`: the truncation of `exp` through `w²`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Nat

namespace QED.DimReg


/-- `ζ(k) = ∑_{n ≥ 1} 1 / n ^ k` as a real series (meaningful for `k ≥ 2`). -/
noncomputable def zetaNat (k : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k

theorem summable_zetaNat {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ k) := by
  have h := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := k)).mpr (by omega))
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem zetaNat_nonneg (k : ℕ) : 0 ≤ zetaNat k :=
  tsum_nonneg fun n => by positivity

theorem zetaNat_le_zetaNat_two {k : ℕ} (hk : 2 ≤ k) : zetaNat k ≤ zetaNat 2 := by
  refine (summable_zetaNat hk).tsum_le_tsum (fun n => ?_) (summable_zetaNat le_rfl)
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hk)

theorem zetaNat_two : zetaNat 2 = Real.pi ^ 2 / 6 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h
  norm_num at h
  simpa [zetaNat] using h.tsum_eq

theorem zetaNat_four : zetaNat 4 = Real.pi ^ 4 / 90 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h
  norm_num at h
  simpa [zetaNat] using h.tsum_eq

theorem zetaNat_three : zetaNat 3 = QED.Polylog.zeta3 := rfl

theorem zetaNat_five : zetaNat 5 = QED.Polylog.zeta5 := rfl

theorem zetaNat_le_two {k : ℕ} (hk : 2 ≤ k) : zetaNat k ≤ 2 := by
  refine (zetaNat_le_zetaNat_two hk).trans ?_
  rw [zetaNat_two]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- The Taylor coefficients of `log Γ(1 + z) + γ z`: `(-1) ^ m ζ(m + 2) / (m + 2)` at
`z ^ (m + 2)`. -/
noncomputable def logGammaCoeff (m : ℕ) : ℂ := (-1) ^ m * (zetaNat (m + 2) : ℂ) / ((m : ℂ) + 2)

theorem norm_logGammaCoeff_le (m : ℕ) : ‖logGammaCoeff m‖ ≤ 1 := by
  have h2 : (2 : ℝ) ≤ ‖(m : ℂ) + 2‖ := by
    have : ((m : ℂ) + 2) = ((m + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith [m.cast_nonneg (α := ℝ)]
  rw [logGammaCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (zetaNat_nonneg _), div_le_one (by linarith)]
  linarith [zetaNat_le_two (k := m + 2) (by omega)]

/-- `log Γ(1 + z) + γ z = ∑_{m ≥ 0} (-1) ^ m ζ(m + 2) / (m + 2) z ^ (m + 2)` (for `‖z‖ < 1`). -/
noncomputable def logGammaTail (z : ℂ) : ℂ := ∑' m : ℕ, logGammaCoeff m * z ^ (m + 2)

/-! ### Power series with bounded coefficients -/

theorem summable_mul_pow {c : ℕ → ℂ} {C : ℝ} (hc : ∀ m, ‖c m‖ ≤ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun m => c m * z ^ m) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C)
    fun m => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hc m) (by positivity)

theorem analyticAt_tsum_mul_pow {c : ℕ → ℂ} {C : ℝ} (hc : ∀ m, ‖c m‖ ≤ C) :
    AnalyticAt ℂ (fun z => ∑' m, c m * z ^ m) 0 := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
  refine DifferentiableOn.analyticAt (s := Metric.ball 0 (1 / 2)) ?_
    (Metric.ball_mem_nhds _ (by norm_num))
  refine differentiableOn_tsum_of_summable_norm (u := fun m => C * (1 / 2) ^ m)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C)
    (fun m => (by fun_prop : Differentiable ℂ fun z : ℂ => c m * z ^ m).differentiableOn)
    Metric.isOpen_ball fun m w hw => ?_
  rw [mem_ball_zero_iff] at hw
  rw [norm_mul, norm_pow]
  exact mul_le_mul (hc m) (pow_le_pow_left₀ (norm_nonneg _) hw.le m) (by positivity) hC

/-! ### The double series -/

/-- The double family `(-1) ^ m / (m + 2) · (z / (n + 1)) ^ (m + 2)`. -/
noncomputable def logGammaTerm (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  (-1) ^ p.2 / ((p.2 : ℂ) + 2) * (z / ((p.1 : ℂ) + 1)) ^ (p.2 + 2)

theorem summable_logGammaTerm {z : ℂ} (hz : ‖z‖ < 1) : Summable (logGammaTerm z) := by
  have hg := summable_geometric_of_lt_one (norm_nonneg z) hz
  have hs := summable_zetaNat (k := 2) le_rfl
  refine Summable.of_norm_bounded
    (g := fun p : ℕ × ℕ => ‖z‖ ^ p.2 * (1 / ((p.1 : ℝ) + 1) ^ 2))
    ((Summable.mul_of_nonneg hg hs (fun _ => by positivity) (fun _ => by positivity)).prod_symm
      |>.congr fun p => by simp) fun p => ?_
  obtain ⟨n, m⟩ := p
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
  have hnn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hm : (1 : ℝ) ≤ ‖(m : ℂ) + 2‖ := by
    rw [show ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith [m.cast_nonneg (α := ℝ)]
  simp only [logGammaTerm]
  rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, norm_div, hnn]
  have hq : ‖z‖ / ((n : ℝ) + 1) ≤ ‖z‖ := div_le_self (norm_nonneg _) hn
  have hq1 : ‖z‖ / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    div_le_div_of_nonneg_right hz.le (by positivity)
  calc 1 / ‖(m : ℂ) + 2‖ * (‖z‖ / ((n : ℝ) + 1)) ^ (m + 2)
      ≤ 1 * ((‖z‖ / ((n : ℝ) + 1)) ^ m * (‖z‖ / ((n : ℝ) + 1)) ^ 2) := by
        rw [pow_add]
        exact mul_le_mul_of_nonneg_right ((div_le_one (by linarith)).mpr hm) (by positivity)
    _ ≤ ‖z‖ ^ m * (1 / ((n : ℝ) + 1)) ^ 2 := by
        rw [one_mul]
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hq m)
          (pow_le_pow_left₀ (by positivity) hq1 2) (by positivity) (by positivity)
    _ = ‖z‖ ^ m * (1 / ((n : ℝ) + 1) ^ 2) := by rw [div_pow, one_pow]

theorem hasSum_logGammaTerm_fst {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    HasSum (fun m => logGammaTerm z (n, m))
      (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))) := by
  set w := z / ((n : ℂ) + 1) with hw
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  have hw1 : ‖w‖ < 1 := by
    rw [hw, norm_div]
    exact (div_le_self (norm_nonneg _) hn).trans_lt hz
  have h := (hasSum_nat_add_iff' 2).mpr (hasSum_taylorSeries_log hw1)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  norm_num at h
  convert h.neg using 1
  · funext m
    simp only [logGammaTerm]
    ring
  · ring

theorem hasSum_logGammaTerm_snd (z : ℂ) (m : ℕ) :
    HasSum (fun n => logGammaTerm z (n, m)) (logGammaCoeff m * z ^ (m + 2)) := by
  have h := (summable_zetaNat (k := m + 2) (by omega)).hasSum
  have h' := (Complex.hasSum_ofReal.mpr h).mul_left ((-1) ^ m / ((m : ℂ) + 2) * z ^ (m + 2))
  convert h' using 1
  · funext n
    simp only [logGammaTerm, div_pow]
    push_cast
    field_simp
  · rw [logGammaCoeff, zetaNat]
    push_cast
    ring

theorem hasSum_log_one_add {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))) (logGammaTail z) := by
  have hS := summable_logGammaTerm hz
  have h1 := hS.hasSum.prod_fiberwise (hasSum_logGammaTerm_fst hz)
  have h2 := hS.prod_symm.hasSum.prod_fiberwise (fun m => hasSum_logGammaTerm_snd z m)
  have h3 : ∑' p : ℕ × ℕ, logGammaTerm z p.swap = ∑' p, logGammaTerm z p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (logGammaTerm z)
  rw [h3] at h2
  rw [logGammaTail, h2.tsum_eq]
  exact h1

/-! ### The Euler–Gauss product -/

theorem one_add_div_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (j : ℕ) : 1 + z / ((j : ℂ) + 1) ≠ 0 := by
  have hn : (1 : ℝ) ≤ ‖(j : ℂ) + 1‖ := by
    rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith [j.cast_nonneg (α := ℝ)]
  intro h
  have h1 : z / ((j : ℂ) + 1) = -1 := by linear_combination h
  have h2 := congrArg norm h1
  rw [norm_div, norm_neg, norm_one] at h2
  have := div_le_self (norm_nonneg z) hn
  linarith

theorem mul_GammaSeq_eq_exp {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    z * GammaSeq z n =
      exp ((Real.log n : ℂ) * z - ∑ j ∈ Finset.range n, log (1 + z / ((j : ℂ) + 1))) := by
  have hj : ∀ j : ℕ, ((j : ℂ) + 1) ≠ 0 := fun j => by exact_mod_cast Nat.succ_ne_zero j
  have hprod : ∏ j ∈ Finset.range (n + 1), (z + j) =
      z * ((n ! : ℂ) * ∏ j ∈ Finset.range n, (1 + z / ((j : ℂ) + 1))) := by
    rw [Finset.prod_range_succ', mul_comm]
    simp only [Nat.cast_zero, add_zero]
    congr 1
    rw [← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    field_simp [hj j]
    ring
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [GammaSeq, hprod, cpow_def_of_ne_zero (by exact_mod_cast hn), ← natCast_log, exp_sub,
    exp_sum, Finset.prod_congr rfl (fun j _ => exp_log (one_add_div_ne_zero hz j))]
  have hP : ∏ j ∈ Finset.range n, (1 + z / ((j : ℂ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => one_add_div_ne_zero hz j
  field_simp

/-- **The Weierstrass form of `Γ(1 + z)`.** For `‖z‖ < 1`,
`Γ(1 + z) = exp(-γ z + ∑_{k ≥ 2} (-1) ^ k ζ(k) / k · z ^ k)`. -/
theorem Gamma_one_add_eq_exp_logGammaTail {z : ℂ} (hz : ‖z‖ < 1) :
    Gamma (1 + z) = exp (-(Real.eulerMascheroniConstant : ℂ) * z + logGammaTail z) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [logGammaTail]
  have hlim1 : Tendsto (fun n => z * GammaSeq z n) atTop (𝓝 (Gamma (1 + z))) := by
    rw [add_comm, Gamma_add_one z hz0]
    exact (GammaSeq_tendsto_Gamma z).const_mul z
  have hH : Tendsto (fun n : ℕ => (((harmonic n : ℝ) - Real.log n : ℝ) : ℂ)) atTop
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
  have hlim2 := (continuous_exp.tendsto _).comp
    ((hH.neg.mul_const z).add (hasSum_log_one_add hz).tendsto_sum_nat)
  refine tendsto_nhds_unique hlim1 (hlim2.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [Function.comp_apply, mul_GammaSeq_eq_exp hz hz0 hn]
  congr 1
  rw [Finset.sum_sub_distrib]
  have hh : ∑ j ∈ Finset.range n, z / ((j : ℂ) + 1) = z * ((harmonic n : ℝ) : ℂ) := by
    simp only [harmonic]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hh]
  push_cast
  ring

/-! ### Truncations with analytic remainders -/

/-- The remainder of `logGammaTail` after `z ^ 5`, divided by `z ^ 6`. -/
noncomputable def logGammaRem (z : ℂ) : ℂ := ∑' m : ℕ, logGammaCoeff (m + 4) * z ^ m

theorem analyticAt_logGammaRem : AnalyticAt ℂ logGammaRem 0 :=
  analyticAt_tsum_mul_pow fun m => norm_logGammaCoeff_le (m + 4)

theorem logGammaTail_eq {z : ℂ} (hz : ‖z‖ < 1) :
    logGammaTail z = (Real.pi : ℂ) ^ 2 / 12 * z ^ 2 - (QED.Polylog.zeta3 : ℂ) / 3 * z ^ 3 +
      (Real.pi : ℂ) ^ 4 / 360 * z ^ 4 - (QED.Polylog.zeta5 : ℂ) / 5 * z ^ 5 +
      z ^ 6 * logGammaRem z := by
  have hs : Summable (fun m => logGammaCoeff m * z ^ (m + 2)) :=
    ((summable_mul_pow (fun m => norm_logGammaCoeff_le m) hz).mul_left (z ^ 2)).congr
      fun m => by ring
  rw [logGammaTail, ← hs.sum_add_tsum_nat_add 4]
  have ht : ∑' m, logGammaCoeff (m + 4) * z ^ (m + 4 + 2) = z ^ 6 * logGammaRem z := by
    rw [logGammaRem, ← tsum_mul_left]
    congr 1
    funext m
    ring
  rw [ht]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, logGammaCoeff]
  rw [← zetaNat_three, ← zetaNat_five]
  norm_num [zetaNat_two, zetaNat_four]
  ring

/-- **The Taylor expansion of `Γ(1 + z)` through `z ^ 5`**, with analytic remainder. -/
theorem Gamma_one_add_eq_exp {z : ℂ} (hz : ‖z‖ < 1) :
    Gamma (1 + z) = exp (-(Real.eulerMascheroniConstant : ℂ) * z +
      (Real.pi : ℂ) ^ 2 / 12 * z ^ 2 - (QED.Polylog.zeta3 : ℂ) / 3 * z ^ 3 +
      (Real.pi : ℂ) ^ 4 / 360 * z ^ 4 - (QED.Polylog.zeta5 : ℂ) / 5 * z ^ 5 +
      z ^ 6 * logGammaRem z) := by
  rw [Gamma_one_add_eq_exp_logGammaTail hz, logGammaTail_eq hz]
  ring_nf

/-- The remainder of `exp` after `w ^ 2`, divided by `w ^ 3`. -/
noncomputable def expRem3 (w : ℂ) : ℂ := ∑' m : ℕ, 1 / ((m + 3)! : ℂ) * w ^ m

theorem analyticAt_expRem3 : AnalyticAt ℂ expRem3 0 := by
  refine analyticAt_tsum_mul_pow (C := 1) fun m => ?_
  rw [norm_div, norm_one, Complex.norm_natCast]
  exact div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    (by positivity)

theorem exp_eq_expRem3 (w : ℂ) : exp w = 1 + w + w ^ 2 / 2 + w ^ 3 * expRem3 w := by
  have h : HasSum (fun n => w ^ n / (n ! : ℂ)) (exp w) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp w
  rw [← h.tsum_eq, ← h.summable.sum_add_tsum_nat_add 3, expRem3, ← tsum_mul_left]
  congr 1
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  · congr 1
    funext m
    rw [pow_add]
    ring

end QED.DimReg
