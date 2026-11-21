/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# R-KS, stage D: the photon-mass integral of a summed density, with the `1/u` tails cancelled

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). At a fixed outer node, the summed photon-mass density of the classes and
the mass class is a combination `∑ᵢ cᵢ/(u + mᵢ)` (the inner one-loop densities are
superpositions of propagators in the photon mass² `u`) plus terms `dⱼ mⱼ/(u + mⱼ)²`. Each term
alone has a `1/u` tail at `u → ∞`; the face identity says `∑ᵢ cᵢ = 0`, and then the `u`-integral
is absolutely convergent and elementary.

Main results:

* `ksD_integral_pvTerm`: `∫_{u > 0} (1/(u + m) - 1/(u + 1)) du = -log m`;
* `ksD_integral_pv`: if `∑ᵢ cᵢ = 0`, then `∫_{u > 0} ∑ᵢ cᵢ/(u + mᵢ) du = -∑ᵢ cᵢ log mᵢ`;
* `ksD_integral_sqTerm`: `∫_{u > 0} m/(u + m)² du = 1`;
* `ksD_integral_swap_pv`: the same `u`-integral under an outer integral over the nodes, given
  the joint integrability of the summed density.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- One term with its tail subtracted: `1/(u + m) - 1/(u + 1)`. -/
noncomputable def ksDPvTerm (m u : ℝ) : ℝ := 1 / (u + m) - 1 / (u + 1)

theorem ksD_hasDerivAt_pvTerm {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => log ((u + m) / (u + 1))) (ksDPvTerm m u) u := by
  have h1 : u + m ≠ 0 := by linarith
  have h2 : u + 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_id' u).add_const m).fun_div ((hasDerivAt_id' u).add_const 1) h2).log
    (div_pos (by linarith) (by linarith)).ne'
  refine h.congr_deriv ?_
  simp only [ksDPvTerm]
  field_simp

theorem ksD_tendsto_pvTerm (m : ℝ) :
    Tendsto (fun u : ℝ => log ((u + m) / (u + 1))) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => (1 + m / u) / (1 + 1 / u)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun u : ℝ => m / u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := (h0.const_add 1).div (h1.const_add 1) (by norm_num)
    rw [add_zero, div_one] at this
    exact this
  have h' : Tendsto (fun u : ℝ => (u + m) / (u + 1)) atTop (𝓝 1) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    field_simp
  have := (continuousAt_log one_ne_zero).tendsto.comp h'
  simpa [Function.comp_def] using this

theorem ksD_continuousWithinAt_pvTerm {m : ℝ} (hm : 0 < m) :
    ContinuousWithinAt (fun u : ℝ => log ((u + m) / (u + 1))) (Ici 0) 0 := by
  refine ContinuousAt.continuousWithinAt ?_
  exact ((continuousAt_id.add continuousAt_const).div (continuousAt_id.add continuousAt_const)
    (by norm_num)).log (by simp [hm.ne'])

theorem ksD_pvTerm_nonneg {m u : ℝ} (hm1 : m ≤ 1) (hm : 0 < m) (hu : 0 < u) :
    0 ≤ ksDPvTerm m u := by
  simp only [ksDPvTerm, sub_nonneg]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem ksD_pvTerm_nonpos {m u : ℝ} (hm1 : 1 ≤ m) (hu : 0 < u) : ksDPvTerm m u ≤ 0 := by
  simp only [ksDPvTerm, sub_nonpos]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem ksD_integrableOn_pvTerm {m : ℝ} (hm : 0 < m) : IntegrableOn (ksDPvTerm m) (Ioi 0) := by
  rcases le_total m 1 with h | h
  · exact integrableOn_Ioi_deriv_of_nonneg (ksD_continuousWithinAt_pvTerm hm)
      (fun u hu => ksD_hasDerivAt_pvTerm hm hu) (fun u hu => ksD_pvTerm_nonneg h hm hu)
      (ksD_tendsto_pvTerm m)
  · exact integrableOn_Ioi_deriv_of_nonpos (ksD_continuousWithinAt_pvTerm hm)
      (fun u hu => ksD_hasDerivAt_pvTerm hm hu) (fun u hu => ksD_pvTerm_nonpos h hu)
      (ksD_tendsto_pvTerm m)

/-- **`∫_{u > 0} (1/(u + m) - 1/(u + 1)) du = -log m`.** -/
theorem ksD_integral_pvTerm {m : ℝ} (hm : 0 < m) :
    ∫ u in Ioi (0 : ℝ), ksDPvTerm m u = -log m := by
  have hval : (0 : ℝ) - log ((0 + m) / (0 + 1)) = -log m := by simp
  rcases le_total m 1 with h | h
  · rw [integral_Ioi_of_hasDerivAt_of_nonneg (ksD_continuousWithinAt_pvTerm hm)
      (fun u hu => ksD_hasDerivAt_pvTerm hm hu) (fun u hu => ksD_pvTerm_nonneg h hm hu)
      (ksD_tendsto_pvTerm m), hval]
  · rw [integral_Ioi_of_hasDerivAt_of_nonpos (ksD_continuousWithinAt_pvTerm hm)
      (fun u hu => ksD_hasDerivAt_pvTerm hm hu) (fun u hu => ksD_pvTerm_nonpos h hu)
      (ksD_tendsto_pvTerm m), hval]

variable {ι : Type*}

/-- With `∑ᵢ cᵢ = 0`, the summed density is the sum of the tail-subtracted terms. -/
theorem ksD_sum_eq_sum_pvTerm (S : Finset ι) (c m : ι → ℝ) (hc : ∑ i ∈ S, c i = 0) (u : ℝ) :
    ∑ i ∈ S, c i / (u + m i) = ∑ i ∈ S, c i * ksDPvTerm (m i) u := by
  have h : ∑ i ∈ S, c i * ksDPvTerm (m i) u =
      ∑ i ∈ S, c i / (u + m i) - (∑ i ∈ S, c i) * (1 / (u + 1)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ksDPvTerm]
    ring
  rw [h, hc, zero_mul, sub_zero]

/-- **The summed photon-mass density is integrable** once the `1/u` tails cancel. -/
theorem ksD_integrableOn_pv (S : Finset ι) (c m : ι → ℝ) (hm : ∀ i ∈ S, 0 < m i)
    (hc : ∑ i ∈ S, c i = 0) : IntegrableOn (fun u => ∑ i ∈ S, c i / (u + m i)) (Ioi 0) := by
  simp_rw [ksD_sum_eq_sum_pvTerm S c m hc]
  exact integrable_finsetSum S fun i hi => (ksD_integrableOn_pvTerm (hm i hi)).const_mul _

/-- **The photon-mass integral of the summed density**: if `∑ᵢ cᵢ = 0` and every `mᵢ > 0`,
then `∫_{u > 0} ∑ᵢ cᵢ/(u + mᵢ) du = -∑ᵢ cᵢ log mᵢ`. -/
theorem ksD_integral_pv (S : Finset ι) (c m : ι → ℝ) (hm : ∀ i ∈ S, 0 < m i)
    (hc : ∑ i ∈ S, c i = 0) :
    ∫ u in Ioi (0 : ℝ), ∑ i ∈ S, c i / (u + m i) = -∑ i ∈ S, c i * log (m i) := by
  simp_rw [ksD_sum_eq_sum_pvTerm S c m hc]
  rw [integral_finsetSum S fun i hi => (ksD_integrableOn_pvTerm (hm i hi)).const_mul _,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_const_mul, ksD_integral_pvTerm (hm i hi)]
  ring

/-- **`∫_{u > 0} m/(u + m)² du = 1`** for `m > 0`. -/
theorem ksD_integral_sqTerm {m : ℝ} (hm : 0 < m) :
    ∫ u in Ioi (0 : ℝ), m / (u + m) ^ 2 = 1 := by
  have hder : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => -(m / (u + m))) (m / (u + m) ^ 2) u :=
    fun u hu => by
      have hu' : (0 : ℝ) < u := hu
      have h := ((hasDerivAt_const u m).fun_div ((hasDerivAt_id' u).add_const m)
        (by linarith : u + m ≠ 0)).neg
      refine h.congr_deriv ?_
      ring
  have hcont : ContinuousWithinAt (fun u : ℝ => -(m / (u + m))) (Ici 0) 0 :=
    (continuousAt_const.div (continuousAt_id.add continuousAt_const) (by simp [hm.ne'])).neg
      |>.continuousWithinAt
  have hlim : Tendsto (fun u : ℝ => -(m / (u + m))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := m)).div_atTop (tendsto_atTop_add_const_right _ m tendsto_id)
    simpa using this.neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder (fun u hu => by
    have : (0 : ℝ) < u := hu
    positivity) hlim]
  field_simp
  ring

/-- **The `u`-integral under an outer integral over the nodes**: if at every node `z` the summed
density is `∑ᵢ cᵢ(z)/(u + mᵢ(z))` with `∑ᵢ cᵢ(z) = 0` and `mᵢ(z) > 0`, and it is jointly
integrable, then its `u`-integral is the node integral of `-∑ᵢ cᵢ log mᵢ`. -/
theorem ksD_integral_swap_pv {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} [SFinite ν]
    (S : Finset ι) (c m : ι → Z → ℝ) (hm : ∀ z, ∀ i ∈ S, 0 < m i z)
    (hc : ∀ z, ∑ i ∈ S, c i z = 0)
    (hint : Integrable (Function.uncurry fun (u : ℝ) (z : Z) => ∑ i ∈ S, c i z / (u + m i z))
      ((volume.restrict (Ioi (0 : ℝ))).prod ν)) :
    ∫ u in Ioi (0 : ℝ), ∫ z, ∑ i ∈ S, c i z / (u + m i z) ∂ν =
      ∫ z, -∑ i ∈ S, c i z * log (m i z) ∂ν := by
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact ksD_integral_pv S (fun i => c i z) (fun i => m i z) (fun i hi => hm z i hi) (hc z)

end QED.ChainProof.SetAKS

end
