/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDDisp
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# R-KS, stage D: the per-node dispersion under an outer integral

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). After the photon-mass integral, the summed closed form is an integral over
the remaining nodes `z` of weights `w(z)` times logarithmic nodes `log(1 + s/t₀(z))`, with
thresholds `t₀(z) ≥ c > 0`. The dispersion of each node (`ksD_log_eq_integral`) and Fubini give
one dispersive integral over `t > c`, whose density is the `w`-weighted distribution function
of the thresholds, `ρ(t) = ∫ w(z) 1{t₀(z) < t} dν(z)`.

Main results:

* `ksD_integrableOn_logNodeKer`: `s/(t(s + t))` is integrable on `(c, ∞)` for `c > 0`, `s > -c`;
* `ksD_integral_logNode_swap`:
  `∫ w(z) log(1 + s/t₀(z)) dν = ∫_{t > c} (∫ w(z) 1{t₀(z) < t} dν) s/(t(s + t)) dt`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

theorem ksD_integrableOn_logNodeKer {s c : ℝ} (hc : 0 < c) (hs : -c < s) :
    IntegrableOn (fun t : ℝ => s / (t * (s + t))) (Ioi c) := by
  have hpos : ∀ t ∈ Ioi c, 0 < t ∧ 0 < s + t := fun t ht => by
    have : c < t := ht
    exact ⟨by linarith, by linarith⟩
  have hder : ∀ t ∈ Ioi c, HasDerivAt (fun t : ℝ => log (t / (s + t))) (s / (t * (s + t))) t :=
    fun t ht => ksD_hasDerivAt_logNode (hpos t ht).1 (hpos t ht).2
  have hcont : ContinuousWithinAt (fun t : ℝ => log (t / (s + t))) (Ici c) c := by
    have hst : 0 < s + c := by linarith
    exact ((continuousAt_id.div (continuousAt_const.add continuousAt_id) hst.ne')).log
      (div_pos hc hst).ne' |>.continuousWithinAt
  rcases le_or_gt 0 s with h0 | h0
  · exact integrableOn_Ioi_deriv_of_nonneg hcont hder (fun t ht => by
      obtain ⟨a, b⟩ := hpos t ht
      positivity) (ksD_tendsto_logNode s)
  · exact integrableOn_Ioi_deriv_of_nonpos hcont hder (fun t ht => by
      obtain ⟨a, b⟩ := hpos t ht
      exact div_nonpos_of_nonpos_of_nonneg h0.le (mul_pos a b).le) (ksD_tendsto_logNode s)

/-- **The per-node dispersion under an outer integral**: for a finite measure `ν` on the nodes,
an integrable weight `w` and measurable thresholds `t₀ ≥ c > 0`, and `s > -c`,
`∫ w log(1 + s/t₀) dν = ∫_{t > c} (∫ w 1{t₀ < t} dν) s/(t(s + t)) dt`. -/
theorem ksD_integral_logNode_swap {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    [SFinite ν] {w t₀ : Z → ℝ} {s c : ℝ} (hw : Integrable w ν) (ht₀ : Measurable t₀)
    (hc : 0 < c) (hct : ∀ z, c ≤ t₀ z) (hs : -c < s) :
    ∫ z, w z * log (1 + s / t₀ z) ∂ν =
      ∫ t in Ioi c, (∫ z, {z | t₀ z < t}.indicator w z ∂ν) * (s / (t * (s + t))) := by
  set k : ℝ → ℝ := fun t => s / (t * (s + t)) with hk
  have hkint := ksD_integrableOn_logNodeKer hc hs
  -- step 1: each node as a dispersive integral over `t > c`
  have h1 : ∀ z, w z * log (1 + s / t₀ z) = ∫ t in Ioi c, w z * (Ioi (t₀ z)).indicator k t := by
    intro z
    have hz : 0 < t₀ z := hc.trans_le (hct z)
    rw [ksD_log_eq_integral hz (by linarith [hct z]), integral_const_mul,
      setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right (hct z)]
  -- step 2: Fubini
  have hmeas : MeasurableSet {p : Z × ℝ | t₀ p.1 < p.2} :=
    measurableSet_lt (ht₀.comp measurable_fst) measurable_snd
  have hF : (Function.uncurry fun z t => w z * (Ioi (t₀ z)).indicator k t) =
      {p : Z × ℝ | t₀ p.1 < p.2}.indicator (fun p => w p.1 * k p.2) := by
    funext p
    simp only [Function.uncurry, indicator, mem_Ioi, mem_ofPred_eq]
    split_ifs <;> simp
  have hint : Integrable (Function.uncurry fun z t => w z * (Ioi (t₀ z)).indicator k t)
      (ν.prod (volume.restrict (Ioi c))) := by
    rw [hF]
    exact (hw.mul_prod hkint).indicator hmeas
  rw [integral_congr_ae (Eventually.of_forall h1), integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [indicator, mem_Ioi, mem_ofPred_eq, hk]
  split_ifs <;> simp

end QED.ChainProof.SetAKS

end
