/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDNode

/-!
# Set (a), stage D: the exchange of a node integral with a dispersive integral

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At each
node `z` of an outer measure `ν`, a finite part has a once-subtracted dispersive form over
`T > t₀(z)` with a density `n(z, T)` (`ksW_ksUQ_sub_eq` for the `VA` class). If the thresholds
stay above `c` and the joint integrand is integrable on `ν × (c, ∞)`, Fubini gives one
dispersive integral whose density is `ρ(T) = ∫ 1{t₀(z) < T} n(z, T) dν(z)`:

  `∫ (∫_{T > t₀(z)} n(z,T) s/(T(s+T)) dT) dν = ∫_{T > c} ρ(T) s/(T(s+T)) dT`.

Main result:

* **`ksW_integral_dispersion_swap`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- **The exchange of the node integral with the dispersive integral.** -/
theorem ksW_integral_dispersion_swap {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    [SFinite ν] {n : Z → ℝ → ℝ} {t₀ : Z → ℝ} {s c : ℝ} (hct : ∀ z, c ≤ t₀ z)
    (hint : Integrable ({p : Z × ℝ | t₀ p.1 < p.2}.indicator
      (fun p => n p.1 p.2 * (s / (p.2 * (s + p.2))))) (ν.prod (volume.restrict (Ioi c)))) :
    ∫ z, (∫ T in Ioi (t₀ z), n z T * (s / (T * (s + T)))) ∂ν =
      ∫ T in Ioi c, (∫ z, {z | t₀ z < T}.indicator (fun z => n z T) z ∂ν) *
        (s / (T * (s + T))) := by
  have h1 : ∀ z, ∫ T in Ioi (t₀ z), n z T * (s / (T * (s + T))) =
      ∫ T in Ioi c, {p : Z × ℝ | t₀ p.1 < p.2}.indicator
        (fun p => n p.1 p.2 * (s / (p.2 * (s + p.2)))) (z, T) := fun z => by
    have he : ∀ T, {p : Z × ℝ | t₀ p.1 < p.2}.indicator
        (fun p => n p.1 p.2 * (s / (p.2 * (s + p.2)))) (z, T) =
          (Ioi (t₀ z)).indicator (fun T => n z T * (s / (T * (s + T)))) T := fun T => by
      simp only [indicator, mem_ofPred_eq, mem_Ioi]
    simp only [he]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right (hct z)]
  rw [integral_congr_ae (Eventually.of_forall h1)]
  rw [integral_integral_swap (f := fun z T => {p : Z × ℝ | t₀ p.1 < p.2}.indicator
    (fun p => n p.1 p.2 * (s / (p.2 * (s + p.2)))) (z, T)) hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun T _ => ?_
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [indicator, mem_ofPred_eq]
  split_ifs <;> simp

end QED.ChainProof.SetAKS

end
