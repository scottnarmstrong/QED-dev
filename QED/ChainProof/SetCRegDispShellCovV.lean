/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellCovS
public import QED.ChainProof.SetCRegMainBDT
import Mathlib.Tactic.Ring

/-!
# Set (c): shell value and slope of `covAX`, `covBX` in the spectral variable

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4.

* `covX_value`: `covAX(-m²) + 3 covBX(-m²) = ∫₀¹ ∑_f c_f w (x(1-x))⁻¹ 2 seShellVal(R_{T_f})`;
* `covX_slope`: `-covAX(-m²) + 2m² covAX'(-m²) + 6m² covBX'(-m²) =
  ∫₀¹ ∑_f c_f w (x(1-x))⁻¹ (-2 seShellSlope(R_{T_f}) - Tail_{R_{T_f}}(0))`;
* `integral_covWt_eq`: `∫₀¹ ∑_f c_f w (x(1-x))⁻¹ K(T_f(x)) = -(1/2) ∫₀¹ ρ(v) ∑_f c_f
  K(M_f² t_v/m²) dv` (the change of variables `v = |1 - 2x|`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel
open QED.ChainProof.SetCPauli QED.ChainProof.SetCK
open QED.TwoLoop.VPHalfAtAssembly (specMu mem_Ioo_mul_pos)

/-- A flavour-summed `x`-integrand of a kernel `K(T)`. -/
noncomputable def covGK (P : Params) (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ f, P.loopCoeff f * covWt x * (x * (1 - x))⁻¹ * K (covT P f x)

section XLevel

variable {P : Params} {δ : ℝ} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hγΛ : P.mγ < P.Λ)
  (hγ2 : P.mγ < 2 * P.m) (hmass : ∀ f, P.m ≤ P.mass f) (hδ : 0 < δ)
  (hδA : 2 * δ ≤ P.mγ ^ 2) (hδm : δ ≤ P.m ^ 2)

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- **The shell value at the `x`-level.** -/
theorem covX_value :
    IntervalIntegrable (covGK P fun T => 2 * seShellVal (vpPhotonT P.m P.mγ P.Λ T) P.m)
        volume 0 1 ∧
      covAX P (-P.m ^ 2) + 3 * covBX P (-P.m ^ 2) = ∫ x in (0 : ℝ)..1,
        covGK P (fun T => 2 * seShellVal (vpPhotonT P.m P.mγ P.Λ T) P.m) x := by
  have hΛ : 0 < P.Λ := hmγ.trans hγΛ
  have hs : -P.m ^ 2 ∈ Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ) := ⟨by linarith, by linarith⟩
  obtain ⟨iA, -, -⟩ := hasDerivAt_covAX hm hmγ hγΛ hγ2 hmass hδ hδA hδm hs
  obtain ⟨iB, -, -⟩ := hasDerivAt_covBX hm hmγ hγΛ hγ2 hmass hδ hδA hδm hs
  have hpt : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 →
      covG P covAU (-P.m ^ 2) x + 3 * covG P covBU (-P.m ^ 2) x =
        covGK P (fun T => 2 * seShellVal (vpPhotonT P.m P.mγ P.Λ T) P.m) x := by
    filter_upwards [ae_covT_ne (P := P) hΛ, Measure.ae_ne volume (1 : ℝ)] with x hx hx1 hxI
    rw [uIoc_of_le zero_le_one] at hxI
    have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
    have e : ∀ f, covAU P.m P.mγ P.Λ (covT P f x) (-P.m ^ 2) +
        3 * covBU P.m P.mγ P.Λ (covT P f x) (-P.m ^ 2) =
        2 * seShellVal (vpPhotonT P.m P.mγ P.Λ (covT P f x)) P.m := fun f => by
      obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ :=
        covT_facts hm hmγ hγΛ hγ2 hmass hδ hδA hδm hxI' (hx hxI' f)
      exact covAU_shell_value hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc
    simp only [covG, covGK, Fin.sum_univ_three, ← e]
    ring
  have hI := (iA.add (iB.const_mul 3)).congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hpt)
  refine ⟨hI, ?_⟩
  unfold covAX covBX
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add iA (iB.const_mul 3)]
  exact intervalIntegral.integral_congr_ae hpt

include hm hmγ hγΛ hγ2 hmass hδ hδA hδm in
/-- **The shell slope at the `x`-level.** -/
theorem covX_slope :
    IntervalIntegrable (covGK P fun T => -2 * seShellSlope (vpPhotonT P.m P.mγ P.Λ T) P.m -
        photonTail (vpPhotonT P.m P.mγ P.Λ T) 0) volume 0 1 ∧
      -covAX P (-P.m ^ 2) + 2 * P.m ^ 2 * covAX' P (-P.m ^ 2) +
        6 * P.m ^ 2 * covBX' P (-P.m ^ 2) = ∫ x in (0 : ℝ)..1,
        covGK P (fun T => -2 * seShellSlope (vpPhotonT P.m P.mγ P.Λ T) P.m -
          photonTail (vpPhotonT P.m P.mγ P.Λ T) 0) x := by
  have hΛ : 0 < P.Λ := hmγ.trans hγΛ
  have hs : -P.m ^ 2 ∈ Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ) := ⟨by linarith, by linarith⟩
  obtain ⟨iA, iA', -⟩ := hasDerivAt_covAX hm hmγ hγΛ hγ2 hmass hδ hδA hδm hs
  obtain ⟨-, iB', -⟩ := hasDerivAt_covBX hm hmγ hγΛ hγ2 hmass hδ hδA hδm hs
  have hpt : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 →
      -covG P covAU (-P.m ^ 2) x + 2 * P.m ^ 2 * covG P covAU' (-P.m ^ 2) x +
        6 * P.m ^ 2 * covG P covBU' (-P.m ^ 2) x =
        covGK P (fun T => -2 * seShellSlope (vpPhotonT P.m P.mγ P.Λ T) P.m -
          photonTail (vpPhotonT P.m P.mγ P.Λ T) 0) x := by
    filter_upwards [ae_covT_ne (P := P) hΛ, Measure.ae_ne volume (1 : ℝ)] with x hx hx1 hxI
    rw [uIoc_of_le zero_le_one] at hxI
    have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
    have e : ∀ f, -covAU P.m P.mγ P.Λ (covT P f x) (-P.m ^ 2) +
        2 * P.m ^ 2 * covAU' P.m P.mγ P.Λ (covT P f x) (-P.m ^ 2) +
        6 * P.m ^ 2 * covBU' P.m P.mγ P.Λ (covT P f x) (-P.m ^ 2) =
        -2 * seShellSlope (vpPhotonT P.m P.mγ P.Λ (covT P f x)) P.m -
          photonTail (vpPhotonT P.m P.mγ P.Λ (covT P f x)) 0 := fun f => by
      obtain ⟨hT, hδB, hδU, hab, hac, hbc, -⟩ :=
        covT_facts hm hmγ hγΛ hγ2 hmass hδ hδA hδm hxI' (hx hxI' f)
      exact covAU_shell_slope hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc
    simp only [covG, covGK, Fin.sum_univ_three, ← e]
    ring
  have hsum := ((iA.neg.add (iA'.const_mul (2 * P.m ^ 2))).add (iB'.const_mul (6 * P.m ^ 2)))
  have hI := hsum.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hpt)
  refine ⟨hI, ?_⟩
  unfold covAX covAX' covBX'
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_add (f := fun x => -covG P covAU (-P.m ^ 2) x) iA.neg
      (iA'.const_mul (2 * P.m ^ 2)),
    ← intervalIntegral.integral_add (f := fun x => -covG P covAU (-P.m ^ 2) x +
      2 * P.m ^ 2 * covG P covAU' (-P.m ^ 2) x) (iA.neg.add (iA'.const_mul (2 * P.m ^ 2)))
      (iB'.const_mul (6 * P.m ^ 2))]
  exact intervalIntegral.integral_congr_ae hpt

end XLevel

/-- **The change of variables `v = |1 - 2x|`** for a flavour-summed integrand. -/
theorem integral_covWt_eq {P : Params} {K : ℝ → ℝ}
    (hK : IntervalIntegrable (covGK P K) volume 0 1) :
    ((∫ x in (0 : ℝ)..1, covGK P K x : ℝ) : ℂ) = -(1 / 2) * ∫ v in Ioo (0 : ℝ) 1,
      (setCKSpecRho v : ℂ) * ∑ f, (P.loopCoeff f : ℂ) *
        (K (P.mass f ^ 2 / P.m ^ 2 * setCKSpecMass v) : ℂ) := by
  set H : ℝ → ℂ := fun x => ((x * (1 - x) : ℝ) : ℂ)⁻¹ *
    ∑ f, (P.loopCoeff f : ℂ) * (K (covT P f x) : ℂ) with hHdef
  have hFH : ∀ x, ((covGK P K x : ℝ) : ℂ) = (bubWt x : ℂ) * H x := fun x => by
    simp only [covGK, hHdef, bubWt, covWt, Fin.sum_univ_three]
    push_cast
    ring
  have hF : IntegrableOn (fun x => (bubWt x : ℂ) * H x) (Ioo 0 1) := by
    have h := (hK.1.mono_set Ioo_subset_Ioc_self).ofReal (𝕜 := ℂ)
    refine h.congr_fun (fun x _ => hFH x) measurableSet_Ioo
  have hH : ∀ x ∈ Ioo (0 : ℝ) 1, H x = ((x * (1 - x) : ℝ) : ℂ)⁻¹ *
      (fun t => ∑ f, (P.loopCoeff f : ℂ) * (K (P.mass f ^ 2 / P.m ^ 2 * t) : ℂ))
        (1 / (x * (1 - x))) := fun x hx => by
    simp only [hHdef]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : covT P f x = P.mass f ^ 2 / P.m ^ 2 * (1 / (x * (1 - x))) := by
      unfold covT
      rw [(specMu_sq_eq (M := P.mass f) hx).1]
      ring
    rw [e]
  have h := (integral_bubWt_eq (g := fun t => ∑ f, (P.loopCoeff f : ℂ) *
    (K (P.mass f ^ 2 / P.m ^ 2 * t) : ℂ)) hF hH).2
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_complex_ofReal]
  simp only [hFH]
  exact h

end QED.ChainProof.SetCRegDisp

end
