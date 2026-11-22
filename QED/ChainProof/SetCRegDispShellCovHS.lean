/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellCovV
public import QED.ChainProof.SetCRegDispShellKerC
import Mathlib.Tactic.Ring

/-!
# Set (c): the shell data of the self-energy limit in dispersion form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4.

* **`shellDisp_shellKer_C`**: `ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel
open QED.ChainProof.SetCPauli QED.ChainProof.SetCK
open QED.ChainProof.SetAPauli (regParams regFlavors)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ}

/-- The flavour sum of `dispPVF` at the regulated parameters. -/
theorem dispPVF_eq_sum (hm : 0 < P₀.m) (u : ℝ → ℂ) (v : ℝ) :
    dispPVF P₀.m M₁ M₂ c₁ c₂ u v = (setCKSpecRho v : ℂ) *
      ∑ f, ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).loopCoeff f : ℂ) *
        u ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass f ^ 2 /
          (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m ^ 2 * setCKSpecMass v) := by
  have h : P₀.m ^ 2 / P₀.m ^ 2 = 1 := div_self (pow_ne_zero 2 hm.ne')
  simp only [dispPVF, Fin.sum_univ_three, Params.loopCoeff, Params.mass]
  simp [h]

/-- **The shell data of the self-energy limit are the dispersion integrals of `shellKer₀` and
`shellKer₁C`.** -/
theorem shellDisp_shellKer_C (P₀ : Params) : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀) := by
  refine shellDisp_of_values_C fun M₁ M₂ c₁ c₂ mγ Λ D S hA r hr A B hlim σ₀ σ₁ h₀ h₁ => ?_
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, hγΛ, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  set P := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hP
  have hPm : P.m = P₀.m := rfl
  have hPe : P.e = P₀.e := rfl
  have hmass := regParams_mass_ge hA
  obtain ⟨hδ, hδA, hδm, -, -⟩ := covMargin_facts hm hmγ hr
  set δ := covMargin P₀.m mγ r with hδdef
  have hs0 : -P₀.m ^ 2 ∈ Ioo (-P₀.m ^ 2 - δ) (-P₀.m ^ 2 + δ) := ⟨by linarith, by linarith⟩
  obtain ⟨eA, eB⟩ := seLimitSel_coef_eq hA hr hlim hs0
  set c : ℝ := P₀.e ^ 4 / (32 * π ^ 4) with hc
  have hκI : (1 / I) * covKappa P = -(c : ℂ) := by
    have h : ∀ z : ℂ, (1 / I) * (-I * z) = -z := fun z => by
      have := I_ne_zero
      field_simp
    rw [covKappa_eq, hPe]
    exact h _
  refine ⟨?_, ?_⟩
  · -- the shell value
    obtain ⟨iV, eV⟩ := covX_value (P := P) hm hmγ hγΛ hm2 hmass hδ hδA hδm
    have cV := integral_covWt_eq (P := P) iV
    have hσ : (σ₀ : ℂ) = (c : ℂ) * P₀.m *
        ((covAX P (-P₀.m ^ 2) + 3 * covBX P (-P₀.m ^ 2) : ℝ) : ℂ) := by
      rw [← h₀, eA, eB, hκI]
      push_cast
      ring
    rw [hσ, eV, cV]
    have hd : ∀ v, dispPVF P₀.m M₁ M₂ c₁ c₂ (shellKer₀ P₀ mγ Λ) v =
        (-(c * P₀.m / 2) : ℂ) * ((setCKSpecRho v : ℂ) * ∑ f, (P.loopCoeff f : ℂ) *
          ((2 * seShellVal (vpPhotonT P.m P.mγ P.Λ
            (P.mass f ^ 2 / P.m ^ 2 * setCKSpecMass v)) P.m : ℝ) : ℂ)) := fun v => by
      rw [dispPVF_eq_sum (mγ := mγ) (Λ := Λ) hm]
      simp only [shellKer₀, Fin.sum_univ_three, hc]
      push_cast
      ring
    simp_rw [hd]
    rw [integral_const_mul]
    ring
  · -- the shell slope
    have hAe : A =ᶠ[𝓝 (-P₀.m ^ 2)] fun t => (1 / I) * covKappa P * (covAX P t : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs0] with t ht
      exact (seLimitSel_coef_eq hA hr hlim ht).1
    have hBe : B =ᶠ[𝓝 (-P₀.m ^ 2)] fun t => (1 / I) * covKappa P * (-3) * (covBX P t : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs0] with t ht
      exact (seLimitSel_coef_eq hA hr hlim ht).2
    obtain ⟨-, -, dA⟩ := hasDerivAt_covAX (P := P) hm hmγ hγΛ hm2 hmass hδ hδA hδm hs0
    obtain ⟨-, -, dB⟩ := hasDerivAt_covBX (P := P) hm hmγ hγΛ hm2 hmass hδ hδA hδm hs0
    have dA' : HasDerivAt A ((1 / I) * covKappa P * (covAX' P (-P₀.m ^ 2) : ℂ)) (-P₀.m ^ 2) :=
      (dA.ofReal_comp.const_mul ((1 / I) * covKappa P)).congr_of_eventuallyEq hAe
    have dB' : HasDerivAt B ((1 / I) * covKappa P * (-3) * (covBX' P (-P₀.m ^ 2) : ℂ))
        (-P₀.m ^ 2) :=
      (dB.ofReal_comp.const_mul ((1 / I) * covKappa P * (-3))).congr_of_eventuallyEq hBe
    have hz : HasDerivAt (fun z : ℝ => -z ^ 2) (2 * P₀.m) (-P₀.m) := by
      convert (hasDerivAt_pow 2 (-P₀.m)).neg using 1
      ring
    have hzv : -P₀.m ^ 2 = -(-P₀.m) ^ 2 := by ring
    have gA := (dA'.scomp_of_eq (-P₀.m) hz hzv).mul (hasDerivAt_id (-P₀.m)).ofReal_comp
    have gB := (dB'.scomp_of_eq (-P₀.m) hz hzv).mul_const (P₀.m : ℂ)
    have g := gA.add gB
    have hshell : HasDerivAt (QED.GradedProof.GEx2.shellFun A B P₀.m)
        ((2 * P₀.m) • ((1 / I) * covKappa P * (covAX' P (-P₀.m ^ 2) : ℂ)) *
            (((id (-P₀.m) : ℝ)) : ℂ) +
          (A ∘ fun z : ℝ => -z ^ 2) (-P₀.m) * ((1 : ℝ) : ℂ) +
          (2 * P₀.m) • ((1 / I) * covKappa P * (-3) * (covBX' P (-P₀.m ^ 2) : ℂ)) *
            (P₀.m : ℂ)) (-P₀.m) := by
      convert g using 1
      funext z
      simp only [QED.GradedProof.GEx2.shellFun, Function.comp, Pi.add_apply, Pi.mul_apply, id]
    have hσ := h₁.unique hshell
    obtain ⟨iS, eS⟩ := covX_slope (P := P) hm hmγ hγΛ hm2 hmass hδ hδA hδm
    have cS := integral_covWt_eq (P := P) iS
    have hA0 : A (-P₀.m ^ 2) = (1 / I) * covKappa P * (covAX P (-P₀.m ^ 2) : ℂ) := eA
    have hσ' : (σ₁ : ℂ) = (c : ℂ) * ((-covAX P (-P₀.m ^ 2) + 2 * P₀.m ^ 2 *
        covAX' P (-P₀.m ^ 2) + 6 * P₀.m ^ 2 * covBX' P (-P₀.m ^ 2) : ℝ) : ℂ) := by
      rw [hσ]
      simp only [Function.comp, id, ← hzv, hA0, Complex.real_smul, hκI]
      push_cast
      ring
    rw [hσ', eS, cS]
    have hd : ∀ v, dispPVF P₀.m M₁ M₂ c₁ c₂ (shellKer₁C P₀ mγ Λ) v =
        (-(c / 2) : ℂ) * ((setCKSpecRho v : ℂ) * ∑ f, (P.loopCoeff f : ℂ) *
          ((-2 * seShellSlope (vpPhotonT P.m P.mγ P.Λ
            (P.mass f ^ 2 / P.m ^ 2 * setCKSpecMass v)) P.m - photonTail (vpPhotonT P.m P.mγ P.Λ
              (P.mass f ^ 2 / P.m ^ 2 * setCKSpecMass v)) 0 : ℝ) : ℂ)) := fun v => by
      rw [dispPVF_eq_sum (mγ := mγ) (Λ := Λ) hm]
      simp only [shellKer₁C, Fin.sum_univ_three, hc]
      push_cast
      ring
    simp_rw [hd]
    rw [integral_const_mul]
    ring

end QED.ChainProof.SetCRegDisp

end
