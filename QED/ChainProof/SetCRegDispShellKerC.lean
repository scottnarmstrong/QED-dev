/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellKer

/-!
# Set (c): the shell-slope kernel with the longitudinal part of the vacuum polarization

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS` of
`QED.ChainProof.SetCRegDisp.setCRegLimitDisp_of_pieces` through
`QED.ChainProof.SetCRegDisp.isDispPV_S_of_shell`.

The kernel `QED.ChainProof.SetCRegDisp.shellKer₁` is the shell slope of the one-loop
self-energy with the photon function `R_T` inserted with `g^{ρσ}` alone. The vacuum
polarization tensor, and the `δ₃` counterterm (`QED.TwoLoop.Insertion.photonCtFactor`), are
transverse, `R_T(k²) (g^{ρσ} - k^ρ k^σ/k²)`. The longitudinal part adds
`-R_T(k²)/k² · k̸ S_m(p - k) k̸` to the integrand, and
`k̸ S_m(p - k) k̸ = (p̸ + m) S_m(p - k) (p̸ + m) - (p̸ + m) - k̸`
(`QED.ChainProof.SetCRegDisp.neg_seChainK_eq`): the odd term drops out, the sandwiched term
vanishes to second order on the shell, and the middle term shifts `A` and `B` by the same
constant `(e²/16π²) ∫₀^∞ R_T`. The shell value is unchanged, and the slope gains
`(e²/16π²) ∫₀^∞ R_T` (the Landau minus Feynman structure of `Z₂`). With the charge factor
`e²/4π²` of the inserted photon, the corrected kernel is

`shellKer₁C = shellKer₁ + (e⁴/64π⁴) ∫₀^∞ R_T`.

This was checked numerically (30 digits) against a direct computation of the slope of the
one-loop self-energy with the transverse photon `R_T(k²)(g - kk/k²)`; it is not proved here.

## Main statements

* `shellKer₁C`, `shellKer₁C_eq`: the corrected kernel, `shellKer₁` plus the longitudinal term;
* `norm_shellKer₁C_le`, `measurable_shellKer₁C`: `‖w(T)‖ ≤ C/T`, measurability;
* **`shellDisp_of_values_C`**: `ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)` from the two value
  identities alone.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli

/-- **The shell-slope kernel with the longitudinal part**:
`(e⁴/(32π⁴)) (∫₀¹ (2m² x(1+x) R_T(a₀) - (1-x) Tail_{R_T}(a₀)) dx + ½ ∫₀^∞ R_T)`. -/
noncomputable def shellKer₁C (P₀ : Params) (mγ Λ T : ℝ) : ℂ :=
  ((P₀.e ^ 4 / (32 * Real.pi ^ 4) *
      (seShellSlope (vpPhotonT P₀.m mγ Λ T) P₀.m +
        photonTail (vpPhotonT P₀.m mγ Λ T) 0 / 2) : ℝ) : ℂ)

variable (P₀ : Params) {mγ Λ : ℝ}

/-- **The correction**: `shellKer₁C = shellKer₁ + (e⁴/64π⁴) ∫₀^∞ R_T`. -/
theorem shellKer₁C_eq (mγ Λ T : ℝ) :
    shellKer₁C P₀ mγ Λ T = shellKer₁ P₀ mγ Λ T +
      ((P₀.e ^ 4 / (64 * Real.pi ^ 4) * photonTail (vpPhotonT P₀.m mγ Λ T) 0 : ℝ) : ℂ) := by
  unfold shellKer₁C shellKer₁
  push_cast
  ring

/-- **The corrected kernel decays like `1/T`.** -/
theorem norm_shellKer₁C_le (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hm : 0 < P₀.m) {T : ℝ} (hT : 0 < T) :
    ‖shellKer₁C P₀ mγ Λ T‖ ≤
      (|P₀.e ^ 4 / (32 * Real.pi ^ 4)| * ((4 * P₀.m ^ 2 + Real.pi) * (photonK mγ Λ / P₀.m ^ 2)) +
        |P₀.e ^ 4 / (64 * Real.pi ^ 4)| * (photonK mγ Λ / P₀.m ^ 2 * Real.pi)) / T := by
  rw [shellKer₁C_eq, add_div]
  refine (norm_add_le _ _).trans (add_le_add (norm_shellKer₁_le P₀ hmγ hΛ hm hT) ?_)
  rw [Complex.norm_real, norm_mul, Real.norm_eq_abs, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h0 := photonTail_nonneg hmγ hΛ hT hm (le_refl (0 : ℝ))
  have h1 := photonTail_le hmγ hΛ hT hm (le_refl (0 : ℝ))
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine h1.trans (le_of_eq ?_)
  field_simp

theorem measurable_shellKer₁C (mγ Λ : ℝ) : Measurable (shellKer₁C P₀ mγ Λ) := by
  have h : Measurable fun T : ℝ => photonTail (vpPhotonT P₀.m mγ Λ T) 0 :=
    (measurable_photonTail_vp P₀.m mγ Λ).comp (measurable_id.prodMk measurable_const)
  exact Complex.measurable_ofReal.comp (measurable_const.mul
    ((measurable_seShellSlope P₀.m mγ Λ).add (h.div_const 2)))

open QED.ChainProof.SetAPauli (regParams regFlavors) in
/-- **`ShellDisp` with the corrected slope kernel from the value identities alone**: the
integrability conjuncts of `IsDispPV` hold for `shellKer₀`, `shellKer₁C` at every admissible
datum. -/
theorem shellDisp_of_values_C {P₀ : Params}
    (hval : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ r : ℝ, 0 < r →
      ∀ A B : ℝ → ℂ, SetCLink.SELimitSel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (SetCLink.dZero D) r A B → ∀ σ₀ σ₁ : ℝ,
      A (-P₀.m ^ 2) * ((-P₀.m : ℝ) : ℂ) + B (-P₀.m ^ 2) * P₀.m = σ₀ →
      HasDerivAt (QED.GradedProof.GEx2.shellFun A B P₀.m) σ₁ (-P₀.m) →
      (σ₀ : ℂ) = ∫ v in Ioo (0 : ℝ) 1, dispPVF P₀.m M₁ M₂ c₁ c₂ (shellKer₀ P₀ mγ Λ) v ∧
        (σ₁ : ℂ) = ∫ v in Ioo (0 : ℝ) 1, dispPVF P₀.m M₁ M₂ c₁ c₂ (shellKer₁C P₀ mγ Λ) v) :
    ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA r hr A B hlim σ₀ σ₁ h₀ h₁
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, -, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  obtain ⟨v₀, v₁⟩ := hval M₁ M₂ c₁ c₂ mγ Λ D s hA r hr A B hlim σ₀ σ₁ h₀ h₁
  exact ⟨⟨integrableOn_dispPVF_of_le hm.ne' (hm.trans hM₁).ne' (hm.trans hM₂).ne'
      (measurable_shellKer₀ P₀ mγ Λ) fun T hT => norm_shellKer₀_le P₀ hmγ hΛ hm hT, v₀⟩,
    ⟨integrableOn_dispPVF_of_le hm.ne' (hm.trans hM₁).ne' (hm.trans hM₂).ne'
      (measurable_shellKer₁C P₀ mγ Λ) fun T hT => norm_shellKer₁C_le P₀ hmγ hΛ hm hT, v₁⟩⟩

end QED.ChainProof.SetCRegDisp

end
