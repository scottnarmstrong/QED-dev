/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.OneLoop.PacketAmplitudeSmooth
import QED.OneLoop.PacketLimit
import QED.Integration.PacketMoment

/-!
# Provider for `QED.OneLoop.integrable_and_tendsto_sourceMagneticMoment`

Proves packet 4b's theorem goal (W₄) (obligation O-24, decision D-18) as
`QED.Provider.OneLoop.integrable_and_tendsto_sourceMagneticMoment`, with the binder convention
of decision D-13. This module must never import the frozen anchor.

The current density is the two-momentum Fourier integral of the packet amplitude
`F(k, k') = w(k') w(k) M(k', k)` (`packetCurrentDensity_eq`), which is smooth with compact
support (`QED.OneLoop.PacketAmplitudeSmooth`). The first position moment therefore converges
absolutely and equals `(2π)³ (i/2) ∫ (∂_k - ∂_{k'})F` on the diagonal
(`QED.integral_mul_packetFourier`). On the diagonal the derivatives of the weights cancel
(`fderiv_packetAmplitude_diag_sub`), so the source magnetic moment is the weighted average of
`g(P) = i D(P) / (4 ω_P)`, where `D = (∂_k - ∂_{k'})M`, against the weight `w² (2π)³ 2ω`, whose
integral is `⟨e|e⟩`. As the packet narrows the average tends to `g(0)`
(`tendsto_packetAverage`), and the Breit-frame response gives `D(0) = -4 i m μ`
(`fderiv_packetMatrixElement_breit`), so `g(0) = μ`.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff
open QED.OneLoop

namespace QED.Provider.OneLoop

/-- Packet 4b's (W₄), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem integrable_and_tendsto_sourceMagneticMoment {e Z₁ m mγ Λ : ℝ}
    (hm : 0 < m := by assumption) (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ := by assumption)
    (hφc : HasCompactSupport φ := by assumption)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0 := by assumption) :
    (∀ lam > 0, Integrable fun x : Fin 3 → ℝ =>
      (x 0 : ℂ) * packetCurrentDensity e Z₁ m mγ Λ hm hmγ hΛ φ lam x) ∧
    ∀ μ : ℝ, IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ →
      Tendsto (fun lam => sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam) (𝓝[>] 0)
        (𝓝 (μ : ℂ)) := by
  set M : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℂ :=
    fun kk => packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1 with hMdef
  have hMs : ContDiff ℝ ∞ M := contDiff_packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ
  have hF : ∀ lam, ContDiff ℝ ∞ (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) :=
    fun lam => contDiff_packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ hφ lam
  have hFc : ∀ lam > (0 : ℝ),
      HasCompactSupport (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) :=
    fun lam hlam => hasCompactSupport_packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ hφc hlam.ne'
  have hρ : ∀ lam, packetCurrentDensity e Z₁ m mγ Λ hm hmγ hΛ φ lam =
      QED.packetFourier (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam) := fun lam => by
    funext x
    rw [packetCurrentDensity_eq]
    rfl
  refine ⟨fun lam hlam => ?_, fun μ hμ => ?_⟩
  · rw [hρ]
    exact QED.integrable_mul_packetFourier (hF lam) (hFc lam hlam) 0
  · have hMd : Differentiable ℝ M := hMs.differentiable (by simp)
    set D : (Fin 3 → ℝ) → ℂ := fun P =>
      fderiv ℝ M (P, P) (Pi.single 0 1, 0) - fderiv ℝ M (P, P) (0, Pi.single 0 1) with hDdef
    have hdiag : Continuous fun P : Fin 3 → ℝ => (P, P) := continuous_id.prodMk continuous_id
    have hfd : Continuous (fderiv ℝ M) := hMs.continuous_fderiv (by simp)
    have hD : Continuous D :=
      ((hfd.comp hdiag).clm_apply continuous_const).sub
        ((hfd.comp hdiag).clm_apply continuous_const)
    have hω : ∀ P, 0 < oneParticleMomentum m P 0 := fun P => oneParticleMomentum_pos hm P
    set g : (Fin 3 → ℝ) → ℂ := fun P => I * D P / (4 * (oneParticleMomentum m P 0 : ℂ))
      with hgdef
    have hωc : Continuous fun P => oneParticleMomentum m P 0 :=
      (continuous_apply 0).comp (contDiff_oneParticleMomentum hm).continuous
    have hg : Continuous g := by
      refine (continuous_const.mul hD).div (continuous_const.mul (continuous_ofReal.comp hωc)) ?_
      intro P
      have := hω P
      exact mul_ne_zero (by norm_num) (by exact_mod_cast this.ne')
    have hω0 : oneParticleMomentum m 0 0 = m := by
      simp [oneParticleMomentum, Real.sqrt_sq hm.le]
    have hg0 : g 0 = μ := by
      simp only [hgdef, hDdef]
      rw [fderiv_packetMatrixElement_breit e Z₁ m mγ Λ hm hmγ hΛ (hMd _) hμ, hω0]
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
      rw [I_sq]
      ring
    have key : ∀ lam > (0 : ℝ), sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam =
        (∫ P : Fin 3 → ℝ, ((packetWeight m φ lam P ^ 2 *
            ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m P 0)) : ℝ) : ℂ) * g P)
          / (packetNormSq m φ lam : ℂ) := by
      intro lam hlam
      unfold sourceMagneticMoment
      rw [hρ, QED.integral_mul_packetFourier (hF lam) (hFc lam hlam) 0]
      congr 1
      have hwd : ∀ P, DifferentiableAt ℝ (packetWeight m φ lam) P := fun P =>
        ((contDiff_packetWeight hm hφ lam).differentiable (by simp)) P
      simp_rw [fderiv_packetAmplitude_diag_sub e Z₁ m mγ Λ hm hmγ hΛ φ lam _ 0 (hwd _) (hMd _)]
      rw [← integral_const_mul]
      congr 1
      funext P
      simp only [hgdef, hDdef]
      have hωP : (oneParticleMomentum m P 0 : ℂ) ≠ 0 := by exact_mod_cast (hω P).ne'
      push_cast
      field_simp
      ring
    rw [← hg0]
    exact (tendsto_packetAverage hm hφ.continuous hφc hφ0 hg).congr'
      (eventually_nhdsWithin_of_forall fun lam hlam => (key lam hlam).symm)

end QED.Provider.OneLoop

end
