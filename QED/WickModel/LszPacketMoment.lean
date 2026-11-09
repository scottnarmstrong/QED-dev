/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszSourceMagneticMoment
public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.Frozen.OneLoop.SourceMagneticMomentLimit
import QED.WickModel.LszPacketAmplitude
import QED.OneLoop.PacketAmplitude
import QED.OneLoop.PacketAmplitudeSmooth
import QED.Integration.PacketMoment

/-!
# The LSZ source magnetic moment

For the LSZ source magnetic moment (L₇) of a smooth compactly supported profile `φ`, this module
proves:

* the position integral of (L₇) converges absolutely at every packet width `λ > 0`;
* at every `λ > 0`, (L₇) equals the packet-4b source magnetic moment (W₃) at `Z₁ = 1 + δ₁`.

The current density (L₆) is the two-momentum Fourier integral of the LSZ packet amplitude
`F_L`, which is smooth with compact support
(`QED.WickModel.LszPacket.contDiff_lszPacketAmplitude`,
`QED.WickModel.LszPacket.hasCompactSupport_lszPacketAmplitude`); so the first position moment
converges absolutely (`QED.integrable_mul_packetFourier`) and equals
`(2π)³ (i/2) ∫ (∂_k - ∂_{k'}) F_L` on the diagonal (`QED.integral_mul_packetFourier`). On the
diagonal `F_L` has the same derivative as the packet-4b amplitude at `Z₁ = 1 + δ₁`
(`QED.WickModel.LszPacket.fderiv_lszPacketAmplitude_diag`), whose first moment is the numerator
of (W₃) by the same formula; the denominators `⟨e|e⟩` agree.

With the sealed packet-4b theorem (W₄), it follows that (L₇) tends to every response magnetic
moment (R₀) at `Z₁ = 1 + δ₁` as `λ → 0⁺`.

## Main statements

* `QED.WickModel.LszPacket.integrable_mul_lszPacketCurrentDensity`: absolute convergence.
* `QED.WickModel.LszPacket.lszSourceMagneticMoment_eq`: (L₇) equals (W₃) at `Z₁ = 1 + δ₁`.
* `QED.WickModel.LszPacket.tendsto_lszSourceMagneticMoment`: the limit `λ → 0⁺`, with the
  limit characterized by (R₀) at `Z₁ = 1 + δ₁`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped ContDiff
open QED.OneLoop

namespace QED.WickModel

/-- **Absolute convergence of the position integral of (L₇).** For a smooth compactly supported
profile `φ` and every packet width `λ > 0`, `x ↦ x¹ ⟨e|J²(x)|e⟩` (LSZ form (L₆)) is integrable. -/
theorem LszPacket.integrable_mul_lszPacketCurrentDensity (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∀ lam > 0, Integrable fun x : Fin 3 → ℝ =>
      (x 0 : ℂ) * lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam x := by
  intro lam hlam
  rw [LszPacket.lszPacketCurrentDensity_eq]
  exact QED.integrable_mul_packetFourier
    (LszPacket.contDiff_lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ lam)
    (LszPacket.hasCompactSupport_lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφc
      hlam.ne') 0

/-- **(L₇) equals (W₃) at every packet width.** For a smooth compactly supported profile `φ` and
every `λ > 0`, the LSZ source magnetic moment equals the packet-4b source magnetic moment with
vertex counterterm `Z₁ = 1 + δ₁`: the photon-leg term `q² G` of the LSZ amplitude has zero
derivative on the diagonal, so it does not contribute to the first position moment. -/
theorem LszPacket.lszSourceMagneticMoment_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∀ lam > 0, lszSourceMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam =
      sourceMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ φ lam := by
  intro lam hlam
  have hρ : packetCurrentDensity P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ φ lam =
      QED.packetFourier (packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ φ lam) := by
    funext x
    rw [packetCurrentDensity_eq]
    rfl
  unfold lszSourceMagneticMoment sourceMagneticMoment
  congr 1
  rw [LszPacket.lszPacketCurrentDensity_eq, hρ,
    QED.integral_mul_packetFourier
      (LszPacket.contDiff_lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ lam)
      (LszPacket.hasCompactSupport_lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφc
        hlam.ne') 0,
    QED.integral_mul_packetFourier
      (contDiff_packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ hφ lam)
      (hasCompactSupport_packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ hφc hlam.ne') 0]
  simp_rw [LszPacket.fderiv_lszPacketAmplitude_diag P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ lam]

/-- **The limit of (L₇).** For a smooth compactly supported profile `φ` that is not identically
zero on `[0, ∞)`, the LSZ source magnetic moment tends, as `λ → 0⁺`, to every response magnetic
moment (R₀) with vertex counterterm `Z₁ = 1 + δ₁`; by (L₇) = (W₃) and the sealed (W₄). -/
theorem LszPacket.tendsto_lszSourceMagneticMoment (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) (μ : ℝ)
    (hμ : IsResponseMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ μ) :
    Tendsto (fun lam => lszSourceMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam)
      (𝓝[>] 0) (𝓝 (μ : ℂ)) :=
  ((integrable_and_tendsto_sourceMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ φ hφ hφc
    hφ0).2 μ hμ).congr' (eventually_nhdsWithin_of_forall fun lam hlam =>
      (LszPacket.lszSourceMagneticMoment_eq P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ hφc lam
        hlam).symm)

end QED.WickModel

end
