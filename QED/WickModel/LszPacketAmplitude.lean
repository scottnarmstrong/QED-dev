/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszPacketCurrentDensity
public import QED.OneLoop.PacketAmplitude
public import QED.Integration.PacketMoment
public import QED.WickModel.VacuumPolarizationLimit
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
import QED.Frozen.WickModel.LszAmplitudeSpec
import QED.WickModel.LszLimit
import QED.WickModel.LszPhotonLeg
import QED.OneLoop.PacketAmplitudeSmooth
import QED.Algebra.OnShell
import QED.Algebra.SpinorSmooth
import QED.Integration.ParametricSmooth
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The amplitude of the LSZ wave-packet current density

The frozen LSZ current density `QED.WickModel.lszPacketCurrentDensity` (packet 6c, (L₆)) is the
two-momentum Fourier integral `QED.packetFourier` of the LSZ packet amplitude
`F_L(k, k') = w(k') w(k) M_L(k', k)`, where `w` is the packet weight
(`QED.OneLoop.packetWeight`) and `M_L(k', k)` is the LSZ amplitude (L₂) between the one-electron
momenta `p(k⃗')`, `p(k⃗)`, spins up, index `2`.

By the uniqueness half of the characterization (L₂′), the LSZ amplitude is the closed form
`LszLimit.closedForm`: the packet-4b matrix element `ū₊(k') V²(k', k) u₊(k)` at `Z₁ = 1 + δ₁`,
plus the photon-leg term `q² G(k', k)` with `q = p(k⃗') - p(k⃗)` and
`G = e [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū₊(k') γ² u₊(k)` (`LszPacket.photonFactor`). So
`F_L = F + q² w w G`, with `F` the packet-4b amplitude (`QED.OneLoop.packetAmplitude`).

Since `q² ≥ 0` on shell, `Π = -δ₃ + Π_loop` is smooth there and `G` is `C^∞`; hence `F_L` is
`C^∞` with compact support. On the diagonal `k⃗ = k⃗'` the transfer `q` vanishes, so the derivative
of `q²` vanishes there, and `F_L` and `F` have the same derivative on the diagonal.

## Main definitions

* `QED.WickModel.LszPacket.transferSq`: `q² = (p(k⃗') - p(k⃗))²`.
* `QED.WickModel.LszPacket.photonFactor`: the photon-leg factor `G(k', k)`.
* `QED.WickModel.LszPacket.lszPacketAmplitude`: the LSZ packet amplitude `F_L(k, k')`.

## Main statements

* `QED.WickModel.LszPacket.lszPacketCurrentDensity_eq`: (L₆) is `packetFourier F_L`.
* `QED.WickModel.LszPacket.lszAmplitude_oneParticle`: `M_L = ū₊ V² u₊ + q² G`.
* `QED.WickModel.LszPacket.contDiff_lszPacketAmplitude`: `F_L` is `C^∞`.
* `QED.WickModel.LszPacket.hasCompactSupport_lszPacketAmplitude`: `F_L` has compact support.
* `QED.WickModel.LszPacket.fderiv_lszPacketAmplitude_diag`: on the diagonal, `F_L` and the
  packet-4b amplitude at `Z₁ = 1 + δ₁` have the same derivative.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Set MeasureTheory
open scoped ContDiff
open QED.OneLoop

namespace QED.WickModel

/-! ### Definitions -/

/-- The squared momentum transfer `q² = (p(k⃗') - p(k⃗))²` between one-electron momenta. -/
noncomputable def LszPacket.transferSq (m : ℝ) (k' k : Fin 3 → ℝ) : ℝ :=
  Minkowski.dot (oneParticleMomentum m k' - oneParticleMomentum m k)
    (oneParticleMomentum m k' - oneParticleMomentum m k)

/-- The photon-leg factor `G(k', k) = e [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū₊(k') γ² u₊(k)`,
with `Π = -δ₃ + Π_loop` and `q² = LszPacket.transferSq`; the photon-leg term of the LSZ amplitude
is `q² G(k', k)`. -/
noncomputable def LszPacket.photonFactor (P : Params) (k' k : Fin 3 → ℝ) : ℂ :=
  (P.e : ℂ) * (((LszPacket.transferSq P.m k' k + P.mγ ^ 2)⁻¹
      - (LszPacket.transferSq P.m k' k + P.Λ ^ 2)⁻¹ : ℝ) : ℂ)
    * (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (LszPacket.transferSq P.m k' k) : ℂ))
    * (Dirac.bar (Dirac.spinor P.m (oneParticleMomentum P.m k') 0) ⬝ᵥ
        (Dirac.gamma 2 *ᵥ Dirac.spinor P.m (oneParticleMomentum P.m k) 0))

/-- The LSZ packet amplitude `F_L(k, k') = w(k') w(k) M_L(k', k)`, with `M_L` the LSZ amplitude
(L₂) between one-electron momenta, spins up, index `2`; the ket momentum `k` comes first. -/
noncomputable def LszPacket.lszPacketAmplitude (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (φ : ℝ → ℝ) (lam : ℝ) (k k' : Fin 3 → ℝ) : ℂ :=
  ((packetWeight P.m φ lam k' * packetWeight P.m φ lam k : ℝ) : ℂ)
    * lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon (oneParticleMomentum P.m k')
        (oneParticleMomentum P.m k) (dot_oneParticleMomentum P.m k')
        (dot_oneParticleMomentum P.m k) (oneParticleMomentum_pos hm k')
        (oneParticleMomentum_pos hm k) 0 0 2

/-! ### The current density as a Fourier integral -/

/-- The LSZ current density (L₆) is the two-momentum Fourier integral of the LSZ packet
amplitude. -/
theorem LszPacket.lszPacketCurrentDensity_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (φ : ℝ → ℝ) (lam : ℝ) :
    lszPacketCurrentDensity P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam =
      QED.packetFourier (LszPacket.lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam) := by
  funext x
  unfold lszPacketCurrentDensity QED.packetFourier LszPacket.lszPacketAmplitude packetWeight
  congr 1; ext k; congr 1; ext k'
  rw [mul_right_comm]
  congr 2
  push_cast
  ring

/-! ### The LSZ amplitude between one-electron momenta -/

/-- The LSZ amplitude is the closed form `LszLimit.closedForm`, by the uniqueness half of its
characterization (L₂′). -/
private theorem LszPacket.lszAmplitude_eq_closedForm (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      LszLimit.closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 s' s μ :=
  ((lszAmplitude_spec P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ).2 _
    (lszLimit_closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ)).symm

/-- **The LSZ amplitude between one-electron momenta.** It is the packet-4b matrix element at
`Z₁ = 1 + δ₁` plus `q² G(k', k)`. -/
theorem LszPacket.lszAmplitude_oneParticle (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (k' k : Fin 3 → ℝ) :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon (oneParticleMomentum P.m k')
        (oneParticleMomentum P.m k) (dot_oneParticleMomentum P.m k')
        (dot_oneParticleMomentum P.m k) (oneParticleMomentum_pos hm k')
        (oneParticleMomentum_pos hm k) 0 0 2 =
      packetMatrixElement P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ k' k
        + (LszPacket.transferSq P.m k' k : ℂ) * LszPacket.photonFactor P k' k := by
  rw [LszPacket.lszAmplitude_eq_closedForm, LszLimit.closedForm, vacuumPolarization_eq_loop]
  unfold packetMatrixElement LszPacket.photonFactor LszPacket.transferSq
  congr 1
  push_cast
  ring

/-- The LSZ packet amplitude is the packet-4b amplitude at `Z₁ = 1 + δ₁` plus
`q² w(k') w(k) G(k', k)`. -/
theorem LszPacket.uncurry_lszPacketAmplitude (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (φ : ℝ → ℝ) (lam : ℝ) :
    Function.uncurry (LszPacket.lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam) =
      fun kk => Function.uncurry (packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ φ lam) kk
        + (LszPacket.transferSq P.m kk.2 kk.1 : ℂ) *
          (((packetWeight P.m φ lam kk.2 * packetWeight P.m φ lam kk.1 : ℝ) : ℂ)
            * LszPacket.photonFactor P kk.2 kk.1) := by
  funext kk
  obtain ⟨k, k'⟩ := kk
  simp only [Function.uncurry_apply_pair, LszPacket.lszPacketAmplitude, packetAmplitude,
    LszPacket.lszAmplitude_oneParticle]
  ring

/-! ### Smoothness and compact support -/

/-- `(k⃗, k⃗') ↦ q²` is `C^∞`. -/
theorem LszPacket.contDiff_transferSq {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => LszPacket.transferSq m kk.2 kk.1) :=
  contDiff_dot_self_comp (contDiff_oneParticleMomentum_sub hm)

/-- Between one-electron momenta the transfer is spacelike or null: `q² ≥ 0`. -/
theorem LszPacket.transferSq_nonneg {m : ℝ} (hm : 0 < m) (k' k : Fin 3 → ℝ) :
    0 ≤ LszPacket.transferSq m k' k :=
  Minkowski.dot_sub_self_nonneg_of_onShell (dot_oneParticleMomentum m k')
    (dot_oneParticleMomentum m k) (oneParticleMomentum_pos hm k') (oneParticleMomentum_pos hm k)

/-- **Smoothness of `Π_loop`.** For `m > 0` and regulator fermions heavier than the electron,
`vacuumPolarizationLoop P` is `C^∞` on `s > -4m²`. -/
theorem LszPacket.contDiffOn_vacuumPolarizationLoop {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) :
    ContDiffOn ℝ ∞ (vacuumPolarizationLoop P) (Ioi (-(4 * P.m ^ 2))) := by
  have hD : ∀ f, ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2) := fun f => by
    unfold vacuumPolarizationFeynmanMass
    fun_prop
  set W := ⋂ f : Fin 3, {q : ℝ × ℝ | 0 < vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2}
  have hW : IsOpen W :=
    isOpen_iInter_of_finite fun f => isOpen_lt continuous_const (hD f).continuous
  have hUW : Ioi (-(4 * P.m ^ 2)) ×ˢ Icc (0 : ℝ) 1 ⊆ W := fun q hq => mem_iInter.mpr fun f => by
    change 0 < vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2
    rw [← VacuumPolarizationLimit.selfEnergyFeynmanMass_eq]
    exact VacuumPolarizationLimit.selfEnergyFeynmanMass_mass_pos hm hM₁ hM₂ hq.1 hq.2 f
  have hw : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.2 * (1 - q.2)) := by fun_prop
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.2 * (1 - q.2) *
      ∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f) q.1 q.2)) W :=
    hw.contDiffOn.mul (ContDiffOn.sum fun f _ => contDiffOn_const.mul
      ((hD f).contDiffOn.log fun q hq => (mem_iInter.mp hq f).ne'))
  have h := QED.Integration.contDiffOn_integral_of_contDiffOn_prod
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) isCompact_Icc
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => Ioc_subset_Icc_self hx)
    isOpen_Ioi hW hUW hg
  refine (contDiffOn_const (c := P.e ^ 2 / (2 * Real.pi ^ 2))).mul h |>.congr fun s _ => ?_
  simp only [vacuumPolarizationLoop, intervalIntegral.integral_of_le zero_le_one]

/-- **Smoothness of the photon-leg factor.** `(k⃗, k⃗') ↦ G(k', k)` is `C^∞`. -/
theorem LszPacket.contDiff_photonFactor {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) :
    ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => LszPacket.photonFactor P kk.2 kk.1) := by
  have hQ := LszPacket.contDiff_transferSq hm
  have hQ0 := fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => LszPacket.transferSq_nonneg hm kk.2 kk.1
  have hD : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (LszPacket.transferSq P.m kk.2 kk.1 + P.mγ ^ 2)⁻¹
        - (LszPacket.transferSq P.m kk.2 kk.1 + P.Λ ^ 2)⁻¹) :=
    ((hQ.add contDiff_const).inv fun kk => (add_pos_of_nonneg_of_pos (hQ0 kk)
      (pow_pos hmγ 2)).ne').sub ((hQ.add contDiff_const).inv fun kk =>
        (add_pos_of_nonneg_of_pos (hQ0 kk) (pow_pos hΛ 2)).ne')
  have hPi : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      vacuumPolarizationLoop P (LszPacket.transferSq P.m kk.2 kk.1)) :=
    (LszPacket.contDiffOn_vacuumPolarizationLoop hm hM₁ hM₂).comp_contDiff hQ
      fun kk => dot_oneParticleMomentum_sub_mem_Ioi hm kk.2 kk.1
  have hk : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => oneParticleMomentum P.m kk.1) :=
    (contDiff_oneParticleMomentum hm).comp contDiff_fst
  have hk' : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => oneParticleMomentum P.m kk.2) :=
    (contDiff_oneParticleMomentum hm).comp contDiff_snd
  have hu := Dirac.contDiff_spinor_comp hm hk (fun kk => oneParticleMomentum_pos hm kk.1) 0
  have hw := Dirac.contDiff_bar_comp
    (Dirac.contDiff_spinor_comp hm hk' (fun kk => oneParticleMomentum_pos hm kk.2) 0)
  have hS := Dirac.contDiff_dotProduct_mulVec (M := fun _ => Dirac.gamma 2) hw hu
    fun i j => contDiff_const
  unfold LszPacket.photonFactor
  exact ((contDiff_const.mul (Dirac.contDiff_ofReal_comp hD)).mul
    (contDiff_const.add (Dirac.contDiff_ofReal_comp hPi))).mul hS

/-- **Smoothness of the LSZ packet amplitude.** For a `C^∞` profile `φ`, the LSZ packet amplitude
`F_L(k, k')` is `C^∞` in `(k⃗, k⃗')` jointly. -/
theorem LszPacket.contDiff_lszPacketAmplitude (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (lam : ℝ) :
    ContDiff ℝ ∞
      (Function.uncurry
        (LszPacket.lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam)) := by
  rw [LszPacket.uncurry_lszPacketAmplitude]
  have hw := contDiff_packetWeight hm hφ lam
  exact (contDiff_packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ hφ lam).add
    ((Dirac.contDiff_ofReal_comp (LszPacket.contDiff_transferSq hm)).mul
      ((Dirac.contDiff_ofReal_comp ((hw.comp contDiff_snd).mul (hw.comp contDiff_fst))).mul
        (LszPacket.contDiff_photonFactor hm hmγ hΛ hM₁ hM₂)))

/-- **Compact support of the LSZ packet amplitude.** If the profile `φ` has compact support and
`λ ≠ 0`, then `F_L(k, k')` has compact support in `(k⃗, k⃗')`. -/
theorem LszPacket.hasCompactSupport_lszPacketAmplitude (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) {lam : ℝ}
    (hlam : lam ≠ 0) :
    HasCompactSupport
      (Function.uncurry
        (LszPacket.lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam)) := by
  obtain ⟨r, hr⟩ := exists_norm_le_of_packetWeight_ne_zero (m := P.m) hφc hlam
  refine HasCompactSupport.intro (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) r)
    fun kk hkk => ?_
  by_contra hne
  apply hkk
  have h1 : packetWeight P.m φ lam kk.2 * packetWeight P.m φ lam kk.1 ≠ 0 := by
    intro h
    apply hne
    simp [Function.uncurry, LszPacket.lszPacketAmplitude, h]
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (hr _ (right_ne_zero_of_mul h1)) (hr _ (left_ne_zero_of_mul h1))

/-! ### The derivative on the diagonal -/

/-- If a differentiable four-vector field `q` vanishes at `x`, then `y ↦ q(y)²` has derivative
`0` at `x`. -/
theorem LszPacket.hasFDerivAt_dot_self_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : E → Fin 4 → ℝ} {x : E} (hq : DifferentiableAt ℝ q x) (h0 : q x = 0) :
    HasFDerivAt (fun y => Minkowski.dot (q y) (q y)) (0 : E →L[ℝ] ℝ) x := by
  have hc : ∀ μ, HasFDerivAt (fun y => q y μ)
      ((ContinuousLinearMap.proj μ).comp (fderiv ℝ q x)) x :=
    fun μ => hasFDerivAt_pi'.1 hq.hasFDerivAt μ
  have hz : ∀ μ, q x μ = 0 := fun μ => by simp [h0]
  have h := (((((hc 0).fun_mul (hc 0)).fun_neg.fun_add ((hc 1).fun_mul (hc 1))).fun_add
    ((hc 2).fun_mul (hc 2))).fun_add ((hc 3).fun_mul (hc 3)))
  simp only [hz, zero_smul, add_zero, neg_zero] at h
  simpa only [Minkowski.dot_eq] using h

/-- **The derivative on the diagonal.** At every diagonal point `(P, P)`, the LSZ packet amplitude
and the packet-4b amplitude at `Z₁ = 1 + δ₁` have the same derivative: the difference is
`q² w w G` and `q`, hence the derivative of `q²`, vanishes on the diagonal. -/
theorem LszPacket.fderiv_lszPacketAmplitude_diag (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (lam : ℝ)
    (K : Fin 3 → ℝ) :
    fderiv ℝ
        (Function.uncurry (LszPacket.lszPacketAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam))
        (K, K) =
      fderiv ℝ (Function.uncurry (packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ φ lam))
        (K, K) := by
  have hw := contDiff_packetWeight hm hφ lam
  have hG : ContDiff ℝ ∞ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ((packetWeight P.m φ lam kk.2 * packetWeight P.m φ lam kk.1 : ℝ) : ℂ)
        * LszPacket.photonFactor P kk.2 kk.1) :=
    (Dirac.contDiff_ofReal_comp ((hw.comp contDiff_snd).mul (hw.comp contDiff_fst))).mul
      (LszPacket.contDiff_photonFactor hm hmγ hΛ hM₁ hM₂)
  have hQr := LszPacket.hasFDerivAt_dot_self_of_eq_zero
    ((contDiff_oneParticleMomentum_sub hm).differentiable (by simp) (K, K)) (by simp)
  have hQ : HasFDerivAt (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (LszPacket.transferSq P.m kk.2 kk.1 : ℂ))
      (0 : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) →L[ℝ] ℂ) (K, K) := by
    have hc : HasFDerivAt ((↑) : ℝ → ℂ) Complex.ofRealCLM
        (LszPacket.transferSq P.m K K) := Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def, LszPacket.transferSq] using hc.comp (K, K) hQr
  have hQ0 : LszPacket.transferSq P.m K K = 0 := by
    simp [LszPacket.transferSq, Minkowski.dot_eq]
  have hph : HasFDerivAt (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (LszPacket.transferSq P.m kk.2 kk.1 : ℂ) *
        (((packetWeight P.m φ lam kk.2 * packetWeight P.m φ lam kk.1 : ℝ) : ℂ)
          * LszPacket.photonFactor P kk.2 kk.1))
      (0 : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) →L[ℝ] ℂ) (K, K) := by
    convert hQ.fun_mul (hG.differentiable (by simp) (K, K)).hasFDerivAt using 1
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hQ0]
  have hF := ((contDiff_packetAmplitude P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ hφ lam).differentiable
    (by simp) (K, K)).hasFDerivAt
  rw [LszPacket.uncurry_lszPacketAmplitude, (hF.fun_add hph).fderiv, add_zero]

end QED.WickModel

end
