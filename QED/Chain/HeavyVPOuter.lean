/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyVPUnit
public import QED.TwoLoop.UnitVPLink
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-flavour VP unit as the outer functional of a flavour-summed subtracted `Π` (O3-M2)

Helper-level generalization of `QED.TwoLoop.UnitVPLink.vpUnitReg_eq_vpOuterF2` from the frozen
three-flavour model (loop mass = open-line mass) to an **arbitrary finite family of loop
flavours**, with the open-line mass `1`. It is **not** frozen and does not depend on any
multi-lepton model: the flavour family is given by explicit masses and coefficients, so that a
later model whose vacuum polarization unfolds to `flavourPi` can use these statements directly.

## Objects

* `flavourPi e mass coeff s = (e²/(2π²)) ∫₀¹ x(1-x) ∑_f c_f log(M_f² + x(1-x)s) dx`: the loop
  function of `QED.WickModel.vacuumPolarizationLoop` for a finite flavour family `ι`; for the
  frozen model, `vacuumPolarizationLoop P = flavourPi P.e P.mass P.loopCoeff` by definition
  (`vacuumPolarizationLoop_eq_flavourPi`).
* `heavyMass M_L M₁ M₂ = ![M_L, M₁, M₂]`, `heavyCoeff c₁ c₂ = ![1, c₁, c₂]`, and
  `heavyPi e M_L M₁ M₂ c₁ c₂ = flavourPi e (heavyMass ..) (heavyCoeff ..)`: one heavy lepton with
  its own Pauli–Villars pair.

## Main statements

* `flavourPi_sub_zero`: the spectral form of the subtracted function,
  `Π(s) - Π(0) = (e²/(4π²)) ∑_f c_f specJ(M_f, s)` for `s ≥ 0` and nonzero masses.
* `outerF2_flavourPi_sub`: **for any finite flavour family**, with `0 < m_γ < Λ` and
  `m_γ² < 4M_f²`, `16π⁴ outerF2 (s ↦ (Π(s) - Π(0)) s D(s)²) = e² ∑_f c_f vpFlavour M_f m_γ Λ`.
* `heavyOuter_eq_heavyUnitReg`: for one heavy lepton with the two Pauli–Villars conditions of
  its own mass, `16π⁴ outerF2 (s ↦ (Π_ℓ(s) - Π_ℓ(0)) s D(s)²) = e² heavyUnitReg M_L m_γ Λ M₁ M₂`.
* `outerF2_blocks`: for a finite set of leptons, each with its own Pauli–Villars pair (the
  flavour family `Σ ℓ, Fin 3`), the outer functional of the total subtracted `Π` is
  `e² ∑_ℓ heavyUnitReg (m_ℓ) m_γ Λ (M₁ℓ) (M₂ℓ)`: the flavour sum splits into blocks.
* `vpOuterF2_eq_heavyUnitReg_one`: at `M_L = 1` the heavy statement reproduces
  `QED.TwoLoop.UnitVPLink.vpUnitReg_eq_vpOuterF2` for the frozen model.
* `specJ_smul`, `flavourPi_sub_zero_smul`: the subtracted function is invariant under a common
  rescaling `M_f ↦ t M_f`, `s ↦ t² s` (the `Π` part of the mass-scaling step).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain.HeavyVP

open QED.WickModel QED.TwoLoop.VPUnit QED.TwoLoop.UnitVPLink

variable {ι : Type*} [Fintype ι]

/-! ### The flavour-summed loop function -/

/-- **The one-loop VP loop function of a finite flavour family** (masses `mass f`, loop
coefficients `coeff f`, charge `e`):
`(e²/(2π²)) ∫₀¹ x(1-x) ∑_f c_f log(M_f² + x(1-x)s) dx`, the body of
`QED.WickModel.vacuumPolarizationLoop` with the flavours as parameters. -/
noncomputable def flavourPi (e : ℝ) (mass coeff : ι → ℝ) (s : ℝ) : ℝ :=
  e ^ 2 / (2 * π ^ 2) * ∫ x in (0 : ℝ)..1, x * (1 - x) *
    ∑ f, coeff f * Real.log (vacuumPolarizationFeynmanMass (mass f) s x)

/-- The frozen model's loop function is `flavourPi` of its three flavours. -/
theorem vacuumPolarizationLoop_eq_flavourPi (P : Params) :
    vacuumPolarizationLoop P = flavourPi P.e P.mass P.loopCoeff := rfl

theorem intervalIntegrable_flavourLoop {mass coeff : ι → ℝ} (hmass : ∀ f, mass f ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) :
    IntervalIntegrable (fun x => x * (1 - x) *
      ∑ f, coeff f * Real.log (vacuumPolarizationFeynmanMass (mass f) s x)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
  refine (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).continuousOn.mul ?_
  refine continuousOn_finsetSum _ fun f _ => continuousOn_const.mul ?_
  refine ContinuousOn.log ?_ fun x hx => (feynmanMass_pos (hmass f) hs hx).ne'
  unfold vacuumPolarizationFeynmanMass
  fun_prop

/-- **The spectral form of the subtracted loop function**: for nonzero masses and `s ≥ 0`,
`Π(s) - Π(0) = (e²/(4π²)) ∑_f c_f ∫₀¹ ρ(v) s/(s + 4M_f²/(1-v²)) dv`. -/
theorem flavourPi_sub_zero {e : ℝ} {mass coeff : ι → ℝ} (hmass : ∀ f, mass f ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) :
    flavourPi e mass coeff s - flavourPi e mass coeff 0 =
      e ^ 2 / (4 * π ^ 2) * ∑ f, coeff f * specJ (mass f) s := by
  unfold flavourPi
  rw [← mul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_flavourLoop hmass hs)
    (intervalIntegrable_flavourLoop hmass le_rfl)]
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1,
      x * (1 - x) * ∑ f, coeff f * Real.log (vacuumPolarizationFeynmanMass (mass f) s x) -
        x * (1 - x) * ∑ f, coeff f * Real.log (vacuumPolarizationFeynmanMass (mass f) 0 x) =
      ∑ f, coeff f * (x * (1 - x) * Real.log ((mass f ^ 2 + x * (1 - x) * s) / mass f ^ 2)) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h1 := feynmanMass_pos (hmass f) hs hx
    have h2 : (0 : ℝ) < mass f ^ 2 := by have := hmass f; positivity
    unfold vacuumPolarizationFeynmanMass at h1 ⊢
    rw [Real.log_div h1.ne' h2.ne', mul_zero, add_zero]
    ring
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_finsetSum fun f _ =>
      (intervalIntegrable_log_ratio (hmass f) hs).const_mul _]
  have hspec : ∀ f, ∫ x in (0 : ℝ)..1, coeff f *
      (x * (1 - x) * Real.log ((mass f ^ 2 + x * (1 - x) * s) / mass f ^ 2)) =
      coeff f * (1 / 2 * specJ (mass f) s) := fun f => by
    have hK : -(4 * mass f ^ 2) < s := by
      have := hmass f
      have : 0 < mass f ^ 2 := by positivity
      linarith
    rw [intervalIntegral.integral_const_mul, integral_mul_log_eq_spectral (hmass f) hK]
    rfl
  simp only [hspec]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-! ### The outer functional of the subtracted function -/

/-- **The outer functional of a flavour-summed subtracted `Π` (any finite flavour family).**
With nonzero masses, `0 < m_γ < Λ` and `m_γ² < 4M_f²` for every flavour,
`16π⁴ outerF2 (s ↦ (Π(s) - Π(0)) s D(s)²) = e² ∑_f c_f vpFlavour M_f m_γ Λ`. -/
theorem outerF2_flavourPi_sub {e mγ Λ : ℝ} {mass coeff : ι → ℝ} (hmass : ∀ f, mass f ≠ 0)
    (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : ∀ f, mγ ^ 2 < 4 * mass f ^ 2) :
    16 * π ^ 4 * outerF2 (fun s => (flavourPi e mass coeff s - flavourPi e mass coeff 0) * s *
        photonD mγ Λ s ^ 2) =
      e ^ 2 * ∑ f, coeff f * vpFlavour (mass f) mγ Λ := by
  have F := fun f => vpFlavour_eq_outer (hmass f) hmγ hmΛ (hm2 f)
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1,
      x ^ 2 * ((flavourPi e mass coeff (photonVar x) - flavourPi e mass coeff 0) * photonVar x *
        photonD mγ Λ (photonVar x) ^ 2) =
      e ^ 2 / (4 * π ^ 2) * ∑ f, coeff f * flavOuter (mass f) mγ Λ x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [flavourPi_sub_zero hmass (photonVar_nonneg hx)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    unfold flavOuter
    ring
  have hv : ∀ f, ∫ x in (0 : ℝ)..1, coeff f * flavOuter (mass f) mγ Λ x =
      coeff f * vpFlavour (mass f) mγ Λ := fun f => by
    rw [intervalIntegral.integral_const_mul, ← (F f).2]
  unfold outerF2
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun f _ => (F f).1.const_mul _]
  simp only [hv]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The same with the counterterm written as `δ₃ = Π(0)` (the photon on-shell condition). -/
theorem outerF2_flavourPi_delta3 {e mγ Λ δ₃ : ℝ} {mass coeff : ι → ℝ} (hmass : ∀ f, mass f ≠ 0)
    (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : ∀ f, mγ ^ 2 < 4 * mass f ^ 2)
    (hδ₃ : δ₃ = flavourPi e mass coeff 0) :
    16 * π ^ 4 * outerF2 (fun s => (flavourPi e mass coeff s - δ₃) * s * photonD mγ Λ s ^ 2) =
      e ^ 2 * ∑ f, coeff f * vpFlavour (mass f) mγ Λ := by
  subst hδ₃
  exact outerF2_flavourPi_sub hmass hmγ hmΛ hm2

/-! ### One heavy lepton with its own Pauli–Villars pair -/

/-- The masses of one lepton block: the lepton of mass `M_L` and its regulators `M₁, M₂`. -/
noncomputable def heavyMass (ML M₁ M₂ : ℝ) : Fin 3 → ℝ := ![ML, M₁, M₂]

/-- The loop coefficients of one lepton block: `1, c₁, c₂`. -/
noncomputable def heavyCoeff (c₁ c₂ : ℝ) : Fin 3 → ℝ := ![1, c₁, c₂]

/-- The loop function of one heavy lepton with its own Pauli–Villars pair. -/
noncomputable def heavyPi (e ML M₁ M₂ c₁ c₂ : ℝ) : ℝ → ℝ :=
  flavourPi e (heavyMass ML M₁ M₂) (heavyCoeff c₁ c₂)

/-- The frozen model's loop function is the block of the open-line lepton. -/
theorem vacuumPolarizationLoop_eq_heavyPi (P : Params) :
    vacuumPolarizationLoop P = heavyPi P.e P.m P.M₁ P.M₂ P.c₁ P.c₂ := rfl

/-- The block sum of the vpFlavour values with the Pauli–Villars conditions of the loop mass. -/
theorem sum_heavy_vpFlavour {ML M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hML : 0 < ML) (hM₂ : ML < M₂)
    (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : ML ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) :
    ∑ f, heavyCoeff c₁ c₂ f * vpFlavour (heavyMass ML M₁ M₂ f) mγ Λ =
      heavyUnitReg ML mγ Λ M₁ M₂ := by
  obtain ⟨hc₁, hc₂⟩ := pvL_unique (sq_ne_sq_of_pvL hML hM₂ hPV₁ hPV₂) hPV₁ hPV₂
  rw [Fin.sum_univ_three]
  simp only [heavyCoeff, heavyMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, heavyUnitReg, hc₁, hc₂]

theorem heavyMass_ne_zero {ML M₁ M₂ : ℝ} (hML : 0 < ML) (hM₁ : ML < M₁) (hM₂ : ML < M₂)
    (f : Fin 3) : heavyMass ML M₁ M₂ f ≠ 0 := by
  fin_cases f
  · exact hML.ne'
  · exact (hML.trans hM₁).ne'
  · exact (hML.trans hM₂).ne'

theorem heavyMass_photon {ML M₁ M₂ mγ : ℝ} (hML : 0 < ML) (hM₁ : ML < M₁) (hM₂ : ML < M₂)
    (hmγ : 0 < mγ) (hm2 : mγ < 2 * ML) (f : Fin 3) :
    mγ ^ 2 < 4 * heavyMass ML M₁ M₂ f ^ 2 := by
  have h0 : mγ ^ 2 < 4 * ML ^ 2 := by nlinarith
  fin_cases f
  · exact h0
  · change mγ ^ 2 < 4 * M₁ ^ 2
    nlinarith
  · change mγ ^ 2 < 4 * M₂ ^ 2
    nlinarith

/-- **The heavy-flavour VP unit is the outer functional of the heavy lepton's subtracted `Π`.**
For a loop lepton of mass `M_L > 0` with regulators `M₁, M₂ > M_L` and coefficients satisfying
the Pauli–Villars conditions of `M_L`, `0 < m_γ < Λ` and `m_γ < 2M_L`:
`16π⁴ outerF2 (s ↦ (Π_ℓ(s) - Π_ℓ(0)) s D(s)²) = e² heavyUnitReg M_L m_γ Λ M₁ M₂`. -/
theorem heavyOuter_eq_heavyUnitReg {e ML M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hML : 0 < ML) (hM₁ : ML < M₁)
    (hM₂ : ML < M₂) (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : ML ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0)
    (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : mγ < 2 * ML) :
    16 * π ^ 4 * outerF2 (fun s => (heavyPi e ML M₁ M₂ c₁ c₂ s - heavyPi e ML M₁ M₂ c₁ c₂ 0) * s *
        photonD mγ Λ s ^ 2) =
      e ^ 2 * heavyUnitReg ML mγ Λ M₁ M₂ := by
  unfold heavyPi
  rw [outerF2_flavourPi_sub (heavyMass_ne_zero hML hM₁ hM₂) hmγ hmΛ
    (heavyMass_photon hML hM₁ hM₂ hmγ hm2), sum_heavy_vpFlavour hML hM₂ hPV₁ hPV₂]

/-- **At loop mass `1` the heavy statement is the frozen model's identity**
(`QED.TwoLoop.UnitVPLink.vpUnitReg_eq_vpOuterF2`, re-derived): at `m = 1`, with the Pauli–Villars
conditions, `0 < m_γ < Λ`, `m_γ < 2` and `δ₃ = Π_loop(0)`,
`16π⁴ vpOuterF2 P = e² heavyUnitReg 1 m_γ Λ M₁ M₂ = e² vpUnitReg m_γ Λ M₁ M₂`. -/
theorem vpOuterF2_eq_heavyUnitReg_one (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁)
    (hM₂ : 1 < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hmγ : 0 < P.mγ)
    (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) (hδ₃ : P.δ₃ = vacuumPolarizationLoop P 0) :
    16 * π ^ 4 * vpOuterF2 P = P.e ^ 2 * heavyUnitReg 1 P.mγ P.Λ P.M₁ P.M₂ ∧
      heavyUnitReg 1 P.mγ P.Λ P.M₁ P.M₂ = vpUnitReg P.mγ P.Λ P.M₁ P.M₂ := by
  refine ⟨?_, heavyUnitReg_one _ _ _ _⟩
  rw [hm] at hPV₂
  have key := heavyOuter_eq_heavyUnitReg (e := P.e) (c₁ := P.c₁) (c₂ := P.c₂) one_pos hM₁ hM₂
    hPV₁ hPV₂ hmγ hmΛ (by linarith)
  unfold vpOuterF2
  rw [hδ₃, vacuumPolarizationLoop_eq_heavyPi, hm]
  exact key

/-! ### Several leptons, each with its own Pauli–Villars pair -/

/-- **The flavour sum splits into lepton blocks.** For a finite set `L` of leptons, lepton `ℓ` of
mass `m_ℓ > 0` with its own regulators `M₁ℓ, M₂ℓ > m_ℓ` and coefficients satisfying the
Pauli–Villars conditions of `m_ℓ`, with `0 < m_γ < Λ` and `m_γ < 2m_ℓ`: the outer functional of
the total subtracted loop function of the flavour family `Σ ℓ, Fin 3` is
`e² ∑_ℓ heavyUnitReg m_ℓ m_γ Λ M₁ℓ M₂ℓ`. -/
theorem outerF2_blocks {L : Type*} [Fintype L] {e mγ Λ : ℝ} {ml M₁ M₂ c₁ c₂ : L → ℝ}
    (hml : ∀ ℓ, 0 < ml ℓ) (hM₁ : ∀ ℓ, ml ℓ < M₁ ℓ) (hM₂ : ∀ ℓ, ml ℓ < M₂ ℓ)
    (hPV₁ : ∀ ℓ, 1 + c₁ ℓ + c₂ ℓ = 0)
    (hPV₂ : ∀ ℓ, ml ℓ ^ 2 + c₁ ℓ * M₁ ℓ ^ 2 + c₂ ℓ * M₂ ℓ ^ 2 = 0)
    (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : ∀ ℓ, mγ < 2 * ml ℓ) :
    16 * π ^ 4 * outerF2 (fun s =>
        (flavourPi e (fun p : (Σ _ : L, Fin 3) => heavyMass (ml p.1) (M₁ p.1) (M₂ p.1) p.2)
            (fun p => heavyCoeff (c₁ p.1) (c₂ p.1) p.2) s -
          flavourPi e (fun p : (Σ _ : L, Fin 3) => heavyMass (ml p.1) (M₁ p.1) (M₂ p.1) p.2)
            (fun p => heavyCoeff (c₁ p.1) (c₂ p.1) p.2) 0) * s * photonD mγ Λ s ^ 2) =
      e ^ 2 * ∑ ℓ, heavyUnitReg (ml ℓ) mγ Λ (M₁ ℓ) (M₂ ℓ) := by
  have h := outerF2_flavourPi_sub (e := e)
    (mass := fun p : (Σ _ : L, Fin 3) => heavyMass (ml p.1) (M₁ p.1) (M₂ p.1) p.2)
    (coeff := fun p => heavyCoeff (c₁ p.1) (c₂ p.1) p.2)
    (fun p => heavyMass_ne_zero (hml p.1) (hM₁ p.1) (hM₂ p.1) p.2) hmγ hmΛ
    (fun p => heavyMass_photon (hml p.1) (hM₁ p.1) (hM₂ p.1) hmγ (hm2 p.1) p.2)
  rw [h, Fintype.sum_sigma]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => sum_heavy_vpFlavour (hml ℓ) (hM₂ ℓ) (hPV₁ ℓ) (hPV₂ ℓ)

/-! ### Scale invariance of the subtracted function -/

/-- `specJ (tM) (t²s) = specJ M s` for `t ≠ 0`. -/
theorem specJ_smul {t : ℝ} (ht : t ≠ 0) (M s : ℝ) : specJ (t * M) (t ^ 2 * s) = specJ M s := by
  unfold specJ
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  refine intervalIntegral.integral_congr fun v _ => ?_
  have e : t ^ 2 * s + 4 * (t * M) ^ 2 / (1 - v ^ 2) = t ^ 2 * (s + 4 * M ^ 2 / (1 - v ^ 2)) := by
    rw [mul_pow, mul_add]
    ring
  rw [e, mul_div_mul_left _ _ ht2]

/-- **The subtracted loop function is invariant under a common mass rescaling**: for `t ≠ 0`,
nonzero masses and `s ≥ 0`, `Π_{tM}(t²s) - Π_{tM}(0) = Π_M(s) - Π_M(0)`. -/
theorem flavourPi_sub_zero_smul {e t : ℝ} (ht : t ≠ 0) {mass coeff : ι → ℝ}
    (hmass : ∀ f, mass f ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    flavourPi e (fun f => t * mass f) coeff (t ^ 2 * s) -
        flavourPi e (fun f => t * mass f) coeff 0 =
      flavourPi e mass coeff s - flavourPi e mass coeff 0 := by
  rw [flavourPi_sub_zero (fun f => mul_ne_zero ht (hmass f)) (by positivity),
    flavourPi_sub_zero hmass hs]
  simp only [specJ_smul ht]

end QED.Chain.HeavyVP
