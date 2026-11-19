/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCValueOuter
public import QED.ChainProof.HCLinks
public import QED.TwoLoop.CountertermScaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The set (b) photon function: its `q² → 0⁺` limit and its value in units of `m` (O3-9, O3-10)

Helper level, Phase 5 Stage 1a, toward `QED.ChainProof.ChainPauliAtLink`. The two-insertion chain
replaces the photon propagator `D` by `D (Π k² D)²` with the renormalized `Π = Π_loop - δ₃`; its
photon function is

`chainPhoton P s = (Π_loop(s) - δ₃)² s² D(s)³`

(`Π_loop = QED.WickModel.vacuumPolarizationLoop P`, flavour-summed with the Pauli–Villars
coefficients of `P`; `D = QED.TwoLoop.UnitVPLink.photonD m_γ Λ`). This file is about the explicit
functional `outerAt P.m s (chainPhoton P)` of `QED/ChainProof/HCValueOuter.lean`.

## Main statements

* `chainPhoton_eq_chainSpec`: with `δ₃ = Π_loop(0)` (the photon condition (Z₈)), on `s ≥ 0` the
  photon function is the spectral form
  `chainSpec P s = ((e²/(4π²)) ∑_f c_f specJ(M_f, s))² s² D(s)³`.
* `continuousOn_specJ`: each spectral bubble is continuous on `(0, ∞)` (dominated convergence in
  the spectral variable).
* `abs_chainSpec_le`: `|chainSpec P s| ≤ (e²/(4π²))² A² Λ²` on `s ≥ 0`, with
  `A = ∑_f |c_f|/(15 M_f²)`, from `specJ(M, s) ≤ s/(15M²)` and `s⁴ D³ ≤ Λ²`.
* `tendsto_outerAt_chainPhoton` (**O3-9 on the explicit side**): at admissible parameters,
  `outerAt m s (chainPhoton P) → outerAt m 0 (chainPhoton P)` as `s → 0⁺`.
* `outerAt_chainPhoton_zero` (**O3-10 with the mass scaling**): at admissible parameters,
  `e² outerAt m 0 (chainPhoton P) = e⁶ chainRegMass m m_γ Λ M₁ M₂/(64π⁶)`. The proof scales
  `specJ(M, m² t) = specJ(M/m, t)` and `D_{m_γ,Λ}(m² t) = D_{m_γ/m, Λ/m}(t)/m²`, then uses the
  Pauli–Villars conditions in units of `m` (`QED.Chain.ChainB.sum_heavy_specJ`); at `m = 1` it is
  `QED.Chain.ChainB.chainModel_eq_chainReg`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real
open QED.WickModel (Params vacuumPolarizationLoop)

namespace QED.ChainProof.HCValue

open QED.TwoLoop.UnitVPLink QED.TwoLoop.VPUnit QED.Chain.ChainB QED.Chain.HeavyVP

/-- **The set (b) photon function** `(Π_loop(s) - δ₃)² s² D(s)³`. -/
noncomputable def chainPhoton (P : Params) (s : ℝ) : ℝ :=
  (vacuumPolarizationLoop P s - P.δ₃) ^ 2 * s ^ 2 * photonD P.mγ P.Λ s ^ 3

/-- The spectral form `((e²/(4π²)) ∑_f c_f specJ(M_f, s))² s² D(s)³` of `chainPhoton`. -/
noncomputable def chainSpec (P : Params) (s : ℝ) : ℝ :=
  (P.e ^ 2 / (4 * π ^ 2) * ∑ f, P.loopCoeff f * specJ (P.mass f) s) ^ 2 * s ^ 2 *
    photonD P.mγ P.Λ s ^ 3

/-- With `δ₃ = Π_loop(0)`, the photon function is its spectral form on `s ≥ 0`. -/
theorem chainPhoton_eq_chainSpec {P : Params} (hmass : ∀ f, P.mass f ≠ 0)
    (hδ₃ : P.δ₃ = vacuumPolarizationLoop P 0) {s : ℝ} (hs : 0 ≤ s) :
    chainPhoton P s = chainSpec P s := by
  unfold chainPhoton chainSpec
  rw [hδ₃, vacuumPolarizationLoop_sub_zero P hmass hs]

/-! ### Continuity and bounds -/

/-- **Each spectral bubble is continuous on `(0, ∞)`.** -/
theorem continuousOn_specJ {M : ℝ} (hM : M ≠ 0) : ContinuousOn (specJ M) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  refine ContinuousAt.continuousWithinAt ?_
  unfold specJ
  have hM2 : 0 < M ^ 2 := by positivity
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => 2 * t₀ / (4 * M ^ 2)) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun s => ?_
    have : Measurable fun v : ℝ => rho v * (s / (s + 4 * M ^ 2 / (1 - v ^ 2))) := by
      unfold rho
      fun_prop
    exact this.aestronglyMeasurable
  · have hev : ∀ᶠ s in 𝓝 t₀, s ∈ Ioo 0 (2 * t₀) := Ioo_mem_nhds ht₀' (by linarith)
    filter_upwards [hev] with s hs
    refine Eventually.of_forall fun v hv => ?_
    rw [uIoc_of_le zero_le_one] at hv
    obtain ⟨b0, b1⟩ := specJ_integrand_bound hM hs.1.le (Ioc_subset_Icc_self hv)
    rw [Real.norm_eq_abs, abs_of_nonneg b0]
    refine b1.trans ?_
    have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hv0 : 0 ≤ v ^ 2 * (1 - v ^ 2 / 3) := mul_nonneg (sq_nonneg v) (by linarith)
    have hv1 : v ^ 2 * (1 - v ^ 2 / 3) ≤ 1 := by nlinarith [sq_nonneg v]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [hs.1, hs.2]
  · have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with v hv1 hv
    rw [uIoc_of_le zero_le_one] at hv
    have hv' : v < 1 := lt_of_le_of_ne hv.2 hv1
    have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
    have hc : 0 < 4 * M ^ 2 / (1 - v ^ 2) := by positivity
    refine continuousAt_const.mul (continuousAt_id.div (continuousAt_id.add continuousAt_const) ?_)
    change t₀ + 4 * M ^ 2 / (1 - v ^ 2) ≠ 0
    linarith

/-- `D(s) ≥ 0` for `s ≥ 0` and `0 < m_γ ≤ Λ`. -/
theorem photonD_nonneg {mγ Λ s : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ ≤ Λ) (hs : 0 ≤ s) :
    0 ≤ photonD mγ Λ s := by
  unfold photonD
  have ha : 0 < s + mγ ^ 2 := by positivity
  have hb : s + mγ ^ 2 ≤ s + Λ ^ 2 := by nlinarith
  linarith [one_div_le_one_div_of_le ha hb]

/-- The photon function is continuous on `(0, ∞)`. -/
theorem continuousOn_chainSpec {P : Params} (hmass : ∀ f, P.mass f ≠ 0) (hmγ : 0 < P.mγ) :
    ContinuousOn (chainSpec P) (Ioi 0) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hJ : ∀ f, ContinuousAt (specJ (P.mass f)) t := fun f =>
    (continuousOn_specJ (hmass f)).continuousAt (Ioi_mem_nhds ht')
  have hD : ContinuousAt (photonD P.mγ P.Λ) t := by
    unfold photonD
    have h1 : t + P.mγ ^ 2 ≠ 0 := by positivity
    have h2 : t + P.Λ ^ 2 ≠ 0 := by positivity
    exact (continuousAt_const.div (continuousAt_id.add continuousAt_const) h1).sub
      (continuousAt_const.div (continuousAt_id.add continuousAt_const) h2)
  have hS : ContinuousAt (fun s => ∑ f, P.loopCoeff f * specJ (P.mass f) s) t := by
    simp only [Fin.sum_univ_three]
    exact ((continuousAt_const.mul (hJ 0)).add (continuousAt_const.mul (hJ 1))).add
      (continuousAt_const.mul (hJ 2))
  unfold chainSpec
  exact (((continuousAt_const.mul hS).pow 2).mul (continuousAt_id.pow 2)).mul (hD.pow 3)

theorem measurable_chainSpec (P : Params) : Measurable (chainSpec P) := by
  unfold chainSpec
  have hJ : ∀ f, Measurable (specJ (P.mass f)) := fun f => measurable_specJ _
  have hS : Measurable (fun s => ∑ f, P.loopCoeff f * specJ (P.mass f) s) :=
    Finset.measurable_sum _ fun f _ => (hJ f).const_mul _
  exact ((hS.const_mul _).pow_const 2).mul (measurable_id.pow_const 2) |>.mul
    ((measurable_photonD _ _).pow_const 3)

/-- The constant `A = ∑_f |c_f|/(15 M_f²)` of the small-`s` bound of the flavour sum. -/
noncomputable def specConst (P : Params) : ℝ := ∑ f, |P.loopCoeff f| / (15 * P.mass f ^ 2)

theorem abs_sum_specJ_le {P : Params} (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    |∑ f, P.loopCoeff f * specJ (P.mass f) s| ≤ specConst P * s := by
  unfold specConst
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [abs_mul, abs_of_nonneg (specJ_nonneg (hmass f) hs)]
  calc |P.loopCoeff f| * specJ (P.mass f) s ≤ |P.loopCoeff f| * (s / (15 * P.mass f ^ 2)) :=
        mul_le_mul_of_nonneg_left (specJ_le_div (hmass f) hs) (abs_nonneg _)
    _ = |P.loopCoeff f| / (15 * P.mass f ^ 2) * s := by ring

/-- **The photon function is bounded on `[0, ∞)`**: `|chainSpec P s| ≤ (e²/(4π²))² A² Λ²`. -/
theorem abs_chainSpec_le {P : Params} (hmass : ∀ f, P.mass f ≠ 0) (hmγ : 0 < P.mγ)
    (hmΛ : P.mγ ≤ P.Λ) {s : ℝ} (hs : 0 ≤ s) :
    |chainSpec P s| ≤ (P.e ^ 2 / (4 * π ^ 2)) ^ 2 * specConst P ^ 2 * P.Λ ^ 2 := by
  set S := ∑ f, P.loopCoeff f * specJ (P.mass f) s with hSdef
  set k := P.e ^ 2 / (4 * π ^ 2) with hk
  have hSb := abs_sum_specJ_le hmass hs
  rw [← hSdef] at hSb
  have hD := photonD_nonneg hmγ hmΛ hs
  obtain ⟨d0, d1⟩ := sq_sq_photonD_cube_le hmγ hmΛ hs
  have hS2 : S ^ 2 ≤ (specConst P * s) ^ 2 := by
    rw [← sq_abs S]
    exact pow_le_pow_left₀ (abs_nonneg S) hSb 2
  have hT : 0 ≤ s ^ 2 * photonD P.mγ P.Λ s ^ 3 := by positivity
  have e1 : chainSpec P s = k ^ 2 * S ^ 2 * (s ^ 2 * photonD P.mγ P.Λ s ^ 3) := by
    simp only [chainSpec, ← hSdef, ← hk]
    ring
  have h0 : 0 ≤ chainSpec P s := by rw [e1]; positivity
  rw [abs_of_nonneg h0, e1]
  calc k ^ 2 * S ^ 2 * (s ^ 2 * photonD P.mγ P.Λ s ^ 3)
      ≤ k ^ 2 * (specConst P * s) ^ 2 * (s ^ 2 * photonD P.mγ P.Λ s ^ 3) := by
        gcongr
    _ = k ^ 2 * specConst P ^ 2 * (s ^ 4 * photonD P.mγ P.Λ s ^ 3) := by ring
    _ ≤ k ^ 2 * specConst P ^ 2 * P.Λ ^ 2 := by gcongr

/-! ### The admissible parameters -/

theorem mass_ne_zero_of_admissible {P : Params} (hA : ChainAdmissible P) (f : Fin 3) :
    P.mass f ≠ 0 := by
  have hm := hA.hm
  have h1 : 0 < P.M₁ := hm.trans hA.hM₁
  have h2 : 0 < P.M₂ := hm.trans hA.hM₂
  fin_cases f
  · exact hm.ne'
  · exact h1.ne'
  · exact h2.ne'

theorem delta3_eq_of_admissible {P : Params} (hA : ChainAdmissible P) :
    P.δ₃ = vacuumPolarizationLoop P 0 :=
  (QED.TwoLoop.Scaling.isPhotonOnShell_iff P hA.hm hA.hM₁ hA.hM₂ hA.hPV₁ hA.hPV₂).1 hA.photon

/-- At admissible parameters, `outerAt m s` of the photon function is that of its spectral form,
for `s ≥ 0`. -/
theorem outerAt_chainPhoton_eq {P : Params} (hA : ChainAdmissible P) {s : ℝ} (hs : 0 ≤ s) :
    outerAt P.m s (chainPhoton P) = outerAt P.m s (chainSpec P) :=
  outerAt_congr hs fun _ ht =>
    chainPhoton_eq_chainSpec (mass_ne_zero_of_admissible hA) (delta3_eq_of_admissible hA) ht

/-- **The `q² → 0⁺` limit of the explicit set (b) functional at fixed regulators.** -/
theorem tendsto_outerAt_chainPhoton {P : Params} (hA : ChainAdmissible P) :
    Tendsto (fun s => outerAt P.m s (chainPhoton P)) (𝓝[>] 0)
      (𝓝 (outerAt P.m 0 (chainPhoton P))) := by
  have hmass := mass_ne_zero_of_admissible hA
  have hev : (fun s => outerAt P.m s (chainSpec P)) =ᶠ[𝓝[>] 0]
      fun s => outerAt P.m s (chainPhoton P) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact (outerAt_chainPhoton_eq hA hs.le).symm
  rw [outerAt_chainPhoton_eq hA le_rfl]
  exact (tendsto_outerAt hA.hm (measurable_chainSpec P) (continuousOn_chainSpec hmass hA.hmγ)
    fun _ ht => abs_chainSpec_le hmass hA.hmγ hA.hmγΛ.le ht).congr' hev

/-! ### The value at `q² = 0`, in units of `m` -/

/-- `specJ(M, m² t) = specJ(M/m, t)`. -/
theorem specJ_mul_sq {m : ℝ} (hm : m ≠ 0) (M t : ℝ) : specJ M (m ^ 2 * t) = specJ (M / m) t := by
  unfold specJ
  refine intervalIntegral.integral_congr fun v _ => ?_
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  congr 1
  have e1 : m ^ 2 * t + 4 * M ^ 2 / (1 - v ^ 2) =
      m ^ 2 * (t + 4 * (M / m) ^ 2 / (1 - v ^ 2)) := by
    field_simp
  rw [e1, mul_div_mul_left _ _ hm2]

/-- `D_{m_γ, Λ}(m² t) = D_{m_γ/m, Λ/m}(t)/m²`. -/
theorem photonD_mul_sq {m : ℝ} (hm : m ≠ 0) (mγ Λ t : ℝ) :
    photonD mγ Λ (m ^ 2 * t) = photonD (mγ / m) (Λ / m) t / m ^ 2 := by
  unfold photonD
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have e1 : m ^ 2 * t + mγ ^ 2 = m ^ 2 * (t + (mγ / m) ^ 2) := by field_simp
  have e2 : m ^ 2 * t + Λ ^ 2 = m ^ 2 * (t + (Λ / m) ^ 2) := by field_simp
  rw [e1, e2]
  field_simp

/-- The flavour sum at `m² t` is `jSum` in units of `m`, by the Pauli–Villars conditions. -/
theorem sum_specJ_mul_sq {P : Params} (hA : ChainAdmissible P) (t : ℝ) :
    ∑ f, P.loopCoeff f * specJ (P.mass f) (P.m ^ 2 * t) = jSum (P.M₁ / P.m) (P.M₂ / P.m) t := by
  have hm := hA.hm
  have hM₂ : 1 < P.M₂ / P.m := by rw [one_lt_div hm]; exact hA.hM₂
  have hPV₂ : 1 ^ 2 + P.c₁ * (P.M₁ / P.m) ^ 2 + P.c₂ * (P.M₂ / P.m) ^ 2 = 0 := by
    have h := hA.hPV₂
    have hm2 : P.m ^ 2 ≠ 0 := by positivity
    field_simp
    linarith
  rw [← sum_heavy_specJ hM₂ hA.hPV₁ hPV₂ t, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Params.loopCoeff, Params.mass, heavyCoeff, heavyMass, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    specJ_mul_sq hm.ne', div_self hm.ne']

/-- The spectral photon function at `m² t`, in units of `m`. -/
theorem chainSpec_mul_sq {P : Params} (hA : ChainAdmissible P) (t : ℝ) :
    chainSpec P (P.m ^ 2 * t) = (P.e ^ 2 / (4 * π ^ 2)) ^ 2 / P.m ^ 2 *
      (t ^ 2 * photonD (P.mγ / P.m) (P.Λ / P.m) t ^ 3 * jSum (P.M₁ / P.m) (P.M₂ / P.m) t ^ 2) := by
  have hm := hA.hm
  unfold chainSpec
  rw [sum_specJ_mul_sq hA, photonD_mul_sq hm.ne']
  field_simp

/-- **The value at `q² = 0` in units of the electron mass (O3-10 with the mass scaling).** At
admissible parameters, `e² outerAt m 0 (chainPhoton P) = e⁶ chainRegMass m m_γ Λ M₁ M₂/(64π⁶)`. -/
theorem outerAt_chainPhoton_zero {P : Params} (hA : ChainAdmissible P) :
    P.e ^ 2 * outerAt P.m 0 (chainPhoton P) =
      P.e ^ 6 * chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ / (64 * π ^ 6) := by
  have hm := hA.hm
  rw [outerAt_chainPhoton_eq hA le_rfl, outerAt_zero]
  have hpt : ∀ y ∈ uIcc (0 : ℝ) 1, y ^ 2 * chainSpec P (P.m ^ 2 * photonVar y) =
      (P.e ^ 2 / (4 * π ^ 2)) ^ 2 / P.m ^ 2 *
        (y ^ 2 * (photonVar y ^ 2 * photonD (P.mγ / P.m) (P.Λ / P.m) (photonVar y) ^ 3 *
          jSum (P.M₁ / P.m) (P.M₂ / P.m) (photonVar y) ^ 2)) := by
    intro y _
    rw [chainSpec_mul_sq hA]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  unfold chainRegMass
  rw [chainReg]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end QED.ChainProof.HCValue

end
