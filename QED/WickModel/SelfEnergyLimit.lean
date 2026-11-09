/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.SelfEnergyEnergyFirst
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.OneLoop.VertexSpatial
import QED.Integration.ParametricSmooth
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop self-energy: limit and covariant form

The loop term of the one-loop self-energy is the energy-first integral (prescription M1,
decision D-5) of `QED.WickModel.selfEnergyIntegrand`, the integrand of `i Σ(p̸)` in the primary
source's (62.28), with the Pauli–Villars photon. This module proves that its limit `ε → 0⁺`
exists below threshold and has the covariant form `i (A(p²) p̸ + B(p²) m)`, with `A` and `B`
explicit Feynman-parameter integrals that are smooth in `s = p²`.

Write `D_M(s, x) = x m² + (1 - x) M² + x (1 - x) s` (`QED.WickModel.selfEnergyFeynmanMass`) and
`L(s, x) = log (D_Λ(s, x) / D_{m_γ}(s, x))`. Then
`A(s) = -(e² / 8π²) ∫₀¹ (1 - x) L(s, x) dx` and `B(s) = -(e² / 4π²) ∫₀¹ L(s, x) dx`.
This is the Pauli–Villars form of the source's (62.29)–(62.33): the dimensionally regulated
`2/ε - log D` is replaced by the paired logarithm `log(D_Λ / D_{m_γ})`.

The domain is `s > -(m + m_γ)²` and `s > -(m + Λ)²`, below both thresholds, where both Feynman
masses are positive on `[0, 1]` (`QED.WickModel.selfEnergyFeynmanMass_pos`). When
`m_γ ≤ Λ` the second condition follows from the first.

## Main definitions

* `QED.WickModel.selfEnergyLoopA`, `QED.WickModel.selfEnergyLoopB`: the coefficients `A` and `B`.

## Main statements

* `QED.WickModel.tendsto_energyFirstIntegral_selfEnergyIntegrand`: the limit `ε → 0⁺` of the
  energy-first integral of each entry of the integrand is the entry of
  `i (A(p²) p̸ + B(p²) m)`.
* `QED.WickModel.contDiffOn_selfEnergyLoopA` and `QED.WickModel.contDiffOn_selfEnergyLoopB`:
  `A` and `B` are `C^∞` below both thresholds.
* The variants with suffix `_of_le` assume `m_γ ≤ Λ` and only the photon-mass threshold.

## Proof

The limit is `∫ v, spatialG 0 v`
(`QED.WickModel.SelfEnergyLimit.tendsto_energyFirstIntegral_selfEnergyIntegrand_spatialG`). At
`ε = 0` the spatial integral is swapped with the Feynman-parameter integral
(`integral_spatialG_zero_eq`). At fixed `x`, translating the spatial momentum by `x p⃗` and
symmetrizing under `v⃗ ↦ -v⃗` removes the part of the numerator linear in `v⃗`; the remaining
radial integral is the Pauli–Villars-paired logarithm `2π log(D_Λ / D_{m_γ})`
(`integral_timeT_zero_sub`). The numerator at the shifted momentum is `-4m - 2(1 - x) p̸`.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real ContDiff

namespace QED.WickModel

/-- The coefficient `A(s)` of `p̸` in the one-loop self-energy `Σ(p̸) = A(p²) p̸ + B(p²) m`, with
the Pauli–Villars photon:
`A(s) = -(e² / 8π²) ∫₀¹ (1 - x) log (D_Λ(s, x) / D_{m_γ}(s, x)) dx`, where
`D_M(s, x) = x m² + (1 - x) M² + x (1 - x) s`. It is real-valued. -/
noncomputable def selfEnergyLoopA (P : Params) (s : ℝ) : ℂ :=
  ((-(P.e ^ 2 / (8 * π ^ 2)) * ∫ x in (0 : ℝ)..1, (1 - x) *
      Real.log (selfEnergyFeynmanMass P.m P.Λ s x / selfEnergyFeynmanMass P.m P.mγ s x) : ℝ) : ℂ)

/-- The coefficient `B(s)` of `m` in the one-loop self-energy `Σ(p̸) = A(p²) p̸ + B(p²) m`, with
the Pauli–Villars photon:
`B(s) = -(e² / 4π²) ∫₀¹ log (D_Λ(s, x) / D_{m_γ}(s, x)) dx`, where
`D_M(s, x) = x m² + (1 - x) M² + x (1 - x) s`. It is real-valued. -/
noncomputable def selfEnergyLoopB (P : Params) (s : ℝ) : ℂ :=
  ((-(P.e ^ 2 / (4 * π ^ 2)) * ∫ x in (0 : ℝ)..1,
      Real.log (selfEnergyFeynmanMass P.m P.Λ s x / selfEnergyFeynmanMass P.m P.mγ s x) : ℝ) : ℂ)

namespace SelfEnergyLimit

/-! ### The boundary value at `ε = 0` -/

/-- The uniform Pauli–Villars bound persists at `ε = 0`. -/
theorem norm_timeT_zero_sub_le {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p : Fin 4 → ℝ} (hpγ : -(m + mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(m + Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    ∃ Cb : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeT m mγ 0 p i j x v - timeT m Λ 0 p i j x v‖ ≤ Cb * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  obtain ⟨Cb, -, hCb⟩ := norm_timeT_sub_le hm hmγ hΛ hpγ hpΛ i j
  refine ⟨Cb, fun x hx v => ?_⟩
  have hlim := ((tendsto_timeT i j (massW_pos hm hmγ hpγ hx v)).sub
    (tendsto_timeT i j (massW_pos hm hΛ hpΛ hx v))).norm
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hCb ε hε x hx v)

/-- The closed-form energy integral is measurable along continuous parameters. -/
theorem measurable_timeT_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (m M ε : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) {fx : X → ℝ}
    {fv : X → Fin 3 → ℝ} (hx : Continuous fx) (hv : Continuous fv) :
    Measurable fun q => timeT m M ε p i j (fx q) (fv q) := by
  have hW : Continuous fun q => massW m M p (fx q) (fv q) := by
    simp only [massW, selfEnergyFeynmanMass, Fin.sum_univ_three]
    fun_prop
  have hX : Measurable fun q => (-(massW m M p (fx q) (fv q) : ℂ) + ε * I) :=
    (Complex.measurable_ofReal.comp hW.measurable).neg.add_const _
  have hN : Continuous fun q => numer m p (Fin.cons (-(fx q * p 0)) (fv q) : Fin 4 → ℝ) i j :=
    (continuous_numer m p i j).comp
      (Continuous.finCons (A := fun _ : Fin 4 => ℝ) (by fun_prop) hv)
  unfold timeT
  exact (measurable_const.mul hN.measurable).mul (hX.pow_const _)

/-- The closed-form energy integral is jointly measurable in `(v⃗, x)`. -/
theorem measurable_timeT (m M ε : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) :
    Measurable fun q : (Fin 3 → ℝ) × ℝ => timeT m M ε p i j q.2 q.1 :=
  measurable_timeT_comp m M ε p i j continuous_snd continuous_fst

/-- The closed-form energy integral at `ε = 0`, with the phase made explicit. -/
theorem timeT_zero_eq {m M : ℝ} {p : Fin 4 → ℝ} (i j : Fin 4) {x : ℝ} {v : Fin 3 → ℝ}
    (hW : 0 < massW m M p x v) :
    timeT m M 0 p i j x v =
      I * (π / 2 : ℂ) * numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j
        * ((massW m M p x v ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp only [timeT, ofReal_zero, zero_mul, add_zero]
  rw [VertexLimit.neg_ofReal_cpow_neg_three_halves hW]
  ring

/-- Translating the spatial momentum by `x p⃗` removes the shift in the mass term. -/
theorem massW_sub (m M : ℝ) (p : Fin 4 → ℝ) (x : ℝ) (w : Fin 3 → ℝ) :
    massW m M p x (w - fun k => x * p k.succ)
      = ∑ k, w k ^ 2 + selfEnergyFeynmanMass m M (Minkowski.dot p p) x := by
  simp only [massW, Pi.sub_apply, sub_add_cancel]

/-- `(-x p⁰, w⃗ - x p⃗) = (0, w⃗) - x p`. -/
theorem cons_neg_sub_eq (p : Fin 4 → ℝ) (x : ℝ) (w : Fin 3 → ℝ) :
    (Fin.cons (-(x * p 0)) (w - fun k => x * p k.succ) : Fin 4 → ℝ) = Fin.cons 0 w - x • p := by
  funext q
  refine Fin.cases ?_ (fun k => ?_) q <;> simp

/-- At `ε = 0`, after translating the spatial momentum by `x p⃗`. -/
theorem timeT_zero_shift {m M : ℝ} {p : Fin 4 → ℝ} (i j : Fin 4) {x : ℝ}
    (hD : 0 < selfEnergyFeynmanMass m M (Minkowski.dot p p) x) (w : Fin 3 → ℝ) :
    timeT m M 0 p i j x (w - fun k => x * p k.succ) =
      I * (π / 2 : ℂ) * numer m p (Fin.cons 0 w - x • p : Fin 4 → ℝ) i j *
        (((∑ k, w k ^ 2 + selfEnergyFeynmanMass m M (Minkowski.dot p p) x) ^ (-(3 / 2 : ℝ)) : ℝ)
          : ℂ) := by
  have hW : 0 < massW m M p x (w - fun k => x * p k.succ) := by
    rw [massW_sub]
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (w k)
    linarith
  rw [timeT_zero_eq i j hW, massW_sub, cons_neg_sub_eq]

/-- `(-a)̸ = -a̸`. -/
theorem slash_neg (a : Fin 4 → ℝ) : Dirac.slash (-a) = -Dirac.slash a := by
  rw [← neg_one_smul ℝ a, Dirac.slash_smul]
  simp

/-- The numerator at opposite spatial momenta averages to its value at `-x p`. -/
theorem numer_add_numer_neg (m : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) (x : ℝ) (w : Fin 3 → ℝ) :
    numer m p (Fin.cons 0 w - x • p : Fin 4 → ℝ) i j
        + numer m p (Fin.cons 0 (-w) - x • p : Fin 4 → ℝ) i j
      = 2 * numer m p (-(x • p)) i j := by
  have hneg : (Fin.cons 0 (-w) : Fin 4 → ℝ) = -(Fin.cons 0 w : Fin 4 → ℝ) := by
    funext q
    refine Fin.cases ?_ (fun k => ?_) q <;> simp
  have h1 : (Fin.cons 0 w - x • p : Fin 4 → ℝ) = -(x • p) + Fin.cons 0 w := by abel
  have h2 : (-(Fin.cons 0 w : Fin 4 → ℝ) - x • p) = -(x • p) + -(Fin.cons 0 w : Fin 4 → ℝ) := by
    abel
  rw [hneg, h1, h2, numer_add, numer_add, slash_neg, Matrix.neg_apply]
  ring

/-- Symmetrization: if `f(v - b) + f(-v - b) = h(v)`, then `∫ f = (1/2) ∫ h`. -/
theorem integral_eq_half_integral_of_add_neg {f h : (Fin 3 → ℝ) → ℂ} (hf : Integrable f)
    (b : Fin 3 → ℝ) (hfh : ∀ v, f (v - b) + f (-v - b) = h v) :
    ∫ v, f v = (1 / 2 : ℂ) * ∫ v, h v := by
  have h1 : ∫ v, f (v - b) = ∫ v, f v := integral_sub_right_eq_self f b
  have h2 : ∫ v, f (-v - b) = ∫ v, f (v - b) :=
    integral_neg_eq_self (fun v => f (v - b)) volume
  have hg : Integrable fun v => f (v - b) := hf.comp_sub_right b
  have hg' : Integrable fun v => f (-v - b) := hg.comp_neg
  have h3 : ∫ v, h v = (∫ v, f (v - b)) + ∫ v, f (-v - b) := by
    rw [← integral_add hg hg']
    exact integral_congr_ae (Eventually.of_forall fun v => (hfh v).symm)
  rw [h3, h2, h1]
  ring

/-- **The spatial integral at fixed Feynman parameter.** At `ε = 0`,
`∫ d³v (T_γ - T_Λ) = i π² log(D_Λ / D_γ) N(-x p)`, with `N(-x p) = -4m - 2(1 - x) p̸`. -/
theorem integral_timeT_zero_sub {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p : Fin 4 → ℝ} (hpγ : -(m + mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(m + Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫ v : Fin 3 → ℝ, (timeT m mγ 0 p i j x v - timeT m Λ 0 p i j x v) =
      I * ((π ^ 2 * Real.log (selfEnergyFeynmanMass m Λ (Minkowski.dot p p) x
          / selfEnergyFeynmanMass m mγ (Minkowski.dot p p) x) : ℝ) : ℂ)
        * numer m p (-(x • p)) i j := by
  have hDγ := selfEnergyFeynmanMass_pos hm hmγ hpγ hx
  have hDΛ := selfEnergyFeynmanMass_pos hm hΛ hpΛ hx
  obtain ⟨Cb, hCb⟩ := norm_timeT_zero_sub_le hm hmγ hΛ hpγ hpΛ i j
  have hf : Integrable fun v : Fin 3 → ℝ => timeT m mγ 0 p i j x v - timeT m Λ 0 p i j x v := by
    have hmeas : Measurable fun v : Fin 3 → ℝ =>
        timeT m mγ 0 p i j x v - timeT m Λ 0 p i j x v :=
      (measurable_timeT_comp m mγ 0 p i j continuous_const continuous_id).sub
        (measurable_timeT_comp m Λ 0 p i j continuous_const continuous_id)
    exact ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4)
      (by simp; norm_num)).const_mul Cb).mono' hmeas.aestronglyMeasurable
        (Eventually.of_forall fun v => hCb x hx v)
  rw [integral_eq_half_integral_of_add_neg hf (fun k => x * p k.succ)
    (h := fun v => I * (π : ℂ) * numer m p (-(x • p)) i j *
      (VertexLimit.pairedRpow32 (selfEnergyFeynmanMass m mγ (Minkowski.dot p p) x)
        (selfEnergyFeynmanMass m Λ (Minkowski.dot p p) x) (∑ k, v k ^ 2) : ℂ))]
  · rw [integral_const_mul, integral_complex_ofReal, VertexLimit.integral_pairedRpow32 hDγ hDΛ]
    push_cast
    ring
  · intro v
    have hsq : ∑ k, (-v) k ^ 2 = ∑ k, v k ^ 2 := by simp
    rw [timeT_zero_shift i j hDγ, timeT_zero_shift i j hDΛ, timeT_zero_shift i j hDγ,
      timeT_zero_shift i j hDΛ, hsq, VertexLimit.pairedRpow32]
    have hN := numer_add_numer_neg m p i j x v
    push_cast
    linear_combination (I * (π / 2 : ℂ) *
      ((((∑ k, v k ^ 2 + selfEnergyFeynmanMass m mγ (Minkowski.dot p p) x) ^ (-(3 / 2 : ℝ)) : ℝ)
        : ℂ) - (((∑ k, v k ^ 2 + selfEnergyFeynmanMass m Λ (Minkowski.dot p p) x) ^
          (-(3 / 2 : ℝ)) : ℝ) : ℂ))) * hN

/-- At `ε = 0`, the spatial integral and the Feynman-parameter integral can be swapped. -/
theorem integral_spatialG_zero_eq {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ} (hpγ : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(P.m + P.Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    ∫ v, spatialG P 0 p i j v = ∫ x in Ioc (0 : ℝ) 1, kappa P.e *
      ∫ v, (timeT P.m P.mγ 0 p i j x v - timeT P.m P.Λ 0 p i j x v) := by
  obtain ⟨Cb, hCb⟩ := norm_timeT_zero_sub_le hm hmγ hΛ hpγ hpΛ i j
  set F : (Fin 3 → ℝ) → ℝ → ℂ := fun v x => kappa P.e *
    (timeT P.m P.mγ 0 p i j x v - timeT P.m P.Λ 0 p i j x v) with hF
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hg := ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4)
      (by simp; norm_num)).const_mul (‖kappa P.e‖ * Cb)).mul_prod
        (integrable_const (μ := volume.restrict (Ioc (0 : ℝ) 1)) (1 : ℝ))
    refine Integrable.mono' hg ?_ ((ae_prod_restrict_Ioc _).mono fun q hq => ?_)
    · exact (measurable_const.mul ((measurable_timeT _ _ 0 p i j).sub
        (measurable_timeT _ _ 0 p i j))).aestronglyMeasurable
    · obtain ⟨v, x⟩ := q
      simp only [Function.uncurry_apply_pair, hF, mul_one] at hq ⊢
      rw [norm_mul]
      calc ‖kappa P.e‖ * ‖timeT P.m P.mγ 0 p i j x v - timeT P.m P.Λ 0 p i j x v‖
          ≤ ‖kappa P.e‖ * (Cb * (1 + ‖v‖) ^ (-(4 : ℝ))) := by
            gcongr
            exact hCb x (Ioc_subset_Icc_self hq) v
        _ = ‖kappa P.e‖ * Cb * (1 + ‖v‖) ^ (-(4 : ℝ)) := by ring
  have hG : ∀ v, spatialG P 0 p i j v = ∫ x in Ioc (0 : ℝ) 1, F v x := fun v => rfl
  simp_rw [hG]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF]
  rw [integral_const_mul]

/-! ### Assembly -/

/-- The overall constant is `(ie)² (1/i)² (2π)⁻⁴ = e² / (16 π⁴)`. -/
theorem kappa_eq (e : ℝ) : kappa e = ((e ^ 2 / (16 * π ^ 4) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [kappa]
  push_cast
  field_simp
  ring_nf

/-- The numerator at the shifted loop momentum `-x p` is `-4m - 2(1 - x) p̸`. -/
theorem numer_neg_smul (m : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) (x : ℝ) :
    numer m p (-(x • p)) i j
      = -(4 * (m : ℂ)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j
        - 2 * (((1 - x : ℝ) : ℂ) * Dirac.slash p i j) := by
  have h : p + -(x • p) = (1 - x) • p := by
    rw [sub_smul, one_smul, sub_eq_add_neg]
  simp only [numer, h, Dirac.slash_smul, Matrix.smul_apply, smul_eq_mul]

/-- Below threshold the Feynman-parameter logarithm is continuous on `[0, 1]`. -/
theorem continuousOn_log_div {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {s : ℝ} (hsγ : -(P.m + P.mγ) ^ 2 < s) (hsΛ : -(P.m + P.Λ) ^ 2 < s) :
    ContinuousOn (fun x => Real.log (selfEnergyFeynmanMass P.m P.Λ s x
      / selfEnergyFeynmanMass P.m P.mγ s x)) (Icc (0 : ℝ) 1) :=
  ((continuous_selfEnergyFeynmanMass _ _ _).continuousOn.div
    (continuous_selfEnergyFeynmanMass _ _ _).continuousOn
    fun _ hx => (selfEnergyFeynmanMass_pos hm hmγ hsγ hx).ne').log
    fun _ hx => (div_pos (selfEnergyFeynmanMass_pos hm hΛ hsΛ hx)
      (selfEnergyFeynmanMass_pos hm hmγ hsγ hx)).ne'

/-- The limit `∫ v, spatialG 0 v` is the entry of `i (A(p²) p̸ + B(p²) m)`. -/
theorem integral_spatialG_zero_eq_loop {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ} (hpγ : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(P.m + P.Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    ∫ v, spatialG P 0 p i j v =
      I * ((selfEnergyLoopA P (Minkowski.dot p p)) • Dirac.slash p
        + (selfEnergyLoopB P (Minkowski.dot p p) * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j := by
  rw [integral_spatialG_zero_eq hm hmγ hΛ hpγ hpΛ i j]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun x => Real.log
      (selfEnergyFeynmanMass P.m P.Λ (Minkowski.dot p p) x
        / selfEnergyFeynmanMass P.m P.mγ (Minkowski.dot p p) x) := ⟨_, rfl⟩
  have hLc : ContinuousOn L (Icc (0 : ℝ) 1) := by
    rw [hL]
    exact continuousOn_log_div hm hmγ hΛ hpγ hpΛ
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℂ, c = I * ((-(P.e ^ 2 / (4 * π ^ 2)) : ℝ) : ℂ) * P.m *
      (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℂ, c = I * ((-(P.e ^ 2 / (8 * π ^ 2)) : ℝ) : ℂ) *
      Dirac.slash p i j := ⟨_, rfl⟩
  have jL : Integrable (fun x => c₁ * (L x : ℂ)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Integrable.ofReal ((hLc.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self)).const_mul c₁
  have jL1 : Integrable (fun x => c₂ * (((1 - x) * L x : ℝ) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Integrable.ofReal (((ContinuousOn.mul (by fun_prop) hLc).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self)).const_mul c₂
  have hpt : ∀ x ∈ Ioc (0 : ℝ) 1, kappa P.e *
      ∫ v, (timeT P.m P.mγ 0 p i j x v - timeT P.m P.Λ 0 p i j x v)
        = c₁ * (L x : ℂ) + c₂ * (((1 - x) * L x : ℝ) : ℂ) := by
    intro x hx
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [integral_timeT_zero_sub hm hmγ hΛ hpγ hpΛ i j (Ioc_subset_Icc_self hx), kappa_eq,
      numer_neg_smul, hc₁, hc₂, hL]
    push_cast
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add jL jL1, integral_const_mul,
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  simp only [selfEnergyLoopA, selfEnergyLoopB, intervalIntegral.integral_of_le zero_le_one, hc₁,
    hc₂, hL]
  push_cast
  ring

end SelfEnergyLimit

/-! ### The main statements -/

/-- **The one-loop self-energy below threshold.** For `m, m_γ, Λ > 0` and `p² > -(m + m_γ)²`,
`p² > -(m + Λ)²`, the energy-first integral of each entry of the integrand of `i Σ(p̸)` in (62.28)
converges, as `ε → 0⁺`, to the entry of `i (A(p²) p̸ + B(p²) m)`, with `A = selfEnergyLoopA` and
`B = selfEnergyLoopB`. -/
theorem tendsto_energyFirstIntegral_selfEnergyIntegrand {P : Params} (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ}
    (hpγ : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p) (hpΛ : -(P.m + P.Λ) ^ 2 < Minkowski.dot p p)
    (i j : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun ℓ => selfEnergyIntegrand P ε p ℓ i j)
      (𝓝[>] 0) (𝓝 (I * ((selfEnergyLoopA P (Minkowski.dot p p)) • Dirac.slash p
        + (selfEnergyLoopB P (Minkowski.dot p p) * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
          i j)) := by
  have h := SelfEnergyLimit.tendsto_energyFirstIntegral_selfEnergyIntegrand_spatialG hm hmγ hΛ
    hpγ hpΛ i j
  rwa [SelfEnergyLimit.integral_spatialG_zero_eq_loop hm hmγ hΛ hpγ hpΛ i j] at h

/-- For `m_γ ≤ Λ`, `-(m + Λ)² ≤ -(m + m_γ)²`. -/
theorem SelfEnergyLimit.neg_sq_add_le_of_le {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hmγΛ : mγ ≤ Λ) :
    -(m + Λ) ^ 2 ≤ -(m + mγ) ^ 2 :=
  neg_le_neg (pow_le_pow_left₀ (by positivity) (by linarith) 2)

/-- **The one-loop self-energy below threshold**, for `m_γ ≤ Λ`: then `p² > -(m + m_γ)²`
suffices. -/
theorem tendsto_energyFirstIntegral_selfEnergyIntegrand_of_le {P : Params} (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hmγΛ : P.mγ ≤ P.Λ) {p : Fin 4 → ℝ}
    (hp : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun ℓ => selfEnergyIntegrand P ε p ℓ i j)
      (𝓝[>] 0) (𝓝 (I * ((selfEnergyLoopA P (Minkowski.dot p p)) • Dirac.slash p
        + (selfEnergyLoopB P (Minkowski.dot p p) * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j)) :=
  tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ hp
    ((SelfEnergyLimit.neg_sq_add_le_of_le hm hmγ hmγΛ).trans_lt hp) i j

/-! ### Smoothness in `s = p²` -/

namespace SelfEnergyLimit

/-- The Feynman mass term is a polynomial in `(s, x)`. -/
theorem contDiff_selfEnergyFeynmanMass (m M : ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => selfEnergyFeynmanMass m M q.1 q.2) := by
  unfold selfEnergyFeynmanMass
  fun_prop

/-- The open set of `(s, x)` where both Feynman masses are positive. -/
theorem isOpen_feynmanMass_pos (m mγ Λ : ℝ) :
    IsOpen {q : ℝ × ℝ | 0 < selfEnergyFeynmanMass m mγ q.1 q.2
      ∧ 0 < selfEnergyFeynmanMass m Λ q.1 q.2} :=
  (isOpen_lt continuous_const (contDiff_selfEnergyFeynmanMass m mγ).continuous).inter
    (isOpen_lt continuous_const (contDiff_selfEnergyFeynmanMass m Λ).continuous)

/-- Below both thresholds, both Feynman masses are positive on the closed unit interval. -/
theorem prod_Icc_subset_feynmanMass_pos {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    (Ioi (-(m + mγ) ^ 2) ∩ Ioi (-(m + Λ) ^ 2)) ×ˢ Icc (0 : ℝ) 1
      ⊆ {q : ℝ × ℝ | 0 < selfEnergyFeynmanMass m mγ q.1 q.2
        ∧ 0 < selfEnergyFeynmanMass m Λ q.1 q.2} :=
  fun _ hq => ⟨selfEnergyFeynmanMass_pos hm hmγ hq.1.1 hq.2,
    selfEnergyFeynmanMass_pos hm hΛ hq.1.2 hq.2⟩

/-- Smoothness of `s ↦ ∫₀¹ w(x) log (D_Λ(s, x) / D_{m_γ}(s, x)) dx` for a polynomial weight. -/
theorem contDiffOn_integral_mul_log {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiffOn ℝ ∞ (fun s => ∫ x in (0 : ℝ)..1, w x *
        Real.log (selfEnergyFeynmanMass m Λ s x / selfEnergyFeynmanMass m mγ s x))
      (Ioi (-(m + mγ) ^ 2) ∩ Ioi (-(m + Λ) ^ 2)) := by
  set W := {q : ℝ × ℝ | 0 < selfEnergyFeynmanMass m mγ q.1 q.2
    ∧ 0 < selfEnergyFeynmanMass m Λ q.1 q.2}
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => selfEnergyFeynmanMass m mγ q.1 q.2) W :=
    (contDiff_selfEnergyFeynmanMass m mγ).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => selfEnergyFeynmanMass m Λ q.1 q.2) W :=
    (contDiff_selfEnergyFeynmanMass m Λ).contDiffOn
  have hlog : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
      Real.log (selfEnergyFeynmanMass m Λ q.1 q.2 / selfEnergyFeynmanMass m mγ q.1 q.2)) W :=
    (h2.div h1 fun q hq => hq.1.ne').log fun q hq => (div_pos hq.2 hq.1).ne'
  have hw' : ContDiff ℝ ∞ (fun q : ℝ × ℝ => w q.2) := hw.comp contDiff_snd
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => w q.2 *
      Real.log (selfEnergyFeynmanMass m Λ q.1 q.2 / selfEnergyFeynmanMass m mγ q.1 q.2)) W :=
    hw'.contDiffOn.mul hlog
  have h := contDiffOn_integral_of_contDiffOn_prod (μ := volume.restrict (Ioc (0 : ℝ) 1))
    isCompact_Icc ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => Ioc_subset_Icc_self hx)
    (isOpen_Ioi.inter isOpen_Ioi) (isOpen_feynmanMass_pos m mγ Λ)
    (prod_Icc_subset_feynmanMass_pos hm hmγ hΛ) hg
  refine h.congr fun s _ => ?_
  simp only [intervalIntegral.integral_of_le zero_le_one]

/-- The complex coercion of a `C^∞` real function is `C^∞`. -/
theorem contDiffOn_ofReal {f : ℝ → ℝ} {U : Set ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun s => (f s : ℂ)) U :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

end SelfEnergyLimit

/-- **Smoothness of `A`.** For `m, m_γ, Λ > 0`, `selfEnergyLoopA` is `C^∞` in `s = p²` below
both thresholds. -/
theorem contDiffOn_selfEnergyLoopA {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) :
    ContDiffOn ℝ ∞ (selfEnergyLoopA P) (Ioi (-(P.m + P.mγ) ^ 2) ∩ Ioi (-(P.m + P.Λ) ^ 2)) :=
  SelfEnergyLimit.contDiffOn_ofReal (contDiffOn_const.mul
    (SelfEnergyLimit.contDiffOn_integral_mul_log hm hmγ hΛ (w := fun x => 1 - x)
      (by fun_prop)))

/-- **Smoothness of `B`.** For `m, m_γ, Λ > 0`, `selfEnergyLoopB` is `C^∞` in `s = p²` below
both thresholds. -/
theorem contDiffOn_selfEnergyLoopB {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) :
    ContDiffOn ℝ ∞ (selfEnergyLoopB P) (Ioi (-(P.m + P.mγ) ^ 2) ∩ Ioi (-(P.m + P.Λ) ^ 2)) := by
  have h := SelfEnergyLimit.contDiffOn_integral_mul_log hm hmγ hΛ (w := fun _ => 1)
    contDiff_const
  simp only [one_mul] at h
  exact SelfEnergyLimit.contDiffOn_ofReal (contDiffOn_const.mul h)

/-- For `m_γ ≤ Λ`, the photon-mass threshold is the binding one. -/
theorem SelfEnergyLimit.Ioi_inter_Ioi_eq_of_le {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hmγΛ : mγ ≤ Λ) :
    Ioi (-(m + mγ) ^ 2) ∩ Ioi (-(m + Λ) ^ 2) = Ioi (-(m + mγ) ^ 2) :=
  inter_eq_left.mpr (Ioi_subset_Ioi (SelfEnergyLimit.neg_sq_add_le_of_le hm hmγ hmγΛ))

/-- **Smoothness of `A`** for `m_γ ≤ Λ`, on `s > -(m + m_γ)²`. -/
theorem contDiffOn_selfEnergyLoopA_of_le {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hmγΛ : P.mγ ≤ P.Λ) :
    ContDiffOn ℝ ∞ (selfEnergyLoopA P) (Ioi (-(P.m + P.mγ) ^ 2)) := by
  rw [← SelfEnergyLimit.Ioi_inter_Ioi_eq_of_le hm hmγ hmγΛ]
  exact contDiffOn_selfEnergyLoopA hm hmγ hΛ

/-- **Smoothness of `B`** for `m_γ ≤ Λ`, on `s > -(m + m_γ)²`. -/
theorem contDiffOn_selfEnergyLoopB_of_le {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hmγΛ : P.mγ ≤ P.Λ) :
    ContDiffOn ℝ ∞ (selfEnergyLoopB P) (Ioi (-(P.m + P.mγ) ^ 2)) := by
  rw [← SelfEnergyLimit.Ioi_inter_Ioi_eq_of_le hm hmγ hmγΛ]
  exact contDiffOn_selfEnergyLoopB hm hmγ hΛ

end QED.WickModel

end
