/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVPFubiniBoundOuter
public import QED.TwoLoop.NestedVPFubiniBoundInner
public import QED.TwoLoop.ClassIntegrableVP
import QED.Integration.LoopBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Fubini condition of nested-equals-joint for the vacuum-polarization class

Obligation O2-8 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3) for the class `VP` at fixed `ε > 0`:
the hypothesis `hG` of `QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested_energyFirst` is
proved, and with `hJ` (`QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_VP`) the
nested-equals-joint identity holds unconditionally.

For every spatial photon momentum `w`, the function
`(t, v⃗) ↦ ∫ dq⁰ nestedIntegrand(q = (q⁰, v⃗), k = (t, w))` is integrable on `ℝ × ℝ³`. Its value
is `∑ ρ σ, vpOuter(k) ρ σ · spatialG(k, v⃗) ρ σ` (packet 6b), and

* `‖vpOuter((t, w))‖ ≤ C (1 + |t|)⁻¹⁰` (`QED.TwoLoop.NestedVPFubiniBound.decaysLike_vpOuter`);
* `‖spatialG(k, v⃗)‖ ≤ C (1 + ‖k‖)^{17/2} (1 + ‖v⃗‖)^{-7/2}`
  (`QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly`);

so the integrand is dominated by `C (1 + |t|)^{-3/2} (1 + ‖v⃗‖)^{-7/2}`, integrable on `ℝ × ℝ³`.

## Main statements

* `QED.TwoLoop.NestedVPFubiniBound.integrable_nestedIntegrand_time`: **the condition `hG`**, for
  every `w`.
* `QED.TwoLoop.NestedVPFubiniBound.contractionValue₂_VP_eq_nested`: **nested equals joint for the
  class `VP` at fixed `ε > 0`**, under the mass and Pauli–Villars conditions and momentum
  conservation only.
* `QED.TwoLoop.NestedVPFubiniBound.contractionValue₂_VP_eq_onePIFunction`: the same with the
  frozen one-loop two-photon function inserted.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.TwoLoop.NestedVPFubiniBound

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop QED.TwoLoop.Enumeration

/-! ### Continuity of the outer factor in the photon energy -/

theorem denom_ne_zero (M : ℝ) {ε : ℝ} (hε : 0 < ε) (q : Fin 4 → ℝ) : denom M ε q ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [denom_im] at this
  simp only [Complex.zero_im, neg_eq_zero] at this
  exact hε.ne' this

theorem continuous_inv_denom (M : ℝ) {ε : ℝ} (hε : 0 < ε) {q : ℝ → Fin 4 → ℝ}
    (hq : Continuous q) : Continuous fun t => (denom M ε (q t))⁻¹ := by
  refine Continuous.inv₀ ?_ fun t => denom_ne_zero M hε (q t)
  unfold denom
  have := VertexLimit.continuous_dot_comp hq hq
  fun_prop

theorem continuous_lower : Continuous fun ℓ : Fin 4 → ℝ => Minkowski.lower ℓ := by
  simp only [Minkowski.lower_eq]
  refine continuous_pi fun κ => ?_
  fin_cases κ <;> simp <;> fun_prop

theorem continuous_slash {q : ℝ → Fin 4 → ℝ} (hq : Continuous q) :
    Continuous fun t => Dirac.slash (q t) := by
  unfold Dirac.slash
  refine continuous_finsetSum _ fun κ _ => ?_
  exact Continuous.smul (f := fun t => ((Minkowski.lower (q t) κ : ℝ) : ℂ))
    (g := fun _ => Dirac.gamma κ)
    (continuous_ofReal.comp ((continuous_apply κ).comp (continuous_lower.comp hq)))
    continuous_const

theorem continuous_electronPropagator (m : ℝ) {ε : ℝ} (hε : 0 < ε) {q : ℝ → Fin 4 → ℝ}
    (hq : Continuous q) : Continuous fun t => electronPropagator m ε (q t) :=
  (continuous_inv_denom m hε hq).smul (continuous_const.sub (continuous_slash hq))

theorem continuous_photonPropagator (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {q : ℝ → Fin 4 → ℝ}
    (hq : Continuous q) (ρ σ : Fin 4) : Continuous fun t => photonPropagator mγ Λ ε (q t) ρ σ :=
  continuous_const.mul ((continuous_inv_denom mγ hε hq).sub (continuous_inv_denom Λ hε hq))

/-- The outer factor is continuous in the photon energy, for `ε > 0`. -/
theorem continuous_vpOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (w : Fin 3 → ℝ)
    (α β μ ρ σ : Fin 4) :
    Continuous fun t => NestedVP.vpOuter P p kext (Fin.cons t w) α β μ ρ σ := by
  have hk : Continuous fun t : ℝ => (Fin.cons t w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_id continuous_const
  have hchain : ∀ μ' ρ' ν', Continuous fun t =>
      NestedVP.outerChain P p kext (Fin.cons t w) μ' ρ' ν' := fun μ' ρ' ν' => by
    unfold NestedVP.outerChain
    exact ((((continuous_const.matrix_mul (continuous_electronPropagator P.m hε
      (continuous_const.sub hk))).matrix_mul continuous_const).matrix_mul
        (continuous_electronPropagator P.m hε (continuous_const.sub hk))).matrix_mul
          continuous_const)
  unfold NestedVP.vpOuter
  refine continuous_const.mul (continuous_finsetSum _ fun l0 _ =>
    continuous_finsetSum _ fun l2 _ => ?_)
  refine ((((continuous_apply β).comp ((continuous_apply α).comp (hchain μ l0 l2))).mul
    (continuous_photonPropagator P.mγ P.Λ hε hk l0 ρ)).mul
      (continuous_photonPropagator P.mγ P.Λ hε hk.neg l2 σ))

/-! ### Integrability -/

/-- Joint measurability of the energy integral along `k = (t, w)`. -/
theorem aestronglyMeasurable_spatialG_cons (P : Params) (hε : 0 < P.ε) (w : Fin 3 → ℝ)
    (ρ σ : Fin 4) : AEStronglyMeasurable
      (fun x : ℝ × (Fin 3 → ℝ) => spatialG P P.ε (Fin.cons x.1 w) ρ σ x.2) volume := by
  have hc : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
      kappa P.e * timeSum P P.ε (Fin.cons z.1.1 w) ρ σ z.2 z.1.2 := by
    have hk : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ => (Fin.cons z.1.1 w : Fin 4 → ℝ) :=
      Continuous.finCons (A := fun _ : Fin 4 => ℝ) (continuous_fst.comp continuous_fst)
        continuous_const
    have h2 : Continuous fun z : (ℝ × (Fin 3 → ℝ)) × ℝ =>
        ((Fin.cons z.1.1 w : Fin 4 → ℝ), z.1.2, z.2) :=
      hk.prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have h3 := (continuous_timeSum_joint hε P ρ σ).comp h2
    exact continuous_const.mul h3
  exact (hc.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).aestronglyMeasurable

/-- `1 + ‖(t, w)‖ ≤ (1 + |t|) (1 + ‖w‖)`. -/
theorem one_add_norm_cons_le (t : ℝ) (w : Fin 3 → ℝ) :
    1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖ ≤ (1 + |t|) * (1 + ‖w‖) := by
  have h := QED.Integration.norm_finCons_le t w
  nlinarith [abs_nonneg t, norm_nonneg w, mul_nonneg (abs_nonneg t) (norm_nonneg w)]

/-- **One term of the Fubini condition is integrable**: at fixed `ε > 0` and spatial photon
momentum `w`, `(t, v⃗) ↦ vpOuter((t, w)) ρ σ · spatialG((t, w), v⃗) ρ σ` is integrable. -/
theorem integrable_vpOuter_mul_spatialG {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      NestedVP.vpOuter P p kext (Fin.cons x.1 w) α β μ ρ σ *
        spatialG P P.ε (Fin.cons x.1 w) ρ σ x.2 := by
  obtain ⟨Co, hCo⟩ := decaysLike_vpOuter P hε p kext w α β μ ρ σ
  have hCo0 := DecaysLike.const_nonneg hCo
  obtain ⟨Ci, hCi0, hCi⟩ := exists_norm_spatialG_le_poly hm hM₁ hM₂ hPV₁ hPV₂ hε ρ σ
  set K := Co * Ci * (1 + ‖w‖) ^ (17 / 2 : ℝ)
  have hint : Integrable (fun x : ℝ × (Fin 3 → ℝ) =>
      K * ((1 + ‖x.1‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖x.2‖) ^ (-(7 / 2 : ℝ)))) := by
    refine Integrable.const_mul ?_ K
    exact (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)).mul_prod
      (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2) (by simp; norm_num))
  refine hint.mono' (((continuous_vpOuter P hε p kext w α β μ ρ σ).comp
    continuous_fst).aestronglyMeasurable.mul (aestronglyMeasurable_spatialG_cons P hε w ρ σ))
    (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨t, v⟩ := x
  simp only
  rw [norm_mul, Real.norm_eq_abs]
  have ht0 : 0 < 1 + |t| := one_add_abs_pos t
  have hw0 : 0 < 1 + ‖w‖ := by positivity
  have hv0 : 0 < 1 + ‖v‖ := by positivity
  have h1 := hCo t
  have h2 := hCi (Fin.cons t w) v
  have hk : (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ)
      ≤ (1 + |t|) ^ (17 / 2 : ℝ) * (1 + ‖w‖) ^ (17 / 2 : ℝ) := by
    rw [← Real.mul_rpow ht0.le hw0.le]
    exact Real.rpow_le_rpow (by positivity) (one_add_norm_cons_le t w) (by norm_num)
  have hz : (1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ (17 / 2 : ℝ) = (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add ht0]
    norm_num
  calc ‖NestedVP.vpOuter P p kext (Fin.cons t w) α β μ ρ σ‖ *
        ‖spatialG P P.ε (Fin.cons t w) ρ σ v‖
      ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
          (Ci * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
          (Ci * ((1 + |t|) ^ (17 / 2 : ℝ) * (1 + ‖w‖) ^ (17 / 2 : ℝ)) *
            (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by gcongr
    _ = K * (((1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ (17 / 2 : ℝ)) *
          (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by ring
    _ = K * ((1 + |t|) ^ (-(3 / 2 : ℝ)) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by rw [hz]

/-- **The Fubini condition `hG` of nested-equals-joint for `VP`** (O2-8), at fixed `ε > 0`, for
every spatial photon momentum `w`: the energy integral over `q⁰` of the nested integrand at
`q = (q⁰, v⃗)`, `k = (t, w)` is integrable in `(t, v⃗)`. -/
theorem integrable_nestedIntegrand_time {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, NestedVP.nestedIntegrand P p kext α β μ ![Fin.cons t₁ x.2, Fin.cons x.1 w] := by
  have e : (fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, NestedVP.nestedIntegrand P p kext α β μ ![Fin.cons t₁ x.2, Fin.cons x.1 w]) =
      fun x => ∑ ρ : Fin 4, ∑ σ : Fin 4, NestedVP.vpOuter P p kext (Fin.cons x.1 w) α β μ ρ σ *
        spatialG P P.ε (Fin.cons x.1 w) ρ σ x.2 := by
    funext x
    rw [NestedVP.integral_nestedIntegrand_time P hε]
    simp only [integral_vacuumPolarizationIntegrand_time hε]
  rw [e]
  exact integrable_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ =>
    integrable_vpOuter_mul_spatialG hm hM₁ hM₂ hPV₁ hPV₂ hε p kext α β μ w ρ σ

/-! ### Nested equals joint, unconditionally at fixed `ε` -/

/-- **Nested equals joint for the vacuum-polarization class** (O2-8, at fixed `ε > 0`), with
both integrability hypotheses proved: under momentum conservation, `m > 0`, `M_f > m` and the
Pauli–Villars conditions, the value (T₁₀) of the class `VP` is the energy-first integral (D) over
the photon momentum `k` of `∑ ρ σ, vpOuter … k ρ σ * Π^{ρσ}_ε(k)`, with `Π^{ρσ}_ε(k)` the
energy-first integral (D) of the one-loop vacuum polarization integrand at the same `ε`. -/
theorem contractionValue₂_VP_eq_nested (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, NestedVP.vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          QED.OneLoop.energyFirstIntegral fun q =>
            QED.WickModel.vacuumPolarizationIntegrand P P.ε k q ρ σ :=
  ClassIntegrable.contractionValue₂_VP_eq_nested_energyFirst_of_hG P hmom αOut βIn μ hm hM₁ hM₂
    hPV₁ hPV₂ hε (Filter.Eventually.of_forall fun w =>
      integrable_nestedIntegrand_time hm hM₁ hM₂ hPV₁ hPV₂ hε (pIn 0) (kIn 0) (αOut 0) (βIn 0)
        (μ 0) w)

/-- **Nested equals joint, with the frozen one-loop vacuum polarization inserted**, at fixed
`ε > 0` and with no integrability hypothesis: `Π^{ρσ}_ε(k)` is the frozen one-loop 1PI function
with two external photons of momenta `k`, `-k` at order `≤ 2` (X₂₈), minus its counterterm tree. -/
theorem contractionValue₂_VP_eq_onePIFunction (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, NestedVP.vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          (onePIFunction P 0 2 2 ![] ![] ![k, -k] ![] ![] ![ρ, σ] +
            I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric ρ σ - k ρ * k σ) : ℝ) : ℂ)) :=
  NestedVP.contractionValue₂_VP_eq_onePIFunction P hmom αOut βIn μ hm hM₁ hM₂ hPV₁ hPV₂ hε
    (ClassIntegrable.jointEnergyFirstIntegrable_VP P hε hPV₁ hPV₂ hmom αOut βIn μ)
    (Filter.Eventually.of_forall fun w =>
      integrable_nestedIntegrand_time hm hM₁ hM₂ hPV₁ hPV₂ hε (pIn 0) (kIn 0) (αOut 0) (βIn 0)
        (μ 0) w)

end QED.TwoLoop.NestedVPFubiniBound

end
