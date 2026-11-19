/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCNestedFubini
public import QED.TwoLoop.NestedVPFubiniBound
public import QED.TwoLoop.VPHalfAtInner
import QED.Integration.LoopBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounds for the three-loop Fubini step of the set (b) chain

Helper level, Phase 5 Stage 1a, obligation O3-6 (`docs/HIGHER-LOOP-PLAN.md`), the inner-first
route of `QED.ChainProof.jointEnergyFirstIntegral_three_eq_nested_innerFirst`. This file collects
the analytic inputs, all at fixed `ε > 0`:

* **continuity** of the propagators and of the one-loop vacuum polarization integrand
  `vacuumPolarizationIntegrand P ε k q ρ σ` jointly in `(k, q)` (`continuous_vpIntegrand_comp`),
  and strong measurability of its energy integral (`stronglyMeasurable_vpTime`) and of its
  energy-first integral `Π_ε(k)` (`stronglyMeasurable_vpPi`);
* **the unintegrated bubble** (the new bound needed by the condition `hA`): with fixed spatial
  momenta `a` of the loop and `b` of the photon, the integrand at loop energy `t` and photon
  energy `τ` is at most `C (1 + |t + τ|)⁻¹ (1 + |t|)⁻¹ ≤ C (1 + |τ|) (1 + |t|)⁻²`
  (`exists_norm_vpIntegrand_cons_le`, `inv_one_add_abs_add_le`). No Pauli–Villars cancellation
  is used: each propagator decays like the inverse of its energy;
* **the integrated bubble** (needed by the condition `hB`): from the closed form of
  `QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`,
  `‖Π_ε^{ρσ}(k)‖ ≤ C (1 + ‖k‖)⁴` (`exists_norm_vpPi_le`). The crude bound
  `∫ d³v |spatialG(k, v)| ≤ C (1 + ‖k‖)^{17/2}` would not suffice;
* **the outer factor** of the bubble–bubble class: the open-line chain contracted with three
  regulated photon propagators (`chainOuter`), continuous for `ε > 0` (`continuous_chainOuter`)
  and decaying like `(1 + |t|)⁻¹⁴` in the photon energy (`decaysLike_chainOuter`): two electron
  propagators and three Pauli–Villars photon propagators.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.HCLimit

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos one_le_one_add_abs)

/-! ### Continuity -/

theorem continuous_slash_comp {X : Type*} [TopologicalSpace X] {q : X → Fin 4 → ℝ}
    (hq : Continuous q) : Continuous fun x => Dirac.slash (q x) := by
  unfold Dirac.slash
  refine continuous_finsetSum _ fun κ _ => ?_
  exact Continuous.smul (f := fun x => ((Minkowski.lower (q x) κ : ℝ) : ℂ))
    (g := fun _ => Dirac.gamma κ)
    (continuous_ofReal.comp ((continuous_apply κ).comp
      (QED.TwoLoop.NestedVPFubiniBound.continuous_lower.comp hq))) continuous_const

theorem continuous_inv_denom_comp (M : ℝ) {ε : ℝ} (hε : 0 < ε) {X : Type*} [TopologicalSpace X]
    {q : X → Fin 4 → ℝ} (hq : Continuous q) : Continuous fun x => (denom M ε (q x))⁻¹ := by
  refine Continuous.inv₀ ?_ fun x => QED.TwoLoop.NestedVPFubiniBound.denom_ne_zero M hε (q x)
  unfold denom
  have := QED.OneLoop.VertexLimit.continuous_dot_comp hq hq
  fun_prop

theorem continuous_electronPropagator_comp (M : ℝ) {ε : ℝ} (hε : 0 < ε) {X : Type*}
    [TopologicalSpace X] {q : X → Fin 4 → ℝ} (hq : Continuous q) :
    Continuous fun x => electronPropagator M ε (q x) :=
  (continuous_inv_denom_comp M hε hq).smul (continuous_const.sub (continuous_slash_comp hq))

theorem continuous_photonPropagator_comp (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {X : Type*}
    [TopologicalSpace X] {q : X → Fin 4 → ℝ} (hq : Continuous q) (ρ σ : Fin 4) :
    Continuous fun x => photonPropagator mγ Λ ε (q x) ρ σ :=
  continuous_const.mul ((continuous_inv_denom_comp mγ hε hq).sub
    (continuous_inv_denom_comp Λ hε hq))

/-- The one-loop vacuum polarization integrand is jointly continuous for `ε > 0`. -/
theorem continuous_vpIntegrand_comp (P : Params) {ε : ℝ} (hε : 0 < ε) {X : Type*}
    [TopologicalSpace X] {k q : X → Fin 4 → ℝ} (hk : Continuous k) (hq : Continuous q)
    (ρ σ : Fin 4) : Continuous fun x => vacuumPolarizationIntegrand P ε (k x) (q x) ρ σ := by
  unfold vacuumPolarizationIntegrand
  refine continuous_const.mul (continuous_finsetSum _ fun f _ => continuous_const.mul ?_)
  exact ((((continuous_electronPropagator_comp _ hε (hq.add hk)).matrix_mul
    continuous_const).matrix_mul (continuous_electronPropagator_comp _ hε hq)).matrix_mul
      continuous_const).matrix_trace

theorem continuous_cons_fst {X : Type*} [TopologicalSpace X] {t : X → ℝ} {v : X → Fin 3 → ℝ}
    (ht : Continuous t) (hv : Continuous v) : Continuous fun x => (Fin.cons (t x) (v x) : Fin 4 → ℝ) :=
  Continuous.finCons (A := fun _ : Fin 4 => ℝ) ht hv

/-- The energy integral of the vacuum polarization integrand is strongly measurable in the photon
momentum and the spatial loop momentum. -/
theorem stronglyMeasurable_vpTime (P : Params) {ε : ℝ} (hε : 0 < ε) (ρ σ : Fin 4) :
    StronglyMeasurable fun z : (Fin 4 → ℝ) × (Fin 3 → ℝ) =>
      ∫ t : ℝ, vacuumPolarizationIntegrand P ε z.1 (Fin.cons t z.2) ρ σ := by
  have hc : Continuous fun y : ((Fin 4 → ℝ) × (Fin 3 → ℝ)) × ℝ =>
      vacuumPolarizationIntegrand P ε y.1.1 (Fin.cons y.2 y.1.2) ρ σ :=
    continuous_vpIntegrand_comp P hε (continuous_fst.comp continuous_fst)
      (continuous_cons_fst continuous_snd (continuous_snd.comp continuous_fst)) ρ σ
  exact hc.stronglyMeasurable.integral_prod_right'

/-- The energy-first integral `Π_ε(k)` is strongly measurable in the photon momentum. -/
theorem stronglyMeasurable_vpPi (P : Params) {ε : ℝ} (hε : 0 < ε) (ρ σ : Fin 4) :
    StronglyMeasurable fun k : Fin 4 → ℝ =>
      energyFirstIntegral fun q => vacuumPolarizationIntegrand P ε k q ρ σ :=
  (stronglyMeasurable_vpTime P hε ρ σ).integral_prod_right'

/-! ### The unintegrated bubble -/

theorem cons_add_cons (t τ : ℝ) (a b : Fin 3 → ℝ) :
    (Fin.cons t a : Fin 4 → ℝ) + Fin.cons τ b = Fin.cons (t + τ) (a + b) := by
  funext i
  refine Fin.cases rfl (fun j => rfl) i

/-- `(1 + |t + τ|)⁻¹ ≤ (1 + |τ|) (1 + |t|)⁻¹`. -/
theorem inv_one_add_abs_add_le (t τ : ℝ) : (1 + |t + τ|)⁻¹ ≤ (1 + |τ|) * (1 + |t|)⁻¹ := by
  have ht : |t| ≤ |t + τ| + |τ| := by
    have := abs_add_le (t + τ) (-τ)
    rwa [add_neg_cancel_right, abs_neg] at this
  have h1 : (1 + |t|) / (1 + |τ|) ≤ 1 + |t + τ| := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg τ, abs_nonneg (t + τ), mul_nonneg (abs_nonneg τ) (abs_nonneg (t + τ))]
  calc (1 + |t + τ|)⁻¹ ≤ ((1 + |t|) / (1 + |τ|))⁻¹ := inv_anti₀ (by positivity) h1
    _ = (1 + |τ|) * (1 + |t|)⁻¹ := by rw [inv_div, div_eq_mul_inv]

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_norm_electronPropagator_cons_le (M : ℝ) {ε : ℝ} (hε : 0 < ε) (a : Fin 3 → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, ‖electronPropagator M ε (Fin.cons t a)‖ ≤ C * (1 + |t|)⁻¹ := by
  obtain ⟨C, hC⟩ := QED.TwoLoop.NestedVPFubiniBound.decaysLike_electronPropagator M hε
    (fun t => (Fin.cons t a : Fin 4 → ℝ)) le_rfl (norm_nonneg a) (fun t => by simp)
    (fun t i => by simp) (fun t => QED.Integration.norm_finCons_le t a)
  refine ⟨C, QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hC, fun t => ?_⟩
  simpa using hC t

theorem norm_trace_le (X : Matrix (Fin 4) (Fin 4) ℂ) : ‖Matrix.trace X‖ ≤ 4 * ‖X‖ := by
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Matrix.diag X i‖ ≤ ∑ _i : Fin 4, ‖X‖ :=
        Finset.sum_le_sum fun i _ => QED.TwoLoop.NestedVPFubiniBound.norm_apply_le_norm X i i
    _ = 4 * ‖X‖ := by simp

theorem norm_mul_four_le (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    ‖A * B * C * D‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ :=
  (norm_mul_le (A * B * C) D).trans
    (mul_le_mul_of_nonneg_right (norm_mul₃_le (a := A) (b := B) (c := C)) (norm_nonneg _))

/-- **The unintegrated bubble**: with fixed spatial momenta `a` (loop) and `b` (photon), the
vacuum polarization integrand at loop energy `t` and photon energy `τ` is bounded by
`C (1 + |t + τ|)⁻¹ (1 + |t|)⁻¹`, with `C` independent of `t` and `τ`. -/
theorem exists_norm_vpIntegrand_cons_le (P : Params) {ε : ℝ} (hε : 0 < ε) (a b : Fin 3 → ℝ)
    (ρ σ : Fin 4) : ∃ C, 0 ≤ C ∧ ∀ t τ : ℝ,
      ‖vacuumPolarizationIntegrand P ε (Fin.cons τ b) (Fin.cons t a) ρ σ‖ ≤
        C * ((1 + |t + τ|)⁻¹ * (1 + |t|)⁻¹) := by
  choose C1 hC1 hC1' using fun f : Fin 3 =>
    exists_norm_electronPropagator_cons_le (P.mass f) hε (a + b)
  choose C2 hC2 hC2' using fun f : Fin 3 => exists_norm_electronPropagator_cons_le (P.mass f) hε a
  set g := ‖Dirac.gamma ρ‖ * ‖Dirac.gamma σ‖
  have hg : 0 ≤ g := by positivity
  refine ⟨‖(-1) * (I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹‖ * ∑ f, ‖(P.loopCoeff f : ℂ)‖ * (4 * (C1 f * C2 f * g)), ?_, fun t τ => ?_⟩
  · exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun f _ =>
      mul_nonneg (norm_nonneg _) (by have := hC1 f; have := hC2 f; positivity))
  have hu1 : 0 ≤ (1 + |t + τ|)⁻¹ := by positivity
  have hu2 : 0 ≤ (1 + |t|)⁻¹ := by positivity
  have hterm : ∀ f : Fin 3, ‖(P.loopCoeff f : ℂ) *
      Matrix.trace (electronPropagator (P.mass f) ε (Fin.cons (t + τ) (a + b)) * Dirac.gamma ρ *
        electronPropagator (P.mass f) ε (Fin.cons t a) * Dirac.gamma σ)‖ ≤
      ‖(P.loopCoeff f : ℂ)‖ * (4 * (C1 f * C2 f * g)) * ((1 + |t + τ|)⁻¹ * (1 + |t|)⁻¹) := by
    intro f
    rw [norm_mul, mul_assoc ‖(P.loopCoeff f : ℂ)‖]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg ((P.loopCoeff f : ℂ)))
    refine (norm_trace_le _).trans ?_
    have h1 := hC1' f (t + τ)
    have h2 := hC2' f t
    have hm := norm_mul_four_le (electronPropagator (P.mass f) ε (Fin.cons (t + τ) (a + b)))
      (Dirac.gamma ρ) (electronPropagator (P.mass f) ε (Fin.cons t a)) (Dirac.gamma σ)
    have hb : ‖electronPropagator (P.mass f) ε (Fin.cons (t + τ) (a + b))‖ * ‖Dirac.gamma ρ‖ *
        ‖electronPropagator (P.mass f) ε (Fin.cons t a)‖ * ‖Dirac.gamma σ‖ ≤
        (C1 f * (1 + |t + τ|)⁻¹) * ‖Dirac.gamma ρ‖ * (C2 f * (1 + |t|)⁻¹) * ‖Dirac.gamma σ‖ := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right h1
        (norm_nonneg _)) h2 (norm_nonneg _) ?_) (norm_nonneg _)
      exact mul_nonneg (mul_nonneg (hC1 f) hu1) (norm_nonneg _)
    calc 4 * ‖_‖ ≤ 4 * ((C1 f * (1 + |t + τ|)⁻¹) * ‖Dirac.gamma ρ‖ * (C2 f * (1 + |t|)⁻¹) *
          ‖Dirac.gamma σ‖) := by
          have := hm.trans hb
          linarith
      _ = _ := by ring
  unfold vacuumPolarizationIntegrand
  rw [cons_add_cons, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (le_of_eq (mul_assoc _ _ _).symm)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun f _ => hterm f

end MatrixNorm

/-! ### The integrated bubble -/

/-- `‖log(F - iε)‖ ≤ |log ε| + (|F| + ε) + π`. -/
theorem norm_log_sub_le (F : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖log ((F : ℂ) - ε * I)‖ ≤ |Real.log ε| + (|F| + ε) + π := by
  set z : ℂ := (F : ℂ) - ε * I
  have hz1 : ε ≤ ‖z‖ := QED.TwoLoop.NestedVPFubiniBound.le_norm_sub_mul_I F hε
  have hz2 : ‖z‖ ≤ |F| + ε := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    simp [abs_of_pos hε]
  have hzpos : 0 < ‖z‖ := hε.trans_le hz1
  have hlog : |Real.log ‖z‖| ≤ |Real.log ε| + ‖z‖ := by
    rcases le_or_gt 1 ‖z‖ with h | h
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      have := Real.log_le_sub_one_of_pos hzpos
      linarith [abs_nonneg (Real.log ε)]
    · rw [abs_of_neg (Real.log_neg hzpos h)]
      have := Real.log_le_log hε hz1
      have := neg_abs_le (Real.log ε)
      linarith [norm_nonneg z]
  calc ‖log z‖ ≤ |(log z).re| + |(log z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖z‖| + |arg z| := by rw [log_re, log_im]
    _ ≤ (|Real.log ε| + ‖z‖) + π := add_le_add hlog (abs_arg_le_pi z)
    _ ≤ |Real.log ε| + (|F| + ε) + π := by linarith

theorem abs_feynmanMass_le (M s : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |vacuumPolarizationFeynmanMass M s x| ≤ M ^ 2 + |s| := by
  unfold vacuumPolarizationFeynmanMass
  have h0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
  have h1 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (sq_nonneg M), abs_mul, abs_of_nonneg h0]
  have := abs_nonneg s
  nlinarith

/-- The constant of the bound on `vpLogSum`. -/
noncomputable def logConst (P : Params) (ε : ℝ) : ℝ :=
  ∑ f, ‖(P.loopCoeff f : ℂ)‖ * (|Real.log ε| + P.mass f ^ 2 + ε + π + 1)

theorem logConst_nonneg (P : Params) {ε : ℝ} (hε : 0 < ε) : 0 ≤ logConst P ε :=
  Finset.sum_nonneg fun f _ => mul_nonneg (norm_nonneg _) (by positivity)

theorem norm_vpLogSum_le (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖QED.TwoLoop.VPHalfAt.vpLogSum P ε s x‖ ≤ logConst P ε * (1 + |s|) := by
  unfold QED.TwoLoop.VPHalfAt.vpLogSum logConst
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := norm_log_sub_le (vacuumPolarizationFeynmanMass (P.mass f) s x) hε
  have h2 := abs_feynmanMass_le (P.mass f) s hx
  have hs := abs_nonneg s
  have hA : 0 ≤ |Real.log ε| + P.mass f ^ 2 + ε + π := by positivity
  nlinarith

theorem norm_vpLoopEps_le (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ‖QED.TwoLoop.VPHalfAt.vpLoopEps P ε s‖ ≤
      |P.e ^ 2 / (2 * π ^ 2)| * (logConst P ε * (1 + |s|)) := by
  unfold QED.TwoLoop.VPHalfAt.vpLoopEps
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := logConst P ε * (1 + |s|))
    (f := fun x => ((x * (1 - x) : ℝ) : ℂ) * QED.TwoLoop.VPHalfAt.vpLogSum P ε s x)
    (fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ x * (1 - x) := mul_nonneg hx'.1 (by linarith [hx'.2])
      have h1 : |x * (1 - x)| ≤ 1 := by rw [abs_of_nonneg h0]; nlinarith [hx'.1, hx'.2]
      have hL := norm_vpLogSum_le P hε s hx'
      have hK : 0 ≤ logConst P ε * (1 + |s|) :=
        mul_nonneg (logConst_nonneg P hε) (by positivity)
      calc |x * (1 - x)| * ‖QED.TwoLoop.VPHalfAt.vpLogSum P ε s x‖
          ≤ 1 * (logConst P ε * (1 + |s|)) :=
            mul_le_mul h1 hL (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
  simpa using h

theorem norm_vpExtraEps_le (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ‖QED.TwoLoop.VPHalfAt.vpExtraEps P ε s‖ ≤
      |P.e ^ 2 / (4 * π ^ 2)| * (logConst P ε * (1 + |s|)) := by
  unfold QED.TwoLoop.VPHalfAt.vpExtraEps
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := logConst P ε * (1 + |s|)) (f := fun x => QED.TwoLoop.VPHalfAt.vpLogSum P ε s x)
    (fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      exact norm_vpLogSum_le P hε s (Ioc_subset_Icc_self hx))
  simpa using h

/-- **The integrated bubble grows at most like `(1 + ‖k‖)⁴`**: for `ε > 0`, the mass and the
Pauli–Villars conditions, `‖Π_ε^{ρσ}(k)‖ ≤ C (1 + ‖k‖)⁴` with `C` independent of `k`. -/
theorem exists_norm_vpPi_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (ρ σ : Fin 4) :
    ∃ C, 0 ≤ C ∧ ∀ k : Fin 4 → ℝ,
      ‖energyFirstIntegral (fun q => vacuumPolarizationIntegrand P ε k q ρ σ)‖ ≤
        C * (1 + ‖k‖) ^ 4 := by
  set c₁ := |P.e ^ 2 / (2 * π ^ 2)| * logConst P ε
  set c₂ := |P.e ^ 2 / (4 * π ^ 2)| * logConst P ε
  have hK := logConst_nonneg P hε
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  refine ⟨25 * c₁ + 5 * ε * c₂, by positivity, fun k => ?_⟩
  rw [QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂
    hε k ρ σ]
  set s := Minkowski.dot k k
  set u := 1 + ‖k‖
  have hk := norm_nonneg k
  have hu1 : 1 ≤ u := by simp only [u]; linarith
  have hs : |s| ≤ 4 * ‖k‖ ^ 2 := by
    have := abs_dot_le k k
    nlinarith
  have hs5 : 1 + |s| ≤ 5 * u ^ 2 := by nlinarith
  have hkk : |k ρ * k σ| ≤ ‖k‖ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (abs_apply_le k ρ) (abs_apply_le k σ) (abs_nonneg _) hk
  have hg := abs_metric_le ρ σ
  have hT : |s * Minkowski.metric ρ σ - k ρ * k σ| ≤ 5 * u ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have : |s| * |Minkowski.metric ρ σ| ≤ |s| := by
      nlinarith [abs_nonneg s, abs_nonneg (Minkowski.metric ρ σ)]
    nlinarith
  have hL := norm_vpLoopEps_le P hε s
  have hE := norm_vpExtraEps_le P hε s
  have hL' : ‖QED.TwoLoop.VPHalfAt.vpLoopEps P ε s‖ ≤ c₁ * (5 * u ^ 2) := by
    refine hL.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hs5 hc₁
  have hE' : ‖QED.TwoLoop.VPHalfAt.vpExtraEps P ε s‖ ≤ c₂ * (5 * u ^ 2) := by
    refine hE.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hs5 hc₂
  have hu2 : u ^ 2 ≤ u ^ 4 := by nlinarith
  calc ‖I * QED.TwoLoop.VPHalfAt.vpLoopEps P ε s *
          ((s * Minkowski.metric ρ σ - k ρ * k σ : ℝ) : ℂ) +
        (ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P ε s * (Minkowski.metric ρ σ : ℂ)‖
      ≤ ‖QED.TwoLoop.VPHalfAt.vpLoopEps P ε s‖ * |s * Minkowski.metric ρ σ - k ρ * k σ| +
          ε * ‖QED.TwoLoop.VPHalfAt.vpExtraEps P ε s‖ * |Minkowski.metric ρ σ| := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
          abs_of_pos hε]
    _ ≤ (c₁ * (5 * u ^ 2)) * (5 * u ^ 2) + ε * (c₂ * (5 * u ^ 2)) * 1 := by
        gcongr
    _ = 25 * c₁ * u ^ 2 * u ^ 2 + 5 * ε * c₂ * u ^ 2 := by ring
    _ ≤ 25 * c₁ * u ^ 4 + 5 * ε * c₂ * u ^ 4 := by
        have h4 : u ^ 2 * u ^ 2 = u ^ 4 := by ring
        have : 25 * c₁ * u ^ 2 * u ^ 2 = 25 * c₁ * u ^ 4 := by rw [mul_assoc, h4]
        rw [this]
        gcongr
    _ = (25 * c₁ + 5 * ε * c₂) * u ^ 4 := by ring

/-! ### The outer factor of the bubble–bubble class -/

/-- **The outer factor of the bubble–bubble class**, for the Lorentz indices `(ρ, σ)` of the
first bubble (the one next to the vertex of `ρ`-side photon `k`) and `(ρ', σ')` of the second:
the open-line chain `QED.TwoLoop.NestedVP.outerChain` contracted with the photon propagators of
momenta `k` (into the first bubble), `k` (between the bubbles) and `-k` (out of the second),
times the constants of the three open-line vertices, of the five outer propagators and of the
outer loop measure `(2π)⁻⁴`. The two closed-loop signs carried by the two vacuum polarization
integrands cancel. This is the candidate outer factor of the nested form; its identification with
the amplitude of `QED.ChainProof.Enum.repBB` is not proved here. -/
noncomputable def chainOuter (P : Params) (p kext k : Fin 4 → ℝ) (α β μ : Fin 4)
    (a b : Fin 4 × Fin 4) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 5 *
    ∑ l0 : Fin 4, ∑ l2 : Fin 4, QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 α β *
      photonPropagator P.mγ P.Λ P.ε k l0 a.1 * photonPropagator P.mγ P.Λ P.ε k a.2 b.1 *
      photonPropagator P.mγ P.Λ P.ε (-k) l2 b.2

/-- The outer factor is continuous in the photon momentum, for `ε > 0`. -/
theorem continuous_chainOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (a b : Fin 4 × Fin 4) : Continuous fun k => chainOuter P p kext k α β μ a b := by
  have hchain : ∀ l0 l2, Continuous fun k =>
      QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 := fun l0 l2 => by
    unfold QED.TwoLoop.NestedVP.outerChain
    exact ((((continuous_const.matrix_mul (continuous_electronPropagator_comp P.m hε
      (continuous_const.sub continuous_id))).matrix_mul continuous_const).matrix_mul
        (continuous_electronPropagator_comp P.m hε (continuous_const.sub continuous_id))).matrix_mul
          continuous_const)
  unfold chainOuter
  refine continuous_const.mul (continuous_finsetSum _ fun l0 _ =>
    continuous_finsetSum _ fun l2 _ => ?_)
  refine (((?_ : Continuous fun k => QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 α β).mul
    (continuous_photonPropagator_comp _ _ hε continuous_id _ _)).mul
      (continuous_photonPropagator_comp _ _ hε continuous_id _ _)).mul
        (continuous_photonPropagator_comp _ _ hε continuous_neg _ _)
  exact (continuous_apply β).comp ((continuous_apply α).comp (hchain l0 l2))

/-- **The outer factor decays like `(1 + |t|)⁻¹⁴`** in the photon energy `t`, at fixed `ε > 0`,
external momenta and spatial photon momentum `w`. -/
theorem decaysLike_chainOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (w : Fin 3 → ℝ)
    (α β μ : Fin 4) (a b : Fin 4 × Fin 4) :
    DecaysLike (fun t => chainOuter P p kext (Fin.cons t w) α β μ a b) 14 := by
  have hk := QED.TwoLoop.NestedVPFubiniBound.decaysLike_photonPropagator P.mγ P.Λ hε
    (fun t => (Fin.cons t w : Fin 4 → ℝ)) (fun t => by simp) (fun t i => by simp)
  have hk' := QED.TwoLoop.NestedVPFubiniBound.decaysLike_photonPropagator P.mγ P.Λ hε
    (fun t => -(Fin.cons t w : Fin 4 → ℝ)) (fun t => by simp) (fun t i => by simp)
  have h := (QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const
    ((((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 5)).mul
    (QED.TwoLoop.NestedVPFubiniBound.DecaysLike.sum Finset.univ fun l0 _ =>
      QED.TwoLoop.NestedVPFubiniBound.DecaysLike.sum Finset.univ fun l2 _ =>
      ((((QED.TwoLoop.NestedVPFubiniBound.decaysLike_outerChain P hε p kext w μ l0 l2).apply
        α β).mul (hk l0 a.1)).mul (hk a.2 b.1)).mul (hk' l2 b.2))
  exact h.congr fun t => rfl

end QED.ChainProof.HCLimit

end
