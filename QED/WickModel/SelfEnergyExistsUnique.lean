/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.Wick.VertexKindOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import QED.Frozen.Algebra.Slash
public import QED.Frozen.Algebra.Dot
public import QED.Frozen.Algebra.Metric
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Complex.Basic
public import QED.WickModel.TwoPointClassification
public import QED.WickModel.SelfEnergyLimit
import QED.Integration.LoopBounds
import QED.Integration.ShiftedEnergyIntegral
import QED.OneLoop.VertexEnergyFirst
import QED.Algebra.Minkowski
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The electron self-energy: well-definedness and covariant form

A proof of the packet 6b candidate (Z₁) (decision D-25), under the name
`QED.WickModel.selfEnergy_existsUnique'`.

## Main statements

* `QED.WickModel.SelfEnergyLimit.integrable_spatialG`: for every `ε > 0` and every external
  momentum `p`, above or below threshold, the energy integral `spatialG ε` of the self-energy
  integrand is integrable over the spatial loop momentum. The Pauli–Villars difference decays
  like `(1 + ‖v‖)⁻⁴` (`norm_timeT_sub_le_of_pos`): for large `‖v‖` the spatial mass terms are
  positive and of order `‖v‖²`, and on the bounded remainder `ε > 0` bounds the integrand.
* `QED.WickModel.IsSelfEnergyLoop.regulatedAmplitude_eq`: the regulated amplitude of a
  self-energy loop is `(2π)⁴` times the self-energy integrand at the loop momentum `ℓ - p`.
* `QED.WickModel.selfEnergy_existsUnique'`: the candidate (Z₁). The integrability conjunct
  follows from the classification of the one-loop 1PI contractions (only the two self-energy
  loops have a loop line) and the translation invariance of the two Lebesgue integrals. The
  coefficients are `A = selfEnergyLoopA - δ₂` and `B = selfEnergyLoopB - δ_m`. They are unique
  because, for `p = ((1 - s)/2, 0, 0, (1 + s)/2)`, `p² = s`, the `(0, 0)` entry of `p̸` is `0` and
  its `(1, 3)` entry is `-1`.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.WickModel

namespace SelfEnergyLimit

/-! ### Integrability at fixed `ε > 0` for every external momentum -/

/-- For `ε > 0`, `‖(-W + iε)^{-3/2}‖ ≤ ε^{-3/2}` for every real `W`. -/
theorem norm_cpow_neg_three_halves_le {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    ‖(-(W : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖ ≤ ε ^ (-(3 / 2 : ℝ)) := by
  rw [show -(3 / 2 : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
  refine Real.rpow_le_rpow_of_nonpos hε ?_ (by norm_num)
  calc ε = |(-(W : ℂ) + ε * I).im| := by simp [abs_of_pos hε]
    _ ≤ ‖-(W : ℂ) + ε * I‖ := abs_im_le_norm _

/-- The spatial mass term is at least `c (1 + ‖v‖)² - (|p²| + 1)` on `[0, 1]`, for a constant
`c > 0` depending only on `‖p‖`, for every pair of masses. -/
theorem exists_mul_sq_sub_le_massW (p : Fin 4 → ℝ) :
    ∃ c > 0, ∀ (m M : ℝ), ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      c * (1 + ‖v‖) ^ 2 - (|Minkowski.dot p p| + 1) ≤ massW m M p x v := by
  obtain ⟨c, hc, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) ‖p‖ one_pos
  refine ⟨c, hc, fun m M x hx v => ?_⟩
  have hb : ‖(fun k : Fin 3 => x * p k.succ)‖ ≤ ‖p‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun k => ?_
    have h1 := norm_le_pi_norm p k.succ
    rw [Real.norm_eq_abs] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
    nlinarith [abs_nonneg (p k.succ), hx.2]
  set s := Minkowski.dot p p
  have hF : -|s| ≤ selfEnergyFeynmanMass m M s x := by
    have hy0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
    have hy1 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
    have h1 : -(x * (1 - x)) * |s| ≤ x * (1 - x) * s := by
      nlinarith [neg_abs_le s]
    have h2 : 0 ≤ x * m ^ 2 := mul_nonneg hx.1 (sq_nonneg m)
    have h3 : 0 ≤ (1 - x) * M ^ 2 := mul_nonneg (by linarith [hx.2]) (sq_nonneg M)
    unfold selfEnergyFeynmanMass
    nlinarith [abs_nonneg s]
  have h := hcoer v _ (selfEnergyFeynmanMass m M s x + (|s| + 1)) hb (by linarith)
  simp only [massW]
  linarith

/-- **The Pauli–Villars difference at fixed `ε > 0`.** For every external momentum `p` and all
masses, the difference of the closed-form energy integrals decays like `(1 + ‖v‖)⁻⁴`, uniformly
in the Feynman parameter. Unlike `norm_timeT_sub_le`, this bound is not uniform in `ε` and needs
no threshold condition. -/
theorem norm_timeT_sub_le_of_pos {ε : ℝ} (hε : 0 < ε) (m mγ Λ : ℝ) (p : Fin 4 → ℝ)
    (i j : Fin 4) :
    ∃ Cb : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeT m mγ ε p i j x v - timeT m Λ ε p i j x v‖ ≤ Cb * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  obtain ⟨CN, hCN0, hCN⟩ := exists_norm_numer_le m p i j
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_sq_sub_le_massW p
  set K : ℝ := |Minkowski.dot p p| + 1
  have hK : 0 < K := by positivity
  set L : ℝ := mγ ^ 2 + Λ ^ 2
  set A : ℝ := π / 2 * (CN * (1 + ‖p‖))
  have hA : 0 ≤ A := by positivity
  set C1 : ℝ := A * (3 / 2 * L * (c1 / 2) ^ (-(3 / 2 + 1 : ℝ)))
  set C2 : ℝ := A * (2 * ε ^ (-(3 / 2 : ℝ))) * (2 * K / c1) ^ 3
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨C1 + C2, fun x hx v => ?_⟩
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  have hu4 : u ^ (-(4 : ℝ)) = (u ^ 4)⁻¹ := by
    rw [Real.rpow_neg hu0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hupow : 0 ≤ u ^ (-(4 : ℝ)) := Real.rpow_nonneg hu0 _
  set Wγ : ℝ := massW m mγ p x v
  set WΛ : ℝ := massW m Λ p x v
  have hNt : ‖numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j‖ ≤ CN * (1 + ‖p‖) * u := by
    refine (hCN _).trans ?_
    have ha : |-(x * p 0)| ≤ ‖p‖ := by
      have h1 := norm_le_pi_norm p 0
      rw [Real.norm_eq_abs] at h1
      rw [abs_neg, abs_mul, abs_of_nonneg hx.1]
      nlinarith [abs_nonneg (p 0), hx.2]
    have h1 := norm_finCons_le (-(x * p 0)) v
    have h2 : 1 + ‖(Fin.cons (-(x * p 0)) v : Fin 4 → ℝ)‖ ≤ (1 + ‖p‖) * u := by
      simp only [u]
      nlinarith [norm_nonneg v, norm_nonneg p]
    calc CN * (1 + ‖(Fin.cons (-(x * p 0)) v : Fin 4 → ℝ)‖) ≤ CN * ((1 + ‖p‖) * u) := by
          gcongr
      _ = CN * (1 + ‖p‖) * u := by ring
  have hsplit : timeT m mγ ε p i j x v - timeT m Λ ε p i j x v
      = (π / 2 : ℂ) * numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j *
        ((-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))) := by
    simp only [timeT, Wγ, WΛ]
    ring
  rw [hsplit, norm_mul, norm_mul, norm_ofReal_div_two_pi]
  by_cases hlarge : 2 * K ≤ c1 * u ^ 2
  · -- far from the origin both spatial mass terms are positive and of order `‖v‖²`
    have hpos : 0 < c1 / 2 * u ^ 2 := by positivity
    have hWγ : c1 / 2 * u ^ 2 ≤ Wγ := by linarith [hcoer m mγ x hx v]
    have hWΛ : c1 / 2 * u ^ 2 ≤ WΛ := by linarith [hcoer m Λ x hx v]
    have hWγ0 : 0 < Wγ := hpos.trans_le hWγ
    have hWΛ0 : 0 < WΛ := hpos.trans_le hWΛ
    have hmin : c1 / 2 * u ^ 2 ≤ min Wγ WΛ := le_min hWγ hWΛ
    have hΔ : |Wγ - WΛ| ≤ L := by
      have h : Wγ - WΛ = (1 - x) * (mγ ^ 2 - Λ ^ 2) := by
        simp only [Wγ, WΛ, massW, selfEnergyFeynmanMass]
        ring
      rw [h, abs_mul, abs_of_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)]
      have : |mγ ^ 2 - Λ ^ 2| ≤ L := by
        simp only [L]
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg mγ, sq_nonneg Λ]
      have hx1 : 1 - x ≤ 1 := by linarith [hx.1]
      nlinarith [abs_nonneg (mγ ^ 2 - Λ ^ 2)]
    have hs32 : (-(((3 / 2 : ℝ)) : ℂ)) = -(3 / 2 : ℂ) := by push_cast; ring
    have l1 := norm_cpow_sub_cpow_le (s := 3 / 2) hWγ0 hWΛ0 hε (by norm_num)
    rw [hs32] at l1
    have r1 : (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ))
        ≤ (c1 / 2) ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
      calc (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ (c1 / 2 * u ^ 2) ^ (-(3 / 2 + 1 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hmin (by norm_num)
        _ = (c1 / 2) ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
            rw [VertexLimit.rpow_mul_sq_neg (by positivity) hu0]
            norm_num
    have hu45 : u * u ^ (-(5 : ℝ)) = u ^ (-(4 : ℝ)) := by
      rw [show (-(4 : ℝ)) = 1 + -5 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    calc π / 2 * ‖numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j‖ *
          ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
        ≤ π / 2 * (CN * (1 + ‖p‖) * u) *
          (3 / 2 * |Wγ - WΛ| * (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ))) := by
          gcongr
      _ ≤ π / 2 * (CN * (1 + ‖p‖) * u) *
          (3 / 2 * L * ((c1 / 2) ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)))) := by
          gcongr
      _ = C1 * (u * u ^ (-(5 : ℝ))) := by simp only [C1, A]; ring
      _ = C1 * u ^ (-(4 : ℝ)) := by rw [hu45]
      _ ≤ (C1 + C2) * u ^ (-(4 : ℝ)) := by gcongr; linarith
  · -- near the origin `ε > 0` bounds each term
    rw [not_le] at hlarge
    have hu2 : u ^ 2 ≤ 2 * K / c1 := by
      rw [le_div_iff₀ hc1]
      linarith
    have hu5 : u * u ^ 4 ≤ (2 * K / c1) ^ 3 :=
      calc u * u ^ 4 = u ^ 5 := by ring
        _ ≤ u ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
        _ = (u ^ 2) ^ 3 := by ring
        _ ≤ (2 * K / c1) ^ 3 := pow_le_pow_left₀ (by positivity) hu2 3
    have hb : u ≤ (2 * K / c1) ^ 3 * (u ^ 4)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      exact hu5
    have hcp := norm_cpow_neg_three_halves_le hε Wγ
    have hcp' := norm_cpow_neg_three_halves_le hε WΛ
    calc π / 2 * ‖numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j‖ *
          ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
        ≤ π / 2 * (CN * (1 + ‖p‖) * u) * (ε ^ (-(3 / 2 : ℝ)) + ε ^ (-(3 / 2 : ℝ))) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hcp hcp')
      _ = A * (2 * ε ^ (-(3 / 2 : ℝ))) * u := by simp only [A]; ring
      _ ≤ A * (2 * ε ^ (-(3 / 2 : ℝ))) * ((2 * K / c1) ^ 3 * (u ^ 4)⁻¹) := by gcongr
      _ = C2 * u ^ (-(4 : ℝ)) := by rw [hu4]; simp only [C2]; ring
      _ ≤ (C1 + C2) * u ^ (-(4 : ℝ)) := by gcongr; linarith

/-- At fixed `ε > 0`, the energy integral `spatialG ε` is bounded by `C (1 + ‖v‖)⁻⁴`, for every
external momentum. -/
theorem exists_norm_spatialG_le_of_pos {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ)
    (i j : Fin 4) :
    ∃ C : ℝ, ∀ v : Fin 3 → ℝ, ‖spatialG P ε p i j v‖ ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  obtain ⟨Cb, hCb⟩ := norm_timeT_sub_le_of_pos hε P.m P.mγ P.Λ p i j
  refine ⟨‖kappa P.e‖ * Cb * (volume.restrict (Ioc (0 : ℝ) 1)).real univ, fun v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun x => kappa P.e * (timeT P.m P.mγ ε p i j x v - timeT P.m P.Λ ε p i j x v))
    (C := ‖kappa P.e‖ * (Cb * (1 + ‖v‖) ^ (-(4 : ℝ))))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCb x (Ioc_subset_Icc_self hx) v) (norm_nonneg _))
  refine h.trans (le_of_eq ?_)
  ring

/-- **The spatial stage of M1 at fixed `ε > 0`.** For every `ε > 0` and every external momentum
`p`, the energy integral of each entry of the self-energy integrand is integrable over the
spatial loop momentum. -/
theorem integrable_spatialG {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ) (i j : Fin 4) :
    Integrable (spatialG P ε p i j) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le_of_pos hε P p i j
  exact ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4)
    (by simp; norm_num)).const_mul C).mono' (aestronglyMeasurable_spatialG hε P p i j)
    (Eventually.of_forall hC)

/-- **The energy stage of M1 at fixed `ε > 0`.** For every `ε > 0`, external momentum `p` and
spatial loop momentum `v`, each entry of the self-energy integrand is integrable in the loop
energy. -/
theorem integrable_selfEnergyIntegrand_time {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ)
    (i j : Fin 4) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => selfEnergyIntegrand P ε p (Fin.cons t v : Fin 4 → ℝ) i j := by
  simp_rw [selfEnergyIntegrand_eq_integral hε]
  exact (integrable_jointF hε P p i j v).integral_prod_left

/-- `(t, v) - c = (t - c⁰, v - c⃗)` in the energy-first coordinates. -/
theorem cons_sub_eq (t : ℝ) (v : Fin 3 → ℝ) (c : Fin 4 → ℝ) :
    (Fin.cons t v : Fin 4 → ℝ) - c = Fin.cons (t - c 0) (v - Fin.tail c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

/-- **Both stages of M1 at fixed `ε > 0`, at a translated loop momentum.** For every `ε > 0`,
external momentum `p` and translation `c`, each entry of `ℓ ↦ selfEnergyIntegrand (ℓ - c)` is
integrable in the loop energy, and its energy integral is integrable over the spatial loop
momentum. -/
theorem integrable_selfEnergyIntegrand_sub {ε : ℝ} (hε : 0 < ε) (P : Params) (p c : Fin 4 → ℝ)
    (i j : Fin 4) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      selfEnergyIntegrand P ε p ((Fin.cons t v : Fin 4 → ℝ) - c) i j) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      selfEnergyIntegrand P ε p ((Fin.cons t v : Fin 4 → ℝ) - c) i j := by
  simp_rw [cons_sub_eq]
  refine ⟨fun v => ?_, ?_⟩
  · exact (integrable_selfEnergyIntegrand_time hε P p i j (v - Fin.tail c)).comp_sub_right (c 0)
  · have h : ∀ v : Fin 3 → ℝ,
        ∫ t : ℝ, selfEnergyIntegrand P ε p (Fin.cons (t - c 0) (v - Fin.tail c)) i j =
          spatialG P ε p i j (v - Fin.tail c) := fun v => by
      rw [integral_sub_right_eq_self
        (fun t : ℝ => selfEnergyIntegrand P ε p (Fin.cons t (v - Fin.tail c)) i j) (c 0),
        integral_selfEnergyIntegrand_time hε]
    simp_rw [h]
    exact (integrable_spatialG hε P p i j).comp_sub_right (Fin.tail c)

end SelfEnergyLimit

/-! ### The regulated amplitude of a self-energy loop -/

/-- **The regulated amplitude of a self-energy loop** is `(2π)⁴` times the self-energy integrand
of (62.28) at the translated loop momentum `ℓ - p`, for equal incoming and outgoing momenta `p`.
This is the pointwise identity behind `IsSelfEnergyLoop.contractionValue_eq`. -/
theorem IsSelfEnergyLoop.regulatedAmplitude_eq (P : Params) {C : Contraction 1 0 gauge2}
    {a b : Fin 2} (hC : IsSelfEnergyLoop C a b) (p : Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    regulatedAmplitude P C ![p] ![p] kIn ℓ αOut βIn μ =
      (((2 * Real.pi) ^ 4 : ℝ) : ℂ) * selfEnergyIntegrand P P.ε p (ℓ - p) (αOut 0) (βIn 0) := by
  have hc : (((2 * Real.pi) ^ 4 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 4).ne'
  rw [regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.eq_electronFlavoring hφ),
    hC.contractionAmplitude_eq, hC.photonPropagator_lineMomentum, selfEnergyIntegrand]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, add_sub_cancel]
  have hsum : ∀ (D : Fin 4 → Fin 4 → ℂ) (S : Matrix (Fin 4) (Fin 4) ℂ),
      (∀ μ ν, D μ ν = D ν μ) →
      ∑ μ, ∑ ν, D μ ν * (Dirac.gamma ν * S * Dirac.gamma μ) (αOut 0) (βIn 0) =
        ∑ μ, ∑ ν, D μ ν * (Dirac.gamma μ * S * Dirac.gamma ν) (αOut 0) (βIn 0) :=
    fun D S hD => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hD]
  rw [hsum _ _ (QED.OneLoop.photonPropagator_comm _ _ _ _)]
  field_simp

/-! ### The one-loop 1PI contractions of the self-energy -/

/-- **The integrability conjunct of (Z₁).** For `ε > 0`, every one-loop 1PI contraction of the
one-electron function at order `≤ 2` has a loop integrand that is integrable in both stages of
M1. Such a contraction is one of the two self-energy loops: no contraction without vertices is
1PI, the only 1PI contraction of a single vertex is the `fermionCt` tree, which has no internal
line, and two vertices of total order `≤ 2` are two gauge vertices. -/
theorem integrable_regulatedAmplitude_selfEnergy (P : Params) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order ≤ 2) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) (hloop : ∃ f : Line C, IsLoopLine f) (p : Fin 4 → ℝ) (α β : Fin 4) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![] := by
  have hN : N ≤ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun t _ => one_le_order (κ t)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h
    omega
  rcases N with _ | _ | _ | N
  · exact absurd hC (not_isOnePI_of_fin_zero_left C)
  · obtain ⟨k, rfl⟩ : ∃ k, κ = oneVertex k := ⟨κ 0, eq_oneVertex κ⟩
    by_cases hk : k = .fermionCt
    · subst hk
      rw [isOnePI_iff_eq_selfEnergyTree] at hC
      subst hC
      obtain ⟨f, -⟩ := hloop
      exact IsEmpty.elim (inferInstanceAs (IsEmpty (Line selfEnergyTree))) f
    · exact absurd hC (not_isOnePI_oneVertex_selfEnergy hk C)
  · obtain rfl := eq_gauge2_of_sum_order_le hκ
    obtain ⟨a, b, hab⟩ := hC.exists_isSelfEnergyLoop
    simp_rw [hab.regulatedAmplitude_eq, Matrix.cons_val_zero]
    obtain ⟨h1, h2⟩ := SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hε
      { P with ε := ε } p p α β
    exact ⟨fun v => (h1 v).const_mul _, by simpa only [integral_const_mul] using h2.const_mul _⟩
  · omega

/-! ### Uniqueness of the coefficients -/

/-- A four-vector with `p² = s`: `p = ((1 - s)/2, 0, 0, (1 + s)/2)`. -/
noncomputable def selfEnergyTestMomentum (s : ℝ) : Fin 4 → ℝ :=
  ![(1 - s) / 2, 0, 0, (1 + s) / 2]

/-- The test momentum has `p² = s`. -/
theorem dot_selfEnergyTestMomentum (s : ℝ) :
    Minkowski.dot (selfEnergyTestMomentum s) (selfEnergyTestMomentum s) = s := by
  simp [Minkowski.dot_eq, selfEnergyTestMomentum]
  ring

/-- `A p̸ + B m` determines `A` and `B` at the test momentum, for `m ≠ 0`: the `(0, 0)` entry of
`p̸` is `0` and its `(1, 3)` entry is `-1`. -/
theorem eq_of_smul_slash_add_apply {m : ℝ} (hm : m ≠ 0) (s : ℝ) {a b a' b' : ℂ}
    (h : ∀ α β : Fin 4,
      (a • Dirac.slash (selfEnergyTestMomentum s)
        + (b * m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β =
      (a' • Dirac.slash (selfEnergyTestMomentum s)
        + (b' * m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β) :
    (a, b) = (a', b') := by
  have e00 : Dirac.slash (selfEnergyTestMomentum s) 0 0 = 0 := by
    simp [Dirac.slash, Fin.sum_univ_four, Dirac.gamma]
  have e13 : Dirac.slash (selfEnergyTestMomentum s) 1 3 = -1 := by
    simp [Dirac.slash, Fin.sum_univ_four, Minkowski.lower_eq, Dirac.gamma,
      selfEnergyTestMomentum]
    ring
  have h00 := h 0 0
  have h13 := h 1 3
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e00, e13, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 4) ≠ 3 by decide), mul_zero, mul_one, zero_add,
    add_zero] at h00 h13
  have hb : b = b' := mul_right_cancel₀ (ofReal_ne_zero.mpr hm) h00
  have ha : a = a' := by linear_combination -h13
  rw [ha, hb]

/-! ### The theorem -/

/-- (Z₁) **The electron self-energy: well-definedness and covariant form (packet 6b theorem goal;
decision D-25).** For `m, m_γ, Λ > 0`: first, for every `ε > 0` the loop integrand of every
one-loop 1PI contraction of the one-electron function at order `e²` is integrable in both stages
of the energy-first prescription M1, so its value (X₂₇) is a genuine integral. Second, there is a
unique pair of functions `A, B` of `s = p²` on the region `s > -(m + min(m_γ, Λ))²`, below the
thresholds of the electron with the photon and with the Pauli–Villars photon, such that, for
every `p` with `p²` in that region,
`Σ_ε(p) := (1/i) [i Σ_ε(p)]`, where `[i Σ_ε(p)]_{αβ}` is the one-electron 1PI function (X₂₈) at
order `e²` with the outgoing index `α` as row and the incoming index `β` as column
((62.27)–(62.28)), tends as `ε → 0⁺` to `A(p²) p̸ + B(p²) m`, entry by entry. The self-energy
has no closed fermion loop at this order, so it does not depend on the regulator fermions. -/
theorem selfEnergy_existsUnique' (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
    ∃! AB : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
          (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
  refine ⟨fun ε hε N κ hκ C hC hloop p α β =>
    integrable_regulatedAmplitude_selfEnergy P hε hκ C hC hloop p α β, ?_⟩
  set AB₀ : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ :=
    fun s => (selfEnergyLoopA P s.1 - P.δ₂, selfEnergyLoopB P s.1 - P.δm)
  have hex : ∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p)
      (α β : Fin 4),
      Tendsto (fun ε : ℝ => (1 / I) *
          onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
        (𝓝[>] 0)
        (𝓝 (((AB₀ ⟨_, hp⟩).1 • Dirac.slash p
          + ((AB₀ ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
    intro p hp α β
    have hmin : -(P.m + P.mγ) ^ 2 ≤ -(P.m + min P.mγ P.Λ) ^ 2 ∧
        -(P.m + P.Λ) ^ 2 ≤ -(P.m + min P.mγ P.Λ) ^ 2 := by
      have h0 : 0 ≤ P.m + min P.mγ P.Λ := by positivity
      exact ⟨neg_le_neg (pow_le_pow_left₀ h0 (by linarith [min_le_left P.mγ P.Λ]) 2),
        neg_le_neg (pow_le_pow_left₀ h0 (by linarith [min_le_right P.mγ P.Λ]) 2)⟩
    have hlim := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ
      (hmin.1.trans_lt hp) (hmin.2.trans_lt hp) α β
    set X : ℂ := ((P.δ₂ : ℂ) • Dirac.slash p +
      ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β
    have heq : (fun ε : ℝ => (1 / I) *
        onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![]) =
        fun ε : ℝ => (1 / I) * (-I * X) + (1 / I) *
          QED.OneLoop.energyFirstIntegral fun ℓ => selfEnergyIntegrand P ε p ℓ α β := by
      funext ε
      rw [onePIFunction_selfEnergy, mul_add]
      rfl
    rw [heq]
    convert (hlim.const_mul (1 / I)).const_add ((1 / I) * (-I * X)) using 2
    simp only [X, AB₀, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    push_cast
    ring
  refine ⟨AB₀, hex, fun AB hAB => ?_⟩
  funext ⟨s, hs⟩
  have hdot := dot_selfEnergyTestMomentum s
  have hp : -(P.m + min P.mγ P.Λ) ^ 2 <
      Minkowski.dot (selfEnergyTestMomentum s) (selfEnergyTestMomentum s) := by
    rw [hdot]
    exact hs
  have key := fun α β => tendsto_nhds_unique (hAB _ hp α β) (hex _ hp α β)
  have hsub : (⟨_, hp⟩ : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s}) = ⟨s, hs⟩ :=
    Subtype.ext hdot
  rw [hsub] at key
  exact eq_of_smul_slash_add_apply hm.ne' s key

end QED.WickModel

end
