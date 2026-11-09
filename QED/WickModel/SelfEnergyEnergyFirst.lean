/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPoint
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import QED.OneLoop.VertexEnergyFirst
public import QED.Algebra.Contraction
import QED.Integration.LoopBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix

/-!
# The energy-first integral of the one-loop self-energy

Analytic machinery for the integrand `QED.WickModel.selfEnergyIntegrand` of the loop term of
`i Σ(p̸)` in the primary source's (62.28), under prescription M1 (decision D-5). It mirrors the
treatment of the one-loop vertex in `QED.OneLoop.VertexEnergyFirst`, with two propagator
denominators instead of three.

Fix the parameters, the external momentum `p`, and one matrix entry. For `ε > 0` and spatial loop
momentum `v`:

1. The gamma-matrix contraction `γ^μ (m - q̸) γ_μ = -4m - 2q̸` factors the integrand as
   `κ N(ℓ) [(D_e D_γ)⁻¹ - (D_e D_Λ)⁻¹]`, with `D_e` the electron and `D_M` the photon
   denominators (`selfEnergyIntegrand_apply`). Each product is a Feynman-parameter integral
   over `x ∈ (0, 1]` (`QED.Integration.inv_mul_eq_integral_feynman_two`), whose combined
   denominator is `-(t + x p⁰)² + W - iε` after completing the square (`combDen_cons`). The mass
   term is `W = |v⃗ + x p⃗|² + x m² + (1 - x) M² + x (1 - x) p²`.
2. The integrand is jointly integrable in the loop energy and the Feynman parameter, so the two
   integrals can be swapped; the numerator is affine in the loop energy, and the energy
   integral is evaluated in closed form (`integral_linear_mul_shifted_two`), giving
   `spatialG ε v` (`integral_selfEnergyIntegrand_time`).
3. Below both thresholds, `p² > -(m + m_γ)²` and `p² > -(m + Λ)²`, the Feynman mass term is
   bounded below by a positive constant, and the Pauli–Villars difference is bounded by
   `C (1 + ‖v‖)⁻⁴` uniformly in `ε > 0` (`norm_timeT_sub_le`).
4. Dominated convergence, first over the Feynman parameter and then over `v`, gives the limit
   `ε → 0⁺` of the energy-first integral: `∫ v, spatialG 0 v`
   (`tendsto_energyFirstIntegral_selfEnergyIntegrand_spatialG`).

The declarations in `QED.WickModel.SelfEnergyLimit` are internal helpers, not source-facing
definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.WickModel

/-- The Feynman mass term of the one-loop self-energy, `x m² + (1 - x) M² + x (1 - x) s`, with
`x` the Feynman parameter of the electron line, `M` the photon mass, and `s = p²`. -/
noncomputable def selfEnergyFeynmanMass (m M s x : ℝ) : ℝ :=
  x * m ^ 2 + (1 - x) * M ^ 2 + x * (1 - x) * s

/-- The Feynman mass term is a sum of a square and a multiple of `(m + M)² + s`. -/
theorem selfEnergyFeynmanMass_eq (m M s x : ℝ) :
    selfEnergyFeynmanMass m M s x
      = (x * m - (1 - x) * M) ^ 2 + x * (1 - x) * ((m + M) ^ 2 + s) := by
  unfold selfEnergyFeynmanMass
  ring

/-- **Below threshold the Feynman mass term is positive**: for `m, M > 0`, `s > -(m + M)²` and
`x ∈ [0, 1]`, `x m² + (1 - x) M² + x (1 - x) s > 0`. -/
theorem selfEnergyFeynmanMass_pos {m M s x : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hs : -(m + M) ^ 2 < s) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < selfEnergyFeynmanMass m M s x := by
  obtain ⟨hx0, hx1⟩ := hx
  rw [selfEnergyFeynmanMass_eq]
  rcases eq_or_lt_of_le hx0 with h0 | h0
  · subst h0
    have : (0 * m - (1 - 0) * M) ^ 2 + 0 * (1 - 0) * ((m + M) ^ 2 + s) = M ^ 2 := by ring
    rw [this]
    positivity
  rcases eq_or_lt_of_le hx1 with h1 | h1
  · subst h1
    have : (1 * m - (1 - 1) * M) ^ 2 + 1 * (1 - 1) * ((m + M) ^ 2 + s) = m ^ 2 := by ring
    rw [this]
    positivity
  · have : 0 < x * (1 - x) * ((m + M) ^ 2 + s) :=
      mul_pos (mul_pos h0 (by linarith)) (by linarith)
    positivity

/-- The Feynman mass term is continuous in the Feynman parameter. -/
theorem continuous_selfEnergyFeynmanMass (m M s : ℝ) :
    Continuous fun x => selfEnergyFeynmanMass m M s x := by
  unfold selfEnergyFeynmanMass
  fun_prop

/-- Below threshold the Feynman mass term is bounded below by a positive constant on `[0, 1]`. -/
theorem exists_pos_le_selfEnergyFeynmanMass {m M s : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hs : -(m + M) ^ 2 < s) :
    ∃ D₀ > 0, ∀ x ∈ Icc (0 : ℝ) 1, D₀ ≤ selfEnergyFeynmanMass m M s x := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (continuous_selfEnergyFeynmanMass m M s).continuousOn
  exact ⟨_, selfEnergyFeynmanMass_pos hm hM hs hx₀, fun x hx => hmin hx⟩

namespace SelfEnergyLimit

/-! ### Notation for the proof -/

/-- The overall constant `(ie)² (1/i)² (2π)⁻⁴` of the (62.28) integrand. -/
noncomputable def kappa (e : ℝ) : ℂ :=
  (I * e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- The `(i, j)` entry of the contracted Dirac numerator `γ^μ (m - (p̸ + ℓ̸)) γ_μ`, which equals
`-4m - 2 (p̸ + ℓ̸)`. -/
noncomputable def numer (m : ℝ) (p ℓ : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  -(4 * (m : ℂ)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) i j - 2 * Dirac.slash (p + ℓ) i j

/-- The coefficient of the loop energy in the numerator. -/
noncomputable def slope (i j : Fin 4) : ℂ :=
  -2 * Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) i j

/-- The spatial mass term `W = Σₖ (vₖ + x p^{k+1})² + D_M(x)` after completing the square. -/
noncomputable def massW (m M : ℝ) (p : Fin 4 → ℝ) (x : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ k : Fin 3, (v k + x * p k.succ) ^ 2 + selfEnergyFeynmanMass m M (Minkowski.dot p p) x

/-- The Feynman-combined denominator `x D_e + (1 - x) D_M` of one Pauli–Villars term. -/
noncomputable def combDen (m M ε : ℝ) (p : Fin 4 → ℝ) (x : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  (x : ℂ) * denom m ε (p + ℓ) + (1 - x) * denom M ε ℓ

/-- The closed-form energy integral of one Pauli–Villars term. -/
noncomputable def timeT (m M ε : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) (x : ℝ)
    (v : Fin 3 → ℝ) : ℂ :=
  (π / 2 : ℂ) * numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j *
    (-(massW m M p x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))

/-- The energy integral of the integrand, after the Feynman-parameter integral. -/
noncomputable def spatialG (P : Params) (ε : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4)
    (v : Fin 3 → ℝ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, kappa P.e * (timeT P.m P.mγ ε p i j x v - timeT P.m P.Λ ε p i j x v)

/-- The integrand on `ℝ × (0, 1]` at fixed `ε` and spatial momentum `v`, as a function of the
loop energy and the Feynman parameter. -/
noncomputable def jointF (P : Params) (ε : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) (v : Fin 3 → ℝ)
    (q : ℝ × ℝ) : ℂ :=
  kappa P.e * numer P.m p (Fin.cons q.1 v : Fin 4 → ℝ) i j *
    (combDen P.m P.mγ ε p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-2 : ℤ)
      - combDen P.m P.Λ ε p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-2 : ℤ))

/-! ### The gamma-matrix contraction -/

/-- `Σ_{μν} g_{μν} γ^ν X γ^μ = γ^μ X γ_μ`. -/
theorem sum_metric_smul_gamma_mul (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ ν, ((Minkowski.metric μ ν : ℝ) : ℂ) • (Dirac.gamma ν * X * Dirac.gamma μ)
      = ∑ μ, Dirac.gamma μ * X * Dirac.gammaLower μ := by
  simp only [Dirac.gammaLower, Matrix.mul_sum, Matrix.mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [Minkowski.metric_symm]

/-- `γ^μ (c - q̸) γ_μ = -4c - 2q̸`. -/
theorem sum_gamma_mul_sub_slash_mul_gammaLower (c : ℂ) (q : Fin 4 → ℝ) :
    ∑ μ, Dirac.gamma μ * (c • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash q) *
        Dirac.gammaLower μ
      = (-(4 * c)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (2 : ℂ) • Dirac.slash q := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, ← Finset.smul_sum, Dirac.contract_one,
    Dirac.contract_slash, smul_smul]
  congr 2
  ring

/-- The integrand as a scalar multiple of the contracted numerator. -/
theorem selfEnergyIntegrand_eq (P : Params) (ε : ℝ) (p ℓ : Fin 4 → ℝ) :
    selfEnergyIntegrand P ε p ℓ =
      (kappa P.e * (((denom P.mγ ε ℓ)⁻¹ - (denom P.Λ ε ℓ)⁻¹) * (denom P.m ε (p + ℓ))⁻¹)) •
        ((-(4 * (P.m : ℂ))) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (2 : ℂ) • Dirac.slash (p + ℓ)) := by
  have h : ∀ μ ν : Fin 4, photonPropagator P.mγ P.Λ ε ℓ μ ν •
      (Dirac.gamma ν * electronPropagator P.m ε (p + ℓ) * Dirac.gamma μ)
      = (((denom P.mγ ε ℓ)⁻¹ - (denom P.Λ ε ℓ)⁻¹) * (denom P.m ε (p + ℓ))⁻¹) •
        (((Minkowski.metric μ ν : ℝ) : ℂ) • (Dirac.gamma ν *
          ((P.m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p + ℓ)) * Dirac.gamma μ)) := by
    intro μ ν
    simp only [photonPropagator, electronPropagator, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      denom]
    congr 1
    ring
  rw [selfEnergyIntegrand, Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => h μ ν]
  simp only [← Finset.smul_sum]
  rw [sum_metric_smul_gamma_mul, sum_gamma_mul_sub_slash_mul_gammaLower, smul_smul, kappa]

/-- Entrywise factorization of the integrand. -/
theorem selfEnergyIntegrand_apply (P : Params) (ε : ℝ) (p ℓ : Fin 4 → ℝ) (i j : Fin 4) :
    selfEnergyIntegrand P ε p ℓ i j =
      kappa P.e * (((denom P.mγ ε ℓ)⁻¹ - (denom P.Λ ε ℓ)⁻¹) * (denom P.m ε (p + ℓ))⁻¹) *
        numer P.m p ℓ i j := by
  rw [selfEnergyIntegrand_eq, Matrix.smul_apply, smul_eq_mul, numer]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/-! ### Elementary facts -/

/-- The numerator is affine in the loop momentum. -/
theorem numer_add (m : ℝ) (p ℓ k : Fin 4 → ℝ) (i j : Fin 4) :
    numer m p (ℓ + k) i j = numer m p ℓ i j - 2 * Dirac.slash k i j := by
  simp only [numer, ← add_assoc, Dirac.slash_add, Matrix.add_apply]
  ring

/-- The numerator is affine in the loop energy. -/
theorem numer_cons (m : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) (t : ℝ) (v : Fin 3 → ℝ) :
    numer m p (Fin.cons t v : Fin 4 → ℝ) i j
      = slope i j * t + numer m p (Fin.cons 0 v : Fin 4 → ℝ) i j := by
  simp only [numer, slope, slash_add_cons p t v, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Completing the square in the Feynman-combined denominator. -/
theorem combDen_cons (m M ε : ℝ) (p : Fin 4 → ℝ) (x t : ℝ) (v : Fin 3 → ℝ) :
    combDen m M ε p x (Fin.cons t v : Fin 4 → ℝ) =
      -((t : ℂ) + (x * p 0 : ℝ)) ^ 2 + ((massW m M p x v : ℂ) - (ε : ℂ) * I) := by
  have key : x * (Minkowski.dot (p + Fin.cons t v) (p + Fin.cons t v) + m ^ 2)
      + (1 - x) * (Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) + M ^ 2)
      = -(t + x * p 0) ^ 2 + massW m M p x v := by
    have h2 : (Fin.cons t v : Fin 4 → ℝ) 2 = v 1 := rfl
    have h3 : (Fin.cons t v : Fin 4 → ℝ) 3 = v 2 := rfl
    have h4 : (Fin.succ 2 : Fin 4) = 3 := rfl
    simp only [massW, selfEnergyFeynmanMass, Minkowski.dot_eq, Fin.sum_univ_three, Pi.add_apply,
      Fin.cons_zero, Fin.cons_one, h2, h3, h4, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) key
  simp only [combDen, denom]
  push_cast at hc ⊢
  linear_combination hc

/-- The imaginary part of the combined denominator is `-ε`. -/
theorem combDen_im (m M ε : ℝ) (p : Fin 4 → ℝ) (x : ℝ) (ℓ : Fin 4 → ℝ) :
    (combDen m M ε p x ℓ).im = -ε := by
  simp only [combDen, add_im, mul_im, ofReal_re, ofReal_im, denom_im, sub_re, sub_im, one_re,
    one_im]
  ring

/-- For `ε ≠ 0` the combined denominator does not vanish. -/
theorem combDen_ne_zero {ε : ℝ} (hε : ε ≠ 0) (m M : ℝ) (p : Fin 4 → ℝ) (x : ℝ)
    (ℓ : Fin 4 → ℝ) : combDen m M ε p x ℓ ≠ 0 := by
  intro h
  have := combDen_im m M ε p x ℓ
  rw [h, zero_im] at this
  exact hε (by linarith)

/-- The combined denominator is continuous in the Feynman parameter. -/
theorem continuous_combDen (m M ε : ℝ) (p : Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    Continuous fun x : ℝ => combDen m M ε p x ℓ := by
  unfold combDen
  fun_prop

/-! ### Step 1: Feynman parameters -/

/-- For `ε ≠ 0` the squared inverse combined denominator is integrable over `(0, 1]`. -/
theorem integrableOn_combDen_zpow {ε : ℝ} (hε : ε ≠ 0) (m M : ℝ) (p : Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) :
    IntegrableOn (fun x : ℝ => combDen m M ε p x ℓ ^ (-2 : ℤ)) (Ioc (0 : ℝ) 1) := by
  have h : Continuous fun x : ℝ => combDen m M ε p x ℓ ^ (-2 : ℤ) :=
    (continuous_combDen m M ε p ℓ).zpow₀ _ fun x => Or.inl (combDen_ne_zero hε m M p x ℓ)
  exact (h.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- Two denominators as a Feynman-parameter integral over `(0, 1]`. -/
theorem inv_mul_denom_eq_integral {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p ℓ : Fin 4 → ℝ) :
    (denom m ε (p + ℓ) * denom M ε ℓ)⁻¹
      = ∫ x in Ioc (0 : ℝ) 1, combDen m M ε p x ℓ ^ (-2 : ℤ) := by
  have hA : (denom m ε (p + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hB : (denom M ε ℓ).im < 0 := by rw [denom_im]; linarith
  rw [inv_mul_eq_integral_feynman_two (ne_zero_of_im_neg hB)
    fun x hx => convex_combo_ne_zero hA hB hx, intervalIntegral.integral_of_le zero_le_one]
  rfl

/-- The integrand as a Feynman-parameter integral. -/
theorem selfEnergyIntegrand_eq_integral {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ)
    (i j : Fin 4) (t : ℝ) (v : Fin 3 → ℝ) :
    selfEnergyIntegrand P ε p (Fin.cons t v : Fin 4 → ℝ) i j =
      ∫ x in Ioc (0 : ℝ) 1, jointF P ε p i j v (t, x) := by
  set ℓ : Fin 4 → ℝ := Fin.cons t v
  have key : ((denom P.mγ ε ℓ)⁻¹ - (denom P.Λ ε ℓ)⁻¹) * (denom P.m ε (p + ℓ))⁻¹
      = (denom P.m ε (p + ℓ) * denom P.mγ ε ℓ)⁻¹ - (denom P.m ε (p + ℓ) * denom P.Λ ε ℓ)⁻¹ := by
    simp only [mul_inv]
    ring
  rw [selfEnergyIntegrand_apply, key, inv_mul_denom_eq_integral hε,
    inv_mul_denom_eq_integral hε, ← integral_sub (integrableOn_combDen_zpow hε.ne' _ _ p ℓ)
      (integrableOn_combDen_zpow hε.ne' _ _ p ℓ), ← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [jointF, ℓ]
  ring

/-! ### Step 2: the energy integral -/

/-- The first moment `t (t² + z)⁻²` is integrable for `z` in the slit plane. -/
theorem integrable_mul_sq_add_zpow_two {z : ℂ} (hz : z ∈ slitPlane) :
    Integrable fun t : ℝ => (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) := by
  obtain ⟨δ, hδ, c, hc, hbd⟩ := exists_lower_bound_add_of_mem_slitPlane hz
  have hb := hbd z (Metric.mem_ball_self hδ)
  have hne := sq_add_ne_zero_of_lower_bound hc hb
  refine (integrable_inv_one_add_sq.const_mul (c ^ 2)⁻¹).mono'
    (continuous_ofReal.mul (Continuous.zpow₀ (by fun_prop) _
      fun t => Or.inl (hne t))).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 := hb (t ^ 2) (sq_nonneg t)
  rw [ofReal_pow] at h1
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  have ht : ‖(t : ℂ)‖ ≤ 1 + t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  rw [norm_mul, norm_zpow, zpow_neg, zpow_ofNat]
  calc ‖(t : ℂ)‖ * (‖(t : ℂ) ^ 2 + z‖ ^ 2)⁻¹ ≤ (1 + t ^ 2) * ((c * (1 + t ^ 2)) ^ 2)⁻¹ := by
        gcongr
    _ = (c ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
        have : 0 < 1 + t ^ 2 := by positivity
        field_simp

/-- The odd moment vanishes: `∫ t (t² + z)⁻² dt = 0`. -/
theorem integral_mul_sq_add_zpow_two (z : ℂ) :
    ∫ t : ℝ, (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ)) volume
  simp only [ofReal_neg, neg_sq, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- `(-u² + w)⁻² = (u² - w)⁻²`. -/
theorem neg_sq_add_zpow_two (u w : ℂ) :
    (-u ^ 2 + w) ^ (-2 : ℤ) = (u ^ 2 + -w) ^ (-2 : ℤ) := by
  rw [show -u ^ 2 + w = -(u ^ 2 + -w) by ring, Even.neg_zpow (by decide)]

/-- An affine numerator against the square of a shifted denominator is integrable. -/
theorem integrable_linear_mul_shifted_two {w : ℂ} (hw : -w ∈ slitPlane) (a : ℝ) (β γ : ℂ) :
    Integrable fun t : ℝ => (β * t + γ) * (-((t : ℂ) + a) ^ 2 + w) ^ (-2 : ℤ) := by
  have i0 : Integrable fun s : ℝ => ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ) := by
    simpa using integrable_sq_add_zpow hw 2 (by norm_num)
  have i1 := integrable_mul_sq_add_zpow_two hw
  refine (((i1.const_mul β).add (i0.const_mul (γ - β * a))).comp_add_right a).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, neg_sq_add_zpow_two, ofReal_add]
  ring

/-- **Affine numerator against the square of a shifted denominator.** For `-w` in the slit
plane, `∫ (β t + γ) (-(t + a)² + w)⁻² dt = (γ - β a) (π/2) (-w)^{-3/2}`. -/
theorem integral_linear_mul_shifted_two {w : ℂ} (hw : -w ∈ slitPlane) (a : ℝ) (β γ : ℂ) :
    ∫ t : ℝ, (β * t + γ) * (-((t : ℂ) + a) ^ 2 + w) ^ (-2 : ℤ)
      = (γ - β * a) * ((π / 2 : ℂ) * (-w) ^ (-(3 / 2 : ℂ))) := by
  have i0 : Integrable fun s : ℝ => ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ) := by
    simpa using integrable_sq_add_zpow hw 2 (by norm_num)
  have i1 := integrable_mul_sq_add_zpow_two hw
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ,
      G = (fun s : ℝ => β * ((s : ℂ) * ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ)))
        + (fun s : ℝ => (γ - β * a) * ((s : ℂ) ^ 2 + -w) ^ (-2 : ℤ)) :=
    ⟨_, rfl⟩
  have hpt : ∀ t : ℝ, (β * t + γ) * (-((t : ℂ) + a) ^ 2 + w) ^ (-2 : ℤ) = G (t + a) := by
    intro t
    simp only [hG, Pi.add_apply, ofReal_add, neg_sq_add_zpow_two]
    ring
  simp_rw [hpt]
  rw [integral_add_right_eq_self G a, hG, integral_add' (i1.const_mul _) (i0.const_mul _),
    integral_const_mul, integral_const_mul, integral_mul_sq_add_zpow_two,
    integral_sq_add_zpow_two hw]
  ring

/-- For `ε > 0`, `-(W - iε)` lies in the slit plane. -/
theorem mem_slitPlane_neg_massW_sub {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    -((W : ℂ) - (ε : ℂ) * I) ∈ slitPlane := by
  rw [neg_sub', sub_neg_eq_add]
  exact VertexLimit.mem_slitPlane_neg_add_mul_I hε _

/-- At fixed Feynman parameter and spatial momentum, the numerator against one squared combined
denominator is integrable in the loop energy. -/
theorem integrable_numer_mul_combDen {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p : Fin 4 → ℝ)
    (i j : Fin 4) (x : ℝ) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => numer m p (Fin.cons t v : Fin 4 → ℝ) i j *
      combDen m M ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ) := by
  have hpt : ∀ t : ℝ, numer m p (Fin.cons t v : Fin 4 → ℝ) i j *
      combDen m M ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)
      = (slope i j * t + numer m p (Fin.cons 0 v : Fin 4 → ℝ) i j) *
        (-((t : ℂ) + (x * p 0 : ℝ)) ^ 2 + ((massW m M p x v : ℂ) - (ε : ℂ) * I)) ^ (-2 : ℤ) :=
    fun t => by rw [numer_cons, combDen_cons]
  simp_rw [hpt]
  exact integrable_linear_mul_shifted_two (mem_slitPlane_neg_massW_sub hε _) _ _ _

/-- The closed-form energy integral of the numerator against one squared combined denominator. -/
theorem integral_numer_mul_combDen {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p : Fin 4 → ℝ)
    (i j : Fin 4) (x : ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, numer m p (Fin.cons t v : Fin 4 → ℝ) i j *
      combDen m M ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ) = timeT m M ε p i j x v := by
  have hpt : ∀ t : ℝ, numer m p (Fin.cons t v : Fin 4 → ℝ) i j *
      combDen m M ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)
      = (slope i j * t + numer m p (Fin.cons 0 v : Fin 4 → ℝ) i j) *
        (-((t : ℂ) + (x * p 0 : ℝ)) ^ 2 + ((massW m M p x v : ℂ) - (ε : ℂ) * I)) ^ (-2 : ℤ) :=
    fun t => by rw [numer_cons, combDen_cons]
  simp_rw [hpt]
  rw [integral_linear_mul_shifted_two (mem_slitPlane_neg_massW_sub hε _), timeT,
    numer_cons m p i j (-(x * p 0)) v]
  have hneg : -((massW m M p x v : ℂ) - (ε : ℂ) * I) = -(massW m M p x v : ℂ) + ε * I := by
    ring
  rw [hneg]
  push_cast
  ring

/-! ### Step 2: joint integrability and the closed-form energy integral -/

/-- Almost every point of a product with Lebesgue measure on `(0, 1]` has second coordinate in `(0,
1]`. -/
theorem ae_prod_restrict_Ioc {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] :
    ∀ᵐ q ∂μ.prod (volume.restrict (Ioc (0 : ℝ) 1)), q.2 ∈ Ioc (0 : ℝ) 1 := by
  have h : μ.prod (volume.restrict (Ioc (0 : ℝ) 1))
      = (μ.prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioc (0 : ℝ) 1) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ioc) fun q hq => hq.2

/-- Norm bound for the square of a combined denominator. -/
theorem norm_zpow_neg_two_le {c s : ℝ} {Z : ℂ} (hc : 0 < c) (hs : 0 ≤ s)
    (hZ : c * (1 + s) ≤ ‖Z‖) : ‖Z ^ (-2 : ℤ)‖ ≤ (c ^ 2)⁻¹ * ((1 + s) ^ 2)⁻¹ := by
  have h1 : 0 < c * (1 + s) := by positivity
  rw [norm_zpow, zpow_neg, zpow_ofNat, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le hZ 2)

/-- `|t| ≤ 1 + t²`. -/
theorem norm_ofReal_le_one_add_sq (t : ℝ) : ‖(t : ℂ)‖ ≤ 1 + t ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]

/-- The numerator is continuous along a continuous loop energy. -/
theorem continuous_numer_cons (m : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) (v : Fin 3 → ℝ)
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous fun x => numer m p (Fin.cons (f x) v : Fin 4 → ℝ) i j := by
  have h : (fun x => numer m p (Fin.cons (f x) v : Fin 4 → ℝ) i j)
      = fun x => slope i j * (f x : ℂ) + numer m p (Fin.cons 0 v : Fin 4 → ℝ) i j :=
    funext fun x => numer_cons m p i j (f x) v
  rw [h]
  fun_prop

/-- The spatial mass term is continuous in the Feynman parameter. -/
theorem continuous_massW (m M : ℝ) (p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Continuous fun x => massW m M p x v := by
  simp only [massW, selfEnergyFeynmanMass, Fin.sum_univ_three]
  fun_prop

/-- The combined denominator is jointly continuous in the loop energy and the Feynman parameter. -/
theorem continuous_combDen_cons (m M ε : ℝ) (p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Continuous fun q : ℝ × ℝ => combDen m M ε p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) := by
  have hW := (continuous_massW m M p v).comp (continuous_snd : Continuous fun q : ℝ × ℝ => q.2)
  simp only [Function.comp_def] at hW
  simp_rw [combDen_cons]
  fun_prop

/-- For `ε ≠ 0` the joint integrand is continuous. -/
theorem continuous_jointF {ε : ℝ} (hε : ε ≠ 0) (P : Params) (p : Fin 4 → ℝ) (i j : Fin 4)
    (v : Fin 3 → ℝ) : Continuous (jointF P ε p i j v) := by
  unfold jointF
  have hN := continuous_numer_cons P.m p i j v (continuous_fst : Continuous fun q : ℝ × ℝ => q.1)
  have hγ := (continuous_combDen_cons P.m P.mγ ε p v).zpow₀ (-2)
    fun q => Or.inl (combDen_ne_zero hε _ _ p q.2 _)
  have hΛ := (continuous_combDen_cons P.m P.Λ ε p v).zpow₀ (-2)
    fun q => Or.inl (combDen_ne_zero hε _ _ p q.2 _)
  fun_prop

/-- For `ε > 0` the joint integrand is integrable in the loop energy and the Feynman parameter. -/
theorem integrable_jointF {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ) (i j : Fin 4)
    (v : Fin 3 → ℝ) :
    Integrable (jointF P ε p i j v)
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  obtain ⟨Cγ, hCγ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_massW P.m P.mγ p v).continuousOn (s := Icc (0 : ℝ) 1)
  obtain ⟨CΛ, hCΛ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_massW P.m P.Λ p v).continuousOn (s := Icc (0 : ℝ) 1)
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε |p 0| (max Cγ CΛ)
  set Cn : ℝ := ‖slope i j‖ + ‖numer P.m p (Fin.cons 0 v : Fin 4 → ℝ) i j‖
  set G : ℝ := ‖kappa P.e‖ * Cn * (2 * (c ^ 2)⁻¹)
  refine Integrable.mono' (g := fun q : ℝ × ℝ => G * (1 + q.1 ^ 2)⁻¹ * 1) ?_
    (continuous_jointF hε.ne' P p i j v).aestronglyMeasurable
    ((ae_prod_restrict_Ioc _).mono fun q hq => ?_)
  · exact (integrable_inv_one_add_sq.const_mul G).mul_prod (integrable_const (1 : ℝ))
  obtain ⟨t, x⟩ := q
  simp only at hq ⊢
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hq
  have ha : |x * p 0| ≤ |p 0| := by
    rw [abs_mul, abs_of_nonneg hxI.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hxI.2
  have hZ : ∀ M, massW P.m M p x v ≤ max Cγ CΛ →
      c * (1 + t ^ 2) ≤ ‖combDen P.m M ε p x (Fin.cons t v : Fin 4 → ℝ)‖ := by
    intro M hM
    rw [combDen_cons, ← add_sub_assoc]
    exact hcb t _ _ ha hM
  have hWγ : massW P.m P.mγ p x v ≤ max Cγ CΛ :=
    ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCγ x hxI)).trans (le_max_left _ _)
  have hWΛ : massW P.m P.Λ p x v ≤ max Cγ CΛ :=
    ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCΛ x hxI)).trans (le_max_right _ _)
  have hb1 := norm_zpow_neg_two_le hc (sq_nonneg t) (hZ _ hWγ)
  have hb2 := norm_zpow_neg_two_le hc (sq_nonneg t) (hZ _ hWΛ)
  have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hN : ‖numer P.m p (Fin.cons t v : Fin 4 → ℝ) i j‖ ≤ Cn * (1 + t ^ 2) := by
    rw [numer_cons]
    calc ‖slope i j * t + numer P.m p (Fin.cons 0 v : Fin 4 → ℝ) i j‖
        ≤ ‖slope i j‖ * ‖(t : ℂ)‖ + ‖numer P.m p (Fin.cons 0 v : Fin 4 → ℝ) i j‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ ‖slope i j‖ * (1 + t ^ 2)
          + ‖numer P.m p (Fin.cons 0 v : Fin 4 → ℝ) i j‖ * (1 + t ^ 2) := by
          gcongr
          · exact norm_ofReal_le_one_add_sq t
          · exact le_mul_of_one_le_right (norm_nonneg _) h1
      _ = Cn * (1 + t ^ 2) := by simp only [Cn]; ring
  have h1t : 0 < 1 + t ^ 2 := by positivity
  rw [jointF, norm_mul, norm_mul, mul_one]
  calc ‖kappa P.e‖ * ‖numer P.m p (Fin.cons t v : Fin 4 → ℝ) i j‖ *
        ‖combDen P.m P.mγ ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)
          - combDen P.m P.Λ ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)‖
      ≤ ‖kappa P.e‖ * (Cn * (1 + t ^ 2)) *
        ((c ^ 2)⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹ + (c ^ 2)⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
    _ = G * (1 + t ^ 2)⁻¹ := by
        simp only [G]
        field_simp
        ring

/-- The energy integral of the integrand equals `spatialG`. -/
theorem integral_selfEnergyIntegrand_time {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ)
    (i j : Fin 4) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, selfEnergyIntegrand P ε p (Fin.cons t v : Fin 4 → ℝ) i j = spatialG P ε p i j v := by
  simp_rw [selfEnergyIntegrand_eq_integral hε]
  rw [integral_integral_swap (f := fun t x => jointF P ε p i j v (t, x))
    (integrable_jointF hε P p i j v)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hpt : ∀ t : ℝ, jointF P ε p i j v (t, x) =
      kappa P.e * (numer P.m p (Fin.cons t v : Fin 4 → ℝ) i j *
          combDen P.m P.mγ ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)
        - numer P.m p (Fin.cons t v : Fin 4 → ℝ) i j *
          combDen P.m P.Λ ε p x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)) := by
    intro t
    simp only [jointF]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrable_numer_mul_combDen hε _ _ p i j x v)
    (integrable_numer_mul_combDen hε _ _ p i j x v), integral_numer_mul_combDen hε,
    integral_numer_mul_combDen hε]

/-! ### Step 3: the uniform Pauli–Villars bound -/

/-- A covariant component is bounded by the sup norm. -/
theorem norm_lower_le (ℓ : Fin 4 → ℝ) (κ : Fin 4) : ‖Minkowski.lower ℓ κ‖ ≤ ‖ℓ‖ := by
  have h := norm_le_pi_norm ℓ
  rw [Minkowski.lower_eq]
  fin_cases κ
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · simpa using h 3

/-- An entry of `ℓ̸` grows at most linearly in `ℓ`. -/
theorem norm_slash_apply_le (ℓ : Fin 4 → ℝ) (i j : Fin 4) :
    ‖Dirac.slash ℓ i j‖ ≤ (∑ κ, ‖Dirac.gamma κ i j‖) * ‖ℓ‖ := by
  have h : Dirac.slash ℓ i j = ∑ κ, ((Minkowski.lower ℓ κ : ℝ) : ℂ) * Dirac.gamma κ i j := by
    simp only [Dirac.slash, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_mul, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_lower_le ℓ κ) (norm_nonneg _)

/-- The numerator grows at most linearly. -/
theorem exists_norm_numer_le (m : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ, ‖numer m p ℓ i j‖ ≤ C * (1 + ‖ℓ‖) := by
  set Gs := ∑ κ, ‖Dirac.gamma κ i j‖
  have hGs : 0 ≤ Gs := Finset.sum_nonneg fun κ _ => norm_nonneg _
  refine ⟨‖numer m p 0 i j‖ + 2 * Gs, by positivity, fun ℓ => ?_⟩
  have h := numer_add m p 0 ℓ i j
  rw [zero_add] at h
  rw [h]
  have hs := norm_slash_apply_le ℓ i j
  calc ‖numer m p 0 i j - 2 * Dirac.slash ℓ i j‖ ≤ ‖numer m p 0 i j‖ + 2 * (Gs * ‖ℓ‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_ofNat]
        gcongr
    _ ≤ (‖numer m p 0 i j‖ + 2 * Gs) * (1 + ‖ℓ‖) := by
        nlinarith [norm_nonneg ℓ, norm_nonneg (numer m p 0 i j)]

/-- `‖π/2‖ = π/2`. -/
theorem norm_ofReal_div_two_pi : ‖(π / 2 : ℂ)‖ = π / 2 := by
  rw [show (π / 2 : ℂ) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The Pauli–Villars difference of the closed-form energy integrals decays like `‖v‖⁻⁴`,
uniformly in `ε > 0` and in the Feynman parameter. -/
theorem norm_timeT_sub_le {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p : Fin 4 → ℝ} (hpγ : -(m + mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(m + Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ ε > 0, ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeT m mγ ε p i j x v - timeT m Λ ε p i j x v‖ ≤ Cb * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  obtain ⟨CN, hCN0, hCN⟩ := exists_norm_numer_le m p i j
  obtain ⟨Dγ, hDγ, hDγle⟩ := exists_pos_le_selfEnergyFeynmanMass hm hmγ hpγ
  obtain ⟨DΛ, hDΛ, hDΛle⟩ := exists_pos_le_selfEnergyFeynmanMass hm hΛ hpΛ
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) ‖p‖ (lt_min hDγ hDΛ)
  set L : ℝ := mγ ^ 2 + Λ ^ 2
  refine ⟨π / 2 * (CN * (1 + ‖p‖)) * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))), by positivity,
    fun ε hε x hx v => ?_⟩
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  set Wγ : ℝ := massW m mγ p x v
  set WΛ : ℝ := massW m Λ p x v
  have hb : ‖(fun k : Fin 3 => x * p k.succ)‖ ≤ ‖p‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun k => ?_
    have h1 := norm_le_pi_norm p k.succ
    rw [Real.norm_eq_abs] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
    nlinarith [abs_nonneg (p k.succ), hx.2]
  have hWγ : c1 * u ^ 2 ≤ Wγ := hcoer v _ _ hb ((min_le_left _ _).trans (hDγle x hx))
  have hWΛ : c1 * u ^ 2 ≤ WΛ := hcoer v _ _ hb ((min_le_right _ _).trans (hDΛle x hx))
  have hpos : 0 < c1 * u ^ 2 := by positivity
  have hWγ0 : 0 < Wγ := hpos.trans_le hWγ
  have hWΛ0 : 0 < WΛ := hpos.trans_le hWΛ
  have hmin : c1 * u ^ 2 ≤ min Wγ WΛ := le_min hWγ hWΛ
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
  have r1 : (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
    calc (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ (c1 * u ^ 2) ^ (-(3 / 2 + 1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hmin (by norm_num)
      _ = c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
          rw [VertexLimit.rpow_mul_sq_neg hc1.le hu0]
          norm_num
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
  have hu4 : u * u ^ (-(5 : ℝ)) = u ^ (-(4 : ℝ)) := by
    rw [show (-(4 : ℝ)) = 1 + -5 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have hsplit : timeT m mγ ε p i j x v - timeT m Λ ε p i j x v
      = (π / 2 : ℂ) * numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j *
        ((-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))) := by
    simp only [timeT, Wγ, WΛ]
    ring
  rw [hsplit, norm_mul, norm_mul, norm_ofReal_div_two_pi]
  calc π / 2 * ‖numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j‖ *
        ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
      ≤ π / 2 * (CN * (1 + ‖p‖) * u) *
        (3 / 2 * |Wγ - WΛ| * (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ))) := by
        gcongr
    _ ≤ π / 2 * (CN * (1 + ‖p‖) * u) *
        (3 / 2 * L * (c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)))) := by
        gcongr
    _ = π / 2 * (CN * (1 + ‖p‖)) * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ)))
        * (u * u ^ (-(5 : ℝ))) := by ring
    _ = _ := by rw [hu4]

/-! ### Step 4: dominated convergence -/

/-- Below threshold the spatial mass term is positive on `[0, 1]`. -/
theorem massW_pos {m M : ℝ} (hm : 0 < m) (hM : 0 < M) {p : Fin 4 → ℝ}
    (hp : -(m + M) ^ 2 < Minkowski.dot p p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (v : Fin 3 → ℝ) : 0 < massW m M p x v := by
  have h1 := selfEnergyFeynmanMass_pos hm hM hp hx
  have h3 : 0 ≤ ∑ k : Fin 3, (v k + x * p k.succ) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  simp only [massW]
  linarith

/-- For `ε > 0` the closed-form energy integral is continuous in the Feynman parameter. -/
theorem continuous_timeT {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4)
    (v : Fin 3 → ℝ) : Continuous fun x => timeT m M ε p i j x v := by
  unfold timeT
  have hW := continuous_massW m M p v
  have hX : Continuous fun x => (-(massW m M p x v : ℂ) + ε * I) := by fun_prop
  have h32 := hX.cpow (continuous_const (y := -(3 / 2 : ℂ)))
    (fun x => VertexLimit.mem_slitPlane_neg_add_mul_I hε _)
  have hN := continuous_numer_cons m p i j v (by fun_prop : Continuous fun x : ℝ => -(x * p 0))
  fun_prop

/-- For a positive mass term, the closed-form energy integral converges as `ε → 0⁺`. -/
theorem tendsto_timeT {m M : ℝ} {p : Fin 4 → ℝ} (i j : Fin 4) {x : ℝ} {v : Fin 3 → ℝ}
    (hW : 0 < massW m M p x v) :
    Tendsto (fun ε : ℝ => timeT m M ε p i j x v) (𝓝[>] 0) (𝓝 (timeT m M 0 p i j x v)) := by
  have h0 : timeT m M 0 p i j x v =
      (π / 2 : ℂ) * numer m p (Fin.cons (-(x * p 0)) v : Fin 4 → ℝ) i j
        * (-(massW m M p x v : ℂ)) ^ (-(3 / 2 : ℂ)) := by
    simp only [timeT, ofReal_zero, zero_mul, add_zero]
  rw [h0]
  exact (tendsto_cpow_neg_add_mul_I hW _).const_mul _

/-- Below threshold, `spatialG ε v → spatialG 0 v` as `ε → 0⁺`, by dominated convergence over the
Feynman parameter. -/
theorem tendsto_spatialG {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hpγ : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(P.m + P.Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) (v : Fin 3 → ℝ) :
    Tendsto (fun ε : ℝ => spatialG P ε p i j v) (𝓝[>] 0) (𝓝 (spatialG P 0 p i j v)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := norm_timeT_sub_le hm hmγ hΛ hpγ hpΛ i j
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖kappa P.e‖ * Cb) ?_ ?_
    (integrable_const _) ?_
  · refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    have h1 := continuous_timeT hε P.m P.mγ p i j v
    have h2 := continuous_timeT hε P.m P.Λ p i j v
    exact (by fun_prop : Continuous fun x : ℝ => kappa P.e *
      (timeT P.m P.mγ ε p i j x v - timeT P.m P.Λ ε p i j x v)).aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun ε hε =>
      (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    have hxI : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have hu : (1 + ‖v‖) ^ (-(4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
    rw [norm_mul]
    calc ‖kappa P.e‖ * ‖timeT P.m P.mγ ε p i j x v - timeT P.m P.Λ ε p i j x v‖
        ≤ ‖kappa P.e‖ * (Cb * 1) := by
          gcongr
          exact (hCb ε hε x hxI v).trans (mul_le_mul_of_nonneg_left hu hCb0)
      _ = ‖kappa P.e‖ * Cb := by ring
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    have hxI : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    exact ((tendsto_timeT i j (massW_pos hm hmγ hpγ hxI v)).sub
      (tendsto_timeT i j (massW_pos hm hΛ hpΛ hxI v))).const_mul _

/-- The numerator is continuous in the loop momentum. -/
theorem continuous_numer (m : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) :
    Continuous fun ℓ => numer m p ℓ i j := by
  have hslash : Continuous Dirac.slash := by
    unfold Dirac.slash Minkowski.lower
    fun_prop
  unfold numer
  exact continuous_const.sub (continuous_const.mul
    ((hslash.comp (continuous_const.add continuous_id)).matrix_elem i j))

/-- For `ε ≠ 0` each entry of the integrand is continuous in `(v⃗, t)`. -/
theorem continuous_selfEnergyIntegrand_cons {ε : ℝ} (hε : ε ≠ 0) (P : Params)
    (p : Fin 4 → ℝ) (i j : Fin 4) :
    Continuous fun q : (Fin 3 → ℝ) × ℝ =>
      selfEnergyIntegrand P ε p (Fin.cons q.2 q.1 : Fin 4 → ℝ) i j := by
  simp_rw [selfEnergyIntegrand_apply]
  have hℓ : Continuous fun q : (Fin 3 → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst
  have hd : ∀ (M : ℝ) (k : (Fin 3 → ℝ) × ℝ → Fin 4 → ℝ), Continuous k →
      Continuous fun q => (denom M ε (k q))⁻¹ := by
    intro M k hk
    refine Continuous.inv₀ ?_ fun q h => ?_
    · unfold denom
      have := VertexLimit.continuous_dot_comp hk hk
      fun_prop
    · have := denom_im M ε (k q)
      rw [h, zero_im] at this
      exact hε (by linarith)
  have h1 := hd P.mγ _ hℓ
  have h2 := hd P.Λ _ hℓ
  have h3 := hd P.m _ (continuous_const (y := p).add hℓ)
  have hN := (continuous_numer P.m p i j).comp hℓ
  simp only [Function.comp_def] at hN
  fun_prop

/-! ### The energy-first integral and its limit -/

/-- For `ε > 0` the energy-first integral is `∫ v, spatialG ε v`. -/
theorem energyFirstIntegral_eq_integral_spatialG {ε : ℝ} (hε : 0 < ε) (P : Params)
    (p : Fin 4 → ℝ) (i j : Fin 4) :
    (energyFirstIntegral fun ℓ => selfEnergyIntegrand P ε p ℓ i j)
      = ∫ v, spatialG P ε p i j v := by
  simp only [energyFirstIntegral]
  exact integral_congr_ae (Eventually.of_forall fun v =>
    integral_selfEnergyIntegrand_time hε P p i j v)

/-- For `ε > 0`, `spatialG ε` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_spatialG {ε : ℝ} (hε : 0 < ε) (P : Params) (p : Fin 4 → ℝ)
    (i j : Fin 4) : AEStronglyMeasurable (spatialG P ε p i j) volume := by
  have h := (continuous_selfEnergyIntegrand_cons hε.ne' P p i j).stronglyMeasurable
    |>.integral_prod_right' (ν := (volume : Measure ℝ))
  exact h.aestronglyMeasurable.congr
    (Eventually.of_forall fun v => integral_selfEnergyIntegrand_time hε P p i j v)

/-- The uniform `(1 + ‖v‖)⁻⁴` bound on the energy integral. -/
theorem exists_norm_spatialG_le {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hpγ : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p)
    (hpΛ : -(P.m + P.Λ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    ∃ C : ℝ, ∀ ε > 0, ∀ v : Fin 3 → ℝ,
      ‖spatialG P ε p i j v‖ ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  obtain ⟨Cb, -, hCb⟩ := norm_timeT_sub_le hm hmγ hΛ hpγ hpΛ i j
  refine ⟨‖kappa P.e‖ * Cb * (volume.restrict (Ioc (0 : ℝ) 1)).real univ, fun ε hε v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun x => kappa P.e * (timeT P.m P.mγ ε p i j x v - timeT P.m P.Λ ε p i j x v))
    (C := ‖kappa P.e‖ * (Cb * (1 + ‖v‖) ^ (-(4 : ℝ))))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCb ε hε x (Ioc_subset_Icc_self hx) v) (norm_nonneg _))
  refine h.trans (le_of_eq ?_)
  ring

/-- The energy-first integral of each entry of the self-energy integrand converges, as
`ε → 0⁺`, to the integral over `v` of `spatialG 0 v`. -/
theorem tendsto_energyFirstIntegral_selfEnergyIntegrand_spatialG {P : Params} (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ}
    (hpγ : -(P.m + P.mγ) ^ 2 < Minkowski.dot p p) (hpΛ : -(P.m + P.Λ) ^ 2 < Minkowski.dot p p)
    (i j : Fin 4) :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => selfEnergyIntegrand P ε p ℓ i j)
      (𝓝[>] 0) (𝓝 (∫ v, spatialG P 0 p i j v)) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le hm hmγ hΛ hpγ hpΛ i j
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4)
    (by simp; norm_num)).const_mul C
  have hlim : Tendsto (fun ε : ℝ => ∫ v, spatialG P ε p i j v) (𝓝[>] 0)
      (𝓝 (∫ v, spatialG P 0 p i j v)) :=
    tendsto_integral_filter_of_dominated_convergence _
      (eventually_nhdsWithin_of_forall fun ε hε => aestronglyMeasurable_spatialG hε P p i j)
      (eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall (hC ε hε))
      hbnd
      (Eventually.of_forall fun v => tendsto_spatialG hm hmγ hΛ hpγ hpΛ i j v)
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact (energyFirstIntegral_eq_integral_spatialG hε P p i j).symm

end SelfEnergyLimit

end QED.WickModel

end
