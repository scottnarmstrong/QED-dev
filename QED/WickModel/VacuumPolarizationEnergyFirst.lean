/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationAlgebra
public import QED.WickModel.VacuumPolarizationBounds
public import QED.WickModel.SelfEnergyEnergyFirst
import QED.Integration.LoopBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The energy-first integral of the one-loop vacuum polarization

Analytic machinery for `QED.WickModel.vacuumPolarizationIntegrand` under prescription M1
(decision D-5), with the Pauli–Villars flavors of decision D-22. Fix the parameters, the photon
momentum `k` and the Lorentz indices `μ`, `ν`.

1. For `ε > 0`, each flavor's term `N_f(ℓ) / (D_f(ℓ + k) D_f(ℓ))` is a Feynman-parameter
   integral over `x ∈ (0, 1]` of `N_f(ℓ) (-(t + x k⁰)² + W_f - iε)⁻²`, where
   `W_f = Σ (v_i + x k^{i+1})² + M_f² + x (1 - x) k²` (`SelfEnergyLimit.massW`). The integrand is
   jointly integrable in the loop energy and `x` (`integrable_jointF`), and the energy integral is
   `timeT` in closed form (`integral_jointF_time`). Each flavor is integrable in the loop energy.
2. The Pauli–Villars sum `timeSum` of the closed forms decays like `(1 + ‖v‖)⁻⁵`, by the
   cancellation bounds of `QED.WickModel.VacuumPolarizationBounds`: this needs
   `∑ c_f = 0` and `∑ c_f M_f² = 0` (`norm_timeSum_le`). For each `ε > 0` it gives the
   integrability of the energy integral in the spatial momentum, for every `k`
   (`integrable_spatialG`); below the pair threshold `k² > -4m²` the bound is uniform in `ε`.
3. Dominated convergence gives the limit `ε → 0⁺` of the energy-first integral below threshold:
   `∫ v, spatialG 0 v` (`tendsto_energyFirstIntegral_spatialG`).

The declarations here are internal helpers of packet 6b, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.WickModel

namespace VacuumPolarizationLimit

/-! ### Notation for the proof -/

/-- The closed-form energy integral of the flavor-`M` term at Feynman parameter `x`:
`(π/2) z^{-3/2} (α z + N(-x k⁰, v⃗))` with `z = -W + iε`. -/
noncomputable def timeT (M ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  (π / 2 : ℂ) * (-(SelfEnergyLimit.massW M M k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)) *
    ((alpha μ ν : ℂ) * (-(SelfEnergyLimit.massW M M k x v : ℂ) + ε * I)
      + (numer M k (Fin.cons (-(x * k 0)) v) μ ν : ℂ))

/-- The Pauli–Villars sum of the closed-form energy integrals. -/
noncomputable def timeSum (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ)
    (v : Fin 3 → ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * timeT (P.mass f) ε k μ ν x v

/-- The energy integral of the integrand, after the Feynman-parameter integral. -/
noncomputable def spatialG (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (v : Fin 3 → ℝ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, kappa P.e * timeSum P ε k μ ν x v

/-- The flavor-`M` integrand on `ℝ × (0, 1]`, as a function of the loop energy and the Feynman
parameter. -/
noncomputable def jointF (M ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (v : Fin 3 → ℝ)
    (q : ℝ × ℝ) : ℂ :=
  (numer M k (Fin.cons q.1 v) μ ν : ℂ) *
    SelfEnergyLimit.combDen M M ε k q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-2 : ℤ)

/-- The flavor-`M` term of the integrand, `N(ℓ) / (D(ℓ + k) D(ℓ))`. -/
noncomputable def flavorTerm (M ε : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  (numer M k ℓ μ ν : ℂ) * (denom M ε (ℓ + k) * denom M ε ℓ)⁻¹

/-! ### Continuity of the numerator -/

/-- The numerator is continuous in the loop momentum. -/
theorem continuous_numer (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    Continuous fun ℓ => numer M k ℓ μ ν := by
  have hd := VertexLimit.continuous_dot_comp (continuous_id.add continuous_const)
    (continuous_id : Continuous fun ℓ : Fin 4 → ℝ => ℓ) (g := id) (f := fun ℓ => ℓ + k)
  unfold numer
  have h1 : Continuous fun ℓ : Fin 4 → ℝ => (ℓ + k) μ := (continuous_apply μ).comp
    (continuous_id.add continuous_const)
  have h2 : Continuous fun ℓ : Fin 4 → ℝ => (ℓ + k) ν := (continuous_apply ν).comp
    (continuous_id.add continuous_const)
  have h3 : Continuous fun ℓ : Fin 4 → ℝ => ℓ μ := continuous_apply μ
  have h4 : Continuous fun ℓ : Fin 4 → ℝ => ℓ ν := continuous_apply ν
  simp only [id] at hd
  fun_prop

/-- The numerator is continuous along a continuous loop momentum `(f, g)`. -/
theorem continuous_numer_cons (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) {X : Type*}
    [TopologicalSpace X] {f : X → ℝ} {g : X → Fin 3 → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun q => numer M k (Fin.cons (f q) (g q)) μ ν :=
  (continuous_numer M k μ ν).comp (Continuous.finCons (A := fun _ : Fin 4 => ℝ) hf hg)

/-- The numerator grows at most quadratically in the loop energy. -/
theorem exists_abs_numer_cons_le (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (v : Fin 3 → ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, |numer M k (Fin.cons t v) μ ν| ≤ C * (1 + t ^ 2) := by
  refine ⟨|numer M k (Fin.cons (-0) v) μ ν| + |linCoeff k (Fin.cons (-0) v) e0 μ ν|
    + |alpha μ ν|, fun t => ?_⟩
  rw [numer_cons_eq M k μ ν t 0 v, add_zero]
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  have h1 : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc |numer M k (Fin.cons (-0) v) μ ν + t * linCoeff k (Fin.cons (-0) v) e0 μ ν
        + t ^ 2 * alpha μ ν|
      ≤ |numer M k (Fin.cons (-0) v) μ ν| + |t| * |linCoeff k (Fin.cons (-0) v) e0 μ ν|
        + t ^ 2 * |alpha μ ν| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
    _ ≤ |numer M k (Fin.cons (-0) v) μ ν| * (1 + t ^ 2)
        + (1 + t ^ 2) * |linCoeff k (Fin.cons (-0) v) e0 μ ν| + (1 + t ^ 2) * |alpha μ ν| := by
        gcongr
        · exact le_mul_of_one_le_right (abs_nonneg _) h1
        · linarith
    _ = _ := by ring

/-! ### Step 1: Feynman parameters and the energy integral -/

/-- For `ε ≠ 0` the flavor integrand is jointly continuous. -/
theorem continuous_jointF {ε : ℝ} (hε : ε ≠ 0) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (v : Fin 3 → ℝ) : Continuous (jointF M ε k μ ν v) := by
  unfold jointF
  have hN := continuous_numer_cons M k μ ν (continuous_fst : Continuous fun q : ℝ × ℝ => q.1)
    (continuous_const (y := v))
  have hD := (SelfEnergyLimit.continuous_combDen_cons M M ε k v).zpow₀ (-2)
    fun q => Or.inl (SelfEnergyLimit.combDen_ne_zero hε _ _ k q.2 _)
  exact (continuous_ofReal.comp hN).mul hD

/-- For `ε > 0` the flavor integrand is integrable in the loop energy and the Feynman
parameter. -/
theorem integrable_jointF {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (v : Fin 3 → ℝ) :
    Integrable (jointF M ε k μ ν v)
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  obtain ⟨CW, hCW⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (SelfEnergyLimit.continuous_massW M M k v).continuousOn (s := Icc (0 : ℝ) 1)
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε |k 0| CW
  obtain ⟨Cn, hCn⟩ := exists_abs_numer_cons_le M k μ ν v
  have hCn0 : 0 ≤ Cn := by
    have := hCn 0
    nlinarith [abs_nonneg (numer M k (Fin.cons 0 v) μ ν)]
  refine Integrable.mono' (g := fun q : ℝ × ℝ => Cn * (c ^ 2)⁻¹ * (1 + q.1 ^ 2)⁻¹ * 1) ?_
    (continuous_jointF hε.ne' M k μ ν v).aestronglyMeasurable
    ((SelfEnergyLimit.ae_prod_restrict_Ioc _).mono fun q hq => ?_)
  · exact (integrable_inv_one_add_sq.const_mul _).mul_prod (integrable_const (1 : ℝ))
  obtain ⟨t, x⟩ := q
  simp only at hq ⊢
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hq
  have ha : |x * k 0| ≤ |k 0| := by
    rw [abs_mul, abs_of_nonneg hxI.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hxI.2
  have hW : SelfEnergyLimit.massW M M k x v ≤ CW :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCW x hxI)
  have hZ : c * (1 + t ^ 2) ≤
      ‖SelfEnergyLimit.combDen M M ε k x (Fin.cons t v : Fin 4 → ℝ)‖ := by
    rw [SelfEnergyLimit.combDen_cons, ← add_sub_assoc]
    exact hcb t _ _ ha hW
  have hb := SelfEnergyLimit.norm_zpow_neg_two_le hc (sq_nonneg t) hZ
  have h1t : 0 < 1 + t ^ 2 := by positivity
  rw [jointF, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_one]
  calc |numer M k (Fin.cons t v) μ ν| *
        ‖SelfEnergyLimit.combDen M M ε k x (Fin.cons t v : Fin 4 → ℝ) ^ (-2 : ℤ)‖
      ≤ (Cn * (1 + t ^ 2)) * ((c ^ 2)⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹) := by
        gcongr
        exact hCn t
    _ = Cn * (c ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
        field_simp

/-- The flavor term as a Feynman-parameter integral. -/
theorem flavorTerm_eq_integral {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (t : ℝ) (v : Fin 3 → ℝ) :
    flavorTerm M ε k (Fin.cons t v) μ ν = ∫ x in Ioc (0 : ℝ) 1, jointF M ε k μ ν v (t, x) := by
  rw [flavorTerm, add_comm (Fin.cons t v : Fin 4 → ℝ) k,
    SelfEnergyLimit.inv_mul_denom_eq_integral hε M M k, ← integral_const_mul]
  rfl

/-- **The energy integral at fixed Feynman parameter** is `timeT`. -/
theorem integral_jointF_time {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (x : ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, jointF M ε k μ ν v (t, x) = timeT M ε k μ ν x v := by
  set W := SelfEnergyLimit.massW M M k x v
  have hpt : ∀ t : ℝ, jointF M ε k μ ν v (t, x) =
      ((numer M k (Fin.cons (-(x * k 0)) v) μ ν : ℂ)
        + ((t : ℂ) + ((x * k 0 : ℝ) : ℂ)) * (linCoeff k (Fin.cons (-(x * k 0)) v) e0 μ ν : ℂ)
        + ((t : ℂ) + ((x * k 0 : ℝ) : ℂ)) ^ 2 * (alpha μ ν : ℂ)) *
        (-((t : ℂ) + ((x * k 0 : ℝ) : ℂ)) ^ 2 + ((W : ℂ) - (ε : ℂ) * I)) ^ (-2 : ℤ) := by
    intro t
    simp only [jointF]
    rw [numer_cons_eq M k μ ν t (x * k 0) v, SelfEnergyLimit.combDen_cons]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_quadratic_shifted_two (SelfEnergyLimit.mem_slitPlane_neg_massW_sub hε W), timeT]
  have hneg : -((W : ℂ) - (ε : ℂ) * I) = -(W : ℂ) + ε * I := by ring
  rw [hneg]

/-- The flavor term is integrable in the loop energy, and its energy integral is the
Feynman-parameter integral of `timeT`. -/
theorem integrable_flavorTerm_time {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (v : Fin 3 → ℝ) : Integrable fun t : ℝ => flavorTerm M ε k (Fin.cons t v) μ ν := by
  refine (integrable_jointF hε M k μ ν v).integral_prod_left.congr
    (Eventually.of_forall fun t => ?_)
  exact (flavorTerm_eq_integral hε M k μ ν t v).symm

/-- The energy integral of the flavor term is the Feynman-parameter integral of `timeT`. -/
theorem integral_flavorTerm_time {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (v : Fin 3 → ℝ) :
    ∫ t : ℝ, flavorTerm M ε k (Fin.cons t v) μ ν = ∫ x in Ioc (0 : ℝ) 1, timeT M ε k μ ν x v := by
  simp_rw [flavorTerm_eq_integral hε]
  rw [integral_integral_swap (f := fun t x => jointF M ε k μ ν v (t, x))
    (integrable_jointF hε M k μ ν v)]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_jointF_time hε M k μ ν x v)

/-! ### The energy integral of the integrand -/

/-- The closed-form energy integral is jointly continuous in `(v⃗, x)` for `ε > 0`. -/
theorem continuous_timeT {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    Continuous fun q : (Fin 3 → ℝ) × ℝ => timeT M ε k μ ν q.2 q.1 := by
  have hW : Continuous fun q : (Fin 3 → ℝ) × ℝ => SelfEnergyLimit.massW M M k q.2 q.1 := by
    simp only [SelfEnergyLimit.massW, selfEnergyFeynmanMass, Fin.sum_univ_three]
    fun_prop
  have hX : Continuous fun q : (Fin 3 → ℝ) × ℝ =>
      (-(SelfEnergyLimit.massW M M k q.2 q.1 : ℂ) + ε * I) := by fun_prop
  have h32 := hX.cpow (continuous_const (y := -(3 / 2 : ℂ)))
    (fun q => VertexLimit.mem_slitPlane_neg_add_mul_I hε _)
  have hN := continuous_ofReal.comp (continuous_numer_cons M k μ ν
    (f := fun q : (Fin 3 → ℝ) × ℝ => -(q.2 * k 0)) (g := fun q => q.1) (by fun_prop)
    continuous_fst)
  simp only [Function.comp_def] at hN
  unfold timeT
  fun_prop

/-- For `ε > 0` the closed-form energy integral is integrable over the Feynman parameter. -/
theorem integrableOn_timeT {ε : ℝ} (hε : 0 < ε) (M : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (v : Fin 3 → ℝ) : IntegrableOn (fun x => timeT M ε k μ ν x v) (Ioc (0 : ℝ) 1) :=
  (((continuous_timeT hε M k μ ν).comp (continuous_const.prodMk continuous_id)).continuousOn
    |>.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- **The integrand is integrable in the loop energy** for `ε > 0`. -/
theorem integrable_vacuumPolarizationIntegrand_time {ε : ℝ} (hε : 0 < ε) (P : Params)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => vacuumPolarizationIntegrand P ε k (Fin.cons t v) μ ν := by
  simp_rw [vacuumPolarizationIntegrand_eq]
  exact (integrable_finsetSum _ fun f _ =>
    (integrable_flavorTerm_time hε _ k μ ν v).const_mul _).const_mul _

/-- **The energy integral of the integrand** is `spatialG`. -/
theorem integral_vacuumPolarizationIntegrand_time {ε : ℝ} (hε : 0 < ε) (P : Params)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, vacuumPolarizationIntegrand P ε k (Fin.cons t v) μ ν = spatialG P ε k μ ν v := by
  have hF : ∀ t : ℝ, vacuumPolarizationIntegrand P ε k (Fin.cons t v) μ ν =
      kappa P.e * ∑ f, (P.loopCoeff f : ℂ) * flavorTerm (P.mass f) ε k (Fin.cons t v) μ ν :=
    fun t => vacuumPolarizationIntegrand_eq P ε k _ μ ν
  simp_rw [hF]
  rw [integral_const_mul, integral_finsetSum _ fun f _ =>
    (integrable_flavorTerm_time hε _ k μ ν v).const_mul _]
  simp_rw [integral_const_mul, integral_flavorTerm_time hε]
  rw [spatialG]
  simp only [timeSum, Finset.mul_sum]
  rw [integral_finsetSum _ fun f _ => ((integrableOn_timeT hε _ k μ ν v).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul, integral_const_mul]

/-- For `ε > 0`, `spatialG ε` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_spatialG {ε : ℝ} (hε : 0 < ε) (P : Params) (k : Fin 4 → ℝ)
    (μ ν : Fin 4) : AEStronglyMeasurable (spatialG P ε k μ ν) volume := by
  have hc : Continuous fun q : (Fin 3 → ℝ) × ℝ => kappa P.e * timeSum P ε k μ ν q.2 q.1 := by
    unfold timeSum
    exact continuous_const.mul (continuous_finsetSum _ fun f _ =>
      continuous_const.mul (continuous_timeT hε _ k μ ν))
  exact (hc.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).aestronglyMeasurable

/-! ### Step 2: the Pauli–Villars decay of the closed forms -/

/-- `W_M - W_{M'} = M² - M'²`. -/
theorem massW_sub_massW (M M' : ℝ) (k : Fin 4 → ℝ) (x : ℝ) (v : Fin 3 → ℝ) :
    SelfEnergyLimit.massW M M k x v - SelfEnergyLimit.massW M' M' k x v = M ^ 2 - M' ^ 2 := by
  simp only [SelfEnergyLimit.massW, selfEnergyFeynmanMass]
  ring

/-- `N_M - N_{M'} = -4 (M² - M'²) g^{μν}`. -/
theorem numer_sub_numer (M M' : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) :
    numer M k ℓ μ ν - numer M' k ℓ μ ν = -(4 * (M ^ 2 - M' ^ 2) * Minkowski.metric μ ν) := by
  simp only [numer]
  ring

/-- The flavor-independent part of the bracket of `timeT`. -/
noncomputable def bracketA (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ)
    (v : Fin 3 → ℝ) : ℂ :=
  (alpha μ ν : ℂ) * (-(SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v : ℂ) + ε * I)
    + (numer (P.mass 0) k (Fin.cons (-(x * k 0)) v) μ ν : ℂ)

/-- The flavor-dependent part of the bracket of `timeT`, `-(M_f² - m²) (α + 4 g^{μν})`. -/
noncomputable def bracketB (P : Params) (μ ν : Fin 4) (f : Fin 3) : ℝ :=
  -((P.mass f ^ 2 - P.mass 0 ^ 2) * (alpha μ ν + 4 * Minkowski.metric μ ν))

/-- The bracket of the flavor-`f` closed form splits as `A + B_f`. -/
theorem bracket_eq (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ)
    (v : Fin 3 → ℝ) (f : Fin 3) :
    (alpha μ ν : ℂ) * (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I)
      + (numer (P.mass f) k (Fin.cons (-(x * k 0)) v) μ ν : ℂ)
      = bracketA P ε k μ ν x v + (bracketB P μ ν f : ℂ) := by
  have h1 := congrArg (fun r : ℝ => (r : ℂ)) (massW_sub_massW (P.mass f) (P.mass 0) k x v)
  have h2 := congrArg (fun r : ℝ => (r : ℂ))
    (numer_sub_numer (P.mass f) (P.mass 0) k (Fin.cons (-(x * k 0)) v) μ ν)
  simp only [bracketA, bracketB]
  push_cast at h1 h2 ⊢
  linear_combination (-(alpha μ ν : ℂ)) * h1 + h2

/-- **The Pauli–Villars sum of the closed forms**:
`∑_f c_f T_f = (π/2) (A ∑_f c_f z_f^{-3/2} + ∑_f c_f B_f z_f^{-3/2})`. -/
theorem timeSum_eq (P : Params) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ)
    (v : Fin 3 → ℝ) :
    timeSum P ε k μ ν x v = (π / 2 : ℂ) * (bracketA P ε k μ ν x v *
        ∑ f, (P.loopCoeff f : ℂ) *
          (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
      + ∑ f, ((P.loopCoeff f * bracketB P μ ν f : ℝ) : ℂ) *
          (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))) := by
  simp only [timeSum, timeT, mul_assoc, bracket_eq]
  simp only [Fin.sum_univ_three]
  push_cast
  ring

/-- Under the Pauli–Villars conditions, `∑_f c_f = 0`. -/
theorem sum_loopCoeff {P : Params} (hPV₁ : 1 + P.c₁ + P.c₂ = 0) : ∑ f, P.loopCoeff f = 0 := by
  simp [Fin.sum_univ_three, Params.loopCoeff, hPV₁]

/-- Under the Pauli–Villars conditions, `∑_f c_f M_f² = 0`. -/
theorem sum_loopCoeff_mul_mass_sq {P : Params}
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    ∑ f, P.loopCoeff f * P.mass f ^ 2 = 0 := by
  simp [Fin.sum_univ_three, Params.loopCoeff, Params.mass, hPV₂]

/-- Under the Pauli–Villars conditions, `∑_f c_f (M_f² - m²) = 0`. -/
theorem sum_loopCoeff_mul_mass_sq_sub {P : Params} (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    ∑ f, P.loopCoeff f * (P.mass f ^ 2 - P.mass 0 ^ 2) = 0 := by
  have h1 := sum_loopCoeff hPV₁
  have h2 := sum_loopCoeff_mul_mass_sq hPV₂
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, h2, zero_mul, sub_zero]

/-- The regulator fermions are heavier than the electron. -/
theorem mass_sq_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (f : Fin 3) : P.mass 0 ^ 2 ≤ P.mass f ^ 2 := by
  have h0 : P.mass 0 = P.m := rfl
  fin_cases f
  · exact le_rfl
  · change P.mass 0 ^ 2 ≤ P.M₁ ^ 2
    rw [h0]
    exact pow_le_pow_left₀ hm.le hM₁.le 2
  · change P.mass 0 ^ 2 ≤ P.M₂ ^ 2
    rw [h0]
    exact pow_le_pow_left₀ hm.le hM₂.le 2

/-- A component is bounded by the sup norm. -/
theorem abs_apply_le (ℓ : Fin 4 → ℝ) (μ : Fin 4) : |ℓ μ| ≤ ‖ℓ‖ := by
  have := norm_le_pi_norm ℓ μ
  rwa [Real.norm_eq_abs] at this

/-- `|a·b| ≤ 4 ‖a‖ ‖b‖`. -/
theorem abs_dot_le (a b : Fin 4 → ℝ) : |Minkowski.dot a b| ≤ 4 * (‖a‖ * ‖b‖) := by
  have h : ∀ i : Fin 4, |a i * b i| ≤ ‖a‖ * ‖b‖ := fun i => by
    rw [abs_mul]
    exact mul_le_mul (abs_apply_le a i) (abs_apply_le b i) (abs_nonneg _) (norm_nonneg _)
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  have h3 := abs_le.mp (h 3)
  rw [Minkowski.dot_eq, abs_le]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `|g^{μν}| ≤ 1`. -/
theorem abs_metric_le (μ ν : Fin 4) : |Minkowski.metric μ ν| ≤ 1 := by
  unfold Minkowski.metric
  split_ifs <;> simp

/-- The numerator grows at most quadratically in the loop momentum. -/
theorem abs_numer_le (M : ℝ) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) :
    |numer M k ℓ μ ν| ≤ 4 * (6 * (1 + ‖k‖) + M ^ 2) * (1 + ‖ℓ‖) ^ 2 := by
  have hk := norm_nonneg k
  have hl := norm_nonneg ℓ
  have hlk : ‖ℓ + k‖ ≤ ‖ℓ‖ + ‖k‖ := norm_add_le _ _
  have e1 : |(ℓ + k) μ * ℓ ν| ≤ (‖ℓ‖ + ‖k‖) * ‖ℓ‖ := by
    rw [abs_mul]
    exact mul_le_mul ((abs_apply_le _ μ).trans hlk) (abs_apply_le ℓ ν) (abs_nonneg _)
      (by positivity)
  have e2 : |(ℓ + k) ν * ℓ μ| ≤ (‖ℓ‖ + ‖k‖) * ‖ℓ‖ := by
    rw [abs_mul]
    exact mul_le_mul ((abs_apply_le _ ν).trans hlk) (abs_apply_le ℓ μ) (abs_nonneg _)
      (by positivity)
  have e3 : |Minkowski.dot (ℓ + k) ℓ| ≤ 4 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) :=
    (abs_dot_le _ _).trans (by gcongr)
  have e5 : |(Minkowski.dot (ℓ + k) ℓ + M ^ 2) * Minkowski.metric μ ν|
      ≤ 4 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2 := by
    rw [abs_mul]
    calc |Minkowski.dot (ℓ + k) ℓ + M ^ 2| * |Minkowski.metric μ ν|
        ≤ (4 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2) * 1 := by
          gcongr
          · refine (abs_add_le _ _).trans ?_
            rw [abs_of_nonneg (sq_nonneg M)]
            linarith
          · exact abs_metric_le μ ν
      _ = _ := by ring
  have hsum : |(ℓ + k) μ * ℓ ν + (ℓ + k) ν * ℓ μ
      - (Minkowski.dot (ℓ + k) ℓ + M ^ 2) * Minkowski.metric μ ν|
      ≤ 6 * ((‖ℓ‖ + ‖k‖) * ‖ℓ‖) + M ^ 2 := by
    refine (abs_sub _ _).trans ?_
    have := abs_add_le ((ℓ + k) μ * ℓ ν) ((ℓ + k) ν * ℓ μ)
    linarith
  unfold numer
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hq : (‖ℓ‖ + ‖k‖) * ‖ℓ‖ ≤ (1 + ‖k‖) * (1 + ‖ℓ‖) ^ 2 := by
    nlinarith [mul_nonneg hk hl, mul_nonneg hk (sq_nonneg ‖ℓ‖)]
  have hM : M ^ 2 ≤ M ^ 2 * (1 + ‖ℓ‖) ^ 2 := by nlinarith [sq_nonneg M, sq_nonneg ‖ℓ‖]
  nlinarith

/-- The shift `x k⃗` has norm at most `‖k‖` for `x ∈ [0, 1]`. -/
theorem norm_shift_le (k : Fin 4 → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖(fun i : Fin 3 => x * k i.succ)‖ ≤ ‖k‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg k)).2 fun i => ?_
  have h1 := norm_le_pi_norm k i.succ
  rw [Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
  nlinarith [abs_nonneg (k i.succ), hx.2]

/-- The Feynman mass term grows at most quadratically in the spatial momentum. -/
theorem abs_massW_le (M : ℝ) (k : Fin 4 → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (v : Fin 3 → ℝ) :
    |SelfEnergyLimit.massW M M k x v|
      ≤ (3 * (1 + ‖k‖) ^ 2 + M ^ 2 + |Minkowski.dot k k|) * (1 + ‖v‖) ^ 2 := by
  have hb := norm_shift_le k hx
  have hv := norm_nonneg v
  have hk := norm_nonneg k
  have hi : ∀ i : Fin 3, (v i + x * k i.succ) ^ 2 ≤ (1 + ‖k‖) ^ 2 * (1 + ‖v‖) ^ 2 := by
    intro i
    have h1 : |v i + x * k i.succ| ≤ ‖v‖ + ‖k‖ := by
      have hv' := norm_le_pi_norm v i
      have hb' := norm_le_pi_norm (fun i : Fin 3 => x * k i.succ) i
      rw [Real.norm_eq_abs] at hv' hb'
      exact (abs_add_le _ _).trans (by linarith)
    have h2 : ‖v‖ + ‖k‖ ≤ (1 + ‖k‖) * (1 + ‖v‖) := by nlinarith
    calc (v i + x * k i.succ) ^ 2 = |v i + x * k i.succ| ^ 2 := (sq_abs _).symm
      _ ≤ ((1 + ‖k‖) * (1 + ‖v‖)) ^ 2 := by gcongr; exact h1.trans h2
      _ = _ := by ring
  have hD : |selfEnergyFeynmanMass M M (Minkowski.dot k k) x| ≤ M ^ 2 + |Minkowski.dot k k| := by
    have : selfEnergyFeynmanMass M M (Minkowski.dot k k) x
        = M ^ 2 + x * (1 - x) * Minkowski.dot k k := by
      unfold selfEnergyFeynmanMass
      ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (sq_nonneg M), abs_mul, abs_of_nonneg (by nlinarith [hx.1, hx.2] :
      0 ≤ x * (1 - x))]
    have : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
    nlinarith [abs_nonneg (Minkowski.dot k k)]
  have hu : 1 ≤ (1 + ‖v‖) ^ 2 := by nlinarith
  have hS : 0 ≤ ∑ i : Fin 3, (v i + x * k i.succ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [SelfEnergyLimit.massW]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hS, Fin.sum_univ_three]
  have := hi 0
  have := hi 1
  have := hi 2
  nlinarith [abs_nonneg (Minkowski.dot k k), sq_nonneg M]

/-- `λ^{-r} ≤ c^{-r} u^{-2r}` when `c u² ≤ λ`. -/
theorem rpow_neg_le_of_mul_sq_le {c u lam r : ℝ} (hc : 0 < c) (hu : 0 < u)
    (hlam : c * u ^ 2 ≤ lam) (hr : 0 ≤ r) : lam ^ (-r) ≤ c ^ (-r) * u ^ (-(2 * r)) := by
  rw [← VertexLimit.rpow_mul_sq_neg hc.le hu.le]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hlam (by linarith)

/-- The constant in the quadratic growth of the flavor-independent bracket. -/
noncomputable def constA (P : Params) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  |alpha μ ν| * (3 * (1 + ‖k‖) ^ 2 + P.mass 0 ^ 2 + |Minkowski.dot k k|) + |alpha μ ν|
    + 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) * (1 + ‖k‖) ^ 2

/-- The flavor-independent bracket grows at most quadratically in the spatial momentum. -/
theorem norm_bracketA_le (P : Params) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (v : Fin 3 → ℝ) :
    ‖bracketA P ε k μ ν x v‖ ≤ constA P k μ ν * (1 + ε) * (1 + ‖v‖) ^ 2 := by
  have hu1 : 1 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have hu2 : 1 ≤ (1 + ‖v‖) ^ 2 := by nlinarith
  have hW0 := abs_massW_le (P.mass 0) k hx v
  have hl : ‖(Fin.cons (-(x * k 0)) v : Fin 4 → ℝ)‖ ≤ ‖k‖ + ‖v‖ := by
    refine (norm_finCons_le _ _).trans ?_
    have h1 := abs_apply_le k 0
    have : |-(x * k 0)| ≤ |k 0| := by
      rw [abs_neg, abs_mul, abs_of_nonneg hx.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hx.2
    linarith
  have hlu : (1 + ‖(Fin.cons (-(x * k 0)) v : Fin 4 → ℝ)‖) ^ 2
      ≤ (1 + ‖k‖) ^ 2 * (1 + ‖v‖) ^ 2 := by
    rw [← mul_pow]
    gcongr
    nlinarith [norm_nonneg k, norm_nonneg v]
  have hN : |numer (P.mass 0) k (Fin.cons (-(x * k 0)) v) μ ν|
      ≤ 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) * (1 + ‖k‖) ^ 2 * (1 + ‖v‖) ^ 2 := by
    refine (abs_numer_le _ k _ μ ν).trans ?_
    have : 0 ≤ 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) := by positivity
    calc 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) * (1 + ‖(Fin.cons (-(x * k 0)) v : Fin 4 → ℝ)‖) ^ 2
        ≤ 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) * ((1 + ‖k‖) ^ 2 * (1 + ‖v‖) ^ 2) := by gcongr
      _ = _ := by ring
  have hz : ‖-(SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v : ℂ) + ε * I‖
      ≤ |SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v| + ε := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos hε]
  have hα : 0 ≤ |alpha μ ν| := abs_nonneg _
  have hεu : ε ≤ ε * (1 + ‖v‖) ^ 2 := le_mul_of_one_le_right hε.le hu2
  simp only [bracketA]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have e : constA P k μ ν * (1 + ε) * (1 + ‖v‖) ^ 2
      = |alpha μ ν| * ((3 * (1 + ‖k‖) ^ 2 + P.mass 0 ^ 2 + |Minkowski.dot k k|) * (1 + ‖v‖) ^ 2
          + ε * (1 + ‖v‖) ^ 2)
        + 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) * (1 + ‖k‖) ^ 2 * (1 + ‖v‖) ^ 2
        + (|alpha μ ν| * (3 * (1 + ‖k‖) ^ 2 + P.mass 0 ^ 2 + |Minkowski.dot k k|) * ε
            * (1 + ‖v‖) ^ 2 + |alpha μ ν| * (1 + ‖v‖) ^ 2
          + 4 * (6 * (1 + ‖k‖) + P.mass 0 ^ 2) * (1 + ‖k‖) ^ 2 * ε * (1 + ‖v‖) ^ 2) := by
    simp only [constA]
    ring
  rw [e]
  refine le_add_of_le_of_nonneg (add_le_add ?_ hN) (by positivity)
  exact mul_le_mul_of_nonneg_left (hz.trans (add_le_add hW0 hεu)) hα

/-- The second-order Pauli–Villars constant `∑_f |c_f| (M_f² - m²)²`. -/
noncomputable def constS₂ (P : Params) : ℝ :=
  ∑ f, |P.loopCoeff f| * (P.mass f ^ 2 - P.mass 0 ^ 2) ^ 2

/-- The first-order Pauli–Villars constant `∑_f |c_f B_f| (M_f² - m²)`. -/
noncomputable def constS₁ (P : Params) (μ ν : Fin 4) : ℝ :=
  ∑ f, |P.loopCoeff f * bracketB P μ ν f| * (P.mass f ^ 2 - P.mass 0 ^ 2)

/-- The Feynman mass terms of the flavors are ordered: `W_0 ≤ W_f`. -/
theorem massW_le_massW {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (k : Fin 4 → ℝ) (x : ℝ) (v : Fin 3 → ℝ) (f : Fin 3) :
    SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v
      ≤ SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v := by
  have h1 := massW_sub_massW (P.mass f) (P.mass 0) k x v
  have h2 := mass_sq_le hm hM₁ hM₂ f
  linarith

/-- Second-order cancellation for the closed forms: `‖∑_f c_f z_f^{-3/2}‖ ≤ C λ^{-7/2}`. -/
theorem norm_sum_loopCoeff_cpow_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (k : Fin 4 → ℝ) (x : ℝ) (v : Fin 3 → ℝ) :
    ‖∑ f, (P.loopCoeff f : ℂ) *
        (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
      ≤ 3 / 2 * (3 / 2 + 1) * constS₂ P
        * (max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)) ^ (-(3 / 2 + 2 : ℝ)) := by
  have hc0 := sum_loopCoeff hPV₁
  have hcW : ∑ f, P.loopCoeff f * SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v = 0 := by
    have h : ∀ f, P.loopCoeff f * SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v
        = P.loopCoeff f * SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v
          + P.loopCoeff f * (P.mass f ^ 2 - P.mass 0 ^ 2) := fun f => by
      rw [← massW_sub_massW (P.mass f) (P.mass 0) k x v]
      ring
    simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, hc0, zero_mul, zero_add]
    exact sum_loopCoeff_mul_mass_sq_sub hPV₁ hPV₂
  have b2 := norm_sum_cpow_le_two hε (by norm_num : (0 : ℝ) ≤ 3 / 2) hc0 hcW
    (massW_le_massW hm hM₁ hM₂ k x v)
  have e32 : (-(((3 / 2 : ℝ)) : ℂ)) = -(3 / 2 : ℂ) := by push_cast; ring
  rw [e32] at b2
  simp only [massW_sub_massW] at b2
  exact b2

/-- First-order cancellation for the closed forms: `‖∑_f c_f B_f z_f^{-3/2}‖ ≤ C λ^{-5/2}`. -/
theorem norm_sum_loopCoeff_bracketB_cpow_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) (x : ℝ) (v : Fin 3 → ℝ) :
    ‖∑ f, ((P.loopCoeff f * bracketB P μ ν f : ℝ) : ℂ) *
        (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
      ≤ 3 / 2 * constS₁ P μ ν
        * (max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)) ^ (-(3 / 2 + 1 : ℝ)) := by
  have hcB : ∑ f, P.loopCoeff f * bracketB P μ ν f = 0 := by
    have h : ∀ f, P.loopCoeff f * bracketB P μ ν f
        = -(alpha μ ν + 4 * Minkowski.metric μ ν)
          * (P.loopCoeff f * (P.mass f ^ 2 - P.mass 0 ^ 2)) :=
      fun f => by simp only [bracketB]; ring
    simp only [h, ← Finset.mul_sum, sum_loopCoeff_mul_mass_sq_sub hPV₁ hPV₂, mul_zero]
  have b1 := norm_sum_mul_cpow_le_one hε (by norm_num : (0 : ℝ) ≤ 3 / 2) hcB
    (W := fun f => SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v)
    (massW_le_massW hm hM₁ hM₂ k x v)
  have e32 : (-(((3 / 2 : ℝ)) : ℂ)) = -(3 / 2 : ℂ) := by push_cast; ring
  rw [e32] at b1
  simp only [massW_sub_massW] at b1
  exact b1

/-- The constant of the Pauli–Villars decay bound. -/
noncomputable def constK (P : Params) (k : Fin 4 → ℝ) (μ ν : Fin 4) (c : ℝ) : ℝ :=
  π / 2 * (constA P k μ ν * (3 / 2 * (3 / 2 + 1) * constS₂ P * c ^ (-(3 / 2 + 2 : ℝ)))
    + 3 / 2 * constS₁ P μ ν * c ^ (-(3 / 2 + 1 : ℝ)))

/-- **The Pauli–Villars decay of the closed forms.** Under the Pauli–Villars conditions, if
`max ε W_0 ≥ c (1 + ‖v‖)²`, then `‖∑_f c_f T_f‖ ≤ K (1 + ε) (1 + ‖v‖)⁻⁵`, with `K` depending
only on `c`, the parameters, `k`, `μ` and `ν`. -/
theorem norm_timeSum_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (v : Fin 3 → ℝ)
    (hlow : c * (1 + ‖v‖) ^ 2 ≤ max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)) :
    ‖timeSum P ε k μ ν x v‖ ≤ constK P k μ ν c * (1 + ε) * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  have hu0 : 0 < 1 + ‖v‖ := by positivity
  have hA := norm_bracketA_le P hε k μ ν hx v
  have b2 := norm_sum_loopCoeff_cpow_le hm hM₁ hM₂ hPV₁ hPV₂ hε k x v
  have b1 := norm_sum_loopCoeff_bracketB_cpow_le hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν x v
  have r2 := rpow_neg_le_of_mul_sq_le hc hu0 hlow (r := 3 / 2 + 2) (by norm_num)
  have r1 := rpow_neg_le_of_mul_sq_le hc hu0 hlow (r := 3 / 2 + 1) (by norm_num)
  have hS₂ : 0 ≤ constS₂ P := Finset.sum_nonneg fun f _ => by positivity
  have hS₁ : 0 ≤ constS₁ P μ ν := Finset.sum_nonneg fun f _ =>
    mul_nonneg (abs_nonneg _) (sub_nonneg.2 (mass_sq_le hm hM₁ hM₂ f))
  have hCA : 0 ≤ constA P k μ ν := by unfold constA; positivity
  set Z₂ := ∑ f, (P.loopCoeff f : ℂ) *
    (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
  set Z₁ := ∑ f, ((P.loopCoeff f * bracketB P μ ν f : ℝ) : ℂ) *
    (-(SelfEnergyLimit.massW (P.mass f) (P.mass f) k x v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
  set lam := max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)
  set u := 1 + ‖v‖
  have hu7 : u ^ 2 * u ^ (-(2 * (3 / 2 + 2 : ℝ))) = u ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu0]
    norm_num
  have hu5 : u ^ (-(2 * (3 / 2 + 1 : ℝ))) = u ^ (-(5 : ℝ)) := by norm_num
  have hlam : 0 < lam := lt_max_of_lt_left hε
  have hl2 : 0 ≤ lam ^ (-(3 / 2 + 2 : ℝ)) := by positivity
  have hc2 : 0 ≤ c ^ (-(3 / 2 + 2 : ℝ)) := by positivity
  have hc1 : 0 ≤ c ^ (-(3 / 2 + 1 : ℝ)) := by positivity
  have hu5p : 0 ≤ u ^ (-(5 : ℝ)) := by positivity
  have step1 : ‖bracketA P ε k μ ν x v * Z₂ + Z₁‖
      ≤ constA P k μ ν * (1 + ε) * u ^ 2 * (3 / 2 * (3 / 2 + 1) * constS₂ P *
          lam ^ (-(3 / 2 + 2 : ℝ))) + 3 / 2 * constS₁ P μ ν * lam ^ (-(3 / 2 + 1 : ℝ)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ b1)
    rw [norm_mul]
    exact mul_le_mul hA b2 (norm_nonneg _) (by positivity)
  have step2 : constA P k μ ν * (1 + ε) * u ^ 2 * (3 / 2 * (3 / 2 + 1) * constS₂ P *
          lam ^ (-(3 / 2 + 2 : ℝ))) + 3 / 2 * constS₁ P μ ν * lam ^ (-(3 / 2 + 1 : ℝ))
      ≤ constA P k μ ν * (1 + ε) * (3 / 2 * (3 / 2 + 1) * constS₂ P * c ^ (-(3 / 2 + 2 : ℝ)))
          * (u ^ 2 * u ^ (-(2 * (3 / 2 + 2 : ℝ))))
        + 3 / 2 * constS₁ P μ ν * c ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(2 * (3 / 2 + 1 : ℝ))) := by
    have e1 : constA P k μ ν * (1 + ε) * (3 / 2 * (3 / 2 + 1) * constS₂ P * c ^ (-(3 / 2 + 2 : ℝ)))
          * (u ^ 2 * u ^ (-(2 * (3 / 2 + 2 : ℝ))))
        = constA P k μ ν * (1 + ε) * u ^ 2 * (3 / 2 * (3 / 2 + 1) * constS₂ P *
          (c ^ (-(3 / 2 + 2 : ℝ)) * u ^ (-(2 * (3 / 2 + 2 : ℝ))))) := by ring
    have e2 : 3 / 2 * constS₁ P μ ν * c ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(2 * (3 / 2 + 1 : ℝ)))
        = 3 / 2 * constS₁ P μ ν * (c ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(2 * (3 / 2 + 1 : ℝ)))) := by
      ring
    rw [e1, e2]
    gcongr
  rw [hu7, hu5] at step2
  rw [timeSum_eq, norm_mul, SelfEnergyLimit.norm_ofReal_div_two_pi]
  refine (mul_le_mul_of_nonneg_left (step1.trans step2) (by positivity)).trans ?_
  have hS : 0 ≤ 3 / 2 * constS₁ P μ ν * c ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by positivity
  have e : constK P k μ ν c * (1 + ε) * u ^ (-(5 : ℝ))
      = π / 2 * (constA P k μ ν * (1 + ε) * (3 / 2 * (3 / 2 + 1) * constS₂ P
          * c ^ (-(3 / 2 + 2 : ℝ))) * u ^ (-(5 : ℝ))
        + 3 / 2 * constS₁ P μ ν * c ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ))
        + ε * (3 / 2 * constS₁ P μ ν * c ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)))) := by
    simp only [constK]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hε.le hS)) (by positivity)

/-- The constant of the decay bound is nonnegative. -/
theorem constK_nonneg {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) {c : ℝ} (hc : 0 < c) : 0 ≤ constK P k μ ν c := by
  have hS₂ : 0 ≤ constS₂ P := Finset.sum_nonneg fun f _ => by positivity
  have hS₁ : 0 ≤ constS₁ P μ ν := Finset.sum_nonneg fun f _ =>
    mul_nonneg (abs_nonneg _) (sub_nonneg.2 (mass_sq_le hm hM₁ hM₂ f))
  have hCA : 0 ≤ constA P k μ ν := by unfold constA; positivity
  unfold constK
  positivity

/-! ### Lower bounds on the Feynman mass term -/

/-- **Below the pair threshold** `k² > -4m²`, `W_0 ≥ c (1 + ‖v‖)²` uniformly in `x ∈ [0, 1]`. -/
theorem exists_mul_le_massW_of_threshold {P : Params} (hm : 0 < P.m) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) :
    ∃ c > 0, ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      c * (1 + ‖v‖) ^ 2 ≤ SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v := by
  have h0 : P.mass 0 = P.m := rfl
  have hs : -(P.mass 0 + P.mass 0) ^ 2 < Minkowski.dot k k := by
    rw [h0]
    nlinarith
  obtain ⟨D₀, hD₀, hle⟩ := exists_pos_le_selfEnergyFeynmanMass (h0 ▸ hm) (h0 ▸ hm) hs
  obtain ⟨c, hc, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) ‖k‖ hD₀
  exact ⟨c, hc, fun x hx v => hcoer v _ _ (norm_shift_le k hx) (hle x hx)⟩

/-- **For each `ε > 0`**, whatever `k`, `max ε W_0 ≥ c (1 + ‖v‖)²` uniformly in `x ∈ [0, 1]`. -/
theorem exists_mul_le_max_massW (P : Params) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    ∃ c > 0, ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      c * (1 + ‖v‖) ^ 2 ≤ max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v) := by
  obtain ⟨c₀, hc₀, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) ‖k‖ one_pos
  have hK : 0 < 1 + |Minkowski.dot k k| := by positivity
  refine ⟨min (c₀ / 2) (ε * c₀ / (2 * (1 + |Minkowski.dot k k|))), by positivity,
    fun x hx v => ?_⟩
  have h1 := hcoer v (fun i => x * k i.succ) 1 (norm_shift_le k hx) le_rfl
  have hD : -|Minkowski.dot k k|
      ≤ selfEnergyFeynmanMass (P.mass 0) (P.mass 0) (Minkowski.dot k k) x := by
    have e : selfEnergyFeynmanMass (P.mass 0) (P.mass 0) (Minkowski.dot k k) x
        = P.mass 0 ^ 2 + x * (1 - x) * Minkowski.dot k k := by
      unfold selfEnergyFeynmanMass
      ring
    rw [e]
    have hx1 : 0 ≤ x * (1 - x) := by nlinarith [hx.1, hx.2]
    have hx2 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
    have h3 := mul_le_mul_of_nonneg_left (neg_abs_le (Minkowski.dot k k)) hx1
    nlinarith [abs_nonneg (Minkowski.dot k k), sq_nonneg (P.mass 0)]
  have hW : c₀ * (1 + ‖v‖) ^ 2 - (1 + |Minkowski.dot k k|)
      ≤ SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v := by
    simp only [SelfEnergyLimit.massW]
    linarith
  rcases le_or_gt (2 * (1 + |Minkowski.dot k k|)) (c₀ * (1 + ‖v‖) ^ 2) with h | h
  · calc min (c₀ / 2) (ε * c₀ / (2 * (1 + |Minkowski.dot k k|))) * (1 + ‖v‖) ^ 2
        ≤ c₀ / 2 * (1 + ‖v‖) ^ 2 := by gcongr; exact min_le_left _ _
      _ ≤ SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v := by linarith
      _ ≤ _ := le_max_right _ _
  · calc min (c₀ / 2) (ε * c₀ / (2 * (1 + |Minkowski.dot k k|))) * (1 + ‖v‖) ^ 2
        ≤ ε * c₀ / (2 * (1 + |Minkowski.dot k k|)) * (1 + ‖v‖) ^ 2 := by
          gcongr
          exact min_le_right _ _
      _ = ε * (c₀ * (1 + ‖v‖) ^ 2 / (2 * (1 + |Minkowski.dot k k|))) := by ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          exact h.le
      _ = ε := mul_one ε
      _ ≤ _ := le_max_left _ _

/-! ### Integrability of the energy integral -/

/-- For `ε > 0` the Pauli–Villars sum of closed forms is jointly continuous in `(v⃗, x)`. -/
theorem continuous_timeSum {ε : ℝ} (hε : 0 < ε) (P : Params) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    Continuous fun q : (Fin 3 → ℝ) × ℝ => timeSum P ε k μ ν q.2 q.1 := by
  unfold timeSum
  exact continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_timeT hε _ k μ ν)

/-- The bound on `spatialG ε`. -/
theorem norm_spatialG_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ)
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1,
      c * (1 + ‖v‖) ^ 2 ≤ max ε (SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v)) :
    ‖spatialG P ε k μ ν v‖ ≤ ‖kappa P.e‖ * (constK P k μ ν c * (1 + ε) * (1 + ‖v‖) ^ (-(5 : ℝ)))
      * (volume.restrict (Ioc (0 : ℝ) 1)).real univ :=
  norm_integral_le_of_norm_le_const ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε
      (Ioc_subset_Icc_self hx) v (hlow x (Ioc_subset_Icc_self hx))) (norm_nonneg _))

/-- **For each `ε > 0` and every `k`, the energy integral is integrable in the spatial
momentum**, under the Pauli–Villars conditions. -/
theorem integrable_spatialG {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) : Integrable (spatialG P ε k μ ν) := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_le_max_massW P hε k
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (‖kappa P.e‖ * (constK P k μ ν c * (1 + ε))
      * (volume.restrict (Ioc (0 : ℝ) 1)).real univ)
  refine hbnd.mono' (aestronglyMeasurable_spatialG hε P k μ ν)
    (Eventually.of_forall fun v => ?_)
  refine (norm_spatialG_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε v fun x hx => hlow x hx v).trans
    (le_of_eq ?_)
  ring

/-- **The energy integral is integrable in the spatial momentum** for `ε > 0` and every `k`. -/
theorem integrable_integral_vacuumPolarizationIntegrand {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, vacuumPolarizationIntegrand P ε k (Fin.cons t v) μ ν :=
  (integrable_spatialG hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν).congr
    (Eventually.of_forall fun v => (integral_vacuumPolarizationIntegrand_time hε P k μ ν v).symm)

/-! ### Step 3: dominated convergence -/

/-- For a positive mass term, the closed form converges as `ε → 0⁺`. -/
theorem tendsto_timeT {M : ℝ} {k : Fin 4 → ℝ} (μ ν : Fin 4) {x : ℝ} {v : Fin 3 → ℝ}
    (hW : 0 < SelfEnergyLimit.massW M M k x v) :
    Tendsto (fun ε : ℝ => timeT M ε k μ ν x v) (𝓝[>] 0) (𝓝 (timeT M 0 k μ ν x v)) := by
  set W := SelfEnergyLimit.massW M M k x v
  have h1 := tendsto_cpow_neg_add_mul_I hW (-(3 / 2 : ℂ))
  have hc : Continuous fun ε : ℝ => (alpha μ ν : ℂ) * (-(W : ℂ) + ε * I)
      + (numer M k (Fin.cons (-(x * k 0)) v) μ ν : ℂ) := by fun_prop
  have h2 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h0 : timeT M 0 k μ ν x v = (π / 2 : ℂ) * (-(W : ℂ)) ^ (-(3 / 2 : ℂ)) *
      ((alpha μ ν : ℂ) * (-(W : ℂ) + ((0 : ℝ) : ℂ) * I)
        + (numer M k (Fin.cons (-(x * k 0)) v) μ ν : ℂ)) := by
    simp only [timeT, ofReal_zero, zero_mul, add_zero, W]
  rw [h0]
  exact (h1.const_mul _).mul h2

/-- Below threshold, the Pauli–Villars sum of the closed forms converges as `ε → 0⁺`. -/
theorem tendsto_timeSum {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    {k : Fin 4 → ℝ} (μ ν : Fin 4) {x : ℝ} {v : Fin 3 → ℝ}
    (hW : 0 < SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v) :
    Tendsto (fun ε : ℝ => timeSum P ε k μ ν x v) (𝓝[>] 0) (𝓝 (timeSum P 0 k μ ν x v)) := by
  unfold timeSum
  exact tendsto_finsetSum _ fun f _ => (tendsto_timeT μ ν
    (hW.trans_le (massW_le_massW hm hM₁ hM₂ k x v f))).const_mul _

/-- **The uniform bound at `ε = 0`**, below threshold. -/
theorem norm_timeSum_zero_le {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {k : Fin 4 → ℝ} (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeSum P 0 k μ ν x v‖ ≤ K * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_le_massW_of_threshold hm hk
  refine ⟨constK P k μ ν c, constK_nonneg hm hM₁ hM₂ k μ ν hc, fun x hx v => ?_⟩
  have hW : 0 < SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v :=
    lt_of_lt_of_le (by positivity) (hlow x hx v)
  have hlim := (tendsto_timeSum hm hM₁ hM₂ μ ν hW).norm
  have hb : Tendsto (fun ε : ℝ => constK P k μ ν c * (1 + ε) * (1 + ‖v‖) ^ (-(5 : ℝ)))
      (𝓝[>] 0) (𝓝 (constK P k μ ν c * (1 + 0) * (1 + ‖v‖) ^ (-(5 : ℝ)))) :=
    ((((continuous_const.add continuous_id).tendsto 0).const_mul _).mul_const _).mono_left
      nhdsWithin_le_nhds
  have h := le_of_tendsto_of_tendsto hlim hb (eventually_nhdsWithin_of_forall fun ε hε =>
    norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε hx v
      ((hlow x hx v).trans (le_max_right _ _)))
  simpa using h

/-- Below threshold, `spatialG ε v → spatialG 0 v` as `ε → 0⁺`, by dominated convergence over
the Feynman parameter. -/
theorem tendsto_spatialG {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {k : Fin 4 → ℝ} (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) (v : Fin 3 → ℝ) :
    Tendsto (fun ε : ℝ => spatialG P ε k μ ν v) (𝓝[>] 0) (𝓝 (spatialG P 0 k μ ν v)) := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_le_massW_of_threshold hm hk
  have hK := constK_nonneg hm hM₁ hM₂ k μ ν hc
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => ‖kappa P.e‖ * (constK P k μ ν c * 2)) ?_ ?_ (integrable_const _) ?_
  · refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    exact (continuous_const.mul ((continuous_timeSum hε P k μ ν).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    have hxI := Ioc_subset_Icc_self hx
    have hb := norm_timeSum_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε.1 hxI v
      ((hlow x hxI v).trans (le_max_right _ _))
    have hu : (1 + ‖v‖) ^ (-(5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
    have hu0 : 0 ≤ (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hb.trans ?_) (norm_nonneg _)
    calc constK P k μ ν c * (1 + ε) * (1 + ‖v‖) ^ (-(5 : ℝ))
        ≤ constK P k μ ν c * 2 * 1 := by
          gcongr
          linarith [hε.2]
      _ = _ := mul_one _
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    have hxI := Ioc_subset_Icc_self hx
    have hW : 0 < SelfEnergyLimit.massW (P.mass 0) (P.mass 0) k x v :=
      lt_of_lt_of_le (by positivity) (hlow x hxI v)
    exact (tendsto_timeSum hm hM₁ hM₂ μ ν hW).const_mul _

/-- **The limit of the energy-first integral below threshold**: as `ε → 0⁺`, the energy-first
integral of the integrand converges to `∫ v, spatialG 0 v`. -/
theorem tendsto_energyFirstIntegral_spatialG {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vacuumPolarizationIntegrand P ε k ℓ μ ν)
      (𝓝[>] 0) (𝓝 (∫ v, spatialG P 0 k μ ν v)) := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_le_massW_of_threshold hm hk
  have hK := constK_nonneg hm hM₁ hM₂ k μ ν hc
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (‖kappa P.e‖ * (constK P k μ ν c * 2)
      * (volume.restrict (Ioc (0 : ℝ) 1)).real univ)
  have hlim : Tendsto (fun ε : ℝ => ∫ v, spatialG P ε k μ ν v) (𝓝[>] 0)
      (𝓝 (∫ v, spatialG P 0 k μ ν v)) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (eventually_nhdsWithin_of_forall fun ε hε => aestronglyMeasurable_spatialG hε P k μ ν)
      ?_ hbnd (Eventually.of_forall fun v => tendsto_spatialG hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν v)
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    refine Eventually.of_forall fun v => ?_
    have hb := norm_spatialG_le hm hM₁ hM₂ hPV₁ hPV₂ k μ ν hc hε.1 v
      fun x hx => (hlow x hx v).trans (le_max_right _ _)
    have hu0 : 0 ≤ (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
    have hvol : 0 ≤ (volume.restrict (Ioc (0 : ℝ) 1)).real univ := measureReal_nonneg
    refine hb.trans ?_
    have h2 : constK P k μ ν c * (1 + ε) ≤ constK P k μ ν c * 2 := by
      gcongr
      linarith [hε.2]
    calc ‖kappa P.e‖ * (constK P k μ ν c * (1 + ε) * (1 + ‖v‖) ^ (-(5 : ℝ)))
          * (volume.restrict (Ioc (0 : ℝ) 1)).real univ
        ≤ ‖kappa P.e‖ * (constK P k μ ν c * 2 * (1 + ‖v‖) ^ (-(5 : ℝ)))
          * (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by gcongr
      _ = _ := by ring
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  simp only [energyFirstIntegral]
  exact (integral_congr_ae (Eventually.of_forall fun v =>
    integral_vacuumPolarizationIntegrand_time hε P k μ ν v)).symm

end VacuumPolarizationLimit

end QED.WickModel

end
