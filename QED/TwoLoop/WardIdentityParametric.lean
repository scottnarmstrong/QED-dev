/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ElectronOnShell
public import QED.OneLoop.ChargeCondition
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop Ward identity on the Feynman-parameter closed forms

At fixed regulators `m, m_γ, Λ > 0`, the counterterm `δ₂ = onShellδ₂ P` fixed by the electron
on-shell conditions and the value `A₀ = chargeA0` of the one-loop vertex's `γ^μ` coefficient at
`q² = 0` (which fixes `Z₁ = 1 - A₀` by the charge condition) satisfy `A₀ = -δ₂`. This is the
Ward identity `Z₁ = Z₂` of the primary source's (68.13), proved directly on the parametric
closed forms, at `ε = 0`, without differentiating the regulated integrals at `ε > 0`.

Write `D_M(x) = x m² + (1 - x) M² - x (1 - x) m² = x² m² + (1 - x) M²` for the self-energy
Feynman mass at `p² = -m²` (it is also the vertex Feynman mass at `q² = 0`, with `x` the vertex
parameter `y`), and `L(x) = log (D_Λ(x) / D_{m_γ}(x))`. Then, with `c = e² / 8π²`,

* `A₀ = c ∫₀¹ x (L(x) + (x² + 2x - 2) m² (1/D_{m_γ} - 1/D_Λ)) dx`,
* `δ₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)
      = -c (∫₀¹ (1 - x) L(x) dx + 2m² ∫₀¹ x (1 - x)(1 + x) (1/D_Λ - 1/D_{m_γ}) dx)`,

and `A₀ + δ₂ = c ∫₀¹ ((2x - 1) L(x) + m² (2x² - x³)(1/D_{m_γ} - 1/D_Λ)) dx`. The integrand is
the derivative of `(x² - x) L(x)`, which vanishes at both ends: this uses
`(x² - x) D_M'(x) = x D_M(x) - m² (2x² - x³)`, for each mass `M` separately, so the identity
holds for each Pauli–Villars term.

## Main statements

* `QED.TwoLoop.Ward.hasDerivAt_integral_mul_log`: differentiation under the integral sign of the
  self-energy coefficients at `s = -m²`.
* `QED.TwoLoop.Ward.integral_wardIntegrand_eq_zero`: the integral of the total derivative above
  vanishes.
* `QED.TwoLoop.Ward.chargeA0_eq_neg_onShellδ₂`: the parametric Ward identity `A₀ = -δ₂`.
* `QED.TwoLoop.Ward.chargeZ_eq_one_add_onShellδ₂`: `Z₁ = 1 + δ₂`, i.e. `Z₁ = Z₂`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open QED.WickModel QED.OneLoop.VertexLimit QED.Integration
open scoped Real Interval

namespace QED.TwoLoop.Ward

/-! ### The Feynman mass near `p² = -m²` -/

/-- A uniform lower bound for the self-energy Feynman mass near `s = -m²`: if `c ≤ m²/4`,
`c ≤ M²/2` and `|s + m²| < c`, then `D_M(s, x) ≥ c/2` on `[0, 1]`. -/
theorem half_le_selfEnergyFeynmanMass {m M c s x : ℝ} (hcm : c ≤ m ^ 2 / 4)
    (hcM : c ≤ M ^ 2 / 2) (hx : x ∈ Icc (0 : ℝ) 1) (hs : |s + m ^ 2| < c) :
    c / 2 ≤ selfEnergyFeynmanMass m M s x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hs.le
  have hsplit : selfEnergyFeynmanMass m M s x
      = x ^ 2 * m ^ 2 + (1 - x) * M ^ 2 + x * (1 - x) * (s + m ^ 2) := by
    unfold selfEnergyFeynmanMass; ring
  have key : c ≤ x ^ 2 * m ^ 2 + (1 - x) * M ^ 2 := by
    rcases le_total x (1 / 2) with h | h
    · have h1 : M ^ 2 / 2 ≤ (1 - x) * M ^ 2 := by nlinarith [sq_nonneg M]
      nlinarith [sq_nonneg (x * m)]
    · have hx2 : 1 / 4 ≤ x ^ 2 := by nlinarith
      have h1 : m ^ 2 / 4 ≤ x ^ 2 * m ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg m)]
      nlinarith [sq_nonneg M]
  have h2 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have h3 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have h4 : 0 ≤ x * (1 - x) * (s + m ^ 2 + c) :=
    mul_nonneg h2 (by linarith [(abs_lt.mp hs).1])
  have h5 : x * (1 - x) * c ≤ 1 / 4 * c := mul_le_mul_of_nonneg_right h3 hc0
  rw [hsplit]
  nlinarith

/-- The self-energy Feynman mass at `s = -m²` is positive on `[0, 1]`. -/
theorem selfEnergyFeynmanMass_onShell_pos {m M x : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 < selfEnergyFeynmanMass m M (-m ^ 2) x :=
  selfEnergyFeynmanMass_pos hm hM (by nlinarith) hx

/-- The self-energy Feynman mass is continuous in the Feynman parameter. -/
theorem continuous_selfEnergyFeynmanMass (m M s : ℝ) :
    Continuous fun x => selfEnergyFeynmanMass m M s x := by
  unfold selfEnergyFeynmanMass; fun_prop

/-- The `s`-derivative of the self-energy Feynman mass. -/
theorem hasDerivAt_selfEnergyFeynmanMass_left (m M x s : ℝ) :
    HasDerivAt (fun s => selfEnergyFeynmanMass m M s x) (x * (1 - x)) s := by
  have h := ((hasDerivAt_id s).const_mul (x * (1 - x))).const_add (x * m ^ 2 + (1 - x) * M ^ 2)
  convert h using 1
  · funext t; simp only [selfEnergyFeynmanMass, id]
  · ring

/-- The `x`-derivative of the self-energy Feynman mass at `s = -m²`. -/
theorem hasDerivAt_selfEnergyFeynmanMass_onShell (m M x : ℝ) :
    HasDerivAt (fun x => selfEnergyFeynmanMass m M (-m ^ 2) x) (2 * x * m ^ 2 - M ^ 2) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (m ^ 2)).sub
    ((hasDerivAt_id x).const_mul (M ^ 2))).add_const (M ^ 2)
  convert h using 1
  · funext t; simp only [selfEnergyFeynmanMass, Pi.sub_apply, id]; ring
  · norm_num; ring

/-! ### Differentiation of the self-energy coefficients at `p² = -m²` -/

/-- **Differentiation under the integral sign at `s = -m²`.** For `m, m_γ, Λ > 0` and a
continuous weight `w` with `|w| ≤ 1` on `[0, 1]`, the function
`s ↦ ∫₀¹ w(x) log (D_Λ(s, x) / D_{m_γ}(s, x)) dx` has derivative
`∫₀¹ w(x) (x (1 - x) / D_Λ(-m², x) - x (1 - x) / D_{m_γ}(-m², x)) dx` at `s = -m²`. -/
theorem hasDerivAt_integral_mul_log {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {w : ℝ → ℝ} (hw : Continuous w) (hw1 : ∀ x ∈ Icc (0 : ℝ) 1, |w x| ≤ 1) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..1, w x *
        Real.log (selfEnergyFeynmanMass m Λ s x / selfEnergyFeynmanMass m mγ s x))
      (∫ x in (0 : ℝ)..1, w x *
        (x * (1 - x) / selfEnergyFeynmanMass m Λ (-m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass m mγ (-m ^ 2) x)) (-m ^ 2) := by
  set c : ℝ := min (m ^ 2 / 4) (min (mγ ^ 2 / 2) (Λ ^ 2 / 2)) with hc
  have hc0 : 0 < c := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hcm : c ≤ m ^ 2 / 4 := min_le_left _ _
  have hcγ : c ≤ mγ ^ 2 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcΛ : c ≤ Λ ^ 2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  -- On the ball `|s + m²| < c` both Feynman masses are at least `c / 2` on `[0, 1]`.
  have hlow : ∀ M : ℝ, c ≤ M ^ 2 / 2 → ∀ s ∈ ball (-m ^ 2) c, ∀ x ∈ Icc (0 : ℝ) 1,
      c / 2 ≤ selfEnergyFeynmanMass m M s x := by
    intro M hcM s hs x hx
    refine half_le_selfEnergyFeynmanMass hcm hcM hx ?_
    rw [mem_ball, Real.dist_eq] at hs
    simpa [sub_neg_eq_add] using hs
  have hpos : ∀ M : ℝ, c ≤ M ^ 2 / 2 → ∀ s ∈ ball (-m ^ 2) c, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < selfEnergyFeynmanMass m M s x := fun M hcM s hs x hx =>
    (half_pos hc0).trans_le (hlow M hcM s hs x hx)
  have hmeas : ∀ s : ℝ, Measurable fun x => w x *
      Real.log (selfEnergyFeynmanMass m Λ s x / selfEnergyFeynmanMass m mγ s x) := fun s =>
    hw.measurable.mul (Real.measurable_log.comp
      ((continuous_selfEnergyFeynmanMass m Λ s).measurable.div
        (continuous_selfEnergyFeynmanMass m mγ s).measurable))
  have hcenter : -m ^ 2 ∈ ball (-m ^ 2) c := mem_ball_self hc0
  have hF_int : IntervalIntegrable (fun x => w x *
      Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x / selfEnergyFeynmanMass m mγ (-m ^ 2) x))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    refine hw.continuousOn.mul (ContinuousOn.log ?_ fun x hx => ?_)
    · exact (continuous_selfEnergyFeynmanMass m Λ _).continuousOn.div
        (continuous_selfEnergyFeynmanMass m mγ _).continuousOn fun x hx =>
          (hpos mγ hcγ _ hcenter x hx).ne'
    · exact (div_pos (hpos Λ hcΛ _ hcenter x hx) (hpos mγ hcγ _ hcenter x hx)).ne'
  have hF'_meas : AEStronglyMeasurable (fun x => w x *
      (x * (1 - x) / selfEnergyFeynmanMass m Λ (-m ^ 2) x
        - x * (1 - x) / selfEnergyFeynmanMass m mγ (-m ^ 2) x))
      (volume.restrict (Ι (0 : ℝ) 1)) :=
    (hw.measurable.mul
      (((by fun_prop : Continuous fun x : ℝ => x * (1 - x)).measurable.div
        (continuous_selfEnergyFeynmanMass m Λ _).measurable).sub
      ((by fun_prop : Continuous fun x : ℝ => x * (1 - x)).measurable.div
        (continuous_selfEnergyFeynmanMass m mγ _).measurable))).aestronglyMeasurable
  have hbound : ∀ M : ℝ, c ≤ M ^ 2 / 2 → ∀ s ∈ ball (-m ^ 2) c, ∀ x ∈ Icc (0 : ℝ) 1,
      |x * (1 - x) / selfEnergyFeynmanMass m M s x| ≤ 2 / c := by
    intro M hcM s hs x hx
    have hD := hlow M hcM s hs x hx
    have hD0 := hpos M hcM s hs x hx
    have h2 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
    have h3 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
    rw [abs_of_nonneg (div_nonneg h2 hD0.le), div_le_div_iff₀ hD0 hc0]
    nlinarith
  have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1)
    (F := fun s x => w x *
      Real.log (selfEnergyFeynmanMass m Λ s x / selfEnergyFeynmanMass m mγ s x))
    (F' := fun s x => w x * (x * (1 - x) / selfEnergyFeynmanMass m Λ s x
      - x * (1 - x) / selfEnergyFeynmanMass m mγ s x))
    (bound := fun _ => 4 / c) (ball_mem_nhds _ hc0)
    (Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) hF_int hF'_meas
    ?_ intervalIntegrable_const ?_
  · exact hres.2
  · refine ae_of_all _ fun x hx s hs => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have hw' := hw1 x hx'
    have hΛb := hbound Λ hcΛ s hs x hx'
    have hγb := hbound mγ hcγ s hs x hx'
    rw [Real.norm_eq_abs, abs_mul]
    calc |w x| * |x * (1 - x) / selfEnergyFeynmanMass m Λ s x
          - x * (1 - x) / selfEnergyFeynmanMass m mγ s x|
        ≤ 1 * (2 / c + 2 / c) :=
          mul_le_mul hw' ((abs_sub _ _).trans (add_le_add hΛb hγb)) (abs_nonneg _) zero_le_one
      _ = 4 / c := by ring
  · refine ae_of_all _ fun x hx s hs => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have hΛ0 := (hpos Λ hcΛ s hs x hx').ne'
    have hγ0 := (hpos mγ hcγ s hs x hx').ne'
    have h := (((hasDerivAt_selfEnergyFeynmanMass_left m Λ x s).div
      (hasDerivAt_selfEnergyFeynmanMass_left m mγ x s) hγ0).log
      (div_ne_zero hΛ0 hγ0)).const_mul (w x)
    simp only [Pi.div_apply] at h
    refine h.congr_deriv ?_
    field_simp

/-! ### Continuity on `[0, 1]` at `p² = -m²` -/

section OnShell

variable {m mγ Λ M : ℝ}

/-- The paired logarithm `L(x) = log (D_Λ(x) / D_{m_γ}(x))` is continuous on `[0, 1]`. -/
theorem continuousOn_log_onShell (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ContinuousOn (fun x => Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x
      / selfEnergyFeynmanMass m mγ (-m ^ 2) x)) (Icc (0 : ℝ) 1) :=
  ((continuous_selfEnergyFeynmanMass m Λ _).continuousOn.div
    (continuous_selfEnergyFeynmanMass m mγ _).continuousOn fun _ hx =>
      (selfEnergyFeynmanMass_onShell_pos hm hmγ hx).ne').log fun _ hx =>
    (div_pos (selfEnergyFeynmanMass_onShell_pos hm hΛ hx)
      (selfEnergyFeynmanMass_onShell_pos hm hmγ hx)).ne'

/-- `1 / D_M(x)` is continuous on `[0, 1]`. -/
theorem continuousOn_inv_onShell (hm : 0 < m) (hM : 0 < M) :
    ContinuousOn (fun x => (selfEnergyFeynmanMass m M (-m ^ 2) x)⁻¹) (Icc (0 : ℝ) 1) :=
  (continuous_selfEnergyFeynmanMass m M _).continuousOn.inv₀ fun _ hx =>
    (selfEnergyFeynmanMass_onShell_pos hm hM hx).ne'

/-- `x (1 - x) / D_M(x)` is continuous on `[0, 1]`. -/
theorem continuousOn_div_onShell (hm : 0 < m) (hM : 0 < M) :
    ContinuousOn (fun x => x * (1 - x) / selfEnergyFeynmanMass m M (-m ^ 2) x)
      (Icc (0 : ℝ) 1) :=
  (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).continuousOn.div
    (continuous_selfEnergyFeynmanMass m M _).continuousOn fun _ hx =>
      (selfEnergyFeynmanMass_onShell_pos hm hM hx).ne'

/-- A function continuous on `[0, 1]` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    IntervalIntegrable f volume 0 1 :=
  ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le zero_le_one])

end OnShell

/-! ### The total derivative -/

/-- **The Ward integrand is a total derivative.** For `m, m_γ, Λ > 0`,
`∫₀¹ ((2x - 1) L(x) + m² (2x² - x³)(1/D_{m_γ}(x) - 1/D_Λ(x))) dx = 0`, since the integrand is
the derivative of `(x² - x) L(x)`. -/
theorem integral_wardIntegrand_eq_zero {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) :
    ∫ x in (0 : ℝ)..1, ((2 * x - 1) * Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x
        / selfEnergyFeynmanMass m mγ (-m ^ 2) x)
      + m ^ 2 * (2 * x ^ 2 - x ^ 3) * ((selfEnergyFeynmanMass m mγ (-m ^ 2) x)⁻¹
        - (selfEnergyFeynmanMass m Λ (-m ^ 2) x)⁻¹)) = 0 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => (x ^ 2 - x) *
      Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x / selfEnergyFeynmanMass m mγ (-m ^ 2) x))
      ((2 * x - 1) * Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x
          / selfEnergyFeynmanMass m mγ (-m ^ 2) x)
        + m ^ 2 * (2 * x ^ 2 - x ^ 3) * ((selfEnergyFeynmanMass m mγ (-m ^ 2) x)⁻¹
          - (selfEnergyFeynmanMass m Λ (-m ^ 2) x)⁻¹)) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hΛ0 := (selfEnergyFeynmanMass_onShell_pos hm hΛ hx).ne'
    have hγ0 := (selfEnergyFeynmanMass_onShell_pos hm hmγ hx).ne'
    have h := ((hasDerivAt_pow 2 x).sub (hasDerivAt_id x)).mul
      (((hasDerivAt_selfEnergyFeynmanMass_onShell m Λ x).div
        (hasDerivAt_selfEnergyFeynmanMass_onShell m mγ x) hγ0).log (div_ne_zero hΛ0 hγ0))
    simp only [Pi.div_apply, Pi.sub_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
    refine h.congr_deriv ?_
    set L := Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x
      / selfEnergyFeynmanMass m mγ (-m ^ 2) x)
    field_simp
    simp only [selfEnergyFeynmanMass]
    ring
  have hint : IntervalIntegrable (fun x => (2 * x - 1) *
      Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) x / selfEnergyFeynmanMass m mγ (-m ^ 2) x)
      + m ^ 2 * (2 * x ^ 2 - x ^ 3) * ((selfEnergyFeynmanMass m mγ (-m ^ 2) x)⁻¹
        - (selfEnergyFeynmanMass m Λ (-m ^ 2) x)⁻¹)) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc
      (((by fun_prop : Continuous fun x : ℝ => 2 * x - 1).continuousOn.mul
        (continuousOn_log_onShell hm hmγ hΛ)).add
      ((by fun_prop : Continuous fun x : ℝ => m ^ 2 * (2 * x ^ 2 - x ^ 3)).continuousOn.mul
        ((continuousOn_inv_onShell hm hmγ).sub (continuousOn_inv_onShell hm hΛ))))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-! ### The two closed forms -/

/-- **The vertex's `γ^μ` coefficient at `q² = 0` as a one-dimensional integral.** The integrand
of `A(0)` depends only on the parameter `y`, and its mass term is the self-energy Feynman mass
at `p² = -m²`: `∫ dF A(0) = ∫₀¹ 2y (L(y) + (y² + 2y - 2) m² (1/D_{m_γ}(y) - 1/D_Λ(y))) dy`, in
the source's form `1 - 4(1 - y) + (1 - y)² = y² + 2y - 2`. -/
theorem integral_formIntegrandAq_zero (m mγ Λ : ℝ) :
    ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure
      = ∫ y in (0 : ℝ)..1, 2 * y * (Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) y
          / selfEnergyFeynmanMass m mγ (-m ^ 2) y)
        + 1 / 2 * ((selfEnergyFeynmanMass m mγ (-m ^ 2) y)⁻¹
          - (selfEnergyFeynmanMass m Λ (-m ^ 2) y)⁻¹)
          * (2 * ((1 - 4 * (1 - y) + (1 - y) ^ 2) * m ^ 2))) := by
  have hD : ∀ (M : ℝ) (z : ℝ × ℝ), massDq m M 0 z = selfEnergyFeynmanMass m M (-m ^ 2) z.2 := by
    intro M z
    unfold massDq selfEnergyFeynmanMass
    ring
  set g : ℝ → ℝ := fun y => 2 * y * (Real.log (selfEnergyFeynmanMass m Λ (-m ^ 2) y
          / selfEnergyFeynmanMass m mγ (-m ^ 2) y)
        + 1 / 2 * ((selfEnergyFeynmanMass m mγ (-m ^ 2) y)⁻¹
          - (selfEnergyFeynmanMass m Λ (-m ^ 2) y)⁻¹)
          * (2 * ((1 - 4 * (1 - y) + (1 - y) ^ 2) * m ^ 2))) with hg
  have h : (fun z => formIntegrandAq m mγ Λ 0 z) = fun z : ℝ × ℝ => g z.2 := by
    funext z
    simp only [hg, formIntegrandAq, hD, mul_zero, sub_zero]
  rw [h, feynmanMeasure, integral_fun_snd g, intervalIntegral.integral_of_le zero_le_one]
  simp [Measure.real, hg]

/-- `|1 - x| ≤ 1` on `[0, 1]`. -/
theorem abs_one_sub_le_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |1 - x| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- **The on-shell `δ₂` in closed form.** For `m, m_γ, Λ > 0`,
`δ₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)` with
`A(-m²) = -(e²/8π²) ∫₀¹ (1 - x) L`, `A'(-m²) = -(e²/8π²) ∫₀¹ (1 - x) k`,
`B'(-m²) = -(e²/4π²) ∫₀¹ k`, where `k(x) = x (1 - x) (1/D_Λ(x) - 1/D_{m_γ}(x))`. -/
theorem onShellδ₂_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    onShellδ₂ P = -(P.e ^ 2 / (8 * π ^ 2)) * (∫ x in (0 : ℝ)..1, (1 - x) *
        Real.log (selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x))
      - 2 * P.m ^ 2 * (-(P.e ^ 2 / (8 * π ^ 2)) * ∫ x in (0 : ℝ)..1, (1 - x) *
        (x * (1 - x) / selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x))
      + 2 * P.m ^ 2 * (-(P.e ^ 2 / (4 * π ^ 2)) * ∫ x in (0 : ℝ)..1,
        (x * (1 - x) / selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)) := by
  have hA := (hasDerivAt_integral_mul_log hm hmγ hΛ (w := fun x => 1 - x) (by fun_prop)
    fun _ hx => abs_one_sub_le_one hx).const_mul (-(P.e ^ 2 / (8 * π ^ 2)))
  have hB := (hasDerivAt_integral_mul_log hm hmγ hΛ (w := fun _ => 1) continuous_const
    fun _ _ => by simp).const_mul (-(P.e ^ 2 / (4 * π ^ 2)))
  simp only [one_mul] at hB
  have hA' : deriv (fun s => (selfEnergyLoopA P s).re) (-P.m ^ 2)
      = -(P.e ^ 2 / (8 * π ^ 2)) * ∫ x in (0 : ℝ)..1, (1 - x) *
        (x * (1 - x) / selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x) := by
    simp only [selfEnergyLoopA, Complex.ofReal_re]
    exact hA.deriv
  have hB' : deriv (fun s => (selfEnergyLoopB P s).re) (-P.m ^ 2)
      = -(P.e ^ 2 / (4 * π ^ 2)) * ∫ x in (0 : ℝ)..1,
        (x * (1 - x) / selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x) := by
    simp only [selfEnergyLoopB, Complex.ofReal_re]
    exact hB.deriv
  rw [onShellδ₂, hA', hB']
  simp only [selfEnergyLoopA, Complex.ofReal_re]

/-- **The parametric Ward identity.** For `m, m_γ, Λ > 0`, the value `A₀ = chargeA0` of the
one-loop vertex's `γ^μ` coefficient at `q² = 0` is minus the counterterm `δ₂ = onShellδ₂ P`
fixed by the electron on-shell conditions: `A₀ = -δ₂`. -/
theorem chargeA0_eq_neg_onShellδ₂ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) : chargeA0 P.e P.m P.mγ P.Λ = -onShellδ₂ P := by
  have hL := continuousOn_log_onShell hm hmγ hΛ
  have hkΛ := continuousOn_div_onShell (M := P.Λ) hm hΛ
  have hkγ := continuousOn_div_onShell (M := P.mγ) hm hmγ
  have hiΛ := continuousOn_inv_onShell (M := P.Λ) hm hΛ
  have hiγ := continuousOn_inv_onShell (M := P.mγ) hm hmγ
  have hw : ∀ f : ℝ → ℝ, Continuous f → ContinuousOn f (Icc (0 : ℝ) 1) :=
    fun f hf => hf.continuousOn
  -- The four integrands.
  have i1 := intervalIntegrable_of_continuousOn_Icc
    ((hw (fun y : ℝ => 2 * y) (by fun_prop)).mul (hL.add
      (((hw (fun _ => (1 / 2 : ℝ)) continuous_const).mul (hiγ.sub hiΛ)).mul
        (hw (fun y : ℝ => 2 * ((1 - 4 * (1 - y) + (1 - y) ^ 2) * P.m ^ 2)) (by fun_prop)))))
  have i2 := intervalIntegrable_of_continuousOn_Icc
    ((hw (fun x : ℝ => 1 - x) (by fun_prop)).mul hL)
  have i3 := intervalIntegrable_of_continuousOn_Icc
    ((hw (fun x : ℝ => 1 - x) (by fun_prop)).mul (hkΛ.sub hkγ))
  have i4 := intervalIntegrable_of_continuousOn_Icc (hkΛ.sub hkγ)
  simp only [Pi.mul_def, Pi.add_def, Pi.sub_def] at i1 i2 i3 i4
  have hW := integral_wardIntegrand_eq_zero hm hmγ hΛ
  have hW' : ∫ x in (0 : ℝ)..1, (1 / 2 * (2 * x * (Real.log
          (selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
            / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)
        + 1 / 2 * ((selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)⁻¹
          - (selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x)⁻¹)
          * (2 * ((1 - 4 * (1 - x) + (1 - x) ^ 2) * P.m ^ 2))))
      - (1 - x) * Real.log (selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)
      + 2 * P.m ^ 2 * ((1 - x) *
        (x * (1 - x) / selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x))
      - 4 * P.m ^ 2 *
        (x * (1 - x) / selfEnergyFeynmanMass P.m P.Λ (-P.m ^ 2) x
          - x * (1 - x) / selfEnergyFeynmanMass P.m P.mγ (-P.m ^ 2) x)) = 0 := by
    refine Eq.trans (intervalIntegral.integral_congr fun x _ => ?_) hW
    ring
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hW'
  all_goals try first
    | exact i1.const_mul _
    | exact i2
    | exact i3.const_mul _
    | exact i4.const_mul _
    | exact (i1.const_mul _).sub i2
    | exact ((i1.const_mul _).sub i2).add (i3.const_mul _)
  rw [chargeA0, integral_formIntegrandAq_zero, onShellδ₂_eq P hm hmγ hΛ]
  linear_combination (P.e ^ 2 / (8 * π ^ 2)) * hW'

/-- **The Ward identity `Z₁ = Z₂` on the closed forms.** For `m, m_γ, Λ > 0`, the counterterm
`Z₁ = chargeZ = 1 - A₀` fixed by the charge condition is `1 + δ₂` with `δ₂ = onShellδ₂ P` fixed
by the electron on-shell conditions. -/
theorem chargeZ_eq_one_add_onShellδ₂ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) : chargeZ P.e P.m P.mγ P.Λ = 1 + onShellδ₂ P := by
  rw [chargeZ, chargeA0_eq_neg_onShellδ₂ P hm hmγ hΛ, sub_neg_eq_add]

end QED.TwoLoop.Ward

end
