/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalf
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The subtracted bubble half at fixed `q`, and the `q → 0` step

A reduction of `QED.TwoLoop.VPHalf.VPHalfSub` (the subtracted bubble half of the VP unit) to a
statement at **fixed** on-shell external momenta, with the `q → 0` limit carried out once and for
all on the explicit side.

* **The spectral side at fixed `q² = s`** (`specFlavour`, `specSum`): one flavour of mass `M`
  contributes `∫₀¹ ρ(v) (Λ² - m_γ²)² (∫ kernVP m m_γ Λ μ_v s)/2 dv` with `μ_v = √(4M²/(1-v²))`
  (`specMass`), the `ρ`-superposition of the `q² = s` Pauli kernels of the one-loop vertex with
  photon factor `(Λ² - m_γ²)² k⁴/((k² + m_γ²)² (k² + Λ²)² (k² + μ_v²))`. At `m = 1`, `s = 0` it
  is `vpFlavour M m_γ Λ` (`specFlavour_one_zero`, from `QED.TwoLoop.VPHalf.vpFlavour_eq_perV`).
* **Continuity at `s = 0` uniformly in the spectral variable** (`tendsto_specFlavour_zero`): the
  kernel is bounded by `2m²/(μ² a² b²)` (`kern5_le_inv_mu`), and `ρ(v)/μ_v² = v²(1 - v²/3)/(4M²)`
  is bounded, so dominated convergence in `v` applies.
* **The fixed-`q` statement** (`VPHalfSubAt P p p'`): the Pauli numerator of the `ε → 0⁺` limit of
  the class `VP`, minus twice that of the `δ₃` class at `δ₃ = -Π_loop(0)`, equals
  `i · (e q² (4m² + q²)²/m) · (e⁴/(16π⁴)) · ∑_f c_f specFlavour m M_f m_γ Λ q²`. This is the
  normalization of the frozen one-loop vertex (`QED.TwoLoop.VPHalf.tendsto_efi_perVIntegrand`)
  with photon function `(Π_loop(k²) - Π_loop(0)) k² D(k²)²` in its spectral form. Its explicit
  form (`vpHalfSubAt_iff`) involves the VP class alone: the `δ₃` class is explicit
  (`QED.TwoLoop.VPUnitNested.pauliNum_ctLimitV_d3`).
* **Outer form** (`vpHalfSubAt_iff_outer`): equivalently, `-pauliNum (VP)` at fixed `q` is
  `i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ 2 y² m² Π_loop(K) K D(K)²` over the Feynman square, with
  `K = y² (m² + x(1-x) q²)/(1-y)` (`vpK`): the one-loop vertex with the photon function
  `Π_loop(k²) k² D(k²)²`, with no spectral representation. The bridge is Fubini in the spectral
  variable (`specFlavour_eq_outer`) and the photon-function form of the kernels
  (`kernVP_eq_photon`, `kernD3_eq_photon`).
* **The reduction** (`vpHalfSub_of_eventually`): at `m = 1`, admissible regulators and the
  Pauli–Villars conditions, if `VPHalfSubAt` holds along the curve `p'(u)` for all small `u ≠ 0`,
  then `VPHalfSub P`, hence `VPHalf P` (`vpHalf_of_eventually`) and, at `e = 1`, `VPUnitNested P`
  (`vpUnitNested_of_eventually`).

## What remains

`VPHalfSubAt` at fixed `q² > 0` (small): the identity, at fixed external momenta, between two
`ε → 0⁺` limits, that of the two-loop class `VP` (an explicit parametric integral over nine
Feynman parameters, `QED.TwoLoop.ClassLimit`) and the spectral superposition of one-loop
vertices. It is obligation O2-8 at the `ε → 0` level, now without any `q → 0` step.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalf

open QED.WickModel QED.TwoLoop.UnitVPLink QED.TwoLoop.VPUnitNested QED.TwoLoop.VPUnit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.Integration (feynmanMeasure)

/-! ### The spectral side at fixed `q² = s` -/

/-- The spectral mass `μ_v = √(4M²/(1-v²))`. -/
noncomputable def specMass (M v : ℝ) : ℝ := Real.sqrt (4 * M ^ 2 / (1 - v ^ 2))

/-- **One flavour of the spectral side at `q² = s`**:
`∫₀¹ ρ(v) (Λ² - m_γ²)² (∫ kernVP m m_γ Λ μ_v s)/2 dv`. -/
noncomputable def specFlavour (m M mγ Λ s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, rho v *
    ((Λ ^ 2 - mγ ^ 2) ^ 2 * (∫ z, kernVP m mγ Λ (specMass M v) s z ∂feynmanMeasure) / 2)

/-- **The spectral side at `q² = s`**: `∑_f c_f specFlavour m M_f m_γ Λ s`. -/
noncomputable def specSum (P : Params) (s : ℝ) : ℝ :=
  ∑ f, P.loopCoeff f * specFlavour P.m (P.mass f) P.mγ P.Λ s

/-- At `m = 1`, `s = 0` one flavour of the spectral side is `vpFlavour`. -/
theorem specFlavour_one_zero {M mγ Λ : ℝ} (hM : M ≠ 0) (hmγ : 0 < mγ) (hmΛ : mγ < Λ)
    (hm2 : mγ ^ 2 < 4 * M ^ 2) : specFlavour 1 M mγ Λ 0 = vpFlavour M mγ Λ := by
  rw [vpFlavour_eq_perV hM hmγ hmΛ hm2]
  rfl

/-! ### Continuity at `s = 0`, uniformly in `v` -/

/-- `kern5 ≤ 2m²/(μ² a² b²)` on the square, for `s ≥ 0` and `μ > 0`. -/
theorem kern5_le_inv_mu {m s a b c d μ : ℝ} {z : ℝ × ℝ} (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ)
    (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    kern5 m a b c d μ s z ≤ 2 * m ^ 2 * ((μ ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by
  have hy : 0 < z.2 := hz.2.1
  have hy1 : z.2 ≤ 1 := hz.2.2
  have h1 : 0 ≤ 1 - z.2 := by linarith
  have hDa := kDen_pos a hm hs hz
  have hDb := kDen_pos b hm hs hz
  have hDc := kDen_pos c hm hs hz
  have hDd := kDen_pos d hm hs hz
  have hDμ := kDen_pos μ hm hs hz
  have hC := kC_pos' hm hs hz
  have f2 : ∀ M : ℝ, kC m s z / kDen m M s z ≤ 1 := fun M => by
    rw [div_le_one (kDen_pos M hm hs hz)]
    have : (1 - z.2) * M ^ 2 ≥ 0 := mul_nonneg h1 (sq_nonneg _)
    unfold kDen; linarith
  have fμ := one_sub_div_kDen_le hμ hm hs hz
  have fa := one_sub_div_kDen_le ha hm hs hz
  have fb := one_sub_div_kDen_le hb hm hs hz
  have f1 : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m μ s z ≤ 2 * m ^ 2 * (μ ^ 2)⁻¹ := by
    have hy2 : z.2 ^ 2 ≤ 1 := by nlinarith
    have e : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m μ s z =
        2 * m ^ 2 * z.2 ^ 2 * ((1 - z.2) / kDen m μ s z) := by ring
    rw [e]
    have g : 0 ≤ (1 - z.2) / kDen m μ s z := by positivity
    calc 2 * m ^ 2 * z.2 ^ 2 * ((1 - z.2) / kDen m μ s z)
        ≤ 2 * m ^ 2 * 1 * (μ ^ 2)⁻¹ := by gcongr
      _ = 2 * m ^ 2 * (μ ^ 2)⁻¹ := by ring
  rw [kern5_eq_mul]
  have g1 : 0 ≤ 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m μ s z := by positivity
  have g2 : 0 ≤ kC m s z / kDen m d s z := by positivity
  have g2' : 0 ≤ kC m s z / kDen m c s z := by positivity
  have g3 : 0 ≤ (1 - z.2) / kDen m a s z := by positivity
  have g4 : 0 ≤ (1 - z.2) / kDen m b s z := by positivity
  have f2d := f2 d
  have f2c := f2 c
  calc _ ≤ 2 * m ^ 2 * (μ ^ 2)⁻¹ * 1 * 1 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by gcongr
    _ = 2 * m ^ 2 * ((μ ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by ring

theorem feynmanMeasure_real_univ : feynmanMeasure.real univ = 1 := by
  rw [Measure.real, QED.Integration.feynmanMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
  simp

theorem integral_kernVP_nonneg {m a b μ s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) :
    0 ≤ ∫ z, kernVP m a b μ s z ∂feynmanMeasure := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure] with z hz
  exact kern5_nonneg hm hs hz

theorem integral_kernVP_le {m a b μ s : ℝ} (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) (hm : 0 < m)
    (hs : 0 ≤ s) :
    ∫ z, kernVP m a b μ s z ∂feynmanMeasure ≤
      2 * m ^ 2 * ((μ ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by
  have h := norm_integral_le_of_norm_le_const (μ := feynmanMeasure)
    (f := kernVP m a b μ s) (C := 2 * m ^ 2 * ((μ ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))) (by
      filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure] with z hz
      rw [Real.norm_eq_abs, kernVP, abs_of_nonneg (kern5_nonneg hm hs hz)]
      exact kern5_le_inv_mu ha hb hμ hm hs hz)
  rw [feynmanMeasure_real_univ, mul_one] at h
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)

/-- `ρ(v)/μ_v² = v²(1 - v²/3)/(4M²)` for `0 < v < 1`, `M ≠ 0`. -/
theorem rho_mul_inv_specMass_sq {M v : ℝ} (hM : M ≠ 0) (hv : v ∈ Ioo (0 : ℝ) 1) :
    rho v * (specMass M v ^ 2)⁻¹ = v ^ 2 * (1 - v ^ 2 / 3) / (4 * M ^ 2) := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have h0 : 0 ≤ 4 * M ^ 2 / (1 - v ^ 2) := by positivity
  rw [specMass, Real.sq_sqrt h0, rho]
  field_simp

theorem specMass_pos {M v : ℝ} (hM : M ≠ 0) (hv : v ∈ Ioo (0 : ℝ) 1) : 0 < specMass M v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have : 0 < 4 * M ^ 2 / (1 - v ^ 2) := by positivity
  exact Real.sqrt_pos.2 this

/-- The pointwise bound behind the dominated convergence and Fubini in the spectral variable. -/
theorem rho_mul_kern_le {m M a b v X : ℝ} (hM : M ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (hv : v ∈ Ioo (0 : ℝ) 1) (hX0 : 0 ≤ X)
    (hX : X ≤ 2 * m ^ 2 * ((specMass M v ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))) :
    0 ≤ rho v * ((b ^ 2 - a ^ 2) ^ 2 * X / 2) ∧
      rho v * ((b ^ 2 - a ^ 2) ^ 2 * X / 2) ≤
        (b ^ 2 - a ^ 2) ^ 2 / 2 * (m ^ 2 / (2 * M ^ 2) * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hrho0 : 0 ≤ rho v := by
    unfold rho
    have : 0 ≤ 1 - v ^ 2 / 3 := by nlinarith [hv.1, hv.2]
    positivity
  refine ⟨by positivity, ?_⟩
  have hr := rho_mul_inv_specMass_sq hM hv
  have hv2 : v ^ 2 * (1 - v ^ 2 / 3) ≤ 1 := by nlinarith [hv.1, hv.2]
  have hM2 : 0 < M ^ 2 := by positivity
  have hab : 0 ≤ (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by positivity
  calc rho v * ((b ^ 2 - a ^ 2) ^ 2 * X / 2)
      ≤ rho v * ((b ^ 2 - a ^ 2) ^ 2 *
        (2 * m ^ 2 * ((specMass M v ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))) / 2) := by gcongr
    _ = (b ^ 2 - a ^ 2) ^ 2 * m ^ 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) *
        (rho v * (specMass M v ^ 2)⁻¹) := by ring
    _ = (b ^ 2 - a ^ 2) ^ 2 * m ^ 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) *
        (v ^ 2 * (1 - v ^ 2 / 3) / (4 * M ^ 2)) := by rw [hr]
    _ ≤ (b ^ 2 - a ^ 2) ^ 2 * m ^ 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) * (1 / (4 * M ^ 2)) := by
        gcongr
    _ = (b ^ 2 - a ^ 2) ^ 2 / 2 * (m ^ 2 / (2 * M ^ 2) * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by
        field_simp; ring

/-- **The spectral side is continuous at `q² = 0` from the right**, uniformly in the spectral
variable: dominated convergence in `v` with the bound `ρ(v) ∫ kernVP ≤ m²/(2 M² a² b²)`. -/
theorem tendsto_specFlavour_zero {m M a b : ℝ} (hm : 0 < m) (hM : M ≠ 0) (ha : 0 < a)
    (hb : 0 < b) :
    Tendsto (specFlavour m M a b) (𝓝[≥] 0) (𝓝 (specFlavour m M a b 0)) := by
  unfold specFlavour
  set K : ℝ := (b ^ 2 - a ^ 2) ^ 2 / 2 * (m ^ 2 / (2 * M ^ 2) * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_
    intervalIntegrable_const ?_
  · refine Eventually.of_forall fun s => ?_
    have hmeas : Measurable fun p : ℝ × (ℝ × ℝ) => kernVP m a b (specMass M p.1) s p.2 := by
      unfold kernVP kern5 kDen kC specMass
      fun_prop
    have hint := (hmeas.stronglyMeasurable.integral_prod_right' (ν := feynmanMeasure))
    have hrho : Measurable rho := by unfold rho; fun_prop
    exact (hrho.mul ((hint.measurable.const_mul _).div_const _)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with v hv1 hv
    rw [uIoc_of_le zero_le_one] at hv
    have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩
    have hμ := specMass_pos hM hvI
    have hI0 := integral_kernVP_nonneg (a := a) (b := b) (μ := specMass M v) hm hs
    have hI1 := integral_kernVP_le ha hb hμ hm hs
    have hb' := rho_mul_kern_le (m := m) hM ha hb hvI hI0 hI1
    rw [Real.norm_eq_abs, abs_of_nonneg hb'.1]
    exact hb'.2
  · refine Eventually.of_forall fun v _ => ?_
    exact (((tendsto_integral_kernVP_zero (μ := specMass M v) ha hb hm).const_mul
      ((b ^ 2 - a ^ 2) ^ 2)).div_const 2).const_mul (rho v)

/-! ### The fixed-`q` statement -/

/-- **The subtracted bubble half at fixed external momenta** (open): the Pauli numerator of the
`ε → 0⁺` limit of `VP`, minus twice that of the `δ₃` class at `δ₃ = -Π_loop(0)`, is the spectral
side, `i · (e q² (4m² + q²)²/m) · (e⁴/(16π⁴)) · specSum P q²`. -/
def VPHalfSubAt (P : Params) (p p' : Fin 4 → ℝ) : Prop :=
  -pauliNum P.m p' p (classLimitV .VP P p p') -
      2 * pauliNum P.m p' p (ctLimitV .d3Slot0 (subtractedParams P) p p') =
    I * ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
      ((P.e ^ 4 / (16 * π ^ 4) * specSum P (Minkowski.dot (p' - p) (p' - p)) : ℝ) : ℂ)

/-- **The fixed-`q` statement involves the VP class alone**: at on-shell positive-energy `p, p'`
with `q² > 0`, `VPHalfSubAt P p p'` says that `-pauliNum (VP)` is
`i · (e q² (4m² + q²)²/m)` times
`Π_loop(0) (Λ² - m_γ²)² (e²/(8π²)) ∫ kernD3 m m_γ Λ q² + (e⁴/(16π⁴)) specSum P q²`, the outer
one-loop form of `Π_loop(k²) k² D(k²)²`. -/
theorem vpHalfSubAt_iff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    VPHalfSubAt P p p' ↔
      -pauliNum P.m p' p (classLimitV .VP P p p') =
        I * ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
            (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
          ((vacuumPolarizationLoop P 0 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
              (P.e ^ 2 / (8 * π ^ 2) * ∫ z, kernD3 P.m P.mγ P.Λ (Minkowski.dot (p' - p) (p' - p))
                z ∂feynmanMeasure) +
            P.e ^ 4 / (16 * π ^ 4) * specSum P (Minkowski.dot (p' - p) (p' - p)) : ℝ) : ℂ) := by
  have hd := pauliNum_ctLimitV_d3 (subtractedParams P) hm hmγ hΛ hp hp' hp0 hp0' hq
  simp only [subtractedParams] at hd
  unfold VPHalfSubAt
  simp only [subtractedParams]
  rw [hd]
  push_cast
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-! ### The fixed-`q` statement in outer form -/

/-- The Euclidean photon virtuality of the Feynman-parameter kernels, `K = C/(1-y)`,
`C = y² (m² + x(1-x) s)`. -/
noncomputable def vpK (m s : ℝ) (z : ℝ × ℝ) : ℝ := kC m s z / (1 - z.2)

theorem kDen_eq_vpK {m M s : ℝ} {z : ℝ × ℝ} (h1 : 1 - z.2 ≠ 0) :
    kDen m M s z = (1 - z.2) * (vpK m s z + M ^ 2) := by
  unfold kDen vpK
  field_simp
  ring

theorem kC_eq_vpK {m s : ℝ} {z : ℝ × ℝ} (h1 : 1 - z.2 ≠ 0) :
    kC m s z = (1 - z.2) * vpK m s z := by
  unfold vpK
  field_simp

/-- **The spectral-component kernel in photon-function form**: for `0 < y < 1`, `s ≥ 0`,
`(b² - a²)² kernVP m a b μ s z / 2 = y² m² K D(K)² · K/(K + μ²)` with `K = vpK m s z`,
`D = photonD a b`. -/
theorem kernVP_eq_photon {m a b μ s : ℝ} {z : ℝ × ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    (b ^ 2 - a ^ 2) ^ 2 * kernVP m a b μ s z / 2 =
      z.2 ^ 2 * m ^ 2 * (vpK m s z * photonD a b (vpK m s z) ^ 2) *
        (vpK m s z / (vpK m s z + μ ^ 2)) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hK : 0 < vpK m s z := div_pos (kC_pos' hm hs hz) h1
  have hKa : vpK m s z + a ^ 2 ≠ 0 := by positivity
  have hKb : vpK m s z + b ^ 2 ≠ 0 := by positivity
  have hKμ : vpK m s z + μ ^ 2 ≠ 0 := by positivity
  simp only [kernVP, kern5, kDen_eq_vpK h1.ne', kC_eq_vpK h1.ne', photonD]
  field_simp
  ring

/-- **The `δ₃` kernel in photon-function form**: for `0 < y < 1`, `s ≥ 0`,
`(b² - a²)² kernD3 m a b s z = 2 y² m² K D(K)²`. -/
theorem kernD3_eq_photon {m a b s : ℝ} {z : ℝ × ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    (b ^ 2 - a ^ 2) ^ 2 * kernD3 m a b s z =
      2 * (z.2 ^ 2 * m ^ 2 * (vpK m s z * photonD a b (vpK m s z) ^ 2)) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hK : 0 < vpK m s z := div_pos (kC_pos' hm hs hz) h1
  have hKa : vpK m s z + a ^ 2 ≠ 0 := by positivity
  have hKb : vpK m s z + b ^ 2 ≠ 0 := by positivity
  simp only [kernD3, kern4, kDen_eq_vpK h1.ne', kC_eq_vpK h1.ne', photonD]
  field_simp
  ring

/-- The outer integrand of one flavour at `q² = s`: `y² m² K D(K)² J_M(K)`, with `J_M` the
spectral integral `QED.TwoLoop.UnitVPLink.specJ`. -/
noncomputable def outerFlav (m M a b s : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.2 ^ 2 * m ^ 2 * (vpK m s z * photonD a b (vpK m s z) ^ 2) * specJ M (vpK m s z)

theorem ae_volume_Ioc_mem_Ioo : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) 1)), v ∈ Ioo (0 : ℝ) 1 := by
  have hne : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) 1)), v ≠ 1 := ae_restrict_of_ae ae_ne_one
  filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with v hv hv'
  exact ⟨hv'.1, lt_of_le_of_ne hv'.2 hv⟩

theorem ae_feynmanMeasure_ne_one : ∀ᵐ z ∂feynmanMeasure,
    z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 ∧ z.2 ≠ 1 := by
  have h : ∀ᵐ z ∂feynmanMeasure, z.2 ≠ 1 := by
    rw [QED.Integration.feynmanMeasure]
    exact Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae ae_ne_one)
  filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure, h] with z hz hz1
  exact ⟨hz, hz1⟩

/-- **One flavour of the spectral side in outer form**: `specFlavour m M a b s = ∫ outerFlav`, and
the outer integrand is integrable. Fubini in `(z, v)` with the uniform bound `rho_mul_kern_le`,
then the spectral integral in `v` at fixed `z`. -/
theorem specFlavour_eq_outer {m M a b s : ℝ} (hm : 0 < m) (hM : M ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) :
    Integrable (outerFlav m M a b s) feynmanMeasure ∧
      specFlavour m M a b s = ∫ z, outerFlav m M a b s z ∂feynmanMeasure := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  set G : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    rho p.2 * ((b ^ 2 - a ^ 2) ^ 2 * kernVP m a b (specMass M p.2) s p.1 / 2) with hG
  have hGm : Measurable G := by
    simp only [G]
    unfold rho kernVP kern5 kDen kC specMass
    fun_prop
  have hGi : Integrable G (feynmanMeasure.prod ν) := by
    refine Integrable.mono' (integrable_const
      ((b ^ 2 - a ^ 2) ^ 2 / 2 * (m ^ 2 / (2 * M ^ 2) * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))))
      hGm.aestronglyMeasurable ?_
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := feynmanMeasure) (ν := ν)).ae
      QED.OneLoop.VertexLimit.ae_feynmanMeasure
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := feynmanMeasure) (ν := ν)).ae
      ae_volume_Ioc_mem_Ioo
    filter_upwards [h1, h2] with p hz hv
    have hμ := specMass_pos hM hv
    have hb' := rho_mul_kern_le (m := m) (X := kernVP m a b (specMass M p.2) s p.1) hM ha hb hv
      (kern5_nonneg hm hs hz) (kern5_le_inv_mu (c := a) (d := b) ha hb hμ hm hs hz)
    rw [Real.norm_eq_abs, abs_of_nonneg hb'.1]
    exact hb'.2
  -- the inner `v`-integral at fixed `z`
  have hin : ∀ᵐ z ∂feynmanMeasure, ∫ v, G (z, v) ∂ν = outerFlav m M a b s z := by
    filter_upwards [ae_feynmanMeasure_ne_one] with z ⟨hz, hy1⟩
    have e1 : ∫ v, G (z, v) ∂ν = ∫ v, z.2 ^ 2 * m ^ 2 * (vpK m s z *
        photonD a b (vpK m s z) ^ 2) * (rho v * (vpK m s z /
          (vpK m s z + 4 * M ^ 2 / (1 - v ^ 2)))) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [ae_volume_Ioc_mem_Ioo] with v hv
      have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
      have h0 : 0 ≤ 4 * M ^ 2 / (1 - v ^ 2) := by positivity
      simp only [G]
      rw [mul_div_assoc, ← mul_div_assoc, kernVP_eq_photon hm hs hz hy1, specMass,
        Real.sq_sqrt h0]
      ring
    rw [e1, integral_const_mul, outerFlav, specJ, intervalIntegral.integral_of_le zero_le_one]
  have hval : ∀ v, ∫ z, G (z, v) ∂feynmanMeasure =
      rho v * ((b ^ 2 - a ^ 2) ^ 2 *
        (∫ z, kernVP m a b (specMass M v) s z ∂feynmanMeasure) / 2) := fun v => by
    simp only [G]
    rw [integral_const_mul, integral_div, integral_const_mul]
  refine ⟨(hGi.integral_prod_left).congr hin, ?_⟩
  unfold specFlavour
  simp_rw [← hval]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_prod_symm G hGi,
    integral_prod G hGi]
  exact integral_congr_ae hin

/-- **The fixed-`q` statement in outer form**: at on-shell positive-energy `p, p'` with `q² > 0`
and nonzero loop masses, `VPHalfSubAt P p p'` says that the Pauli numerator of the `ε → 0⁺` limit
of `VP` is the one-loop vertex of the photon function `Π_loop(k²) k² D(k²)²` in Feynman
parameters: `-pauliNum (VP) = i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ 2 y² m² Π_loop(K) K D(K)²`,
`K = C/(1-y)`. No spectral representation appears. -/
theorem vpHalfSubAt_iff_outer (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, P.mass f ≠ 0) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    VPHalfSubAt P p p' ↔
      -pauliNum P.m p' p (classLimitV .VP P p p') =
        I * ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
            (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
          ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
            (vacuumPolarizationLoop P (vpK P.m (Minkowski.dot (p' - p) (p' - p)) z) *
              vpK P.m (Minkowski.dot (p' - p) (p' - p)) z *
              photonD P.mγ P.Λ (vpK P.m (Minkowski.dot (p' - p) (p' - p)) z) ^ 2))
            ∂feynmanMeasure : ℝ) : ℂ) := by
  rw [vpHalfSubAt_iff P hm hmγ hΛ hp hp' hp0 hp0' hq]
  set s := Minkowski.dot (p' - p) (p' - p)
  have hs : 0 ≤ s := hq.le
  set P0 := vacuumPolarizationLoop P 0
  have O0 := specFlavour_eq_outer (s := s) hm (hmass 0) hmγ hΛ hs
  have O1 := specFlavour_eq_outer (s := s) hm (hmass 1) hmγ hΛ hs
  have O2 := specFlavour_eq_outer (s := s) hm (hmass 2) hmγ hΛ hs
  have hD3 : Integrable (kernD3 P.m P.mγ P.Λ s) feynmanMeasure := integrable_kern4 hmγ hΛ hm hs
  have hpt : ∀ᵐ z ∂feynmanMeasure, 2 * (z.2 ^ 2 * P.m ^ 2 *
      (vacuumPolarizationLoop P (vpK P.m s z) * vpK P.m s z *
        photonD P.mγ P.Λ (vpK P.m s z) ^ 2)) =
      P0 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernD3 P.m P.mγ P.Λ s z +
        P.e ^ 2 / (4 * π ^ 2) * 2 * (outerFlav P.m (P.mass 0) P.mγ P.Λ s z +
          P.c₁ * outerFlav P.m (P.mass 1) P.mγ P.Λ s z +
          P.c₂ * outerFlav P.m (P.mass 2) P.mγ P.Λ s z) := by
    filter_upwards [ae_feynmanMeasure_ne_one] with z ⟨hz, hy1⟩
    have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
    have hK : 0 ≤ vpK P.m s z := (div_pos (kC_pos' hm hs hz) h1).le
    have hsub := vacuumPolarizationLoop_sub_zero P hmass hK
    rw [Fin.sum_univ_three] at hsub
    simp only [Params.loopCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hsub
    have hPi : vacuumPolarizationLoop P (vpK P.m s z) = P0 + P.e ^ 2 / (4 * π ^ 2) *
        (1 * specJ (P.mass 0) (vpK P.m s z) + P.c₁ * specJ (P.mass 1) (vpK P.m s z) +
          P.c₂ * specJ (P.mass 2) (vpK P.m s z)) := by linarith
    have hk := kernD3_eq_photon (a := P.mγ) (b := P.Λ) hm hs hz hy1
    rw [mul_assoc P0, hk, hPi]
    simp only [outerFlav]
    ring
  have hI : ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
      (vacuumPolarizationLoop P (vpK P.m s z) * vpK P.m s z *
        photonD P.mγ P.Λ (vpK P.m s z) ^ 2)) ∂feynmanMeasure =
      P0 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ z, kernD3 P.m P.mγ P.Λ s z ∂feynmanMeasure +
        P.e ^ 2 / (4 * π ^ 2) * 2 * specSum P s := by
    have i01 : Integrable (fun z => outerFlav P.m (P.mass 0) P.mγ P.Λ s z +
        P.c₁ * outerFlav P.m (P.mass 1) P.mγ P.Λ s z) feynmanMeasure :=
      O0.1.add (O1.1.const_mul _)
    have i012 : Integrable (fun z => outerFlav P.m (P.mass 0) P.mγ P.Λ s z +
        P.c₁ * outerFlav P.m (P.mass 1) P.mγ P.Λ s z +
        P.c₂ * outerFlav P.m (P.mass 2) P.mγ P.Λ s z) feynmanMeasure :=
      i01.add (O2.1.const_mul _)
    have iD : Integrable (fun z => P0 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernD3 P.m P.mγ P.Λ s z)
        feynmanMeasure := hD3.const_mul _
    have iS : Integrable (fun z => P.e ^ 2 / (4 * π ^ 2) * 2 *
        (outerFlav P.m (P.mass 0) P.mγ P.Λ s z + P.c₁ * outerFlav P.m (P.mass 1) P.mγ P.Λ s z +
          P.c₂ * outerFlav P.m (P.mass 2) P.mγ P.Λ s z)) feynmanMeasure := i012.const_mul _
    rw [integral_congr_ae hpt, integral_add iD iS, integral_const_mul, integral_const_mul,
      integral_add i01 (O2.1.const_mul _), integral_add O0.1 (O1.1.const_mul _),
      integral_const_mul, integral_const_mul, ← O0.2, ← O1.2, ← O2.2]
    unfold specSum
    rw [Fin.sum_univ_three]
    simp only [Params.loopCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hI]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have e : P0 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
        (P.e ^ 2 / (8 * π ^ 2) * ∫ z, kernD3 P.m P.mγ P.Λ s z ∂feynmanMeasure) +
      P.e ^ 4 / (16 * π ^ 4) * specSum P s =
      P.e ^ 2 / (8 * π ^ 2) * (P0 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
        ∫ z, kernD3 P.m P.mγ P.Λ s z ∂feynmanMeasure +
        P.e ^ 2 / (4 * π ^ 2) * 2 * specSum P s) := by
    field_simp
    ring
  rw [e]

/-! ### The reduction -/

theorem one_le_mass {P : Params} (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂) (f : Fin 3) :
    1 ≤ P.mass f := by
  fin_cases f
  · simp [Params.mass, hm]
  · simp only [Params.mass]; exact hM₁.le
  · simp only [Params.mass]; exact hM₂.le

/-- At `m = 1` and admissible regulators, the spectral side at `q² = 0` is
`∑_f c_f vpFlavour M_f m_γ Λ`. -/
theorem specSum_zero (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) :
    specSum P 0 = ∑ f, P.loopCoeff f * vpFlavour (P.mass f) P.mγ P.Λ := by
  unfold specSum
  refine Finset.sum_congr rfl fun f _ => ?_
  have h1 := one_le_mass hm hM₁ hM₂ f
  rw [hm, specFlavour_one_zero (by linarith) hmγ hmΛ (by nlinarith)]

/-- **`VPHalfSub` from its fixed-`q` form near `q = 0`**: at `m = 1`, regulator masses
`M₁, M₂ > 1`, `0 < m_γ < Λ`, `m_γ < 2` and the two Pauli–Villars conditions, if `VPHalfSubAt` holds
along the curve `p'(u)` for all small `u ≠ 0`, then `VPHalfSub P`. -/
theorem vpHalfSub_of_eventually (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (h : ∀ᶠ u in 𝓝[≠] (0 : ℝ), VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m u)) :
    VPHalfSub P := by
  have hm0 : 0 < P.m := by rw [hm]; norm_num
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  have hmass : ∀ f, P.mass f ≠ 0 := mass_ne_zero_of hm hM₁ hM₂
  -- the two class limits along the curve
  have hVP := QED.TwoLoop.PauliZeroExplicit.tendsto_VP_explicit P hm0 hmγ hΛ (by linarith)
    (by linarith) hc₁ hc₂
  have hD3 := QED.TwoLoop.PauliZeroExplicit.tendsto_d3Slot0_explicit (subtractedParams P) hm0 hmγ
    hΛ
  simp only [subtractedParams] at hD3
  -- the explicit side along the curve
  set Φ : ℝ → ℂ := fun u => I * ((P.e : ℂ) * ((4 * P.m ^ 2 / (1 - u ^ 2) : ℝ) : ℂ) *
    (4 * (P.m : ℂ) ^ 2 + (curveQ P.m u : ℂ)) ^ 2 / P.m) *
      ((P.e ^ 4 / (16 * π ^ 4) * specSum P (curveQ P.m u) : ℝ) : ℂ) with hΦ
  have hcq : ContinuousAt (curveQ P.m) 0 := by
    unfold curveQ
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hcq0 : curveQ P.m 0 = 0 := by simp [curveQ]
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hcqT : Tendsto (curveQ P.m) (𝓝[≠] 0) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hcq.tendsto
      rw [hcq0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [h0] with u hu
      exact curveQ_nonneg P.m hu
  have hST : Tendsto (fun u => specSum P (curveQ P.m u)) (𝓝[≠] 0) (𝓝 (specSum P 0)) := by
    unfold specSum
    exact tendsto_finsetSum _ fun f _ =>
      ((tendsto_specFlavour_zero hm0 (hmass f) hmγ hΛ).comp hcqT).const_mul _
  have hden : Tendsto (fun u : ℝ => 4 * P.m ^ 2 / (1 - u ^ 2)) (𝓝[≠] 0)
      (𝓝 (4 * P.m ^ 2 / (1 - 0 ^ 2))) :=
    (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hcqC : Tendsto (fun u => (curveQ P.m u : ℂ)) (𝓝[≠] 0) (𝓝 ((0 : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp
      (hcq.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ))))
    rw [hcq0] at this
    exact this
  have hΦT : Tendsto Φ (𝓝[≠] 0) (𝓝 (I * ((P.e : ℂ) *
      ((4 * P.m ^ 2 / (1 - 0 ^ 2) : ℝ) : ℂ) * (4 * (P.m : ℂ) ^ 2 + ((0 : ℝ) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 4 / (16 * π ^ 4) * specSum P 0 : ℝ) : ℂ))) := by
    have c1 := (Complex.continuous_ofReal.tendsto _).comp hden
    have c3 := (Complex.continuous_ofReal.tendsto _).comp
      (hST.const_mul (P.e ^ 4 / (16 * π ^ 4)))
    exact (tendsto_const_nhds.mul ((((tendsto_const_nhds.mul c1).mul
      ((tendsto_const_nhds.add hcqC).pow 2)).div_const _))).mul c3
  -- the combination of the class limits is `u² Φ(u)` along the curve
  have hS : ∀ w, w ∈ Ioo (-1 : ℝ) 1 → VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m w) →
      -pauliNum P.m (curveMomentum P.m w) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m w)) -
        2 * pauliNum P.m (curveMomentum P.m w) (restMomentum P.m)
          (ctLimitV .d3Slot0 { P with δ₃ := -vacuumPolarizationLoop P 0 } (restMomentum P.m)
            (curveMomentum P.m w)) = (w : ℂ) ^ 2 * Φ w := by
    intro w hw hA
    unfold VPHalfSubAt at hA
    simp only [subtractedParams] at hA
    rw [hA, dot_curveMomentum_sub P.m hw]
    have hw1 := (one_sub_sq_pos hw).ne'
    have hQw : ((curveQ P.m w : ℝ) : ℂ) =
        (w : ℂ) ^ 2 * ((4 * P.m ^ 2 / (1 - w ^ 2) : ℝ) : ℂ) := by
      rw [← ofReal_pow, ← ofReal_mul]
      congr 1
      unfold curveQ
      field_simp
    simp only [hΦ]
    generalize specSum P (curveQ P.m w) = G
    rw [hQw]
    ring
  have hEv : Tendsto (fun u : ℝ =>
      -((pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (classLimitV .VP P (restMomentum P.m) (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2)) -
        2 * ((pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d3Slot0 { P with δ₃ := -vacuumPolarizationLoop P 0 } (restMomentum P.m)
            (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d3Slot0 { P with δ₃ := -vacuumPolarizationLoop P 0 } (restMomentum P.m)
            (curveMomentum P.m (-u)))) / (2 * (u : ℂ) ^ 2)))
      (𝓝[≠] 0) (𝓝 (I * ((P.e : ℂ) *
      ((4 * P.m ^ 2 / (1 - 0 ^ 2) : ℝ) : ℂ) * (4 * (P.m : ℂ) ^ 2 + ((0 : ℝ) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 4 / (16 * π ^ 4) * specSum P 0 : ℝ) : ℂ))) := by
    refine hΦT.congr' ?_
    have hneg : ∀ᶠ u in 𝓝[≠] (0 : ℝ),
        VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m (-u)) := by
      have hT : Tendsto (fun u : ℝ => -u) (𝓝[≠] 0) (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Tendsto (fun u : ℝ => -u) (𝓝 0) (𝓝 (-0)) := tendsto_id.neg
          rw [neg_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
          exact neg_ne_zero.mpr hu
      have h' : ∀ᶠ u in 𝓝[≠] (0 : ℝ), VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m u) := by
        simpa only [VPHalfSubAt, subtractedParams] using h
      exact hT.eventually h'
    have h' : ∀ᶠ u in 𝓝[≠] (0 : ℝ), VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m u) := by
      simpa only [VPHalfSubAt, subtractedParams] using h
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 ∧ u ≠ 0 := h0.and self_mem_nhdsWithin
    filter_upwards [h1, h', hneg] with u ⟨hu, hu0⟩ hA hA'
    have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have e1 := hS u hu hA
    have e2 := hS (-u) hu' hA'
    have hΦn : Φ (-u) = Φ u := by simp only [hΦ, curveQ_neg, neg_sq]
    rw [hΦn] at e2
    have hu0' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0
    push_cast at e2
    field_simp
    linear_combination (-1 : ℂ) * e1 - e2
  have hLim := (hVP.neg).sub (hD3.const_mul 2)
  have hEq := tendsto_nhds_unique hLim hEv
  -- conclude
  unfold VPHalfSub
  simp only [subtractedParams]
  rw [← specSum_zero P hm hM₁ hM₂ hmγ hmΛ hm2]
  have hgoal : -QED.TwoLoop.PauliZeroExplicit.vpZero P -
      2 * QED.TwoLoop.PauliZeroExplicit.d3Zero { P with δ₃ := -vacuumPolarizationLoop P 0 } =
      I * ((P.e : ℂ) * ((4 * P.m ^ 2 / (1 - 0 ^ 2) : ℝ) : ℂ) *
        (4 * (P.m : ℂ) ^ 2 + ((0 : ℝ) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 4 / (16 * π ^ 4) * specSum P 0 : ℝ) : ℂ) := hEq
  rw [hgoal, hm]
  push_cast
  field_simp
  ring

/-- **`VPHalf` from the fixed-`q` statement near `q = 0`** (through `vpHalf_iff_vpHalfSub`). -/
theorem vpHalf_of_eventually (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (h : ∀ᶠ u in 𝓝[≠] (0 : ℝ), VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m u)) :
    VPHalf P :=
  (vpHalf_iff_vpHalfSub P hm hM₁ hM₂ hmγ hmΛ hm2).2
    (vpHalfSub_of_eventually P hm hM₁ hM₂ hmγ hmΛ hm2 hc₁ hc₂ h)

/-- **The nested form of the VP unit from the fixed-`q` statement near `q = 0`**, at `e = 1`
(through `vpUnitNested_iff_vpHalf`). -/
theorem vpUnitNested_of_eventually (P : Params) (hm : P.m = 1) (he : P.e = 1) (hM₁ : 1 < P.M₁)
    (hM₂ : 1 < P.M₂) (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (h : ∀ᶠ u in 𝓝[≠] (0 : ℝ), VPHalfSubAt P (restMomentum P.m) (curveMomentum P.m u)) :
    VPUnitNested P :=
  (vpUnitNested_iff_vpHalf P hm he hM₁ hM₂ hmγ hmΛ hm2).2
    (vpHalf_of_eventually P hm hM₁ hM₂ hmγ hmΛ hm2 hc₁ hc₂ h)

end QED.TwoLoop.VPHalf

end
