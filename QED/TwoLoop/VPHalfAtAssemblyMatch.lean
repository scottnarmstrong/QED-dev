/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyLimit
public import QED.TwoLoop.VPHalfSub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The subtracted bubble half at fixed `q`: matching the outer form

Step 6 of the assembly (obligation O2-8 at the `ε → 0` level), and its consequences.

* `vacuumPolarizationLoop_eq_ibp`: at `ε = 0`, the integration by parts in the Feynman parameter
  of the model's loop function: for `K ≥ 0`,
  `Π_loop(K) = (e²/2π²)((1/6) ∑_f c_f log M_f²`
  `- ∫₀¹ (x²/2 - x³/3) ∑_f c_f (1-2x)K/(M_f² + x(1-x)K))`.
* `outer_eq`: the outer form `∫ 2 y² m² Π_loop(K) K D(K)²` of
  `QED.TwoLoop.VPHalf.vpHalfSubAt_iff_outer` equals `(Λ² - m_γ²)² (e²/2π²)` times
  `(1/6) L₀ ∫ kernD3 - ∫₀¹ ∑_f c_f (1-2x)(x²/2 - x³/3)(x(1-x))⁻¹ ∫ kernVP(μ_x) dx`, by the
  photon-function forms of the kernels (`QED.TwoLoop.VPHalf.kernVP_eq_photon`,
  `QED.TwoLoop.VPHalf.kernD3_eq_photon`) and Fubini between the outer Feynman parameters and `x`.
* **`vpHalfSubAt_of`**: `QED.TwoLoop.VPHalf.VPHalfSubAt P p p'` holds at every pair of on-shell,
  positive-energy momenta with `q² > 0`, under the mass conditions `0 < m < M₁, M₂`,
  `0 < m_γ < Λ` and the Pauli–Villars conditions.
* `vpHalfSub_of_assembly`, `vpHalf_of_assembly`, `vpUnitNested_of_assembly`: hence
  `VPHalfSub`, `VPHalf` and, at `e = 1`, `VPUnitNested`, with no remaining hypothesis beyond the
  regulator conditions of `QED.TwoLoop.VPHalf.vpUnitNested_of_eventually`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace QED.TwoLoop.VPHalfAtAssembly

open QED.WickModel QED.OneLoop QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalf QED.TwoLoop.UnitVPLink QED.TwoLoop.LimitCovariance
open QED.Integration (feynmanMeasure)

/-! ### The loop function after integration by parts, at `ε = 0` -/

/-- **The model's loop function after integration by parts in the Feynman parameter**. -/
theorem vacuumPolarizationLoop_eq_ibp (P : Params) (hmass : ∀ f, P.mass f ≠ 0) {K : ℝ}
    (hK : 0 ≤ K) :
    vacuumPolarizationLoop P K = P.e ^ 2 / (2 * π ^ 2) *
      ((1 / 6) * ∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2) -
        ∫ x in (0 : ℝ)..1, (x ^ 2 / 2 - x ^ 3 / 3) *
          ∑ f, P.loopCoeff f *
            ((1 - 2 * x) * K / vacuumPolarizationFeynmanMass (P.mass f) K x)) := by
  set u : ℝ → ℝ := fun x => ∑ f, P.loopCoeff f *
    Real.log (vacuumPolarizationFeynmanMass (P.mass f) K x)
  set u' : ℝ → ℝ := fun x => ∑ f, P.loopCoeff f *
    ((1 - 2 * x) * K / vacuumPolarizationFeynmanMass (P.mass f) K x)
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x := by
    intro x hx
    rw [hI] at hx
    refine HasDerivAt.fun_sum fun f _ => ?_
    have hD : HasDerivAt (fun x : ℝ => vacuumPolarizationFeynmanMass (P.mass f) K x)
        ((1 - 2 * x) * K) x := by
      unfold vacuumPolarizationFeynmanMass
      have := ((((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).mul
        (hasDerivAt_const x K)).const_add (P.mass f ^ 2))
      refine this.congr_deriv ?_
      simp only [id, Pi.sub_apply]
      ring
    exact (hD.log (feynmanMass_pos (hmass f) hK hx).ne').const_mul _
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 2 / 2 - x ^ 3 / 3)
      (x * (1 - x)) x := fun x _ => by
    have := ((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_pow 3 x).div_const 3)
    refine this.congr_deriv ?_
    push_cast
    ring
  have hu'c : ContinuousOn u' (uIcc 0 1) := by
    rw [hI]
    refine continuousOn_finsetSum _ fun f _ => continuousOn_const.mul ?_
    refine ContinuousOn.div (by fun_prop) (by unfold vacuumPolarizationFeynmanMass; fun_prop)
      fun x hx => (feynmanMass_pos (hmass f) hK hx).ne'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'c.intervalIntegrable
    ((by fun_prop : Continuous fun x : ℝ => x * (1 - x)).intervalIntegrable 0 1)
  unfold vacuumPolarizationLoop
  congr 1
  have e : ∫ x in (0 : ℝ)..1, x * (1 - x) *
      ∑ f, P.loopCoeff f * Real.log (vacuumPolarizationFeynmanMass (P.mass f) K x) =
      ∫ x in (0 : ℝ)..1, u x * (x * (1 - x)) := by
    congr 1
    funext x
    simp only [u]
    ring
  rw [e, hibp]
  have e2 : ∫ x in (0 : ℝ)..1, u' x * (x ^ 2 / 2 - x ^ 3 / 3) =
      ∫ x in (0 : ℝ)..1, (x ^ 2 / 2 - x ^ 3 / 3) * u' x := by
    congr 1
    funext x
    ring
  rw [e2]
  simp only [u, u', vacuumPolarizationFeynmanMass]
  norm_num
  ring

/-! ### The outer form in kernels -/

/-- The integrand in `(z, x)` of the spectral part of the outer form. -/
noncomputable def phiZX (P : Params) (s : ℝ) (z : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∑ f, P.loopCoeff f * ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) * (x * (1 - x))⁻¹ *
    ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s z))

theorem specMu_sq {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    specMu M x ^ 2 = M ^ 2 / (x * (1 - x)) := by
  have := mem_Ioo_mul_pos hx
  rw [specMu, Real.sq_sqrt (by positivity)]

/-- The pointwise form of the outer integrand. -/
theorem outer_pt (P : Params) (hm : 0 < P.m) (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {z : ℝ × ℝ} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    2 * (z.2 ^ 2 * P.m ^ 2 * (vacuumPolarizationLoop P (vpK P.m s z) * vpK P.m s z *
      photonD P.mγ P.Λ (vpK P.m s z) ^ 2)) =
      P.e ^ 2 / (2 * π ^ 2) * ((1 / 6) * (∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)) *
        ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernD3 P.m P.mγ P.Λ s z) -
        ∫ x in (0 : ℝ)..1, phiZX P s z x) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hKp : 0 < vpK P.m s z := div_pos (kC_pos' hm hs hz) h1
  set K := vpK P.m s z
  set W := z.2 ^ 2 * P.m ^ 2 * (K * photonD P.mγ P.Λ K ^ 2)
  rw [vacuumPolarizationLoop_eq_ibp P hmass hKp.le]
  have hk := kernD3_eq_photon (a := P.mγ) (b := P.Λ) hm hs hz hy1
  have hint : ∫ x in (0 : ℝ)..1, phiZX P s z x = 2 * W * ∫ x in (0 : ℝ)..1,
      (x ^ 2 / 2 - x ^ 3 / 3) * ∑ f, P.loopCoeff f *
        ((1 - 2 * x) * K / vacuumPolarizationFeynmanMass (P.mass f) K x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one_real] with x hx1 hx
    have hx' := mem_Ioo_of_uIoc hx hx1
    have hxp := mem_Ioo_mul_pos hx'
    simp only [phiZX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hv := kernVP_eq_photon (a := P.mγ) (b := P.Λ) (μ := specMu (P.mass f) x) hm hs hz hy1
    rw [specMu_sq hx'] at hv
    have hM : 0 < P.mass f ^ 2 := by have := hmass f; positivity
    have hF : vacuumPolarizationFeynmanMass (P.mass f) K x ≠ 0 := by
      unfold vacuumPolarizationFeynmanMass; positivity
    have hKμ : K + P.mass f ^ 2 / (x * (1 - x)) ≠ 0 := by positivity
    have hx0 : x ≠ 0 := hx'.1.ne'
    have hx1' : 1 - x ≠ 0 := (sub_pos.2 hx'.2).ne'
    have hF' : P.mass f ^ 2 + x * (1 - x) * K ≠ 0 := by positivity
    have hfrac : K / (K + P.mass f ^ 2 / (x * (1 - x))) =
        x * (1 - x) * K / (P.mass f ^ 2 + x * (1 - x) * K) := by
      field_simp
      ring
    have hkv : (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s z =
        2 * (W * (x * (1 - x) * K / (P.mass f ^ 2 + x * (1 - x) * K))) := by
      rw [← hfrac]; simp only [W]; linarith
    rw [hkv]
    unfold vacuumPolarizationFeynmanMass at hF ⊢
    field_simp
  rw [hint]
  have hk' : (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernD3 P.m P.mγ P.Λ s z = 2 * W := hk
  rw [hk']
  ring

theorem norm_coef_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |(1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3)| ≤ 1 := by
  have a1 := hx.1
  have a2 := hx.2
  have h1 : |1 - 2 * x| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |x ^ 2 / 2 - x ^ 3 / 3| ≤ 1 := by
    have a3 : x ^ 2 ≤ 1 := by nlinarith
    have a4 : x ^ 3 ≤ 1 := by nlinarith
    have a5 : 0 ≤ x ^ 3 := by positivity
    have a6 : 0 ≤ x ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul]
  calc |1 - 2 * x| * |x ^ 2 / 2 - x ^ 3 / 3| ≤ 1 * 1 := by gcongr
    _ = 1 := by ring

theorem kernVP_div_le {m a b M s : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hs : 0 ≤ s) {z : ℝ × ℝ} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ (x * (1 - x))⁻¹ * kernVP m a b (specMu M x) s z ∧
      (x * (1 - x))⁻¹ * kernVP m a b (specMu M x) s z ≤
        2 * m ^ 2 * ((M ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by
  have hxp := mem_Ioo_mul_pos hx
  have hμ : 0 < specMu M x := hM.trans_le (specMu_ge hM hx)
  have h0 := kern5_nonneg (a := a) (b := b) (c := a) (d := b) (μ := specMu M x) hm hs hz
  have h1 := kern5_le_inv_mu (c := a) (d := b) ha hb hμ hm hs hz
  rw [specMu_sq hx] at h1
  refine ⟨mul_nonneg (by positivity) h0, ?_⟩
  calc (x * (1 - x))⁻¹ * kernVP m a b (specMu M x) s z
      ≤ (x * (1 - x))⁻¹ * (2 * m ^ 2 * ((M ^ 2 / (x * (1 - x)))⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))) := by
        gcongr; exact h1
    _ = 2 * m ^ 2 * ((M ^ 2)⁻¹ * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)) := by
        have hx0 : x ≠ 0 := hx.1.ne'
        have hx1' : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
        rw [inv_div]
        field_simp

theorem integrable_phiZX (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => phiZX P s q.1 q.2)
      (feynmanMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set B : ℝ := ∑ f, |P.loopCoeff f| * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
    (2 * P.m ^ 2 * ((P.mass f ^ 2)⁻¹ * ((P.mγ ^ 2)⁻¹ * (P.Λ ^ 2)⁻¹))))
  have hmeas : Measurable fun q : (ℝ × ℝ) × ℝ => phiZX P s q.1 q.2 := by
    unfold phiZX kernVP kern5 kDen kC specMu
    fun_prop
  refine Integrable.mono' (integrable_const B) hmeas.aestronglyMeasurable ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := feynmanMeasure)
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae QED.OneLoop.VertexLimit.ae_feynmanMeasure
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := feynmanMeasure)
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae ae_Ioc_mem_Ioo
  filter_upwards [h1, h2] with q hz hx
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  obtain ⟨k0, k1⟩ := kernVP_div_le (m := P.m) (a := P.mγ) (b := P.Λ) hm hmγ hΛ (hmass f) hs hz hx
  have hc := norm_coef_le hx
  have e : P.loopCoeff f * ((1 - 2 * q.2) * (q.2 ^ 2 / 2 - q.2 ^ 3 / 3) * (q.2 * (1 - q.2))⁻¹ *
      ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernVP P.m P.mγ P.Λ (specMu (P.mass f) q.2) s q.1)) =
      P.loopCoeff f * ((1 - 2 * q.2) * (q.2 ^ 2 / 2 - q.2 ^ 3 / 3)) *
        ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ((q.2 * (1 - q.2))⁻¹ *
          kernVP P.m P.mγ P.Λ (specMu (P.mass f) q.2) s q.1)) := by ring
  rw [e, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) k0), abs_mul]
  calc |P.loopCoeff f| * |(1 - 2 * q.2) * (q.2 ^ 2 / 2 - q.2 ^ 3 / 3)| *
        ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ((q.2 * (1 - q.2))⁻¹ *
          kernVP P.m P.mγ P.Λ (specMu (P.mass f) q.2) s q.1))
      ≤ |P.loopCoeff f| * 1 * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
          (2 * P.m ^ 2 * ((P.mass f ^ 2)⁻¹ * ((P.mγ ^ 2)⁻¹ * (P.Λ ^ 2)⁻¹)))) := by
        gcongr
    _ = |P.loopCoeff f| * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
          (2 * P.m ^ 2 * ((P.mass f ^ 2)⁻¹ * ((P.mγ ^ 2)⁻¹ * (P.Λ ^ 2)⁻¹)))) := by ring

/-- **The outer form in kernels.** -/
theorem outer_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s) :
    ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 * (vacuumPolarizationLoop P (vpK P.m s z) * vpK P.m s z *
      photonD P.mγ P.Λ (vpK P.m s z) ^ 2)) ∂feynmanMeasure =
      P.e ^ 2 / (2 * π ^ 2) * ((1 / 6) * (∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)) *
        ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ z, kernD3 P.m P.mγ P.Λ s z ∂feynmanMeasure) -
        ∫ x in (0 : ℝ)..1, ∑ f, P.loopCoeff f * ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) *
          (x * (1 - x))⁻¹ * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
            ∫ z, kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s z ∂feynmanMeasure))) := by
  have hmass' : ∀ f, P.mass f ≠ 0 := fun f => (hmass f).ne'
  rw [integral_congr_ae (ae_feynmanMeasure_ne_one.mono fun z hz =>
    outer_pt P hm hmass' hs hz.1 hz.2)]
  have hΦ := integrable_phiZX P hm hmγ hΛ hmass hs
  have hD : Integrable (kernD3 P.m P.mγ P.Λ s) feynmanMeasure := integrable_kern4 hmγ hΛ hm hs
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_const_mul, integral_sub ((hD.const_mul _).const_mul _) hΦ.integral_prod_left,
    integral_const_mul, integral_const_mul, integral_integral_swap hΦ]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp only [phiZX]
  have hi : ∀ f ∈ Finset.univ, Integrable (fun z => P.loopCoeff f *
      ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) * (x * (1 - x))⁻¹ *
        ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s z)))
      feynmanMeasure := fun f _ =>
    (((integrable_kern5 (c := P.mγ) (d := P.Λ) (μ := specMu (P.mass f) x) hmγ hΛ hm hs :
      Integrable (kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s) feynmanMeasure).const_mul
        _).const_mul _).const_mul _
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-! ### The fixed-`q` statement -/

/-- **The subtracted bubble half at fixed external momenta** (obligation O2-8 at the `ε → 0`
level): for `0 < m < M₁, M₂`, `0 < m_γ < Λ`, the Pauli–Villars conditions and on-shell
positive-energy `p, p'` with `q² > 0`, `VPHalfSubAt P p p'` holds. -/
theorem vpHalfSubAt_of (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) : VPHalfSubAt P p p' := by
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  have hmass : ∀ f, 0 < P.mass f := fun f => hm.trans_le (mass_ge hM₁ hM₂ f)
  rw [vpHalfSubAt_iff_outer P hm hmγ hΛ (fun f => (hmass f).ne') hp hp' hp0 hp0' hq,
    pauliNum_classLimitV_VP P hm hM₁ hM₂ hmγ hmΛ hPV₁ hPV₂ hp hp' hp0 hp0' hq,
    outer_eq P hm hmγ hΛ hmass hq.le]
  set s := Minkowski.dot (p' - p) (p' - p)
  set Cq : ℂ := (P.e : ℂ) * (s : ℂ) * (4 * (P.m : ℂ) ^ 2 + (s : ℂ)) ^ 2 / P.m
  set E : ℝ := P.e ^ 2 / (8 * π ^ 2)
  set B : ℝ := (P.Λ ^ 2 - P.mγ ^ 2) ^ 2
  set L : ℝ := ∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)
  set XD : ℝ := ∫ z, kernD3 P.m P.mγ P.Λ s z ∂feynmanMeasure
  set J0 : ℝ := ∫ x in (0 : ℝ)..1, ∑ f, P.loopCoeff f * ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) *
    (x * (1 - x))⁻¹ * ∫ z, kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s z ∂feynmanMeasure)
  have hL : logSum P 0 = ((L : ℝ) : ℂ) := by
    simp only [logSum, L]
    push_cast
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Complex.ofReal_log (sq_nonneg _)]
    push_cast
    ring_nf
  have hJ : ∫ x in (0 : ℝ)..1, ∑ f, (P.loopCoeff f : ℂ) * (uCoef P x *
      (((x * (1 - x) : ℝ) : ℂ)⁻¹ * (I * Cq * ((E * ∫ z, kernVP P.m P.mγ P.Λ (specMu (P.mass f) x)
        s z ∂feynmanMeasure : ℝ) : ℂ)))) = (I * cOne P * I * Cq * (E : ℂ)) * (J0 : ℂ) := by
    simp only [J0]
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [uCoef, wOne]
    push_cast
    ring
  have hJB : ∫ x in (0 : ℝ)..1, ∑ f, P.loopCoeff f * ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) *
      (x * (1 - x))⁻¹ * (B * ∫ z, kernVP P.m P.mγ P.Λ (specMu (P.mass f) x) s z
        ∂feynmanMeasure)) = B * J0 := by
    simp only [J0]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  rw [hL, hJ, hJB]
  simp only [kappaVP, cOne, B]
  push_cast
  linear_combination (-I * (((P.Λ : ℂ) ^ 2 - (P.mγ : ℂ) ^ 2) ^ 2 *
    ((P.e : ℂ) ^ 2 / (2 * (π : ℂ) ^ 2)) * Cq * (E : ℂ) *
    ((1 / 6) * (L : ℂ) * (XD : ℂ) - (J0 : ℂ)))) * Complex.I_sq

/-! ### `VPHalfSub`, `VPHalf` and `VPUnitNested` -/

/-- `VPHalfSubAt` along the boost curve, for every small `u ≠ 0`. -/
theorem eventually_vpHalfSubAt (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    ∀ᶠ u in 𝓝[≠] (0 : ℝ), VPHalfSubAt P (QED.TwoLoop.PauliZero.restMomentum P.m)
      (QED.TwoLoop.PauliZeroLimit.curveMomentum P.m u) := by
  have hm0 : 0 < P.m := by rw [hm]; norm_num
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  refine vpHalfSubAt_of P hm0 (by rw [hm]; exact hM₁) (by rw [hm]; exact hM₂) hmγ hmΛ hc₁ hc₂
    QED.TwoLoop.PauliZero.dot_restMomentum (dot_curveMomentum P.m hu)
    (by simp [QED.TwoLoop.PauliZero.restMomentum, hm0]) (curveMomentum_pos hm0 hu) ?_
  rw [dot_curveMomentum_sub P.m hu]
  have h1 := one_sub_sq_pos hu
  have h2 : 0 < u ^ 2 := by positivity
  unfold curveQ
  positivity

/-- **`VPHalfSub`, unconditionally** under the regulator conditions. -/
theorem vpHalfSub_of_assembly (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) : VPHalfSub P :=
  vpHalfSub_of_eventually P hm hM₁ hM₂ hmγ hmΛ hm2 hc₁ hc₂
    (eventually_vpHalfSubAt P hm hM₁ hM₂ hmγ hmΛ hc₁ hc₂)

/-- **`VPHalf`, unconditionally** under the regulator conditions. -/
theorem vpHalf_of_assembly (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) : VPHalf P :=
  vpHalf_of_eventually P hm hM₁ hM₂ hmγ hmΛ hm2 hc₁ hc₂
    (eventually_vpHalfSubAt P hm hM₁ hM₂ hmγ hmΛ hc₁ hc₂)

/-- **The nested form of the VP unit, unconditionally** at `e = 1` under the regulator
conditions. -/
theorem vpUnitNested_of_assembly (P : Params) (hm : P.m = 1) (he : P.e = 1) (hM₁ : 1 < P.M₁)
    (hM₂ : 1 < P.M₂) (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    VPUnitNested P :=
  vpUnitNested_of_eventually P hm he hM₁ hM₂ hmγ hmΛ hm2 hc₁ hc₂
    (eventually_vpHalfSubAt P hm hM₁ hM₂ hmγ hmΛ hc₁ hc₂)

end QED.TwoLoop.VPHalfAtAssembly

end
