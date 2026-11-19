/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDLimit
public import QED.ChainProof.HCSideLinks
public import QED.TwoLoop.VPHalfAtAssemblyMatch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The outer form of the bubble–`δ₃` photon function

Helper level, Phase 5 Stage 1a (O3-6 for `QED.ChainProof.Enum.repBD s`, `repDB s`). The nested
value of a bubble–`δ₃` class is the one-loop outer functional of
`QED.ChainProof.HCSide.sidePhoton = (δ₃/2) Π_loop(s) s² D(s)³`. With the integration by parts
of the loop function in its Feynman parameter
(`QED.TwoLoop.VPHalfAtAssembly.vacuumPolarizationLoop_eq_ibp`) this file writes its outer
integral in the photon-function forms that the limit of
`QED/ChainProof/HCSideBDLimit.lean` produces:

* `sideOuter_pt`: pointwise on the open square,
  `2 y² m² sidePhoton(K) = (δ₃/2)(e²/2π²)((1/6) L₀ · 2 y² m² K² D³ - ∫₀¹ phiX x dx)`, with
  `phiX x = ∑_f c_f (1-2x)(x²/2 - x³/3)(x(1-x))⁻¹ · 2 y² m² K³ D³/(K + μ_x²)`;
* `abs_sideX_le`: the spectral integrand is bounded uniformly in `x` and `z`;
* **`outer_eq_side`**: the outer integral with Fubini between the outer Feynman parameters and `x`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.VPUnitNested
open QED.TwoLoop.VPHalfAtAssembly (specMu specMu_sq specMu_ge mem_Ioo_mul_pos ae_Ioc_mem_Ioo
  vacuumPolarizationLoop_eq_ibp mem_Ioo_of_uIoc ae_ne_one_real norm_coef_le mass_ge)
open QED.TwoLoop.VPHalf (kernVP kern5 vpK kDen_eq_vpK kC_eq_vpK integrable_kern5
  ae_feynmanMeasure_ne_one)
open QED.TwoLoop.UnitVPLink (photonD)
open QED.Integration (feynmanMeasure)

/-! ### Definitions -/

/-- The constant part of the outer integrand, `2 y² m² K² D(K)³`. -/
noncomputable def sideC (P : Params) (s : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * (z.2 ^ 2 * P.m ^ 2 * (vpK P.m s z ^ 2 * photonD P.mγ P.Λ (vpK P.m s z) ^ 3))

/-- The spectral part of flavour mass `M`, `2 y² m² K³ D(K)³/(K + μ_x²)`. -/
noncomputable def sideX (P : Params) (s M x : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * (z.2 ^ 2 * P.m ^ 2 * (vpK P.m s z ^ 3 * photonD P.mγ P.Λ (vpK P.m s z) ^ 3 /
    (vpK P.m s z + specMu M x ^ 2)))

/-- The weight `(1-2x)(x²/2 - x³/3)(x(1-x))⁻¹`. -/
noncomputable def sideW (x : ℝ) : ℝ := (1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) * (x * (1 - x))⁻¹

/-- The spectral integrand in `(z, x)`. -/
noncomputable def phiX (P : Params) (s : ℝ) (z : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∑ f, P.loopCoeff f * (sideW x * sideX P s (P.mass f) x z)

/-! ### The pointwise form -/

theorem vpK_nonneg {m s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : 0 ≤ vpK m s z := by
  unfold vpK kC
  have h1 : 0 ≤ 1 - z.2 := sub_nonneg.2 hz.2.2
  have h2 : 0 ≤ z.1 * (1 - z.1) := mul_nonneg hz.1.1.le (sub_nonneg.2 hz.1.2)
  have : 0 ≤ m ^ 2 + z.1 * (1 - z.1) * s := by positivity
  positivity

/-- **The pointwise outer form of the bubble–`δ₃` photon function.** -/
theorem sideOuter_pt (P : Params) (hm : 0 < P.m) (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) {z : ℝ × ℝ} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    2 * (z.2 ^ 2 * P.m ^ 2 * sidePhoton P (vpK P.m s z)) =
      P.δ₃ / 2 * (P.e ^ 2 / (2 * π ^ 2) *
        ((1 / 6) * (∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)) * sideC P s z -
          ∫ x in (0 : ℝ)..1, phiX P s z x)) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hKp : 0 < vpK P.m s z := div_pos (kC_pos' hm hs hz) h1
  set K := vpK P.m s z with hKd
  set D := photonD P.mγ P.Λ K with hDd
  set W := 2 * (z.2 ^ 2 * P.m ^ 2 * (K ^ 2 * D ^ 3))
  have hint : ∫ x in (0 : ℝ)..1, phiX P s z x = W * ∫ x in (0 : ℝ)..1,
      (x ^ 2 / 2 - x ^ 3 / 3) * ∑ f, P.loopCoeff f *
        ((1 - 2 * x) * K / vacuumPolarizationFeynmanMass (P.mass f) K x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one_real] with x hx1 hx
    have hx' := mem_Ioo_of_uIoc hx hx1
    have hxp := mem_Ioo_mul_pos hx'
    simp only [phiX, sideW, sideX, Finset.mul_sum, ← hKd, ← hDd]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [specMu_sq hx']
    have hM : 0 < P.mass f ^ 2 := by have := hmass f; positivity
    have hKμ : K + P.mass f ^ 2 / (x * (1 - x)) ≠ 0 := by positivity
    have hx0 : x ≠ 0 := hx'.1.ne'
    have hx1' : 1 - x ≠ 0 := (sub_pos.2 hx'.2).ne'
    have hF' : P.mass f ^ 2 + x * (1 - x) * K ≠ 0 := by positivity
    unfold vacuumPolarizationFeynmanMass
    simp only [W]
    field_simp
    ring
  rw [hint]
  unfold sidePhoton sideC
  rw [vacuumPolarizationLoop_eq_ibp P hmass hKp.le]
  simp only [W, K, D]
  ring

/-! ### Bounds -/

theorem abs_kD_le {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K) :
    |K * photonD a b K| ≤ |b ^ 2 - a ^ 2| / b ^ 2 := by
  have hKa : 0 < K + a ^ 2 := by positivity
  have hKb : 0 < K + b ^ 2 := by positivity
  have e : K * photonD a b K = (b ^ 2 - a ^ 2) * (K / ((K + a ^ 2) * (K + b ^ 2))) := by
    unfold photonD
    field_simp
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ K / ((K + a ^ 2) * (K + b ^ 2))),
    div_eq_mul_inv |b ^ 2 - a ^ 2|]
  gcongr
  rw [div_le_iff₀ (by positivity)]
  have : 0 < b ^ 2 := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ this]
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- **The spectral integrand is bounded uniformly** in `x ∈ (0, 1)` and `z` in the square. -/
theorem abs_sideX_le (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {M : ℝ} (hM : 0 < M)
    {s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |(x * (1 - x))⁻¹ * sideX P s M x z| ≤
      2 * P.m ^ 2 * ((|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 / M ^ 2) := by
  have hc := mem_Ioo_mul_pos hx
  have hK := vpK_nonneg (m := P.m) hs hz
  set K := vpK P.m s z with hKd
  set c := x * (1 - x) with hcd
  have hKD := abs_kD_le hmγ hΛ hK
  have hy0 : 0 ≤ z.2 := hz.2.1.le
  have hy1 : z.2 ≤ 1 := hz.2.2
  have hden : 0 < c * K + M ^ 2 := by positivity
  have e : c⁻¹ * sideX P s M x z =
      2 * z.2 ^ 2 * P.m ^ 2 * (K * photonD P.mγ P.Λ K) ^ 3 / (c * K + M ^ 2) := by
    unfold sideX
    rw [specMu_sq hx, ← hKd, ← hcd]
    have hKμ : K + M ^ 2 / c ≠ 0 := by positivity
    field_simp
  rw [e, abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
  have h2 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
  rw [h2, abs_of_nonneg hy0]
  have hz2 : z.2 ^ 2 ≤ 1 := by nlinarith
  have hpow : |K * photonD P.mγ P.Λ K| ^ 3 ≤ (|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hKD 3
  have hM2 : 0 < M ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hA : 0 ≤ (|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 := by positivity
  have hcK : M ^ 2 ≤ c * K + M ^ 2 := by nlinarith [mul_nonneg hc.le hK]
  calc 2 * z.2 ^ 2 * |P.m| ^ 2 * |K * photonD P.mγ P.Λ K| ^ 3
      ≤ 2 * 1 * |P.m| ^ 2 * (|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 := by gcongr
    _ = 2 * P.m ^ 2 * ((|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 / M ^ 2) * M ^ 2 := by
        rw [sq_abs]; field_simp
    _ ≤ 2 * P.m ^ 2 * ((|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 / M ^ 2) * (c * K + M ^ 2) := by
        gcongr

theorem measurable_sideX (P : Params) (s M : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => sideX P s M q.2 q.1 := by
  unfold sideX vpK kC photonD specMu
  fun_prop

theorem integrable_phiX (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => phiX P s q.1 q.2)
      (feynmanMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set B : ℝ := ∑ f, |P.loopCoeff f| *
    (2 * P.m ^ 2 * ((|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 / P.mass f ^ 2))
  have hmeas : Measurable fun q : (ℝ × ℝ) × ℝ => phiX P s q.1 q.2 := by
    unfold phiX sideW
    exact Finset.measurable_sum _ fun f _ => measurable_const.mul
      ((by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ =>
        (1 - 2 * q.2) * (q.2 ^ 2 / 2 - q.2 ^ 3 / 3) * (q.2 * (1 - q.2))⁻¹).mul
        (measurable_sideX P s (P.mass f)))
  refine Integrable.mono' (integrable_const B) hmeas.aestronglyMeasurable ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := feynmanMeasure)
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae QED.OneLoop.VertexLimit.ae_feynmanMeasure
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := feynmanMeasure)
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae ae_Ioc_mem_Ioo
  filter_upwards [h1, h2] with q hz hx
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  have hb := abs_sideX_le P hmγ hΛ (hmass f) hs hz hx
  have hc := norm_coef_le hx
  have e : P.loopCoeff f * (sideW q.2 * sideX P s (P.mass f) q.2 q.1) =
      P.loopCoeff f * ((1 - 2 * q.2) * (q.2 ^ 2 / 2 - q.2 ^ 3 / 3)) *
        ((q.2 * (1 - q.2))⁻¹ * sideX P s (P.mass f) q.2 q.1) := by
    unfold sideW; ring
  rw [e, abs_mul, abs_mul]
  calc |P.loopCoeff f| * |(1 - 2 * q.2) * (q.2 ^ 2 / 2 - q.2 ^ 3 / 3)| *
        |(q.2 * (1 - q.2))⁻¹ * sideX P s (P.mass f) q.2 q.1|
      ≤ |P.loopCoeff f| * 1 *
        (2 * P.m ^ 2 * ((|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 / P.mass f ^ 2)) := by
        gcongr
    _ = _ := by ring

theorem sideC_eq_kernVP (P : Params) (hm : 0 < P.m) {s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    sideC P s z = (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
      (kernVP P.m P.mγ P.Λ P.mγ s z - kernVP P.m P.mγ P.Λ P.Λ s z) := by
  rw [kernVP_sub_eq_photon hm hs hz hy1]
  rfl

theorem integrable_sideC (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ}
    (hs : 0 ≤ s) : Integrable (sideC P s) feynmanMeasure := by
  have hI : Integrable (fun z => (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
      (kernVP P.m P.mγ P.Λ P.mγ s z - kernVP P.m P.mγ P.Λ P.Λ s z)) feynmanMeasure :=
    ((integrable_kern5 hmγ hΛ hm hs).sub (integrable_kern5 hmγ hΛ hm hs)).const_mul _
  refine hI.congr ?_
  filter_upwards [ae_feynmanMeasure_ne_one] with z hz
  exact (sideC_eq_kernVP P hm hs hz.1 hz.2).symm

/-- The `z`-slice of the spectral part is integrable at every `x ∈ (0, 1)`. -/
theorem integrable_sideX_slice (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {M : ℝ}
    (hM : 0 < M) {s : ℝ} (hs : 0 ≤ s) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun z => (x * (1 - x))⁻¹ * sideX P s M x z) feynmanMeasure := by
  have hmeas : Measurable fun z : ℝ × ℝ => (x * (1 - x))⁻¹ * sideX P s M x z :=
    measurable_const.mul ((measurable_sideX P s M).comp (by fun_prop :
      Measurable fun z : ℝ × ℝ => ((z, x) : (ℝ × ℝ) × ℝ)))
  refine Integrable.mono' (integrable_const
    (2 * P.m ^ 2 * ((|P.Λ ^ 2 - P.mγ ^ 2| / P.Λ ^ 2) ^ 3 / M ^ 2))) hmeas.aestronglyMeasurable ?_
  filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs]
  exact abs_sideX_le P hmγ hΛ hM hs hz hx

/-- **The outer integral of the bubble–`δ₃` photon function**, with the spectral part as an
iterated integral. -/
theorem outer_eq_side (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s) :
    ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 * sidePhoton P (vpK P.m s z)) ∂feynmanMeasure =
      P.δ₃ / 2 * (P.e ^ 2 / (2 * π ^ 2) *
        ((1 / 6) * (∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)) *
            ∫ z, sideC P s z ∂feynmanMeasure -
          ∫ x in (0 : ℝ)..1, ∑ f, P.loopCoeff f * ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) *
            ∫ z, (x * (1 - x))⁻¹ * sideX P s (P.mass f) x z ∂feynmanMeasure))) := by
  have hmass' : ∀ f, P.mass f ≠ 0 := fun f => (hmass f).ne'
  rw [integral_congr_ae (ae_feynmanMeasure_ne_one.mono fun z hz =>
    sideOuter_pt P hm hmass' hs hz.1 hz.2)]
  have hΦ := integrable_phiX P hmγ hΛ hmass hs
  have hD := integrable_sideC P hm hmγ hΛ hs
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_const_mul, integral_const_mul,
    integral_sub (hD.const_mul _) hΦ.integral_prod_left, integral_const_mul,
    integral_integral_swap hΦ]
  congr 3
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [ae_ne_one_real] with x hx1 hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  simp only [phiX]
  have hi : ∀ f ∈ Finset.univ, Integrable (fun z => P.loopCoeff f *
      (sideW x * sideX P s (P.mass f) x z)) feynmanMeasure := fun f _ => by
    have h := ((integrable_sideX_slice P hmγ hΛ (hmass f) hs hx').const_mul
      ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3))).const_mul (P.loopCoeff f)
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [sideW]
    ring
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sideW]
  ring

end QED.ChainProof.HCSide

end
