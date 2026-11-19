/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2Value
public import QED.ChainProof.HCBB2Pauli

/-!
# The value identity of the bubble–bubble class

Helper level, Phase 5 Stage 1a (O3-6 nested value for `QED.ChainProof.Enum.repBB`). This file
proves `QED.ChainProof.HCBB2.BBPauliValue`: the explicit limit `bbPauliLimit` of the Pauli
numerator at the canonical pair is the one-loop Pauli functional of the photon function
`enumPhoton 0 = Π_loop² s² D³`.

* `kernG_snoc`, `kernG_succ_eq`: a spectral mass `μ` appended to the masses multiplies the kernel
  by `(1-y)/D_μ`; one more power of `K` multiplies it by `K = vpK`.
* `sf m s M x z = (x(1-x))⁻¹ (1-y)/D_{μ(M,x)}` (`μ = specMu M x`): `0 ≤ sf ≤ 1/M²`
  (`sf_nonneg`, `sf_le`), and `sf = 1/(M² + x(1-x)K)` off `y = 1` (`sf_eq`).
* `B1`, `B2`: the integrands in `(z, x)` and `(z, (x₁, x₂))` of the one- and two-insertion
  parts, integrable on the product measures (`integrable_B1`, `integrable_B2`).
* `oneLim_eq`, `twoLim_eq`: the engine limits `oneLim`, `twoLim` as `pauliConst · (e²/8π²) ∫ B`,
  from `QED.ChainProof.HCBB2.powLimit_pauliChain_eq`.
* `outer_bb_eq`: the outer form `∫ 2 y² m² Π_loop(K)² K² D(K)³` in the three kernels, by the
  integration by parts `QED.TwoLoop.VPHalfAtAssembly.vacuumPolarizationLoop_eq_ibp`, the
  photon form of `kernG` and Fubini.
* **`bbPauliValue`**: `BBPauliValue`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.OneLoop QED.OneLoop.VertexLimit QED.WickModel QED.Integration
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAtGen QED.TwoLoop.VPHalf QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.HCSide QED.ChainProof.HCValue QED.TwoLoop.UnitVPLink QED.TwoLoop.PauliZero

/-! ### The kernel with an appended mass -/

theorem kernG_snoc (m s : ℝ) (j : ℕ) {k : ℕ} (hj : j ≤ k + 1) (Ms : Fin (k + 2) → ℝ) (μ : ℝ)
    (z : ℝ × ℝ) :
    kernG m s j (Fin.snoc Ms μ : Fin (k + 1 + 2) → ℝ) z =
      kernG m s j Ms z * ((1 - z.2) / kDen m μ s z) := by
  unfold kernG
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have e : k + 1 + 1 - j = (k + 1 - j) + 1 := by omega
  rw [e, pow_succ]
  ring

theorem kernG_succ_eq {m s : ℝ} (j : ℕ) {k : ℕ} (hj : j + 1 ≤ k + 1) (Ms : Fin (k + 2) → ℝ)
    {z : ℝ × ℝ} (h1 : 1 - z.2 ≠ 0) :
    kernG m s (j + 1) Ms z = vpK m s z * kernG m s j Ms z := by
  unfold kernG
  rw [kC_eq_vpK h1]
  have e : k + 1 - j = (k + 1 - (j + 1)) + 1 := by omega
  rw [e, pow_succ]
  field_simp
  ring

/-- The spectral factor `(x(1-x))⁻¹ (1-y)/D_{μ(M,x)}`. -/
noncomputable def sf (m s M x : ℝ) (z : ℝ × ℝ) : ℝ :=
  (x * (1 - x))⁻¹ * ((1 - z.2) / kDen m (specMu M x) s z)

section SF

variable {m s M x : ℝ} {z : ℝ × ℝ}

theorem sf_eq' (hx : x ∈ Ioo (0 : ℝ) 1) :
    sf m s M x z = (1 - z.2) / ((1 - z.2) * M ^ 2 + x * (1 - x) * kC m s z) := by
  have hxp := mem_Ioo_mul_pos hx
  unfold sf kDen
  rw [specMu_sq hx, inv_mul_eq_div, div_div]
  congr 1
  have e : M ^ 2 / (x * (1 - x)) * (x * (1 - x)) = M ^ 2 := div_mul_cancel₀ _ hxp.ne'
  linear_combination (1 - z.2) * e

theorem sf_nonneg (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ sf m s M x z := by
  have hxp := mem_Ioo_mul_pos hx
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hC := kC_pos' hm hs hz
  rw [sf_eq' hx]
  positivity

theorem sf_le (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hM : 0 < M) : sf m s M x z ≤ 1 / M ^ 2 := by
  have hxp := mem_Ioo_mul_pos hx
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hC := kC_pos' hm hs hz
  rw [sf_eq' hx, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hxp hC]

theorem sf_eq (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
    (hy1 : z.2 ≠ 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hM : 0 < M) :
    sf m s M x z = 1 / (M ^ 2 + x * (1 - x) * vpK m s z) := by
  have hxp := mem_Ioo_mul_pos hx
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hK : 0 < vpK m s z := div_pos (kC_pos' hm hs hz) h1
  rw [sf_eq' hx, kC_eq_vpK h1.ne']
  have : 0 < M ^ 2 + x * (1 - x) * vpK m s z := by positivity
  field_simp

theorem measurable_sf (m s M : ℝ) : Measurable fun q : (ℝ × ℝ) × ℝ => sf m s M q.2 q.1 := by
  unfold sf kDen kC specMu
  fun_prop

end SF

/-- `(x(1-x))⁻¹ kernG j (Ms, μ(M, x)) = sf · kernG j Ms`. -/
theorem inv_mul_kernG_snoc (m s : ℝ) (j : ℕ) {k : ℕ} (hj : j ≤ k + 1) (Ms : Fin (k + 2) → ℝ)
    (M x : ℝ) (z : ℝ × ℝ) :
    (x * (1 - x))⁻¹ * kernG m s j (Fin.snoc Ms (specMu M x) : Fin (k + 1 + 2) → ℝ) z =
      sf m s M x z * kernG m s j Ms z := by
  rw [kernG_snoc m s j hj, sf]
  ring

/-! ### The integrands -/

/-- The weight `(1 - 2x)(x²/2 - x³/3)`. -/
noncomputable def Wt (x : ℝ) : ℝ := (1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3)

/-- The one-insertion integrand in `(z, x)`. -/
noncomputable def B1 (P : Params) (s : ℝ) (z : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∑ f, P.loopCoeff f * (Wt x * (sf P.m s (P.mass f) x z * kernG P.m s 3 (ms6 P) z))

/-- The two-insertion integrand in `(z, (x₁, x₂))`. -/
noncomputable def B2 (P : Params) (s : ℝ) (z : ℝ × ℝ) (w : ℝ × ℝ) : ℝ :=
  ∑ f, ∑ g, P.loopCoeff f * P.loopCoeff g * (Wt w.1 * Wt w.2 *
    (sf P.m s (P.mass f) w.1 z * sf P.m s (P.mass g) w.2 z * kernG P.m s 4 (ms6 P) z))

theorem ms6_ge (P : Params) : ∀ i, min P.mγ P.Λ ≤ ms6 P i := fun i => by
  fin_cases i <;> simp [ms6]

section Integrable

variable {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s)
include hm hmγ hΛ hmass hs

theorem integrable_B1 :
    Integrable (fun q : (ℝ × ℝ) × ℝ => B1 P s q.1 q.2)
      (feynmanMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set M₀ := min P.mγ P.Λ
  have hM₀ : 0 < M₀ := lt_min hmγ hΛ
  set B : ℝ := ∑ f, |P.loopCoeff f| * (1 / P.mass f ^ 2 * (2 / (M₀ ^ 2) ^ (4 + 1 - 3)))
  have hk := measurable_kernG P.m s 3 (ms6 P)
  have hmeas : Measurable fun q : (ℝ × ℝ) × ℝ => B1 P s q.1 q.2 := by
    unfold B1 Wt
    refine Finset.measurable_sum _ fun f _ => ?_
    have := measurable_sf P.m s (P.mass f)
    fun_prop
  refine Integrable.mono' (integrable_const B) hmeas.aestronglyMeasurable ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := feynmanMeasure)
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae QED.OneLoop.VertexLimit.ae_feynmanMeasure
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := feynmanMeasure)
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae ae_Ioc_mem_Ioo
  filter_upwards [h1, h2] with q hz hx
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  have hc : |Wt q.2| ≤ 1 := QED.TwoLoop.VPHalfAtAssembly.norm_coef_le hx
  have s0 := sf_nonneg (M := P.mass f) hm hs hz hx
  have s1 := sf_le hm hs hz hx (hmass f)
  have k0 := kernG_nonneg hm hs hz 3 (ms6 P)
  have k1 := kernG_le hm hs hz hM₀ 3 (by norm_num) (ms6_ge P)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg (mul_nonneg s0 k0)]
  calc |Wt q.2| * (sf P.m s (P.mass f) q.2 q.1 * kernG P.m s 3 (ms6 P) q.1)
      ≤ 1 * (1 / P.mass f ^ 2 * (2 / (M₀ ^ 2) ^ (4 + 1 - 3))) := by gcongr
    _ = _ := one_mul _

theorem integrable_B2 :
    Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => B2 P s q.1 q.2) (feynmanMeasure.prod nu2) := by
  set M₀ := min P.mγ P.Λ
  have hM₀ : 0 < M₀ := lt_min hmγ hΛ
  set B : ℝ := ∑ f, ∑ g, |P.loopCoeff f * P.loopCoeff g| *
    (1 / P.mass f ^ 2 * (1 / P.mass g ^ 2) * (2 / (M₀ ^ 2) ^ (4 + 1 - 4)))
  have hk := measurable_kernG P.m s 4 (ms6 P)
  have hmeas : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => B2 P s q.1 q.2 := by
    unfold B2 Wt
    refine Finset.measurable_sum _ fun f _ => Finset.measurable_sum _ fun g _ => ?_
    have h1 := (measurable_sf P.m s (P.mass f)).comp
      (measurable_fst.prodMk (measurable_snd.fst) :
        Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1, q.2.1))
    have h2 := (measurable_sf P.m s (P.mass g)).comp
      (measurable_fst.prodMk (measurable_snd.snd) :
        Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1, q.2.2))
    simp only [Function.comp_def] at h1 h2
    fun_prop
  refine Integrable.mono' (integrable_const B) hmeas.aestronglyMeasurable ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := feynmanMeasure) (ν := nu2)).ae
    QED.OneLoop.VertexLimit.ae_feynmanMeasure
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := feynmanMeasure) (ν := nu2)).ae ae_nu2_mem
  filter_upwards [h1, h2] with q hz ⟨hx, hy⟩
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  have hc1 : |Wt q.2.1| ≤ 1 := QED.TwoLoop.VPHalfAtAssembly.norm_coef_le hx
  have hc2 : |Wt q.2.2| ≤ 1 := QED.TwoLoop.VPHalfAtAssembly.norm_coef_le hy
  have s0 := sf_nonneg (M := P.mass f) hm hs hz hx
  have s1 := sf_le hm hs hz hx (hmass f)
  have t0 := sf_nonneg (M := P.mass g) hm hs hz hy
  have t1 := sf_le hm hs hz hy (hmass g)
  have k0 := kernG_nonneg hm hs hz 4 (ms6 P)
  have k1 := kernG_le hm hs hz hM₀ 4 (by norm_num) (ms6_ge P)
  rw [abs_mul (P.loopCoeff f * P.loopCoeff g)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg s0 t0) k0)]
  calc |Wt q.2.1| * |Wt q.2.2| *
        (sf P.m s (P.mass f) q.2.1 q.1 * sf P.m s (P.mass g) q.2.2 q.1 * kernG P.m s 4 (ms6 P) q.1)
      ≤ 1 * 1 * (1 / P.mass f ^ 2 * (1 / P.mass g ^ 2) * (2 / (M₀ ^ 2) ^ (4 + 1 - 4))) := by
        gcongr
    _ = _ := by ring

end Integrable

/-! ### The engine limits -/

theorem specMu_pos {M x : ℝ} (hM : 0 < M) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < specMu M x :=
  hM.trans_le (specMu_ge hM hx)

theorem snoc_pos {k : ℕ} {Ms : Fin (k + 2) → ℝ} (h : ∀ i, 0 < Ms i) {μ : ℝ} (hμ : 0 < μ) :
    ∀ i, 0 < (Fin.snoc Ms μ : Fin (k + 1 + 2) → ℝ) i := fun i => by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa only [Fin.snoc_last] using hμ
  · simpa only [Fin.snoc_castSucc] using h i

theorem ms6_pos {P : Params} (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : ∀ i, 0 < ms6 P i := fun i => by
  fin_cases i <;> simp [ms6, hmγ, hΛ]

theorem mass_pos' {P : Params} (hA : QED.ChainProof.ChainAdmissible P) (f : Fin 3) :
    0 < P.mass f := hA.hm.trans_le (mass_ge hA.hM₁ hA.hM₂ f)

section Engine

variable {P : Params} (hA : QED.ChainProof.ChainAdmissible P) {p' p : Fin 4 → ℝ}
  (hpq : QED.ChainProof.IsPairQ P.m p' p) {α : ℂ}
  (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
include hA hpq hα

omit hα in
theorem integral_B1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ z, B1 P (Minkowski.dot (p' - p) (p' - p)) z x ∂feynmanMeasure =
      ∑ f, P.loopCoeff f * (Wt x * ((x * (1 - x))⁻¹ *
        ∫ z, kernG P.m (Minkowski.dot (p' - p) (p' - p)) 3
          (Fin.snoc (ms6 P) (specMu (P.mass f) x) : Fin (4 + 1 + 2) → ℝ) z ∂feynmanMeasure)) := by
  obtain ⟨-, -, -, -, hq⟩ := hpq
  set q := Minkowski.dot (p' - p) (p' - p)
  have hI : ∀ f, Integrable (fun z => kernG P.m q 3
      (Fin.snoc (ms6 P) (specMu (P.mass f) x) : Fin (4 + 1 + 2) → ℝ) z) feynmanMeasure := by
    intro f
    obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all
      (snoc_pos (ms6_pos hA.hmγ hA.hΛ) (specMu_pos (mass_pos' hA f) hx))
    exact integrable_kernG hA.hm hq.le hM₀ 3 (by norm_num) hMs
  have e : (fun z => B1 P q z x) = fun z => ∑ f, P.loopCoeff f * (Wt x * ((x * (1 - x))⁻¹ *
      kernG P.m q 3 (Fin.snoc (ms6 P) (specMu (P.mass f) x) : Fin (4 + 1 + 2) → ℝ) z)) := by
    funext z
    simp only [B1, inv_mul_kernG_snoc P.m q 3 (by norm_num : 3 ≤ 4 + 1)]
  rw [e, integral_finsetSum _ fun f _ => (((hI f).const_mul _).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_const_mul]

omit hα in
theorem integral_B2_eq {w : ℝ × ℝ} (hx : w.1 ∈ Ioo (0 : ℝ) 1) (hy : w.2 ∈ Ioo (0 : ℝ) 1) :
    ∫ z, B2 P (Minkowski.dot (p' - p) (p' - p)) z w ∂feynmanMeasure =
      ∑ f, ∑ g, P.loopCoeff f * P.loopCoeff g * (Wt w.1 * Wt w.2 *
        ((w.1 * (1 - w.1))⁻¹ * ((w.2 * (1 - w.2))⁻¹ *
          ∫ z, kernG P.m (Minkowski.dot (p' - p) (p' - p)) 4
            (Fin.snoc (Fin.snoc (ms6 P) (specMu (P.mass f) w.1) : Fin (4 + 1 + 2) → ℝ)
              (specMu (P.mass g) w.2) : Fin (5 + 1 + 2) → ℝ) z ∂feynmanMeasure))) := by
  obtain ⟨-, -, -, -, hq⟩ := hpq
  set q := Minkowski.dot (p' - p) (p' - p)
  have hI : ∀ f g, Integrable (fun z => kernG P.m q 4
      (Fin.snoc (Fin.snoc (ms6 P) (specMu (P.mass f) w.1) : Fin (4 + 1 + 2) → ℝ)
        (specMu (P.mass g) w.2) : Fin (5 + 1 + 2) → ℝ) z) feynmanMeasure := by
    intro f g
    obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all
      (snoc_pos (snoc_pos (ms6_pos hA.hmγ hA.hΛ) (specMu_pos (mass_pos' hA f) hx))
        (specMu_pos (mass_pos' hA g) hy))
    exact integrable_kernG hA.hm hq.le hM₀ 4 (by norm_num) hMs
  have e : (fun z => B2 P q z w) = fun z => ∑ f, ∑ g, P.loopCoeff f * P.loopCoeff g *
      (Wt w.1 * Wt w.2 * ((w.1 * (1 - w.1))⁻¹ * ((w.2 * (1 - w.2))⁻¹ *
        kernG P.m q 4 (Fin.snoc (Fin.snoc (ms6 P) (specMu (P.mass f) w.1) :
          Fin (4 + 1 + 2) → ℝ) (specMu (P.mass g) w.2) : Fin (5 + 1 + 2) → ℝ) z))) := by
    funext z
    simp only [B2, inv_mul_kernG_snoc P.m q 4 (by norm_num : 4 ≤ 5 + 1)]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
    have h := inv_mul_kernG_snoc P.m q 4 (by norm_num : 4 ≤ 4 + 1) (ms6 P) (P.mass f) w.1 z
    linear_combination (-(P.loopCoeff f * P.loopCoeff g * (Wt w.1 * Wt w.2) *
      sf P.m q (P.mass g) w.2 z)) * h
  rw [e, integral_finsetSum _ fun f _ => integrable_finsetSum _ fun g _ =>
    ((((hI f g).const_mul _).const_mul _).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_finsetSum _ fun g _ =>
    ((((hI f g).const_mul _).const_mul _).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

theorem oneLim_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    oneLim P α (pauliChain P.e P.m p' p) (ms6 P) 2 wOne p' p x =
      pauliConst P.e P.m (Minkowski.dot (p' - p) (p' - p)) *
        ((P.e ^ 2 / (8 * π ^ 2) *
          ∫ z, B1 P (Minkowski.dot (p' - p) (p' - p)) z x ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hpq : QED.ChainProof.IsPairQ P.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  rw [integral_B1_eq hA hpq hx, oneLim]
  have hv : ∀ f, specLimit α (pauliChain P.e P.m p' p) P.m p' p (2 + 1) 1 (ms6 P) ![P.mass f] ![x]
      = ((x * (1 - x) : ℝ) : ℂ)⁻¹ * valG P.e P.m p' p 3
        (Fin.snoc (ms6 P) (specMu (P.mass f) x) : Fin (4 + 1 + 2) → ℝ) := by
    intro f
    rw [specLimit_succ, specLimit_zero]
    simp only [Matrix.cons_val_zero]
    rw [powLimit_pauliChain_eq hA.hm hp' hp hp0' hp0 hq hα 3 _ (by norm_num)
      (snoc_pos (ms6_pos hA.hmγ hA.hΛ) (specMu_pos (mass_pos' hA f) hx))]
  simp only [hv, valG_def, wOne, Wt]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

theorem twoLim_eq {w : ℝ × ℝ} (hx : w.1 ∈ Ioo (0 : ℝ) 1) (hy : w.2 ∈ Ioo (0 : ℝ) 1) :
    twoLim P α (pauliChain P.e P.m p' p) (ms6 P) 2 wOne wOne p' p w =
      pauliConst P.e P.m (Minkowski.dot (p' - p) (p' - p)) *
        ((P.e ^ 2 / (8 * π ^ 2) *
          ∫ z, B2 P (Minkowski.dot (p' - p) (p' - p)) z w ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hpq : QED.ChainProof.IsPairQ P.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  rw [integral_B2_eq hA hpq hx hy, twoLim]
  have hv : ∀ f g, specLimit α (pauliChain P.e P.m p' p) P.m p' p (2 + 2) 2 (ms6 P)
      ![P.mass f, P.mass g] ![w.1, w.2] =
        ((w.1 * (1 - w.1) : ℝ) : ℂ)⁻¹ * (((w.2 * (1 - w.2) : ℝ) : ℂ)⁻¹ * valG P.e P.m p' p 4
          (Fin.snoc (Fin.snoc (ms6 P) (specMu (P.mass f) w.1) : Fin (4 + 1 + 2) → ℝ)
            (specMu (P.mass g) w.2) : Fin (5 + 1 + 2) → ℝ)) := by
    intro f g
    rw [specLimit_succ, specLimit_succ, specLimit_zero]
    simp only [Matrix.cons_val_zero, Fin.tail, Matrix.cons_val_succ]
    rw [powLimit_pauliChain_eq hA.hm hp' hp hp0' hp0 hq hα 4 _ (by norm_num)
      (snoc_pos (snoc_pos (ms6_pos hA.hmγ hA.hΛ) (specMu_pos (mass_pos' hA f) hx))
        (specMu_pos (mass_pos' hA g) hy))]
  simp only [hv, valG_def, wOne, Wt]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  ring

end Engine

/-! ### The outer form -/

/-- `L₀ = ∑_f c_f log M_f²`. -/
noncomputable def L0 (P : Params) : ℝ := ∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)

theorem logSum_zero (P : Params) : logSum P 0 = ((L0 P : ℝ) : ℂ) := by
  unfold logSum L0
  push_cast
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Complex.ofReal_log (sq_nonneg _)]
  simp

/-- **The pointwise outer form** of `2 y² m² Π_loop(K)² K² D(K)³`. -/
theorem outer_bb_pt (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    2 * (z.2 ^ 2 * P.m ^ 2 * enumPhoton 0 P (vpK P.m s z)) =
      (P.e ^ 2 / (2 * π ^ 2)) ^ 2 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 3 *
        ((1 / 36) * L0 P ^ 2 * kernG P.m s 2 (ms6 P) z -
          (1 / 3) * L0 P * (∫ x in Ioc (0 : ℝ) 1, B1 P s z x) + ∫ w, B2 P s z w ∂nu2) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hK : 0 < vpK P.m s z := div_pos (kC_pos' hm hs hz) h1
  set K := vpK P.m s z
  set φ := kernG P.m s 2 (ms6 P) z
  set g : ℝ → ℝ := fun x => (x ^ 2 / 2 - x ^ 3 / 3) * ∑ f, P.loopCoeff f *
    ((1 - 2 * x) * K / vacuumPolarizationFeynmanMass (P.mass f) K x)
  have hk3 : kernG P.m s 3 (ms6 P) z = K * φ := kernG_succ_eq 2 (k := 4) (by norm_num) _ h1.ne'
  have hk4 : kernG P.m s 4 (ms6 P) z = K * (K * φ) := by
    rw [kernG_succ_eq 3 (k := 4) (by norm_num) _ h1.ne', hk3]
  have hsf : ∀ f, ∀ x ∈ Ioo (0 : ℝ) 1, sf P.m s (P.mass f) x z * K =
      K / vacuumPolarizationFeynmanMass (P.mass f) K x := by
    intro f x hx
    have hxp := mem_Ioo_mul_pos hx
    have hF : 0 < P.mass f ^ 2 + x * (1 - x) * K := by have := hmass f; positivity
    rw [sf_eq hm hs hz hy1 hx (hmass f), vacuumPolarizationFeynmanMass]
    change 1 / (P.mass f ^ 2 + x * (1 - x) * K) * K = K / (P.mass f ^ 2 + x * (1 - x) * K)
    ring
  have hA1 : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∑ f, P.loopCoeff f * (Wt x * (sf P.m s (P.mass f) x z * K)) = g x := by
    intro x hx
    simp only [g, Wt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hsf f x hx]
    ring
  have hB1 : ∀ x ∈ Ioo (0 : ℝ) 1, B1 P s z x = φ * g x := by
    intro x hx
    rw [← hA1 x hx, Finset.mul_sum]
    simp only [B1, hk3]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hB2 : ∀ w : ℝ × ℝ, w.1 ∈ Ioo (0 : ℝ) 1 → w.2 ∈ Ioo (0 : ℝ) 1 →
      B2 P s z w = φ * (g w.1 * g w.2) := by
    intro w hx hy
    rw [← hA1 w.1 hx, ← hA1 w.2 hy, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [B2, hk4]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' _ => ?_
    ring
  have hI1 : ∫ x in Ioc (0 : ℝ) 1, B1 P s z x = φ * ∫ x in Ioc (0 : ℝ) 1, g x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_Ioc_mem_Ioo.mono fun x hx => hB1 x hx)
  have hI2 : ∫ w, B2 P s z w ∂nu2 =
      φ * ((∫ x in Ioc (0 : ℝ) 1, g x) * ∫ x in Ioc (0 : ℝ) 1, g x) := by
    rw [← integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := volume.restrict (Ioc (0 : ℝ) 1)) g g, ← integral_const_mul]
    exact integral_congr_ae (ae_nu2_mem.mono fun w hw => hB2 w hw.1 hw.2)
  have hφ : (P.Λ ^ 2 - P.mγ ^ 2) ^ 3 * φ =
      2 * z.2 ^ 2 * P.m ^ 2 * K ^ 2 * photonD P.mγ P.Λ K ^ 3 := by
    simp only [φ]
    rw [kernG_photon_eq 2 (by norm_num) (ms6 P) h1.ne'
      (fun i => by have := ms6_pos hmγ hΛ i; positivity)]
    simp only [ms6, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, photonD]
    rw [show vpK P.m s z = K from rfl]
    have ha : K + P.mγ ^ 2 ≠ 0 := by positivity
    have hb : K + P.Λ ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hibp := vacuumPolarizationLoop_eq_ibp P (fun f => (hmass f).ne') hK.le
  rw [intervalIntegral.integral_of_le zero_le_one] at hibp
  rw [hI1, hI2]
  simp only [enumPhoton, enumCoeff, enumPow, Matrix.cons_val_zero, one_mul]
  rw [hibp]
  set I := ∫ x in Ioc (0 : ℝ) 1, g x
  change _ = (P.e ^ 2 / (2 * π ^ 2)) ^ 2 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 3 *
    ((1 / 36) * (∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)) ^ 2 * φ -
      (1 / 3) * (∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)) * (φ * I) + φ * (I * I))
  linear_combination (-(P.e ^ 2 / (2 * π ^ 2) *
    ((1 / 6) * ∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2) - I)) ^ 2) * hφ

/-- **The outer form in the three kernels.** -/
theorem outer_bb_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hmass : ∀ f, 0 < P.mass f) {s : ℝ} (hs : 0 ≤ s) :
    ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 * enumPhoton 0 P (vpK P.m s z)) ∂feynmanMeasure =
      (P.e ^ 2 / (2 * π ^ 2)) ^ 2 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 3 *
        ((1 / 36) * L0 P ^ 2 * (∫ z, kernG P.m s 2 (ms6 P) z ∂feynmanMeasure) -
          (1 / 3) * L0 P * (∫ x in Ioc (0 : ℝ) 1, ∫ z, B1 P s z x ∂feynmanMeasure) +
          ∫ w, ∫ z, B2 P s z w ∂feynmanMeasure ∂nu2) := by
  rw [integral_congr_ae (ae_feynmanMeasure_ne_one.mono fun z hz =>
    outer_bb_pt P hm hmγ hΛ hmass hs hz.1 hz.2)]
  have h1 := integrable_B1 hm hmγ hΛ hmass hs
  have h2 := integrable_B2 hm hmγ hΛ hmass hs
  have hk := integrable_kernG hm hs (lt_min hmγ hΛ) 2 (by norm_num) (ms6_ge P)
  have i1 : Integrable (fun z => ∫ x in Ioc (0 : ℝ) 1, B1 P s z x) feynmanMeasure :=
    h1.integral_prod_left
  have i2 : Integrable (fun z => ∫ w, B2 P s z w ∂nu2) feynmanMeasure := h2.integral_prod_left
  rw [integral_const_mul, integral_add (f := fun a => 1 / 36 * L0 P ^ 2 * kernG P.m s 2 (ms6 P) a -
      1 / 3 * L0 P * ∫ x in Ioc (0 : ℝ) 1, B1 P s a x) ((hk.const_mul _).sub (i1.const_mul _)) i2,
    integral_sub (hk.const_mul _) (i1.const_mul _),
    integral_const_mul, integral_const_mul]
  have h1' : Integrable (Function.uncurry fun z x => B1 P s z x)
      (feynmanMeasure.prod (volume.restrict (Ioc (0 : ℝ) 1))) := h1
  have h2' : Integrable (Function.uncurry fun z w => B2 P s z w) (feynmanMeasure.prod nu2) := h2
  rw [integral_integral_swap h1', integral_integral_swap h2']

/-! ### The value identity -/

/-- **The value identity of the bubble–bubble class** (`BBPauliValue`). -/
theorem bbPauliValue : BBPauliValue := by
  intro P hA
  filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
  have hpq := isPairQ_canonical' hA.hm hQ
  have hqQ := QED.TwoLoop.PauliZero.dot_boostMomentum_sub_restMomentum (m := P.m) hA.hm hQ.le
  set p' := boostMomentum P.m Q
  set p := restMomentum P.m
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hpq : QED.ChainProof.IsPairQ P.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  have hα := Classical.choose_spec (pauliChain_quadratic P.e P.m p' p)
  set α := Classical.choose (pauliChain_quadratic P.e P.m p' p)
  have hmass := mass_pos' hA
  have h1 : ∫ x in Ioc (0 : ℝ) 1, oneLim P α (pauliChain P.e P.m p' p) (ms6 P) 2 wOne p' p x =
      pauliConst P.e P.m Q * ((P.e ^ 2 / (8 * π ^ 2) *
        ∫ x in Ioc (0 : ℝ) 1, ∫ z, B1 P Q z x ∂feynmanMeasure : ℝ) : ℂ) := by
    rw [integral_congr_ae (ae_Ioc_mem_Ioo.mono fun x hx => oneLim_eq hA hpq hα hx),
      integral_const_mul, integral_complex_ofReal, integral_const_mul, hqQ]
  have h2 : ∫ w, twoLim P α (pauliChain P.e P.m p' p) (ms6 P) 2 wOne wOne p' p w ∂nu2 =
      pauliConst P.e P.m Q * ((P.e ^ 2 / (8 * π ^ 2) *
        ∫ w, ∫ z, B2 P Q z w ∂feynmanMeasure ∂nu2 : ℝ) : ℂ) := by
    rw [integral_congr_ae (ae_nu2_mem.mono fun w hw => twoLim_eq hA hpq hα hw.1 hw.2),
      integral_const_mul, integral_complex_ofReal, integral_const_mul, hqQ]
  have h0 := powLimit_pauliChain_eq hA.hm hp' hp hp0' hp0 hq hα 2 (ms6 P) (by norm_num)
    (ms6_pos hA.hmγ hA.hΛ)
  rw [valG_def, hqQ] at h0
  rw [bbPauliLimit, ggLimit, h0, h1, h2, logSum_zero,
    outer_bb_eq P hA.hm hA.hmγ hA.hΛ hmass hQ.le, cOne]
  push_cast
  ring

end QED.ChainProof.HCBB2

end
