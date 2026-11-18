/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyFubini
public import QED.TwoLoop.LimitCovarianceClasses
public import QED.TwoLoop.ClassLimitVP
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `ε → 0⁺` limit of the Pauli-projected vacuum-polarization class

Step 5 of the assembly (obligation O2-8 at the `ε → 0` level): dominated convergence in the inner
Feynman parameter `x`.

* `tendsto_efi_gInt`: for `0 < x < 1`, the energy-first integral of the `x`-integrand `gInt x`
  tends to `phiZero x = ∑_f c_f u(x) (x(1-x))⁻¹ s2Prod5Limit(a, b, a, b, μ_x)`: the `qInt 2`
  pieces converge by the engine
  (`QED.TwoLoop.VPHalfAtLimit.tendsto_energyFirstIntegral_s2Prod5Integrand`,
  with the prescription `ε/(x(1-x))` on the spectral line), and the `ε qInt 1` pieces vanish,
  being `ε` times a bounded quantity.
* `tendsto_pauliNum_classValue`: the Pauli numerator of the class value tends to
  `κ (i c₁ L₀/6) s1Prod4Limit(a, b, a, b) - κ ∫₀¹ phiZero`; the `ε S_ε` term vanishes.
* **`pauliNum_classLimitV_VP`**: the same for the Pauli numerator of the class limit `classLimitV`,
  with the engine limits identified with the frozen one-loop kernels `kernD3`, `kernVP`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace QED.TwoLoop.VPHalfAtAssembly

open QED.WickModel QED.OneLoop QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAt QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration (feynmanMeasure)
open QED.TwoLoop.VPHalf (kernVP kern5)

/-! ### Elementary limits -/

/-- A product of a term bounded by `K ε` and an eventually bounded term tends to `0`. -/
theorem tendsto_mul_of_le_eps {a b : ℝ → ℂ} {K B : ℝ}
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖a ε‖ ≤ K * ε) (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖b ε‖ ≤ B) :
    Tendsto (fun ε => a ε * b ε) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun ε => K * ε * B) ?_ ?_
  · filter_upwards [ha, hb, self_mem_nhdsWithin] with ε h1 h2 (h3 : 0 < ε)
    rw [norm_mul]
    have hB : 0 ≤ B := (norm_nonneg _).trans h2
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  · have h : Tendsto (fun ε : ℝ => K * ε * B) (𝓝 0) (𝓝 (K * 0 * B)) :=
      ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
    rw [mul_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_logSum (P : Params) (hmass : ∀ f, P.mass f ≠ 0) :
    Tendsto (logSum P) (𝓝[>] 0) (𝓝 (logSum P 0)) := by
  refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
  unfold logSum
  refine tendsto_finsetSum _ fun f _ => tendsto_const_nhds.mul ?_
  refine ContinuousAt.clog (by fun_prop) ?_
  have h : (0 : ℝ) < P.mass f ^ 2 := by have := hmass f; positivity
  simpa using (Complex.ofReal_mem_slitPlane.2 h)

theorem norm_vCoef_le_eps (P : Params) {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖vCoef P ε x‖ ≤ P.e ^ 2 / (4 * π ^ 2) * ε := by
  have h1 : |1 - 2 * x| ≤ 1 := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h3 : 0 ≤ P.e ^ 2 / (4 * π ^ 2) := by positivity
  simp only [vCoef, cTwo, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3,
    abs_of_pos hε, abs_of_pos hx.1]
  have := hx.1.le
  have := hx.2.le
  calc |1 - 2 * x| * ε * (P.e ^ 2 / (4 * π ^ 2)) * x
      ≤ 1 * ε * (P.e ^ 2 / (4 * π ^ 2)) * 1 := by gcongr
    _ = P.e ^ 2 / (4 * π ^ 2) * ε := by ring

theorem tendsto_specEta {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => specEta ε x) (𝓝[>] 0) (𝓝[>] 0) := by
  have h0 := mem_Ioo_mul_pos hx
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun ε : ℝ => ε / (x * (1 - x))) (𝓝 0) (𝓝 (0 / (x * (1 - x)))) :=
      (continuous_id.div_const _).tendsto 0
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact div_pos hε h0

theorem ev_pos_le_one : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 := nhdsWithin_le_nhds (Iic_mem_nhds zero_lt_one)
  exact h1.and h2

/-- The pointwise limit of the `x`-integrand. -/
noncomputable def phiZero (P : Params) (α : ℂ) (p' p : Fin 4 → ℝ) (x : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * (uCoef P x * (((x * (1 - x) : ℝ) : ℂ)⁻¹ *
    s2Prod5Limit α (pauliChain P.e P.m p' p) P.m ![P.mγ, P.Λ, P.mγ, P.Λ, specMu (P.mass f) x]
      p' p))

theorem mass_ge {P : Params} (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (f : Fin 3) :
    P.m ≤ P.mass f := by
  fin_cases f
  · exact le_rfl
  · exact hM₁.le
  · exact hM₂.le

/-- **The pointwise limit of the `x`-integrand**, for `0 < x < 1`. -/
theorem tendsto_efi_gInt (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => energyFirstIntegral (gInt P ε p' p x)) (𝓝[>] 0)
      (𝓝 (phiZero P α p' p x)) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  set N := pauliChain P.e P.m p' p
  obtain ⟨C0, hC0, hC⟩ := exists_good_pieces (Mlo := P.m) hm hmγ hΛ hm hp' hp hp0' hp0
    (continuous_pauliChain P.e P.m p' p) hα hCN
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := ev_pos_le_one
  have h0 : ((x * (1 - x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  -- the `qInt 2` pieces converge by the engine
  have hq2 : ∀ f, Tendsto (fun ε => energyFirstIntegral
      (qInt 2 N P.m P.mγ P.Λ (P.mass f) ε x p' p)) (𝓝[>] 0)
      (𝓝 (((x * (1 - x) : ℝ) : ℂ)⁻¹ *
        s2Prod5Limit α N P.m ![P.mγ, P.Λ, P.mγ, P.Λ, specMu (P.mass f) x] p' p)) := by
    intro f
    set M₀ := min P.mγ (min P.Λ P.m)
    have hM₀ : 0 < M₀ := lt_min hmγ (lt_min hΛ hm)
    have hMf : P.m ≤ P.mass f := mass_ge hM₁ hM₂ f
    have hMs : ∀ j, M₀ ≤ (![P.mγ, P.Λ, P.mγ, P.Λ, specMu (P.mass f) x] : Fin 5 → ℝ) j := by
      have h1 : M₀ ≤ P.mγ := min_le_left _ _
      have h2 : M₀ ≤ P.Λ := (min_le_right _ _).trans (min_le_left _ _)
      have h3 : M₀ ≤ P.m := (min_le_right _ _).trans (min_le_right _ _)
      have h4 : P.mass f ≤ specMu (P.mass f) x := specMu_ge (hm.trans_le hMf) hx
      intro j
      fin_cases j <;> simp [h1, h2]
      linarith
    have hes : ∀ j, Tendsto (fun ε : ℝ => (![ε, ε, ε, ε, specEta ε x] : Fin 5 → ℝ) j)
        (𝓝[>] 0) (𝓝[>] 0) := by
      intro j
      fin_cases j
      · exact tendsto_id
      · exact tendsto_id
      · exact tendsto_id
      · exact tendsto_id
      · exact tendsto_specEta hx
    have h := tendsto_energyFirstIntegral_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0
      (continuous_pauliChain P.e P.m p' p) hα hCN hMs (ε := id) tendsto_id hes
    refine (h.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← efi_const_mul]
    congr 1
    funext ℓ
    rw [qInt_eq_lim 2 N P.m P.mγ P.Λ (P.mass f) hε hx p' p ℓ]
    simp only [s2Prod5Integrand, P5, prodIntegrand, id]
    ring
  -- the `ε qInt 1` pieces vanish
  have hq1 : ∀ f, Tendsto (fun ε => vCoef P ε x * energyFirstIntegral
      (qInt 1 N P.m P.mγ P.Λ (P.mass f) ε x p' p)) (𝓝[>] 0) (𝓝 0) := by
    intro f
    refine tendsto_mul_of_le_eps (K := P.e ^ 2 / (4 * π ^ 2)) (B := C0 * I5) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact norm_vCoef_le_eps P hε hx
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, -, -, hq⟩ := hC ε hε hε1
      exact (hq (P.mass f) (mass_ge hM₁ hM₂ f) x hx).1.1.norm_efi_le
  have hlim : Tendsto (fun ε => ∑ f, (P.loopCoeff f : ℂ) *
      (uCoef P x * energyFirstIntegral (qInt 2 N P.m P.mγ P.Λ (P.mass f) ε x p' p) +
        vCoef P ε x * energyFirstIntegral (qInt 1 N P.m P.mγ P.Λ (P.mass f) ε x p' p)))
      (𝓝[>] 0) (𝓝 (∑ f, (P.loopCoeff f : ℂ) * (uCoef P x * (((x * (1 - x) : ℝ) : ℂ)⁻¹ *
        s2Prod5Limit α N P.m ![P.mγ, P.Λ, P.mγ, P.Λ, specMu (P.mass f) x] p' p) + 0))) :=
    tendsto_finsetSum _ fun f _ => tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul (hq2 f)).add (hq1 f))
  simp only [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with ε ⟨hε, hε1⟩
  obtain ⟨G, -, -, -, hq⟩ := hC ε hε hε1
  have hI : ∀ f, EFInt (fun k => (P.loopCoeff f : ℂ) *
      (uCoef P x * qInt 2 N P.m P.mγ P.Λ (P.mass f) ε x p' p k +
        vCoef P ε x * qInt 1 N P.m P.mγ P.Λ (P.mass f) ε x p' p k)) := fun f =>
    (((hq (P.mass f) (mass_ge hM₁ hM₂ f) x hx).2.1.1.const_mul _).add
      ((hq (P.mass f) (mass_ge hM₁ hM₂ f) x hx).1.1.1.const_mul _)).const_mul _
  have e : gInt P ε p' p x = fun k => ∑ f, (P.loopCoeff f : ℂ) *
      (uCoef P x * qInt 2 N P.m P.mγ P.Λ (P.mass f) ε x p' p k +
        vCoef P ε x * qInt 1 N P.m P.mγ P.Λ (P.mass f) ε x p' p k) :=
    funext fun k => gInt_eq P ε p' p x k
  rw [e, efi_sum _ fun f _ => hI f]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [efi_const_mul, efi_add (((hq (P.mass f) (mass_ge hM₁ hM₂ f) x hx).2.1.1.const_mul _))
    ((hq (P.mass f) (mass_ge hM₁ hM₂ f) x hx).1.1.1.const_mul _), efi_const_mul, efi_const_mul]

theorem ae_ne_one_real : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
  simp [ae_iff, measure_singleton]

theorem mem_Ioo_of_uIoc {x : ℝ} (h : x ∈ Ι (0 : ℝ) 1) (h1 : x ≠ 1) : x ∈ Ioo (0 : ℝ) 1 := by
  rw [uIoc_of_le zero_le_one] at h
  exact ⟨h.1, lt_of_le_of_ne h.2 h1⟩

/-- **The limit of the Pauli numerator of the class value.** -/
theorem tendsto_pauliNum_classValue (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    Tendsto (fun ε => pauliNum P.m p' p (fun μ => Matrix.of fun i j =>
      contractionValue₂ { P with ε := ε } Class5.VP.rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ))) (𝓝[>] 0)
      (𝓝 (kappaVP P * (I * cOne P * (1 / 6) * logSum P 0) *
          s1Prod4Limit α (pauliChain P.e P.m p' p) P.m ![P.mγ, P.Λ, P.mγ, P.Λ] p' p -
        kappaVP P * ∫ x in (0 : ℝ)..1, phiZero P α p' p x)) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  set N := pauliChain P.e P.m p' p
  obtain ⟨C, hC0, hC⟩ := exists_good_gInt P hm hM₁ hM₂ hmγ hΛ hp' hp hp0' hp0
  have hmass : ∀ f, P.mass f ≠ 0 := fun f => (hm.trans_le (mass_ge hM₁ hM₂ f)).ne'
  have hev := ev_pos_le_one
  -- the `k²` term
  have T1 : Tendsto (fun ε : ℝ => energyFirstIntegral (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) *
      P4 N P.m P.mγ P.Λ ε p' p ℓ)) (𝓝[>] 0)
      (𝓝 (s1Prod4Limit α N P.m ![P.mγ, P.Λ, P.mγ, P.Λ] p' p)) := by
    set M₀ := min P.mγ P.Λ
    have hM₀ : 0 < M₀ := lt_min hmγ hΛ
    have hMs : ∀ j, M₀ ≤ (![P.mγ, P.Λ, P.mγ, P.Λ] : Fin 4 → ℝ) j := by
      intro j; fin_cases j <;> simp [M₀]
    have h := tendsto_energyFirstIntegral_s1Prod4Integrand hm hM₀ hp' hp hp0' hp0
      (continuous_pauliChain P.e P.m p' p) hα hCN hMs (ε := id) (es := fun ε _ => ε) tendsto_id
      (fun _ => tendsto_id)
    refine h.congr fun ε => ?_
    congr 1
    funext ℓ
    simp only [s1Prod4Integrand, P4, prodIntegrand, id]
    ring
  -- the `ε S_ε` term vanishes
  have T2 : Tendsto (fun ε : ℝ => ((ε : ℂ) * cTwo P * logSum P ε) *
      energyFirstIntegral (P4 N P.m P.mγ P.Λ ε p' p)) (𝓝[>] 0) (𝓝 0) := by
    have hL := tendsto_logSum P hmass
    have hLb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖logSum P ε‖ ≤ ‖logSum P 0‖ + 1 := by
      have := hL.norm
      exact this.eventually (eventually_le_nhds (by linarith))
    refine tendsto_mul_of_le_eps (K := ‖cTwo P‖ * (‖logSum P 0‖ + 1)) (B := C * I5) ?_ ?_
    · filter_upwards [hLb, self_mem_nhdsWithin] with ε h1 (h2 : 0 < ε)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
      calc ε * ‖cTwo P‖ * ‖logSum P ε‖ ≤ ε * ‖cTwo P‖ * (‖logSum P 0‖ + 1) := by gcongr
        _ = ‖cTwo P‖ * (‖logSum P 0‖ + 1) * ε := by ring
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, h4, -, -⟩ := hC ε hε hε1
      exact h4.1.norm_efi_le
  -- dominated convergence in `x`
  have T3 : Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..1, energyFirstIntegral (gInt P ε p' p x))
      (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, phiZero P α p' p x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C * I5)
      ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, -, -, hg⟩ := hC ε hε hε1
      rw [uIoc_of_le zero_le_one]
      exact aestronglyMeasurable_efi_gInt P ε p' p hg
    · filter_upwards [hev] with ε ⟨hε, hε1⟩
      obtain ⟨G, -, -, -, hg⟩ := hC ε hε hε1
      filter_upwards [ae_ne_one_real] with x hx1 hx
      exact norm_efi_gInt_le hg (mem_Ioo_of_uIoc hx hx1)
    · filter_upwards [ae_ne_one_real] with x hx1 hx
      exact tendsto_efi_gInt P hm hM₁ hM₂ hmγ hΛ hp' hp hp0' hp0 hα (mem_Ioo_of_uIoc hx hx1)
  have hlim := ((((tendsto_logSum P hmass).const_mul (I * cOne P * (1 / 6))).const_mul
    (kappaVP P)).mul T1).add (T2.const_mul (kappaVP P)) |>.sub (T3.const_mul (kappaVP P))
  rw [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with ε ⟨hε, hε1⟩
  obtain ⟨G, -, h4, hs4, hg⟩ := hC ε hε hε1
  rw [pauliNum_classValue_eq P hm hM₁ hM₂ hPV₁ hPV₂ hε hp hp' hq,
    efi_hInt_eq P hε p' p h4 hs4 hg]
  ring

/-- **The Pauli numerator of the class value tends to that of the class limit** (each entry
converges, `QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP`). -/
theorem tendsto_pauliNum_classLimitV (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    Tendsto (fun ε => pauliNum P.m p' p (fun μ => Matrix.of fun i j =>
      contractionValue₂ { P with ε := ε } Class5.VP.rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ))) (𝓝[>] 0)
      (𝓝 (pauliNum P.m p' p (classLimitV .VP P p p'))) := by
  have hent : ∀ μ i j : Fin 4, Tendsto (fun ε =>
      contractionValue₂ { P with ε := ε } Class5.VP.rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) (𝓝[>] 0)
      (𝓝 (classLimitV .VP P p p' μ i j)) := by
    intro μ i j
    obtain ⟨Q, -, -, h⟩ := ClassLimit.tendsto_contractionValue₂_VP P hm hmγ hΛ hM₁.le hM₂.le
      hPV₁ hPV₂ (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) (by simp) hp
      hp' hq (fun _ => i) (fun _ => j) (fun _ => μ)
    exact tendsto_nhds_limUnder ⟨_, h⟩
  simp only [pauliNum_eq_sum, Matrix.of_apply]
  exact tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun i _ => tendsto_finsetSum _
    fun j _ => tendsto_const_nhds.mul (hent μ i j)

/-- The level sets of `x(1-x)` are finite. -/
theorem finite_mul_one_sub_eq (r : ℝ) : {x : ℝ | x * (1 - x) = r}.Finite := by
  refine Set.Finite.subset (Set.toFinite {(1 + Real.sqrt (1 - 4 * r)) / 2,
    (1 - Real.sqrt (1 - 4 * r)) / 2}) fun x (hx : x * (1 - x) = r) => ?_
  have h : (2 * x - 1) ^ 2 = 1 - 4 * r := by rw [← hx]; ring
  have h2 : |2 * x - 1| = Real.sqrt (1 - 4 * r) := by rw [← h, Real.sqrt_sq_eq_abs]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases abs_eq (Real.sqrt_nonneg _) |>.1 h2 with h3 | h3
  · left; linarith
  · right; linarith

/-- For `c > 0`, the spectral mass equals `c` only at finitely many `x ∈ (0, 1)`. -/
theorem ae_specMu_ne {M c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo (0 : ℝ) 1 → specMu M x ≠ c := by
  have hfin := finite_mul_one_sub_eq (M ^ 2 / c ^ 2)
  have h0 : volume {x : ℝ | x * (1 - x) = M ^ 2 / c ^ 2} = 0 := hfin.measure_zero _
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  simp only [not_imp, not_not, Set.mem_ofPred_eq] at hx ⊢
  obtain ⟨hx, he⟩ := hx
  have hp := mem_Ioo_mul_pos hx
  have h1 : M ^ 2 / (x * (1 - x)) = c ^ 2 := by
    rw [← he, specMu, Real.sq_sqrt (by positivity)]
  rw [div_eq_iff hp.ne'] at h1
  rw [eq_div_iff (by positivity)]
  linear_combination (-1 : ℝ) * h1

/-- **The Pauli numerator of the class limit**, at fixed on-shell momenta with `q² > 0`, with the
engine limits identified with the frozen one-loop kernels. -/
theorem pauliNum_classLimitV_VP (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    pauliNum P.m p' p (classLimitV .VP P p p') =
      kappaVP P * (I * cOne P * (1 / 6) * logSum P 0) *
          (I * ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
            (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
          ((P.e ^ 2 / (8 * π ^ 2) *
            ∫ z, kernD3 P.m P.mγ P.Λ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) :
              ℂ)) -
        kappaVP P * ∫ x in (0 : ℝ)..1, ∑ f, (P.loopCoeff f : ℂ) * (uCoef P x *
          (((x * (1 - x) : ℝ) : ℂ)⁻¹ *
            (I * ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
              (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
            ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP P.m P.mγ P.Λ (specMu (P.mass f) x)
              (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ)))) := by
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  obtain ⟨α, hα⟩ := pauliChain_quadratic P.e P.m p' p
  have h1 := tendsto_pauliNum_classLimitV P hm hM₁ hM₂ hmγ hΛ hPV₁ hPV₂ hp hp' hq.le
  have h2 := tendsto_pauliNum_classValue P hm hM₁ hM₂ hmγ hΛ hPV₁ hPV₂ hp hp' hp0 hp0' hq hα
  rw [tendsto_nhds_unique h1 h2, s1Prod4Limit_pauliChain_eq_kernD3 P.e hm hmγ hΛ hp' hp hp0' hp0
    hq hmΛ.ne hα]
  congr 2
  refine intervalIntegral.integral_congr_ae ?_
  have hae : ∀ f : Fin 3, ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo (0 : ℝ) 1 →
      specMu (P.mass f) x ≠ P.mγ ∧ specMu (P.mass f) x ≠ P.Λ := fun f => by
    filter_upwards [ae_specMu_ne (M := P.mass f) hmγ, ae_specMu_ne (M := P.mass f) hΛ]
      with x h1 h2 hx
    exact ⟨h1 hx, h2 hx⟩
  filter_upwards [hae 0, hae 1, hae 2, ae_ne_one_real] with x a0 a1 a2 hx1 hx
  have hx' := mem_Ioo_of_uIoc hx hx1
  simp only [phiZero]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hf : specMu (P.mass f) x ≠ P.mγ ∧ specMu (P.mass f) x ≠ P.Λ := by
    fin_cases f
    · exact a0 hx'
    · exact a1 hx'
    · exact a2 hx'
  have hμ : 0 < specMu (P.mass f) x :=
    (hm.trans_le (mass_ge hM₁ hM₂ f)).trans_le (specMu_ge (hm.trans_le (mass_ge hM₁ hM₂ f)) hx')
  rw [s2Prod5Limit_pauliChain_eq_kernVP P.e hm hmγ hΛ hμ hp' hp hp0' hp0 hq hmΛ.ne hf.1.symm
    hf.2.symm hα]

end QED.TwoLoop.VPHalfAtAssembly

end
