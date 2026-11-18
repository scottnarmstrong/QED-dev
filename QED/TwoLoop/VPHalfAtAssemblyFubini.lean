/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyProj
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fubini in the inner Feynman parameter at fixed `ε`

Steps 3 and 4 of the assembly of the `ε → 0⁺` limit of the vacuum-polarization class
(obligation O2-8 at the `ε → 0` level). At fixed `ε > 0` the Pauli-projected outer integrand
`QED.TwoLoop.VPHalfAtAssembly.hInt` contains the transverse and extra coefficients `Π̂_ε`, `S_ε`,
which after the integration by parts (`QED.TwoLoop.VPHalfAt.vpLoopEps_eq_spectral`,
`QED.TwoLoop.VPHalfAt.vpExtraEps_eq_spectral`) are constants plus integrals over the Feynman
parameter `x` of rational functions of `k²`.

* `hInt_eq`: `hInt = κ (i c₁ L_ε/6) k² P₄ + κ ε c₂ L_ε P₄ - κ ∫₀¹ gInt x dx`, with
  `κ = i (Λ² - m_γ²)²`, `L_ε = ∑_f c_f log(M_f² - iε)` and the `x`-integrand `gInt`.
* `gInt_eq`: for `0 < x < 1`, `gInt x` is a combination of the pieces `qInt 2` and `qInt 1` of
  `QED/TwoLoop/VPHalfAtAssemblyPieces.lean` with coefficients bounded uniformly in `x`
  (`exists_good_gInt`).
* `efi_intervalIntegral_swap`: the energy-first integral commutes with `∫₀¹ dx` when, at every
  spatial momentum, the integrand is integrable in `(energy, x)` and its energy integral is
  integrable in `(spatial momentum, x)`; the two conditions follow from the uniform bounds.
* **`efi_hInt_eq`**: for `0 < ε ≤ 1`,
  `∫_D hInt = κ (i c₁ L_ε/6) ∫_D k² P₄ + κ ε c₂ L_ε ∫_D P₄ - κ ∫₀¹ (∫_D gInt x) dx`, with the
  `x`-integrand bounded by a constant independent of `ε` and `x`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtAssembly

open QED.WickModel QED.OneLoop QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAt QED.TwoLoop.Bridge

/-! ### The generic exchange -/

/-- **The energy-first integral commutes with `∫₀¹ dx`** under the two integrability conditions,
and the `x`-integral is integrable in both stages. -/
theorem efi_intervalIntegral_swap (g : ℝ → (Fin 4 → ℝ) → ℂ)
    (h1 : ∀ v : Fin 3 → ℝ, Integrable (fun q : ℝ × ℝ => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ))
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (h2 : Integrable (fun q : (Fin 3 → ℝ) × ℝ => ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ))
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    EFInt (fun ℓ => ∫ x in (0 : ℝ)..1, g x ℓ) ∧
      energyFirstIntegral (fun ℓ => ∫ x in (0 : ℝ)..1, g x ℓ) =
        ∫ x in (0 : ℝ)..1, energyFirstIntegral (g x) := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have hin : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, ∫ x in Ioc (0 : ℝ) 1, g x (Fin.cons t v : Fin 4 → ℝ) =
      ∫ x in Ioc (0 : ℝ) 1, ∫ t : ℝ, g x (Fin.cons t v : Fin 4 → ℝ) := fun v =>
    integral_integral_swap (f := fun (t : ℝ) (x : ℝ) => g x (Fin.cons t v : Fin 4 → ℝ)) (h1 v)
  refine ⟨⟨fun v => (h1 v).integral_prod_left, ?_⟩, ?_⟩
  · simp_rw [hin]
    exact h2.integral_prod_left
  · unfold energyFirstIntegral
    simp_rw [hin]
    exact integral_integral_swap (f := fun (v : Fin 3 → ℝ) (x : ℝ) =>
      ∫ t : ℝ, g x (Fin.cons t v : Fin 4 → ℝ)) h2

theorem ae_Ioc_mem_Ioo : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
  have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioc] with v hv hv'
  exact ⟨hv'.1, lt_of_le_of_ne hv'.2 hv⟩

/-- The integrability conditions of the exchange from a family of `Good` integrands. -/
theorem integrable_of_good (g : ℝ → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ x ∈ Ioo (0 : ℝ) 1, Good (g x) C G) :
    (∀ v : Fin 3 → ℝ, Integrable (fun q : ℝ × ℝ => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ))
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1)))) ∧
    Integrable (fun q : (Fin 3 → ℝ) × ℝ => ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ))
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hIoo : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 :=
    ae_Ioc_mem_Ioo
  constructor
  · intro v
    have hm : Measurable fun q : ℝ × ℝ => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ) :=
      hgm.comp (by fun_prop : Measurable fun q : ℝ × ℝ => (((v, q.2), q.1) :
        ((Fin 3 → ℝ) × ℝ) × ℝ))
    refine Integrable.mono' (g := fun q : ℝ × ℝ => G v * (1 + q.1 ^ 2)⁻¹ * 1)
      ((integrable_inv_one_add_sq.const_mul (G v)).mul_prod (integrable_const (1 : ℝ)))
      hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae hIoo
    filter_upwards [h2] with q hq
    rw [mul_one]
    exact (hg q.2 hq).2 v q.1
  · have hm : StronglyMeasurable fun q : (Fin 3 → ℝ) × ℝ =>
        ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ) :=
      hgm.stronglyMeasurable.integral_prod_right'
    refine Integrable.mono' (g := fun q : (Fin 3 → ℝ) × ℝ => C * (1 + ‖q.1‖) ^ (-(5 : ℝ)) * 1)
      ((integrable_one_add_norm_five.const_mul C).mul_prod (integrable_const (1 : ℝ)))
      hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).ae hIoo
    filter_upwards [h2] with q hq
    rw [mul_one]
    exact (hg q.2 hq).1.2 q.1

/-! ### The decomposition of the outer integrand -/

/-- `e²/(2π²)`. -/
noncomputable def cOne (P : Params) : ℂ := ((P.e ^ 2 / (2 * π ^ 2) : ℝ) : ℂ)

/-- `e²/(4π²)`. -/
noncomputable def cTwo (P : Params) : ℂ := ((P.e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ)

/-- `L_ε = ∑_f c_f log(M_f² - iε)`. -/
noncomputable def logSum (P : Params) (ε : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * log (((P.mass f ^ 2 : ℝ) : ℂ) - ε * I)

/-- `κ = i (Λ² - m_γ²)²`. -/
noncomputable def kappaVP (P : Params) : ℂ := I * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ)

/-- The weight `x²/2 - x³/3` of the transverse coefficient. -/
noncomputable def wOne (x : ℝ) : ℂ := ((x ^ 2 / 2 - x ^ 3 / 3 : ℝ) : ℂ)

/-- The `x`-integrand of the outer integrand. -/
noncomputable def gInt (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (x : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k * vpRatSum P ε (Minkowski.dot k k) x *
    (I * cOne P * wOne x * (Minkowski.dot k k : ℂ) + (ε : ℂ) * cTwo P * (x : ℂ))

/-- **The outer integrand split into its constant part and the `x`-integral**. -/
theorem hInt_eq (P : Params) {ε : ℝ} (hε : 0 < ε) (p' p k : Fin 4 → ℝ) :
    hInt P ε p' p k =
      kappaVP P * (I * cOne P * (1 / 6) * logSum P ε) *
          ((Minkowski.dot k k : ℂ) * P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k) +
        kappaVP P * ((ε : ℂ) * cTwo P * logSum P ε) *
          P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k -
        kappaVP P * ∫ x in (0 : ℝ)..1, gInt P ε p' p x k := by
  set s := Minkowski.dot k k
  set Q := P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k
  have i1 : IntervalIntegrable (fun x => vpRatSum P ε s x * wOne x) volume 0 1 :=
    ((continuous_vpRatSum P hε s).mul (by unfold wOne; fun_prop)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x => vpRatSum P ε s x * (x : ℂ)) volume 0 1 :=
    ((continuous_vpRatSum P hε s).mul (by fun_prop)).intervalIntegrable 0 1
  have hg : ∫ x in (0 : ℝ)..1, gInt P ε p' p x k =
      Q * (I * cOne P * s) * (∫ x in (0 : ℝ)..1, vpRatSum P ε s x * wOne x) +
        Q * ((ε : ℂ) * cTwo P) * ∫ x in (0 : ℝ)..1, vpRatSum P ε s x * (x : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _)]
    congr 1
    funext x
    simp only [gInt, Q, s]
    ring
  unfold hInt
  rw [vpLoopEps_eq_spectral P hε, vpExtraEps_eq_spectral P hε, hg]
  simp only [kappaVP, cOne, cTwo, logSum, wOne, Q, s]
  ring

/-- The coefficient of `qInt 2` in `gInt`. -/
noncomputable def uCoef (P : Params) (x : ℝ) : ℂ := ((1 - 2 * x : ℝ) : ℂ) * I * cOne P * wOne x

/-- The coefficient of `qInt 1` in `gInt`. -/
noncomputable def vCoef (P : Params) (ε x : ℝ) : ℂ :=
  ((1 - 2 * x : ℝ) : ℂ) * (ε : ℂ) * cTwo P * (x : ℂ)

/-- **`gInt` in terms of the pieces** `qInt 2` and `qInt 1`. -/
theorem gInt_eq (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) (x : ℝ) (k : Fin 4 → ℝ) :
    gInt P ε p' p x k = ∑ f, (P.loopCoeff f : ℂ) *
      (uCoef P x * qInt 2 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ (P.mass f) ε x p' p k +
        vCoef P ε x * qInt 1 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ (P.mass f) ε x p' p k) := by
  simp only [gInt, vpRatSum, qInt, fDen, uCoef, vCoef, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

theorem Good.mul_le {F : (Fin 4 → ℝ) → ℂ} {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hF : Good F C G)
    {c : ℂ} {B : ℝ} (hc : ‖c‖ ≤ B) :
    Good (fun ℓ => c * F ℓ) (B * C) (fun v => B * G v) := by
  have hC := hF.1.nonneg_const
  have hG : ∀ v, 0 ≤ G v := fun v => by
    have h := (norm_nonneg _).trans (hF.2 v 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  exact (hF.const_mul c).mono (mul_le_mul_of_nonneg_right hc hC)
    (fun v => mul_le_mul_of_nonneg_right hc (hG v))

theorem norm_uCoef_le (P : Params) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖uCoef P x‖ ≤ P.e ^ 2 / (2 * π ^ 2) := by
  have h1 : |1 - 2 * x| ≤ 1 := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h2 : |x ^ 2 / 2 - x ^ 3 / 3| ≤ 1 := by
    have a1 := hx.1
    have a2 := hx.2
    have a3 : x ^ 2 ≤ 1 := by nlinarith
    have a4 : x ^ 3 ≤ 1 := by nlinarith
    have a5 : 0 ≤ x ^ 3 := by positivity
    have a6 : 0 ≤ x ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith
  have h3 : 0 ≤ P.e ^ 2 / (2 * π ^ 2) := by positivity
  simp only [uCoef, cOne, wOne, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
    abs_of_nonneg h3, mul_one]
  calc |1 - 2 * x| * (P.e ^ 2 / (2 * π ^ 2)) * |x ^ 2 / 2 - x ^ 3 / 3|
      ≤ 1 * (P.e ^ 2 / (2 * π ^ 2)) * 1 := by gcongr
    _ = P.e ^ 2 / (2 * π ^ 2) := by ring

theorem norm_vCoef_le (P : Params) {ε x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : ‖vCoef P ε x‖ ≤ P.e ^ 2 / (4 * π ^ 2) := by
  have h1 : |1 - 2 * x| ≤ 1 := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h3 : 0 ≤ P.e ^ 2 / (4 * π ^ 2) := by positivity
  simp only [vCoef, cTwo, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3,
    abs_of_pos hε, abs_of_pos hx.1]
  calc |1 - 2 * x| * ε * (P.e ^ 2 / (4 * π ^ 2)) * x
      ≤ 1 * 1 * (P.e ^ 2 / (4 * π ^ 2)) * 1 := by
        have := hx.1.le
        have := hx.2.le
        gcongr
    _ = P.e ^ 2 / (4 * π ^ 2) := by ring

/-- **The `x`-integrand and the constant parts are `Good` uniformly**: one constant for all
`ε ∈ (0, 1]` and `x ∈ (0, 1)`. -/
theorem exists_good_gInt (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧
      Good (P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p) C G ∧
      Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) *
        P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p ℓ) C G ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, Good (gInt P ε p' p x) C G := by
  obtain ⟨α, hα⟩ := pauliChain_quadratic P.e P.m p' p
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  obtain ⟨C0, hC0, hC⟩ := exists_good_pieces (Mlo := P.m) hm hmγ hΛ hm hp' hp hp0' hp0
    (continuous_pauliChain P.e P.m p' p) hα hCN
  set R : ℝ := P.e ^ 2 / (2 * π ^ 2) + P.e ^ 2 / (4 * π ^ 2)
  have hR : 0 ≤ R := by positivity
  set S : ℝ := ‖(P.loopCoeff 0 : ℂ)‖ + ‖(P.loopCoeff 1 : ℂ)‖ + ‖(P.loopCoeff 2 : ℂ)‖
  have hS : 0 ≤ S := by positivity
  refine ⟨(1 + S * R) * C0, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨G0, hG0, h4, hs4, hq⟩ := hC ε hε hε1
  have hSR : 1 ≤ 1 + S * R := by nlinarith
  refine ⟨fun v => (1 + S * R) * G0 v, fun v => by have := hG0 v; positivity,
    h4.mono (le_mul_of_one_le_left hC0 hSR) (fun v => le_mul_of_one_le_left (hG0 v) hSR),
    hs4.mono (le_mul_of_one_le_left hC0 hSR) (fun v => le_mul_of_one_le_left (hG0 v) hSR),
    fun x hx => ?_⟩
  have hmass : ∀ f, P.m ≤ P.mass f := by
    intro f; fin_cases f
    · exact le_rfl
    · exact hM₁.le
    · exact hM₂.le
  have hin : ∀ f, Good (fun k => uCoef P x *
      qInt 2 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ (P.mass f) ε x p' p k +
        vCoef P ε x * qInt 1 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ (P.mass f) ε x p' p k)
      (R * C0) (fun v => R * G0 v) := by
    intro f
    obtain ⟨q1, q2⟩ := hq (P.mass f) (hmass f) x hx
    have h := (q2.mul_le (norm_uCoef_le P hx)).add (q1.mul_le (norm_vCoef_le P hε hε1 hx))
    refine h.mono (le_of_eq ?_) (fun v => le_of_eq ?_)
    · simp only [R]; ring
    · simp only [R]; ring
  have h0 := (hin 0).mul_le (c := (P.loopCoeff 0 : ℂ)) le_rfl
  have h1 := (hin 1).mul_le (c := (P.loopCoeff 1 : ℂ)) le_rfl
  have h2 := (hin 2).mul_le (c := (P.loopCoeff 2 : ℂ)) le_rfl
  have h := (h0.add h1).add h2
  refine (h.congr fun k => ?_).mono ?_ ?_
  · rw [gInt_eq, Fin.sum_univ_three]
  · have : S * (R * C0) ≤ (1 + S * R) * C0 := by nlinarith
    simp only [S] at this ⊢
    linarith
  · intro v
    have hv := hG0 v
    have : S * (R * G0 v) ≤ (1 + S * R) * G0 v := by nlinarith
    simp only [S] at this ⊢
    linarith

theorem measurable_gInt (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      gInt P ε p' p q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst.fst
  have hs : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    (VertexLimit.continuous_dot_comp hℓ hℓ).measurable
  have hx : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => q.1.2 := measurable_fst.snd
  have hN := ((continuous_pauliChain P.e P.m p' p).comp hℓ).measurable
  have hD : ∀ (M e : ℝ) (c : Fin 4 → ℝ), Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      denom M e (c + (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)) := fun M e c =>
    (continuous_denom_joint continuous_const continuous_const (continuous_const.add hℓ)).measurable
  have hD0 : ∀ (M e : ℝ), Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      denom M e (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := fun M e =>
    (continuous_denom_joint continuous_const continuous_const hℓ).measurable
  have hc : ∀ {r : ((Fin 3 → ℝ) × ℝ) × ℝ → ℝ}, Measurable r →
      Measurable fun q => ((r q : ℝ) : ℂ) := fun hr => Complex.measurable_ofReal.comp hr
  have hA : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
    unfold P4 prodIntegrand
    exact hN.mul (((hD P.m ε p').mul (hD P.m ε p)).inv.mul
      (Finset.measurable_prod _ fun j _ => (hD0 _ _).inv))
  have hB : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      vpRatSum P ε (Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)) q.1.2 := by
    unfold vpRatSum vacuumPolarizationFeynmanMass
    refine Finset.measurable_sum _ fun f _ => ?_
    refine (measurable_const.mul (hc ((measurable_const.sub (hx.const_mul 2)).mul hs))).div
      ((hc (measurable_const.add ((hx.mul (measurable_const.sub hx)).mul hs))).sub
        measurable_const)
  have hC : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      I * cOne P * wOne q.1.2 * ((Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) : ℝ) : ℂ) + (ε : ℂ) * cTwo P * ((q.1.2 : ℝ) : ℂ) := by
    unfold wOne
    exact ((measurable_const.mul (hc (((hx.pow_const 2).div_const 2).sub
      ((hx.pow_const 3).div_const 3)))).mul (hc hs)).add (measurable_const.mul (hc hx))
  exact (hA.mul hB).mul hC

theorem efi_sub {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) (hG : EFInt G) :
    energyFirstIntegral (fun ℓ => F ℓ - G ℓ) = energyFirstIntegral F - energyFirstIntegral G := by
  have h := efi_add hF (hG.const_mul (-1))
  rw [efi_const_mul] at h
  have e : (fun ℓ => F ℓ - G ℓ) = fun ℓ => F ℓ + -1 * G ℓ := funext fun ℓ => by ring
  rw [e, h]
  ring

/-- **The energy-first integral of the outer integrand after Fubini in `x`**, at fixed
`ε ∈ (0, 1]`, given the uniform bounds. -/
theorem efi_hInt_eq (P : Params) {ε : ℝ} (hε : 0 < ε) (p' p : Fin 4 → ℝ) {C : ℝ}
    {G : (Fin 3 → ℝ) → ℝ}
    (h4 : Good (P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p) C G)
    (hs4 : Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) *
        P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p ℓ) C G)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, Good (gInt P ε p' p x) C G) :
    energyFirstIntegral (hInt P ε p' p) =
      kappaVP P * (I * cOne P * (1 / 6) * logSum P ε) *
          energyFirstIntegral (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) *
            P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p ℓ) +
        kappaVP P * ((ε : ℂ) * cTwo P * logSum P ε) *
          energyFirstIntegral (P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p) -
        kappaVP P * ∫ x in (0 : ℝ)..1, energyFirstIntegral (gInt P ε p' p x) := by
  obtain ⟨i1, i2⟩ := integrable_of_good (gInt P ε p' p) (measurable_gInt P ε p' p) hg
  obtain ⟨hI, hE⟩ := efi_intervalIntegral_swap (gInt P ε p' p) i1 i2
  have e : hInt P ε p' p = fun k =>
      (kappaVP P * (I * cOne P * (1 / 6) * logSum P ε) *
          ((Minkowski.dot k k : ℂ) * P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k) +
        kappaVP P * ((ε : ℂ) * cTwo P * logSum P ε) *
          P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k) -
        kappaVP P * ∫ x in (0 : ℝ)..1, gInt P ε p' p x k :=
    funext fun k => hInt_eq P hε p' p k
  rw [e, efi_sub ((hs4.1.1.const_mul _).add (h4.1.1.const_mul _)) (hI.const_mul _),
    efi_add (hs4.1.1.const_mul _) (h4.1.1.const_mul _), efi_const_mul, efi_const_mul,
    efi_const_mul, hE]

/-- The `x`-integrand of the energy-first integral is bounded uniformly. -/
theorem norm_efi_gInt_le {P : Params} {ε : ℝ} {p' p : Fin 4 → ℝ} {C : ℝ}
    {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ x ∈ Ioo (0 : ℝ) 1, Good (gInt P ε p' p x) C G) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : ‖energyFirstIntegral (gInt P ε p' p x)‖ ≤ C * I5 :=
  (hg x hx).1.norm_efi_le

/-- The `x`-integrand of the energy-first integral is measurable. -/
theorem aestronglyMeasurable_efi_gInt (P : Params) (ε : ℝ) (p' p : Fin 4 → ℝ) {C : ℝ}
    {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ x ∈ Ioo (0 : ℝ) 1, Good (gInt P ε p' p x) C G) :
    AEStronglyMeasurable (fun x => energyFirstIntegral (gInt P ε p' p x))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨-, i2⟩ := integrable_of_good (gInt P ε p' p) (measurable_gInt P ε p' p) hg
  exact i2.integral_prod_right.aestronglyMeasurable

end QED.TwoLoop.VPHalfAtAssembly

end
