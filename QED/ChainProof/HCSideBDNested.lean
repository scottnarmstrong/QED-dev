/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDMatch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The nested value of the bubble–`δ₃` and `δ₃`–bubble classes, from their nested form

Helper level, Phase 5 Stage 1a (O3-6 for `QED.ChainProof.Enum.repBD s`, `repDB s`).

* **`tendsto_efi_pauliNum_bdIntegrand`**: the energy-first integral of the Pauli projection of the
  bubble–`δ₃` outer integrand `QED.ChainProof.HCSide.bdIntegrand` tends, as `ε → 0⁺`, to
  `i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ 2 y² m² sidePhoton(K)`, the one-loop Pauli functional of the
  photon function `QED.ChainProof.HCSide.sidePhoton = (δ₃/2) Π_loop(s) s² D(s)³`. This is proved
  with no hypothesis beyond `ChainAdmissible` and an admissible pair: the generic engine
  (`QED.TwoLoop.VPHalfAtGen.tendsto_efi_hIntG`) for the two five-denominator pieces, the
  difference quotients of `QED/ChainProof/HCSideBDLimit.lean`, the five-denominator kernel
  values (`QED.ChainProof.HCSide.s2Prod5Limit_pauliChain_eq_kernVP_all`) and the outer form
  `QED.ChainProof.HCSide.outer_eq_side`.
* `BDNestedForm C r`: the **nested form** of a representative at fixed `ε > 0`: every entry of
  its class vertex is `(r/i)` times the energy-first integral of the corresponding entry of
  `bdIntegrand`, and that entry is integrable in both stages. This is the content of the Wick step
  (the amplitude of `repBD s`), the Fubini step (nested equals joint) and the closed form of the
  inner bubble, with the overall constant `r` left open.
* **`repNested_of_bdNestedForm`**: `BDNestedForm C r → RepNested C (r · sidePhoton)`. With
  `r = 1` this is the input `RepNested (repBD s) sidePhoton` (resp. `repDB s`) of
  `QED.ChainProof.HCSide.classLinks_of_reps`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel (Params Contraction vacuumPolarizationLoop)
open QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero
open QED.ChainProof.HCValue QED.ChainProof.HCLimit
open QED.TwoLoop.VPHalfAtAssembly (cOne uCoef wOne logSum specMu specMu_ge mass_ge
  ae_specMu_ne ae_ne_one_real mem_Ioo_of_uIoc ev_pos_le_one mem_Ioo_mul_pos)
open QED.TwoLoop.VPHalfAtLimit (massShift s2Prod5Limit pauliChain_bound continuous_pauliChain
  pauliChain_quadratic)
open QED.TwoLoop.VPHalfAtGen
open QED.TwoLoop.VPHalf (kernVP integrable_kern5 ae_feynmanMeasure_ne_one vpK)
open QED.Integration (feynmanMeasure)
open QED.OneLoop (energyFirstIntegral)

/-! ### The limit in terms of the generic engine -/

/-- The limit of `QED.TwoLoop.VPHalfAtGen.tendsto_efi_hIntG` over the masses `(a, b, a, b, M)`. -/
noncomputable def sideL (P : Params) (α : ℂ) (p' p : Fin 4 → ℝ) (M : ℝ) : ℂ :=
  (I * cOne P * (1 / 6) * logSum P 0) *
      powLimit α (pauliChain P.e P.m p' p) P.m p' p 1 (sideMs P.mγ P.Λ M) -
    ∫ x in (0 : ℝ)..1, phiZeroG P α p' p (sideMs P.mγ P.Λ M) x

theorem sideMs_ge' (P : Params) {M : ℝ} (hM : min P.mγ P.m ≤ M) (hmγΛ : P.mγ < P.Λ) :
    ∀ i, min P.mγ P.m ≤ sideMs P.mγ P.Λ M i :=
  sideMs_ge (min_le_left _ _) ((min_le_left _ _).trans hmγΛ.le) hM

/-- The limit of the Pauli-projected bubble–`δ₃` integrand in terms of `sideL`. -/
theorem tendsto_efi_pauliNum_bdIntegrand_L (P : Params) (hA : ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    Tendsto (fun ε => energyFirstIntegral fun k =>
        pauliNum P.m p' p (fun μ => bdIntegrand P p' p μ ε k)) (𝓝[>] 0)
      (𝓝 ((-(I / 2) * P.δ₃) * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        (((P.Λ ^ 2 : ℝ) : ℂ) * sideL P α p' p P.Λ -
          ((P.mγ ^ 2 : ℝ) : ℂ) * sideL P α p' p P.mγ))) := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hM₀ : 0 < min P.mγ P.m := lt_min hA.hmγ hA.hm
  have hM₀m : min P.mγ P.m ≤ P.m := min_le_right _ _
  have hgb := sideMs_ge' P (M := P.Λ) ((min_le_left _ _).trans hA.hmγΛ.le) hA.hmγΛ
  have hga := sideMs_ge' P (M := P.mγ) (min_le_left _ _) hA.hmγΛ
  have Tb := tendsto_efi_hIntG P hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m (k := 2 + 1) (by omega)
    (sideMs P.mγ P.Λ P.Λ) hgb hp' hp hp0' hp0 hα
  have Ta := tendsto_efi_hIntG P hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m (k := 2 + 1) (by omega)
    (sideMs P.mγ P.Λ P.mγ) hga hp' hp hp0' hp0 hα
  have L := (((tendsto_massShift_nhds P.Λ).mul Tb).sub
    ((tendsto_massShift_nhds P.mγ).mul Ta)).const_mul
    ((-(I / 2) * P.δ₃) * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ))
  refine L.congr' ?_
  filter_upwards [ev_pos_le_one] with ε ⟨hε, hε1⟩
  have ib := efInt_hIntG P hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m (k := 2 + 1) (by omega)
    (sideMs P.mγ P.Λ P.Λ) hgb hp' hp hp0' hp0 hε hε1
  have ia := efInt_hIntG P hA.hm hA.hM₁ hA.hM₂ hM₀ hM₀m (k := 2 + 1) (by omega)
    (sideMs P.mγ P.Λ P.mγ) hga hp' hp hp0' hp0 hε hε1
  have e : (fun k => pauliNum P.m p' p (fun μ => bdIntegrand P p' p μ ε k)) = fun k =>
      ((-(I / 2) * P.δ₃) * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ)) *
        (massShift P.Λ ε * hIntG P (sideMs P.mγ P.Λ P.Λ) ε p' p k -
          massShift P.mγ ε * hIntG P (sideMs P.mγ P.Λ P.mγ) ε p' p k) :=
    funext fun k => pauliNum_bdIntegrand P hA.hm.ne' hε hp' hp hq k
  rw [e, efi_const_mul, QED.TwoLoop.VPHalfAtAssembly.efi_sub (ib.const_mul _) (ia.const_mul _),
    efi_const_mul, efi_const_mul]

/-! ### The value -/

theorem specLimit_one (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (M x : ℝ) :
    specLimit α N m p' p j 1 Ms ![M] ![x] = ((x * (1 - x) : ℝ) : ℂ)⁻¹ *
      powLimit α N m p' p j (Fin.snoc Ms (specMu M x) : Fin (k + 1 + 2) → ℝ) := rfl

/-- The real bracket of kernels in photon form, integrated. -/
theorem integral_bracket_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hmγΛ : P.mγ < P.Λ)
    {s : ℝ} (hs : 0 ≤ s) {M x : ℝ} (hμa : specMu M x ^ 2 ≠ P.mγ ^ 2)
    (hμb : specMu M x ^ 2 ≠ P.Λ ^ 2) :
    P.Λ ^ 2 / (specMu M x ^ 2 - P.Λ ^ 2) * ((∫ z, kernVP P.m P.mγ P.Λ P.Λ s z ∂feynmanMeasure) -
        ∫ z, kernVP P.m P.mγ P.Λ (specMu M x) s z ∂feynmanMeasure) -
      P.mγ ^ 2 / (specMu M x ^ 2 - P.mγ ^ 2) *
        ((∫ z, kernVP P.m P.mγ P.Λ P.mγ s z ∂feynmanMeasure) -
          ∫ z, kernVP P.m P.mγ P.Λ (specMu M x) s z ∂feynmanMeasure) =
      ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2)⁻¹ * ∫ z, sideX P s M x z ∂feynmanMeasure := by
  have hΛ : 0 < P.Λ := hmγ.trans hmγΛ
  have hab : (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 ≠ 0 := by
    have : P.mγ ^ 2 < P.Λ ^ 2 := by gcongr
    positivity
  have iA : ∀ μ, Integrable (kernVP P.m P.mγ P.Λ μ s) feynmanMeasure := fun μ =>
    integrable_kern5 hmγ hΛ hm hs
  have hX : ∫ z, sideX P s M x z ∂feynmanMeasure = (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
      (P.Λ ^ 2 / (specMu M x ^ 2 - P.Λ ^ 2) * ((∫ z, kernVP P.m P.mγ P.Λ P.Λ s z ∂feynmanMeasure) -
        ∫ z, kernVP P.m P.mγ P.Λ (specMu M x) s z ∂feynmanMeasure) -
      P.mγ ^ 2 / (specMu M x ^ 2 - P.mγ ^ 2) *
        ((∫ z, kernVP P.m P.mγ P.Λ P.mγ s z ∂feynmanMeasure) -
          ∫ z, kernVP P.m P.mγ P.Λ (specMu M x) s z ∂feynmanMeasure)) := by
    have hc : ∫ z, sideX P s M x z ∂feynmanMeasure = ∫ z, (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 *
        (P.Λ ^ 2 / (specMu M x ^ 2 - P.Λ ^ 2) *
            (kernVP P.m P.mγ P.Λ P.Λ s z - kernVP P.m P.mγ P.Λ (specMu M x) s z) -
          P.mγ ^ 2 / (specMu M x ^ 2 - P.mγ ^ 2) *
            (kernVP P.m P.mγ P.Λ P.mγ s z - kernVP P.m P.mγ P.Λ (specMu M x) s z))
          ∂feynmanMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [ae_feynmanMeasure_ne_one] with z hz
      exact (kernVP_side_eq_photon hm hs hz.1 hz.2 hμa hμb).symm
    have i1 : Integrable (fun z => P.Λ ^ 2 / (specMu M x ^ 2 - P.Λ ^ 2) *
        (kernVP P.m P.mγ P.Λ P.Λ s z - kernVP P.m P.mγ P.Λ (specMu M x) s z)) feynmanMeasure :=
      ((iA _).sub (iA _)).const_mul _
    have i2 : Integrable (fun z => P.mγ ^ 2 / (specMu M x ^ 2 - P.mγ ^ 2) *
        (kernVP P.m P.mγ P.Λ P.mγ s z - kernVP P.m P.mγ P.Λ (specMu M x) s z)) feynmanMeasure :=
      ((iA _).sub (iA _)).const_mul _
    rw [hc, integral_const_mul, integral_sub i1 i2, integral_const_mul, integral_const_mul,
      integral_sub (iA _) (iA _), integral_sub (iA _) (iA _)]
  rw [hX, ← mul_assoc, inv_mul_cancel₀ hab, one_mul]

theorem logSum_zero_eq (P : Params) :
    logSum P 0 = (((∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2) : ℝ)) : ℂ) := by
  simp only [logSum]
  push_cast
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Complex.ofReal_log (sq_nonneg _)]
  push_cast
  ring_nf

/-- **The value of the bubble–`δ₃` limit**: `-(i/2) δ₃ (b² - a²)² (b² L_b - a² L_a)` is the
one-loop Pauli functional of `sidePhoton`. -/
theorem side_value_eq (P : Params) (hA : ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : IsPairQ P.m p' p) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain P.e P.m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    (-(I / 2) * P.δ₃) * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        (((P.Λ ^ 2 : ℝ) : ℂ) * sideL P α p' p P.Λ - ((P.mγ ^ 2 : ℝ) : ℂ) * sideL P α p' p P.mγ) =
      pauliConst P.e P.m (Minkowski.dot (p' - p) (p' - p)) *
        ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
          sidePhoton P (vpK P.m (Minkowski.dot (p' - p) (p' - p)) z)) ∂feynmanMeasure : ℝ) :
            ℂ) := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm := hA.hm
  have hmγ := hA.hmγ
  have hΛ := hA.hΛ
  have hab : P.mγ ≠ P.Λ := hA.hmγΛ.ne
  have hmass : ∀ f, 0 < P.mass f := fun f => hm.trans_le (mass_ge hA.hM₁ hA.hM₂ f)
  set s := Minkowski.dot (p' - p) (p' - p)
  set N := pauliChain P.e P.m p' p
  set Kc := pauliConst P.e P.m s
  set E : ℝ := P.e ^ 2 / (8 * π ^ 2)
  set B : ℝ := (P.Λ ^ 2 - P.mγ ^ 2) ^ 2
  have hB : B ≠ 0 := by
    have : P.mγ ^ 2 < P.Λ ^ 2 := by gcongr; exact hA.hmγΛ
    simp only [B]; positivity
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  have hNc := continuous_pauliChain P.e P.m p' p
  -- the five-denominator values
  have hP2 : ∀ M, 0 < M → powLimit α N P.m p' p 2 (sideMs P.mγ P.Λ M) =
      Kc * ((E * ∫ z, kernVP P.m P.mγ P.Λ M s z ∂feynmanMeasure : ℝ) : ℂ) := fun M hM => by
    rw [powLimit_two_sideMs hm hmγ hΛ hM hp' hp hp0' hp0 hNc hα hCN,
      s2Prod5Limit_pauliChain_eq_kernVP_all P.e hm hmγ hΛ hM hp' hp hp0' hp0 hq hab hα]
    rfl
  -- the constant part
  have iK : ∀ μ, Integrable (kernVP P.m P.mγ P.Λ μ s) feynmanMeasure := fun μ =>
    integrable_kern5 hmγ hΛ hm hq.le
  have hC : ∫ z, sideC P s z ∂feynmanMeasure = B *
      ((∫ z, kernVP P.m P.mγ P.Λ P.mγ s z ∂feynmanMeasure) -
        ∫ z, kernVP P.m P.mγ P.Λ P.Λ s z ∂feynmanMeasure) := by
    rw [← integral_sub (iK _) (iK _), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure_ne_one] with z hz
    exact sideC_eq_kernVP P hm hq.le hz.1 hz.2
  have h1 := powLimit_one_comb hm hmγ hΛ hp' hp hp0' hp0 hNc hα hCN (a := P.mγ) (b := P.Λ)
  rw [hP2 _ hmγ, hP2 _ hΛ] at h1
  -- the spectral part, pointwise in `x`
  have hae : ∀ f : Fin 3, ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo (0 : ℝ) 1 →
      specMu (P.mass f) x ≠ P.mγ ∧ specMu (P.mass f) x ≠ P.Λ := fun f => by
    filter_upwards [ae_specMu_ne (M := P.mass f) hmγ, ae_specMu_ne (M := P.mass f) hΛ]
      with x h1 h2 hx
    exact ⟨h1 hx, h2 hx⟩
  set J : ℝ := ∫ x in (0 : ℝ)..1, ∑ f, P.loopCoeff f * ((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) *
    ∫ z, (x * (1 - x))⁻¹ * sideX P s (P.mass f) x z ∂feynmanMeasure)
  have hphi : ∫ x in (0 : ℝ)..1, (((P.Λ ^ 2 : ℝ) : ℂ) *
        phiZeroG P α p' p (sideMs P.mγ P.Λ P.Λ) x -
      ((P.mγ ^ 2 : ℝ) : ℂ) * phiZeroG P α p' p (sideMs P.mγ P.Λ P.mγ) x) =
      (I * cOne P * Kc * ((E / B : ℝ) : ℂ)) * (J : ℂ) := by
    simp only [J]
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae 0, hae 1, hae 2, ae_ne_one_real] with x a0 a1 a2 hx1 hx
    have hx' := mem_Ioo_of_uIoc hx hx1
    have hxp := mem_Ioo_mul_pos hx'
    simp only [phiZeroG, specLimit_one]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hf : specMu (P.mass f) x ≠ P.mγ ∧ specMu (P.mass f) x ≠ P.Λ := by
      fin_cases f
      · exact a0 hx'
      · exact a1 hx'
      · exact a2 hx'
    set μ := specMu (P.mass f) x
    have hμ : 0 < μ := (hmass f).trans_le (specMu_ge (hmass f) hx')
    have hμa : μ ^ 2 ≠ P.mγ ^ 2 := fun h => hf.1 (by
      have := (sq_eq_sq₀ hμ.le hmγ.le).1 h; exact this)
    have hμb : μ ^ 2 ≠ P.Λ ^ 2 := fun h => hf.2 (by
      have := (sq_eq_sq₀ hμ.le hΛ.le).1 h; exact this)
    rw [powLimit_two_snoc hm hmγ hΛ hΛ hμ hμb hp' hp hp0' hp0 hNc hα hCN,
      powLimit_two_snoc hm hmγ hΛ hmγ hμ hμa hp' hp hp0' hp0 hNc hα hCN,
      hP2 _ hΛ, hP2 _ hmγ, hP2 _ hμ]
    have hbr := integral_bracket_eq P hm hmγ hA.hmγΛ hq.le (M := P.mass f) (x := x) hμa hμb
    rw [integral_const_mul]
    set KA := ∫ z, kernVP P.m P.mγ P.Λ P.mγ s z ∂feynmanMeasure
    set KB := ∫ z, kernVP P.m P.mγ P.Λ P.Λ s z ∂feynmanMeasure
    set KM := ∫ z, kernVP P.m P.mγ P.Λ μ s z ∂feynmanMeasure
    set X := ∫ z, sideX P s (P.mass f) x z ∂feynmanMeasure
    have hbr' : ((P.Λ ^ 2 / (μ ^ 2 - P.Λ ^ 2) * (KB - KM) -
        P.mγ ^ 2 / (μ ^ 2 - P.mγ ^ 2) * (KA - KM) : ℝ) : ℂ) = ((B⁻¹ * X : ℝ) : ℂ) := by
      rw [hbr]
    simp only [uCoef, wOne]
    push_cast at hbr' ⊢
    linear_combination ((P.loopCoeff f : ℂ) * (1 - 2 * (x : ℂ)) * I * cOne P *
      ((x : ℂ) ^ 2 / 2 - (x : ℂ) ^ 3 / 3) * ((x : ℂ) * (1 - (x : ℂ)))⁻¹ * Kc * (E : ℂ)) * hbr'
  -- assembling
  have hM₀ : 0 < min P.mγ P.m := lt_min hmγ hm
  have hM₀m : min P.mγ P.m ≤ P.m := min_le_right _ _
  have hφb := intervalIntegrable_phiZeroG P hm hA.hM₁ hA.hM₂ hM₀ hM₀m (k := 2 + 1) (by omega)
    (sideMs P.mγ P.Λ P.Λ) (sideMs_ge' P ((min_le_left _ _).trans hA.hmγΛ.le) hA.hmγΛ)
    hp' hp hp0' hp0 hα
  have hφa := intervalIntegrable_phiZeroG P hm hA.hM₁ hA.hM₂ hM₀ hM₀m (k := 2 + 1) (by omega)
    (sideMs P.mγ P.Λ P.mγ) (sideMs_ge' P (min_le_left _ _) hA.hmγΛ) hp' hp hp0' hp0 hα
  have hsplit : ((P.Λ ^ 2 : ℝ) : ℂ) * sideL P α p' p P.Λ -
      ((P.mγ ^ 2 : ℝ) : ℂ) * sideL P α p' p P.mγ =
      (I * cOne P * (1 / 6) * logSum P 0) *
        (((P.Λ ^ 2 : ℝ) : ℂ) * powLimit α N P.m p' p 1 (sideMs P.mγ P.Λ P.Λ) -
          ((P.mγ ^ 2 : ℝ) : ℂ) * powLimit α N P.m p' p 1 (sideMs P.mγ P.Λ P.mγ)) -
      ∫ x in (0 : ℝ)..1, (((P.Λ ^ 2 : ℝ) : ℂ) * phiZeroG P α p' p (sideMs P.mγ P.Λ P.Λ) x -
        ((P.mγ ^ 2 : ℝ) : ℂ) * phiZeroG P α p' p (sideMs P.mγ P.Λ P.mγ) x) := by
    simp only [sideL]
    rw [intervalIntegral.integral_sub (hφb.const_mul _) (hφa.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hsplit, h1, hphi, outer_eq_side P hm hmγ hΛ hmass hq.le, hC, logSum_zero_eq]
  set KA := ∫ z, kernVP P.m P.mγ P.Λ P.mγ s z ∂feynmanMeasure
  set KB := ∫ z, kernVP P.m P.mγ P.Λ P.Λ s z ∂feynmanMeasure
  set L₀ := ∑ f, P.loopCoeff f * Real.log (P.mass f ^ 2)
  have hBc : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB
  have hEB : ((B : ℝ) : ℂ) * ((E : ℂ) / ((B : ℝ) : ℂ)) = (E : ℂ) := by field_simp
  simp only [cOne]
  push_cast
  linear_combination (-(1 / 2) * (P.δ₃ : ℂ) * ((P.e : ℂ) ^ 2 / (2 * (π : ℂ) ^ 2)) * Kc *
      ((B : ℂ) * (1 / 6) * (L₀ : ℂ) * (E : ℂ) * ((KA : ℂ) - (KB : ℂ)) -
        (B : ℂ) * ((E : ℂ) / (B : ℂ)) * (J : ℂ))) * Complex.I_sq +
    (-(1 / 2) * (P.δ₃ : ℂ) * ((P.e : ℂ) ^ 2 / (2 * (π : ℂ) ^ 2)) * Kc * (J : ℂ)) * hEB

/-- **The `ε → 0⁺` limit of the Pauli-projected bubble–`δ₃` outer integrand**: the one-loop Pauli
functional of `sidePhoton`, at every admissible pair, with no further hypothesis. -/
theorem tendsto_efi_pauliNum_bdIntegrand (P : Params) (hA : ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) :
    Tendsto (fun ε => energyFirstIntegral fun k =>
        pauliNum P.m p' p (fun μ => bdIntegrand P p' p μ ε k)) (𝓝[>] 0)
      (𝓝 (pauliConst P.e P.m (Minkowski.dot (p' - p) (p' - p)) *
        ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
          sidePhoton P (vpK P.m (Minkowski.dot (p' - p) (p' - p)) z)) ∂feynmanMeasure : ℝ) :
            ℂ))) := by
  obtain ⟨α, hα⟩ := pauliChain_quadratic P.e P.m p' p
  rw [← side_value_eq P hA hpq hα]
  exact tendsto_efi_pauliNum_bdIntegrand_L P hA hpq hα

/-! ### The nested value from the nested form -/

/-- **The nested form of a bubble–`δ₃` (or `δ₃`–bubble) representative** with overall constant
`r`: at admissible parameters and pairs, for all small `ε > 0`, every entry of the class vertex is
`(r/i)` times the energy-first integral of the corresponding entry of `bdIntegrand`, and that
entry is integrable in both stages of (D). -/
def BDNestedForm {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (r : ℝ) : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ p' p : Fin 4 → ℝ, IsPairQ P.m p' p →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ μ α β : Fin 4,
      classV C { P with ε := ε } p' p μ α β =
        ((r : ℂ) / I) * energyFirstIntegral (fun k => bdIntegrand P p' p μ ε k α β) ∧
      EFInt (fun k => bdIntegrand P p' p μ ε k α β)

/-- **`RepNested` from the nested form**: a representative in nested form with constant `r` has
the nested value `e² outerAt m q² (r · sidePhoton)`. -/
theorem repNested_of_bdNestedForm {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    {r : ℝ} (hC : BDNestedForm C r) :
    RepNested C (fun P t => r * sidePhoton P t) := by
  intro P hA
  filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
  intro Y hY
  have hpq := isPairQ_canonical' hA.hm hQ
  have hdot := dot_boostMomentum_sub_restMomentum hA.hm hQ.le
  set p' := boostMomentum P.m Q
  set p := restMomentum P.m
  refine formFactorProj₂_of_pauliNum hA.he hA.hm hQ hdot ?_
  have hT := (tendsto_efi_pauliNum_bdIntegrand P hA hpq).const_mul ((r : ℂ) / I)
  rw [hdot] at hT
  have hsum : Tendsto (fun ε => ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 *
      classV C { P with ε := ε } p' p j.1 j.2.1 j.2.2) (𝓝[>] 0)
      (𝓝 (pauliNum P.m p' p Y)) := by
    rw [pauliNum_eq_sum_idx]
    exact tendsto_finsetSum _ fun j _ => (hY j.1 j.2.1 j.2.2).const_mul _
  have hval := tendsto_nhds_unique hsum (hT.congr' ?_)
  · rw [hval]
    have e : ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 * (r * sidePhoton P (vpK P.m Q z))) ∂feynmanMeasure =
        r * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 * sidePhoton P (vpK P.m Q z)) ∂feynmanMeasure := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    rw [e]
    push_cast
    ring
  · filter_upwards [hC P hA p' p hpq] with ε hε
    have hI : ∀ j : Idx, EFInt fun k => pauliWt P.m p' p j.1 j.2.1 j.2.2 *
        bdIntegrand P p' p j.1 ε k j.2.1 j.2.2 := fun j =>
      (hε j.1 j.2.1 j.2.2).2.const_mul _
    have e : (fun k => pauliNum P.m p' p (fun μ => bdIntegrand P p' p μ ε k)) =
        fun k => ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 *
          bdIntegrand P p' p j.1 ε k j.2.1 j.2.2 :=
      funext fun k => pauliNum_eq_sum_idx _ _ _ _
    rw [e, efi_sum _ fun j _ => hI j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [efi_const_mul, (hε j.1 j.2.1 j.2.2).1]
    ring

end QED.ChainProof.HCSide

end
