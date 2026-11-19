/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideKernel
public import QED.ChainProof.HCLimitDDLimit
public import QED.TwoLoop.VPUnitNestedAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The nested value of the `δ₃`–`δ₃` classes of set (b) at fixed `q`

Helper level, Phase 5 Stage 1a (O3-6 for the one-loop classes, at fixed `q`). The value (T₁₀) of
each `δ₃`–`δ₃` representative `QED.ChainProof.Enum.repDD s₀ s₁` is the energy-first integral of
the one-loop vertex chain with the double insertion `ddInsertion`
(`QED.ChainProof.HCLimit.contractionValue₂_repDD`), here `ddIntegrand`.

* `pauliNum_ddIntegrand`: **the Pauli projection of the integrand**, exactly at `ε > 0`, is
  `(δ₃²/4)(Λ² - m_γ²)²` times the difference of the `(k²)²`, five-denominator vertices with masses
  `(m_γ, Λ, m_γ, Λ, m_γ)` and `(m_γ, Λ, m_γ, Λ, Λ)` (`ddInsertion_eq`, the `δ₃` numerator
  `QED.TwoLoop.VPUnitNested.pauliNum_numD3`, whose longitudinal part has no Pauli component, and
  `d(k) = D_{m_γ}⁻¹ - D_Λ⁻¹`).
* `efInt_ddIntegrand`: each entry of the integrand is integrable in both stages of (D).
* `tendsto_efi_pauliNum_ddIntegrand`: its energy-first integral converges to
  `(δ₃²/4) i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ 2 y² m² K² D(K)³`, the one-loop vertex with the
  photon function `(δ₃²/4) k⁴ D(k²)³` (`QED.ChainProof.HCSide.s2Prod5Limit_pauliChain_eq_kernVP_all`
  and `QED.ChainProof.HCSide.kernVP_sub_eq_photon`).
* **`formFactorProj₂_repDD`**: every `ε → 0⁺` limit `Y` of the class vertex
  `QED.ChainProof.HCValue.classV (repDD s₀ s₁)` at an admissible pair has Pauli projection
  `e² outerAt m q² ((δ₃²/4) s² D(s)³)`. With `enumPhoton r P` for `r = 5, …, 8` this is the
  `δ₃`–`δ₃` part of `QED.ChainProof.HCValue.ClassNestedAtLink enumClass enumPhoton`
  (`classNestedAt_enum_DD`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.ChainProof.Enum QED.ChainProof.HCValue QED.ChainProof.HCLimit
open QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalf (kern5 kernVP integrable_kern5 ae_feynmanMeasure_ne_one vpK)
open QED.TwoLoop.UnitVPLink (photonD)
open QED.Integration (feynmanMeasure)

/-- The `δ₃`–`δ₃` integrand: the one-loop vertex chain with the double insertion. -/
noncomputable def ddIntegrand (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ε : ℝ)
    (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
    (QED.OneLoop.electronPropagator P.m ε (p + k)) (ddInsertion P.δ₃ P.mγ P.Λ ε k)

/-! ### The Pauli projection of the integrand -/

/-- **The Pauli projection of the `δ₃`–`δ₃` integrand**, exactly at `ε > 0`. -/
theorem pauliNum_ddIntegrand (P : Params) (hm : P.m ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => ddIntegrand P p' p μ ε k) =
      ((P.δ₃ ^ 2 / 4 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        (s2Prod5Integrand (pauliChain P.e P.m p' p) P.m ![P.mγ, P.Λ, P.mγ, P.Λ, P.mγ]
            (fun _ => ε) ε p' p k -
          s2Prod5Integrand (pauliChain P.e P.m p' p) P.m ![P.mγ, P.Λ, P.mγ, P.Λ, P.Λ]
            (fun _ => ε) ε p' p k) := by
  set c : ℂ := ((1 / I) * (-(I / 2) * P.δ₃)) * (((Minkowski.dot k k : ℝ) : ℂ) *
    pvScalar P.mγ P.Λ ε k)
  set s : ℂ := (propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹ *
    (((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹) *
      ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹))
  have e1 : (fun μ => ddIntegrand P p' p μ ε k) = fun μ => (c * s) • numD3 P p' p μ k := by
    funext μ
    have hins : ddInsertion P.δ₃ P.mγ P.Λ ε k = fun ν ρ =>
        c * photonInsertion P.δ₃ P.mγ P.Λ ε k ν ρ :=
      funext fun ν => funext fun ρ => ddInsertion_eq P.δ₃ P.mγ P.Λ ε k ν ρ
    rw [ddIntegrand, hins, vertexChain_smul_photon, integrand_d3_eq P hε.ne', smul_smul]
  have hI : (1 / I) * (-(I / 2) * (P.δ₃ : ℂ)) = -((P.δ₃ : ℂ) / 2) := by
    field_simp
  rw [e1, pauliNum_smul, pauliNum_numD3 P hm hp' hp hq k]
  simp only [c, s, hI, s2Prod5Integrand, Fin.prod_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, ← propDenom_eq_denom]
  change -((P.δ₃ : ℂ) / 2) * (((Minkowski.dot k k : ℝ) : ℂ) *
      ((propDenom P.mγ ε k)⁻¹ - (propDenom P.Λ ε k)⁻¹)) * _ * _ = _
  push_cast
  ring

/-! ### Integrability of the entries -/

theorem efInt_sub {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) (hG : EFInt G) :
    EFInt fun ℓ => F ℓ - G ℓ := by
  have h := hF.add (hG.const_mul (-1))
  simpa [sub_eq_add_neg] using h

/-- The two pieces `ddPiece1`, `ddPiece2` of the `δ₃`–`δ₃` integrand are integrable in both
stages of (D), for `ε > 0`. -/
theorem efInt_ddPieces (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ α β : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    EFInt (ddPiece1 P p' p μ α β ε) ∧ EFInt (ddPiece2 P p' p μ α β ε) := by
  obtain ⟨hI1, -⟩ := exists_tendsto_of_kinds' (by norm_num) kindsDD1 (massesDD1 P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsDD1, massesDD1])
    (fun i hi => by
      obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
      fin_cases i <;> simp_all [kindsDD1, massesDD1])
    (by decide) (by decide) (by decide)
    (fun k => numD3 P p' p μ k α β) (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece1 P p' p μ α β)
    (fun ε hε ℓ => by
      rw [ddPiece1, integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD1, massesDD1,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  obtain ⟨hI2, -⟩ := exists_tendsto_of_kinds' (by norm_num) kindsDD2 (massesDD2 P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsDD2, massesDD2])
    (fun i hi => by
      obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
      fin_cases i <;> simp_all [kindsDD2, massesDD2])
    (by decide) (by decide) (by decide)
    (fun k => numD3 P p' p μ k α β) (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece2 P p' p μ α β)
    (fun ε hε ℓ => by
      rw [ddPiece2, integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD2, massesDD2,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  exact ⟨⟨(hI1 ε hε).1, (hI1 ε hε).2⟩, ⟨(hI2 ε hε).1, (hI2 ε hε).2⟩⟩

/-- **Each entry of the `δ₃`–`δ₃` integrand is integrable in both stages of (D)**, for `ε > 0`. -/
theorem efInt_ddIntegrand (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ α β : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    EFInt fun k => ddIntegrand P p' p μ ε k α β := by
  obtain ⟨h1, h2⟩ := efInt_ddPieces P hm hmγ hΛ hp hp' hq μ α β hε
  have h := (efInt_sub h1 (h2.const_mul (((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))).const_mul
    (ddCoeff P)
  refine ⟨fun v => (h.1 v).congr (Eventually.of_forall fun t => ?_), h.2.congr
    (Eventually.of_forall fun v => integral_congr_ae (Eventually.of_forall fun t => ?_))⟩ <;>
  · simp only [ddIntegrand]
    rw [ddIntegrand_eq P hε]

/-! ### The limit of the Pauli-projected integral -/

theorem efInt_s2Prod5Integrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Ms : Fin 5 → ℝ} (hMs : ∀ j, M₀ ≤ Ms j)
    {ε : ℝ} (hε : 0 < ε) :
    EFInt (s2Prod5Integrand N m Ms (fun _ => ε) ε p' p) := by
  have hes : ∀ j : Fin 5, 0 < (fun _ => ε : Fin 5 → ℝ) j := fun _ => hε
  have i1 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 2, Ms 3, Ms 4]) (es := ![ε, ε, ε])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact hε) hε
  have i2 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 0, Ms 2, Ms 3, Ms 4]) (es := ![ε, ε, ε, ε])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact hε) hε
  have i3 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 1, Ms 2, Ms 3, Ms 4]) (es := ![ε, ε, ε, ε])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact hε) hε
  have i4 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := Ms) (es := fun _ => ε) hMs hes hε
  have h := ((i1.add (i2.const_mul (-massShift (Ms 0) ε))).add
    (i3.const_mul (-massShift (Ms 1) ε))).add
    (i4.const_mul (massShift (Ms 0) ε * massShift (Ms 1) ε))
  have e : s2Prod5Integrand N m Ms (fun _ => ε) ε p' p = fun ℓ =>
      ((prodIntegrand N m ![Ms 2, Ms 3, Ms 4] ![ε, ε, ε] ε p' p ℓ
        + (-massShift (Ms 0) ε) *
          prodIntegrand N m ![Ms 0, Ms 2, Ms 3, Ms 4] ![ε, ε, ε, ε] ε p' p ℓ)
        + (-massShift (Ms 1) ε) *
          prodIntegrand N m ![Ms 1, Ms 2, Ms 3, Ms 4] ![ε, ε, ε, ε] ε p' p ℓ)
        + (massShift (Ms 0) ε * massShift (Ms 1) ε) *
          prodIntegrand N m Ms (fun _ => ε) ε p' p ℓ := by
    funext ℓ
    rw [s2Prod5Integrand_eq N m Ms hes ε p' p ℓ]
    have h3 : (![(fun _ => ε : Fin 5 → ℝ) 2, (fun _ => ε : Fin 5 → ℝ) 3,
        (fun _ => ε : Fin 5 → ℝ) 4] : Fin 3 → ℝ) = ![ε, ε, ε] := rfl
    simp only [h3]
    ring
  rw [e]
  exact h

/-- The constant `i (e q² (4m² + q²)²/m)` of the one-loop Pauli functional. -/
noncomputable def pauliConst (e m s : ℝ) : ℂ :=
  I * ((e : ℂ) * (s : ℂ) * (4 * (m : ℂ) ^ 2 + (s : ℂ)) ^ 2 / m)

/-- **The `ε → 0⁺` limit of the Pauli-projected `δ₃`–`δ₃` integral**: the one-loop Pauli
functional of the photon function `(δ₃²/4) k⁴ D(k²)³`. -/
theorem tendsto_efi_pauliNum_ddIntegrand (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hab : P.mγ ≠ P.Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun k =>
        pauliNum P.m p' p (fun μ => ddIntegrand P p' p μ ε k)) (𝓝[>] 0)
      (𝓝 (pauliConst P.e P.m (Minkowski.dot (p' - p) (p' - p)) *
        ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
          (P.δ₃ ^ 2 / 4 * (vpK P.m (Minkowski.dot (p' - p) (p' - p)) z ^ 2 *
            photonD P.mγ P.Λ (vpK P.m (Minkowski.dot (p' - p) (p' - p)) z) ^ 3)))
          ∂feynmanMeasure : ℝ) : ℂ))) := by
  set q2 := Minkowski.dot (p' - p) (p' - p)
  set a := P.mγ
  set b := P.Λ
  obtain ⟨α, hα⟩ := pauliChain_quadratic P.e P.m p' p
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  set M₀ := min a b
  have hM₀ : 0 < M₀ := lt_min hmγ hΛ
  have hMa : ∀ j, M₀ ≤ (![a, b, a, b, a] : Fin 5 → ℝ) j := fun j => by
    have := min_le_left a b; have := min_le_right a b
    fin_cases j <;> simp <;> linarith
  have hMb : ∀ j, M₀ ≤ (![a, b, a, b, b] : Fin 5 → ℝ) j := fun j => by
    have := min_le_left a b; have := min_le_right a b
    fin_cases j <;> simp <;> linarith
  have lA := tendsto_energyFirstIntegral_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0
    (continuous_pauliChain P.e P.m p' p) hα hCN hMa (l := 𝓝[>] (0 : ℝ)) (ε := id)
    (es := fun ε _ => ε) tendsto_id (fun _ => tendsto_id)
  have lB := tendsto_energyFirstIntegral_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0
    (continuous_pauliChain P.e P.m p' p) hα hCN hMb (l := 𝓝[>] (0 : ℝ)) (ε := id)
    (es := fun ε _ => ε) tendsto_id (fun _ => tendsto_id)
  rw [s2Prod5Limit_pauliChain_eq_kernVP_all P.e hm hmγ hΛ hmγ hp' hp hp0' hp0 hq hab hα] at lA
  rw [s2Prod5Limit_pauliChain_eq_kernVP_all P.e hm hmγ hΛ hΛ hp' hp hp0' hp0 hq hab hα] at lB
  have hlim := (lA.sub lB).const_mul ((P.δ₃ ^ 2 / 4 * (b ^ 2 - a ^ 2) ^ 2 : ℝ) : ℂ)
  -- the value
  have hval : ((P.δ₃ ^ 2 / 4 * (b ^ 2 - a ^ 2) ^ 2 : ℝ) : ℂ) *
      (I * ((P.e : ℂ) * (q2 : ℂ) * (4 * (P.m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / P.m) *
          ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP P.m a b a q2 z ∂feynmanMeasure : ℝ) : ℂ) -
        I * ((P.e : ℂ) * (q2 : ℂ) * (4 * (P.m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / P.m) *
          ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP P.m a b b q2 z ∂feynmanMeasure : ℝ) : ℂ)) =
      pauliConst P.e P.m q2 * ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
        (P.δ₃ ^ 2 / 4 * (vpK P.m q2 z ^ 2 * photonD a b (vpK P.m q2 z) ^ 3)))
          ∂feynmanMeasure : ℝ) : ℂ) := by
    have hint : ∫ z, 2 * (z.2 ^ 2 * P.m ^ 2 *
        (P.δ₃ ^ 2 / 4 * (vpK P.m q2 z ^ 2 * photonD a b (vpK P.m q2 z) ^ 3))) ∂feynmanMeasure =
        P.δ₃ ^ 2 / 4 * (b ^ 2 - a ^ 2) ^ 2 * ((∫ z, kernVP P.m a b a q2 z ∂feynmanMeasure) -
          ∫ z, kernVP P.m a b b q2 z ∂feynmanMeasure) := by
      have iA : Integrable (kernVP P.m a b a q2) feynmanMeasure := integrable_kern5 hmγ hΛ hm hq.le
      have iB : Integrable (kernVP P.m a b b q2) feynmanMeasure := integrable_kern5 hmγ hΛ hm hq.le
      rw [← integral_sub iA iB, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_feynmanMeasure_ne_one] with z ⟨hz, hy1⟩
      have h := kernVP_sub_eq_photon (a := a) (b := b) hm hq.le hz hy1
      calc 2 * (z.2 ^ 2 * P.m ^ 2 *
            (P.δ₃ ^ 2 / 4 * (vpK P.m q2 z ^ 2 * photonD a b (vpK P.m q2 z) ^ 3)))
          = P.δ₃ ^ 2 / 4 *
              (2 * (z.2 ^ 2 * P.m ^ 2 * (vpK P.m q2 z ^ 2 * photonD a b (vpK P.m q2 z) ^ 3))) := by
            ring
        _ = _ := by rw [← h]; ring
    rw [hint, pauliConst]
    push_cast
    ring
  rw [← hval]
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  have iA := efInt_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain P.e P.m p' p)
    hα hCN hMa hε
  have iB := efInt_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain P.e P.m p' p)
    hα hCN hMb hε
  have e : (fun k => pauliNum P.m p' p (fun μ => ddIntegrand P p' p μ ε k)) = fun k =>
      ((P.δ₃ ^ 2 / 4 * (b ^ 2 - a ^ 2) ^ 2 : ℝ) : ℂ) *
        (s2Prod5Integrand (pauliChain P.e P.m p' p) P.m ![a, b, a, b, a] (fun _ => ε) ε p' p k +
          (-1) * s2Prod5Integrand (pauliChain P.e P.m p' p) P.m ![a, b, a, b, b]
            (fun _ => ε) ε p' p k) := by
    funext k
    rw [pauliNum_ddIntegrand P hm.ne' hε hp' hp hq k]
    ring
  simp only [id]
  rw [e, efi_const_mul, efi_add iA (iB.const_mul _), efi_const_mul]
  ring

/-! ### The nested value of the class limit -/

theorem classV_repDD_eq (P : Params) (s₀ s₁ : Fin 2) (ε : ℝ) (p' p : Fin 4 → ℝ) (μ α β : Fin 4) :
    classV (repDD s₀ s₁) { P with ε := ε } p' p μ α β =
      (1 / I) * QED.OneLoop.energyFirstIntegral fun k => ddIntegrand P p' p μ ε k α β := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hΦ : chainFlavors P =
      (⟨({ P with ε := ε } : Params).mass, ({ P with ε := ε } : Params).loopCoeff, 0⟩ :
        QED.Lepton.Flavors (Fin 3)) := rfl
  simp only [classV, Matrix.of_apply]
  rw [hΦ, QED.ChainProof.Enum.contractionValue₂_params',
    contractionValue₂_repDD { P with ε := ε } s₀ s₁ hmom (fun _ => α) (fun _ => β) (fun _ => μ)]
  rfl

/-- The one-loop Pauli functional `e² outerAt` in terms of `pauliConst`. -/
theorem formFactorProj₂_of_pauliNum {e m s : ℝ} (he : e ≠ 0) (hm : 0 < m) (hs : 0 < s)
    {p' p : Fin 4 → ℝ} (hq : Minkowski.dot (p' - p) (p' - p) = s)
    {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {R : ℝ → ℝ}
    (h : pauliNum m p' p Y = (1 / I) * (pauliConst e m s *
      ((e ^ 2 / (8 * π ^ 2) * ∫ z, 2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z)) ∂feynmanMeasure : ℝ) :
        ℂ))) :
    QED.OneLoop.formFactorProj₂ e m p' p Y = ((e ^ 2 * outerAt m s R : ℝ) : ℂ) := by
  rw [formFactorProj₂_eq_pauliNum, h, hq, pauliConst, outerAt]
  generalize (∫ z, 2 * (z.2 ^ 2 * m ^ 2 * R (vpK m s z)) ∂feynmanMeasure) = J
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h4 : (4 * (m : ℂ) ^ 2 + (s : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 4 * m ^ 2 + s := by positivity
    exact_mod_cast this.ne'
  have h4' : (m : ℂ) ^ 2 * 4 + (s : ℂ) ≠ 0 := by rw [mul_comm]; exact h4
  push_cast
  field_simp

/-- **The nested value of a `δ₃`–`δ₃` class limit at fixed `q`**: every `ε → 0⁺` limit `Y` of
`classV (repDD s₀ s₁)` at an admissible pair has Pauli projection
`e² outerAt m q² ((δ₃²/4) s² D(s)³)`. -/
theorem formFactorProj₂_repDD (s₀ s₁ : Fin 2) {P : Params} (hA : ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repDD s₀ s₁) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j))) :
    QED.OneLoop.formFactorProj₂ P.e P.m p' p Y =
      ((P.e ^ 2 * outerAt P.m (Minkowski.dot (p' - p) (p' - p))
        (fun s => P.δ₃ ^ 2 / 4 * (s ^ 2 * photonD P.mγ P.Λ s ^ 3)) : ℝ) : ℂ) := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  refine formFactorProj₂_of_pauliNum hA.he hA.hm hq rfl ?_
  have hT := (tendsto_efi_pauliNum_ddIntegrand P hA.hm hA.hmγ hA.hΛ hA.hmγΛ.ne hp' hp hp0' hp0
    hq).const_mul (1 / I)
  refine tendsto_nhds_unique ?_ hT
  -- the Pauli numerator of the limit is the limit of the Pauli numerators
  have hsum : Tendsto (fun ε => ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 *
      classV (repDD s₀ s₁) { P with ε := ε } p' p j.1 j.2.1 j.2.2) (𝓝[>] 0)
      (𝓝 (pauliNum P.m p' p Y)) := by
    rw [pauliNum_eq_sum_idx]
    exact tendsto_finsetSum _ fun j _ => (hY j.1 j.2.1 j.2.2).const_mul _
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  have hI : ∀ j : Idx, EFInt fun k => pauliWt P.m p' p j.1 j.2.1 j.2.2 *
      ddIntegrand P p' p j.1 ε k j.2.1 j.2.2 := fun j =>
    (efInt_ddIntegrand P hA.hm hA.hmγ hA.hΛ hp hp' hq.le j.1 j.2.1 j.2.2 hε).const_mul _
  simp only [classV_repDD_eq]
  have e : (fun k => pauliNum P.m p' p (fun μ => ddIntegrand P p' p μ ε k)) =
      fun k => ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 *
        ddIntegrand P p' p j.1 ε k j.2.1 j.2.2 :=
    funext fun k => pauliNum_eq_sum_idx _ _ _ _
  rw [e, efi_sum _ fun j _ => hI j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [efi_const_mul]
  ring

end QED.ChainProof.HCSide

end
