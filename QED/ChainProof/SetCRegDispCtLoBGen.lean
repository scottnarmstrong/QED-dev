/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBPhoton
public import QED.TwoLoop.VPHalfAtGenSpec
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The doubled vertex: uniform bounds, powers of `k²` and spectral insertions

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c). The analogue, for
the vertex with the electron denominator of the open line `d` doubled
(`QED.ChainProof.CtLoB.dblProdIntegrand`), of `QED/TwoLoop/VPHalfAtAssemblyBound.lean`,
`QED/TwoLoop/VPHalfAtGenPow.lean` and `QED/TwoLoop/VPHalfAtGenSpec.lean`.

* `exists_goodEF_dblProdIntegrand`, `exists_ptBd_dblProdIntegrand`, `efInt_dblProdIntegrand`:
  the doubled photon-product vertex is `QED.TwoLoop.VPHalfAtAssembly.GoodEF` with one constant for
  all photon masses `≥ M₀` and all positive prescriptions, and satisfies a pointwise bound
  uniform in the masses and in photon prescriptions `≥ e₀ > 0`.
* `dblPowInt j Ms es`: `(k²)ʲ` times the doubled vertex; `dblPowInt_succ` (one `k²` absorbed by
  the first photon denominator), `dblPowLimit` (the limit, by the same recursion from
  `dblProdLimit`), **`tendsto_efi_dblPowInt`**, **`exists_good_dblPowInt`**, `efInt_dblPowInt`.
* `dblSpecInt j Ms es Msp xs`: `dblPowInt` times `r` spectral factors
  `1/(M² + x(1-x)k² - iε)` (`QED.TwoLoop.VPHalfAtAssembly.fDen`); `dblSpecInt_succ_lim`,
  `dblSpecInt_succ_fact`, `dblSpecLimit`, **`tendsto_efi_dblSpecInt`** (at fixed Feynman
  parameters in `(0, 1)`), **`exists_good_dblSpecInt`** (uniform in the Feynman parameters and
  in the flavour masses `≥ M_lo ≥ M₀`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAtGen

/-! ### Uniform bounds on the doubled photon-product vertex -/

section Bounds

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

theorem efInt_dblProdIntegrand (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (d : Fin 2) :
    EFInt (dblProdIntegrand N m Ms es ε d p' p) :=
  ⟨(energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε d).1,
    (energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε
      d).2.1⟩

/-- **The doubled photon-product vertex is `GoodEF` uniformly**: one constant for all photon
masses `≥ M₀`, all positive photon prescriptions and all positive electron prescriptions. -/
theorem exists_goodEF_dblProdIntegrand (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (k : ℕ) (d : Fin 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) → (∀ j, 0 < es j) →
      ∀ ε : ℝ, 0 < ε → GoodEF (dblProdIntegrand N m Ms es ε d p' p) K := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 2)
    (by omega)
  set Δ := simplexSet (k + 1)
  set Cw : ℝ := ((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * ((k + 1 : ℕ) + 3)
  have hCw : 0 ≤ Cw := by positivity
  have hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖dblWt d (k + 1) z‖ ≤ Cw :=
    fun z hz => by simpa [Cw] using dblWt_norm_le d (k + 1) hz
  set B : ℝ := Cw * C
  have hB0 : 0 ≤ B := by positivity
  refine ⟨((k + 1).factorial : ℝ) * (B * (volume : Measure (Fin (k + 1) → ℝ)).real Δ),
    by positivity, fun Ms es hMs hes ε hε => ?_⟩
  refine ⟨efInt_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε d, fun v => ?_⟩
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  rw [integral_time_dblProdIntegrand hNc hNb m Ms hes hε d p' p v, norm_mul,
    Complex.norm_natCast]
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  have hbd : ∀ᵐ u ∂(volume.restrict Δ),
      ‖∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p ((v, u), t)‖ ≤
        B * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
    filter_upwards [hΔ] with u hu
    have hs : ∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p ((v, u), t) =
        spatialW (dblWt d (k + 1)) α N m (mixMass Ms u) (k + 2) ε (mixEps es u) p' p v :=
      integral_time_dblIntegrand hNc hNq hNb m (mixMass Ms u) (k + 1) (η := mixEps es u) hε
        (he₀.trans_le (mixEps_ge hes₀ hu)) d p' p v
    rw [hs]
    exact norm_spatialW_le hwb
      (fun z hz w => hC (mixMass Ms u) (mixMass_ge hM₀.le hMs hu) _ z hz w) v
  have h := norm_integral_le_of_norm_le_const hbd
  rw [Measure.real, Measure.restrict_apply_univ] at h
  calc ((k + 1).factorial : ℝ) *
        ‖∫ u in Δ, ∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p ((v, u), t)‖
      ≤ ((k + 1).factorial : ℝ) * (B * (1 + ‖v‖) ^ (-(5 : ℝ)) * (volume Δ).toReal) := by
        gcongr
    _ = ((k + 1).factorial : ℝ) * (B * (volume : Measure (Fin (k + 1) → ℝ)).real Δ) *
        (1 + ‖v‖) ^ (-(5 : ℝ)) := by
        rw [Measure.real]; ring

/-- **The pointwise bound on the doubled photon-product vertex**, uniform in the photon masses
and in photon prescriptions `≥ e₀ > 0`, at a fixed electron prescription. -/
theorem exists_ptBd_dblProdIntegrand (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) (k : ℕ)
    {ε e₀ : ℝ} (hε : 0 < ε) (he₀ : 0 < e₀) (d : Fin 2) (p' p : Fin 4 → ℝ) :
    ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, e₀ ≤ es j) →
      PtBd (dblProdIntegrand N m Ms es ε d p' p) G := by
  choose G hG using fun v => exists_norm_dblIntegrand_cons_le hNb m (k + 1) hε he₀ d p' p v
  set V : ℝ := (volume : Measure (Fin (k + 1) → ℝ)).real (simplexSet (k + 1))
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨fun v => ((k + 1).factorial : ℝ) * (max (G v) 0 * V), fun v => by positivity,
    fun Ms es hes v t => ?_⟩
  have hes' : ∀ j, 0 < es j := fun j => he₀.trans_le (hes j)
  rw [dblProdIntegrand_eq_integral N m Ms hes' ε d p' p, norm_mul, Complex.norm_natCast]
  have hΔ : ∀ᵐ u ∂(volume.restrict (simplexSet (k + 1))), u ∈ simplexSet (k + 1) :=
    ae_restrict_mem (measurableSet_simplexSet _)
  have hbd : ∀ᵐ u ∂(volume.restrict (simplexSet (k + 1))),
      ‖dblIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) d p' p
          (Fin.cons t v : Fin 4 → ℝ)‖ ≤ max (G v) 0 * (1 + t ^ 2)⁻¹ := by
    filter_upwards [hΔ] with u hu
    refine (hG v _ _ (mixEps_ge hes hu) t).trans ?_
    gcongr
    exact le_max_left _ _
  have h := norm_integral_le_of_norm_le_const hbd
  rw [Measure.real, Measure.restrict_apply_univ] at h
  calc ((k + 1).factorial : ℝ) * ‖∫ u in simplexSet (k + 1),
        dblIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) d p' p
          (Fin.cons t v : Fin 4 → ℝ)‖
      ≤ ((k + 1).factorial : ℝ) * (max (G v) 0 * (1 + t ^ 2)⁻¹ *
          (volume (simplexSet (k + 1))).toReal) := by gcongr
    _ = ((k + 1).factorial : ℝ) * (max (G v) 0 * V) * (1 + t ^ 2)⁻¹ := by
        simp only [V, Measure.real]; ring

end Bounds

/-! ### Powers of `k²` -/

/-- `k² · ∏_{j ≤ k+2} D_j⁻¹ = ∏_{j ≥ 1} D_j⁻¹ - t₀ ∏_j D_j⁻¹` for the doubled vertex,
`t₀ = M₀² - i ε₀`. -/
theorem dblProdIntegrand_mul_s (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 3) → ℝ)
    (hes0 : 0 < es 0) (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * dblProdIntegrand N m Ms es ε d p' p ℓ =
      dblProdIntegrand N m (Fin.tail Ms) (Fin.tail es) ε d p' p ℓ -
        massShift (Ms 0) (es 0) * dblProdIntegrand N m Ms es ε d p' p ℓ := by
  have h0 := denom_ne_zero_of_pos (M := Ms 0) hes0 ℓ
  have e0 := denom_eq_add_massShift (Ms 0) (es 0) ℓ
  simp only [dblProdIntegrand]
  rw [Fin.prod_univ_succ]
  simp only [Fin.tail]
  have hs : ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) = denom (Ms 0) (es 0) ℓ - massShift (Ms 0) (es 0) := by
    rw [e0]; ring
  rw [hs]
  linear_combination (N ℓ * ((denom m ε (p' + ℓ) * denom m ε (p + ℓ) *
    denom m ε (dblMom d p' p ℓ))⁻¹ * ∏ i : Fin (k + 2), (denom (Ms i.succ) (es i.succ) ℓ)⁻¹)) *
    mul_inv_cancel₀ h0

/-- `(k²)ʲ N(ℓ) / (D_m(p'+ℓ; ε) D_m(p+ℓ; ε) D_m(ℓ_d; ε) ∏_i D_{M_i}(ℓ; ε_i))`. -/
noncomputable def dblPowInt (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * dblProdIntegrand N m Ms es ε d p' p ℓ

/-- The limit of the energy-first integral of `dblPowInt j Ms`, by the absorption recursion. -/
noncomputable def dblPowLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (d : Fin 2)
    (p' p : Fin 4 → ℝ) : (j : ℕ) → {k : ℕ} → (Fin (k + 2) → ℝ) → ℂ
  | 0, _, Ms => dblProdLimit α N m Ms d p' p
  | _ + 1, 0, _ => 0
  | j + 1, _ + 1, Ms =>
      dblPowLimit α N m d p' p j (Fin.tail Ms) -
        ((Ms 0 ^ 2 : ℝ) : ℂ) * dblPowLimit α N m d p' p j Ms

theorem dblPowLimit_zero (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ)
    {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    dblPowLimit α N m d p' p 0 Ms = dblProdLimit α N m Ms d p' p := by
  simp [dblPowLimit]

theorem dblPowLimit_succ (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (j : ℕ) {k : ℕ} (Ms : Fin (k + 3) → ℝ) :
    dblPowLimit α N m d p' p (j + 1) Ms =
      dblPowLimit α N m d p' p j (Fin.tail Ms) -
        ((Ms 0 ^ 2 : ℝ) : ℂ) * dblPowLimit α N m d p' p j Ms := by
  simp [dblPowLimit]

theorem dblPowInt_zero (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblPowInt N m 0 Ms es ε d p' p ℓ = dblProdIntegrand N m Ms es ε d p' p ℓ := by
  simp [dblPowInt]

/-- **One `k²` absorbed by the first photon denominator.** -/
theorem dblPowInt_succ (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 3) → ℝ) (hes0 : 0 < es 0) (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblPowInt N m (j + 1) Ms es ε d p' p ℓ =
      dblPowInt N m j (Fin.tail Ms) (Fin.tail es) ε d p' p ℓ -
        massShift (Ms 0) (es 0) * dblPowInt N m j Ms es ε d p' p ℓ := by
  have h := dblProdIntegrand_mul_s N m Ms es hes0 ε d p' p ℓ
  simp only [dblPowInt, pow_succ]
  linear_combination ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * h

section Pow

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- **The `GoodEF` bound for `(k²)ʲ` over `k + 2` photon denominators**, `j ≤ k`, for the
doubled vertex: the constant is `(1 + T)ʲ K` whenever the first `j` shifts are bounded by `T`. -/
theorem exists_goodEF_dblPowInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (d : Fin 2) :
    ∀ (j k : ℕ), j ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ Ms es : Fin (k + 2) → ℝ,
      (∀ i, M₀ ≤ Ms i) → (∀ i, 0 < es i) →
      (∀ i : Fin (k + 2), i.val < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      ∀ ε : ℝ, 0 < ε → GoodEF (dblPowInt N m j Ms es ε d p' p) ((1 + T) ^ j * K) := by
  intro j
  induction j with
  | zero =>
    intro k _
    obtain ⟨K, hK, h⟩ := exists_goodEF_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb k d
    refine ⟨K, hK, fun T _ Ms es hMs hes _ ε hε => ?_⟩
    exact ((h Ms es hMs hes ε hε).congr fun ℓ =>
      (dblPowInt_zero N m Ms es ε d p' p ℓ).symm).mono' (by simp)
  | succ j ih =>
    intro k hjk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨K1, hK1, h1⟩ := ih k (by omega)
    obtain ⟨K2, hK2, h2⟩ := ih (k + 1) (by omega)
    refine ⟨K1 + K2, by positivity, fun T hT Ms es hMs hes hTs ε hε => ?_⟩
    have g1 := h1 T hT (Fin.tail Ms) (Fin.tail es) (fun i => hMs _) (fun i => hes _)
      (fun i hi => hTs i.succ (by simp; omega)) ε hε
    have g2 := h2 T hT Ms es hMs hes (fun i hi => hTs i (by omega)) ε hε
    have t0 : ‖massShift (Ms 0) (es 0)‖ ≤ T := hTs 0 (by simp)
    have h := g1.sub (g2.const_mul (massShift (Ms 0) (es 0)))
    refine (h.congr fun ℓ => (dblPowInt_succ N m j Ms es (hes 0) ε d p' p ℓ).symm).mono' ?_
    have hTj : 0 ≤ (1 + T) ^ j := by positivity
    have a : ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2) ≤ T * ((1 + T) ^ j * K2) :=
      mul_le_mul_of_nonneg_right t0 (by positivity)
    have b : (1 + T) ^ j * K1 ≤ (1 + T) ^ j * ((1 + T) * K1) := by
      gcongr; nlinarith
    have c : T * ((1 + T) ^ j * K2) ≤ (1 + T) ^ j * ((1 + T) * K2) := by
      have : T * K2 ≤ (1 + T) * K2 := by nlinarith
      nlinarith
    calc (1 + T) ^ j * K1 + ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2)
        ≤ (1 + T) ^ j * ((1 + T) * K1) + (1 + T) ^ j * ((1 + T) * K2) := by linarith
      _ = (1 + T) ^ (j + 1) * (K1 + K2) := by ring

/-- **The pointwise bound for `(k²)ʲ` over `k + 2` photon denominators**, `j ≤ k`, for the
doubled vertex, uniform in the masses and in photon prescriptions `≥ e₀`. -/
theorem exists_ptBd_dblPowInt (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {ε e₀ : ℝ}
    (hε : 0 < ε) (he₀ : 0 < e₀) (d : Fin 2) (p' p : Fin 4 → ℝ) :
    ∀ (j k : ℕ), j ≤ k → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), i.val < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      PtBd (dblPowInt N m j Ms es ε d p' p) (fun v => (1 + T) ^ j * G v) := by
  intro j
  induction j with
  | zero =>
    intro k _
    obtain ⟨G, hG, h⟩ := exists_ptBd_dblProdIntegrand hNb m k hε he₀ d p' p
    refine ⟨G, hG, fun T _ Ms es hes _ v t => ?_⟩
    rw [dblPowInt_zero]
    simpa using h Ms es hes v t
  | succ j ih =>
    intro k hjk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨G1, hG1, h1⟩ := ih k (by omega)
    obtain ⟨G2, hG2, h2⟩ := ih (k + 1) (by omega)
    refine ⟨fun v => G1 v + G2 v, fun v => by have := hG1 v; have := hG2 v; positivity,
      fun T hT Ms es hes hTs => ?_⟩
    have hes0 : 0 < es 0 := he₀.trans_le (hes 0)
    have g1 := h1 T hT (Fin.tail Ms) (Fin.tail es) (fun i => hes _)
      (fun i hi => hTs i.succ (by simp; omega))
    have g2 := h2 T hT Ms es hes (fun i hi => hTs i (by omega))
    have t0 : ‖massShift (Ms 0) (es 0)‖ ≤ T := hTs 0 (by simp)
    intro v t
    rw [dblPowInt_succ N m j Ms es hes0 ε d p' p]
    have a1 := g1 v t
    have a2 := g2 v t
    have hT1 : 0 ≤ (1 + T) ^ j := by positivity
    have ht : 0 < (1 + t ^ 2)⁻¹ := by positivity
    have hG1v := hG1 v
    have hG2v := hG2 v
    calc ‖dblPowInt N m j (Fin.tail Ms) (Fin.tail es) ε d p' p (Fin.cons t v) -
          massShift (Ms 0) (es 0) * dblPowInt N m j Ms es ε d p' p (Fin.cons t v)‖
        ≤ ‖dblPowInt N m j (Fin.tail Ms) (Fin.tail es) ε d p' p (Fin.cons t v)‖ +
          ‖massShift (Ms 0) (es 0)‖ * ‖dblPowInt N m j Ms es ε d p' p (Fin.cons t v)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ (1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹ + T * ((1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹) := by
          gcongr
      _ ≤ (1 + T) ^ (j + 1) * (G1 v + G2 v) * (1 + t ^ 2)⁻¹ := by
          have e1 : 0 ≤ (1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹ := by positivity
          have e2 : 0 ≤ (1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹ := by positivity
          have key : (1 + T) ^ (j + 1) * (G1 v + G2 v) * (1 + t ^ 2)⁻¹ =
              (1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹ + T * ((1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹) +
              (1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹ +
              T * ((1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹) := by ring
          rw [key]
          nlinarith [mul_nonneg hT e1, mul_nonneg hT e2]

/-- The two bounds together: `Good`. -/
theorem exists_good_dblPowInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (d : Fin 2) (j k : ℕ) (hjk : j ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε e₀ : ℝ, 0 < ε → 0 < e₀ → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧
      ∀ T : ℝ, 0 ≤ T → ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, M₀ ≤ Ms i) → (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), i.val < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      Good (dblPowInt N m j Ms es ε d p' p) ((1 + T) ^ j * K)
        (fun v => (1 + T) ^ j * G v) := by
  obtain ⟨K, hK, hEF⟩ := exists_goodEF_dblPowInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb d j k hjk
  refine ⟨K, hK, fun ε e₀ hε he₀ => ?_⟩
  obtain ⟨G, hG, hPt⟩ := exists_ptBd_dblPowInt (N := N) hNb m hε he₀ d p' p j k hjk
  exact ⟨G, hG, fun T hT Ms es hMs hes hTs =>
    ⟨hEF T hT Ms es hMs (fun i => he₀.trans_le (hes i)) hTs ε hε, hPt T hT Ms es hes hTs⟩⟩

/-- Integrability in both stages, for `j ≤ k` and positive prescriptions. -/
theorem efInt_dblPowInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (d : Fin 2) {j k : ℕ} (hjk : j ≤ k)
    {Ms es : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (hes : ∀ i, 0 < es i) {ε : ℝ}
    (hε : 0 < ε) : EFInt (dblPowInt N m j Ms es ε d p' p) := by
  obtain ⟨K, -, h⟩ := exists_goodEF_dblPowInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb d j k hjk
  have hT : 0 ≤ ∑ i, ‖massShift (Ms i) (es i)‖ := by positivity
  exact (h _ hT Ms es hMs hes (fun i _ => Finset.single_le_sum
    (f := fun i => ‖massShift (Ms i) (es i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    ε hε).1

/-- **The `ε → 0⁺` limit of `(k²)ʲ` over `k + 2` photon denominators for the doubled vertex**,
`j ≤ k`: along any countably generated filter on which the electron prescription and every photon
prescription tend to `0⁺`, the energy-first integral tends to `dblPowLimit j Ms`. -/
theorem tendsto_efi_dblPowInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (d : Fin 2) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) :
    ∀ (j k : ℕ), j ≤ k → ∀ (Ms : Fin (k + 2) → ℝ) (es : ι → Fin (k + 2) → ℝ),
      (∀ i, M₀ ≤ Ms i) → (∀ i, Tendsto (fun t => es t i) l (𝓝[>] 0)) →
      Tendsto (fun t => energyFirstIntegral (dblPowInt N m j Ms (es t) (ε t) d p' p)) l
        (𝓝 (dblPowLimit α N m d p' p j Ms)) := by
  have hεpos : ∀ᶠ t in l, 0 < ε t := hε self_mem_nhdsWithin
  intro j
  induction j with
  | zero =>
    intro k _ Ms es hMs hes
    rw [dblPowLimit_zero]
    have e : ∀ t, dblPowInt N m 0 Ms (es t) (ε t) d p' p =
        dblProdIntegrand N m Ms (es t) (ε t) d p' p :=
      fun t => funext fun ℓ => dblPowInt_zero N m Ms (es t) (ε t) d p' p ℓ
    simp only [e]
    exact tendsto_energyFirstIntegral_dblProdIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs d
      hε hes
  | succ j ih =>
    intro k hjk Ms es hMs hes
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hespos : ∀ᶠ t in l, ∀ i, 0 < es t i :=
      eventually_all.2 fun i => (hes i) self_mem_nhdsWithin
    have l1 := ih k (by omega) (Fin.tail Ms) (fun t => Fin.tail (es t)) (fun i => hMs _)
      (fun i => hes _)
    have l2 := ih (k + 1) (by omega) Ms es hMs hes
    have l0 := QED.TwoLoop.VPHalfAtGen.tendsto_massShift (Ms 0)
      ((hes 0).mono_right nhdsWithin_le_nhds)
    rw [dblPowLimit_succ]
    refine (l1.sub (l0.mul l2)).congr' ?_
    filter_upwards [hεpos, hespos] with t ht hest
    have i1 := efInt_dblPowInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb d (j := j) (k := k)
      (by omega) (Ms := Fin.tail Ms) (es := Fin.tail (es t)) (fun i => hMs _)
      (fun i => hest _) ht
    have i2 := efInt_dblPowInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb d (j := j) (k := k + 1)
      (by omega) (Ms := Ms) (es := es t) hMs hest ht
    have e : dblPowInt N m (j + 1) Ms (es t) (ε t) d p' p = fun ℓ =>
        dblPowInt N m j (Fin.tail Ms) (Fin.tail (es t)) (ε t) d p' p ℓ +
          (-massShift (Ms 0) (es t 0)) * dblPowInt N m j Ms (es t) (ε t) d p' p ℓ := by
      funext ℓ
      rw [dblPowInt_succ N m j Ms (es t) (hest 0)]
      ring
    rw [e, efi_add i1 (i2.const_mul _), efi_const_mul]
    ring

end Pow

/-! ### Spectral insertions -/

/-- `(k²)ʲ N / (D D D_d ∏ D_{M_i}(ε_i)) · ∏_{i<r} 1/(M_i² + x_i(1-x_i)k² - iε)`. -/
noncomputable def dblSpecInt (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) {r : ℕ} (Msp xs : Fin r → ℝ) (ε : ℝ) (d : Fin 2)
    (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  dblPowInt N m j Ms es ε d p' p ℓ * ∏ i, (fDen (Msp i) ε (xs i) ℓ)⁻¹

/-- The limit of `dblSpecInt` at fixed Feynman parameters. -/
noncomputable def dblSpecLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (d : Fin 2)
    (p' p : Fin 4 → ℝ) (j : ℕ) :
    (r : ℕ) → {k : ℕ} → (Fin (k + 2) → ℝ) → (Fin r → ℝ) → (Fin r → ℝ) → ℂ
  | 0, _, Ms, _, _ => dblPowLimit α N m d p' p j Ms
  | r + 1, k, Ms, Msp, xs => ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
      dblSpecLimit α N m d p' p j r (k := k + 1)
        (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp)
        (Fin.tail xs)

theorem dblSpecLimit_zero (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin 0 → ℝ) :
    dblSpecLimit α N m d p' p j 0 Ms Msp xs = dblPowLimit α N m d p' p j Ms := rfl

theorem dblSpecLimit_succ (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (j r : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin (r + 1) → ℝ) :
    dblSpecLimit α N m d p' p j (r + 1) Ms Msp xs = ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
      dblSpecLimit α N m d p' p j r (k := k + 1)
        (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp)
        (Fin.tail xs) := rfl

theorem dblProdIntegrand_snoc (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (μ η ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblProdIntegrand N m (Fin.snoc Ms μ : Fin (k + 1 + 2) → ℝ)
        (Fin.snoc es η : Fin (k + 1 + 2) → ℝ) ε d p' p ℓ =
      dblProdIntegrand N m Ms es ε d p' p ℓ * (denom μ η ℓ)⁻¹ := by
  unfold dblProdIntegrand
  rw [Fin.prod_univ_castSucc (n := k + 2)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem dblPowInt_snoc (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (μ η ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblPowInt N m j (Fin.snoc Ms μ : Fin (k + 1 + 2) → ℝ) (Fin.snoc es η : Fin (k + 1 + 2) → ℝ)
        ε d p' p ℓ = dblPowInt N m j Ms es ε d p' p ℓ * (denom μ η ℓ)⁻¹ := by
  rw [dblPowInt, dblPowInt, dblProdIntegrand_snoc]
  ring

/-- **The limit form of one insertion** for the doubled vertex. -/
theorem dblSpecInt_succ_lim (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) {r : ℕ} (Msp xs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hx : xs 0 ∈ Ioo (0 : ℝ) 1) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblSpecInt N m j Ms es Msp xs ε d p' p ℓ = ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
      dblSpecInt N m j (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ)
        (Fin.snoc es (specEta ε (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp) (Fin.tail xs)
        ε d p' p ℓ := by
  have h0 : ((xs 0 * (1 - xs 0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero (Msp 0) hε (xs 0) ℓ
  unfold dblSpecInt
  rw [dblPowInt_snoc, denom_specMu hx, Fin.prod_univ_succ]
  simp only [Fin.tail]
  field_simp

/-- **The factored form of one insertion** for the doubled vertex:
`1/(M² + x(1-x)k² - iε) = t⁻¹ (1 - k² D_{μ_x}⁻¹)`, `t = M² - iε`. -/
theorem dblSpecInt_succ_fact (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) {r : ℕ} (Msp xs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hx : xs 0 ∈ Ioo (0 : ℝ) 1) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) :
    dblSpecInt N m j Ms es Msp xs ε d p' p ℓ = (massShift (Msp 0) ε)⁻¹ *
      (dblSpecInt N m j Ms es (Fin.tail Msp) (Fin.tail xs) ε d p' p ℓ -
        dblSpecInt N m (j + 1) (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ)
          (Fin.snoc es (specEta ε (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp) (Fin.tail xs)
          ε d p' p ℓ) := by
  have h0 : ((xs 0 * (1 - xs 0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero (Msp 0) hε (xs 0) ℓ
  have hS := massShift_ne_zero (Msp 0) hε
  have e : fDen (Msp 0) ε (xs 0) ℓ = massShift (Msp 0) ε +
      ((xs 0 * (1 - xs 0) : ℝ) : ℂ) * ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) := by
    simp only [fDen, massShift, QED.WickModel.vacuumPolarizationFeynmanMass]
    push_cast
    ring
  unfold dblSpecInt
  rw [dblPowInt_snoc, denom_specMu hx, Fin.prod_univ_succ]
  simp only [Fin.tail, dblPowInt, pow_succ]
  field_simp
  rw [e]
  ring

section Spec

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- **The `ε → 0⁺` limit with `r` spectral insertions at fixed Feynman parameters** for the
doubled vertex, `j ≤ k`. -/
theorem tendsto_efi_dblSpecInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (d : Fin 2) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (j : ℕ) :
    ∀ (r k : ℕ), j ≤ k → ∀ (Ms : Fin (k + 2) → ℝ) (es : ι → Fin (k + 2) → ℝ)
      (Msp xs : Fin r → ℝ), (∀ i, M₀ ≤ Ms i) → (∀ i, M₀ ≤ Msp i) →
      (∀ i, xs i ∈ Ioo (0 : ℝ) 1) → (∀ i, Tendsto (fun t => es t i) l (𝓝[>] 0)) →
      Tendsto (fun t => energyFirstIntegral (dblSpecInt N m j Ms (es t) Msp xs (ε t) d p' p)) l
        (𝓝 (dblSpecLimit α N m d p' p j r Ms Msp xs)) := by
  have hεpos : ∀ᶠ t in l, 0 < ε t := hε self_mem_nhdsWithin
  intro r
  induction r with
  | zero =>
    intro k hjk Ms es Msp xs hMs _ _ hes
    have e : ∀ t, dblSpecInt N m j Ms (es t) Msp xs (ε t) d p' p =
        dblPowInt N m j Ms (es t) (ε t) d p' p :=
      fun t => funext fun ℓ => by simp [dblSpecInt]
    simp only [e, dblSpecLimit_zero]
    exact tendsto_efi_dblPowInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb d hε j k hjk Ms es hMs hes
  | succ r ih =>
    intro k hjk Ms es Msp xs hMs hMsp hxs hes
    have hx0 := hxs 0
    have hμ : M₀ ≤ specMu (Msp 0) (xs 0) :=
      (hMsp 0).trans (specMu_ge (hM₀.trans_le (hMsp 0)) hx0)
    have hlim := ih (k + 1) (by omega) (Fin.snoc Ms (specMu (Msp 0) (xs 0)))
      (fun t => Fin.snoc (es t) (specEta (ε t) (xs 0))) (Fin.tail Msp) (Fin.tail xs)
      (fun i => Fin.lastCases (by simpa using hμ) (fun i => by simpa using hMs i) i)
      (fun i => hMsp _) (fun i => hxs _)
      (fun i => Fin.lastCases (by simpa using tendsto_specEta' hx0 hε)
        (fun i => by simpa using hes i) i)
    rw [dblSpecLimit_succ]
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [hεpos] with t ht
    have e : dblSpecInt N m j Ms (es t) Msp xs (ε t) d p' p = fun ℓ =>
        ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
          dblSpecInt N m j (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ)
            (Fin.snoc (es t) (specEta (ε t) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp)
            (Fin.tail xs) (ε t) d p' p ℓ :=
      funext fun ℓ => dblSpecInt_succ_lim N m j Ms (es t) Msp xs ht hx0 d p' p ℓ
    rw [e, efi_const_mul]

/-- **`dblSpecInt` is `Good` uniformly in the Feynman parameters and the flavour masses**, for
`j ≤ k` and `j + r ≤ k + 2`, when the first `j + r` shifts are bounded by `T`. -/
theorem exists_good_dblSpecInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (d : Fin 2) {Mlo : ℝ} (hMlo : M₀ ≤ Mlo) :
    ∀ (r j k : ℕ), j ≤ k → j + r ≤ k + 2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ ε e₀ : ℝ, 0 < ε → 0 < e₀ → e₀ ≤ ε →
      ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, M₀ ≤ Ms i) → (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), i.val < j + r → ‖massShift (Ms i) (es i)‖ ≤ T) →
      ∀ Msp xs : Fin r → ℝ, (∀ i, Mlo ≤ Msp i) → (∀ i, xs i ∈ Ioo (0 : ℝ) 1) →
      Good (dblSpecInt N m j Ms es Msp xs ε d p' p) ((1 + T) ^ (j + r) * K)
        (fun v => (1 + T) ^ (j + r) * G v) := by
  intro r
  induction r with
  | zero =>
    intro j k hjk _
    obtain ⟨K, hK, h⟩ := exists_good_dblPowInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb d j k hjk
    refine ⟨K, hK, fun ε e₀ hε he₀ _ => ?_⟩
    obtain ⟨G, hG, hg⟩ := h ε e₀ hε he₀
    refine ⟨G, hG, fun T hT Ms es hMs hes hTs Msp xs _ _ => ?_⟩
    exact (hg T hT Ms es hMs hes (fun i hi => hTs i (by simpa using hi))).congr
      fun ℓ => by simp [dblSpecInt]
  | succ r ih =>
    intro j k hjk hjr
    have hMlo0 : 0 < Mlo := hM₀.trans_le hMlo
    obtain ⟨K1, hK1, h1⟩ := ih j k hjk (by omega)
    obtain ⟨K2, hK2, h2⟩ := ih (j + 1) (k + 1) (by omega) (by omega)
    set L : ℝ := (Mlo ^ 2)⁻¹
    have hL : 0 ≤ L := by positivity
    refine ⟨L * (K1 + K2), by positivity, fun ε e₀ hε he₀ he₀ε => ?_⟩
    obtain ⟨G1, hG1, g1⟩ := h1 ε e₀ hε he₀ he₀ε
    obtain ⟨G2, hG2, g2⟩ := h2 ε e₀ hε he₀ he₀ε
    refine ⟨fun v => L * (G1 v + G2 v), fun v => by have := hG1 v; have := hG2 v; positivity,
      fun T hT Ms es hMs hes hTs Msp xs hMsp hxs => ?_⟩
    have hx0 := hxs 0
    have hμ : M₀ ≤ specMu (Msp 0) (xs 0) :=
      hMlo.trans ((hMsp 0).trans (specMu_ge (hMlo0.trans_le (hMsp 0)) hx0))
    have hη : e₀ ≤ specEta ε (xs 0) := he₀ε.trans (specEta_ge hε hx0)
    have a1 := g1 T hT Ms es hMs hes (fun i hi => hTs i (by omega)) (Fin.tail Msp) (Fin.tail xs)
      (fun i => hMsp _) (fun i => hxs _)
    have a2 := g2 T hT (Fin.snoc Ms (specMu (Msp 0) (xs 0)))
      (Fin.snoc es (specEta ε (xs 0)))
      (fun i => Fin.lastCases (by simpa using hμ) (fun i => by simpa using hMs i) i)
      (fun i => Fin.lastCases (by simpa using hη) (fun i => by simpa using hes i) i)
      (fun i hi => by
        rw [snoc_castSucc_of_lt Ms _ i (by omega), snoc_castSucc_of_lt es _ i (by omega)]
        exact hTs _ (by simp only; omega))
      (Fin.tail Msp) (Fin.tail xs) (fun i => hMsp _) (fun i => hxs _)
    have hinv : ‖(massShift (Msp 0) ε)⁻¹‖ ≤ L :=
      (norm_inv_massShift_le ε (hMlo0.trans_le (hMsp 0))).trans
        (inv_anti₀ (by positivity) (pow_le_pow_left₀ hMlo0.le (hMsp 0) 2))
    have h := (a1.sub a2).const_mul (massShift (Msp 0) ε)⁻¹
    refine (h.congr fun ℓ =>
      (dblSpecInt_succ_fact N m j Ms es Msp xs hε hx0 d p' p ℓ).symm).mono ?_ ?_
    · have hTj : 0 ≤ (1 + T) ^ (j + r) := by positivity
      have hT1 : (1 + T) ^ (j + r) ≤ (1 + T) ^ (j + (r + 1)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have e2 : (1 + T) ^ (j + 1 + r) = (1 + T) ^ (j + (r + 1)) := by ring_nf
      rw [e2]
      calc ‖(massShift (Msp 0) ε)⁻¹‖ *
            ((1 + T) ^ (j + r) * K1 + (1 + T) ^ (j + (r + 1)) * K2)
          ≤ L * ((1 + T) ^ (j + (r + 1)) * K1 + (1 + T) ^ (j + (r + 1)) * K2) := by
            gcongr
        _ = (1 + T) ^ (j + (r + 1)) * (L * (K1 + K2)) := by ring
    · intro v
      have hTj : 0 ≤ (1 + T) ^ (j + r) := by positivity
      have hT1 : (1 + T) ^ (j + r) ≤ (1 + T) ^ (j + (r + 1)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have e2 : (1 + T) ^ (j + 1 + r) = (1 + T) ^ (j + (r + 1)) := by ring_nf
      have := hG1 v
      have := hG2 v
      simp only
      rw [e2]
      calc ‖(massShift (Msp 0) ε)⁻¹‖ * ((1 + T) ^ (j + r) * G1 v +
            (1 + T) ^ (j + (r + 1)) * G2 v)
          ≤ L * ((1 + T) ^ (j + (r + 1)) * G1 v + (1 + T) ^ (j + (r + 1)) * G2 v) := by
            gcongr
        _ = (1 + T) ^ (j + (r + 1)) * (L * (G1 v + G2 v)) := by ring

end Spec

end QED.ChainProof.CtLoB

end
