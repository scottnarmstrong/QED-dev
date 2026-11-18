/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitD3
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform bounds for the photon-product vertices

Bounds for the assembly of the `ε → 0⁺` limit of the vacuum-polarization class
(`QED.TwoLoop.VPHalf.VPHalfSubAt`, obligation O2-8 at the `ε → 0` level). The engine of
`QED/TwoLoop/VPHalfAtLimit*.lean` gives limits; the assembly also needs bounds that are uniform
in the photon masses (above a fixed `M₀ > 0`) and in **all** positive prescriptions, to exchange
the Feynman-parameter integral of the inner loop with the energy-first integral and to apply
dominated convergence in it.

* `GoodEF F C`: `F` is integrable in both stages of the energy-first integral and its energy
  integral at spatial momentum `v` is bounded by `C (1 + ‖v‖)⁻⁵`. Closed under sums and scalar
  multiples (`GoodEF.add`, `GoodEF.const_mul`); it bounds the energy-first integral by
  `C ∫ (1 + ‖v‖)⁻⁵` (`GoodEF.norm_efi_le`). `Good F C G` adds the pointwise bound
  `‖F(t, v)‖ ≤ G(v) (1 + t²)⁻¹` (`PtBd`), used for Fubini in a parameter at fixed `v`.
* `exists_goodEF_prodIntegrand`, `exists_ptBd_prodIntegrand`: for `k + 2` photon denominators
  with masses `≥ M₀`, the vertex `QED.TwoLoop.VPHalfAtLimit.prodIntegrand` is `GoodEF` with a
  constant independent of the masses and of all prescriptions (from
  `QED.TwoLoop.VPHalfAtLimit.exists_norm_timeP_le`), and satisfies a pointwise bound independent
  of the masses and of photon prescriptions `≥ e₀ > 0`.
* `prodIntegrand_mul_s`, `good_s1`, `good_s2`, `good_s3`: a factor `k²` is absorbed by the
  first photon denominator, `k² / D₀ = 1 - t₀ / D₀`, so `(k²)ʲ` times a product of `j + 2` or more
  photon denominators is `Good` with constants `(1 + T)ʲ K`, `(1 + T)ʲ G`, `T` a bound on the
  shifts `t = M² - i ε` of the absorbing denominators.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtAssembly

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested

/-! ### The predicate -/

/-- `F` is integrable in both stages of the energy-first integral, and its energy integral is
bounded by `C (1 + ‖v‖)⁻⁵`. -/
def GoodEF (F : (Fin 4 → ℝ) → ℂ) (C : ℝ) : Prop :=
  EFInt F ∧ ∀ v : Fin 3 → ℝ, ‖∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ))

/-- The integral `∫ (1 + ‖v‖)⁻⁵` over `ℝ³`. -/
noncomputable def I5 : ℝ := ∫ v : Fin 3 → ℝ, (1 + ‖v‖) ^ (-(5 : ℝ))

theorem integrable_one_add_norm_five :
    Integrable fun v : Fin 3 → ℝ => (1 + ‖v‖) ^ (-(5 : ℝ)) :=
  integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5) (by simp; norm_num)

theorem I5_nonneg : 0 ≤ I5 :=
  integral_nonneg fun v => Real.rpow_nonneg (by positivity) _

namespace GoodEF

variable {F G : (Fin 4 → ℝ) → ℂ} {C D : ℝ}

theorem congr (hF : GoodEF F C) (h : ∀ ℓ, F ℓ = G ℓ) : GoodEF G C := by
  have e : F = G := funext h
  exact e ▸ hF

theorem mono' (hF : GoodEF F C) (h : C ≤ D) : GoodEF F D :=
  ⟨hF.1, fun v => (hF.2 v).trans (by gcongr)⟩

theorem add (hF : GoodEF F C) (hG : GoodEF G D) : GoodEF (fun ℓ => F ℓ + G ℓ) (C + D) := by
  refine ⟨hF.1.add hG.1, fun v => ?_⟩
  rw [integral_add (hF.1.1 v) (hG.1.1 v)]
  refine (norm_add_le _ _).trans ?_
  have := hF.2 v
  have := hG.2 v
  linarith

theorem const_mul (hF : GoodEF F C) (c : ℂ) : GoodEF (fun ℓ => c * F ℓ) (‖c‖ * C) := by
  refine ⟨hF.1.const_mul c, fun v => ?_⟩
  rw [integral_const_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF.2 v) (norm_nonneg _)

theorem sub (hF : GoodEF F C) (hG : GoodEF G D) : GoodEF (fun ℓ => F ℓ - G ℓ) (C + D) := by
  have h := hF.add (hG.const_mul (-1))
  simp only [norm_neg, norm_one, one_mul] at h
  exact h.congr fun ℓ => by ring

theorem norm_efi_le (hF : GoodEF F C) : ‖energyFirstIntegral F‖ ≤ C * I5 := by
  unfold energyFirstIntegral I5
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (integrable_one_add_norm_five.const_mul C)
    (Eventually.of_forall hF.2)

theorem nonneg_const (hF : GoodEF F C) : 0 ≤ C := by
  have h := hF.2 0
  have h1 : (0 : ℝ) < (1 + ‖(0 : Fin 3 → ℝ)‖) ^ (-(5 : ℝ)) := Real.rpow_pos_of_pos (by simp) _
  have h2 := (norm_nonneg _).trans h
  exact nonneg_of_mul_nonneg_left h2 h1

end GoodEF

/-- A pointwise bound `‖F(t, v)‖ ≤ G(v) (1 + t²)⁻¹` on the integrand. -/
def PtBd (F : (Fin 4 → ℝ) → ℂ) (G : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ (v : Fin 3 → ℝ) (t : ℝ), ‖F (Fin.cons t v : Fin 4 → ℝ)‖ ≤ G v * (1 + t ^ 2)⁻¹

/-- `GoodEF` together with a pointwise bound. -/
def Good (F : (Fin 4 → ℝ) → ℂ) (C : ℝ) (G : (Fin 3 → ℝ) → ℝ) : Prop := GoodEF F C ∧ PtBd F G

namespace Good

variable {F F' : (Fin 4 → ℝ) → ℂ} {C D : ℝ} {G G' : (Fin 3 → ℝ) → ℝ}

theorem congr (hF : Good F C G) (h : ∀ ℓ, F ℓ = F' ℓ) : Good F' C G := by
  have e : F = F' := funext h
  exact e ▸ hF

theorem mono (hF : Good F C G) (h : C ≤ D) (hG : ∀ v, G v ≤ G' v) : Good F D G' :=
  ⟨hF.1.mono' h, fun v t => (hF.2 v t).trans (by gcongr; exact hG v)⟩

theorem add (hF : Good F C G) (hF' : Good F' D G') :
    Good (fun ℓ => F ℓ + F' ℓ) (C + D) (fun v => G v + G' v) := by
  refine ⟨hF.1.add hF'.1, fun v t => ?_⟩
  refine (norm_add_le _ _).trans ?_
  have := hF.2 v t
  have := hF'.2 v t
  linarith

theorem const_mul (hF : Good F C G) (c : ℂ) :
    Good (fun ℓ => c * F ℓ) (‖c‖ * C) (fun v => ‖c‖ * G v) := by
  refine ⟨hF.1.const_mul c, fun v t => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF.2 v t) (norm_nonneg _)

theorem sub (hF : Good F C G) (hF' : Good F' D G') :
    Good (fun ℓ => F ℓ - F' ℓ) (C + D) (fun v => G v + G' v) := by
  have h := hF.add (hF'.const_mul (-1))
  simp only [norm_neg, norm_one, one_mul] at h
  exact h.congr fun ℓ => by ring

end Good

/-! ### The photon-product vertex -/

/-- **The photon-product vertex is `GoodEF` uniformly**: one constant for all photon masses
`≥ M₀`, all positive photon prescriptions and all positive electron prescriptions. -/
theorem exists_goodEF_prodIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) → (∀ j, 0 < es j) →
      ∀ ε : ℝ, 0 < ε → GoodEF (prodIntegrand N m Ms es ε p' p) K := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 1)
    (by omega)
  set Δ := simplexSet (k + 1)
  set B : ℝ := (((k + 1 : ℕ) : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) + 2) * C
  have hB0 : 0 ≤ B := by positivity
  refine ⟨((k + 1).factorial : ℝ) * (B * (volume : Measure (Fin (k + 1) → ℝ)).real Δ),
    by positivity, fun Ms es hMs hes ε hε => ?_⟩
  refine ⟨efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε, fun v => ?_⟩
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  rw [integral_time_prodIntegrand hNc hNb m Ms hes hε p' p v, norm_mul, Complex.norm_natCast]
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  have hbd : ∀ᵐ u ∂(volume.restrict Δ),
      ‖∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t)‖ ≤ B * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
    filter_upwards [hΔ] with u hu
    have hs : ∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t) =
        spatialP α N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p v :=
      integral_time_powIntegrand hNc hNq hNb m (mixMass Ms u) (k + 1) (η := mixEps es u) hε
        (he₀.trans_le (mixEps_ge hes₀ hu)) p' p v
    rw [hs]
    exact norm_spatialP_le (fun z hz w => hC (mixMass Ms u) (mixMass_ge hM₀.le hMs hu) _ z hz w) v
  have h := norm_integral_le_of_norm_le_const hbd
  rw [Measure.real, Measure.restrict_apply_univ] at h
  calc ((k + 1).factorial : ℝ) * ‖∫ u in Δ, ∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t)‖
      ≤ ((k + 1).factorial : ℝ) * (B * (1 + ‖v‖) ^ (-(5 : ℝ)) * (volume Δ).toReal) := by
        gcongr
    _ = ((k + 1).factorial : ℝ) * (B * (volume : Measure (Fin (k + 1) → ℝ)).real Δ) *
        (1 + ‖v‖) ^ (-(5 : ℝ)) := by
        rw [Measure.real]; ring

/-- **The pointwise bound on the photon-product vertex**, uniform in the photon masses and in
photon prescriptions `≥ e₀ > 0`, at a fixed electron prescription. -/
theorem exists_ptBd_prodIntegrand {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) (k : ℕ) {ε e₀ : ℝ} (hε : 0 < ε)
    (he₀ : 0 < e₀) (p' p : Fin 4 → ℝ) :
    ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, e₀ ≤ es j) →
      PtBd (prodIntegrand N m Ms es ε p' p) G := by
  choose G hG using fun v => exists_norm_powIntegrand_cons_le hNb m (k + 1) hε he₀ p' p v
  set V : ℝ := (volume : Measure (Fin (k + 1) → ℝ)).real (simplexSet (k + 1))
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨fun v => ((k + 1).factorial : ℝ) * (max (G v) 0 * V), fun v => by positivity,
    fun Ms es hes v t => ?_⟩
  have hes' : ∀ j, 0 < es j := fun j => he₀.trans_le (hes j)
  rw [prodIntegrand_eq_integral N m Ms hes' ε p' p, norm_mul, Complex.norm_natCast]
  have hΔ : ∀ᵐ u ∂(volume.restrict (simplexSet (k + 1))), u ∈ simplexSet (k + 1) :=
    ae_restrict_mem (measurableSet_simplexSet _)
  have hbd : ∀ᵐ u ∂(volume.restrict (simplexSet (k + 1))),
      ‖powIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p (Fin.cons t v : Fin 4 → ℝ)‖
        ≤ max (G v) 0 * (1 + t ^ 2)⁻¹ := by
    filter_upwards [hΔ] with u hu
    refine (hG v _ _ (mixEps_ge hes hu) t).trans ?_
    gcongr
    exact le_max_left _ _
  have h := norm_integral_le_of_norm_le_const hbd
  rw [Measure.real, Measure.restrict_apply_univ] at h
  calc ((k + 1).factorial : ℝ) * ‖∫ u in simplexSet (k + 1),
        powIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p (Fin.cons t v : Fin 4 → ℝ)‖
      ≤ ((k + 1).factorial : ℝ) * (max (G v) 0 * (1 + t ^ 2)⁻¹ *
          (volume (simplexSet (k + 1))).toReal) := by gcongr
    _ = ((k + 1).factorial : ℝ) * (max (G v) 0 * V) * (1 + t ^ 2)⁻¹ := by
        simp only [V, Measure.real]; ring

/-! ### Absorbing `k²` into a photon denominator -/

/-- `k² · ∏_{j ≤ k+2} D_j⁻¹ = ∏_{j ≥ 1} D_j⁻¹ - t₀ ∏_j D_j⁻¹`, with `t₀ = M₀² - i ε₀`. -/
theorem prodIntegrand_mul_s (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 3) → ℝ)
    (hes0 : 0 < es 0) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * prodIntegrand N m Ms es ε p' p ℓ =
      prodIntegrand N m (Fin.tail Ms) (Fin.tail es) ε p' p ℓ -
        massShift (Ms 0) (es 0) * prodIntegrand N m Ms es ε p' p ℓ := by
  have h0 := denom_ne_zero_of_pos (M := Ms 0) hes0 ℓ
  have e0 := denom_eq_add_massShift (Ms 0) (es 0) ℓ
  simp only [prodIntegrand]
  rw [Fin.prod_univ_succ]
  simp only [Fin.tail]
  have hs : ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) = denom (Ms 0) (es 0) ℓ - massShift (Ms 0) (es 0) := by
    rw [e0]; ring
  rw [hs]
  field_simp

theorem norm_massShift_le {M e : ℝ} (he : 0 ≤ e) : ‖massShift M e‖ ≤ M ^ 2 + e := by
  unfold massShift
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg M), abs_of_nonneg he]

section Absorb

variable {N : (Fin 4 → ℝ) → ℂ} {m ε K T : ℝ} {G : (Fin 3 → ℝ) → ℝ} {p' p : Fin 4 → ℝ}

/-- One factor `k²`. -/
theorem good_s1 {k : ℕ} (Ms es : Fin (k + 3) → ℝ) (hes0 : 0 < es 0)
    (hT : ‖massShift (Ms 0) (es 0)‖ ≤ T)
    (h1 : Good (prodIntegrand N m (Fin.tail Ms) (Fin.tail es) ε p' p) K G)
    (h2 : Good (prodIntegrand N m Ms es ε p' p) K G) :
    Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * prodIntegrand N m Ms es ε p' p ℓ)
      ((1 + T) * K) (fun v => (1 + T) * G v) := by
  have hK := h2.1.nonneg_const
  have hG : ∀ v, 0 ≤ G v := fun v => by
    have h := (norm_nonneg _).trans (h2.2 v 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have h := h1.sub (h2.const_mul (massShift (Ms 0) (es 0)))
  refine (h.congr fun ℓ => (prodIntegrand_mul_s N m Ms es hes0 ε p' p ℓ).symm).mono ?_ ?_
  · nlinarith
  · intro v
    have := hG v
    nlinarith

/-- Two factors `k²`. -/
theorem good_s2 {k : ℕ} (Ms es : Fin (k + 4) → ℝ) (hes0 : 0 < es 0) (hes1 : 0 < es 1)
    (hT0 : 0 ≤ T) (hT : ‖massShift (Ms 0) (es 0)‖ ≤ T)
    (hT' : ‖massShift (Ms 1) (es 1)‖ ≤ T)
    (h1 : Good (prodIntegrand N m (Fin.tail (Fin.tail Ms)) (Fin.tail (Fin.tail es)) ε p' p) K G)
    (h2 : Good (prodIntegrand N m (Fin.tail Ms) (Fin.tail es) ε p' p) K G)
    (h3 : Good (prodIntegrand N m Ms es ε p' p) K G) :
    Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 2 * prodIntegrand N m Ms es ε p' p ℓ)
      ((1 + T) ^ 2 * K) (fun v => (1 + T) ^ 2 * G v) := by
  have hK := h3.1.nonneg_const
  have hG : ∀ v, 0 ≤ G v := fun v => by
    have h := (norm_nonneg _).trans (h3.2 v 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have a1 := good_s1 (k := k) (Fin.tail Ms) (Fin.tail es) hes1 hT' h1 h2
  have a2 := good_s1 (k := k + 1) Ms es hes0 hT h2 h3
  have h := a1.sub (a2.const_mul (massShift (Ms 0) (es 0)))
  refine (h.congr fun ℓ => ?_).mono ?_ ?_
  · linear_combination (-((Minkowski.dot ℓ ℓ : ℝ) : ℂ)) *
      prodIntegrand_mul_s N m Ms es hes0 ε p' p ℓ
  · have := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ (1 + T) * K)
    nlinarith
  · intro v
    have := mul_le_mul_of_nonneg_right hT (by have := hG v; positivity : 0 ≤ (1 + T) * G v)
    nlinarith

/-- Three factors `k²`. -/
theorem good_s3 {k : ℕ} (Ms es : Fin (k + 5) → ℝ) (hes0 : 0 < es 0) (hes1 : 0 < es 1)
    (hes2 : 0 < es 2) (hT0 : 0 ≤ T) (hT : ‖massShift (Ms 0) (es 0)‖ ≤ T)
    (hT' : ‖massShift (Ms 1) (es 1)‖ ≤ T) (hT'' : ‖massShift (Ms 2) (es 2)‖ ≤ T)
    (h1 : Good (prodIntegrand N m (Fin.tail (Fin.tail (Fin.tail Ms)))
      (Fin.tail (Fin.tail (Fin.tail es))) ε p' p) K G)
    (h2 : Good (prodIntegrand N m (Fin.tail (Fin.tail Ms)) (Fin.tail (Fin.tail es)) ε p' p) K G)
    (h3 : Good (prodIntegrand N m (Fin.tail Ms) (Fin.tail es) ε p' p) K G)
    (h4 : Good (prodIntegrand N m Ms es ε p' p) K G) :
    Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 3 * prodIntegrand N m Ms es ε p' p ℓ)
      ((1 + T) ^ 3 * K) (fun v => (1 + T) ^ 3 * G v) := by
  have hK := h4.1.nonneg_const
  have hG : ∀ v, 0 ≤ G v := fun v => by
    have h := (norm_nonneg _).trans (h4.2 v 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have a1 := good_s2 (k := k) (Fin.tail Ms) (Fin.tail es) hes1 hes2 hT0 hT' hT'' h1 h2 h3
  have a2 := good_s2 (k := k + 1) Ms es hes0 hes1 hT0 hT hT' h2 h3 h4
  have h := a1.sub (a2.const_mul (massShift (Ms 0) (es 0)))
  refine (h.congr fun ℓ => ?_).mono ?_ ?_
  · linear_combination (-((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 2) *
      prodIntegrand_mul_s N m Ms es hes0 ε p' p ℓ
  · have := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ (1 + T) ^ 2 * K)
    nlinarith
  · intro v
    have := mul_le_mul_of_nonneg_right hT (by have := hG v; positivity : 0 ≤ (1 + T) ^ 2 * G v)
    nlinarith

end Absorb

end QED.TwoLoop.VPHalfAtAssembly

end
