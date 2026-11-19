/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCLimitBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nested equals joint for the bubble–bubble integrand, at fixed `ε`

Helper level, Phase 5 Stage 1a, obligation O3-6 (`docs/HIGHER-LOOP-PLAN.md`, risk R2), at fixed
`ε > 0`. The bubble–bubble integrand in the nested routing, with loop momenta `ℓ 0 = q₁` (first
bubble), `ℓ 1 = q₂` (second bubble) and `ℓ 2 = k` (photon), is

`bbIntegrand P O ℓ = ∑_{a b} O(k) a b · Π-integrand(k, q₁)_{a} · Π-integrand(k, q₂)_{b}`,

with `a = (ρ, σ)`, `b = (ρ', σ')` the Lorentz indices of the two bubbles and `O` an outer factor.
For `O` continuous with decay `(1 + |k⁰|)⁻¹⁴` at fixed spatial `k` (`IsChainOuter`; the candidate
outer factor `QED.ChainProof.HCLimit.chainOuter` qualifies, `isChainOuter_chainOuter`):

* `integrable_bb_hA`, `integrable_bb_hB`: **the two Fubini conditions** `hA`, `hB` of the
  inner-first route `QED.ChainProof.jointEnergyFirstIntegral_three_eq_nested_innerFirst` hold, for
  every spatial momentum (not only almost every), under the mass and Pauli–Villars conditions.
  - `hA` uses the unintegrated-bubble bound `C (1 + |τ|)(1 + |t|)⁻²`, the inner bound
    `(1 + ‖k‖)^{17/2} (1 + ‖v‖)^{-7/2}` and the decay `14`: the dominating function is
    `(1 + |t₂|)⁻² (1 + |t₃|)^{-9/2} (1 + ‖v₁‖)^{-7/2}`.
  - `hB` uses the closed-form bound `(1 + ‖k‖)⁴` of the integrated first bubble, the inner bound
    and the decay `14`: the dominating function is `(1 + |t₃|)^{-3/2} (1 + ‖v₂‖)^{-7/2}`. The
    exponent `14` is exactly what is needed (`14 > 4 + 17/2 + 1`).
* **`jointEnergyFirstIntegral_bbIntegrand`**: if both stages of the joint energy-first integral
  of `bbIntegrand P O` are integrable (`hF`, the form of the integrability companion (HC₀)), then
  the joint integral is the outer one-loop energy-first integral of
  `∑_{a b} O(k) a b Π_ε(k)_a Π_ε(k)_b`, with `Π_ε(k)_a` the energy-first integral of the one-loop
  vacuum polarization (`piEps`), and with the closed form of
  `QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq` inserted
  (`jointEnergyFirstIntegral_bbIntegrand_closedForm`).

## What is not proved here

* `hF` (three-loop integrability of `bbIntegrand`). It is the transport of (HC₀) for the
  representative `QED.ChainProof.Enum.repBB` to the nested routing; it is a hypothesis here.
* The identification of `(2π)⁻¹²` times the regulated amplitude of `repBB`, in the nested routing,
  with `bbIntegrand P (chainOuter …)` (the three-loop analogue of
  `QED.TwoLoop.NestedVP.integrand_eq`).
* The limit `ε → 0⁺` of the outer integral.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.HCLimit

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos one_le_one_add_abs)

/-! ### The integrand -/

/-- An outer factor for the bubble–bubble integrand: continuous, and decaying like
`(1 + |t|)⁻¹⁴` in the photon energy at fixed spatial photon momentum. -/
structure IsChainOuter (O : (Fin 4 → ℝ) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℂ) : Prop where
  cont : ∀ a b, Continuous fun k => O k a b
  decay : ∀ (w : Fin 3 → ℝ) a b, DecaysLike (fun t => O (Fin.cons t w) a b) 14

/-- The bubble–bubble integrand in the nested routing: `ℓ 0`, `ℓ 1` on the two bubbles, `ℓ 2` on
the photon. -/
noncomputable def bbIntegrand (P : Params) (O : (Fin 4 → ℝ) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℂ)
    (ℓ : Fin 3 → Fin 4 → ℝ) : ℂ :=
  ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O (ℓ 2) a b *
    vacuumPolarizationIntegrand P P.ε (ℓ 2) (ℓ 0) a.1 a.2 *
    vacuumPolarizationIntegrand P P.ε (ℓ 2) (ℓ 1) b.1 b.2

/-- The one-loop vacuum polarization at fixed `ε = P.ε`, as an energy-first integral. -/
noncomputable def piEps (P : Params) (k : Fin 4 → ℝ) (a : Fin 4 × Fin 4) : ℂ :=
  energyFirstIntegral fun q => vacuumPolarizationIntegrand P P.ε k q a.1 a.2

theorem bbIntegrand_vec (P : Params) (O : (Fin 4 → ℝ) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℂ)
    (q₁ q₂ k : Fin 4 → ℝ) :
    bbIntegrand P O ![q₁, q₂, k] = ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O k a b *
      vacuumPolarizationIntegrand P P.ε k q₁ a.1 a.2 *
      vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2 := rfl

/-- The candidate outer factor `chainOuter` is an outer factor, for `ε > 0`. -/
theorem isChainOuter_chainOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ)
    (α β μ : Fin 4) : IsChainOuter fun k => chainOuter P p kext k α β μ :=
  ⟨fun a b => continuous_chainOuter P hε p kext α β μ a b,
    fun w a b => decaysLike_chainOuter P hε p kext w α β μ a b⟩

/-! ### Finite sums -/

theorem integral_sum_sum {X : Type*} [MeasureSpace X] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → X → ℂ) (hf : ∀ a b, Integrable (f a b)) :
    ∫ x, ∑ a, ∑ b, f a b x = ∑ a, ∑ b, ∫ x, f a b x := by
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hf a b]
  exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hf a b

theorem efi_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → κ → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ a b, QED.TwoLoop.NestedVP.IntegrableD (F a b)) :
    energyFirstIntegral (fun ℓ => ∑ a, ∑ b, F a b ℓ) =
      ∑ a, ∑ b, energyFirstIntegral (F a b) := by
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun a _ =>
    QED.TwoLoop.NestedVP.IntegrableD.finsetSum _ fun b _ => hF a b]
  exact Finset.sum_congr rfl fun a _ =>
    QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun b _ => hF a b

variable {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
  (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
  (hε : 0 < P.ε)
  {O : (Fin 4 → ℝ) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℂ}

include hε in
/-- The energy integral over `q₁⁰` of the integrand. -/
theorem integral_bb_time (k q₂ : Fin 4 → ℝ) (w₁ : Fin 3 → ℝ) :
    ∫ t₁ : ℝ, bbIntegrand P O ![Fin.cons t₁ w₁, q₂, k] =
      ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O k a b *
        (∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε k (Fin.cons t₁ w₁) a.1 a.2) *
        vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2 := by
  simp only [bbIntegrand_vec]
  have hI := fun a : Fin 4 × Fin 4 =>
    integrable_vacuumPolarizationIntegrand_time hε P k a.1 a.2 w₁
  have e : ∀ (a b : Fin 4 × Fin 4) (t₁ : ℝ), O k a b *
      vacuumPolarizationIntegrand P P.ε k (Fin.cons t₁ w₁) a.1 a.2 *
      vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2 =
      (O k a b * vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2) *
        vacuumPolarizationIntegrand P P.ε k (Fin.cons t₁ w₁) a.1 a.2 := fun _ _ _ => by ring
  simp only [e]
  rw [integral_sum_sum _ fun a b => (hI a).const_mul _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]
  ring

/-! ### Real-number bounds -/

theorem rpow_cons_le (t : ℝ) (w : Fin 3 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ r ≤ (1 + |t|) ^ r * (1 + ‖w‖) ^ r := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity)
    (QED.TwoLoop.NestedVPFubiniBound.one_add_norm_cons_le t w) hr

/-- The arithmetic of the dominating function of `hA`. -/
theorem bound_A {CO CG CV : ℝ} (hCO : 0 ≤ CO) (hCG : 0 ≤ CG) (hCV : 0 ≤ CV) (w : Fin 3 → ℝ)
    (t₂ t₃ : ℝ) (v : Fin 3 → ℝ) {x y z : ℝ}
    (hx : x ≤ CO * (1 + |t₃|) ^ (-(14 : ℤ)))
    (hy : y ≤ CG * (1 + ‖(Fin.cons t₃ w : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)))
    (hz : z ≤ CV * ((1 + |t₂ + t₃|)⁻¹ * (1 + |t₂|)⁻¹)) (_hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hz0 : 0 ≤ z) :
    x * y * z ≤ CO * (CG * (1 + ‖w‖) ^ (17 / 2 : ℝ)) * CV *
      (((1 + |t₂|) ^ (-(2 : ℝ)) * (1 + |t₃|) ^ (-(9 / 2 : ℝ))) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by
  set A := 1 + |t₂|
  set B := 1 + |t₃|
  set Wn := 1 + ‖w‖
  set V := 1 + ‖v‖
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hW : 0 < Wn := by positivity
  have hV : 0 < V := by positivity
  have hy' : y ≤ CG * (B ^ (17 / 2 : ℝ) * Wn ^ (17 / 2 : ℝ)) * V ^ (-(7 / 2 : ℝ)) :=
    hy.trans (by gcongr; exact rpow_cons_le t₃ w (by norm_num))
  have hz' : z ≤ CV * ((B * A⁻¹) * A⁻¹) := by
    refine hz.trans (mul_le_mul_of_nonneg_left ?_ hCV)
    exact mul_le_mul_of_nonneg_right (inv_one_add_abs_add_le t₂ t₃) (by positivity)
  have h1 : x * y * z ≤ (CO * B ^ (-(14 : ℤ))) *
      (CG * (B ^ (17 / 2 : ℝ) * Wn ^ (17 / 2 : ℝ)) * V ^ (-(7 / 2 : ℝ))) *
      (CV * ((B * A⁻¹) * A⁻¹)) := by
    refine mul_le_mul (mul_le_mul hx hy' hy0 (by positivity)) hz' hz0 (by positivity)
  have eA : A ^ (-(2 : ℝ)) = A⁻¹ * A⁻¹ := by
    rw [Real.rpow_neg hA.le, Real.rpow_two, sq, mul_inv]
  have eB : B ^ (-(9 / 2 : ℝ)) = B ^ (-(14 : ℤ)) * B ^ (17 / 2 : ℝ) * B := by
    calc B ^ (-(9 / 2 : ℝ)) = B ^ (((-14 : ℤ) : ℝ) + 17 / 2 + 1) := by norm_num
      _ = B ^ ((-14 : ℤ) : ℝ) * B ^ (17 / 2 : ℝ) * B ^ (1 : ℝ) := by
          rw [Real.rpow_add hB, Real.rpow_add hB]
      _ = _ := by rw [Real.rpow_intCast, Real.rpow_one]
  rw [eA, eB]
  refine h1.trans (le_of_eq ?_)
  ring

/-- The arithmetic of the dominating function of `hB`. -/
theorem bound_B {CO CP CG : ℝ} (hCO : 0 ≤ CO) (hCP : 0 ≤ CP) (hCG : 0 ≤ CG) (w : Fin 3 → ℝ)
    (t : ℝ) (v : Fin 3 → ℝ) {x y z : ℝ}
    (hx : x ≤ CO * (1 + |t|) ^ (-(14 : ℤ)))
    (hy : y ≤ CP * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ 4)
    (hz : z ≤ CG * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ)))
    (_hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) :
    x * y * z ≤ CO * (CP * (1 + ‖w‖) ^ 4) * (CG * (1 + ‖w‖) ^ (17 / 2 : ℝ)) *
      ((1 + |t|) ^ (-(3 / 2 : ℝ)) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by
  set B := 1 + |t|
  set Wn := 1 + ‖w‖
  set V := 1 + ‖v‖
  have hB : 0 < B := by positivity
  have hW : 0 < Wn := by positivity
  have hV : 0 < V := by positivity
  have hy' : y ≤ CP * (B ^ 4 * Wn ^ 4) := by
    refine hy.trans (mul_le_mul_of_nonneg_left ?_ hCP)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (QED.TwoLoop.NestedVPFubiniBound.one_add_norm_cons_le t w) 4
  have hz' : z ≤ CG * (B ^ (17 / 2 : ℝ) * Wn ^ (17 / 2 : ℝ)) * V ^ (-(7 / 2 : ℝ)) :=
    hz.trans (by gcongr; exact rpow_cons_le t w (by norm_num))
  have h1 : x * y * z ≤ (CO * B ^ (-(14 : ℤ))) * (CP * (B ^ 4 * Wn ^ 4)) *
      (CG * (B ^ (17 / 2 : ℝ) * Wn ^ (17 / 2 : ℝ)) * V ^ (-(7 / 2 : ℝ))) :=
    mul_le_mul (mul_le_mul hx hy' hy0 (by positivity)) hz' hz0 (by positivity)
  have eB : B ^ (-(3 / 2 : ℝ)) = B ^ (-(14 : ℤ)) * B ^ 4 * B ^ (17 / 2 : ℝ) := by
    calc B ^ (-(3 / 2 : ℝ)) = B ^ (((-14 : ℤ) : ℝ) + (4 : ℕ) + 17 / 2) := by norm_num
      _ = B ^ ((-14 : ℤ) : ℝ) * B ^ ((4 : ℕ) : ℝ) * B ^ (17 / 2 : ℝ) := by
          rw [Real.rpow_add hB, Real.rpow_add hB]
      _ = _ := by rw [Real.rpow_intCast, Real.rpow_natCast]
  rw [eB]
  refine h1.trans (le_of_eq ?_)
  ring

/-! ### The Fubini condition `hA` -/

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- One term of `hA` is integrable. -/
theorem integrable_bbTerm_A (hO : IsChainOuter O) (w w₂ : Fin 3 → ℝ) (a b : Fin 4 × Fin 4) :
    Integrable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      O (Fin.cons p.1.2 w) a b *
        (∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons p.1.2 w) (Fin.cons t₁ p.2) a.1 a.2) *
        vacuumPolarizationIntegrand P P.ε (Fin.cons p.1.2 w) (Fin.cons p.1.1 w₂) b.1 b.2 := by
  obtain ⟨CO, hCO⟩ := hO.decay w a b
  have hCO0 := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCO
  obtain ⟨CG, hCG0, hCG⟩ :=
    QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly hm hM₁ hM₂ hPV₁ hPV₂ hε a.1 a.2
  obtain ⟨CV, hCV0, hCV⟩ := exists_norm_vpIntegrand_cons_le P hε w₂ w b.1 b.2
  set K := CO * (CG * (1 + ‖w‖) ^ (17 / 2 : ℝ)) * CV
  have hint : Integrable (fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      K * (((1 + ‖p.1.1‖) ^ (-(2 : ℝ)) * (1 + ‖p.1.2‖) ^ (-(9 / 2 : ℝ))) *
        (1 + ‖p.2‖) ^ (-(7 / 2 : ℝ)))) := by
    refine Integrable.const_mul ?_ K
    exact ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).mul_prod
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 9 / 2) (by simp; norm_num))).mul_prod
      (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2) (by simp; norm_num))
  have hk : Continuous fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (Fin.cons p.1.2 w : Fin 4 → ℝ) :=
    continuous_cons_fst (continuous_snd.comp continuous_fst) continuous_const
  have m1 : Continuous fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => O (Fin.cons p.1.2 w) a b :=
    (hO.cont a b).comp hk
  have m2 : StronglyMeasurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons p.1.2 w) (Fin.cons t₁ p.2) a.1 a.2 :=
    by
      have hmm := (hk.prodMk continuous_snd).measurable
      simpa only [Function.comp_def] using (stronglyMeasurable_vpTime P hε a.1 a.2).comp_measurable hmm
  have m3 : Continuous fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      vacuumPolarizationIntegrand P P.ε (Fin.cons p.1.2 w) (Fin.cons p.1.1 w₂) b.1 b.2 :=
    continuous_vpIntegrand_comp P hε hk
      (continuous_cons_fst (continuous_fst.comp continuous_fst) continuous_const) b.1 b.2
  refine hint.mono' ((m1.aestronglyMeasurable.mul m2.aestronglyMeasurable).mul
    m3.aestronglyMeasurable) (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨⟨t₂, t₃⟩, v⟩ := p
  simp only [Real.norm_eq_abs]
  rw [norm_mul, norm_mul, integral_vacuumPolarizationIntegrand_time hε]
  have hz := hCV t₂ t₃
  exact bound_A hCO0 hCG0 hCV0 w t₂ t₃ v (hCO t₃) (hCG _ v) hz (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _)

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **The Fubini condition `hA`** of the inner-first route, for every `w`, `w₂`. -/
theorem integrable_bb_hA (hO : IsChainOuter O) (w w₂ : Fin 3 → ℝ) :
    Integrable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, bbIntegrand P O ![Fin.cons t₁ p.2, Fin.cons p.1.1 w₂, Fin.cons p.1.2 w] := by
  have e : (fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, bbIntegrand P O ![Fin.cons t₁ p.2, Fin.cons p.1.1 w₂, Fin.cons p.1.2 w]) =
      fun p => ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O (Fin.cons p.1.2 w) a b *
        (∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons p.1.2 w) (Fin.cons t₁ p.2) a.1 a.2) *
        vacuumPolarizationIntegrand P P.ε (Fin.cons p.1.2 w) (Fin.cons p.1.1 w₂) b.1 b.2 := by
    funext p
    exact integral_bb_time hε _ _ _
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_bbTerm_A hm hM₁ hM₂ hPV₁ hPV₂ hε hO w w₂ a b

/-! ### The Fubini condition `hB` -/

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- The three inner integrals of `hB`: the first bubble completely, then the energy of the
second. -/
theorem integral_bb_hB_eq (k : Fin 4 → ℝ) (v₂ : Fin 3 → ℝ) :
    ∫ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ, bbIntegrand P O ![Fin.cons t₁ w₁, Fin.cons t₂ v₂, k] =
      ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O k a b * piEps P k a *
        ∫ t₂ : ℝ, vacuumPolarizationIntegrand P P.ε k (Fin.cons t₂ v₂) b.1 b.2 := by
  have hW := fun a : Fin 4 × Fin 4 =>
    integrable_integral_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε k a.1 a.2
  have hT := fun b : Fin 4 × Fin 4 =>
    integrable_vacuumPolarizationIntegrand_time hε P k b.1 b.2 v₂
  have h1 : ∀ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ,
      bbIntegrand P O ![Fin.cons t₁ w₁, Fin.cons t₂ v₂, k] =
      ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, (O k a b * piEps P k a) *
        vacuumPolarizationIntegrand P P.ε k (Fin.cons t₂ v₂) b.1 b.2 := by
    intro t₂
    simp only [integral_bb_time hε]
    have e : ∀ (a b : Fin 4 × Fin 4) (w₁ : Fin 3 → ℝ), O k a b *
        (∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε k (Fin.cons t₁ w₁) a.1 a.2) *
        vacuumPolarizationIntegrand P P.ε k (Fin.cons t₂ v₂) b.1 b.2 =
        (O k a b * vacuumPolarizationIntegrand P P.ε k (Fin.cons t₂ v₂) b.1 b.2) *
          ∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε k (Fin.cons t₁ w₁) a.1 a.2 :=
      fun _ _ _ => by ring
    simp only [e]
    rw [integral_sum_sum _ fun a b => (hW a).const_mul _]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
    simp only [piEps, energyFirstIntegral]
    ring
  simp only [h1]
  rw [integral_sum_sum _ fun a b => (hT b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- One term of `hB` is integrable. -/
theorem integrable_bbTerm_B (hO : IsChainOuter O) (w : Fin 3 → ℝ) (a b : Fin 4 × Fin 4) :
    Integrable fun p : ℝ × (Fin 3 → ℝ) =>
      O (Fin.cons p.1 w) a b * piEps P (Fin.cons p.1 w) a *
        ∫ t₂ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons p.1 w) (Fin.cons t₂ p.2) b.1 b.2 := by
  obtain ⟨CO, hCO⟩ := hO.decay w a b
  have hCO0 := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCO
  obtain ⟨CP, hCP0, hCP⟩ := exists_norm_vpPi_le hm hM₁ hM₂ hPV₁ hPV₂ hε a.1 a.2
  obtain ⟨CG, hCG0, hCG⟩ :=
    QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly hm hM₁ hM₂ hPV₁ hPV₂ hε b.1 b.2
  set K := CO * (CP * (1 + ‖w‖) ^ 4) * (CG * (1 + ‖w‖) ^ (17 / 2 : ℝ))
  have hint : Integrable (fun p : ℝ × (Fin 3 → ℝ) =>
      K * ((1 + ‖p.1‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖p.2‖) ^ (-(7 / 2 : ℝ)))) := by
    refine Integrable.const_mul ?_ K
    exact (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)).mul_prod
      (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2) (by simp; norm_num))
  have hk : Continuous fun p : ℝ × (Fin 3 → ℝ) => (Fin.cons p.1 w : Fin 4 → ℝ) :=
    continuous_cons_fst continuous_fst continuous_const
  have m1 : Continuous fun p : ℝ × (Fin 3 → ℝ) => O (Fin.cons p.1 w) a b :=
    (hO.cont a b).comp hk
  have m2 : StronglyMeasurable fun p : ℝ × (Fin 3 → ℝ) => piEps P (Fin.cons p.1 w) a :=
    by
      have hmm := hk.measurable
      simpa only [Function.comp_def, piEps] using (stronglyMeasurable_vpPi P hε a.1 a.2).comp_measurable hmm
  have m3 : StronglyMeasurable fun p : ℝ × (Fin 3 → ℝ) =>
      ∫ t₂ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons p.1 w) (Fin.cons t₂ p.2) b.1 b.2 :=
    by
      have hmm := (hk.prodMk continuous_snd).measurable
      simpa only [Function.comp_def] using (stronglyMeasurable_vpTime P hε b.1 b.2).comp_measurable hmm
  refine hint.mono' ((m1.aestronglyMeasurable.mul m2.aestronglyMeasurable).mul
    m3.aestronglyMeasurable) (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨t, v⟩ := p
  simp only [Real.norm_eq_abs]
  rw [norm_mul, norm_mul, integral_vacuumPolarizationIntegrand_time hε]
  exact bound_B hCO0 hCP0 hCG0 w t v (hCO t) (hCP _) (hCG _ v) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _)

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **The Fubini condition `hB`** of the inner-first route, for every `w`. -/
theorem integrable_bb_hB (hO : IsChainOuter O) (w : Fin 3 → ℝ) :
    Integrable fun p : ℝ × (Fin 3 → ℝ) =>
      ∫ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ,
        bbIntegrand P O ![Fin.cons t₁ w₁, Fin.cons t₂ p.2, Fin.cons p.1 w] := by
  have e : (fun p : ℝ × (Fin 3 → ℝ) => ∫ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ,
      bbIntegrand P O ![Fin.cons t₁ w₁, Fin.cons t₂ p.2, Fin.cons p.1 w]) =
      fun p => ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O (Fin.cons p.1 w) a b *
        piEps P (Fin.cons p.1 w) a *
        ∫ t₂ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons p.1 w) (Fin.cons t₂ p.2) b.1 b.2 := by
    funext p
    exact integral_bb_hB_eq hm hM₁ hM₂ hPV₁ hPV₂ hε _ _
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_bbTerm_B hm hM₁ hM₂ hPV₁ hPV₂ hε hO w a b

/-! ### Nested equals joint -/

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- The nested energy-first integrals of the integrand, at each photon momentum. -/
theorem efi_efi_bbIntegrand (k : Fin 4 → ℝ) :
    energyFirstIntegral (fun q₂ => energyFirstIntegral fun q₁ => bbIntegrand P O ![q₁, q₂, k]) =
      ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O k a b * piEps P k a * piEps P k b := by
  have hD := fun a : Fin 4 × Fin 4 =>
    QED.TwoLoop.NestedVP.integrableD_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε k a.1 a.2
  have h1 : ∀ q₂ : Fin 4 → ℝ, energyFirstIntegral (fun q₁ => bbIntegrand P O ![q₁, q₂, k]) =
      ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, (O k a b * piEps P k a) *
        vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2 := by
    intro q₂
    simp only [bbIntegrand_vec]
    have e : ∀ (a b : Fin 4 × Fin 4) (q₁ : Fin 4 → ℝ), O k a b *
        vacuumPolarizationIntegrand P P.ε k q₁ a.1 a.2 *
        vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2 =
        (O k a b * vacuumPolarizationIntegrand P P.ε k q₂ b.1 b.2) *
          vacuumPolarizationIntegrand P P.ε k q₁ a.1 a.2 := fun _ _ _ => by ring
    simp only [e]
    rw [efi_sum_sum _ fun a b => (hD a).const_mul _]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
    simp only [piEps]
    ring
  simp only [h1]
  rw [efi_sum_sum _ fun a b => (hD b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  rfl

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **Nested equals joint for the bubble–bubble integrand** (O3-6, at fixed `ε > 0`): under the
mass and Pauli–Villars conditions, for an outer factor with decay `14`, if both stages of the joint
energy-first integral are integrable (`hF`), the joint integral (T₉) at three loops is the outer
one-loop energy-first integral of `∑_{a b} O(k) a b Π_ε(k)_a Π_ε(k)_b`. -/
theorem jointEnergyFirstIntegral_bbIntegrand (hO : IsChainOuter O)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 (bbIntegrand P O)) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 (bbIntegrand P O) =
      energyFirstIntegral fun k =>
        ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O k a b * piEps P k a * piEps P k b := by
  rw [jointEnergyFirstIntegral_three_eq_nested_innerFirst _ hF
    (Filter.Eventually.of_forall fun w => Filter.Eventually.of_forall fun w₂ =>
      integrable_bb_hA hm hM₁ hM₂ hPV₁ hPV₂ hε hO w w₂)
    (Filter.Eventually.of_forall fun w => integrable_bb_hB hm hM₁ hM₂ hPV₁ hPV₂ hε hO w)]
  simp only [efi_efi_bbIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε]

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- `Π_ε(k)` in closed form. -/
theorem piEps_eq (k : Fin 4 → ℝ) (a : Fin 4 × Fin 4) :
    piEps P k a =
      I * QED.TwoLoop.VPHalfAt.vpLoopEps P P.ε (Minkowski.dot k k) *
          ((Minkowski.dot k k * Minkowski.metric a.1 a.2 - k a.1 * k a.2 : ℝ) : ℂ)
        + (P.ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P P.ε (Minkowski.dot k k) *
          (Minkowski.metric a.1 a.2 : ℂ) :=
  QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂ hε
    k a.1 a.2

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **Nested equals joint with both bubbles in closed form**: the joint integral of the
bubble–bubble integrand is the outer one-loop energy-first integral of
`∑_{a b} O(k) a b T_a(k) T_b(k)`,
`T_{ρσ}(k) = i Π̂_ε(k²)(k² g_{ρσ} - k_ρ k_σ) + ε S_ε(k²) g_{ρσ}`. -/
theorem jointEnergyFirstIntegral_bbIntegrand_closedForm (hO : IsChainOuter O)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 (bbIntegrand P O)) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 (bbIntegrand P O) =
      energyFirstIntegral fun k =>
        ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O k a b *
          (I * QED.TwoLoop.VPHalfAt.vpLoopEps P P.ε (Minkowski.dot k k) *
              ((Minkowski.dot k k * Minkowski.metric a.1 a.2 - k a.1 * k a.2 : ℝ) : ℂ)
            + (P.ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P P.ε (Minkowski.dot k k) *
              (Minkowski.metric a.1 a.2 : ℂ)) *
          (I * QED.TwoLoop.VPHalfAt.vpLoopEps P P.ε (Minkowski.dot k k) *
              ((Minkowski.dot k k * Minkowski.metric b.1 b.2 - k b.1 * k b.2 : ℝ) : ℂ)
            + (P.ε : ℂ) * QED.TwoLoop.VPHalfAt.vpExtraEps P P.ε (Minkowski.dot k k) *
              (Minkowski.metric b.1 b.2 : ℂ)) := by
  rw [jointEnergyFirstIntegral_bbIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε hO hF]
  simp only [piEps_eq hm hM₁ hM₂ hPV₁ hPV₂ hε]

/-- **The candidate chain outer factor**: nested equals joint for
`bbIntegrand P (chainOuter P p kext · α β μ)`, given its three-loop integrability. -/
theorem jointEnergyFirstIntegral_bbIntegrand_chainOuter (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3
      (bbIntegrand P fun k => chainOuter P p kext k α β μ)) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 (bbIntegrand P fun k => chainOuter P p kext k α β μ) =
      energyFirstIntegral fun k => ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4,
        chainOuter P p kext k α β μ a b * piEps P k a * piEps P k b :=
  jointEnergyFirstIntegral_bbIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε
    (isChainOuter_chainOuter P hε p kext α β μ) hF

end QED.ChainProof.HCLimit

end
