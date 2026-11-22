/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVPFubiniBound
public import QED.TwoLoop.VPHalfAtAssemblyProj

/-!
# Set (a), obligation (N): nested equals joint for an outer factor and an inner tensor

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`, the nested form
`QED.ChainProof.SetANest.LoopNested` of the two-loop classes (an outer one-loop vertex with a
one-loop insertion on its photon line). It abstracts
`QED.ChainProof.HCSide.jointEnergyFirstIntegral_nestedF` from the vacuum polarization integrand
to any inner tensor integrand `G(k, q)^{ρσ}` with polynomial bounds.

For an outer factor `O(k)^{ρσ}` and an inner integrand `G`, `outerInner O G ℓ =
∑ ρ σ, O(ℓ 1)^{ρσ} G(ℓ 1, ℓ 0)^{ρσ}` (loop momentum `ℓ 0` of the insertion, photon momentum
`ℓ 1`). Hypotheses (`OneLoopInnerBound a b G`): at every `k`, `G(k, ·)` is integrable in both
stages of the energy-first integral, the energy integral `∫ dq⁰ G(k, q)` is jointly measurable along
`k = (k⁰, w)` and bounded by `C (1 + ‖k‖)^a (1 + ‖q⃗‖)^{-b}` with `0 ≤ a < 9`, `3 < b`.

* `integrable_decay_mul_bound`: a continuous factor decaying like `(1 + |t|)⁻¹⁰` times such a
  function is integrable in `(t, q⃗)`;
* **`jointEnergyFirstIntegral_outerInner`**: if both stages of the joint integral (T₉) of
  `outerInner O G` are integrable and every entry of `O((t, w))` is continuous in `t` and decays
  like `(1 + |t|)⁻¹⁰`, the joint integral is the energy-first integral of
  `k ↦ ∑ ρ σ, O(k)^{ρσ} ∫_D G(k, ·)^{ρσ}`
  (`QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested`), and that outer integrand is
  integrable in both stages.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetANest

open QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos one_add_norm_cons_le)
open QED.TwoLoop.VPUnitNested (EFInt)

/-- The two-loop integrand of an outer factor `O` and an inner tensor integrand `G`: loop
momentum `ℓ 0` of the insertion, photon momentum `ℓ 1`. -/
noncomputable def outerInner (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, O (ℓ 1) ρ σ * G (ℓ 1) (ℓ 0) ρ σ

/-- The outer integrand with the inner energy-first integral done. -/
noncomputable def outerOf (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) : ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, O k ρ σ * energyFirstIntegral fun q => G k q ρ σ

/-- The hypotheses on an inner tensor integrand: integrability of both stages at every `k`, and
the energy integral jointly measurable along `k = (k⁰, w)` with a bound
`C (1 + ‖k‖)^a (1 + ‖q⃗‖)^{-b}`. -/
structure OneLoopInnerBound (a b : ℝ) (G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) :
    Prop where
  time : ∀ k ρ σ (v : Fin 3 → ℝ), Integrable fun t : ℝ => G k (Fin.cons t v) ρ σ
  spatial : ∀ k ρ σ, Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, G k (Fin.cons t v) ρ σ
  meas : ∀ (w : Fin 3 → ℝ) ρ σ, AEStronglyMeasurable
    (fun x : ℝ × (Fin 3 → ℝ) => ∫ t : ℝ, G (Fin.cons x.1 w) (Fin.cons t x.2) ρ σ) volume
  bound : ∀ ρ σ, ∃ C : ℝ, ∀ (k : Fin 4 → ℝ) (v : Fin 3 → ℝ),
    ‖∫ t : ℝ, G k (Fin.cons t v) ρ σ‖ ≤ C * (1 + ‖k‖) ^ a * (1 + ‖v‖) ^ (-b)

variable {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 9) (hb : 3 < b)

include ha0 ha hb in
/-- **One term of the Fubini condition**: a continuous factor decaying like `(1 + |t|)⁻¹⁰` times
a function bounded by `C (1 + ‖(t, w)‖)^a (1 + ‖v‖)^{-b}` is integrable in `(t, v)`. -/
theorem integrable_decay_mul_bound {g : ℝ → ℂ} (hc : Continuous g) (hd : DecaysLike g 10)
    (w : Fin 3 → ℝ) {S : ℝ × (Fin 3 → ℝ) → ℂ} (hS : AEStronglyMeasurable S volume) {C : ℝ}
    (hC : ∀ x : ℝ × (Fin 3 → ℝ),
      ‖S x‖ ≤ C * (1 + ‖(Fin.cons x.1 w : Fin 4 → ℝ)‖) ^ a * (1 + ‖x.2‖) ^ (-b)) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) => g x.1 * S x := by
  obtain ⟨Co, hCo⟩ := hd
  have hCo0 := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCo
  set K := Co * |C| * (1 + ‖w‖) ^ a
  have hint : Integrable (fun x : ℝ × (Fin 3 → ℝ) =>
      K * ((1 + ‖x.1‖) ^ (-(10 - a)) * (1 + ‖x.2‖) ^ (-b))) := by
    refine Integrable.const_mul ?_ K
    exact (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 10 - a)
      (by simp; linarith)).mul_prod
      (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := b) (by simp; linarith))
  refine hint.mono' ((hc.comp continuous_fst).aestronglyMeasurable.mul hS)
    (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨t, v⟩ := x
  simp only
  rw [norm_mul, Real.norm_eq_abs]
  have ht0 : 0 < 1 + |t| := one_add_abs_pos t
  have hw0 : 0 < 1 + ‖w‖ := by positivity
  have h1 := hCo t
  have h2 : ‖S (t, v)‖ ≤ |C| * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ a * (1 + ‖v‖) ^ (-b) :=
    (hC (t, v)).trans (by gcongr; exact le_abs_self C)
  have hk : (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ a ≤ (1 + |t|) ^ a * (1 + ‖w‖) ^ a := by
    rw [← Real.mul_rpow ht0.le hw0.le]
    exact Real.rpow_le_rpow (by positivity) (one_add_norm_cons_le t w) ha0
  have hz : (1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ a = (1 + |t|) ^ (-(10 - a)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  calc ‖g t‖ * ‖S (t, v)‖
      ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
          (|C| * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ a * (1 + ‖v‖) ^ (-b)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
          (|C| * ((1 + |t|) ^ a * (1 + ‖w‖) ^ a) * (1 + ‖v‖) ^ (-b)) := by gcongr
    _ = K * (((1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ a) * (1 + ‖v‖) ^ (-b)) := by ring
    _ = K * ((1 + |t|) ^ (-(10 - a)) * (1 + ‖v‖) ^ (-b)) := by rw [hz]

/-- The energy integral over `q⁰` of `outerInner`. -/
theorem integral_outerInner_time (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    {G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hG : OneLoopInnerBound a b G)
    (k : Fin 4 → ℝ) (w₁ : Fin 3 → ℝ) :
    ∫ t₁ : ℝ, outerInner O G ![Fin.cons t₁ w₁, k] =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, O k ρ σ * ∫ t₁ : ℝ, G k (Fin.cons t₁ w₁) ρ σ := by
  have hI := fun ρ σ => hG.time k ρ σ w₁
  simp only [outerInner, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ => (hI ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [integral_finsetSum _ fun σ _ => (hI ρ σ).const_mul _]
  simp only [integral_const_mul]

include ha0 ha hb in
/-- **The Fubini condition for `outerInner`**, at every spatial photon momentum. -/
theorem integrable_outerInner_time (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    {G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hG : OneLoopInnerBound a b G)
    (hc : ∀ w ρ σ, Continuous fun t => O (Fin.cons t w) ρ σ)
    (hd : ∀ w ρ σ, DecaysLike (fun t => O (Fin.cons t w) ρ σ) 10) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, outerInner O G ![Fin.cons t₁ x.2, Fin.cons x.1 w] := by
  simp only [integral_outerInner_time O hG]
  refine integrable_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ => ?_
  obtain ⟨C, hC⟩ := hG.bound ρ σ
  exact integrable_decay_mul_bound ha0 ha hb (hc w ρ σ) (hd w ρ σ) w (hG.meas w ρ σ)
    (C := C) fun x => hC _ _

/-- The inner energy-first integral of `outerInner` is `outerOf`. -/
theorem energyFirstIntegral_outerInner (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    {G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hG : OneLoopInnerBound a b G)
    (k : Fin 4 → ℝ) :
    energyFirstIntegral (fun q => outerInner O G ![q, k]) = outerOf O G k := by
  have hD : ∀ ρ σ, QED.TwoLoop.NestedVP.IntegrableD fun q => G k q ρ σ :=
    fun ρ σ => ⟨hG.time k ρ σ, hG.spatial k ρ σ⟩
  simp only [outerInner, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun ρ _ =>
    QED.TwoLoop.NestedVP.IntegrableD.finsetSum _ fun σ _ => (hD ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun σ _ => (hD ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]

include ha0 ha hb in
/-- **Nested equals joint for an outer factor and an inner tensor integrand**: for an outer
factor with continuous entries decaying like `(1 + |t|)⁻¹⁰` along `k = (t, w)`, an inner
integrand with `OneLoopInnerBound a b`, `0 ≤ a < 9`, `3 < b`, and both stages of the joint integral
integrable, the joint integral is the energy-first integral of `outerOf O G`, which is integrable
in both stages. -/
theorem jointEnergyFirstIntegral_outerInner (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    {G : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hG : OneLoopInnerBound a b G)
    (hc : ∀ w ρ σ, Continuous fun t => O (Fin.cons t w) ρ σ)
    (hd : ∀ w ρ σ, DecaysLike (fun t => O (Fin.cons t w) ρ σ) 10)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 (outerInner O G)) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (outerInner O G) = energyFirstIntegral (outerOf O G) ∧
      EFInt (outerOf O G) := by
  have hT := integrable_outerInner_time ha0 ha hb O hG hc hd
  have he : (fun k => energyFirstIntegral fun q => outerInner O G ![q, k]) = outerOf O G :=
    funext (energyFirstIntegral_outerInner O hG)
  refine ⟨?_, ?_⟩
  · rw [QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested _ hF (ae_of_all _ hT), he]
  · have h := QED.TwoLoop.VPHalfAtAssembly.efInt_of_joint _ hF hT
    rwa [he] at h

end QED.ChainProof.SetANest

end
