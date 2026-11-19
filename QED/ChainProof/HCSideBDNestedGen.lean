/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVPFubiniBound
public import QED.TwoLoop.VPHalfAtAssemblyProj

/-!
# Nested equals joint for a vacuum-polarization insertion with a general outer factor

Helper for the nested form of the bubble–`δ₃` and `δ₃`–bubble classes. For an outer factor
`O(k)^{ρσ}`, the two-loop integrand `nestedF P O ℓ = ∑ ρ σ, O(ℓ₁)^{ρσ} Π^{ρσ}_ε(ℓ₁, ℓ₀)`, with
`Π` the one-loop vacuum polarization integrand, has, at fixed `ε > 0`:

* `integrable_outer_mul_spatialG`, `integrable_nestedF_time`: the Fubini condition of
  `QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested` at every spatial photon momentum, when
  every entry of `O((t, w))` is continuous in `t` and decays like `(1 + |t|)⁻¹⁰` (as for
  `QED.TwoLoop.NestedVPFubiniBound.integrable_vpOuter_mul_spatialG`);
* **`jointEnergyFirstIntegral_nestedF`**: given both stages of the joint integral, the joint
  integral is the energy-first integral of `outerF P O k = ∑ ρ σ, O(k)^{ρσ} T^{ρσ}(k)` with the
  closed form `T = i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g` of the inner loop, and `outerF P O` is
  integrable in both stages.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.HCSide

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos one_add_norm_cons_le
  aestronglyMeasurable_spatialG_cons exists_norm_spatialG_le_poly)
open QED.TwoLoop.VPHalfAt (vpLoopEps vpExtraEps energyFirstIntegral_vacuumPolarizationIntegrand_eq)
open QED.TwoLoop.VPHalfAtAssembly (vpT efInt_of_joint)
open QED.TwoLoop.VPUnitNested (EFInt)

/-- The two-loop integrand with outer factor `O`: loop momentum `ℓ 0`, photon momentum `ℓ 1`. -/
noncomputable def nestedF (P : Params) (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, O (ℓ 1) ρ σ * vacuumPolarizationIntegrand P P.ε (ℓ 1) (ℓ 0) ρ σ

/-- The outer integrand with the inner loop in closed form. -/
noncomputable def outerF (P : Params) (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) :
    ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, O k ρ σ * vpT (I * vpLoopEps P P.ε (Minkowski.dot k k))
    ((P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k)) k ρ σ

variable {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
  (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
  (hε : 0 < P.ε)

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **One term of the Fubini condition**: a continuous factor decaying like `(1 + |t|)⁻¹⁰` times
the energy integral of the vacuum polarization integrand is integrable in `(t, v⃗)`. -/
theorem integrable_outer_mul_spatialG {g : ℝ → ℂ} (hc : Continuous g) (hd : DecaysLike g 10)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) => g x.1 * spatialG P P.ε (Fin.cons x.1 w) ρ σ x.2 := by
  obtain ⟨Co, hCo⟩ := hd
  have hCo0 := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCo
  obtain ⟨Ci, hCi0, hCi⟩ := exists_norm_spatialG_le_poly hm hM₁ hM₂ hPV₁ hPV₂ hε ρ σ
  set K := Co * Ci * (1 + ‖w‖) ^ (17 / 2 : ℝ)
  have hint : Integrable (fun x : ℝ × (Fin 3 → ℝ) =>
      K * ((1 + ‖x.1‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖x.2‖) ^ (-(7 / 2 : ℝ)))) := by
    refine Integrable.const_mul ?_ K
    exact (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)).mul_prod
      (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2) (by simp; norm_num))
  refine hint.mono' ((hc.comp continuous_fst).aestronglyMeasurable.mul
    (aestronglyMeasurable_spatialG_cons P hε w ρ σ)) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨t, v⟩ := x
  simp only
  rw [norm_mul, Real.norm_eq_abs]
  have ht0 : 0 < 1 + |t| := one_add_abs_pos t
  have hw0 : 0 < 1 + ‖w‖ := by positivity
  have hv0 : 0 < 1 + ‖v‖ := by positivity
  have h1 := hCo t
  have h2 := hCi (Fin.cons t w) v
  have hk : (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ)
      ≤ (1 + |t|) ^ (17 / 2 : ℝ) * (1 + ‖w‖) ^ (17 / 2 : ℝ) := by
    rw [← Real.mul_rpow ht0.le hw0.le]
    exact Real.rpow_le_rpow (by positivity) (one_add_norm_cons_le t w) (by norm_num)
  have hz : (1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ (17 / 2 : ℝ) = (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add ht0]
    norm_num
  calc ‖g t‖ * ‖spatialG P P.ε (Fin.cons t w) ρ σ v‖
      ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
          (Ci * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
          (Ci * ((1 + |t|) ^ (17 / 2 : ℝ) * (1 + ‖w‖) ^ (17 / 2 : ℝ)) *
            (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by gcongr
    _ = K * (((1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ (17 / 2 : ℝ)) *
          (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by ring
    _ = K * ((1 + |t|) ^ (-(3 / 2 : ℝ)) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by rw [hz]

include hε in
/-- The energy integral over `q⁰` of `nestedF`. -/
theorem integral_nestedF_time (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ)
    (w₁ : Fin 3 → ℝ) :
    ∫ t₁ : ℝ, nestedF P O ![Fin.cons t₁ w₁, k] =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, O k ρ σ * spatialG P P.ε k ρ σ w₁ := by
  have hI := fun ρ σ => integrable_vacuumPolarizationIntegrand_time hε P k ρ σ w₁
  simp only [nestedF, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ => (hI ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [integral_finsetSum _ fun σ _ => (hI ρ σ).const_mul _]
  simp only [integral_const_mul, integral_vacuumPolarizationIntegrand_time hε]

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **The Fubini condition for `nestedF`**, at every spatial photon momentum. -/
theorem integrable_nestedF_time (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hc : ∀ w ρ σ, Continuous fun t => O (Fin.cons t w) ρ σ)
    (hd : ∀ w ρ σ, DecaysLike (fun t => O (Fin.cons t w) ρ σ) 10) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, nestedF P O ![Fin.cons t₁ x.2, Fin.cons x.1 w] := by
  simp only [integral_nestedF_time hε]
  exact integrable_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ =>
    integrable_outer_mul_spatialG hm hM₁ hM₂ hPV₁ hPV₂ hε (hc w ρ σ) (hd w ρ σ) w ρ σ

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- The inner energy-first integral of `nestedF` is `outerF`. -/
theorem energyFirstIntegral_nestedF (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) :
    energyFirstIntegral (fun q => nestedF P O ![q, k]) = outerF P O k := by
  have hD := QED.TwoLoop.NestedVP.integrableD_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂
    hε k
  simp only [nestedF, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun ρ _ =>
    QED.TwoLoop.NestedVP.IntegrableD.finsetSum _ fun σ _ => (hD ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun σ _ => (hD ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂ hε]
  rfl

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **Nested equals joint with the inner loop in closed form**, for an outer factor with
continuous entries decaying like `(1 + |t|)⁻¹⁰` along `k = (t, w)`. -/
theorem jointEnergyFirstIntegral_nestedF (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hc : ∀ w ρ σ, Continuous fun t => O (Fin.cons t w) ρ σ)
    (hd : ∀ w ρ σ, DecaysLike (fun t => O (Fin.cons t w) ρ σ) 10)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 (nestedF P O)) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (nestedF P O) = energyFirstIntegral (outerF P O) ∧
      EFInt (outerF P O) := by
  have hG := integrable_nestedF_time hm hM₁ hM₂ hPV₁ hPV₂ hε O hc hd
  have he : (fun k => energyFirstIntegral fun q => nestedF P O ![q, k]) = outerF P O :=
    funext (energyFirstIntegral_nestedF hm hM₁ hM₂ hPV₁ hPV₂ hε O)
  refine ⟨?_, ?_⟩
  · rw [QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested _ hF (ae_of_all _ hG), he]
  · have h := efInt_of_joint _ hF hG
    rwa [he] at h

end QED.ChainProof.HCSide

end
