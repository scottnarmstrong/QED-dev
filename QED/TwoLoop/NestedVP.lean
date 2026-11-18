/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVPAmplitude
public import QED.TwoLoop.NestedVPFubini
public import QED.WickModel.VacuumPolarizationEnergyFirst
public import QED.WickModel.TwoPointClassification

/-!
# Nested equals joint for the vacuum-polarization class, at fixed `ε`

Obligation O2-8 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3) for the class `VP` of five gauge
vertices, at fixed `ε > 0`. The value (T₁₀) of the class is the joint energy-first integral (T₉)
over two loop momenta of its regulated amplitude. We prove that it equals the one-loop
energy-first integral (D) over the photon momentum `k` of an outer factor times the one-loop
vacuum polarization at `k`, regulated and flavour-summed, at the same `ε`:

`contractionValue₂ P VP = ∫_D dk ∑ ρ σ, vpOuter … k ρ σ * Π^{ρσ}_ε(k)`,
`Π^{ρσ}_ε(k) = ∫_D dq vacuumPolarizationIntegrand P P.ε k q ρ σ`.

By `QED.WickModel.onePIFunction_vacuumPolarization`, `Π^{ρσ}_ε(k)` is the frozen one-loop 1PI
two-photon function `onePIFunction P 0 2 2 … ![k, -k] … ![ρ, σ]` (X₂₈) with its counterterm tree
`-i δ₃ (k² g^{ρσ} - k^ρ k^σ)` removed (`contractionValue₂_VP_eq_onePIFunction`).

## Main statements

* `QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add`: integrability of both
  stages of (T₉) is invariant under integer unimodular affine changes of loop momenta.
* `QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested_energyFirst`: **nested equals joint**,
  under explicit hypotheses: momentum conservation, `ε > 0`, the mass and Pauli–Villars
  conditions (they give the integrability of the inner one-loop integral, packet 6b), the
  integrability of both stages of the joint prescription for the class (the content of O2-7 for
  `VP`, stated on the frozen integrand), and `hG`: for almost every spatial photon momentum, the
  inner energy integral is integrable jointly in the photon energy and the spatial loop momentum
  of the fermion loop.
* `QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_onePIFunction`: the same with the frozen
  one-loop two-photon function inserted.

## What is not proved here

The two integrability hypotheses. `hJ` is O2-7 for this class. `hG` asks, at fixed `v₂`, for
`∫ dt₂ |outer(k)| ∫ d³v₁ |∫ dt₁ Π-integrand| < ∞`. The inner absolute spatial integral is finite
for each `k` (packet 6b: the flavour-summed energy integral decays like `(1 + |v₁|)⁻⁵`), but the
packet-6b bound has a constant depending on `k` only through an existential, so the growth in the
photon energy `t₂` is not controlled; a quantitative version (polynomial growth in `k`, against
the `|t₂|⁻¹⁰` decay of the outer factor) would prove `hG`. Absolute integrability of the
integrand over the energy `t₁` together with the spatial `v₁` fails, even after the flavour sum,
by the following estimate (not a Lean theorem): near the mass shells the shifts between flavours
are of the same order `1/|v₁|` as the widths `ε/|v₁|`, so the absolute energy integral does not
decay in `v₁`. The proof therefore always
integrates `t₁` first, as both prescriptions do, and exchanges only `t₂` with `v₁`.
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.TwoLoop.NestedVP

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.JointIntegralInvariance

/-! ### Transport of integrability -/

/-- An affine map with linear part of determinant `±1` preserves an additive Haar measure and is a
measurable embedding. -/
theorem measurePreserving_linear_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] [μ.IsAddRightInvariant] (f : E →ₗ[ℝ] E) (hf : |LinearMap.det f| = 1)
    (b : E) : MeasurePreserving (fun x => f x + b) μ μ ∧ MeasurableEmbedding (fun x => f x + b) := by
  have h0 : LinearMap.det f ≠ 0 := by
    intro h
    rw [h, abs_zero] at hf
    exact zero_ne_one hf
  let e : E ≃L[ℝ] E := (f.equivOfDetNeZero h0).toContinuousLinearEquiv
  have he : (e : E → E) = f := rfl
  have hmp : MeasurePreserving e μ μ := by
    refine ⟨e.continuous.measurable, ?_⟩
    rw [he, Measure.map_linearMap_addHaar_eq_smul_addHaar μ h0, abs_inv, hf, inv_one,
      ENNReal.ofReal_one, one_smul]
  refine ⟨(measurePreserving_add_right μ b).comp hmp, ?_⟩
  exact (e.toHomeomorph.trans (Homeomorph.addRight b)).measurableEmbedding

/-- The action of an integer matrix plus a shift, on the loop momenta split into energies and
spatial components. -/
theorem matrix_add_joinMomenta {L : ℕ} (M : Matrix (Fin L) (Fin L) ℤ) (a : Fin L → Fin 4 → ℝ)
    (t : Fin L → ℝ) (v : Fin L → Fin 3 → ℝ) :
    (fun s => ∑ r, M s r • joinMomenta t v r) + a =
      joinMomenta (matrixAct ℝ M t + fun s => a s 0)
        (matrixAct (Fin 3 → ℝ) M v + fun s => Fin.tail (a s)) := by
  rw [← joinMomenta_add]
  congr 1
  funext s i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [joinMomenta, matrixAct_apply, Finset.sum_apply]

/-- **Integrability of both stages of the joint energy-first integral (T₉′) is invariant under
integer unimodular affine changes** `ℓ ↦ M ℓ + a` of the loop momenta (O2-6). -/
theorem jointEnergyFirstIntegrable_comp_matrix_add (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ)
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) (a : Fin L → Fin 4 → ℝ)
    (hF : jointEnergyFirstIntegrable L F) :
    jointEnergyFirstIntegrable L (fun ℓ => F ((fun s => ∑ r, M s r • ℓ r) + a)) := by
  have hdet := abs_intCast_det_eq_one hM
  obtain ⟨hα, hαe⟩ := measurePreserving_linear_add volume (matrixAct ℝ M)
    (by rw [det_matrixAct_real, hdet]) (fun s => a s 0)
  obtain ⟨hβ, hβe⟩ := measurePreserving_linear_add volume (matrixAct (Fin 3 → ℝ) M)
    (by rw [det_matrixAct_pi, abs_pow, hdet, one_pow]) (fun s => Fin.tail (a s))
  obtain ⟨hF₁, hF₂⟩ := hF
  change ∀ v, Integrable fun t => F (joinMomenta t v) at hF₁
  change Integrable fun v => ∫ t, F (joinMomenta t v) at hF₂
  refine ⟨fun v => ?_, ?_⟩
  · change Integrable fun t => F ((fun s => ∑ r, M s r • joinMomenta t v r) + a)
    simp only [matrix_add_joinMomenta]
    exact (hα.integrable_comp_emb hαe).mpr (hF₁ _)
  · change Integrable fun v => ∫ t, F ((fun s => ∑ r, M s r • joinMomenta t v r) + a)
    simp only [matrix_add_joinMomenta]
    have hin : ∀ v : Fin L → Fin 3 → ℝ,
        ∫ t, F (joinMomenta (matrixAct ℝ M t + fun s => a s 0)
          (matrixAct (Fin 3 → ℝ) M v + fun s => Fin.tail (a s))) =
        ∫ t, F (joinMomenta t (matrixAct (Fin 3 → ℝ) M v + fun s => Fin.tail (a s))) := fun v =>
      hα.integral_comp hαe (fun t => F (joinMomenta t
        (matrixAct (Fin 3 → ℝ) M v + fun s => Fin.tail (a s))))
    simp only [hin]
    exact (hβ.integrable_comp_emb hβe).mpr hF₂

/-! ### The nested integrand -/

/-- The integrand of the class `VP` in the nested routing, `q = ℓ 0` on the fermion loop and
`k = ℓ 1` on the photon line, in factorized form. -/
noncomputable def nestedIntegrand (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P p kext (ℓ 1) α β μ ρ σ *
    vacuumPolarizationIntegrand P P.ε (ℓ 1) (ℓ 0) ρ σ

/-- The inverse change of loop momenta `ℓ ↦ (p - ℓ 1, ℓ 0)`, integer unimodular. -/
def unswapMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

theorem isUnit_det_unswapMat : IsUnit unswapMat.det := by
  rw [Matrix.det_fin_two]
  simp [unswapMat]

theorem unswapMat_act (ℓ : Fin 2 → Fin 4 → ℝ) (p : Fin 4 → ℝ) :
    ((fun s => ∑ r, unswapMat s r • ℓ r) + ![p, 0]) 0 = p - ℓ 1 ∧
      ((fun s => ∑ r, unswapMat s r • ℓ r) + ![p, 0]) 1 = ℓ 0 := by
  simp [unswapMat, Fin.sum_univ_two, sub_eq_neg_add]

/-- The integrand of the value (T₁₀) of the class, in the frozen routing. -/
noncomputable def frozenIntegrand (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
    regulatedAmplitude₂ P Class5.VP.rep pIn kIn (lineMomentum₂ Class5.VP.rep pOut pIn kIn ℓ)
      αOut βIn μ

/-- The frozen integrand at the changed loop momenta is the nested integrand. -/
theorem frozenIntegrand_unswap (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    frozenIntegrand P pOut pIn kIn αOut βIn μ
        ((fun s => ∑ r, unswapMat s r • ℓ r) + ![pIn 0, 0]) =
      nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) ℓ := by
  obtain ⟨h0, h1⟩ := unswapMat_act ℓ (pIn 0)
  rw [frozenIntegrand, lineMomentum₂_cV hmom, h0, h1, sub_sub_cancel, integrand_eq]
  rfl

/-- **The joint integrability transported to the nested routing.** -/
theorem jointEnergyFirstIntegrable_nested (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hJ : jointEnergyFirstIntegrable 2 (frozenIntegrand P pOut pIn kIn αOut βIn μ)) :
    jointEnergyFirstIntegrable 2 (nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)) := by
  have h := jointEnergyFirstIntegrable_comp_matrix_add 2 _ unswapMat isUnit_det_unswapMat
    ![pIn 0, 0] hJ
  simp only [frozenIntegrand_unswap P hmom] at h
  exact h

/-! ### The inner integral -/

/-- Integrability in both stages of the energy-first integral (D). -/
def IntegrableD (F : (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v)

theorem IntegrableD.const_mul {F : (Fin 4 → ℝ) → ℂ} (hF : IntegrableD F) (c : ℂ) :
    IntegrableD fun ℓ => c * F ℓ :=
  ⟨fun v => (hF.1 v).const_mul c, by
    simp only [integral_const_mul]
    exact hF.2.const_mul c⟩

theorem IntegrableD.finsetSum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → ℂ}
    (hF : ∀ i ∈ s, IntegrableD (F i)) : IntegrableD fun ℓ => ∑ i ∈ s, F i ℓ := by
  have hinner : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, ∑ i ∈ s, F i (Fin.cons t v) =
      ∑ i ∈ s, ∫ t : ℝ, F i (Fin.cons t v) := fun v =>
    integral_finsetSum s fun i hi => (hF i hi).1 v
  refine ⟨fun v => integrable_finsetSum s fun i hi => (hF i hi).1 v, ?_⟩
  simp_rw [hinner]
  exact integrable_finsetSum s fun i hi => (hF i hi).2

/-- The energy-first integral (D) is additive on integrable integrands. -/
theorem energyFirstIntegral_finsetSum {ι : Type*} (s : Finset ι) (F : ι → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ i ∈ s, IntegrableD (F i)) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => ∑ i ∈ s, F i ℓ) =
      ∑ i ∈ s, QED.OneLoop.energyFirstIntegral (F i) := by
  unfold QED.OneLoop.energyFirstIntegral
  have hinner : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, ∑ i ∈ s, F i (Fin.cons t v) =
      ∑ i ∈ s, ∫ t : ℝ, F i (Fin.cons t v) := fun v =>
    integral_finsetSum s fun i hi => (hF i hi).1 v
  simp_rw [hinner]
  exact integral_finsetSum s fun i hi => (hF i hi).2

theorem energyFirstIntegral_const_mul (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => c * F ℓ) = c * QED.OneLoop.energyFirstIntegral F := by
  unfold QED.OneLoop.energyFirstIntegral
  simp only [integral_const_mul]

/-- The one-loop vacuum polarization integrand is integrable in both stages, for `ε > 0`, under
the mass and Pauli–Villars conditions (packet 6b). -/
theorem integrableD_vacuumPolarizationIntegrand {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε) (k : Fin 4 → ℝ)
    (ρ σ : Fin 4) : IntegrableD fun q => vacuumPolarizationIntegrand P P.ε k q ρ σ :=
  ⟨VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε P k ρ σ,
    VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂
      hε k ρ σ⟩

/-- The inner energy-first integral of the nested integrand is the outer factor times the
one-loop vacuum polarization, at each photon momentum `k`. -/
theorem energyFirstIntegral_nestedIntegrand {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ) :
    QED.OneLoop.energyFirstIntegral (fun q => nestedIntegrand P p kext α β μ ![q, k]) =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P p kext k α β μ ρ σ *
        QED.OneLoop.energyFirstIntegral fun q => vacuumPolarizationIntegrand P P.ε k q ρ σ := by
  have hD := integrableD_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε k
  simp only [nestedIntegrand, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [energyFirstIntegral_finsetSum _ _ fun ρ _ =>
    IntegrableD.finsetSum _ fun σ _ => (hD ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [energyFirstIntegral_finsetSum _ _ fun σ _ => (hD ρ σ).const_mul _]
  simp only [energyFirstIntegral_const_mul]

/-- The energy integral over `q⁰` of the nested integrand is the outer factor times the energy
integral of the one-loop vacuum polarization integrand, for `ε > 0`. -/
theorem integral_nestedIntegrand_time (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ)
    (α β μ : Fin 4) (k : Fin 4 → ℝ) (w₁ : Fin 3 → ℝ) :
    ∫ t₁ : ℝ, nestedIntegrand P p kext α β μ ![Fin.cons t₁ w₁, k] =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P p kext k α β μ ρ σ *
        ∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε k (Fin.cons t₁ w₁) ρ σ := by
  have hI := fun ρ σ =>
    VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε P k ρ σ w₁
  simp only [nestedIntegrand, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ => (hI ρ σ).const_mul _]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [integral_finsetSum _ fun σ _ => (hI ρ σ).const_mul _]
  simp only [integral_const_mul]

/-! ### Nested equals joint -/

/-- **Nested equals joint for the vacuum-polarization class** (O2-8, at fixed `ε > 0`). Under
momentum conservation, the mass and Pauli–Villars conditions, the integrability of both stages of
the joint prescription for the class (`hJ`, on the integrand of the value (T₁₀) in the frozen
routing) and the integrability `hG` of the inner energy integral in the photon energy and the
spatial loop momentum of the fermion loop, the value of the class is the energy-first integral
(D) over the photon momentum `k` of `∑ ρ σ, vpOuter … k ρ σ * Π^{ρσ}_ε(k)`, where `Π^{ρσ}_ε(k)` is the
energy-first integral (D) of the one-loop vacuum polarization integrand of (62.12), the
Pauli–Villars flavours summed inside it, at the same `ε`. -/
theorem contractionValue₂_VP_eq_nested_energyFirst (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (hJ : jointEnergyFirstIntegrable 2 (frozenIntegrand P pOut pIn kIn αOut βIn μ))
    (hG : ∀ᵐ w₂ : Fin 3 → ℝ, Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)
        ![Fin.cons t₁ x.2, Fin.cons x.1 w₂]) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          QED.OneLoop.energyFirstIntegral fun q => vacuumPolarizationIntegrand P P.ε k q ρ σ := by
  rw [contractionValue₂_VP_eq_nested P hmom]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cV pIn kIn (nestedMom (pIn 0) (kIn 0) (ℓ 0) (ℓ 1)) αOut βIn μ) =
      nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) := by
    funext ℓ
    rw [integrand_eq]
    rfl
  rw [e, jointEnergyFirstIntegral_eq_nested _ (jointEnergyFirstIntegrable_nested P hmom αOut βIn μ hJ)
    hG]
  simp only [energyFirstIntegral_nestedIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε]

/-- **Nested equals joint for the vacuum-polarization class**, with the Fubini hypothesis stated
on the outer factor times the energy integral of the one-loop vacuum polarization integrand: for
almost every spatial photon momentum `w₂`, the function
`(k⁰, q⃗) ↦ ∑ ρ σ, vpOuter … k ρ σ * ∫ dq⁰ Π-integrand(k, q)`, `k = (k⁰, w₂)`, is integrable. -/
theorem contractionValue₂_VP_eq_nested_energyFirst' (P : Params)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (hJ : jointEnergyFirstIntegrable 2 (frozenIntegrand P pOut pIn kIn αOut βIn μ))
    (hG : ∀ᵐ w₂ : Fin 3 → ℝ, Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∑ ρ : Fin 4, ∑ σ : Fin 4,
        vpOuter P (pIn 0) (kIn 0) (Fin.cons x.1 w₂) (αOut 0) (βIn 0) (μ 0) ρ σ *
          ∫ t₁ : ℝ, vacuumPolarizationIntegrand P P.ε (Fin.cons x.1 w₂) (Fin.cons t₁ x.2) ρ σ) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          QED.OneLoop.energyFirstIntegral fun q => vacuumPolarizationIntegrand P P.ε k q ρ σ := by
  refine contractionValue₂_VP_eq_nested_energyFirst P hmom αOut βIn μ hm hM₁ hM₂ hPV₁ hPV₂ hε hJ
    (hG.mono fun w₂ hw₂ => ?_)
  simp only [integral_nestedIntegrand_time P hε]
  exact hw₂

/-- **Nested equals joint, with the frozen one-loop vacuum polarization inserted**: as
`contractionValue₂_VP_eq_nested_energyFirst`, with `Π^{ρσ}_ε(k)` written as the frozen one-loop
1PI function with two external photons of momenta `k`, `-k` at order `≤ 2` (X₂₈), minus its
counterterm tree `-i δ₃ (k² g^{ρσ} - k^ρ k^σ)`. -/
theorem contractionValue₂_VP_eq_onePIFunction (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (hJ : jointEnergyFirstIntegrable 2 (frozenIntegrand P pOut pIn kIn αOut βIn μ))
    (hG : ∀ᵐ w₂ : Fin 3 → ℝ, Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)
        ![Fin.cons t₁ x.2, Fin.cons x.1 w₂]) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun k =>
        ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
          (onePIFunction P 0 2 2 ![] ![] ![k, -k] ![] ![] ![ρ, σ] +
            I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric ρ σ - k ρ * k σ) : ℝ) : ℂ)) := by
  rw [contractionValue₂_VP_eq_nested_energyFirst P hmom αOut βIn μ hm hM₁ hM₂ hPV₁ hPV₂ hε hJ hG]
  congr 1
  funext k
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [onePIFunction_vacuumPolarization]
  ring

end QED.TwoLoop.NestedVP

end
