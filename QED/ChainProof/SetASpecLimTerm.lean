/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecPow
public import QED.TwoLoop.VPHalfAtGenFubini
public import QED.TwoLoop.VPHalfAtGenAssembly
public import QED.TwoLoop.VPHalfAtLimitPhoton

/-!
# Set (a): the `ε → 0⁺` limit of one spectral term of the dressed outer vertex

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The fixed-`ε` spectral form of the two-loop vacuum polarization
(`QED.ChainProof.SetASpec.setASpec_vacuumPolarizationPart_two_spectral`) writes `Π⁽⁴⁾_ε(k)` as a
finite sum of terms `t(k) (k²)ʲ ∫_Δ w(x) fDen(√A(x), ε, ξ(x), k)^{-r}` with integrable weights.
Inserted in the outer one-loop vertex, each term gives the outer integrand
`∫_Δ w(x) specInt N m j Ms (ε, …, ε) (√A(x))^{×r} (ξ(x))^{×r} ε`
(`QED.TwoLoop.VPHalfAtGen.specInt`). This file passes to the limit `ε → 0⁺` in such a term,
for weights `w_ε` that may depend on `ε` (as the weights of the fixed-`ε` form do), converge
almost everywhere and have one integrable majorant for `ε ∈ (0, 1]`.

* `saLim_integrable_param`, **`saLim_efi_integral_eq`**: Fubini between the energy-first integral
  and an integral over parameters with an integrable weight (the generalization of
  `QED.TwoLoop.VPHalfAtGen.efi_integral_eq_of_good` from bounded to integrable weights).
* **`saLim_tendsto`**: dominated convergence in the parameters with integrable weights `w_i`
  converging almost everywhere.
* `saLim_measurable_specInt`: joint measurability of `specInt` when the masses and the Feynman
  parameters of the spectral factors are measurable functions of the parameter.
* **`saLim_tendsto_term`**: for `j ≤ k` and any `r`, at every `ε ∈ (0, 1]` the outer energy-first
  integral of the term is `∫_Δ w_ε · EFI(specInt …)`, and as `ε → 0⁺` it tends to
  `∫_Δ w₀ · specLimit α N m p' p j r Ms (√A) ξ`. The uniform bounds are
  `QED.ChainProof.SetASpec.setASpec_exists_good_specPow`, the pointwise limit is
  `QED.TwoLoop.VPHalfAtGen.tendsto_efi_specInt`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAtGen

/-! ### Fubini and dominated convergence with integrable weights -/

section Weighted

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **The two Fubini conditions with an integrable weight**: `w x · g x ℓ` for a jointly
measurable family `g` that is `Good` with one constant and one pointwise bound. -/
theorem saLim_integrable_param [IsFiniteMeasure ν] (w : X → ℂ) (hw : Integrable w ν)
    (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ᵐ x ∂ν, Good (g x) C G) :
    (∀ v : Fin 3 → ℝ, Integrable (fun q : ℝ × X => w q.2 * g q.2 (Fin.cons q.1 v : Fin 4 → ℝ))
      ((volume : Measure ℝ).prod ν)) ∧
    Integrable (fun q : (Fin 3 → ℝ) × X => ∫ t : ℝ, w q.2 * g q.2 (Fin.cons t q.1 : Fin 4 → ℝ))
      ((volume : Measure (Fin 3 → ℝ)).prod ν) := by
  constructor
  · intro v
    have hm : Measurable fun q : ℝ × X => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ) :=
      hgm.comp (by fun_prop : Measurable fun q : ℝ × X => (((v, q.2), q.1) :
        ((Fin 3 → ℝ) × X) × ℝ))
    have hws : AEStronglyMeasurable (fun q : ℝ × X => w q.2) ((volume : Measure ℝ).prod ν) :=
      hw.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    refine Integrable.mono' (g := fun q : ℝ × X => G v * (1 + q.1 ^ 2)⁻¹ * ‖w q.2‖)
      ((integrable_inv_one_add_sq.const_mul (G v)).mul_prod hw.norm)
      (hws.mul hm.aestronglyMeasurable) ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := ν)).ae hg
    filter_upwards [h2] with q hq
    rw [norm_mul, mul_comm ‖w q.2‖]
    exact mul_le_mul_of_nonneg_right (hq.2 v q.1) (norm_nonneg _)
  · have hm : StronglyMeasurable fun q : (Fin 3 → ℝ) × X =>
        ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ) :=
      hgm.stronglyMeasurable.integral_prod_right'
    have hws : AEStronglyMeasurable (fun q : (Fin 3 → ℝ) × X => w q.2)
        ((volume : Measure (Fin 3 → ℝ)).prod ν) :=
      hw.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have e : (fun q : (Fin 3 → ℝ) × X => ∫ t : ℝ, w q.2 * g q.2 (Fin.cons t q.1 : Fin 4 → ℝ)) =
        fun q => w q.2 * ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ) :=
      funext fun q => integral_const_mul _ _
    rw [e]
    refine Integrable.mono'
      (g := fun q : (Fin 3 → ℝ) × X => C * (1 + ‖q.1‖) ^ (-(5 : ℝ)) * ‖w q.2‖)
      ((integrable_one_add_norm_five.const_mul C).mul_prod hw.norm)
      (hws.mul hm.aestronglyMeasurable) ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := ν)).ae hg
    filter_upwards [h2] with q hq
    rw [norm_mul, mul_comm ‖w q.2‖]
    exact mul_le_mul_of_nonneg_right (hq.1.2 q.1) (norm_nonneg _)

/-- **The exchange with an integrable weight**: `∫_D ∫ w g dν = ∫ w (∫_D g) dν`, both stages
integrable. -/
theorem saLim_efi_integral_eq [IsFiniteMeasure ν] (w : X → ℂ) (hw : Integrable w ν)
    (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ᵐ x ∂ν, Good (g x) C G) :
    EFInt (fun ℓ => ∫ x, w x * g x ℓ ∂ν) ∧
      energyFirstIntegral (fun ℓ => ∫ x, w x * g x ℓ ∂ν) =
        ∫ x, w x * energyFirstIntegral (g x) ∂ν := by
  obtain ⟨h1, h2⟩ := saLim_integrable_param w hw g hgm hg
  obtain ⟨hE, he⟩ := efi_integral_swap (fun x ℓ => w x * g x ℓ) h1 h2
  refine ⟨hE, he.trans ?_⟩
  simp_rw [efi_const_mul]

/-- **Dominated convergence in the parameters with integrable weights.** -/
theorem saLim_tendsto [IsFiniteMeasure ν] {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (w : ι → X → ℂ) (w₀ : X → ℂ) (h : X → ℝ) (hh : Integrable h ν)
    (hwm : ∀ᶠ i in l, AEStronglyMeasurable (w i) ν)
    (hwb : ∀ᶠ i in l, ∀ᵐ x ∂ν, ‖w i x‖ ≤ h x)
    (hwl : ∀ᵐ x ∂ν, Tendsto (fun i => w i x) l (𝓝 (w₀ x)))
    (g : ι → X → (Fin 4 → ℝ) → ℂ) (F : X → ℂ) {C : ℝ}
    (hgm : ∀ᶠ i in l, Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ =>
      g i q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    (hg : ∀ᶠ i in l, ∃ G : (Fin 3 → ℝ) → ℝ, ∀ᵐ x ∂ν, Good (g i x) C G)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i => energyFirstIntegral (g i x)) l (𝓝 (F x))) :
    Tendsto (fun i => ∫ x, w i x * energyFirstIntegral (g i x) ∂ν) l
      (𝓝 (∫ x, w₀ x * F x ∂ν)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => h x * (C * I5)) ?_ ?_
    (hh.mul_const _) ?_
  · filter_upwards [hwm, hgm, hg] with i hw hm ⟨G, hG⟩
    exact hw.mul (aestronglyMeasurable_efi_param (g i) hm hG)
  · filter_upwards [hwb, hg] with i hb ⟨G, hG⟩
    filter_upwards [hb, hG] with x h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2.1.norm_efi_le (norm_nonneg _) ((norm_nonneg _).trans h1)
  · filter_upwards [hwl, hlim] with x h1 h2
    exact h1.mul h2

end Weighted

/-! ### Measurability -/

theorem saLim_measurable_comp_cons {X : Type*} [MeasurableSpace X] {g : X → (Fin 4 → ℝ) → ℂ}
    (hg : Measurable fun q : X × (Fin 4 → ℝ) => g q.1 q.2) :
    Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hc : Continuous fun r : (Fin 3 → ℝ) × ℝ => (Fin.cons r.2 r.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst
  have hℓ : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    hc.measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  exact hg.comp (measurable_fst.snd.prodMk hℓ)

/-- Joint measurability of `specInt` when the masses and Feynman parameters of the spectral
factors are measurable functions of the parameter. -/
theorem saLim_measurable_specInt {X : Type*} [MeasurableSpace X] {N : (Fin 4 → ℝ) → ℂ}
    (hNc : Continuous N) (m : ℝ) (j : ℕ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ) {r : ℕ}
    {Msp xs : X → Fin r → ℝ} (hMsp : ∀ i, Measurable fun x => Msp x i)
    (hxs : ∀ i, Measurable fun x => xs x i) (ε : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : X × (Fin 4 → ℝ) => specInt N m j Ms es (Msp q.1) (xs q.1) ε p' p q.2 := by
  have hs : Measurable fun q : X × (Fin 4 → ℝ) => Minkowski.dot q.2 q.2 :=
    (VertexLimit.continuous_dot_comp continuous_id continuous_id).measurable.comp measurable_snd
  have hc : ∀ {r : X × (Fin 4 → ℝ) → ℝ}, Measurable r → Measurable fun q => ((r q : ℝ) : ℂ) :=
    fun hr => Complex.measurable_ofReal.comp hr
  have hD : ∀ (M e : ℝ) (c : Fin 4 → ℝ), Measurable fun q : X × (Fin 4 → ℝ) =>
      denom M e (c + q.2) := fun M e c =>
    ((continuous_denom_joint continuous_const continuous_const
      (continuous_const.add continuous_id)).measurable.comp measurable_snd :)
  have hD0 : ∀ (M e : ℝ), Measurable fun q : X × (Fin 4 → ℝ) => denom M e q.2 := fun M e =>
    ((continuous_denom_joint continuous_const continuous_const continuous_id).measurable.comp
      measurable_snd :)
  unfold specInt powInt prodIntegrand
  refine (((hc hs).pow_const j).mul ((hNc.measurable.comp measurable_snd).mul
    (((hD m ε p').mul (hD m ε p)).inv.mul
      (Finset.measurable_prod _ fun i _ => (hD0 _ _).inv)))).mul
    (Finset.measurable_prod _ fun i _ => ?_)
  unfold fDen QED.WickModel.vacuumPolarizationFeynmanMass
  have hx : Measurable fun q : X × (Fin 4 → ℝ) => xs q.1 i := (hxs i).comp measurable_fst
  have hM : Measurable fun q : X × (Fin 4 → ℝ) => Msp q.1 i := (hMsp i).comp measurable_fst
  exact ((hc ((hM.pow_const 2).add ((hx.mul (measurable_const.sub hx)).mul hs))).sub
    measurable_const).inv

/-! ### One spectral term -/

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- The outer integrand of one spectral term at `ε`: the parameter integral of the weight times
`specInt` with `r` copies of the spectral factor of mass `√A(x)` and parameter `ξ(x)`, all
photon-type prescriptions equal to `ε`. -/
noncomputable def saLimTermInt (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (r : ℕ) {n : ℕ} (A ξ : (Fin n → ℝ) → ℝ)
    (w : (Fin n → ℝ) → ℂ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  ∫ x in simplexSet n, w x * specInt N m j Ms (fun _ => ε) (fun _ : Fin r => √(A x))
    (fun _ => ξ x) ε p' p ℓ

/-- The limit of one spectral term. -/
noncomputable def saLimTermLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ)
    (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (r : ℕ) {n : ℕ} (A ξ : (Fin n → ℝ) → ℝ)
    (w : (Fin n → ℝ) → ℂ) : ℂ :=
  ∫ x in simplexSet n, w x * specLimit α N m p' p j r Ms (fun _ : Fin r => √(A x))
    (fun _ => ξ x)

/-- **The limit of one spectral term of the dressed outer vertex.** For an outer numerator `N`
with the hypotheses of the engine, `j ≤ k`, any number `r` of spectral factors of mass
`√A(x) ≥ M_lo ≥ M₀` and parameter `ξ(x) ∈ (0, 1)` (almost everywhere), and weights `w_ε`
converging almost everywhere to `w₀` with an integrable majorant on `ε ∈ (0, 1]`:
* at every `ε ∈ (0, 1]` the term is integrable in both stages and its energy-first integral is
  `∫_Δ w_ε · EFI(specInt …)`;
* as `ε → 0⁺` its energy-first integral tends to `∫_Δ w₀ · specLimit α N m p' p j r Ms (√A) ξ`. -/
theorem saLim_tendsto_term (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Mlo : ℝ} (hMlo : M₀ ≤ Mlo)
    {j k : ℕ} (hjk : j ≤ k) (Ms : Fin (k + 2) → ℝ) (hMs : ∀ i, M₀ ≤ Ms i) (r : ℕ) {n : ℕ}
    {A ξ : (Fin n → ℝ) → ℝ} (hA : Measurable A) (hξ : Measurable ξ) (hAlo : ∀ x, Mlo ^ 2 ≤ A x)
    (hξ01 : ∀ᵐ x ∂(volume.restrict (simplexSet n)), ξ x ∈ Ioo (0 : ℝ) 1)
    (w : ℝ → (Fin n → ℝ) → ℂ) (w₀ : (Fin n → ℝ) → ℂ) (h : (Fin n → ℝ) → ℝ)
    (hh : IntegrableOn h (simplexSet n))
    (hwm : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      AEStronglyMeasurable (w ε) (volume.restrict (simplexSet n)))
    (hwb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (simplexSet n)), ‖w ε x‖ ≤ h x)
    (hwl : ∀ᵐ x ∂(volume.restrict (simplexSet n)),
      Tendsto (fun ε => w ε x) (𝓝[>] 0) (𝓝 (w₀ x))) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → EFInt (saLimTermInt N m j Ms r A ξ (w ε) ε p' p) ∧
      energyFirstIntegral (saLimTermInt N m j Ms r A ξ (w ε) ε p' p) =
        ∫ x in simplexSet n, w ε x * energyFirstIntegral (specInt N m j Ms (fun _ => ε)
          (fun _ : Fin r => √(A x)) (fun _ => ξ x) ε p' p)) ∧
    Tendsto (fun ε => energyFirstIntegral (saLimTermInt N m j Ms r A ξ (w ε) ε p' p))
      (𝓝[>] 0) (𝓝 (saLimTermLimit α N m p' p j Ms r A ξ w₀)) := by
  set ν : Measure (Fin n → ℝ) := volume.restrict (simplexSet n) with hν
  have hMlo0 : 0 ≤ Mlo := hM₀.le.trans hMlo
  have hsq : ∀ x, Mlo ≤ √(A x) := fun x =>
    (le_abs_self Mlo).trans (Real.abs_le_sqrt (hAlo x))
  obtain ⟨K, -, hK⟩ := setASpec_exists_good_specPow hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMlo
    r j k hjk
  set T : ℝ := ∑ i, Ms i ^ 2 + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  -- uniform `Good` bounds for `ε ∈ (0, 1]`
  have hgood : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ, ∀ᵐ x ∂ν,
      Good (specInt N m j Ms (fun _ => ε) (fun _ : Fin r => √(A x)) (fun _ => ξ x) ε p' p)
        ((1 + T) ^ j * K) G := by
    intro ε hε hε1
    obtain ⟨G, -, hG⟩ := hK ε ε hε hε le_rfl
    refine ⟨fun v => (1 + T) ^ j * G v, ?_⟩
    filter_upwards [hξ01] with x hx
    exact hG T hT0 Ms (fun _ => ε) hMs (fun _ => le_rfl)
      (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) (√(A x)) (ξ x) (hsq x) hx
  have hgm : ∀ ε : ℝ, Measurable fun q : ((Fin 3 → ℝ) × (Fin n → ℝ)) × ℝ =>
      specInt N m j Ms (fun _ => ε) (fun _ : Fin r => √(A q.1.2)) (fun _ => ξ q.1.2) ε p' p
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := fun ε =>
    saLim_measurable_comp_cons (g := fun x => specInt N m j Ms (fun _ => ε)
      (fun _ : Fin r => √(A x)) (fun _ => ξ x) ε p' p)
      (saLim_measurable_specInt hNc m j Ms (fun _ => ε) (Msp := fun x _ => √(A x))
        (xs := fun x _ => ξ x) (fun _ => hA.sqrt) (fun _ => hξ) ε p' p)
  have hfub : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → EFInt (saLimTermInt N m j Ms r A ξ (w ε) ε p' p) ∧
      energyFirstIntegral (saLimTermInt N m j Ms r A ξ (w ε) ε p' p) =
        ∫ x in simplexSet n, w ε x * energyFirstIntegral (specInt N m j Ms (fun _ => ε)
          (fun _ : Fin r => √(A x)) (fun _ => ξ x) ε p' p) := by
    intro ε hε hε1
    obtain ⟨G, hG⟩ := hgood ε hε hε1
    have hwi : Integrable (w ε) ν := Integrable.mono' hh (hwm ε hε hε1) (hwb ε hε hε1)
    exact saLim_efi_integral_eq (w ε) hwi _ (hgm ε) hG
  refine ⟨hfub, ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε using hε
  refine Tendsto.congr' (f₁ := fun ε => ∫ x in simplexSet n, w ε x *
    energyFirstIntegral (specInt N m j Ms (fun _ => ε) (fun _ : Fin r => √(A x))
      (fun _ => ξ x) ε p' p)) ?_ ?_
  · filter_upwards [hev] with ε hε
    exact (hfub ε hε.1 hε.2).2.symm
  refine saLim_tendsto (ν := ν) w w₀ h hh ?_ ?_ hwl
    (fun ε x => specInt N m j Ms (fun _ => ε) (fun _ : Fin r => √(A x)) (fun _ => ξ x) ε p' p)
    _ (C := (1 + T) ^ j * K) (Eventually.of_forall hgm) ?_ ?_
  · filter_upwards [hev] with ε hε using hwm ε hε.1 hε.2
  · filter_upwards [hev] with ε hε using hwb ε hε.1 hε.2
  · filter_upwards [hev] with ε hε using hgood ε hε.1 hε.2
  · filter_upwards [hξ01] with x hx
    exact tendsto_efi_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (l := 𝓝[>] (0 : ℝ))
      (ε := id) tendsto_id j r k hjk Ms (fun t _ => t) (fun _ => √(A x)) (fun _ => ξ x) hMs
      (fun _ => hMlo.trans (hsq x)) (fun _ => hx) (fun _ => tendsto_id)

end QED.ChainProof.SetASpec

end
