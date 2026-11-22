/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEProd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop self-energy building blocks: the limit of vanishing prescriptions

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S4 of the plan, second half
(the limit). Below threshold (`c₀ ≤ y m² + (1 - y) M₀² + y (1 - y) P²` on `[0, 1]`) and for
photon masses `≥ M₀ ≥ 0`, the closed-form energy integral `seSpatial` of the building block
`sePow` (`QED/ChainProof/SetCRegDispShellSEPow.lean`) converges, when all prescriptions tend to
`0⁺`, by dominated convergence with the uniform bound `exists_norm_seTime_le`:

* `tendsto_integral_seSpatial`: `∫ seSpatial(ε, η, M) → ∫ seSpatial(0, 0, M_*)` (also continuous
  in the photon mass);
* `tendsto_efi_sePow`: the same for the energy-first integral of `sePow`;
* `efi_seProd_eq`, **`tendsto_efi_seProd`**: the photon product `seProd` tends to `seProdLim`,
  `(k + 1)! ∫_Δ ∫ seSpatial(0, 0, M(u))`, which does not depend on the prescriptions;
* `tendsto_efi_of_eq_sub`, `seL1`, `seL2`, `seL3`: factors `k²` absorbed into a photon
  denominator (`QED.ChainProof.SetCRegDispSE.seProd_mul_s`) in the limit.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDispSE

open QED.OneLoop QED.Integration QED.Integration.Feynman QED.WickModel
open QED.WickModel.SelfEnergyLimit
open QED.TwoLoop.VPUnitNested (EFInt)
open QED.TwoLoop.VPHalfAtLimit (energyConst tendsto_cpow_neg_add_mul_I_of mixMass mixEps
  mixMass_ge mixEps_ge exists_pos_le_all continuous_mixEps_eps continuous_mixMass_masses
  massShift)

/-! ### The spatial integrand -/

theorem seEff_nonneg {ε η y : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ seEff ε η y := by
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  exact add_nonneg (mul_nonneg hy.1 hε) (mul_nonneg hy1 hη)

theorem continuous_massW_mass_se (m : ℝ) (P : Fin 4 → ℝ) (y : ℝ) (v : Fin 3 → ℝ) :
    Continuous fun M => massW m M P y v := by
  unfold massW selfEnergyFeynmanMass
  fun_prop

theorem seMassW_pos_of_le {m M c₀ : ℝ} (hc₀ : 0 < c₀) {P : Fin 4 → ℝ} {y : ℝ}
    (h : c₀ ≤ selfEnergyFeynmanMass m M (Minkowski.dot P P) y) (v : Fin 3 → ℝ) :
    0 < massW m M P y v := by
  unfold massW
  have : 0 ≤ ∑ k : Fin 3, (v k + y * P k.succ) ^ 2 := by positivity
  linarith

/-- Joint measurability of the closed form in `((M, v), y)`, the photon mass varying. -/
theorem measurable_seTime {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ) (m : ℝ)
    (n : ℕ) (ε η : ℝ) (P : Fin 4 → ℝ) :
    Measurable fun q : (ℝ × (Fin 3 → ℝ)) × ℝ =>
      seWt n q.2 * seTime α N m q.1.1 n (seEff ε η q.2) P q.2 q.1.2 := by
  have hW : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × ℝ => massW m q.1.1 P q.2 q.1.2 := by
    refine Continuous.measurable ?_
    simp only [massW, selfEnergyFeynmanMass, Fin.sum_univ_three]
    fun_prop
  have hc : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × ℝ =>
      (Fin.cons (-(q.2 * P 0)) q.1.2 : Fin 4 → ℝ) :=
    (Continuous.finCons (A := fun _ : Fin 4 => ℝ) (continuous_snd.mul continuous_const).neg
      continuous_fst.snd).measurable
  have hN : Measurable N := hNc.measurable
  have hf' : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × ℝ => seWt n q.2 :=
    ((continuous_seWt n).comp continuous_snd).measurable
  unfold seTime seEff
  fun_prop

theorem aestronglyMeasurable_seSpatial {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ)
    (m M : ℝ) (n : ℕ) (ε η : ℝ) (P : Fin 4 → ℝ) :
    AEStronglyMeasurable (seSpatial α N m M n ε η P) volume := by
  have h : Measurable fun q : (Fin 3 → ℝ) × ℝ =>
      seWt n q.2 * seTime α N m M n (seEff ε η q.2) P q.2 q.1 :=
    (measurable_seTime hNc α m n ε η P).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact (h.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).aestronglyMeasurable

theorem stronglyMeasurable_integral_seSpatial_mix {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N)
    (α : ℂ) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε η : ℝ) (P : Fin 4 → ℝ) :
    StronglyMeasurable fun u : Fin (k + 1) → ℝ =>
      ∫ v, seSpatial α N m (mixMass Ms u) (k + 1) ε η P v := by
  have hf : Measurable fun q : ((Fin (k + 1) → ℝ) × (Fin 3 → ℝ)) × ℝ =>
      seWt (k + 1) q.2 * seTime α N m (mixMass Ms q.1.1) (k + 1) (seEff ε η q.2) P q.2 q.1.2 :=
    (measurable_seTime hNc α m (k + 1) ε η P).comp
      ((((QED.TwoLoop.VPHalfAtLimit.continuous_mixMass Ms).comp continuous_fst.fst).prodMk
        continuous_fst.snd).measurable.prodMk measurable_snd)
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).integral_prod_right'

/-- The bound on `∫ seSpatial`. -/
theorem norm_integral_seSpatial_le {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M : ℝ} {n : ℕ} {ε η : ℝ}
    {P : Fin 4 → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖seTime α N m M n (seEff ε η y) P y v‖ ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ))) :
    ‖∫ v, seSpatial α N m M n ε η P v‖ ≤
      ∫ v : Fin 3 → ℝ, (n + 1) * C * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun v => norm_seSpatial_le hC v)
  have h := integrable_one_add_norm_four.const_mul ((n + 1) * C)
  simpa only [mul_assoc] using h

/-! ### The limit of the spatial integral -/

section Limit

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
  {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ} {n d : ℕ} {CN : ℝ}
  (hNd : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ d) (hd : d + 1 ≤ 2 * n) (hα : α = 0 ∨ 2 ≤ n)

include hM₀ hc₀ hP hNc hNd hd hα in
/-- **Convergence of the spatial integral**: along any countably generated filter on which
`ε, η → 0` with `ε, η ≥ 0` and `M → M_*` with `M ≥ M₀`, `∫ seSpatial(ε, η, M)` tends to
`∫ seSpatial(0, 0, M_*)`. -/
theorem tendsto_integral_seSpatial {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [l.NeBot] {ε η M : ι → ℝ} {Ms : ℝ} (hε : Tendsto ε l (𝓝 0)) (hη : Tendsto η l (𝓝 0))
    (hε0 : ∀ᶠ i in l, 0 ≤ ε i) (hη0 : ∀ᶠ i in l, 0 ≤ η i) (hM : Tendsto M l (𝓝 Ms))
    (hMge : ∀ᶠ i in l, M₀ ≤ M i) :
    Tendsto (fun i => ∫ v, seSpatial α N m (M i) n (ε i) (η i) P v) l
      (𝓝 (∫ v, seSpatial α N m Ms n 0 0 P v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_seTime_le hM₀ hc₀ hP α hNd hd hα
  have hMs : M₀ ≤ Ms := ge_of_tendsto hM hMge
  have hbnd := integrable_one_add_norm_four.const_mul ((n + 1) * C)
  have hae : ∀ᵐ y ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)), y ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun y hy => Ioc_subset_Icc_self hy
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hpt : ∀ v : Fin 3 → ℝ, Tendsto (fun i => seSpatial α N m (M i) n (ε i) (η i) P v) l
      (𝓝 (seSpatial α N m Ms n 0 0 P v)) := by
    intro v
    simp only [seSpatial]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ((n : ℝ) + 1) * C)
      ?_ ?_ (integrable_const _) ?_
    · refine Eventually.of_forall fun i => ?_
      have hc : Measurable fun y : ℝ => (((M i, v), y) : (ℝ × (Fin 3 → ℝ)) × ℝ) :=
        measurable_const.prodMk measurable_id
      exact ((measurable_seTime hNc α m n (ε i) (η i) P).comp hc).aestronglyMeasurable
    · filter_upwards [hMge] with i hi
      refine hae.mono fun y hy => ?_
      have hu : (1 + ‖v‖) ^ (-(4 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
      rw [norm_mul]
      calc ‖seWt n y‖ * ‖seTime α N m (M i) n (seEff (ε i) (η i) y) P y v‖
          ≤ (n + 1) * (C * 1) :=
            mul_le_mul (seWt_norm_le hy) ((hC (M i) hi _ y hy v).trans
              (mul_le_mul_of_nonneg_left hu hC0)) (norm_nonneg _) (by positivity)
        _ = (n + 1) * C := by ring
    · refine hae.mono fun y hy => ?_
      have hD : c₀ ≤ selfEnergyFeynmanMass m Ms (Minkowski.dot P P) y :=
        (hP y hy).trans (selfEnergyFeynmanMass_mono hM₀ hMs hy)
      have hW₀ := seMassW_pos_of_le hc₀ hD v
      have hWt : Tendsto (fun i => massW m (M i) P y v) l (𝓝 (massW m Ms P y v)) :=
        ((continuous_massW_mass_se m P y v).tendsto Ms).comp hM
      have he : Tendsto (fun i => seEff (ε i) (η i) y) l (𝓝 0) := by
        have := (hε.const_mul y).add (hη.const_mul (1 - y))
        simpa [seEff] using this
      have he0 : ∀ᶠ i in l, 0 ≤ seEff (ε i) (η i) y := by
        filter_upwards [hε0, hη0] with i h1 h2
        exact seEff_nonneg h1 h2 hy
      have l1 := tendsto_cpow_neg_add_mul_I_of hW₀ hWt he he0 (-(((n : ℝ) + 1 / 2 : ℝ) : ℂ))
      have l2 := tendsto_cpow_neg_add_mul_I_of hW₀ hWt he he0 (-(((n : ℝ) + 3 / 2 : ℝ) : ℂ))
      have h0 : seTime α N m Ms n (seEff 0 0 y) P y v =
          (-1) ^ (n + 2) * (α * ((energyConst (n + 1) - energyConst (n + 2) : ℝ) : ℂ) *
              (-(massW m Ms P y v : ℂ)) ^ (-(((n : ℝ) + 1 / 2 : ℝ) : ℂ)) +
            N (Fin.cons (-(y * P 0)) v : Fin 4 → ℝ) * (energyConst (n + 2) : ℂ) *
              (-(massW m Ms P y v : ℂ)) ^ (-(((n : ℝ) + 3 / 2 : ℝ) : ℂ))) := by
        simp [seTime, seEff]
      rw [h0]
      unfold seTime
      exact (((l1.const_mul _).add (l2.const_mul _)).const_mul _).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbnd
    (Eventually.of_forall hpt)
  · exact Eventually.of_forall fun i => aestronglyMeasurable_seSpatial hNc α m (M i) n _ _ P
  · filter_upwards [hMge] with i hi
    exact Eventually.of_forall fun v => norm_seSpatial_le
      (fun y hy v => hC (M i) hi _ y hy v) v

end Limit

/-- The energy-first integral of the building block is the integral of `seSpatial`. -/
theorem energyFirstIntegral_sePow_eq {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (P : Fin 4 → ℝ) :
    energyFirstIntegral (sePow N m M n ε η P) = ∫ v, seSpatial α N m M n ε η P v := by
  unfold energyFirstIntegral
  simp_rw [integral_time_sePow hNc hNq hNb m M n hε hη P]

section Prod

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
  {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
  (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
  {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {d : ℕ} {CN' : ℝ}
  (hNd : ∀ ℓ, ‖N ℓ‖ ≤ CN' * (1 + ‖ℓ‖) ^ d)

include hM₀ hc₀ hP hNc hNq hNb hNd in
/-- **The limit of the building block**: along any countably generated filter on which
`ε, η → 0⁺` and `M → M_*` with `M ≥ M₀`, the energy-first integral of `sePow` tends to
`∫ seSpatial(0, 0, M_*)`. -/
theorem tendsto_efi_sePow {n : ℕ} (hd : d + 1 ≤ 2 * n) (hα : α = 0 ∨ 2 ≤ n)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε η M : ι → ℝ} {Ms : ℝ}
    (hε : Tendsto ε l (𝓝[>] 0)) (hη : Tendsto η l (𝓝[>] 0)) (hM : Tendsto M l (𝓝 Ms))
    (hMge : ∀ᶠ i in l, M₀ ≤ M i) :
    Tendsto (fun i => energyFirstIntegral (sePow N m (M i) n (ε i) (η i) P)) l
      (𝓝 (∫ v, seSpatial α N m Ms n 0 0 P v)) := by
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε self_mem_nhdsWithin
  have hηpos : ∀ᶠ i in l, 0 < η i := hη self_mem_nhdsWithin
  have hlim := tendsto_integral_seSpatial hM₀ hc₀ hP hNc hNd hd hα
    (hε.mono_right nhdsWithin_le_nhds) (hη.mono_right nhdsWithin_le_nhds)
    (hεpos.mono fun _ h => h.le) (hηpos.mono fun _ h => h.le) hM hMge
  refine hlim.congr' ?_
  filter_upwards [hεpos, hηpos] with i h1 h2
  exact (energyFirstIntegral_sePow_eq hNc hNq hNb m (M i) n h1 h2 P).symm

include hM₀ hc₀ hP hNc hNq hNb hNd in
/-- Space × simplex integrability of the energy integral of the mixed building block. -/
theorem integrable_seMix_space {k : ℕ} (hd : d ≤ 2 * k + 1) (hα : α = 0 ∨ 1 ≤ k)
    {Ms es : Fin (k + 2) → ℝ} (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun x : (Fin 3 → ℝ) × (Fin (k + 1) → ℝ) =>
        ∫ t : ℝ, seMix N m Ms es ε P (x, t))
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (simplexSet (k + 1)))) := by
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  obtain ⟨C, _, hC⟩ := exists_norm_seTime_le hM₀ hc₀ hP α hNd (n := k + 1) (by omega)
    (by rcases hα with h | h; exacts [Or.inl h, Or.inr (by omega)])
  have hFm : StronglyMeasurable (seMix N m Ms es ε P) :=
    (measurable_sePow_mix hNc m Ms es ε P).stronglyMeasurable
  have hGm : StronglyMeasurable fun x : (Fin 3 → ℝ) × (Fin (k + 1) → ℝ) =>
      ∫ t : ℝ, seMix N m Ms es ε P (x, t) :=
    hFm.integral_prod_right'
  have hb := integrable_one_add_norm_four.const_mul (((k + 1 : ℕ) + 1) * C)
  refine Integrable.mono' (hb.mul_prod (integrable_const (1 : ℝ))) hGm.aestronglyMeasurable ?_
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
    (ν := volume.restrict (simplexSet (k + 1)))).ae
    (ae_restrict_mem (measurableSet_simplexSet (k + 1)))
  filter_upwards [h2] with x hx
  rw [mul_one]
  have hs : ∫ t : ℝ, seMix N m Ms es ε P (x, t) =
      seSpatial α N m (mixMass Ms x.2) (k + 1) ε (mixEps es x.2) P x.1 :=
    integral_time_sePow hNc hNq hNb m (mixMass Ms x.2) (k + 1) (η := mixEps es x.2) hε
      (he₀.trans_le (mixEps_ge hes₀ hx)) P x.1
  rw [hs]
  exact norm_seSpatial_le (fun y hy v => hC (mixMass Ms x.2) (mixMass_ge hM₀ hMs hx) _ y hy v)
    x.1

include hM₀ hc₀ hP hNc hNq hNb hNd in
/-- **The photon superposition commutes with the energy-first integral.** -/
theorem efi_seProd_eq {k : ℕ} (hd : d ≤ 2 * k + 1) (hα : α = 0 ∨ 1 ≤ k)
    {Ms es : Fin (k + 2) → ℝ} (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ}
    (hε : 0 < ε) :
    energyFirstIntegral (seProd N m Ms es ε P) = ((k + 1).factorial : ℂ) *
      ∫ u in simplexSet (k + 1),
        energyFirstIntegral (sePow N m (mixMass Ms u) (k + 1) ε (mixEps es u) P) := by
  have hint2 := integrable_seMix_space hM₀ hc₀ hP hNc hNq hNb hNd hd hα hMs hes hε
  rw [energyFirstIntegral]
  simp_rw [integral_time_seProd hNc hNb m Ms hes hε P]
  rw [integral_const_mul, integral_integral_swap hint2]
  rfl

/-- The limit of the photon product: `(k + 1)! ∫_Δ ∫ seSpatial(0, 0, M(u))`. -/
noncomputable def seProdLim (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  ((k + 1).factorial : ℂ) *
    ∫ u in simplexSet (k + 1), ∫ v, seSpatial α N m (mixMass Ms u) (k + 1) 0 0 P v

include hM₀ hc₀ hP hNc hNq hNb hNd in
/-- **The limit of the photon product**: when `ε → 0⁺` and every photon prescription
`ε_j → 0⁺`, the energy-first integral of `seProd` tends to `seProdLim`. -/
theorem tendsto_efi_seProd {k : ℕ} (hd : d ≤ 2 * k + 1) (hα : α = 0 ∨ 1 ≤ k)
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ j, M₀ ≤ Ms j) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ} {es : ι → Fin (k + 2) → ℝ}
    (hε : Tendsto ε l (𝓝[>] 0)) (hes : ∀ j, Tendsto (fun i => es i j) l (𝓝[>] 0)) :
    Tendsto (fun i => energyFirstIntegral (seProd N m Ms (es i) (ε i) P)) l
      (𝓝 (seProdLim α N m Ms P)) := by
  have hd' : d + 1 ≤ 2 * (k + 1) := by omega
  have hα' : α = 0 ∨ 2 ≤ k + 1 := by
    rcases hα with h | h; exacts [Or.inl h, Or.inr (by omega)]
  obtain ⟨C, hC0, hC⟩ := exists_norm_seTime_le hM₀ hc₀ hP α hNd hd' hα'
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε self_mem_nhdsWithin
  have hespos : ∀ᶠ i in l, ∀ j, 0 < es i j :=
    eventually_all.2 fun j => (hes j) self_mem_nhdsWithin
  set Δ := simplexSet (k + 1)
  set B : ℝ := ∫ v : Fin 3 → ℝ, (((k + 1 : ℕ) : ℝ) + 1) * C * (1 + ‖v‖) ^ (-(4 : ℝ))
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  have hes0 : Tendsto es l (𝓝 0) :=
    tendsto_pi_nhds.2 fun j => (hes j).mono_right nhdsWithin_le_nhds
  have hlim : Tendsto (fun i => ∫ u in Δ,
      energyFirstIntegral (sePow N m (mixMass Ms u) (k + 1) (ε i) (mixEps (es i) u) P))
      l (𝓝 (∫ u in Δ, ∫ v, seSpatial α N m (mixMass Ms u) (k + 1) 0 0 P v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
      (integrable_const B) ?_
    · refine Eventually.of_forall fun i => ?_
      have h := ((measurable_sePow_mix hNc m Ms (es i) (ε i) P).stronglyMeasurable
        |>.integral_prod_right' (ν := (volume : Measure ℝ))).integral_prod_left'
          (μ := (volume : Measure (Fin 3 → ℝ)))
      exact h.aestronglyMeasurable
    · filter_upwards [hεpos, hespos] with i h1 h2
      obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all h2
      filter_upwards [hΔ] with u hu
      rw [energyFirstIntegral_sePow_eq hNc hNq hNb m _ _ h1
        (he₀.trans_le (mixEps_ge hes₀ hu)) P]
      exact norm_integral_seSpatial_le
        (fun y hy v => hC (mixMass Ms u) (mixMass_ge hM₀ hMs hu) _ y hy v)
    · filter_upwards [hΔ] with u hu
      have hη : Tendsto (fun i => mixEps (es i) u) l (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := ((continuous_mixEps_eps u).tendsto 0).comp hes0
          simpa [mixEps, Function.comp_def] using this
        · filter_upwards [hespos] with i h2
          obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all h2
          exact he₀.trans_le (mixEps_ge hes₀ hu)
      exact tendsto_efi_sePow hM₀ hc₀ hP hNc hNq hNb hNd hd' hα' hε hη tendsto_const_nhds
        (Eventually.of_forall fun _ => mixMass_ge hM₀ hMs hu)
  refine (hlim.const_mul ((k + 1).factorial : ℂ)).congr' ?_
  filter_upwards [hεpos, hespos] with i h1 h2
  exact (efi_seProd_eq hM₀ hc₀ hP hNc hNq hNb hNd hd hα hMs h2 h1).symm

end Prod

/-! ### Absorbing factors `k²` in the limit -/

theorem energyFirstIntegral_sub_of_efInt {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F)
    (hG : EFInt G) :
    energyFirstIntegral (fun ℓ => F ℓ - G ℓ) = energyFirstIntegral F - energyFirstIntegral G := by
  unfold energyFirstIntegral
  have e : (fun v : Fin 3 → ℝ => ∫ t : ℝ, (F (Fin.cons t v : Fin 4 → ℝ) -
      G (Fin.cons t v : Fin 4 → ℝ))) = fun v => (∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)) -
        ∫ t : ℝ, G (Fin.cons t v : Fin 4 → ℝ) :=
    funext fun v => integral_sub (hF.1 v) (hG.1 v)
  rw [e, integral_sub hF.2 hG.2]

theorem efi_const_mul_se (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    energyFirstIntegral (fun ℓ => c * F ℓ) = c * energyFirstIntegral F := by
  unfold energyFirstIntegral
  simp_rw [integral_const_mul]

/-- **The limit of a difference**: if `X_i = Y_i - c_i Z_i` pointwise with `Y_i`, `Z_i`
integrable in both stages, `efi Y_i → a`, `efi Z_i → b` and `c_i → c`, then `efi X_i → a - c b`. -/
theorem tendsto_efi_of_eq_sub {ι : Type*} {l : Filter ι} {X Y Z : ι → (Fin 4 → ℝ) → ℂ}
    {c : ι → ℂ} {a b c₀ : ℂ} (hX : ∀ᶠ i in l, ∀ ℓ, X i ℓ = Y i ℓ - c i * Z i ℓ)
    (hY : ∀ᶠ i in l, EFInt (Y i)) (hZ : ∀ᶠ i in l, EFInt (Z i))
    (ha : Tendsto (fun i => energyFirstIntegral (Y i)) l (𝓝 a))
    (hb : Tendsto (fun i => energyFirstIntegral (Z i)) l (𝓝 b)) (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun i => energyFirstIntegral (X i)) l (𝓝 (a - c₀ * b)) := by
  refine (ha.sub (hc.mul hb)).congr' ?_
  filter_upwards [hX, hY, hZ] with i h1 h2 h3
  have e : X i = fun ℓ => Y i ℓ - c i * Z i ℓ := funext h1
  rw [e, energyFirstIntegral_sub_of_efInt h2 (h3.const_mul (c i)),
    efi_const_mul_se]

/-- The limit of `k² seProd`. -/
noncomputable def seL1 (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 3) → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  seProdLim α N m (Fin.tail Ms) P - ((Ms 0 ^ 2 : ℝ) : ℂ) * seProdLim α N m Ms P

/-- The limit of `(k²)² seProd`. -/
noncomputable def seL2 (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 4) → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  seL1 α N m (Fin.tail Ms) P - ((Ms 0 ^ 2 : ℝ) : ℂ) * seL1 α N m Ms P

/-- The limit of `(k²)³ seProd`. -/
noncomputable def seL3 (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 5) → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  seL2 α N m (Fin.tail Ms) P - ((Ms 0 ^ 2 : ℝ) : ℂ) * seL2 α N m Ms P

end QED.ChainProof.SetCRegDispSE

end
