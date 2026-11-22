/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestedAtValEngine

/-!
# The `g` part of a list of spectral terms at spacelike momenta

Helper level for `QED.ChainProof.SetAPauli.SetANestedAt`. For a list `L` of good spectral terms
(the `T★ᵤ` list of `Π⁽⁴⁾_ε`), the photon function of the set (a) nested value is built from the
`g` part `piG L K = Σ_{g terms} c Kʲ specS(K)`. This file relates it to the transverse form factor:

* `norm_specS_integrand_le`, `integrable_specS_integrand`: for `K ≥ 0` the integrand of
  `specS` is bounded by the majorant of the weights times `M_lo^{-2r}`;
* `norm_specS_le`, `continuousOn_specS`: `specS` is bounded and continuous on `[0, ∞)`;
* `spVec K = (0, √K, 0, 0)`, with `spVec K · spVec K = K` for `K ≥ 0`;
* `tendsto_saOuterTensor_spVec`: at `k = spVec K` and the entry `(2, 2)` (where `g = 1` and
  `k k = 0`) the list tensor tends to `piG L K` as `ε → 0⁺`, by dominated convergence;
* **`piG_eq_of_tendsto`**: if that entry tends to `c (K g₂₂ - k₂ k₂) = c K`, then
  `piG L K = c K`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetANestedAt

open QED.TwoLoop.VPHalfAtAssembly QED.ChainProof.SetASpec
open QED.Integration.Feynman (simplexSet)

/-! ### Bounds and continuity of the spectral integral -/

section Spec

variable {Mlo : ℝ} {τ : SAOuterTerm}

theorem one_div_pow_re_le {A x K : ℝ} (hMlo : 0 < Mlo) (hA : Mlo ^ 2 ≤ A)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hK : 0 ≤ K) (r : ℕ) :
    ‖(((A + x * (1 - x) * K) ^ r : ℝ) : ℂ)⁻¹‖ ≤ (1 / Mlo ^ 2) ^ r := by
  have hx1 := mem_Ioo_mul_pos hx
  have h0 : Mlo ^ 2 ≤ A + x * (1 - x) * K := by nlinarith [mul_nonneg hx1.le hK]
  have hp : (0 : ℝ) < Mlo ^ 2 := by positivity
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_pow,
    abs_of_pos (hp.trans_le h0), ← inv_pow, one_div]
  exact pow_le_pow_left₀ (inv_pos.2 (hp.trans_le h0)).le (inv_anti₀ hp h0) r

theorem norm_specS_integrand_le (hMlo : 0 < Mlo) (hτ : τ.Good Mlo) :
    ∃ h : (Fin τ.n → ℝ) → ℝ, IntegrableOn h (simplexSet τ.n) ∧
      ∀ᵐ x ∂(volume.restrict (simplexSet τ.n)), ∀ K : ℝ, 0 ≤ K →
        ‖τ.w₀ x * (((τ.A x + τ.ξ x * (1 - τ.ξ x) * K) ^ τ.r : ℝ) : ℂ)⁻¹‖ ≤
          h x * (1 / Mlo ^ 2) ^ τ.r := by
  obtain ⟨-, -, -, hAlo, hξ01, ⟨h, hh, hw⟩, hwl⟩ := hτ
  refine ⟨h, hh, ?_⟩
  filter_upwards [ae_norm_w₀_le (fun ε h0 h1 => (hw ε h0 h1).2) hwl, hξ01] with x hb hx K hK
  rw [norm_mul]
  exact mul_le_mul hb (one_div_pow_re_le hMlo (hAlo x) hx hK τ.r) (norm_nonneg _)
    ((norm_nonneg _).trans hb)

theorem aestronglyMeasurable_specS_integrand (hτ : τ.Good Mlo) (K : ℝ) :
    AEStronglyMeasurable
      (fun x => τ.w₀ x * (((τ.A x + τ.ξ x * (1 - τ.ξ x) * K) ^ τ.r : ℝ) : ℂ)⁻¹)
      (volume.restrict (simplexSet τ.n)) := by
  obtain ⟨-, hA, hξ, -, -, ⟨h, -, hw⟩, hwl⟩ := hτ
  refine (aestronglyMeasurable_w₀ (fun ε h0 h1 => (hw ε h0 h1).1) hwl).mul ?_
  exact (Measurable.inv (Complex.measurable_ofReal.comp (by fun_prop))).aestronglyMeasurable

theorem norm_specS_le (hMlo : 0 < Mlo) (hτ : τ.Good Mlo) :
    ∃ C : ℝ, ∀ K : ℝ, 0 ≤ K → ‖specS τ K‖ ≤ C := by
  obtain ⟨h, hh, hb⟩ := norm_specS_integrand_le hMlo hτ
  refine ⟨∫ x in simplexSet τ.n, h x * (1 / Mlo ^ 2) ^ τ.r, fun K hK => ?_⟩
  exact norm_integral_le_of_norm_le (hh.mul_const _) (hb.mono fun x hx => hx K hK)

theorem continuousOn_specS (hMlo : 0 < Mlo) (hτ : τ.Good Mlo) :
    ContinuousOn (specS τ) (Ici 0) := by
  obtain ⟨h, hh, hb⟩ := norm_specS_integrand_le hMlo hτ
  have hξ01 := hτ.2.2.2.2.1
  refine continuousOn_of_dominated (fun K _ => aestronglyMeasurable_specS_integrand hτ K)
    (fun K hK => hb.mono fun x hx => hx K hK) (hh.mul_const _) ?_
  filter_upwards [hξ01] with x hx
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ ?_ fun K hK => ?_)
  · exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
  · have hx1 := mem_Ioo_mul_pos hx
    have hA : 0 < τ.A x := (by positivity : (0 : ℝ) < Mlo ^ 2).trans_le (hτ.2.2.2.1 x)
    have : 0 < τ.A x + τ.ξ x * (1 - τ.ξ x) * K := by
      have : 0 ≤ τ.ξ x * (1 - τ.ξ x) * K := mul_nonneg hx1.le hK
      linarith
    exact_mod_cast (pow_pos this τ.r).ne'

end Spec

/-! ### The `g` part and the spacelike limit -/

/-- The `g` part of a list of spectral terms at `K`: `Σ_{g terms} c Kʲ specS(K)`. -/
noncomputable def piG (L : List (ℂ × SAOuterTerm)) (K : ℝ) : ℂ :=
  (L.map fun q => q.1 * ((if q.2.t then 0 else 1) * ((K ^ q.2.j : ℝ) : ℂ) * specS q.2 K)).sum

/-- The spacelike vector `(0, √K, 0, 0)`. -/
noncomputable def spVec (K : ℝ) : Fin 4 → ℝ := ![0, √K, 0, 0]

theorem dot_spVec {K : ℝ} (hK : 0 ≤ K) : Minkowski.dot (spVec K) (spVec K) = K := by
  simp [Minkowski.dot_eq, spVec, Real.mul_self_sqrt hK]

theorem saTens_spVec (t : Bool) (K : ℝ) :
    saTens t (spVec K) 2 2 = if t then 0 else 1 := by
  cases t <;> simp [saTens, spVec, Minkowski.metric]

/-- **The spectral scalar at `k² = K ≥ 0` tends to `Kʲ specS(K)`** as `ε → 0⁺`. -/
theorem tendsto_saSpecScalar {Mlo : ℝ} (hMlo : 0 < Mlo) {τ : SAOuterTerm} (hτ : τ.Good Mlo)
    {k : Fin 4 → ℝ} {K : ℝ} (hK : 0 ≤ K) (hk : Minkowski.dot k k = K) :
    Tendsto (fun ε => saSpecScalar τ.j τ.r τ.A τ.ξ (τ.w ε) ε k) (𝓝[>] 0)
      (𝓝 (((K ^ τ.j : ℝ) : ℂ) * specS τ K)) := by
  obtain ⟨-, hA, hξ, hAlo, hξ01, ⟨h, hh, hw⟩, hwl⟩ := id hτ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε using hε
  unfold saSpecScalar
  rw [hk]
  push_cast
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun x => h x * (1 / Mlo ^ 2) ^ τ.r)
    ?_ ?_ (hh.mul_const _) ?_
  · filter_upwards [hev] with ε hε
    refine (hw ε hε.1 hε.2).1.mul (Measurable.aestronglyMeasurable ?_)
    unfold fDen QED.WickModel.vacuumPolarizationFeynmanMass
    fun_prop
  · filter_upwards [hev] with ε hε
    filter_upwards [(hw ε hε.1 hε.2).2, hξ01] with x hb hx
    rw [norm_mul]
    refine mul_le_mul hb ?_ (norm_nonneg _) ((norm_nonneg _).trans hb)
    have hx1 := mem_Ioo_mul_pos hx
    have hp : (0 : ℝ) < Mlo ^ 2 := by positivity
    have h0 : Mlo ^ 2 ≤ τ.A x + τ.ξ x * (1 - τ.ξ x) * K := by
      nlinarith [mul_nonneg hx1.le hK, hAlo x]
    have hre : (fDen (√(τ.A x)) ε (τ.ξ x) k).re = τ.A x + τ.ξ x * (1 - τ.ξ x) * K := by
      simp [fDen, QED.WickModel.vacuumPolarizationFeynmanMass, hk,
        Real.sq_sqrt (hp.le.trans (hAlo x))]
    have hn : Mlo ^ 2 ≤ ‖fDen (√(τ.A x)) ε (τ.ξ x) k‖ :=
      (hre ▸ h0).trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    rw [norm_inv, norm_pow, ← inv_pow, one_div]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hp hn) _
  · filter_upwards [hwl, hξ01] with x hl hx
    have hx1 := mem_Ioo_mul_pos hx
    have hA0 : 0 ≤ τ.A x := (by positivity : (0 : ℝ) ≤ Mlo ^ 2).trans (hAlo x)
    have hpos : 0 < τ.A x + τ.ξ x * (1 - τ.ξ x) * K := by
      have : 0 < Mlo ^ 2 := by positivity
      nlinarith [mul_nonneg hx1.le hK, hAlo x]
    have hc : Tendsto (fun ε : ℝ => fDen (√(τ.A x)) ε (τ.ξ x) k) (𝓝[>] 0)
        (𝓝 (((τ.A x + τ.ξ x * (1 - τ.ξ x) * K : ℝ) : ℂ))) := by
      have hct : Continuous fun ε : ℝ => fDen (√(τ.A x)) ε (τ.ξ x) k := by
        unfold fDen; fun_prop
      have h0 := (hct.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert h0 using 2
      simp [fDen, QED.WickModel.vacuumPolarizationFeynmanMass, hk, Real.sq_sqrt hA0]
    have hne : (((τ.A x + τ.ξ x * (1 - τ.ξ x) * K : ℝ) : ℂ)) ^ τ.r ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hpos.ne')
    have := hl.mul ((hc.pow τ.r).inv₀ hne)
    simpa only [Complex.ofReal_pow] using this

/-- **The `(2, 2)` entry of the list tensor at `spVec K` tends to `piG L K`.** -/
theorem tendsto_saOuterTensor_spVec {Mlo : ℝ} (hMlo : 0 < Mlo) {L : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ L, q.2.Good Mlo) {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun ε => saOuterTensor L ε (spVec K) 2 2) (𝓝[>] 0) (𝓝 (piG L K)) := by
  unfold saOuterTensor piG
  refine tendsto_list_sum' L fun q hq => ?_
  unfold SAOuterTerm.val
  rw [saTens_spVec]
  have := tendsto_saSpecScalar hMlo (hL q hq) hK (dot_spVec hK)
  have h2 := (this.const_mul (if q.2.t then (0 : ℂ) else 1)).const_mul q.1
  convert h2 using 2
  ring

/-- **The `g` part from the transverse limit**: if the `(2, 2)` entry at `spVec K` tends to
`c (K g₂₂ - k₂ k₂)`, then `piG L K = c K`. -/
theorem piG_eq_of_tendsto {Mlo : ℝ} (hMlo : 0 < Mlo) {L : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ L, q.2.Good Mlo) {K : ℝ} (hK : 0 ≤ K) {c : ℂ}
    (h : Tendsto (fun ε => saOuterTensor L ε (spVec K) 2 2) (𝓝[>] 0)
      (𝓝 (c * ((Minkowski.dot (spVec K) (spVec K) * Minkowski.metric 2 2 -
        spVec K 2 * spVec K 2 : ℝ) : ℂ)))) :
    piG L K = c * K := by
  rw [tendsto_nhds_unique (tendsto_saOuterTensor_spVec hMlo hL hK) h, dot_spVec hK]
  simp [spVec, Minkowski.metric]
