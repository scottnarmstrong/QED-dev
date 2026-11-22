/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestedAtPauli
public import QED.ChainProof.HCBB2ValueBB

/-!
# The engine limits of the Pauli-projected set (a) terms as one-loop Pauli functionals

Helper level for `QED.ChainProof.SetAPauli.SetANestedAt`. The Pauli numerator of every set (a)
limit is `(1/i)` times `setAPauliLim`, a combination of the engine limits
`SALimTerm.lim` of the Pauli-projected outer integrands `pauliTerm` of the spectral terms
(`QED.ChainProof.SetANestedAt.exists_pauliNum_setALim`). This file evaluates one such limit.

* `specLimit_pauliChain_const`: with `r` spectral factors of one mass `M` and one parameter
  `x ∈ (0, 1)`, the iterated engine limit is `pauliConst · (e²/8π²) ∫ sf^r kernG`, by
  `QED.ChainProof.HCBB2.powLimit_pauliChain_eq` and the absorption of each spectral mass
  (`QED.ChainProof.HCBB2.inv_mul_kernG_snoc`).
* `aestronglyMeasurable_w₀`, `ae_norm_w₀_le`: the limit weight of a good term is measurable and
  under the majorant of the weights.
* `specS τ K = ∫_Δ w₀ (A + ξ(1-ξ) K)^{-r}`: the spectral integral of a term at `K`.
* **`lim_pauliTerm_eq`**: for a good term, the engine limit is
  `pauliConst · (e²/8π²) ∫ kernG(j, (m_γ, Λ, m_γ, Λ)) · specS(K)` with `K = vpK`, the integrand
  being integrable (Fubini over the simplex and the Feynman square).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetANestedAt

open QED.OneLoop QED.Integration QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtGen
open QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPHalf QED.TwoLoop.VPHalfAtLimit
open QED.ChainProof.HCSide QED.ChainProof.HCBB2 QED.ChainProof.SetASpec
open QED.Integration.Feynman (simplexSet)

/-! ### The iterated engine limit with constant spectral factors -/

section Engine

variable {e m : ℝ} {p' p : Fin 4 → ℝ} (hm : 0 < m) (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
  (hq : 0 < Minkowski.dot (p' - p) (p' - p))
  {α : ℂ} (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
include hm hp' hp hp0' hp0 hq hα

/-- **The iterated engine limit of the Pauli-projected chain** with `r` spectral factors of mass
`M > 0` and parameter `x ∈ (0, 1)`: `pauliConst · (e²/8π²) ∫ sf^r kernG`. -/
theorem specLimit_pauliChain_const (j : ℕ) {M x : ℝ} (hM : 0 < M) (hx : x ∈ Ioo (0 : ℝ) 1)
    (r : ℕ) : ∀ {k : ℕ} (Ms : Fin (k + 2) → ℝ), j ≤ k → (∀ i, 0 < Ms i) →
      specLimit α (pauliChain e m p' p) m p' p j r Ms (fun _ => M) (fun _ => x) =
        pauliConst e m (Minkowski.dot (p' - p) (p' - p)) *
          ((e ^ 2 / (8 * π ^ 2) * ∫ z, sf m (Minkowski.dot (p' - p) (p' - p)) M x z ^ r *
            kernG m (Minkowski.dot (p' - p) (p' - p)) j Ms z ∂feynmanMeasure : ℝ) : ℂ) := by
  induction r with
  | zero =>
    intro k Ms hj hpos
    rw [specLimit_zero, powLimit_pauliChain_eq hm hp' hp hp0' hp0 hq hα j Ms hj hpos, valG]
    simp only [pow_zero, one_mul]
  | succ r ih =>
    intro k Ms hj hpos
    set s := Minkowski.dot (p' - p) (p' - p)
    rw [specLimit_succ]
    have h := ih (k := k + 1) (Fin.snoc Ms (specMu M x) : Fin (k + 1 + 2) → ℝ) (by omega)
      (snoc_pos hpos (specMu_pos hM hx))
    have e1 : (Fin.tail fun _ : Fin (r + 1) => M) = fun _ => M := rfl
    have e2 : (Fin.tail fun _ : Fin (r + 1) => x) = fun _ => x := rfl
    rw [e1, e2, h]
    have hI : ∫ z, sf m s M x z ^ (r + 1) * kernG m s j Ms z ∂feynmanMeasure =
        (x * (1 - x))⁻¹ * ∫ z, sf m s M x z ^ r *
          kernG m s j (Fin.snoc Ms (specMu M x) : Fin (k + 1 + 2) → ℝ) z ∂feynmanMeasure := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      have h' := inv_mul_kernG_snoc m s j (by omega : j ≤ k + 1) Ms M x z
      simp only
      rw [pow_succ]
      linear_combination (-(sf m s M x z ^ r)) * h'
    rw [hI]
    push_cast
    ring

end Engine

/-! ### The limit weight of a good term -/

section Weight

variable {n : ℕ} {w : ℝ → (Fin n → ℝ) → ℂ} {w₀ : (Fin n → ℝ) → ℂ} {h : (Fin n → ℝ) → ℝ}
  {ν : Measure (Fin n → ℝ)}

theorem tendsto_one_div_nhdsGT :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun k => show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity⟩

theorem one_div_mem_Ioc (k : ℕ) : 1 / ((k : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 :=
  ⟨by positivity, by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith⟩

theorem aestronglyMeasurable_w₀
    (hwm : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → AEStronglyMeasurable (w ε) ν)
    (hwl : ∀ᵐ x ∂ν, Tendsto (fun ε => w ε x) (𝓝[>] 0) (𝓝 (w₀ x))) :
    AEStronglyMeasurable w₀ ν :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => hwm _ (one_div_mem_Ioc k).1 (one_div_mem_Ioc k).2)
    (hwl.mono fun _ hx => hx.comp tendsto_one_div_nhdsGT)

theorem ae_norm_w₀_le
    (hwb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂ν, ‖w ε x‖ ≤ h x)
    (hwl : ∀ᵐ x ∂ν, Tendsto (fun ε => w ε x) (𝓝[>] 0) (𝓝 (w₀ x))) :
    ∀ᵐ x ∂ν, ‖w₀ x‖ ≤ h x := by
  have hall : ∀ᵐ x ∂ν, ∀ k : ℕ, ‖w (1 / ((k : ℝ) + 1)) x‖ ≤ h x :=
    ae_all_iff.2 fun k => hwb _ (one_div_mem_Ioc k).1 (one_div_mem_Ioc k).2
  filter_upwards [hall, hwl] with x hb hl
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hl.comp tendsto_one_div_nhdsGT)) hb

end Weight

/-! ### The spectral integral and the value of one term -/

/-- The spectral integral of a term at `K`: `∫_Δ w₀ (A + ξ(1-ξ) K)^{-r}`. -/
noncomputable def specS (τ : SAOuterTerm) (K : ℝ) : ℂ :=
  ∫ x in simplexSet τ.n, τ.w₀ x * (((τ.A x + τ.ξ x * (1 - τ.ξ x) * K) ^ τ.r : ℝ) : ℂ)⁻¹

theorem saMs4_pos {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) : ∀ i, 0 < saMs4 mγ Λ i := fun i => by
  fin_cases i <;> simp [saMs4, hmγ, hΛ]

theorem saMs4_ge (mγ Λ : ℝ) : ∀ i, min mγ Λ ≤ saMs4 mγ Λ i := fun i => by
  fin_cases i <;> simp [saMs4]

theorem measurable_sf_param {n : ℕ} {A ξ : (Fin n → ℝ) → ℝ} (hA : Measurable A)
    (hξ : Measurable ξ) (m s : ℝ) :
    Measurable fun q : (Fin n → ℝ) × (ℝ × ℝ) => sf m s (√(A q.1)) (ξ q.1) q.2 := by
  unfold sf kDen kC specMu
  have h1 : Measurable fun q : (Fin n → ℝ) × (ℝ × ℝ) => A q.1 := hA.comp measurable_fst
  have h2 : Measurable fun q : (Fin n → ℝ) × (ℝ × ℝ) => ξ q.1 := hξ.comp measurable_fst
  fun_prop

/-- **The engine limit of the Pauli-projected outer integrand of a good term**: integrable in
the Feynman parameters, and equal to `pauliConst · (e²/8π²) ∫ kernG(j) · specS(K)`. -/
theorem lim_pauliTerm_eq {e m : ℝ} {p' p : Fin 4 → ℝ} (hm : 0 < m)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {Mlo mγ Λ : ℝ} (hMlo : 0 < Mlo)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) {τ : SAOuterTerm} (hτ : τ.Good Mlo) :
    Integrable (fun z => ((kernG m (Minkowski.dot (p' - p) (p' - p)) τ.j (saMs4 mγ Λ) z : ℝ) :
        ℂ) * specS τ (vpK m (Minkowski.dot (p' - p) (p' - p)) z)) feynmanMeasure ∧
    (pauliTerm e m p' p τ).lim m (saMs4 mγ Λ) p' p =
      pauliConst e m (Minkowski.dot (p' - p) (p' - p)) * ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) *
        ∫ z, ((kernG m (Minkowski.dot (p' - p) (p' - p)) τ.j (saMs4 mγ Λ) z : ℝ) : ℂ) *
          specS τ (vpK m (Minkowski.dot (p' - p) (p' - p)) z) ∂feynmanMeasure := by
  obtain ⟨hj, hA, hξ, hAlo, hξ01, ⟨h, hh, hw⟩, hwl⟩ := id hτ
  have hj2 : τ.j ≤ 2 := by split_ifs at hj <;> omega
  set s := Minkowski.dot (p' - p) (p' - p) with hs
  set ν : Measure (Fin τ.n → ℝ) := volume.restrict (simplexSet τ.n) with hν
  have hw₀m : AEStronglyMeasurable τ.w₀ ν :=
    aestronglyMeasurable_w₀ (fun ε h0 h1 => (hw ε h0 h1).1) hwl
  have hw₀b : ∀ᵐ x ∂ν, ‖τ.w₀ x‖ ≤ h x := ae_norm_w₀_le (fun ε h0 h1 => (hw ε h0 h1).2) hwl
  have hα := Classical.choose_spec (pauliChain_quadratic e m p' p)
  set α := Classical.choose (pauliChain_quadratic e m p' p)
  have hA0 : ∀ x, 0 < τ.A x := fun x => (by positivity : (0 : ℝ) < Mlo ^ 2).trans_le (hAlo x)
  have hsqA : ∀ x, 0 < √(τ.A x) := fun x => Real.sqrt_pos.2 (hA0 x)
  have hMloA : ∀ x, Mlo ≤ √(τ.A x) := fun x =>
    (le_abs_self Mlo).trans (Real.abs_le_sqrt (hAlo x))
  set G : (Fin τ.n → ℝ) → ℝ × ℝ → ℝ := fun x z =>
    sf m s (√(τ.A x)) (τ.ξ x) z ^ τ.r * kernG m s τ.j (saMs4 mγ Λ) z with hG
  set M₀ := min mγ Λ
  have hM₀ : 0 < M₀ := lt_min hmγ hΛ
  set B : ℝ := (1 / Mlo ^ 2) ^ τ.r * (2 / (M₀ ^ 2) ^ (2 + 1 - τ.j))
  -- the integrand on the product is integrable
  have hGm : Measurable fun q : (Fin τ.n → ℝ) × (ℝ × ℝ) => G q.1 q.2 := by
    have h1 := measurable_sf_param hA hξ m s
    have h2 : Measurable fun q : (Fin τ.n → ℝ) × (ℝ × ℝ) => kernG m s τ.j (saMs4 mγ Λ) q.2 :=
      (measurable_kernG m s τ.j (saMs4 mγ Λ)).comp measurable_snd
    exact (h1.pow_const τ.r).mul h2
  have hFi : Integrable (fun q : (Fin τ.n → ℝ) × (ℝ × ℝ) => τ.w₀ q.1 * ((G q.1 q.2 : ℝ) : ℂ))
      (ν.prod feynmanMeasure) := by
    have hint : Integrable h ν := hh
    refine Integrable.mono' (hint.mul_prod (integrable_const B)) ?_ ?_
    · exact hw₀m.comp_fst.mul (Complex.measurable_ofReal.comp hGm).aestronglyMeasurable
    have e1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := feynmanMeasure)).ae hw₀b
    have e2 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := feynmanMeasure)).ae hξ01
    have e3 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := feynmanMeasure)).ae
      QED.OneLoop.VertexLimit.ae_feynmanMeasure
    filter_upwards [e1, e2, e3] with q hb hx hz
    have s0 := sf_nonneg (M := √(τ.A q.1)) hm hq.le hz hx
    have s1 := sf_le hm hq.le hz hx (hsqA q.1)
    have s2 : 1 / √(τ.A q.1) ^ 2 ≤ 1 / Mlo ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hMlo.le (hMloA q.1) 2)
    have k0 := kernG_nonneg hm hq.le hz τ.j (saMs4 mγ Λ)
    have k1 := kernG_le hm hq.le hz hM₀ τ.j (by omega) (saMs4_ge mγ Λ)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg s0 _) k0)]
    exact mul_le_mul hb (mul_le_mul (pow_le_pow_left₀ s0 (s1.trans s2) _) k1 k0
      (by positivity)) (by positivity) ((norm_nonneg _).trans hb)
  -- the pointwise value in the Feynman parameters
  have hpt : ∀ᵐ z ∂feynmanMeasure, ∫ x, τ.w₀ x * ((G x z : ℝ) : ℂ) ∂ν =
      ((kernG m s τ.j (saMs4 mγ Λ) z : ℝ) : ℂ) * specS τ (vpK m s z) := by
    filter_upwards [QED.TwoLoop.VPHalf.ae_feynmanMeasure_ne_one] with z ⟨hz, hz1⟩
    rw [specS, ← integral_const_mul]
    refine integral_congr_ae (hξ01.mono fun x hx => ?_)
    have hsf := sf_eq hm hq.le hz hz1 hx (hsqA x)
    rw [Real.sq_sqrt (hA0 x).le] at hsf
    simp only [hG, hsf, one_div, inv_pow]
    push_cast
    ring
  refine ⟨(hFi.integral_prod_right).congr hpt, ?_⟩
  -- the limit
  have hlim : (pauliTerm e m p' p τ).lim m (saMs4 mγ Λ) p' p =
      ∫ x, τ.w₀ x * specLimit α (pauliChain e m p' p) m p' p τ.j τ.r (saMs4 mγ Λ)
        (fun _ => √(τ.A x)) (fun _ => τ.ξ x) ∂ν := rfl
  have hval : ∀ᵐ x ∂ν, τ.w₀ x * specLimit α (pauliChain e m p' p) m p' p τ.j τ.r (saMs4 mγ Λ)
      (fun _ => √(τ.A x)) (fun _ => τ.ξ x) = pauliConst e m s * ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) *
        ∫ z, τ.w₀ x * ((G x z : ℝ) : ℂ) ∂feynmanMeasure := by
    filter_upwards [hξ01] with x hx
    rw [specLimit_pauliChain_const hm hp' hp hp0' hp0 hq hα τ.j (hsqA x) hx τ.r (saMs4 mγ Λ)
      hj2 (saMs4_pos hmγ hΛ), integral_const_mul, integral_complex_ofReal]
    push_cast
    ring
  rw [hlim, integral_congr_ae hval, integral_const_mul, integral_integral_swap hFi,
    integral_congr_ae hpt]
