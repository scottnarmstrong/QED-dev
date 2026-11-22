/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestedAtVal

/-!
# Regularity of the set (a) photon function

Helper level for `QED.ChainProof.SetAPauli.SetAPhotonReg`. The photon function
`QED.ChainProof.SetANestedAt.setAR P₀` is measurable, continuous on `(0, ∞)` and bounded on
`[0, ∞)` at every regulator set (`m < M₁, M₂`, `0 < m_γ < Λ`).

If no admissible `(c₁, c₂, D)` carries a transverse form factor, `setAPol = 0` and `setAR = 0`.
Otherwise the chosen form factor `Pol` lives at admissible data, where `Π⁽⁴⁾_ε` has the
`ε`-uniform spectral form `T★ᵤ` (`QED.ChainProof.SetANestedAt.regFlavors_spec`, a list `L` of
good terms), and `K Pol(K) = piG L K` for `K > 0` (`piG_eq_of_tendsto`). So on `(0, ∞)`
`setAR(K) = Re piG(K) · D(K)²`, which is continuous (`continuousOn_specS`) and bounded
(`norm_specS_le` and `Kʲ D(K)² ≤ m_γ^{-2(2-j)}` for `j ≤ 2`, `pow_mul_photonD_sq_le`).

* **`setAPhotonReg`**: `SetAPhotonReg P₀ (setAR P₀)` for `m > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetANestedAt

open QED.TwoLoop.UnitVPLink QED.ChainProof.SetASpec QED.ChainProof.SetAPauli

/-! ### The photon factor -/

theorem photonD_le {mγ Λ t : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (ht : 0 ≤ t) :
    photonD mγ Λ t ≤ 1 / (t + mγ ^ 2) := by
  unfold photonD
  have : 0 ≤ 1 / (t + Λ ^ 2) := by
    have : 0 < Λ := hmγ.trans hmΛ
    positivity
  linarith

/-- `Kʲ D(K)² ≤ m_γ^{-2(2-j)}` for `K ≥ 0`, `j ≤ 2`. -/
theorem pow_mul_photonD_sq_le {mγ Λ t : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (ht : 0 ≤ t) {j : ℕ}
    (hj : j ≤ 2) : t ^ j * photonD mγ Λ t ^ 2 ≤ (1 / mγ ^ 2) ^ (2 - j) := by
  set a := t + mγ ^ 2
  have hm2 : 0 < mγ ^ 2 := by positivity
  have ha : 0 < a := by positivity
  have hta : t ≤ a := by linarith
  have hia : 1 / a ≤ 1 / mγ ^ 2 := one_div_le_one_div_of_le hm2 (by linarith)
  have hD := pow_le_pow_left₀ (QED.ChainProof.HCValue.photonD_nonneg hmγ hmΛ.le ht)
    (photonD_le hmγ hmΛ ht) 2
  have hia0 : 0 ≤ 1 / a := by positivity
  refine (mul_le_mul_of_nonneg_left hD (pow_nonneg ht j)).trans ?_
  interval_cases j
  · simpa using pow_le_pow_left₀ hia0 hia 2
  · have : t * (1 / a) ^ 2 ≤ 1 / a := by
      rw [sq, ← mul_assoc]
      refine mul_le_of_le_one_left hia0 ?_
      rw [mul_one_div, div_le_one ha]
      exact hta
    simpa using this.trans hia
  · have : t * (1 / a) ≤ 1 := by
      rw [mul_one_div, div_le_one ha]
      exact hta
    have h0 : 0 ≤ t * (1 / a) := mul_nonneg ht hia0
    have h2 := pow_le_one₀ (n := 2) h0 this
    rw [mul_pow] at h2
    simpa using h2

theorem continuousOn_photonD {mγ Λ : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ < Λ) :
    ContinuousOn (photonD mγ Λ) (Ioi 0) := by
  have hΛ : 0 < Λ := hmγ.trans hmΛ
  unfold photonD
  refine ContinuousOn.sub (continuousOn_const.div (by fun_prop) fun t ht => ?_)
    (continuousOn_const.div (by fun_prop) fun t ht => ?_)
  · have : (0 : ℝ) < t := ht
    positivity
  · have : (0 : ℝ) < t := ht
    positivity

/-! ### The `g` part on `(0, ∞)` -/

theorem continuousOn_list_sum' {ι : Type*} (L : List ι) {F : ι → ℝ → ℂ} {s : Set ℝ}
    (h : ∀ q ∈ L, ContinuousOn (F q) s) :
    ContinuousOn (fun t => (L.map fun q => F q t).sum) s := by
  induction L with
  | nil => simpa using continuousOn_const
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h q (List.mem_cons_self ..)).add (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem continuousOn_piG {Mlo : ℝ} (hMlo : 0 < Mlo) {L : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ L, q.2.Good Mlo) : ContinuousOn (piG L) (Ici 0) := by
  unfold piG
  refine continuousOn_list_sum' L fun q hq => ?_
  refine continuousOn_const.mul ((continuousOn_const.mul ?_).mul
    (continuousOn_specS hMlo (hL q hq)))
  exact (Complex.continuous_ofReal.comp (continuous_pow q.2.j)).continuousOn

theorem exists_norm_piG_mul_le {Mlo mγ Λ : ℝ} (hMlo : 0 < Mlo) (hmγ : 0 < mγ) (hmΛ : mγ < Λ) :
    ∀ L : List (ℂ × SAOuterTerm), (∀ q ∈ L, q.2.Good Mlo) →
      ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖piG L t‖ * photonD mγ Λ t ^ 2 ≤ C := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨0, fun t _ => by simp [piG]⟩
  | cons q L ih =>
    intro hL
    obtain ⟨C, hC⟩ := ih fun r hr => hL r (List.mem_cons_of_mem _ hr)
    have hq := hL q (List.mem_cons_self ..)
    obtain ⟨Cq, hCq⟩ := norm_specS_le hMlo hq
    have hj : q.2.j ≤ 2 := by have := hq.1; split_ifs at this <;> omega
    refine ⟨‖q.1‖ * (Cq * (1 / mγ ^ 2) ^ (2 - q.2.j)) + C, fun t ht => ?_⟩
    have hpiG : piG (q :: L) t = q.1 * ((if q.2.t then 0 else 1) * ((t ^ q.2.j : ℝ) : ℂ) *
        specS q.2 t) + piG L t := by
      simp only [piG, List.map_cons, List.sum_cons]
    have hif : ‖(if q.2.t then (0 : ℂ) else 1)‖ ≤ 1 := by split_ifs <;> simp
    have hP := pow_mul_photonD_sq_le hmγ hmΛ ht hj
    have hD2 : 0 ≤ photonD mγ Λ t ^ 2 := sq_nonneg _
    have hS := hCq t ht
    have hC0 : 0 ≤ Cq := (norm_nonneg _).trans hS
    rw [hpiG]
    refine (mul_le_mul_of_nonneg_right (norm_add_le _ _) hD2).trans ?_
    rw [add_mul]
    refine add_le_add ?_ (hC t ht)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ht _)]
    calc ‖q.1‖ * (‖(if q.2.t then (0 : ℂ) else 1)‖ * t ^ q.2.j * ‖specS q.2 t‖) *
          photonD mγ Λ t ^ 2
        ≤ ‖q.1‖ * (1 * t ^ q.2.j * Cq) * photonD mγ Λ t ^ 2 := by gcongr
      _ = ‖q.1‖ * (Cq * (t ^ q.2.j * photonD mγ Λ t ^ 2)) := by ring
      _ ≤ ‖q.1‖ * (Cq * (1 / mγ ^ 2) ^ (2 - q.2.j)) := by gcongr

/-! ### Regularity -/

/-- The photon function on `(0, ∞)`. -/
noncomputable def setARpos (P₀ : Params) (mγ Λ M₁ M₂ : ℝ) (K : ℝ) : ℝ :=
  (setAPol P₀ mγ Λ M₁ M₂ K).re * K * photonD mγ Λ K ^ 2

theorem setARpos_reg {P₀ : Params} (hm : 0 < P₀.m) {M₁ M₂ mγ Λ : ℝ} (hmγ : 0 < mγ)
    (hmΛ : mγ < Λ) :
    ContinuousOn (setARpos P₀ mγ Λ M₁ M₂) (Ioi 0) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 < t → |setARpos P₀ mγ Λ M₁ M₂ t| ≤ C := by
  by_cases hex : ∃ Pol, SetAPolAt P₀ M₁ M₂ mγ Λ Pol
  · have hP : setAPol P₀ mγ Λ M₁ M₂ = hex.choose := by
      unfold setAPol
      simp only [hex, ↓reduceDIte]
    obtain ⟨c₁, c₂, D, hA, hPol⟩ := hex.choose_spec
    obtain ⟨L, hL, hVP⟩ := regFlavors_spec hm hA
    obtain ⟨-, -, -, -, -, hΛ, -, -, -⟩ := id hA
    set Mlo := min P₀.m (min mγ Λ)
    have hMlo : 0 < Mlo := lt_min hm (lt_min hmγ hΛ)
    have hg : ∀ t : ℝ, 0 < t → setARpos P₀ mγ Λ M₁ M₂ t = (piG L t).re * photonD mγ Λ t ^ 2 := by
      intro t ht
      have hk : -(4 * P₀.m ^ 2) < Minkowski.dot (spVec t) (spVec t) := by
        rw [dot_spVec ht.le]; nlinarith
      have hT : Tendsto (fun ε => saOuterTensor L ε (spVec t) 2 2) (𝓝[>] 0)
          (𝓝 (Classical.choose hex (Minkowski.dot (spVec t) (spVec t)) *
            ((Minkowski.dot (spVec t) (spVec t) * Minkowski.metric 2 2 -
              spVec t 2 * spVec t 2 : ℝ) : ℂ))) := by
        refine (hPol (spVec t) hk 2 2).congr' ?_
        filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
        exact hVP ε hε.1 hε.2 _ 2 2
      have h := piG_eq_of_tendsto hMlo hL ht.le hT
      rw [dot_spVec ht.le] at h
      rw [setARpos, hP, h, Complex.re_mul_ofReal]
    refine ⟨?_, ?_⟩
    · refine ContinuousOn.congr ?_ fun t ht => hg t ht
      refine ContinuousOn.mul ?_ ((continuousOn_photonD hmγ hmΛ).pow 2)
      exact Complex.continuous_re.comp_continuousOn
        ((continuousOn_piG hMlo hL).mono Ioi_subset_Ici_self)
    · obtain ⟨C, hC⟩ := exists_norm_piG_mul_le hMlo hmγ hmΛ L hL
      refine ⟨C, fun t ht => ?_⟩
      rw [hg t ht, abs_mul, abs_of_nonneg (sq_nonneg (photonD mγ Λ t))]
      exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (sq_nonneg _)).trans
        (hC t ht.le)
  · have hP : setAPol P₀ mγ Λ M₁ M₂ = 0 := by
      unfold setAPol
      simp only [hex, ↓reduceDIte]
    have h0 : setARpos P₀ mγ Λ M₁ M₂ = fun _ => 0 := by
      funext t
      simp [setARpos, hP]
    rw [h0]
    exact ⟨continuousOn_const, 0, fun t _ => by simp⟩

/-- **Regularity of the set (a) photon function**: `SetAPhotonReg P₀ (setAR P₀)`. -/
theorem setAPhotonReg {P₀ : Params} (hm : 0 < P₀.m) : SetAPhotonReg P₀ (setAR P₀) := by
  intro M₁ M₂ mγ Λ _ _ hmγ hmΛ
  obtain ⟨hc, C, hC⟩ := setARpos_reg (M₁ := M₁) (M₂ := M₂) hm hmγ hmΛ
  have hR : setAR P₀ mγ Λ M₁ M₂ = (Ioi (0 : ℝ)).piecewise (setARpos P₀ mγ Λ M₁ M₂) 0 := by
    funext t
    by_cases ht : 0 < t
    · simp [setAR, setARpos, Set.piecewise, ht]
    · simp [setAR, Set.piecewise, ht]
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]
    exact hc.measurable_piecewise continuousOn_const measurableSet_Ioi
  · refine hc.congr fun t ht => ?_
    simp [setAR, setARpos, show (0 : ℝ) < t from ht]
  · refine ⟨max C 0, fun t ht => ?_⟩
    rcases ht.lt_or_eq with ht | rfl
    · have : setAR P₀ mγ Λ M₁ M₂ t = setARpos P₀ mγ Λ M₁ M₂ t := by
        simp [setAR, setARpos, ht]
      rw [this]
      exact (hC t ht).trans (le_max_left _ _)
    · simp [setAR]
