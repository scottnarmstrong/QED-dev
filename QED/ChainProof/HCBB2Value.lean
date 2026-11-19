/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtGenAssembly
public import QED.TwoLoop.VPHalfAtAssemblyMatch
public import QED.ChainProof.HCSideDD

/-!
# The value of the engine limits for the Pauli-projected chain

Helper level, Phase 5 Stage 1a (O3-6 nested values for the classes of set (b)). The generic
engine `QED/TwoLoop/VPHalfAtGenPow.lean` gives the `ε → 0⁺` limit `powLimit j Ms` of
`(k²)ʲ N / (D_m(p'+k) D_m(p+k) ∏_{i<k+2} D_{M_i}(k))` as a simplex integral. For the
Pauli-projected Feynman-gauge chain `N = Pg = QED.TwoLoop.VPUnitNested.pauliChain` this file
identifies it with the outer one-loop Pauli functional of the photon function
`K ↦ Kʲ ∏_i (K + M_i²)⁻¹`:

* `kernG m s j Ms z = 2 y² (1-y) m² C^j (1-y)^{k+1-j} / ∏_i D_{M_i}` (`C = kC`, `D_M = kDen`), the
  common shape of `kern4`, `kern5`, `kernVP`, `kernD3`; `kernG_eq_photon`: on the open square it
  is `2 y² m² Kʲ ∏_i (K + M_i²)⁻¹` with `K = vpK m s z`.
* `kernG_nonneg`, `kernG_le`: `0 ≤ kernG ≤ 2/(M₀²)^{k+1-j}` for masses `≥ M₀ > 0`, `j ≤ k + 1`.
* `valG e m p' p j Ms = pauliConst e m q² · ((e²/8π²) ∫ kernG m q² j Ms)`.
* **`prodLimit_pauliChain_eq`**: `prodLimit = valG 0` for all positive masses: two masses from the
  frozen one-loop vertex (`QED.TwoLoop.VPUnitNested.tendsto_efi_pauliVI`), more masses by the
  partial fraction `(D₁ - D₀)/(D₀ D₁) = 1/D₀ - 1/D₁` at a common prescription and uniqueness of
  limits, repeated squared masses by continuity in the masses
  (`QED.TwoLoop.VPHalfAtLimit.tendsto_prodLimit` and dominated convergence).
* **`powLimit_pauliChain_eq`**: `powLimit j Ms = valG j Ms` for `j ≤ k`, by the absorption
  recursion of both sides.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.OneLoop QED.OneLoop.VertexLimit QED.WickModel QED.Integration
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAtGen QED.TwoLoop.VPHalf QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.HCSide

/-! ### The kernel -/

/-- `2 y² (1-y) m² C^j (1-y)^{k+1-j} / ∏_i D_{M_i}`. -/
noncomputable def kernG (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ j * (1 - z.2) ^ (k + 1 - j) /
    ∏ i, kDen m (Ms i) s z

/-- The value: the one-loop Pauli functional of `Kʲ ∏_i (K + M_i²)⁻¹`. -/
noncomputable def valG (e m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    ℂ :=
  pauliConst e m (Minkowski.dot (p' - p) (p' - p)) *
    ((e ^ 2 / (8 * π ^ 2) * ∫ z, kernG m (Minkowski.dot (p' - p) (p' - p)) j Ms z
      ∂feynmanMeasure : ℝ) : ℂ)

/-- The first mass dropped from the second slot: `(M₀, M₂, M₃, …)`. -/
def dropOne {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) : Fin (k + 2) → ℝ :=
  Fin.cons (Ms 0) (fun i : Fin (k + 1) => Ms i.succ.succ)

theorem measurable_kernG (m s : ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    Measurable (kernG m s j Ms) := by
  unfold kernG kDen kC
  refine Measurable.div (by fun_prop) (Finset.measurable_prod _ fun i _ => by fun_prop)

theorem kernG_photon_eq {m s : ℝ} (j : ℕ) {k : ℕ} (hj : j ≤ k + 1) (Ms : Fin (k + 2) → ℝ)
    {z : ℝ × ℝ} (h1 : 1 - z.2 ≠ 0) (hK : ∀ i, vpK m s z + Ms i ^ 2 ≠ 0) :
    kernG m s j Ms z = 2 * z.2 ^ 2 * m ^ 2 * vpK m s z ^ j * ∏ i, (vpK m s z + Ms i ^ 2)⁻¹ := by
  unfold kernG
  simp only [kDen_eq_vpK h1, kC_eq_vpK h1, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib]
  have hp : ∏ i, (vpK m s z + Ms i ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hK i
  have e : (1 - z.2) ^ (k + 2) = (1 - z.2) ^ j * (1 - z.2) ^ (k + 1 - j) * (1 - z.2) := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [e]
  field_simp
  rw [mul_pow]
  ring

/-! ### Bounds -/

section Bounds

variable {m s M₀ : ℝ} {z : ℝ × ℝ}

theorem kDen_ge (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hM₀ : 0 < M₀) {M : ℝ} (hM : M₀ ≤ M) :
    (1 - z.2) * M₀ ^ 2 + kC m s z ≤ kDen m M s z := by
  unfold kDen
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have : M₀ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM₀.le hM 2
  nlinarith

theorem kernG_nonneg (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
    (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) : 0 ≤ kernG m s j Ms z := by
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hC := (kC_pos' hm hs hz).le
  unfold kernG
  exact div_nonneg (by positivity)
    (Finset.prod_nonneg fun i _ => (kDen_pos (Ms i) hm hs hz).le)

/-- **The uniform bound** `kernG ≤ 2/(M₀²)^{k+1-j}`. -/
theorem kernG_le (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
    (hM₀ : 0 < M₀) (j : ℕ) {k : ℕ} (hj : j ≤ k + 1) {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, M₀ ≤ Ms i) : kernG m s j Ms z ≤ 2 / (M₀ ^ 2) ^ (k + 1 - j) := by
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hy1 : 1 - z.2 ≤ 1 := by linarith [hz.2.1]
  have hCp := kC_pos' hm hs hz
  have hCge : z.2 ^ 2 * m ^ 2 ≤ kC m s z :=
    kC_ge hs ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩
  set D₀ := (1 - z.2) * M₀ ^ 2 + kC m s z
  have hD₀ : 0 < D₀ := by positivity
  have hM2 : 0 < M₀ ^ 2 := by positivity
  set a := k + 1 - j
  have hprod : D₀ ^ (k + 2) ≤ ∏ i, kDen m (Ms i) s z := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin (k + 2) => D₀)
      (g := fun i => kDen m (Ms i) s z) (h0 := fun _ _ => hD₀.le)
      (h1 := fun i _ => kDen_ge hz hM₀ (hMs i))
    simpa using this
  have hN0 : 0 ≤ 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ j * (1 - z.2) ^ a := by positivity
  have hyD : 1 - z.2 ≤ D₀ / M₀ ^ 2 := by
    rw [le_div_iff₀ hM2]; simp only [D₀]; linarith
  have hN : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ j * (1 - z.2) ^ a ≤
      2 * D₀ ^ (k + 2) / (M₀ ^ 2) ^ a := by
    have e : D₀ ^ (k + 2) = D₀ * D₀ ^ j * D₀ ^ a := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [e, mul_div_assoc]
    have hCD : kC m s z ≤ D₀ := by simp only [D₀]; nlinarith
    calc 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ j * (1 - z.2) ^ a
        = 2 * (z.2 ^ 2 * m ^ 2) * (1 - z.2) * kC m s z ^ j * (1 - z.2) ^ a := by ring
      _ ≤ 2 * D₀ * 1 * D₀ ^ j * (D₀ / M₀ ^ 2) ^ a := by
          gcongr
          exact hCge.trans hCD
      _ = 2 * (D₀ * D₀ ^ j * D₀ ^ a / (M₀ ^ 2) ^ a) := by rw [div_pow]; ring
  unfold kernG
  calc 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ j * (1 - z.2) ^ a / ∏ i, kDen m (Ms i) s z
      ≤ 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ j * (1 - z.2) ^ a / D₀ ^ (k + 2) :=
        div_le_div_of_nonneg_left hN0 (by positivity) hprod
    _ ≤ 2 * D₀ ^ (k + 2) / (M₀ ^ 2) ^ a / D₀ ^ (k + 2) := by gcongr
    _ = 2 / (M₀ ^ 2) ^ a := by field_simp

theorem integrable_kernG (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) (j : ℕ) {k : ℕ}
    (hj : j ≤ k + 1) {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) :
    Integrable (kernG m s j Ms) feynmanMeasure := by
  refine Integrable.mono' (integrable_const (2 / (M₀ ^ 2) ^ (k + 1 - j)))
    (measurable_kernG m s j Ms).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (kernG_nonneg hm hs hz j Ms)]
  exact kernG_le hm hs hz hM₀ j hj hMs

end Bounds

/-! ### The recursions of the kernel -/

theorem kernG_succ (m s : ℝ) (j : ℕ) {k : ℕ} (hj : j ≤ k) (Ms : Fin (k + 1 + 2) → ℝ)
    {z : ℝ × ℝ} (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    kernG m s (j + 1) Ms z =
      kernG m s j (Fin.tail Ms) z - Ms 0 ^ 2 * kernG m s j Ms z := by
  unfold kernG
  rw [Fin.prod_univ_succ]
  simp only [Fin.tail]
  have hR : ∏ i : Fin (k + 2), kDen m (Ms i.succ) s z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => hD _
  have h0 := hD 0
  have e1 : k + 1 + 1 - (j + 1) = k + 1 - j := by omega
  have e2 : k + 1 + 1 - j = (k + 1 - j) + 1 := by omega
  rw [e1, e2, pow_succ]
  field_simp
  unfold kDen
  ring

theorem kernG_drop (m s : ℝ) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) {z : ℝ × ℝ}
    (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    (Ms 1 ^ 2 - Ms 0 ^ 2) * kernG m s 0 Ms z =
      kernG m s 0 (dropOne Ms) z - kernG m s 0 (Fin.tail Ms) z := by
  unfold kernG
  simp only [Fin.prod_univ_succ, dropOne, Fin.tail, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_zero_eq_one, pow_zero, mul_one, Nat.sub_zero]
  have hR : ∏ i : Fin k, kDen m (Ms i.succ.succ.succ) s z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => hD _
  have h0 := hD 0
  have h1 := hD 1
  have h2 := hD 2
  rw [pow_succ (1 - z.2) (k + 1)]
  field_simp
  unfold kDen
  ring

/-! ### The value: two masses -/

section Value

variable {e m : ℝ} {p' p : Fin 4 → ℝ}

theorem valG_def (e m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    valG e m p' p j Ms = pauliConst e m (Minkowski.dot (p' - p) (p' - p)) *
      ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) *
        ((∫ z, kernG m (Minkowski.dot (p' - p) (p' - p)) j Ms z ∂feynmanMeasure : ℝ) : ℂ) := by
  rw [valG]
  push_cast
  ring

theorem pauliIntegrand_eq_kernG (m a x s : ℝ) {z : ℝ × ℝ} (ha : kDen m a s z ≠ 0)
    (hx : kDen m x s z ≠ 0) :
    pauliIntegrand m (a, x, s) z = (x ^ 2 - a ^ 2) * kernG m s 0 ![a, x] z := by
  rw [pauliIntegrand_eq_kDen]
  unfold kernG
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pow_zero, mul_one, Nat.sub_zero]
  field_simp
  unfold kDen at *
  ring

/-- The value recursion of the partial fraction. -/
theorem valG_drop (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ)
    (hpos : ∀ i, 0 < Ms i) :
    ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) * valG e m p' p 0 Ms =
      valG e m p' p 0 (dropOne Ms) - valG e m p' p 0 (Fin.tail Ms) := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hD : ∀ i, M₀ ≤ dropOne Ms i := fun i => by
    cases i using Fin.cases with
    | zero => exact hMs 0
    | succ i => exact hMs _
  have hI : (Ms 1 ^ 2 - Ms 0 ^ 2) * ∫ z, kernG m q 0 Ms z ∂feynmanMeasure =
      (∫ z, kernG m q 0 (dropOne Ms) z ∂feynmanMeasure) -
        ∫ z, kernG m q 0 (Fin.tail Ms) z ∂feynmanMeasure := by
    rw [← integral_const_mul, ← integral_sub (integrable_kernG hm hq hM₀ 0 (by omega) hD)
      (integrable_kernG hm hq hM₀ 0 (by omega) (Ms := Fin.tail Ms) fun i => hMs _)]
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact kernG_drop m q Ms fun i => (kDen_pos _ hm hq hz).ne'
  have hI' := congrArg (fun x : ℝ => (x : ℂ)) hI
  push_cast at hI'
  rw [valG_def, valG_def, valG_def]
  generalize ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) = r
  push_cast
  linear_combination (pauliConst e m q * r) * hI'

/-- The value recursion of the absorption. -/
theorem valG_succ (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (j : ℕ) {k : ℕ} (hj : j ≤ k)
    (Ms : Fin (k + 1 + 2) → ℝ) (hpos : ∀ i, 0 < Ms i) :
    valG e m p' p (j + 1) Ms =
      valG e m p' p j (Fin.tail Ms) - ((Ms 0 ^ 2 : ℝ) : ℂ) * valG e m p' p j Ms := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hI : ∫ z, kernG m q (j + 1) Ms z ∂feynmanMeasure =
      (∫ z, kernG m q j (Fin.tail Ms) z ∂feynmanMeasure) -
        Ms 0 ^ 2 * ∫ z, kernG m q j Ms z ∂feynmanMeasure := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_kernG hm hq hM₀ j (by omega) (Ms := Fin.tail Ms) fun i => hMs _)
      ((integrable_kernG hm hq hM₀ j (by omega) hMs).const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact kernG_succ m q j hj Ms fun i => (kDen_pos _ hm hq hz).ne'
  have hI' := congrArg (fun x : ℝ => (x : ℂ)) hI
  push_cast at hI'
  rw [valG_def, valG_def, valG_def, hI']
  generalize ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) = r
  push_cast
  ring

/-- The perturbed masses `M_i + δ (i + 1)`. -/
def pert {k : ℕ} (Ms : Fin (k + 2) → ℝ) (δ : ℝ) : Fin (k + 2) → ℝ :=
  fun i => Ms i + δ * ((i : ℕ) + 1)

theorem tendsto_pert {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    Tendsto (pert Ms) (𝓝[>] 0) (𝓝 Ms) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  have h : Tendsto (fun δ : ℝ => Ms i + δ * ((i : ℕ) + 1)) (𝓝 0)
      (𝓝 (Ms i + 0 * ((i : ℕ) + 1))) :=
    tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem eventually_pert_inj {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hpos : ∀ i, 0 < Ms i) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∀ i, 0 < pert Ms δ i) ∧
      ∀ i l, i ≠ l → pert Ms δ i ^ 2 ≠ pert Ms δ l ^ 2 := by
  have hT := tendsto_pert Ms
  have hne : ∀ i l, i ≠ l → ∀ᶠ δ in 𝓝[>] (0 : ℝ), pert Ms δ i ≠ pert Ms δ l := by
    intro i l hil
    by_cases hM : Ms i = Ms l
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) h
      simp only [pert, hM, add_right_inj] at h
      have h2 := mul_left_cancel₀ hδ.ne' h
      have h3 : ((i : ℕ) : ℝ) = ((l : ℕ) : ℝ) := by linarith
      exact hil (Fin.ext (by exact_mod_cast h3))
    · have hc : Tendsto (fun δ => pert Ms δ i - pert Ms δ l) (𝓝[>] 0) (𝓝 (Ms i - Ms l)) :=
        (tendsto_pi_nhds.1 hT i).sub (tendsto_pi_nhds.1 hT l)
      filter_upwards [hc.eventually_ne (sub_ne_zero.2 hM)] with δ hδ h
      exact hδ (sub_eq_zero.2 h)
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i l, i ≠ l → pert Ms δ i ≠ pert Ms δ l := by
    refine eventually_all.2 fun i => eventually_all.2 fun l => ?_
    by_cases hil : i = l
    · exact Eventually.of_forall fun _ h => absurd hil h
    · filter_upwards [hne i l hil] with δ h _ using h
  filter_upwards [hall, self_mem_nhdsWithin] with δ h (hδ : 0 < δ)
  have hp : ∀ i, 0 < pert Ms δ i := fun i => by
    have := hpos i
    simp only [pert]
    positivity
  exact ⟨hp, fun i l hil hsq => h i l hil ((pow_left_inj₀ (hp i).le (hp l).le two_ne_zero).1 hsq)⟩

theorem continuousAt_kernG_zero {m s : ℝ} {k : ℕ} {z : ℝ × ℝ} {Ms : Fin (k + 2) → ℝ}
    (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    ContinuousAt (fun M : Fin (k + 2) → ℝ => kernG m s 0 M z) Ms := by
  unfold kernG
  refine ContinuousAt.div continuousAt_const ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hD i)
  refine (continuous_finsetProd _ fun i _ => ?_).continuousAt
  unfold kDen
  fun_prop

/-- **Continuity of the value in the masses.** -/
theorem tendsto_valG_pert (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hpos : ∀ i, 0 < Ms i) :
    Tendsto (fun δ => valG e m p' p 0 (pert Ms δ)) (𝓝[>] 0) (𝓝 (valG e m p' p 0 Ms)) := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hge : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, M₀ ≤ pert Ms δ i := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
    have : 0 ≤ δ * ((i : ℕ) + 1) := by positivity
    simp only [pert]
    linarith [hMs i]
  have hI : Tendsto (fun δ => ∫ z, kernG m q 0 (pert Ms δ) z ∂feynmanMeasure) (𝓝[>] 0)
      (𝓝 (∫ z, kernG m q 0 Ms z ∂feynmanMeasure)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 / (M₀ ^ 2) ^ (k + 1 - 0))
      (Eventually.of_forall fun δ => (measurable_kernG m q 0 _).aestronglyMeasurable) ?_
      (integrable_const _) ?_
    · filter_upwards [hge] with δ hδ
      filter_upwards [ae_feynmanMeasure] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (kernG_nonneg hm hq hz 0 _)]
      exact kernG_le hm hq hz hM₀ 0 (by omega) hδ
    · filter_upwards [ae_feynmanMeasure] with z hz
      exact (continuousAt_kernG_zero fun i => (kDen_pos _ hm hq hz).ne').tendsto.comp
        (tendsto_pert Ms)
  have h2 := ((Complex.continuous_ofReal.tendsto _).comp
    (hI.const_mul (e ^ 2 / (8 * π ^ 2)))).const_mul (pauliConst e m q)
  exact h2

variable (hm : 0 < m) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
  (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
  {α : ℂ} (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
include hm hp' hp hp0' hp0 hq hα

/-- **Two distinct masses**, from the frozen one-loop vertex. -/
theorem prodLimit_two {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hax : a ^ 2 ≠ x ^ 2) :
    prodLimit α (pauliChain e m p' p) m ![a, x] p' p = valG e m p' p 0 ![a, x] := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  set M₀ := min a x
  have hM₀ : 0 < M₀ := lt_min ha hx
  have hMs : ∀ i, M₀ ≤ (![a, x] : Fin (0 + 2) → ℝ) i := fun i => by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have T1 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0
    (continuous_pauliChain e m p' p) hα hCN hMs (l := 𝓝[>] (0 : ℝ)) (ε := id)
    (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  have T2 := tendsto_efi_pauliVI (e := e) hm ha hx hp' hp hp0' hp0
  have hc : ((x ^ 2 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 (Ne.symm hax)
  have T1' := T1.const_mul ((x ^ 2 - a ^ 2 : ℝ) : ℂ)
  have hev : (fun ε => energyFirstIntegral fun k =>
      pauliNum m p' p (fun μ => vertexIntegrand e m a x ε p' p μ k)) =ᶠ[𝓝[>] 0]
      fun ε => ((x ^ 2 - a ^ 2 : ℝ) : ℂ) *
        energyFirstIntegral
          (prodIntegrand (pauliChain e m p' p) m ![a, x] (fun _ => ε) ε p' p) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← efi_const_mul]
    congr 1
    funext k
    rw [pauliNum_vertexIntegrand e m a x hε.ne' p' p k]
    simp only [prodIntegrand, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, propDenom_eq_denom, mul_one, mul_inv]
    ring
  have hU := tendsto_nhds_unique (T2.congr' hev) T1'
  rw [pauliNum_vertexOneLoop e hm ha hx hp' hp hp0' hp0 hq, formFactorB_eq hp' hp] at hU
  have hint : ∫ z, pauliIntegrand m (a, x, Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure =
      (x ^ 2 - a ^ 2) * ∫ z, kernG m (Minkowski.dot (p' - p) (p' - p)) 0 ![a, x] z
        ∂feynmanMeasure := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact pauliIntegrand_eq_kernG m a x _ (kDen_pos a hm hq.le hz).ne' (kDen_pos x hm hq.le hz).ne'
  rw [hint] at hU
  apply mul_left_cancel₀ hc
  rw [← hU, valG_def, pauliConst]
  push_cast
  ring

omit hq in
/-- `(M₁² - M₀²) prodLimit = prodLimit (drop M₁) - prodLimit (drop M₀)`. -/
theorem prodLimit_drop {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) (hpos : ∀ i, 0 < Ms i) :
    ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) * prodLimit α (pauliChain e m p' p) m Ms p' p =
      prodLimit α (pauliChain e m p' p) m (dropOne Ms) p' p -
        prodLimit α (pauliChain e m p' p) m (Fin.tail Ms) p' p := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  have hNc := continuous_pauliChain e m p' p
  have hD : ∀ i, M₀ ≤ dropOne Ms i := fun i => by
    cases i using Fin.cases with
    | zero => exact hMs 0
    | succ i => exact hMs _
  have hT : ∀ i, M₀ ≤ Fin.tail Ms i := fun i => hMs _
  have T0 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hα hCN hMs
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  have T1 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hα hCN hD
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  have T2 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hα hCN hT
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  refine tendsto_nhds_unique (T0.const_mul _) ((T1.sub T2).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have i1 := energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hα hCN hD
    (fun _ => hε) hε
  have i2 := energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hα hCN hT
    (fun _ => hε) hε
  simp only [id]
  rw [← efi_sub ⟨i1.1, i1.2.1⟩ ⟨i2.1, i2.2.1⟩, ← efi_const_mul]
  congr 1
  funext ℓ
  simp only [prodIntegrand, Fin.prod_univ_succ, dropOne, Fin.tail, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_zero_eq_one]
  have h0 := denom_ne_zero_of_pos (M := Ms 0) hε ℓ
  have h1 := denom_ne_zero_of_pos (M := Ms 1) hε ℓ
  have hd : denom (Ms 1) ε ℓ - denom (Ms 0) ε ℓ = ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) := by
    simp only [denom]; push_cast; ring
  rw [← hd]
  field_simp

/-- **Distinct squared masses.** -/
theorem prodLimit_inj (k : ℕ) (Ms : Fin (k + 2) → ℝ) (hpos : ∀ i, 0 < Ms i)
    (hinj : ∀ i l, i ≠ l → Ms i ^ 2 ≠ Ms l ^ 2) :
    prodLimit α (pauliChain e m p' p) m Ms p' p = valG e m p' p 0 Ms := by
  induction k with
  | zero =>
    have h : Ms = ![Ms 0, Ms 1] := by
      funext i; fin_cases i <;> rfl
    rw [h]
    exact prodLimit_two hm hp' hp hp0' hp0 hq hα (hpos 0) (hpos 1) (hinj 0 1 (by decide))
  | succ k ih =>
    have hc : ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.2 (hinj 1 0 (by simp))
    have h1 := ih (dropOne Ms) (fun i => by
        cases i using Fin.cases with
        | zero => exact hpos 0
        | succ i => exact hpos _)
      (fun i l hil => by
        cases i using Fin.cases with
        | zero =>
          cases l using Fin.cases with
          | zero => exact absurd rfl hil
          | succ l => exact hinj _ _ (Fin.succ_ne_zero _).symm
        | succ i =>
          cases l using Fin.cases with
          | zero => exact hinj _ _ (Fin.succ_ne_zero _)
          | succ l =>
            exact hinj _ _ fun h => hil (Fin.ext (by
              have := congrArg Fin.val h
              simp at this
              simp
              omega)))
    have h2 := ih (Fin.tail Ms) (fun i => hpos _)
      (fun i l hil => hinj _ _ fun h => hil (Fin.succ_inj.1 h))
    apply mul_left_cancel₀ hc
    rw [prodLimit_drop hm hp' hp hp0' hp0 hα Ms hpos, h1, h2,
      valG_drop e hm p' p hq.le Ms hpos]

/-- **The two-electron, photon-product limit of the Pauli-projected chain**: for all positive
photon masses, `prodLimit = valG 0`. -/
theorem prodLimit_pauliChain_eq {k : ℕ} (Ms : Fin (k + 2) → ℝ) (hpos : ∀ i, 0 < Ms i) :
    prodLimit α (pauliChain e m p' p) m Ms p' p = valG e m p' p 0 Ms := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  have hge : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, M₀ ≤ pert Ms δ i := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
    have : 0 ≤ δ * ((i : ℕ) + 1) := by positivity
    simp only [pert]
    linarith [hMs i]
  have L1 := tendsto_prodLimit hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) α hCN
    (tendsto_pert Ms) hge
  have heq : (fun δ => prodLimit α (pauliChain e m p' p) m (pert Ms δ) p' p) =ᶠ[𝓝[>] 0]
      fun δ => valG e m p' p 0 (pert Ms δ) := by
    filter_upwards [eventually_pert_inj hpos] with δ ⟨h1, h2⟩
    exact prodLimit_inj hm hp' hp hp0' hp0 hq hα k _ h1 h2
  exact tendsto_nhds_unique (L1.congr' heq) (tendsto_valG_pert e hm p' p hq.le hpos)

/-- **The engine limit of the Pauli-projected chain**: `powLimit j Ms = valG j Ms` for `j ≤ k`
and positive masses, i.e. the one-loop Pauli functional of `Kʲ ∏_i (K + M_i²)⁻¹`. -/
theorem powLimit_pauliChain_eq (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (hj : j ≤ k)
    (hpos : ∀ i, 0 < Ms i) :
    powLimit α (pauliChain e m p' p) m p' p j Ms = valG e m p' p j Ms := by
  induction j generalizing k with
  | zero => rw [powLimit_zero]; exact prodLimit_pauliChain_eq hm hp' hp hp0' hp0 hq hα Ms hpos
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [powLimit_succ, ih (Fin.tail Ms) (by omega) fun i => hpos _, ih Ms (by omega) hpos,
        valG_succ e hm p' p hq.le j (by omega) Ms hpos]

end Value

end QED.ChainProof.HCBB2

end
