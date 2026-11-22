/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestedAtValPol
public import QED.ChainProof.SetANestedAtValReal
public import QED.ChainProof.SetANestedAtValUniq
public import QED.ChainProof.HCValueLink
public import QED.ChainProof.HCValueOuter
public import QED.GradedProof.RPi4Reduce

/-!
# The nested value of the set (a) limits, conditional on the nested form

Helper level for `QED.ChainProof.SetAPauli.SetANestedAt` (the nested value of the set (a)
limits at fixed `q`). Under the nested form `SetANestForm P₀` (obligation (N) of
`SetALimitLink`, **open**, see `QED/ChainProof/SetANestedAtPauli.lean`) this file proves
`SetANestedAt P₀ (setAR P₀)` for an explicit photon function.

* `setAPauliLim_eq`: the Pauli limit `setAPauliLim` of a list of good spectral terms is the
  one-loop Pauli functional of `2 y² m² D(K)² piG(K)`, with `D = photonD` and `piG` the `g` part
  of the list (`QED/ChainProof/SetANestedAtValEngine.lean`, Fubini there; the photon form of
  `kernG` and `(Λ² - m_γ²)² ((K + m_γ²)(K + Λ²))⁻² = D(K)²`).
* `SetAPolAt`, `setAPol`, **`setAR`**: the photon function. `setAPol P₀ m_γ Λ M₁ M₂` is a
  transverse form factor of the order-`e⁴` vacuum polarization at some admissible
  `(c₁, c₂, D)` (`0` if there is none), and
  `setAR P₀ m_γ Λ M₁ M₂ K = Re Pol(K) · K · D(K)²` for `K > 0`, `0` for `K ≤ 0`.
* `setAPol_eq`: at any admissible `(c₁, c₂, D)` every transverse form factor agrees with
  `setAPol` on `s > -4m²` (`c₁, c₂` by `pvCoeffs_unique`, `D` by
  `vacuumPolarizationPart_two_eq_of_renormalized`, then `RPi4.pol_eq_of_tendsto`).
* `piG_eq_setAR`: for `K > 0`, `piG(K) D(K)² = setAR(K)` (the `g` part is `K Pol(K)` by
  `piG_eq_of_tendsto`, and `Pol` is real by `pol_im_eq_zero`).
* **`setANestedAt_of_nestForm`**: `SetANestForm P₀ → SetANestedAt P₀ (setAR P₀)`, for `e ≠ 0`,
  `m > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetANestedAt

open QED.OneLoop QED.Integration QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalf
open QED.TwoLoop.UnitVPLink QED.ChainProof.HCSide QED.ChainProof.HCBB2 QED.ChainProof.SetASpec
open QED.ChainProof.SetAPauli QED.TwoLoop.PauliZero

/-! ### The photon form of the Pauli limit -/

theorem prod_saMs4_inv (mγ Λ K : ℝ) (h1 : K + mγ ^ 2 ≠ 0) (h2 : K + Λ ^ 2 ≠ 0) :
    (Λ ^ 2 - mγ ^ 2) ^ 2 * ∏ i, (K + saMs4 mγ Λ i ^ 2)⁻¹ = photonD mγ Λ K ^ 2 := by
  have e : ∏ i, (K + saMs4 mγ Λ i ^ 2)⁻¹ = ((K + mγ ^ 2)⁻¹ * (K + Λ ^ 2)⁻¹) ^ 2 := by
    simp [Fin.prod_univ_succ, saMs4]
    ring
  rw [e, photonD]
  field_simp
  ring

theorem termCoef_kernG {m s mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) (τ : SAOuterTerm)
    (hj : τ.j ≤ 3) {z : ℝ × ℝ} (h1 : 1 - z.2 ≠ 0) (hK : 0 < vpK m s z) (S : ℂ) :
    termCoef mγ Λ τ * (((kernG m s τ.j (saMs4 mγ Λ) z : ℝ) : ℂ) * S) =
      ((2 * z.2 ^ 2 * m ^ 2 * photonD mγ Λ (vpK m s z) ^ 2 : ℝ) : ℂ) *
        ((if τ.t then 0 else 1) * ((vpK m s z ^ τ.j : ℝ) : ℂ) * S) := by
  have hk := kernG_photon_eq (k := 2) τ.j hj (saMs4 mγ Λ) h1
    (fun i => by have := saMs4_pos hmγ hΛ i; positivity)
  have hp := prod_saMs4_inv mγ Λ (vpK m s z) (by positivity) (by positivity)
  unfold termCoef
  cases ht : τ.t
  · simp only [Bool.false_eq_true, ite_false, hk, ← hp]
    push_cast
    ring
  · simp

theorem integrable_list_sum' {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (L : List ι)
    (F : ι → α → ℂ) (h : ∀ q ∈ L, Integrable (F q) μ) :
    Integrable (fun z => (L.map fun q => F q z).sum) μ := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h q (List.mem_cons_self ..)).add (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem integral_list_sum' {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (L : List ι)
    (F : ι → α → ℂ) (h : ∀ q ∈ L, Integrable (F q) μ) :
    ∫ z, (L.map fun q => F q z).sum ∂μ = (L.map fun q => ∫ z, F q z ∂μ).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (h q (List.mem_cons_self ..))
      (integrable_list_sum' L F fun r hr => h r (List.mem_cons_of_mem _ hr)),
      ih fun r hr => h r (List.mem_cons_of_mem _ hr)]

/-- **The Pauli limit of a list of good terms** is the one-loop Pauli functional of
`2 y² m² D(K)² piG(K)`. -/
theorem setAPauliLim_eq {e m : ℝ} {p' p : Fin 4 → ℝ} (hm : 0 < m)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {Mlo mγ Λ : ℝ} (hMlo : 0 < Mlo)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) {L : List (ℂ × SAOuterTerm)} (hL : ∀ q ∈ L, q.2.Good Mlo) :
    setAPauliLim e m mγ Λ L p' p =
      pauliConst e m (Minkowski.dot (p' - p) (p' - p)) * ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) *
        ∫ z, ((2 * z.2 ^ 2 * m ^ 2 *
          photonD mγ Λ (vpK m (Minkowski.dot (p' - p) (p' - p)) z) ^ 2 : ℝ) : ℂ) *
          piG L (vpK m (Minkowski.dot (p' - p) (p' - p)) z) ∂feynmanMeasure := by
  set s := Minkowski.dot (p' - p) (p' - p)
  have hI := fun q (hq' : q ∈ L) =>
    lim_pauliTerm_eq (e := e) hm hp' hp hp0' hp0 hq hMlo hmγ hΛ (hL q hq')
  set F : ℂ × SAOuterTerm → ℝ × ℝ → ℂ := fun q z => q.1 * (termCoef mγ Λ q.2 *
    (((kernG m s q.2.j (saMs4 mγ Λ) z : ℝ) : ℂ) * specS q.2 (vpK m s z)))
  have hF : ∀ q ∈ L, Integrable (F q) feynmanMeasure := fun q hq' =>
    (((hI q hq').1.const_mul _).const_mul _)
  unfold setAPauliLim
  have e1 : (L.map fun q => q.1 * (termCoef mγ Λ q.2 *
      (pauliTerm e m p' p q.2).lim m (saMs4 mγ Λ) p' p)) =
      L.map fun q => pauliConst e m s * ((e ^ 2 / (8 * π ^ 2) : ℝ) : ℂ) *
        ∫ z, F q z ∂feynmanMeasure := List.map_congr_left fun q hq' => by
    rw [(hI q hq').2]
    simp only [F, integral_const_mul]
    ring
  rw [e1, List.sum_map_mul_left, ← integral_list_sum' L F hF]
  congr 1
  refine integral_congr_ae (QED.TwoLoop.VPHalf.ae_feynmanMeasure_ne_one.mono fun z hz => ?_)
  obtain ⟨hz, hz1⟩ := hz
  have h1 : 1 - z.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hK : 0 < vpK m s z := QED.ChainProof.HCValue.vpK_pos hm.ne' hq.le
    ⟨hz.1, hz.2.1, lt_of_le_of_ne hz.2.2 hz1⟩
  simp only [F, piG]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q hq' => ?_)
  have hj : q.2.j ≤ 3 := by have := (hL q hq').1; split_ifs at this <;> omega
  rw [termCoef_kernG hmγ hΛ q.2 hj h1 hK]
  ring

/-! ### The photon function -/

/-- `Pol` is a transverse form factor of the order-`e⁴` vacuum polarization on `s > -4m²` at some
admissible `(c₁, c₂, D)` with regulator masses `M₁, M₂, m_γ, Λ`. -/
def SetAPolAt (P₀ : Params) (M₁ M₂ mγ Λ : ℝ) (Pol : ℝ → ℂ) : Prop :=
  ∃ c₁ c₂ : ℝ, ∃ D : RegCt, SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D ∧
    QED.GradedProof.RPi4.IsPol (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
      D (4 * P₀.m ^ 2) Pol

open scoped Classical in
/-- The fixed-regulator form factor: a chosen `Pol` with `SetAPolAt`, or `0` if none exists. -/
noncomputable def setAPol (P₀ : Params) (mγ Λ M₁ M₂ : ℝ) : ℝ → ℂ :=
  if h : ∃ Pol, SetAPolAt P₀ M₁ M₂ mγ Λ Pol then h.choose else 0

/-- **The photon function of set (a)**: `Re Pol(K) · K · D(K)²` for `K > 0`, `0` for `K ≤ 0`. -/
noncomputable def setAR (P₀ : Params) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ M₁ M₂ K => if 0 < K then (setAPol P₀ mγ Λ M₁ M₂ K).re * K * photonD mγ Λ K ^ 2 else 0

section Fixed

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}

theorem regFlavors_mass_ge (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) :
    ∀ g, P₀.m ≤ (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass g :=
  QED.GradedProof.RPi4.le_leptonFlavors_mass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hA.1 hA.2.1
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0)

theorem exists_isPol (hm : 0 < P₀.m) (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) :
    ∃ Pol, QED.GradedProof.RPi4.IsPol (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (4 * P₀.m ^ 2) Pol := by
  obtain ⟨-, -, hPV₁, hPV₂, hmγ, hΛ, -, -, hD⟩ := id hA
  exact QED.GradedProof.RPi4.exists_pol _ _ D Graded.leptonRep P₀.m hm (regFlavors_mass_ge hA)
    hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₁ _ _ hPV₁ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₂ _ _ hPV₂ fun ℓ => ℓ.elim0) hD

/-- **Every form factor at admissible data agrees with `setAPol`** on `s > -4m²`. -/
theorem setAPol_eq (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D)
    {Pol : ℝ → ℂ} (hPol : QED.GradedProof.RPi4.IsPol (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (4 * P₀.m ^ 2) Pol) {s : ℝ}
    (hs : -(4 * P₀.m ^ 2) < s) : setAPol P₀ mγ Λ M₁ M₂ s = Pol s := by
  have hex : ∃ Pol, SetAPolAt P₀ M₁ M₂ mγ Λ Pol := ⟨Pol, c₁, c₂, D, hA, hPol⟩
  unfold setAPol
  simp only [hex, ↓reduceDIte]
  obtain ⟨c₁', c₂', D', hA', hPol'⟩ := hex.choose_spec
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, -, -, hD⟩ := hA
  obtain ⟨-, -, hPV₁', hPV₂', -, -, -, -, hD'⟩ := id hA'
  obtain ⟨rfl, rfl⟩ := pvCoeffs_unique hm hM₁ hPV₁' hPV₂' hPV₁ hPV₂
  have hVP := vacuumPolarizationPart_two_eq_of_renormalized (regParams P₀ M₁ M₂ c₁' c₂' mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁' c₂' mγ Λ) Graded.leptonRep P₀.m he hm (regFlavors_mass_ge hA')
    hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_sum_coeff _ _ hPV₁ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_sum_coeff_mass _ _ hPV₂ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₁ _ _ hPV₁ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₂ _ _ hPV₂ fun ℓ => ℓ.elim0) hD' hD
  have hPol'' : QED.GradedProof.RPi4.IsPol (regParams P₀ M₁ M₂ c₁' c₂' mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁' c₂' mγ Λ) D (4 * P₀.m ^ 2) (Classical.choose hex) := by
    intro k hk μ ν
    have := hPol' k hk μ ν
    simp only [hVP] at this
    exact this
  exact QED.GradedProof.RPi4.pol_eq_of_tendsto _ _ D hPol'' hPol hs

/-- **The photon function from the `g` part**: for `K > 0`, `piG(K) D(K)² = setAR(K)`. -/
theorem piG_mul_photonD_eq (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) {L : List (ℂ × SAOuterTerm)} {Mlo : ℝ}
    (hMlo : 0 < Mlo) (hL : ∀ q ∈ L, q.2.Good Mlo)
    (hVP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
      Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 k a b = saOuterTensor L ε k a b)
    {K : ℝ} (hK : 0 < K) :
    piG L K * ((photonD mγ Λ K ^ 2 : ℝ) : ℂ) = ((setAR P₀ mγ Λ M₁ M₂ K : ℝ) : ℂ) := by
  obtain ⟨Pol, hPol⟩ := exists_isPol hm hA
  have hs : -(4 * P₀.m ^ 2) < K := by nlinarith
  have hk : -(4 * P₀.m ^ 2) < Minkowski.dot (spVec K) (spVec K) := by
    rw [dot_spVec hK.le]; exact hs
  have hT := hPol (spVec K) hk 2 2
  have hT' : Tendsto (fun ε => saOuterTensor L ε (spVec K) 2 2) (𝓝[>] 0)
      (𝓝 (Pol (Minkowski.dot (spVec K) (spVec K)) *
        ((Minkowski.dot (spVec K) (spVec K) * Minkowski.metric 2 2 -
          spVec K 2 * spVec K 2 : ℝ) : ℂ))) := by
    refine hT.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact hVP ε hε.1 hε.2 _ 2 2
  have hg := piG_eq_of_tendsto hMlo hL hK.le hT'
  rw [dot_spVec hK.le] at hg
  obtain ⟨-, -, hPV₁, hPV₂, hmγ, hΛ, -, -, hD⟩ := id hA
  have hre := pol_im_eq_zero _ _ D Graded.leptonRep P₀.m hm (regFlavors_mass_ge hA) hmγ hΛ
    QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₁ _ _ hPV₁ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₂ _ _ hPV₂ fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.hD_of_renormalized _ _ _ hD) hPol hs
  have hP : Pol K = ((setAPol P₀ mγ Λ M₁ M₂ K).re : ℂ) := by
    rw [setAPol_eq he hm hA hPol hs]
    exact Complex.ext rfl (by simpa using hre)
  rw [hg, hP]
  simp only [setAR, hK, ↓reduceIte]
  push_cast
  ring

end Fixed

/-! ### The nested value -/

/-- **The nested value of the set (a) limits from the nested form** (`SetANestForm`, open):
`SetANestedAt P₀ (setAR P₀)`. -/
theorem setANestedAt_of_nestForm {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hN : SetANestForm P₀) : SetANestedAt P₀ (setAR P₀) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D hA
  filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q) V hV
  have hpq := QED.ChainProof.HCValue.isPairQ_canonical' hm hQ
  have hqQ := QED.TwoLoop.PauliZero.dot_boostMomentum_sub_restMomentum (m := P₀.m) hm hQ.le
  obtain ⟨L, hL, hVP, hval⟩ := exists_pauliNum_setALim hm hN hA
  set p' := boostMomentum P₀.m Q
  set p := restMomentum P₀.m
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := id hpq
  obtain ⟨-, -, -, -, hmγ, hΛ, -, -, -⟩ := id hA
  set s := Minkowski.dot (p' - p) (p' - p)
  have hMlo : 0 < min P₀.m (min mγ Λ) := lt_min hm (lt_min hmγ hΛ)
  have h1 := hval p' p hpq V hV
  rw [setAPauliLim_eq hm hp' hp hp0' hp0 hq hMlo hmγ hΛ hL] at h1
  have hint : ∫ z, ((2 * z.2 ^ 2 * P₀.m ^ 2 * photonD mγ Λ (vpK P₀.m s z) ^ 2 : ℝ) : ℂ) *
      piG L (vpK P₀.m s z) ∂feynmanMeasure =
      ((∫ z, 2 * (z.2 ^ 2 * P₀.m ^ 2 * setAR P₀ mγ Λ M₁ M₂ (vpK P₀.m s z)) ∂feynmanMeasure :
        ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae
      (QED.TwoLoop.VPHalf.ae_feynmanMeasure_ne_one.mono fun z hz => ?_)
    obtain ⟨hz, hz1⟩ := hz
    have hK : 0 < vpK P₀.m s z := QED.ChainProof.HCValue.vpK_pos hm.ne' hq.le
      ⟨hz.1, hz.2.1, lt_of_le_of_ne hz.2.2 hz1⟩
    have e1 := piG_mul_photonD_eq he hm hA hMlo hL hVP hK
    push_cast at e1 ⊢
    linear_combination (2 * (z.2 : ℂ) ^ 2 * (P₀.m : ℂ) ^ 2) * e1
  rw [hint] at h1
  have h2 := formFactorProj₂_of_pauliNum he hm hq (rfl : s = s) (Y := V)
    (R := setAR P₀ mγ Λ M₁ M₂) (by rw [h1]; push_cast; ring)
  rw [h2, show s = Q from hqQ]

end QED.ChainProof.SetANestedAt

end
