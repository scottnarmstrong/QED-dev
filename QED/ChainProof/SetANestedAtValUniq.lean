/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPartCongr
public import QED.Frozen.Graded.ExistsUniqueWithLevelZero
public import QED.Frozen.Graded.ExistsUniqueWithLevelOne
public import QED.Frozen.Graded.VacuumPolarizationPart
public import QED.Frozen.Graded.SelfEnergyPart
public import QED.Frozen.Graded.VertexPart
public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Frozen.Graded.IsPhotonOnShellAt

/-!
# The renormalized order-`e⁴` vacuum polarization does not depend on the choice of counterterms

Helper level for `QED.ChainProof.SetAPauli.SetANestedAt`, whose photon function may depend on
the regulator masses only. Two facts make the order-`e⁴` vacuum polarization at fixed admissible
regulators independent of the remaining data:

* `AgreeBelow D D' n`: the counterterm data agree on the levels `k < n`;
* `selfEnergyPart_congr`, `vertexPart_congr`, `vacuumPolarizationPart_congr`: by (G-loc)
  (`QED.Graded.selectedPart_congr`) the parts at order `n` read only those levels, and so do the
  renormalization conditions (`isRenormalizedThrough_congr`);
* **`agreeBelow_two`**: two counterterm sets renormalized through order `e⁴` agree on the levels
  `0` and `1`, by the uniqueness halves of (G-ex₁) and (G-ex₂)
  (`QED.Graded.existsUnique_withLevel_zero`, `QED.Graded.existsUnique_withLevel_one`);
* **`vacuumPolarizationPart_two_eq_of_renormalized`**: hence their order-`e⁴` vacuum polarizations
  are equal at every `ε`;
* `pvCoeffs_unique`: the two Pauli–Villars conditions fix `c₁`, `c₂` when `0 < m < M₁`.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.ChainProof.SetANestedAt

variable {F : Type} [Fintype F] [DecidableEq F]

/-- The counterterm data `D`, `D'` agree on the levels `k < n`. -/
def AgreeBelow (D D' : Counterterms F) (n : ℕ) : Prop :=
  (∀ f k, k < n → D.d₁ f k = D'.d₁ f k ∧ D.d₂ f k = D'.d₂ f k ∧ D.dm f k = D'.dm f k) ∧
    ∀ k, k < n → D.d₃ k = D'.d₃ k

section Congr

variable {D D' : Counterterms F} {n : ℕ}

omit [Fintype F] [DecidableEq F] in
theorem AgreeBelow.mono (h : AgreeBelow D D' n) {j : ℕ} (hj : j ≤ n) : AgreeBelow D D' j :=
  ⟨fun f k hk => h.1 f k (by omega), fun k hk => h.2 k (by omega)⟩

theorem selfEnergyPart_congr (h : AgreeBelow D D' n) (P : Params) (Φ : Lepton.Flavors F)
    (f : F) : selfEnergyPart P Φ D f n = selfEnergyPart P Φ D' f n := by
  funext p
  ext α β
  simp only [selfEnergyPart, Matrix.of_apply, onePIPart]
  rw [selectedPart_congr P _ D D' 1 0 _ (2 * n) (fun f k hk => h.1 f k (by omega))
    (fun k hk => h.2 k (by omega))]

theorem vertexPart_congr (h : AgreeBelow D D' n) (P : Params) (Φ : Lepton.Flavors F)
    (f : F) : vertexPart P Φ D f n = vertexPart P Φ D' f n := by
  funext p' p μ
  ext i j
  simp only [vertexPart, Matrix.of_apply, onePIPart]
  rw [selectedPart_congr P _ D D' 1 1 _ (2 * n + 1) (fun f k hk => h.1 f k (by omega))
    (fun k hk => h.2 k (by omega))]

theorem vacuumPolarizationPart_congr (h : AgreeBelow D D' n) (P : Params)
    (Φ : Lepton.Flavors F) : vacuumPolarizationPart P Φ D n = vacuumPolarizationPart P Φ D' n := by
  funext k μ ν
  simp only [vacuumPolarizationPart, onePIPart]
  rw [selectedPart_congr P _ D D' 0 2 _ (2 * n) (fun f k hk => h.1 f k (by omega))
    (fun k hk => h.2 k (by omega))]

theorem isRenormalizedThrough_congr (h : AgreeBelow D D' n) (P : Params)
    (Φ : Lepton.Flavors F) (rep : F → F) :
    IsRenormalizedThrough P Φ D rep n ↔ IsRenormalizedThrough P Φ D' rep n := by
  have hc : ∀ j, j ≤ n → (((∀ f, rep f = f → IsOnShellAt P Φ D f j ∧
      IsChargeNormalizedAt P Φ D f j) ∧ IsPhotonOnShellAt P Φ D j) ↔
      ((∀ f, rep f = f → IsOnShellAt P Φ D' f j ∧ IsChargeNormalizedAt P Φ D' f j) ∧
        IsPhotonOnShellAt P Φ D' j)) := by
    intro j hj
    have hS := selfEnergyPart_congr (h.mono hj)
    have hV := vertexPart_congr (h.mono hj)
    have hP := vacuumPolarizationPart_congr (h.mono hj)
    simp only [IsOnShellAt, IsChargeNormalizedAt, IsPhotonOnShellAt, hS, hV, hP]
  unfold IsRenormalizedThrough
  refine and_congr ⟨fun h1 f k hk => ?_, fun h1 f k hk => ?_⟩
    (forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hj => hc j hj)
  · obtain ⟨a, b, c⟩ := h.1 f k hk
    obtain ⟨a', b', c'⟩ := h.1 (rep f) k hk
    obtain ⟨x, y, z⟩ := h1 f k hk
    exact ⟨a.symm.trans (x.trans a'), b.symm.trans (y.trans b'), c.symm.trans (z.trans c')⟩
  · obtain ⟨a, b, c⟩ := h.1 f k hk
    obtain ⟨a', b', c'⟩ := h.1 (rep f) k hk
    obtain ⟨x, y, z⟩ := h1 f k hk
    exact ⟨a.trans (x.trans a'.symm), b.trans (y.trans b'.symm), c.trans (z.trans c'.symm)⟩

end Congr

/-! ### Uniqueness through order `e⁴` -/

/-- The level-`k` data of `D`. -/
def levelData (D : Counterterms F) (k : ℕ) : (F → ℝ × ℝ × ℝ) × ℝ :=
  (fun f => (D.d₁ f k, D.d₂ f k, D.dm f k), D.d₃ k)

omit [Fintype F] [DecidableEq F] in
theorem withLevel_levelData (D : Counterterms F) (k : ℕ) :
    D.withLevel k (levelData D k).1 (levelData D k).2 = D := by
  rcases D with ⟨d₁, d₂, dm, d₃⟩
  simp only [Counterterms.withLevel, levelData, Counterterms.mk.injEq]
  refine ⟨funext fun f => funext fun j => ?_, funext fun f => funext fun j => ?_,
    funext fun f => funext fun j => ?_, funext fun j => ?_⟩ <;> split_ifs with h <;> simp [h]

/-- **Two counterterm sets renormalized through order `e⁴` agree on the levels `0` and `1`.** -/
theorem agreeBelow_two (P : Params) (Φ : Lepton.Flavors F) {D D' : Counterterms F}
    (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∑ f, Φ.coeff f = 0) (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hbPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hbPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) (hD' : IsRenormalizedThrough P Φ D' rep 2) :
    AgreeBelow D D' 2 := by
  have one : ∀ {E : Counterterms F}, IsRenormalizedThrough P Φ E rep 2 →
      IsRenormalizedThrough P Φ E rep 1 := fun h =>
    ⟨fun f k hk => h.1 f k (by omega), fun j hj hj1 => h.2 j hj (by omega)⟩
  -- level `0`
  obtain ⟨x, -, hx⟩ := existsUnique_withLevel_zero P Φ D rep he
    (fun f => hm₀.trans_le (hmass f)) hmγ hΛ hrep hPV₁ hPV₂
  have h0 : levelData D 0 = levelData D' 0 := by
    have a := hx (levelData D 0) (by
      show IsRenormalizedThrough P Φ (D.withLevel 0 (levelData D 0).1 (levelData D 0).2) rep 1
      rw [withLevel_levelData]; exact one hD)
    have b := hx (levelData D' 0) ((isRenormalizedThrough_congr (D' := D')
      ⟨fun f k hk => by
        obtain rfl : k = 0 := by omega
        simp [Counterterms.withLevel, levelData],
       fun k hk => by
        obtain rfl : k = 0 := by omega
        simp [Counterterms.withLevel, levelData]⟩ P Φ rep).2 (one hD'))
    rw [a, b]
  -- level `1`
  obtain ⟨y, -, hy⟩ := existsUnique_withLevel_one P Φ D rep m₀ he hm₀ hmass hmγ hΛ hrep
    hbPV₁ hbPV₂ (one hD)
  have h1 : levelData D 1 = levelData D' 1 := by
    have a := hy (levelData D 1) (by
      show IsRenormalizedThrough P Φ (D.withLevel 1 (levelData D 1).1 (levelData D 1).2) rep 2
      rw [withLevel_levelData]; exact hD)
    have b := hy (levelData D' 1) ((isRenormalizedThrough_congr (D' := D')
      ⟨fun f k hk => by
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · have := congrFun (congrArg Prod.fst h0) f
          simp only [levelData, Prod.mk.injEq] at this
          simp [Counterterms.withLevel, this]
        · simp [Counterterms.withLevel, levelData],
       fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · have := congrArg Prod.snd h0
          simp only [levelData] at this
          simp [Counterterms.withLevel, this]
        · simp [Counterterms.withLevel, levelData]⟩ P Φ rep).2 hD')
    rw [a, b]
  refine ⟨fun f k hk => ?_, fun k hk => ?_⟩
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have := congrFun (congrArg Prod.fst h0) f
      simpa only [levelData, Prod.mk.injEq] using this
    · have := congrFun (congrArg Prod.fst h1) f
      simpa only [levelData, Prod.mk.injEq] using this
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact congrArg Prod.snd h0
    · exact congrArg Prod.snd h1

/-- **The order-`e⁴` vacuum polarization of two renormalized counterterm sets agree**, at every
`ε`. -/
theorem vacuumPolarizationPart_two_eq_of_renormalized (P : Params) (Φ : Lepton.Flavors F)
    {D D' : Counterterms F} (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hbPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hbPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) (hD' : IsRenormalizedThrough P Φ D' rep 2)
    (P' : Params) : vacuumPolarizationPart P' Φ D 2 = vacuumPolarizationPart P' Φ D' 2 :=
  vacuumPolarizationPart_congr (agreeBelow_two P Φ rep m₀ he hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂
    hbPV₁ hbPV₂ hD hD') P' Φ

/-- **The Pauli–Villars conditions fix the coefficients** when `0 < m < M₁`. -/
theorem pvCoeffs_unique {m M₁ M₂ c₁ c₂ c₁' c₂' : ℝ} (hm : 0 < m) (hM₁ : m < M₁)
    (h1 : 1 + c₁ + c₂ = 0) (h2 : m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0)
    (h1' : 1 + c₁' + c₂' = 0) (h2' : m ^ 2 + c₁' * M₁ ^ 2 + c₂' * M₂ ^ 2 = 0) :
    c₁ = c₁' ∧ c₂ = c₂' := by
  have hne : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := by
    intro h
    have : m ^ 2 = M₁ ^ 2 := by linear_combination h2 - M₁ ^ 2 * h1 + c₂ * h
    nlinarith
  have hc : (c₁ - c₁') * (M₁ ^ 2 - M₂ ^ 2) = 0 := by
    linear_combination h2 - h2' - M₂ ^ 2 * (h1 - h1')
  have e1 : c₁ = c₁' := sub_eq_zero.1 ((mul_eq_zero.1 hc).resolve_right hne)
  exact ⟨e1, by linear_combination h1 - h1' - e1⟩
