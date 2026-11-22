/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliFinal
public import QED.GradedProof.Homogeneity

/-!
# Set (c): the Pauli values of the main classes are canonical

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hcan` of
`QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp`. The 36 main classes
(`mainFam`) are contractions at the grading `0`: every counterterm vertex (the `photonCt` vertex of
`repD i s`) is read at the level `0`. So their values read the counterterms only through the
level `0`, and at two admissible data with the same `m_γ, Λ, M₁, M₂` (equal `c₁, c₂, s` and levels
`0, 1` of `D`, `QED.ChainProof.SetCPauli.setCAdm_unique`) the class values agree for every `ε`.
Hence the class limits agree, and any per-class Pauli value is canonical.

* `contractionAmplitude_congr_level`, **`contractionValue_congr_level`**: (G₃), (G₅) read only
  the levels `g t` of the counterterm vertices;
* **`mainFam_congr`**: the main class values agree at counterterms agreeing on the level `0`;
* **`isClassLimC_main_congr`**: the main class limits at the set (c) data depend on `D` only
  through its levels `0`, `1`;
* **`clsCanon_main`**: every Pauli value `β` of a main class with a limit link is canonical
  (`ClsCanon`); no other input;
* **`isFormFactorPair_vertexSetC_pauli_limit_of_mainLinks`**: (HS₆) from the main-class limit,
  covariance and Pauli links, the `♯`-oddness of the main-class limits and the regulator limit,
  the input `hcan` discharged.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction IsOnePI)

namespace QED.ChainProof.SetCPauli

open QED.Graded
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.ChainProof.SetANestedAt (AgreeBelow)

/-! ### Locality in the level of the counterterm vertices -/

section Congr

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  {D D' : Counterterms F} {n : ℕ} (hD : AgreeBelow D D' n)
include hD

omit [Fintype F] [DecidableEq F] in
/-- (G₃) reads only the levels `g t` of the counterterm vertices. -/
theorem contractionAmplitude_congr_level {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring F κ) (g : Grading κ) (hg : ∀ t, g t < n)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ =
      contractionAmplitude P Φ D' C φ g pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  congr 3
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases h : κ t = .gauge
  · exact QED.GradedProof.vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t h
  · have hb := hg ⟨t, h⟩
    simp only [h, ↓reduceDIte]
    rw [(hD.1 _ _ hb).1, (hD.1 _ _ hb).2.1, (hD.1 _ _ hb).2.2, hD.2 _ hb]

/-- **(G₅) reads only the levels `g t` of the counterterm vertices.** -/
theorem contractionValue_congr_level {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ) (hg : ∀ t, g t < n)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C g pOut pIn kIn αOut βIn μ =
      contractionValue P Φ D' C g pOut pIn kIn αOut βIn μ := by
  have hr : ∀ k, regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ =
      regulatedAmplitude P Φ D' C g pIn kIn k αOut βIn μ := fun k =>
    Finset.sum_congr rfl fun φ _ => by
      rw [contractionAmplitude_congr_level P Φ hD C φ g hg]
  unfold contractionValue
  simp only [hr]

end Congr

/-! ### The main class values and limits -/

/-- **The main class values read the counterterms only through the level `0`.** -/
theorem mainFam_congr (P : Params) (Φ : Lepton.Flavors (Fin 3 ⊕ Fin 0 × Fin 3)) {D D' : RegCt}
    (hD : AgreeBelow D D' 1) (p' p : Fin 4 → ℝ) (μ : Fin 4) (r : MainIdx) :
    mainFam P Φ D p' p μ r = mainFam P Φ D' p' p μ r := by
  have hg : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (t : CtVertex κ), (0 : Grading κ) t < 1 :=
    fun _ => Nat.one_pos
  rcases r with i | ⟨i, s⟩
  · ext α β
    simp only [mainFam, mainVal, clsVal, Matrix.neg_apply, Matrix.of_apply,
      contractionValue_congr_level P Φ hD _ _ hg]
  · ext α β
    simp only [mainFam, mainVal, clsVal, Matrix.of_apply,
      contractionValue_congr_level P Φ hD _ _ hg]

variable {P₀ : Params}

/-- **The main class limits depend on `D` only through its levels `0`, `1`.** -/
theorem isClassLimC_main_congr {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D D' : RegCt} (hD : AgreeBelow D D' 2)
    (s : ℝ × ℝ × ℝ) (r : MainIdx) (p' p : Fin 4 → ℝ) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    IsClassLimC mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y ↔
      IsClassLimC mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D' s r p' p Y := by
  have h1 : AgreeBelow (shareCt D s) (shareCt D' s) 1 := (agreeBelow_withLevel_one hD s).mono
    (by norm_num)
  unfold IsClassLimC
  simp only [mainFam_congr _ _ h1]

/-- **The Pauli value of a main class is canonical**: any `β` with a Pauli link of a main class
with a limit link takes the same value at all admissible data with the same `m_γ, Λ, M₁, M₂`. -/
theorem clsCanon_main (he : P₀.e ≠ 0) {r : MainIdx} {β : ClsPauliVal}
    (hL : SetCClassLim mainFam P₀ r) (hP : SetCClassPauli mainFam P₀ r β) : ClsCanon P₀ β := by
  intro M₁ M₂ c₁ c₂ c₁' c₂' mγ Λ D D' s s' hA hA'
  have hA₀ := hA
  obtain ⟨rfl, rfl, hD, rfl⟩ := setCAdm_unique he hA hA'
  have hm : 0 < P₀.m := by obtain ⟨-, -, -, -, hmγ, -, -, hm2, -⟩ := hA; linarith
  refine eq_of_forall_dist_le fun η hη => ?_
  have h2 : 0 < η / 2 := half_pos hη
  obtain ⟨Q, ⟨hQ, hQ'⟩, hQ0⟩ := (((hP M₁ M₂ c₁ c₂ mγ Λ D s hA₀ _ h2).and
    (hP M₁ M₂ c₁ c₂ mγ Λ D' s hA' _ h2)).and self_mem_nhdsWithin).exists
  have hpq := QED.ChainProof.HCValue.isPairQ_canonical' hm hQ0
  obtain ⟨Y, hY⟩ := hL M₁ M₂ c₁ c₂ mγ Λ D s hA₀ _ _ hpq
  have hY' := (isClassLimC_main_congr hD s r _ _ Y).1 hY
  have e1 := hQ Y hY
  have e2 := hQ' Y hY'
  rw [dist_eq_norm]
  calc ‖β M₁ M₂ c₁ c₂ mγ Λ D s - β M₁ M₂ c₁ c₂ mγ Λ D' s‖
      ≤ ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (TwoLoop.PauliZero.boostMomentum P₀.m Q)
            (TwoLoop.PauliZero.restMomentum P₀.m) Y - β M₁ M₂ c₁ c₂ mγ Λ D s‖ +
          ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (TwoLoop.PauliZero.boostMomentum P₀.m Q)
            (TwoLoop.PauliZero.restMomentum P₀.m) Y - β M₁ M₂ c₁ c₂ mγ Λ D' s‖ := by
        rw [← norm_neg (_ - β M₁ M₂ c₁ c₂ mγ Λ D s)]
        refine (norm_add_le _ _).trans_eq' ?_
        congr 1
        ring
    _ ≤ η := by linarith

/-- The main Pauli values of a family with limit links are canonical. -/
theorem clsCanon_main_all (he : P₀.e ≠ 0) {βM : MainIdx → ClsPauliVal}
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r)) :
    ∀ r, ClsCanon P₀ (βM r) := fun r => clsCanon_main he (hM r) (hPM r)

end QED.ChainProof.SetCPauli

namespace QED.ThreeLoop

open QED.ChainProof.SetCPauli (MainIdx ClsPauliVal mainFam SetCClassLim SetCClassCov
  SetCClassPauli SetCClassSharp SetCRegLimitB setCPauliB)

/-- **The remaining interface of set (c), canonicity discharged**: (HS₆) from the main-class
limit, covariance and Pauli links, `♯`-odd main-class limits and the regulator limit of
`b = setCPauliB P₀ βᴹ`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_mainLinks (P₀ : Params)
    {βM : MainIdx → ClsPauliVal}
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r)) (hSM : ∀ r, SetCClassSharp mainFam P₀ r)
    (hreg : SetCRegLimitB P₀ (setCPauliB P₀ βM))
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_mainSharp P₀ hM hMc hPM
    (QED.ChainProof.SetCPauli.clsCanon_main_all he hM hPM) hSM hreg he hm η hη

end QED.ThreeLoop

end
