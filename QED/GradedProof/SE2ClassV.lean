/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassVNum

/-!
# The class `V`: the two-loop vacuum-polarization self-energy is integrable

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2: the class obligation `ClassInt repV` (`classInt_repV`).

## Proof

* **Routing.** The chords of `repV` are the open line `0 → 1` and the loop line `3 → 2`,
  carrying `ℓ₀` and `ℓ₁`; the conserved routing `vMom` (open line `ℓ₀`, loop lines `u = ℓ₁` and
  `v = p - ℓ₀ + ℓ₁`, photons `p - ℓ₀` and `ℓ₀ - p`) is therefore the frozen routing (T₄). All
  momenta are rows of the integer matrix `baseA` with shifts `basePP p`.
* **Flavour sum.** The integrand is `∑_f c_f C (E₀ + M_f² E₂) D_f(u)⁻¹ D_f(v)⁻¹ R`
  (`v_amplitude_eq`), `R` the open-line and photon denominators. By the two Pauli–Villars
  conditions (`QED.TwoLoop.Bridge.flavourSum_propDenom`) this is `K C R` times
  `(E₀ + m² E₂)(a₀b₀b₁b₂ + a₀a₁b₁b₂ + a₀a₁a₂b₂) - E₂ (a₁b₁b₂ + a₁a₂b₂)`, with `a_f = D_f(u)⁻¹`,
  `b_f = D_f(v)⁻¹` (the factors `D_{M₂}(u) a₂` and `D_{M₁}(v) b₁` cancel).
* **Pieces.** Each of the five terms is a polynomial numerator over the line denominators of
  parametric data whose loop matrix consists of rows of `baseA`: nine lines (open line, four
  bubble lines, two photon pairs) for the first three, eight for the last two. The numerators
  satisfy the pointwise bound for `{0, 1, 2}` (exponent `3`) or `{0}` (exponent `1`), the
  criterion is decided, and the representation under the refined bound
  (`jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined`, `N ≥ 8`) gives
  (T₉′) for each; sums are integrable.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound IntNoSubdivergenceRefined)
open Complex

/-! ### Lines, chords and the routing -/

theorem v_line_cases (f : Line repV) :
    f = .inl vf1 ∨ f = .inl vf2 ∨ f = .inl vf3 ∨ f = .inr vg1 ∨ f = .inr vg2 := by
  rcases f with f | g
  · rcases v_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases v_photonLine_cases g with rfl | rfl <;> simp

theorem v_isChord_iff (g : Line repV) : IsChord g ↔ g = .inl vf1 ∨ g = .inl vf2 := by
  have c1 : IsChord (.inl vf1 : Line repV) := by decide +kernel
  have c2 : IsChord (.inl vf2 : Line repV) := by decide +kernel
  have c3 : ¬ IsChord (.inl vf3 : Line repV) := by decide +kernel
  have c4 : ¬ IsChord (.inr vg1 : Line repV) := by decide +kernel
  have c5 : ¬ IsChord (.inr vg2 : Line repV) := by decide +kernel
  obtain ⟨n12, n13, n23, -⟩ := v_ne
  rcases v_line_cases g with rfl | rfl | rfl | rfl | rfl
  · simp [c1]
  · simp [c2]
  · simp [c3, n13.symm, n23.symm]
  · simp [c4]
  · simp [c5]

theorem v_ends : (Line.ends (.inl vf1 : Line repV)) = (0, 1) ∧
    (Line.ends (.inl vf2 : Line repV)) = (3, 2) ∧ (Line.ends (.inl vf3 : Line repV)) = (2, 3) ∧
    (Line.ends (.inr vg1 : Line repV)) = (0, 2) ∧ (Line.ends (.inr vg2 : Line repV)) = (1, 3) := by
  decide +kernel

theorem v_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggg, t.1 = v ∧ repV.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_gggg, t.1 = v ∧ repV.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

open scoped Classical in
theorem v_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl vf1 : Line repV) = ℓ 0 ∧
      chordMomentum ℓ (.inl vf2 : Line repV) = ℓ 1 := by
  have l1 : (Line.label (.inl vf1 : Line repV)) = 1 := rfl
  have l2 : (Line.label (.inl vf2 : Line repV)) = 2 := rfl
  have h0 : (Finset.univ.filter fun g : Line repV =>
      IsChord g ∧ g.label < (Line.label (.inl vf1 : Line repV))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (v_isChord_iff g).mp hg with rfl | rfl
    · simp at hl
    · simp [l1, l2] at hl
  have h1 : (Finset.univ.filter fun g : Line repV =>
      IsChord g ∧ g.label < (Line.label (.inl vf2 : Line repV))).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨.inl vf1, Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (v_isChord_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(v_isChord_iff _).mpr (Or.inl rfl), by simp [l1, l2]⟩
  constructor
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_zero]; convert h0)
    · exact absurd (by convert (show 0 < 2 by norm_num) using 2; convert h0) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_one]; convert h1)
    · exact absurd (by convert (show 1 < 2 by norm_num) using 2; convert h1) h

/-- The rows of the momenta of `repV`: open line `ℓ₀`, loop lines `ℓ₁` and `-ℓ₀ + ℓ₁`,
photons `-ℓ₀` and `ℓ₀`. -/
def baseA : Fin 5 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![-1, 1], ![-1, 0], ![1, 0]]

/-- The shifts of the momenta of `repV`. -/
def basePP (p : Fin 4 → ℝ) : Fin 5 → Fin 4 → ℝ := ![0, 0, p, p, -p]

/-- The row of each line of `repV`. -/
def idxV (f : Line repV) : Fin 5 :=
  if f = .inl vf1 then 0 else if f = .inl vf2 then 1 else if f = .inl vf3 then 2 else
    if f = .inr vg1 then 3 else 4

theorem idxV_apply : idxV (.inl vf1) = 0 ∧ idxV (.inl vf2) = 1 ∧ idxV (.inl vf3) = 2 ∧
    idxV (.inr vg1) = 3 ∧ idxV (.inr vg2) = 4 := by
  decide +kernel

/-- The routing of `V`. -/
def vMom (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repV) : Fin 4 → ℝ :=
  QED.Integration.TwoLoop.lineMomentum (castLoopMatrix baseA) (basePP p) (idxV f) ℓ

theorem vMom_apply (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vMom p ℓ (.inl vf1) = ℓ 0 ∧ vMom p ℓ (.inl vf2) = ℓ 1 ∧
      vMom p ℓ (.inl vf3) = p - ℓ 0 + ℓ 1 ∧ vMom p ℓ (.inr vg1) = p - ℓ 0 ∧
      vMom p ℓ (.inr vg2) = ℓ 0 - p := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := idxV_apply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [vMom, i1, i2, i3, i4, i5, QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, baseA,
      basePP, Fin.sum_univ_two] <;>
    ring

theorem v_isConserved (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved repV ![p] ![p] ![] (vMom p ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := v_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := vMom_apply p ℓ
  obtain ⟨n12, n13, n23, n45⟩ := v_ne
  intro v
  rw [inflow, Fintype.sum_sum_type, sum_eq_of_three n12 n13 n23 v_fermionLine_cases,
    sum_eq_of_two n45 v_photonLine_cases, externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := v_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, m1, m2, m3, m4, m5, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> simp
  ring

theorem lineMomentum₂_repV (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repV ![p] ![p] ![] ℓ = vMom p ℓ := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (v_isConserved p ℓ) (fun g hg => ?_) f).symm
  obtain ⟨c1, c2⟩ := v_chordMomentum ℓ
  obtain ⟨m1, m2, -, -, -⟩ := vMom_apply p ℓ
  rcases (v_isChord_iff g).mp hg with rfl | rfl
  · rw [c1, m1]
  · rw [c2, m2]

/-! ### The pieces -/

/-- A piece: a numerator over the line denominators of data whose rows are rows of `baseA`. -/
theorem jointEnergyFirstIntegrable_vPiece {m : ℕ} (hm : 7 ≤ m) (sh : Fin (m + 1) → Fin 5)
    (Ms : Fin (m + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) (p : Fin 4 → ℝ) {E : Finset (Fin (m + 1))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => baseA (sh i))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix fun i => baseA (sh i)) E 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => F ℓ *
      ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms ε i
        ℓ)⁻¹) := by
  obtain ⟨Q, rfl⟩ := hpoly.exists_loopQuartic
  exact
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q _ _ Ms hm hε
      ((QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB

/-- The line rows of the five pieces. -/
def sh1 : Fin 9 → Fin 5 := ![0, 1, 2, 2, 2, 3, 3, 4, 4]
def sh2 : Fin 9 → Fin 5 := ![0, 1, 2, 1, 2, 3, 3, 4, 4]
def sh3 : Fin 9 → Fin 5 := ![0, 1, 2, 1, 1, 3, 3, 4, 4]
def sh4 : Fin 8 → Fin 5 := ![0, 1, 2, 2, 3, 3, 4, 4]
def sh5 : Fin 8 → Fin 5 := ![0, 1, 2, 1, 3, 3, 4, 4]

theorem crit_sh : IntNoSubdivergenceRefined 2 {0, 1, 2} (fun i => baseA (sh1 i)) ∧
    IntNoSubdivergenceRefined 2 {0, 1, 2} (fun i => baseA (sh2 i)) ∧
    IntNoSubdivergenceRefined 2 {0, 1, 2} (fun i => baseA (sh3 i)) ∧
    IntNoSubdivergenceRefined 2 {0} (fun i => baseA (sh4 i)) ∧
    IntNoSubdivergenceRefined 2 {0} (fun i => baseA (sh5 i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The masses of the five pieces. -/
def ms1 (Q : Params) : Fin 9 → ℝ := ![Q.m, Q.m, Q.m, Q.M₁, Q.M₂, Q.mγ, Q.Λ, Q.mγ, Q.Λ]
def ms2 (Q : Params) : Fin 9 → ℝ := ![Q.m, Q.m, Q.M₁, Q.M₁, Q.M₂, Q.mγ, Q.Λ, Q.mγ, Q.Λ]
def ms3 (Q : Params) : Fin 9 → ℝ := ![Q.m, Q.m, Q.M₂, Q.M₁, Q.M₂, Q.mγ, Q.Λ, Q.mγ, Q.Λ]
def ms4 (Q : Params) : Fin 8 → ℝ := ![Q.m, Q.M₁, Q.M₁, Q.M₂, Q.mγ, Q.Λ, Q.mγ, Q.Λ]
def ms5 (Q : Params) : Fin 8 → ℝ := ![Q.m, Q.M₁, Q.M₂, Q.M₂, Q.mγ, Q.Λ, Q.mγ, Q.Λ]

section Products

variable (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)

/-- The momentum of row `j`. -/
noncomputable abbrev bm (j : Fin 5) : Fin 4 → ℝ :=
  QED.Integration.TwoLoop.lineMomentum (castLoopMatrix baseA) (basePP p) j ℓ

/-- The open-line and photon denominators. -/
noncomputable abbrev denR : ℂ :=
  (propDenom Q.m Q.ε (bm p ℓ 0))⁻¹ *
    ((propDenom Q.mγ Q.ε (bm p ℓ 3))⁻¹ * (propDenom Q.Λ Q.ε (bm p ℓ 3))⁻¹) *
    ((propDenom Q.mγ Q.ε (bm p ℓ 4))⁻¹ * (propDenom Q.Λ Q.ε (bm p ℓ 4))⁻¹)

theorem lineDenom_sh {m : ℕ} (sh : Fin (m + 1) → Fin 5) (Ms : Fin (m + 1) → ℝ) (ε : ℝ)
    (i : Fin (m + 1)) : lineDenom (castLoopMatrix fun i => baseA (sh i))
      (fun i => basePP p (sh i)) Ms ε i ℓ = propDenom (Ms i) ε (bm p ℓ (sh i)) := rfl

theorem prod1 : ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh1 i)) (fun i => basePP p (sh1 i))
    (ms1 Q) Q.ε i ℓ)⁻¹ = denR Q p ℓ * ((propDenom Q.m Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.m Q.ε (bm p ℓ 2))⁻¹ * (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ *
      (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, lineDenom_sh, sh1, ms1,
    Matrix.cons_val_zero, Matrix.cons_val_succ, denR]
  ring

theorem prod2 : ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh2 i)) (fun i => basePP p (sh2 i))
    (ms2 Q) Q.ε i ℓ)⁻¹ = denR Q p ℓ * ((propDenom Q.m Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ * (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ *
      (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, lineDenom_sh, sh2, ms2,
    Matrix.cons_val_zero, Matrix.cons_val_succ, denR]
  ring

theorem prod3 : ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh3 i)) (fun i => basePP p (sh3 i))
    (ms3 Q) Q.ε i ℓ)⁻¹ = denR Q p ℓ * ((propDenom Q.m Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, lineDenom_sh, sh3, ms3,
    Matrix.cons_val_zero, Matrix.cons_val_succ, denR]
  ring

theorem prod4 : ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh4 i)) (fun i => basePP p (sh4 i))
    (ms4 Q) Q.ε i ℓ)⁻¹ = denR Q p ℓ * ((propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, lineDenom_sh, sh4, ms4,
    Matrix.cons_val_zero, Matrix.cons_val_succ, denR]
  ring

theorem prod5 : ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh5 i)) (fun i => basePP p (sh5 i))
    (ms5 Q) Q.ε i ℓ)⁻¹ = denR Q p ℓ * ((propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₂ Q.ε (bm p ℓ 1))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, lineDenom_sh, sh5, ms5,
    Matrix.cons_val_zero, Matrix.cons_val_succ, denR]
  ring

end Products

/-! ### The class obligation -/

/-- **The class obligation for `V`.** -/
theorem classInt_repV : ClassInt repV := by
  intro Q hQ p α β
  have hε := hQ.hε
  have hε' : Q.ε ≠ 0 := hε.ne'
  rw [loopCount_repV]
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  set C : ℂ := (I * Q.e) ^ 4 * (1 / I) ^ 5 with hC
  set K : ℂ := ((((Q.M₁ ^ 2 - Q.m ^ 2) * (Q.M₂ ^ 2 - Q.m ^ 2)) : ℝ) : ℂ) with hK
  set F1 : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ => κ * C * K *
    (seE0 Q α β (bm p ℓ 0) (bm p ℓ 1) (bm p ℓ 2) + ((Q.m ^ 2 : ℝ) : ℂ) * seE2 Q α β (bm p ℓ 0))
    with hF1
  set F2 : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ => -(κ * C * K * seE2 Q α β (bm p ℓ 0)) with hF2
  have ha : ∀ j : Fin 5, IsLoopAffine fun ℓ => bm p ℓ j := fun j =>
    isLoopAffine_lineMomentum _ _ _
  have hp1 : IsLoopPoly 2 4 F1 := by
    have h2 := ((isLoopPoly_seE2 Q α β (ha 0)).mono (n' := 3) (by norm_num)).const_mul
      ((Q.m ^ 2 : ℝ) : ℂ)
    exact (((isLoopPoly_seE0 Q α β (ha 0) (ha 1) (ha 2)).add h2).const_mul (κ * C * K)).mono
      (by norm_num)
  have hp2 : IsLoopPoly 2 4 F2 := by
    have h := ((isLoopPoly_seE2 Q α β (ha 0)).const_mul (-(κ * C * K))).mono (n' := 4)
      (by norm_num)
    refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ => ?_)).mp h
    simp only [hF2]
    ring
  have hB1 : ∀ sh : Fin (8 + 1) → Fin 5, sh 0 = 0 → sh 1 = 1 → sh 2 = 2 →
      RefinedBound (castLoopMatrix fun i => baseA (sh i)) {0, 1, 2} 4 F1 := by
    intro sh s0 s1 s2
    have e : ∀ (j : Fin (8 + 1)) (k : Fin 5), sh j = k → ∀ ℓ, QED.Integration.TwoLoop.lineMomentum
        (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) j ℓ = bm p ℓ k := by
      intro j k hjk ℓ
      exact congrArg (bm p ℓ) hjk
    have h0 := refinedBound_seE0 (castLoopMatrix fun i => baseA (sh i))
      (fun i => basePP p (sh i)) Q α β (e0 := 0) (e1 := 1) (e2 := 2) (by decide) (by decide)
      (by decide)
    have h2 := (refinedBound_seE2 (castLoopMatrix fun i => baseA (sh i))
      (fun i => basePP p (sh i)) Q α β 0).mono (E' := {0, 1, 2}) (by decide) (by norm_num :
        1 ≤ 3)
    simp only [e 0 0 s0, e 1 1 s1, e 2 2 s2] at h0 h2
    exact ((h0.add (h2.const_mul ((Q.m ^ 2 : ℝ) : ℂ))).const_mul (κ * C * K)).mono subset_rfl
      (by norm_num)
  have hB2 : ∀ sh : Fin (7 + 1) → Fin 5, sh 0 = 0 →
      RefinedBound (castLoopMatrix fun i => baseA (sh i)) {0} 4 F2 := by
    intro sh s0
    have e : ∀ ℓ, QED.Integration.TwoLoop.lineMomentum
        (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) 0 ℓ = bm p ℓ 0 := by
      intro ℓ
      exact congrArg (bm p ℓ) s0
    have h2 := refinedBound_seE2 (castLoopMatrix fun i => baseA (sh i))
      (fun i => basePP p (sh i)) Q α β 0
    simp only [e] at h2
    exact ((h2.const_mul (κ * C * K)).neg).mono subset_rfl (by norm_num)
  have key : ∀ ℓ : Fin 2 → Fin 4 → ℝ, κ * regulatedAmplitude₂ Q repV ![p] ![]
      (lineMomentum₂ repV ![p] ![p] ![] ℓ) ![α] ![β] ![] =
      F1 ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh1 i))
          (fun i => basePP p (sh1 i)) (ms1 Q) Q.ε i ℓ)⁻¹ +
        F1 ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh2 i))
          (fun i => basePP p (sh2 i)) (ms2 Q) Q.ε i ℓ)⁻¹ +
        F1 ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh3 i))
          (fun i => basePP p (sh3 i)) (ms3 Q) Q.ε i ℓ)⁻¹ +
        F2 ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh4 i))
          (fun i => basePP p (sh4 i)) (ms4 Q) Q.ε i ℓ)⁻¹ +
        F2 ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh5 i))
          (fun i => basePP p (sh5 i)) (ms5 Q) Q.ε i ℓ)⁻¹ := by
    intro ℓ
    obtain ⟨i1, i2, i3, i4, i5⟩ := idxV_apply
    have hv : ∀ f, vMom p ℓ f = bm p ℓ (idxV f) := fun _ => rfl
    have hc0 : Q.loopCoeff 0 = 1 := rfl
    have hc1 : Q.loopCoeff 1 = Q.c₁ := rfl
    have hc2 : Q.loopCoeff 2 = Q.c₂ := rfl
    have hm0 : Q.mass 0 = Q.m := rfl
    have hm1 : Q.mass 1 = Q.M₁ := rfl
    have hm2 : Q.mass 2 = Q.M₂ := rfl
    rw [lineMomentum₂_repV, regulatedAmplitude₂_repV, Fin.sum_univ_three, v_amplitude_eq _ hε',
      v_amplitude_eq _ hε', v_amplitude_eq _ hε', prod1, prod2, prod3, prod4, prod5]
    simp only [hv, i1, i2, i3, i4, i5, hc0, hc1, hc2, hm0, hm1, hm2, Complex.ofReal_one]
    have hfl := flavourSum_propDenom hε' (bm p ℓ 1) (bm p ℓ 2) hQ.pv₁ hQ.pv₂
      (seE0 Q α β (bm p ℓ 0) (bm p ℓ 1) (bm p ℓ 2)) (seE2 Q α β (bm p ℓ 0))
    have hu : propDenom Q.M₂ Q.ε (bm p ℓ 1) * (propDenom Q.M₂ Q.ε (bm p ℓ 1))⁻¹ = 1 :=
      mul_inv_cancel₀ (propDenom_ne_zero hε' _)
    have hw : propDenom Q.M₁ Q.ε (bm p ℓ 2) * (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ = 1 :=
      mul_inv_cancel₀ (propDenom_ne_zero hε' _)
    simp only [hF1, hF2, denR]
    linear_combination (κ * C * denR Q p ℓ) * hfl -
      (κ * C * K * seE2 Q α β (bm p ℓ 0) * denR Q p ℓ * (propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ *
        (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) * hu -
      (κ * C * K * seE2 Q α β (bm p ℓ 0) * denR Q p ℓ * (propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ *
        (propDenom Q.M₂ Q.ε (bm p ℓ 1))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) * hw
  simp only [key]
  obtain ⟨c1, c2, c3, c4, c5⟩ := crit_sh
  refine QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add ?_ ?_) ?_) ?_) ?_
  · exact jointEnergyFirstIntegrable_vPiece (by norm_num) sh1 (ms1 Q) hε p c1 hp1
      (hB1 sh1 rfl rfl rfl)
  · exact jointEnergyFirstIntegrable_vPiece (by norm_num) sh2 (ms2 Q) hε p c2 hp1
      (hB1 sh2 rfl rfl rfl)
  · exact jointEnergyFirstIntegrable_vPiece (by norm_num) sh3 (ms3 Q) hε p c3 hp1
      (hB1 sh3 rfl rfl rfl)
  · exact jointEnergyFirstIntegrable_vPiece (by norm_num) sh4 (ms4 Q) hε p c4 hp2 (hB2 sh4 rfl)
  · exact jointEnergyFirstIntegrable_vPiece (by norm_num) sh5 (ms5 Q) hε p c5 hp2 (hB2 sh5 rfl)

end QED.GradedProof.SE2

end
