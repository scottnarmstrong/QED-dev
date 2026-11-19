/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2TwoLoopGggg

/-!
# The classes `R` and `X`: the two-loop rainbow and crossed self-energies

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. The representatives `repR`, `repX` of
`QED/GradedProof/SE2Classes.lean` have four `gauge` vertices `0, 1, 2, 3` on the open electron
line `0 → 1 → 2 → 3` and two photon lines, `(0 3) (1 2)` for `R` and `(0 2) (1 3)` for `X`. For
each:

* the lines, their ends, the two chords (T₁) and their loop momenta (T₃), checked by
  `decide +kernel`;
* an explicit conserved routing given by an integer loop matrix for seven parametric lines (the
  three electron lines and the two Pauli–Villars photon pairs), which is therefore the frozen
  routing (T₄);
* the amplitude denominators as the product of the seven line denominators, and the decidable
  numerator-aware criterion;
* the class obligation `ClassInt` (`classInt_repR`, `classInt_repX`), from
  `QED.GradedProof.SE2.jointEnergyFirstIntegrable_gggg`.

The chords are the electron lines `0 → 1` and `1 → 2`, carrying `ℓ₀` and `ℓ₁`. For `R` the line
momenta are `ℓ₀, ℓ₁, ℓ₀` on the electron lines and `p - ℓ₀`, `ℓ₀ - ℓ₁` on the photon lines; for
`X` they are `ℓ₀, ℓ₁, p - ℓ₀ + ℓ₁` and `p - ℓ₀`, `ℓ₀ - ℓ₁`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix IntNoSubdivergenceRefined)
open Complex MeasureTheory

/-! ### The rainbow `R` -/

section R

/-- The electron line `0 → 1` of `repR`. -/
def rf1 : FermionLine repR := ⟨fvK k_gggg 1, by decide +kernel⟩
/-- The electron line `1 → 2` of `repR`. -/
def rf2 : FermionLine repR := ⟨fvK k_gggg 2, by decide +kernel⟩
/-- The electron line `2 → 3` of `repR`. -/
def rf3 : FermionLine repR := ⟨fvK k_gggg 3, by decide +kernel⟩
/-- The photon line `0 → 3` of `repR`. -/
def rg1 : PhotonLine repR := ⟨psK k_gggg 0 0, by decide +kernel⟩
/-- The photon line `1 → 2` of `repR`. -/
def rg2 : PhotonLine repR := ⟨psK k_gggg 1 0, by decide +kernel⟩

theorem r_fermionLine_cases : ∀ f : FermionLine repR, f = rf1 ∨ f = rf2 ∨ f = rf3 := by
  decide +kernel

theorem r_photonLine_cases : ∀ g : PhotonLine repR, g = rg1 ∨ g = rg2 := by decide +kernel

theorem r_fermion_ne : rf1 ≠ rf2 ∧ rf1 ≠ rf3 ∧ rf2 ≠ rf3 ∧ rg1 ≠ rg2 := by decide +kernel

theorem r_line_cases (f : Line repR) :
    f = .inl rf1 ∨ f = .inl rf2 ∨ f = .inl rf3 ∨ f = .inr rg1 ∨ f = .inr rg2 := by
  rcases f with f | g
  · rcases r_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases r_photonLine_cases g with rfl | rfl <;> simp

theorem r_isChord_iff (g : Line repR) : IsChord g ↔ g = .inl rf1 ∨ g = .inl rf2 := by
  have c1 : IsChord (.inl rf1 : Line repR) := by decide +kernel
  have c2 : IsChord (.inl rf2 : Line repR) := by decide +kernel
  have c3 : ¬ IsChord (.inl rf3 : Line repR) := by decide +kernel
  have c4 : ¬ IsChord (.inr rg1 : Line repR) := by decide +kernel
  have c5 : ¬ IsChord (.inr rg2 : Line repR) := by decide +kernel
  obtain ⟨n12, n13, n23, -⟩ := r_fermion_ne
  rcases r_line_cases g with rfl | rfl | rfl | rfl | rfl
  · simp [c1]
  · simp [c2]
  · simp [c3, n13.symm, n23.symm]
  · simp [c4]
  · simp [c5]

theorem r_ends : (Line.ends (.inl rf1 : Line repR)) = (0, 1) ∧
    (Line.ends (.inl rf2 : Line repR)) = (1, 2) ∧ (Line.ends (.inl rf3 : Line repR)) = (2, 3) ∧
    (Line.ends (.inr rg1 : Line repR)) = (0, 3) ∧ (Line.ends (.inr rg2 : Line repR)) = (1, 2) := by
  decide +kernel

theorem r_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggg, t.1 = v ∧ repR.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_gggg, t.1 = v ∧ repR.1.1 (.inl 0) = .inr t) ↔ v = 3) := by
  revert v
  decide +kernel

open scoped Classical in
theorem r_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl rf1 : Line repR) = ℓ 0 ∧
      chordMomentum ℓ (.inl rf2 : Line repR) = ℓ 1 := by
  have l1 : (Line.label (.inl rf1 : Line repR)) = 1 := rfl
  have l2 : (Line.label (.inl rf2 : Line repR)) = 2 := rfl
  have h0 : (Finset.univ.filter fun g : Line repR =>
      IsChord g ∧ g.label < (Line.label (.inl rf1 : Line repR))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (r_isChord_iff g).mp hg with rfl | rfl
    · simp at hl
    · simp [l1, l2] at hl
  have h1 : (Finset.univ.filter fun g : Line repR =>
      IsChord g ∧ g.label < (Line.label (.inl rf2 : Line repR))).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨.inl rf1, Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (r_isChord_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(r_isChord_iff _).mpr (Or.inl rfl), by simp [l1, l2]⟩
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

/-- The loop matrix of `R`: electron lines `ℓ₀, ℓ₁, ℓ₀`, photon pairs `-ℓ₀`, `ℓ₀ - ℓ₁`. -/
def aR : Fin 7 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![1, 0], ![-1, 0], ![-1, 0], ![1, -1], ![1, -1]]

/-- The external momenta of the lines of `R`. -/
def ppR (p : Fin 4 → ℝ) : Fin 7 → Fin 4 → ℝ := ![0, 0, 0, p, p, 0, 0]

theorem intCrit_R : IntNoSubdivergenceRefined 2 {0, 1, 2} aR := by decide

/-- The parametric line of each line of `R`. -/
def idxR (f : Line repR) : Fin 7 :=
  if f = .inl rf1 then 0 else if f = .inl rf2 then 1 else if f = .inl rf3 then 2 else
    if f = .inr rg1 then 3 else 5

theorem idxR_apply : idxR (.inl rf1) = 0 ∧ idxR (.inl rf2) = 1 ∧ idxR (.inl rf3) = 2 ∧
    idxR (.inr rg1) = 3 ∧ idxR (.inr rg2) = 5 := by
  decide +kernel

/-- The routing of `R`. -/
def rMom (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repR) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix aR) (ppR p) (idxR f) ℓ

theorem rMom_apply (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    rMom p ℓ (.inl rf1) = ℓ 0 ∧ rMom p ℓ (.inl rf2) = ℓ 1 ∧ rMom p ℓ (.inl rf3) = ℓ 0 ∧
      rMom p ℓ (.inr rg1) = p - ℓ 0 ∧ rMom p ℓ (.inr rg2) = ℓ 0 - ℓ 1 := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := idxR_apply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [rMom, i1, i2, i3, i4, i5, QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, aR,
      ppR, Fin.sum_univ_two] <;>
    ring

theorem r_isConserved (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved repR ![p] ![p] ![] (rMom p ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := r_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := rMom_apply p ℓ
  obtain ⟨n12, n13, n23, n45⟩ := r_fermion_ne
  intro v
  rw [inflow, Fintype.sum_sum_type, sum_eq_of_three n12 n13 n23 r_fermionLine_cases,
    sum_eq_of_two n45 r_photonLine_cases, externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := r_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, m1, m2, m3, m4, m5, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> simp <;> ring

theorem lineMomentum₂_repR (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repR ![p] ![p] ![] ℓ = rMom p ℓ := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (r_isConserved p ℓ) (fun g hg => ?_) f).symm
  obtain ⟨c1, c2⟩ := r_chordMomentum ℓ
  obtain ⟨m1, m2, -, -, -⟩ := rMom_apply p ℓ
  rcases (r_isChord_iff g).mp hg with rfl | rfl
  · rw [c1, m1]
  · rw [c2, m2]

theorem r_denominator (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator Q repR (zeroFlavoring k_gggg) (lineMomentum₂ repR ![p] ![p] ![] ℓ) =
      ∏ i, (lineDenom (castLoopMatrix aR) (ppR p) (massesSE Q) Q.ε i ℓ)⁻¹ := by
  obtain ⟨n12, n13, n23, n45⟩ := r_fermion_ne
  obtain ⟨i1, i2, i3, i4, i5⟩ := idxR_apply
  rw [lineMomentum₂_repR, amplitudeDenominator,
    prod_eq_of_three n12 n13 n23 r_fermionLine_cases, prod_eq_of_two n45 r_photonLine_cases,
    Fin.prod_univ_seven]
  simp only [lineDenom_eq_propDenom, rMom, i1, i2, i3, i4, i5]
  have h4 : lineMomentum (castLoopMatrix aR) (ppR p) 4 ℓ =
      lineMomentum (castLoopMatrix aR) (ppR p) 3 ℓ := by
    funext μ
    simp [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, aR, ppR]
  have h6 : lineMomentum (castLoopMatrix aR) (ppR p) 6 ℓ =
      lineMomentum (castLoopMatrix aR) (ppR p) 5 ℓ := by
    funext μ
    simp [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, aR, ppR]
  rw [h4, h6]
  simp only [massesSE, QED.TwoLoop.Insertion.zeroFlavoring, Params.mass]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- **The class obligation for `R`.** -/
theorem classInt_repR : ClassInt repR := by
  intro Q hQ p α β
  obtain ⟨i1, i2, i3, -, -⟩ := idxR_apply
  refine jointEnergyFirstIntegrable_gggg repR (sameCycle_of_pow (n := 5) (by decide +kernel))
    loopCount_repR (by decide +kernel) aR intCrit_R Q hQ.hε p (ppR p)
    (fun f => idxR (.inl f)) ?_ ?_ (fun ℓ f => by rw [lineMomentum₂_repR]; rfl)
    (r_denominator Q p) α β
  · intro f g h
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases r_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

end R

/-! ### The crossed graph `X` -/

section X

/-- The electron line `0 → 1` of `repX`. -/
def xf1 : FermionLine repX := ⟨fvK k_gggg 1, by decide +kernel⟩
/-- The electron line `1 → 2` of `repX`. -/
def xf2 : FermionLine repX := ⟨fvK k_gggg 2, by decide +kernel⟩
/-- The electron line `2 → 3` of `repX`. -/
def xf3 : FermionLine repX := ⟨fvK k_gggg 3, by decide +kernel⟩
/-- The photon line `0 → 2` of `repX`. -/
def xg1 : PhotonLine repX := ⟨psK k_gggg 0 0, by decide +kernel⟩
/-- The photon line `1 → 3` of `repX`. -/
def xg2 : PhotonLine repX := ⟨psK k_gggg 1 0, by decide +kernel⟩

theorem x_fermionLine_cases : ∀ f : FermionLine repX, f = xf1 ∨ f = xf2 ∨ f = xf3 := by
  decide +kernel

theorem x_photonLine_cases : ∀ g : PhotonLine repX, g = xg1 ∨ g = xg2 := by decide +kernel

theorem x_fermion_ne : xf1 ≠ xf2 ∧ xf1 ≠ xf3 ∧ xf2 ≠ xf3 ∧ xg1 ≠ xg2 := by decide +kernel

theorem x_line_cases (f : Line repX) :
    f = .inl xf1 ∨ f = .inl xf2 ∨ f = .inl xf3 ∨ f = .inr xg1 ∨ f = .inr xg2 := by
  rcases f with f | g
  · rcases x_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases x_photonLine_cases g with rfl | rfl <;> simp

theorem x_isChord_iff (g : Line repX) : IsChord g ↔ g = .inl xf1 ∨ g = .inl xf2 := by
  have c1 : IsChord (.inl xf1 : Line repX) := by decide +kernel
  have c2 : IsChord (.inl xf2 : Line repX) := by decide +kernel
  have c3 : ¬ IsChord (.inl xf3 : Line repX) := by decide +kernel
  have c4 : ¬ IsChord (.inr xg1 : Line repX) := by decide +kernel
  have c5 : ¬ IsChord (.inr xg2 : Line repX) := by decide +kernel
  obtain ⟨n12, n13, n23, -⟩ := x_fermion_ne
  rcases x_line_cases g with rfl | rfl | rfl | rfl | rfl
  · simp [c1]
  · simp [c2]
  · simp [c3, n13.symm, n23.symm]
  · simp [c4]
  · simp [c5]

theorem x_ends : (Line.ends (.inl xf1 : Line repX)) = (0, 1) ∧
    (Line.ends (.inl xf2 : Line repX)) = (1, 2) ∧ (Line.ends (.inl xf3 : Line repX)) = (2, 3) ∧
    (Line.ends (.inr xg1 : Line repX)) = (0, 2) ∧ (Line.ends (.inr xg2 : Line repX)) = (1, 3) := by
  decide +kernel

theorem x_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggg, t.1 = v ∧ repX.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_gggg, t.1 = v ∧ repX.1.1 (.inl 0) = .inr t) ↔ v = 3) := by
  revert v
  decide +kernel

open scoped Classical in
theorem x_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl xf1 : Line repX) = ℓ 0 ∧
      chordMomentum ℓ (.inl xf2 : Line repX) = ℓ 1 := by
  have l1 : (Line.label (.inl xf1 : Line repX)) = 1 := rfl
  have l2 : (Line.label (.inl xf2 : Line repX)) = 2 := rfl
  have h0 : (Finset.univ.filter fun g : Line repX =>
      IsChord g ∧ g.label < (Line.label (.inl xf1 : Line repX))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (x_isChord_iff g).mp hg with rfl | rfl
    · simp at hl
    · simp [l1, l2] at hl
  have h1 : (Finset.univ.filter fun g : Line repX =>
      IsChord g ∧ g.label < (Line.label (.inl xf2 : Line repX))).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨.inl xf1, Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (x_isChord_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(x_isChord_iff _).mpr (Or.inl rfl), by simp [l1, l2]⟩
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

/-- The loop matrix of `X`: electron lines `ℓ₀, ℓ₁, -ℓ₀ + ℓ₁`, photon pairs `-ℓ₀`, `ℓ₀ - ℓ₁`. -/
def aX : Fin 7 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![-1, 1], ![-1, 0], ![-1, 0], ![1, -1], ![1, -1]]

/-- The external momenta of the lines of `X`. -/
def ppX (p : Fin 4 → ℝ) : Fin 7 → Fin 4 → ℝ := ![0, 0, p, p, p, 0, 0]

theorem intCrit_X : IntNoSubdivergenceRefined 2 {0, 1, 2} aX := by decide

/-- The parametric line of each line of `X`. -/
def idxX (f : Line repX) : Fin 7 :=
  if f = .inl xf1 then 0 else if f = .inl xf2 then 1 else if f = .inl xf3 then 2 else
    if f = .inr xg1 then 3 else 5

theorem idxX_apply : idxX (.inl xf1) = 0 ∧ idxX (.inl xf2) = 1 ∧ idxX (.inl xf3) = 2 ∧
    idxX (.inr xg1) = 3 ∧ idxX (.inr xg2) = 5 := by
  decide +kernel

/-- The routing of `X`. -/
def xMom (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repX) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix aX) (ppX p) (idxX f) ℓ

theorem xMom_apply (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    xMom p ℓ (.inl xf1) = ℓ 0 ∧ xMom p ℓ (.inl xf2) = ℓ 1 ∧ xMom p ℓ (.inl xf3) = p - ℓ 0 + ℓ 1 ∧
      xMom p ℓ (.inr xg1) = p - ℓ 0 ∧ xMom p ℓ (.inr xg2) = ℓ 0 - ℓ 1 := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := idxX_apply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [xMom, i1, i2, i3, i4, i5, QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, aX,
      ppX, Fin.sum_univ_two] <;>
    ring

theorem x_isConserved (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved repX ![p] ![p] ![] (xMom p ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := x_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := xMom_apply p ℓ
  obtain ⟨n12, n13, n23, n45⟩ := x_fermion_ne
  intro v
  rw [inflow, Fintype.sum_sum_type, sum_eq_of_three n12 n13 n23 x_fermionLine_cases,
    sum_eq_of_two n45 x_photonLine_cases, externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := x_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, m1, m2, m3, m4, m5, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> simp <;> ring

theorem lineMomentum₂_repX (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repX ![p] ![p] ![] ℓ = xMom p ℓ := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (x_isConserved p ℓ) (fun g hg => ?_) f).symm
  obtain ⟨c1, c2⟩ := x_chordMomentum ℓ
  obtain ⟨m1, m2, -, -, -⟩ := xMom_apply p ℓ
  rcases (x_isChord_iff g).mp hg with rfl | rfl
  · rw [c1, m1]
  · rw [c2, m2]

theorem x_denominator (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator Q repX (zeroFlavoring k_gggg) (lineMomentum₂ repX ![p] ![p] ![] ℓ) =
      ∏ i, (lineDenom (castLoopMatrix aX) (ppX p) (massesSE Q) Q.ε i ℓ)⁻¹ := by
  obtain ⟨n12, n13, n23, n45⟩ := x_fermion_ne
  obtain ⟨i1, i2, i3, i4, i5⟩ := idxX_apply
  rw [lineMomentum₂_repX, amplitudeDenominator,
    prod_eq_of_three n12 n13 n23 x_fermionLine_cases, prod_eq_of_two n45 x_photonLine_cases,
    Fin.prod_univ_seven]
  simp only [lineDenom_eq_propDenom, xMom, i1, i2, i3, i4, i5]
  have h4 : lineMomentum (castLoopMatrix aX) (ppX p) 4 ℓ =
      lineMomentum (castLoopMatrix aX) (ppX p) 3 ℓ := by
    funext μ
    simp [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, aX, ppX]
  have h6 : lineMomentum (castLoopMatrix aX) (ppX p) 6 ℓ =
      lineMomentum (castLoopMatrix aX) (ppX p) 5 ℓ := by
    funext μ
    simp [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, aX, ppX]
  rw [h4, h6]
  simp only [massesSE, QED.TwoLoop.Insertion.zeroFlavoring, Params.mass]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- **The class obligation for `X`.** -/
theorem classInt_repX : ClassInt repX := by
  intro Q hQ p α β
  obtain ⟨i1, i2, i3, -, -⟩ := idxX_apply
  refine jointEnergyFirstIntegrable_gggg repX (sameCycle_of_pow (n := 5) (by decide +kernel))
    loopCount_repX (by decide +kernel) aX intCrit_X Q hQ.hε p (ppX p)
    (fun f => idxX (.inl f)) ?_ ?_ (fun ℓ f => by rw [lineMomentum₂_repX]; rfl)
    (x_denominator Q p) α β
  · intro f g h
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases x_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

end X

end QED.GradedProof.SE2

end
