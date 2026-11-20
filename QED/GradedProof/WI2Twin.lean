/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Slot

/-!
# Two electron slots around a middle matrix

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the class `F` (the `δ₂`, `δ_m` insertion on the internal electron line). Its numerator
is `twN = ∑ₗ cₗ Aₗ (m - k̸₀) G (m - k̸₁) Bₗ` with the electron numerators of two lines `e 0`, `e 1`
and a middle matrix `G` (the counterterm vertex) bounded by a third line `e₂`.

* `SEData.twE`, `twN`, `twQ` (`q̸ = (c_{e j} r)̸` in slot `j`), `twV` (the insertion
  `(m - k̸) q̸ (m - k̸)` in slot `j`), `twR` (the matrix `Y` in the middle): pointwise bounds and
  degrees; `twV_eq` (the insertion identity).
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2

/-- The bound of a product of five matrices with disjoint line sets. -/
theorem refinedBoundMat_five {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ}
    {S₀ S₂ S₁ : Finset (Fin (m + 1))} {k₀ k₂ k₁ : ℕ} (A B : Matrix (Fin 4) (Fin 4) ℂ)
    {X₀ G X₁ : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h₀ : RefinedBoundMat al S₀ k₀ X₀) (h₂ : RefinedBoundMat al S₂ k₂ G)
    (h₁ : RefinedBoundMat al S₁ k₁ X₁) (d₀₂ : Disjoint S₀ S₂) (d₁ : Disjoint (S₀ ∪ S₂) S₁) :
    RefinedBoundMat al (S₀ ∪ S₂ ∪ S₁) (k₀ + k₂ + k₁)
      fun ℓ => A * X₀ ℓ * G ℓ * X₁ ℓ * B := by
  have h := (((((RefinedBoundMat.const A).mul h₀ (Finset.disjoint_empty_left _)).mul h₂
    (by simpa using d₀₂)).mul h₁ (by simpa using d₁)).mul (RefinedBoundMat.const B)
      (Finset.disjoint_empty_right _))
  simpa using h

theorem refinedBound_tw_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {m : ℕ}
    {al : Fin (m + 1) → Fin 2 → ℝ} {S : Finset (Fin (m + 1))} {k : ℕ}
    {M : ι → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ l, RefinedBoundMat al S k (M l)) (a b : Fin 4) :
    RefinedBound al S k fun ℓ => (∑ l, c l • M l ℓ) a b := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact RefinedBound.sum _ fun l _ => (h l a b).const_mul _

theorem isLoopPoly_tw_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {L k : ℕ}
    {M : ι → (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ l, IsLoopPolyMat L k (M l)) (a b : Fin 4) :
    IsLoopPoly L k fun ℓ => (∑ l, c l • M l ℓ) a b := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact IsLoopPoly.sum _ fun l _ => (h l a b).const_mul _

variable (D : SEData) (e : Fin 2 → Fin (D.m + 1)) (mass : ℝ) {ι : Type*} [Fintype ι]
  (A B : ι → Matrix (Fin 4) (Fin 4) ℂ) (c : ι → ℂ)

/-- The two-slot product `∑ₗ cₗ Aₗ X₀ G X₁ Bₗ`. -/
noncomputable def tw (X : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ) (G : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l, c l • (A l * X 0 * G * X 1 * B l)

/-- The electron numerators of the lines `e j`. -/
noncomputable def twE (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Fin 2 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun j => electronNumerator mass (lineMomentum D.α (D.mom p) (e j) ℓ)

variable (G : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)

/-- The numerator `∑ₗ cₗ Aₗ (m - k̸₀) G (m - k̸₁) Bₗ`. -/
noncomputable def twN (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  tw A B c (D.twE e mass p ℓ) (G p ℓ)

/-- The numerator with `q̸ = (c_{e j} r)̸` in slot `j`. -/
noncomputable def twQ (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 2) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  tw A B c (Function.update (D.twE e mass p ℓ) j (Dirac.slash (D.mom r (e j)))) (G p ℓ)

/-- The numerator with the insertion `(m - k̸) q̸ (m - k̸)` in slot `j`. -/
noncomputable def twV (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 2) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  tw A B c (Function.update (D.twE e mass p ℓ) j
    (D.twE e mass p ℓ j * Dirac.slash (D.mom r (e j)) * D.twE e mass p ℓ j)) (G p ℓ)

/-- The numerator with the matrix `Y` in the middle. -/
noncomputable def twR (p : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  tw A B c (D.twE e mass p ℓ) Y

omit [Fintype ι] in
theorem tw_update_ins [Fintype ι] (X : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ)
    (Gm : Matrix (Fin 4) (Fin 4) ℂ) (j : Fin 2) (k q : Fin 4 → ℝ) :
    tw A B c (Function.update X j (electronNumerator mass k * Dirac.slash q *
        electronNumerator mass k)) Gm =
      ((Minkowski.dot k k + mass ^ 2 : ℝ) : ℂ) • tw A B c (Function.update X j (Dirac.slash q)) Gm
        + ((2 * Minkowski.dot q k : ℝ) : ℂ) •
          tw A B c (Function.update X j (electronNumerator mass k)) Gm := by
  simp only [electronNumerator]
  rw [numerator_slash_numerator]
  simp only [tw, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm _ (c l), smul_comm _ (c l), ← smul_add]
  congr 1
  fin_cases j <;> simp [Function.update, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- **The insertion identity** for the two-slot numerator. -/
theorem twV_eq (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 2) :
    D.twV e mass A B c G p r ℓ j =
      ((Minkowski.dot (lineMomentum D.α (D.mom p) (e j) ℓ)
          (lineMomentum D.α (D.mom p) (e j) ℓ) + mass ^ 2 : ℝ) : ℂ) • D.twQ e mass A B c G p r ℓ j +
      ((2 * Minkowski.dot (D.mom r (e j)) (lineMomentum D.α (D.mom p) (e j) ℓ) : ℝ) : ℂ) •
        D.twN e mass A B c G p ℓ := by
  rw [twV, show D.twE e mass p ℓ j = electronNumerator mass
    (lineMomentum D.α (D.mom p) (e j) ℓ) from rfl, tw_update_ins, ← show D.twE e mass p ℓ j =
    electronNumerator mass (lineMomentum D.α (D.mom p) (e j) ℓ) from rfl, Function.update_eq_self]
  rfl

section Bounds

variable {e₂ : Fin (D.m + 1)} (he : e 0 ≠ e 1) (h20 : e₂ ≠ e 0) (h21 : e₂ ≠ e 1)
  (hE : ∀ j, e j ∈ D.E) (hE2 : e₂ ∈ D.E) (hGb : ∀ p, RefinedBoundMat D.α {e₂} 1 (G p))

omit [Fintype ι] in
theorem refinedBoundMat_twE (p : Fin 4 → ℝ) (j : Fin 2) :
    RefinedBoundMat D.α {e j} 1 fun ℓ => D.twE e mass p ℓ j := fun a b =>
  refinedBound_electronNumerator D.α (D.mom p) (e j) mass a b

include he h20 h21 hE hE2 hGb

theorem refinedBound_twN (p : Fin 4 → ℝ) (a b : Fin 4) :
    RefinedBound D.α D.E 3 fun ℓ => D.twN e mass A B c G p ℓ a b := by
  refine (refinedBound_tw_sum c (S := {e 0} ∪ {e₂} ∪ {e 1}) (fun l =>
    refinedBoundMat_five (A l) (B l) (D.refinedBoundMat_twE e mass p 0) (hGb p)
      (D.refinedBoundMat_twE e mass p 1) (by simpa using h20.symm) (by simpa using
        ⟨he.symm, h21.symm⟩)) a b).mono ?_ le_rfl
  intro x hx
  simp only [Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl) | rfl
  exacts [hE 0, hE2, hE 1]

omit he in
theorem refinedBound_twQ (p r : Fin 4 → ℝ) (j : Fin 2) (a b : Fin 4) :
    RefinedBound D.α D.E 4 fun ℓ => D.twQ e mass A B c G p r ℓ j a b := by
  have hs : ∀ x ∈ ({e 0} ∪ {e₂} ∪ {e 1} : Finset _), x ∈ D.E := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl) | rfl
    exacts [hE 0, hE2, hE 1]
  have hS := RefinedBoundMat.const (al := D.α) (Dirac.slash (D.mom r (e j)))
  fin_cases j
  · refine (refinedBound_tw_sum c (S := ∅ ∪ {e₂} ∪ {e 1}) (fun l =>
      refinedBoundMat_five (A l) (B l) hS (hGb p) (D.refinedBoundMat_twE e mass p 1)
        (Finset.disjoint_empty_left _) (by simpa using h21)) a b).mono ?_ (by norm_num)
    intro x hx
    exact hs x (by simp only [Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty] at hx ⊢; tauto)
  · refine (refinedBound_tw_sum c (S := {e 0} ∪ {e₂} ∪ ∅) (fun l =>
      refinedBoundMat_five (A l) (B l) (D.refinedBoundMat_twE e mass p 0) (hGb p) hS
        (by simpa using h20.symm) (Finset.disjoint_empty_right _)) a b).mono ?_ (by norm_num)
    intro x hx
    exact hs x (by simp only [Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty] at hx ⊢; tauto)

omit h20 h21 hE2 hGb in
theorem refinedBound_twR (p : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    RefinedBound D.α D.E 4 fun ℓ => D.twR e mass A B c p Y ℓ a b := by
  refine (refinedBound_tw_sum c (S := {e 0} ∪ ∅ ∪ {e 1}) (fun l =>
    refinedBoundMat_five (A l) (B l) (D.refinedBoundMat_twE e mass p 0)
      (RefinedBoundMat.const Y) (D.refinedBoundMat_twE e mass p 1)
      (Finset.disjoint_empty_right _) (by simpa using he)) a b).mono ?_ (by norm_num)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false] at hx
  rcases hx with rfl | rfl
  exacts [hE 0, hE 1]

end Bounds

section Dbl

variable {e₂ : Fin (D.m + 1)} (he : e 0 ≠ e 1) (h20 : e₂ ≠ e 0) (h21 : e₂ ≠ e 1)
  (hE : ∀ j, e j ∈ D.E) (hE2 : e₂ ∈ D.E) (hGb : ∀ p, RefinedBoundMat D.α {e₂} 1 (G p))

omit [Fintype ι] in
theorem refinedBoundMat_twE_dbl (i : Fin (D.m + 1)) (p : Fin 4 → ℝ) (j : Fin 2) :
    RefinedBoundMat (dbl i D.α) {(e j).castSucc} 1 fun ℓ => D.twE e mass p ℓ j := fun a b => by
  have h : ∀ ℓ, D.twE e mass p ℓ j = electronNumerator mass
      (lineMomentum (dbl i D.α) (dbl i (D.mom p)) (e j).castSucc ℓ) := fun ℓ => by
    rw [lineMomentum_dbl, dblIdx_castSucc]
    rfl
  simp only [h]
  exact refinedBound_electronNumerator _ _ _ mass a b

omit [Fintype ι] in
theorem refinedBoundMat_twE_last (p : Fin 4 → ℝ) (j : Fin 2) :
    RefinedBoundMat (dbl (e j) D.α) {Fin.last (D.m + 1)} 1 fun ℓ => D.twE e mass p ℓ j :=
  fun a b => by
    have h : ∀ ℓ, D.twE e mass p ℓ j = electronNumerator mass
        (lineMomentum (dbl (e j) D.α) (dbl (e j) (D.mom p)) (Fin.last (D.m + 1)) ℓ) := fun ℓ => by
      rw [lineMomentum_dbl_last]
      rfl
    simp only [h]
    exact refinedBound_electronNumerator _ _ _ mass a b

omit [Fintype ι] in
theorem refinedBoundMat_twIns (p r : Fin 4 → ℝ) (j : Fin 2) :
    RefinedBoundMat (dbl (e j) D.α) ({(e j).castSucc} ∪ {Fin.last (D.m + 1)}) 2 fun ℓ =>
      D.twE e mass p ℓ j * Dirac.slash (D.mom r (e j)) * D.twE e mass p ℓ j := by
  have h := ((D.refinedBoundMat_twE_dbl e mass (e j) p j).mul
    (RefinedBoundMat.const (Dirac.slash (D.mom r (e j)))) (Finset.disjoint_empty_right _)).mul
      (D.refinedBoundMat_twE_last e mass p j) (by simp)
  simpa using h

include he h20 h21 hE hE2 hGb

theorem refinedBound_twV (p r : Fin 4 → ℝ) (j : Fin 2) (a b : Fin 4) :
    RefinedBound (dbl (e j) D.α) (dblLines D.E) 4 fun ℓ => D.twV e mass A B c G p r ℓ j a b := by
  have hG : ∀ i, RefinedBoundMat (dbl i D.α) {e₂.castSucc} 1 (G p) := fun i a b => by
    simpa using refinedBound_dbl_map (hGb p a b) i
  have hc : ∀ x ∈ D.E, x.castSucc ∈ dblLines D.E := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hx)
  have hl : Fin.last (D.m + 1) ∈ dblLines D.E := Finset.mem_insert_self _ _
  fin_cases j
  · refine (refinedBound_tw_sum c (S := ({(e 0).castSucc} ∪ {Fin.last (D.m + 1)}) ∪
      {e₂.castSucc} ∪ {(e 1).castSucc}) (fun l => refinedBoundMat_five (A l) (B l)
        (D.refinedBoundMat_twIns e mass p r 0) (hG (e 0))
        (D.refinedBoundMat_twE_dbl e mass (e 0) p 1) (by simp [h20])
        (by simp [Ne.symm he, Ne.symm h21])) a b).mono ?_ le_rfl
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with ((rfl | rfl) | rfl) | rfl
    exacts [hc _ (hE 0), hl, hc _ hE2, hc _ (hE 1)]
  · refine (refinedBound_tw_sum c (S := {(e 0).castSucc} ∪ {e₂.castSucc} ∪
      ({(e 1).castSucc} ∪ {Fin.last (D.m + 1)})) (fun l => refinedBoundMat_five (A l) (B l)
        (D.refinedBoundMat_twE_dbl e mass (e 1) p 0) (hG (e 1))
        (D.refinedBoundMat_twIns e mass p r 1) (by simp [Ne.symm h20])
        (by simp [Ne.symm he, Ne.symm h21, fun x => (Fin.castSucc_ne_last x).symm])) a b).mono ?_
          le_rfl
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with ((rfl | rfl) | rfl | rfl)
    exacts [hc _ (hE 0), hc _ hE2, hc _ (hE 1), hl]

end Dbl

section Degree

variable (hGp : ∀ p, IsLoopPolyMat 2 1 (G p))

omit [Fintype ι] in
theorem isLoopPolyMat_twE (p : Fin 4 → ℝ) (j : Fin 2) :
    IsLoopPolyMat 2 1 fun ℓ => D.twE e mass p ℓ j :=
  (isLoopAffine_lineMomentum D.α (D.mom p) (e j)).isLoopPolyMat_electronNumerator mass

include hGp

theorem isLoopPoly_twN (p : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.twN e mass A B c G p ℓ a b :=
  isLoopPoly_tw_sum c (fun l => by
    simpa using ((((IsLoopPolyMat.const (L := 2) (A l)).mul (D.isLoopPolyMat_twE e mass p 0)).mul
      (hGp p)).mul (D.isLoopPolyMat_twE e mass p 1)).mul (IsLoopPolyMat.const (B l))) a b

theorem isLoopPoly_twQ (p r : Fin 4 → ℝ) (j : Fin 2) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.twQ e mass A B c G p r ℓ j a b := by
  have hS := IsLoopPolyMat.const (L := 2) (Dirac.slash (D.mom r (e j)))
  fin_cases j
  · exact (isLoopPoly_tw_sum c (fun l => by
      simpa using ((((IsLoopPolyMat.const (L := 2) (A l)).mul hS).mul (hGp p)).mul
        (D.isLoopPolyMat_twE e mass p 1)).mul (IsLoopPolyMat.const (B l))) a b).mono
          (by norm_num)
  · exact (isLoopPoly_tw_sum c (fun l => by
      simpa using ((((IsLoopPolyMat.const (L := 2) (A l)).mul
        (D.isLoopPolyMat_twE e mass p 0)).mul (hGp p)).mul hS).mul
          (IsLoopPolyMat.const (B l))) a b).mono (by norm_num)

theorem isLoopPoly_twV (p r : Fin 4 → ℝ) (j : Fin 2) (a b : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => D.twV e mass A B c G p r ℓ j a b := by
  have hI := ((D.isLoopPolyMat_twE e mass p j).mul
    (IsLoopPolyMat.const (L := 2) (Dirac.slash (D.mom r (e j))))).mul
      (D.isLoopPolyMat_twE e mass p j)
  fin_cases j
  · exact isLoopPoly_tw_sum c (fun l => by
      simpa using ((((IsLoopPolyMat.const (L := 2) (A l)).mul hI).mul (hGp p)).mul
        (D.isLoopPolyMat_twE e mass p 1)).mul (IsLoopPolyMat.const (B l))) a b
  · exact isLoopPoly_tw_sum c (fun l => by
      simpa using ((((IsLoopPolyMat.const (L := 2) (A l)).mul
        (D.isLoopPolyMat_twE e mass p 0)).mul (hGp p)).mul hI).mul
          (IsLoopPolyMat.const (B l))) a b

omit hGp in
theorem isLoopPoly_twR (p : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.twR e mass A B c p Y ℓ a b :=
  (isLoopPoly_tw_sum c (fun l => by
    simpa using ((((IsLoopPolyMat.const (L := 2) (A l)).mul (D.isLoopPolyMat_twE e mass p 0)).mul
      (IsLoopPolyMat.const Y)).mul (D.isLoopPolyMat_twE e mass p 1)).mul
        (IsLoopPolyMat.const (B l))) a b).mono (by norm_num)

end Degree

theorem isLoopPoly_twN_mom (hGy : ∀ ℓ, IsLoopPolyMat 1 1 fun y => G (y 0) ℓ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 1 3 fun y => D.twN e mass A B c G (y 0) ℓ a b := by
  have hE : ∀ j, IsLoopPolyMat 1 1 fun y => D.twE e mass (y 0) ℓ j := fun j =>
    IsLoopAffine.isLoopPolyMat_electronNumerator ⟨![D.cs (e j)], lineMomentum D.α 0 (e j) ℓ,
      fun y => by
        funext μ
        simp [lineMomentum, mom]
        ring⟩ mass
  exact isLoopPoly_tw_sum c (fun l => by
    simpa using ((((IsLoopPolyMat.const (L := 1) (A l)).mul (hE 0)).mul (hGy ℓ)).mul
      (hE 1)).mul (IsLoopPolyMat.const (B l))) a b

end QED.GradedProof.SE2.SEData

end
