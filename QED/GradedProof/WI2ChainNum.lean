/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Chain
public import QED.GradedProof.WI2Ward
public import QED.GradedProof.SE2TwoLoopGggg
public import QED.TwoLoop.ClassIntegrableLoopPoly

/-!
# Open-chain numerators on self-energy data

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes `R` and `X`. On self-energy data `D` with three electron lines
`e : Fin 3 → lines`:

* `SEData.pvF`: the parametric value of a function of the loop momenta (that of any admissible
  quartic with these values, `SEData.pvF_eq`, else `0`).
* `SEData.chN`: the open chain with `m - k̸ₑⱼ` in slot `j`; `SEData.chQ`: the same with `q̸ⱼ`
  (`qⱼ = cₑⱼ r`) in slot `j`; `SEData.chV`: the same with the insertion `(m - k̸) q̸ⱼ (m - k̸)` in
  slot `j`.
* Their degrees and pointwise bounds: `chN` has degree three and is bounded by the electron lines;
  `chQ` has degree two; `chV` has degree four and is bounded on the data with line `e j` doubled,
  the second factor `m - k̸` carried by the new line.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2

variable (D : SEData)

/-- **The parametric value of a function** of the loop momenta: that of an admissible quartic with
these values, if there is one. -/
noncomputable def pvF (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (q : Fin (D.m + 1) → Fin 4 → ℝ) : ℂ := by
  classical
  exact if h : ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = F then D.pv h.choose q else 0

variable {D} in
theorem pvF_eq {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {Q : LoopQuartic} (hQ : D.Good Q)
    (he : Q.eval = F) {q : Fin (D.m + 1) → Fin 4 → ℝ} (hV : D.VPos q) : D.pvF F q = D.pv Q q := by
  have h : ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = F := ⟨Q, hQ, he⟩
  simp only [pvF, h, ↓reduceDIte]
  exact pv_unique h.choose_spec.1 hQ (h.choose_spec.2.trans he.symm) hV

variable (e : Fin 3 → Fin (D.m + 1)) (w : (Fin 4 → Fin 4) → ℂ) (mass : ℝ)

/-- The electron numerators `m - k̸ₑⱼ` at the external momentum `p`. -/
noncomputable def chE (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Fin 3 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun j => electronNumerator mass (lineMomentum D.α (D.mom p) (e j) ℓ)

/-- The open chain with the electron numerators. -/
noncomputable def chN (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  chainAt w (D.chE e mass p ℓ)

/-- The open chain with `q̸ⱼ = (cₑⱼ r)̸` in slot `j`. -/
noncomputable def chQ (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 3) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  chainAt w (Function.update (D.chE e mass p ℓ) j (Dirac.slash (D.mom r (e j))))

/-- The open chain with the insertion `(m - k̸) q̸ⱼ (m - k̸)` in slot `j`. -/
noncomputable def chV (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 3) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  chainAt w (Function.update (D.chE e mass p ℓ) j
    (D.chE e mass p ℓ j * Dirac.slash (D.mom r (e j)) * D.chE e mass p ℓ j))

variable {e}

theorem disjoint_singleton_of_injective (he : Function.Injective e) (j₁ j₂ : Fin 3)
    (h : j₁ ≠ j₂) : Disjoint ({e j₁} : Finset (Fin (D.m + 1))) {e j₂} :=
  Finset.disjoint_singleton.mpr fun h' => h (he h')

theorem union_image_subset (hE : ∀ j, e j ∈ D.E) :
    ({e 2} ∪ {e 1} ∪ {e 0} : Finset (Fin (D.m + 1))) ⊆ D.E := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl) | rfl <;> exact hE _

theorem refinedBound_chN (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E) (p : Fin 4 → ℝ)
    (a b : Fin 4) : RefinedBound D.α D.E 3 fun ℓ => D.chN e w mass p ℓ a b := by
  have h := refinedBoundMat_chainAt (al := D.α) w (F := fun ℓ => D.chE e mass p ℓ)
    (S := fun j => {e j}) (d := fun _ => 1)
    (fun j a b => refinedBound_electronNumerator D.α (D.mom p) (e j) mass a b)
    (D.disjoint_singleton_of_injective he)
  exact (h a b).mono (D.union_image_subset hE) le_rfl

theorem isLoopPoly_chN (p : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.chN e w mass p ℓ a b :=
  isLoopPolyMat_chainAt w (L := 2) (F := fun ℓ => D.chE e mass p ℓ) (d := fun _ => 1)
    (fun j => (isLoopAffine_lineMomentum D.α (D.mom p) (e j)).isLoopPolyMat_electronNumerator
      mass) a b

theorem isLoopPoly_chN_mom (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 1 3 fun y => D.chN e w mass (y 0) ℓ a b := by
  refine isLoopPolyMat_chainAt w (L := 1) (F := fun y => D.chE e mass (y 0) ℓ)
    (d := fun _ => 1) (fun j => IsLoopAffine.isLoopPolyMat_electronNumerator ?_ mass) a b
  exact ⟨![D.cs (e j)], lineMomentum D.α 0 (e j) ℓ, fun y => by
    funext μ
    simp [lineMomentum, mom]
    ring⟩

theorem good_chN (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E) (p : Fin 4 → ℝ)
    (a b : Fin 4) : ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧
      Q.eval = fun ℓ => D.chN e w mass p ℓ a b := by
  obtain ⟨Q, hq, hQ⟩ := IsLoopPoly.exists_loopQuartic_cubic (D.isLoopPoly_chN w mass p a b)
  refine ⟨Q, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
  rw [hQ]
  exact (D.refinedBound_chN w mass he hE p a b).mono subset_rfl (by norm_num)

theorem union_subset_of_forall {n : ℕ} {S : Fin 3 → Finset (Fin n)} {T : Finset (Fin n)}
    (h : ∀ j, S j ⊆ T) : S 2 ∪ S 1 ∪ S 0 ⊆ T :=
  Finset.union_subset (Finset.union_subset (h 2) (h 1)) (h 0)

theorem refinedBound_chQ (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E) (p r : Fin 4 → ℝ)
    (j : Fin 3) (a b : Fin 4) : RefinedBound D.α D.E 4 fun ℓ => D.chQ e w mass p r ℓ j a b := by
  have h := refinedBoundMat_chainAt (al := D.α) w
    (F := fun ℓ => Function.update (D.chE e mass p ℓ) j (Dirac.slash (D.mom r (e j))))
    (S := Function.update (fun j => {e j}) j ∅) (d := Function.update (fun _ => 1) j 0)
    (fun j' => ?_) (fun j₁ j₂ h12 => ?_)
  · refine (h a b).mono (union_subset_of_forall fun j' => ?_) ?_
    · by_cases hj : j' = j
      · subst hj
        simp
      · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne,
          Finset.singleton_subset_iff]
        exact hE j'
    · fin_cases j <;> simp
  · by_cases hj : j' = j
    · subst hj
      simp only [Function.update_self]
      exact RefinedBoundMat.const _
    · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]
      exact fun a b => refinedBound_electronNumerator D.α (D.mom p) (e j') mass a b
  · by_cases h1 : j₁ = j
    · subst h1
      simp
    · by_cases h2 : j₂ = j
      · subst h2
        simp
      · simp only [ne_eq, h1, h2, not_false_eq_true, Function.update_of_ne]
        exact D.disjoint_singleton_of_injective he j₁ j₂ h12

theorem isLoopPoly_chQ (p r : Fin 4 → ℝ) (j : Fin 3) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.chQ e w mass p r ℓ j a b := by
  refine isLoopPolyMat_chainAt w (L := 2)
    (F := fun ℓ => Function.update (D.chE e mass p ℓ) j (Dirac.slash (D.mom r (e j))))
    (d := fun _ => 1) (fun j' => ?_) a b
  by_cases hj : j' = j
  · subst hj
    simp only [Function.update_self]
    exact fun _ _ => IsLoopPoly.const _
  · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]
    exact (isLoopAffine_lineMomentum D.α (D.mom p) (e j')).isLoopPolyMat_electronNumerator mass

theorem good_chQ (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E) (p r : Fin 4 → ℝ)
    (j : Fin 3) (a b : Fin 4) : ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧
      Q.eval = fun ℓ => D.chQ e w mass p r ℓ j a b := by
  obtain ⟨Q, hq, hQ⟩ := IsLoopPoly.exists_loopQuartic_cubic (D.isLoopPoly_chQ w mass p r j a b)
  refine ⟨Q, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
  rw [hQ]
  exact D.refinedBound_chQ w mass he hE p r j a b

theorem chE_dbl (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (i : Fin (D.m + 1)) (j : Fin 3) :
    D.chE e mass p ℓ j =
      electronNumerator mass (lineMomentum (dbl i D.α) (dbl i (D.mom p)) (e j).castSucc ℓ) := by
  rw [lineMomentum_dbl, dblIdx_castSucc]
  rfl

theorem chE_dbl_last (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 3) :
    D.chE e mass p ℓ j = electronNumerator mass
      (lineMomentum (dbl (e j) D.α) (dbl (e j) (D.mom p)) (Fin.last (D.m + 1)) ℓ) := by
  rw [lineMomentum_dbl_last]
  rfl

theorem refinedBound_chV (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E) (p r : Fin 4 → ℝ)
    (j : Fin 3) (a b : Fin 4) :
    RefinedBound (dbl (e j) D.α) (dblLines D.E) 4 fun ℓ => D.chV e w mass p r ℓ j a b := by
  set i := e j
  have hslot : RefinedBoundMat (dbl i D.α) ({(e j).castSucc} ∪ {Fin.last (D.m + 1)}) 2
      fun ℓ => D.chE e mass p ℓ j * Dirac.slash (D.mom r (e j)) * D.chE e mass p ℓ j := by
    have h1 : RefinedBoundMat (dbl i D.α) {(e j).castSucc} 1 fun ℓ => D.chE e mass p ℓ j :=
      fun a b => by
        simp only [D.chE_dbl mass p _ i j]
        exact refinedBound_electronNumerator _ _ _ mass a b
    have h2 : RefinedBoundMat (dbl i D.α) {Fin.last (D.m + 1)} 1
        fun ℓ => D.chE e mass p ℓ j := fun a b => by
      simp only [D.chE_dbl_last mass p _ j]
      exact refinedBound_electronNumerator _ _ _ mass a b
    have h := (h1.mul (RefinedBoundMat.const (Dirac.slash (D.mom r (e j))))
      (Finset.disjoint_empty_right _)).mul h2 (by simp)
    simpa using h
  have h := refinedBoundMat_chainAt (al := dbl i D.α) w
    (F := fun ℓ => Function.update (D.chE e mass p ℓ) j
      (D.chE e mass p ℓ j * Dirac.slash (D.mom r (e j)) * D.chE e mass p ℓ j))
    (S := Function.update (fun j => {(e j).castSucc}) j
      ({(e j).castSucc} ∪ {Fin.last (D.m + 1)}))
    (d := Function.update (fun _ => 1) j 2) (fun j' => ?_) (fun j₁ j₂ h12 => ?_)
  · refine (h a b).mono (union_subset_of_forall fun j' => ?_) ?_
    · have hc : ∀ k, (e k).castSucc ∈ dblLines D.E := fun k =>
        Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ (hE k))
      by_cases hj : j' = j
      · subst hj
        simp only [Function.update_self, Finset.union_subset_iff,
          Finset.singleton_subset_iff]
        exact ⟨hc _, Finset.mem_insert_self _ _⟩
      · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne,
          Finset.singleton_subset_iff]
        exact hc j'
    · fin_cases j <;> simp
  · by_cases hj : j' = j
    · subst hj
      simp only [Function.update_self]
      exact hslot
    · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]
      exact fun a b => by
        simp only [D.chE_dbl mass p _ i j']
        exact refinedBound_electronNumerator _ _ _ mass a b
  · have hne : ∀ k₁ k₂ : Fin 3, k₁ ≠ k₂ → (e k₁).castSucc ≠ (e k₂).castSucc := fun k₁ k₂ h h' =>
      h (he (Fin.castSucc_injective _ h'))
    have hl : ∀ k : Fin 3, (e k).castSucc ≠ Fin.last (D.m + 1) := fun k => Fin.castSucc_ne_last _
    by_cases h1 : j₁ = j
    · subst h1
      have h2 : j₂ ≠ j₁ := fun h => h12 h.symm
      simp only [Function.update_self, ne_eq, h2, not_false_eq_true, Function.update_of_ne,
        Finset.disjoint_union_left, Finset.disjoint_singleton]
      exact ⟨hne _ _ h12, fun h => hl j₂ h.symm⟩
    · by_cases h2 : j₂ = j
      · subst h2
        simp only [Function.update_self, ne_eq, h1, not_false_eq_true, Function.update_of_ne,
          Finset.disjoint_union_right, Finset.disjoint_singleton]
        exact ⟨hne _ _ h12, hl j₁⟩
      · simp only [ne_eq, h1, h2, not_false_eq_true, Function.update_of_ne,
          Finset.disjoint_singleton]
        exact hne _ _ h12

theorem isLoopPoly_chV (p r : Fin 4 → ℝ) (j : Fin 3) (a b : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => D.chV e w mass p r ℓ j a b := by
  have hE : ∀ k, IsLoopPolyMat 2 1 fun ℓ => D.chE e mass p ℓ k := fun k =>
    (isLoopAffine_lineMomentum D.α (D.mom p) (e k)).isLoopPolyMat_electronNumerator mass
  have h := isLoopPolyMat_chainAt w (L := 2)
    (F := fun ℓ => Function.update (D.chE e mass p ℓ) j
      (D.chE e mass p ℓ j * Dirac.slash (D.mom r (e j)) * D.chE e mass p ℓ j))
    (d := Function.update (fun _ => 1) j 2) (fun j' => ?_)
  · have hd : (Function.update (fun _ => 1) j 2 : Fin 3 → ℕ) 2 +
        Function.update (fun _ => 1) j 2 1 + Function.update (fun _ => 1) j 2 0 = 4 := by
      fin_cases j <;> simp
    rw [hd] at h
    exact h a b
  · by_cases hj : j' = j
    · subst hj
      simp only [Function.update_self]
      simpa using ((hE j').mul (IsLoopPolyMat.const _)).mul (hE j')
    · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]
      exact hE j'

theorem good_chV (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E) (p r : Fin 4 → ℝ)
    (j : Fin 3) (a b : Fin 4) : ∃ Q : LoopQuartic, (D.dup (e j)).Good Q ∧
      Q.eval = fun ℓ => D.chV e w mass p r ℓ j a b := by
  obtain ⟨Q, hQ⟩ := IsLoopPoly.exists_loopQuartic (D.isLoopPoly_chV w mass p r j a b)
  refine ⟨Q, ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega), ?_⟩, hQ⟩
  rw [hQ]
  exact D.refinedBound_chV w mass he hE p r j a b

end QED.GradedProof.SE2.SEData

end
