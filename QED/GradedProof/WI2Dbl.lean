/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Merge
public import QED.GradedProof.SE2ParamPiece

/-!
# The doubled-line parametric data

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A3′. Doubling line `i` (`dbl i`, the line appended as a last line) with the new line added to
the numerator lines (`dblLines E`):

* `noSubdivergenceRefined_dbl`: the refined criterion survives. For a row in the direction class of
  line `i` nothing changes; for any other row the new line adds one to the number of lines outside
  the class and at most one to the numerator lines outside it, and `2k + e + 1 < 2n + 2` follows
  from `2k + e < 2n`;
* `lineWeight_dbl`, `refinedBound_dbl_map`, `refinedBound_dLine`: the old numerator keeps its
  bound, and the derivative `2 kᵢ(ℓ)·qᵢ` of the line denominator is bounded by the new line;
* `SEData.dup`: the doubled data as self-energy data, with `mom` doubled (`SEData.dup_mom`), and
  positivity of `V` transferred (`SEData.VPos.dup`, through `splitAt`);
* `SEData.good_mulLin`: the insertion numerator `P · (2 kᵢ·qᵢ)` of a cubic `P` with exponent three
  is admissible on the doubled data.
-/

@[expose] public section

open Complex MeasureTheory Matrix

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.Minkowski

variable {m : ℕ}

/-- The line of the undoubled data read by each line of the doubled data. -/
def dblIdx (i : Fin (m + 1)) : Fin (m + 2) → Fin (m + 1) :=
  Fin.snoc (α := fun _ => Fin (m + 1)) id i

@[simp] theorem dblIdx_castSucc (i j : Fin (m + 1)) : dblIdx i j.castSucc = j := by
  simp [dblIdx]

@[simp] theorem dblIdx_last (i : Fin (m + 1)) : dblIdx i (Fin.last (m + 1)) = i := by
  simp [dblIdx]

theorem dbl_apply {β : Type*} (i : Fin (m + 1)) (f : Fin (m + 1) → β) (j : Fin (m + 2)) :
    dbl i f j = f (dblIdx i j) := by
  induction j using Fin.lastCases with
  | last => simp [dbl]
  | cast k => simp [dbl]

theorem pairDet_dbl (α : Fin (m + 1) → Fin 2 → ℝ) (i : Fin (m + 1)) (a b : Fin (m + 2)) :
    pairDet (dbl i α) a b = pairDet α (dblIdx i a) (dblIdx i b) := by
  simp only [pairDet, dbl_apply]

/-- The numerator lines of the doubled data: the old ones and the new last line. -/
def dblLines (E : Finset (Fin (m + 1))) : Finset (Fin (m + 2)) :=
  insert (Fin.last (m + 1)) (E.map Fin.castSuccEmb)

theorem last_notMem_map (E : Finset (Fin (m + 1))) :
    Fin.last (m + 1) ∉ E.map Fin.castSuccEmb := by
  simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
  exact fun j _ h => Fin.castSucc_ne_last j h

theorem card_filter_univ_dbl (i : Fin (m + 1)) (p : Fin (m + 1) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun j : Fin (m + 2) => p (dblIdx i j)).card =
      (Finset.univ.filter p).card + if p i then 1 else 0 := by
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [dblIdx_castSucc, dblIdx_last]

theorem card_filter_dblLines (E : Finset (Fin (m + 1))) (i : Fin (m + 1)) (p : Fin (m + 1) → Prop)
    [DecidablePred p] :
    ((dblLines E).filter fun j => p (dblIdx i j)).card =
      (E.filter p).card + if p i then 1 else 0 := by
  simp only [Finset.card_filter, dblLines]
  rw [Finset.sum_insert (last_notMem_map E), Finset.sum_map]
  simp only [Fin.castSuccEmb_apply, dblIdx_castSucc, dblIdx_last]
  ring

/-- **The refined criterion survives the doubling of a line** (with the new line a numerator
line). -/
theorem noSubdivergenceRefined_dbl {k : ℕ} {E : Finset (Fin (m + 1))}
    {α : Fin (m + 1) → Fin 2 → ℝ} (h : NoSubdivergenceRefined k E α) (i : Fin (m + 1)) :
    NoSubdivergenceRefined k (dblLines E) (dbl i α) := by
  intro a
  have h1 := card_filter_univ_dbl i (fun j => pairDet α (dblIdx i a) j ≠ 0)
  have h2 := card_filter_dblLines E i (fun j => pairDet α (dblIdx i a) j ≠ 0)
  have h0 := h (dblIdx i a)
  simp only [pairDet_dbl]
  rw [h1, h2]
  split_ifs <;> omega

/-! ### The refined bounds -/

theorem lineWeight_dbl_map (α : Fin (m + 1) → Fin 2 → ℝ) (i : Fin (m + 1))
    (E : Finset (Fin (m + 1))) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lineWeight (dbl i α) (E.map Fin.castSuccEmb) A = lineWeight α E A := by
  simp only [lineWeight, Finset.prod_map, Fin.castSuccEmb_apply, dbl_apply, dblIdx_castSucc]

theorem lineWeight_dbl (α : Fin (m + 1) → Fin 2 → ℝ) (i : Fin (m + 1))
    (E : Finset (Fin (m + 1))) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lineWeight (dbl i α) (dblLines E) A =
      Real.sqrt (1 + α i ⬝ᵥ A⁻¹ *ᵥ α i) * lineWeight α E A := by
  rw [← lineWeight_dbl_map α i E A]
  simp only [lineWeight, dblLines]
  rw [Finset.prod_insert (last_notMem_map E), dbl_apply, dblIdx_last]

theorem refinedBound_dbl_map {k : ℕ} {E : Finset (Fin (m + 1))} {α : Fin (m + 1) → Fin 2 → ℝ}
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : RefinedBound α E k F) (i : Fin (m + 1)) :
    RefinedBound (dbl i α) (E.map Fin.castSuccEmb) k F := by
  obtain ⟨C, hC, hF⟩ := h
  exact ⟨C, hC, fun A hA ℓ => by rw [lineWeight_dbl_map]; exact hF A hA ℓ⟩

theorem lineMomentum_dbl_last (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (dbl i α) (dbl i p) (Fin.last (m + 1)) ℓ = lineMomentum α p i ℓ := by
  funext μ
  simp [lineMomentum, dbl]

/-- **The derivative of a line denominator is bounded by the new line**: `∂Dᵢ = 2 kᵢ(ℓ)·qᵢ`. -/
theorem refinedBound_dLine (α : Fin (m + 1) → Fin 2 → ℝ) (p q : Fin (m + 1) → Fin 4 → ℝ)
    (i : Fin (m + 1)) :
    RefinedBound (dbl i α) {Fin.last (m + 1)} 1 fun ℓ =>
      dLineC (p i) (q i) + linF (dLineL (α i) (q i)) (loopComp ℓ) := by
  have e : (fun ℓ => dLineC (p i) (q i) + linF (dLineL (α i) (q i)) (loopComp ℓ)) =
      fun ℓ => ∑ μ, ((2 * lower (q i) μ : ℝ) : ℂ) *
        ((lineMomentum (dbl i α) (dbl i p) (Fin.last (m + 1)) ℓ μ : ℝ) : ℂ) := by
    funext ℓ
    rw [dLineC_add_linF, lineMomentum_dbl_last, dot_comm, dot_eq_sum_lower]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp only [lineMomentum]; push_cast; ring
  rw [e]
  exact RefinedBound.sum _ fun μ _ => (refinedBound_lineMomentum _ _ _ μ).const_mul _

/-- Every point of the doubled simplex is a split of a point of the simplex. -/
theorem exists_splitAt {i : Fin (m + 1)} {z' : Fin (m + 2) → ℝ} (h0 : ∀ j, 0 ≤ z' j)
    (h1 : ∑ j, z' j = 1) :
    ∃ (z : Fin (m + 1) → ℝ) (t : ℝ), (∀ j, 0 ≤ z j) ∧ ∑ j, z j = 1 ∧ z' = splitAt i z t := by
  refine ⟨Function.update (fun j => z' j.castSucc) i (z' i.castSucc + z' (Fin.last _)),
    z' i.castSucc, fun j => ?_, ?_, ?_⟩
  · rcases eq_or_ne j i with rfl | hj
    · simp only [Function.update_self]; exact add_nonneg (h0 _) (h0 _)
    · rw [Function.update_of_ne hj]; exact h0 _
  · rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← h1, Fin.sum_univ_castSucc]
    have := Finset.add_sum_erase Finset.univ (fun j : Fin (m + 1) => z' j.castSucc)
      (Finset.mem_univ i)
    rw [Finset.sdiff_singleton_eq_erase, ← this]
    ring
  · funext j
    induction j using Fin.lastCases with
    | last => simp [splitAt_last]
    | cast j =>
      rw [splitAt_castSucc]
      rcases eq_or_ne j i with rfl | hj
      · simp
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]

end QED.GradedProof.WI2

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.GradedProof.WI2

/-- **The data with line `i` doubled**, the new line a numerator line. -/
def dup (D : SEData) (i : Fin (D.m + 1)) : SEData where
  m := D.m + 1
  α := dbl i D.α
  cs := dbl i D.cs
  M := dbl i D.M
  E := dblLines D.E
  hm := by have := D.hm; omega
  hcrit := noSubdivergenceRefined_dbl D.hcrit i

theorem dup_mom (D : SEData) (i : Fin (D.m + 1)) (p : Fin 4 → ℝ) :
    (D.dup i).mom p = dbl i (D.mom p) := by
  show (fun j : Fin (D.m + 2) => dbl i D.cs j • p) = dbl i (D.mom p)
  funext j
  rw [dbl_apply, dbl_apply]
  rfl

/-- **Positivity of `V` passes to the doubled data.** -/
theorem VPos.dup {D : SEData} {q : Fin (D.m + 1) → Fin 4 → ℝ} (h : D.VPos q)
    (i : Fin (D.m + 1)) : (D.dup i).VPos (dbl i q) := by
  obtain ⟨c, hc, hV⟩ := h
  refine ⟨c, hc, fun z' h0 h1 hU => ?_⟩
  obtain ⟨z, t, hz0, hz1, rfl⟩ := exists_splitAt (i := i) h0 h1
  change c ≤ symanzikV (dbl i D.α) (dbl i q) (dbl i D.M) _
  change symanzikU (dbl i D.α) _ ≠ 0 at hU
  rw [symanzikU_dbl] at hU
  rw [symanzikV_dbl]
  exact hV z hz0 hz1 hU

/-- **The insertion numerator is admissible on the doubled data**: `P · (2 kᵢ·qᵢ)` for a cubic
`P` with exponent three. -/
theorem good_mulLin (D : SEData) (i : Fin (D.m + 1)) {P : LoopQuartic} (hq : P.quart = 0)
    (hP : RefinedBound D.α D.E 3 P.eval) (p q : Fin (D.m + 1) → Fin 4 → ℝ) :
    (D.dup i).Good (Cubic.mulLin P (dLineC (p i) (q i)) (dLineL (D.α i) (q i))) := by
  refine ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega), ?_⟩
  have hb := (refinedBound_dbl_map hP i).mul (refinedBound_dLine D.α p q i)
    (Finset.disjoint_singleton_right.mpr (last_notMem_map D.E))
  have e : (Cubic.mulLin P (dLineC (p i) (q i)) (dLineL (D.α i) (q i))).eval =
      fun ℓ => P.eval ℓ * (dLineC (p i) (q i) + linF (dLineL (D.α i) (q i)) (loopComp ℓ)) := by
    funext ℓ
    exact evalC_mulLin P hq _ _ _
  rw [e]
  change RefinedBound (dbl i D.α) (dblLines D.E) 4 _
  rw [dblLines, Finset.insert_eq, Finset.union_comm]
  exact hb

end QED.GradedProof.SE2.SEData

end
