/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0TwoLoopEntries
public import QED.GradedProof.X0AffPoly
public import QED.GradedProof.X0NsCrit

/-!
# (X₀): (T₉′) at two loops for lines with multiplicities

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. Lines `i : ι` (any finite type) carry the momenta
`k_i = a_{i0} ℓ₀ + a_{i1} ℓ₁ + q_i` (`rowMom`) with integer rows `a_i`, a list `ms i` of masses
(one propagator denominator `D_M(k_i) = k_i·k_i + M² - iε` each) and a numerator factor
`N_i(k_i)`, a sum of products of at most `d_i` affine factors (`AffPoly`), or anything if
`a_i = 0`. If the multiplicities pass `LinesCrit`, then
`z ∏_i N_i(k_i) ∏_{M ∈ ms i} D_M(k_i)⁻¹` satisfies (T₉′) at two loops for every `ε > 0`
(`jointEnergyFirstIntegrable_lines`); with `PadCrit` one may first multiply by
`D₀(k_e) D₀(k_e)⁻¹` on one line (`jointEnergyFirstIntegrable_lines_pad`).

## Proof

Each copy `(i, j)`, `j < |ms i|`, of a line is a line of the parametric data (indexed by
`Fin (m + 1)` through an equivalence); the numerator factor `N_i` is bounded by `d_i` copies of
line `i`, and the criterion and the sizes of `LinesCrit` are those of
`IntNoSubdivergenceRefined` and of the refined and cubic two-loop theorems.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Integration.TwoLoop (castLoopMatrix lineDenom lineMomentum RefinedBound intPairDet
  refinedBound_lineMomentum IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic)
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopAffine propDenom propDenom_ne_zero)

/-- The momentum `a₀ ℓ₀ + a₁ ℓ₁ + q` of a line with integer row `a` and shift `q`. -/
def rowMom (a : Fin 2 → ℤ) (q : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  ((a 0 : ℤ) : ℝ) • ℓ 0 + ((a 1 : ℤ) : ℝ) • ℓ 1 + q

theorem rowMom_zero (q : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : rowMom 0 q ℓ = q := by
  simp [rowMom]

theorem isLoopAffine_rowMom (a : Fin 2 → ℤ) (q : Fin 4 → ℝ) : IsLoopAffine (rowMom a q) :=
  ⟨fun s => ((a s : ℤ) : ℝ), q, fun ℓ => by simp [rowMom, Fin.sum_univ_two]⟩

theorem lineMomentum_cast {m : ℕ} (a : Fin (m + 1) → Fin 2 → ℤ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (s : Fin (m + 1)) : lineMomentum (castLoopMatrix a) q s = rowMom (a s) (q s) := by
  funext ℓ μ
  simp [lineMomentum, rowMom, castLoopMatrix, Fin.sum_univ_two]

/-- An `AffPoly` numerator at an affine momentum is a polynomial in the loop momenta. -/
theorem AffPoly.isLoopPoly_comp {d : ℕ} {P : (Fin 4 → ℝ) → ℂ} (h : AffPoly d P)
    {K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hK : IsLoopAffine K) :
    IsLoopPoly 2 d fun ℓ => P (K ℓ) := by
  induction h with
  | const z => exact IsLoopPoly.const z
  | aff u w => exact (IsLoopPoly.const u).add (IsLoopPoly.sum _ fun ν _ =>
      (hK.isLoopPoly_coord ν).const_mul (w ν))
  | mul _ _ ih ih' => exact ih.mul ih'
  | add _ _ ih ih' => exact ih.add ih'
  | mono hd _ ih => exact ih.mono hd

/-- **The pointwise bound for an `AffPoly` numerator at a line momentum**, by any `d` lines
carrying that momentum. -/
theorem refinedBound_affPoly_lines {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) {d : ℕ}
    {P : (Fin 4 → ℝ) → ℂ} (h : AffPoly d P) :
    ∀ S : Finset (Fin (m + 1)), S.card = d → (∀ s ∈ S, lineMomentum α p s = K) →
      RefinedBound α S d fun ℓ => P (K ℓ) := by
  classical
  induction h with
  | const z =>
    intro S hS _
    rw [Finset.card_eq_zero.mp hS]
    exact RefinedBound.const z
  | aff u w =>
    intro S hS hK
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hS
    rw [← hK s (Finset.mem_singleton_self s)]
    exact ((RefinedBound.const u).mono (Finset.empty_subset _) (Nat.zero_le _)).add
      (RefinedBound.sum _ fun ν _ => (refinedBound_lineMomentum α p s ν).const_mul (w ν))
  | @mul d d' N N' _ _ ih ih' =>
    intro S hS hK
    obtain ⟨S₁, hS₁, hc₁⟩ := Finset.exists_subset_card_eq (s := S) (n := d) (by omega)
    have hc₂ : (S \ S₁).card = d' := by rw [Finset.card_sdiff_of_subset hS₁]; omega
    have hm := (ih S₁ hc₁ fun s hs => hK s (hS₁ hs)).mul
      (ih' (S \ S₁) hc₂ fun s hs => hK s (Finset.sdiff_subset hs)) Finset.disjoint_sdiff
    rwa [Finset.union_sdiff_of_subset hS₁] at hm
  | add _ _ ih ih' => exact fun S hS hK => (ih S hS hK).add (ih' S hS hK)
  | @mono d d' N hd _ ih =>
    intro S hS hK
    obtain ⟨S₁, hS₁, hc₁⟩ := Finset.exists_subset_card_eq (s := S) (n := d) (by omega)
    exact (ih S₁ hc₁ fun s hs => hK s (hS₁ hs)).mono hS₁ hd

/-- Products over pairwise disjoint sets of lines. -/
theorem refinedBound_prod_sets {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {κ : Type*}
    [DecidableEq κ] (s : Finset κ) (S : κ → Finset (Fin (m + 1))) (d : κ → ℕ)
    {F : κ → (Fin 2 → Fin 4 → ℝ) → ℂ} (hS : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (h : ∀ i ∈ s, RefinedBound α (S i) (d i) (F i)) :
    RefinedBound α (s.biUnion S) (∑ i ∈ s, d i) fun ℓ => ∏ i ∈ s, F i ℓ := by
  induction s using Finset.induction_on with
  | empty => simpa using (RefinedBound.const 1 : RefinedBound α ∅ 0 fun _ => (1 : ℂ))
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi j hj => hS i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        fun i hi => h i (Finset.mem_insert_of_mem hi))
      ((Finset.disjoint_biUnion_right _ _ _).mpr fun j hj => hS a (Finset.mem_insert_self a s) j
        (Finset.mem_insert_of_mem hj) fun h => ha (h ▸ hj))
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.biUnion_insert]
    exact h1

/-- **(T₉′) at two loops for a polynomial numerator bounded by its lines.** -/
theorem jointEnergyFirstIntegrable_twoLoopNum {m : ℕ} (a : Fin (m + 1) → Fin 2 → ℤ)
    (q : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (E : Finset (Fin (m + 1))) {d : ℕ} {N : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 d N)
    (hB : RefinedBound (castLoopMatrix a) E d N) (hcrit : IntNoSubdivergenceRefined 2 E a)
    (hsize : (7 ≤ m ∧ d ≤ 4) ∨ (6 ≤ m ∧ d ≤ 3)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      N ℓ * ∏ i, (lineDenom (castLoopMatrix a) q Ms ε i ℓ)⁻¹ := by
  have hcr := (noSubdivergenceRefined_castLoopMatrix_iff 2 E a).mpr hcrit
  rcases hsize with ⟨hm, hd⟩ | ⟨hm, hd⟩
  · obtain ⟨Q, hQ⟩ := (hpoly.mono hd).exists_loopQuartic
    rw [← hQ] at hB
    have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q _ q Ms hm hε hcr (hB.mono le_rfl hd)
    rw [hQ] at h
    exact h
  · obtain ⟨Q, hq, hQ⟩ := QED.GradedProof.SE2.IsLoopPoly.exists_loopQuartic_cubic (hpoly.mono hd)
    rw [← hQ] at hB
    have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
      Q _ q Ms hq hm hε hcr (hB.mono le_rfl (by omega))
    rw [hQ] at h
    exact h

/-- `D_M(k)` is a polynomial of degree two in `k`. -/
theorem affPoly_propDenom (M ε : ℝ) : AffPoly 2 fun k => propDenom M ε k := by
  have hc : ∀ μ : Fin 4, AffPoly 1 fun k : Fin 4 → ℝ => ((k μ : ℝ) : ℂ) := fun μ => by
    have h : (fun k : Fin 4 → ℝ => ((k μ : ℝ) : ℂ)) =
        fun k => 0 + ∑ ν, (if ν = μ then (1 : ℂ) else 0) * ((k ν : ℝ) : ℂ) := by
      funext k
      simp
    rw [h]
    exact AffPoly.aff _ _
  have hs := (AffPoly.sum Finset.univ fun μ _ => AffPoly.sum Finset.univ fun ν _ =>
    ((hc μ).mul (hc ν)).const_mul ((Minkowski.metric μ ν : ℝ) : ℂ)).add
    (AffPoly.const' 2 (((M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
  refine (congrArg _ (funext fun k => ?_)).mp hs
  simp only [propDenom, Minkowski.dot]
  push_cast
  simp only [mul_assoc]
  ring

/-- **(T₉′) at two loops for lines with multiplicities.** -/
theorem jointEnergyFirstIntegrable_lines {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Fin 2 → ℤ) (q : ι → Fin 4 → ℝ) (ms : ι → List ℝ) (d : ι → ℕ)
    (N : ι → (Fin 4 → ℝ) → ℂ) (hN : ∀ i, AffPoly (d i) (N i) ∨ a i = 0)
    (hcrit : LinesCrit a (fun i => (ms i).length) d) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * ∏ i, (N i (rowMom (a i) (q i) ℓ) *
        ((ms i).map fun M => (propDenom M ε (rowMom (a i) (q i) ℓ))⁻¹).prod) := by
  classical
  obtain ⟨hdeg, hcount, hsize⟩ := hcrit
  simp only [DegOK, CountOK, SizeOK] at hdeg hcount hsize
  have hX : Fintype.card (Σ i, Fin (ms i).length) = ∑ i, (ms i).length := by
    simp [Fintype.card_sigma]
  obtain ⟨m, hm⟩ : ∃ m, ∑ i, (ms i).length = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by rcases hsize with h | h <;> omega)).symm⟩
  set e : (Σ i, Fin (ms i).length) ≃ Fin (m + 1) := Fintype.equivFinOfCardEq (hX.trans hm)
    with he
  set a' : Fin (m + 1) → Fin 2 → ℤ := fun s => a (e.symm s).1 with ha'
  set q' : Fin (m + 1) → Fin 4 → ℝ := fun s => q (e.symm s).1 with hq'
  set Ms' : Fin (m + 1) → ℝ := fun s => (ms (e.symm s).1).get (e.symm s).2 with hMs'
  -- lines carrying no loop momentum have no copies
  have htree : ∀ i, a i = 0 → (ms i).length = 0 := fun i hi => by
    by_contra hne
    have h := hcount i (Nat.pos_of_ne_zero hne)
    have h0 : Finset.univ.filter (fun j => rdet (a i) (a j) ≠ 0) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun j _ => by simp [rdet, hi]
    rw [h0] at h
    simp at h
  -- the copies bounding the numerator factors
  set S : ι → Finset (Fin (m + 1)) := fun i =>
    (Finset.univ.filter fun j : Fin (ms i).length => j.val < d i).map
      ⟨fun j => e ⟨i, j⟩, e.injective.comp sigma_mk_injective⟩ with hS
  have hScard : ∀ i, (S i).card = d i := fun i => by
    rw [hS, Finset.card_map, Fin.card_filter_val_lt]
    exact min_eq_right (hdeg i)
  have hmem : ∀ i s, s ∈ S i → ∃ j : Fin (ms i).length, e.symm s = ⟨i, j⟩ := fun i s hs => by
    simp only [hS, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨j, -, rfl⟩ := hs
    exact ⟨j, by simp⟩
  have hSmom : ∀ i, ∀ s ∈ S i, lineMomentum (castLoopMatrix a') q' s = rowMom (a i) (q i) :=
    fun i s hs => by
      obtain ⟨j, hj⟩ := hmem i s hs
      rw [lineMomentum_cast]
      simp only [ha', hq', hj]
  have hdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ i' ∈ (Finset.univ : Finset ι), i ≠ i' →
      Disjoint (S i) (S i') := fun i _ i' _ hii' => by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨j, hj⟩ := hmem i s hs
    obtain ⟨j', hj'⟩ := hmem i' s hs'
    rw [hj] at hj'
    exact hii' (congrArg Sigma.fst hj')
  set E := (Finset.univ : Finset ι).biUnion S with hE
  -- the numerator
  have hB : RefinedBound (castLoopMatrix a') E (∑ i, d i) fun ℓ =>
      z * ∏ i, N i (rowMom (a i) (q i) ℓ) := by
    refine (refinedBound_prod_sets Finset.univ S d hdisj fun i _ => ?_).const_mul z
    rcases hN i with hP | h0
    · exact refinedBound_affPoly_lines _ q' _ hP (S i) (hScard i) (hSmom i)
    · have hd0 : d i = 0 := by have := hdeg i; rw [htree i h0] at this; omega
      have hS0 : S i = ∅ := Finset.card_eq_zero.mp ((hScard i).trans hd0)
      rw [hS0, hd0]
      simp only [h0, rowMom_zero]
      exact RefinedBound.const _
  have hpoly : IsLoopPoly 2 (∑ i, d i) fun ℓ => z * ∏ i, N i (rowMom (a i) (q i) ℓ) := by
    refine (IsLoopPoly.prod Finset.univ d fun i _ => ?_).const_mul z
    rcases hN i with hP | h0
    · exact hP.isLoopPoly_comp (isLoopAffine_rowMom _ _)
    · simp only [h0, rowMom_zero]
      exact IsLoopPoly.const _
  -- the criterion
  have hcrit' : IntNoSubdivergenceRefined 2 E a' := by
    intro s
    set x := e.symm s with hx
    have h := hcount x.1 (Fin.pos x.2)
    have hdet : ∀ t, intPairDet a' s t = rdet (a x.1) (a (e.symm t).1) := fun t => rfl
    have h1 : (Finset.univ.filter fun t => intPairDet a' s t ≠ 0).card =
        ∑ j ∈ Finset.univ.filter (fun j => rdet (a x.1) (a j) ≠ 0), (ms j).length := by
      simp only [hdet]
      calc (Finset.univ.filter fun t => rdet (a x.1) (a (e.symm t).1) ≠ 0).card
          = ∑ t, (if rdet (a x.1) (a (e.symm t).1) ≠ 0 then 1 else 0) := Finset.card_filter _ _
        _ = ∑ y : (Σ i, Fin (ms i).length), (if rdet (a x.1) (a y.1) ≠ 0 then 1 else 0) :=
          Equiv.sum_comp e.symm (fun y => if rdet (a x.1) (a y.1) ≠ 0 then 1 else 0)
        _ = ∑ i, ∑ _j : Fin (ms i).length, (if rdet (a x.1) (a i) ≠ 0 then 1 else 0) :=
          Fintype.sum_sigma _
        _ = ∑ i, if rdet (a x.1) (a i) ≠ 0 then (ms i).length else 0 :=
          Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
        _ = _ := (Finset.sum_filter _ _).symm
    have h2 : (E.filter fun t => intPairDet a' s t ≠ 0).card =
        ∑ j ∈ Finset.univ.filter (fun j => rdet (a x.1) (a j) ≠ 0), d j := by
      simp only [hdet]
      rw [hE, Finset.filter_biUnion, Finset.card_biUnion (fun i _ i' _ hii' =>
        Finset.disjoint_filter_filter (hdisj i (Finset.mem_univ _) i' (Finset.mem_univ _) hii')),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rw [← hScard i]
        congr 1
        refine Finset.filter_true_of_mem fun t ht => ?_
        obtain ⟨j, hj⟩ := hmem i t ht
        rw [hj]
        exact hi
      · rw [Finset.card_eq_zero]
        refine Finset.filter_false_of_mem fun t ht => ?_
        obtain ⟨j, hj⟩ := hmem i t ht
        rw [hj]
        exact hi
    rw [h1, h2]
    omega
  have hsize' : (7 ≤ m ∧ ∑ i, d i ≤ 4) ∨ (6 ≤ m ∧ ∑ i, d i ≤ 3) := by
    rcases hsize with h | h
    · exact Or.inl ⟨by omega, h.2⟩
    · exact Or.inr ⟨by omega, h.2⟩
  have h := jointEnergyFirstIntegrable_twoLoopNum a' q' Ms' hε E hpoly hB hcrit' hsize'
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  have hden : ∏ s, (lineDenom (castLoopMatrix a') q' Ms' ε s ℓ)⁻¹ =
      ∏ i, ((ms i).map fun M => (propDenom M ε (rowMom (a i) (q i) ℓ))⁻¹).prod := by
    calc ∏ s, (lineDenom (castLoopMatrix a') q' Ms' ε s ℓ)⁻¹
        = ∏ y : (Σ i, Fin (ms i).length), (lineDenom (castLoopMatrix a') q' Ms' ε (e y) ℓ)⁻¹ :=
          (Equiv.prod_comp e _).symm
      _ = ∏ y : (Σ i, Fin (ms i).length),
          (propDenom ((ms y.1).get y.2) ε (rowMom (a y.1) (q y.1) ℓ))⁻¹ := by
          refine Finset.prod_congr rfl fun y _ => ?_
          rw [QED.TwoLoop.Bridge.lineDenom_eq_propDenom, lineMomentum_cast]
          have key : ∀ x' x : (Σ i, Fin (ms i).length), x' = x →
              (ms x'.1).get x'.2 = (ms x.1).get x.2 := by
            rintro _ _ rfl
            rfl
          simp only [ha', hq', hMs', key _ _ (e.symm_apply_apply y), Equiv.symm_apply_apply]
      _ = ∏ i, ∏ j : Fin (ms i).length,
          (propDenom ((ms i).get j) ε (rowMom (a i) (q i) ℓ))⁻¹ := Fintype.prod_sigma _
      _ = _ := Finset.prod_congr rfl fun i _ => by
          simp only [List.get_eq_getElem]
          exact Fin.prod_univ_fun_getElem (ms i) fun M => (propDenom M ε (rowMom (a i) (q i) ℓ))⁻¹
  rw [hden, mul_assoc, ← Finset.prod_mul_distrib]

/-- **(T₉′) at two loops for lines with multiplicities, with padding.** -/
theorem jointEnergyFirstIntegrable_lines_pad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Fin 2 → ℤ) (q : ι → Fin 4 → ℝ) (ms : ι → List ℝ) (d : ι → ℕ)
    (N : ι → (Fin 4 → ℝ) → ℂ) (hN : ∀ i, AffPoly (d i) (N i) ∨ a i = 0)
    (hcrit : PadCrit a (fun i => (ms i).length) d) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * ∏ i, (N i (rowMom (a i) (q i) ℓ) *
        ((ms i).map fun M => (propDenom M ε (rowMom (a i) (q i) ℓ))⁻¹).prod) := by
  classical
  rcases hcrit with h | ⟨e, -, he⟩
  · exact jointEnergyFirstIntegrable_lines a q ms d N hN h hε z
  set ms' : ι → List ℝ := fun i => if i = e then 0 :: ms i else ms i with hms'
  set N' : ι → (Fin 4 → ℝ) → ℂ := fun i =>
    if i = e then (fun k => N i k * propDenom 0 ε k) else N i with hN'
  have hlen : (fun i => (ms' i).length) = bump (fun i => (ms i).length) e 1 := by
    funext i
    by_cases h : i = e <;> simp [hms', bump, h]
  have hae : a e ≠ 0 := fun h0 => by
    have h := he.2.1 e (by simp [bump])
    have h0' : Finset.univ.filter (fun j => rdet (a e) (a j) ≠ 0) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun j _ => by simp [rdet, h0]
    rw [h0'] at h
    simp at h
  have hN'' : ∀ i, AffPoly (bump d e 2 i) (N' i) ∨ a i = 0 := fun i => by
    by_cases h : i = e
    · subst h
      refine Or.inl ?_
      simp only [hN', bump, ↓reduceIte]
      exact ((hN i).resolve_right hae).mul (affPoly_propDenom 0 ε)
    · rcases hN i with hP | h0
      · refine Or.inl ?_
        simpa [hN', bump, h] using hP
      · exact Or.inr h0
  have h := jointEnergyFirstIntegrable_lines a q ms' (bump d e 2) N' hN'' (hlen ▸ he) hε z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = e
  · subst hi
    have hD := propDenom_ne_zero (M := 0) hε.ne' (rowMom (a i) (q i) ℓ)
    simp only [hms', hN', ↓reduceIte, List.map_cons, List.prod_cons]
    field_simp
  · simp [hms', hN', hi]

end QED.GradedProof.X0

end
