/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopPrune
public import QED.DimReg.ThreeLoopFaceTrees

/-!
# A cheaper pruned checker, and checks split at cut subtrees

The line test `QED.DimReg.LineCont.formOk` of a leaf form only depends on three linear
combinations of the pulled-back unit exponents: on the box with flags `fl`, with
`Sᵢ = h Dᵢ - wᵢ` (`i ∈ T`) or `wᵢ` (else), `Cᵢ = Dᵢ` (`i ∈ T`) or `0`, `Tᵢ = 1` (`i ∈ T`) or `0`,
the slope of the `k`-th form is `(pull S)ₖ - h mₖ`, its `d`-coefficient is `(pull C)ₖ - mₖ`, and
its `ν`-coefficients are nonnegative iff `(pull T)ₖ = 0`. The checker `pchk3` carries these three
vectors instead of the seven unit exponents (`check_of_pchk3`).

A check is split into independent pieces at cut subtrees: `stAt` computes the subtree and the
checker state along a path, and `pchk3_of_cut` assembles the check of a tree from the check of
its skeleton above the cuts (`pchkCut`) and the checks at the cuts.
-/

@[expose] public section

namespace QED.DimReg.LineCont

open QED.DimReg.Sector

variable {N : ℕ}

/-- The leaf test from the three pulled vectors `[S, C, T]` and the minimal exponent `m`. -/
def leaf3 (N h : ℕ) (V : List (List ℕ)) (m : List ℕ) : Bool :=
  (List.range N).all fun k =>
    Nat.blt (h * m.getD k 0) ((V.getD 0 []).getD k 0) &&
      (((V.getD 1 []).getD k 0 != m.getD k 0) || (V.getD 2 []).getD k 0 == 0)

/-- **The pruned checker with three carried vectors.** -/
def pchk3 (h : ℕ) : SplitTree N → List (List ℕ) → List (List ℕ) → Bool
  | .leaf, Q, V => match findMin Q with
    | some m => leaf3 N h V m
    | none => false
  | .node i j l r, Q, V => (i != j) &&
      pchk3 h l (prune (Q.map (pullStep i j))) (V.map (pullStep i j)) &&
      pchk3 h r (prune (Q.map (pullStep j i))) (V.map (pullStep j i))

theorem leaf3_congr (h : ℕ) (V : List (List ℕ)) {m m' : List ℕ}
    (e : ∀ k, m.getD k 0 = m'.getD k 0) : leaf3 N h V m = leaf3 N h V m' := by
  simp only [leaf3, e]

/-- **Soundness of `pchk3`.** -/
theorem pchk3_sound (h : ℕ) :
    ∀ (t : SplitTree N) (P : NPoly) (Q V : List (List ℕ)), Inv P Q →
      pchk3 h t Q V = true →
      t.validB = true ∧ ∀ ps ∈ t.paths, leafOk (NPoly.minE (P.pull ps)) (P.pull ps) = true ∧
        leaf3 N h (V.map (pullExp ps)) (NPoly.minE (P.pull ps)) = true
  | .leaf, P, Q, V, hI, hc => by
    simp only [pchk3] at hc
    split at hc
    · rename_i m hm
      refine ⟨rfl, fun ps hps => ?_⟩
      simp only [SplitTree.paths, List.mem_singleton] at hps
      subst hps
      have hV : V.map (pullExp ([] : List (Fin N × Fin N))) = V := by simp [pullExp]
      rw [pull_nil, hV]
      obtain ⟨hl, heq⟩ := leaf_of_findMin hI hm
      exact ⟨hl, by rw [leaf3_congr h V heq]; exact hc⟩
    · exact absurd hc Bool.false_ne_true
  | .node i j l r, P, Q, V, hI, hc => by
    simp only [pchk3, Bool.and_eq_true] at hc
    obtain ⟨⟨hij, hl⟩, hr⟩ := hc
    obtain ⟨vl, hl⟩ := pchk3_sound h l _ _ _ (inv_pull hI i j) hl
    obtain ⟨vr, hr⟩ := pchk3_sound h r _ _ _ (inv_pull hI j i) hr
    refine ⟨by simp [SplitTree.validB, hij, vl, vr], fun ps hps => ?_⟩
    simp only [SplitTree.paths, List.mem_append, List.mem_map] at hps
    rcases hps with ⟨qs, hqs, rfl⟩ | ⟨qs, hqs, rfl⟩
    · rw [pull_cons, map_pullExp_cons]; exact hl qs hqs
    · rw [pull_cons, map_pullExp_cons]; exact hr qs hqs

/-! ### Linear combinations of pulled exponents -/

/-- `v = Σᵢ cᵢ uᵢ` coordinatewise. -/
def LinC (c : Fin N → ℕ) (u : Fin N → List ℕ) (v : List ℕ) : Prop :=
  ∀ k, v.getD k 0 = ∑ i, c i * (u i).getD k 0

theorem linC_pullStep {c : Fin N → ℕ} {u : Fin N → List ℕ} {v : List ℕ} (hv : LinC c u v)
    (a b : Fin N) : LinC c (fun i => pullStep a b (u i)) (pullStep a b v) := by
  intro k
  simp only [getD_pullStep, hv k, hv a]
  split_ifs <;> simp [mul_add, Finset.sum_add_distrib]

theorem linC_pullExp : ∀ (ps : List (Fin N × Fin N)) {c : Fin N → ℕ} {u : Fin N → List ℕ}
    {v : List ℕ}, LinC c u v → LinC c (fun i => pullExp ps (u i)) (pullExp ps v)
  | [], _, _, _, hv => hv
  | p :: ps, _, _, _, hv => linC_pullExp ps (linC_pullStep hv p.1 p.2)

theorem linC_vec (c : Fin N → ℕ) : LinC c (fun i => unitExp i) ((List.finRange N).map c) := by
  intro k
  simp only [unitExp, getD_addAt, List.getD_nil, zero_add, mul_ite, mul_one, mul_zero]
  by_cases hk : k < N
  · rw [show k = ((⟨k, hk⟩ : Fin N) : ℕ) from rfl, getD_map_finRange,
      Finset.sum_eq_single (⟨k, hk⟩ : Fin N)
        (fun i _ hi => ite_eq_right_iff.2 fun e => absurd (Fin.ext e.symm) hi)
        (by simp)]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun e => by omega).symm

/-! ### The three vectors of a box -/

/-- The coefficients of `S`. -/
def coefS3 (D : List ℕ) (fl : List Bool) (w : Fin N → ℕ) (h : ℕ) (i : Fin N) : ℕ :=
  if fl.getD i false then h * D.getD i 0 - w i else w i

/-- The coefficients of `C`. -/
def coefC3 (D : List ℕ) (fl : List Bool) (i : Fin N) : ℕ :=
  if fl.getD i false then D.getD i 0 else 0

/-- The coefficients of `T`. -/
def coefT3 (fl : List Bool) (i : Fin N) : ℕ := if fl.getD i false then 1 else 0

/-- The initial vectors `[S, C, T]` of a box. -/
def vec3 (N : ℕ) (D : List ℕ) (fl : List Bool) (w : Fin N → ℕ) (h : ℕ) : List (List ℕ) :=
  [(List.finRange N).map (coefS3 D fl w h), (List.finRange N).map (coefC3 D fl),
    (List.finRange N).map (coefT3 fl)]

theorem formOk_of_leaf3 {D : List ℕ} {fl : List Bool} {w : Fin N → ℕ} {h : ℕ}
    (hw : ∀ i : Fin N, fl.getD i false = true → w i ≤ h * D.getD i 0)
    (ps : List (Fin N × Fin N)) (m : List ℕ)
    (hc : leaf3 N h ((vec3 N D fl w h).map (pullExp ps)) m = true) (k : Fin N) :
    formOk w h (formU D fl ((unitList N).map (pullExp ps)) m k) = true := by
  have hS := linC_pullExp ps (linC_vec (coefS3 D fl w h)) k
  have hC := linC_pullExp ps (linC_vec (coefC3 D fl)) k
  have hT := linC_pullExp ps (linC_vec (coefT3 (N := N) fl)) k
  beta_reduce at hS hC hT
  generalize hz : (fun i : Fin N => (pullExp ps (unitExp i)).getD k 0) = z
  have hz' : ∀ i : Fin N, (pullExp ps (unitExp i)).getD k 0 = z i := fun i => by rw [← hz]
  simp only [hz'] at hS hC hT
  have hU : ∀ i : Fin N, (((unitList N).map (pullExp ps)).getD i []).getD k 0 = z i := by
    intro i
    simp only [unitList, List.map_map]
    rw [getD_map_finRange (pullExp ps ∘ fun i : Fin N => unitExp i) i []]
    exact hz' i
  simp only [leaf3, vec3, List.map_cons, List.map_nil, List.all_eq_true, List.mem_range,
    List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq, Nat.blt_eq] at hc
  obtain ⟨h1, h2⟩ := hc k k.2
  rw [hS] at h1
  rw [hC, hT] at h2
  simp only [formOk, formU, slopeZ, getD_map_finRange, hU, sum_map_finRange, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_finRange,
    true_implies]
  constructor
  · have e : ∀ i : Fin N, (if fl.getD i false = true then -(z i : ℤ) else (z i : ℤ)) * w i +
        h * (if fl.getD i false = true then (D.getD i 0 : ℤ) * z i else 0) =
        ((coefS3 D fl w h i * z i : ℕ) : ℤ) := by
      intro i
      simp only [coefS3]
      split_ifs with hf
      · push_cast [Nat.cast_sub (hw i hf)]; ring
      · push_cast; ring
    have e2 : ∑ i : Fin N, (if fl.getD i false = true then -(z i : ℤ) else (z i : ℤ)) * w i +
        h * (∑ i : Fin N, (if fl.getD i false = true then (D.getD i 0 : ℤ) * z i else 0) -
          (m.getD k 0 : ℤ)) = (∑ i, coefS3 D fl w h i * z i : ℕ) - h * (m.getD k 0 : ℤ) := by
      rw [mul_sub, Finset.mul_sum, ← add_sub_assoc, ← Finset.sum_add_distrib]
      push_cast
      rw [Finset.sum_congr rfl fun i _ => e i]
      push_cast; ring
    rw [e2]
    have : h * m.getD k 0 < ∑ i, coefS3 D fl w h i * z i := h1
    omega
  · rcases h2 with h2 | h2
    · left
      have e : ∑ i : Fin N, (if fl.getD i false = true then (D.getD i 0 : ℤ) * z i else 0) =
          ((∑ i, coefC3 D fl i * z i : ℕ) : ℤ) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [coefC3]; split_ifs <;> simp
      rw [e]
      omega
    · right
      intro i
      have := (Finset.sum_eq_zero_iff.1 h2) i (Finset.mem_univ _)
      simp only [coefT3] at this
      split_ifs with hf
      · simp only [hf, ite_true, one_mul] at this
        simp [this]
      · simp

/-- **The three-vector check implies the sector check and the line check** of a box. -/
theorem check_of_pchk3 {D : List ℕ} {fl : List Bool} {w : Fin N → ℕ} {h : ℕ}
    (hw : ∀ i : Fin N, fl.getD i false = true → w i ≤ h * D.getD i 0)
    {t : SplitTree N} {P : NPoly} (hP : ∀ s ∈ P, s.2 ≠ 0)
    (hc : pchk3 h t (prune (P.map Prod.fst)) (vec3 N D fl w h) = true) :
    (⟨t, [P]⟩ : SDCert N).check = true ∧ ∀ ps ∈ t.paths, ∀ k,
      formOk w h (leafForm D fl ps (NPoly.minE (P.pull ps)) k) = true := by
  obtain ⟨hv, hl⟩ := pchk3_sound h t P _ _ (inv_root hP) hc
  refine ⟨?_, fun ps hps k => ?_⟩
  · simp only [SDCert.check, hv, Bool.true_and, List.all_eq_true, List.mem_singleton,
      forall_eq]
    exact fun ps hps => (hl ps hps).1
  · rw [formOk_congr (leafForm_snd D fl ps _ k)]
    exact formOk_of_leaf3 hw ps _ (hl ps hps).2 k

/-! ### Cuts -/

/-- The subtree and the state of `pchk3` at a path (`false` left, `true` right). -/
def stAt : SplitTree N → List Bool → List (List ℕ) → List (List ℕ) →
    SplitTree N × List (List ℕ) × List (List ℕ)
  | t, [], Q, V => (t, Q, V)
  | .leaf, _ :: _, Q, V => (.leaf, Q, V)
  | .node i j l _, false :: c, Q, V =>
    stAt l c (prune (Q.map (pullStep i j))) (V.map (pullStep i j))
  | .node i j _ r, true :: c, Q, V =>
    stAt r c (prune (Q.map (pullStep j i))) (V.map (pullStep j i))

/-- `pchk3` at a state. -/
def chk3 (h : ℕ) (s : SplitTree N × List (List ℕ) × List (List ℕ)) : Bool :=
  pchk3 h s.1 s.2.1 s.2.2

/-- The check of the skeleton above the cuts (paths in `cuts` are assumed). -/
def pchkCut (h : ℕ) (cuts : List (List Bool)) :
    SplitTree N → List Bool → List (List ℕ) → List (List ℕ) → Bool
  | .leaf, pre, Q, V => cuts.contains pre || pchk3 h (.leaf : SplitTree N) Q V
  | .node i j l r, pre, Q, V => cuts.contains pre || ((i != j) &&
      pchkCut h cuts l (pre ++ [false]) (prune (Q.map (pullStep i j))) (V.map (pullStep i j)) &&
      pchkCut h cuts r (pre ++ [true]) (prune (Q.map (pullStep j i))) (V.map (pullStep j i)))

/-- **A check assembled from the skeleton and the cut subtrees.** -/
theorem pchk3_of_cut (h : ℕ) (cuts : List (List Bool)) :
    ∀ (t : SplitTree N) (pre : List Bool) (Q V : List (List ℕ)),
      pchkCut h cuts t pre Q V = true →
      (∀ c, pre ++ c ∈ cuts → chk3 h (stAt t c Q V) = true) → pchk3 h t Q V = true
  | .leaf, pre, Q, V, hc, H => by
    simp only [pchkCut, Bool.or_eq_true, List.contains_iff_mem] at hc
    rcases hc with hc | hc
    · exact H [] (by simpa using hc)
    · exact hc
  | .node i j l r, pre, Q, V, hc, H => by
    simp only [pchkCut, Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨⟨hij, hl⟩, hr⟩
    · exact H [] (by simpa using hc)
    · simp only [pchk3, Bool.and_eq_true]
      refine ⟨⟨hij, pchk3_of_cut h cuts l _ _ _ hl fun c hc => ?_⟩,
        pchk3_of_cut h cuts r _ _ _ hr fun c hc => ?_⟩
      · exact H (false :: c) (by simpa using hc)
      · exact H (true :: c) (by simpa using hc)

end QED.DimReg.LineCont

namespace QED.DimReg.ThreeLoop

open QED.DimReg.Sector QED.DimReg.LineCont

/-- The `n` low bits of `b`, lowest first. -/
def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, b => (b % 2 == 1) :: bitsOf n (b / 2)

/-- The splitting tree of the box with index `b`. -/
def treeB (b : ℕ) : SplitTree 7 := decodeTree (treeData.getD b [])

/-- The root state of the pruned exponents of the box with index `b`. -/
def rootQ (b : ℕ) : List (List ℕ) := prune ((boxPoly7 (bitsOf 7 b)).map Prod.fst)

/-- The root vectors `[S, C, T]` of the box with index `b`. -/
def rootV (b : ℕ) : List (List ℕ) := vec3 7 d7 (bitsOf 7 b) w7 h7

/-- The check of the subtree at the path `c` of the box with index `b`. -/
def chkJob (b : ℕ) (c : List Bool) : Bool := chk3 h7 (stAt (treeB b) c (rootQ b) (rootV b))

end QED.DimReg.ThreeLoop
