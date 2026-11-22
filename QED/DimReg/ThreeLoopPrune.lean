/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFace

/-!
# A pruned incremental sector checker

The leaf test of `QED.DimReg.Sector.SDCert.check` only depends on the minimal exponents of a
polynomial: a term that dominates another one entrywise stays dominated after every pull-back
(the substitution `yᵢ ↦ yⱼ yᵢ` is monotone on exponents). The checker `pchk` therefore carries
only the exponents that are not strictly dominated (`prune`), pulled back one step at a time,
together with the pulled-back unit exponents for the line test. On average fewer than two
exponents survive per node of the trees of `QED.DimReg.ThreeLoop.g7`, against `64` terms.

* `pchk_sound`: a passing check gives the sector check and the line check of
  `QED.DimReg.LineCont.formOk` for the full box polynomial (`check_of_pchk`).
-/

@[expose] public section

namespace QED.DimReg.LineCont

open QED.DimReg.Sector

variable {N : ℕ}

/-- Strict domination: `b ≤ a` entrywise and `b` has smaller total degree. -/
def sdom (b a : List ℕ) : Bool := leExp b a && decide (b.sum < a.sum)

/-- The exponents that are not strictly dominated. -/
def prune (L : List (List ℕ)) : List (List ℕ) := L.filter fun a => !(L.any fun b => sdom b a)

/-- An exponent below all others, if there is one. -/
def findMin (Q : List (List ℕ)) : Option (List ℕ) := Q.find? fun q => Q.all (leExp q)

/-- **The pruned incremental checker.** -/
def pchk (D : List ℕ) (fl : List Bool) (w : Fin N → ℕ) (h : ℕ) :
    SplitTree N → List (List ℕ) → List (List ℕ) → Bool
  | .leaf, Q, U => match findMin Q with
    | some m => (List.finRange N).all fun k => formOk w h (formU D fl U m k)
    | none => false
  | .node i j l r, Q, U => (i != j) &&
      pchk D fl w h l (prune (Q.map (pullStep i j))) (U.map (pullStep i j)) &&
      pchk D fl w h r (prune (Q.map (pullStep j i))) (U.map (pullStep j i))

/-! ### Exponent lemmas -/

theorem leExp_of_getD_le : ∀ {a b : List ℕ}, (∀ k, a.getD k 0 ≤ b.getD k 0) → leExp a b = true
  | [], _, _ => rfl
  | a :: as, [], h => by
    have h0 : a ≤ 0 := by simpa using h 0
    simp only [leExp, Bool.and_eq_true]
    exact ⟨by simp only [Nat.beq_eq]; omega, leExp_of_getD_le fun k => by simpa using h (k + 1)⟩
  | a :: as, b :: bs, h => by
    have h0 := h 0
    simp only [List.getD_cons_zero] at h0
    simp only [leExp, Bool.and_eq_true, Nat.ble_eq]
    exact ⟨h0, leExp_of_getD_le fun k => by simpa using h (k + 1)⟩

theorem getD_minExp : ∀ (a b : List ℕ) (k : ℕ),
    (minExp a b).getD k 0 = min (a.getD k 0) (b.getD k 0)
  | [], b, k => by simp [minExp]
  | a :: as, [], k => by simp [minExp]
  | a :: as, b :: bs, k => by
    cases k with
    | zero => simp [minExp]
    | succ k => simpa [minExp] using getD_minExp as bs k

theorem minE_le : ∀ {P : NPoly}, ∀ t ∈ P, ∀ k, (NPoly.minE P).getD k 0 ≤ t.1.getD k 0
  | [], t, ht, _ => by simp at ht
  | [s], t, ht, k => by
    simp only [List.mem_singleton] at ht
    subst ht
    simp [NPoly.minE]
  | s :: s' :: ss, t, ht, k => by
    rw [show NPoly.minE (s :: s' :: ss) = minExp s.1 (NPoly.minE (s' :: ss)) from rfl,
      getD_minExp]
    rcases List.mem_cons.1 ht with rfl | ht
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (minE_le t ht k)

theorem le_minE : ∀ {P : NPoly}, P ≠ [] → ∀ {c : List ℕ},
    (∀ t ∈ P, ∀ k, c.getD k 0 ≤ t.1.getD k 0) → ∀ k, c.getD k 0 ≤ (NPoly.minE P).getD k 0
  | [], hP, _, _, _ => absurd rfl hP
  | [s], _, c, h, k => by simpa [NPoly.minE] using h s (by simp) k
  | s :: s' :: ss, _, c, h, k => by
    rw [show NPoly.minE (s :: s' :: ss) = minExp s.1 (NPoly.minE (s' :: ss)) from rfl,
      getD_minExp]
    exact le_min (h s (by simp) k)
      (le_minE (by simp) (fun t ht => h t (List.mem_cons_of_mem _ ht)) k)

theorem getD_pullStep (i j : Fin N) (α : List ℕ) (k : ℕ) :
    (pullStep i j α).getD k 0 = α.getD k 0 + if k = j then α.getD i 0 else 0 := by
  rw [pullStep, getD_addAt]

theorem pullStep_mono (i j : Fin N) {a b : List ℕ} (h : ∀ k, a.getD k 0 ≤ b.getD k 0) (k : ℕ) :
    (pullStep i j a).getD k 0 ≤ (pullStep i j b).getD k 0 := by
  rw [getD_pullStep, getD_pullStep]
  have := h k
  have := h i
  split_ifs <;> omega

theorem mem_of_mem_prune {L : List (List ℕ)} {a : List ℕ} (h : a ∈ prune L) : a ∈ L :=
  List.mem_of_mem_filter h

theorem exists_prune_le {L : List (List ℕ)} :
    ∀ (n : ℕ) (a : List ℕ), a.sum ≤ n → a ∈ L →
      ∃ c ∈ prune L, ∀ k, c.getD k 0 ≤ a.getD k 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn ha
  by_cases hk : (L.any fun b => sdom b a) = true
  · obtain ⟨b, hb, hba⟩ := List.any_eq_true.1 hk
    simp only [sdom, Bool.and_eq_true, decide_eq_true_eq] at hba
    obtain ⟨c, hc, hcb⟩ := ih b.sum (by omega) b le_rfl hb
    exact ⟨c, hc, fun k => (hcb k).trans (getD_le_of_leExp hba.1 k)⟩
  · refine ⟨a, ?_, fun _ => le_rfl⟩
    simp only [Bool.not_eq_true] at hk
    exact List.mem_filter.2 ⟨ha, by simp [hk]⟩

/-! ### The invariant -/

/-- `Q` consists of exponents of terms of `P` with nonzero coefficients, and every term of `P`
dominates an element of `Q`. -/
def Inv (P : NPoly) (Q : List (List ℕ)) : Prop :=
  (∀ q ∈ Q, ∃ t ∈ P, t.1 = q ∧ t.2 ≠ 0) ∧ ∀ t ∈ P, ∃ q ∈ Q, ∀ k, q.getD k 0 ≤ t.1.getD k 0

theorem inv_pull {P : NPoly} {Q : List (List ℕ)} (hI : Inv P Q) (i j : Fin N) :
    Inv (P.pull [(i, j)]) (prune (Q.map (pullStep i j))) := by
  obtain ⟨h1, h2⟩ := hI
  refine ⟨fun q hq => ?_, fun t ht => ?_⟩
  · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 (mem_of_mem_prune hq)
    obtain ⟨t, ht, rfl, hc⟩ := h1 q₀ hq₀
    exact ⟨(pullStep i j t.1, t.2), List.mem_map.2 ⟨t, ht, by simp [pullExp]⟩, rfl, hc⟩
  · obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    obtain ⟨q, hq, hle⟩ := h2 t₀ ht₀
    obtain ⟨c, hc, hcle⟩ := exists_prune_le _ (pullStep i j q) le_rfl
      (List.mem_map_of_mem (f := pullStep i j) hq)
    exact ⟨c, hc, fun k => (hcle k).trans (by simpa [pullExp] using pullStep_mono i j hle k)⟩

theorem leaf_of_findMin {P : NPoly} {Q : List (List ℕ)} (hI : Inv P Q) {m : List ℕ}
    (hm : findMin Q = some m) :
    leafOk (NPoly.minE P) P = true ∧ ∀ k, (NPoly.minE P).getD k 0 = m.getD k 0 := by
  obtain ⟨h1, h2⟩ := hI
  have hmQ := List.mem_of_find?_eq_some hm
  have hmin := List.find?_some hm
  simp only [List.all_eq_true] at hmin
  obtain ⟨t₀, ht₀, ht₀m, hc⟩ := h1 m hmQ
  have hle : ∀ t ∈ P, ∀ k, m.getD k 0 ≤ t.1.getD k 0 := fun t ht k => by
    obtain ⟨q, hq, hqt⟩ := h2 t ht
    exact (getD_le_of_leExp (hmin q hq) k).trans (hqt k)
  have heq : ∀ k, (NPoly.minE P).getD k 0 = m.getD k 0 := fun k =>
    le_antisymm (by simpa [ht₀m] using minE_le t₀ ht₀ k)
      (le_minE (List.ne_nil_of_mem ht₀) hle k)
  refine ⟨?_, heq⟩
  simp only [leafOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  refine ⟨fun t ht => leExp_of_getD_le fun k => minE_le t ht k, t₀, ht₀, ?_⟩
  simp only [bne_iff_ne, ne_eq]
  exact ⟨leExp_of_getD_le fun k => by rw [heq, ht₀m], hc⟩

theorem formU_congr_m (D : List ℕ) (fl : List Bool) (U : List (List ℕ)) {m m' : List ℕ}
    (k : Fin N) (h : m.getD k 0 = m'.getD k 0) : formU D fl U m k = formU D fl U m' k := by
  simp only [formU, h]

/-- **Soundness of the pruned checker.** -/
theorem pchk_sound (D : List ℕ) (fl : List Bool) (w : Fin N → ℕ) (h : ℕ) :
    ∀ (t : SplitTree N) (P : NPoly) (Q U : List (List ℕ)), Inv P Q →
      pchk D fl w h t Q U = true →
      t.validB = true ∧ ∀ ps ∈ t.paths, leafOk (NPoly.minE (P.pull ps)) (P.pull ps) = true ∧
        ∀ k : Fin N, formOk w h (formU D fl (U.map (pullExp ps)) (NPoly.minE (P.pull ps)) k) =
          true
  | .leaf, P, Q, U, hI, hc => by
    simp only [pchk] at hc
    split at hc
    · rename_i m hm
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
      refine ⟨rfl, fun ps hps => ?_⟩
      simp only [SplitTree.paths, List.mem_singleton] at hps
      subst hps
      have hU : U.map (pullExp ([] : List (Fin N × Fin N))) = U := by simp [pullExp]
      rw [pull_nil, hU]
      obtain ⟨hl, heq⟩ := leaf_of_findMin hI hm
      exact ⟨hl, fun k => by rw [formU_congr_m D fl U k (heq k)]; exact hc k⟩
    · exact absurd hc Bool.false_ne_true
  | .node i j l r, P, Q, U, hI, hc => by
    simp only [pchk, Bool.and_eq_true] at hc
    obtain ⟨⟨hij, hl⟩, hr⟩ := hc
    obtain ⟨vl, hl⟩ := pchk_sound D fl w h l _ _ _ (inv_pull hI i j) hl
    obtain ⟨vr, hr⟩ := pchk_sound D fl w h r _ _ _ (inv_pull hI j i) hr
    refine ⟨by simp [SplitTree.validB, hij, vl, vr], fun ps hps => ?_⟩
    simp only [SplitTree.paths, List.mem_append, List.mem_map] at hps
    rcases hps with ⟨qs, hqs, rfl⟩ | ⟨qs, hqs, rfl⟩
    · rw [pull_cons, map_pullExp_cons]; exact hl qs hqs
    · rw [pull_cons, map_pullExp_cons]; exact hr qs hqs

theorem inv_root {P : NPoly} (hP : ∀ t ∈ P, t.2 ≠ 0) : Inv P (prune (P.map Prod.fst)) := by
  refine ⟨fun q hq => ?_, fun t ht => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (mem_of_mem_prune hq)
    exact ⟨t, ht, rfl, hP t ht⟩
  · exact exists_prune_le _ t.1 le_rfl (List.mem_map_of_mem ht)

/-- **The pruned check implies the sector check and the line check** of a box. -/
theorem check_of_pchk {D : List ℕ} {fl : List Bool} {w : Fin N → ℕ} {h : ℕ}
    {t : SplitTree N} {P : NPoly} (hP : ∀ s ∈ P, s.2 ≠ 0)
    (hc : pchk D fl w h t (prune (P.map Prod.fst)) (unitList N) = true) :
    (⟨t, [P]⟩ : SDCert N).check = true ∧ ∀ ps ∈ t.paths, ∀ k,
      formOk w h (leafForm D fl ps (NPoly.minE (P.pull ps)) k) = true := by
  obtain ⟨hv, hl⟩ := pchk_sound D fl w h t P _ _ (inv_root hP) hc
  refine ⟨?_, fun ps hps k => ?_⟩
  · simp only [SDCert.check, hv, Bool.true_and, List.all_eq_true, List.mem_singleton,
      forall_eq]
    exact fun ps hps => (hl ps hps).1
  · rw [formOk_congr (leafForm_snd D fl ps _ k)]
    exact (hl ps hps).2 k

end QED.DimReg.LineCont

namespace QED.DimReg.ThreeLoop

open QED.DimReg.Sector QED.DimReg.LineCont

/-- The pruned check of one box. -/
def boxOkP (fl : List Bool) (t : SplitTree 7) : Bool :=
  pchk d7 fl w7 h7 t (prune ((boxPoly7 fl).map Prod.fst)) (unitList 7)

end QED.DimReg.ThreeLoop
