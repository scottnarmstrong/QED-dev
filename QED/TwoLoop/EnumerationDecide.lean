/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.IsOnePI
public import QED.TwoLoop.ChordLoopLine
public import QED.TwoLoop.LoopBound

/-!
# A kernel-efficient decision procedure for one-particle irreducibility

Obligation O2-2 (the enumeration of the order-`e⁵` vertex) is checked partly by kernel
evaluation (`decide +kernel`). The frozen predicates `IsOnePI` (X₁₈) and `IsChord` (T₁) are
stated with `Relation.ReflTransGen` over `Joined` (X₁₄), which has no efficient decision
procedure. This file supplies one and proves it correct, for every contraction.

* `QED.TwoLoop.Enumeration.lineData C`: the multiset of the pairs (label (X₂₀), ends (X₁₃)) of
  the internal lines of `C`, computed once.
* `QED.TwoLoop.Enumeration.reachE E p u k`: the vertices reached from `u` in at most `k` steps
  along the edges of `E` whose label satisfies `p`.
* `QED.TwoLoop.Enumeration.reflTransGen_iff_mem_reachSet`: for a decidable relation on a finite
  type, reachability is membership in the `card`-step reachable set.
* `QED.TwoLoop.Enumeration.isOnePI_iff_onePIE`: `IsOnePI C` iff the externals are attached and
  the Boolean test `onePIE (lineData C)` holds.
* `QED.TwoLoop.Enumeration.isChord_iff`: `IsChord f` iff the head of `f` is reached from its tail
  along lines of larger label.

The decidability instances are scoped to `QED.TwoLoop.Enumeration`, so they never compete with
the classical instances used by the frozen definitions.
-/

@[expose] public section

namespace QED.TwoLoop.Enumeration

open QED.WickModel Relation

/-! ### Reachable sets of a relation on a finite type -/

section Reach

variable {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- The elements reached from `u` by at most `k` steps of `r`. -/
def reachSet (u : α) : ℕ → Finset α
  | 0 => {u}
  | k + 1 => reachSet u k ∪ Finset.univ.filter (fun w => ∃ v ∈ reachSet u k, r v w)

theorem mem_reachSet_succ (u : α) (k : ℕ) (w : α) :
    w ∈ reachSet r u (k + 1) ↔ w ∈ reachSet r u k ∨ ∃ v ∈ reachSet r u k, r v w := by
  simp [reachSet]

theorem reachSet_mono (u : α) {k m : ℕ} (h : k ≤ m) : reachSet r u k ⊆ reachSet r u m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem reflTransGen_of_mem_reachSet (u : α) :
    ∀ k w, w ∈ reachSet r u k → ReflTransGen r u w
  | 0, w, h => by
    simp only [reachSet, Finset.mem_singleton] at h
    subst h
    exact .refl
  | k + 1, w, h => by
    rcases (mem_reachSet_succ r u k w).mp h with h | ⟨v, hv, hvw⟩
    · exact reflTransGen_of_mem_reachSet u k w h
    · exact (reflTransGen_of_mem_reachSet u k v hv).tail hvw

theorem reachSet_add_of_succ_eq (u : α) {k : ℕ} (h : reachSet r u (k + 1) = reachSet r u k) :
    ∀ m, reachSet r u (k + m) = reachSet r u k
  | 0 => rfl
  | m + 1 => by
    have ih := reachSet_add_of_succ_eq u h m
    rw [← Nat.add_assoc]
    show reachSet r u (k + m) ∪ _ = _
    simp only [ih]
    exact h

theorem mem_reachSet_of_succ_eq (u : α) {k : ℕ} (h : reachSet r u (k + 1) = reachSet r u k)
    {w : α} (hw : ReflTransGen r u w) : w ∈ reachSet r u k := by
  induction hw with
  | refl => exact reachSet_mono r u (Nat.zero_le k) (by simp [reachSet])
  | tail _ hbc ih =>
    rw [← h]
    exact (mem_reachSet_succ r u k _).mpr (Or.inr ⟨_, ih, hbc⟩)

theorem card_reachSet_ge (u : α) :
    ∀ n, (∀ k < n, reachSet r u (k + 1) ≠ reachSet r u k) → n + 1 ≤ (reachSet r u n).card
  | 0, _ => by simp [reachSet]
  | n + 1, h => by
    have ih := card_reachSet_ge u n fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hss : reachSet r u n ⊂ reachSet r u (n + 1) :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨reachSet_mono r u (Nat.le_succ n), (h n n.lt_succ_self).symm⟩
    have := Finset.card_lt_card hss
    omega

/-- Reachability on a finite type is membership in the `card`-step reachable set. -/
theorem reflTransGen_iff_mem_reachSet (u w : α) :
    ReflTransGen r u w ↔ w ∈ reachSet r u (Fintype.card α) := by
  refine ⟨fun hw => ?_, reflTransGen_of_mem_reachSet r u _ w⟩
  by_cases hk : ∃ k < Fintype.card α, reachSet r u (k + 1) = reachSet r u k
  · obtain ⟨k, hk, he⟩ := hk
    have := reachSet_add_of_succ_eq r u he (Fintype.card α - k)
    rw [Nat.add_sub_cancel' hk.le] at this
    rw [this]
    exact mem_reachSet_of_succ_eq r u he hw
  · push Not at hk
    have := card_reachSet_ge r u _ hk
    have := Finset.card_le_univ (reachSet r u (Fintype.card α))
    omega

end Reach

/-! ### Boolean search in a multiset -/

/-- `mAny m q`: some element of `m` satisfies the Boolean test `q`. Unlike the instance
`Multiset.decidableDexistsMultiset`, it does not go through `Multiset.attach`. -/
def mAny {α : Type*} (m : Multiset α) (q : α → Bool) : Bool :=
  Quot.liftOn m (fun l => l.any q) (fun _ _ h => (List.Perm.any_eq h).symm ▸ rfl)

theorem mAny_eq_true {α : Type*} (m : Multiset α) (q : α → Bool) :
    mAny m q = true ↔ ∃ x ∈ m, q x = true := by
  induction m using Quot.inductionOn with
  | h l => simp [mAny]

/-! ### Reachability along labelled edges -/

section Edges

variable {N : ℕ}

/-- One step along an edge of `E` (a label and two ends) whose label satisfies `p`, in either
direction. -/
def StepE (E : Multiset (ℕ × Fin N × Fin N)) (p : ℕ → Bool) (v w : Fin N) : Prop :=
  ∃ x ∈ E, p x.1 = true ∧ ((x.2.1 = v ∧ x.2.2 = w) ∨ (x.2.2 = v ∧ x.2.1 = w))

/-- The vertices reached from `u` by at most `k` steps along edges of `E` whose label satisfies
`p`; `reachSet (StepE E p)` written with Boolean tests for kernel evaluation. -/
def reachE (E : Multiset (ℕ × Fin N × Fin N)) (p : ℕ → Bool) (u : Fin N) :
    ℕ → Finset (Fin N)
  | 0 => {u}
  | k + 1 => reachE E p u k ∪ Finset.univ.filter (fun w => mAny E (fun x => p x.1 &&
      ((decide (x.2.1 ∈ reachE E p u k) && decide (x.2.2 = w)) ||
        (decide (x.2.2 ∈ reachE E p u k) && decide (x.2.1 = w)))) = true)

instance (E : Multiset (ℕ × Fin N × Fin N)) (p : ℕ → Bool) : DecidableRel (StepE E p) :=
  fun v w => decidable_of_iff (mAny E (fun x => p x.1 &&
      ((decide (x.2.1 = v) && decide (x.2.2 = w)) ||
        (decide (x.2.2 = v) && decide (x.2.1 = w)))) = true) (by
    rw [mAny_eq_true]
    simp [StepE])

theorem reachE_eq_reachSet (E : Multiset (ℕ × Fin N × Fin N)) (p : ℕ → Bool) (u : Fin N) :
    ∀ k, reachE E p u k = reachSet (StepE E p) u k
  | 0 => rfl
  | k + 1 => by
    ext w
    rw [mem_reachSet_succ, ← reachE_eq_reachSet E p u k]
    simp only [reachE, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      mAny_eq_true, StepE]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact Or.inl h
      · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨hp, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact Or.inr ⟨_, h1, x, hx, hp, Or.inl ⟨rfl, h2⟩⟩
        · exact Or.inr ⟨_, h1, x, hx, hp, Or.inr ⟨rfl, h2⟩⟩
    · rintro (h | ⟨v, hv, x, hx, hp, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
      · exact Or.inl h
      · subst h1
        exact Or.inr ⟨x, hx, by simp [hp, hv, h2]⟩
      · subst h1
        exact Or.inr ⟨x, hx, by simp [hp, hv, h2]⟩

theorem reflTransGen_stepE_iff (E : Multiset (ℕ × Fin N × Fin N)) (p : ℕ → Bool) (u w : Fin N) :
    ReflTransGen (StepE E p) u w ↔ w ∈ reachE E p u N := by
  rw [reachE_eq_reachSet, reflTransGen_iff_mem_reachSet, Fintype.card_fin]

/-- The Boolean one-particle-irreducibility test on labelled edges: every vertex is reached
from vertex `0`, and the ends of every edge are joined by the other edges. -/
def onePIE (E : Multiset (ℕ × Fin N × Fin N)) : Bool :=
  decide (∀ (h : 0 < N) (w : Fin N), w ∈ reachE E (fun _ => true) ⟨0, h⟩ N) &&
    mAny E (fun x => !decide (x.2.2 ∈ reachE E (fun l => l != x.1) x.2.1 N)) == false

end Edges

/-! ### The line data of a contraction -/

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The labels (X₂₀) and ends (X₁₃) of the internal lines of `C`. -/
def lineData (C : Contraction nf nA κ) : Multiset (ℕ × Fin N × Fin N) :=
  (Finset.univ : Finset (Line C)).val.map fun f => (f.label, f.ends)

theorem mem_lineData {C : Contraction nf nA κ} {x : ℕ × Fin N × Fin N} :
    x ∈ lineData C ↔ ∃ f : Line C, (f.label, f.ends) = x := by
  simp [lineData]

/-- `Joined` (X₁₄) outside a set described by labels is a step along the line data. -/
theorem joined_iff_stepE (C : Contraction nf nA κ) (S : Set (Line C)) (p : ℕ → Bool)
    (hp : ∀ f : Line C, f ∉ S ↔ p f.label = true) (u w : Fin N) :
    Joined C S u w ↔ StepE (lineData C) p u w := by
  constructor
  · rintro ⟨f, hf, h⟩
    refine ⟨(f.label, f.ends), mem_lineData.mpr ⟨f, rfl⟩, (hp f).mp hf, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · exact Or.inr ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  · rintro ⟨x, hx, hpx, h⟩
    obtain ⟨f, rfl⟩ := mem_lineData.mp hx
    refine ⟨f, (hp f).mpr hpx, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h2 h1)

theorem reflTransGen_joined_iff (C : Contraction nf nA κ) (S : Set (Line C)) (p : ℕ → Bool)
    (hp : ∀ f : Line C, f ∉ S ↔ p f.label = true) (u w : Fin N) :
    ReflTransGen (Joined C S) u w ↔ w ∈ reachE (lineData C) p u N := by
  have : Joined C S = StepE (lineData C) p := by
    funext a b
    exact propext (joined_iff_stepE C S p hp a b)
  rw [this, reflTransGen_stepE_iff]

theorem not_isBridge_iff {C : Contraction nf nA κ} (f : Line C) :
    ¬ IsBridge f ↔ f.ends.2 ∈ reachE (lineData C) (fun l => l != f.label) f.ends.1 N := by
  rw [IsBridge, not_not]
  refine reflTransGen_joined_iff C {f} _ (fun g => ?_) _ _
  simp only [Set.mem_singleton_iff, bne_iff_ne, ne_eq]
  exact ⟨fun h h' => h (Chord.label_injective h'), fun h h' => h (congrArg _ h')⟩

/-- `IsChord f` (T₁): the head of `f` is reached from its tail along lines of larger label. -/
theorem isChord_iff {C : Contraction nf nA κ} (f : Line C) :
    IsChord f ↔ f.ends.2 ∈ reachE (lineData C) (fun l => decide (f.label < l)) f.ends.1 N := by
  refine reflTransGen_joined_iff C _ _ (fun g => ?_) _ _
  simp

theorem verticesConnected_iff (C : Contraction nf nA κ) :
    VerticesConnected C ↔ ∀ (h : 0 < N) (w : Fin N),
      w ∈ reachE (lineData C) (fun _ => true) ⟨0, h⟩ N := by
  have key : ∀ u w, ReflTransGen (Joined C ∅) u w ↔
      w ∈ reachE (lineData C) (fun _ => true) u N :=
    reflTransGen_joined_iff C ∅ _ (fun _ => by simp)
  constructor
  · intro hC h w
    exact (key _ _).mp (hC _ _)
  · intro h u w
    have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) u.2
    exact (LoopBound.reflTransGen_joined_symm ((key _ _).mpr (h hN u))).trans
      ((key _ _).mpr (h hN w))

theorem onePIE_lineData_iff (C : Contraction nf nA κ) :
    onePIE (lineData C) = true ↔ VerticesConnected C ∧ ∀ f : Line C, ¬ IsBridge f := by
  have hB : (mAny (lineData C) (fun x =>
      !decide (x.2.2 ∈ reachE (lineData C) (fun l => l != x.1) x.2.1 N)) == false) = true ↔
      ∀ f : Line C, ¬ IsBridge f := by
    rw [beq_iff_eq, Bool.eq_false_iff, ne_eq, mAny_eq_true]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_exists,
      not_and, not_not]
    constructor
    · intro h f
      exact (not_isBridge_iff f).mpr (h _ (mem_lineData.mpr ⟨f, rfl⟩))
    · intro h x hx
      obtain ⟨f, rfl⟩ := mem_lineData.mp hx
      exact (not_isBridge_iff f).mp (h f)
  rw [onePIE, Bool.and_eq_true, decide_eq_true_eq, hB, verticesConnected_iff]

/-- **One-particle irreducibility by a Boolean test.** `IsOnePI C` (X₁₈) iff the externals are
attached and `onePIE (lineData C)` holds. -/
theorem isOnePI_iff_onePIE (C : Contraction nf nA κ) :
    IsOnePI C ↔ ExternalsAttached C ∧ onePIE (lineData C) = true := by
  rw [onePIE_lineData_iff, IsOnePI]

/-- Externals attached (X₁₆) is decidable. -/
scoped instance instDecidableExternalsAttached (C : Contraction nf nA κ) :
    Decidable (ExternalsAttached C) :=
  inferInstanceAs (Decidable ((∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) ∧
    ∀ i j : Fin nA, C.1.2 (.inl i) ≠ .inl j))

/-- One-particle irreducibility (X₁₈) is decidable, through `isOnePI_iff_onePIE`. -/
scoped instance instDecidableIsOnePI (C : Contraction nf nA κ) : Decidable (IsOnePI C) :=
  decidable_of_iff _ (isOnePI_iff_onePIE C).symm

/-- `IsChord` (T₁) is decidable, through `isChord_iff`. -/
scoped instance instDecidableIsChord {C : Contraction nf nA κ} (f : Line C) :
    Decidable (IsChord f) :=
  decidable_of_iff _ (isChord_iff f).symm

open scoped Classical in
/-- The loop count (T₂) computed with the decidable `IsChord`. -/
theorem loopCount_eq_card (C : Contraction nf nA κ) :
    loopCount C = (@Finset.filter (Line C) (fun f => IsChord f)
      (fun f => instDecidableIsChord f) Finset.univ).card := by
  unfold loopCount
  congr 1
  exact Finset.filter_congr_decidable _ _ _

end QED.TwoLoop.Enumeration

end
