/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.LineMomentum
public import QED.TwoLoop.LoopBound
public import QED.TwoLoop.ChordLoopLine
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Momentum conservation of the two-loop routing

The routing `lineMomentum₂` (T₄) of packet T1 (decision D-38) is the unique momentum assignment
that is conserved at every vertex and gives each chord (T₁) its loop momentum (T₃)
(obligation O2-5 (i)).

Sign conventions: a line carries its momentum from its tail `f.ends.1` to its head `f.ends.2`
(X₁₃), and `externalMomentum C pOut pIn kIn v` (X₁₉) is the external momentum flowing into `v`.
An assignment `P` is conserved (`IsConserved`) when at every vertex `v` the incoming minus the
outgoing line momenta (`inflow P v`) plus the external momentum at `v` is `0`.

* `QED.TwoLoop.Routing.not_reflTransGen_ends_of_not_isChord`: the lines that are not chords form a
  forest: the ends of such a line `f` are not joined by lines other than `f` that are not chords.
  The proof is Kruskal's: by downward induction on a label threshold, the non-chords above it form
  a forest.
* `QED.TwoLoop.Routing.eq_lineMomentum₂_of_isConserved` (uniqueness): every conserved assignment
  that gives each chord its loop momentum is `lineMomentum₂`. Summing the conservation law over
  the tail side of a non-chord `f` (a cut crossed by `f` and by chords only) gives its momentum.
  No connectedness and no condition on the external momenta is needed.
* `QED.TwoLoop.Routing.isConserved_lineMomentum₂` (conservation): for a contraction with connected
  vertices (X₁₇) whose external momenta sum to zero, `lineMomentum₂` is conserved. The incidence
  map from momenta on the non-chords to vertex injections is injective (by the cut argument), and
  there are at least `V - 1` non-chords, so its image is the whole space of injections summing to
  zero; the conserved assignment it provides is `lineMomentum₂` by uniqueness.
-/

@[expose] public section

namespace QED.TwoLoop.Routing

open QED.WickModel Relation QED.TwoLoop.LoopBound

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Conservation -/

/-- The line momentum flowing into the vertex `v`: incoming minus outgoing, for momentum flowing
from the tail of each line to its head (X₁₃). A self-loop contributes `0`. -/
noncomputable def inflow {C : Contraction nf nA κ} (P : Line C → Fin 4 → ℝ) (v : Fin N) :
    Fin 4 → ℝ :=
  ∑ g, ((if g.ends.2 = v then P g else 0) - (if g.ends.1 = v then P g else 0))

/-- The momentum assignment `P` on the internal lines is conserved at every vertex: the incoming
minus the outgoing line momenta plus the external momentum (X₁₉) at the vertex is `0`. -/
def IsConserved (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (P : Line C → Fin 4 → ℝ) : Prop :=
  ∀ v, inflow P v + externalMomentum C pOut pIn kIn v = 0

/-- The line momenta flowing into all vertices sum to zero. -/
theorem sum_inflow {C : Contraction nf nA κ} (P : Line C → Fin 4 → ℝ) :
    ∑ v, inflow P v = 0 := by
  unfold inflow
  rw [Finset.sum_comm]
  simp [Finset.sum_sub_distrib]

/-! ### The non-chords form a forest -/

theorem reflTransGen_joined_of_subset {C : Contraction nf nA κ} {S S' : Set (Line C)} (h : S ⊆ S')
    {u w : Fin N} (hr : ReflTransGen (Joined C S') u w) : ReflTransGen (Joined C S) u w := by
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih =>
    obtain ⟨g, hg, he⟩ := hbc
    exact ih.tail ⟨g, fun hg' => hg (h hg'), he⟩

/-- Paths of a relation each of whose steps is a step of an equivalence `R` or the edge `a b`:
their ends are related by `R`, or by `R` through the edge. -/
theorem reflTransGen_cases_of_step {α : Type*} {R r : α → α → Prop} (hrefl : ∀ x, R x x)
    (hsymm : ∀ {x y}, R x y → R y x) (htrans : ∀ {x y z}, R x y → R y z → R x z) {a b : α}
    (hstep : ∀ {u w}, r u w → R u w ∨ (u = a ∧ w = b) ∨ (u = b ∧ w = a)) {x y : α}
    (h : ReflTransGen r x y) : R x y ∨ (R x a ∧ R b y) ∨ (R x b ∧ R a y) := by
  induction h with
  | refl => exact Or.inl (hrefl x)
  | tail _ hzw ih =>
    rcases hstep hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases ih with ih | ih | ih
    · exact Or.inl (htrans ih h)
    · exact Or.inr (Or.inl ⟨ih.1, htrans ih.2 h⟩)
    · exact Or.inr (Or.inr ⟨ih.1, htrans ih.2 h⟩)
    · exact Or.inr (Or.inl ⟨ih, hrefl _⟩)
    · exact Or.inl (htrans ih.1 (hsymm ih.2))
    · exact Or.inl ih.1
    · exact Or.inr (Or.inr ⟨ih, hrefl _⟩)
    · exact Or.inl ih.1
    · exact Or.inl (htrans ih.1 (hsymm ih.2))

/-- The Kruskal step: if the non-chords of label above `m` form a forest, so do those of label at
least `m`. -/
theorem forest_step {C : Contraction nf nA κ} (m : ℕ)
    (ih : ∀ g : Line C, ¬ IsChord g → m + 1 ≤ g.label →
      ¬ ReflTransGen (Joined C {h | h = g ∨ IsChord h ∨ h.label < m + 1}) g.ends.1 g.ends.2) :
    ∀ g : Line C, ¬ IsChord g → m ≤ g.label →
      ¬ ReflTransGen (Joined C {h | h = g ∨ IsChord h ∨ h.label < m}) g.ends.1 g.ends.2 := by
  intro g hg hgm hr
  by_cases hf : ∃ f : Line C, ¬ IsChord f ∧ f.label = m
  · obtain ⟨f, hfc, hfm⟩ := hf
    have hlab : ∀ h : Line C, h.label = m → h = f := fun h hh =>
      Chord.label_injective (hh.trans hfm.symm)
    by_cases hgf : g = f
    · subst hgf
      refine hg (reflTransGen_joined_of_subset (fun h (hh : h.label ≤ g.label) => ?_) hr)
      rcases lt_or_eq_of_le hh with hh | hh
      · exact Or.inr (Or.inr (hfm ▸ hh))
      · exact Or.inl (hlab h (hh.trans hfm))
    · have hgm' : m + 1 ≤ g.label := by
        have : g.label ≠ m := fun h => hgf (hlab g h)
        omega
      have hmono : ∀ {u w : Fin N},
          ReflTransGen (Joined C {h | h = g ∨ IsChord h ∨ h.label < m + 1}) u w →
            ReflTransGen (Joined C {h : Line C | h.label ≤ f.label}) u w :=
        reflTransGen_joined_of_subset fun h (hh : h.label ≤ f.label) => Or.inr (Or.inr (by omega))
      have hgstep : Joined C {h : Line C | h.label ≤ f.label} g.ends.1 g.ends.2 :=
        ⟨g, fun hh => by
          change g.label ≤ f.label at hh
          omega, Or.inl rfl⟩
      have key := reflTransGen_cases_of_step
        (R := ReflTransGen (Joined C {h | h = g ∨ IsChord h ∨ h.label < m + 1}))
        (a := f.ends.1) (b := f.ends.2) (fun _ => .refl) reflTransGen_joined_symm
        (fun h1 h2 => h1.trans h2) ?_ hr
      · rcases key with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ih g hg hgm' h
        · exact hfc ((reflTransGen_joined_symm (hmono h1)).trans
            ((ReflTransGen.single hgstep).trans (reflTransGen_joined_symm (hmono h2))))
        · exact hfc ((hmono h2).trans ((ReflTransGen.single (joined_symm hgstep)).trans
            (hmono h1)))
      · rintro u w ⟨h, hh, he⟩
        by_cases hhf : h = f
        · subst hhf
          right
          rcases he with he | he
          · exact Or.inl ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
          · exact Or.inr ⟨(congrArg Prod.snd he).symm, (congrArg Prod.fst he).symm⟩
        · refine Or.inl (.single ⟨h, fun hh' => hh ?_, he⟩)
          rcases hh' with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
            · exact Or.inr (Or.inr h1)
            · exact absurd (hlab h h1) hhf
  · simp only [not_exists, not_and] at hf
    have hgm' : m + 1 ≤ g.label := by
      have := hf g hg
      omega
    refine ih g hg hgm' (reflTransGen_joined_of_subset (fun h hh => ?_) hr)
    rcases hh with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
      · exact Or.inr (Or.inr h1)
      · by_contra hc
        exact hf h (fun hch => hc (Or.inr (Or.inl hch))) h1

/-- **The non-chords form a forest**: the ends of a line that is not a chord are not joined by
lines other than itself that are not chords. -/
theorem not_reflTransGen_ends_of_not_isChord {C : Contraction nf nA κ} {f : Line C}
    (hf : ¬ IsChord f) :
    ¬ ReflTransGen (Joined C {g | g = f ∨ IsChord g}) f.ends.1 f.ends.2 := by
  have hall : ∀ n m : ℕ, (∀ g : Line C, g.label < m + n) → ∀ g : Line C, ¬ IsChord g →
      m ≤ g.label →
        ¬ ReflTransGen (Joined C {h | h = g ∨ IsChord h ∨ h.label < m}) g.ends.1 g.ends.2 := by
    intro n
    induction n with
    | zero =>
      intro m hm g _ hg
      have := hm g
      omega
    | succ n ihn =>
      intro m hm
      exact forest_step m (ihn (m + 1) fun g => by have := hm g; omega)
  have hB : ∀ g : Line C, g.label < 0 + Finset.univ.sup (fun g : Line C => g.label + 1) :=
    fun g => by
      have := Finset.le_sup (f := fun g : Line C => g.label + 1) (Finset.mem_univ g)
      omega
  intro hr
  refine hall _ 0 hB f hf (Nat.zero_le _) (reflTransGen_joined_of_subset (fun h hh => ?_) hr)
  rcases hh with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 (Nat.not_lt_zero _)

/-! ### Uniqueness: the cut at a non-chord -/

open scoped Classical in
/-- Summing the line momenta flowing into the vertices of the tail side of a non-chord `f`: only
`f`, which leaves it, and the chords cross its boundary. -/
theorem sum_inflow_tailSide {C : Contraction nf nA κ} (P : Line C → Fin 4 → ℝ) {f : Line C}
    (hf : ¬ IsChord f) :
    ∑ v ∈ Finset.univ.filter
        (fun v => ReflTransGen (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v), inflow P v =
      ∑ v ∈ Finset.univ.filter
          (fun v => ReflTransGen (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v),
        ∑ g ∈ Finset.univ.filter (fun g : Line C => IsChord g),
          ((if g.ends.2 = v then P g else 0) - (if g.ends.1 = v then P g else 0)) - P f := by
  set S := Finset.univ.filter
    (fun v => ReflTransGen (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v) with hS
  have hmem : ∀ v, v ∈ S ↔ ReflTransGen (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v :=
    fun v => by simp [hS]
  unfold inflow
  simp_rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : Line C => IsChord g)]
  rw [Finset.sum_add_distrib, sub_eq_add_neg]
  congr 1
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun g _ => (show ∑ v ∈ S, ((if g.ends.2 = v then P g else 0) -
      (if g.ends.1 = v then P g else 0)) =
        (if g.ends.2 ∈ S then P g else 0) - (if g.ends.1 ∈ S then P g else 0) by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq])]
  rw [Finset.sum_eq_single_of_mem f (by simp [hf])]
  · have h1 : f.ends.2 ∉ S := fun h => not_reflTransGen_ends_of_not_isChord hf ((hmem _).1 h)
    have h2 : f.ends.1 ∈ S := (hmem _).2 .refl
    simp [h1, h2]
  · intro g hg hgf
    have hgc : ¬ IsChord g := (Finset.mem_filter.mp hg).2
    have hj : Joined C {g | g = f ∨ IsChord g} g.ends.1 g.ends.2 :=
      ⟨g, fun h => h.elim hgf hgc, Or.inl rfl⟩
    have hiff : g.ends.2 ∈ S ↔ g.ends.1 ∈ S := by
      rw [hmem, hmem]
      exact ⟨fun h => h.tail (joined_symm hj), fun h => h.tail hj⟩
    by_cases h : g.ends.1 ∈ S
    · simp [h, hiff.2 h]
    · simp [h, mt hiff.1 h]

/-- **Uniqueness of the routing** (O2-5 (i)): every momentum assignment that is conserved at every
vertex and gives each chord its loop momentum is `lineMomentum₂`. No connectedness and no
condition on the external momenta is assumed. -/
theorem eq_lineMomentum₂_of_isConserved {L : ℕ} {C : Contraction nf nA κ}
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} {ℓ : Fin L → Fin 4 → ℝ}
    {P : Line C → Fin 4 → ℝ} (hP : IsConserved C pOut pIn kIn P)
    (hchord : ∀ g, IsChord g → P g = chordMomentum ℓ g) (f : Line C) :
    P f = lineMomentum₂ C pOut pIn kIn ℓ f := by
  classical
  unfold lineMomentum₂
  split_ifs with hf
  · exact hchord f hf
  · have hcut := sum_inflow_tailSide P hf
    rw [Finset.sum_congr rfl fun v _ => eq_neg_of_add_eq_zero_left (hP v),
      Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun g hg => by
        rw [hchord g (Finset.mem_filter.mp hg).2], eq_sub_iff_add_eq] at hcut
    rw [Finset.sum_add_distrib, ← hcut, Finset.sum_neg_distrib]
    abel

/-! ### Conservation for connected contractions -/

/-- The line momenta flowing into the vertices, as a linear map of the line momenta. -/
noncomputable def inflowLin (C : Contraction nf nA κ) :
    (Line C → Fin 4 → ℝ) →ₗ[ℝ] (Fin N → Fin 4 → ℝ) where
  toFun P := inflow P
  map_add' P Q := by
    funext v
    simp only [inflow, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp [add_comm]
  map_smul' c P := by
    funext v
    simp only [inflow, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp

open scoped Classical in
/-- Momenta on the non-chords, extended by zero to the chords. -/
noncomputable def extendLin (C : Contraction nf nA κ) :
    ({g : Line C // ¬ IsChord g} → Fin 4 → ℝ) →ₗ[ℝ] (Line C → Fin 4 → ℝ) where
  toFun Q g := if h : IsChord g then 0 else Q ⟨g, h⟩
  map_add' Q Q' := by
    funext g
    by_cases h : IsChord g <;> simp [h]
  map_smul' c Q := by
    funext g
    by_cases h : IsChord g <;> simp [h]

theorem extendLin_apply_of_isChord {C : Contraction nf nA κ}
    (Q : {g : Line C // ¬ IsChord g} → Fin 4 → ℝ) {g : Line C} (hg : IsChord g) :
    extendLin C Q g = 0 := by
  simp [extendLin, hg]

theorem extendLin_apply_of_not_isChord {C : Contraction nf nA κ}
    (Q : {g : Line C // ¬ IsChord g} → Fin 4 → ℝ) {g : Line C} (hg : ¬ IsChord g) :
    extendLin C Q g = Q ⟨g, hg⟩ := by
  simp [extendLin, hg]

/-- The incidence map of the non-chords is injective: a conserved assignment without
injections that vanishes on the chords vanishes. -/
theorem injective_inflowLin_comp_extendLin (C : Contraction nf nA κ) :
    Function.Injective ((inflowLin C).comp (extendLin C)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Q hQ
  funext ⟨f, hf⟩
  have h1 : ∀ v, inflow (extendLin C Q) v = 0 := fun v => congrFun hQ v
  have hcut := sum_inflow_tailSide (extendLin C Q) hf
  simp only [h1, Finset.sum_const_zero] at hcut
  rw [Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun g hg => by
    rw [extendLin_apply_of_isChord Q (Finset.mem_filter.mp hg).2, ite_self, ite_self, sub_zero],
    zero_sub, extendLin_apply_of_not_isChord Q hf] at hcut
  exact neg_eq_zero.mp hcut.symm

/-- The sum of the vertex injections, as a linear map. -/
noncomputable def sumLin (N : ℕ) : (Fin N → Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun J := ∑ v, J v
  map_add' J J' := by simp [Finset.sum_add_distrib]
  map_smul' c J := by simp [Finset.smul_sum]

theorem sumLin_apply (J : Fin N → Fin 4 → ℝ) : sumLin N J = ∑ v, J v :=
  rfl

/-- With at least one vertex, the injections summing to zero have dimension `4 (V - 1)`. -/
theorem finrank_ker_sumLin_add (hN : 0 < N) :
    Module.finrank ℝ (LinearMap.ker (sumLin N)) + 4 = N * 4 := by
  have hsurj : Function.Surjective (sumLin N) := fun x =>
    ⟨fun v => if v = ⟨0, hN⟩ then x else 0, by simp [sumLin_apply]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (sumLin N)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
  simp [Module.finrank_pi_fintype] at h
  omega

/-- The line momenta flowing into the vertices sum to zero. -/
theorem range_inflowLin_comp_extendLin_le (C : Contraction nf nA κ) :
    LinearMap.range ((inflowLin C).comp (extendLin C)) ≤ LinearMap.ker (sumLin N) := by
  rintro _ ⟨Q, rfl⟩
  rw [LinearMap.mem_ker, sumLin_apply]
  exact sum_inflow _

theorem finrank_range_inflowLin_comp_extendLin (C : Contraction nf nA κ) :
    Module.finrank ℝ (LinearMap.range ((inflowLin C).comp (extendLin C))) =
      Nat.card {g : Line C // ¬ IsChord g} * 4 := by
  classical
  rw [LinearMap.finrank_range_of_inj (injective_inflowLin_comp_extendLin C)]
  simp [Module.finrank_pi_fintype, Nat.card_eq_fintype_card]

/-- **At most `V - 1` lines are not chords**, for a contraction with at least one vertex: they
form a forest. -/
theorem card_nonChord_add_one_le (C : Contraction nf nA κ) (hN : 0 < N) :
    Nat.card {g : Line C // ¬ IsChord g} + 1 ≤ N := by
  have h1 := Submodule.finrank_mono (range_inflowLin_comp_extendLin_le C)
  have h2 := finrank_ker_sumLin_add hN
  rw [finrank_range_inflowLin_comp_extendLin] at h1
  omega

/-- **Momentum conservation of the routing** (O2-5 (i)): for a contraction with connected
vertices (X₁₇) whose external momenta (X₁₉) sum to zero, `lineMomentum₂` is conserved at every
vertex: the incoming minus the outgoing line momenta plus the external momentum is `0`. -/
theorem isConserved_lineMomentum₂ {L : ℕ} {C : Contraction nf nA κ} (hV : VerticesConnected C)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) (ℓ : Fin L → Fin 4 → ℝ) :
    IsConserved C pOut pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro v
    exact v.elim0
  have hker := finrank_ker_sumLin_add hN
  have hrange := finrank_range_inflowLin_comp_extendLin C
  have hcard := card_le_card_nonChord_add_one hV
  have heq : LinearMap.range ((inflowLin C).comp (extendLin C)) = LinearMap.ker (sumLin N) :=
    Submodule.eq_of_le_of_finrank_le (range_inflowLin_comp_extendLin_le C) (by omega)
  set chordPart : Line C → Fin 4 → ℝ := fun g => if IsChord g then chordMomentum ℓ g else 0
    with hchordPart
  have hJ : (fun v => -(externalMomentum C pOut pIn kIn v + inflow chordPart v)) ∈
      LinearMap.ker (sumLin N) := by
    rw [LinearMap.mem_ker, sumLin_apply, Finset.sum_neg_distrib, Finset.sum_add_distrib, hsum,
      sum_inflow, add_zero, neg_zero]
  rw [← heq] at hJ
  obtain ⟨Q, hQ⟩ := hJ
  have hPc : IsConserved C pOut pIn kIn (chordPart + extendLin C Q) := by
    intro v
    have h := congrFun ((inflowLin C).map_add chordPart (extendLin C Q)) v
    have hQv := congrFun hQ v
    change inflow (chordPart + extendLin C Q) v = inflow chordPart v + inflow (extendLin C Q) v
      at h
    change inflow (extendLin C Q) v = -(externalMomentum C pOut pIn kIn v + inflow chordPart v)
      at hQv
    rw [h, hQv]
    abel
  have hPeq : chordPart + extendLin C Q = lineMomentum₂ C pOut pIn kIn ℓ :=
    funext (eq_lineMomentum₂_of_isConserved hPc fun g hg => by
      simp [hchordPart, hg, extendLin_apply_of_isChord Q hg])
  rw [← hPeq]
  exact hPc

end QED.TwoLoop.Routing

end
