/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.Embed
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.IsOnePI
import QED.TwoLoop.LoopBound
import QED.TwoLoop.LoopBoundTwoExact
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card

/-!
# A counterterm on a closed fermion loop costs a loop

The combinatorial input of the embedding goals (E-G₁), (E-G₃), (E-G₅) of the Phase 5 Stage 2
packet (decision D-57): in the range of orders of these goals, every counterterm vertex with
fermion fields lies on the fermion line of an external field (`CtReaches`).

* `card_le_card_add_one`: if the lines outside `S` connect the vertices, then
  `V ≤ #(lines outside S) + 1`.
* A fermion line on a closed fermion cycle is never needed for connectivity: its ends are joined
  by the other lines of the cycle (`reflTransGen_ends_fline`).
* `one_le_loopCount`: with connected vertices, a closed fermion cycle gives `loopCount ≥ 1`.
* `two_le_loopCount`: for a 1PI contraction with an external fermion, a closed fermion cycle
  gives `loopCount ≥ 2`: delete a line of the cycle and a line leaving the cycle's vertices
  (which is not a bridge).
* `two_mul_loopCount_add_le_sum_order`: by the loop formula
  `2 · loopCount + 2 nf + nA = V₃ + 2` (O2-5 (iii)) and `∑ order = V₃ + 2 #(counterterms)`, a
  contraction with a counterterm vertex has `2 · loopCount + 2 nf + nA ≤ ∑ order`.
* Hence `ctReaches_of_connected` (order `< 2 nf + nA + 2`) and `ctReaches_of_isOnePI`
  (order `< 2 nf + nA + 4`, `nf ≥ 1`).
-/

@[expose] public section

open Relation
open QED.WickModel (Contraction Line FermionLine PhotonLine Joined VerticesConnected
  ExternalsAttached IsOnePI IsBridge loopCount)

namespace QED.GradedProof

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Counting the lines that connect the vertices -/

/-- The simple graph on the vertices whose edges are the lines outside `S`. -/
def outsideGraph (C : Contraction nf nA κ) (S : Set (Line C)) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (Joined C S)

theorem outsideGraph_reachable {C : Contraction nf nA κ} {S : Set (Line C)}
    (hS : ∀ u w, ReflTransGen (Joined C S) u w) (u w : Fin N) :
    (outsideGraph C S).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hS u w with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    by_cases hb : b = c
    · exact hb ▸ ih
    · exact ih.tail ⟨hb, Or.inl hbc⟩

theorem exists_line_of_mem_edgeSet {C : Contraction nf nA κ} {S : Set (Line C)}
    (e : (outsideGraph C S).edgeSet) :
    ∃ g : {g : Line C // g ∉ S}, s(g.1.ends.1, g.1.ends.2) = e.1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u w =>
    obtain ⟨-, h | h⟩ := he
    · obtain ⟨g, hg, hends | hends⟩ := h
      · exact ⟨⟨g, hg⟩, by simp [hends]⟩
      · exact ⟨⟨g, hg⟩, by simp [hends, Sym2.eq_swap]⟩
    · obtain ⟨g, hg, hends | hends⟩ := h
      · exact ⟨⟨g, hg⟩, by simp [hends, Sym2.eq_swap]⟩
      · exact ⟨⟨g, hg⟩, by simp [hends]⟩

theorem card_edgeSet_outsideGraph_le (C : Contraction nf nA κ) (S : Set (Line C)) :
    Nat.card (outsideGraph C S).edgeSet ≤ Nat.card {g : Line C // g ∉ S} := by
  choose F hF using exists_line_of_mem_edgeSet (C := C) (S := S)
  refine Nat.card_le_card_of_injective F fun e e' h => Subtype.ext ?_
  rw [← hF e, ← hF e', h]

/-- **If the lines outside `S` connect the vertices, there are at least `V - 1` of them.** -/
theorem card_le_card_add_one {C : Contraction nf nA κ} {S : Set (Line C)}
    (hS : ∀ u w, ReflTransGen (Joined C S) u w) :
    N ≤ Nat.card {g : Line C // g ∉ S} + 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · omega
  have hconn : (outsideGraph C S).Connected :=
    { preconnected := outsideGraph_reachable hS
      nonempty := ⟨⟨0, hN⟩⟩ }
  have := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_fin] at this
  have := card_edgeSet_outsideGraph_le C S
  omega

theorem card_compl_add (C : Contraction nf nA κ) (S : Set (Line C)) :
    Nat.card {g : Line C // g ∉ S} + S.ncard = Nat.card (Line C) := by
  have h := Set.ncard_add_ncard_compl S
  rw [← Nat.card_coe_set_eq Sᶜ] at h
  change S.ncard + Nat.card {g : Line C // g ∉ S} = _ at h
  omega

/-! ### Closed fermion cycles -/

section Cycle

variable {C : Contraction nf nA κ} {t : Wick.FermionVertex κ}

theorem sameCycle_of_apply_eq' {α : Type} {σ : Equiv.Perm α} {a b : α} (h : σ a = b) :
    σ.SameCycle a b :=
  h ▸ Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl σ a)

/-- On a cycle without external field, the `Ψ` of every vertex is contracted with a vertex. -/
theorem isRight_of_sameCycle (hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t))
    {a : Wick.FermionVertex κ} (ha : C.1.1.SameCycle (.inr a) (.inr t)) :
    (C.1.1 (.inr a)).isRight := by
  rcases h : C.1.1 (.inr a) with i | b
  · exact absurd ((sameCycle_of_apply_eq' h).symm.trans ha) (hZ i)
  · rfl

theorem apply_eq_inr_getRight {a : Wick.FermionVertex κ} (ha : (C.1.1 (.inr a)).isRight) :
    C.1.1 (.inr a) = .inr ((C.1.1 (.inr a)).getRight ha) :=
  (Sum.inr_getRight _ ha).symm

/-- **The lines of a closed cycle join its vertices.** Following the cycle from `x` to `t`,
every step is a fermion line of the cycle starting at a vertex other than `t`. -/
theorem reflTransGen_of_cycle (hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t))
    {T : Set (Line C)}
    (hT : ∀ (a : Wick.FermionVertex κ) (ha : (C.1.1 (.inr a)).isRight),
      C.1.1.SameCycle (.inr a) (.inr t) → a ≠ t → (.inl ⟨a, ha⟩ : Line C) ∉ T) :
    ∀ (n : ℕ) (x : Wick.FermionVertex κ), C.1.1.SameCycle (.inr x) (.inr t) →
      (C.1.1 ^ n) (.inr x) = .inr t → ReflTransGen (Joined C T) x.1 t.1 := by
  intro n
  induction n with
  | zero =>
    intro x _ h
    simp only [pow_zero, Equiv.Perm.coe_one, id_eq, Sum.inr.injEq] at h
    rw [h]
  | succ n ih =>
    intro x hx h
    by_cases hxt : x = t
    · rw [hxt]
    have hr := isRight_of_sameCycle hZ hx
    have hy := apply_eq_inr_getRight hr
    set y := (C.1.1 (.inr x)).getRight hr
    have hyc : C.1.1.SameCycle (.inr y) (.inr t) := (sameCycle_of_apply_eq' hy).symm.trans hx
    have h' : (C.1.1 ^ n) (.inr y) = .inr t := by
      rw [pow_succ, Equiv.Perm.mul_apply, hy] at h
      exact h
    have hj : Joined C T x.1 y.1 := ⟨.inl ⟨x, hr⟩, hT x hr hx hxt, Or.inr rfl⟩
    exact ReflTransGen.head hj (ih y hyc h')

/-- The fermion line at `t`, on a cycle without external field. -/
def fline (hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t)) : Line C :=
  .inl ⟨t, isRight_of_sameCycle hZ (Equiv.Perm.SameCycle.refl _ _)⟩

/-- **A fermion line of a closed cycle is not needed for connectivity.** -/
theorem reflTransGen_ends_fline (hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t))
    {T : Set (Line C)}
    (hT : ∀ (a : Wick.FermionVertex κ) (ha : (C.1.1 (.inr a)).isRight),
      C.1.1.SameCycle (.inr a) (.inr t) → a ≠ t → (.inl ⟨a, ha⟩ : Line C) ∉ T) :
    ReflTransGen (Joined C T) (fline hZ).ends.1 (fline hZ).ends.2 := by
  have hr := isRight_of_sameCycle hZ (Equiv.Perm.SameCycle.refl C.1.1 (.inr t))
  have hy := apply_eq_inr_getRight hr
  set s := (C.1.1 (.inr t)).getRight hr
  have hs : C.1.1.SameCycle (.inr s) (.inr t) :=
    (sameCycle_of_apply_eq' hy).symm
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  exact reflTransGen_of_cycle hZ hT n s hs hn

theorem ne_fline {hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t)} {a : Wick.FermionVertex κ}
    (ha : (C.1.1 (.inr a)).isRight) (hat : a ≠ t) : (.inl ⟨a, ha⟩ : Line C) ≠ fline hZ :=
  fun h => hat (congrArg (fun x : FermionLine C => x.1) (Sum.inl_injective h))

/-- **With connected vertices, a closed fermion cycle gives a loop.** -/
theorem one_le_loopCount (hV : VerticesConnected C)
    (hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t)) : 1 ≤ loopCount C := by
  have hconn : ∀ u w, ReflTransGen (Joined C {fline hZ}) u w := fun u w =>
    QED.TwoLoop.LoopBound.reflTransGen_joined_of_ends (fun g _ => by
      by_cases hg : g = fline hZ
      · subst hg
        exact reflTransGen_ends_fline hZ fun a ha _ hat hmem => ne_fline ha hat hmem
      · exact .single ⟨g, hg, Or.inl rfl⟩) (hV u w)
  have h1 := card_le_card_add_one hconn
  have h2 := card_compl_add C {fline hZ}
  rw [Set.ncard_singleton] at h2
  have h3 := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq hV (Fin.pos t.1)
  omega

/-- The vertices of the fermion fields on the cycle of `t`. -/
def CycleVertex (C : Contraction nf nA κ) (t : Wick.FermionVertex κ) (v : Fin N) : Prop :=
  ∃ a : Wick.FermionVertex κ, a.1 = v ∧ C.1.1.SameCycle (.inr a) (.inr t)

theorem exists_cross {α : Type} {r : α → α → Prop} {p : α → Prop} {a b : α}
    (h : ReflTransGen r a b) (ha : p a) (hb : ¬ p b) : ∃ x y, r x y ∧ p x ∧ ¬ p y := by
  induction h with
  | refl => exact absurd ha hb
  | @tail b c _ hbc ih =>
    by_cases hpb : p b
    · exact ⟨b, c, hbc, hpb, hb⟩
    · exact ih hpb

/-- Both ends of a fermion line of the cycle are vertices of the cycle. -/
theorem cycleVertex_ends {a : Wick.FermionVertex κ} (ha : (C.1.1 (.inr a)).isRight)
    (hac : C.1.1.SameCycle (.inr a) (.inr t)) :
    CycleVertex C t (Line.ends (.inl ⟨a, ha⟩ : Line C)).1 ∧
      CycleVertex C t (Line.ends (.inl ⟨a, ha⟩ : Line C)).2 := by
  have hy := apply_eq_inr_getRight ha
  refine ⟨⟨(C.1.1 (.inr a)).getRight ha, rfl, (sameCycle_of_apply_eq' hy).symm.trans hac⟩,
    ⟨a, rfl, hac⟩⟩

/-- **For a 1PI contraction with an external fermion, a closed fermion cycle gives two loops.** -/
theorem two_le_loopCount (hC : IsOnePI C) (i₀ : Fin nf)
    (hZ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr t)) : 2 ≤ loopCount C := by
  classical
  have hA := hC.1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, C.1.1 (.inl i₀) = .inr s₀ := by
    rcases h : C.1.1 (.inl i₀) with j | s
    · exact absurd h (hA.1 i₀ j)
    · exact ⟨s, rfl⟩
  have hout : ¬ CycleVertex C t s₀.1 := by
    rintro ⟨a, ha, hac⟩
    have has : a = s₀ := Subtype.ext ha
    subst has
    exact hZ i₀ ((sameCycle_of_apply_eq' hs₀).trans hac)
  have hin : CycleVertex C t t.1 := ⟨t, rfl, Equiv.Perm.SameCycle.refl _ _⟩
  obtain ⟨x, y, ⟨g, -, hends⟩, hx, hy⟩ := exists_cross (hC.2.1 t.1 s₀.1) hin hout
  -- `g` leaves the cycle's vertices, so it is not a fermion line of the cycle
  have hgne : ∀ (a : Wick.FermionVertex κ) (ha : (C.1.1 (.inr a)).isRight),
      C.1.1.SameCycle (.inr a) (.inr t) → (.inl ⟨a, ha⟩ : Line C) ≠ g := by
    intro a ha hac hag
    have := cycleVertex_ends ha hac
    rw [hag] at this
    rcases hends with h | h <;> rw [h] at this
    · exact hy this.2
    · exact hy this.1
  have hfg : fline hZ ≠ g := hgne t _ (Equiv.Perm.SameCycle.refl _ _)
  -- without `g` the vertices stay connected
  have hg : ReflTransGen (Joined C {g}) g.ends.1 g.ends.2 := by
    by_contra h
    exact hC.2.2 g h
  have hconn : ∀ u w, ReflTransGen (Joined C {fline hZ, g}) u w := by
    intro u w
    have h1 : ReflTransGen (Joined C {g}) u w :=
      QED.TwoLoop.LoopBound.reflTransGen_joined_of_ends (fun l _ => by
        by_cases hl : l = g
        · subst hl
          exact hg
        · exact .single ⟨l, hl, Or.inl rfl⟩) (hC.2.1 u w)
    refine QED.TwoLoop.LoopBound.reflTransGen_joined_of_ends (fun l hl => ?_) h1
    by_cases hlf : l = fline hZ
    · subst hlf
      refine reflTransGen_ends_fline hZ fun a ha hac hat hmem => ?_
      rcases hmem with h | h
      · exact ne_fline ha hat h
      · exact hgne a ha hac h
    · refine .single ⟨l, ?_, Or.inl rfl⟩
      rintro (h | h)
      · exact hlf h
      · exact hl h
  have h1 := card_le_card_add_one hconn
  have h2 := card_compl_add C {fline hZ, g}
  rw [Set.ncard_pair hfg] at h2
  have h3 := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq hC.2.1 (Fin.pos t.1)
  omega

end Cycle

/-! ### The order of a contraction with a counterterm vertex -/

/-- The order (V₁) of a vertex sequence is the number of `gauge` and `gaugeCt` vertices plus twice
the number of counterterm vertices. -/
theorem sum_order_eq (κ : Fin N → Wick.VertexKind) :
    ∑ t, (κ t).order = (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card +
      2 * (Finset.univ.filter fun t => κ t ≠ .gauge).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by cases κ t <;> rfl

/-- **A counterterm vertex costs two orders.** With attached externals and connected vertices,
`2 · loopCount + 2 nf + nA ≤ ∑ order` as soon as there is a counterterm vertex. -/
theorem two_mul_loopCount_add_le_sum_order {C : Contraction nf nA κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (t : Fin N) (ht : κ t ≠ .gauge) :
    2 * loopCount C + 2 * nf + nA ≤ ∑ t, (κ t).order := by
  have h1 := QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq hA hV (Fin.pos t)
  have h2 := sum_order_eq κ
  have h3 : 1 ≤ (Finset.univ.filter fun t => κ t ≠ .gauge).card :=
    Finset.card_pos.2 ⟨t, by simp [ht]⟩
  omega

/-- **Below order `2 nf + nA + 2`, a connected contraction has its counterterm vertices on the
lines of the external fermions.** -/
theorem ctReaches_of_connected {C : Contraction nf nA κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (h : ∑ t, (κ t).order < 2 * nf + nA + 2) : CtReaches C := by
  intro t ht
  by_contra hne
  push Not at hne
  have h1 := one_le_loopCount hV hne
  have h2 := two_mul_loopCount_add_le_sum_order hA hV t.1 ht
  omega

/-- **Below order `2 nf + nA + 4`, a 1PI contraction with an external fermion has its
counterterm vertices on the lines of the external fermions.** -/
theorem ctReaches_of_isOnePI {C : Contraction nf nA κ} (hC : IsOnePI C) (hnf : 1 ≤ nf)
    (h : ∑ t, (κ t).order < 2 * nf + nA + 4) : CtReaches C := by
  intro t ht
  by_contra hne
  push Not at hne
  have h1 := two_le_loopCount hC ⟨0, hnf⟩ hne
  have h2 := two_mul_loopCount_add_le_sum_order hC.1 hC.2.1 t.1 ht
  omega

end QED.GradedProof

end
