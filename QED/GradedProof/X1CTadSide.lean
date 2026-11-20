/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CTadpole
import QED.TwoLoop.LoopBound
import QED.TwoLoop.EnumerationRelabel
import QED.TwoLoop.ChordLoopLine

/-!
# (X₁) piece C: the tadpole side of a photon bridge

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C4 (graph side). `contractionValue_eq_zero_of_tadSide` kills the
value of a contraction with a set `T` of vertices (`TadSide`) crossed by exactly one line. This
file builds `TadSide` from graph data.

* `tadSide_of_crossing`: if exactly one line crosses the boundary of `T`, it is a photon line, and
  no external field is attached to `T`, then `TadSide C T`. Closedness: a fermion line with one
  end in `T` would cross. Parity: the photon fields of `T` other than the end of the crossing
  line are paired among themselves by the photon pairing (`Finset.sum_involution` in `ZMod 2`),
  so `T` has an odd number of photon fields; a `gauge` or `gaugeCt` vertex has one, a `photonCt`
  vertex two and a `fermionCt` vertex none.
* `tadSide_of_isBridge`: for a photon bridge `g` and one of its ends `w`, the vertices joined to
  `w` without `g` (`tadComp`) are crossed only by `g`; if no external is attached to them, they
  form a tadpole side.
* `contractionValue_eq_zero_of_isBridge`: then the value vanishes (any grading, no
  integrability), from `contractionValue_eq_zero_of_tadSide`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line FermionLine PhotonLine VerticesConnected Joined
  IsBridge externalMomentum)
open QED.Graded
open QED.GradedProof.X0 (isZ)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 nA κ}

/-! ### Photon fields and photon lines -/

/-- Two paired photon fields are the ends of a photon line. -/
theorem tadSide_photon_pair {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    ∃ l : PhotonLine C, (l.1 = a ∧ l.head = b) ∨ (l.1 = b ∧ l.head = a) := by
  rcases lt_trichotomy (Wick.photonKey a) (Wick.photonKey b) with hab | hab | hab
  · exact ⟨⟨a, b, h, hab⟩, Or.inl ⟨rfl, QED.TwoLoop.Enumeration.head_eq _ h⟩⟩
  · obtain rfl := QED.TwoLoop.Chord.photonKey_injective hab
    exact absurd h (C.2 _).2
  · have h' : C.1.2 (.inr b) = .inr a := by rw [← h, (C.2 _).1]
    exact ⟨⟨b, a, h', hab⟩, Or.inr ⟨rfl, QED.TwoLoop.Enumeration.head_eq _ h'⟩⟩

/-- The partner of a photon field under the photon pairing (itself if external). -/
def tadSide_partner (C : Contraction 1 nA κ) (a : Wick.PhotonSlot κ) : Wick.PhotonSlot κ :=
  match C.1.2 (.inr a) with
  | .inr b => b
  | .inl _ => a

theorem tadSide_partner_eq {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    tadSide_partner C a = b := by
  unfold tadSide_partner
  rw [h]

variable {T : Fin N → Prop} [DecidablePred T]

/-- Two pairs of photon fields, each with exactly the first field in `T`, have the same first
field when only `g` crosses the boundary of `T`. -/
theorem tadSide_eq_of_crossing {g : PhotonLine C}
    (hone : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → l = .inr g) {a b a' b' : Wick.PhotonSlot κ}
    (h : C.1.2 (.inr a) = .inr b) (ha : T a.1) (hb : ¬ T b.1)
    (h' : C.1.2 (.inr a') = .inr b') (ha' : T a'.1) (hb' : ¬ T b'.1) : a = a' := by
  obtain ⟨l, hl⟩ := tadSide_photon_pair h
  obtain ⟨l', hl'⟩ := tadSide_photon_pair h'
  have e1 : (Sum.inr l : Line C) = .inr g := hone _ (by
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [Line.ends, h1, h2] <;> tauto)
  have e2 : (Sum.inr l' : Line C) = .inr g := hone _ (by
    rcases hl' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [Line.ends, h1, h2] <;> tauto)
  obtain rfl := Sum.inr_injective e1
  obtain rfl := Sum.inr_injective e2
  rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hl' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact h1.symm.trans h3
  · exact absurd ((h1.symm.trans h3) ▸ ha) hb'
  · exact absurd ((h2.symm.trans h4) ▸ ha) hb'
  · exact h2.symm.trans h4

/-! ### The parity of a tadpole side -/

/-- The photon fields at the vertices of `T`. -/
theorem tadSide_card_slots :
    (Finset.univ.filter fun a : Wick.PhotonSlot κ => T a.1).card =
      ∑ t ∈ Finset.univ.filter T, (κ t).photonSlots := by
  have hs : (Finset.univ.filter fun a : Wick.PhotonSlot κ => T a.1) =
      (Finset.univ.filter T).sigma fun _ => Finset.univ := by
    ext ⟨t, i⟩
    simp
  rw [hs, Finset.card_sigma]
  simp

/-- The parity of the photon fields of `T` is that of its `gauge` and `gaugeCt` vertices. -/
theorem tadSide_slots_mod_two :
    (∑ t ∈ Finset.univ.filter T, (κ t).photonSlots) % 2 =
      ((Finset.univ.filter T).filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card % 2 := by
  have hk : ∀ k : Wick.VertexKind,
      k.photonSlots % 2 = (if k = .gauge ∨ k = .gaugeCt then 1 else 0) % 2 := by
    intro k
    cases k <;> decide
  rw [Finset.card_filter, Finset.sum_nat_mod,
    Finset.sum_nat_mod _ 2 (fun t => if κ t = .gauge ∨ κ t = .gaugeCt then 1 else 0)]
  simp only [hk]

/-- The `gauge` and `gaugeCt` vertices of `T`, counted through their fermion fields. -/
theorem tadSide_card_gauge :
    (Finset.univ.filter fun s : {s : Wick.FermionVertex κ // T s.1} =>
      κ s.1.1 = .gauge ∨ κ s.1.1 = .gaugeCt).card =
      ((Finset.univ.filter T).filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card := by
  refine Finset.card_bij (fun s _ => s.1.1) (fun s hs => ?_) (fun s _ s' _ h => ?_)
    (fun t ht => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨s.2, hs⟩
  · exact Subtype.ext (Subtype.ext h)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hne : κ t ≠ .photonCt := by rcases ht.2 with h | h <;> rw [h] <;> decide
    exact ⟨⟨⟨t, hne⟩, ht.1⟩, by simp [ht.2], rfl⟩

/-- **A set crossed by one photon line, with no external attached, is a tadpole side.** -/
theorem tadSide_of_crossing (g : PhotonLine C)
    (hone : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → l = .inr g)
    (hcross : ¬ (T g.1.1 ↔ T g.head.1))
    (hfo : ∀ s, C.1.1 (.inl 0) = .inr s → ¬ T s.1)
    (hfi : ∀ s, C.1.1 (.inr s) = .inl 0 → ¬ T s.1)
    (hph : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1) : TadSide C T := by
  refine ⟨fun x => ?_, hph, ?_⟩
  · rcases x with i | s
    · obtain rfl := Subsingleton.elim i 0
      rcases h : C.1.1 (.inl 0) with j | s
      · rfl
      · simp [isZ, hfo s h]
    · rcases h : C.1.1 (.inr s) with j | s'
      · obtain rfl := Subsingleton.elim j 0
        simp [isZ, hfi s h]
      · have hiff : T s'.1 ↔ T s.1 := by
          by_contra hne
          have hl := hone (.inl ⟨s, by rw [h]; rfl⟩) (by
            simp only [Line.ends]
            rwa [QED.TwoLoop.Enumeration.tail_eq _ h])
          exact absurd hl (by simp)
        simp only [isZ]
        exact decide_eq_decide.mpr hiff
  · -- the end `a₀` of `g` in `T`, paired with the end `a₁` outside `T`
    obtain ⟨a₀, a₁, hT0, hT1, hτ⟩ : ∃ a₀ a₁ : Wick.PhotonSlot κ,
        T a₀.1 ∧ ¬ T a₁.1 ∧ C.1.2 (.inr a₀) = .inr a₁ := by
      by_cases h1 : T g.1.1
      · exact ⟨g.1, g.head, h1, fun h2 => hcross ⟨fun _ => h2, fun _ => h1⟩,
          QED.TwoLoop.LoopBound.apply_inr_photonLine g⟩
      · exact ⟨g.head, g.1, by tauto, h1, QED.TwoLoop.LoopBound.apply_inr_head g⟩
    set SA := Finset.univ.filter fun a : Wick.PhotonSlot κ => T a.1 with hSA
    have hmem : a₀ ∈ SA := by simp [hSA, hT0]
    -- every other field of `T` is paired inside `T`, with a field other than `a₀`
    have key : ∀ a ∈ SA.erase a₀, C.1.2 (.inr a) = .inr (tadSide_partner C a) ∧
        tadSide_partner C a ∈ SA.erase a₀ := by
      intro a ha
      obtain ⟨hne, ha⟩ := Finset.mem_erase.1 ha
      have haT : T a.1 := (Finset.mem_filter.1 ha).2
      obtain ⟨b, hb⟩ : ∃ b, C.1.2 (.inr a) = .inr b := by
        rcases h : C.1.2 (.inr a) with j | b
        · have h' : C.1.2 (.inl j) = .inr a := by rw [← h, (C.2 _).1]
          exact absurd haT (hph j a h')
        · exact ⟨b, rfl⟩
      rw [tadSide_partner_eq hb]
      refine ⟨hb, Finset.mem_erase.2 ⟨fun hb0 => ?_, ?_⟩⟩
      · subst hb0
        have h' : C.1.2 (.inr b) = .inr a := by rw [← hb, (C.2 _).1]
        rw [hτ] at h'
        exact hT1 (Sum.inr_injective h' ▸ haT)
      · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        by_contra hbT
        exact hne (tadSide_eq_of_crossing hone hb haT hbT hτ hT0 hT1)
    have hsum : ∑ a ∈ SA.erase a₀, (1 : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun a _ => tadSide_partner C a) (fun _ _ => by decide)
        (fun a ha _ hfix => ?_) (fun a ha => (key a ha).2) (fun a ha => ?_)
      · have h := (key a ha).1
        rw [hfix] at h
        exact (C.2 _).2 h
      · have h := (key a ha).1
        have h' : C.1.2 (.inr (tadSide_partner C a)) = .inr a := by rw [← h, (C.2 _).1]
        exact tadSide_partner_eq h'
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even] at hsum
    have hcard := Finset.card_erase_add_one hmem
    have h1 : SA.card = _ := tadSide_card_slots (κ := κ) (T := T)
    have h2 := tadSide_slots_mod_two (κ := κ) (T := T)
    rw [tadSide_card_gauge, Nat.odd_iff]
    obtain ⟨m, hm⟩ := hsum
    omega

/-! ### The side of a photon bridge -/

/-- The vertices joined to `w` without the line `g`. -/
def tadComp (C : Contraction 1 nA κ) (g : PhotonLine C) (w v : Fin N) : Prop :=
  Relation.ReflTransGen (Joined C {(.inr g : Line C)}) w v

theorem tadComp_symm {g : PhotonLine C} {u v : Fin N}
    (h : Relation.ReflTransGen (Joined C {(.inr g : Line C)}) u v) :
    Relation.ReflTransGen (Joined C {(.inr g : Line C)}) v u := by
  induction h with
  | refl => exact .refl
  | tail _ hJ ih =>
    obtain ⟨f, hf, he⟩ := hJ
    exact Relation.ReflTransGen.head ⟨f, hf, he.symm⟩ ih

/-- Only `g` crosses the boundary of `tadComp C g w`. -/
theorem tadComp_crossing (g : PhotonLine C) (w : Fin N) (l : Line C)
    (hl : ¬ (tadComp C g w l.ends.1 ↔ tadComp C g w l.ends.2)) : l = .inr g := by
  by_contra hne
  have hJ : Joined C {(.inr g : Line C)} l.ends.1 l.ends.2 := ⟨l, hne, Or.inl rfl⟩
  have hJ' : Joined C {(.inr g : Line C)} l.ends.2 l.ends.1 := ⟨l, hne, Or.inr rfl⟩
  exact hl ⟨fun h => h.tail hJ, fun h => h.tail hJ'⟩

/-- A photon bridge crosses the boundary of the side of either of its ends. -/
theorem tadComp_bridge {g : PhotonLine C} (hb : IsBridge (.inr g : Line C)) {w : Fin N}
    (hw : w = g.1.1 ∨ w = g.head.1) : ¬ (tadComp C g w g.1.1 ↔ tadComp C g w g.head.1) := by
  intro hiff
  apply hb
  simp only [Line.ends]
  rcases hw with rfl | rfl
  · exact hiff.1 Relation.ReflTransGen.refl
  · exact tadComp_symm (hiff.2 Relation.ReflTransGen.refl)

open scoped Classical in
/-- **The side of a photon bridge with no external attached is a tadpole side.** -/
theorem tadSide_of_isBridge {g : PhotonLine C} (hb : IsBridge (.inr g : Line C)) {w : Fin N}
    (hw : w = g.1.1 ∨ w = g.head.1)
    (hfo : ∀ s, C.1.1 (.inl 0) = .inr s → ¬ tadComp C g w s.1)
    (hfi : ∀ s, C.1.1 (.inr s) = .inl 0 → ¬ tadComp C g w s.1)
    (hph : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ tadComp C g w a.1) :
    TadSide C (tadComp C g w) :=
  tadSide_of_crossing g (tadComp_crossing g w) (tadComp_bridge hb hw) hfo hfi hph

open scoped Classical in
/-- **A contraction with a photon bridge whose side has no external has value `0`** (any
grading, no integrability). -/
theorem contractionValue_eq_zero_of_isBridge (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (gr : Grading κ) {g : PhotonLine C}
    (hb : IsBridge (.inr g : Line C)) {w : Fin N} (hw : w = g.1.1 ∨ w = g.head.1)
    (hfo : ∀ s, C.1.1 (.inl 0) = .inr s → ¬ tadComp C g w s.1)
    (hfi : ∀ s, C.1.1 (.inr s) = .inl 0 → ¬ tadComp C g w s.1)
    (hph : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ tadComp C g w a.1) (hV : VerticesConnected C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (hs : ∑ v, externalMomentum C pOut pIn kIn v = 0) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) : contractionValue P Φ D C gr pOut pIn kIn αOut βIn μ = 0 :=
  contractionValue_eq_zero_of_tadSide P Φ D gr (tadSide_of_isBridge hb hw hfo hfi hph)
    (tadComp_crossing g w) hV pOut pIn kIn hs αOut βIn μ

end QED.GradedProof.X1C

end
