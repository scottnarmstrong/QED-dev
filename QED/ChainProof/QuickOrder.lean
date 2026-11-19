/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Wick.VertexKindPhotonSlots
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.BigOperators.Fin

/-!
# A vacuum-polarization chain has total order `2n + 3`

For the chain predicate (C₁) `QED.VPChain.IsVPChain n`, every vertex is a `gauge` or a `photonCt`
vertex, whose order (V₁) equals its number of photon fields (V₂); so the total order is the number
of photon fields. The photon fields are exactly the field `sb` of the middle vertex and the fields
`src i`, `dst i` (`i ≤ n`) of the chain, and these `2n + 3` fields are distinct: the walk
`src 0, dst 0, src 1, …, dst n` alternates the photon pairing and the insertion pairing, both
fixed-point-free and functional, and starts and ends at the open line.

* `QED.ChainProof.Quick.order_sum_of_isVPChain`: `IsVPChain n C → ∑ t, (κ t).order = 2 * n + 3`.
* `QED.ChainProof.Quick.le_sum_order`: every sequence of `N` vertices has total order at least `N`.
-/

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ChainProof.Quick

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- Every vertex has order at least one, so `N` vertices have total order at least `N`. -/
theorem le_sum_order (κ : Fin N → Wick.VertexKind) : N ≤ ∑ t, (κ t).order := by
  have h : ∀ t, 1 ≤ (κ t).order := fun t => by cases κ t <;> decide
  simpa using Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h t)

/-- Two photon fields of the same `gauge` vertex are equal. -/
theorem photonSlot_eq_of_gauge {s s' : Wick.PhotonSlot κ} (h : s.1 = s'.1)
    (hg : κ s.1 = .gauge) : s = s' := by
  have h1 : (κ s.1).photonSlots = 1 := by rw [hg]; rfl
  have h1' : (κ s'.1).photonSlots = 1 := by rw [← h, hg]; rfl
  have hk := lt_of_lt_of_eq s.2.isLt h1
  have hk' := lt_of_lt_of_eq s'.2.isLt h1'
  exact Sigma.ext h ((Fin.heq_ext_iff (by rw [h])).mpr (by omega))

/-- A photon field of a `photonCt` vertex is one of any two distinct photon fields of it. -/
theorem photonSlot_eq_or_of_photonCt {x y s : Wick.PhotonSlot κ} (hx : x.1 = s.1) (hy : y.1 = s.1)
    (hct : κ s.1 = .photonCt) (hxy : x ≠ y) : s = x ∨ s = y := by
  have h2 : (κ s.1).photonSlots = 2 := by rw [hct]; rfl
  have h2x : (κ x.1).photonSlots = 2 := by rw [hx, hct]; rfl
  have h2y : (κ y.1).photonSlots = 2 := by rw [hy, hct]; rfl
  have hk := lt_of_lt_of_eq s.2.isLt h2
  have hkx := lt_of_lt_of_eq x.2.isLt h2x
  have hky := lt_of_lt_of_eq y.2.isLt h2y
  have hne : (x.2 : ℕ) ≠ y.2 := fun h =>
    hxy (Sigma.ext (hx.trans hy.symm) ((Fin.heq_ext_iff (by rw [hx, hy])).mpr h))
  by_cases hkk : (s.2 : ℕ) = x.2
  · exact Or.inl (Sigma.ext hx.symm ((Fin.heq_ext_iff (by rw [hx])).mpr hkk))
  · exact Or.inr (Sigma.ext hy.symm ((Fin.heq_ext_iff (by rw [hy])).mpr (by omega)))

/-- The insertion pairing of the photon fields: two fields on the two vertices of a closed
two-vertex fermion loop, or the two fields of one `photonCt` vertex (the clause of (C₁)). -/
def InsPair (C : Contraction 1 1 κ) (s s' : Wick.PhotonSlot κ) : Prop :=
  (κ s.1 = .gauge ∧ κ s'.1 = .gauge ∧ s.1 ≠ s'.1 ∧
      ∃ u w : Wick.FermionVertex κ, u.1 = s.1 ∧ w.1 = s'.1 ∧
        C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr u) ∨
    (κ s.1 = .photonCt ∧ s'.1 = s.1 ∧ s' ≠ s)

theorem InsPair.symm {C : Contraction 1 1 κ} {s s' : Wick.PhotonSlot κ} (h : InsPair C s s') :
    InsPair C s' s := by
  rcases h with ⟨g1, g2, hne, u, w, hu, hw, huw, hwu⟩ | ⟨hct, heq, hne⟩
  · exact Or.inl ⟨g2, g1, fun h => hne h.symm, w, u, hw, hu, hwu, huw⟩
  · exact Or.inr ⟨heq ▸ hct, heq.symm, fun h => hne h.symm⟩

theorem InsPair.irrefl {C : Contraction 1 1 κ} {s : Wick.PhotonSlot κ} (h : InsPair C s s) :
    False := by
  rcases h with ⟨_, _, hne, _⟩ | ⟨_, _, hne⟩
  · exact hne rfl
  · exact hne rfl

theorem InsPair.unique {C : Contraction 1 1 κ} {s y y' : Wick.PhotonSlot κ} (h : InsPair C s y)
    (h' : InsPair C s y') : y = y' := by
  rcases h with ⟨g1, g2, -, u, w, hu, hw, huw, -⟩ | ⟨hct, heq, hne⟩ <;>
    rcases h' with ⟨g1', g2', -, u', w', hu', hw', huw', -⟩ | ⟨hct', heq', hne'⟩
  · have huu : u = u' := Subtype.ext (hu.trans hu'.symm)
    subst huu
    have hww : w = w' := by
      rw [huw] at huw'
      exact Sum.inr_injective huw'
    subst hww
    exact photonSlot_eq_of_gauge (hw.symm.trans hw') g2
  · rw [g1] at hct'
    exact absurd hct' (by decide)
  · rw [g1'] at hct
    exact absurd hct (by decide)
  · rcases photonSlot_eq_or_of_photonCt (x := s) (y := y) (s := y') heq'.symm
      (heq.trans heq'.symm) (by rw [heq']; exact hct) (fun h => hne h.symm) with h | h
    · exact absurd h hne'
    · exact h.symm

/-- **A chain with `n` insertions has total order `2n + 3`.** -/
theorem order_sum_of_isVPChain {n : ℕ} {C : Contraction 1 1 κ} (h : QED.VPChain.IsVPChain n C) :
    ∑ t, (κ t).order = 2 * n + 3 := by
  obtain ⟨a, b, c, sb, src, dst, ha, hb, hc, h0a, hab, hbc, hc0, hsb, hτ0, hsrc0, hdstn, hτ,
    hins, hall⟩ := h
  have hinv := C.2
  have hτ' : ∀ i, C.1.2 (.inr (dst i)) = .inr (src i) := fun i => by
    rw [← hτ i, (hinv _).1]
  have hτsb : C.1.2 (.inr sb) = .inl 0 := by rw [← hτ0, (hinv _).1]
  have hR : ∀ i : Fin n, InsPair C (dst i.castSucc) (src i.succ) := hins
  -- the open-line vertices
  have hac : a.1 ≠ c.1 := by
    intro h
    have h' : a = c := Subtype.ext h
    rw [h', hc0] at hab
    exact Sum.inl_ne_inr hab
  -- the vertices of the insertions are not `a` or `c`
  have hloop : ∀ u w : Wick.FermionVertex κ, C.1.1 (.inr u) = .inr w →
      C.1.1 (.inr w) = .inr u → u.1 ≠ a.1 ∧ u.1 ≠ c.1 := by
    intro u w huw hwu
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hu : u = a := Subtype.ext h
      subst hu
      rw [hab] at huw
      have hw : w = b := (Sum.inr_injective huw).symm
      subst hw
      rw [hbc] at hwu
      exact hac (congrArg Subtype.val (Sum.inr_injective hwu)).symm
    · have hu : u = c := Subtype.ext h
      subst hu
      rw [hc0] at huw
      exact Sum.inl_ne_inr huw
  have hinsv : ∀ i : Fin n, (dst i.castSucc).1 ≠ a.1 ∧ (dst i.castSucc).1 ≠ c.1 ∧
      (src i.succ).1 ≠ a.1 ∧ (src i.succ).1 ≠ c.1 := by
    intro i
    rcases hins i with ⟨-, -, -, u, w, hu, hw, huw, hwu⟩ | ⟨hct, heq, -⟩
    · rw [← hu, ← hw]
      exact ⟨(hloop u w huw hwu).1, (hloop u w huw hwu).2, (hloop w u hwu huw).1,
        (hloop w u hwu huw).2⟩
    · rw [heq]
      have hna : (dst i.castSucc).1 ≠ a.1 := fun h => by
        rw [h, ha] at hct; exact absurd hct (by decide)
      have hnc : (dst i.castSucc).1 ≠ c.1 := fun h => by
        rw [h, hc] at hct; exact absurd hct (by decide)
      exact ⟨hna, hnc, hna, hnc⟩
  -- no `src` is a `dst`
  have hsd : ∀ i j : Fin (n + 1), src i ≠ dst j := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro j hj
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact (hinsv j').1 (by rw [← hj, hsrc0])
      · exact hac (by rw [← hsrc0, ← hdstn, hj])
    | succ i ih =>
      intro j hj
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have h1 : InsPair C (src i.succ) (dst i.castSucc) := (hR i).symm
        have h2 : InsPair C (src i.succ) (src j'.succ) := hj ▸ hR j'
        have h3 : src j'.succ = dst i.castSucc := h2.unique h1
        have h4 : dst j'.succ = src i.castSucc := by
          have := hτ j'.succ
          rw [h3, hτ'] at this
          exact (Sum.inr_injective this).symm
        exact ih j'.succ h4.symm
      · exact (hinsv i).2.2.2 (by rw [hj, hdstn])
  -- `src` is injective
  have hss : ∀ i j : Fin (n + 1), src i = src j → i = j := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro j hj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rfl
      · exact absurd (by rw [← hj, hsrc0]) (hinsv j').2.2.1
    | succ i ih =>
      intro j hj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd (by rw [hj, hsrc0]) (hinsv i).2.2.1
      · have h1 : InsPair C (src i.succ) (dst i.castSucc) := (hR i).symm
        have h2 : InsPair C (src i.succ) (dst j'.castSucc) := hj ▸ (hR j').symm
        have h3 : dst i.castSucc = dst j'.castSucc := h1.unique h2
        have h4 : src i.castSucc = src j'.castSucc := by
          have := hτ' i.castSucc
          rw [h3, hτ'] at this
          exact (Sum.inr_injective this).symm
        exact congrArg Fin.succ (Fin.castSucc_injective _ (ih _ h4))
  have hdd : ∀ i j : Fin (n + 1), dst i = dst j → i = j := by
    intro i j h
    apply hss
    have := hτ' i
    rw [h, hτ'] at this
    exact (Sum.inr_injective this).symm
  have hsbs : ∀ i, sb ≠ src i := fun i h => by
    have := hτ i
    rw [← h, hτsb] at this
    exact Sum.inl_ne_inr this
  have hsbd : ∀ i, sb ≠ dst i := fun i h => by
    have := hτ' i
    rw [← h, hτsb] at this
    exact Sum.inl_ne_inr this
  -- every vertex is `gauge` or `photonCt`
  have hkind : ∀ t, κ t = .gauge ∨ κ t = .photonCt := by
    intro t
    rcases hall t with rfl | rfl | rfl | ⟨i, rfl | rfl⟩
    · exact Or.inl ha
    · exact Or.inl hb
    · exact Or.inl hc
    · rcases hins i with ⟨g1, -⟩ | ⟨hct, -⟩
      · exact Or.inl g1
      · exact Or.inr hct
    · rcases hins i with ⟨-, g2, -⟩ | ⟨hct, heq, -⟩
      · exact Or.inl g2
      · exact Or.inr (heq ▸ hct)
  -- the photon fields are `sb`, `src i`, `dst i`
  let f : Option (Fin (n + 1) ⊕ Fin (n + 1)) → Wick.PhotonSlot κ := fun o =>
    match o with
    | none => sb
    | some (.inl i) => src i
    | some (.inr i) => dst i
  have hf : Function.Bijective f := by
    constructor
    · rintro (_ | i | i) (_ | j | j) h <;> simp only [f] at h
      · rfl
      · exact absurd h (hsbs j)
      · exact absurd h (hsbd j)
      · exact absurd h.symm (hsbs i)
      · rw [hss i j h]
      · exact absurd h (hsd i j)
      · exact absurd h.symm (hsbd i)
      · exact absurd h.symm (hsd j i)
      · rw [hdd i j h]
    · intro s
      rcases hall s.1 with h | h | h | ⟨i, h | h⟩
      · exact ⟨some (.inl 0), photonSlot_eq_of_gauge (hsrc0.trans h.symm) (by rw [hsrc0]; exact ha)⟩
      · exact ⟨none, photonSlot_eq_of_gauge (hsb.trans h.symm) (by rw [hsb]; exact hb)⟩
      · exact ⟨some (.inr (Fin.last n)),
          photonSlot_eq_of_gauge (hdstn.trans h.symm) (by rw [hdstn]; exact hc)⟩
      · rcases hins i with ⟨g1, -⟩ | ⟨hct, heq, hne⟩
        · exact ⟨some (.inr i.castSucc), photonSlot_eq_of_gauge h.symm g1⟩
        · rcases photonSlot_eq_or_of_photonCt (x := dst i.castSucc) (y := src i.succ) h.symm
            (heq.trans h.symm) (h ▸ hct) (fun h' => hne h'.symm) with h' | h'
          · exact ⟨some (.inr i.castSucc), h'.symm⟩
          · exact ⟨some (.inl i.succ), h'.symm⟩
      · rcases hins i with ⟨-, g2, -⟩ | ⟨hct, heq, hne⟩
        · exact ⟨some (.inl i.succ), photonSlot_eq_of_gauge h.symm g2⟩
        · rcases photonSlot_eq_or_of_photonCt (x := dst i.castSucc) (y := src i.succ)
            (heq.symm.trans h.symm) h.symm (by rw [h, heq]; exact hct)
            (fun h' => hne h'.symm) with h' | h'
          · exact ⟨some (.inr i.castSucc), h'.symm⟩
          · exact ⟨some (.inl i.succ), h'.symm⟩
  have hcard := Fintype.card_of_bijective hf
  simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at hcard
  have hsum : ∑ t, (κ t).order = ∑ t, (κ t).photonSlots := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases hkind t with h | h <;> rw [h] <;> rfl
  have hslots : Fintype.card (Wick.PhotonSlot κ) = ∑ t, (κ t).photonSlots := by
    simp [Wick.PhotonSlot, Fintype.card_sigma]
  omega

end QED.ChainProof.Quick

end
