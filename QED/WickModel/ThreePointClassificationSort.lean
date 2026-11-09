/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationShapes

/-!
# Three gauge vertices: the connected contractions that are not 1PI

The classification of the connected contractions of three gauge vertices with one external
fermion pair and one external photon that are not 1PI (packet 6a, decision D-24):

* `nonOnePI_iff`: they are exactly the self-energy loops on the incoming and the outgoing leg,
  the vacuum polarization loops, and the tadpoles.
* The four shapes are mutually exclusive.

The proof follows the fermion line from `Ψ(x)`. If it returns to `Ψ̄(y)` after one vertex, the
other two vertices form a closed loop of two vertices (a vacuum polarization loop unless the
external photon is at the open line's vertex, which then is isolated) or two self-loops (one of
which then is isolated). After two vertices, the third is a self-loop (a tadpole unless it holds
the external photon). After three vertices, the external photon is at the first vertex (an
incoming-leg self-energy), the middle vertex (the vertex correction, which is 1PI) or the last
vertex (an outgoing-leg self-energy).
-/

@[expose] public section

open Complex

namespace QED.WickModel

open Wick (gauge3)

variable {C : Contraction 1 1 gauge3}

/-- The four shapes of the connected contractions of three gauge vertices that are not 1PI. -/
def IsNonOnePIShape (C : Contraction 1 1 gauge3) : Prop :=
  (∃ a b c, IsSEin C a b c) ∨ (∃ a b c, IsSEout C a b c) ∨ (∃ a v w, IsVP C a v w) ∨
    ∃ a b c u, IsTP C a b c u

/-- The values of a permutation of the fermion fields. -/
private theorem fields_cover {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∀ y : Fin 1 ⊕ Wick.FermionVertex gauge3,
      y = .inr (Wick.fv a) ∨ y = .inr (Wick.fv b) ∨ y = .inl 0 ∨ y = .inr (Wick.fv c) := by
  intro y
  rcases fermion_field_cases hab hbc hac y with h | h | h | h <;> simp [h]

/-- The fermion line continues from `a` to `b`: the remaining shapes. -/
private theorem cases_of_ab {a b c u : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hout : C.1.1 (.inl 0) = .inr (Wick.fv a))
    (hσa : C.1.1 (.inr (Wick.fv a)) = .inr (Wick.fv b)) (hu : PhotonAt C u)
    (hconn : VerticesConnected C) (h1PI : ¬ IsOnePI C) : IsNonOnePIShape C := by
  have hX := fields_cover hab hbc hac
  have hX' : ∀ y : Fin 1 ⊕ Wick.FermionVertex gauge3,
      y = .inr (Wick.fv a) ∨ y = .inr (Wick.fv b) ∨ y = .inr (Wick.fv c) ∨ y = .inl 0 := by
    intro y
    rcases hX y with h | h | h | h <;> simp [h]
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.fv s) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠
      .inr (Wick.fv t) := fun s t h h' => h (fv3_injective (Sum.inr_injective h'))
  rcases perm_apply_cases_of_two (x₃ := .inr (Wick.fv b)) hX hout hσa Sum.inr_ne_inl
      (hne b a hab.symm) with hσb | hσb
  · -- `Ψ̄(y) → b → a → Ψ(x)`, with a self-loop at `c`
    have hσc : C.1.1 (.inr (Wick.fv c)) = .inr (Wick.fv c) :=
      perm_apply_eq_of_three hX hout hσa hσb Sum.inr_ne_inl (hne c a hac.symm) (hne c b hbc.symm)
    by_cases huc : u = c
    · subst huc
      exact absurd hconn (not_verticesConnected_of_isolated hu (isolated_of_self hσc))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, c, u, ⟨hab, hbc, hac, hout, hσa, hσb, hσc, hu, huc⟩⟩))
  · -- the chain `Ψ̄(y) → c → b → a → Ψ(x)`
    have hσc : C.1.1 (.inr (Wick.fv c)) = .inl 0 :=
      perm_apply_eq_of_three hX' hout hσa hσb Sum.inr_ne_inl (hne c a hac.symm)
        (hne c b hbc.symm)
    have hC : IsChain3 C a b c := ⟨hab, hbc, hac, hout, hσa, hσb, hσc⟩
    rcases fin_three_eq_or hab hbc hac u with rfl | rfl | rfl
    · exact Or.inl ⟨u, b, c, hC, hu⟩
    · exact absurd (hC.isOnePI hu) h1PI
    · exact Or.inr (Or.inl ⟨a, b, u, hC, hu⟩)

/-- **The connected contractions that are not 1PI have one of the four shapes.** -/
theorem isNonOnePIShape_of {C : Contraction 1 1 gauge3}
    (h : (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C) : IsNonOnePIShape C := by
  obtain ⟨⟨hext, hconn⟩, h1PI⟩ := h
  obtain ⟨a, hout⟩ : ∃ a, C.1.1 (.inl 0) = .inr (Wick.fv a) := by
    rcases hC : C.1.1 (.inl 0) with i | t
    · exact absurd hC (hext.1 0 i)
    · exact ⟨t.1, rfl⟩
  obtain ⟨u, hu⟩ := exists_photonAt C
  obtain ⟨b, c, hab, hbc, hac⟩ : ∃ b c : Fin 3, a ≠ b ∧ b ≠ c ∧ a ≠ c :=
    ⟨a + 1, a + 2, by fin_cases a <;> decide⟩
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.fv s) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠
      .inr (Wick.fv t) := fun s t h h' => h (fv3_injective (Sum.inr_injective h'))
  rcases fermion_field_cases hab hbc hac (C.1.1 (.inr (Wick.fv a))) with hσa | hσa | hσa | hσa
  · -- the open fermion line is `Ψ̄(y) → a → Ψ(x)`
    have hX : ∀ y : Fin 1 ⊕ Wick.FermionVertex gauge3,
        y = .inr (Wick.fv a) ∨ y = .inl 0 ∨ y = .inr (Wick.fv b) ∨ y = .inr (Wick.fv c) := by
      intro y
      rcases fermion_field_cases hab hbc hac y with h | h | h | h <;> simp [h]
    have hX' : ∀ y : Fin 1 ⊕ Wick.FermionVertex gauge3,
        y = .inr (Wick.fv a) ∨ y = .inl 0 ∨ y = .inr (Wick.fv c) ∨ y = .inr (Wick.fv b) := by
      intro y
      rcases hX y with h | h | h | h <;> simp [h]
    rcases perm_apply_cases_of_two (x₃ := .inr (Wick.fv b)) hX hout hσa
        Sum.inr_ne_inl (hne b a hab.symm) with hσb | hσb
    · -- a self-loop at `b`
      have hσc : C.1.1 (.inr (Wick.fv c)) = .inr (Wick.fv c) :=
        perm_apply_eq_of_three hX hout hσa hσb Sum.inr_ne_inl (hne c a hac.symm)
          (hne c b hbc.symm)
      exfalso
      rcases fin_three_eq_or hab hbc hac u with rfl | rfl | rfl
      · exact not_verticesConnected_of_isolated hu (isolated_of_out_inn hout hσa) hconn
      · exact not_verticesConnected_of_isolated hu (isolated_of_self hσb) hconn
      · exact not_verticesConnected_of_isolated hu (isolated_of_self hσc) hconn
    · -- the closed loop through `b` and `c`
      have hσc : C.1.1 (.inr (Wick.fv c)) = .inr (Wick.fv b) :=
        perm_apply_eq_of_three hX' hout hσa hσb Sum.inr_ne_inl (hne c a hac.symm)
          (hne c b hbc.symm)
      rcases fin_three_eq_or hab hbc hac u with rfl | rfl | rfl
      · exact absurd hconn (not_verticesConnected_of_isolated hu (isolated_of_out_inn hout hσa))
      · exact Or.inr (Or.inr (Or.inl ⟨a, u, c, ⟨hab, hbc, hac, hout, hσa, hσb, hσc, hu⟩⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨a, u, b, ⟨hac, hbc.symm, hab, hout, hσa, hσc, hσb, hu⟩⟩))
  · exact absurd (C.1.1.injective (hout.trans hσa.symm)) Sum.inl_ne_inr
  · exact cases_of_ab hab hbc hac hout hσa hu hconn h1PI
  · exact cases_of_ab hac hbc.symm hab hout hσa hu hconn h1PI

/-- Every contraction of one of the four shapes is connected but not 1PI. -/
theorem IsNonOnePIShape.connected_not_isOnePI {C : Contraction 1 1 gauge3}
    (h : IsNonOnePIShape C) : (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · exact h.connected_not_isOnePI
  · exact h.connected_not_isOnePI
  · exact h.connected_not_isOnePI
  · exact h.connected_not_isOnePI

/-- **Classification**: a contraction of three gauge vertices is connected but not 1PI exactly
when it is an incoming- or outgoing-leg self-energy loop, a vacuum polarization loop, or a
tadpole. -/
theorem nonOnePI_iff (C : Contraction 1 1 gauge3) :
    ((ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C) ↔ IsNonOnePIShape C :=
  ⟨isNonOnePIShape_of, IsNonOnePIShape.connected_not_isOnePI⟩

/-! ### The shapes are mutually exclusive -/

/-- The vertex attached to `Ψ(x)` is determined. -/
private theorem out_inj {a a' : Fin 3} (h : C.1.1 (.inl 0) = .inr (Wick.fv a))
    (h' : C.1.1 (.inl 0) = .inr (Wick.fv a')) : a = a' :=
  fv3_injective (Sum.inr_injective (h.symm.trans h'))

/-- The vertex of the external photon is determined. -/
theorem PhotonAt.inj {u u' : Fin 3} (h : PhotonAt C u) (h' : PhotonAt C u') : u = u' :=
  ps3_injective (Sum.inr_injective (h.symm.trans h'))

/-- An incoming-leg self-energy loop is not an outgoing-leg one. -/
theorem IsSEin.not_isSEout {a b c a' b' c' : Fin 3} (h : IsSEin C a b c)
    (h' : IsSEout C a' b' c') : False := by
  have ha := out_inj h.chain.out h'.chain.out
  subst ha
  have hb : b = b' := fv3_injective (Sum.inr_injective (h.chain.ab.symm.trans h'.chain.ab))
  subst hb
  have hc : c = c' := fv3_injective (Sum.inr_injective (h.chain.bc.symm.trans h'.chain.bc))
  subst hc
  exact h.chain.hac (h.photon.inj h'.photon)

/-- A chain is not a vacuum polarization loop. -/
theorem IsChain3.not_isVP {a b c a' v w : Fin 3} (h : IsChain3 C a b c) (h' : IsVP C a' v w) :
    False := by
  have ha := out_inj h.out h'.out
  subst ha
  have := h'.inn
  rw [h.ab] at this
  exact Sum.inr_ne_inl this

/-- A chain is not a tadpole. -/
theorem IsChain3.not_isTP {a b c a' b' c' u : Fin 3} (h : IsChain3 C a b c)
    (h' : IsTP C a' b' c' u) : False := by
  have ha := out_inj h.out h'.out
  subst ha
  have hb : b = b' := fv3_injective (Sum.inr_injective (h.ab.symm.trans h'.ab))
  subst hb
  have := h'.inn
  rw [h.bc] at this
  exact Sum.inr_ne_inl this

/-- A vacuum polarization loop is not a tadpole. -/
theorem IsVP.not_isTP {a v w a' b' c' u : Fin 3} (h : IsVP C a v w) (h' : IsTP C a' b' c' u) :
    False := by
  have ha := out_inj h.out h'.out
  subst ha
  have := h'.ab
  rw [h.inn] at this
  exact Sum.inl_ne_inr this

end QED.WickModel

end
