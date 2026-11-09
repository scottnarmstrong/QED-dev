/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationGauge3
public import QED.WickModel.ThreePointClassificationTadpole

/-!
# Three gauge vertices: the shapes of the contractions

The shapes of the contractions of three gauge vertices with one external fermion pair and one
external photon (packet 6a, decision D-24), their internal lines, and which of them are
connected and 1PI:

* `IsChain3 C a b c`: the fermion line runs `Ψ̄(y) → c → b → a → Ψ(x)`. With the external photon at
  `a` it is `IsSEin` (connected, not 1PI: the line `b → a` is a bridge); at `b` it is the vertex
  correction (1PI, `IsChain3.isOnePI`); at `c` it is `IsSEout` (the line `c → b` is a bridge).
* `IsVP C a v w`: a vacuum polarization loop; the photon line `a – w` is a bridge.
* `IsTP C a b c u`: a tadpole; the photon line to `c` is a bridge, and so is the line `b → a`, so
  the self-loop at `c` is the loop line (`IsTP.isLoopLine`).
* `not_verticesConnected_of_isolated`: a vertex whose fields are contracted only with external
  fields or with each other disconnects the contraction.
-/

@[expose] public section

open Complex

namespace QED.WickModel

open Wick (gauge3)

variable {C : Contraction 1 1 gauge3}

/-! ### Shapes -/

/-- The fermion line of `C` runs `Ψ̄(y) → c → b → a → Ψ(x)`. -/
structure IsChain3 (C : Contraction 1 1 gauge3) (a b c : Fin 3) : Prop where
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c
  out : C.1.1 (.inl 0) = .inr (Wick.fv a)
  ab : C.1.1 (.inr (Wick.fv a)) = .inr (Wick.fv b)
  bc : C.1.1 (.inr (Wick.fv b)) = .inr (Wick.fv c)
  inn : C.1.1 (.inr (Wick.fv c)) = .inl 0

/-- A self-energy loop on the incoming leg: the chain `Ψ̄(y) → c → b → a → Ψ(x)` with the external
photon at `a`; the photon line joins `b` and `c`. -/
structure IsSEin (C : Contraction 1 1 gauge3) (a b c : Fin 3) : Prop where
  chain : IsChain3 C a b c
  photon : PhotonAt C a

/-- A self-energy loop on the outgoing leg: the chain `Ψ̄(y) → c → b → a → Ψ(x)` with the external
photon at `c`; the photon line joins `a` and `b`. -/
structure IsSEout (C : Contraction 1 1 gauge3) (a b c : Fin 3) : Prop where
  chain : IsChain3 C a b c
  photon : PhotonAt C c

/-- A vacuum polarization loop on the photon leg: the fermion line `Ψ̄(y) → a → Ψ(x)`, the closed
fermion loop through `v` and `w`, the external photon at `v`, and the photon line joining `a`
and `w`. -/
structure IsVP (C : Contraction 1 1 gauge3) (a v w : Fin 3) : Prop where
  hav : a ≠ v
  hvw : v ≠ w
  haw : a ≠ w
  out : C.1.1 (.inl 0) = .inr (Wick.fv a)
  inn : C.1.1 (.inr (Wick.fv a)) = .inl 0
  vw : C.1.1 (.inr (Wick.fv v)) = .inr (Wick.fv w)
  wv : C.1.1 (.inr (Wick.fv w)) = .inr (Wick.fv v)
  photon : PhotonAt C v

/-- A tadpole: the fermion line `Ψ̄(y) → b → a → Ψ(x)`, the `Ψ` of `c` contracted with its own
`Ψ̄`, and the external photon at `u ≠ c`; the photon line joins `c` to the other vertex of the
fermion line. -/
structure IsTP (C : Contraction 1 1 gauge3) (a b c u : Fin 3) : Prop where
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c
  out : C.1.1 (.inl 0) = .inr (Wick.fv a)
  ab : C.1.1 (.inr (Wick.fv a)) = .inr (Wick.fv b)
  inn : C.1.1 (.inr (Wick.fv b)) = .inl 0
  cc : C.1.1 (.inr (Wick.fv c)) = .inr (Wick.fv c)
  photon : PhotonAt C u
  huc : u ≠ c

/-! ### Externals and isolated vertices -/

/-- The externals are attached when `Ψ(x)` is contracted with a vertex field. -/
theorem externalsAttached_of_out {a : Fin 3} (h : C.1.1 (.inl 0) = .inr (Wick.fv a)) :
    ExternalsAttached C := by
  refine ⟨fun i j => ?_, photon_attached_of_one⟩
  rw [Subsingleton.elim i 0, h]
  exact Sum.inr_ne_inl

/-- **An isolated vertex.** If the external photon is at `u`, and the `Ψ` and `Ψ̄` of `u` are
contracted with external fields or with each other, the vertices are not connected. -/
theorem not_verticesConnected_of_isolated {u : Fin 3} (hu : PhotonAt C u)
    (hσ : ∀ t s : Fin 3, C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s) → (t = u ↔ s = u)) :
    ¬ VerticesConnected C := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 3, u ≠ w := ⟨u + 1, by fin_cases u <;> decide⟩
  refine not_verticesConnected_of_forall_not_crosses hw
    (forall_not_crosses_of_isolated (fun t s h => ?_) (fun s s' h => ?_))
  · rw [fv3_eq t, fv3_eq s] at h
    exact hσ _ _ h
  · have := hu.fst_ne h
    exact ⟨fun h' => absurd h' this.1, fun h' => absurd h' this.2⟩

/-- A vertex on a one-vertex open fermion line is isolated from the other fermion fields. -/
theorem isolated_of_out_inn {a : Fin 3} (hout : C.1.1 (.inl 0) = .inr (Wick.fv a))
    (hinn : C.1.1 (.inr (Wick.fv a)) = .inl 0) (t s : Fin 3)
    (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) : t = a ↔ s = a := by
  constructor
  · rintro rfl
    rw [hinn] at h
    exact absurd h Sum.inl_ne_inr
  · rintro rfl
    rw [← hout] at h
    exact absurd (C.1.1.injective h) Sum.inr_ne_inl

/-- A vertex whose `Ψ` is contracted with its own `Ψ̄` is isolated from the other fermion
fields. -/
theorem isolated_of_self {c : Fin 3} (hc : C.1.1 (.inr (Wick.fv c)) = .inr (Wick.fv c))
    (t s : Fin 3) (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) : t = c ↔ s = c := by
  constructor
  · rintro rfl
    rw [hc] at h
    exact (fv3_injective (Sum.inr_injective h)).symm
  · rintro rfl
    rw [← hc] at h
    exact fv3_injective (Sum.inr_injective (C.1.1.injective h))

/-! ### Chains -/

namespace IsChain3

variable {a b c : Fin 3}

/-- The fermion line from `b` to `a`. -/
def lineA (hC : IsChain3 C a b c) : FermionLine C := fline hC.ab

/-- The fermion line from `c` to `b`. -/
def lineB (hC : IsChain3 C a b c) : FermionLine C := fline hC.bc

/-- The fermion line `lineA` is indexed by the `Ψ` of `a`. -/
@[simp]
theorem lineA_val (hC : IsChain3 C a b c) : hC.lineA.1 = Wick.fv a := rfl

/-- The fermion line `lineA` starts at `b`. -/
@[simp]
theorem tail_lineA (hC : IsChain3 C a b c) : hC.lineA.tail = Wick.fv b := tail_fline _

/-- The fermion line `lineB` is indexed by the `Ψ` of `b`. -/
@[simp]
theorem lineB_val (hC : IsChain3 C a b c) : hC.lineB.1 = Wick.fv b := rfl

/-- The fermion line `lineB` starts at `c`. -/
@[simp]
theorem tail_lineB (hC : IsChain3 C a b c) : hC.lineB.tail = Wick.fv c := tail_fline _

/-- The internal fermion lines of a chain. -/
theorem fermionLine_cases (hC : IsChain3 C a b c) (f : FermionLine C) :
    f = hC.lineA ∨ f = hC.lineB := by
  rcases fv3_cases hC.hab hC.hbc hC.hac f.1 with h | h | h
  · exact Or.inl (eq_fline _ f h)
  · exact Or.inr (eq_fline _ f h)
  · exact absurd h (val_ne_of_eq_inl hC.inn f)

/-- The two fermion lines are distinct. -/
theorem lineA_ne_lineB (hC : IsChain3 C a b c) : hC.lineA ≠ hC.lineB := fun h =>
  hC.hab (fv3_injective (congrArg Subtype.val h))

/-- The fermion line from `b` to `a`. -/
theorem ends_lineA (hC : IsChain3 C a b c) :
    Line.ends (.inl hC.lineA : Line C) = (b, a) := ends_fline _

/-- The fermion line from `c` to `b`. -/
theorem ends_lineB (hC : IsChain3 C a b c) :
    Line.ends (.inl hC.lineB : Line C) = (c, b) := ends_fline _

/-- A chain connects the three vertices. -/
theorem verticesConnected (hC : IsChain3 C a b c) : VerticesConnected C :=
  verticesConnected_of_three hC.hab hC.hbc hC.hac
    (joined_of_ends (Set.notMem_empty _) hC.ends_lineA).symm
    (joined_of_ends (Set.notMem_empty _) hC.ends_lineB).symm

end IsChain3

/-! ### Self-energy loops -/

namespace IsSEin

variable {a b c : Fin 3}

/-- The photon line of an incoming-leg self-energy loop, joining `b` and `c`. -/
def photonLine (hC : IsSEin C a b c) : PhotonLine C :=
  hC.photon.line hC.chain.hab hC.chain.hbc hC.chain.hac

/-- The internal lines of an incoming-leg self-energy loop. -/
theorem line_cases (hC : IsSEin C a b c) (l : Line C) :
    l = .inl hC.chain.lineA ∨ l = .inl hC.chain.lineB ∨ l = .inr hC.photonLine := by
  rcases l with f | l
  · rcases hC.chain.fermionLine_cases f with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (congrArg _ (hC.photon.eq_line _ _ _ l)))

/-- The photon line joins `b` and `c`. -/
theorem ends_photonLine (hC : IsSEin C a b c) :
    Line.ends (.inr hC.photonLine : Line C) = (b, c) ∨
      Line.ends (.inr hC.photonLine : Line C) = (c, b) :=
  hC.photon.ends_line _ _ _

/-- The line from `b` to `a` is a bridge. -/
theorem isBridge_lineA (hC : IsSEin C a b c) : IsBridge (.inl hC.chain.lineA : Line C) := by
  have hab := hC.chain.hab
  have hac := hC.chain.hac
  refine isBridge_of_closed' {b, c} (Or.inl ?_) fun l hl => ?_
  · rw [hC.chain.ends_lineA]
    simp [hab, hac]
  · rcases hC.line_cases l with rfl | rfl | rfl
    · exact absurd rfl hl
    · rw [hC.chain.ends_lineB]
      simp
    · rcases hC.ends_photonLine with h | h <;> rw [h] <;> simp

/-- An incoming-leg self-energy loop is connected but not 1PI. -/
theorem connected_not_isOnePI (hC : IsSEin C a b c) :
    (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C :=
  ⟨⟨externalsAttached_of_out hC.chain.out, hC.chain.verticesConnected⟩,
    fun h => h.2.2 _ hC.isBridge_lineA⟩

end IsSEin

namespace IsSEout

variable {a b c : Fin 3}

/-- The photon line of an outgoing-leg self-energy loop, joining `a` and `b`. -/
def photonLine (hC : IsSEout C a b c) : PhotonLine C :=
  hC.photon.line hC.chain.hac.symm hC.chain.hab hC.chain.hbc.symm

/-- The internal lines of an outgoing-leg self-energy loop. -/
theorem line_cases (hC : IsSEout C a b c) (l : Line C) :
    l = .inl hC.chain.lineA ∨ l = .inl hC.chain.lineB ∨ l = .inr hC.photonLine := by
  rcases l with f | l
  · rcases hC.chain.fermionLine_cases f with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (congrArg _ (hC.photon.eq_line _ _ _ l)))

/-- The photon line joins `a` and `b`. -/
theorem ends_photonLine (hC : IsSEout C a b c) :
    Line.ends (.inr hC.photonLine : Line C) = (a, b) ∨
      Line.ends (.inr hC.photonLine : Line C) = (b, a) :=
  hC.photon.ends_line _ _ _

/-- The line from `c` to `b` is a bridge. -/
theorem isBridge_lineB (hC : IsSEout C a b c) : IsBridge (.inl hC.chain.lineB : Line C) := by
  have hbc := hC.chain.hbc
  have hac := hC.chain.hac
  refine isBridge_of_closed' {c} (Or.inl ?_) fun l hl => ?_
  · rw [hC.chain.ends_lineB]
    simp [hbc]
  · rcases hC.line_cases l with rfl | rfl | rfl
    · rw [hC.chain.ends_lineA]
      simp [hbc, hac]
    · exact absurd rfl hl
    · rcases hC.ends_photonLine with h | h <;> rw [h] <;> simp [hbc, hac]

/-- An outgoing-leg self-energy loop is connected but not 1PI. -/
theorem connected_not_isOnePI (hC : IsSEout C a b c) :
    (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C :=
  ⟨⟨externalsAttached_of_out hC.chain.out, hC.chain.verticesConnected⟩,
    fun h => h.2.2 _ hC.isBridge_lineB⟩

end IsSEout

/-! ### The vertex correction -/

/-- **The vertex correction is 1PI**: with the external photon at the middle vertex `b` of the
chain, the photon line joins `a` and `c`, and the three internal lines form a triangle. -/
theorem IsChain3.isOnePI {a b c : Fin 3} (hC : IsChain3 C a b c) (hb : PhotonAt C b) :
    IsOnePI C := by
  have hab := hC.hab
  have hbc := hC.hbc
  have hac := hC.hac
  set pl := hb.line hab.symm hac hbc
  have hpl : Line.ends (.inr pl : Line C) = (a, c) ∨ Line.ends (.inr pl : Line C) = (c, a) :=
    hb.ends_line _ _ _
  have hlines : ∀ l : Line C, l = .inl hC.lineA ∨ l = .inl hC.lineB ∨ l = .inr pl := by
    rintro (f | l)
    · rcases hC.fermionLine_cases f with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (congrArg _ (hb.eq_line _ _ _ l)))
  have hA : (Sum.inl hC.lineA : Line C) ≠ .inl hC.lineB := fun h =>
    hC.lineA_ne_lineB (Sum.inl_injective h)
  have jA : ∀ {S : Set (Line C)}, (.inl hC.lineA : Line C) ∉ S → Joined C S a b := fun h =>
    (joined_of_ends h hC.ends_lineA).symm
  have jB : ∀ {S : Set (Line C)}, (.inl hC.lineB : Line C) ∉ S → Joined C S b c := fun h =>
    (joined_of_ends h hC.ends_lineB).symm
  have jP : ∀ {S : Set (Line C)}, (.inr pl : Line C) ∉ S → Joined C S a c := fun h =>
    ⟨_, h, hpl⟩
  refine ⟨externalsAttached_of_out hC.out, hC.verticesConnected, fun l hl => ?_⟩
  unfold IsBridge at hl
  rcases hlines l with rfl | rfl | rfl
  · rw [hC.ends_lineA] at hl
    exact hl ((Relation.ReflTransGen.single (jB (by simp [hA.symm]))).trans
      (.single (jP (by simp)).symm))
  · rw [hC.ends_lineB] at hl
    exact hl ((Relation.ReflTransGen.single (jP (by simp)).symm).trans
      (.single (jA (by simp [hA]))))
  · have hpath : Relation.ReflTransGen (Joined C {.inr pl}) a c :=
      (Relation.ReflTransGen.single (jA (by simp))).trans (.single (jB (by simp)))
    rcases hpl with h | h <;> rw [h] at hl
    · exact hl hpath
    · exact hl ((Relation.ReflTransGen.single (jB (by simp)).symm).trans
        (.single (jA (by simp)).symm))

/-! ### Vacuum polarization loops -/

namespace IsVP

variable {a v w : Fin 3}

/-- The fermion line from `w` to `v`. -/
def lineV (hC : IsVP C a v w) : FermionLine C := fline hC.vw

/-- The fermion line from `v` to `w`. -/
def lineW (hC : IsVP C a v w) : FermionLine C := fline hC.wv

/-- The photon line, joining `a` and `w`. -/
def photonLine (hC : IsVP C a v w) : PhotonLine C :=
  hC.photon.line hC.hav.symm hC.haw hC.hvw

/-- The fermion line `lineV` is indexed by the `Ψ` of `v`. -/
@[simp]
theorem lineV_val (hC : IsVP C a v w) : hC.lineV.1 = Wick.fv v := rfl

/-- The fermion line `lineV` starts at `w`. -/
@[simp]
theorem tail_lineV (hC : IsVP C a v w) : hC.lineV.tail = Wick.fv w := tail_fline _

/-- The fermion line `lineW` is indexed by the `Ψ` of `w`. -/
@[simp]
theorem lineW_val (hC : IsVP C a v w) : hC.lineW.1 = Wick.fv w := rfl

/-- The fermion line `lineW` starts at `v`. -/
@[simp]
theorem tail_lineW (hC : IsVP C a v w) : hC.lineW.tail = Wick.fv v := tail_fline _

/-- The two fermion lines are distinct. -/
theorem lineV_ne_lineW (hC : IsVP C a v w) : hC.lineV ≠ hC.lineW := fun h =>
  hC.hvw (fv3_injective (congrArg Subtype.val h))

/-- The internal fermion lines of a vacuum polarization loop. -/
theorem fermionLine_cases (hC : IsVP C a v w) (f : FermionLine C) :
    f = hC.lineV ∨ f = hC.lineW := by
  rcases fv3_cases hC.hav hC.hvw hC.haw f.1 with h | h | h
  · exact absurd h (val_ne_of_eq_inl hC.inn f)
  · exact Or.inl (eq_fline _ f h)
  · exact Or.inr (eq_fline _ f h)

/-- The internal lines of a vacuum polarization loop. -/
theorem line_cases (hC : IsVP C a v w) (l : Line C) :
    l = .inl hC.lineV ∨ l = .inl hC.lineW ∨ l = .inr hC.photonLine := by
  rcases l with f | l
  · rcases hC.fermionLine_cases f with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (congrArg _ (hC.photon.eq_line _ _ _ l)))

/-- The fermion line from `w` to `v`. -/
theorem ends_lineV (hC : IsVP C a v w) : Line.ends (.inl hC.lineV : Line C) = (w, v) :=
  ends_fline _

/-- The fermion line from `v` to `w`. -/
theorem ends_lineW (hC : IsVP C a v w) : Line.ends (.inl hC.lineW : Line C) = (v, w) :=
  ends_fline _

/-- The photon line joins `a` and `w`. -/
theorem ends_photonLine (hC : IsVP C a v w) :
    Line.ends (.inr hC.photonLine : Line C) = (a, w) ∨
      Line.ends (.inr hC.photonLine : Line C) = (w, a) :=
  hC.photon.ends_line _ _ _

/-- The photon line is a bridge. -/
theorem isBridge_photonLine (hC : IsVP C a v w) : IsBridge (.inr hC.photonLine : Line C) := by
  have hav := hC.hav
  have haw := hC.haw
  refine isBridge_of_closed' {a} ?_ fun l hl => ?_
  · rcases hC.ends_photonLine with h | h <;> rw [h]
    · exact Or.inl (by simp [haw.symm])
    · exact Or.inr (by simp [haw.symm])
  · rcases hC.line_cases l with rfl | rfl | rfl
    · rw [hC.ends_lineV]
      simp [hav.symm, haw.symm]
    · rw [hC.ends_lineW]
      simp [hav.symm, haw.symm]
    · exact absurd rfl hl

/-- A vacuum polarization loop is connected but not 1PI. -/
theorem connected_not_isOnePI (hC : IsVP C a v w) :
    (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C := by
  refine ⟨⟨externalsAttached_of_out hC.out, ?_⟩, fun h => h.2.2 _ hC.isBridge_photonLine⟩
  exact verticesConnected_of_three hC.haw hC.hvw.symm hC.hav
    ⟨_, Set.notMem_empty _, hC.ends_photonLine⟩
    (joined_of_ends (Set.notMem_empty _) hC.ends_lineV)

end IsVP

/-! ### Tadpoles -/

namespace IsTP

variable {a b c u : Fin 3}

/-- The fermion line from `b` to `a`. -/
def lineA (hC : IsTP C a b c u) : FermionLine C := fline hC.ab

/-- The self-loop at `c`. -/
def loopC (hC : IsTP C a b c u) : FermionLine C := fline hC.cc

/-- The internal fermion lines of a tadpole. -/
theorem fermionLine_cases (hC : IsTP C a b c u) (f : FermionLine C) :
    f = hC.lineA ∨ f = hC.loopC := by
  rcases fv3_cases hC.hab hC.hbc hC.hac f.1 with h | h | h
  · exact Or.inl (eq_fline _ f h)
  · exact absurd h (val_ne_of_eq_inl hC.inn f)
  · exact Or.inr (eq_fline _ f h)

/-- The vertex `w` of the fermion line joined to `c` by the photon line: the one of `a`, `b`
without the external photon. -/
theorem exists_photon_partner (hC : IsTP C a b c u) :
    (u = a ∧ C.1.2 (.inr (Wick.ps b)) = .inr (Wick.ps c)) ∨
      (u = b ∧ C.1.2 (.inr (Wick.ps a)) = .inr (Wick.ps c)) := by
  rcases fin_three_eq_or hC.hab hC.hbc hC.hac u with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, hC.photon.snd_pair hC.hab hC.hbc hC.hac⟩
  · exact Or.inr ⟨rfl, hC.photon.snd_pair hC.hab.symm hC.hac hC.hbc⟩
  · exact absurd rfl hC.huc

/-- The fermion line from `b` to `a` is a bridge: removing it isolates the vertex with the
external photon. -/
theorem isBridge_lineA (hC : IsTP C a b c u) : IsBridge (.inl hC.lineA : Line C) := by
  have hab := hC.hab
  have hbc := hC.hbc
  have hac := hC.hac
  have hlA : Line.ends (.inl hC.lineA : Line C) = (b, a) := ends_fline _
  have hloop : Line.ends (.inl hC.loopC : Line C) = (c, c) := ends_fline _
  have hother : ∀ l : Line C, l ≠ .inl hC.lineA → l = .inl hC.loopC ∨ ∃ g : PhotonLine C,
      l = .inr g := by
    rintro (f | g) hl
    · rcases hC.fermionLine_cases f with rfl | rfl
      · exact absurd rfl hl
      · exact Or.inl rfl
    · exact Or.inr ⟨g, rfl⟩
  rcases hC.exists_photon_partner with ⟨hu, hp⟩ | ⟨hu, hp⟩ <;> have hu' := hu.symm <;>
    subst hu'
  · refine isBridge_of_closed' {b, c} (Or.inl (by rw [hlA]; simp [hab, hac])) fun l hl => ?_
    rcases hother l hl with rfl | ⟨g, rfl⟩
    · rw [hloop]
    · rw [hC.photon.eq_line hab hbc hac g]
      rcases hC.photon.ends_line hab hbc hac with h | h <;> rw [h] <;> simp
  · refine isBridge_of_closed' {b} (Or.inl (by rw [hlA]; simp [hab])) fun l hl => ?_
    rcases hother l hl with rfl | ⟨g, rfl⟩
    · rw [hloop]
    · rw [hC.photon.eq_line hab.symm hac hbc g]
      rcases hC.photon.ends_line hab.symm hac hbc with h | h <;> rw [h] <;>
        simp [hab, hbc.symm]

/-- **The self-loop at `c` is the loop line**: it is not a bridge, the other fermion line is a
bridge, and the photon line has a larger label. -/
theorem isLoopLine (hC : IsTP C a b c u) : IsLoopLine (.inl hC.loopC : Line C) := by
  refine ⟨not_isBridge_of_ends_eq (by rw [show Line.ends (.inl hC.loopC : Line C) = (c, c) from
    ends_fline _]), fun l hl => ?_⟩
  rcases l with f | g
  · rcases hC.fermionLine_cases f with rfl | rfl
    · exact absurd hC.isBridge_lineA hl
    · exact le_rfl
  · have := label_inr_ge g
    have hc : Line.label (.inl hC.loopC : Line C) = c.val := label_fline _
    omega

/-- **A tadpole has value `0`**, at every `ε` and for all momenta. -/
theorem contractionValue_eq_zero (P : Params) (hC : IsTP C a b c u)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue P C pOut pIn kIn αOut βIn μ = 0 :=
  contractionValue_eq_zero_of_selfLoop P (fun _ => rfl) hC.isLoopLine (tail_fline hC.cc) _ _ _ _
    _ _

/-- A tadpole is connected but not 1PI: the photon line joining `c` to the fermion line is a
bridge. -/
theorem connected_not_isOnePI (hC : IsTP C a b c u) :
    (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C := by
  have hab := hC.hab
  have hbc := hC.hbc
  have hac := hC.hac
  have hlA : Line.ends (.inl hC.lineA : Line C) = (b, a) := ends_fline _
  have hloop : Line.ends (.inl hC.loopC : Line C) = (c, c) := ends_fline _
  refine ⟨⟨externalsAttached_of_out hC.out, ?_⟩, fun h => ?_⟩
  · rcases hC.exists_photon_partner with ⟨hu, -⟩ | ⟨hu, -⟩ <;> have hu' := hu.symm <;>
      subst hu'
    · exact verticesConnected_of_three hab hbc hac (joined_of_ends (Set.notMem_empty _) hlA).symm
        ⟨_, Set.notMem_empty _, hC.photon.ends_line hab hbc hac⟩
    · exact verticesConnected_of_three hab.symm hac hbc (joined_of_ends (Set.notMem_empty _) hlA)
        ⟨_, Set.notMem_empty _, hC.photon.ends_line hab.symm hac hbc⟩
  · rcases hC.exists_photon_partner with ⟨hu, -⟩ | ⟨hu, -⟩ <;> have hu' := hu.symm <;>
      subst hu'
    · refine h.2.2 (.inr (hC.photon.line hab hbc hac)) (isBridge_of_closed' {c} ?_ fun l hl => ?_)
      · rcases hC.photon.ends_line hab hbc hac with h' | h' <;> rw [h']
        · exact Or.inr (by simp [hbc])
        · exact Or.inl (by simp [hbc])
      · rcases l with f | g
        · rcases hC.fermionLine_cases f with rfl | rfl
          · rw [hlA]; simp [hbc, hac]
          · rw [hloop]
        · exact absurd (congrArg _ (hC.photon.eq_line hab hbc hac g)) hl
    · refine h.2.2 (.inr (hC.photon.line hab.symm hac hbc))
        (isBridge_of_closed' {c} ?_ fun l hl => ?_)
      · rcases hC.photon.ends_line hab.symm hac hbc with h' | h' <;> rw [h']
        · exact Or.inr (by simp [hac])
        · exact Or.inl (by simp [hac])
      · rcases l with f | g
        · rcases hC.fermionLine_cases f with rfl | rfl
          · rw [hlA]; simp [hbc, hac]
          · rw [hloop]
        · exact absurd (congrArg _ (hC.photon.eq_line hab.symm hac hbc g)) hl

end IsTP

end QED.WickModel

end
