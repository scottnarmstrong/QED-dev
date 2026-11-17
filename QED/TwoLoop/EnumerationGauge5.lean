/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.EnumerationDecide
public import QED.TwoLoop.EnumerationRelabel

/-!
# The 1PI contractions of five gauge vertices

Obligation O2-2 (section 3.1 of `docs/TWO-LOOP-DERIVATION.md`) for the kind sequence of five
`gauge` vertices, `nf = nA = 1`: the order-`e⁵` electron–photon vertex without counterterms.

The nine classes (`Class5`) and a representative contraction of each (`Class5.rep`), with the
vertices `0, …, 4` and the fermion flow from the incoming electron `Ψ̄(y)` to the outgoing `Ψ(x)`:

| class | open line | closed loop | external photon at | internal photons | sign |
| --- | --- | --- | --- | --- | --- |
| `L` (ladder) | `0 1 2 3 4` | — | `2` | `(0 4) (1 3)` | `+1` |
| `X` (crossed ladder) | `0 1 2 3 4` | — | `2` | `(0 3) (1 4)` | `+1` |
| `Cp` (corner C₊) | `0 1 2 3 4` | — | `1` | `(0 3) (2 4)` | `+1` |
| `Cm` (corner C₋) | `0 1 2 3 4` | — | `3` | `(0 2) (1 4)` | `+1` |
| `Sp` (self-energy S₊, outgoing line) | `0 1 2 3 4` | — | `1` | `(0 4) (2 3)` | `+1` |
| `Sm` (self-energy S₋, incoming line) | `0 1 2 3 4` | — | `3` | `(0 4) (1 2)` | `+1` |
| `VP` (vacuum polarization) | `0 1 2` | `3 → 4 → 3` | `1` | `(0 3) (2 4)` | `-1` |
| `Fp` (Furry triangle) | `0 1` | `2 → 3 → 4 → 2` | `2` | `(0 3) (1 4)` | `-1` |
| `Fm` (Furry triangle, reversed) | `0 1` | `2 → 4 → 3 → 2` | `2` | `(0 3) (1 4)` | `-1` |

## Main statements

* `QED.TwoLoop.Enumeration.exists_rep_of_isOnePI`: every 1PI contraction of five gauge vertices
  is a relabelling (`relabel`) of one of the nine representatives.
* `QED.TwoLoop.Enumeration.relabel_rep_inj`: the relabellings of the representatives are
  pairwise distinct (no class coincides with another, and no representative has a nontrivial
  automorphism).
* `QED.TwoLoop.Enumeration.sum_isOnePI_gauges5`: **the structural theorem**: for every function
  `G` on contractions, the sum over the 1PI contractions of `fermionSign C * G C` is
  `∑ c, sign c * ∑ π : Perm (Fin 5), G (relabel π c.rep)`.
* `QED.TwoLoop.Enumeration.card_isOnePI_gauges5`: there are `9 · 5! = 1080` of them.
* `QED.TwoLoop.Enumeration.sum_isOnePI_gauges5_of_invariant`: for `G` invariant under
  relabelling, the sum is `5! ∑ c, sign c * G c.rep`, so the `1/5!` of the Wick expansion
  cancels and each class enters with coefficient one and its sign (section 3.3).

## Method

The finite checks are kernel evaluations (`decide +kernel`; no `native_decide`), each kept
small:

* `exists_std_*`: every fermion pairing becomes, after the relabelling read off from its cycles
  (`orderFun`), one of the 32 normal forms `stdList` (open line `0, 1, …`, then the closed loops
  as consecutive blocks), split by the image of the external `Ψ`;
* `inv_mem`: the photon pairings are the 15 of `invList`;
* `classify_std*`: each of the `32 × 15` contractions with a normal-form fermion pairing that
  is 1PI is a relabelling of a representative (14 of them are);
* `relabel_rep_eq`: a relabelling of a representative is a representative only trivially;
* `rep_isOnePI`, `fermionSign_rep`, `loopCount_rep`: the representatives are 1PI, with the
  signs above and two loops (T₂).

Relabelling preserves 1PI and the sign (`QED.TwoLoop.Enumeration.isOnePI_relabel_iff`,
`fermionSign_relabel`), which transports the normal-form checks to all `6! · 15 = 10800`
contractions.
-/

@[expose] public section

namespace QED.TwoLoop.Enumeration

open QED.WickModel

/-! ### Concrete contractions -/

/-- The fermion fields of vertex `t`. -/
def fv5 (t : Fin 5) : Wick.FermionVertex (gauges 5) := ⟨t, fun h => Wick.VertexKind.noConfusion h⟩

/-- The photon field of vertex `t`. -/
def ps5 (t : Fin 5) : Wick.PhotonSlot (gauges 5) := ⟨t, ⟨0, Nat.one_pos⟩⟩

/-- The fermion pairing with open line `y → v₁ → ⋯ → v_k → x` (`openLine = [v₁, …, v_k]`) and
closed loops `l₁ → l₂ → ⋯ → l₁` (each `[l₁, l₂, …]`), the arrows giving the fermion flow: a line
from `s` to `t` contracts the `Ψ` of `t` with the `Ψ̄` of `s`. -/
def fermionPerm (openLine : List (Fin 5)) (loops : List (List (Fin 5))) :
    Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)) :=
  (Sum.inl 0 :: openLine.reverse.map (Sum.inr ∘ fv5)).formPerm *
    (loops.map fun l => (l.reverse.map (Sum.inr ∘ fv5)).formPerm).prod

/-- The photon pairing with the external photon at vertex `ext` and internal photon lines
`pairs`. -/
def photonPerm (ext : Fin 5) (pairs : List (Fin 5 × Fin 5)) :
    Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 5)) :=
  Equiv.swap (.inl 0) (.inr (ps5 ext)) *
    (pairs.map fun p => Equiv.swap (.inr (ps5 p.1)) (.inr (ps5 p.2))).prod

/-- The nine classes of 1PI vertex graphs with five gauge vertices (section 3.1). -/
inductive Class5
  /-- ladder -/
  | L
  /-- crossed ladder -/
  | X
  /-- corner, vertex subgraph at the fourth vertex of the open line -/
  | Cp
  /-- corner, vertex subgraph at the second vertex of the open line -/
  | Cm
  /-- self-energy on the outgoing internal electron line -/
  | Sp
  /-- self-energy on the incoming internal electron line -/
  | Sm
  /-- vacuum polarization on the internal photon -/
  | VP
  /-- Furry triangle, fermion flow from the external-photon vertex towards the photon to `v₁` -/
  | Fp
  /-- Furry triangle, the other orientation -/
  | Fm
  deriving DecidableEq

instance : Fintype Class5 :=
  ⟨{.L, .X, .Cp, .Cm, .Sp, .Sm, .VP, .Fp, .Fm}, fun x => by cases x <;> simp⟩

theorem card_class5 : Fintype.card Class5 = 9 := rfl

/-- The fermion pairing of the representative. -/
def Class5.sigma : Class5 → Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))
  | .VP => fermionPerm [0, 1, 2] [[3, 4]]
  | .Fp => fermionPerm [0, 1] [[2, 3, 4]]
  | .Fm => fermionPerm [0, 1] [[2, 4, 3]]
  | _ => fermionPerm [0, 1, 2, 3, 4] []

/-- The photon pairing of the representative. -/
def Class5.tau : Class5 → Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 5))
  | .L => photonPerm 2 [(0, 4), (1, 3)]
  | .X => photonPerm 2 [(0, 3), (1, 4)]
  | .Cp => photonPerm 1 [(0, 3), (2, 4)]
  | .Cm => photonPerm 3 [(0, 2), (1, 4)]
  | .Sp => photonPerm 1 [(0, 4), (2, 3)]
  | .Sm => photonPerm 3 [(0, 4), (1, 2)]
  | .VP => photonPerm 1 [(0, 3), (2, 4)]
  | .Fp => photonPerm 2 [(0, 3), (1, 4)]
  | .Fm => photonPerm 2 [(0, 3), (1, 4)]

theorem Class5.tau_involutive : ∀ c : Class5, ∀ b, c.tau (c.tau b) = b ∧ c.tau b ≠ b := by
  decide +kernel

/-- The representative contraction of a class (the table in the module docstring). -/
def Class5.rep (c : Class5) : Contraction 1 1 (gauges 5) := ⟨(c.sigma, c.tau), c.tau_involutive⟩

/-- The sign of a class: `-1` exactly when it has a closed fermion loop. -/
def Class5.sign : Class5 → ℤ
  | .VP | .Fp | .Fm => -1
  | _ => 1

/-- Equality of contractions of five gauge vertices is decidable. -/
scoped instance : DecidableEq (Contraction 1 1 (gauges 5)) := fun a b =>
  decidable_of_iff (a.1.1 = b.1.1 ∧ a.1.2 = b.1.2) (by rw [← Prod.ext_iff, Subtype.ext_iff])

/-! ### Finite checks on the representatives -/

theorem rep_isOnePI : ∀ c : Class5, IsOnePI c.rep := by decide +kernel

theorem fermionSign_rep : ∀ c : Class5, fermionSign c.rep = c.sign := by decide +kernel

/-- Each representative has two loops (T₂): these are genuine two-loop contractions. -/
theorem loopCount_rep (c : Class5) : loopCount c.rep = 2 := by
  rw [loopCount_eq_card]
  revert c
  decide +kernel

theorem relabel_rep_eq : ∀ (c c' : Class5) (ρ : Equiv.Perm (Fin 5)),
    relabel ρ c.rep = c'.rep → c = c' ∧ ρ = 1 := by decide +kernel

/-! ### Photon pairings -/

/-- A fixed-point-free involution of the photon fields. -/
def IsInvol (τ : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 5))) : Prop :=
  ∀ b, τ (τ b) = b ∧ τ b ≠ b

instance : DecidablePred IsInvol := fun τ => by unfold IsInvol; infer_instance

/-- The fifteen photon pairings. -/
def invList : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 5))) :=
  [photonPerm 0 [(1, 2), (3, 4)],
    photonPerm 0 [(1, 3), (2, 4)],
    photonPerm 0 [(1, 4), (2, 3)],
    photonPerm 1 [(0, 2), (3, 4)],
    photonPerm 1 [(0, 3), (2, 4)],
    photonPerm 1 [(0, 4), (2, 3)],
    photonPerm 2 [(0, 1), (3, 4)],
    photonPerm 2 [(0, 3), (1, 4)],
    photonPerm 2 [(0, 4), (1, 3)],
    photonPerm 3 [(0, 1), (2, 4)],
    photonPerm 3 [(0, 2), (1, 4)],
    photonPerm 3 [(0, 4), (1, 2)],
    photonPerm 4 [(0, 1), (2, 3)],
    photonPerm 4 [(0, 2), (1, 3)],
    photonPerm 4 [(0, 3), (1, 2)]]

theorem inv_mem : ∀ τ : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 5)),
    IsInvol τ → τ ∈ invList := by decide +kernel

theorem invList_isInvol : ∀ τ ∈ invList, IsInvol τ := by decide +kernel

/-- The fifteen contractions with fermion pairing `σ`. -/
def withSigma (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :
    List (Contraction 1 1 (gauges 5)) :=
  invList.attach.map fun τ => ⟨(σ, τ.1), fun b => invList_isInvol τ.1 τ.2 b⟩

theorem mem_withSigma (C : Contraction 1 1 (gauges 5)) : C ∈ withSigma C.1.1 :=
  List.mem_map.mpr ⟨⟨C.1.2, inv_mem _ C.2⟩, List.mem_attach _ _, rfl⟩

/-! ### Fermion pairings in normal form -/

/-- Fermion pairings in normal form, part 0. -/
def stdList0 : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :=
  [fermionPerm [0, 1, 2, 3, 4] [],
    fermionPerm [0, 1, 2, 3] [[4]],
    fermionPerm [0, 1, 2] [[3], [4]],
    fermionPerm [0, 1, 2] [[3, 4]],
    fermionPerm [0, 1] [[2], [3], [4]],
    fermionPerm [0, 1] [[2], [3, 4]],
    fermionPerm [0, 1] [[2, 3], [4]],
    fermionPerm [0, 1] [[2, 3, 4]]]

/-- Fermion pairings in normal form, part 1. -/
def stdList1 : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :=
  [fermionPerm [0] [[1], [2], [3], [4]],
    fermionPerm [0] [[1], [2], [3, 4]],
    fermionPerm [0] [[1], [2, 3], [4]],
    fermionPerm [0] [[1], [2, 3, 4]],
    fermionPerm [0] [[1, 2], [3], [4]],
    fermionPerm [0] [[1, 2], [3, 4]],
    fermionPerm [0] [[1, 2, 3], [4]],
    fermionPerm [0] [[1, 2, 3, 4]]]

/-- Fermion pairings in normal form, part 2. -/
def stdList2 : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :=
  [fermionPerm [] [[0], [1], [2], [3], [4]],
    fermionPerm [] [[0], [1], [2], [3, 4]],
    fermionPerm [] [[0], [1], [2, 3], [4]],
    fermionPerm [] [[0], [1], [2, 3, 4]],
    fermionPerm [] [[0], [1, 2], [3], [4]],
    fermionPerm [] [[0], [1, 2], [3, 4]],
    fermionPerm [] [[0], [1, 2, 3], [4]],
    fermionPerm [] [[0], [1, 2, 3, 4]]]

/-- Fermion pairings in normal form, part 3. -/
def stdList3 : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :=
  [fermionPerm [] [[0, 1], [2], [3], [4]],
    fermionPerm [] [[0, 1], [2], [3, 4]],
    fermionPerm [] [[0, 1], [2, 3], [4]],
    fermionPerm [] [[0, 1], [2, 3, 4]],
    fermionPerm [] [[0, 1, 2], [3], [4]],
    fermionPerm [] [[0, 1, 2], [3, 4]],
    fermionPerm [] [[0, 1, 2, 3], [4]],
    fermionPerm [] [[0, 1, 2, 3, 4]]]

/-- The 32 fermion pairings in normal form: the open line `0 → 1 → ⋯ → k-1`, then the closed
loops as consecutive blocks `b → b+1 → ⋯ → e → b`. -/
def stdList : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :=
  stdList0 ++ stdList1 ++ stdList2 ++ stdList3

/-- Follow `σ⁻¹` (the fermion flow) from `x` until `stop`, listing the vertices met. -/
def chainFrom (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)))
    (stop : Fin 1 ⊕ Wick.FermionVertex (gauges 5)) :
    Fin 1 ⊕ Wick.FermionVertex (gauges 5) → ℕ → List (Fin 5)
  | _, 0 => []
  | x, n + 1 =>
    match σ.symm x with
    | .inl _ => []
    | .inr t => if (Sum.inr t : Fin 1 ⊕ Wick.FermionVertex (gauges 5)) = stop then []
      else t.1 :: chainFrom σ stop (.inr t) n

/-- The vertices in the order of the open line, then of the closed loops, each loop started at
its smallest vertex, the loops ordered by their smallest vertex. -/
def vertexOrder (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) : List (Fin 5) :=
  (List.finRange 5).foldl (fun acc t => if t ∈ acc then acc else
      acc ++ (t :: chainFrom σ (.inr (fv5 t)) (.inr (fv5 t)) 5))
    (chainFrom σ (.inl 0) (.inl 0) 5)

/-- The `i`-th vertex of `vertexOrder σ`. -/
def orderFun (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) (i : Fin 5) : Fin 5 :=
  (vertexOrder σ).getD i 0

/-- The permutation of a bijection, with the inverse computed by search (`Fintype.bijInv`). -/
def permOfBij {n : ℕ} (g : Fin n → Fin n) (h : Function.Bijective g) : Equiv.Perm (Fin n) where
  toFun := g
  invFun := Fintype.bijInv h
  left_inv := Fintype.leftInverse_bijInv h
  right_inv := Fintype.rightInverse_bijInv h

/-- The relabelling read off from the cycles of `σ` puts `σ` in normal form. -/
def StdWitness (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) : Prop :=
  ∃ h : Function.Bijective (orderFun σ),
    (extF (permOfBij (orderFun σ) h).symm).permCongr σ ∈ stdList

instance : DecidablePred StdWitness := fun σ => by unfold StdWitness; infer_instance

theorem exists_std_inl : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)),
    σ (.inl 0) = .inl 0 → StdWitness σ := by
  decide +kernel

theorem exists_std_v0 : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)),
    σ (.inl 0) = .inr (fv5 0) → StdWitness σ := by
  decide +kernel

theorem exists_std_v1 : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)),
    σ (.inl 0) = .inr (fv5 1) → StdWitness σ := by
  decide +kernel

theorem exists_std_v2 : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)),
    σ (.inl 0) = .inr (fv5 2) → StdWitness σ := by
  decide +kernel

theorem exists_std_v3 : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)),
    σ (.inl 0) = .inr (fv5 3) → StdWitness σ := by
  decide +kernel

theorem exists_std_v4 : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)),
    σ (.inl 0) = .inr (fv5 4) → StdWitness σ := by
  decide +kernel

theorem exists_std (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) :
    ∃ ρ : Equiv.Perm (Fin 5), (extF ρ).permCongr σ ∈ stdList := by
  have hv : ∀ t : Fin 5, σ (.inl 0) = .inr (fv5 t) → StdWitness σ := by
    intro t
    fin_cases t
    exacts [exists_std_v0 σ, exists_std_v1 σ, exists_std_v2 σ, exists_std_v3 σ, exists_std_v4 σ]
  have key : StdWitness σ := by
    rcases hσ : σ (.inl 0) with i | t
    · exact exists_std_inl σ (by rw [hσ, Subsingleton.elim i 0])
    · exact hv t.1 (by rw [hσ]; rfl)
  obtain ⟨h, hmem⟩ := key
  exact ⟨_, hmem⟩

/-! ### Classification of the normal forms -/

theorem classify_std0 : ∀ σ ∈ stdList0, ∀ C ∈ withSigma σ, IsOnePI C →
    ∃ c : Class5, ∃ ρ : Equiv.Perm (Fin 5), C = relabel ρ c.rep := by
  decide +kernel

theorem classify_std1 : ∀ σ ∈ stdList1, ∀ C ∈ withSigma σ, IsOnePI C →
    ∃ c : Class5, ∃ ρ : Equiv.Perm (Fin 5), C = relabel ρ c.rep := by
  decide +kernel

theorem classify_std2 : ∀ σ ∈ stdList2, ∀ C ∈ withSigma σ, IsOnePI C →
    ∃ c : Class5, ∃ ρ : Equiv.Perm (Fin 5), C = relabel ρ c.rep := by
  decide +kernel

theorem classify_std3 : ∀ σ ∈ stdList3, ∀ C ∈ withSigma σ, IsOnePI C →
    ∃ c : Class5, ∃ ρ : Equiv.Perm (Fin 5), C = relabel ρ c.rep := by
  decide +kernel

theorem classify_std : ∀ σ ∈ stdList, ∀ C ∈ withSigma σ, IsOnePI C →
    ∃ c : Class5, ∃ ρ : Equiv.Perm (Fin 5), C = relabel ρ c.rep := by
  intro σ hσ
  simp only [stdList, List.mem_append] at hσ
  rcases hσ with ((h | h) | h) | h
  · exact classify_std0 σ h
  · exact classify_std1 σ h
  · exact classify_std2 σ h
  · exact classify_std3 σ h

/-! ### The classification -/

/-- **Every 1PI contraction of five gauge vertices is a relabelling of a representative.** -/
theorem exists_rep_of_isOnePI {C : Contraction 1 1 (gauges 5)} (hC : IsOnePI C) :
    ∃ c : Class5, ∃ π : Equiv.Perm (Fin 5), C = relabel π c.rep := by
  obtain ⟨ρ, hρ⟩ := exists_std C.1.1
  have h0 : IsOnePI (relabel ρ C) := (isOnePI_relabel_iff ρ C).mpr hC
  obtain ⟨c, π, hπ⟩ := classify_std _ hρ (relabel ρ C) (mem_withSigma _) h0
  refine ⟨c, ρ⁻¹ * π, ?_⟩
  rw [relabel_mul, ← hπ, ← relabel_mul, inv_mul_cancel, relabel_one]

/-- **The relabellings of the representatives are pairwise distinct.** -/
theorem relabel_rep_inj {c c' : Class5} {π π' : Equiv.Perm (Fin 5)}
    (h : relabel π c.rep = relabel π' c'.rep) : c = c' ∧ π = π' := by
  have h' : relabel (π'⁻¹ * π) c.rep = c'.rep := by
    rw [relabel_mul, h, ← relabel_mul, inv_mul_cancel, relabel_one]
  obtain ⟨hc, hρ⟩ := relabel_rep_eq c c' _ h'
  exact ⟨hc, (inv_mul_eq_one.mp hρ).symm⟩

/-- The structural sum over any finset whose members are exactly the 1PI contractions. -/
theorem sum_of_mem_iff {s : Finset (Contraction 1 1 (gauges 5))}
    (hs : ∀ C, C ∈ s ↔ IsOnePI C) (G : Contraction 1 1 (gauges 5) → ℂ) :
    ∑ C ∈ s, ((fermionSign C : ℤ) : ℂ) * G C =
      ∑ c : Class5, (c.sign : ℂ) * ∑ π : Equiv.Perm (Fin 5), G (relabel π c.rep) := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ => relabel x.2 x.1.rep) (fun x _ => ?_) (fun x _ y _ hxy => ?_)
    (fun C hC => ?_) (fun x _ => ?_)
  · exact (hs _).mpr ((isOnePI_relabel_iff _ _).mpr (rep_isOnePI _))
  · obtain ⟨h1, h2⟩ := relabel_rep_inj hxy
    exact Prod.ext h1 h2
  · obtain ⟨c, π, rfl⟩ := exists_rep_of_isOnePI ((hs C).mp hC)
    exact ⟨(c, π), by simp, rfl⟩
  · rw [fermionSign_relabel, fermionSign_rep]

/-- The count over any finset whose members are exactly the 1PI contractions. -/
theorem card_of_mem_iff {s : Finset (Contraction 1 1 (gauges 5))}
    (hs : ∀ C, C ∈ s ↔ IsOnePI C) : s.card = 1080 := by
  have : s.card = (Finset.univ : Finset (Class5 × Equiv.Perm (Fin 5))).card := by
    symm
    refine Finset.card_bij (fun x _ => relabel x.2 x.1.rep) (fun x _ => ?_)
      (fun x _ y _ hxy => ?_) (fun C hC => ?_)
    · exact (hs _).mpr ((isOnePI_relabel_iff _ _).mpr (rep_isOnePI _))
    · obtain ⟨h1, h2⟩ := relabel_rep_inj hxy
      exact Prod.ext h1 h2
    · obtain ⟨c, π, rfl⟩ := exists_rep_of_isOnePI ((hs C).mp hC)
      exact ⟨(c, π), by simp, rfl⟩
  rw [this, Finset.card_univ, Fintype.card_prod, card_class5, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- **The 1PI contractions of five gauge vertices, summed with their signs** (obligation O2-2,
the no-counterterm part). For every function `G` of the contractions, the sum over the 1PI
contractions of `fermionSign C * G C` is the sum over the nine classes of the class sign times
the sum of `G` over the `5!` relabellings of the representative. The instances are arbitrary
(in particular the classical ones of the frozen `onePIFunction₂`). -/
theorem sum_isOnePI_gauges5 {instF : Fintype (Contraction 1 1 (gauges 5))}
    {instD : DecidablePred (IsOnePI (nf := 1) (nA := 1) (κ := gauges 5))}
    (G : Contraction 1 1 (gauges 5) → ℂ) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 (gauges 5))).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * G C =
      ∑ c : Class5, (c.sign : ℂ) * ∑ π : Equiv.Perm (Fin 5), G (relabel π c.rep) :=
  sum_of_mem_iff (fun C => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) G

/-- There are `9 · 5! = 1080` 1PI contractions of five gauge vertices. -/
theorem card_isOnePI_gauges5 {instF : Fintype (Contraction 1 1 (gauges 5))}
    {instD : DecidablePred (IsOnePI (nf := 1) (nA := 1) (κ := gauges 5))} :
    ((Finset.univ : Finset (Contraction 1 1 (gauges 5))).filter IsOnePI).card = 1080 :=
  card_of_mem_iff fun C => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Coefficient one per class.** For a function `G` invariant under relabelling (as the value
of a contraction is expected to be, section 3.3), the signed sum over the 1PI contractions is
`5!` times the sum over the classes of the class sign times the value of the representative. -/
theorem sum_isOnePI_gauges5_of_invariant {instF : Fintype (Contraction 1 1 (gauges 5))}
    {instD : DecidablePred (IsOnePI (nf := 1) (nA := 1) (κ := gauges 5))}
    (G : Contraction 1 1 (gauges 5) → ℂ)
    (hG : ∀ π C, G (relabel π C) = G C) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 (gauges 5))).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * G C =
      (Nat.factorial 5 : ℂ) * ∑ c : Class5, (c.sign : ℂ) * G c.rep := by
  rw [sum_isOnePI_gauges5, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hG, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  ring

end QED.TwoLoop.Enumeration

end
