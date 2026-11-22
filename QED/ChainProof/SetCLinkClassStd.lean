/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkReps
public import QED.TwoLoop.RelabelCountertermLines
public import QED.Frozen.Wick.VertexKindFintype

/-!
# The set (c) classification: standard forms and the finite search space

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step. A set (c) contraction is classified in two stages: its
vertices are first renumbered along the open line (the element last), which puts the fermion
pairing in the standard form `stdNext κ L b` (open line `0 → 1 → ⋯ → L - 1`, and, if `b`, a
bubble `L ⇄ L + 1`); the photon pairing is then one of the perfect matchings of the photon fields
(`matchings`), so the contraction lies in the explicit finite list `stdContractions κ L b`, which
is searched by kernel evaluation (`QED/ChainProof/SetCLinkClassDecB.lean`, …).

* `QED.ChainProof.SetCLink.exists_matching`: a fixed-point-free involution of a finite type is
  the product of the transpositions of one of the perfect matchings of any duplicate-free list of
  all its elements.
* `QED.ChainProof.SetCLink.mem_stdContractions`: a contraction whose fermion pairing agrees with
  `stdNext κ L b` lies in `stdContractions κ L b`.
* `QED.ChainProof.SetCLink.relabelK_trans`, `relabelK_self`: relabellings compose, and a
  relabelling fixing every vertex is the identity.
* `QED.ChainProof.SetCLink.repsCZ`, `repsCS`, `repsC`: the 56 representatives of
  `QED/ChainProof/SetCLinkReps.lean` by vertex number (`RepC`: kinds, contraction, grading); the
  level-`0` ones (a bubble or a `δ₃` element) and the level-`1` ones (the VP-share counterterm
  graphs).
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum

variable {N : ℕ}

/-- Equality of contractions is decidable. -/
scoped instance instDecidableEqContractionC {κ : Fin N → Wick.VertexKind} :
    DecidableEq (Contraction 1 1 κ) := fun a b =>
  decidable_of_iff (a.1.1 = b.1.1 ∧ a.1.2 = b.1.2) (by rw [← Prod.ext_iff, Subtype.ext_iff])

/-! ### The standard fermion pairing -/

/-- The fermion field of vertex `i` (the external field if `i ≥ N` or `i` is a `photonCt`). -/
def toFN (κ : Fin N → Wick.VertexKind) (i : ℕ) : Fin 1 ⊕ Wick.FermionVertex κ :=
  if h : i < N then (if h' : κ ⟨i, h⟩ = .photonCt then .inl 0 else .inr ⟨⟨i, h⟩, h'⟩) else .inl 0

/-- **The standard fermion pairing**: the open line `Ψ(x) → 0 → 1 → ⋯ → L - 1 → Ψ̄(y)`, and, if
`b`, the bubble `L ⇄ L + 1`; every other fermion field is fixed. -/
def stdNext (κ : Fin N → Wick.VertexKind) (L : ℕ) (b : Bool) :
    Fin 1 ⊕ Wick.FermionVertex κ → Fin 1 ⊕ Wick.FermionVertex κ
  | .inl _ => if 0 < L then toFN κ 0 else .inl 0
  | .inr v =>
    if v.1.val + 1 < L then toFN κ (v.1.val + 1)
    else if v.1.val + 1 = L then .inl 0
    else if b ∧ v.1.val = L then toFN κ (L + 1)
    else if b ∧ v.1.val = L + 1 then toFN κ L
    else .inr v

/-- The permutation of a bijection of a finite type, with the inverse computed by search. -/
def permOfBijF {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) (h : Function.Bijective f) :
    Equiv.Perm α where
  toFun := f
  invFun := Fintype.bijInv h
  left_inv := Fintype.leftInverse_bijInv h
  right_inv := Fintype.rightInverse_bijInv h

/-- The standard fermion pairing as a permutation (the identity if `stdNext` is not bijective). -/
def stdSigma (κ : Fin N → Wick.VertexKind) (L : ℕ) (b : Bool) :
    Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ) :=
  if h : Function.Bijective (stdNext κ L b) then permOfBijF _ h else 1

/-! ### Perfect matchings -/

/-- The photon fields: the external one, then those of the vertices in order. -/
def slotList (κ : Fin N → Wick.VertexKind) : List (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  .inl 0 :: (List.finRange N).flatMap fun t =>
    (List.finRange (κ t).photonSlots).map fun j => .inr ⟨t, j⟩

/-- The perfect matchings of a list (with fuel `n`): the head is paired with each later element,
and the rest is matched recursively. -/
def matchings {α : Type*} [DecidableEq α] : ℕ → List α → List (List (α × α))
  | _, [] => [[]]
  | 0, _ :: _ => []
  | n + 1, x :: l => l.flatMap fun y => (matchings n (l.erase y)).map ((x, y) :: ·)

/-- The product of the transpositions of a matching. -/
def swapsPerm {α : Type*} [DecidableEq α] (m : List (α × α)) : Equiv.Perm α :=
  (m.map fun p => Equiv.swap p.1 p.2).prod

/-- **The contractions in standard form**: the standard fermion pairing, and a photon pairing
from a perfect matching of the photon fields. -/
def stdContractions (κ : Fin N → Wick.VertexKind) (L : ℕ) (b : Bool) :
    List (Contraction 1 1 κ) :=
  (matchings (slotList κ).length (slotList κ)).filterMap fun m =>
    if h : ∀ x, swapsPerm m (swapsPerm m x) = x ∧ swapsPerm m x ≠ x then
      some ⟨(stdSigma κ L b, swapsPerm m), h⟩ else none

theorem mem_slotList {κ : Fin N → Wick.VertexKind} (x : Fin 1 ⊕ Wick.PhotonSlot κ) :
    x ∈ slotList κ := by
  rcases x with i | ⟨t, j⟩
  · rw [Subsingleton.elim i 0]
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨t, List.mem_finRange t,
      List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩)

theorem slotList_nodup (κ : Fin N → Wick.VertexKind) : (slotList κ).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp [List.mem_flatMap]
  · refine List.nodup_flatMap.mpr ⟨fun t _ => (List.nodup_finRange _).map fun a b h => ?_, ?_⟩
    · simpa using h
    · refine (List.nodup_finRange N).imp fun {a b} hab x hxa hxb => hab ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hxa
      obtain ⟨j', -, e⟩ := List.mem_map.mp hxb
      exact ((Sigma.mk.inj_iff.mp (Sum.inr_injective e)).1).symm

/-- **A fixed-point-free involution is a matching.** For every duplicate-free list `l` closed
under `τ` and every fuel `n ≥ l.length`, some matching of `l` agrees with `τ` on `l` and fixes
every element off `l`. -/
theorem exists_matching {α : Type*} [DecidableEq α] (τ : Equiv.Perm α)
    (hτ : ∀ x, τ (τ x) = x ∧ τ x ≠ x) : ∀ (n : ℕ) (l : List α), l.length ≤ n → l.Nodup →
      (∀ x ∈ l, τ x ∈ l) →
        ∃ m ∈ matchings n l, (∀ x ∈ l, swapsPerm m x = τ x) ∧ ∀ x, x ∉ l → swapsPerm m x = x := by
  intro n
  induction n with
  | zero =>
    intro l hl _ _
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    exact ⟨[], by simp [matchings], by simp, fun x _ => rfl⟩
  | succ n ih =>
    intro l hl hnd hcl
    cases l with
    | nil => exact ⟨[], by simp [matchings], by simp, fun x _ => rfl⟩
    | cons x l' =>
      have hx' : x ∉ l' := (List.nodup_cons.mp hnd).1
      have hnd' : l'.Nodup := (List.nodup_cons.mp hnd).2
      have hy : τ x ∈ l' := by
        rcases List.mem_cons.mp (hcl x List.mem_cons_self) with h | h
        · exact absurd h (hτ x).2
        · exact h
      have hyx : τ (τ x) = x := (hτ x).1
      have hcl' : ∀ z ∈ l'.erase (τ x), τ z ∈ l'.erase (τ x) := by
        intro z hz
        rw [hnd'.mem_erase_iff] at hz ⊢
        obtain ⟨hzy, hz'⟩ := hz
        have hzx : z ≠ x := fun e => hx' (e ▸ hz')
        refine ⟨fun e => hzx (τ.injective e), ?_⟩
        rcases List.mem_cons.mp (hcl z (List.mem_cons_of_mem _ hz')) with h | h
        · exact absurd (by rw [← h, (hτ z).1]) hzy
        · exact h
      have hlen : (l'.erase (τ x)).length ≤ n := by
        rw [List.length_erase_of_mem hy]
        simp only [List.length_cons] at hl
        omega
      obtain ⟨m', hm', hin, hout⟩ := ih (l'.erase (τ x)) hlen (hnd'.erase _) hcl'
      have hs : ∀ z, swapsPerm ((x, τ x) :: m') z = Equiv.swap x (τ x) (swapsPerm m' z) :=
        fun z => by simp [swapsPerm, Equiv.Perm.mul_apply]
      have hxe : x ∉ l'.erase (τ x) := fun h => hx' (List.mem_of_mem_erase h)
      have hye : τ x ∉ l'.erase (τ x) := hnd'.not_mem_erase
      refine ⟨(x, τ x) :: m', ?_, ?_, ?_⟩
      · simp only [matchings, List.mem_flatMap, List.mem_map]
        exact ⟨τ x, hy, m', hm', rfl⟩
      · intro z hz
        rw [hs]
        rcases List.mem_cons.mp hz with rfl | hz'
        · rw [hout z hxe, Equiv.swap_apply_left]
        · by_cases hzy : z = τ x
          · rw [hzy, hout _ hye, Equiv.swap_apply_right, hyx]
          · have hze : z ∈ l'.erase (τ x) := hnd'.mem_erase_iff.mpr ⟨hzy, hz'⟩
            have h1 := hcl' z hze
            rw [hin z hze]
            exact Equiv.swap_apply_of_ne_of_ne (fun e => hxe (e ▸ h1)) (fun e => hye (e ▸ h1))
      · intro z hz
        rw [hs]
        have hzx : z ≠ x := fun e => hz (e ▸ List.mem_cons_self)
        have hzl' : z ∉ l' := fun h => hz (List.mem_cons_of_mem _ h)
        have hzy : z ≠ τ x := fun e => hzl' (e ▸ hy)
        rw [hout z (fun h => hzl' (List.mem_of_mem_erase h)),
          Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- **A contraction in standard form is listed.** -/
theorem mem_stdContractions {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (L : ℕ)
    (b : Bool) (h : ∀ z, C.1.1 z = stdNext κ L b z) : C ∈ stdContractions κ L b := by
  have hfun : stdNext κ L b = ⇑C.1.1 := funext fun z => (h z).symm
  have hbij : Function.Bijective (stdNext κ L b) := hfun ▸ C.1.1.bijective
  have hσ : stdSigma κ L b = C.1.1 := by
    ext z
    simp only [stdSigma, dite_eq_left hbij]
    exact (h z).symm
  obtain ⟨m, hm, hin, -⟩ := exists_matching C.1.2 C.2 _ (slotList κ) le_rfl (slotList_nodup κ)
    (fun x _ => mem_slotList _)
  have hτ : swapsPerm m = C.1.2 := Equiv.ext fun x => hin x (mem_slotList x)
  have hinv : ∀ x, swapsPerm m (swapsPerm m x) = x ∧ swapsPerm m x ≠ x := by
    rw [hτ]
    exact C.2
  unfold stdContractions
  rw [List.mem_filterMap]
  refine ⟨m, hm, ?_⟩
  rw [dite_eq_left hinv]
  exact congrArg some (Subtype.ext (Prod.ext hσ hτ))

/-! ### Relabellings compose -/

section Compose

variable {κ₁ κ₂ κ₃ : Fin N → Wick.VertexKind}

/-- **Relabellings compose.** -/
theorem relabelK_trans (π₁ : Equiv.Perm (Fin N)) (h₁ : ∀ t, κ₂ (π₁ t) = κ₁ t)
    (π₂ : Equiv.Perm (Fin N)) (h₂ : ∀ t, κ₃ (π₂ t) = κ₂ t)
    (h₃ : ∀ t, κ₃ ((π₂ * π₁) t) = κ₁ t) (C : Contraction 1 1 κ₁) :
    relabelK π₂ h₂ (relabelK π₁ h₁ C) = relabelK (π₂ * π₁) h₃ C := by
  have eF : ∀ z : Fin 1 ⊕ Wick.FermionVertex κ₁,
      extFK π₂ h₂ (extFK π₁ h₁ z) = extFK (π₂ * π₁) h₃ z := by
    rintro (i | v) <;> rfl
  have eP : ∀ z : Fin 1 ⊕ Wick.PhotonSlot κ₁,
      extPK π₂ h₂ (extPK π₁ h₁ z) = extPK (π₂ * π₁) h₃ z := by
    rintro (i | v) <;> rfl
  refine Subtype.ext (Prod.ext (Equiv.ext fun y => ?_) (Equiv.ext fun y => ?_))
  · obtain ⟨z, rfl⟩ := (extFK (π₂ * π₁) h₃).surjective y
    rw [relabelK_fst_apply, ← eF, ← eF, relabelK_fst_apply, relabelK_fst_apply]
  · obtain ⟨z, rfl⟩ := (extPK (π₂ * π₁) h₃).surjective y
    rw [relabelK_snd_apply, ← eP, ← eP, relabelK_snd_apply, relabelK_snd_apply]

/-- **A relabelling fixing every vertex is the identity.** -/
theorem relabelK_self (π : Equiv.Perm (Fin N)) (hπ : ∀ t, π t = t) (h : ∀ t, κ₁ (π t) = κ₁ t)
    (C : Contraction 1 1 κ₁) : relabelK π h C = C := by
  have eF : ∀ z : Fin 1 ⊕ Wick.FermionVertex κ₁, extFK π h z = z := by
    rintro (i | v)
    · rfl
    · exact congrArg Sum.inr (fv_ext (hπ v.1))
  have eP : ∀ z : Fin 1 ⊕ Wick.PhotonSlot κ₁, extPK π h z = z := by
    rintro (i | a)
    · rfl
    · exact congrArg Sum.inr (ps_ext (hπ a.1) rfl)
  refine Subtype.ext (Prod.ext (Equiv.ext fun y => ?_) (Equiv.ext fun y => ?_))
  · have e := relabelK_fst_apply π h C y
    rwa [eF, eF] at e
  · have e := relabelK_snd_apply π h C y
    rwa [eP, eP] at e

end Compose

/-! ### The kind sequences of the search -/

/-- An open line of kinds `ℓ`, then a bubble (two `gauge` vertices). -/
def kindsB {L : ℕ} (ℓ : Fin L → Wick.VertexKind) : Fin (L + 2) → Wick.VertexKind :=
  fun i => if h : i.val < L then ℓ ⟨i.val, h⟩ else .gauge

/-- An open line of kinds `ℓ`, then a `photonCt` vertex. -/
def kindsD {L : ℕ} (ℓ : Fin L → Wick.VertexKind) : Fin (L + 1) → Wick.VertexKind :=
  fun i => if h : i.val < L then ℓ ⟨i.val, h⟩ else .photonCt

/-- The exchange of the two bubble vertices `L`, `L + 1`. -/
def swapLast (L : ℕ) : Equiv.Perm (Fin (L + 2)) :=
  Equiv.swap (Fin.castSucc (Fin.last L)) (Fin.last (L + 1))

/-- The kind conditions of the element branches at graded order `7`: the vertex orders sum to an
odd number at most `7`, and if less, some vertex is a `gaugeCt` or `fermionCt` vertex (the
counterterm of positive level). -/
def KFilter {M : ℕ} (κ : Fin M → Wick.VertexKind) : Prop :=
  ∑ t, (κ t).order ≤ 7 ∧ (∑ t, (κ t).order) % 2 = 1 ∧
    (∑ t, (κ t).order < 7 → ∃ t, κ t ≠ .gauge ∧ κ t ≠ .photonCt)

instance {M : ℕ} (κ : Fin M → Wick.VertexKind) : Decidable (KFilter κ) := by
  unfold KFilter; infer_instance

/-- The kind conditions of the VP-share branch: no `photonCt` vertex, vertex orders summing to
`5`, and exactly one vertex other than `gauge`. -/
def SFilter {M : ℕ} (κ : Fin M → Wick.VertexKind) : Prop :=
  (∀ t, κ t ≠ .photonCt) ∧ ∑ t, (κ t).order = 5 ∧ (∃ t, κ t ≠ .gauge) ∧
    ∀ t t', κ t ≠ .gauge → κ t' ≠ .gauge → t = t'

instance {M : ℕ} (κ : Fin M → Wick.VertexKind) : Decidable (SFilter κ) := by
  unfold SFilter; infer_instance

/-! ### The representatives by vertex number -/

/-- A set (c) representative: its kinds, its contraction and its grading. -/
structure RepC (N : ℕ) where
  /-- the kind sequence -/
  kinds : Fin N → Wick.VertexKind
  /-- the contraction -/
  rep : Contraction 1 1 kinds
  /-- the grading -/
  grad : Graded.Grading kinds

/-- The level-`0` representatives (a bubble or a `δ₃` element), by vertex number. -/
def repsCZ : (N : ℕ) → List (RepC N)
  | 7 => (List.finRange 12).map fun i => ⟨kB, repB i, 0⟩
  | 6 => (List.finRange 12).flatMap (fun i => [⟨kD, repD i 0, 0⟩, ⟨kD, repD i 1, 0⟩]) ++
      [⟨kCB0, repCB0, 0⟩, ⟨kCB1, repCB1, 0⟩]
  | 5 => [⟨kCB2, repCB2, 0⟩, ⟨kCB3, repCB3, 0⟩, ⟨kCB4, repCB4, 0⟩, ⟨kCD0, repCD0 0, 0⟩,
      ⟨kCD0, repCD0 1, 0⟩, ⟨kCD1, repCD1 0, 0⟩, ⟨kCD1, repCD1 1, 0⟩]
  | 4 => [⟨kCD2, repCD2 0, 0⟩, ⟨kCD2, repCD2 1, 0⟩, ⟨kCD3, repCD3 0, 0⟩, ⟨kCD3, repCD3 1, 0⟩,
      ⟨kCD4, repCD4 0, 0⟩, ⟨kCD4, repCD4 1, 0⟩]
  | _ => []

/-- The level-`1` representatives (the VP-share counterterm graphs), by vertex number. -/
def repsCS : (N : ℕ) → List (RepC N)
  | 4 => [⟨kS0, repS0, gOne _⟩, ⟨kS1, repS1, gOne _⟩]
  | 3 => [⟨kS2, repS2, gOne _⟩, ⟨kS3, repS3, gOne _⟩, ⟨kS4, repS4, gOne _⟩]
  | _ => []

/-- The set (c) representatives with `N` vertices. -/
def repsC (N : ℕ) : List (RepC N) := repsCZ N ++ repsCS N

end QED.ChainProof.SetCLink

end
