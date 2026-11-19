/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumReps
public import QED.TwoLoop.CountertermInsertionD3

/-!
# The `δ₃`–`δ₃` classes of set (b): explicit values

Helper level, Phase 5 Stage 1a (O3-6 for the one-loop classes). The representative
`QED.ChainProof.Enum.repDD s₀ s₁` (`s₀`, `s₁` the fields of the two `photonCt` vertices `3`, `4`
facing the vertex `a = 2`) is a one-loop vertex graph: the open line `0 → 1 → 2` (external photon
at `1`) and the photon chain `2 — 3ₛ₀`, `3ₛ₀' — 4ₛ₁`, `4ₛ₁' — 0`. For all four field pairings at
once:

* the lines, ends, chord (the line `0 → 1`) and a conserved routing (`decide +kernel`,
  `ring`): the loop momentum `ℓ` runs on the line `0 → 1`, `ℓ + k` on `1 → 2`, `ℓ - p` on the photon
  lines from `2` and between the `photonCt` vertices, `p - ℓ` on the photon line from `0`;
* `dd_amplitude`: the amplitude (T₇) at arbitrary line momenta;
* **`contractionValue₂_repDD`**: the value (T₁₀) is the energy-first integral of the one-loop
  vertex chain with the double insertion `ddInsertion = (1/i)² Δ̃ V Δ̃ V Δ̃` (`V` the `photonCt`
  factor, half the counterterm rule), at every `ε`, under momentum conservation, with no
  integrability hypothesis. It does not depend on the field pairing.
-/

@[expose] public section

namespace QED.ChainProof.HCLimit

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel
open QED.TwoLoop.Insertion QED.ChainProof.Enum Complex

/-! ### Lines and routing -/

/-- The fermion line `0 → 1`. -/
def ddf1 (s₀ s₁ : Fin 2) : FermionLine (repDD s₀ s₁) :=
  ⟨fv kDD 1, by revert s₀ s₁; decide +kernel⟩
/-- The fermion line `1 → 2`. -/
def ddf2 (s₀ s₁ : Fin 2) : FermionLine (repDD s₀ s₁) :=
  ⟨fv kDD 2, by revert s₀ s₁; decide +kernel⟩
/-- The photon line from vertex `2` to the field `s₀` of vertex `3`. -/
def ddA (s₀ s₁ : Fin 2) : PhotonLine (repDD s₀ s₁) :=
  ⟨pg kDD 2, by revert s₀ s₁; decide +kernel⟩
/-- The photon line from the field `s₀'` of vertex `3` to the field `s₁` of vertex `4`. -/
def ddM (s₀ s₁ : Fin 2) : PhotonLine (repDD s₀ s₁) :=
  ⟨pc kDD 3 s₀.rev, by revert s₀ s₁; decide +kernel⟩
/-- The photon line from vertex `0` to the field `s₁'` of vertex `4`. -/
def ddC (s₀ s₁ : Fin 2) : PhotonLine (repDD s₀ s₁) :=
  ⟨pg kDD 0, by revert s₀ s₁; decide +kernel⟩

theorem dd_fermionLine_cases : ∀ s₀ s₁ (f : FermionLine (repDD s₀ s₁)),
    f = ddf1 s₀ s₁ ∨ f = ddf2 s₀ s₁ := by
  decide +kernel

theorem dd_photonLine_cases : ∀ s₀ s₁ (g : PhotonLine (repDD s₀ s₁)),
    g = ddA s₀ s₁ ∨ g = ddM s₀ s₁ ∨ g = ddC s₀ s₁ := by
  decide +kernel

theorem dd_line_cases : ∀ s₀ s₁ (f : Line (repDD s₀ s₁)),
    f = .inl (ddf1 s₀ s₁) ∨ f = .inl (ddf2 s₀ s₁) ∨ f = .inr (ddA s₀ s₁) ∨
      f = .inr (ddM s₀ s₁) ∨ f = .inr (ddC s₀ s₁) := by
  rintro s₀ s₁ (f | g)
  · rcases dd_fermionLine_cases s₀ s₁ f with rfl | rfl <;> simp
  · rcases dd_photonLine_cases s₀ s₁ g with rfl | rfl | rfl <;> simp

theorem dd_isChord_iff : ∀ s₀ s₁ (g : Line (repDD s₀ s₁)), IsChord g ↔ g = .inl (ddf1 s₀ s₁) := by
  decide +kernel

theorem dd_ends : ∀ s₀ s₁, (Line.ends (.inl (ddf1 s₀ s₁) : Line (repDD s₀ s₁))) = (0, 1) ∧
    (Line.ends (.inl (ddf2 s₀ s₁) : Line (repDD s₀ s₁))) = (1, 2) ∧
    (Line.ends (.inr (ddA s₀ s₁) : Line (repDD s₀ s₁))) = (2, 3) ∧
    (Line.ends (.inr (ddM s₀ s₁) : Line (repDD s₀ s₁))) = (3, 4) ∧
    (Line.ends (.inr (ddC s₀ s₁) : Line (repDD s₀ s₁))) = (0, 4) := by
  decide +kernel

theorem dd_tails : ∀ s₀ s₁, (ddf1 s₀ s₁).tail = fv kDD 0 ∧ (ddf2 s₀ s₁).tail = fv kDD 1 ∧
    (ddA s₀ s₁).head = pc kDD 3 s₀ ∧ (ddM s₀ s₁).head = pc kDD 4 s₁ ∧
    (ddC s₀ s₁).head = pc kDD 4 s₁.rev := by
  decide +kernel

theorem dd_ext : ∀ s₀ s₁ (v : Fin 5),
    ((∃ t : Wick.FermionVertex kDD, t.1 = v ∧ (repDD s₀ s₁).1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kDD, a.1 = v ∧ (repDD s₀ s₁).1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kDD, t.1 = v ∧ (repDD s₀ s₁).1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  decide +kernel

theorem dd_sameCycle : ∀ s₀ s₁ (x : Fin 1 ⊕ Wick.FermionVertex kDD),
    ∃ i : Fin 4, ((repDD s₀ s₁).1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem dd_sameCycle' (s₀ s₁ : Fin 2) (x : Fin 1 ⊕ Wick.FermionVertex kDD) :
    Equiv.Perm.SameCycle (repDD s₀ s₁).1.1 x (.inl 0) :=
  sameCycle_of_pow (n := 4) (dd_sameCycle s₀ s₁) x

theorem sum_eq_of_five {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M]
    {a b c d e : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) (g : X → M) :
    ∑ x, g x = g a + g b + g c + g d + g e := by
  have : (Finset.univ : Finset X) = {a, b, c, d, e} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_insert (by simp [hab, hac, had, hae]),
    Finset.sum_insert (by simp [hbc, hbd, hbe]), Finset.sum_insert (by simp [hcd, hce]),
    Finset.sum_pair hde]
  abel

/-- The routing of `repDD s₀ s₁`: `ℓ` on `0 → 1`, `ℓ + k` on `1 → 2`, `ℓ - p` on the photon lines
from `2` and from `3`, `p - ℓ` on the photon line from `0`. -/
def ddMom (s₀ s₁ : Fin 2) (p k ℓ : Fin 4 → ℝ) (f : Line (repDD s₀ s₁)) : Fin 4 → ℝ :=
  if f = .inl (ddf1 s₀ s₁) then ℓ else if f = .inl (ddf2 s₀ s₁) then ℓ + k
    else if f = .inr (ddC s₀ s₁) then p - ℓ else ℓ - p

theorem dd_ne : ∀ s₀ s₁, (.inl (ddf1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inl (ddf2 s₀ s₁) ∧
    (.inl (ddf1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddA s₀ s₁) ∧
    (.inl (ddf1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddM s₀ s₁) ∧
    (.inl (ddf1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddC s₀ s₁) ∧
    (.inl (ddf2 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddA s₀ s₁) ∧
    (.inl (ddf2 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddM s₀ s₁) ∧
    (.inl (ddf2 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddC s₀ s₁) ∧
    (.inr (ddA s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddM s₀ s₁) ∧
    (.inr (ddA s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddC s₀ s₁) ∧
    (.inr (ddM s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddC s₀ s₁) := by
  intro s₀ s₁
  have hf : ∀ {f g : FermionLine (repDD s₀ s₁)}, f.1.1 ≠ g.1.1 →
      (.inl f : Line (repDD s₀ s₁)) ≠ .inl g := fun h e => h (by rw [Sum.inl.inj e])
  have hg : ∀ {f g : PhotonLine (repDD s₀ s₁)}, f.1.1 ≠ g.1.1 →
      (.inr f : Line (repDD s₀ s₁)) ≠ .inr g := fun h e => h (by rw [Sum.inr.inj e])
  exact ⟨hf fun h => (by decide : (1 : Fin 5) ≠ 2) h, Sum.inl_ne_inr, Sum.inl_ne_inr,
    Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr,
    hg fun h => (by decide : (2 : Fin 5) ≠ 3) h,
    hg fun h => (by decide : (2 : Fin 5) ≠ 0) h,
    hg fun h => (by decide : (3 : Fin 5) ≠ 0) h⟩

theorem ddMom_apply (s₀ s₁ : Fin 2) (p k ℓ : Fin 4 → ℝ) :
    ddMom s₀ s₁ p k ℓ (.inl (ddf1 s₀ s₁)) = ℓ ∧ ddMom s₀ s₁ p k ℓ (.inl (ddf2 s₀ s₁)) = ℓ + k ∧
    ddMom s₀ s₁ p k ℓ (.inr (ddA s₀ s₁)) = ℓ - p ∧ ddMom s₀ s₁ p k ℓ (.inr (ddM s₀ s₁)) = ℓ - p ∧
    ddMom s₀ s₁ p k ℓ (.inr (ddC s₀ s₁)) = p - ℓ := by
  obtain ⟨n12, n1A, n1M, n1C, n2A, n2M, n2C, nAM, nAC, nMC⟩ := dd_ne s₀ s₁
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · rw [ddMom, ite_eq_right n12.symm, ite_eq_left rfl]
  · rw [ddMom, ite_eq_right n1A.symm, ite_eq_right n2A.symm, ite_eq_right nAC]
  · rw [ddMom, ite_eq_right n1M.symm, ite_eq_right n2M.symm, ite_eq_right nMC]
  · rw [ddMom, ite_eq_right n1C.symm, ite_eq_right n2C.symm, ite_eq_left rfl]

theorem dd_isConserved (s₀ s₁ : Fin 2) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 4 → ℝ) :
    IsConserved (repDD s₀ s₁) pOut pIn kIn (ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := dd_ends s₀ s₁
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ (pIn 0) (kIn 0) ℓ
  obtain ⟨n12, n1A, n1M, n1C, n2A, n2M, n2C, nAM, nAC, nMC⟩ := dd_ne s₀ s₁
  intro v
  rw [inflow, sum_eq_of_five n12 n1A n1M n1C n2A n2M n2C nAM nAC nMC (dd_line_cases s₀ s₁),
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := dd_ext s₀ s₁ v
  simp only [e1, e2, e3, e4, e5, x1, x2, x3, m1, m2, m3, m4, m5]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

/-! ### The amplitude -/

/-- A sum over the functions on a type covered by seven distinct elements. -/
theorem sum_pi_seven {X R M : Type*} [Fintype X] [DecidableEq X] [Fintype R] [AddCommMonoid M]
    {x₁ x₂ x₃ x₄ x₅ x₆ x₇ : X}
    (h : [x₁, x₂, x₃, x₄, x₅, x₆, x₇].Nodup)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = x₄ ∨ x = x₅ ∨ x = x₆ ∨ x = x₇)
    (g : (X → R) → M) :
    ∑ f, g f = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f', ∑ g',
      g (fun t => if t = x₁ then a else if t = x₂ then b else if t = x₃ then c else
        if t = x₄ then d else if t = x₅ then e else if t = x₆ then f' else g') := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h12, h13, h14, h15, h16, h17⟩, ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩,
    ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67, -⟩ := h
  let E : (X → R) ≃ R × R × R × R × R × R × R :=
    { toFun := fun f => (f x₁, f x₂, f x₃, f x₄, f x₅, f x₆, f x₇)
      invFun := fun q t =>
        if t = x₁ then q.1 else if t = x₂ then q.2.1 else if t = x₃ then q.2.2.1 else
          if t = x₄ then q.2.2.2.1 else if t = x₅ then q.2.2.2.2.1 else
            if t = x₆ then q.2.2.2.2.2.1 else q.2.2.2.2.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17,
            Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27, Ne.symm h34,
            Ne.symm h35, Ne.symm h36, Ne.symm h37, Ne.symm h45, Ne.symm h46, Ne.symm h47,
            Ne.symm h56, Ne.symm h57, Ne.symm h67]
      right_inv := fun q => by
        simp [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17,
          Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27, Ne.symm h34,
          Ne.symm h35, Ne.symm h36, Ne.symm h37, Ne.symm h45, Ne.symm h46, Ne.symm h47,
          Ne.symm h56, Ne.symm h57, Ne.symm h67] }
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

theorem dd_cond (s₀ s₁ : Fin 2) (α β : Wick.FermionVertex kDD → Fin 4)
    (lor : Wick.PhotonSlot kDD → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repDD s₀ s₁).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repDD s₀ s₁).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repDD s₀ s₁).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kDD 1) = μ 0 ∧ (α (fv kDD 2) = αOut 0 ∧ β (fv kDD 0) = βIn 0) := by
  have h1 : ∀ t, (repDD s₀ s₁).1.1 (.inl 0) = .inr t ↔ t = fv kDD 2 := by
    revert s₀ s₁; decide +kernel
  have h2 : ∀ t, (repDD s₀ s₁).1.1 (.inr t) = .inl 0 ↔ t = fv kDD 0 := by
    revert s₀ s₁; decide +kernel
  have h3 : ∀ a, (repDD s₀ s₁).1.2 (.inl 0) = .inr a ↔ a = pg kDD 1 := by
    revert s₀ s₁; decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- The `photonCt` factor is symmetric, so its fields may be read in either order. -/
theorem photonCtFactor_slots (δ₃ : ℝ) (k : Fin 4 → ℝ) (lor : Wick.PhotonSlot kDD → Fin 4)
    (t : Fin 5) (ht : (kDD t).photonSlots = 2) (h0 : 0 < (kDD t).photonSlots)
    (h1 : 1 < (kDD t).photonSlots) (s : Fin 2) :
    photonCtFactor δ₃ k (lor ⟨t, ⟨0, h0⟩⟩) (lor ⟨t, ⟨1, h1⟩⟩) =
      photonCtFactor δ₃ k (lor (pc kDD t s ht)) (lor (pc kDD t s.rev ht)) := by
  fin_cases s
  · rfl
  · exact photonCtFactor_comm _ _ _ _

theorem dd_slots_nodup : ∀ s₀ s₁ : Fin 2,
    [pg kDD 0, pg kDD 1, pg kDD 2, pc kDD 4 s₁.rev, pc kDD 4 s₁, pc kDD 3 s₀.rev,
      pc kDD 3 s₀].Nodup := by
  decide +kernel

theorem dd_slots_cover : ∀ (s₀ s₁ : Fin 2) (x : Wick.PhotonSlot kDD),
    x = pg kDD 0 ∨ x = pg kDD 1 ∨ x = pg kDD 2 ∨ x = pc kDD 4 s₁.rev ∨ x = pc kDD 4 s₁ ∨
      x = pc kDD 3 s₀.rev ∨ x = pc kDD 3 s₀ := by
  decide +kernel

theorem dd_vals : ∀ s₀ s₁, (ddf1 s₀ s₁).1 = fv kDD 1 ∧ (ddf2 s₀ s₁).1 = fv kDD 2 ∧
    (ddA s₀ s₁).1 = pg kDD 2 ∧ (ddM s₀ s₁).1 = pc kDD 3 s₀.rev ∧ (ddC s₀ s₁).1 = pg kDD 0 :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩


/-- The double `photonCt` insertion `(1/i)² ∑ Δ̃_{νx} V^{xy} Δ̃_{yz} V^{zw} Δ̃_{wρ}`, `V` the
`photonCt` factor of one field pairing. -/
noncomputable def ddInsertion (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  (1 / I) ^ 2 * ∑ x, ∑ y, ∑ z, ∑ w, QED.OneLoop.photonPropagator mγ Λ ε k ν x *
    photonCtFactor δ₃ k x y * QED.OneLoop.photonPropagator mγ Λ ε k y z *
    photonCtFactor δ₃ k z w * QED.OneLoop.photonPropagator mγ Λ ε k w ρ

theorem dd_fne (s₀ s₁ : Fin 2) : ddf1 s₀ s₁ ≠ ddf2 s₀ s₁ := fun h =>
  (by decide : (1 : Fin 5) ≠ 2) (congrArg (fun f : FermionLine (repDD s₀ s₁) => f.1.1) h)

theorem dd_gne (s₀ s₁ : Fin 2) : ddA s₀ s₁ ≠ ddM s₀ s₁ ∧ ddA s₀ s₁ ≠ ddC s₀ s₁ ∧
    ddM s₀ s₁ ≠ ddC s₀ s₁ :=
  ⟨fun h => (by decide : (2 : Fin 5) ≠ 3) (congrArg (fun f : PhotonLine (repDD s₀ s₁) => f.1.1) h),
    fun h => (by decide : (2 : Fin 5) ≠ 0) (congrArg (fun f : PhotonLine (repDD s₀ s₁) => f.1.1) h),
    fun h => (by decide : (3 : Fin 5) ≠ 0) (congrArg (fun f : PhotonLine (repDD s₀ s₁) => f.1.1) h)⟩

/-- **The amplitude of `repDD s₀ s₁`** at arbitrary line momenta `k`: the one-loop vertex chain
contracted with the photon chain `Δ̃(k_C) V(k₄) Δ̃(k_M) V(k₃) Δ̃(k_A)`, with `kₜ` the momentum
entering the field `0` of the `photonCt` vertex `t` (T₆). -/
theorem dd_amplitude (P : Params) (s₀ s₁ : Fin 2) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repDD s₀ s₁) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repDD s₀ s₁) (zeroFlavoring kDD) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, ((1 / I) ^ 2 * ∑ x, ∑ y, ∑ z, ∑ w,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr (ddC s₀ s₁))) ν x *
            photonCtFactor P.δ₃ (photonMomentum₂ (repDD s₀ s₁) kIn k ⟨4, ⟨0, by decide⟩⟩) y x *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr (ddM s₀ s₁))) z y *
            photonCtFactor P.δ₃ (photonMomentum₂ (repDD s₀ s₁) kIn k ⟨3, ⟨0, by decide⟩⟩) w z *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr (ddA s₀ s₁))) ρ w) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl (ddf2 s₀ s₁))) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl (ddf1 s₀ s₁))) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, hA, hM, hC⟩ := dd_tails s₀ s₁
  obtain ⟨v1, v2, vA, vM, vC⟩ := dd_vals s₀ s₁
  obtain ⟨nAM, nAC, nMC⟩ := dd_gne s₀ s₁
  set k3 := photonMomentum₂ (repDD s₀ s₁) kIn k ⟨3, ⟨0, by decide⟩⟩
  set k4 := photonMomentum₂ (repDD s₀ s₁) kIn k ⟨4, ⟨0, by decide⟩⟩
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kDD → Fin 4, ∑ β : Wick.FermionVertex kDD → Fin 4,
      ∑ lor : Wick.PhotonSlot kDD → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kDD → Fin 4,
    (if lor (pg kDD 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ((1 / I) ^ 2 * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr (ddC s₀ s₁)))
            (lor (pg kDD 0)) (lor (pc kDD 4 s₁.rev)) *
          photonCtFactor P.δ₃ k4 (lor (pc kDD 4 s₁)) (lor (pc kDD 4 s₁.rev)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr (ddM s₀ s₁)))
            (lor (pc kDD 3 s₀.rev)) (lor (pc kDD 4 s₁)) *
          photonCtFactor P.δ₃ k3 (lor (pc kDD 3 s₀)) (lor (pc kDD 3 s₀.rev)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr (ddA s₀ s₁)))
            (lor (pg kDD 2)) (lor (pc kDD 3 s₀)))) *
        (Dirac.gamma (lor (pg kDD 2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl (ddf2 s₀ s₁))) *
          Dirac.gamma (lor (pg kDD 1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl (ddf1 s₀ s₁))) *
          Dirac.gamma (lor (pg kDD 0))) (αOut 0) (βIn 0)) = _)
  · rw [← photonCtFactor_slots P.δ₃ k3 lor 3 rfl (by decide) (by decide) s₀,
      ← photonCtFactor_slots P.δ₃ k4 lor 4 rfl (by decide) (by decide) s₁]
    rw [← sum_spinor_chain3 (x₁ := fv kDD 2) (x₂ := fv kDD 1) (x₃ := fv kDD 0)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [dd_cond, Fin.prod_univ_five,
      prod_eq_of_two (dd_fne s₀ s₁) (dd_fermionLine_cases s₀ s₁),
      prod_eq_of_three nAM nAC nMC (dd_photonLine_cases s₀ s₁),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kDD 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kDD 1 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kDD 2 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show kDD 3 = .photonCt from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show kDD 4 = .photonCt from rfl),
      t1, t2, hA, hM, hC, v1, v2, vA, vM, vC, ite_and_eq_mul]
    simp only [fv, pg, zeroFlavoring, Params.mass, Matrix.cons_val_zero, photonCtFactor]
    ring
  · have hnd := dd_slots_nodup s₀ s₁
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    obtain ⟨⟨n01, n02, n03, n04, n05, n06⟩, ⟨n12, n13, n14, n15, n16⟩, ⟨n23, n24, n25, n26⟩,
      ⟨n34, n35, n36⟩, ⟨n45, n46⟩, n56, -⟩ := hnd
    rw [sum_pi_seven (dd_slots_nodup s₀ s₁) (dd_slots_cover s₀ s₁)]
    simp only [ite_true, Ne.symm n01, Ne.symm n02, Ne.symm n03, Ne.symm n04, Ne.symm n05,
      Ne.symm n06, Ne.symm n12, Ne.symm n13, Ne.symm n14, Ne.symm n15, Ne.symm n16, Ne.symm n23,
      Ne.symm n24, Ne.symm n25, Ne.symm n26, Ne.symm n34, Ne.symm n35, Ne.symm n36, Ne.symm n45,
      Ne.symm n46, Ne.symm n56, ite_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

/-- The momentum entering the field `0` of the `photonCt` vertex `3` is `±(ℓ - p)`, so the
`photonCt` factor there is that at `ℓ - p`. -/
theorem dd_ct3 (δ₃ : ℝ) (s₀ s₁ : Fin 2) (kIn : Fin 1 → Fin 4 → ℝ) (p k ℓ : Fin 4 → ℝ)
    (a b : Fin 4) :
    photonCtFactor δ₃ (photonMomentum₂ (repDD s₀ s₁) kIn (ddMom s₀ s₁ p k ℓ)
      ⟨3, ⟨0, by decide⟩⟩) a b = photonCtFactor δ₃ (ℓ - p) a b := by
  have hext : ¬ (repDD s₀ s₁).1.2 (.inl 0) = .inr ⟨3, ⟨0, by decide⟩⟩ := by
    revert s₀ s₁; decide +kernel
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ p k ℓ
  obtain ⟨-, -, hA, hM, hC⟩ := dd_tails s₀ s₁
  obtain ⟨-, -, vA, vM, vC⟩ := dd_vals s₀ s₁
  obtain ⟨nAM, nAC, nMC⟩ := dd_gne s₀ s₁
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_three nAM nAC nMC (dd_photonLine_cases s₀ s₁),
    hA, hM, hC, vA, vM, vC, m3, m4, m5]
  fin_cases s₀ <;> fin_cases s₁ <;> simp [pc, pg, Fin.ext_iff] <;>
    rw [← neg_sub ℓ p, photonCtFactor_neg]

/-- The same at the `photonCt` vertex `4`. -/
theorem dd_ct4 (δ₃ : ℝ) (s₀ s₁ : Fin 2) (kIn : Fin 1 → Fin 4 → ℝ) (p k ℓ : Fin 4 → ℝ)
    (a b : Fin 4) :
    photonCtFactor δ₃ (photonMomentum₂ (repDD s₀ s₁) kIn (ddMom s₀ s₁ p k ℓ)
      ⟨4, ⟨0, by decide⟩⟩) a b = photonCtFactor δ₃ (ℓ - p) a b := by
  have hext : ¬ (repDD s₀ s₁).1.2 (.inl 0) = .inr ⟨4, ⟨0, by decide⟩⟩ := by
    revert s₀ s₁; decide +kernel
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ p k ℓ
  obtain ⟨-, -, hA, hM, hC⟩ := dd_tails s₀ s₁
  obtain ⟨-, -, vA, vM, vC⟩ := dd_vals s₀ s₁
  obtain ⟨nAM, nAC, nMC⟩ := dd_gne s₀ s₁
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_three nAM nAC nMC (dd_photonLine_cases s₀ s₁),
    hA, hM, hC, vA, vM, vC, m3, m4, m5]
  fin_cases s₀ <;> fin_cases s₁ <;> simp [pc, pg, Fin.ext_iff] <;>
    rw [← neg_sub ℓ p, photonCtFactor_neg]

/-- **The value of the `δ₃`–`δ₃` class** (any field pairing): under momentum conservation, the
energy-first integral of the one-loop vertex chain whose photon factor is the double `photonCt`
insertion `ddInsertion`, at every `ε`. -/
theorem contractionValue₂_repDD (P : Params) (s₀ s₁ : Fin 2) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P (repDD s₀ s₁) pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + ℓ))
          (ddInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P (dd_isChord_iff s₀ s₁)
    (ddMom s₀ s₁ (pIn 0) (kIn 0)) (dd_isConserved s₀ s₁ hmom)
    (fun ℓ => (ddMom_apply s₀ s₁ _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (dd_sameCycle' s₀ s₁), dd_amplitude]
  simp only [dd_ct3, dd_ct4]
  rw [m1, m2, m3, m4, m5, vertexChain, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, ddInsertion]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
  rw [photonCtFactor_comm _ _ y x, photonPropagator_comm' _ _ _ _ z y,
    photonCtFactor_comm _ _ w z, photonPropagator_comm' _ _ _ _ ρ w]
  ring

end QED.ChainProof.HCLimit

end
