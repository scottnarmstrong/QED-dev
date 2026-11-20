/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CSplit
public import QED.Frozen.Graded.ContractionAmplitude

/-!
# (X₁) piece C: the amplitude as a sum of index terms, and sums over a split

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

* `vtxOf`, `bodyOf`, `lineFac`, `IndOf`: the vertex factor, the product of the vertex and line
  factors, and
  the external index condition of (G₃); `contractionAmplitude_eq_sum` writes (G₃) as a sum over
  the index assignments `IdxAsg κ` of `[IndOf] · bodyOf`; `bodyOf_eq` writes the line factors
  as one product over the lines.
* `vtxOf_split_left`, `_right` (`rfl`): the vertex factor of `κ` at a vertex of a piece is that
  of the piece, with the flavouring `flL`/`flR`, the grading `gradL`/`gradR` and composed indices.
* `joinF`, `joinT`, `sum_joinT`: an index assignment of `κ` is a pair of assignments of the
  pieces.
* `collapse_left`, `collapse_right`: the sum over a joining index of an indicator.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂)
open QED.Graded

variable {N N₁ N₂ : ℕ} {F : Type}

/-- The vertex factor (V₁₉) of vertex `t` with the coefficients and mass of (G₃). -/
noncomputable def vtxOf (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (κ : Fin N → Wick.VertexKind) (φ : Flavoring F κ) (g : Grading κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) :
    ℂ :=
  let lv : ℕ := if h : κ t = .gauge then 0 else g ⟨t, h⟩
  let fl : F := if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩
  let c : ℝ := P.e ^ (2 * (lv + 1))
  Wick.vertexFactor P.e (c * D.d₁ fl lv) (c * D.d₂ fl lv) (c * D.dm fl lv)
    (c * D.d₃ lv) (Φ.mass fl) α β lor kψ kA t

/-- The product of the vertex and line factors of (G₃) at fixed indices. -/
noncomputable def bodyOf (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    {nf nA : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring F κ)
    (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : ℂ :=
  (∏ t, vtxOf P Φ D κ φ g α β lor (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t) *
    (∏ f : FermionLine C, (1 / I) *
      QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k (.inl f)) (β f.1) (α f.tail)) *
    ∏ g' : PhotonLine C, (1 / I) *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g')) (lor g'.1) (lor g'.head)

/-- The factor of an internal line in (G₃). -/
noncomputable def lineFac (P : Params) (Φ : Lepton.Flavors F) {nf nA : ℕ}
    {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} (φ : Flavoring F κ)
    (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : Line C → ℂ :=
  Sum.elim (fun f => (1 / I) *
      QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k (.inl f)) (β f.1) (α f.tail))
    fun g' => (1 / I) *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g')) (lor g'.1) (lor g'.head)

theorem bodyOf_eq (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    {nf nA : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring F κ)
    (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) :
    bodyOf P Φ D C φ g pIn kIn k α β lor =
      (∏ t, vtxOf P Φ D κ φ g α β lor (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t) *
        ∏ l, lineFac P Φ φ k α β lor l := by
  unfold bodyOf lineFac
  rw [mul_assoc, Fintype.prod_sum_type (α₁ := FermionLine C) (α₂ := PhotonLine C)]
  rfl

/-- The external index condition of (G₃). -/
def IndOf {nf nA : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : Prop :=
  (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
    (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
    (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j)

/-- The index assignments of the fields of `κ`: `Ψ̄` indices, `Ψ` indices, Lorentz indices. -/
abbrev IdxAsg (κ : Fin N → Wick.VertexKind) : Type :=
  (Wick.FermionVertex κ → Fin 4) × (Wick.FermionVertex κ → Fin 4) × (Wick.PhotonSlot κ → Fin 4)

open scoped Classical in
/-- **(G₃) as a sum of index terms.** -/
theorem contractionAmplitude_eq_sum (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    {nf nA : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring F κ)
    (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ =
      ∑ v : IdxAsg κ, (if IndOf C αOut βIn μ v.1 v.2.1 v.2.2 then 1 else 0) *
        bodyOf P Φ D C φ g pIn kIn k v.1 v.2.1 v.2.2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  unfold contractionAmplitude
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  unfold bodyOf vtxOf IndOf
  congr 1
  split_ifs <;> rfl

/-! ### The vertex factors of the pieces -/

variable (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
  (κ : Fin N → Wick.VertexKind) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)

/-- The flavouring of the left piece. -/
def flL (φ : Flavoring F κ) : Flavoring F (leftKinds κ e) := fun t => φ (fvSplit κ e (.inl t))

/-- The flavouring of the right piece. -/
def flR (φ : Flavoring F κ) : Flavoring F (rightKinds κ e) := fun t => φ (fvSplit κ e (.inr t))

theorem vtxOf_split_left (φ : Flavoring F κ) (g : Grading κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N₁) :
    vtxOf P Φ D κ φ g α β lor kψ kA (e (.inl t)) =
      vtxOf P Φ D (leftKinds κ e) (flL κ e φ) (gradL κ e g)
        (fun s => α (fvSplit κ e (.inl s))) (fun s => β (fvSplit κ e (.inl s)))
        (fun a => lor (psSplit κ e (.inl a))) (fun s => kψ (fvSplit κ e (.inl s)))
        (fun a => kA (psSplit κ e (.inl a))) t := rfl

theorem vtxOf_split_right (φ : Flavoring F κ) (g : Grading κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N₂) :
    vtxOf P Φ D κ φ g α β lor kψ kA (e (.inr t)) =
      vtxOf P Φ D (rightKinds κ e) (flR κ e φ) (gradR κ e g)
        (fun s => α (fvSplit κ e (.inr s))) (fun s => β (fvSplit κ e (.inr s)))
        (fun a => lor (psSplit κ e (.inr a))) (fun s => kψ (fvSplit κ e (.inr s)))
        (fun a => kA (psSplit κ e (.inr a))) t := rfl

/-! ### Index assignments of a split -/

/-- The function on `X` with values `x₁`, `x₂` on the two summands. -/
def joinF {X₁ X₂ X Y : Type*} (E : X₁ ⊕ X₂ ≃ X) (x₁ : X₁ → Y) (x₂ : X₂ → Y) : X → Y :=
  fun t => Sum.elim x₁ x₂ (E.symm t)

@[simp] theorem joinF_inl {X₁ X₂ X Y : Type*} (E : X₁ ⊕ X₂ ≃ X) (x₁ : X₁ → Y) (x₂ : X₂ → Y)
    (t : X₁) : joinF E x₁ x₂ (E (.inl t)) = x₁ t := by
  simp [joinF]

@[simp] theorem joinF_inr {X₁ X₂ X Y : Type*} (E : X₁ ⊕ X₂ ≃ X) (x₁ : X₁ → Y) (x₂ : X₂ → Y)
    (t : X₂) : joinF E x₁ x₂ (E (.inr t)) = x₂ t := by
  simp [joinF]

/-- The index assignment of `κ` with given assignments of the pieces. -/
def joinT (v₁ : IdxAsg (leftKinds κ e)) (v₂ : IdxAsg (rightKinds κ e)) : IdxAsg κ :=
  (joinF (fvSplit κ e) v₁.1 v₂.1, joinF (fvSplit κ e) v₁.2.1 v₂.2.1,
    joinF (psSplit κ e) v₁.2.2 v₂.2.2)

/-- Index assignments of `κ` are pairs of index assignments of the pieces. -/
def joinTEquiv : IdxAsg (leftKinds κ e) × IdxAsg (rightKinds κ e) ≃ IdxAsg κ where
  toFun v := joinT κ e v.1 v.2
  invFun v := ((fun s => v.1 (fvSplit κ e (.inl s)), fun s => v.2.1 (fvSplit κ e (.inl s)),
      fun a => v.2.2 (psSplit κ e (.inl a))), (fun s => v.1 (fvSplit κ e (.inr s)),
      fun s => v.2.1 (fvSplit κ e (.inr s)), fun a => v.2.2 (psSplit κ e (.inr a))))
  left_inv v := by simp only [joinT, joinF_inl, joinF_inr]
  right_inv v := by
    obtain ⟨α, β, lor⟩ := v
    simp only [joinT, Prod.mk.injEq]
    refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
    · obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
      rcases x with x | x <;> simp only [joinF_inl, joinF_inr]
    · obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
      rcases x with x | x <;> simp only [joinF_inl, joinF_inr]
    · obtain ⟨x, rfl⟩ := (psSplit κ e).surjective t
      rcases x with x | x <;> simp only [joinF_inl, joinF_inr]

theorem sum_joinT {M : Type*} [AddCommMonoid M] (G : IdxAsg κ → M) :
    ∑ v, G v = ∑ v₁, ∑ v₂, G (joinT κ e v₁ v₂) := by
  rw [← (joinTEquiv κ e).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ### Sums over a joining index -/

theorem collapse_left {V : Type*} [Fintype V] (p : V → Fin 4) (Fv : V → ℂ) (Z : Fin 4 → ℂ) :
    ∑ γ, (∑ v, if p v = γ then Fv v else 0) * Z γ = ∑ v, Fv v * Z (p v) := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem collapse_right {V : Type*} [Fintype V] (q : V → Fin 4) (Fv : V → ℂ) (Z : Fin 4 → ℂ) :
    ∑ δ, Z δ * (∑ v, if q v = δ then Fv v else 0) = ∑ v, Z (q v) * Fv v := by
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

end QED.GradedProof.X1C

end
