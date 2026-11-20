/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0ClosedTerm
public import QED.TwoLoop.RelabelCountertermValue
public import QED.Algebra.ChargeConjugation

/-!
# (X₁) piece C: the tadpole sign

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C4. Let `T` be a set of vertices of a contraction `C` with one
external fermion pair (a *tadpole side*, `TadSide`): the fermion pairing maps the fermion fields
of `T` to fermion fields of `T` (so no external fermion is attached to `T` and every fermion line
at `T` stays in `T`), no external photon is attached to `T`, and `T` has an odd number of `gauge`
and `gaugeCt` vertices. Reflect the momenta of the lines whose head lies in `T` (`reflMom`), and
assume every line crossing the boundary of `T` carries momentum `0`. Then the amplitude (G₃)
changes sign (`contractionAmplitude_reflMom`).

## Proof

In the Weyl representation `γ⁵ = diag(-1, -1, 1, 1)` with diagonal `sgn`, the propagator entry
satisfies `S̃(-k)_{ab} = sgn a sgn b S̃(k)_{ab}` and so does the `fermionCt` entry in its momentum,
while `γ^μ_{ab} sgn a sgn b = -γ^μ_{ab}` and the photon factors are even. Every spinor index of a
vertex of `T` occurs once at its vertex and once on a line of `T`, so the signs `sgn` cancel
(`QED.GradedProof.X0.prod_sgn_closed`) and the term picks up `(-1)` per `gauge` or `gaugeCt` vertex
of `T`: an odd number. This is the γ⁵ argument that replaces the one-loop parity `ℓ ↦ -ℓ` of each
factor (which fails beyond one loop).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂)
open QED.TwoLoop.FurryIntegrable (sgn gamma_mul_sgn entry_mul_sgn)
open QED.TwoLoop.Bridge (gamma5_conj_slash gamma5_mul_gamma5)
open QED.GradedProof.X0 (isZ ZLine prod_sgn_closed prod_split_loopT isLoopT isLoopT_iff sgn_sq
  prod_ite_one_eq_subtype)

/-! ### Entry signs -/

theorem slash_mul_sgn (p : Fin 4 → ℝ) (a b : Fin 4) :
    Dirac.slash p a b * (sgn a * sgn b) = -Dirac.slash p a b := by
  have h := entry_mul_sgn (c := -1) (X := Dirac.slash p)
    (by rw [gamma5_conj_slash, neg_one_smul]) a b
  linear_combination h

theorem one_mul_sgn (a b : Fin 4) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) a b * (sgn a * sgn b) = (1 : Matrix (Fin 4) (Fin 4) ℂ) a b := by
  have h := entry_mul_sgn (c := 1) (X := 1)
    (by rw [Matrix.mul_one, gamma5_mul_gamma5, one_smul]) a b
  linear_combination h

theorem dot_neg_neg (k : Fin 4 → ℝ) : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by
  simp [Minkowski.dot]

theorem electronPropagator_neg_apply (M ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.electronPropagator M ε (-k) a b =
      sgn a * sgn b * QED.OneLoop.electronPropagator M ε k a b := by
  simp only [QED.OneLoop.electronPropagator, dot_neg_neg, QED.Dirac.slash_neg, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  linear_combination
    (-((((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * M)) * one_mul_sgn a b +
      (((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * slash_mul_sgn k a b

theorem photonPropagator_neg (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε (-k) μ ν = QED.OneLoop.photonPropagator mγ Λ ε k μ ν := by
  simp only [QED.OneLoop.photonPropagator, dot_neg_neg]

/-! ### Vertex factors -/

section Vertex

variable {N : ℕ} {κ : Fin N → Wick.VertexKind} (e δ₁ δ₂ δm δ₃ m : ℝ)
  (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
  (kψ kψ' : Wick.FermionVertex κ → Fin 4 → ℝ) (kA kA' : Wick.PhotonSlot κ → Fin 4 → ℝ)

/-- A `gauge` or `gaugeCt` factor is odd under the `γ⁵` signs (at any momenta). -/
theorem vertexFactor_gl_mul_sgn {s : Wick.FermionVertex κ}
    (h : κ s.1 = .gauge ∨ κ s.1 = .gaugeCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' s.1 * (sgn (α s) * sgn (β s)) =
      -Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA s.1 := by
  rcases h with h | h
  · rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ h,
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ h]
    linear_combination (I * e) * gamma_mul_sgn _ (α s) (β s)
  · rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ h,
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ h]
    linear_combination (I * ((δ₁ * e : ℝ) : ℂ)) * gamma_mul_sgn _ (α s) (β s)

/-- A `fermionCt` factor at the reflected fermion momentum, times the `γ⁵` signs. -/
theorem vertexFactor_fct_mul_sgn {s : Wick.FermionVertex κ} (h : κ s.1 = .fermionCt)
    (hψ : kψ' s = -kψ s) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' s.1 * (sgn (α s) * sgn (β s)) =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA s.1 := by
  obtain ⟨t, ht⟩ := s
  rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ h,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ h]
  have e1 : kψ' ⟨t, by simp [h]⟩ = -kψ ⟨t, by simp [h]⟩ := hψ
  rw [e1, QED.Dirac.slash_neg]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  linear_combination (I * (δ₂ : ℂ)) * slash_mul_sgn (kψ ⟨t, ht⟩) (α ⟨t, ht⟩) (β ⟨t, ht⟩) +
    (-I * ((δm * m : ℝ) : ℂ)) * one_mul_sgn (α ⟨t, ht⟩) (β ⟨t, ht⟩)

/-- A vertex factor depends only on the momentum of its fermion field and, up to sign, of its
photon fields. -/
theorem vertexFactor_congr_mom (t : Fin N) (hψ : ∀ s : Wick.FermionVertex κ, s.1 = t → kψ' s = kψ s)
    (hA : ∀ a : Wick.PhotonSlot κ, a.1 = t → kA' a = kA a ∨ kA' a = -kA a) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ' kA' t =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t := by
  rcases hk : κ t
  · rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ hk,
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ hk]
  · rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk,
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk]
  · rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk,
      QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk,
      hψ _ rfl]
  · rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ hk,
      QED.TwoLoop.Relabel.vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ hk]
    rcases hA ⟨t, ⟨0, by simp [hk, Wick.VertexKind.photonSlots]⟩⟩ rfl with h | h <;> rw [h]
    simp only [dot_neg_neg, Pi.neg_apply, neg_mul_neg]

end Vertex

/-! ### The reflected line momenta -/

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 nA κ}
  (T : Fin N → Prop) [DecidablePred T]

/-- The line momenta reflected on the lines whose head lies in `T`. -/
def reflMom (k : Line C → Fin 4 → ℝ) : Line C → Fin 4 → ℝ :=
  fun l => if T l.ends.2 then -k l else k l

/-- **A tadpole side**: a set `T` of vertices closed under the fermion pairing, with no external
attached, and with an odd number of `gauge` and `gaugeCt` vertices. -/
structure TadSide (C : Contraction 1 nA κ) (T : Fin N → Prop) [DecidablePred T] : Prop where
  closed : ∀ x, isZ (fun s : Wick.FermionVertex κ => T s.1) (C.1.1 x) =
    isZ (fun s : Wick.FermionVertex κ => T s.1) x
  photon : ∀ j a, C.1.2 (.inl j) = .inr a → ¬ T a.1
  odd : Odd (Finset.univ.filter fun s : {s : Wick.FermionVertex κ // T s.1} =>
    κ s.1.1 = .gauge ∨ κ s.1.1 = .gaugeCt).card

variable {T}

theorem psiMomentum₂_reflMom_of_T (hT : TadSide C T) (pIn : Fin 1 → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) {s : Wick.FermionVertex κ} (hs : T s.1) :
    psiMomentum₂ C pIn (reflMom T k) s = -psiMomentum₂ C pIn k s := by
  unfold psiMomentum₂
  split
  · rename_i i h
    have := hT.closed (.inr s)
    rw [h] at this
    simp [isZ, hs] at this
  · simp [reflMom, Line.ends, hs]

theorem psiMomentum₂_reflMom_of_not (pIn : Fin 1 → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    {s : Wick.FermionVertex κ} (hs : ¬ T s.1) :
    psiMomentum₂ C pIn (reflMom T k) s = psiMomentum₂ C pIn k s := by
  unfold psiMomentum₂
  split
  · rfl
  · simp [reflMom, Line.ends, hs]

theorem photonMomentum₂_reflMom (hT : TadSide C T) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (hcross : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → k l = 0)
    (a : Wick.PhotonSlot κ) :
    photonMomentum₂ C kIn (reflMom T k) a =
      if T a.1 then -photonMomentum₂ C kIn k a else photonMomentum₂ C kIn k a := by
  unfold photonMomentum₂
  by_cases ha : T a.1
  · have hext : (∑ j, if C.1.2 (.inl j) = .inr a then kIn j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [ite_eq_right_iff]
        exact fun h => absurd ha (hT.photon j a h)
    have key : ∀ g : PhotonLine C, (g.head = a ∨ g.1 = a) →
        reflMom T k (.inr g) = -k (.inr g) := by
      rintro g (h | h)
      · simp [reflMom, Line.ends, h, ha]
      · by_cases hh : T g.head.1
        · simp [reflMom, Line.ends, hh]
        · have h0 := hcross (.inr g) (by simp [Line.ends, h, ha, hh])
          simp [reflMom, Line.ends, hh, h0]
    simp only [ha, ↓reduceIte]
    rw [hext, zero_add, zero_add, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    have k1 := fun h => key g (.inl h)
    have k2 := fun h => key g (.inr h)
    by_cases h1 : g.head = a <;> by_cases h2 : g.1 = a <;> simp [h1, h2, k1, k2]
  · have key : ∀ g : PhotonLine C, (g.head = a ∨ g.1 = a) →
        reflMom T k (.inr g) = k (.inr g) := by
      rintro g (h | h)
      · simp [reflMom, Line.ends, h, ha]
      · by_cases hh : T g.head.1
        · have h0 := hcross (.inr g) (by simp [Line.ends, h, ha, hh])
          simp [reflMom, Line.ends, hh, h0]
        · simp [reflMom, Line.ends, hh]
    simp only [ha, ↓reduceIte]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    have k1 := fun h => key g (.inl h)
    have k2 := fun h => key g (.inr h)
    by_cases h1 : g.head = a <;> by_cases h2 : g.1 = a <;> simp [h1, h2, k1, k2]

theorem reflMom_eq_or_neg (k : Line C → Fin 4 → ℝ) (l : Line C) :
    reflMom T k l = k l ∨ reflMom T k l = -k l := by
  unfold reflMom
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

end QED.GradedProof.X1C

end
