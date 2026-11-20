/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CTadAmp
public import QED.GradedProof.X1CSplitRoute
public import QED.Frozen.Graded.ContractionValue

/-!
# (X₁) piece C: tadpoles have value `0`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C4. Let `T` be a tadpole side of a connected contraction `C`
(`TadSide`) such that exactly one line `b` crosses its boundary. Then:

* the line `b` carries momentum `0` in every conserved assignment (`eq_zero_of_crossing`): the
  external momenta at `T` vanish (`externalMomentum_eq_zero_of_tadSide`), and the net inflow into
  `T` is the momentum of `b`, up to sign;
* the reflection `reflMom T` of a conserved assignment is conserved (`isConserved_reflMom`);
* the routing change may flip the signs of loop momenta
  (`jointEnergyFirstIntegral_eq_of_isConserved_pm`, through `ℓ ↦ diag(±1) ℓ`);
* so the value (G₅) equals minus itself (`QED.GradedProof.X1C.regulatedAmplitude_reflMom`):
  `contractionValue_eq_zero_of_tadSide`.

No integrability is assumed.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X1C

open QED.Graded
open QED.WickModel (Params Contraction Line loopCount lineMomentum₂ externalMomentum
  VerticesConnected)
open QED.TwoLoop.Routing (IsConserved inflow isConserved_lineMomentum₂)
open QED.TwoLoop.Relabel (IsIntAffine)
open QED.GradedProof.X0 (isZ)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Routing changes with signs -/

/-- **Routing changes with signs**: as `jointEnergyFirstIntegral_eq_of_isConserved`, with every
loop momentum carried, up to sign, by some line. -/
theorem jointEnergyFirstIntegral_eq_of_isConserved_pm {C : Contraction nf nA κ}
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} {L : ℕ} (hL : loopCount C = L)
    (k : (Fin L → Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (k ℓ)) (haff : ∀ f, IsIntAffine fun ℓ => k ℓ f)
    (hrec : ∀ r : Fin L, ∃ f, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ ℓ, k ℓ f = σ • ℓ r)
    (F : (Line C → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => F (lineMomentum₂ C pOut pIn kIn ℓ)) =
      QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => F (k ℓ)) := by
  choose f σ hσ hf using hrec
  have hσσ : ∀ r, σ r * σ r = 1 := fun r => by rcases hσ r with h | h <;> simp [h]
  set D : Matrix (Fin L) (Fin L) ℤ := Matrix.diagonal σ with hD
  have hDℓ : ∀ ℓ : Fin L → Fin 4 → ℝ, (fun s => ∑ r, D s r • ℓ r) = fun s => σ s • ℓ s := by
    intro ℓ
    funext s
    simp [hD, Matrix.diagonal_apply, ite_smul]
  have hdet : IsUnit D.det := by
    rw [hD, Matrix.det_diagonal]
    have hsq : (∏ r, σ r) * ∏ r, σ r = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun r _ => hσσ r
    exact ⟨⟨_, _, hsq, hsq⟩, rfl⟩
  have h1 := jointEnergyFirstIntegral_eq_of_isConserved hL (fun ℓ => k fun s => σ s • ℓ s)
    (fun ℓ => hcons _) (fun l => ?_) (fun r => ⟨f r, fun ℓ => ?_⟩) F
  · rw [h1]
    have h2 := QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix L
      (fun ℓ => F (k ℓ)) D hdet
    simp only [hDℓ] at h2
    exact h2
  · obtain ⟨m, b, h⟩ := haff l
    refine ⟨fun r => m r * σ r, b, fun ℓ => ?_⟩
    simp only [h, mul_smul]
  · rw [hf r, smul_smul, hσσ, one_smul]

/-! ### The crossing line and the reflected assignment -/

variable {C : Contraction 1 nA κ} {T : Fin N → Prop} [DecidablePred T]

theorem externalMomentum_eq_zero_of_tadSide (hT : TadSide C T) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) {v : Fin N} (hv : T v) : externalMomentum C pOut pIn kIn v = 0 := by
  have h1 : ∀ i, ¬ ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl i := by
    rintro i ⟨t, rfl, h⟩
    have := hT.closed (.inr t)
    rw [h] at this
    simp [isZ, hv] at this
  have h2 : ∀ j, ¬ ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl j) = .inr a := by
    rintro j ⟨a, rfl, h⟩
    exact hT.photon j a h hv
  have h3 : ∀ i, ¬ ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl i) = .inr t := by
    rintro i ⟨t, rfl, h⟩
    have := hT.closed (.inl i)
    rw [h] at this
    simp [isZ, hv] at this
  unfold externalMomentum
  simp [h1, h2, h3]

/-- The net inflow into `T` of an assignment conserved at the vertices of `T`. -/
theorem sum_cut_eq_zero (k : Line C → Fin 4 → ℝ) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (hk : IsConserved C pOut pIn kIn k)
    (hext : ∀ v, T v → externalMomentum C pOut pIn kIn v = 0) :
    ∑ l, ((if T l.ends.2 then k l else 0) - (if T l.ends.1 then k l else 0)) = 0 := by
  have hv : ∀ v, (if T v then inflow k v else 0) = 0 := fun v => by
    split_ifs with h
    · have := hk v
      rwa [hext v h, add_zero] at this
    · rfl
  have hsel : ∀ (w : Fin N) (x : Fin 4 → ℝ),
      ∑ v, (if T v then (if w = v then x else 0) else 0) = if T w then x else 0 := by
    intro w x
    rw [Finset.sum_eq_single w (fun v _ hv' => by simp [Ne.symm hv']) (by simp)]
    simp
  calc ∑ l, ((if T l.ends.2 then k l else 0) - (if T l.ends.1 then k l else 0))
      = ∑ l, ∑ v, ((if T v then (if l.ends.2 = v then k l else 0) else 0) -
          (if T v then (if l.ends.1 = v then k l else 0) else 0)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_sub_distrib, hsel, hsel]
    _ = ∑ v, (if T v then inflow k v else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        unfold inflow
        split_ifs <;> simp
    _ = 0 := Finset.sum_eq_zero fun v _ => hv v

/-- **The only crossing line carries momentum `0`.** -/
theorem eq_zero_of_crossing (hT : TadSide C T) {b : Line C}
    (hone : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → l = b) (k : Line C → Fin 4 → ℝ)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (hk : IsConserved C pOut pIn kIn k)
    (l : Line C) (hl : ¬ (T l.ends.1 ↔ T l.ends.2)) : k l = 0 := by
  have hs := sum_cut_eq_zero k pOut pIn kIn hk
    (fun v hv => externalMomentum_eq_zero_of_tadSide hT pOut pIn kIn hv)
  rw [Finset.sum_eq_single l (fun l' _ hl' => ?_) (by simp)] at hs
  · by_cases h2 : T l.ends.2
    · have h1 : ¬ T l.ends.1 := fun h1 => hl ⟨fun _ => h2, fun _ => h1⟩
      simpa [h1, h2] using hs
    · have h1 : T l.ends.1 := by
        by_contra h1
        exact hl ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      simpa [h1, h2] using hs
  · have hc : T l'.ends.1 ↔ T l'.ends.2 := by
      by_contra hc
      exact hl' ((hone l' hc).trans (hone l hl).symm)
    by_cases h : T l'.ends.2 <;> simp [h, hc]

/-- **The reflected assignment is conserved.** -/
theorem isConserved_reflMom (hT : TadSide C T) {k : Line C → Fin 4 → ℝ}
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ} (hk : IsConserved C pOut pIn kIn k)
    (hcross : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → k l = 0) :
    IsConserved C pOut pIn kIn (reflMom T k) := by
  intro v
  by_cases hv : T v
  · have h := hk v
    rw [externalMomentum_eq_zero_of_tadSide hT pOut pIn kIn hv, add_zero] at h ⊢
    have key : ∀ l : Line C, (l.ends.2 = v ∨ l.ends.1 = v) → reflMom T k l = -k l := by
      rintro l (hl | hl)
      · simp [reflMom, hl, hv]
      · by_cases h2 : T l.ends.2
        · simp [reflMom, h2]
        · have h0 := hcross l (by rw [hl]; exact fun h => h2 (h.1 hv))
          simp [reflMom, h2, h0]
    unfold inflow at h ⊢
    have k1 := fun l h => key l (.inl h)
    have k2 := fun l h => key l (.inr h)
    have hsum : ∑ l : Line C, ((if l.ends.2 = v then reflMom T k l else 0) -
        (if l.ends.1 = v then reflMom T k l else 0)) =
        -∑ l : Line C, ((if l.ends.2 = v then k l else 0) - (if l.ends.1 = v then k l else 0)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h1 : l.ends.2 = v <;> by_cases h2 : l.ends.1 = v <;>
        simp [h1, h2, k1 l, k2 l]
    rw [hsum, h, neg_zero]
  · have key : ∀ l : Line C, (l.ends.2 = v ∨ l.ends.1 = v) → reflMom T k l = k l := by
      rintro l (hl | hl)
      · simp [reflMom, hl, hv]
      · by_cases h2 : T l.ends.2
        · have h0 := hcross l (by rw [hl]; exact fun h => hv (h.2 h2))
          simp [reflMom, h2, h0]
        · simp [reflMom, h2]
    rw [← hk v]
    congr 1
    unfold inflow
    refine Finset.sum_congr rfl fun l _ => ?_
    have k1 := fun h => key l (.inl h)
    have k2 := fun h => key l (.inr h)
    by_cases h1 : l.ends.2 = v <;> by_cases h2 : l.ends.1 = v <;> simp [h1, h2, k1, k2]

theorem isIntAffine_neg {L : ℕ} {F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsIntAffine F) :
    IsIntAffine fun ℓ => -F ℓ := by
  obtain ⟨m, b, h⟩ := hF
  refine ⟨-m, -b, fun ℓ => ?_⟩
  simp only [h, neg_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

/-! ### The value -/

/-- **A tadpole has value `0`**: if exactly one line `b` crosses the boundary of a tadpole side
`T` of a connected contraction, its value (G₅) vanishes, at any grading, momenta and indices with
total external momentum `0`. -/
theorem contractionValue_eq_zero_of_tadSide (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (g : Grading κ) (hT : TadSide C T) {b : Line C}
    (hone : ∀ l : Line C, ¬ (T l.ends.1 ↔ T l.ends.2) → l = b) (hV : VerticesConnected C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (hs : ∑ v, externalMomentum C pOut pIn kIn v = 0) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) : contractionValue P Φ D C g pOut pIn kIn αOut βIn μ = 0 := by
  have hcons := fun ℓ => isConserved_lineMomentum₂ hV hs (L := loopCount C) ℓ
  have hcr := fun ℓ => eq_zero_of_crossing hT hone _ pOut pIn kIn (hcons ℓ)
  set G : (Line C → Fin 4 → ℝ) → ℂ := fun kk => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
    regulatedAmplitude P Φ D C g pIn kIn kk αOut βIn μ with hG
  have h := jointEnergyFirstIntegral_eq_of_isConserved_pm rfl
    (fun ℓ => reflMom T (lineMomentum₂ C pOut pIn kIn ℓ))
    (fun ℓ => isConserved_reflMom hT (hcons ℓ) (hcr ℓ)) (fun l => ?_) (fun r => ?_) G
  · have hneg : ∀ ℓ : Fin (loopCount C) → Fin 4 → ℝ,
        G (reflMom T (lineMomentum₂ C pOut pIn kIn ℓ)) = -G (lineMomentum₂ C pOut pIn kIn ℓ) :=
      fun ℓ => by
        simp only [hG, regulatedAmplitude_reflMom hT (hcr ℓ), mul_neg]
    simp only [hneg] at h
    unfold QED.TwoLoop.jointEnergyFirstIntegral at h
    simp only [MeasureTheory.integral_neg] at h
    unfold contractionValue QED.TwoLoop.jointEnergyFirstIntegral
    exact CharZero.eq_neg_self_iff.1 h
  · by_cases h2 : T l.ends.2
    · simpa [reflMom, h2] using isIntAffine_neg (IsIntAffine.lineMomentum₂ C pOut pIn kIn l)
    · simpa [reflMom, h2] using IsIntAffine.lineMomentum₂ C pOut pIn kIn l
  · obtain ⟨f, hf⟩ := exists_line_lineMomentum₂ C pOut pIn kIn r
    by_cases h2 : T f.ends.2
    · exact ⟨f, -1, .inr rfl, fun ℓ => by simp [reflMom, h2, hf]⟩
    · exact ⟨f, 1, .inl rfl, fun ℓ => by simp [reflMom, h2, hf]⟩

end QED.GradedProof.X1C

end
