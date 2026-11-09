/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassificationGauge2
import QED.Integration.EnergyFirstShift

/-!
# The self-energy loop

The one-loop part of the electron self-energy `onePIFunction P 1 0 2` of the general Wick model
(decisions D-23, D-24, D-25): the contractions of two gauge vertices `gauge2` with one external
fermion pair and no external photon.

* `isOnePI_iff_exists_isSelfEnergyLoop`: a contraction is 1PI exactly when it is a self-energy
  loop `IsSelfEnergyLoop C a b`: the fermion line runs from `Ψ̄(y)` through `b` and `a` to
  `Ψ(x)`, and the photon fields of the two vertices are contracted with each other. The other
  contractions with attached externals are tadpoles, in which the photon line is a bridge.
* `IsSelfEnergyLoop.contractionValue_eq`: the value of a self-energy loop is the energy-first
  integral of `selfEnergyIntegrand` (62.28). The routing gives the fermion line the loop
  momentum `ℓ` and the photon line `±(ℓ - p)`; the shift `ℓ ↦ ℓ - p` of the loop momentum and
  the symmetry of the photon propagator give the integrand `γ^ν S̃(p + ℓ) γ^μ Δ̃_{μν}(ℓ)`.
  Every fermion field lies on the open fermion line, so only the all-electron flavoring is
  preserved, with weight `1`.
* `sum_isOnePI_selfEnergyLoop`: the two self-energy loops (`a = 0` and `a = 1`) have sign `+1`
  and the same value, so the `1/2!` of the Wick expansion leaves one copy.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-! ### The photon line of two gauge vertices without external photons -/

section NoExternalPhoton

variable {nf : ℕ} (C : Contraction nf 0 gauge2)

/-- Without external photons, the photon field of vertex `0` is contracted with that of
vertex `1`. -/
theorem snd_inr_ps2_zero : C.1.2 (.inr (ps2 0)) = .inr (ps2 1) := by
  rcases h : C.1.2 (.inr (ps2 0)) with i | s
  · exact i.elim0
  · rcases ps2_eq_or 0 1 (by decide) s with rfl | rfl
    · exact absurd h (C.2 _).2
    · rfl

/-- Without external photons, the photon field of vertex `1` is contracted with that of
vertex `0`. -/
theorem snd_inr_ps2_one : C.1.2 (.inr (ps2 1)) = .inr (ps2 0) := by
  rw [← snd_inr_ps2_zero C, (C.2 _).1]

/-- The internal photon line of two gauge vertices without external photons. -/
def photonLine2 : PhotonLine C := ⟨ps2 0, ps2 1, snd_inr_ps2_zero C, by simp⟩

/-- The photon line is indexed by the photon field of vertex `0`. -/
@[simp]
theorem photonLine2_val : (photonLine2 C).1 = ps2 0 := rfl

/-- The head of the photon line is the photon field of vertex `1`. -/
@[simp]
theorem head_photonLine2 : (photonLine2 C).head = ps2 1 :=
  PhotonLine.head_eq (snd_inr_ps2_zero C)

/-- The photon line runs from vertex `0` to vertex `1`. -/
theorem ends_photonLine2 : Line.ends (.inr (photonLine2 C) : Line C) = (0, 1) := by
  change ((photonLine2 C).1.1, (photonLine2 C).head.1) = (0, 1)
  rw [head_photonLine2]
  rfl

/-- The photon line is the only internal photon line. -/
theorem eq_photonLine2 (g : PhotonLine C) : g = photonLine2 C := by
  obtain ⟨s, s', hs, hk⟩ := g
  apply Subtype.ext
  change s = ps2 0
  rcases ps2_eq_or 0 1 (by decide) s with rfl | rfl
  · rfl
  · rw [snd_inr_ps2_one C, Sum.inr.injEq] at hs
    subst hs
    simp at hk

/-- A product over the internal photon lines. -/
theorem prod_photonLine2 {M : Type*} [CommMonoid M] (F : PhotonLine C → M) :
    ∏ g, F g = F (photonLine2 C) :=
  Fintype.prod_eq_single _ fun g hg => absurd (eq_photonLine2 C g) hg

end NoExternalPhoton

/-! ### Self-energy loops -/

/-- The contraction `C` of two gauge vertices is the self-energy loop with fermion line
`Ψ̄(y) → b → a → Ψ(x)`: the external `Ψ(x)` is contracted with `Ψ̄_a`, `Ψ_a` with `Ψ̄_b`, and `Ψ_b`
with the external `Ψ̄(y)`. The photon fields of `a` and `b` are then contracted with each
other. -/
def IsSelfEnergyLoop (C : Contraction 1 0 gauge2) (a b : Fin 2) : Prop :=
  a ≠ b ∧ C.1.1 (.inl 0) = .inr (fv2 a) ∧ C.1.1 (.inr (fv2 a)) = .inr (fv2 b) ∧
    C.1.1 (.inr (fv2 b)) = .inl 0

namespace IsSelfEnergyLoop

variable {C : Contraction 1 0 gauge2} {a b : Fin 2}

/-- The two vertices of the loop are distinct. -/
theorem ne (hC : IsSelfEnergyLoop C a b) : a ≠ b := hC.1
/-- The external `Ψ(x)` is contracted with the `Ψ̄` of `a`. -/
theorem psi_out (hC : IsSelfEnergyLoop C a b) : C.1.1 (.inl 0) = .inr (fv2 a) := hC.2.1
/-- The `Ψ` of `a` is contracted with the `Ψ̄` of `b`. -/
theorem psi_a (hC : IsSelfEnergyLoop C a b) : C.1.1 (.inr (fv2 a)) = .inr (fv2 b) := hC.2.2.1
/-- The `Ψ` of `b` is contracted with the external `Ψ̄(y)`. -/
theorem psi_b (hC : IsSelfEnergyLoop C a b) : C.1.1 (.inr (fv2 b)) = .inl 0 := hC.2.2.2

/-- The internal fermion line, from `b` to `a`. -/
def fermionLine (hC : IsSelfEnergyLoop C a b) : FermionLine C :=
  ⟨fv2 a, by simp [hC.psi_a]⟩

/-- The fermion line is indexed by the `Ψ` of `a`. -/
@[simp]
theorem fermionLine_val (hC : IsSelfEnergyLoop C a b) : hC.fermionLine.1 = fv2 a := rfl

/-- The fermion line starts at `b`. -/
@[simp]
theorem tail_fermionLine (hC : IsSelfEnergyLoop C a b) : hC.fermionLine.tail = fv2 b :=
  FermionLine.tail_eq hC.psi_a

/-- The fermion line runs from `b` to `a`. -/
theorem ends_fermionLine (hC : IsSelfEnergyLoop C a b) :
    Line.ends (.inl hC.fermionLine : Line C) = (b, a) := by
  change (hC.fermionLine.tail.1, hC.fermionLine.1.1) = (b, a)
  rw [tail_fermionLine]
  rfl

/-- The fermion line is the only internal fermion line: the `Ψ` of `b` is contracted with the
external `Ψ̄(y)`. -/
theorem eq_fermionLine (hC : IsSelfEnergyLoop C a b) (f : FermionLine C) : f = hC.fermionLine := by
  obtain ⟨t, ht⟩ := f
  apply Subtype.ext
  change t = fv2 a
  rcases fv2_eq_or a b hC.ne t with rfl | rfl
  · rfl
  · rw [hC.psi_b] at ht
    exact absurd ht Bool.false_ne_true

/-- A product over the internal fermion lines. -/
theorem prod_fermionLine (hC : IsSelfEnergyLoop C a b) {M : Type*} [CommMonoid M]
    (F : FermionLine C → M) : ∏ f, F f = F hC.fermionLine :=
  Fintype.prod_eq_single _ fun f hf => absurd (hC.eq_fermionLine f) hf

/-- The internal lines are the fermion line and the photon line. -/
theorem line_cases (hC : IsSelfEnergyLoop C a b) (g : Line C) :
    g = .inl hC.fermionLine ∨ g = .inr (photonLine2 C) := by
  rcases g with f | g
  · exact Or.inl (congrArg _ (hC.eq_fermionLine f))
  · exact Or.inr (congrArg _ (eq_photonLine2 C g))

/-- A self-energy loop is 1PI: its two internal lines join the two vertices. -/
theorem isOnePI (hC : IsSelfEnergyLoop C a b) : IsOnePI C := by
  refine isOnePI_of_fin_two ⟨fun i j => ?_, fun i => i.elim0⟩ (f₁ := .inl hC.fermionLine)
    (f₂ := .inr (photonLine2 C)) Sum.inl_ne_inr ?_ ?_
  · rw [Subsingleton.elim i 0, hC.psi_out]
    exact Sum.inr_ne_inl
  · rw [hC.ends_fermionLine]
    exact hC.ne.symm
  · rw [ends_photonLine2]
    decide

/-- The loop line is the fermion line, whose label `a ≤ 1` is below the label `2` of the photon
line. -/
theorem isLoopLine_iff (hC : IsSelfEnergyLoop C a b) (g : Line C) :
    IsLoopLine g ↔ g = .inl hC.fermionLine := by
  rw [hC.isOnePI.isLoopLine_iff]
  have hlabel : ∀ g : Line C, Line.label (.inl hC.fermionLine : Line C) ≤ g.label := by
    intro g
    rcases hC.line_cases g with rfl | rfl
    · exact le_rfl
    · change a.val ≤ 2 + Wick.photonKey (ps2 0)
      omega
  constructor
  · intro h
    rcases hC.line_cases g with rfl | rfl
    · rfl
    · have := h (.inl hC.fermionLine)
      change 2 + Wick.photonKey (ps2 0) ≤ a.val at this
      omega
  · rintro rfl
    exact hlabel

/-- **Flavor collapse.** Both fermion fields lie on the open fermion line, so the only flavoring
that the loop preserves is the all-electron one. -/
theorem eq_electronFlavoring (hC : IsSelfEnergyLoop C a b) {φ : Flavoring gauge2}
    (hφ : Preserves C φ) : φ = electronFlavoring gauge2 := by
  have ha : φ.1 (fv2 a) = 0 := by
    have := hφ (.inl 0)
    rwa [hC.psi_out] at this
  have hb : φ.1 (fv2 b) = 0 := by
    have := hφ (.inr (fv2 a))
    rw [hC.psi_a] at this
    exact this.trans ha
  apply Subtype.ext
  funext t
  rcases fv2_eq_or a b hC.ne t with rfl | rfl
  · exact ha
  · exact hb

/-- The external momentum at vertex `0`: `pIn` enters at `b`, `pOut` leaves at `a`. -/
theorem externalMomentum_zero (hC : IsSelfEnergyLoop C a b) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) :
    externalMomentum C pOut pIn kIn 0 =
      (if b = 0 then pIn 0 else 0) - (if a = 0 then pOut 0 else 0) := by
  have h1 : (∃ t : Wick.FermionVertex gauge2, t.1 = 0 ∧ C.1.1 (.inr t) = .inl 0) ↔ b = 0 := by
    constructor
    · rintro ⟨t, ht, h⟩
      rw [Sum.inr_injective (C.1.1.injective (h.trans hC.psi_b.symm))] at ht
      exact ht
    · rintro rfl
      exact ⟨fv2 0, rfl, hC.psi_b⟩
  have h2 : (∃ t : Wick.FermionVertex gauge2, t.1 = 0 ∧ C.1.1 (.inl 0) = .inr t) ↔ a = 0 := by
    constructor
    · rintro ⟨t, ht, h⟩
      rw [hC.psi_out, Sum.inr.injEq] at h
      rw [← h] at ht
      exact ht
    · rintro rfl
      exact ⟨fv2 0, rfl, hC.psi_out⟩
  unfold externalMomentum
  simp only [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero, h1, h2]

/-- The photon line carries `pIn - ℓ` or `ℓ - pOut`, the momentum entering at vertex `0`. -/
theorem lineMomentum_photonLine2 (hC : IsSelfEnergyLoop C a b) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ (.inr (photonLine2 C)) =
      (if b = 0 then pIn 0 else 0) - (if a = 0 then pOut 0 else 0) +
        ((if a = 0 then ℓ else 0) - (if b = 0 then ℓ else 0)) := by
  rw [lineMomentum_of_forall_eq_or hC.isLoopLine_iff Sum.inr_ne_inl
      (fun g => (hC.line_cases g).symm), ends_photonLine2, hC.ends_fermionLine,
    hC.externalMomentum_zero]

/-- For equal incoming and outgoing momenta `p`, the photon line carries `±(ℓ - p)`, so its
propagator is that of `ℓ - p`. -/
theorem photonPropagator_lineMomentum (hC : IsSelfEnergyLoop C a b) (mγ Λ ε : ℝ)
    (p : Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    QED.OneLoop.photonPropagator mγ Λ ε
        (lineMomentum C ![p] ![p] kIn ℓ (.inr (photonLine2 C))) =
      QED.OneLoop.photonPropagator mγ Λ ε (ℓ - p) := by
  rw [hC.lineMomentum_photonLine2]
  have hab := hC.ne
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  · congr 1
    simp only [Matrix.cons_val_zero, ite_true, one_ne_zero, ite_false]
    abel
  · funext μ ν
    rw [← QED.OneLoop.photonPropagator_neg]
    congr 1
    simp only [Matrix.cons_val_zero, ite_true, one_ne_zero, ite_false]
    abel

/-- The photon propagator contracted with the Lorentz indices of the two vertices, in either
order. -/
theorem photonPropagator_ps2 (hC : IsSelfEnergyLoop C a b) (mγ Λ ε : ℝ) (k : Fin 4 → ℝ)
    (lor : Wick.PhotonSlot gauge2 → Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k (lor (ps2 0)) (lor (ps2 1)) =
      QED.OneLoop.photonPropagator mγ Λ ε k (lor (ps2 a)) (lor (ps2 b)) := by
  have hab := hC.ne
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  · rfl
  · exact QED.OneLoop.photonPropagator_comm _ _ _ _ _ _

/-- **The amplitude of a self-energy loop**:
`(ie)² (1/i)² ∑_{μν} Δ̃_{μν}(k) (γ^μ S̃(ℓ) γ^ν)_{αβ}`, with the fermion line carrying the loop
momentum `ℓ` and the photon line the routed momentum `k`. -/
theorem contractionAmplitude_eq (P : Params) (hC : IsSelfEnergyLoop C a b)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude P C (electronFlavoring gauge2) pOut pIn kIn ℓ αOut βIn μ =
      (I * P.e) ^ 2 * (1 / I) ^ 2 * ∑ μ', ∑ ν',
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
            (lineMomentum C pOut pIn kIn ℓ (.inr (photonLine2 C))) μ' ν' *
          (Dirac.gamma μ' * QED.OneLoop.electronPropagator P.m P.ε ℓ * Dirac.gamma ν')
            (αOut 0) (βIn 0) := by
  have hloop : lineMomentum C pOut pIn kIn ℓ (.inl hC.fermionLine) = ℓ :=
    lineMomentum_of_isLoopLine ((hC.isLoopLine_iff _).mpr rfl) _ _ _ _
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hC.psi_out,
    spinor_constraint_in_iff_of_one hC.psi_b, IsEmpty.forall_iff, and_true,
    prod_fin_two_eq_mul hC.ne, vertexFactor_gauge2, hC.prod_fermionLine, prod_photonLine2,
    fermionLine_val, tail_fermionLine, photonLine2_val, head_photonLine2, hloop,
    hC.photonPropagator_ps2]
  exact sum_selfEnergy_index (fv2_injective.ne hC.ne) (fv2_eq_or a b hC.ne)
    (ps2_injective.ne hC.ne) (ps2_eq_or a b hC.ne) _ _ _ _ _ _ _

/-- **The value of a self-energy loop** is the energy-first integral of the self-energy integrand
of (62.28), for equal incoming and outgoing momenta `p`. The routed integrand is the source's at
the shifted loop momentum `ℓ - p`, and the energy-first integral is invariant under the shift. -/
theorem contractionValue_eq (P : Params) (hC : IsSelfEnergyLoop C a b) (p : Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionValue P C ![p] ![p] kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        selfEnergyIntegrand P P.ε p ℓ (αOut 0) (βIn 0) := by
  rw [contractionValue_of_isLoopLine P ((hC.isLoopLine_iff _).mpr rfl),
    ← QED.OneLoop.energyFirstIntegral_sub_right_eq_self
      (fun ℓ => selfEnergyIntegrand P P.ε p ℓ (αOut 0) (βIn 0)) p]
  congr 1
  funext ℓ
  rw [regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.eq_electronFlavoring hφ),
    hC.contractionAmplitude_eq, hC.photonPropagator_lineMomentum, selfEnergyIntegrand]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, add_sub_cancel]
  have hsum : ∀ (D : Fin 4 → Fin 4 → ℂ) (S : Matrix (Fin 4) (Fin 4) ℂ),
      (∀ μ ν, D μ ν = D ν μ) →
      ∑ μ, ∑ ν, D μ ν * (Dirac.gamma ν * S * Dirac.gamma μ) (αOut 0) (βIn 0) =
        ∑ μ, ∑ ν, D μ ν * (Dirac.gamma μ * S * Dirac.gamma ν) (αOut 0) (βIn 0) :=
    fun D S hD => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hD]
  rw [hsum _ _ (QED.OneLoop.photonPropagator_comm _ _ _ _)]
  ring

/-- A self-energy loop is determined by its vertex order. -/
theorem ext {C' : Contraction 1 0 gauge2} (hC : IsSelfEnergyLoop C a b)
    (hC' : IsSelfEnergyLoop C' a b) : C = C' := by
  apply Subtype.ext
  apply Prod.ext
  · ext1 x
    rcases x with i | t
    · rw [Subsingleton.elim i 0, hC.psi_out, hC'.psi_out]
    · rcases fv2_eq_or a b hC.ne t with rfl | rfl
      · rw [hC.psi_a, hC'.psi_a]
      · rw [hC.psi_b, hC'.psi_b]
  · ext1 x
    rcases x with i | s
    · exact i.elim0
    · rcases ps2_eq_or 0 1 (by decide) s with rfl | rfl
      · rw [snd_inr_ps2_zero C, snd_inr_ps2_zero C']
      · rw [snd_inr_ps2_one C, snd_inr_ps2_one C']

end IsSelfEnergyLoop

/-- **The 1PI contractions of two gauge vertices with one external fermion pair** are the
self-energy loops. With the externals attached, a 1PI contraction has a fermion line joining the
two vertices (the photon line is the only other line), which forces the open fermion line
`Ψ̄(y) → b → a → Ψ(x)`. -/
theorem IsOnePI.exists_isSelfEnergyLoop {C : Contraction 1 0 gauge2} (hC : IsOnePI C) :
    ∃ a b, IsSelfEnergyLoop C a b := by
  obtain ⟨a, ha⟩ : ∃ a, C.1.1 (.inl 0) = .inr (fv2 a) := by
    rcases h : C.1.1 (.inl 0) with i | t
    · exact absurd h (hC.1.1 0 i)
    · exact ⟨t.1, by rw [fv2_val_eq]⟩
  obtain ⟨b, hab⟩ : ∃ b, a ≠ b := ⟨a + 1, by omega⟩
  obtain ⟨f₁, f₂, hne, h₁, h₂⟩ := hC.exists_crosses_ne (v := 0) (w := 1) (by decide)
  obtain ⟨⟨t, ht⟩, hcross⟩ : ∃ f : FermionLine C, Line.Crosses (.inl f : Line C) 0 := by
    rcases f₁ with f₁ | g₁
    · exact ⟨f₁, h₁⟩
    rcases f₂ with f₂ | g₂
    · exact ⟨f₂, h₂⟩
    exact absurd (congrArg Sum.inr ((eq_photonLine2 C g₁).trans (eq_photonLine2 C g₂).symm)) hne
  obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inr t) = .inr s := by
    rcases h : C.1.1 (.inr t) with i | s
    · rw [h] at ht
      exact absurd ht Bool.false_ne_true
    · exact ⟨s, rfl⟩
  have hst : s ≠ t := by
    intro h
    apply hcross.1
    change (FermionLine.tail ⟨t, ht⟩).1 = t.1
    rw [FermionLine.tail_eq hs, h]
  have hsa : s ≠ fv2 a := by
    rintro rfl
    exact Sum.inr_ne_inl (C.1.1.injective (hs.trans ha.symm))
  have hsb : s = fv2 b := (fv2_eq_or a b hab s).resolve_left hsa
  have hta : t = fv2 a :=
    (fv2_eq_or a b hab t).resolve_right fun h => hst (hsb.trans h.symm)
  subst hsb hta
  refine ⟨a, b, hab, ha, hs, ?_⟩
  rcases h : C.1.1 (.inr (fv2 b)) with i | u
  · rw [Subsingleton.elim i 0]
  · exfalso
    rcases fv2_eq_or a b hab u with rfl | rfl
    · exact Sum.inr_ne_inl (C.1.1.injective (h.trans ha.symm))
    · exact hab (fv2_injective (Sum.inr_injective (C.1.1.injective (hs.trans h.symm))))

/-- The 1PI contractions of two gauge vertices with one external fermion pair are exactly the
self-energy loops. -/
theorem isOnePI_iff_exists_isSelfEnergyLoop (C : Contraction 1 0 gauge2) :
    IsOnePI C ↔ ∃ a b, IsSelfEnergyLoop C a b :=
  ⟨IsOnePI.exists_isSelfEnergyLoop, fun ⟨_, _, h⟩ => h.isOnePI⟩

/-! ### The two self-energy loops -/

/-- The fermion pairing of the self-energy loop `Ψ̄(y) → b → a → Ψ(x)`. -/
def selfEnergyPairing (a b : Fin 2) : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex gauge2) :=
  Equiv.swap (.inl 0) (.inr (fv2 b)) * Equiv.swap (.inl 0) (.inr (fv2 a))

/-- The photon pairing of two gauge vertices without external photons. -/
def gaugePhotonPairing : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot gauge2) :=
  Equiv.swap (.inr (ps2 0)) (.inr (ps2 1))

/-- The photon pairing is a fixed-point-free involution. -/
theorem gaugePhotonPairing_involutive :
    ∀ x, gaugePhotonPairing (gaugePhotonPairing x) = x ∧ gaugePhotonPairing x ≠ x := by
  decide

/-- The self-energy loop `Ψ̄(y) → b → a → Ψ(x)` as a contraction. -/
def selfEnergyLoop (a b : Fin 2) : Contraction 1 0 gauge2 :=
  ⟨(selfEnergyPairing a b, gaugePhotonPairing), gaugePhotonPairing_involutive⟩

/-- The values of the fermion pairing of the self-energy loop. -/
theorem selfEnergyPairing_apply : ∀ a b : Fin 2, a ≠ b →
    selfEnergyPairing a b (.inl 0) = .inr (fv2 a) ∧
      selfEnergyPairing a b (.inr (fv2 a)) = .inr (fv2 b) ∧
      selfEnergyPairing a b (.inr (fv2 b)) = .inl 0 := by
  decide

/-- `selfEnergyLoop a b` is the self-energy loop `Ψ̄(y) → b → a → Ψ(x)`. -/
theorem isSelfEnergyLoop_selfEnergyLoop (a b : Fin 2) (hab : a ≠ b) :
    IsSelfEnergyLoop (selfEnergyLoop a b) a b :=
  ⟨hab, selfEnergyPairing_apply a b hab⟩

/-- A self-energy loop has fermionic sign `+1`: `(-1)²` from the vertices times the sign `+1` of
a 3-cycle. -/
theorem fermionSign_selfEnergyLoop (a b : Fin 2) : fermionSign (selfEnergyLoop a b) = 1 := by
  have hb : (Sum.inl 0 : Fin 1 ⊕ Wick.FermionVertex gauge2) ≠ .inr (fv2 b) := Sum.inl_ne_inr
  have ha : (Sum.inl 0 : Fin 1 ⊕ Wick.FermionVertex gauge2) ≠ .inr (fv2 a) := Sum.inl_ne_inr
  rw [fermionSign, card_fermionVertex_gauge2]
  simp [selfEnergyLoop, selfEnergyPairing, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap ha,
    Equiv.Perm.sign_swap hb]

/-- **The 1PI part of two gauge vertices with one external fermion pair** of momentum `p`: the two
self-energy loops, each of sign `+1` and with the energy-first integral of the self-energy
integrand as value. -/
theorem sum_isOnePI_selfEnergyLoop (P : Params) [Fintype (Contraction 1 0 gauge2)]
    [DecidablePred (IsOnePI (nf := 1) (nA := 0) (κ := gauge2))] (p : Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 gauge2)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C ![p] ![p] kIn αOut βIn μ =
      2 * QED.OneLoop.energyFirstIntegral fun ℓ =>
        selfEnergyIntegrand P P.ε p ℓ (αOut 0) (βIn 0) := by
  classical
  have h01 := isSelfEnergyLoop_selfEnergyLoop 0 1 (by decide)
  have h10 := isSelfEnergyLoop_selfEnergyLoop 1 0 (by decide)
  have hfilter : (Finset.univ : Finset (Contraction 1 0 gauge2)).filter IsOnePI =
      {selfEnergyLoop 0 1, selfEnergyLoop 1 0} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hC
      obtain ⟨a, b, h⟩ := hC.exists_isSelfEnergyLoop
      have hab := h.ne
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      · exact Or.inl (h.ext h01)
      · exact Or.inr (h.ext h10)
    · rintro (rfl | rfl)
      · exact h01.isOnePI
      · exact h10.isOnePI
  have hne : selfEnergyLoop 0 1 ≠ selfEnergyLoop 1 0 := fun h => by
    have h' := h01.psi_out
    rw [h, h10.psi_out, Sum.inr.injEq, fv2_inj] at h'
    exact absurd h' (by decide)
  rw [hfilter, Finset.sum_pair hne, fermionSign_selfEnergyLoop, fermionSign_selfEnergyLoop,
    h01.contractionValue_eq,
    h10.contractionValue_eq]
  push_cast
  ring

end QED.WickModel

end
