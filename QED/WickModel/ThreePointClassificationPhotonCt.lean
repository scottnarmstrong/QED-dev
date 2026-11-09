/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationFermionCt

/-!
# The photon counterterm on the photon leg

The connected contractions of the three-point function `connectedFunction P 1 1 3` (packet 6a,
decision D-24) with one gauge vertex `g` and one photon counterterm vertex `h` (the sequences
`[gauge, photonCt]` and `[photonCt, gauge]`). The external fermions are contracted with the gauge
vertex. A connected contraction contracts the external photon with one photon field `j` of `h`
(`IsPhotonCtLeg C j`) and the other photon field of `h` with that of `g`: the internal photon line
carries `±q`, `q = p' - p`. Each of the two contractions has sign `+1` and value
`∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q)` times half of `-i δ₃ (q² g^{μρ} - q^μ q^ρ)`, the
`photonCt` vertex factor counting one pairing of its two photon fields. Their single internal line
is a bridge, so they are not 1PI.

## Main statements

* `sum_nonOnePI_photonCt`: the sum over the connected contractions that are not 1PI.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-! ### The photon counterterm factor -/

/-- The momentum dependence of the photon counterterm: `δ₃ (k² g^{μν} - k^μ k^ν)`. -/
noncomputable def photonCtTerm (δ₃ : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν)

/-- The photon counterterm is even in the momentum. -/
theorem photonCtTerm_neg (δ₃ : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    photonCtTerm δ₃ (-k) μ ν = photonCtTerm δ₃ k μ ν := by
  simp [photonCtTerm, Minkowski.dot]

/-- The photon counterterm is symmetric in its Lorentz indices. -/
theorem photonCtTerm_comm (δ₃ : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    photonCtTerm δ₃ k μ ν = photonCtTerm δ₃ k ν μ := by
  simp only [photonCtTerm, Minkowski.metric_symm μ ν, mul_comm (k μ)]

/-- The index swap of `Fin 2`. -/
def otherIdx (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0

/-- The other index is different. -/
theorem otherIdx_ne : ∀ j : Fin 2, otherIdx j ≠ j := by decide

/-- An index different from `j` is the other index. -/
theorem eq_otherIdx_of_ne : ∀ j k : Fin 2, k ≠ j → k = otherIdx j := by decide

/-! ### The vertices of a gauge vertex and a photon counterterm -/

section Vertices

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2}

/-- The photon field `k` of the photon counterterm vertex `h`. -/
def photonCtPs (hκh : κ h = .photonCt) (k : Fin 2) : Wick.PhotonSlot κ :=
  ⟨h, ⟨k, by rw [hκh]; exact k.2⟩⟩

/-- The vertex of `photonCtPs`. -/
@[simp]
theorem photonCtPs_fst (hκh : κ h = .photonCt) (k : Fin 2) : (photonCtPs hκh k).1 = h := rfl

/-- The key of the photon field of the gauge vertex. -/
theorem photonKey_gaugePs (hκg : κ g = .gauge) : Wick.photonKey (gaugePs hκg) = 2 * g.val := rfl

/-- The key of a photon field of the photon counterterm vertex. -/
theorem photonKey_photonCtPs (hκh : κ h = .photonCt) (k : Fin 2) :
    Wick.photonKey (photonCtPs hκh k) = 2 * h.val + k.val := rfl

/-- The photon fields of the counterterm vertex are distinct. -/
theorem photonCtPs_injective (hκh : κ h = .photonCt) : Function.Injective (photonCtPs hκh) :=
  fun i j hij => Fin.ext (by
    have := congrArg Wick.photonKey hij
    rw [photonKey_photonCtPs, photonKey_photonCtPs] at this
    omega)

variable (hgh : g ≠ h) (hκg : κ g = .gauge) (hκh : κ h = .photonCt)
include hgh hκg hκh

/-- The photon field of the gauge vertex is not one of the counterterm vertex. -/
theorem gaugePs_ne_photonCtPs (k : Fin 2) : gaugePs hκg ≠ photonCtPs hκh k := fun h' =>
  hgh (congrArg Sigma.fst h')

/-- The only fermion vertex is the gauge vertex. -/
theorem fv_eq_gaugeFv_of_photonCt (x : Wick.FermionVertex κ) : x = gaugeFv hκg := by
  obtain ⟨t, ht⟩ := x
  rcases (by omega : t = g ∨ t = h) with rfl | rfl
  · rfl
  · exact absurd hκh ht

/-- The photon fields: that of the gauge vertex and the two of the counterterm vertex. -/
theorem ps_cases_photonCt (s : Wick.PhotonSlot κ) :
    s = gaugePs hκg ∨ s = photonCtPs hκh 0 ∨ s = photonCtPs hκh 1 := by
  obtain ⟨t, i⟩ := s
  have hi := i.2
  rcases (by omega : t = g ∨ t = h) with rfl | rfl
  · simp only [hκg, Wick.VertexKind.photonSlots] at hi
    exact Or.inl (Sigma.ext rfl (heq_of_eq (Fin.ext (by simp [gaugePs]; omega))))
  · simp only [hκh, Wick.VertexKind.photonSlots] at hi
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h0 | h1
    · exact Or.inr (Or.inl (Sigma.ext rfl (heq_of_eq (Fin.ext (by simp [photonCtPs, h0])))))
    · exact Or.inr (Or.inr (Sigma.ext rfl (heq_of_eq (Fin.ext (by simp [photonCtPs, h1])))))

omit hgh hκg in
/-- The factor of the photon counterterm vertex. -/
theorem vertexFactor_photonCtPs (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA h =
      -(I / 2) * (photonCtTerm δ₃ (kA (photonCtPs hκh 0)) (lor (photonCtPs hκh 0))
        (lor (photonCtPs hκh 1)) : ℂ) :=
  vertexFactor_of_photonCt _ _ _ _ _ _ _ _ _ _ _ hκh

end Vertices

/-! ### The contractions -/

section Contractions

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2}

/-- The external photon is contracted with the photon field `j` of the photon counterterm. -/
def IsPhotonCtLeg (hκh : κ h = .photonCt) (C : Contraction 1 1 κ) (j : Fin 2) : Prop :=
  C.1.2 (.inl 0) = .inr (photonCtPs hκh j)

variable (hgh : g ≠ h) (hκg : κ g = .gauge) (hκh : κ h = .photonCt)
include hgh hκg hκh

/-- With the externals attached, the external fermions are contracted with the gauge vertex. -/
theorem fst_of_photonCt {C : Contraction 1 1 κ} (hext : ExternalsAttached C) :
    C.1.1 (.inl 0) = .inr (gaugeFv hκg) ∧ C.1.1 (.inr (gaugeFv hκg)) = .inl 0 := by
  have hX := fv_eq_gaugeFv_of_photonCt hgh hκg hκh
  have h0 : C.1.1 (.inl 0) = .inr (gaugeFv hκg) := by
    rcases hC : C.1.1 (.inl 0) with i | t
    · exact absurd hC (hext.1 0 i)
    · rw [hX t]
  refine ⟨h0, ?_⟩
  rcases hC : C.1.1 (.inr (gaugeFv hκg)) with i | t
  · rw [Subsingleton.elim i 0]
  · rw [hX t] at hC
    exact absurd (C.1.1.injective (hC.trans h0.symm)) Sum.inr_ne_inl

/-- Without internal fermion lines. -/
theorem isEmpty_fermionLine_of_photonCt {C : Contraction 1 1 κ} (hext : ExternalsAttached C) :
    IsEmpty (FermionLine C) :=
  ⟨fun f => by
    obtain ⟨t, ht⟩ := f
    rw [fv_eq_gaugeFv_of_photonCt hgh hκg hκh t, (fst_of_photonCt hgh hκg hκh hext).2] at ht
    exact Bool.false_ne_true ht⟩

/-- **The connected contractions contract the external photon with the counterterm.** If it is
contracted with the gauge vertex, the two photon fields of the counterterm are contracted with
each other, and the counterterm is disconnected. -/
theorem exists_isPhotonCtLeg {C : Contraction 1 1 κ} (hext : ExternalsAttached C)
    (hconn : VerticesConnected C) : ∃ j, IsPhotonCtLeg hκh C j := by
  have hS := ps_cases_photonCt hgh hκg hκh
  rcases hC : C.1.2 (.inl 0) with i | s
  · exact absurd hC (hext.2 0 i)
  rcases hS s with rfl | rfl | rfl
  · exfalso
    have hg' : C.1.2 (.inr (gaugePs hκg)) = .inl 0 := by rw [← hC, (C.2 _).1]
    obtain ⟨w, hw⟩ : ∃ w : Fin 2, h ≠ w := ⟨g, hgh.symm⟩
    refine not_verticesConnected_of_forall_not_crosses hw
      (forall_not_crosses_of_isolated (fun t s hts => ?_) (fun a b hab => ?_)) hconn
    · rw [fv_eq_gaugeFv_of_photonCt hgh hκg hκh t, (fst_of_photonCt hgh hκg hκh hext).2] at hts
      exact absurd hts Sum.inl_ne_inr
    · rcases hS a with rfl | rfl | rfl
      · rw [hg'] at hab
        exact absurd hab Sum.inl_ne_inr
      all_goals
        rcases hS b with rfl | rfl | rfl
        · have h2 := congrArg C.1.2 hab
          rw [(C.2 _).1, hg'] at h2
          exact absurd h2 Sum.inr_ne_inl
        all_goals exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨0, hC⟩
  · exact ⟨1, hC⟩

namespace IsPhotonCtLeg

variable {C : Contraction 1 1 κ} {j : Fin 2}

omit hgh hκg in
/-- The photon field `j` of the counterterm is contracted with the external photon. -/
theorem snd_photonCtPs (hC : IsPhotonCtLeg hκh C j) :
    C.1.2 (.inr (photonCtPs hκh j)) = .inl 0 := by
  rw [← hC, (C.2 _).1]

/-- The other photon field of the counterterm is contracted with that of the gauge vertex. -/
theorem snd_gaugePs (hC : IsPhotonCtLeg hκh C j) :
    C.1.2 (.inr (gaugePs hκg)) = .inr (photonCtPs hκh (otherIdx j)) := by
  have hS := ps_cases_photonCt hgh hκg hκh
  rcases h' : C.1.2 (.inr (gaugePs hκg)) with i | s
  · rw [Subsingleton.elim i 0, ← hC.snd_photonCtPs hκh] at h'
    exact absurd (Sum.inr_injective (C.1.2.injective h'))
      (gaugePs_ne_photonCtPs hgh hκg hκh j)
  · have hsj : ∀ k, s = photonCtPs hκh k → k ≠ j := by
      rintro k rfl rfl
      rw [← hC] at h'
      exact Sum.inr_ne_inl (C.1.2.injective h')
    rcases hS s with rfl | rfl | rfl
    · exact absurd h' (C.2 _).2
    · rw [← eq_otherIdx_of_ne j 0 (hsj 0 rfl)]
    · rw [← eq_otherIdx_of_ne j 1 (hsj 1 rfl)]

/-- The internal photon line, joining the gauge vertex and the counterterm. -/
def photonLine (hC : IsPhotonCtLeg hκh C j) : PhotonLine C :=
  photonLineOfPair (hC.snd_gaugePs hgh hκg hκh) (gaugePs_ne_photonCtPs hgh hκg hκh _)

/-- The photon line is indexed by one of its two fields, with the other as head. -/
theorem photonLine_spec (hC : IsPhotonCtLeg hκh C j) :
    ((hC.photonLine hgh hκg hκh).1 = gaugePs hκg ∧
        (hC.photonLine hgh hκg hκh).head = photonCtPs hκh (otherIdx j)) ∨
      ((hC.photonLine hgh hκg hκh).1 = photonCtPs hκh (otherIdx j) ∧
        (hC.photonLine hgh hκg hκh).head = gaugePs hκg) :=
  photonLineOfPair_spec _ _

/-- The photon line is the only internal photon line. -/
theorem eq_photonLine (hC : IsPhotonCtLeg hκh C j) (l : PhotonLine C) :
    l = hC.photonLine hgh hκg hκh := by
  have hS := ps_cases_photonCt hgh hκg hκh
  refine PhotonLine.eq_of_mem (z := gaugePs hκg) ?_ ?_
  · have hl := l.apply_eq_inr_head
    rcases hS l.1 with h1 | h1 | h1
    · exact Or.inl h1
    all_goals
      right
      obtain ⟨k, hk⟩ : ∃ k, l.1 = photonCtPs hκh k := ⟨_, h1⟩
      rw [hk] at hl
      by_cases hkj : k = j
      · subst hkj
        rw [hC.snd_photonCtPs hκh] at hl
        exact absurd hl Sum.inl_ne_inr
      · rw [eq_otherIdx_of_ne j k hkj, ← hC.snd_gaugePs hgh hκg hκh, (C.2 _).1] at hl
        exact (Sum.inr_injective hl).symm
  · rcases photonLineOfPair_spec (hC.snd_gaugePs hgh hκg hκh)
      (gaugePs_ne_photonCtPs hgh hκg hκh _) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2

/-- The photon line is the only internal line. -/
theorem eq_inr_photonLine (hC : IsPhotonCtLeg hκh C j) (hext : ExternalsAttached C)
    (l : Line C) : l = .inr (hC.photonLine hgh hκg hκh) := by
  rcases l with f | l
  · exact (isEmpty_fermionLine_of_photonCt hgh hκg hκh hext).elim f
  · rw [hC.eq_photonLine hgh hκg hκh l]

/-- The photon line joins the gauge vertex and the counterterm. -/
theorem ends_photonLine (hC : IsPhotonCtLeg hκh C j) :
    Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C) = (g, h) ∨
      Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C) = (h, g) :=
  ends_photonLineOfPair _ _

/-- **A photon-leg contraction is connected but not 1PI**: its single internal line joins the two
vertices and is a bridge. -/
theorem connected_not_isOnePI (hC : IsPhotonCtLeg hκh C j) (hext : ExternalsAttached C) :
    (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C := by
  have hne : (Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C)).1 ≠
      (Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C)).2 := by
    rcases hC.ends_photonLine hgh hκg hκh with h' | h' <;> rw [h']
    · exact hgh
    · exact hgh.symm
  refine ⟨⟨hext, ?_⟩, fun h1 => h1.2.2 _
    (isBridge_of_forall_eq (hC.eq_inr_photonLine hgh hκg hκh hext) hne)⟩
  rcases hC.ends_photonLine hgh hκg hκh with h' | h'
  · exact verticesConnected_of_two hgh (joined_of_ends (Set.notMem_empty _) h')
  · exact verticesConnected_of_two hgh.symm (joined_of_ends (Set.notMem_empty _) h')

/-- The photon line carries `±q`, `q = p' - p`. -/
theorem lineMomentum_photonLine (hC : IsPhotonCtLeg hκh C j) (hext : ExternalsAttached C)
    (p' p ℓ : Fin 4 → ℝ) :
    lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr (hC.photonLine hgh hκg hκh)) = p' - p ∨
      lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr (hC.photonLine hgh hκg hκh)) = -(p' - p) := by
  have hne : (Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C)).1 ≠
      (Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C)).2 := by
    rcases hC.ends_photonLine hgh hκg hκh with h' | h' <;> rw [h']
    · exact hgh
    · exact hgh.symm
  have hσ := fst_of_photonCt hgh hκg hκh hext
  rw [lineMomentum_of_forall_eq (hC.eq_inr_photonLine hgh hκg hκh hext) hne,
    externalMomentum_eq_of_one hσ.1 hσ.2 hC]
  rcases hC.ends_photonLine hgh hκg hκh with h' | h' <;> rw [h']
  · right
    simp [hgh.symm]
  · left
    simp [hgh]

/-- The momentum into the counterterm through its first photon field is `±q`. -/
theorem photonMomentum_zero (hC : IsPhotonCtLeg hκh C j) (hext : ExternalsAttached C)
    (p' p ℓ : Fin 4 → ℝ) :
    photonMomentum C ![p'] ![p] ![p' - p] ℓ (photonCtPs hκh 0) = p' - p ∨
      photonMomentum C ![p'] ![p] ![p' - p] ℓ (photonCtPs hκh 0) = -(p' - p) := by
  have hinj := photonCtPs_injective hκh
  have hg0 := gaugePs_ne_photonCtPs hgh hκg hκh
  rw [photonMomentum, Fintype.sum_eq_single (hC.photonLine hgh hκg hκh)
    fun l hl => absurd (hC.eq_photonLine hgh hκg hκh l) hl, Fin.sum_univ_one]
  have hlm := hC.lineMomentum_photonLine hgh hκg hκh hext p' p ℓ
  have hspec := hC.photonLine_spec hgh hκg hκh
  rw [hC]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · simp only [show otherIdx 0 = 1 from rfl] at hspec
    rcases hspec with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [hinj.ne, hg0]
  · simp only [show otherIdx 1 = 0 from rfl] at hspec
    rcases hspec with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [hinj.ne, hg0] <;>
      rcases hlm with hlm | hlm <;> simp [hlm]

/-- The amplitude of a photon-leg contraction: half of the photon-leg counterterm. -/
theorem contractionAmplitude_eq (P : Params) (hC : IsPhotonCtLeg hκh C j)
    (hext : ExternalsAttached C) (p' p ℓ : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionAmplitude P C (electronFlavoring κ) ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
          (-(I / 2) * (photonCtTerm P.δ₃ (p' - p) μ ρ : ℂ)) := by
  have hσ := fst_of_photonCt hgh hκg hκh hext
  have := isEmpty_fermionLine_of_photonCt hgh hκg hκh hext
  have hinj := photonCtPs_injective hκh
  have hg0 := gaugePs_ne_photonCtPs hgh hκg hκh
  have hX := fv_eq_gaugeFv_of_photonCt hgh hκg hκh
  have hprop : ∀ lor : Wick.PhotonSlot κ → Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
          (lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inr (hC.photonLine hgh hκg hκh)))
          (lor (hC.photonLine hgh hκg hκh).1) (lor (hC.photonLine hgh hκg hκh).head) =
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) (lor (gaugePs hκg))
          (lor (photonCtPs hκh (otherIdx j))) := fun lor =>
    photonPropagator_of_pair (hC.lineMomentum_photonLine hgh hκg hκh hext p' p ℓ) lor
      (hC.photonLine_spec hgh hκg hκh)
  have hterm : ∀ μ ν, photonCtTerm P.δ₃ (photonMomentum C ![p'] ![p] ![p' - p] ℓ
      (photonCtPs hκh 0)) μ ν = photonCtTerm P.δ₃ (p' - p) μ ν := fun μ ν => by
    rcases hC.photonMomentum_zero hgh hκg hκh hext p' p ℓ with h' | h' <;> rw [h']
    exact photonCtTerm_neg _ _ _ _
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hσ.1, spinor_constraint_in_iff_of_one hσ.2,
    lorentz_constraint_iff_of_one hC, prod_fin_two_eq_mul hgh,
    vertexFactor_gaugeFv hκg, vertexFactor_photonCtPs hκh, hterm, Finset.univ_eq_empty,
    Finset.prod_empty,
    Fintype.prod_eq_single (hC.photonLine hgh hκg hκh)
      fun l hl => absurd (hC.eq_photonLine hgh hκg hκh l) hl, hprop]
  rw [show (∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
      ∑ lor : Wick.PhotonSlot κ → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot κ → Fin 4, ∑ α : Wick.FermionVertex κ → Fin 4,
        ∑ β : Wick.FermionVertex κ → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [sum_pi_eq_of_forall_eq hX]
  have h10 : photonCtPs hκh 1 ≠ photonCtPs hκh 0 := hinj.ne (by decide)
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · simp only [show otherIdx 0 = 1 from rfl]
    rw [sum_pi_eq_of_three (hg0 0) h10.symm (hg0 1) (ps_cases_photonCt hgh hκg hκh)]
    simp only [ite_true, h10, (hg0 _).symm, ite_false]
    simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
    simp only [Matrix.cons_val_zero]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · simp only [show otherIdx 1 = 0 from rfl]
    rw [sum_pi_eq_of_three (hg0 1) h10 (hg0 0) (by
      intro s; rcases ps_cases_photonCt hgh hκg hκh s with h' | h' | h' <;> simp [h'])]
    simp only [ite_true, h10.symm, (hg0 _).symm, ite_false]
    simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
    simp only [Matrix.cons_val_zero]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [photonCtTerm_comm]
    ring


/-- **The value of a photon-leg contraction**: half of
`∑_{νρ} [i e γ^ν]_{αβ} (1/i) Δ̃_{νρ}(q) (-i δ₃ (q² g^{μρ} - q^μ q^ρ))`. -/
theorem contractionValue_eq (P : Params) (hC : IsPhotonCtLeg hκh C j)
    (hext : ExternalsAttached C) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
          (-(I / 2) * (photonCtTerm P.δ₃ (p' - p) μ ρ : ℂ)) := by
  have hne : (Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C)).1 ≠
      (Line.ends (.inr (hC.photonLine hgh hκg hκh) : Line C)).2 := by
    rcases hC.ends_photonLine hgh hκg hκh with h' | h' <;> rw [h']
    · exact hgh
    · exact hgh.symm
  have hφ : ∀ φ : Flavoring κ, Preserves C φ → φ = electronFlavoring κ := fun φ hφ => by
    have h0 := hφ (.inl 0)
    rw [(fst_of_photonCt hgh hκg hκh hext).1] at h0
    apply Subtype.ext
    funext t
    rw [fv_eq_gaugeFv_of_photonCt hgh hκg hκh t]
    exact h0
  rw [contractionValue_of_forall_eq P (hC.eq_inr_photonLine hgh hκg hκh hext) hne,
    regulatedAmplitude_eq_of_forall_preserves P hφ, hC.contractionAmplitude_eq hgh hκg hκh P hext]

/-- A photon-leg contraction has fermionic sign `+1`: `(-1)¹` from the vertex times the sign
`-1` of a transposition. -/
theorem fermionSign_eq (_hC : IsPhotonCtLeg hκh C j) (hext : ExternalsAttached C) :
    fermionSign C = 1 := by
  have hX := fv_eq_gaugeFv_of_photonCt hgh hκg hκh
  have hσ := fst_of_photonCt hgh hκg hκh hext
  have hcard : Fintype.card (Wick.FermionVertex κ) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨gaugeFv hκg, hX⟩
  have hswap : C.1.1 = Equiv.swap (.inl 0) (.inr (gaugeFv hκg)) := by
    ext1 x
    rcases x with i | t
    · rw [Subsingleton.elim i 0, hσ.1, Equiv.swap_apply_left]
    · rw [hX t, hσ.2, Equiv.swap_apply_right]
  rw [fermionSign, hcard, hswap, Equiv.Perm.sign_swap Sum.inl_ne_inr]
  simp

end IsPhotonCtLeg

end Contractions

/-! ### The sum over the connected contractions -/

section Sum

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2}

/-- The photon pairing of a photon-leg contraction: `A(z)` with the photon field `j` of the
counterterm, and its other photon field with that of the gauge vertex. -/
def photonCtPairing (hκg : κ g = .gauge) (hκh : κ h = .photonCt) (j : Fin 2) :
    Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  Equiv.swap (.inl 0) (.inr (photonCtPs hκh j)) *
    Equiv.swap (.inr (gaugePs hκg)) (.inr (photonCtPs hκh (otherIdx j)))

variable (hgh : g ≠ h) (hκg : κ g = .gauge) (hκh : κ h = .photonCt)
include hgh hκg hκh

/-- The photon pairing is a fixed-point-free involution. -/
theorem photonCtPairing_involutive (j : Fin 2) (x : Fin 1 ⊕ Wick.PhotonSlot κ) :
    photonCtPairing hκg hκh j (photonCtPairing hκg hκh j x) = x ∧
      photonCtPairing hκg hκh j x ≠ x := by
  have hinj := photonCtPs_injective hκh
  have hg0 := gaugePs_ne_photonCtPs hgh hκg hκh
  have hj : photonCtPs hκh j ≠ photonCtPs hκh (otherIdx j) := hinj.ne (otherIdx_ne j).symm
  refine swap_mul_swap_involutive Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr
    (fun h' => (hg0 j) (Sum.inr_injective h').symm) (fun h' => hj (Sum.inr_injective h'))
    (fun h' => hg0 _ (Sum.inr_injective h')) (fun y => ?_) x
  rcases y with i | s
  · exact Or.inl (by rw [Subsingleton.elim i 0])
  · right
    rcases ps_cases_photonCt hgh hκg hκh s with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    all_goals
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      all_goals first
        | exact Or.inl rfl
        | exact Or.inr (Or.inr rfl)

/-- The photon-leg contraction with the external photon at the photon field `j`. -/
def photonCtLeg (j : Fin 2) : Contraction 1 1 κ :=
  ⟨(Equiv.swap (.inl 0) (.inr (gaugeFv hκg)), photonCtPairing hκg hκh j),
    photonCtPairing_involutive hgh hκg hκh j⟩

/-- The externals of `photonCtLeg j` are attached. -/
theorem externalsAttached_photonCtLeg (j : Fin 2) :
    ExternalsAttached (photonCtLeg hgh hκg hκh j) := by
  refine ⟨fun i k => ?_, photon_attached_of_one⟩
  rw [Subsingleton.elim i 0]
  change Equiv.swap (Sum.inl 0 : Fin 1 ⊕ Wick.FermionVertex κ) (.inr (gaugeFv hκg)) (.inl 0) ≠ _
  rw [Equiv.swap_apply_left]
  exact Sum.inr_ne_inl

/-- `photonCtLeg j` contracts the external photon with the photon field `j`. -/
theorem isPhotonCtLeg_photonCtLeg (j : Fin 2) :
    IsPhotonCtLeg hκh (photonCtLeg hgh hκg hκh j) j := by
  change photonCtPairing hκg hκh j (.inl 0) = _
  rw [photonCtPairing, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr
    Sum.inl_ne_inr, Equiv.swap_apply_left]

/-- A photon-leg contraction is determined by the photon field of the counterterm contracted with
the external photon. -/
theorem IsPhotonCtLeg.eq_photonCtLeg {C : Contraction 1 1 κ} {j : Fin 2}
    (hC : IsPhotonCtLeg hκh C j) (hext : ExternalsAttached C) : C = photonCtLeg hgh hκg hκh j := by
  have hX := fv_eq_gaugeFv_of_photonCt hgh hκg hκh
  have hσ := fst_of_photonCt hgh hκg hκh hext
  have hC' := isPhotonCtLeg_photonCtLeg hgh hκg hκh j
  apply Subtype.ext
  apply Prod.ext
  · ext1 x
    change C.1.1 x = Equiv.swap (Sum.inl 0 : Fin 1 ⊕ Wick.FermionVertex κ) (.inr (gaugeFv hκg)) x
    rcases x with i | t
    · rw [Subsingleton.elim i 0, hσ.1, Equiv.swap_apply_left]
    · rw [hX t, hσ.2, Equiv.swap_apply_right]
  · ext1 x
    rcases x with i | s
    · rw [Subsingleton.elim i 0, hC, hC']
    · have key : ∀ C' : Contraction 1 1 κ, IsPhotonCtLeg hκh C' j →
          C'.1.2 (.inr s) = (if s = gaugePs hκg then Sum.inr (photonCtPs hκh (otherIdx j))
            else if s = photonCtPs hκh j then Sum.inl 0 else Sum.inr (gaugePs hκg) :
              Fin 1 ⊕ Wick.PhotonSlot κ) := by
        intro C' hC''
        have hg0 := gaugePs_ne_photonCtPs hgh hκg hκh
        split_ifs with h1 h2
        · rw [h1, hC''.snd_gaugePs hgh hκg hκh]
        · rw [h2, hC''.snd_photonCtPs hκh]
        · obtain ⟨k, rfl⟩ : ∃ k, s = photonCtPs hκh k := by
            rcases ps_cases_photonCt hgh hκg hκh s with h' | h' | h'
            · exact absurd h' h1
            · exact ⟨0, h'⟩
            · exact ⟨1, h'⟩
          rw [eq_otherIdx_of_ne j k (fun h'' => h2 (congrArg _ h'')),
            ← hC''.snd_gaugePs hgh hκg hκh, (C'.2 _).1]
      rw [key C hC, key _ hC']

/-- **The connected contractions of a gauge vertex and a photon counterterm that are not 1PI**:
the two photon-leg contractions, of sign `+1`, each with half of the photon-leg counterterm. -/
theorem sum_nonOnePI_photonCt (P : Params) [Fintype (Contraction 1 1 κ)]
    [DecidablePred fun C : Contraction 1 1 κ =>
      (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C]
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
        (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C),
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
          (-I * ((P.δ₃ * (Minkowski.dot (p' - p) (p' - p) * Minkowski.metric μ ρ -
            (p' - p) μ * (p' - p) ρ) : ℝ) : ℂ)) := by
  classical
  have h0 := isPhotonCtLeg_photonCtLeg hgh hκg hκh 0
  have h1 := isPhotonCtLeg_photonCtLeg hgh hκg hκh 1
  have he0 := externalsAttached_photonCtLeg hgh hκg hκh 0
  have he1 := externalsAttached_photonCtLeg hgh hκg hκh 1
  have hfilter : (Finset.univ : Finset (Contraction 1 1 κ)).filter
      (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C) =
      {photonCtLeg hgh hκg hκh 0, photonCtLeg hgh hκg hκh 1} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hext, hconn⟩, -⟩
      obtain ⟨j, hj⟩ := exists_isPhotonCtLeg hgh hκg hκh hext hconn
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact Or.inl (hj.eq_photonCtLeg hgh hκg hκh hext)
      · exact Or.inr (hj.eq_photonCtLeg hgh hκg hκh hext)
    · rintro (rfl | rfl)
      · exact h0.connected_not_isOnePI hgh hκg hκh he0
      · exact h1.connected_not_isOnePI hgh hκg hκh he1
  have hdist : photonCtLeg hgh hκg hκh 0 ≠ photonCtLeg hgh hκg hκh 1 := fun h' => by
    have h'' : IsPhotonCtLeg hκh (photonCtLeg hgh hκg hκh 0) 1 := h' ▸ h1
    unfold IsPhotonCtLeg at h0 h''
    rw [h0] at h''
    exact absurd (photonCtPs_injective hκh (Sum.inr_injective h'')) (by decide)
  rw [hfilter, Finset.sum_pair hdist, h0.fermionSign_eq hgh hκg hκh he0,
    h1.fermionSign_eq hgh hκg hκh he1, h0.contractionValue_eq hgh hκg hκh P he0,
    h1.contractionValue_eq hgh hκg hκh P he1]
  simp only [Int.cast_one, one_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [photonCtTerm]
  ring

end Sum

end QED.WickModel

end
