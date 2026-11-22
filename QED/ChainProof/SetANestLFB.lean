/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLFA

/-!
# Set (a), obligation (N): the nested form of the fermion counterterm class `FB`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form
`QED.ChainProof.SetANest.LoopNested` of `QED.ChainProof.SetALink.repFB` (the level-`0` `δ₂, δ_m`
counterterm at the vertex `5` on the loop line `u → w` of the bubble, loop `3 → 5 → 4 → 3`).

* Routing: `fbMom`, with `ℓ 0 = q` on the two loop lines `4 → 5`, `5 → 3` through the
  counterterm and `ℓ 1 = ℓ` the photon momentum (lines `0 → 1`: `p + ℓ`, `1 → 2`: `p' + ℓ`,
  `3 → 4`: `q + ℓ`, photons `0 → 4`: `-ℓ`, `2 → 3`: `ℓ`), with the chords `0 → 1`, `5 → 3` at
  the frozen loop momenta `fbMat ℓ + (p, 0)`.
* Wick: **`fb_routedIntegrand`**: the integrand in the routing `fbMom` is
  `outerInner lOuter fbInner`, `fbInner(ℓ, q)` the integrand of the class `F1` at `(-ℓ, ℓ)`
  (`QED.GradedProof.VP2.f1_integrand`) at the loop momentum `q + ℓ`.
* `efi_fbInner`: `∫_D fbInner(ℓ, ·) = val0(F1)(-ℓ)`; `fbInner_eq`: it is the block-summed
  inserted bubble with the insertion line at `q` and the other line at `ℓ + q`.
* **`loopNested_repFB_of_bound`**: under `IntHypA` and the inner bound `OneLoopInnerBound a b`
  of that inserted bubble (`0 ≤ a < 9`, `3 < b`), `FB` is in nested form with
  `X(k)^{ab} = (1/i) val0(F1)(-k)^{ab}`.
* **`fermion_group_sum`**: the `fermionCt` group identity of
  `QED.ChainProof.SetANest.hsum_of_groups`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.SetALink QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### Lines and routing -/

/-- The fermion lines of `repFB`, by head `1, …, 5` (tails `0, 1, 5, 3, 4`). -/
def fbL : Fin 5 → FermionLine repFB :=
  ![⟨fv kF 1, by decide +kernel⟩, ⟨fv kF 2, by decide +kernel⟩, ⟨fv kF 3, by decide +kernel⟩,
    ⟨fv kF 4, by decide +kernel⟩, ⟨fv kF 5, by decide +kernel⟩]

/-- The photon lines `0 — 4`, `2 — 3` of `repFB`. -/
def fbP : Fin 2 → PhotonLine repFB :=
  ![⟨pg kF 0, by decide +kernel⟩, ⟨pg kF 2, by decide +kernel⟩]

theorem fbL_bijective : Function.Bijective fbL := by decide +kernel

theorem fbP_bijective : Function.Bijective fbP := by decide +kernel

theorem fb_sum_line {M : Type*} [AddCommMonoid M] (g : Line repFB → M) :
    ∑ f, g f = g (.inl (fbL 0)) + g (.inl (fbL 1)) + g (.inl (fbL 2)) + g (.inl (fbL 3)) +
      g (.inl (fbL 4)) + (g (.inr (fbP 0)) + g (.inr (fbP 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ fbL_bijective).sum_comp,
    ← (Equiv.ofBijective _ fbP_bijective).sum_comp, Fin.sum_univ_five, Fin.sum_univ_two]
  rfl

theorem fb_ends : (Line.ends (.inl (fbL 0) : Line repFB)) = (0, 1) ∧
    (Line.ends (.inl (fbL 1) : Line repFB)) = (1, 2) ∧
    (Line.ends (.inl (fbL 2) : Line repFB)) = (5, 3) ∧
    (Line.ends (.inl (fbL 3) : Line repFB)) = (3, 4) ∧
    (Line.ends (.inl (fbL 4) : Line repFB)) = (4, 5) ∧
    (Line.ends (.inr (fbP 0) : Line repFB)) = (0, 4) ∧
    (Line.ends (.inr (fbP 1) : Line repFB)) = (2, 3) := by decide +kernel

theorem fb_ext (v : Fin 6) :
    ((∃ t : Wick.FermionVertex kF, t.1 = v ∧ repFB.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kF, a.1 = v ∧ repFB.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kF, t.1 = v ∧ repFB.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- **The nested routing of `FB`**: `ℓ 0 = q` on the loop lines `4 → 5`, `5 → 3`, `ℓ 1 = ℓ` the
photon momentum; lines `0 → 1`: `p + ℓ`, `1 → 2`: `p + k + ℓ`, `3 → 4`: `q + ℓ`, photon
`0 → 4`: `-ℓ`, photon `2 → 3`: `ℓ`. -/
def fbMom (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repFB) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p + ℓ 1
  | 2 => p + kext + ℓ 1
  | 3 => ℓ 0
  | 4 => ℓ 0 + ℓ 1
  | 5 => ℓ 0
  | 6 => -ℓ 1
  | _ => ℓ 1

theorem fbMom_apply (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    fbMom p kext ℓ (.inl (fbL 0)) = p + ℓ 1 ∧ fbMom p kext ℓ (.inl (fbL 1)) = p + kext + ℓ 1 ∧
      fbMom p kext ℓ (.inl (fbL 2)) = ℓ 0 ∧ fbMom p kext ℓ (.inl (fbL 3)) = ℓ 0 + ℓ 1 ∧
      fbMom p kext ℓ (.inl (fbL 4)) = ℓ 0 ∧ fbMom p kext ℓ (.inr (fbP 0)) = -ℓ 1 ∧
      fbMom p kext ℓ (.inr (fbP 1)) = ℓ 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isConserved_fbMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) : IsConserved repFB pOut pIn kIn (fbMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4, g0, g1⟩ := fb_ends
  obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := fbMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  obtain ⟨x0, x1, x2⟩ := fb_ext v
  rw [inflow, fb_sum_line, QED.TwoLoop.Insertion.externalMomentum_one_one, hmom]
  simp only [e0, e1, e2, e3, e4, g0, g1, n0, n1, n2, n3, n4, n5, n6, x0, x1, x2]
  fin_cases v
  all_goals simp

theorem fb_isChord_iff : ∀ f : Line repFB,
    IsChord f ↔ f = .inl (fbL 0) ∨ f = .inl (fbL 2) := by
  decide +kernel

theorem fb_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (fbL 0) : Line repFB) = ℓ 0 ∧
      chordMomentum ℓ (.inl (fbL 2) : Line repFB) = ℓ 1 := by
  have h0 : (Finset.univ.filter fun g : Line repFB =>
      IsChord g ∧ g.label < (Line.label (.inl (fbL 0) : Line repFB))).card = 0 := by
    decide +kernel
  have h1 : (Finset.univ.filter fun g : Line repFB =>
      IsChord g ∧ g.label < (Line.label (.inl (fbL 2) : Line repFB))).card = 1 := by
    decide +kernel
  refine ⟨?_, ?_⟩
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by convert h0; rfl)
    · exact absurd (by convert (show 0 < 2 by norm_num) using 2; convert h0) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by convert h1; rfl)
    · exact absurd (by convert (show 1 < 2 by norm_num) using 2; convert h1) h

/-- The unimodular change of loop momenta of `FB`: `ℓ ↦ (ℓ 1, ℓ 0)`. -/
def fbMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem isUnit_det_fbMat : IsUnit fbMat.det := by
  rw [Matrix.det_fin_two]
  simp [fbMat]

/-- The chords of `FB` carry the frozen loop momenta at `fbMat ℓ + (p, 0)`. -/
theorem fb_hchord (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repFB)
    (hf : IsChord f) : fbMom p kext ℓ f =
      chordMomentum ((fun s => ∑ r, fbMat s r • ℓ r) + ![p, 0]) f := by
  obtain ⟨c0, c1⟩ := fb_chordMomentum ((fun s => ∑ r, fbMat s r • ℓ r) + ![p, 0])
  obtain ⟨n0, -, n2, -⟩ := fbMom_apply p kext ℓ
  rcases (fb_isChord_iff f).mp hf with rfl | rfl
  · rw [c0, n0]
    simp [fbMat, Fin.sum_univ_two]
    abel
  · rw [c1, n2]
    simp [fbMat, Fin.sum_univ_two]

/-! ### The amplitude -/

theorem fb_prod_fermionLine {M : Type*} [CommMonoid M] (g : FermionLine repFB → M) :
    ∏ f, g f = g (fbL 0) * g (fbL 1) * g (fbL 2) * g (fbL 3) * g (fbL 4) := by
  rw [← (Equiv.ofBijective _ fbL_bijective).prod_comp, Fin.prod_univ_five]
  rfl

theorem fb_prod_photonLine {M : Type*} [CommMonoid M] (g : PhotonLine repFB → M) :
    ∏ f, g f = g (fbP 0) * g (fbP 1) := by
  rw [← (Equiv.ofBijective _ fbP_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem fb_tails : (fbL 0).tail = fv kF 0 ∧ (fbL 1).tail = fv kF 1 ∧
    (fbL 2).tail = fv kF 5 ∧ (fbL 3).tail = fv kF 3 ∧ (fbL 4).tail = fv kF 4 := by
  decide +kernel

theorem fb_vals : (fbL 0).1 = fv kF 1 ∧ (fbL 1).1 = fv kF 2 ∧ (fbL 2).1 = fv kF 3 ∧
    (fbL 3).1 = fv kF 4 ∧ (fbL 4).1 = fv kF 5 ∧ (fbP 0).1 = pg kF 0 ∧ (fbP 1).1 = pg kF 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fb_heads : (fbP 0).head = pg kF 4 ∧ (fbP 1).head = pg kF 3 := by decide +kernel

theorem fb_cond (α β : Wick.FermionVertex kF → Fin 4) (lor : Wick.PhotonSlot kF → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repFB.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repFB.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repFB.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (lor (pg kF 1) = μ 0 ∧ (α (fv kF 2) = αOut 0 ∧ β (fv kF 0) = βIn 0)) := by
  have h0 : ∀ t, repFB.1.1 (.inl 0) = .inr t ↔ t = fv kF 2 := by decide +kernel
  have h1 : ∀ t, repFB.1.1 (.inr t) = .inl 0 ↔ t = fv kF 0 := by decide +kernel
  have h2 : ∀ a, repFB.1.2 (.inl 0) = .inr a ↔ a = pg kF 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h0, h1, h2, forall_eq]
  tauto

/-- The splitting of the fermion fields of `kF` into the open line `2, 1, 0` and the loop
`4, 3, 5`. -/
noncomputable def fbSplit : Wick.FermionVertex kF ≃ Fin 3 ⊕ Fin 3 :=
  Equiv.ofBijective
    (fun t => (![.inl 2, .inl 1, .inl 0, .inr 1, .inr 0, .inr 2] : Fin 6 → _) t.1)
    (by decide +kernel)

/-- The open-line chain of `FB`. -/
noncomputable def fbChain (P : Params) (m : ℝ) (kk : Line repFB → Fin 4 → ℝ) (μ l2 l0 : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma l2 * QED.OneLoop.electronPropagator m P.ε (kk (.inl (fbL 1))) * Dirac.gamma μ *
    QED.OneLoop.electronPropagator m P.ε (kk (.inl (fbL 0))) * Dirac.gamma l0

/-- The loop trace of `FB`, with the counterterm matrix at the vertex `5`. -/
noncomputable def fbLoop (P : Params) (M d₂ dm : ℝ) (kk : Line repFB → Fin 4 → ℝ)
    (l3 l4 : Fin 4) : ℂ :=
  Matrix.trace (Dirac.gamma l4 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (fbL 3))) *
    Dirac.gamma l3 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (fbL 2))) *
    QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M (kk (.inl (fbL 4))) *
    QED.OneLoop.electronPropagator M P.ε (kk (.inl (fbL 4))))

theorem fb_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (f : F) (pIn kIn : Fin 1 → Fin 4 → ℝ) (kk : Line repFB → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionAmplitude P Φ D repFB (fcFlav Φ f) 0 pIn kIn kk αOut βIn μ =
      (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 *
        ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 0))) l0 l4 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 1))) l2 l3 *
          fbLoop P (Φ.mass f) (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) kk l3 l4 *
          fbChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := fb_tails
  obtain ⟨g0, g1⟩ := fb_heads
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := fb_vals
  have hpsi : QED.WickModel.psiMomentum₂ repFB pIn kk ⟨5, by decide⟩ = kk (.inl (fbL 4)) :=
    QED.TwoLoop.Relabel.psiMomentum₂_of_isRight (by decide +kernel)
  unfold Graded.contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex kF → Fin 4, ∑ β : Wick.FermionVertex kF → Fin 4,
      ∑ lor : Wick.PhotonSlot kF → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [fb_cond, Fin.prod_univ_six, fb_prod_fermionLine, fb_prod_photonLine, t0, t1, t2,
    t3, t4, g0, g1, v0, v1, v2, v3, v4, v5, v6,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kF 0 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kF 1 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kF 2 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kF 3 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kF 4 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _
      (show kF 5 = .fermionCt from rfl), show kF 5 = .fermionCt from rfl,
    dite_false, reduceCtorEq, Pi.zero_apply, zero_add, mul_one, ite_and_eq_mul_ite]
  have hfl : ∀ t : Fin 6, ∀ h, fcFlav Φ f ⟨t, h⟩ = if t.val < 3 then Φ.openLine else f :=
    fun _ _ => rfl
  simp only [fv, pg, hfl, Fin.isValue, Fin.val_one, Fin.val_two, hpsi]
  simp only [show ((5 : Fin 6) : ℕ) < 3 ↔ False by decide,
    show ((4 : Fin 6) : ℕ) < 3 ↔ False by decide,
    show ((3 : Fin 6) : ℕ) < 3 ↔ False by decide, show (1 : ℕ) < 3 ↔ True by decide,
    show (2 : ℕ) < 3 ↔ True by decide, ite_true, ite_false]
  set K : ℂ := (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 with hK
  have hR : K * ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 0))) l0 l4 *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 1))) l2 l3 *
      fbLoop P (Φ.mass f) (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) kk l3 l4 *
      fbChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) =
      ∑ lor : Wick.PhotonSlot kF → Fin 4,
      (if lor ⟨1, ⟨0, by decide⟩⟩ = μ 0 then (1 : ℂ) else 0) * (K *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 0))) (lor ⟨0, ⟨0, by decide⟩⟩)
          (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 1))) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨3, ⟨0, by decide⟩⟩) *
        fbLoop P (Φ.mass f) (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) kk
          (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        fbChain P (Φ.mass Φ.openLine) kk (μ 0) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨0, ⟨0, by decide⟩⟩) (αOut 0) (βIn 0))) := by
    rw [QED.TwoLoop.Insertion.sum_pi_five (x₁ := (⟨1, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kF))
      (x₂ := ⟨4, ⟨0, by decide⟩⟩) (x₃ := ⟨3, ⟨0, by decide⟩⟩) (x₄ := ⟨0, ⟨0, by decide⟩⟩)
      (x₅ := ⟨2, ⟨0, by decide⟩⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
    simp +decide only [ite_false, ite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [hR]
  refine Finset.sum_congr rfl fun lor _ => ?_
  by_cases hL : lor ⟨1, ⟨0, by decide⟩⟩ = μ 0
  · have h := sum_spinor_chain3_loop3 fbSplit (x₁ := ⟨2, by decide⟩) (x₂ := ⟨1, by decide⟩)
      (x₃ := ⟨0, by decide⟩) (y₁ := ⟨4, by decide⟩) (y₂ := ⟨3, by decide⟩)
      (y₃ := ⟨5, by decide⟩) rfl rfl rfl rfl rfl rfl
      (K * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 0)))
        (lor ⟨0, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (fbP 1)))
        (lor ⟨2, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨0, by decide⟩⟩))
      (Dirac.gamma (lor ⟨2, ⟨0, by decide⟩⟩)) (Dirac.gamma (μ 0))
      (Dirac.gamma (lor ⟨0, ⟨0, by decide⟩⟩))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (fbL 1))))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (fbL 0))))
      (Dirac.gamma (lor ⟨4, ⟨0, by decide⟩⟩)) (Dirac.gamma (lor ⟨3, ⟨0, by decide⟩⟩))
      (QED.TwoLoop.Insertion.fermionCtMatrix (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0)
        (Φ.mass f) (kk (.inl (fbL 4))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (fbL 3))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (fbL 2))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (fbL 4)))) (αOut 0) (βIn 0)
    simp only [hL, ite_true, one_mul]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hK]
      simp only [QED.TwoLoop.Insertion.fermionCtMatrix]
      push_cast
      by_cases ha : α ⟨2, by decide⟩ = αOut 0 <;> by_cases hb : β ⟨0, by decide⟩ = βIn 0 <;>
        simp only [ha, hb, and_true, and_false, ite_true, ite_false] <;> ring
    · unfold fbLoop fbChain
      ring
  · simp only [hL, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The preserved flavourings -/

theorem fb_perm : repFB.1.1 (.inl 0) = .inr (fv kF 2) ∧
    repFB.1.1 (.inr (fv kF 2)) = .inr (fv kF 1) ∧
    repFB.1.1 (.inr (fv kF 1)) = .inr (fv kF 0) ∧
    repFB.1.1 (.inr (fv kF 0)) = .inl 0 ∧
    repFB.1.1 (.inr (fv kF 3)) = .inr (fv kF 5) ∧
    repFB.1.1 (.inr (fv kF 4)) = .inr (fv kF 3) ∧
    repFB.1.1 (.inr (fv kF 5)) = .inr (fv kF 4) := by decide +kernel

theorem fb_open : ∀ i, ¬ repFB.1.1.SameCycle (.inl i) (.inr (fv kF 3)) := by decide +kernel

theorem fb_all : ∀ x, (∃ i, repFB.1.1.SameCycle x (.inl i)) ∨
    repFB.1.1.SameCycle x (.inr (fv kF 3)) := by
  decide +kernel

/-- **The flavourings preserved by `repFB`**: the open line has the open-line flavour, the loop
one flavour. -/
theorem fb_preserves_iff {F : Type} (Φ : Lepton.Flavors F) (φ : Graded.Flavoring F kF) :
    Graded.Preserves Φ repFB φ ↔ φ = fcFlav Φ (φ (fv kF 3)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := fb_perm
  constructor
  · intro hφ
    have h0 := hφ (.inl 0)
    have h1 := hφ (.inr (fv kF 2))
    have h2 := hφ (.inr (fv kF 1))
    have h5 := hφ (.inr (fv kF 4))
    have h6 := hφ (.inr (fv kF 5))
    rw [s0] at h0
    rw [s1] at h1
    rw [s2] at h2
    rw [s5] at h5
    rw [s6] at h6
    simp only [Graded.fermionFlavor] at h0 h1 h2 h5 h6
    funext t
    rcases kF_fv_cases t with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [fcFlav, fv] <;> norm_num
    · exact h2.trans (h1.trans h0)
    · exact h1.trans h0
    · exact h0
    · exact h5.symm
    · exact (h5.trans h6).symm
  · intro h a
    rw [h]
    rcases a with i | t
    · rw [Fin.fin_one_eq_zero i, s0]
      simp [Graded.fermionFlavor, fcFlav, fv]
    · rcases kF_fv_cases t with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s3]; simp [Graded.fermionFlavor, fcFlav, fv]
      · rw [s2]; simp [Graded.fermionFlavor, fcFlav, fv]
      · rw [s1]; simp [Graded.fermionFlavor, fcFlav, fv]
      · rw [s4]; simp [Graded.fermionFlavor, fcFlav, fv]
      · rw [s5]; simp [Graded.fermionFlavor, fcFlav, fv]
      · rw [s6]; simp [Graded.fermionFlavor, fcFlav, fv]

/-- **The regulated amplitude of `repFB`** is the sum over the loop flavour of its coefficient
times the amplitude. -/
theorem fb_regulatedAmplitude (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (kk : Line repFB → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.regulatedAmplitude P Φ D repFB 0 pIn kIn kk αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) *
        Graded.contractionAmplitude P Φ D repFB (fcFlav Φ f) 0 pIn kIn kk αOut βIn μ := by
  classical
  unfold Graded.regulatedAmplitude
  refine Finset.sum_nbij' (fun φ => φ (fv kF 3)) (fcFlav Φ) (fun _ _ => Finset.mem_univ _)
    (fun f _ => ?_) (fun φ hφ => ?_) (fun f _ => ?_) (fun φ hφ => ?_)
  · rw [Finset.mem_filter, fb_preserves_iff]
    exact ⟨Finset.mem_univ _, by simp [fcFlav, fv]⟩
  · exact ((fb_preserves_iff Φ φ).mp (Finset.mem_filter.mp hφ).2).symm
  · simp [fcFlav, fv]
  · have hp := (Finset.mem_filter.mp hφ).2
    rw [loopWeight_eq_of_one_loop Φ hp (fv kF 3) fb_open fb_all]
    conv_lhs => rw [(fb_preserves_iff Φ φ).mp hp]
    simp [fcFlav, fv]

/-! ### The Wick factorization -/

/-- The inner integrand of `FB`: the integrand of the class `F1` at `(-ℓ, ℓ)`, loop momentum
shifted to `q + ℓ`. -/
noncomputable def fbInner (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ q : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repF1 0
    ![] ![-ℓ, -(-ℓ)] (QED.GradedProof.VP2.f1Mom (-ℓ) (q + ℓ)) ![] ![] ![a, b]

/-- **The Wick factorization of `FB`**: in the nested routing, the integrand of the value of
`repFB` is the outer factor times the inner integrand of `F1`, summed over the photon slot. -/
theorem fb_routedIntegrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    routedIntegrand P Φ D repFB 0 2 (fun _ => p) (fun _ => p' - p) (fbMom p (p' - p) ℓ)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (fbInner P Φ D) ℓ := by
  have hq' : -ℓ 1 + (ℓ 0 + ℓ 1) = ℓ 0 := by abel
  have hp : p + (p' - p) + ℓ 1 = p' + ℓ 1 := by abel
  simp only [routedIntegrand, fb_regulatedAmplitude, fb_amplitude, outerInner, fbInner,
    QED.GradedProof.VP2.f1_integrand P Φ D id (fun _ => ⟨rfl, rfl⟩), lOuter,
    QED.ChainProof.SetANestV.nestOuter, ← QED.GradedProof.VP2.trace_ins_smul,
    QED.GradedProof.VP2.zk_true, QED.GradedProof.VP2.zk_false, QED.GradedProof.VP2.kF,
    QED.TwoLoop.Insertion.vertexChain, fbLoop, fbChain,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hq', id]
  simp only [show fbMom p (p' - p) ℓ (.inl (fbL 0)) = p + ℓ 1 from rfl,
    show fbMom p (p' - p) ℓ (.inl (fbL 1)) = p' + ℓ 1 from hp,
    show fbMom p (p' - p) ℓ (.inl (fbL 2)) = ℓ 0 from rfl,
    show fbMom p (p' - p) ℓ (.inl (fbL 3)) = ℓ 0 + ℓ 1 from rfl,
    show fbMom p (p' - p) ℓ (.inl (fbL 4)) = ℓ 0 from rfl,
    show fbMom p (p' - p) ℓ (.inr (fbP 0)) = -ℓ 1 from rfl,
    show fbMom p (p' - p) ℓ (.inr (fbP 1)) = ℓ 1 from rfl,
    Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm_out_two]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl
      fun ρ _ => ?_
  rw [QED.TwoLoop.Insertion.photonPropagator_neg', QED.TwoLoop.Insertion.photonPropagator_neg']
  push_cast
  ring

/-! ### The inner integrand -/

/-- **The energy-first integral of the inner integrand of `FB`** is the value of the class `F1`
at `(-ℓ, ℓ)`. -/
theorem efi_fbInner (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.energyFirstIntegral (fun q => fbInner P Φ D ℓ q a b) =
      QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repF1 := by
  have hc := QED.GradedProof.VP2.f1_isChord_iff
  unfold QED.GradedProof.VP2.val0 Graded.contractionValue
  rw [QED.TwoLoop.Insertion.loopCount_eq_one_of_unique hc]
  simp only [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc
    (QED.GradedProof.VP2.f1Mom (-ℓ)) (QED.GradedProof.VP2.f1_isConserved (-ℓ))
    (fun q => (QED.GradedProof.VP2.f1Mom_apply (-ℓ) q).1)]
  rw [QED.TwoLoop.jointEnergyFirstIntegral_one_eq (fun q => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
    Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repF1 0 ![] ![-ℓ, -(-ℓ)]
      (QED.GradedProof.VP2.f1Mom (-ℓ) q) ![] ![] ![a, b])]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_add_right_eq_self _ ℓ]
  simp only [fbInner, mul_one]

/-- **The inner integrand of `FB`** is the block-summed inserted bubble with the insertion line
at `q` and the other line at `1 • ℓ + q`. -/
theorem fbInner_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    fbInner P Φ D = fun k q a b => ∑ f, (Φ.coeff f : ℂ) * (QED.GradedProof.VP2.kF P.e *
      QED.GradedProof.VP2.insG (Dirac.gamma a) (Dirac.gamma b)
        ((fun r => P.e ^ 2 * D.d₂ r 0) (rep f)) ((fun r => P.e ^ 2 * D.dm r 0) (rep f))
        (Φ.mass f) P.ε (QED.GradedProof.VP2.zk ((1 : ℝ) • k) true q)
        (QED.GradedProof.VP2.zk ((1 : ℝ) • k) false q)) := by
  funext ℓ q a b
  rw [fbInner, QED.GradedProof.VP2.f1_integrand P Φ D rep hD]
  simp only [QED.GradedProof.VP2.zk_true, QED.GradedProof.VP2.zk_false, one_smul, add_comm q ℓ,
    neg_add_cancel_left]

/-! ### The nested form -/

/-- **The nested form of `FB`, given the inner bound.** Under the hypotheses `IntHypA` of (HA₀)
and the inner bound `OneLoopInnerBound a b` (`0 ≤ a < 9`, `3 < b`) of the block-summed inserted
bubble of `fbInner_eq`, the class `FB` is in nested form (`LoopNested`) with the photon tensor
`X(k)^{ab} = (1/i) val0(F1)(-k)^{ab}`. -/
theorem loopNested_repFB_of_bound (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep)
    (p' p : Fin 4 → ℝ) {a₀ b₀ : ℝ} (ha0 : 0 ≤ a₀) (ha : a₀ < 9) (hb : 3 < b₀)
    (hG : OneLoopInnerBound a₀ b₀ fun k q a b => ∑ f, (Φ.coeff f : ℂ) *
      (QED.GradedProof.VP2.kF P.e *
        QED.GradedProof.VP2.insG (Dirac.gamma a) (Dirac.gamma b)
          ((fun r => P.e ^ 2 * D.d₂ r 0) (rep f)) ((fun r => P.e ^ 2 * D.dm r 0) (rep f))
          (Φ.mass f) P.ε (QED.GradedProof.VP2.zk ((1 : ℝ) • k) true q)
          (QED.GradedProof.VP2.zk ((1 : ℝ) • k) false q))) :
    LoopNested P Φ D repFB
      (fun k a b => (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repF1)
      p' p := by
  rw [← fbInner_eq P Φ D rep fun f => (hH.hD f).2] at hG
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_fbMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  have hR : ∀ μ i j : Fin 4, (fun ℓ => routedIntegrand P Φ D repFB 0 2 (fun _ => p)
      (fun _ => p' - p) (fbMom p (p' - p) ℓ) (fun _ => i) (fun _ => j) (fun _ => μ)) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) (fbInner P Φ D) :=
    fun μ i j => funext fun ℓ => fb_routedIntegrand P Φ D p' p μ i j ℓ
  have h := loopNested_of_lOuter P Φ D repFB p' p hH.hε ha0 ha hb hG (fun μ i j => ?_)
    (fun μ i j => ?_)
  · have e : (fun k a b =>
        (1 / I) * QED.OneLoop.energyFirstIntegral fun q => fbInner P Φ D k q a b) =
        fun k a b => (1 / I) *
          QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repF1 :=
      funext fun k => funext fun a => funext fun b => by rw [efi_fbInner]
    rwa [e] at h
  · rw [contractionValue_eq_of_routing P Φ D repFB 0 loopCount_repFB (fbMom p (p' - p)) hcons
      fbMat isUnit_det_fbMat ![p, 0] (fb_hchord p (p' - p)), hR]
  · rw [← hR]
    exact jointEnergyFirstIntegrable_of_routing P Φ D repFB 0 loopCount_repFB
      (fbMom p (p' - p)) hcons fbMat isUnit_det_fbMat ![p, 0] (fb_hchord p (p' - p)) _ _ _
      (classIntA_repFB P Φ D rep hH (fun _ => p') (fun _ => p) (fun _ => p' - p) hmom _ _ _)

/-- **The `fermionCt` group identity** for `hsum_of_groups`: the photon tensors of `FA`
(`loopNested_repFA_of_bound`) and `FB` (`loopNested_repFB_of_bound`) sum to `(1/i)` times the
values of `F0` and `F1` at `-ℓ`. -/
theorem fermion_group_sum (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repF0 +
        (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repF1 =
      (1 / I) * (QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repF0 +
        QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repF1) := by
  ring

end QED.ChainProof.SetANest

end
