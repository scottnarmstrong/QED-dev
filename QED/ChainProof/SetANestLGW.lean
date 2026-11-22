/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLGen
public import QED.ChainProof.SetANestLBubble
public import QED.ChainProof.SetANestLRoute
public import QED.ChainProof.SetALinkIntG
public import QED.GradedProof.VP2ClassG0
public import QED.TwoLoop.EnumerationDecide
public import QED.TwoLoop.IntegrableOrderFiveCt
public import QED.Integration.EnergyFirstShift
public import QED.TwoLoop.JointIntegral

/-!
# Set (a), obligation (N): the nested form of the `gaugeCt` class `GW`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form
`QED.ChainProof.SetANest.LoopNested` of `QED.ChainProof.SetALink.repGW` (the level-`0` `δ₁`
counterterm at the vertex `w = 4` of the bubble, the field `y` paired with `c = 0`).

* Routing: `gwMom`, with `ℓ 0 = q` on the loop line `3 → 4` and `ℓ 1 = ℓ` the photon momentum
  (lines `0 → 1`: `p + ℓ`, `1 → 2`: `p' + ℓ`, `4 → 3`: `q - ℓ`, photons `0 → 4`: `-ℓ`,
  `2 → 3`: `ℓ`), conserved (`isConserved_gwMom`), with the chords `0 → 1`, `4 → 3` at the frozen
  loop momenta `gwMat ℓ + (p, 0)` (`gw_hchord`, `gwMat` of determinant `-1`).
* Wick: the preserved flavourings are the loop flavours `f` (`gw_preserves_iff`), with weight
  `c_f` (`gw_regulatedAmplitude`); the amplitude at `f` (`gw_amplitude`) is the open chain times
  the loop trace; **`gw_routedIntegrand`**: the integrand in the routing `gwMom` is
  `outerInner lOuter gwInner`, `gwInner(ℓ, q)` the integrand of the two-photon class `G1` at
  `(-ℓ, ℓ)` (`QED.GradedProof.VP2.g1_integrand`), loop momentum shifted to `q`.
* `efi_gwInner`: `∫_D gwInner(ℓ, ·) = val0(G1)(-ℓ)`; `gwInner_eq`: it is the block-summed bubble
  `blockBubbleNeg`, which has `OneLoopInnerBound (17/2) (7/2)`.
* **`loopNested_repGW`**: under the hypotheses `IntHypA` of (HA₀) and positive masses, `GW` is in
  nested form with `X(k)^{ab} = (1/i) val0(G1)(-k)^{ab}`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.SetALink QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### Lines and routing -/

/-- The fermion lines of `repGW`, by head `1, 2, 3, 4` (tails `0, 1, 4, 3`). -/
def gwL : Fin 4 → FermionLine repGW :=
  ![⟨fv kGW 1, by decide +kernel⟩, ⟨fv kGW 2, by decide +kernel⟩, ⟨fv kGW 3, by decide +kernel⟩,
    ⟨fv kGW 4, by decide +kernel⟩]

/-- The photon lines `0 — 4`, `2 — 3` of `repGW`. -/
def gwP : Fin 2 → PhotonLine repGW :=
  ![⟨pg kGW 0, by decide +kernel⟩, ⟨pg kGW 2, by decide +kernel⟩]

theorem gwL_bijective : Function.Bijective gwL := by decide +kernel

theorem gwP_bijective : Function.Bijective gwP := by decide +kernel

theorem gw_sum_line {M : Type*} [AddCommMonoid M] (g : Line repGW → M) :
    ∑ f, g f = g (.inl (gwL 0)) + g (.inl (gwL 1)) + g (.inl (gwL 2)) + g (.inl (gwL 3)) +
      (g (.inr (gwP 0)) + g (.inr (gwP 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ gwL_bijective).sum_comp,
    ← (Equiv.ofBijective _ gwP_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem gw_ends : (Line.ends (.inl (gwL 0) : Line repGW)) = (0, 1) ∧
    (Line.ends (.inl (gwL 1) : Line repGW)) = (1, 2) ∧
    (Line.ends (.inl (gwL 2) : Line repGW)) = (4, 3) ∧
    (Line.ends (.inl (gwL 3) : Line repGW)) = (3, 4) ∧
    (Line.ends (.inr (gwP 0) : Line repGW)) = (0, 4) ∧
    (Line.ends (.inr (gwP 1) : Line repGW)) = (2, 3) := by decide +kernel

theorem gw_ext (v : Fin 5) :
    ((∃ t : Wick.FermionVertex kGW, t.1 = v ∧ repGW.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kGW, a.1 = v ∧ repGW.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kGW, t.1 = v ∧ repGW.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- **The nested routing of `GW`**: `ℓ 0 = q` on the loop line `3 → 4`, `ℓ 1 = ℓ` the photon
momentum; lines `0 → 1`: `p + ℓ`, `1 → 2`: `p + k + ℓ`, `4 → 3`: `q - ℓ`, `3 → 4`: `q`, photon
`0 → 4`: `-ℓ`, photon `2 → 3`: `ℓ`. -/
def gwMom (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repGW) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p + ℓ 1
  | 2 => p + kext + ℓ 1
  | 3 => ℓ 0 - ℓ 1
  | 4 => ℓ 0
  | 5 => -ℓ 1
  | _ => ℓ 1

theorem gwMom_apply (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    gwMom p kext ℓ (.inl (gwL 0)) = p + ℓ 1 ∧ gwMom p kext ℓ (.inl (gwL 1)) = p + kext + ℓ 1 ∧
      gwMom p kext ℓ (.inl (gwL 2)) = ℓ 0 - ℓ 1 ∧ gwMom p kext ℓ (.inl (gwL 3)) = ℓ 0 ∧
      gwMom p kext ℓ (.inr (gwP 0)) = -ℓ 1 ∧ gwMom p kext ℓ (.inr (gwP 1)) = ℓ 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isConserved_gwMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) : IsConserved repGW pOut pIn kIn (gwMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3, g0, g1⟩ := gw_ends
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := gwMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  obtain ⟨x0, x1, x2⟩ := gw_ext v
  rw [inflow, gw_sum_line, QED.TwoLoop.Insertion.externalMomentum_one_one, hmom]
  simp only [e0, e1, e2, e3, g0, g1, n0, n1, n2, n3, n4, n5, x0, x1, x2]
  fin_cases v
  all_goals simp
  all_goals abel

theorem gw_isChord_iff : ∀ f : Line repGW,
    IsChord f ↔ f = .inl (gwL 0) ∨ f = .inl (gwL 2) := by
  decide +kernel

theorem gw_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (gwL 0) : Line repGW) = ℓ 0 ∧
      chordMomentum ℓ (.inl (gwL 2) : Line repGW) = ℓ 1 := by
  have h0 : (Finset.univ.filter fun g : Line repGW =>
      IsChord g ∧ g.label < (Line.label (.inl (gwL 0) : Line repGW))).card = 0 := by
    decide +kernel
  have h1 : (Finset.univ.filter fun g : Line repGW =>
      IsChord g ∧ g.label < (Line.label (.inl (gwL 2) : Line repGW))).card = 1 := by
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

/-- The unimodular change of loop momenta of `GW`: `ℓ ↦ (ℓ 1, ℓ 0 - ℓ 1)`. -/
def gwMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]

theorem isUnit_det_gwMat : IsUnit gwMat.det := by
  rw [Matrix.det_fin_two]
  simp [gwMat]

/-- The chords of `GW` carry the frozen loop momenta at `gwMat ℓ + (p, 0)`. -/
theorem gw_hchord (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repGW)
    (hf : IsChord f) : gwMom p kext ℓ f =
      chordMomentum ((fun s => ∑ r, gwMat s r • ℓ r) + ![p, 0]) f := by
  obtain ⟨c0, c1⟩ := gw_chordMomentum ((fun s => ∑ r, gwMat s r • ℓ r) + ![p, 0])
  obtain ⟨n0, -, n2, -⟩ := gwMom_apply p kext ℓ
  rcases (gw_isChord_iff f).mp hf with rfl | rfl
  · rw [c0, n0]
    simp [gwMat, Fin.sum_univ_two]
    abel
  · rw [c1, n2]
    simp [gwMat, Fin.sum_univ_two]
    abel

/-! ### The amplitude -/

theorem gw_prod_fermionLine {M : Type*} [CommMonoid M] (g : FermionLine repGW → M) :
    ∏ f, g f = g (gwL 0) * g (gwL 1) * g (gwL 2) * g (gwL 3) := by
  rw [← (Equiv.ofBijective _ gwL_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem gw_prod_photonLine {M : Type*} [CommMonoid M] (g : PhotonLine repGW → M) :
    ∏ f, g f = g (gwP 0) * g (gwP 1) := by
  rw [← (Equiv.ofBijective _ gwP_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem gw_tails : (gwL 0).tail = fv kGW 0 ∧ (gwL 1).tail = fv kGW 1 ∧
    (gwL 2).tail = fv kGW 4 ∧ (gwL 3).tail = fv kGW 3 := by decide +kernel

theorem gw_vals : (gwL 0).1 = fv kGW 1 ∧ (gwL 1).1 = fv kGW 2 ∧ (gwL 2).1 = fv kGW 3 ∧
    (gwL 3).1 = fv kGW 4 ∧ (gwP 0).1 = pg kGW 0 ∧ (gwP 1).1 = pg kGW 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gw_heads : (gwP 0).head = pg kGW 4 ∧ (gwP 1).head = pg kGW 3 := by decide +kernel

theorem gw_cond (α β : Wick.FermionVertex kGW → Fin 4) (lor : Wick.PhotonSlot kGW → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repGW.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repGW.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repGW.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (lor (pg kGW 1) = μ 0 ∧ (α (fv kGW 2) = αOut 0 ∧ β (fv kGW 0) = βIn 0)) := by
  have h0 : ∀ t, repGW.1.1 (.inl 0) = .inr t ↔ t = fv kGW 2 := by decide +kernel
  have h1 : ∀ t, repGW.1.1 (.inr t) = .inl 0 ↔ t = fv kGW 0 := by decide +kernel
  have h2 : ∀ a, repGW.1.2 (.inl 0) = .inr a ↔ a = pg kGW 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h0, h1, h2, forall_eq]
  tauto

/-- The splitting of the fermion fields of `kGW` into the open line `2, 1, 0` and the loop
`3, 4`. -/
noncomputable def gwSplit : Wick.FermionVertex kGW ≃ Fin 3 ⊕ Fin 2 :=
  Equiv.ofBijective (fun t => (![.inl 2, .inl 1, .inl 0, .inr 0, .inr 1] : Fin 5 → _) t.1)
    (by decide +kernel)

/-- The flavouring of `repGW` with the open line of flavour `Φ.openLine` and the loop of flavour
`f`. -/
def gwFlav {F : Type} (Φ : Lepton.Flavors F) (f : F) : Graded.Flavoring F kGW :=
  fun t => if t.1.val < 3 then Φ.openLine else f

/-- The open-line chain of `GW`. -/
noncomputable def gwChain (P : Params) (m : ℝ) (kk : Line repGW → Fin 4 → ℝ) (μ l2 l0 : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma l2 * QED.OneLoop.electronPropagator m P.ε (kk (.inl (gwL 1))) * Dirac.gamma μ *
    QED.OneLoop.electronPropagator m P.ε (kk (.inl (gwL 0))) * Dirac.gamma l0

/-- The loop trace of `GW`. -/
noncomputable def gwLoop (P : Params) (M : ℝ) (kk : Line repGW → Fin 4 → ℝ) (l3 l4 : Fin 4) :
    ℂ :=
  Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (gwL 2))) *
    Dirac.gamma l4 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (gwL 3))))

theorem gw_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (f : F) (pIn kIn : Fin 1 → Fin 4 → ℝ) (kk : Line repGW → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionAmplitude P Φ D repGW (gwFlav Φ f) 0 pIn kIn kk αOut βIn μ =
      (I * P.e) ^ 4 * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 6 *
        ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 0))) l0 l4 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 1))) l2 l3 *
          gwLoop P (Φ.mass f) kk l3 l4 *
          gwChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) := by
  obtain ⟨t0, t1, t2, t3⟩ := gw_tails
  obtain ⟨g0, g1⟩ := gw_heads
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := gw_vals
  unfold Graded.contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex kGW → Fin 4, ∑ β : Wick.FermionVertex kGW → Fin 4,
      ∑ lor : Wick.PhotonSlot kGW → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [gw_cond, Fin.prod_univ_five, gw_prod_fermionLine, gw_prod_photonLine, t0, t1, t2, t3,
    g0, g1, v0, v1, v2, v3, v4, v5,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGW 0 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGW 1 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGW 2 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGW 3 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _
      (show kGW 4 = .gaugeCt from rfl), show kGW 4 = .gaugeCt from rfl, dite_false,
    reduceCtorEq, Pi.zero_apply, zero_add, mul_one, ite_and_eq_mul_ite]
  have hfl : ∀ t : Fin 5, ∀ h, gwFlav Φ f ⟨t, h⟩ = if t.val < 3 then Φ.openLine else f :=
    fun _ _ => rfl
  simp only [fv, pg, hfl, Fin.isValue, Fin.val_one, Fin.val_two]
  simp only [show ((4 : Fin 5) : ℕ) < 3 ↔ False by decide,
    show ((3 : Fin 5) : ℕ) < 3 ↔ False by decide, show (1 : ℕ) < 3 ↔ True by decide,
    show (2 : ℕ) < 3 ↔ True by decide, ite_true, ite_false]
  set K : ℂ := (I * P.e) ^ 4 * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 6 with hK
  have hR : K * ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 0))) l0 l4 *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 1))) l2 l3 *
      gwLoop P (Φ.mass f) kk l3 l4 *
      gwChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) =
      ∑ lor : Wick.PhotonSlot kGW → Fin 4,
      (if lor ⟨1, ⟨0, by decide⟩⟩ = μ 0 then (1 : ℂ) else 0) * (K *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 0))) (lor ⟨0, ⟨0, by decide⟩⟩)
          (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 1))) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨3, ⟨0, by decide⟩⟩) *
        gwLoop P (Φ.mass f) kk (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        gwChain P (Φ.mass Φ.openLine) kk (μ 0) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨0, ⟨0, by decide⟩⟩) (αOut 0) (βIn 0))) := by
    rw [QED.TwoLoop.Insertion.sum_pi_five (x₁ := (⟨1, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kGW))
      (x₂ := ⟨4, ⟨0, by decide⟩⟩) (x₃ := ⟨3, ⟨0, by decide⟩⟩) (x₄ := ⟨0, ⟨0, by decide⟩⟩)
      (x₅ := ⟨2, ⟨0, by decide⟩⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
    simp +decide only [ite_false, ite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [hR]
  refine Finset.sum_congr rfl fun lor _ => ?_
  by_cases hL : lor ⟨1, ⟨0, by decide⟩⟩ = μ 0
  · have h := sum_spinor_chain3_loop2 gwSplit (x₁ := ⟨2, by decide⟩) (x₂ := ⟨1, by decide⟩)
      (x₃ := ⟨0, by decide⟩) (y₁ := ⟨3, by decide⟩) (y₂ := ⟨4, by decide⟩) rfl rfl rfl rfl rfl
      (K * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 0)))
        (lor ⟨0, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (gwP 1)))
        (lor ⟨2, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨0, by decide⟩⟩))
      (Dirac.gamma (lor ⟨2, ⟨0, by decide⟩⟩)) (Dirac.gamma (μ 0))
      (Dirac.gamma (lor ⟨0, ⟨0, by decide⟩⟩))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (gwL 1))))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (gwL 0))))
      (Dirac.gamma (lor ⟨3, ⟨0, by decide⟩⟩)) (Dirac.gamma (lor ⟨4, ⟨0, by decide⟩⟩))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (gwL 2))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (gwL 3)))) (αOut 0) (βIn 0)
    simp only [hL, ite_true, one_mul]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hK]
      push_cast
      by_cases ha : α ⟨2, by decide⟩ = αOut 0 <;> by_cases hb : β ⟨0, by decide⟩ = βIn 0 <;>
        simp only [ha, hb, and_true, and_false, ite_true, ite_false] <;> ring
    · unfold gwLoop gwChain
      ring
  · simp only [hL, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The preserved flavourings -/

theorem gw_perm : repGW.1.1 (.inl 0) = .inr (fv kGW 2) ∧
    repGW.1.1 (.inr (fv kGW 2)) = .inr (fv kGW 1) ∧
    repGW.1.1 (.inr (fv kGW 1)) = .inr (fv kGW 0) ∧
    repGW.1.1 (.inr (fv kGW 0)) = .inl 0 ∧
    repGW.1.1 (.inr (fv kGW 3)) = .inr (fv kGW 4) ∧
    repGW.1.1 (.inr (fv kGW 4)) = .inr (fv kGW 3) := by decide +kernel

theorem gw_fv_cases : ∀ t : Wick.FermionVertex kGW, t = fv kGW 0 ∨ t = fv kGW 1 ∨
    t = fv kGW 2 ∨ t = fv kGW 3 ∨ t = fv kGW 4 := by decide

/-- **The flavourings preserved by `repGW`**: the open line has the open-line flavour, the loop
one flavour. -/
theorem gw_preserves_iff {F : Type} (Φ : Lepton.Flavors F) (φ : Graded.Flavoring F kGW) :
    Graded.Preserves Φ repGW φ ↔ φ = gwFlav Φ (φ (fv kGW 3)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := gw_perm
  constructor
  · intro hφ
    have h0 := hφ (.inl 0)
    have h1 := hφ (.inr (fv kGW 2))
    have h2 := hφ (.inr (fv kGW 1))
    have h5 := hφ (.inr (fv kGW 4))
    rw [s0] at h0
    rw [s1] at h1
    rw [s2] at h2
    rw [s5] at h5
    simp only [Graded.fermionFlavor] at h0 h1 h2 h5
    funext t
    rcases gw_fv_cases t with rfl | rfl | rfl | rfl | rfl <;>
      simp only [gwFlav, fv] <;> norm_num
    · exact h2.trans (h1.trans h0)
    · exact h1.trans h0
    · exact h0
    · exact h5.symm
  · intro h a
    rw [h]
    rcases a with i | t
    · rw [Fin.fin_one_eq_zero i, s0]
      simp [Graded.fermionFlavor, gwFlav, fv]
    · rcases gw_fv_cases t with rfl | rfl | rfl | rfl | rfl
      · rw [s3]; simp [Graded.fermionFlavor, gwFlav, fv]
      · rw [s2]; simp [Graded.fermionFlavor, gwFlav, fv]
      · rw [s1]; simp [Graded.fermionFlavor, gwFlav, fv]
      · rw [s4]; simp [Graded.fermionFlavor, gwFlav, fv]
      · rw [s5]; simp [Graded.fermionFlavor, gwFlav, fv]

/-- **The regulated amplitude of `repGW`** is the sum over the loop flavour of its coefficient
times the amplitude. -/
theorem gw_regulatedAmplitude (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (kk : Line repGW → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.regulatedAmplitude P Φ D repGW 0 pIn kIn kk αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) *
        Graded.contractionAmplitude P Φ D repGW (gwFlav Φ f) 0 pIn kIn kk αOut βIn μ := by
  classical
  unfold Graded.regulatedAmplitude
  refine Finset.sum_nbij' (fun φ => φ (fv kGW 3)) (gwFlav Φ) (fun _ _ => Finset.mem_univ _)
    (fun f _ => ?_) (fun φ hφ => ?_) (fun f _ => ?_) (fun φ hφ => ?_)
  · rw [Finset.mem_filter, gw_preserves_iff]
    exact ⟨Finset.mem_univ _, by simp [gwFlav, fv]⟩
  · exact ((gw_preserves_iff Φ φ).mp (Finset.mem_filter.mp hφ).2).symm
  · simp [gwFlav, fv]
  · have hp := (Finset.mem_filter.mp hφ).2
    rw [loopWeight_eq_of_one_loop Φ hp (fv kGW 3) gw_open gw_all]
    conv_lhs => rw [(gw_preserves_iff Φ φ).mp hp]
    simp [gwFlav, fv]

/-! ### The Wick factorization -/

/-- The inner integrand of `GW`: the integrand of the two-photon class `G1` at `(-ℓ, ℓ)`, loop
momentum shifted to `q`. -/
noncomputable def gwInner (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ q : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repG1 0
    ![] ![-ℓ, -(-ℓ)] (QED.GradedProof.VP2.g1Mom (-ℓ) (q + -ℓ)) ![] ![] ![a, b]

/-- **The Wick factorization of `GW`**: in the nested routing, the integrand of the value of
`repGW` is the outer factor times the inner integrand of `G1`, summed over the photon slot. -/
theorem gw_routedIntegrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    routedIntegrand P Φ D repGW 0 2 (fun _ => p) (fun _ => p' - p) (gwMom p (p' - p) ℓ)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (gwInner P Φ D) ℓ := by
  have hq : ℓ 0 - ℓ 1 - -ℓ 1 = ℓ 0 := by abel
  have hq' : ℓ 0 + -ℓ 1 = ℓ 0 - ℓ 1 := by abel
  have hp : p + (p' - p) + ℓ 1 = p' + ℓ 1 := by abel
  simp only [routedIntegrand, gw_regulatedAmplitude, gw_amplitude, outerInner, gwInner,
    QED.GradedProof.VP2.g1_integrand P Φ D id (fun _ => rfl), lOuter,
    QED.ChainProof.SetANestV.nestOuter,
    QED.TwoLoop.Insertion.vertexChain, QED.GradedProof.VP2.bubbleW, gwLoop, gwChain,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hq', id]
  simp only [show gwMom p (p' - p) ℓ (.inl (gwL 0)) = p + ℓ 1 from rfl,
    show gwMom p (p' - p) ℓ (.inl (gwL 1)) = p' + ℓ 1 from hp,
    show gwMom p (p' - p) ℓ (.inl (gwL 2)) = ℓ 0 - ℓ 1 from rfl,
    show gwMom p (p' - p) ℓ (.inl (gwL 3)) = ℓ 0 from rfl,
    show gwMom p (p' - p) ℓ (.inr (gwP 0)) = -ℓ 1 from rfl,
    show gwMom p (p' - p) ℓ (.inr (gwP 1)) = ℓ 1 from rfl, hq, hq',
    Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm_out_two]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl
      fun ρ _ => ?_
  rw [QED.GradedProof.VP2.trace_rotate4 (Dirac.gamma b),
    QED.TwoLoop.Insertion.photonPropagator_neg', QED.TwoLoop.Insertion.photonPropagator_neg']
  push_cast
  ring

/-! ### The inner integrand -/

/-- **The energy-first integral of the inner integrand of `GW`** is the value of the two-photon
class `G1` at `(-ℓ, ℓ)`. -/
theorem efi_gwInner (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.energyFirstIntegral (fun q => gwInner P Φ D ℓ q a b) =
      QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repG1 := by
  have hc := QED.GradedProof.VP2.g1_isChord_iff
  unfold QED.GradedProof.VP2.val0 Graded.contractionValue
  rw [QED.TwoLoop.Insertion.loopCount_eq_one_of_unique hc]
  simp only [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc
    (QED.GradedProof.VP2.g1Mom (-ℓ)) (QED.GradedProof.VP2.g1_isConserved (-ℓ))
    (fun q => (QED.GradedProof.VP2.g1Mom_apply (-ℓ) q).1)]
  rw [QED.TwoLoop.jointEnergyFirstIntegral_one_eq (fun q => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
    Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repG1 0 ![] ![-ℓ, -(-ℓ)]
      (QED.GradedProof.VP2.g1Mom (-ℓ) q) ![] ![] ![a, b])]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_add_right_eq_self _ (-ℓ)]
  simp only [gwInner, mul_one]

/-- The inner integrand of `GW` is the block-summed bubble at `-ℓ`. -/
theorem gwInner_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F) (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) :
    gwInner P Φ D = blockBubbleNeg P Φ rep (fun r => ((P.e ^ 2 * D.d₁ r 0 : ℝ) : ℂ)) := by
  funext ℓ q a b
  rw [gwInner, QED.GradedProof.VP2.g1_integrand P Φ D rep hD, blockBubbleNeg]
  simp only [sub_neg_eq_add, neg_add_cancel_right]

/-! ### The nested form -/

/-- **The nested form of `GW`.** Under the hypotheses `IntHypA` of (HA₀) and masses bounded
below by `m₀ > 0`, the class `GW` is in nested form (`LoopNested`) with the photon tensor
`X(k)^{ab} = (1/i) val0(G1)(-k)^{ab}`. -/
theorem loopNested_repGW (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (p' p : Fin 4 → ℝ) :
    LoopNested P Φ D repGW
      (fun k a b => (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repG1)
      p' p := by
  have hG : OneLoopInnerBound (17 / 2) (7 / 2) (gwInner P Φ D) := by
    rw [gwInner_eq P Φ D rep fun f => (hH.hD f).1]
    exact oneLoopInnerBound_blockBubbleNeg P Φ rep hm₀ hmass hH.hrep hH.hPV₁ hH.hPV₂ hH.hε _
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_gwMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  have hR : ∀ μ i j : Fin 4, (fun ℓ => routedIntegrand P Φ D repGW 0 2 (fun _ => p)
      (fun _ => p' - p) (gwMom p (p' - p) ℓ) (fun _ => i) (fun _ => j) (fun _ => μ)) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) (gwInner P Φ D) :=
    fun μ i j => funext fun ℓ => gw_routedIntegrand P Φ D p' p μ i j ℓ
  have h := loopNested_of_lOuter P Φ D repGW p' p hH.hε (by norm_num) (by norm_num)
    (by norm_num) hG (fun μ i j => ?_) (fun μ i j => ?_)
  · have e : (fun k a b =>
        (1 / I) * QED.OneLoop.energyFirstIntegral fun q => gwInner P Φ D k q a b) =
        fun k a b => (1 / I) *
          QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repG1 :=
      funext fun k => funext fun a => funext fun b => by rw [efi_gwInner]
    rwa [e] at h
  · rw [contractionValue_eq_of_routing P Φ D repGW 0 loopCount_repGW (gwMom p (p' - p)) hcons
      gwMat isUnit_det_gwMat ![p, 0] (gw_hchord p (p' - p)), hR]
  · rw [← hR]
    exact jointEnergyFirstIntegrable_of_routing P Φ D repGW 0 loopCount_repGW
      (gwMom p (p' - p)) hcons gwMat isUnit_det_gwMat ![p, 0] (gw_hchord p (p' - p)) _ _ _
      (classIntA_repGW P Φ D rep hH (fun _ => p') (fun _ => p) (fun _ => p' - p) hmom _ _ _)

end QED.ChainProof.SetANest

end
