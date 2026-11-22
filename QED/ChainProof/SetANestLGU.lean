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
# Set (a), obligation (N): the nested form of the `gaugeCt` class `GU`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form
`QED.ChainProof.SetANest.LoopNested` of `QED.ChainProof.SetALink.repGU` (the level-`0` `δ₁`
counterterm at the vertex `u = 3` of the bubble, the field `x` paired with `a = 2`).

* Routing: `guMom`, with `ℓ 0 = q` on the loop line `3 → 4` and `ℓ 1 = ℓ` the photon momentum
  (lines `0 → 1`: `p + ℓ`, `1 → 2`: `p' + ℓ`, `4 → 3`: `q - ℓ`, photons `0 → 4`: `-ℓ`,
  `2 → 3`: `ℓ`), conserved (`isConserved_guMom`), with the chords `0 → 1`, `4 → 3` at the frozen
  loop momenta `guMat ℓ + (p, 0)` (`gu_hchord`, `guMat` of determinant `-1`).
* Wick: the preserved flavourings are the loop flavours `f` (`gu_preserves_iff`), with weight
  `c_f` (`gu_regulatedAmplitude`); the amplitude at `f` (`gu_amplitude`) is the open chain times
  the loop trace; **`gu_routedIntegrand`**: the integrand in the routing `guMom` is
  `outerInner lOuter guInner`, `guInner(ℓ, q)` the integrand of the two-photon class `G0` at
  `(-ℓ, ℓ)` (`QED.GradedProof.VP2.g0_integrand`) at the loop momentum `q`.
* `efi_guInner`: `∫_D guInner(ℓ, ·) = val0(G0)(-ℓ)`; `guInner_eq`: it is the block-summed bubble
  `blockBubbleNeg`, which has `OneLoopInnerBound (17/2) (7/2)`.
* **`gauge_group_sum`**: the `gaugeCt` group identity of
  `QED.ChainProof.SetANest.hsum_of_groups`.
* **`loopNested_repGU`**: under the hypotheses `IntHypA` of (HA₀) and positive masses, `GU` is in
  nested form with `X(k)^{ab} = (1/i) val0(G0)(-k)^{ab}`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.SetALink QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### Lines and routing -/

/-- The fermion lines of `repGU`, by head `1, 2, 3, 4` (tails `0, 1, 4, 3`). -/
def guL : Fin 4 → FermionLine repGU :=
  ![⟨fv kGU 1, by decide +kernel⟩, ⟨fv kGU 2, by decide +kernel⟩, ⟨fv kGU 3, by decide +kernel⟩,
    ⟨fv kGU 4, by decide +kernel⟩]

/-- The photon lines `0 — 4`, `2 — 3` of `repGU`. -/
def guP : Fin 2 → PhotonLine repGU :=
  ![⟨pg kGU 0, by decide +kernel⟩, ⟨pg kGU 2, by decide +kernel⟩]

theorem guL_bijective : Function.Bijective guL := by decide +kernel

theorem guP_bijective : Function.Bijective guP := by decide +kernel

theorem gu_sum_line {M : Type*} [AddCommMonoid M] (g : Line repGU → M) :
    ∑ f, g f = g (.inl (guL 0)) + g (.inl (guL 1)) + g (.inl (guL 2)) + g (.inl (guL 3)) +
      (g (.inr (guP 0)) + g (.inr (guP 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ guL_bijective).sum_comp,
    ← (Equiv.ofBijective _ guP_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem gu_ends : (Line.ends (.inl (guL 0) : Line repGU)) = (0, 1) ∧
    (Line.ends (.inl (guL 1) : Line repGU)) = (1, 2) ∧
    (Line.ends (.inl (guL 2) : Line repGU)) = (4, 3) ∧
    (Line.ends (.inl (guL 3) : Line repGU)) = (3, 4) ∧
    (Line.ends (.inr (guP 0) : Line repGU)) = (0, 4) ∧
    (Line.ends (.inr (guP 1) : Line repGU)) = (2, 3) := by decide +kernel

theorem gu_ext (v : Fin 5) :
    ((∃ t : Wick.FermionVertex kGU, t.1 = v ∧ repGU.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kGU, a.1 = v ∧ repGU.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kGU, t.1 = v ∧ repGU.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- **The nested routing of `GU`**: `ℓ 0 = q` on the loop line `3 → 4`, `ℓ 1 = ℓ` the photon
momentum; lines `0 → 1`: `p + ℓ`, `1 → 2`: `p + k + ℓ`, `4 → 3`: `q - ℓ`, `3 → 4`: `q`, photon
`0 → 4`: `-ℓ`, photon `2 → 3`: `ℓ`. -/
def guMom (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repGU) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p + ℓ 1
  | 2 => p + kext + ℓ 1
  | 3 => ℓ 0 - ℓ 1
  | 4 => ℓ 0
  | 5 => -ℓ 1
  | _ => ℓ 1

theorem guMom_apply (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    guMom p kext ℓ (.inl (guL 0)) = p + ℓ 1 ∧ guMom p kext ℓ (.inl (guL 1)) = p + kext + ℓ 1 ∧
      guMom p kext ℓ (.inl (guL 2)) = ℓ 0 - ℓ 1 ∧ guMom p kext ℓ (.inl (guL 3)) = ℓ 0 ∧
      guMom p kext ℓ (.inr (guP 0)) = -ℓ 1 ∧ guMom p kext ℓ (.inr (guP 1)) = ℓ 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isConserved_guMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) : IsConserved repGU pOut pIn kIn (guMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3, g0, g1⟩ := gu_ends
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := guMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  obtain ⟨x0, x1, x2⟩ := gu_ext v
  rw [inflow, gu_sum_line, QED.TwoLoop.Insertion.externalMomentum_one_one, hmom]
  simp only [e0, e1, e2, e3, g0, g1, n0, n1, n2, n3, n4, n5, x0, x1, x2]
  fin_cases v
  all_goals simp
  all_goals abel

theorem gu_isChord_iff : ∀ f : Line repGU,
    IsChord f ↔ f = .inl (guL 0) ∨ f = .inl (guL 2) := by
  decide +kernel

theorem gu_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (guL 0) : Line repGU) = ℓ 0 ∧
      chordMomentum ℓ (.inl (guL 2) : Line repGU) = ℓ 1 := by
  have h0 : (Finset.univ.filter fun g : Line repGU =>
      IsChord g ∧ g.label < (Line.label (.inl (guL 0) : Line repGU))).card = 0 := by
    decide +kernel
  have h1 : (Finset.univ.filter fun g : Line repGU =>
      IsChord g ∧ g.label < (Line.label (.inl (guL 2) : Line repGU))).card = 1 := by
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

/-- The unimodular change of loop momenta of `GU`: `ℓ ↦ (ℓ 1, ℓ 0 - ℓ 1)`. -/
def guMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]

theorem isUnit_det_guMat : IsUnit guMat.det := by
  rw [Matrix.det_fin_two]
  simp [guMat]

/-- The chords of `GU` carry the frozen loop momenta at `guMat ℓ + (p, 0)`. -/
theorem gu_hchord (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repGU)
    (hf : IsChord f) : guMom p kext ℓ f =
      chordMomentum ((fun s => ∑ r, guMat s r • ℓ r) + ![p, 0]) f := by
  obtain ⟨c0, c1⟩ := gu_chordMomentum ((fun s => ∑ r, guMat s r • ℓ r) + ![p, 0])
  obtain ⟨n0, -, n2, -⟩ := guMom_apply p kext ℓ
  rcases (gu_isChord_iff f).mp hf with rfl | rfl
  · rw [c0, n0]
    simp [guMat, Fin.sum_univ_two]
    abel
  · rw [c1, n2]
    simp [guMat, Fin.sum_univ_two]
    abel

/-! ### The amplitude -/

theorem gu_prod_fermionLine {M : Type*} [CommMonoid M] (g : FermionLine repGU → M) :
    ∏ f, g f = g (guL 0) * g (guL 1) * g (guL 2) * g (guL 3) := by
  rw [← (Equiv.ofBijective _ guL_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem gu_prod_photonLine {M : Type*} [CommMonoid M] (g : PhotonLine repGU → M) :
    ∏ f, g f = g (guP 0) * g (guP 1) := by
  rw [← (Equiv.ofBijective _ guP_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem gu_tails : (guL 0).tail = fv kGU 0 ∧ (guL 1).tail = fv kGU 1 ∧
    (guL 2).tail = fv kGU 4 ∧ (guL 3).tail = fv kGU 3 := by decide +kernel

theorem gu_vals : (guL 0).1 = fv kGU 1 ∧ (guL 1).1 = fv kGU 2 ∧ (guL 2).1 = fv kGU 3 ∧
    (guL 3).1 = fv kGU 4 ∧ (guP 0).1 = pg kGU 0 ∧ (guP 1).1 = pg kGU 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gu_heads : (guP 0).head = pg kGU 4 ∧ (guP 1).head = pg kGU 3 := by decide +kernel

theorem gu_cond (α β : Wick.FermionVertex kGU → Fin 4) (lor : Wick.PhotonSlot kGU → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repGU.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repGU.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repGU.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (lor (pg kGU 1) = μ 0 ∧ (α (fv kGU 2) = αOut 0 ∧ β (fv kGU 0) = βIn 0)) := by
  have h0 : ∀ t, repGU.1.1 (.inl 0) = .inr t ↔ t = fv kGU 2 := by decide +kernel
  have h1 : ∀ t, repGU.1.1 (.inr t) = .inl 0 ↔ t = fv kGU 0 := by decide +kernel
  have h2 : ∀ a, repGU.1.2 (.inl 0) = .inr a ↔ a = pg kGU 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h0, h1, h2, forall_eq]
  tauto

/-- The splitting of the fermion fields of `kGU` into the open line `2, 1, 0` and the loop
`3, 4`. -/
noncomputable def guSplit : Wick.FermionVertex kGU ≃ Fin 3 ⊕ Fin 2 :=
  Equiv.ofBijective (fun t => (![.inl 2, .inl 1, .inl 0, .inr 0, .inr 1] : Fin 5 → _) t.1)
    (by decide +kernel)

/-- The flavouring of `repGU` with the open line of flavour `Φ.openLine` and the loop of flavour
`f`. -/
def guFlav {F : Type} (Φ : Lepton.Flavors F) (f : F) : Graded.Flavoring F kGU :=
  fun t => if t.1.val < 3 then Φ.openLine else f

/-- The open-line chain of `GU`. -/
noncomputable def guChain (P : Params) (m : ℝ) (kk : Line repGU → Fin 4 → ℝ) (μ l2 l0 : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma l2 * QED.OneLoop.electronPropagator m P.ε (kk (.inl (guL 1))) * Dirac.gamma μ *
    QED.OneLoop.electronPropagator m P.ε (kk (.inl (guL 0))) * Dirac.gamma l0

/-- The loop trace of `GU`. -/
noncomputable def guLoop (P : Params) (M : ℝ) (kk : Line repGU → Fin 4 → ℝ) (l3 l4 : Fin 4) :
    ℂ :=
  Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (guL 2))) *
    Dirac.gamma l4 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (guL 3))))

theorem gu_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (f : F) (pIn kIn : Fin 1 → Fin 4 → ℝ) (kk : Line repGU → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionAmplitude P Φ D repGU (guFlav Φ f) 0 pIn kIn kk αOut βIn μ =
      (I * P.e) ^ 4 * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 6 *
        ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 0))) l0 l4 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 1))) l2 l3 *
          guLoop P (Φ.mass f) kk l3 l4 *
          guChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) := by
  obtain ⟨t0, t1, t2, t3⟩ := gu_tails
  obtain ⟨g0, g1⟩ := gu_heads
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := gu_vals
  unfold Graded.contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex kGU → Fin 4, ∑ β : Wick.FermionVertex kGU → Fin 4,
      ∑ lor : Wick.PhotonSlot kGU → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [gu_cond, Fin.prod_univ_five, gu_prod_fermionLine, gu_prod_photonLine, t0, t1, t2, t3,
    g0, g1, v0, v1, v2, v3, v4, v5,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGU 0 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGU 1 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGU 2 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show kGU 4 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _
      (show kGU 3 = .gaugeCt from rfl), show kGU 3 = .gaugeCt from rfl, dite_false,
    reduceCtorEq, Pi.zero_apply, zero_add, mul_one, ite_and_eq_mul_ite]
  have hfl : ∀ t : Fin 5, ∀ h, guFlav Φ f ⟨t, h⟩ = if t.val < 3 then Φ.openLine else f :=
    fun _ _ => rfl
  simp only [fv, pg, hfl, Fin.isValue, Fin.val_one, Fin.val_two]
  simp only [show ((4 : Fin 5) : ℕ) < 3 ↔ False by decide,
    show ((3 : Fin 5) : ℕ) < 3 ↔ False by decide, show (1 : ℕ) < 3 ↔ True by decide,
    show (2 : ℕ) < 3 ↔ True by decide, ite_true, ite_false]
  set K : ℂ := (I * P.e) ^ 4 * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 6 with hK
  have hR : K * ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 0))) l0 l4 *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 1))) l2 l3 *
      guLoop P (Φ.mass f) kk l3 l4 *
      guChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) =
      ∑ lor : Wick.PhotonSlot kGU → Fin 4,
      (if lor ⟨1, ⟨0, by decide⟩⟩ = μ 0 then (1 : ℂ) else 0) * (K *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 0))) (lor ⟨0, ⟨0, by decide⟩⟩)
          (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 1))) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨3, ⟨0, by decide⟩⟩) *
        guLoop P (Φ.mass f) kk (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        guChain P (Φ.mass Φ.openLine) kk (μ 0) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨0, ⟨0, by decide⟩⟩) (αOut 0) (βIn 0))) := by
    rw [QED.TwoLoop.Insertion.sum_pi_five (x₁ := (⟨1, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kGU))
      (x₂ := ⟨4, ⟨0, by decide⟩⟩) (x₃ := ⟨3, ⟨0, by decide⟩⟩) (x₄ := ⟨0, ⟨0, by decide⟩⟩)
      (x₅ := ⟨2, ⟨0, by decide⟩⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
    simp +decide only [ite_false, ite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [hR]
  refine Finset.sum_congr rfl fun lor _ => ?_
  by_cases hL : lor ⟨1, ⟨0, by decide⟩⟩ = μ 0
  · have h := sum_spinor_chain3_loop2 guSplit (x₁ := ⟨2, by decide⟩) (x₂ := ⟨1, by decide⟩)
      (x₃ := ⟨0, by decide⟩) (y₁ := ⟨3, by decide⟩) (y₂ := ⟨4, by decide⟩) rfl rfl rfl rfl rfl
      (K * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 0)))
        (lor ⟨0, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (guP 1)))
        (lor ⟨2, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨0, by decide⟩⟩))
      (Dirac.gamma (lor ⟨2, ⟨0, by decide⟩⟩)) (Dirac.gamma (μ 0))
      (Dirac.gamma (lor ⟨0, ⟨0, by decide⟩⟩))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (guL 1))))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (guL 0))))
      (Dirac.gamma (lor ⟨3, ⟨0, by decide⟩⟩)) (Dirac.gamma (lor ⟨4, ⟨0, by decide⟩⟩))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (guL 2))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (guL 3)))) (αOut 0) (βIn 0)
    simp only [hL, ite_true, one_mul]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hK]
      push_cast
      by_cases ha : α ⟨2, by decide⟩ = αOut 0 <;> by_cases hb : β ⟨0, by decide⟩ = βIn 0 <;>
        simp only [ha, hb, and_true, and_false, ite_true, ite_false] <;> ring
    · unfold guLoop guChain
      ring
  · simp only [hL, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The preserved flavourings -/

theorem gu_perm : repGU.1.1 (.inl 0) = .inr (fv kGU 2) ∧
    repGU.1.1 (.inr (fv kGU 2)) = .inr (fv kGU 1) ∧
    repGU.1.1 (.inr (fv kGU 1)) = .inr (fv kGU 0) ∧
    repGU.1.1 (.inr (fv kGU 0)) = .inl 0 ∧
    repGU.1.1 (.inr (fv kGU 3)) = .inr (fv kGU 4) ∧
    repGU.1.1 (.inr (fv kGU 4)) = .inr (fv kGU 3) := by decide +kernel

theorem gu_fv_cases : ∀ t : Wick.FermionVertex kGU, t = fv kGU 0 ∨ t = fv kGU 1 ∨
    t = fv kGU 2 ∨ t = fv kGU 3 ∨ t = fv kGU 4 := by decide

/-- **The flavourings preserved by `repGU`**: the open line has the open-line flavour, the loop
one flavour. -/
theorem gu_preserves_iff {F : Type} (Φ : Lepton.Flavors F) (φ : Graded.Flavoring F kGU) :
    Graded.Preserves Φ repGU φ ↔ φ = guFlav Φ (φ (fv kGU 3)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := gu_perm
  constructor
  · intro hφ
    have h0 := hφ (.inl 0)
    have h1 := hφ (.inr (fv kGU 2))
    have h2 := hφ (.inr (fv kGU 1))
    have h5 := hφ (.inr (fv kGU 4))
    rw [s0] at h0
    rw [s1] at h1
    rw [s2] at h2
    rw [s5] at h5
    simp only [Graded.fermionFlavor] at h0 h1 h2 h5
    funext t
    rcases gu_fv_cases t with rfl | rfl | rfl | rfl | rfl <;>
      simp only [guFlav, fv] <;> norm_num
    · exact h2.trans (h1.trans h0)
    · exact h1.trans h0
    · exact h0
    · exact h5.symm
  · intro h a
    rw [h]
    rcases a with i | t
    · rw [Fin.fin_one_eq_zero i, s0]
      simp [Graded.fermionFlavor, guFlav, fv]
    · rcases gu_fv_cases t with rfl | rfl | rfl | rfl | rfl
      · rw [s3]; simp [Graded.fermionFlavor, guFlav, fv]
      · rw [s2]; simp [Graded.fermionFlavor, guFlav, fv]
      · rw [s1]; simp [Graded.fermionFlavor, guFlav, fv]
      · rw [s4]; simp [Graded.fermionFlavor, guFlav, fv]
      · rw [s5]; simp [Graded.fermionFlavor, guFlav, fv]

/-- **The regulated amplitude of `repGU`** is the sum over the loop flavour of its coefficient
times the amplitude. -/
theorem gu_regulatedAmplitude (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (kk : Line repGU → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.regulatedAmplitude P Φ D repGU 0 pIn kIn kk αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) *
        Graded.contractionAmplitude P Φ D repGU (guFlav Φ f) 0 pIn kIn kk αOut βIn μ := by
  classical
  unfold Graded.regulatedAmplitude
  refine Finset.sum_nbij' (fun φ => φ (fv kGU 3)) (guFlav Φ) (fun _ _ => Finset.mem_univ _)
    (fun f _ => ?_) (fun φ hφ => ?_) (fun f _ => ?_) (fun φ hφ => ?_)
  · rw [Finset.mem_filter, gu_preserves_iff]
    exact ⟨Finset.mem_univ _, by simp [guFlav, fv]⟩
  · exact ((gu_preserves_iff Φ φ).mp (Finset.mem_filter.mp hφ).2).symm
  · simp [guFlav, fv]
  · have hp := (Finset.mem_filter.mp hφ).2
    rw [loopWeight_eq_of_one_loop Φ hp (fv kGU 3) gu_open gu_all]
    conv_lhs => rw [(gu_preserves_iff Φ φ).mp hp]
    simp [guFlav, fv]

/-! ### The Wick factorization -/

/-- The inner integrand of `GU`: the integrand of the two-photon class `G0` at `(-ℓ, ℓ)` and the
loop momentum `q`. -/
noncomputable def guInner (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ q : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repG0 0
    ![] ![-ℓ, -(-ℓ)] (QED.GradedProof.VP2.g0Mom (-ℓ) q) ![] ![] ![a, b]

/-- **The Wick factorization of `GU`**: in the nested routing, the integrand of the value of
`repGU` is the outer factor times the inner integrand of `G0`, summed over the photon slot. -/
theorem gu_routedIntegrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    routedIntegrand P Φ D repGU 0 2 (fun _ => p) (fun _ => p' - p) (guMom p (p' - p) ℓ)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (guInner P Φ D) ℓ := by
  have hq' : ℓ 0 + -ℓ 1 = ℓ 0 - ℓ 1 := by abel
  have hp : p + (p' - p) + ℓ 1 = p' + ℓ 1 := by abel
  simp only [routedIntegrand, gu_regulatedAmplitude, gu_amplitude, outerInner, guInner,
    QED.GradedProof.VP2.g0_integrand P Φ D id (fun _ => rfl), lOuter,
    QED.ChainProof.SetANestV.nestOuter,
    QED.TwoLoop.Insertion.vertexChain, QED.GradedProof.VP2.bubbleW, guLoop, guChain,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hq', id]
  simp only [show guMom p (p' - p) ℓ (.inl (guL 0)) = p + ℓ 1 from rfl,
    show guMom p (p' - p) ℓ (.inl (guL 1)) = p' + ℓ 1 from hp,
    show guMom p (p' - p) ℓ (.inl (guL 2)) = ℓ 0 - ℓ 1 from rfl,
    show guMom p (p' - p) ℓ (.inl (guL 3)) = ℓ 0 from rfl,
    show guMom p (p' - p) ℓ (.inr (guP 0)) = -ℓ 1 from rfl,
    show guMom p (p' - p) ℓ (.inr (guP 1)) = ℓ 1 from rfl,
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

/-- **The energy-first integral of the inner integrand of `GU`** is the value of the two-photon
class `G0` at `(-ℓ, ℓ)`. -/
theorem efi_guInner (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.energyFirstIntegral (fun q => guInner P Φ D ℓ q a b) =
      QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repG0 := by
  have hc := QED.GradedProof.VP2.g0_isChord_iff
  unfold QED.GradedProof.VP2.val0 Graded.contractionValue
  rw [QED.TwoLoop.Insertion.loopCount_eq_one_of_unique hc]
  simp only [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc
    (QED.GradedProof.VP2.g0Mom (-ℓ)) (QED.GradedProof.VP2.g0_isConserved (-ℓ))
    (fun q => (QED.GradedProof.VP2.g0Mom_apply (-ℓ) q).1)]
  rw [QED.TwoLoop.jointEnergyFirstIntegral_one_eq (fun q => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
    Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repG0 0 ![] ![-ℓ, -(-ℓ)]
      (QED.GradedProof.VP2.g0Mom (-ℓ) q) ![] ![] ![a, b])]
  simp only [guInner, mul_one]

/-- The inner integrand of `GU` is the block-summed bubble at `-ℓ`. -/
theorem guInner_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F) (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) :
    guInner P Φ D = blockBubbleNeg P Φ rep (fun r => ((P.e ^ 2 * D.d₁ r 0 : ℝ) : ℂ)) := by
  funext ℓ q a b
  rw [guInner, QED.GradedProof.VP2.g0_integrand P Φ D rep hD, blockBubbleNeg]

/-! ### The nested form -/

/-- **The nested form of `GU`.** Under the hypotheses `IntHypA` of (HA₀) and masses bounded
below by `m₀ > 0`, the class `GU` is in nested form (`LoopNested`) with the photon tensor
`X(k)^{ab} = (1/i) val0(G0)(-k)^{ab}`. -/
theorem loopNested_repGU (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (p' p : Fin 4 → ℝ) :
    LoopNested P Φ D repGU
      (fun k a b => (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repG0)
      p' p := by
  have hG : OneLoopInnerBound (17 / 2) (7 / 2) (guInner P Φ D) := by
    rw [guInner_eq P Φ D rep fun f => (hH.hD f).1]
    exact oneLoopInnerBound_blockBubbleNeg P Φ rep hm₀ hmass hH.hrep hH.hPV₁ hH.hPV₂ hH.hε _
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_guMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  have hR : ∀ μ i j : Fin 4, (fun ℓ => routedIntegrand P Φ D repGU 0 2 (fun _ => p)
      (fun _ => p' - p) (guMom p (p' - p) ℓ) (fun _ => i) (fun _ => j) (fun _ => μ)) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) (guInner P Φ D) :=
    fun μ i j => funext fun ℓ => gu_routedIntegrand P Φ D p' p μ i j ℓ
  have h := loopNested_of_lOuter P Φ D repGU p' p hH.hε (by norm_num) (by norm_num)
    (by norm_num) hG (fun μ i j => ?_) (fun μ i j => ?_)
  · have e : (fun k a b =>
        (1 / I) * QED.OneLoop.energyFirstIntegral fun q => guInner P Φ D k q a b) =
        fun k a b => (1 / I) *
          QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repG0 :=
      funext fun k => funext fun a => funext fun b => by rw [efi_guInner]
    rwa [e] at h
  · rw [contractionValue_eq_of_routing P Φ D repGU 0 loopCount_repGU (guMom p (p' - p)) hcons
      guMat isUnit_det_guMat ![p, 0] (gu_hchord p (p' - p)), hR]
  · rw [← hR]
    exact jointEnergyFirstIntegrable_of_routing P Φ D repGU 0 loopCount_repGU
      (guMom p (p' - p)) hcons guMat isUnit_det_guMat ![p, 0] (gu_hchord p (p' - p)) _ _ _
      (classIntA_repGU P Φ D rep hH (fun _ => p') (fun _ => p) (fun _ => p' - p) hmom _ _ _)

/-- **The `gaugeCt` group identity** for `hsum_of_groups`: the photon tensors of `GW`
(`loopNested_repGW`) and `GU` (`loopNested_repGU`) sum to `(1/i)` times the values of `G0` and
`G1` at `-ℓ`. -/
theorem gauge_group_sum (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repG1 +
        (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repG0 =
      (1 / I) * (QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repG0 +
        QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repG1) := by
  ring

end QED.ChainProof.SetANest

end
