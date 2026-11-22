/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLGen
public import QED.ChainProof.SetANestLRoute
public import QED.ChainProof.SetALinkIntF
public import QED.ChainProof.SetALinkIntKind
public import QED.GradedProof.VP2ClassF
public import QED.TwoLoop.EnumerationDecide
public import QED.TwoLoop.IntegrableOrderFiveCt
public import QED.Integration.EnergyFirstShift
public import QED.TwoLoop.JointIntegral

/-!
# Set (a), obligation (N): the nested form of the fermion counterterm class `FA`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form
`QED.ChainProof.SetANest.LoopNested` of `QED.ChainProof.SetALink.repFA` (the level-`0` `δ₂, δ_m`
counterterm at the vertex `5` on the loop line `w → u` of the bubble, loop `3 → 4 → 5 → 3`).

* `sum_spinor_chain3_loop3`: the spinor sum of an open chain through three vertices and a
  closed loop through three is the chain entry times the loop trace.
* Routing: `faMom`, with `ℓ 0 = q` on the two loop lines `3 → 5`, `5 → 4` through the
  counterterm and `ℓ 1 = ℓ` the photon momentum (lines `0 → 1`: `p + ℓ`, `1 → 2`: `p' + ℓ`,
  `4 → 3`: `q - ℓ`, photons `0 → 4`: `-ℓ`, `2 → 3`: `ℓ`), with the chords `0 → 1`, `4 → 3` at
  the frozen loop momenta `faMat ℓ + (p, 0)`.
* Wick: **`fa_routedIntegrand`**: the integrand in the routing `faMom` is
  `outerInner lOuter faInner`, `faInner(ℓ, q)` the integrand of the class `F0` at `(-ℓ, ℓ)`
  (`QED.GradedProof.VP2.f0_integrand`) at the loop momentum `q`, unshifted.
* `efi_faInner`: `∫_D faInner(ℓ, ·) = val0(F0)(-ℓ)`; `faInner_eq`: it is the block-summed
  inserted bubble with the insertion line at `q` and the other line at `-ℓ + q`.
* **`loopNested_repFA_of_bound`**: under `IntHypA` and the inner bound `OneLoopInnerBound a b`
  of that inserted bubble (`0 ≤ a < 9`, `3 < b`), `FA` is in nested form with
  `X(k)^{ab} = (1/i) val0(F0)(-k)^{ab}`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.SetALink QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### Spinor sums -/

section Spin

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The spinor sum of an open chain through three vertices and a closed loop through three**:
with `α x₁` and `β x₃` fixed, the sum of `c · A₁ S₁ A₂ S₂ A₃ · B₁ T₁ B₂ T₂ B₃ T₃` over the
spinor indices is `c` times the loop trace times the entry of the chain. -/
theorem sum_spinor_chain3_loop3 (e : X ≃ Fin 3 ⊕ Fin 3) {x₁ x₂ x₃ y₁ y₂ y₃ : X}
    (h₁ : e x₁ = .inl 0) (h₂ : e x₂ = .inl 1) (h₃ : e x₃ = .inl 2) (h₄ : e y₁ = .inr 0)
    (h₅ : e y₂ = .inr 1) (h₆ : e y₃ = .inr 2) (c : ℂ)
    (A₁ A₂ A₃ S₁ S₂ B₁ B₂ B₃ T₁ T₂ T₃ : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₃ = b then (1 : ℂ) else 0) *
        (c * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃)) *
          (B₁ (α y₁) (β y₁) * T₁ (β y₁) (α y₂) * B₂ (α y₂) (β y₂) * T₂ (β y₂) (α y₃) *
            B₃ (α y₃) (β y₃) * T₃ (β y₃) (α y₁))) =
      c * Matrix.trace (B₁ * T₁ * B₂ * T₂ * B₃ * T₃) * (A₁ * S₁ * A₂ * S₂ * A₃) a b := by
  rw [sum_pi_sum_equiv e]
  simp only [sum_pi_sum_equiv e (g := fun β => _ * _), h₁, h₂, h₃, h₄, h₅, h₆, Sum.elim_inl,
    Sum.elim_inr]
  have hL := QED.GradedProof.VP2.sum_spinor_loop3 (X := Fin 3) (x₁ := 0) (x₂ := 1) (x₃ := 2)
    (by decide) (by decide) (by decide) (by decide) B₁ B₂ B₃ T₁ T₂ T₃
  have hC := QED.TwoLoop.Insertion.sum_spinor_chain3 (X := Fin 3) (x₁ := 0) (x₂ := 1)
    (x₃ := 2) (by decide) (by decide) (by decide) (by decide)
    (c * Matrix.trace (B₁ * T₁ * B₂ * T₂ * B₃ * T₃)) A₁ A₂ A₃ S₁ S₂ a b
  rw [← hC]
  refine Finset.sum_congr rfl fun α₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β₁ _ => ?_
  rw [← hL]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun β₂ _ => ?_
  ring

end Spin

/-! ### Lines and routing -/

/-- The fermion lines of `repFA`, by head `1, …, 5` (tails `0, 1, 4, 5, 3`). -/
def faL : Fin 5 → FermionLine repFA :=
  ![⟨fv kF 1, by decide +kernel⟩, ⟨fv kF 2, by decide +kernel⟩, ⟨fv kF 3, by decide +kernel⟩,
    ⟨fv kF 4, by decide +kernel⟩, ⟨fv kF 5, by decide +kernel⟩]

/-- The photon lines `0 — 4`, `2 — 3` of `repFA`. -/
def faP : Fin 2 → PhotonLine repFA :=
  ![⟨pg kF 0, by decide +kernel⟩, ⟨pg kF 2, by decide +kernel⟩]

theorem faL_bijective : Function.Bijective faL := by decide +kernel

theorem faP_bijective : Function.Bijective faP := by decide +kernel

theorem fa_sum_line {M : Type*} [AddCommMonoid M] (g : Line repFA → M) :
    ∑ f, g f = g (.inl (faL 0)) + g (.inl (faL 1)) + g (.inl (faL 2)) + g (.inl (faL 3)) +
      g (.inl (faL 4)) + (g (.inr (faP 0)) + g (.inr (faP 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ faL_bijective).sum_comp,
    ← (Equiv.ofBijective _ faP_bijective).sum_comp, Fin.sum_univ_five, Fin.sum_univ_two]
  rfl

theorem fa_ends : (Line.ends (.inl (faL 0) : Line repFA)) = (0, 1) ∧
    (Line.ends (.inl (faL 1) : Line repFA)) = (1, 2) ∧
    (Line.ends (.inl (faL 2) : Line repFA)) = (4, 3) ∧
    (Line.ends (.inl (faL 3) : Line repFA)) = (5, 4) ∧
    (Line.ends (.inl (faL 4) : Line repFA)) = (3, 5) ∧
    (Line.ends (.inr (faP 0) : Line repFA)) = (0, 4) ∧
    (Line.ends (.inr (faP 1) : Line repFA)) = (2, 3) := by decide +kernel

theorem fa_ext (v : Fin 6) :
    ((∃ t : Wick.FermionVertex kF, t.1 = v ∧ repFA.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kF, a.1 = v ∧ repFA.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kF, t.1 = v ∧ repFA.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- **The nested routing of `FA`**: `ℓ 0 = q` on the loop lines `3 → 5`, `5 → 4`, `ℓ 1 = ℓ` the
photon momentum; lines `0 → 1`: `p + ℓ`, `1 → 2`: `p + k + ℓ`, `4 → 3`: `q - ℓ`, photon
`0 → 4`: `-ℓ`, photon `2 → 3`: `ℓ`. -/
def faMom (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repFA) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p + ℓ 1
  | 2 => p + kext + ℓ 1
  | 3 => ℓ 0 - ℓ 1
  | 4 => ℓ 0
  | 5 => ℓ 0
  | 6 => -ℓ 1
  | _ => ℓ 1

theorem faMom_apply (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    faMom p kext ℓ (.inl (faL 0)) = p + ℓ 1 ∧ faMom p kext ℓ (.inl (faL 1)) = p + kext + ℓ 1 ∧
      faMom p kext ℓ (.inl (faL 2)) = ℓ 0 - ℓ 1 ∧ faMom p kext ℓ (.inl (faL 3)) = ℓ 0 ∧
      faMom p kext ℓ (.inl (faL 4)) = ℓ 0 ∧ faMom p kext ℓ (.inr (faP 0)) = -ℓ 1 ∧
      faMom p kext ℓ (.inr (faP 1)) = ℓ 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isConserved_faMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) : IsConserved repFA pOut pIn kIn (faMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4, g0, g1⟩ := fa_ends
  obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := faMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  obtain ⟨x0, x1, x2⟩ := fa_ext v
  rw [inflow, fa_sum_line, QED.TwoLoop.Insertion.externalMomentum_one_one, hmom]
  simp only [e0, e1, e2, e3, e4, g0, g1, n0, n1, n2, n3, n4, n5, n6, x0, x1, x2]
  fin_cases v
  all_goals simp
  all_goals abel

theorem fa_isChord_iff : ∀ f : Line repFA,
    IsChord f ↔ f = .inl (faL 0) ∨ f = .inl (faL 2) := by
  decide +kernel

theorem fa_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (faL 0) : Line repFA) = ℓ 0 ∧
      chordMomentum ℓ (.inl (faL 2) : Line repFA) = ℓ 1 := by
  have h0 : (Finset.univ.filter fun g : Line repFA =>
      IsChord g ∧ g.label < (Line.label (.inl (faL 0) : Line repFA))).card = 0 := by
    decide +kernel
  have h1 : (Finset.univ.filter fun g : Line repFA =>
      IsChord g ∧ g.label < (Line.label (.inl (faL 2) : Line repFA))).card = 1 := by
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

/-- The unimodular change of loop momenta of `FA`: `ℓ ↦ (ℓ 1, ℓ 0 - ℓ 1)`. -/
def faMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]

theorem isUnit_det_faMat : IsUnit faMat.det := by
  rw [Matrix.det_fin_two]
  simp [faMat]

/-- The chords of `FA` carry the frozen loop momenta at `faMat ℓ + (p, 0)`. -/
theorem fa_hchord (p kext : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repFA)
    (hf : IsChord f) : faMom p kext ℓ f =
      chordMomentum ((fun s => ∑ r, faMat s r • ℓ r) + ![p, 0]) f := by
  obtain ⟨c0, c1⟩ := fa_chordMomentum ((fun s => ∑ r, faMat s r • ℓ r) + ![p, 0])
  obtain ⟨n0, -, n2, -⟩ := faMom_apply p kext ℓ
  rcases (fa_isChord_iff f).mp hf with rfl | rfl
  · rw [c0, n0]
    simp [faMat, Fin.sum_univ_two]
    abel
  · rw [c1, n2]
    simp [faMat, Fin.sum_univ_two]
    abel

/-! ### The amplitude -/

theorem fa_prod_fermionLine {M : Type*} [CommMonoid M] (g : FermionLine repFA → M) :
    ∏ f, g f = g (faL 0) * g (faL 1) * g (faL 2) * g (faL 3) * g (faL 4) := by
  rw [← (Equiv.ofBijective _ faL_bijective).prod_comp, Fin.prod_univ_five]
  rfl

theorem fa_prod_photonLine {M : Type*} [CommMonoid M] (g : PhotonLine repFA → M) :
    ∏ f, g f = g (faP 0) * g (faP 1) := by
  rw [← (Equiv.ofBijective _ faP_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem fa_tails : (faL 0).tail = fv kF 0 ∧ (faL 1).tail = fv kF 1 ∧
    (faL 2).tail = fv kF 4 ∧ (faL 3).tail = fv kF 5 ∧ (faL 4).tail = fv kF 3 := by
  decide +kernel

theorem fa_vals : (faL 0).1 = fv kF 1 ∧ (faL 1).1 = fv kF 2 ∧ (faL 2).1 = fv kF 3 ∧
    (faL 3).1 = fv kF 4 ∧ (faL 4).1 = fv kF 5 ∧ (faP 0).1 = pg kF 0 ∧ (faP 1).1 = pg kF 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fa_heads : (faP 0).head = pg kF 4 ∧ (faP 1).head = pg kF 3 := by decide +kernel

theorem fa_cond (α β : Wick.FermionVertex kF → Fin 4) (lor : Wick.PhotonSlot kF → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repFA.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repFA.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repFA.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (lor (pg kF 1) = μ 0 ∧ (α (fv kF 2) = αOut 0 ∧ β (fv kF 0) = βIn 0)) := by
  have h0 : ∀ t, repFA.1.1 (.inl 0) = .inr t ↔ t = fv kF 2 := by decide +kernel
  have h1 : ∀ t, repFA.1.1 (.inr t) = .inl 0 ↔ t = fv kF 0 := by decide +kernel
  have h2 : ∀ a, repFA.1.2 (.inl 0) = .inr a ↔ a = pg kF 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h0, h1, h2, forall_eq]
  tauto

/-- The splitting of the fermion fields of `kF` into the open line `2, 1, 0` and the loop
`3, 4, 5`. -/
noncomputable def faSplit : Wick.FermionVertex kF ≃ Fin 3 ⊕ Fin 3 :=
  Equiv.ofBijective
    (fun t => (![.inl 2, .inl 1, .inl 0, .inr 0, .inr 1, .inr 2] : Fin 6 → _) t.1)
    (by decide +kernel)

/-- The flavouring of `kF` with the open line of flavour `Φ.openLine` and the loop of flavour
`f`. -/
def fcFlav {F : Type} (Φ : Lepton.Flavors F) (f : F) : Graded.Flavoring F kF :=
  fun t => if t.1.val < 3 then Φ.openLine else f

/-- The open-line chain of `FA`. -/
noncomputable def faChain (P : Params) (m : ℝ) (kk : Line repFA → Fin 4 → ℝ) (μ l2 l0 : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma l2 * QED.OneLoop.electronPropagator m P.ε (kk (.inl (faL 1))) * Dirac.gamma μ *
    QED.OneLoop.electronPropagator m P.ε (kk (.inl (faL 0))) * Dirac.gamma l0

/-- The loop trace of `FA`, with the counterterm matrix at the vertex `5`. -/
noncomputable def faLoop (P : Params) (M d₂ dm : ℝ) (kk : Line repFA → Fin 4 → ℝ)
    (l3 l4 : Fin 4) : ℂ :=
  Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (faL 2))) *
    Dirac.gamma l4 * QED.OneLoop.electronPropagator M P.ε (kk (.inl (faL 3))) *
    QED.TwoLoop.Insertion.fermionCtMatrix d₂ dm M (kk (.inl (faL 4))) *
    QED.OneLoop.electronPropagator M P.ε (kk (.inl (faL 4))))

theorem fa_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (f : F) (pIn kIn : Fin 1 → Fin 4 → ℝ) (kk : Line repFA → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionAmplitude P Φ D repFA (fcFlav Φ f) 0 pIn kIn kk αOut βIn μ =
      (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 *
        ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4,
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 0))) l0 l4 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 1))) l2 l3 *
          faLoop P (Φ.mass f) (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) kk l3 l4 *
          faChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := fa_tails
  obtain ⟨g0, g1⟩ := fa_heads
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := fa_vals
  have hpsi : QED.WickModel.psiMomentum₂ repFA pIn kk ⟨5, by decide⟩ = kk (.inl (faL 4)) :=
    QED.TwoLoop.Relabel.psiMomentum₂_of_isRight (by decide +kernel)
  unfold Graded.contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex kF → Fin 4, ∑ β : Wick.FermionVertex kF → Fin 4,
      ∑ lor : Wick.PhotonSlot kF → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [fa_cond, Fin.prod_univ_six, fa_prod_fermionLine, fa_prod_photonLine, t0, t1, t2,
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
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 0))) l0 l4 *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 1))) l2 l3 *
      faLoop P (Φ.mass f) (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) kk l3 l4 *
      faChain P (Φ.mass Φ.openLine) kk (μ 0) l2 l0 (αOut 0) (βIn 0) =
      ∑ lor : Wick.PhotonSlot kF → Fin 4,
      (if lor ⟨1, ⟨0, by decide⟩⟩ = μ 0 then (1 : ℂ) else 0) * (K *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 0))) (lor ⟨0, ⟨0, by decide⟩⟩)
          (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 1))) (lor ⟨2, ⟨0, by decide⟩⟩)
          (lor ⟨3, ⟨0, by decide⟩⟩) *
        faLoop P (Φ.mass f) (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) kk
          (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        faChain P (Φ.mass Φ.openLine) kk (μ 0) (lor ⟨2, ⟨0, by decide⟩⟩)
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
  · have h := sum_spinor_chain3_loop3 faSplit (x₁ := ⟨2, by decide⟩) (x₂ := ⟨1, by decide⟩)
      (x₃ := ⟨0, by decide⟩) (y₁ := ⟨3, by decide⟩) (y₂ := ⟨4, by decide⟩)
      (y₃ := ⟨5, by decide⟩) rfl rfl rfl rfl rfl rfl
      (K * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 0)))
        (lor ⟨0, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨0, by decide⟩⟩) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr (faP 1)))
        (lor ⟨2, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨0, by decide⟩⟩))
      (Dirac.gamma (lor ⟨2, ⟨0, by decide⟩⟩)) (Dirac.gamma (μ 0))
      (Dirac.gamma (lor ⟨0, ⟨0, by decide⟩⟩))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (faL 1))))
      (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (faL 0))))
      (Dirac.gamma (lor ⟨3, ⟨0, by decide⟩⟩)) (Dirac.gamma (lor ⟨4, ⟨0, by decide⟩⟩))
      (QED.TwoLoop.Insertion.fermionCtMatrix (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0)
        (Φ.mass f) (kk (.inl (faL 4))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (faL 2))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (faL 3))))
      (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl (faL 4)))) (αOut 0) (βIn 0)
    simp only [hL, ite_true, one_mul]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hK]
      simp only [QED.TwoLoop.Insertion.fermionCtMatrix]
      push_cast
      by_cases ha : α ⟨2, by decide⟩ = αOut 0 <;> by_cases hb : β ⟨0, by decide⟩ = βIn 0 <;>
        simp only [ha, hb, and_true, and_false, ite_true, ite_false] <;> ring
    · unfold faLoop faChain
      ring
  · simp only [hL, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The preserved flavourings -/

theorem fa_perm : repFA.1.1 (.inl 0) = .inr (fv kF 2) ∧
    repFA.1.1 (.inr (fv kF 2)) = .inr (fv kF 1) ∧
    repFA.1.1 (.inr (fv kF 1)) = .inr (fv kF 0) ∧
    repFA.1.1 (.inr (fv kF 0)) = .inl 0 ∧
    repFA.1.1 (.inr (fv kF 3)) = .inr (fv kF 4) ∧
    repFA.1.1 (.inr (fv kF 4)) = .inr (fv kF 5) ∧
    repFA.1.1 (.inr (fv kF 5)) = .inr (fv kF 3) := by decide +kernel

theorem kF_fv_cases : ∀ t : Wick.FermionVertex kF, t = fv kF 0 ∨ t = fv kF 1 ∨
    t = fv kF 2 ∨ t = fv kF 3 ∨ t = fv kF 4 ∨ t = fv kF 5 := by decide

theorem fa_open : ∀ i, ¬ repFA.1.1.SameCycle (.inl i) (.inr (fv kF 3)) := by decide +kernel

theorem fa_all : ∀ x, (∃ i, repFA.1.1.SameCycle x (.inl i)) ∨
    repFA.1.1.SameCycle x (.inr (fv kF 3)) := by
  decide +kernel

/-- **The flavourings preserved by `repFA`**: the open line has the open-line flavour, the loop
one flavour. -/
theorem fa_preserves_iff {F : Type} (Φ : Lepton.Flavors F) (φ : Graded.Flavoring F kF) :
    Graded.Preserves Φ repFA φ ↔ φ = fcFlav Φ (φ (fv kF 3)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := fa_perm
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
    · exact h5.symm.trans h6.symm
    · exact h6.symm
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

/-- **The regulated amplitude of `repFA`** is the sum over the loop flavour of its coefficient
times the amplitude. -/
theorem fa_regulatedAmplitude (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (kk : Line repFA → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.regulatedAmplitude P Φ D repFA 0 pIn kIn kk αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) *
        Graded.contractionAmplitude P Φ D repFA (fcFlav Φ f) 0 pIn kIn kk αOut βIn μ := by
  classical
  unfold Graded.regulatedAmplitude
  refine Finset.sum_nbij' (fun φ => φ (fv kF 3)) (fcFlav Φ) (fun _ _ => Finset.mem_univ _)
    (fun f _ => ?_) (fun φ hφ => ?_) (fun f _ => ?_) (fun φ hφ => ?_)
  · rw [Finset.mem_filter, fa_preserves_iff]
    exact ⟨Finset.mem_univ _, by simp [fcFlav, fv]⟩
  · exact ((fa_preserves_iff Φ φ).mp (Finset.mem_filter.mp hφ).2).symm
  · simp [fcFlav, fv]
  · have hp := (Finset.mem_filter.mp hφ).2
    rw [loopWeight_eq_of_one_loop Φ hp (fv kF 3) fa_open fa_all]
    conv_lhs => rw [(fa_preserves_iff Φ φ).mp hp]
    simp [fcFlav, fv]

/-! ### The Wick factorization -/

/-- The inner integrand of `FA`: the integrand of the class `F0` at `(-ℓ, ℓ)` and the loop
momentum `q`. -/
noncomputable def faInner (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (ℓ q : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repF0 0
    ![] ![-ℓ, -(-ℓ)] (QED.GradedProof.VP2.f0Mom (-ℓ) q) ![] ![] ![a, b]

/-- **The Wick factorization of `FA`**: in the nested routing, the integrand of the value of
`repFA` is the outer factor times the inner integrand of `F0`, summed over the photon slot. -/
theorem fa_routedIntegrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    routedIntegrand P Φ D repFA 0 2 (fun _ => p) (fun _ => p' - p) (faMom p (p' - p) ℓ)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (faInner P Φ D) ℓ := by
  have hq' : -ℓ 1 + ℓ 0 = ℓ 0 - ℓ 1 := by abel
  have hp : p + (p' - p) + ℓ 1 = p' + ℓ 1 := by abel
  simp only [routedIntegrand, fa_regulatedAmplitude, fa_amplitude, outerInner, faInner,
    QED.GradedProof.VP2.f0_integrand P Φ D id (fun _ => ⟨rfl, rfl⟩), lOuter,
    QED.ChainProof.SetANestV.nestOuter, ← QED.GradedProof.VP2.trace_ins_smul,
    QED.GradedProof.VP2.zk_true, QED.GradedProof.VP2.zk_false, QED.GradedProof.VP2.kF,
    QED.TwoLoop.Insertion.vertexChain, faLoop, faChain,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hq', id]
  simp only [show faMom p (p' - p) ℓ (.inl (faL 0)) = p + ℓ 1 from rfl,
    show faMom p (p' - p) ℓ (.inl (faL 1)) = p' + ℓ 1 from hp,
    show faMom p (p' - p) ℓ (.inl (faL 2)) = ℓ 0 - ℓ 1 from rfl,
    show faMom p (p' - p) ℓ (.inl (faL 3)) = ℓ 0 from rfl,
    show faMom p (p' - p) ℓ (.inl (faL 4)) = ℓ 0 from rfl,
    show faMom p (p' - p) ℓ (.inr (faP 0)) = -ℓ 1 from rfl,
    show faMom p (p' - p) ℓ (.inr (faP 1)) = ℓ 1 from rfl,
    Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm_out_two]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl
      fun ρ _ => ?_
  rw [QED.TwoLoop.Insertion.photonPropagator_neg', QED.TwoLoop.Insertion.photonPropagator_neg']
  push_cast
  ring

/-! ### The inner integrand -/

/-- **The energy-first integral of the inner integrand of `FA`** is the value of the class `F0`
at `(-ℓ, ℓ)`. -/
theorem efi_faInner (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (ℓ : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.energyFirstIntegral (fun q => faInner P Φ D ℓ q a b) =
      QED.GradedProof.VP2.val0 P Φ D (-ℓ) a b QED.GradedProof.VP2.repF0 := by
  have hc := QED.GradedProof.VP2.f0_isChord_iff
  unfold QED.GradedProof.VP2.val0 Graded.contractionValue
  rw [QED.TwoLoop.Insertion.loopCount_eq_one_of_unique hc]
  simp only [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc
    (QED.GradedProof.VP2.f0Mom (-ℓ)) (QED.GradedProof.VP2.f0_isConserved (-ℓ))
    (fun q => (QED.GradedProof.VP2.f0Mom_apply (-ℓ) q).1)]
  rw [QED.TwoLoop.jointEnergyFirstIntegral_one_eq (fun q => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
    Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repF0 0 ![] ![-ℓ, -(-ℓ)]
      (QED.GradedProof.VP2.f0Mom (-ℓ) q) ![] ![] ![a, b])]
  simp only [faInner, mul_one]

/-- **The inner integrand of `FA`** is the block-summed inserted bubble with the insertion line
at `q` and the other line at `(-1) • ℓ + q`. -/
theorem faInner_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    faInner P Φ D = fun k q a b => ∑ f, (Φ.coeff f : ℂ) * (QED.GradedProof.VP2.kF P.e *
      QED.GradedProof.VP2.insG (Dirac.gamma b) (Dirac.gamma a)
        ((fun r => P.e ^ 2 * D.d₂ r 0) (rep f)) ((fun r => P.e ^ 2 * D.dm r 0) (rep f))
        (Φ.mass f) P.ε (QED.GradedProof.VP2.zk ((-1 : ℝ) • k) true q)
        (QED.GradedProof.VP2.zk ((-1 : ℝ) • k) false q)) := by
  funext ℓ q a b
  rw [faInner, QED.GradedProof.VP2.f0_integrand P Φ D rep hD, neg_one_smul]

/-! ### The nested form -/

/-- **The nested form of `FA`, given the inner bound.** Under the hypotheses `IntHypA` of (HA₀)
and the inner bound `OneLoopInnerBound a b` (`0 ≤ a < 9`, `3 < b`) of the block-summed inserted
bubble of `faInner_eq`, the class `FA` is in nested form (`LoopNested`) with the photon tensor
`X(k)^{ab} = (1/i) val0(F0)(-k)^{ab}`. -/
theorem loopNested_repFA_of_bound (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep)
    (p' p : Fin 4 → ℝ) {a₀ b₀ : ℝ} (ha0 : 0 ≤ a₀) (ha : a₀ < 9) (hb : 3 < b₀)
    (hG : OneLoopInnerBound a₀ b₀ fun k q a b => ∑ f, (Φ.coeff f : ℂ) *
      (QED.GradedProof.VP2.kF P.e *
        QED.GradedProof.VP2.insG (Dirac.gamma b) (Dirac.gamma a)
          ((fun r => P.e ^ 2 * D.d₂ r 0) (rep f)) ((fun r => P.e ^ 2 * D.dm r 0) (rep f))
          (Φ.mass f) P.ε (QED.GradedProof.VP2.zk ((-1 : ℝ) • k) true q)
          (QED.GradedProof.VP2.zk ((-1 : ℝ) • k) false q))) :
    LoopNested P Φ D repFA
      (fun k a b => (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repF0)
      p' p := by
  rw [← faInner_eq P Φ D rep fun f => (hH.hD f).2] at hG
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_faMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  have hR : ∀ μ i j : Fin 4, (fun ℓ => routedIntegrand P Φ D repFA 0 2 (fun _ => p)
      (fun _ => p' - p) (faMom p (p' - p) ℓ) (fun _ => i) (fun _ => j) (fun _ => μ)) =
      outerInner (lOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) (faInner P Φ D) :=
    fun μ i j => funext fun ℓ => fa_routedIntegrand P Φ D p' p μ i j ℓ
  have h := loopNested_of_lOuter P Φ D repFA p' p hH.hε ha0 ha hb hG (fun μ i j => ?_)
    (fun μ i j => ?_)
  · have e : (fun k a b =>
        (1 / I) * QED.OneLoop.energyFirstIntegral fun q => faInner P Φ D k q a b) =
        fun k a b => (1 / I) *
          QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repF0 :=
      funext fun k => funext fun a => funext fun b => by rw [efi_faInner]
    rwa [e] at h
  · rw [contractionValue_eq_of_routing P Φ D repFA 0 loopCount_repFA (faMom p (p' - p)) hcons
      faMat isUnit_det_faMat ![p, 0] (fa_hchord p (p' - p)), hR]
  · rw [← hR]
    exact jointEnergyFirstIntegrable_of_routing P Φ D repFA 0 loopCount_repFA
      (faMom p (p' - p)) hcons faMat isUnit_det_faMat ![p, 0] (fa_hchord p (p' - p)) _ _ _
      (classIntA_repFA P Φ D rep hH (fun _ => p') (fun _ => p) (fun _ => p' - p) hmom _ _ _)

end QED.ChainProof.SetANest

end
