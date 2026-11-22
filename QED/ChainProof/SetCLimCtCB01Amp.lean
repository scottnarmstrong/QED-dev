/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCDAmp
public import QED.TwoLoop.NestedVPAmplitude
public import QED.ChainProof.SetCLinkIntCB01
public import QED.ChainProof.SetCLinkIntDeg6

/-!
# Set (c): the T1 amplitudes of the classes `CB0`, `CB1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`repCB0`, `repCB1` are the one-loop vertex with a `fermionCt` vertex on its outgoing (`CB0`,
vertex `1`), resp. incoming (`CB1`, vertex `2`), internal electron line and a closed fermion loop
(vertices `4, 5`) on its photon line. This file computes their T1 values (T₁₀):

* the spinor sum over the six vertices splits into the open chain and the loop trace
  (`spinSum6`);
* the preserved flavorings are the loop flavours `f` (open line flavour `0`), with regulator
  weight `c_f` (`regulatedAmplitude₂_cb0`, `regulatedAmplitude₂_cb1`);
* the amplitude of flavour `f` at arbitrary line momenta (`cb0_amplitude`, `cb1_amplitude`);
* the frozen routing at the loop momenta `cbArg p' λ` is the class routing of `VP`: open lines
  `p' + λ₁`, `p + λ₁`, photons `±λ₁`, loop `λ₀ - λ₁`, `λ₀` (`cb0_lineMomentum`,
  `cb1_lineMomentum`);
* **`contractionValue₂_cb0`, `contractionValue₂_cb1`**: the values as the joint integral (T₉) of
  `(2π)⁻⁸ ∑_f c_f cbAmp P f d p' p α β μ λ`, `d = 1` for `CB0` and `d = 0` for `CB1`, where the
  open line `d` carries the insertion `S̃ X S̃` (`cbLine`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCPauli.CB01

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel
open QED.TwoLoop.Insertion QED.ChainProof.SetCLink
open QED.ChainProof.Enum (fv pg pc)
open QED.GradedProof.X0 (loopCoeff extPart lineMomentum₂_eq_loopCoeff edgeChord edgeSide edgeOf)
open QED.TwoLoop.Enumeration (lineData)

/-! ### Spinor sums over six vertices -/

section Spin

variable {κ : Fin 6 → Wick.VertexKind}

/-- The functions on six fermion vertices as pairs of functions on the open line `0, …, 3` and
on the loop `4, 5`. -/
def splitEquiv6 (hκ : ∀ t, κ t ≠ .photonCt) (R : Type) :
    (Wick.FermionVertex κ → R) ≃ (Fin 4 → R) × (Fin 2 → R) where
  toFun α := (fun i => α ⟨Fin.castLE (by norm_num) i, hκ _⟩, fun j => α ⟨Fin.natAdd 4 j, hκ _⟩)
  invFun p t := if h : t.1.val < 4 then p.1 ⟨t.1.val, h⟩ else p.2 ⟨t.1.val - 4, by omega⟩
  left_inv α := by
    funext t
    obtain ⟨j, hj⟩ := t
    fin_cases j <;> rfl
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> rfl

theorem splitEquiv6_symm_apply (hκ : ∀ t, κ t ≠ .photonCt) {R : Type} (a : Fin 4 → R)
    (b : Fin 2 → R) :
    (splitEquiv6 hκ R).symm (a, b) ⟨0, hκ 0⟩ = a 0 ∧
      (splitEquiv6 hκ R).symm (a, b) ⟨1, hκ 1⟩ = a 1 ∧
      (splitEquiv6 hκ R).symm (a, b) ⟨2, hκ 2⟩ = a 2 ∧
      (splitEquiv6 hκ R).symm (a, b) ⟨3, hκ 3⟩ = a 3 ∧
      (splitEquiv6 hκ R).symm (a, b) ⟨4, hκ 4⟩ = b 0 ∧
      (splitEquiv6 hκ R).symm (a, b) ⟨5, hκ 5⟩ = b 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The spinor sum of a two-vertex loop is a trace. -/
theorem sum_loop2 (B₁ B₂ T₁ T₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ a : Fin 2 → Fin 4, ∑ b : Fin 2 → Fin 4,
        B₁ (a 0) (b 0) * T₁ (b 0) (a 1) * B₂ (a 1) (b 1) * T₂ (b 1) (a 0) =
      Matrix.trace (B₁ * T₁ * B₂ * T₂) := by
  rw [← (finTwoArrowEquiv (Fin 4)).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [← (finTwoArrowEquiv (Fin 4)).symm.sum_comp, Fintype.sum_prod_type,
    finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  conv_rhs => rw [Finset.sum_comm]

/-- The summand of the spinor sum of an open chain through `0, 1, 2, 3` (outgoing vertex `0`)
and a closed loop `4 → 5 → 4`. -/
def spinTerm6 (hκ : ∀ t, κ t ≠ .photonCt) (G : Fin 6 → Matrix (Fin 4) (Fin 4) ℂ)
    (S01 S12 S23 S45 S54 : Matrix (Fin 4) (Fin 4) ℂ) (αe βe : Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) : ℂ :=
  (if α ⟨0, hκ 0⟩ = αe ∧ β ⟨3, hκ 3⟩ = βe then (1 : ℂ) else 0) *
    (G 0 (α ⟨0, hκ 0⟩) (β ⟨0, hκ 0⟩) * G 1 (α ⟨1, hκ 1⟩) (β ⟨1, hκ 1⟩) *
      G 2 (α ⟨2, hκ 2⟩) (β ⟨2, hκ 2⟩) * G 3 (α ⟨3, hκ 3⟩) (β ⟨3, hκ 3⟩) *
      G 4 (α ⟨4, hκ 4⟩) (β ⟨4, hκ 4⟩) * G 5 (α ⟨5, hκ 5⟩) (β ⟨5, hκ 5⟩) *
      (S01 (β ⟨0, hκ 0⟩) (α ⟨1, hκ 1⟩) * S12 (β ⟨1, hκ 1⟩) (α ⟨2, hκ 2⟩) *
        S23 (β ⟨2, hκ 2⟩) (α ⟨3, hκ 3⟩) * S45 (β ⟨4, hκ 4⟩) (α ⟨5, hκ 5⟩) *
        S54 (β ⟨5, hκ 5⟩) (α ⟨4, hκ 4⟩)))

/-- **The spinor sum of six vertices**: the open chain `G₀ S₀₁ G₁ S₁₂ G₂ S₂₃ G₃` times the
trace of the loop `Tr[G₄ S₄₅ G₅ S₅₄]`. -/
theorem spinSum6 (hκ : ∀ t, κ t ≠ .photonCt) (G : Fin 6 → Matrix (Fin 4) (Fin 4) ℂ)
    (S01 S12 S23 S45 S54 : Matrix (Fin 4) (Fin 4) ℂ) (αe βe : Fin 4) :
    ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
        spinTerm6 hκ G S01 S12 S23 S45 S54 αe βe α β =
      (G 0 * S01 * G 1 * S12 * G 2 * S23 * G 3) αe βe *
        Matrix.trace (G 4 * S45 * G 5 * S54) := by
  have hT : ∀ α β, spinTerm6 hκ G S01 S12 S23 S45 S54 αe βe α β =
      ((if α ⟨0, hκ 0⟩ = αe ∧ β ⟨3, hκ 3⟩ = βe then (1 : ℂ) else 0) *
        (1 * (G 0 (α ⟨0, hκ 0⟩) (β ⟨0, hκ 0⟩) * S01 (β ⟨0, hκ 0⟩) (α ⟨1, hκ 1⟩) *
          G 1 (α ⟨1, hκ 1⟩) (β ⟨1, hκ 1⟩) * S12 (β ⟨1, hκ 1⟩) (α ⟨2, hκ 2⟩) *
          G 2 (α ⟨2, hκ 2⟩) (β ⟨2, hκ 2⟩) * S23 (β ⟨2, hκ 2⟩) (α ⟨3, hκ 3⟩) *
          G 3 (α ⟨3, hκ 3⟩) (β ⟨3, hκ 3⟩)))) *
        (G 4 (α ⟨4, hκ 4⟩) (β ⟨4, hκ 4⟩) * S45 (β ⟨4, hκ 4⟩) (α ⟨5, hκ 5⟩) *
          G 5 (α ⟨5, hκ 5⟩) (β ⟨5, hκ 5⟩) * S54 (β ⟨5, hκ 5⟩) (α ⟨4, hκ 4⟩)) := fun α β => by
    unfold spinTerm6
    ring
  simp only [hT]
  rw [← (splitEquiv6 hκ (Fin 4)).symm.sum_comp]
  simp only [← (splitEquiv6 hκ (Fin 4)).symm.sum_comp (fun β => _ * _),
    Fintype.sum_prod_type, splitEquiv6_symm_apply]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_spinor_chain4 (X := Fin 4) (x₁ := 0) (x₂ := 1) (x₃ := 2) (x₄ := 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sum_loop2, one_mul]

end Spin

/-! ### Five lines -/

theorem prod_eq_of_five {X M : Type*} [Fintype X] [DecidableEq X] [CommMonoid M]
    {a b c d e : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) (g : X → M) :
    ∏ x, g x = g a * g b * g c * g d * g e := by
  have : (Finset.univ : Finset X) = {a, b, c, d, e} := by
    ext x
    simpa using hX x
  rw [this, Finset.prod_insert (by simp [hab, hac, had, hae]),
    Finset.prod_insert (by simp [hbc, hbd, hbe]), Finset.prod_insert (by simp [hcd, hce]),
    Finset.prod_pair hde]
  simp only [mul_assoc]

/-! ### `CB0`: the counterterm on the outgoing line -/

section CB0

theorem kCB0_ne : ∀ t, kCB0 t ≠ .photonCt := by decide

/-- The flavoring with the open line of flavour `0` and the loop `4, 5` of flavour `f`. -/
def flavB0 (f : Fin 3) : Flavoring kCB0 :=
  ⟨fun t => if 4 ≤ t.1.val then f else 0, fun t ht => by
    have h : ∀ t : Wick.FermionVertex kCB0, kCB0 t.1 ≠ .gauge → t.1.val < 4 := by decide
    simp [Nat.not_le.mpr (h t ht)]⟩

/-- The line `0 — 1` (outgoing end `0`). -/
def cb0L0 : FermionLine repCB0 := ⟨fv kCB0 0, by decide +kernel⟩
/-- The line `1 — 2`. -/
def cb0L1 : FermionLine repCB0 := ⟨fv kCB0 1, by decide +kernel⟩
/-- The line `2 — 3`. -/
def cb0L2 : FermionLine repCB0 := ⟨fv kCB0 2, by decide +kernel⟩
/-- The loop line `4 — 5`. -/
def cb0L4 : FermionLine repCB0 := ⟨fv kCB0 4, by decide +kernel⟩
/-- The loop line `5 — 4`. -/
def cb0L5 : FermionLine repCB0 := ⟨fv kCB0 5, by decide +kernel⟩
/-- The photon line `0 — 4`. -/
def cb0GA : PhotonLine repCB0 := ⟨pg kCB0 0, by decide +kernel⟩
/-- The photon line `3 — 5`. -/
def cb0GB : PhotonLine repCB0 := ⟨pg kCB0 3, by decide +kernel⟩

theorem cb0_fermionLine_cases : ∀ f : FermionLine repCB0,
    f = cb0L0 ∨ f = cb0L1 ∨ f = cb0L2 ∨ f = cb0L4 ∨ f = cb0L5 := by
  decide +kernel

theorem cb0_photonLine_cases : ∀ g : PhotonLine repCB0, g = cb0GA ∨ g = cb0GB := by
  decide +kernel

theorem cb0_tails : cb0L0.tail = fv kCB0 1 ∧ cb0L1.tail = fv kCB0 2 ∧ cb0L2.tail = fv kCB0 3 ∧
    cb0L4.tail = fv kCB0 5 ∧ cb0L5.tail = fv kCB0 4 ∧ cb0GA.head = pg kCB0 4 ∧
    cb0GB.head = pg kCB0 5 := by
  decide +kernel

theorem cb0_cond (α β : Wick.FermionVertex kCB0 → Fin 4) (lor : Wick.PhotonSlot kCB0 → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repCB0.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repCB0.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repCB0.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kCB0 2) = μ 0 ∧ (α ⟨0, kCB0_ne 0⟩ = αOut 0 ∧ β ⟨3, kCB0_ne 3⟩ = βIn 0) := by
  have h1 : ∀ t, repCB0.1.1 (.inl 0) = .inr t ↔ t = fv kCB0 0 := by decide +kernel
  have h2 : ∀ t, repCB0.1.1 (.inr t) = .inl 0 ↔ t = fv kCB0 3 := by decide +kernel
  have h3 : ∀ a, repCB0.1.2 (.inl 0) = .inr a ↔ a = pg kCB0 2 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem cb0_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line repCB0 → Fin 4 → ℝ)
    (h : kCB0 1 ≠ .photonCt) : psiMomentum₂ repCB0 pIn k ⟨1, h⟩ = k (.inl cb0L1) :=
  psiMomentum₂_of_isRight (t := fv kCB0 1) (by decide +kernel)

theorem flavB0_apply (f : Fin 3) :
    (∀ h, (flavB0 f).1 ⟨0, h⟩ = 0) ∧ (∀ h, (flavB0 f).1 ⟨1, h⟩ = 0) ∧
      (∀ h, (flavB0 f).1 ⟨2, h⟩ = 0) ∧ (∀ h, (flavB0 f).1 ⟨4, h⟩ = f) ∧
      (∀ h, (flavB0 f).1 ⟨5, h⟩ = f) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The open chain of `CB0` at line momenta: `γ^ρ S̃(k₀) X(k₁) S̃(k₁) γ^μ S̃(k₂) γ^ν`. -/
noncomputable def cb0Chain (P : Params) (k0 k1 k2 : Fin 4 → ℝ) (μ ρ ν : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε k0 * fermionCtMatrix P.δ₂ P.δm P.m k1 *
    QED.OneLoop.electronPropagator P.m P.ε k1 * Dirac.gamma μ *
    QED.OneLoop.electronPropagator P.m P.ε k2 * Dirac.gamma ν

/-- **The amplitude of `repCB0`** for the loop flavour `f`, at arbitrary line momenta. -/
theorem cb0_amplitude (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line repCB0 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repCB0 (flavB0 f) pIn kIn k αOut βIn μ =
      (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 * ∑ l0 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
        cb0Chain P (k (.inl cb0L0)) (k (.inl cb0L1)) (k (.inl cb0L2)) (μ 0) l0 l3 (αOut 0)
            (βIn 0) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb0GA)) l0 l4 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb0GB)) l3 l5 *
          Matrix.trace (Dirac.gamma l4 *
            QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb0L4)) * Dirac.gamma l5 *
            QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb0L5))) := by
  obtain ⟨t0, t1, t2, t4, t5, h4, h5⟩ := cb0_tails
  set G : (Wick.PhotonSlot kCB0 → Fin 4) → Fin 6 → Matrix (Fin 4) (Fin 4) ℂ := fun lor =>
    ![Dirac.gamma (lor (pg kCB0 0)), fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cb0L1)),
      Dirac.gamma (lor (pg kCB0 2)), Dirac.gamma (lor (pg kCB0 3)),
      Dirac.gamma (lor (pg kCB0 4)), Dirac.gamma (lor (pg kCB0 5))] with hG
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kCB0 → Fin 4, ∑ β : Wick.FermionVertex kCB0 → Fin 4,
      ∑ lor : Wick.PhotonSlot kCB0 → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kCB0 → Fin 4,
    (if lor (pg kCB0 2) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb0GA)) (lor (pg kCB0 0))
            (lor (pg kCB0 4)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb0GB)) (lor (pg kCB0 3))
            (lor (pg kCB0 5))) *
        ((G lor 0 * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cb0L0)) * G lor 1 *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cb0L1)) * G lor 2 *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cb0L2)) * G lor 3) (αOut 0) (βIn 0) *
          Matrix.trace (G lor 4 * QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb0L4)) *
            G lor 5 * QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb0L5))))) = _)
  · rw [← spinSum6 kCB0_ne (G lor), ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold spinTerm6
    simp only [cb0_cond, Fin.prod_univ_six,
      prod_eq_of_five (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) cb0_fermionLine_cases,
      prod_eq_of_two (by decide) cb0_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB0 0 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show kCB0 1 = .fermionCt from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB0 2 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB0 3 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB0 4 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB0 5 = .gauge from rfl),
      t0, t1, t2, t4, t5, h4, h5, ite_and_eq_mul, hG]
    simp only [show cb0L0.1 = fv kCB0 0 from rfl, show cb0L1.1 = fv kCB0 1 from rfl,
      show cb0L2.1 = fv kCB0 2 from rfl, show cb0L4.1 = fv kCB0 4 from rfl,
      show cb0L5.1 = fv kCB0 5 from rfl, show cb0GA.1 = pg kCB0 0 from rfl,
      show cb0GB.1 = pg kCB0 3 from rfl, pg, fv, flavB0_apply, cb0_psiMomentum,
      Matrix.cons_val]
    simp only [Params.mass, Matrix.cons_val_zero, fermionCtMatrix]
    ring
  · have n0 : pg kCB0 0 ≠ pg kCB0 2 := by decide
    have n3 : pg kCB0 3 ≠ pg kCB0 2 := by decide
    have n30 : pg kCB0 3 ≠ pg kCB0 0 := by decide
    have n4 : pg kCB0 4 ≠ pg kCB0 2 := by decide
    have n40 : pg kCB0 4 ≠ pg kCB0 0 := by decide
    have n43 : pg kCB0 4 ≠ pg kCB0 3 := by decide
    have n5 : pg kCB0 5 ≠ pg kCB0 2 := by decide
    have n50 : pg kCB0 5 ≠ pg kCB0 0 := by decide
    have n53 : pg kCB0 5 ≠ pg kCB0 3 := by decide
    have n54 : pg kCB0 5 ≠ pg kCB0 4 := by decide
    rw [sum_pi_five (x₁ := pg kCB0 2) (x₂ := pg kCB0 0) (x₃ := pg kCB0 3) (x₄ := pg kCB0 4)
      (x₅ := pg kCB0 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [hG, ite_true, n0, n3, n30, n4, n40, n43, n5, n50, n53, n54, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Matrix.cons_val]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    unfold cb0Chain
    ring

/-! #### The preserved flavorings -/

theorem repCB0_pow : repCB0.1.1 ^ 10 = 1 := by decide +kernel

theorem cb0_cycles : ∀ x : Fin 1 ⊕ Wick.FermionVertex kCB0,
    (Equiv.Perm.SameCycle repCB0.1.1 x (.inl 0) ∧ ∀ t, x = .inr t → t.1.val < 4) ∨
      (Equiv.Perm.SameCycle repCB0.1.1 x (.inr (fv kCB0 4)) ∧ ∀ t, x = .inr t → 4 ≤ t.1.val) := by
  simp only [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 10) repCB0_pow]
  decide +kernel

theorem cb0_not_sameCycle :
    ¬ Equiv.Perm.SameCycle repCB0.1.1 (.inl 0) (.inr (fv kCB0 4)) := by
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 10) repCB0_pow]
  decide +kernel

theorem preserves_flavB0 : ∀ f : Fin 3, Preserves repCB0 (flavB0 f) := by
  unfold Preserves
  decide +kernel

/-- **The preserved flavorings of `repCB0`**: the open line has flavour `0`, the loop one
flavour. -/
theorem preserves_iff_cb0 (φ : Flavoring kCB0) :
    Preserves repCB0 φ ↔ φ = flavB0 (φ.1 (fv kCB0 4)) := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_flavB0 _⟩
  rcases cb0_cycles (.inr t) with ⟨h, ht⟩ | ⟨h, ht⟩
  · have := fermionFlavor_eq_of_sameCycle hφ h
    simp only [fermionFlavor] at this
    simp [this, flavB0, Nat.not_le.mpr (ht t rfl)]
  · have := fermionFlavor_eq_of_sameCycle hφ h
    simp only [fermionFlavor] at this
    simp [this, flavB0, ht t rfl]

theorem sum_preserves_cb0 {M : Type*} [AddCommMonoid M] [DecidablePred (Preserves repCB0)]
    (F : Flavoring kCB0 → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring kCB0)).filter (Preserves repCB0), F φ =
      ∑ f : Fin 3, F (flavB0 f) :=
  Finset.sum_nbij' (fun φ => φ.1 (fv kCB0 4)) flavB0 (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_flavB0 f⟩)
    (fun φ hφ => ((preserves_iff_cb0 φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => rfl)
    (fun φ hφ => by rw [← (preserves_iff_cb0 φ).mp (Finset.mem_filter.mp hφ).2])

/-- The closed loop `4 → 5 → 4` of `repCB0`. -/
def loopCB0 : ClosedLoop repCB0 :=
  ⟨Quotient.mk _ (.inr (fv kCB0 4)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact cb0_not_sameCycle (Quotient.exact h)⟩

theorem eq_loopCB0 (q : ClosedLoop repCB0) : q = loopCB0 := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases cb0_cycles x with ⟨h, -⟩ | ⟨h, -⟩
  · exact absurd (Quotient.sound h.symm) (hq 0)
  · exact Quotient.sound h

open scoped Classical in
/-- The regulator weight of the flavour-`f` loop is `c_f`. -/
theorem loopWeight_flavB0 (P : Params) (f : Fin 3) :
    loopWeight P repCB0 (flavB0 f) = P.loopCoeff f := by
  rw [loopWeight, Fintype.prod_eq_single loopCB0 fun q hq => absurd (eq_loopCB0 q) hq]
  have hq : (Quotient.mk _ loopCB0.1.out : Quotient (Equiv.Perm.SameCycle.setoid repCB0.1.1)) =
      Quotient.mk _ (.inr (fv kCB0 4)) := Quotient.out_eq _
  rw [fermionFlavor_eq_of_sameCycle (preserves_flavB0 f) (Quotient.exact hq)]
  rfl

open scoped Classical in
/-- **The regulated amplitude of `repCB0`** is the sum over the loop flavour. -/
theorem regulatedAmplitude₂_cb0 (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line repCB0 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P repCB0 pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P repCB0 (flavB0 f) pIn kIn k αOut βIn μ := by
  rw [regulatedAmplitude₂, sum_preserves_cb0]
  simp only [loopWeight_flavB0]

/-! #### The class routing -/

/-- The unimodular change from the class loop momenta of `VP` to the frozen loop momenta of
`CB0`, `CB1`: `(ℓ₀, ℓ₁) = (λ₁ + p', λ₀ - λ₁)`. -/
def cbMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]

theorem isUnit_det_cbMat : IsUnit cbMat.det := by
  rw [Matrix.det_fin_two]
  simp [cbMat]

/-- The frozen loop momenta at the class loop momenta `λ`. -/
def cbArg (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, cbMat s r • ℓ r) + ![p', 0]

theorem cbArg_apply (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbArg p' ℓ 0 = ℓ 1 + p' ∧ cbArg p' ℓ 1 = ℓ 0 - ℓ 1 := by
  constructor <;> funext μ <;> simp [cbArg, cbMat, Fin.sum_univ_two]; ring

theorem cb0_ext (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 6) :
    QED.WickModel.externalMomentum repCB0 pOut pIn kIn v =
      (if v = 3 then pIn 0 else 0) + (if v = 2 then kIn 0 else 0) -
        (if v = 0 then pOut 0 else 0) := by
  rw [externalMomentum_one_one]
  obtain ⟨h1, h2, h3⟩ := ext_CB0 v
  simp only [h1, h2, h3]

theorem cb0_loopCoeff :
    (loopCoeff repCB0 (.inl cb0L0) 0 = 1 ∧ loopCoeff repCB0 (.inl cb0L0) 1 = 0) ∧
    (loopCoeff repCB0 (.inl cb0L1) 0 = 1 ∧ loopCoeff repCB0 (.inl cb0L1) 1 = 0) ∧
    (loopCoeff repCB0 (.inl cb0L2) 0 = 1 ∧ loopCoeff repCB0 (.inl cb0L2) 1 = 0) ∧
    (loopCoeff repCB0 (.inl cb0L4) 0 = 0 ∧ loopCoeff repCB0 (.inl cb0L4) 1 = 1) ∧
    (loopCoeff repCB0 (.inl cb0L5) 0 = 1 ∧ loopCoeff repCB0 (.inl cb0L5) 1 = 1) ∧
    (loopCoeff repCB0 (.inr cb0GA) 0 = 1 ∧ loopCoeff repCB0 (.inr cb0GA) 1 = 0) ∧
    (loopCoeff repCB0 (.inr cb0GB) 0 = -1 ∧ loopCoeff repCB0 (.inr cb0GB) 1 = 0) := by
  decide +kernel

theorem cb0_extPart (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0) :
    extPart repCB0 pOut pIn kIn (.inl cb0L0) = 0 ∧
    extPart repCB0 pOut pIn kIn (.inl cb0L1) = 0 ∧
    extPart repCB0 pOut pIn kIn (.inl cb0L2) = -kIn 0 ∧
    extPart repCB0 pOut pIn kIn (.inl cb0L4) = 0 ∧
    extPart repCB0 pOut pIn kIn (.inl cb0L5) = -pOut 0 ∧
    extPart repCB0 pOut pIn kIn (.inr cb0GA) = -pOut 0 ∧
    extPart repCB0 pOut pIn kIn (.inr cb0GB) = pOut 0 := by
  have hc : edgeChord (lineData repCB0) (edgeOf (.inl cb0L0)) = true ∧
      edgeChord (lineData repCB0) (edgeOf (.inl cb0L1)) = false ∧
      edgeChord (lineData repCB0) (edgeOf (.inl cb0L2)) = false ∧
      edgeChord (lineData repCB0) (edgeOf (.inl cb0L4)) = true ∧
      edgeChord (lineData repCB0) (edgeOf (.inl cb0L5)) = false ∧
      edgeChord (lineData repCB0) (edgeOf (.inr cb0GA)) = false ∧
      edgeChord (lineData repCB0) (edgeOf (.inr cb0GB)) = false := by
    decide +kernel
  have hs : edgeSide (lineData repCB0) (edgeOf (.inl cb0L1)) = {0, 2, 3, 4, 5} ∧
      edgeSide (lineData repCB0) (edgeOf (.inl cb0L2)) = {0, 3, 4, 5} ∧
      edgeSide (lineData repCB0) (edgeOf (.inl cb0L5)) = {0, 4} ∧
      edgeSide (lineData repCB0) (edgeOf (.inr cb0GA)) = {0} ∧
      edgeSide (lineData repCB0) (edgeOf (.inr cb0GB)) = {1, 2, 3} := by
    decide +kernel
  obtain ⟨c0, c1, c2, c4, c5, cA, cB⟩ := hc
  obtain ⟨s1, s2, s5, sA, sB⟩ := hs
  simp only [QED.ChainProof.SetCLinkDeg6.extPart_of_chord _ _ _ _ c0,
    QED.ChainProof.SetCLinkDeg6.extPart_of_chord _ _ _ _ c4,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ c1,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ c2,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ c5,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ cA,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ cB, s1, s2, s5, sA, sB]
  refine ⟨trivial, ?_, ?_, trivial, ?_, ?_, ?_⟩ <;>
    simp [Finset.sum_insert, cb0_ext, hmom] <;> abel

/-- **The class routing of `CB0`**: the frozen routing at `cbArg p' λ` puts `p' + λ₁` on the
outgoing open line, `p + λ₁` on the incoming one, `λ₀ - λ₁`, `λ₀` on the loop and `∓λ₁` on the
photons. -/
theorem cb0_lineMomentum (p' p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb0L0) = p' + ℓ 1 ∧
      lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb0L1) = p' + ℓ 1 ∧
      lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb0L2) = p + ℓ 1 ∧
      lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb0L4) = ℓ 0 - ℓ 1 ∧
      lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb0L5) = ℓ 0 ∧
      lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inr cb0GA) = ℓ 1 ∧
      lineMomentum₂ repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inr cb0GB) = -ℓ 1 := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨aA, bA⟩, ⟨aB, bB⟩⟩ := cb0_loopCoeff
  obtain ⟨e0, e1, e2, e4, e5, eA, eB⟩ := cb0_extPart (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (by simp)
  obtain ⟨g0, g1⟩ := cbArg_apply p' ℓ
  simp only [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_two, e0, e1, e2, e4, e5, eA, eB, g0, g1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [a0, b0, a1, b1, a2, b2, a4, b4, a5, b5, aA, bA, aB, bB] <;> ring

end CB0

section CB1

theorem kCB1_ne : ∀ t, kCB1 t ≠ .photonCt := by decide

/-- The flavoring with the open line of flavour `0` and the loop `4, 5` of flavour `f`. -/
def flavB1 (f : Fin 3) : Flavoring kCB1 :=
  ⟨fun t => if 4 ≤ t.1.val then f else 0, fun t ht => by
    have h : ∀ t : Wick.FermionVertex kCB1, kCB1 t.1 ≠ .gauge → t.1.val < 4 := by decide
    simp [Nat.not_le.mpr (h t ht)]⟩

/-- The line `0 — 1` (outgoing end `0`). -/
def cb1L0 : FermionLine repCB1 := ⟨fv kCB1 0, by decide +kernel⟩
/-- The line `1 — 2`. -/
def cb1L1 : FermionLine repCB1 := ⟨fv kCB1 1, by decide +kernel⟩
/-- The line `2 — 3`. -/
def cb1L2 : FermionLine repCB1 := ⟨fv kCB1 2, by decide +kernel⟩
/-- The loop line `4 — 5`. -/
def cb1L4 : FermionLine repCB1 := ⟨fv kCB1 4, by decide +kernel⟩
/-- The loop line `5 — 4`. -/
def cb1L5 : FermionLine repCB1 := ⟨fv kCB1 5, by decide +kernel⟩
/-- The photon line `0 — 4`. -/
def cb1GA : PhotonLine repCB1 := ⟨pg kCB1 0, by decide +kernel⟩
/-- The photon line `3 — 5`. -/
def cb1GB : PhotonLine repCB1 := ⟨pg kCB1 3, by decide +kernel⟩

theorem cb1_fermionLine_cases : ∀ f : FermionLine repCB1,
    f = cb1L0 ∨ f = cb1L1 ∨ f = cb1L2 ∨ f = cb1L4 ∨ f = cb1L5 := by
  decide +kernel

theorem cb1_photonLine_cases : ∀ g : PhotonLine repCB1, g = cb1GA ∨ g = cb1GB := by
  decide +kernel

theorem cb1_tails : cb1L0.tail = fv kCB1 1 ∧ cb1L1.tail = fv kCB1 2 ∧ cb1L2.tail = fv kCB1 3 ∧
    cb1L4.tail = fv kCB1 5 ∧ cb1L5.tail = fv kCB1 4 ∧ cb1GA.head = pg kCB1 4 ∧
    cb1GB.head = pg kCB1 5 := by
  decide +kernel

theorem cb1_cond (α β : Wick.FermionVertex kCB1 → Fin 4) (lor : Wick.PhotonSlot kCB1 → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repCB1.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repCB1.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repCB1.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kCB1 1) = μ 0 ∧ (α ⟨0, kCB1_ne 0⟩ = αOut 0 ∧ β ⟨3, kCB1_ne 3⟩ = βIn 0) := by
  have h1 : ∀ t, repCB1.1.1 (.inl 0) = .inr t ↔ t = fv kCB1 0 := by decide +kernel
  have h2 : ∀ t, repCB1.1.1 (.inr t) = .inl 0 ↔ t = fv kCB1 3 := by decide +kernel
  have h3 : ∀ a, repCB1.1.2 (.inl 0) = .inr a ↔ a = pg kCB1 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem cb1_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line repCB1 → Fin 4 → ℝ)
    (h : kCB1 2 ≠ .photonCt) : psiMomentum₂ repCB1 pIn k ⟨2, h⟩ = k (.inl cb1L2) :=
  psiMomentum₂_of_isRight (t := fv kCB1 2) (by decide +kernel)

theorem flavB1_apply (f : Fin 3) :
    (∀ h, (flavB1 f).1 ⟨0, h⟩ = 0) ∧ (∀ h, (flavB1 f).1 ⟨1, h⟩ = 0) ∧
      (∀ h, (flavB1 f).1 ⟨2, h⟩ = 0) ∧ (∀ h, (flavB1 f).1 ⟨4, h⟩ = f) ∧
      (∀ h, (flavB1 f).1 ⟨5, h⟩ = f) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The open chain of `CB1` at line momenta: `γ^ρ S̃(k₀) γ^μ S̃(k₁) X(k₂) S̃(k₂) γ^ν`. -/
noncomputable def cb1Chain (P : Params) (k0 k1 k2 : Fin 4 → ℝ) (μ ρ ν : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε k0 * Dirac.gamma μ *
    QED.OneLoop.electronPropagator P.m P.ε k1 * fermionCtMatrix P.δ₂ P.δm P.m k2 *
    QED.OneLoop.electronPropagator P.m P.ε k2 * Dirac.gamma ν

/-- **The amplitude of `repCB1`** for the loop flavour `f`, at arbitrary line momenta. -/
theorem cb1_amplitude (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line repCB1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repCB1 (flavB1 f) pIn kIn k αOut βIn μ =
      (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 * ∑ l0 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
        cb1Chain P (k (.inl cb1L0)) (k (.inl cb1L1)) (k (.inl cb1L2)) (μ 0) l0 l3 (αOut 0)
            (βIn 0) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb1GA)) l0 l4 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb1GB)) l3 l5 *
          Matrix.trace (Dirac.gamma l4 *
            QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb1L4)) * Dirac.gamma l5 *
            QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb1L5))) := by
  obtain ⟨t0, t1, t2, t4, t5, h4, h5⟩ := cb1_tails
  set G : (Wick.PhotonSlot kCB1 → Fin 4) → Fin 6 → Matrix (Fin 4) (Fin 4) ℂ := fun lor =>
    ![Dirac.gamma (lor (pg kCB1 0)), Dirac.gamma (lor (pg kCB1 1)),
      fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cb1L2)), Dirac.gamma (lor (pg kCB1 3)),
      Dirac.gamma (lor (pg kCB1 4)), Dirac.gamma (lor (pg kCB1 5))] with hG
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kCB1 → Fin 4, ∑ β : Wick.FermionVertex kCB1 → Fin 4,
      ∑ lor : Wick.PhotonSlot kCB1 → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kCB1 → Fin 4,
    (if lor (pg kCB1 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb1GA)) (lor (pg kCB1 0))
            (lor (pg kCB1 4)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cb1GB)) (lor (pg kCB1 3))
            (lor (pg kCB1 5))) *
        ((G lor 0 * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cb1L0)) * G lor 1 *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cb1L1)) * G lor 2 *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cb1L2)) * G lor 3) (αOut 0) (βIn 0) *
          Matrix.trace (G lor 4 * QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb1L4)) *
            G lor 5 * QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl cb1L5))))) = _)
  · rw [← spinSum6 kCB1_ne (G lor), ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold spinTerm6
    simp only [cb1_cond, Fin.prod_univ_six,
      prod_eq_of_five (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) cb1_fermionLine_cases,
      prod_eq_of_two (by decide) cb1_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB1 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB1 1 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show kCB1 2 = .fermionCt from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB1 3 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB1 4 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCB1 5 = .gauge from rfl),
      t0, t1, t2, t4, t5, h4, h5, ite_and_eq_mul, hG]
    simp only [show cb1L0.1 = fv kCB1 0 from rfl, show cb1L1.1 = fv kCB1 1 from rfl,
      show cb1L2.1 = fv kCB1 2 from rfl, show cb1L4.1 = fv kCB1 4 from rfl,
      show cb1L5.1 = fv kCB1 5 from rfl, show cb1GA.1 = pg kCB1 0 from rfl,
      show cb1GB.1 = pg kCB1 3 from rfl, pg, fv, flavB1_apply, cb1_psiMomentum,
      Matrix.cons_val]
    simp only [Params.mass, Matrix.cons_val_zero, fermionCtMatrix]
    ring
  · have n0 : pg kCB1 0 ≠ pg kCB1 1 := by decide
    have n3 : pg kCB1 3 ≠ pg kCB1 1 := by decide
    have n30 : pg kCB1 3 ≠ pg kCB1 0 := by decide
    have n4 : pg kCB1 4 ≠ pg kCB1 1 := by decide
    have n40 : pg kCB1 4 ≠ pg kCB1 0 := by decide
    have n43 : pg kCB1 4 ≠ pg kCB1 3 := by decide
    have n5 : pg kCB1 5 ≠ pg kCB1 1 := by decide
    have n50 : pg kCB1 5 ≠ pg kCB1 0 := by decide
    have n53 : pg kCB1 5 ≠ pg kCB1 3 := by decide
    have n54 : pg kCB1 5 ≠ pg kCB1 4 := by decide
    rw [sum_pi_five (x₁ := pg kCB1 1) (x₂ := pg kCB1 0) (x₃ := pg kCB1 3) (x₄ := pg kCB1 4)
      (x₅ := pg kCB1 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [hG, ite_true, n0, n3, n30, n4, n40, n43, n5, n50, n53, n54, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Matrix.cons_val]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    unfold cb1Chain
    ring

/-! #### The preserved flavorings -/

theorem repCB1_pow : repCB1.1.1 ^ 10 = 1 := by decide +kernel

theorem cb1_cycles : ∀ x : Fin 1 ⊕ Wick.FermionVertex kCB1,
    (Equiv.Perm.SameCycle repCB1.1.1 x (.inl 0) ∧ ∀ t, x = .inr t → t.1.val < 4) ∨
      (Equiv.Perm.SameCycle repCB1.1.1 x (.inr (fv kCB1 4)) ∧ ∀ t, x = .inr t → 4 ≤ t.1.val) := by
  simp only [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 10) repCB1_pow]
  decide +kernel

theorem cb1_not_sameCycle :
    ¬ Equiv.Perm.SameCycle repCB1.1.1 (.inl 0) (.inr (fv kCB1 4)) := by
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 10) repCB1_pow]
  decide +kernel

theorem preserves_flavB1 : ∀ f : Fin 3, Preserves repCB1 (flavB1 f) := by
  unfold Preserves
  decide +kernel

/-- **The preserved flavorings of `repCB1`**: the open line has flavour `0`, the loop one
flavour. -/
theorem preserves_iff_cb1 (φ : Flavoring kCB1) :
    Preserves repCB1 φ ↔ φ = flavB1 (φ.1 (fv kCB1 4)) := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_flavB1 _⟩
  rcases cb1_cycles (.inr t) with ⟨h, ht⟩ | ⟨h, ht⟩
  · have := fermionFlavor_eq_of_sameCycle hφ h
    simp only [fermionFlavor] at this
    simp [this, flavB1, Nat.not_le.mpr (ht t rfl)]
  · have := fermionFlavor_eq_of_sameCycle hφ h
    simp only [fermionFlavor] at this
    simp [this, flavB1, ht t rfl]

theorem sum_preserves_cb1 {M : Type*} [AddCommMonoid M] [DecidablePred (Preserves repCB1)]
    (F : Flavoring kCB1 → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring kCB1)).filter (Preserves repCB1), F φ =
      ∑ f : Fin 3, F (flavB1 f) :=
  Finset.sum_nbij' (fun φ => φ.1 (fv kCB1 4)) flavB1 (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_flavB1 f⟩)
    (fun φ hφ => ((preserves_iff_cb1 φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => rfl)
    (fun φ hφ => by rw [← (preserves_iff_cb1 φ).mp (Finset.mem_filter.mp hφ).2])

/-- The closed loop `4 → 5 → 4` of `repCB1`. -/
def loopCB1 : ClosedLoop repCB1 :=
  ⟨Quotient.mk _ (.inr (fv kCB1 4)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact cb1_not_sameCycle (Quotient.exact h)⟩

theorem eq_loopCB1 (q : ClosedLoop repCB1) : q = loopCB1 := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases cb1_cycles x with ⟨h, -⟩ | ⟨h, -⟩
  · exact absurd (Quotient.sound h.symm) (hq 0)
  · exact Quotient.sound h

open scoped Classical in
/-- The regulator weight of the flavour-`f` loop is `c_f`. -/
theorem loopWeight_flavB1 (P : Params) (f : Fin 3) :
    loopWeight P repCB1 (flavB1 f) = P.loopCoeff f := by
  rw [loopWeight, Fintype.prod_eq_single loopCB1 fun q hq => absurd (eq_loopCB1 q) hq]
  have hq : (Quotient.mk _ loopCB1.1.out : Quotient (Equiv.Perm.SameCycle.setoid repCB1.1.1)) =
      Quotient.mk _ (.inr (fv kCB1 4)) := Quotient.out_eq _
  rw [fermionFlavor_eq_of_sameCycle (preserves_flavB1 f) (Quotient.exact hq)]
  rfl

open scoped Classical in
/-- **The regulated amplitude of `repCB1`** is the sum over the loop flavour. -/
theorem regulatedAmplitude₂_cb1 (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line repCB1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P repCB1 pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P repCB1 (flavB1 f) pIn kIn k αOut βIn μ := by
  rw [regulatedAmplitude₂, sum_preserves_cb1]
  simp only [loopWeight_flavB1]

/-! #### The class routing -/

theorem cb1_ext (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 6) :
    QED.WickModel.externalMomentum repCB1 pOut pIn kIn v =
      (if v = 3 then pIn 0 else 0) + (if v = 1 then kIn 0 else 0) -
        (if v = 0 then pOut 0 else 0) := by
  rw [externalMomentum_one_one]
  have h : ∀ v,
      ((∃ t : Wick.FermionVertex kCB1, t.1 = v ∧ repCB1.1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
      ((∃ a : Wick.PhotonSlot kCB1, a.1 = v ∧ repCB1.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
      ((∃ t : Wick.FermionVertex kCB1, t.1 = v ∧ repCB1.1.1 (.inl 0) = .inr t) ↔ v = 0) := by
    decide +kernel
  obtain ⟨h1, h2, h3⟩ := h v
  simp only [h1, h2, h3]

theorem cb1_loopCoeff :
    (loopCoeff repCB1 (.inl cb1L0) 0 = 1 ∧ loopCoeff repCB1 (.inl cb1L0) 1 = 0) ∧
    (loopCoeff repCB1 (.inl cb1L1) 0 = 1 ∧ loopCoeff repCB1 (.inl cb1L1) 1 = 0) ∧
    (loopCoeff repCB1 (.inl cb1L2) 0 = 1 ∧ loopCoeff repCB1 (.inl cb1L2) 1 = 0) ∧
    (loopCoeff repCB1 (.inl cb1L4) 0 = 0 ∧ loopCoeff repCB1 (.inl cb1L4) 1 = 1) ∧
    (loopCoeff repCB1 (.inl cb1L5) 0 = 1 ∧ loopCoeff repCB1 (.inl cb1L5) 1 = 1) ∧
    (loopCoeff repCB1 (.inr cb1GA) 0 = 1 ∧ loopCoeff repCB1 (.inr cb1GA) 1 = 0) ∧
    (loopCoeff repCB1 (.inr cb1GB) 0 = -1 ∧ loopCoeff repCB1 (.inr cb1GB) 1 = 0) := by
  decide +kernel

theorem cb1_extPart (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0) :
    extPart repCB1 pOut pIn kIn (.inl cb1L0) = 0 ∧
    extPart repCB1 pOut pIn kIn (.inl cb1L1) = -kIn 0 ∧
    extPart repCB1 pOut pIn kIn (.inl cb1L2) = -kIn 0 ∧
    extPart repCB1 pOut pIn kIn (.inl cb1L4) = 0 ∧
    extPart repCB1 pOut pIn kIn (.inl cb1L5) = -pOut 0 ∧
    extPart repCB1 pOut pIn kIn (.inr cb1GA) = -pOut 0 ∧
    extPart repCB1 pOut pIn kIn (.inr cb1GB) = pOut 0 := by
  have hc : edgeChord (lineData repCB1) (edgeOf (.inl cb1L0)) = true ∧
      edgeChord (lineData repCB1) (edgeOf (.inl cb1L1)) = false ∧
      edgeChord (lineData repCB1) (edgeOf (.inl cb1L2)) = false ∧
      edgeChord (lineData repCB1) (edgeOf (.inl cb1L4)) = true ∧
      edgeChord (lineData repCB1) (edgeOf (.inl cb1L5)) = false ∧
      edgeChord (lineData repCB1) (edgeOf (.inr cb1GA)) = false ∧
      edgeChord (lineData repCB1) (edgeOf (.inr cb1GB)) = false := by
    decide +kernel
  have hs : edgeSide (lineData repCB1) (edgeOf (.inl cb1L1)) = {0, 2, 3, 4, 5} ∧
      edgeSide (lineData repCB1) (edgeOf (.inl cb1L2)) = {0, 3, 4, 5} ∧
      edgeSide (lineData repCB1) (edgeOf (.inl cb1L5)) = {0, 4} ∧
      edgeSide (lineData repCB1) (edgeOf (.inr cb1GA)) = {0} ∧
      edgeSide (lineData repCB1) (edgeOf (.inr cb1GB)) = {1, 2, 3} := by
    decide +kernel
  obtain ⟨c0, c1, c2, c4, c5, cA, cB⟩ := hc
  obtain ⟨s1, s2, s5, sA, sB⟩ := hs
  simp only [QED.ChainProof.SetCLinkDeg6.extPart_of_chord _ _ _ _ c0,
    QED.ChainProof.SetCLinkDeg6.extPart_of_chord _ _ _ _ c4,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ c1,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ c2,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ c5,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ cA,
    QED.ChainProof.SetCLinkDeg6.extPart_of_not_chord _ _ _ _ cB, s1, s2, s5, sA, sB]
  refine ⟨trivial, ?_, ?_, trivial, ?_, ?_, ?_⟩ <;>
    simp [Finset.sum_insert, cb1_ext, hmom, add_comm]

/-- **The class routing of `CB1`**: the frozen routing at `cbArg p' λ` puts `p' + λ₁` on the
outgoing open line, `p + λ₁` on the incoming one, `λ₀ - λ₁`, `λ₀` on the loop and `∓λ₁` on the
photons. -/
theorem cb1_lineMomentum (p' p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb1L0) = p' + ℓ 1 ∧
      lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb1L1) = p + ℓ 1 ∧
      lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb1L2) = p + ℓ 1 ∧
      lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb1L4) = ℓ 0 - ℓ 1 ∧
      lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inl cb1L5) = ℓ 0 ∧
      lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inr cb1GA) = ℓ 1 ∧
      lineMomentum₂ repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (cbArg p' ℓ)
        (.inr cb1GB) = -ℓ 1 := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨aA, bA⟩, ⟨aB, bB⟩⟩ := cb1_loopCoeff
  obtain ⟨e0, e1, e2, e4, e5, eA, eB⟩ := cb1_extPart (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (by simp)
  obtain ⟨g0, g1⟩ := cbArg_apply p' ℓ
  simp only [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_two, e0, e1, e2, e4, e5, eA, eB, g0, g1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [a0, b0, a1, b1, a2, b2, a4, b4, a5, b5, aA, bA, aB, bB] <;> ring

end CB1

/-! ### The amplitudes in the class loop momenta -/

/-- The open line `i` (`0`: incoming, `1`: outgoing) of `CB0` (`d = 1`) and `CB1` (`d = 0`) at
momentum `q`: the propagator, with the counterterm insertion `S X S` on the line `d`. -/
noncomputable def cbLine (P : Params) (d i : Fin 2) (q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  if i = d then
    QED.OneLoop.electronPropagator P.m P.ε q * fermionCtMatrix P.δ₂ P.δm P.m q *
      QED.OneLoop.electronPropagator P.m P.ε q
  else QED.OneLoop.electronPropagator P.m P.ε q

/-- **The amplitude of `CB0` (`d = 1`), `CB1` (`d = 0`)** of loop flavour `f`, in the class loop
momenta `λ`: open lines `p' + λ₁`, `p + λ₁`, photons `±λ₁`, loop `λ₀ - λ₁`, `λ₀`. -/
noncomputable def cbAmp (P : Params) (f : Fin 3) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 * ∑ l0 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
    (Dirac.gamma l0 * cbLine P d 1 (p' + ℓ 1) * Dirac.gamma μ * cbLine P d 0 (p + ℓ 1) *
        Dirac.gamma l3) α β *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ 1) l0 l4 *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-ℓ 1) l3 l5 *
      Matrix.trace (Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass f) P.ε (ℓ 0 - ℓ 1) *
        Dirac.gamma l5 * QED.OneLoop.electronPropagator (P.mass f) P.ε (ℓ 0))

/-- **The value of `CB0`** as the joint integral of the flavour sum of `cbAmp _ _ 1`. -/
theorem contractionValue₂_cb0 (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue₂ P repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        ∑ f : Fin 3, (P.loopCoeff f : ℂ) * cbAmp P f 1 p' p α β μ ℓ := by
  rw [contractionValue₂_eq_of_loopCount P loopCount_repCB0,
    ← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2 _ cbMat
      isUnit_det_cbMat ![p', 0]]
  congr 1
  funext ℓ
  have h := cb0_lineMomentum p' p ℓ
  simp only [cbArg] at h
  obtain ⟨h0, h1, h2, h4, h5, hA, hB⟩ := h
  rw [regulatedAmplitude₂_cb0]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [cb0_amplitude, h0, h1, h2, h4, h5, hA, hB]
  simp only [cbAmp, cbLine, cb0Chain, Fin.isValue, ↓reduceIte, Fin.reduceEq, Matrix.mul_assoc]

/-- **The value of `CB1`** as the joint integral of the flavour sum of `cbAmp _ _ 0`. -/
theorem contractionValue₂_cb1 (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue₂ P repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        ∑ f : Fin 3, (P.loopCoeff f : ℂ) * cbAmp P f 0 p' p α β μ ℓ := by
  rw [contractionValue₂_eq_of_loopCount P loopCount_repCB1,
    ← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2 _ cbMat
      isUnit_det_cbMat ![p', 0]]
  congr 1
  funext ℓ
  have h := cb1_lineMomentum p' p ℓ
  simp only [cbArg] at h
  obtain ⟨h0, h1, h2, h4, h5, hA, hB⟩ := h
  rw [regulatedAmplitude₂_cb1]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [cb1_amplitude, h0, h1, h2, h4, h5, hA, hB]
  simp only [cbAmp, cbLine, cb1Chain, Fin.isValue, ↓reduceIte, Fin.reduceEq, Matrix.mul_assoc]

end QED.ChainProof.SetCPauli.CB01

end
