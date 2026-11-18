/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermInsertionBasic
public import QED.TwoLoop.CountertermInsertionChain
public import QED.TwoLoop.CountertermInsertionAlgebra
public import QED.Integration.EnergyFirstShift

/-!
# The `δ₃` classes: explicit values

Part of obligation O2-13 (`docs/TWO-LOOP-DERIVATION.md`, section 5.1). The two counterterm
classes with one `photonCt` vertex (`repD3Slot0`, `repD3Slot1`: the internal photon with slot `0`,
resp. `1`, of the `photonCt` vertex towards `v₁`) are one-loop vertex graphs with two photon lines.
For each:

* the lines, ends, chord and a conserved routing (`decide +kernel`, `ring`); the two photon lines
  carry opposite momenta, and the `photonCt` factor is evaluated at the momentum entering through
  its slot `0` (T₆);
* `d3s*_amplitude`: the amplitude (T₇) at arbitrary line momenta is the one-loop vertex chain
  contracted with `(1/i) Δ̃_{νa} V^{ab} Δ̃_{ρb}` (in the order of the slots), by the index sums of
  `QED/TwoLoop/CountertermInsertionChain.lean` over the five photon fields;
* `contractionValue₂_repD3Slot0`, `contractionValue₂_repD3Slot1`: **the value (T₁₀) is the
  energy-first integral of the one-loop vertex chain with the photon factor `photonInsertion`**,
  at every `ε`, under momentum conservation, with no integrability hypothesis. The propagator and
  the `photonCt` factor are even in the momentum and symmetric in their indices, so both slot
  pairings give the same integrand.
-/

@[expose] public section

namespace QED.TwoLoop.Insertion

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel Complex

/-! ### `δ₃` with slot `0` towards `v₁`: fermion flow `0 → 1 → 2`, external photon at `1`,
photon lines `0 — 3₀`, `2 — 3₁` -/

section D3Slot0

/-- The fermion line `0 → 1` of `repD3Slot0`. -/
def d3s0f1 : FermionLine repD3Slot0 := ⟨fvK k_gggp 1, by decide +kernel⟩
/-- The fermion line `1 → 2` of `repD3Slot0`. -/
def d3s0f2 : FermionLine repD3Slot0 := ⟨fvK k_gggp 2, by decide +kernel⟩
/-- The photon line from vertex `0` to the `photonCt` vertex `3` of `repD3Slot0`. -/
def d3s0gA : PhotonLine repD3Slot0 := ⟨psK k_gggp 0 0, by decide +kernel⟩
/-- The photon line from vertex `2` to the `photonCt` vertex `3` of `repD3Slot0`. -/
def d3s0gB : PhotonLine repD3Slot0 := ⟨psK k_gggp 2 0, by decide +kernel⟩

theorem d3s0_fermionLine_cases : ∀ f : FermionLine repD3Slot0, f = d3s0f1 ∨ f = d3s0f2 := by
  decide +kernel

theorem d3s0_photonLine_cases : ∀ g : PhotonLine repD3Slot0, g = d3s0gA ∨ g = d3s0gB := by
  decide +kernel

theorem d3s0_line_cases : ∀ f : Line repD3Slot0,
    f = .inl d3s0f1 ∨ f = .inl d3s0f2 ∨ f = .inr d3s0gA ∨ f = .inr d3s0gB := by
  decide +kernel

theorem d3s0_isChord_iff : ∀ g : Line repD3Slot0, IsChord g ↔ g = .inl d3s0f1 := by
  decide +kernel

theorem d3s0_ends : (Line.ends (.inl d3s0f1 : Line repD3Slot0)) = (0, 1) ∧
    (Line.ends (.inl d3s0f2 : Line repD3Slot0)) = (1, 2) ∧
    (Line.ends (.inr d3s0gA : Line repD3Slot0)) = (0, 3) ∧
    (Line.ends (.inr d3s0gB : Line repD3Slot0)) = (2, 3) := by
  decide +kernel

theorem d3s0_tails : d3s0f1.tail = fvK k_gggp 0 ∧ d3s0f2.tail = fvK k_gggp 1 ∧
    d3s0gA.head = psK k_gggp 3 0 ∧ d3s0gB.head = psK k_gggp 3 1 := by
  decide +kernel

theorem d3s0_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggp, t.1 = v ∧ repD3Slot0.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggp, a.1 = v ∧ repD3Slot0.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex k_gggp, t.1 = v ∧ repD3Slot0.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- The routing of `repD3Slot0`: `ℓ` on `0 → 1`, `ℓ + k` on `1 → 2`, `p - ℓ` on the photon line
`0 → 3` and `ℓ - p` on the photon line `2 → 3`. -/
def d3s0Mom (p k ℓ : Fin 4 → ℝ) (f : Line repD3Slot0) : Fin 4 → ℝ :=
  if f = .inl d3s0f1 then ℓ else if f = .inl d3s0f2 then ℓ + k else if f = .inr d3s0gA then p - ℓ
    else ℓ - p

theorem d3s0Mom_apply (p k ℓ : Fin 4 → ℝ) : d3s0Mom p k ℓ (.inl d3s0f1) = ℓ ∧
    d3s0Mom p k ℓ (.inl d3s0f2) = ℓ + k ∧ d3s0Mom p k ℓ (.inr d3s0gA) = p - ℓ ∧
    d3s0Mom p k ℓ (.inr d3s0gB) = ℓ - p := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_⟩
  · rw [d3s0Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d3s0Mom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d3s0Mom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d3s0_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD3Slot0 pOut pIn kIn (d3s0Mom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4⟩ := d3s0_ends
  obtain ⟨m1, m2, m3, m4⟩ := d3s0Mom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) d3s0_line_cases, externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d3s0_ext v
  simp only [e1, e2, e3, e4, x1, x2, x3, m1, m2, m3, m4]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem d3s0_cond (α β : Wick.FermionVertex k_gggp → Fin 4) (lor : Wick.PhotonSlot k_gggp → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD3Slot0.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD3Slot0.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD3Slot0.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_gggp 1 0) = μ 0 ∧ (α (fvK k_gggp 2) = αOut 0 ∧ β (fvK k_gggp 0) = βIn 0) := by
  have h1 : ∀ t, repD3Slot0.1.1 (.inl 0) = .inr t ↔ t = fvK k_gggp 2 := by decide +kernel
  have h2 : ∀ t, repD3Slot0.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gggp 0 := by decide +kernel
  have h3 : ∀ a, repD3Slot0.1.2 (.inl 0) = .inr a ↔ a = psK k_gggp 1 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem d3s0_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD3Slot0 → Fin 4 → ℝ) :
    photonMomentum₂ repD3Slot0 kIn k ⟨3, ⟨0, by decide⟩⟩ = k (.inr d3s0gA) := by
  have hext : ¬ repD3Slot0.1.2 (.inl 0) = .inr ⟨3, ⟨0, by decide⟩⟩ := by decide +kernel
  have hA : d3s0gA.head = (⟨3, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := by decide +kernel
  have hB : d3s0gB.head = (⟨3, ⟨1, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := by decide +kernel
  have hA' : d3s0gA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := rfl
  have hB' : d3s0gB.1 = (⟨2, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_two (by decide) d3s0_photonLine_cases, hA, hB, hA',
    hB']
  simp

/-- **The amplitude of `repD3Slot0`** at arbitrary line momenta `k`: the one-loop vertex chain
`γ^ρ S̃(k₁₂) γ^μ S̃(k₀₁) γ^ν` contracted with the inserted photon factor
`(1/i) Δ̃_{νa}(k_A) V^{ab}(k_A) Δ̃_{ρb}(k_B)` (`V` the `photonCt` factor at the momentum `k_A`
entering its slot `0`), with the coupling `(ie)³` and `(1/i)³`. -/
theorem d3s0_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD3Slot0 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD3Slot0 (zeroFlavoring k_gggp) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s0gA)) ν a *
              photonCtFactor P.δ₃ (k (.inr d3s0gA)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s0gB)) ρ b) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s0f2)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s0f1)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4⟩ := d3s0_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_gggp → Fin 4, ∑ β : Wick.FermionVertex k_gggp → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggp → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_gggp → Fin 4,
    (if lor (psK k_gggp 1 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s0gA))
            (lor (psK k_gggp 0 0)) (lor (psK k_gggp 3 0)) *
          photonCtFactor P.δ₃ (k (.inr d3s0gA)) (lor (psK k_gggp 3 0)) (lor (psK k_gggp 3 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s0gB))
            (lor (psK k_gggp 2 0)) (lor (psK k_gggp 3 1)))) *
        (Dirac.gamma (lor (psK k_gggp 2 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s0f2)) *
          Dirac.gamma (lor (psK k_gggp 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s0f1)) *
          Dirac.gamma (lor (psK k_gggp 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fvK k_gggp 2) (x₂ := fvK k_gggp 1) (x₃ := fvK k_gggp 0)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d3s0_cond, Fin.prod_univ_four,
      prod_eq_of_two (by decide) d3s0_fermionLine_cases,
      prod_eq_of_two (by decide) d3s0_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 1 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 2 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 3 = .photonCt from rfl),
      d3s0_photonMomentum, t1, t2, t3, t4, ite_and_eq_mul]
    simp only [show d3s0f1.1 = fvK k_gggp 1 from rfl, show d3s0f2.1 = fvK k_gggp 2 from rfl,
      show d3s0gA.1 = psK k_gggp 0 0 from rfl, show d3s0gB.1 = psK k_gggp 2 0 from rfl, psK, fvK,
      zeroFlavoring, Params.mass, Matrix.cons_val_zero, photonCtFactor]
    ring
  · have n10 : psK k_gggp 1 0 ≠ psK k_gggp 0 0 := by decide
    have n20 : psK k_gggp 2 0 ≠ psK k_gggp 0 0 := by decide
    have n21 : psK k_gggp 2 0 ≠ psK k_gggp 1 0 := by decide
    have n30 : psK k_gggp 3 0 ≠ psK k_gggp 0 0 := by decide
    have n31 : psK k_gggp 3 0 ≠ psK k_gggp 1 0 := by decide
    have n32 : psK k_gggp 3 0 ≠ psK k_gggp 2 0 := by decide
    have m30 : psK k_gggp 3 1 ≠ psK k_gggp 0 0 := by decide
    have m31 : psK k_gggp 3 1 ≠ psK k_gggp 1 0 := by decide
    have m32 : psK k_gggp 3 1 ≠ psK k_gggp 2 0 := by decide
    have m33 : psK k_gggp 3 1 ≠ psK k_gggp 3 0 := by decide
    rw [sum_pi_five (x₁ := psK k_gggp 0 0) (x₂ := psK k_gggp 1 0) (x₃ := psK k_gggp 2 0)
      (x₄ := psK k_gggp 3 0) (x₅ := psK k_gggp 3 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, n30, n31, n32, m30, m31, m32, m33, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₃` with slot `0` towards `v₁`**: under momentum conservation, the energy-first
integral of the one-loop vertex chain whose photon factor is the `photonCt` insertion of one slot
pairing, `(1/i) Δ̃(ℓ) V(ℓ) Δ̃(ℓ)` (`photonInsertion`), at every `ε`. -/
theorem contractionValue₂_repD3Slot0 (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d3s0_isChord_iff (d3s0Mom (pIn 0) (kIn 0))
    (d3s0_isConserved hmom) (fun ℓ => (d3s0Mom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4⟩ := d3s0Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d3s0_amplitude, m1, m2, m3, m4, vertexChain, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', photonCtFactor_neg, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, photonInsertion]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end D3Slot0

/-! ### `δ₃` with slot `1` towards `v₁`: fermion flow `0 → 1 → 2`, external photon at `1`,
photon lines `0 — 3₁`, `2 — 3₀` -/

section D3Slot1

/-- The fermion line `0 → 1` of `repD3Slot1`. -/
def d3s1f1 : FermionLine repD3Slot1 := ⟨fvK k_gggp 1, by decide +kernel⟩
/-- The fermion line `1 → 2` of `repD3Slot1`. -/
def d3s1f2 : FermionLine repD3Slot1 := ⟨fvK k_gggp 2, by decide +kernel⟩
/-- The photon line from vertex `0` to the `photonCt` vertex `3` of `repD3Slot1`. -/
def d3s1gA : PhotonLine repD3Slot1 := ⟨psK k_gggp 0 0, by decide +kernel⟩
/-- The photon line from vertex `2` to the `photonCt` vertex `3` of `repD3Slot1`. -/
def d3s1gB : PhotonLine repD3Slot1 := ⟨psK k_gggp 2 0, by decide +kernel⟩

theorem d3s1_fermionLine_cases : ∀ f : FermionLine repD3Slot1, f = d3s1f1 ∨ f = d3s1f2 := by
  decide +kernel

theorem d3s1_photonLine_cases : ∀ g : PhotonLine repD3Slot1, g = d3s1gA ∨ g = d3s1gB := by
  decide +kernel

theorem d3s1_line_cases : ∀ f : Line repD3Slot1,
    f = .inl d3s1f1 ∨ f = .inl d3s1f2 ∨ f = .inr d3s1gA ∨ f = .inr d3s1gB := by
  decide +kernel

theorem d3s1_isChord_iff : ∀ g : Line repD3Slot1, IsChord g ↔ g = .inl d3s1f1 := by
  decide +kernel

theorem d3s1_ends : (Line.ends (.inl d3s1f1 : Line repD3Slot1)) = (0, 1) ∧
    (Line.ends (.inl d3s1f2 : Line repD3Slot1)) = (1, 2) ∧
    (Line.ends (.inr d3s1gA : Line repD3Slot1)) = (0, 3) ∧
    (Line.ends (.inr d3s1gB : Line repD3Slot1)) = (2, 3) := by
  decide +kernel

theorem d3s1_tails : d3s1f1.tail = fvK k_gggp 0 ∧ d3s1f2.tail = fvK k_gggp 1 ∧
    d3s1gA.head = psK k_gggp 3 1 ∧ d3s1gB.head = psK k_gggp 3 0 := by
  decide +kernel

theorem d3s1_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggp, t.1 = v ∧ repD3Slot1.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggp, a.1 = v ∧ repD3Slot1.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex k_gggp, t.1 = v ∧ repD3Slot1.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- The routing of `repD3Slot1`: `ℓ` on `0 → 1`, `ℓ + k` on `1 → 2`, `p - ℓ` on the photon line
`0 → 3` and `ℓ - p` on the photon line `2 → 3`. -/
def d3s1Mom (p k ℓ : Fin 4 → ℝ) (f : Line repD3Slot1) : Fin 4 → ℝ :=
  if f = .inl d3s1f1 then ℓ else if f = .inl d3s1f2 then ℓ + k else if f = .inr d3s1gA then p - ℓ
    else ℓ - p

theorem d3s1Mom_apply (p k ℓ : Fin 4 → ℝ) : d3s1Mom p k ℓ (.inl d3s1f1) = ℓ ∧
    d3s1Mom p k ℓ (.inl d3s1f2) = ℓ + k ∧ d3s1Mom p k ℓ (.inr d3s1gA) = p - ℓ ∧
    d3s1Mom p k ℓ (.inr d3s1gB) = ℓ - p := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_⟩
  · rw [d3s1Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d3s1Mom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d3s1Mom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d3s1_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD3Slot1 pOut pIn kIn (d3s1Mom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4⟩ := d3s1_ends
  obtain ⟨m1, m2, m3, m4⟩ := d3s1Mom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) d3s1_line_cases, externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d3s1_ext v
  simp only [e1, e2, e3, e4, x1, x2, x3, m1, m2, m3, m4]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem d3s1_cond (α β : Wick.FermionVertex k_gggp → Fin 4) (lor : Wick.PhotonSlot k_gggp → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD3Slot1.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD3Slot1.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD3Slot1.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_gggp 1 0) = μ 0 ∧ (α (fvK k_gggp 2) = αOut 0 ∧ β (fvK k_gggp 0) = βIn 0) := by
  have h1 : ∀ t, repD3Slot1.1.1 (.inl 0) = .inr t ↔ t = fvK k_gggp 2 := by decide +kernel
  have h2 : ∀ t, repD3Slot1.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gggp 0 := by decide +kernel
  have h3 : ∀ a, repD3Slot1.1.2 (.inl 0) = .inr a ↔ a = psK k_gggp 1 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem d3s1_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD3Slot1 → Fin 4 → ℝ) :
    photonMomentum₂ repD3Slot1 kIn k ⟨3, ⟨0, by decide⟩⟩ = k (.inr d3s1gB) := by
  have hext : ¬ repD3Slot1.1.2 (.inl 0) = .inr ⟨3, ⟨0, by decide⟩⟩ := by decide +kernel
  have hA : d3s1gA.head = (⟨3, ⟨1, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := by decide +kernel
  have hB : d3s1gB.head = (⟨3, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := by decide +kernel
  have hA' : d3s1gA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := rfl
  have hB' : d3s1gB.1 = (⟨2, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_gggp) := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_two (by decide) d3s1_photonLine_cases, hA, hB, hA',
    hB']
  simp

/-- **The amplitude of `repD3Slot1`** at arbitrary line momenta `k`: the one-loop vertex chain
`γ^ρ S̃(k₁₂) γ^μ S̃(k₀₁) γ^ν` contracted with the inserted photon factor
`(1/i) Δ̃_{νa}(k_A) V^{ab}(k_A) Δ̃_{ρb}(k_B)` (`V` the `photonCt` factor at the momentum `k_A`
entering its slot `0`), with the coupling `(ie)³` and `(1/i)³`. -/
theorem d3s1_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD3Slot1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD3Slot1 (zeroFlavoring k_gggp) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s1gA)) ν b *
              photonCtFactor P.δ₃ (k (.inr d3s1gB)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s1gB)) ρ a) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s1f2)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s1f1)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4⟩ := d3s1_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_gggp → Fin 4, ∑ β : Wick.FermionVertex k_gggp → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggp → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_gggp → Fin 4,
    (if lor (psK k_gggp 1 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s1gA))
            (lor (psK k_gggp 0 0)) (lor (psK k_gggp 3 1)) *
          photonCtFactor P.δ₃ (k (.inr d3s1gB)) (lor (psK k_gggp 3 0)) (lor (psK k_gggp 3 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d3s1gB))
            (lor (psK k_gggp 2 0)) (lor (psK k_gggp 3 0)))) *
        (Dirac.gamma (lor (psK k_gggp 2 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s1f2)) *
          Dirac.gamma (lor (psK k_gggp 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d3s1f1)) *
          Dirac.gamma (lor (psK k_gggp 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fvK k_gggp 2) (x₂ := fvK k_gggp 1) (x₃ := fvK k_gggp 0)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d3s1_cond, Fin.prod_univ_four,
      prod_eq_of_two (by decide) d3s1_fermionLine_cases,
      prod_eq_of_two (by decide) d3s1_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 1 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 2 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show k_gggp 3 = .photonCt from rfl),
      d3s1_photonMomentum, t1, t2, t3, t4, ite_and_eq_mul]
    simp only [show d3s1f1.1 = fvK k_gggp 1 from rfl, show d3s1f2.1 = fvK k_gggp 2 from rfl,
      show d3s1gA.1 = psK k_gggp 0 0 from rfl, show d3s1gB.1 = psK k_gggp 2 0 from rfl, psK, fvK,
      zeroFlavoring, Params.mass, Matrix.cons_val_zero, photonCtFactor]
    ring
  · have n10 : psK k_gggp 1 0 ≠ psK k_gggp 0 0 := by decide
    have n20 : psK k_gggp 2 0 ≠ psK k_gggp 0 0 := by decide
    have n21 : psK k_gggp 2 0 ≠ psK k_gggp 1 0 := by decide
    have n30 : psK k_gggp 3 0 ≠ psK k_gggp 0 0 := by decide
    have n31 : psK k_gggp 3 0 ≠ psK k_gggp 1 0 := by decide
    have n32 : psK k_gggp 3 0 ≠ psK k_gggp 2 0 := by decide
    have m30 : psK k_gggp 3 1 ≠ psK k_gggp 0 0 := by decide
    have m31 : psK k_gggp 3 1 ≠ psK k_gggp 1 0 := by decide
    have m32 : psK k_gggp 3 1 ≠ psK k_gggp 2 0 := by decide
    have m33 : psK k_gggp 3 1 ≠ psK k_gggp 3 0 := by decide
    rw [sum_pi_five (x₁ := psK k_gggp 0 0) (x₂ := psK k_gggp 1 0) (x₃ := psK k_gggp 2 0)
      (x₄ := psK k_gggp 3 0) (x₅ := psK k_gggp 3 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, n30, n31, n32, m30, m31, m32, m33, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₃` with slot `1` towards `v₁`**: under momentum conservation, the energy-first
integral of the one-loop vertex chain whose photon factor is the `photonCt` insertion of one slot
pairing, `(1/i) Δ̃(ℓ) V(ℓ) Δ̃(ℓ)` (`photonInsertion`), at every `ε`. -/
theorem contractionValue₂_repD3Slot1 (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d3s1_isChord_iff (d3s1Mom (pIn 0) (kIn 0))
    (d3s1_isConserved hmom) (fun ℓ => (d3s1Mom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4⟩ := d3s1Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d3s1_amplitude, m1, m2, m3, m4, vertexChain, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, photonInsertion]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm (f := fun x i => 1 / I *
    (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0) _ i * photonCtFactor P.δ₃ (ℓ - pIn 0) x i *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0) _ x))]
  simp only [photonCtFactor_comm P.δ₃ (ℓ - pIn 0) _ _]
  ring

end D3Slot1

end QED.TwoLoop.Insertion

end
