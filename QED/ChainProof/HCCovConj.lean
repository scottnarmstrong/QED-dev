/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCCovInv
public import QED.ChainProof.HCCovMirror
public import QED.ChainProof.EnumVertex
public import QED.TwoLoop.LimitMirrorLimit
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Charge conjugation of the chain vertex at fixed `ε`, and the mirror link

Helper level, Phase 5 Stage 1a, obligation O3-8 (no `q^μ` term). Charge conjugation reverses
every fermion line. For a contraction `C` with fermion pairing `σ`, the **charge-conjugate
contraction** `ccC C` has pairing `σ⁻¹` and the same photon pairing and vertex kinds
(`ccC`). It is an involution.

* `contractionValue₂_ccC`: for every contraction with attached external fermion fields and no
  `δ₂, δ_m` vertex, with connected vertices, the same loop number as its conjugate, and momentum
  conservation, at every parameter set (so every `ε`), the value (F₇) of `ccC C` with the
  charge-conjugate external data `(-p_in, -p_out, k)` and spinor indices `(p(β), p(α))` is
  `(-1)^{n_A} ∏ᵢ c(αᵢ) c(βᵢ)` times the value of `C` at `(p_out, p_in, k)` and `(α, β)`, with the
  charge-conjugation involution `p` and signs `c` (`QED.Dirac.ccIdx`, `QED.Dirac.ccSign`). As at
  two loops (`QED.TwoLoop.LimitMirror.contractionValue₂_Cm_cc`), the loop momenta change by an
  integer unimodular affine map (`QED.TwoLoop.LimitMirror.exists_routing_change_of_ext`), which
  leaves the joint energy-first integral unchanged for every integrand.
* `isVPChain_ccC`: the chains (C₁) are closed under `ccC`, with `a ↔ c` and the chain reversed.
  For set (b) this swaps the bubble–`δ₃` and `δ₃`–bubble contractions.
* `vertexChain_two_cc`: **charge conjugation of the set (b) chain vertex** at every `ε` and all
  momenta, `C V(p', p)ᵀ C = -V(-p, -p')`, by reindexing the family sum along `ccC`.
* `chainMirrorAt`: with the inversion of all momenta (`QED/ChainProof/HCCovInv.lean`), the
  fixed-`ε` mirror identity `QED.ChainProof.ChainMirrorAt` holds, unconditionally.
* **`chainMirrorLink_of_exists_cov`**: `ChainMirrorLink` follows from `ChainExistsLink` and
  `ChainCovLink`.
* `isFormFactorPair_vertexChain_two_pauli_limit_of_four`: the exact proposition of (HC₃) from the
  class decomposition, the per-class limits and covariance, and the Pauli link; the mirror
  obligation is discharged.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real
open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ photonMomentum₂
  lineMomentum₂ externalMomentum IsOnePI VerticesConnected loopCount fermionSign
  IsElectronOnShell IsPhotonOnShell)

namespace QED.ChainProof.Conj

open QED.ChainProof.Inv QED.Dirac
open QED.TwoLoop.Relabel (LineCorr)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The charge-conjugate contraction -/

/-- **The charge-conjugate contraction**: the fermion pairing `σ` replaced by `σ⁻¹` (every
fermion line reversed, the external `Ψ(xᵢ)` and `Ψ̄(yᵢ)` exchanged), the photon pairing kept. -/
def ccC (C : Contraction nf nA κ) : Contraction nf nA κ := ⟨(C.1.1⁻¹, C.1.2), C.2⟩

@[simp] theorem ccC_fst (C : Contraction nf nA κ) : (ccC C).1.1 = C.1.1⁻¹ := rfl

@[simp] theorem ccC_snd (C : Contraction nf nA κ) : (ccC C).1.2 = C.1.2 := rfl

@[simp] theorem ccC_ccC (C : Contraction nf nA κ) : ccC (ccC C) = C := by
  apply Subtype.ext
  simp [ccC]

theorem ccC_apply_eq_iff (C : Contraction nf nA κ) (x y : Fin nf ⊕ Wick.FermionVertex κ) :
    (ccC C).1.1 x = y ↔ C.1.1 y = x := by
  rw [ccC_fst, Equiv.Perm.inv_eq_iff_eq, eq_comm]

/-! ### The fermion lines -/

theorem fermionLine_spec {C : Contraction nf nA κ} (f : FermionLine C) :
    C.1.1 (.inr f.1) = .inr f.tail := by
  simp only [QED.WickModel.FermionLine.tail]
  exact (Sum.inr_getRight _ _).symm

theorem tail_eq_of {C : Contraction nf nA κ} (f : FermionLine C) {u : Wick.FermionVertex κ}
    (h : C.1.1 (.inr f.1) = .inr u) : f.tail = u := by
  have := (fermionLine_spec f).symm.trans h
  exact Sum.inr_injective this

/-- The line of `ccC C` reversing the line `f` of `C`: indexed by the tail of `f`. -/
def lineCC {C : Contraction nf nA κ} (f : FermionLine C) : FermionLine (ccC C) :=
  ⟨f.tail, by rw [(ccC_apply_eq_iff C _ (.inr f.1)).mpr (fermionLine_spec f)]; rfl⟩

theorem lineCC_val {C : Contraction nf nA κ} (f : FermionLine C) : (lineCC f).1 = f.tail := rfl

theorem lineCC_tail {C : Contraction nf nA κ} (f : FermionLine C) : (lineCC f).tail = f.1 :=
  tail_eq_of (lineCC f) ((ccC_apply_eq_iff C _ _).mpr (fermionLine_spec f))

/-- The reversal of the fermion lines. -/
def fermEquiv (C : Contraction nf nA κ) : FermionLine C ≃ FermionLine (ccC C) where
  toFun := lineCC
  invFun f' := ⟨f'.tail, by
    rw [(ccC_apply_eq_iff C _ _).mp (fermionLine_spec f')]; rfl⟩
  left_inv f := Subtype.ext (lineCC_tail f)
  right_inv f' := Subtype.ext (tail_eq_of _ ((ccC_apply_eq_iff C _ _).mp (fermionLine_spec f')))

theorem fermEquiv_apply (C : Contraction nf nA κ) (f : FermionLine C) :
    fermEquiv C f = lineCC f := rfl

theorem perm_inv_apply {X : Type*} (σ : Equiv.Perm X) (x : X) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

theorem perm_apply_inv {X : Type*} (σ : Equiv.Perm X) (x : X) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

/-- **The line correspondence of `C` and `ccC C`**: the vertices fixed, every fermion line
reversed, every photon line kept. -/
def corrCC (C : Contraction nf nA κ) : LineCorr C (ccC C) where
  vtx := Equiv.refl _
  line := Equiv.sumCongr (fermEquiv C) (Equiv.refl _)
  rev f := f.isLeft
  ends_line f := by
    rcases f with f | g
    · simp only [Sum.isLeft_inl, ite_true, Equiv.refl_apply, QED.WickModel.Line.ends]
      exact Prod.ext (congrArg Subtype.val (lineCC_tail f)) rfl
    · rfl

theorem pull_inl (C : Contraction nf nA κ) (k' : Line (ccC C) → Fin 4 → ℝ) (f : FermionLine C) :
    (corrCC C).pull k' (.inl f) = -k' (.inl (lineCC f)) := by
  simp only [LineCorr.pull, corrCC, Sum.isLeft_inl, ite_true]
  rfl

theorem pull_inr (C : Contraction nf nA κ) (k' : Line (ccC C) → Fin 4 → ℝ) (g : PhotonLine C) :
    (corrCC C).pull k' (.inr g) = k' (.inr g) := by
  simp only [LineCorr.pull, corrCC, Sum.isLeft_inr]
  rfl

theorem photonMomentum₂_ccC (C : Contraction nf nA κ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (ccC C) → Fin 4 → ℝ) :
    photonMomentum₂ (ccC C) kIn k' = photonMomentum₂ C kIn ((corrCC C).pull k') := rfl

open scoped Classical in
theorem externalMomentum_ccC (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (v : Fin N) :
    externalMomentum (ccC C) (-pIn) (-pOut) kIn v = externalMomentum C pOut pIn kIn v := by
  have hA : (∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ (ccC C).1.1 (.inr t) = .inl i then
      (-pOut) i else 0) =
      -∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl i) = .inr t then pOut i else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ccC_apply_eq_iff]
    split_ifs <;> simp
  have hB : (∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ (ccC C).1.1 (.inl i) = .inr t then
      (-pIn) i else 0) =
      -∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl i then pIn i else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ccC_apply_eq_iff]
    split_ifs <;> simp
  unfold externalMomentum
  rw [hA, hB]
  have hK : ∀ a b c : Fin 4 → ℝ, -a + b - -c = c + b - a := fun a b c => by abel
  exact hK _ _ _

/-! ### Flavours along the fermion pairing -/

section Flavour

variable {F : Type} (Φ : QED.Lepton.Flavors F)

theorem preserves_ccC_iff (C : Contraction nf nA κ) (φ : QED.Lepton.Flavoring Φ κ) :
    QED.Lepton.Preserves Φ (ccC C) φ ↔ QED.Lepton.Preserves Φ C φ := by
  constructor
  · intro h a
    have := h (C.1.1 a)
    rw [ccC_fst, perm_inv_apply] at this
    exact this.symm
  · intro h a
    have := h (C.1.1⁻¹ a)
    rw [perm_apply_inv] at this
    exact this.symm

theorem fermionFlavor_zpow {C : Contraction nf nA κ} {φ : QED.Lepton.Flavoring Φ κ}
    (hφ : QED.Lepton.Preserves Φ C φ) (x : Fin nf ⊕ Wick.FermionVertex κ) (i : ℤ) :
    QED.Lepton.fermionFlavor Φ φ ((C.1.1 ^ i) x) = QED.Lepton.fermionFlavor Φ φ x := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [add_comm (i : ℤ) 1, _root_.zpow_one_add, Equiv.Perm.mul_apply, hφ, ih]
  | pred i ih =>
    rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, _root_.zpow_add, _root_.zpow_neg_one, Equiv.Perm.mul_apply,
      ← ih]
    have := hφ (C.1.1⁻¹ ((C.1.1 ^ (-(i : ℤ))) x))
    rw [perm_apply_inv] at this
    exact this.symm

theorem fermionFlavor_of_sameCycle {C : Contraction nf nA κ} {φ : QED.Lepton.Flavoring Φ κ}
    (hφ : QED.Lepton.Preserves Φ C φ) {x y : Fin nf ⊕ Wick.FermionVertex κ}
    (h : Equiv.Perm.SameCycle C.1.1 x y) :
    QED.Lepton.fermionFlavor Φ φ x = QED.Lepton.fermionFlavor Φ φ y := by
  obtain ⟨i, rfl⟩ := h
  exact (fermionFlavor_zpow Φ hφ x i).symm

/-- The closed loops of `C` and `ccC C` are the same cycles. -/
def closedLoopEquiv (C : Contraction nf nA κ) :
    QED.WickModel.ClosedLoop (ccC C) ≃ QED.WickModel.ClosedLoop C :=
  Equiv.subtypeEquiv (Quotient.congrRight fun a b => by
      change Equiv.Perm.SameCycle C.1.1⁻¹ a b ↔ Equiv.Perm.SameCycle C.1.1 a b
      exact Equiv.Perm.sameCycle_inv)
    fun q => by
      induction q using Quotient.inductionOn with
      | h x =>
        refine forall_congr' fun i => not_congr ?_
        change _ ↔ (Quotient.mk _ (Sum.inl i) : Quotient (Equiv.Perm.SameCycle.setoid C.1.1)) =
          Quotient.mk _ x
        rw [Quotient.eq, Quotient.eq]
        exact Equiv.Perm.sameCycle_inv

open scoped Classical in
theorem loopWeight_ccC (C : Contraction nf nA κ) {φ : QED.Lepton.Flavoring Φ κ}
    (hφ : QED.Lepton.Preserves Φ C φ) :
    QED.Lepton.loopWeight Φ (ccC C) φ = QED.Lepton.loopWeight Φ C φ := by
  unfold QED.Lepton.loopWeight
  refine Fintype.prod_equiv (closedLoopEquiv C) _ _ fun q => ?_
  congr 1
  refine fermionFlavor_of_sameCycle Φ hφ ?_
  have h1 : (closedLoopEquiv C q).1 = Quotient.mk _ q.1.out := by
    show Quotient.congrRight _ q.1 = _
    conv_lhs => rw [← Quotient.out_eq q.1]
    rfl
  have h2 : Quotient.mk (Equiv.Perm.SameCycle.setoid C.1.1) (closedLoopEquiv C q).1.out =
      Quotient.mk _ q.1.out := by
    rw [Quotient.out_eq, h1]
  exact (Quotient.exact h2).symm

end Flavour

/-! ### The amplitude -/

/-- Reindexing the double sum over spinor index families along `(α, β) ↦ (p ∘ β, p ∘ α)`. -/
theorem sum_ccIdx {X : Type*} [Fintype X] [DecidableEq X] (G : (X → Fin 4) → (X → Fin 4) → ℂ) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4, G α β =
      ∑ α : X → Fin 4, ∑ β : X → Fin 4, G (fun t => ccIdx (β t)) (fun t => ccIdx (α t)) := by
  let e : (X → Fin 4) × (X → Fin 4) ≃ (X → Fin 4) × (X → Fin 4) :=
    { toFun := fun x => (fun t => ccIdx (x.2 t), fun t => ccIdx (x.1 t))
      invFun := fun x => (fun t => ccIdx (x.2 t), fun t => ccIdx (x.1 t))
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  rw [← Fintype.sum_prod_type' (f := G), ← Fintype.sum_prod_type'
    (f := fun (α β : X → Fin 4) => G (fun t => ccIdx (β t)) (fun t => ccIdx (α t)))]
  exact (Equiv.sum_comp e (fun x => G x.1 x.2)).symm

section VertexFactor

variable (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
  (lor : Wick.PhotonSlot κ → Fin 4)
  (kψ kψ' : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ)

theorem vertexFactor_cc (t : Fin N) (hnf : κ t ≠ .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m (fun x => ccIdx (β x)) (fun x => ccIdx (α x)) lor kψ' kA t =
      vsgn α β ccSign t * Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t := by
  unfold vsgn
  have hcases : κ t = .gauge ∨ κ t = .gaugeCt ∨ κ t = .photonCt := by
    revert hnf
    cases κ t <;> simp
  rcases hcases with hk | hk | hk
  · have hne : κ t ≠ .photonCt := by rw [hk]; decide
    have hs : (κ t).photonSlots = 1 := by rw [hk]; rfl
    rw [dite_eq_left hne, hs, pow_one, vf_gauge _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_gauge _ _ _ _ _ _ _ _ _ _ _ hk, gamma_ccIdx]
    ring
  · have hne : κ t ≠ .photonCt := by rw [hk]; decide
    have hs : (κ t).photonSlots = 1 := by rw [hk]; rfl
    rw [dite_eq_left hne, hs, pow_one, vf_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vf_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk, gamma_ccIdx]
    ring
  · have hs : (κ t).photonSlots = 2 := by rw [hk]; rfl
    rw [dite_eq_right (by rw [hk]; exact fun h => h rfl), hs,
      vf_photonCt _ _ _ _ _ _ _ _ _ _ _ hk, vf_photonCt _ _ _ _ _ _ _ _ _ _ _ hk]
    ring

end VertexFactor

section Value

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : QED.Lepton.Flavors F)

omit [Fintype F] [DecidableEq F] in
open scoped Classical in
/-- **Charge conjugation of the amplitude** (F₅): the amplitude of `ccC C` at line momenta `k'`
and external indices `(p(β), p(α))` is `(-1)^{n_A} ∏ c(α) c(β)` times the amplitude of `C` at the
pulled-back momenta and indices `(α, β)`. -/
theorem contractionAmplitude₂_ccC (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (hnf : ∀ t, κ t ≠ .fermionCt)
    (φ : QED.Lepton.Flavoring Φ κ) (hφ : QED.Lepton.Preserves Φ C φ)
    (pIn pIn' : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (ccC C) → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.contractionAmplitude₂ P Φ (ccC C) φ pIn' kIn k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        QED.Lepton.contractionAmplitude₂ P Φ C φ pIn kIn ((corrCC C).pull k') αOut βIn μ := by
  unfold QED.Lepton.contractionAmplitude₂
  refine (sum_ccIdx _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun lor _ => ?_
  have hiff : ((∀ i t, (ccC C).1.1 (.inl i) = .inr t → ccIdx (β t) = ccIdx (βIn i)) ∧
      (∀ t i, (ccC C).1.1 (.inr t) = .inl i → ccIdx (α t) = ccIdx (αOut i)) ∧
      (∀ j a, (ccC C).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      ((∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j)) := by
    simp only [ccC_apply_eq_iff, ccC_snd, (Function.LeftInverse.injective ccIdx_ccIdx).eq_iff]
    exact ⟨fun h => ⟨fun i t hit => h.2.1 t i hit, fun t i hti => h.1 i t hti, h.2.2⟩,
      fun h => ⟨fun i t hit => h.2.1 t i hit, fun t i hti => h.1 i t hti, h.2.2⟩⟩
  by_cases hc : (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j)
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc, one_mul, one_mul]
    have hp := prod_sign_pairing C hatt ccSign ccSign_mul_self α β αOut βIn hc.1 hc.2.1
    have hV : ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m (fun x => ccIdx (β x))
        (fun x => ccIdx (α x)) lor (psiMomentum₂ (ccC C) pIn' k') (photonMomentum₂ (ccC C) kIn k') t =
        (∏ t, vsgn α β ccSign t) * ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum₂ C pIn ((corrCC C).pull k')) (photonMomentum₂ C kIn ((corrCC C).pull k')) t := by
      rw [← Finset.prod_mul_distrib, photonMomentum₂_ccC]
      exact Finset.prod_congr rfl fun t _ => vertexFactor_cc _ _ _ _ _ _ _ _ _ _ _ _ t (hnf t)
    have hF : ∏ f : FermionLine (ccC C), (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ.1 f.1)) P.ε (k' (.inl f)) (ccIdx (α f.1))
          (ccIdx (β f.tail)) =
        (∏ f : FermionLine C, ccSign (β f.1) * ccSign (α f.tail)) * ∏ f : FermionLine C, (1 / I) *
          QED.OneLoop.electronPropagator (Φ.mass (φ.1 f.1)) P.ε ((corrCC C).pull k' (.inl f))
            (β f.1) (α f.tail) := by
      rw [← Equiv.prod_comp (fermEquiv C), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun f _ => ?_
      have hfl : φ.1 f.tail = φ.1 f.1 := by
        have := hφ (.inr f.1)
        rwa [fermionLine_spec f] at this
      change (1 / I) * QED.OneLoop.electronPropagator (Φ.mass (φ.1 (lineCC f).1)) P.ε
          (k' (.inl (lineCC f))) (ccIdx (α (lineCC f).1)) (ccIdx (β (lineCC f).tail)) = _
      rw [lineCC_val, lineCC_tail, hfl, QED.OneLoop.electronPropagator_ccIdx, pull_inl]
      ring
    have hG : ∏ g : PhotonLine (ccC C), (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k' (.inr g)) (lor g.1) (lor g.head) =
        ∏ g : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ((corrCC C).pull k' (.inr g)) (lor g.1)
          (lor g.head) := rfl
    rw [hV, hF, hG, prod_vsgn, neg_one_pow_card_photonSlot C, ← hp]
    ring
  · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc]
    simp

open scoped Classical in
theorem regulatedAmplitude₂_ccC (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (hnf : ∀ t, κ t ≠ .fermionCt)
    (pIn pIn' : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (ccC C) → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.regulatedAmplitude₂ P Φ (ccC C) pIn' kIn k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        QED.Lepton.regulatedAmplitude₂ P Φ C pIn kIn ((corrCC C).pull k') αOut βIn μ := by
  unfold QED.Lepton.regulatedAmplitude₂
  rw [Finset.mul_sum]
  have hfil : (Finset.univ : Finset (QED.Lepton.Flavoring Φ κ)).filter
      (QED.Lepton.Preserves Φ (ccC C)) =
      (Finset.univ : Finset (QED.Lepton.Flavoring Φ κ)).filter (QED.Lepton.Preserves Φ C) :=
    Finset.filter_congr fun φ _ => preserves_ccC_iff Φ C φ
  rw [hfil]
  refine Finset.sum_congr rfl fun φ hφ => ?_
  have hφ' := (Finset.mem_filter.mp hφ).2
  rw [loopWeight_ccC Φ C hφ', contractionAmplitude₂_ccC P Φ C hatt hnf φ hφ' pIn]
  ring

theorem contractionValue₂_eq_of_loopCount {C : Contraction nf nA κ} {L : ℕ}
    (hL : loopCount C = L) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral L fun ℓ => (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
        QED.Lepton.regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  subst hL
  rfl

/-- **Charge conjugation of the value** (F₇), at every parameter set (so every `ε`). -/
theorem contractionValue₂_ccC (C : Contraction nf nA κ)
    (hatt : ∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) (hnf : ∀ t, κ t ≠ .fermionCt)
    (hV : VerticesConnected C) (hV' : VerticesConnected (ccC C))
    (hL : loopCount (ccC C) = loopCount C)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    QED.Lepton.contractionValue₂ P Φ (ccC C) (-pIn) (-pOut) kIn (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        QED.Lepton.contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := by
  obtain ⟨M, hMdet, a, h⟩ := QED.TwoLoop.LimitMirror.exists_routing_change_of_ext (corrCC C) hV hV'
    (fun v => externalMomentum_ccC C pOut pIn kIn v) hsum rfl hL
  rw [contractionValue₂_eq_of_loopCount P Φ hL, contractionValue₂_eq_of_loopCount P Φ rfl]
  have e : (fun ℓ : Fin (loopCount C) → Fin 4 → ℝ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.Lepton.regulatedAmplitude₂ P Φ (ccC C) (-pOut) kIn
          (lineMomentum₂ (ccC C) (-pIn) (-pOut) kIn ℓ) (fun i => ccIdx (βIn i))
          (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => ((-1) ^ nA * ∏ i, ccSign (αOut i) * ccSign (βIn i)) *
        ((fun ℓ' : Fin (loopCount C) → Fin 4 → ℝ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            QED.Lepton.regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    rw [regulatedAmplitude₂_ccC P Φ C hatt hnf pIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
      (fun ℓ' : Fin (loopCount C) → Fin 4 → ℝ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          QED.Lepton.regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ') αOut βIn μ)
      M hMdet a)

end Value

/-! ### The chains are closed under charge conjugation -/

/-- **The chains (C₁) are closed under charge conjugation**: `a ↔ c`, the chain reversed. -/
theorem isVPChain_ccC {n : ℕ} {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain n C) :
    QED.VPChain.IsVPChain n (ccC C) := by
  obtain ⟨a, b, c, sb, src, dst, hka, hkb, hkc, h0a, hab, hbc, hc0, hsb, hext, hsrc, hdst, hline,
    hins, hall⟩ := hC
  have hline' : ∀ i, C.1.2 (.inr (dst i)) = .inr (src i) := fun i => by
    rw [← hline i, (C.2 _).1]
  refine ⟨c, b, a, sb, fun i => dst (Fin.rev i), fun i => src (Fin.rev i), hkc, hkb, hka,
    (ccC_apply_eq_iff C _ _).mpr hc0, (ccC_apply_eq_iff C _ _).mpr hbc,
    (ccC_apply_eq_iff C _ _).mpr hab, (ccC_apply_eq_iff C _ _).mpr h0a, hsb, hext, ?_, ?_,
    fun i => hline' _, fun i => ?_, fun t => ?_⟩
  · simp only [Fin.rev_zero]
    exact hdst
  · simp only [Fin.rev_last]
    exact hsrc
  · simp only [Fin.rev_castSucc, Fin.rev_succ]
    rcases hins (Fin.rev i) with ⟨hk1, hk2, hne, u, w, hu, hw, huw, hwu⟩ | ⟨hk, heq, hne⟩
    · exact Or.inl ⟨hk2, hk1, Ne.symm hne, w, u, hw, hu, (ccC_apply_eq_iff C _ _).mpr huw,
        (ccC_apply_eq_iff C _ _).mpr hwu⟩
    · exact Or.inr ⟨by rw [heq]; exact hk, heq.symm, Ne.symm hne⟩
  · rcases hall t with h | h | h | ⟨i, h | h⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · refine Or.inr (Or.inr (Or.inr ⟨Fin.rev i, Or.inr ?_⟩))
      simp only [Fin.rev_succ, Fin.rev_rev]
      exact h
    · refine Or.inr (Or.inr (Or.inr ⟨Fin.rev i, Or.inl ?_⟩))
      simp only [Fin.rev_castSucc, Fin.rev_rev]
      exact h

theorem isVPChain_ccC_iff {n : ℕ} (C : Contraction 1 1 κ) :
    QED.VPChain.IsVPChain n (ccC C) ↔ QED.VPChain.IsVPChain n C :=
  ⟨fun h => by simpa using isVPChain_ccC h, isVPChain_ccC⟩

/-- The chains have no `δ₂, δ_m` vertex. -/
theorem ne_fermionCt_of_isVPChain {n : ℕ} {C : Contraction 1 1 κ}
    (hC : QED.VPChain.IsVPChain n C) (t : Fin N) : κ t ≠ .fermionCt := by
  obtain ⟨a, b, c, sb, src, dst, hka, hkb, hkc, -, -, -, -, -, -, -, -, -, hins, hall⟩ := hC
  rcases hall t with rfl | rfl | rfl | ⟨i, rfl | rfl⟩
  · rw [hka]; decide
  · rw [hkb]; decide
  · rw [hkc]; decide
  · rcases hins i with ⟨hk, -⟩ | ⟨hk, -⟩ <;> rw [hk] <;> decide
  · rcases hins i with ⟨-, hk, -⟩ | ⟨hk, heq, -⟩
    · rw [hk]; decide
    · rw [heq, hk]; decide

/-! ### The chain vertex -/

section Chain

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : QED.Lepton.Flavors F)

/-- Charge conjugation of the value of a set (b) chain contraction. -/
theorem contractionValue₂_ccC_chain {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain 2 C)
    (p' p : Fin 4 → ℝ) (a b μ : Fin 4) :
    QED.Lepton.contractionValue₂ P Φ (ccC C) (fun _ => -p) (fun _ => -p') (fun _ => p' - p)
        (fun _ => a) (fun _ => b) (fun _ => μ) =
      -(ccSign a * ccSign b) *
        QED.Lepton.contractionValue₂ P Φ C (fun _ => p') (fun _ => p) (fun _ => p' - p)
          (fun _ => ccIdx b) (fun _ => ccIdx a) (fun _ => μ) := by
  have hC' := isVPChain_ccC hC
  have h1 := QED.ChainProof.Enum.isOnePI_of_isVPChain_two hC
  have h2 := QED.ChainProof.Enum.isOnePI_of_isVPChain_two hC'
  have hL : loopCount (ccC C) = loopCount C := by
    rw [(QED.ChainProof.Enum.loopCount_of_isVPChain_two hC').2,
      (QED.ChainProof.Enum.loopCount_of_isVPChain_two hC).2]
  have hsum : ∑ v, externalMomentum C (fun _ => p') (fun _ => p) (fun _ => p' - p) v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum h1.1]
    simp
  have := contractionValue₂_ccC P Φ C h1.1.1 (ne_fermionCt_of_isVPChain hC) h1.2.1 h2.2.1 hL
    (fun _ => p') (fun _ => p) (fun _ => p' - p) hsum (fun _ => ccIdx b) (fun _ => ccIdx a)
    (fun _ => μ)
  simp only [ccIdx_ccIdx, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, pow_one,
    ccSign_ccIdx] at this
  rw [show (fun _ : Fin 1 => -p) = -fun _ : Fin 1 => p from rfl,
    show (fun _ : Fin 1 => -p') = -fun _ : Fin 1 => p' from rfl, this]
  ring

open scoped Classical in
/-- **Charge conjugation of the set (b) chain vertex** at fixed `ε`, for all momenta:
`V(-p, -p')_{ab} = -c(a) c(b) V(p', p)_{p(b) p(a)}`, i.e. `C V(p', p)ᵀ C = -V(-p, -p')`. -/
theorem vertexChain_two_cc (p' p : Fin 4 → ℝ) (μ a b : Fin 4) :
    QED.VPChain.vertexChain 2 P Φ (-p) (-p') μ a b =
      -(ccSign a * ccSign b) * QED.VPChain.vertexChain 2 P Φ p' p μ (ccIdx b) (ccIdx a) := by
  simp only [QED.VPChain.vertexChain, Matrix.of_apply, QED.Lepton.onePIFamilyFunction₂]
  have hk : (fun _ : Fin 1 => -p - -p') = fun _ => p' - p := by
    funext _
    abel
  rw [hk]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun κ _ => ?_
  refine Finset.sum_nbij' ccC ccC ?_ ?_ (fun C _ => ccC_ccC C) (fun C _ => ccC_ccC C) ?_
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    have h := isVPChain_ccC hC.2
    exact ⟨QED.ChainProof.Enum.isOnePI_of_isVPChain_two h, h⟩
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    have h := isVPChain_ccC hC.2
    exact ⟨QED.ChainProof.Enum.isOnePI_of_isVPChain_two h, h⟩
  · intro C hC
    have hC2 := (Finset.mem_filter.mp hC).2.2
    have hD := isVPChain_ccC hC2
    have hsign : fermionSign (ccC C) = fermionSign C := by
      simp only [fermionSign, ccC_fst, Equiv.Perm.sign_inv]
    have hv := contractionValue₂_ccC_chain P Φ (C := ccC C) hD p' p a b μ
    rw [ccC_ccC] at hv
    rw [hsign, hv]
    ring

/-- The entries of `Γ X Γ`. -/
theorem chir_mul_mul_chir_apply (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    (chir * X * chir) a b = sg a * sg b * X a b := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [sg]
  ring

/-- **The fixed-`ε` mirror identity of the set (b) chain vertex**, for all momenta:
`C V(p', p)ᵀ C = Γ V(p, p') Γ`. -/
theorem chargeConj_vertexChain_two (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    chargeConj * (QED.VPChain.vertexChain 2 P Φ p' p μ)ᵀ * chargeConj =
      chir * QED.VPChain.vertexChain 2 P Φ p p' μ * chir := by
  ext a b
  rw [QED.TwoLoop.LimitMirror.chargeConj_transpose_apply, chir_mul_mul_chir_apply]
  have h1 := vertexChain_two_cc P Φ p' p μ a b
  have h2 := vertexChain_neg P Φ 2 p p' μ a b
  rw [h1] at h2
  linear_combination -h2

end Chain

/-- **`ChainMirrorAt` holds.** -/
theorem chainMirrorAt : ChainMirrorAt :=
  fun P _ ε _ p' p _ μ => chargeConj_vertexChain_two { P with ε := ε } (chainFlavors P) p' p μ

/-- **The mirror link from existence and covariance.** -/
theorem chainMirrorLink_of_exists_cov (hE : ChainExistsLink) (hC : ChainCovLink) :
    ChainMirrorLink :=
  chainMirrorLink_of_mirrorAt hE hC chainMirrorAt

end QED.ChainProof.Conj

end
