/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelInvarianceOrderFive
public import QED.Algebra.ChargeConjugation

/-!
# Furry's theorem for the two orientations of the three-vertex fermion loop

Obligation O2-3 (section 3.3 of `docs/TWO-LOOP-DERIVATION.md`; Srednicki problem 58.2). The
classes `Fp` and `Fm` of five gauge vertices (`QED.TwoLoop.Enumeration.Class5`) are the two
orientations of the closed three-vertex fermion loop `2, 3, 4` attached to the open line `0 → 1`
by the external photon (at `2`) and the internal photons `(0 3)`, `(1 4)`. Their values (T₁₀)
cancel at fixed parameters, under momentum conservation.

* `QED.TwoLoop.Furry.furryCorr`: the line correspondence of `F₊` and `F₋`: the vertices and the
  photon lines are the same, the three fermion lines of the loop are reversed.
* `QED.TwoLoop.Furry.contractionAmplitude₂_Fm`: for a preserved flavoring, the amplitude (T₇) of
  `F₋` at line momenta `k'` is minus that of `F₊` at the pulled-back momenta (the loop momenta
  reversed). The spinor indices of the loop vertices are reindexed by
  `(α, β) ↦ (p ∘ β, p ∘ α)` with the charge-conjugation involution `p`
  (`QED.Dirac.ccIdx`); each of the three gauge vertices gives `-1`
  (`QED.Dirac.gamma_ccIdx`, `C γ^μ C⁻¹ = -(γ^μ)ᵀ`), each propagator none
  (`QED.OneLoop.electronPropagator_ccIdx`, `C S̃(k) C⁻¹ = S̃(-k)ᵀ`, `iε` included), and the
  remaining signs `s(a)²` cancel.
* `QED.TwoLoop.Furry.regulatedAmplitude₂_Fm`: the same for the regulated amplitude (T₈): the
  preserved flavorings and the regulator weights (X₇) of the two orientations agree, since the
  fermion cycles do; the cancellation is flavour by flavour.
* `QED.TwoLoop.Furry.contractionValue₂_Fm`: the value of `F₋` is minus that of `F₊`. The routings
  are related by an integer unimodular affine change of loop momenta
  (`QED.TwoLoop.Relabel.LineCorr.exists_routing_change`), under which the joint energy-first
  integral is invariant for every integrand; it also commutes with negation.
* `QED.TwoLoop.Furry.furry_pair`: **Furry's theorem for the pair**:
  `contractionValue₂ P F₊ + contractionValue₂ P F₋ = 0`.
* `QED.TwoLoop.Furry.onePIFunction₂_five_sub_four_eq_furry`: the order-`e⁵` vertex with the
  Furry pair removed: the seven classes `L, X, C₊, C₋, S₊, S₋, VP` with coefficient one and
  their signs, plus the counterterm contractions.

No integrability is needed: the identities hold for the integrands pointwise, and the joint
prescription (T₉) respects them for every integrand.
-/

@[expose] public section

namespace QED.TwoLoop.Furry

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.TwoLoop.Routing QED.Dirac
  Complex

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The Furry triangle `F₊`: fermion flow `2 → 3 → 4 → 2`. -/
abbrev cP : Contraction 1 1 (gauges 5) := Class5.Fp.rep

/-- The Furry triangle `F₋`: fermion flow `2 → 4 → 3 → 2`. -/
abbrev cM : Contraction 1 1 (gauges 5) := Class5.Fm.rep

/-! ### Finite facts about the two representatives -/

theorem cP_inl (i : Fin 1) (t : FV) : cP.1.1 (.inl i) = .inr t ↔ t = fv5 1 := by
  revert i t
  decide +kernel

theorem cM_inl (i : Fin 1) (t : FV) : cM.1.1 (.inl i) = .inr t ↔ t = fv5 1 := by
  revert i t
  decide +kernel

theorem cP_inr_inl (t : FV) (i : Fin 1) : cP.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem cM_inr_inl (t : FV) (i : Fin 1) : cM.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem cP_three : cP.1.1 (.inr (fv5 3)) = .inr (fv5 2) := by decide +kernel

theorem cP_four : cP.1.1 (.inr (fv5 4)) = .inr (fv5 3) := by decide +kernel

theorem cP_pow_three : cP.1.1 ^ 3 = 1 := by decide +kernel

theorem cM_pow_three : cM.1.1 ^ 3 = 1 := by decide +kernel

/-! ### The fermion lines -/

/-- The fermion lines of `F₊`, by head `1, 2, 3, 4` (tails `0, 4, 2, 3`). -/
def lineP : Fin 4 → FermionLine cP :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The fermion lines of `F₋`, by head `1, 2, 3, 4` (tails `0, 3, 4, 2`). -/
def lineM : Fin 4 → FermionLine cM :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

theorem lineP_bijective : Function.Bijective lineP := by decide +kernel

theorem lineM_bijective : Function.Bijective lineM := by decide +kernel

theorem prod_lineP [Fintype (FermionLine cP)] (g : FermionLine cP → ℂ) :
    ∏ f, g f = g (lineP 0) * g (lineP 1) * g (lineP 2) * g (lineP 3) := by
  rw [← (Equiv.ofBijective _ lineP_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_lineM [Fintype (FermionLine cM)] (g : FermionLine cM → ℂ) :
    ∏ f, g f = g (lineM 0) * g (lineM 1) * g (lineM 2) * g (lineM 3) := by
  rw [← (Equiv.ofBijective _ lineM_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem tail_lineP : (lineP 0).tail = fv5 0 ∧ (lineP 1).tail = fv5 4 ∧ (lineP 2).tail = fv5 2 ∧
    (lineP 3).tail = fv5 3 := by decide +kernel

theorem tail_lineM : (lineM 0).tail = fv5 0 ∧ (lineM 1).tail = fv5 3 ∧ (lineM 2).tail = fv5 4 ∧
    (lineM 3).tail = fv5 2 := by decide +kernel

/-! ### The line correspondence -/

/-- The relabelling of the loop heads: `2 ↦ 4`, `3 ↦ 2`, `4 ↦ 3`. The line of `F₊` with head `h`
and tail `t` corresponds to the line of `F₋` with head `t` and tail `h`. -/
def loopPerm : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 3 4

/-- The fermion lines of `F₊` and `F₋`. -/
def fermEquiv : FermionLine cP ≃ FermionLine cM :=
  Equiv.subtypeEquiv (fvPerm loopPerm) (by decide +kernel)

/-- The photon lines of `F₊` and `F₋`: the photon pairings are equal. -/
def photEquiv : PhotonLine cP ≃ PhotonLine cM :=
  Equiv.subtypeEquivRight fun _ => Iff.rfl

/-- The reversed lines: the fermion lines of the loop. -/
def furryRev : Line cP → Bool
  | .inl f => decide (2 ≤ f.1.1)
  | .inr _ => false

theorem fermEquiv_ends : ∀ f : FermionLine cP,
    ((fermEquiv f).tail.1, (fermEquiv f).1.1) =
      if decide (2 ≤ f.1.1) then (f.1.1, f.tail.1) else (f.tail.1, f.1.1) := by
  decide +kernel

/-- **The line correspondence of the two orientations**: same vertices, same photon lines, the
loop's fermion lines reversed. -/
def furryCorr : LineCorr cP cM where
  vtx := Equiv.refl _
  line := Equiv.sumCongr fermEquiv photEquiv
  rev := furryRev
  ends_line f := by
    rcases f with f | g
    · exact fermEquiv_ends f
    · rfl

theorem fermEquiv_lineP : fermEquiv (lineP 0) = lineM 0 ∧ fermEquiv (lineP 1) = lineM 3 ∧
    fermEquiv (lineP 2) = lineM 1 ∧ fermEquiv (lineP 3) = lineM 2 := by decide +kernel

theorem pull_lineP (k' : Line cM → Fin 4 → ℝ) :
    furryCorr.pull k' (.inl (lineP 0)) = k' (.inl (lineM 0)) ∧
      furryCorr.pull k' (.inl (lineP 1)) = -k' (.inl (lineM 3)) ∧
      furryCorr.pull k' (.inl (lineP 2)) = -k' (.inl (lineM 1)) ∧
      furryCorr.pull k' (.inl (lineP 3)) = -k' (.inl (lineM 2)) := by
  obtain ⟨h0, h1, h2, h3⟩ := fermEquiv_lineP
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, furryCorr, Equiv.sumCongr_apply, Sum.map_inl, h0, h1, h2, h3] <;>
    rfl

/-! ### Flavorings: the two orientations have the same fermion cycles -/

section Cycles

variable {α : Type*}

/-- For a permutation of order dividing three, being in the same cycle is a bounded search. -/
theorem sameCycle_iff_of_pow_three {f : Equiv.Perm α} (hf : f ^ 3 = 1) (x y : α) :
    f.SameCycle x y ↔ ∃ i : Fin 3, (f ^ (i : ℕ)) x = y := by
  constructor
  · rintro ⟨k, rfl⟩
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    refine ⟨⟨(k % 3).toNat, by omega⟩, ?_⟩
    simp only
    have hf' : f ^ (3 : ℤ) = 1 := by exact_mod_cast hf
    rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_eq_zpow_emod k hf']
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℕ), by rw [zpow_natCast]⟩

end Cycles

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- A flavoring is preserved exactly when it is constant on the fermion cycles. -/
theorem preserves_iff_sameCycle (C : Contraction nf nA κ) (φ : Flavoring κ) :
    Preserves C φ ↔
      ∀ x y, Equiv.Perm.SameCycle C.1.1 x y → fermionFlavor φ x = fermionFlavor φ y := by
  refine ⟨fun h x y hxy => fermionFlavor_eq_of_sameCycle h hxy, fun h x => (h _ _ ⟨1, ?_⟩).symm⟩
  simp

/-- Contractions with the same fermion cycles preserve the same flavorings. -/
theorem preserves_iff_of_sameCycle {C C' : Contraction nf nA κ}
    (h : ∀ x y, Equiv.Perm.SameCycle C.1.1 x y ↔ Equiv.Perm.SameCycle C'.1.1 x y)
    (φ : Flavoring κ) : Preserves C φ ↔ Preserves C' φ := by
  simp only [preserves_iff_sameCycle, h]

/-- The fermion cycles of contractions with the same fermion cycles. -/
def cycleEquivOfSameCycle {C C' : Contraction nf nA κ}
    (h : ∀ x y, Equiv.Perm.SameCycle C.1.1 x y ↔ Equiv.Perm.SameCycle C'.1.1 x y) :
    Quotient (Equiv.Perm.SameCycle.setoid C.1.1) ≃
      Quotient (Equiv.Perm.SameCycle.setoid C'.1.1) :=
  Quotient.congr (Equiv.refl _) h

theorem cycleEquivOfSameCycle_mk {C C' : Contraction nf nA κ}
    (h : ∀ x y, Equiv.Perm.SameCycle C.1.1 x y ↔ Equiv.Perm.SameCycle C'.1.1 x y)
    (x : Fin nf ⊕ Wick.FermionVertex κ) :
    cycleEquivOfSameCycle h (Quotient.mk _ x) = Quotient.mk _ x :=
  rfl

/-- The closed loops of contractions with the same fermion cycles. -/
def closedLoopEquivOfSameCycle {C C' : Contraction nf nA κ}
    (h : ∀ x y, Equiv.Perm.SameCycle C.1.1 x y ↔ Equiv.Perm.SameCycle C'.1.1 x y) :
    ClosedLoop C ≃ ClosedLoop C' :=
  Equiv.subtypeEquiv (cycleEquivOfSameCycle h) fun q => by
    refine forall_congr' fun i => not_congr ?_
    rw [← (cycleEquivOfSameCycle h).injective.eq_iff, cycleEquivOfSameCycle_mk]

open scoped Classical in
/-- Contractions with the same fermion cycles have the same regulator weights (X₇) on preserved
flavorings. -/
theorem loopWeight_eq_of_sameCycle (P : Params) {C C' : Contraction nf nA κ}
    (h : ∀ x y, Equiv.Perm.SameCycle C.1.1 x y ↔ Equiv.Perm.SameCycle C'.1.1 x y)
    {φ : Flavoring κ} (hφ : Preserves C' φ) : loopWeight P C φ = loopWeight P C' φ := by
  unfold loopWeight
  apply Fintype.prod_equiv (closedLoopEquivOfSameCycle h)
  intro q
  have hmk : (closedLoopEquivOfSameCycle h q).1 = Quotient.mk _ q.1.out := by
    change cycleEquivOfSameCycle h q.1 = _
    conv_lhs => rw [← Quotient.out_eq q.1]
    rfl
  have hsc : Equiv.Perm.SameCycle C'.1.1 (closedLoopEquivOfSameCycle h q).1.out q.1.out := by
    have h' : (Quotient.mk _ (closedLoopEquivOfSameCycle h q).1.out :
        Quotient (Equiv.Perm.SameCycle.setoid C'.1.1)) = Quotient.mk _ q.1.out := by
      rw [Quotient.out_eq, hmk]
    exact Quotient.exact h'
  rw [fermionFlavor_eq_of_sameCycle hφ hsc]

/-- `F₊` and `F₋` have the same fermion cycles: the loop is reversed, not changed. -/
theorem sameCycle_cP_iff (x y : Fin 1 ⊕ FV) :
    Equiv.Perm.SameCycle cP.1.1 x y ↔ Equiv.Perm.SameCycle cM.1.1 x y := by
  rw [sameCycle_iff_of_pow_three cP_pow_three, sameCycle_iff_of_pow_three cM_pow_three]
  revert x y
  decide +kernel

/-! ### The amplitude -/

/-- The reindexing of the spinor indices: on the loop vertices `2, 3, 4`,
`(α, β) ↦ (p ∘ β, p ∘ α)` with the charge-conjugation involution `p`; elsewhere unchanged. -/
def swapIdx (x : (FV → Fin 4) × (FV → Fin 4)) : (FV → Fin 4) × (FV → Fin 4) :=
  (fun t => if 2 ≤ t.1 then ccIdx (x.2 t) else x.1 t,
    fun t => if 2 ≤ t.1 then ccIdx (x.1 t) else x.2 t)

theorem swapIdx_involutive : Function.Involutive swapIdx := by
  intro x
  ext t <;> by_cases h : 2 ≤ t.1 <;> simp [swapIdx, h]

/-- The reindexing as a permutation. -/
def swapEquiv : Equiv.Perm ((FV → Fin 4) × (FV → Fin 4)) :=
  swapIdx_involutive.toPerm _

/-- Reindexing a double sum over spinor index families by `swapIdx`. -/
theorem sum_swapIdx (F G : (FV → Fin 4) → (FV → Fin 4) → ℂ)
    (h : ∀ α β, F (swapIdx (α, β)).1 (swapIdx (α, β)).2 = -G α β) :
    ∑ α, ∑ β, F α β = -∑ α, ∑ β, G α β := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Equiv.sum_comp swapEquiv,
    ← Finset.sum_neg_distrib]
  exact Fintype.sum_congr _ _ fun x => h x.1 x.2

/-- The scalar identity behind the cancellation: three vertex signs `-1`, and every
charge-conjugation sign `s(a)` occurring twice. -/
theorem furry_algebra (c g0 g1 g2 g3 g4 d S0 S1 S2 S3 Ph a2 b2 a3 b3 a4 b4 : ℂ)
    (ha2 : a2 * a2 = 1) (hb2 : b2 * b2 = 1) (ha3 : a3 * a3 = 1) (hb3 : b3 * b3 = 1)
    (ha4 : a4 * a4 = 1) (hb4 : b4 * b4 = 1) :
    c * g0 * (c * g1) * (c * (-(a2 * b2) * g2)) * (c * (-(a3 * b3) * g3)) *
          (c * (-(a4 * b4) * g4)) *
        (d * S0 * (d * (a2 * b3 * S2)) * (d * (a3 * b4 * S3)) * (d * (a4 * b2 * S1))) * Ph =
      -(c * g0 * (c * g1) * (c * g2) * (c * g3) * (c * g4) *
        (d * S0 * (d * S1) * (d * S2) * (d * S3)) * Ph) := by
  have hQ : a2 * a2 * (b2 * b2) * (a3 * a3) * (b3 * b3) * (a4 * a4) * (b4 * b4) = 1 := by
    rw [ha2, hb2, ha3, hb3, ha4, hb4]
    ring
  linear_combination
    (-(c * g0 * (c * g1) * (c * g2) * (c * g3) * (c * g4) *
      (d * S0 * (d * S1) * (d * S2) * (d * S3)) * Ph)) * hQ

theorem val_lineM : (lineM 0).1 = fv5 1 ∧ (lineM 1).1 = fv5 2 ∧ (lineM 2).1 = fv5 3 ∧
    (lineM 3).1 = fv5 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem val_lineP : (lineP 0).1 = fv5 1 ∧ (lineP 1).1 = fv5 2 ∧ (lineP 2).1 = fv5 3 ∧
    (lineP 3).1 = fv5 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

open scoped Classical in
/-- **Charge conjugation of the loop**: for a flavoring preserved by `F₊`, the amplitude (T₇) of
`F₋` at line momenta `k'` is minus the amplitude of `F₊` at the pulled-back line momenta. -/
theorem contractionAmplitude₂_Fm (P : Params) (φ : Flavoring (gauges 5)) (hφ : Preserves cP φ)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (k' : Line cM → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cM φ pIn kIn k' αOut βIn μ =
      -contractionAmplitude₂ P cP φ pIn kIn (furryCorr.pull k') αOut βIn μ := by
  have h32 : φ.1 (fv5 3) = φ.1 (fv5 2) := by
    have := hφ (.inr (fv5 3))
    rw [cP_three] at this
    exact this.symm
  have h42 : φ.1 (fv5 4) = φ.1 (fv5 2) := by
    have := hφ (.inr (fv5 4))
    rw [cP_four] at this
    exact this.symm.trans h32
  obtain ⟨tP0, tP1, tP2, tP3⟩ := tail_lineP
  obtain ⟨tM0, tM1, tM2, tM3⟩ := tail_lineM
  obtain ⟨p0, p1, p2, p3⟩ := pull_lineP k'
  obtain ⟨vM0, vM1, vM2, vM3⟩ := val_lineM
  obtain ⟨vP0, vP1, vP2, vP3⟩ := val_lineP
  unfold contractionAmplitude₂
  refine sum_swapIdx _ _ fun α β => ?_
  beta_reduce
  rw [← Finset.sum_neg_distrib]
  refine Fintype.sum_congr _ _ fun lor => ?_
  rw [← mul_neg]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine if_congr ?_ rfl rfl
    simp only [cP_inl, cM_inl, cP_inr_inl, cM_inr_inl, forall_eq]
    simp [swapIdx, fv5]
    exact fun _ _ => Iff.rfl
  have hph : (∏ g : PhotonLine cM, (1 / I) *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k' (.inr g)) (lor g.1) (lor g.head)) =
      ∏ g : PhotonLine cP, (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
        (furryCorr.pull k' (.inr g)) (lor g.1) (lor g.head) :=
    (Fintype.prod_equiv photEquiv _ _ fun _ => rfl).symm
  rw [hph]
  simp only [vertexFactor_gauges, Fin.prod_univ_five, prod_lineP, prod_lineM, tP0, tP1, tP2, tP3,
    tM0, tM1, tM2, tM3, p0, p1, p2, p3, vM0, vM1, vM2, vM3, vP0, vP1, vP2, vP3, h32, h42]
  simp only [swapIdx, fv5, Fin.reduceLE, ite_true, ite_false]
  rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
    QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx]
  exact furry_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ccSign_mul_self _) (ccSign_mul_self _)
    (ccSign_mul_self _) (ccSign_mul_self _) (ccSign_mul_self _) (ccSign_mul_self _)

open scoped Classical in
/-- **Charge conjugation of the regulated amplitude** (T₈): the regulated amplitude of `F₋` at line
momenta `k'` is minus that of `F₊` at the pulled-back line momenta. The two orientations preserve
the same flavorings with the same regulator weights, and the amplitudes cancel flavoring by
flavoring. -/
theorem regulatedAmplitude₂_Fm (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k' : Line cM → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cM pIn kIn k' αOut βIn μ =
      -regulatedAmplitude₂ P cP pIn kIn (furryCorr.pull k') αOut βIn μ := by
  unfold regulatedAmplitude₂
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Fintype.sum_congr _ _ fun φ => ?_
  by_cases hφ : Preserves cP φ
  · have hφ' : Preserves cM φ := (preserves_iff_of_sameCycle sameCycle_cP_iff φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte, loopWeight_eq_of_sameCycle P sameCycle_cP_iff hφ',
      contractionAmplitude₂_Fm P φ hφ, mul_neg]
  · have hφ' : ¬ Preserves cM φ := mt (preserves_iff_of_sameCycle sameCycle_cP_iff φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, neg_zero]

/-! ### The value -/

/-- The external momenta of the two orientations agree vertex by vertex. -/
theorem externalMomentum_Fm (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cM pOut pIn kIn (furryCorr.vtx v) = externalMomentum cP pOut pIn kIn v := by
  change externalMomentum cM pOut pIn kIn v = _
  unfold externalMomentum
  simp only [cP_inl, cM_inl, cP_inr_inl, cM_inr_inl]
  rfl

/-- The joint energy-first integral (T₉) commutes with negation, for every integrand. -/
theorem jointEnergyFirstIntegral_neg (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral L (fun ℓ => -F ℓ) = -jointEnergyFirstIntegral L F := by
  unfold jointEnergyFirstIntegral
  simp only [MeasureTheory.integral_neg]

/-- **The value of `F₋` is minus the value of `F₊`** (T₁₀), at every parameter set and all external
indices, under momentum conservation `pOut 0 = pIn 0 + kIn 0`. -/
theorem contractionValue₂_Fm (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Fm.rep pOut pIn kIn αOut βIn μ =
      -contractionValue₂ P Class5.Fp.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .Fp
  have hM := rep_isOnePI .Fm
  have hsum : ∑ v, externalMomentum cP pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := furryCorr.exists_routing_change hP.2.1 hM.2.1
    (externalMomentum_Fm pOut pIn kIn) hsum (loopCount_rep .Fp) (loopCount_rep .Fm)
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Fm),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .Fp)]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cM pIn kIn (lineMomentum₂ cM pOut pIn kIn ℓ) αOut βIn μ) =
      fun ℓ => -((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cP pIn kIn (lineMomentum₂ cP pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    rw [regulatedAmplitude₂_Fm, h, mul_neg]
    rfl
  rw [e, jointEnergyFirstIntegral_neg]
  exact congrArg Neg.neg
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cP pIn kIn (lineMomentum₂ cP pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

/-- **Furry's theorem for the pair** (obligation O2-3): under momentum conservation, the values
(T₁₀) of the two orientations `F₊`, `F₋` of the three-vertex fermion loop cancel, at every
parameter set (in particular at every fixed `ε`) and all external indices. -/
theorem furry_pair (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Fp.rep pOut pIn kIn αOut βIn μ +
      contractionValue₂ P Class5.Fm.rep pOut pIn kIn αOut βIn μ = 0 := by
  rw [contractionValue₂_Fm P hmom, add_neg_cancel]

/-- The classes of five gauge vertices other than the Furry pair. -/
def nonFurry : Finset Class5 := {.L, .X, .Cp, .Cm, .Sp, .Sm, .VP}

/-- **The order-`e⁵` vertex with the Furry pair removed** (obligations O2-2, O2-3): under
momentum conservation `pOut 0 = pIn 0 + kIn 0`, `onePIFunction₂ P 1 1 5 - onePIFunction₂ P 1 1 4`
is the signed sum of the values of the seven classes `L, X, C₊, C₋, S₊, S₋, VP`, each with
coefficient one, plus the 1PI contractions with one counterterm vertex. -/
theorem onePIFunction₂_five_sub_four_eq_furry (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      ∑ c ∈ nonFurry, (c.sign : ℂ) * contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ +
        (Nat.factorial 4 : ℂ)⁻¹ * (listValue P onePI_gggf pOut pIn kIn αOut βIn μ +
          listValue P onePI_gggp pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggfg pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggpg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gfgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gpgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_fggg pOut pIn kIn αOut βIn μ +
          listValue P onePI_pggg pOut pIn kIn αOut βIn μ) +
        (Nat.factorial 3 : ℂ)⁻¹ * (listValue P onePI_ggC pOut pIn kIn αOut βIn μ +
          listValue P onePI_gCg pOut pIn kIn αOut βIn μ +
          listValue P onePI_Cgg pOut pIn kIn αOut βIn μ) := by
  rw [onePIFunction₂_five_sub_four_eq P hmom]
  congr 2
  have hc : nonFurryᶜ = {.Fp, .Fm} := by decide
  rw [← Finset.sum_add_sum_compl nonFurry, hc, Finset.sum_pair (by decide)]
  have h := furry_pair P hmom αOut βIn μ
  simp only [Class5.sign, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
  rw [← neg_add, h, neg_zero, add_zero]

end QED.TwoLoop.Furry

end
