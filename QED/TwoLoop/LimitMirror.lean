/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimit
public import QED.TwoLoop.FurryPair
public import QED.Algebra.SandwichReductionMirror

/-!
# Charge conjugation of the open-line classes: `C₊ ↔ C₋`

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Charge conjugation reverses
the open fermion line. Relabelling the vertices by `v ↦ 4 - v`, the reversed line of `C₊`
(external photon at `1`, internal photons `(0 3)`, `(2 4)`) is the line of `C₋` (external photon
at `3`, internal photons `(0 2)`, `(1 4)`), with all six internal lines reversed.

* `QED.TwoLoop.LimitMirror.exists_routing_change_of_ext`: the routing change of
  `QED.TwoLoop.Relabel.LineCorr.exists_routing_change` when the two contractions carry
  *different* external data whose external momenta match vertex by vertex.
* `QED.TwoLoop.LimitMirror.corrCpCm`: the line correspondence of `C₊` and `C₋`.
* `QED.TwoLoop.LimitMirror.contractionAmplitude₂_Cm_cc`: the amplitude (T₇) of `C₋` at line
  momenta `k'` and external spinor indices `(p(b), p(a))` is `-s(a) s(b)` times the amplitude of
  `C₊` at the pulled-back (negated) momenta and indices `(a, b)`, with the charge-conjugation
  involution `p` and signs `s` (`QED.Dirac.ccIdx`, `QED.Dirac.ccSign`). Each of the five gauge
  vertices gives `-1`, each propagator none.
* `QED.TwoLoop.LimitMirror.contractionValue₂_Cm_cc`: the same for the values (T₁₀), at every
  parameter set (in particular every `ε`), with the external data of `C₋` the charge conjugate
  `(p_out, p_in, k) ↦ (-p_in, -p_out, k)` of those of `C₊`.
-/

@[expose] public section

namespace QED.TwoLoop.LimitMirror

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.TwoLoop.Routing QED.Dirac
  QED.TwoLoop.Bridge Complex

/-! ### Routing changes between different external data -/

section Routing

variable {nf nA N N' : ℕ} {κ : Fin N → Wick.VertexKind} {κ' : Fin N' → Wick.VertexKind}
  {C : Contraction nf nA κ} {C' : Contraction nf nA κ'}

theorem isConserved_pull_of_ext (c : LineCorr C C') {pOut pIn pOut' pIn' : Fin nf → Fin 4 → ℝ}
    {kIn kIn' : Fin nA → Fin 4 → ℝ}
    (hext : ∀ v, externalMomentum C' pOut' pIn' kIn' (c.vtx v) =
      externalMomentum C pOut pIn kIn v)
    {P' : Line C' → Fin 4 → ℝ} (hP' : IsConserved C' pOut' pIn' kIn' P') :
    IsConserved C pOut pIn kIn (c.pull P') := fun v => by
  rw [LineCorr.inflow_pull, ← hext]
  exact hP' _

theorem exists_pull_lineMomentum₂_of_ext (c : LineCorr C C')
    {pOut pIn pOut' pIn' : Fin nf → Fin 4 → ℝ} {kIn kIn' : Fin nA → Fin 4 → ℝ}
    (hV' : VerticesConnected C')
    (hext : ∀ v, externalMomentum C' pOut' pIn' kIn' (c.vtx v) =
      externalMomentum C pOut pIn kIn v)
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) {L : ℕ} (hL : loopCount C = L) :
    ∃ (M : Matrix (Fin L) (Fin L) ℤ) (a : Fin L → Fin 4 → ℝ), ∀ ℓ : Fin L → Fin 4 → ℝ,
      c.pull (lineMomentum₂ C' pOut' pIn' kIn' ℓ) =
        lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a) := by
  have hsum' : ∑ v, externalMomentum C' pOut' pIn' kIn' v = 0 := by
    rw [← c.vtx.sum_comp]
    simp only [hext, hsum]
  have haff : ∀ r, IsIntAffine fun ℓ : Fin L → Fin 4 → ℝ =>
      chordValues hL (c.pull (lineMomentum₂ C' pOut' pIn' kIn' ℓ)) r := fun r => by
    simp only [chordValues, LineCorr.pull]
    exact IsIntAffine.ite _ (IsIntAffine.lineMomentum₂ _ _ _ _ _).neg
      (IsIntAffine.lineMomentum₂ _ _ _ _ _)
  choose M a hMa using haff
  refine ⟨Matrix.of M, fun r => a r, fun ℓ => ?_⟩
  have hcons := isConserved_pull_of_ext c hext (isConserved_lineMomentum₂ hV' hsum' ℓ)
  have hval : matAct (Matrix.of M) ℓ + (fun r => a r) =
      chordValues hL (c.pull (lineMomentum₂ C' pOut' pIn' kIn' ℓ)) := by
    funext r
    exact (hMa r ℓ).symm
  rw [hval]
  funext f
  exact eq_lineMomentum₂_of_isConserved hcons
    (fun g hg => (chordMomentum_chordValues hL _ hg).symm) f

theorem symm_hext_of_ext (c : LineCorr C C') {pOut pIn pOut' pIn' : Fin nf → Fin 4 → ℝ}
    {kIn kIn' : Fin nA → Fin 4 → ℝ}
    (hext : ∀ v, externalMomentum C' pOut' pIn' kIn' (c.vtx v) =
      externalMomentum C pOut pIn kIn v) (v : Fin N') :
    externalMomentum C pOut pIn kIn (c.symm.vtx v) = externalMomentum C' pOut' pIn' kIn' v := by
  have := hext (c.vtx.symm v)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- **Changing the chords between different external data**: for corresponding connected
contractions with the same number `L` of loops, whose external momenta (for the external data of
each) match vertex by vertex and sum to zero, the routing of `C'` pulled back to `C` is the
routing of `C` at `M ℓ + a`, with `M` integer and `det M = ±1`. -/
theorem exists_routing_change_of_ext (c : LineCorr C C')
    {pOut pIn pOut' pIn' : Fin nf → Fin 4 → ℝ} {kIn kIn' : Fin nA → Fin 4 → ℝ}
    (hV : VerticesConnected C) (hV' : VerticesConnected C')
    (hext : ∀ v, externalMomentum C' pOut' pIn' kIn' (c.vtx v) =
      externalMomentum C pOut pIn kIn v)
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) {L : ℕ} (hL : loopCount C = L)
    (hL' : loopCount C' = L) :
    ∃ (M : Matrix (Fin L) (Fin L) ℤ), IsUnit M.det ∧ ∃ a : Fin L → Fin 4 → ℝ,
      ∀ ℓ : Fin L → Fin 4 → ℝ, c.pull (lineMomentum₂ C' pOut' pIn' kIn' ℓ) =
        lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a) := by
  obtain ⟨M, a, h⟩ := exists_pull_lineMomentum₂_of_ext c hV' hext hsum hL
  have hsum' : ∑ v, externalMomentum C' pOut' pIn' kIn' v = 0 := by
    rw [← c.vtx.sum_comp]
    simp only [hext, hsum]
  obtain ⟨M', a', h'⟩ :=
    exists_pull_lineMomentum₂_of_ext c.symm hV (symm_hext_of_ext c hext) hsum' hL'
  refine ⟨M, ?_, a, h⟩
  have hid : ∀ ℓ : Fin L → Fin 4 → ℝ, matAct M' (matAct M ℓ + a) + a' = ℓ := fun ℓ => by
    have h1 := h' (matAct M ℓ + a)
    rw [← h ℓ, LineCorr.pull_symm_pull] at h1
    have h2 := congrArg (chordValues hL') h1
    rw [chordValues_lineMomentum₂, chordValues_lineMomentum₂] at h2
    exact h2.symm
  have h0 := hid 0
  have hMM : ∀ ℓ, matAct (M' * M) ℓ = ℓ := fun ℓ => by
    have := hid ℓ
    rw [matAct_add, matAct_matAct, add_assoc] at this
    have h0' := h0
    rw [show matAct M (0 : Fin L → Fin 4 → ℝ) = 0 by funext s; simp [matAct], zero_add] at h0'
    rwa [h0', add_zero] at this
  have hone := eq_one_of_matAct hMM
  have hdet : M'.det * M.det = 1 := by rw [← Matrix.det_mul, hone, Matrix.det_one]
  exact IsUnit.of_mul_eq_one_right _ hdet

end Routing

/-! ### The line correspondence of `C₊` and `C₋` -/

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-- The reversal `v ↦ 4 - v` of the five vertices. -/
def revV : Equiv.Perm (Fin 5) := Fin.revPerm

/-- The heads of the fermion lines: the line of `C₊` with head `h` (tail `h - 1`) corresponds to
the line of `C₋` with head `5 - h` (tail `4 - h`). -/
def headPermC : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 2 3

/-- The photon lines are indexed by the field of their first vertex: `0 → 3` and `2 → 4` of `C₊`
correspond to `1 → 4` and `0 → 2` of `C₋`. -/
def photPermC : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

def fermEquivC : FermionLine cCp ≃ FermionLine cCm :=
  Equiv.subtypeEquiv (fvPerm headPermC) (by decide +kernel)

def photEquivC : PhotonLine cCp ≃ PhotonLine cCm :=
  Equiv.subtypeEquiv (psPerm photPermC) (by decide +kernel)

theorem ends_corrC : ∀ f : Line cCp,
    Line.ends (Equiv.sumCongr fermEquivC photEquivC f : Line cCm) =
      (revV f.ends.2, revV f.ends.1) := by
  decide +kernel

/-- **The line correspondence of `C₊` and `C₋`**: vertices `v ↦ 4 - v`, every line reversed. -/
def corrCpCm : LineCorr cCp cCm where
  vtx := revV
  line := Equiv.sumCongr fermEquivC photEquivC
  rev := fun _ => true
  ends_line f := by
    simp only [ite_true]
    exact ends_corrC f

/-! ### Finite facts -/

theorem cCp_inl' (i : Fin 1) (t : FV) : cCp.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem cCm_inl' (i : Fin 1) (t : FV) : cCm.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem cCp_inr_inl' (t : FV) (i : Fin 1) : cCp.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem cCm_inr_inl' (t : FV) (i : Fin 1) : cCm.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem cCp_ph (j : Fin 1) (a : PS) : cCp.1.2 (.inl j) = .inr a ↔ a = ps5 1 := by
  revert j a
  decide +kernel

theorem cCm_ph (j : Fin 1) (a : PS) : cCm.1.2 (.inl j) = .inr a ↔ a = ps5 3 := by
  revert j a
  decide +kernel

theorem tail_lineCp : (lineCp 0).tail = fv5 0 ∧ (lineCp 1).tail = fv5 1 ∧
    (lineCp 2).tail = fv5 2 ∧ (lineCp 3).tail = fv5 3 := by decide +kernel

theorem tail_lineCm : (lineCm 0).tail = fv5 0 ∧ (lineCm 1).tail = fv5 1 ∧
    (lineCm 2).tail = fv5 2 ∧ (lineCm 3).tail = fv5 3 := by decide +kernel

theorem val_lineCp : (lineCp 0).1 = fv5 1 ∧ (lineCp 1).1 = fv5 2 ∧ (lineCp 2).1 = fv5 3 ∧
    (lineCp 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem val_lineCm : (lineCm 0).1 = fv5 1 ∧ (lineCm 1).1 = fv5 2 ∧ (lineCm 2).1 = fv5 3 ∧
    (lineCm 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem phot_Cp : (photCp 0).1 = ps5 0 ∧ (photCp 0).head = ps5 3 ∧ (photCp 1).1 = ps5 2 ∧
    (photCp 1).head = ps5 4 := by decide +kernel

theorem phot_Cm : (photCm 0).1 = ps5 0 ∧ (photCm 0).head = ps5 2 ∧ (photCm 1).1 = ps5 1 ∧
    (photCm 1).head = ps5 4 := by decide +kernel

theorem line_corrCpCm : fermEquivC (lineCp 0) = lineCm 3 ∧ fermEquivC (lineCp 1) = lineCm 2 ∧
    fermEquivC (lineCp 2) = lineCm 1 ∧ fermEquivC (lineCp 3) = lineCm 0 ∧
    photEquivC (photCp 0) = photCm 1 ∧ photEquivC (photCp 1) = photCm 0 := by decide +kernel

theorem pull_corrCpCm (k' : Line cCm → Fin 4 → ℝ) :
    corrCpCm.pull k' (.inl (lineCp 0)) = -k' (.inl (lineCm 3)) ∧
      corrCpCm.pull k' (.inl (lineCp 1)) = -k' (.inl (lineCm 2)) ∧
      corrCpCm.pull k' (.inl (lineCp 2)) = -k' (.inl (lineCm 1)) ∧
      corrCpCm.pull k' (.inl (lineCp 3)) = -k' (.inl (lineCm 0)) ∧
      corrCpCm.pull k' (.inr (photCp 0)) = -k' (.inr (photCm 1)) ∧
      corrCpCm.pull k' (.inr (photCp 1)) = -k' (.inr (photCm 0)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := line_corrCpCm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, corrCpCm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, h0, h1,
      h2, h3, h4, h5, ite_true]

theorem fvPerm_revV (t : FV) :
    fvPerm revV t = ⟨Fin.rev t.1, fun h => Wick.VertexKind.noConfusion h⟩ :=
  rfl

theorem psPerm_revV (a : PS) : psPerm revV a = ⟨Fin.rev a.1, a.2⟩ :=
  rfl

/-! ### The amplitude -/

/-- The charge-conjugation reindexing of the spinor indices along the reversed line:
`(α, β) ↦ (p ∘ β ∘ r, p ∘ α ∘ r)`, with `r` the reversal `v ↦ 4 - v`. -/
def swapC (x : (FV → Fin 4) × (FV → Fin 4)) : (FV → Fin 4) × (FV → Fin 4) :=
  (fun t => ccIdx (x.2 (fvPerm revV t)), fun t => ccIdx (x.1 (fvPerm revV t)))

theorem fvPerm_revV_revV (t : FV) : fvPerm revV (fvPerm revV t) = t :=
  Subtype.ext (by simp [revV])

theorem psPerm_revV_revV (a : PS) : psPerm revV (psPerm revV a) = a := by
  rcases a with ⟨v, s⟩
  simp [psPerm_revV]

theorem swapC_involutive : Function.Involutive swapC := by
  intro x
  ext t <;> simp [swapC, fvPerm_revV_revV]

/-- The relabelling of the Lorentz indices along `v ↦ 4 - v`. -/
def lorC (lor : PS → Fin 4) : PS → Fin 4 := fun a => lor (psPerm revV a)

theorem lorC_involutive : Function.Involutive lorC := by
  intro lor
  funext a
  simp [lorC, psPerm_revV_revV]

/-- Reindexing the triple sum over spinor and Lorentz index families. -/
theorem sum_reindexC (F G : (FV → Fin 4) → (FV → Fin 4) → (PS → Fin 4) → ℂ) (c : ℂ)
    (h : ∀ α β lor, F (swapC (α, β)).1 (swapC (α, β)).2 (lorC lor) = c * G α β lor) :
    ∑ α, ∑ β, ∑ lor, F α β lor = c * ∑ α, ∑ β, ∑ lor, G α β lor := by
  have e1 : ∀ α β, ∑ lor, F α β lor = ∑ lor, F α β (lorC lor) := fun α β =>
    (Equiv.sum_comp (lorC_involutive.toPerm _) _).symm
  simp only [e1]
  rw [← Fintype.sum_prod_type' (f := fun α β => ∑ lor, F α β (lorC lor)),
    ← Fintype.sum_prod_type' (f := fun α β => ∑ lor, G α β lor),
    ← Equiv.sum_comp (swapC_involutive.toPerm _), Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_congr _ _ fun lor => h x.1 x.2 lor

theorem ccIdx_injective : Function.Injective ccIdx :=
  Function.LeftInverse.injective ccIdx_ccIdx

theorem ccSign_sq (a : Fin 4) : ccSign a ^ 2 = 1 := by
  rw [sq, ccSign_mul_self]

theorem lorC_ps (lor : PS → Fin 4) :
    lorC lor ⟨0, ⟨0, Nat.one_pos⟩⟩ = lor ⟨4, ⟨0, Nat.one_pos⟩⟩ ∧
      lorC lor ⟨1, ⟨0, Nat.one_pos⟩⟩ = lor ⟨3, ⟨0, Nat.one_pos⟩⟩ ∧
      lorC lor ⟨2, ⟨0, Nat.one_pos⟩⟩ = lor ⟨2, ⟨0, Nat.one_pos⟩⟩ ∧
      lorC lor ⟨3, ⟨0, Nat.one_pos⟩⟩ = lor ⟨1, ⟨0, Nat.one_pos⟩⟩ ∧
      lorC lor ⟨4, ⟨0, Nat.one_pos⟩⟩ = lor ⟨0, ⟨0, Nat.one_pos⟩⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem rev5 : Fin.rev (0 : Fin 5) = 4 ∧ Fin.rev (1 : Fin 5) = 3 ∧ Fin.rev (2 : Fin 5) = 2 ∧
    Fin.rev (3 : Fin 5) = 1 ∧ Fin.rev (4 : Fin 5) = 0 := by decide

/-- The external-index constraints of `C₋` after the reindexing are those of `C₊`. -/
theorem iff_indicator_Cm (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, cCm.1.1 (.inl i) = .inr t → (swapC (α, β)).1 t = ccIdx (βIn i)) ∧
        (∀ t i, cCm.1.1 (.inr t) = .inl i → (swapC (α, β)).2 t = ccIdx (αOut i)) ∧
        (∀ j a, cCm.1.2 (.inl j) = .inr a → lorC lor a = μ j)) ↔
      ((∀ i t, cCp.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, cCp.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, cCp.1.2 (.inl j) = .inr a → lor a = μ j)) := by
  simp only [cCp_inl', cCm_inl', cCp_inr_inl', cCm_inr_inl', cCp_ph, cCm_ph, Fin.forall_fin_one,
    forall_eq]
  simp only [ps5, lorC_ps]
  simp only [swapC, fvPerm_revV, fv5, rev5, ccIdx_injective.eq_iff]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

open scoped Classical in
/-- **Charge conjugation of the corner amplitude**: the amplitude (T₇) of `C₋` at line momenta
`k'` and external spinor indices `(p(b), p(a))` is `-s(a) s(b)` times the amplitude of `C₊` at
the pulled-back momenta and indices `(a, b)`. -/
theorem contractionAmplitude₂_Cm_cc (P : Params) (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ)
    (k' : Line cCm → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cCm zeroFlavoring pIn' kIn' k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionAmplitude₂ P cCp zeroFlavoring pIn kIn (corrCpCm.pull k') αOut βIn μ := by
  obtain ⟨tP0, tP1, tP2, tP3⟩ := tail_lineCp
  obtain ⟨tM0, tM1, tM2, tM3⟩ := tail_lineCm
  obtain ⟨vP0, vP1, vP2, vP3⟩ := val_lineCp
  obtain ⟨vM0, vM1, vM2, vM3⟩ := val_lineCm
  obtain ⟨gP0, gP0', gP1, gP1'⟩ := phot_Cp
  obtain ⟨gM0, gM0', gM1, gM1'⟩ := phot_Cm
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pull_corrCpCm k'
  unfold contractionAmplitude₂
  refine sum_reindexC _ _ _ fun α β lor => ?_
  beta_reduce
  conv_rhs => rw [mul_left_comm]
  have hiff := iff_indicator_Cm α β lor αOut βIn μ
  split_ifs with h1 h2 h2
  · have ha : α ⟨4, fun h => Wick.VertexKind.noConfusion h⟩ = αOut 0 := by
      simpa [fv5] using h2.1 0 _ ((cCp_inl' 0 _).mpr rfl)
    have hb : β ⟨0, fun h => Wick.VertexKind.noConfusion h⟩ = βIn 0 := by
      simpa [fv5] using h2.2.1 _ 0 ((cCp_inr_inl' _ 0).mpr rfl)
    rw [one_mul, one_mul]
    simp only [Relabel.vertexFactor_gauges, Fin.prod_univ_five, prod_fermionLine_Cp,
      prod_fermionLine_Cm, prod_photonLine_Cp, prod_photonLine_Cm, tP0, tP1, tP2, tP3, tM0, tM1,
      tM2, tM3, vP0, vP1, vP2, vP3, vM0, vM1, vM2, vM3, gP0, gP0', gP1, gP1', gM0, gM0', gM1, gM1',
      p0, p1, p2, p3, p4, p5]
    obtain ⟨l0, l1, l2, l3, l4⟩ := lorC_ps lor
    simp only [ps5, l0, l1, l2, l3, l4]
    simp only [swapC, fvPerm_revV, fv5, rev5, zeroFlavoring]
    rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photCm 0))),
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photCm 1))), ← ha, ← hb]
    ring_nf
    simp only [ccSign_sq]
    ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · simp

/-! ### The value -/

/-- The joint energy-first integral (T₉) commutes with constant factors, for every integrand. -/
theorem jointEnergyFirstIntegral_const_mul (L : ℕ) (c : ℂ) (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral L (fun ℓ => c * F ℓ) = c * jointEnergyFirstIntegral L F := by
  unfold jointEnergyFirstIntegral
  simp only [MeasureTheory.integral_const_mul]

/-- The external momenta of `C₋` with the charge-conjugate external data
`(-p_in, -p_out, k)` at the vertex `4 - v` are those of `C₊` at `v`. -/
theorem externalMomentum_Cm_cc (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cCm (fun i => -pIn i) (fun i => -pOut i) kIn (corrCpCm.vtx v) =
      externalMomentum cCp pOut pIn kIn v := by
  change externalMomentum cCm _ _ _ (Fin.rev v) = _
  rw [externalMomentum_cCm, externalMomentum_cCp]
  fin_cases v <;> simp

open scoped Classical in
/-- **Charge conjugation of the corner values** (T₁₀): at every parameter set (in particular at
every `ε`) and under momentum conservation `p_out = p_in + k`, the value of `C₋` with the
charge-conjugate external data `(-p_in, -p_out, k)` and external spinor indices `(p(b), p(a))` is
`-s(a) s(b)` times the value of `C₊` with the data `(p_out, p_in, k)` and indices `(a, b)`. -/
theorem contractionValue₂_Cm_cc (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Cm.rep (fun i => -pIn i) (fun i => -pOut i) kIn
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionValue₂ P Class5.Cp.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .Cp
  have hM := rep_isOnePI .Cm
  have hsum : ∑ v, externalMomentum cCp pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := exists_routing_change_of_ext corrCpCm hP.2.1 hM.2.1
    (externalMomentum_Cm_cc pOut pIn kIn) hsum (loopCount_rep .Cp) (loopCount_rep .Cm)
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Cm),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .Cp)]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cCm (fun i => -pOut i) kIn
        (lineMomentum₂ cCm (fun i => -pIn i) (fun i => -pOut i) kIn ℓ)
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => -(ccSign (αOut 0) * ccSign (βIn 0)) *
        ((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P cCp pIn kIn (lineMomentum₂ cCp pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    beta_reduce
    rw [regulatedAmplitude₂_cCm, regulatedAmplitude₂_cCp,
      contractionAmplitude₂_Cm_cc P pIn kIn (fun i => -pOut i) kIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cCp pIn kIn (lineMomentum₂ cCp pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

end QED.TwoLoop.LimitMirror

end
