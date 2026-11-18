/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitMirror
public import QED.TwoLoop.ParametricBridgeS

/-!
# Charge conjugation of the classes `L`, `X`, `S₊`, `S₋`

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), continuing
`QED/TwoLoop/LimitMirror.lean`. Relabelling the vertices by `v ↦ 4 - v`, the reversed open line of

* `L` (external photon at `2`, internal photons `(0 4)`, `(1 3)`) is the line of `L`;
* `X` (external photon at `2`, internal photons `(0 3)`, `(1 4)`) is the line of `X`;
* `S₊` (external photon at `1`, internal photons `(0 4)`, `(2 3)`) is the line of `S₋` (external
  photon at `3`, internal photons `(0 4)`, `(1 2)`),

with all six internal lines reversed. As for `C₊ ↔ C₋`
(`QED.TwoLoop.LimitMirror.contractionValue₂_Cm_cc`), the value (T₁₀) of the image class with the
charge-conjugate external data `(-p_in, -p_out, k)` and spinor indices `(p(b), p(a))` is
`-s(a) s(b)` times the value of the original class with `(p_out, p_in, k)` and `(a, b)`, at every
parameter set (`contractionValue₂_cc_L`, `contractionValue₂_cc_X`, `contractionValue₂_cc_S`).
-/

@[expose] public section

namespace QED.TwoLoop.LimitMirror

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.TwoLoop.Routing QED.Dirac
  QED.TwoLoop.Bridge Complex

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### The ladder `L` is self-conjugate -/

section L

theorem inl_L (i : Fin 1) (t : FV) : cL.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem inr_inl_L (t : FV) (i : Fin 1) : cL.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem ph_L (j : Fin 1) (a : PS) : cL.1.2 (.inl j) = .inr a ↔ a = ps5 2 := by
  revert j a
  decide +kernel

theorem tail_lineL : (lineL 0).tail = fv5 0 ∧ (lineL 1).tail = fv5 1 ∧
    (lineL 2).tail = fv5 2 ∧ (lineL 3).tail = fv5 3 := by decide +kernel

theorem val_lineL : (lineL 0).1 = fv5 1 ∧ (lineL 1).1 = fv5 2 ∧ (lineL 2).1 = fv5 3 ∧
    (lineL 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem facts_photL : (photL 0).1 = ps5 0 ∧ (photL 0).head = ps5 4 ∧
    (photL 1).1 = ps5 1 ∧ (photL 1).head = ps5 3 := by decide +kernel

def fermEquivL : FermionLine cL ≃ FermionLine cL :=
  Equiv.subtypeEquiv (fvPerm headPermC) (by decide +kernel)

def photEquivL : PhotonLine cL ≃ PhotonLine cL :=
  Equiv.subtypeEquiv (psPerm (1)) (by decide +kernel)

theorem ends_corrL : ∀ f : Line cL,
    Line.ends (Equiv.sumCongr fermEquivL photEquivL f : Line cL) =
      (revV f.ends.2, revV f.ends.1) := by
  decide +kernel

/-- The line correspondence of the reversed open line: vertices `v ↦ 4 - v`, every line reversed. -/
def corrL : LineCorr cL cL where
  vtx := revV
  line := Equiv.sumCongr fermEquivL photEquivL
  rev := fun _ => true
  ends_line f := by
    simp only [ite_true]
    exact ends_corrL f

theorem line_corrL : fermEquivL (lineL 0) = lineL 3 ∧ fermEquivL (lineL 1) = lineL 2 ∧
    fermEquivL (lineL 2) = lineL 1 ∧ fermEquivL (lineL 3) = lineL 0 ∧
    photEquivL (photL 0) = photL 0 ∧ photEquivL (photL 1) = photL 1 := by decide +kernel

theorem pull_corrL (k' : Line cL → Fin 4 → ℝ) :
    corrL.pull k' (.inl (lineL 0)) = -k' (.inl (lineL 3)) ∧
      corrL.pull k' (.inl (lineL 1)) = -k' (.inl (lineL 2)) ∧
      corrL.pull k' (.inl (lineL 2)) = -k' (.inl (lineL 1)) ∧
      corrL.pull k' (.inl (lineL 3)) = -k' (.inl (lineL 0)) ∧
      corrL.pull k' (.inr (photL 0)) = -k' (.inr (photL 0)) ∧
      corrL.pull k' (.inr (photL 1)) = -k' (.inr (photL 1)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := line_corrL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, corrL, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, h0, h1,
      h2, h3, h4, h5, ite_true]

theorem iff_indicator_L (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, cL.1.1 (.inl i) = .inr t → (swapC (α, β)).1 t = ccIdx (βIn i)) ∧
        (∀ t i, cL.1.1 (.inr t) = .inl i → (swapC (α, β)).2 t = ccIdx (αOut i)) ∧
        (∀ j a, cL.1.2 (.inl j) = .inr a → lorC lor a = μ j)) ↔
      ((∀ i t, cL.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, cL.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, cL.1.2 (.inl j) = .inr a → lor a = μ j)) := by
  simp only [inl_L, inr_inl_L, ph_L, Fin.forall_fin_one,
    forall_eq]
  simp only [ps5, lorC_ps]
  simp only [swapC, fvPerm_revV, fv5, rev5, ccIdx_injective.eq_iff]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

open scoped Classical in
/-- **Charge conjugation of the amplitude** (T₇) along the reversed open line. -/
theorem contractionAmplitude₂_cc_L (P : Params) (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ)
    (k' : Line cL → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cL zeroFlavoring pIn' kIn' k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionAmplitude₂ P cL zeroFlavoring pIn kIn (corrL.pull k') αOut βIn μ := by
  obtain ⟨tP0, tP1, tP2, tP3⟩ := tail_lineL
  obtain ⟨vP0, vP1, vP2, vP3⟩ := val_lineL
  obtain ⟨gP0, gP0', gP1, gP1'⟩ := facts_photL
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pull_corrL k'
  unfold contractionAmplitude₂
  refine sum_reindexC _ _ _ fun α β lor => ?_
  beta_reduce
  conv_rhs => rw [mul_left_comm]
  have hiff := iff_indicator_L α β lor αOut βIn μ
  split_ifs with h1 h2 h2
  · have ha : α ⟨4, fun h => Wick.VertexKind.noConfusion h⟩ = αOut 0 := by
      simpa [fv5] using h2.1 0 _ ((inl_L 0 _).mpr rfl)
    have hb : β ⟨0, fun h => Wick.VertexKind.noConfusion h⟩ = βIn 0 := by
      simpa [fv5] using h2.2.1 _ 0 ((inr_inl_L _ 0).mpr rfl)
    rw [one_mul, one_mul]
    simp only [Relabel.vertexFactor_gauges, Fin.prod_univ_five,
      prod_fermionLine_L, prod_photonLine_L,
      tP0, tP1, tP2, tP3, vP0, vP1, vP2, vP3, gP0, gP0', gP1, gP1',
      p0, p1, p2, p3, p4, p5]
    obtain ⟨l0, l1, l2, l3, l4⟩ := lorC_ps lor
    simp only [ps5, l0, l1, l2, l3, l4]
    simp only [swapC, fvPerm_revV, fv5, rev5, zeroFlavoring]
    rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photL 0))),
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photL 1))), ← ha, ← hb]
    ring_nf
    simp only [ccSign_sq]
    ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · simp

theorem externalMomentum_cc_L (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cL (fun i => -pIn i) (fun i => -pOut i) kIn (corrL.vtx v) =
      externalMomentum cL pOut pIn kIn v := by
  change externalMomentum cL _ _ _ (Fin.rev v) = _
  rw [externalMomentum_cL, externalMomentum_cL]
  fin_cases v <;> simp

open scoped Classical in
/-- **Charge conjugation of the values** (T₁₀) along the reversed open line. -/
theorem contractionValue₂_cc_L (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.L.rep (fun i => -pIn i) (fun i => -pOut i) kIn
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionValue₂ P Class5.L.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .L
  have hM := rep_isOnePI .L
  have hsum : ∑ v, externalMomentum cL pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := exists_routing_change_of_ext corrL hP.2.1 hM.2.1
    (externalMomentum_cc_L pOut pIn kIn) hsum (loopCount_rep .L) (loopCount_rep .L)
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .L),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .L)]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cL (fun i => -pOut i) kIn
        (lineMomentum₂ cL (fun i => -pIn i) (fun i => -pOut i) kIn ℓ)
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => -(ccSign (αOut 0) * ccSign (βIn 0)) *
        ((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P cL pIn kIn (lineMomentum₂ cL pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    beta_reduce
    rw [regulatedAmplitude₂_cL, regulatedAmplitude₂_cL,
      contractionAmplitude₂_cc_L P pIn kIn (fun i => -pOut i) kIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cL pIn kIn (lineMomentum₂ cL pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

end L

/-! ### The crossed ladder `X` is self-conjugate -/

section X

theorem inl_X (i : Fin 1) (t : FV) : cX.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem inr_inl_X (t : FV) (i : Fin 1) : cX.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem ph_X (j : Fin 1) (a : PS) : cX.1.2 (.inl j) = .inr a ↔ a = ps5 2 := by
  revert j a
  decide +kernel

theorem tail_lineX : (lineX 0).tail = fv5 0 ∧ (lineX 1).tail = fv5 1 ∧
    (lineX 2).tail = fv5 2 ∧ (lineX 3).tail = fv5 3 := by decide +kernel

theorem val_lineX : (lineX 0).1 = fv5 1 ∧ (lineX 1).1 = fv5 2 ∧ (lineX 2).1 = fv5 3 ∧
    (lineX 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem facts_photX : (photX 0).1 = ps5 0 ∧ (photX 0).head = ps5 3 ∧
    (photX 1).1 = ps5 1 ∧ (photX 1).head = ps5 4 := by decide +kernel

def fermEquivX : FermionLine cX ≃ FermionLine cX :=
  Equiv.subtypeEquiv (fvPerm headPermC) (by decide +kernel)

def photEquivX : PhotonLine cX ≃ PhotonLine cX :=
  Equiv.subtypeEquiv (psPerm (Equiv.swap 0 1)) (by decide +kernel)

theorem ends_corrX : ∀ f : Line cX,
    Line.ends (Equiv.sumCongr fermEquivX photEquivX f : Line cX) =
      (revV f.ends.2, revV f.ends.1) := by
  decide +kernel

/-- The line correspondence of the reversed open line: vertices `v ↦ 4 - v`, every line reversed. -/
def corrX : LineCorr cX cX where
  vtx := revV
  line := Equiv.sumCongr fermEquivX photEquivX
  rev := fun _ => true
  ends_line f := by
    simp only [ite_true]
    exact ends_corrX f

theorem line_corrX : fermEquivX (lineX 0) = lineX 3 ∧ fermEquivX (lineX 1) = lineX 2 ∧
    fermEquivX (lineX 2) = lineX 1 ∧ fermEquivX (lineX 3) = lineX 0 ∧
    photEquivX (photX 0) = photX 1 ∧ photEquivX (photX 1) = photX 0 := by decide +kernel

theorem pull_corrX (k' : Line cX → Fin 4 → ℝ) :
    corrX.pull k' (.inl (lineX 0)) = -k' (.inl (lineX 3)) ∧
      corrX.pull k' (.inl (lineX 1)) = -k' (.inl (lineX 2)) ∧
      corrX.pull k' (.inl (lineX 2)) = -k' (.inl (lineX 1)) ∧
      corrX.pull k' (.inl (lineX 3)) = -k' (.inl (lineX 0)) ∧
      corrX.pull k' (.inr (photX 0)) = -k' (.inr (photX 1)) ∧
      corrX.pull k' (.inr (photX 1)) = -k' (.inr (photX 0)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := line_corrX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, corrX, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, h0, h1,
      h2, h3, h4, h5, ite_true]

theorem iff_indicator_X (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, cX.1.1 (.inl i) = .inr t → (swapC (α, β)).1 t = ccIdx (βIn i)) ∧
        (∀ t i, cX.1.1 (.inr t) = .inl i → (swapC (α, β)).2 t = ccIdx (αOut i)) ∧
        (∀ j a, cX.1.2 (.inl j) = .inr a → lorC lor a = μ j)) ↔
      ((∀ i t, cX.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, cX.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, cX.1.2 (.inl j) = .inr a → lor a = μ j)) := by
  simp only [inl_X, inr_inl_X, ph_X, Fin.forall_fin_one,
    forall_eq]
  simp only [ps5, lorC_ps]
  simp only [swapC, fvPerm_revV, fv5, rev5, ccIdx_injective.eq_iff]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

open scoped Classical in
/-- **Charge conjugation of the amplitude** (T₇) along the reversed open line. -/
theorem contractionAmplitude₂_cc_X (P : Params) (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ)
    (k' : Line cX → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cX zeroFlavoring pIn' kIn' k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionAmplitude₂ P cX zeroFlavoring pIn kIn (corrX.pull k') αOut βIn μ := by
  obtain ⟨tP0, tP1, tP2, tP3⟩ := tail_lineX
  obtain ⟨vP0, vP1, vP2, vP3⟩ := val_lineX
  obtain ⟨gP0, gP0', gP1, gP1'⟩ := facts_photX
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pull_corrX k'
  unfold contractionAmplitude₂
  refine sum_reindexC _ _ _ fun α β lor => ?_
  beta_reduce
  conv_rhs => rw [mul_left_comm]
  have hiff := iff_indicator_X α β lor αOut βIn μ
  split_ifs with h1 h2 h2
  · have ha : α ⟨4, fun h => Wick.VertexKind.noConfusion h⟩ = αOut 0 := by
      simpa [fv5] using h2.1 0 _ ((inl_X 0 _).mpr rfl)
    have hb : β ⟨0, fun h => Wick.VertexKind.noConfusion h⟩ = βIn 0 := by
      simpa [fv5] using h2.2.1 _ 0 ((inr_inl_X _ 0).mpr rfl)
    rw [one_mul, one_mul]
    simp only [Relabel.vertexFactor_gauges, Fin.prod_univ_five,
      prod_fermionLine_X, prod_photonLine_X,
      tP0, tP1, tP2, tP3, vP0, vP1, vP2, vP3, gP0, gP0', gP1, gP1',
      p0, p1, p2, p3, p4, p5]
    obtain ⟨l0, l1, l2, l3, l4⟩ := lorC_ps lor
    simp only [ps5, l0, l1, l2, l3, l4]
    simp only [swapC, fvPerm_revV, fv5, rev5, zeroFlavoring]
    rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photX 0))),
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photX 1))), ← ha, ← hb]
    ring_nf
    simp only [ccSign_sq]
    ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · simp

theorem externalMomentum_cc_X (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cX (fun i => -pIn i) (fun i => -pOut i) kIn (corrX.vtx v) =
      externalMomentum cX pOut pIn kIn v := by
  change externalMomentum cX _ _ _ (Fin.rev v) = _
  rw [externalMomentum_cX, externalMomentum_cX]
  fin_cases v <;> simp

open scoped Classical in
/-- **Charge conjugation of the values** (T₁₀) along the reversed open line. -/
theorem contractionValue₂_cc_X (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.X.rep (fun i => -pIn i) (fun i => -pOut i) kIn
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionValue₂ P Class5.X.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .X
  have hM := rep_isOnePI .X
  have hsum : ∑ v, externalMomentum cX pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := exists_routing_change_of_ext corrX hP.2.1 hM.2.1
    (externalMomentum_cc_X pOut pIn kIn) hsum (loopCount_rep .X) (loopCount_rep .X)
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .X),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .X)]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cX (fun i => -pOut i) kIn
        (lineMomentum₂ cX (fun i => -pIn i) (fun i => -pOut i) kIn ℓ)
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => -(ccSign (αOut 0) * ccSign (βIn 0)) *
        ((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P cX pIn kIn (lineMomentum₂ cX pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    beta_reduce
    rw [regulatedAmplitude₂_cX, regulatedAmplitude₂_cX,
      contractionAmplitude₂_cc_X P pIn kIn (fun i => -pOut i) kIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cX pIn kIn (lineMomentum₂ cX pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

end X

/-! ### `S₊ ↔ S₋` -/

section S

theorem inl_S (i : Fin 1) (t : FV) : cSp.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem inr_inl_S (t : FV) (i : Fin 1) : cSp.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem ph_S (j : Fin 1) (a : PS) : cSp.1.2 (.inl j) = .inr a ↔ a = ps5 1 := by
  revert j a
  decide +kernel

theorem tail_lineSp : (lineSp 0).tail = fv5 0 ∧ (lineSp 1).tail = fv5 1 ∧
    (lineSp 2).tail = fv5 2 ∧ (lineSp 3).tail = fv5 3 := by decide +kernel

theorem val_lineSp : (lineSp 0).1 = fv5 1 ∧ (lineSp 1).1 = fv5 2 ∧ (lineSp 2).1 = fv5 3 ∧
    (lineSp 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem facts_photSp : (photSp 0).1 = ps5 0 ∧ (photSp 0).head = ps5 4 ∧
    (photSp 1).1 = ps5 2 ∧ (photSp 1).head = ps5 3 := by decide +kernel

theorem inl_S' (i : Fin 1) (t : FV) : cSm.1.1 (.inl i) = .inr t ↔ t = fv5 4 := by
  revert i t
  decide +kernel

theorem inr_inl_S' (t : FV) (i : Fin 1) : cSm.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  revert t i
  decide +kernel

theorem ph_S' (j : Fin 1) (a : PS) : cSm.1.2 (.inl j) = .inr a ↔ a = ps5 3 := by
  revert j a
  decide +kernel

theorem tail_lineSm : (lineSm 0).tail = fv5 0 ∧ (lineSm 1).tail = fv5 1 ∧
    (lineSm 2).tail = fv5 2 ∧ (lineSm 3).tail = fv5 3 := by decide +kernel

theorem val_lineSm : (lineSm 0).1 = fv5 1 ∧ (lineSm 1).1 = fv5 2 ∧ (lineSm 2).1 = fv5 3 ∧
    (lineSm 3).1 = fv5 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem facts_photSm : (photSm 0).1 = ps5 0 ∧ (photSm 0).head = ps5 4 ∧
    (photSm 1).1 = ps5 1 ∧ (photSm 1).head = ps5 2 := by decide +kernel

def fermEquivS : FermionLine cSp ≃ FermionLine cSm :=
  Equiv.subtypeEquiv (fvPerm headPermC) (by decide +kernel)

def photEquivS : PhotonLine cSp ≃ PhotonLine cSm :=
  Equiv.subtypeEquiv (psPerm (Equiv.swap 1 2)) (by decide +kernel)

theorem ends_corrS : ∀ f : Line cSp,
    Line.ends (Equiv.sumCongr fermEquivS photEquivS f : Line cSm) =
      (revV f.ends.2, revV f.ends.1) := by
  decide +kernel

/-- The line correspondence of the reversed open line: vertices `v ↦ 4 - v`, every line reversed. -/
def corrS : LineCorr cSp cSm where
  vtx := revV
  line := Equiv.sumCongr fermEquivS photEquivS
  rev := fun _ => true
  ends_line f := by
    simp only [ite_true]
    exact ends_corrS f

theorem line_corrS : fermEquivS (lineSp 0) = lineSm 3 ∧ fermEquivS (lineSp 1) = lineSm 2 ∧
    fermEquivS (lineSp 2) = lineSm 1 ∧ fermEquivS (lineSp 3) = lineSm 0 ∧
    photEquivS (photSp 0) = photSm 0 ∧ photEquivS (photSp 1) = photSm 1 := by decide +kernel

theorem pull_corrS (k' : Line cSm → Fin 4 → ℝ) :
    corrS.pull k' (.inl (lineSp 0)) = -k' (.inl (lineSm 3)) ∧
      corrS.pull k' (.inl (lineSp 1)) = -k' (.inl (lineSm 2)) ∧
      corrS.pull k' (.inl (lineSp 2)) = -k' (.inl (lineSm 1)) ∧
      corrS.pull k' (.inl (lineSp 3)) = -k' (.inl (lineSm 0)) ∧
      corrS.pull k' (.inr (photSp 0)) = -k' (.inr (photSm 0)) ∧
      corrS.pull k' (.inr (photSp 1)) = -k' (.inr (photSm 1)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := line_corrS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, corrS, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, h0, h1,
      h2, h3, h4, h5, ite_true]

theorem iff_indicator_S (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, cSm.1.1 (.inl i) = .inr t → (swapC (α, β)).1 t = ccIdx (βIn i)) ∧
        (∀ t i, cSm.1.1 (.inr t) = .inl i → (swapC (α, β)).2 t = ccIdx (αOut i)) ∧
        (∀ j a, cSm.1.2 (.inl j) = .inr a → lorC lor a = μ j)) ↔
      ((∀ i t, cSp.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, cSp.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, cSp.1.2 (.inl j) = .inr a → lor a = μ j)) := by
  simp only [inl_S, inl_S', inr_inl_S, inr_inl_S', ph_S, ph_S', Fin.forall_fin_one,
    forall_eq]
  simp only [ps5, lorC_ps]
  simp only [swapC, fvPerm_revV, fv5, rev5, ccIdx_injective.eq_iff]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

open scoped Classical in
/-- **Charge conjugation of the amplitude** (T₇) along the reversed open line. -/
theorem contractionAmplitude₂_cc_S (P : Params) (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ)
    (k' : Line cSm → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cSm zeroFlavoring pIn' kIn' k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionAmplitude₂ P cSp zeroFlavoring pIn kIn (corrS.pull k') αOut βIn μ := by
  obtain ⟨tP0, tP1, tP2, tP3⟩ := tail_lineSp
  obtain ⟨vP0, vP1, vP2, vP3⟩ := val_lineSp
  obtain ⟨gP0, gP0', gP1, gP1'⟩ := facts_photSp
  obtain ⟨tM0, tM1, tM2, tM3⟩ := tail_lineSm
  obtain ⟨vM0, vM1, vM2, vM3⟩ := val_lineSm
  obtain ⟨gM0, gM0', gM1, gM1'⟩ := facts_photSm
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pull_corrS k'
  unfold contractionAmplitude₂
  refine sum_reindexC _ _ _ fun α β lor => ?_
  beta_reduce
  conv_rhs => rw [mul_left_comm]
  have hiff := iff_indicator_S α β lor αOut βIn μ
  split_ifs with h1 h2 h2
  · have ha : α ⟨4, fun h => Wick.VertexKind.noConfusion h⟩ = αOut 0 := by
      simpa [fv5] using h2.1 0 _ ((inl_S 0 _).mpr rfl)
    have hb : β ⟨0, fun h => Wick.VertexKind.noConfusion h⟩ = βIn 0 := by
      simpa [fv5] using h2.2.1 _ 0 ((inr_inl_S _ 0).mpr rfl)
    rw [one_mul, one_mul]
    simp only [Relabel.vertexFactor_gauges, Fin.prod_univ_five,
      prod_fermionLine_Sp, prod_fermionLine_Sm, prod_photonLine_Sp,
      prod_photonLine_Sm,
      tP0, tP1, tP2, tP3, vP0, vP1, vP2, vP3, gP0, gP0', gP1, gP1',
      tM0, tM1, tM2, tM3, vM0, vM1, vM2, vM3, gM0, gM0', gM1, gM1',
      p0, p1, p2, p3, p4, p5]
    obtain ⟨l0, l1, l2, l3, l4⟩ := lorC_ps lor
    simp only [ps5, l0, l1, l2, l3, l4]
    simp only [swapC, fvPerm_revV, fv5, rev5, zeroFlavoring]
    rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photSm 0))),
      ← photonPropagator_neg_swap _ _ _ (k' (.inr (photSm 1))), ← ha, ← hb]
    ring_nf
    simp only [ccSign_sq]
    ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · simp

theorem externalMomentum_cc_S (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cSm (fun i => -pIn i) (fun i => -pOut i) kIn (corrS.vtx v) =
      externalMomentum cSp pOut pIn kIn v := by
  change externalMomentum cSm _ _ _ (Fin.rev v) = _
  rw [externalMomentum_cSm, externalMomentum_cSp]
  fin_cases v <;> simp

open scoped Classical in
/-- **Charge conjugation of the values** (T₁₀) along the reversed open line. -/
theorem contractionValue₂_cc_S (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Sm.rep (fun i => -pIn i) (fun i => -pOut i) kIn
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionValue₂ P Class5.Sp.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .Sp
  have hM := rep_isOnePI .Sm
  have hsum : ∑ v, externalMomentum cSp pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := exists_routing_change_of_ext corrS hP.2.1 hM.2.1
    (externalMomentum_cc_S pOut pIn kIn) hsum (loopCount_rep .Sp) (loopCount_rep .Sm)
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Sm),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .Sp)]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cSm (fun i => -pOut i) kIn
        (lineMomentum₂ cSm (fun i => -pIn i) (fun i => -pOut i) kIn ℓ)
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => -(ccSign (αOut 0) * ccSign (βIn 0)) *
        ((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P cSp pIn kIn (lineMomentum₂ cSp pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    beta_reduce
    rw [regulatedAmplitude₂_cSm, regulatedAmplitude₂_cSp,
      contractionAmplitude₂_cc_S P pIn kIn (fun i => -pOut i) kIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cSp pIn kIn (lineMomentum₂ cSp pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

end S

end QED.TwoLoop.LimitMirror

end
