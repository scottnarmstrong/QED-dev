/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitMirrorVertex
public import QED.TwoLoop.ClassLimitVP

/-!
# Charge conjugation of the vacuum-polarization class

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), continuing
`QED/TwoLoop/LimitMirror.lean`. The representative of `VP` has the open line `0 → 1 → 2`
(external photon at `1`), the closed loop `3 → 4 → 3` and the photons `(0 3)`, `(2 4)`. Relabelling
the vertices by `(0 2)(3 4)` and reversing every line (the open line and the loop) maps it to
itself: the class is self-conjugate.

* `contractionAmplitude₂_cc_VP`: for each loop flavour `f`, the amplitude (T₇) at line momenta
  `k'` and spinor indices `(p(b), p(a))` is `-s(a) s(b)` times the amplitude at the pulled-back
  momenta and `(a, b)`: each of the five gauge vertices gives `-1`, each propagator none, and the
  loop flavour is unchanged.
* `contractionValue₂_cc_VP`, `isChargeConjPair_VP`: the same for the regulated amplitude and the
  value (T₁₀), at every parameter set.
* `hasClassLimit_VP`: the limits of `VP` exist at every on-shell pair with `q² ≥ 0`, of either
  energy sign.
* `isMirrorSymmetric_classLimit_VP`: **the `VP` limit is mirror symmetric**, given its covariance
  under the reflection `R_K`.
* `isMirrorSymmetric_headline_of_cov`: the mirror identity of the order-`e⁵` limit from the `R_K`
  covariance of the seven class limits of five gauge vertices and the mirror identity of the
  counterterm part.
-/

@[expose] public section

open Matrix Complex Filter Topology

namespace QED.TwoLoop.LimitMirror

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.TwoLoop.Routing QED.Dirac
  QED.TwoLoop.Bridge QED.OneLoop
open QED.TwoLoop.NestedVP (cV lineV photV flavV)

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### The line correspondence -/

/-- The relabelling `(0 2)(3 4)` of the vertices. -/
def permVP : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 3 4

def fermEquivVP : FermionLine cV ≃ FermionLine cV :=
  Equiv.subtypeEquiv (fvPerm (Equiv.swap 1 2)) (by decide +kernel)

def photEquivVP : PhotonLine cV ≃ PhotonLine cV :=
  Equiv.subtypeEquiv (psPerm (Equiv.swap 0 2)) (by decide +kernel)

/-- The reversed lines: the fermion lines. -/
def revVP : Line cV → Bool
  | .inl _ => true
  | .inr _ => false

theorem ends_corrVP : ∀ f : Line cV,
    Line.ends (Equiv.sumCongr fermEquivVP photEquivVP f : Line cV) =
      if revVP f then (permVP f.ends.2, permVP f.ends.1)
      else (permVP f.ends.1, permVP f.ends.2) := by
  decide +kernel

/-- **The line correspondence of `VP` with itself**: vertices `(0 2)(3 4)`, every fermion line
reversed, the photon lines kept. -/
def corrVP : LineCorr cV cV where
  vtx := permVP
  line := Equiv.sumCongr fermEquivVP photEquivVP
  rev := revVP
  ends_line := ends_corrVP

theorem line_corrVP : fermEquivVP (lineV 0) = lineV 1 ∧ fermEquivVP (lineV 1) = lineV 0 ∧
    fermEquivVP (lineV 2) = lineV 2 ∧ fermEquivVP (lineV 3) = lineV 3 ∧
    photEquivVP (photV 0) = photV 1 ∧ photEquivVP (photV 1) = photV 0 := by decide +kernel

theorem pull_corrVP (k' : Line cV → Fin 4 → ℝ) :
    corrVP.pull k' (.inl (lineV 0)) = -k' (.inl (lineV 1)) ∧
      corrVP.pull k' (.inl (lineV 1)) = -k' (.inl (lineV 0)) ∧
      corrVP.pull k' (.inl (lineV 2)) = -k' (.inl (lineV 2)) ∧
      corrVP.pull k' (.inl (lineV 3)) = -k' (.inl (lineV 3)) ∧
      corrVP.pull k' (.inr (photV 0)) = k' (.inr (photV 1)) ∧
      corrVP.pull k' (.inr (photV 1)) = k' (.inr (photV 0)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := line_corrVP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LineCorr.pull, corrVP, revVP, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, h0,
      h1, h2, h3, h4, h5, ite_true, Bool.false_eq_true, ite_false]

/-! ### The reindexing -/

/-- The charge-conjugation reindexing of the spinor indices along the reversed lines:
`(α, β) ↦ (p ∘ β ∘ π, p ∘ α ∘ π)`, `π = (0 2)(3 4)`. -/
def swapVP (x : (FV → Fin 4) × (FV → Fin 4)) : (FV → Fin 4) × (FV → Fin 4) :=
  (fun t => ccIdx (x.2 (fvPerm permVP t)), fun t => ccIdx (x.1 (fvPerm permVP t)))

theorem fvPerm_permVP_permVP (t : FV) : fvPerm permVP (fvPerm permVP t) = t := by
  rcases t with ⟨v, hv⟩
  apply Subtype.ext
  simp only [fvPerm_val]
  revert v
  decide

theorem swapVP_involutive : Function.Involutive swapVP := by
  intro x
  ext t <;> simp [swapVP, fvPerm_permVP_permVP]

/-- The relabelling of the Lorentz indices along `(0 2)(3 4)`. -/
def lorVP (lor : PS → Fin 4) : PS → Fin 4 := fun a => lor (psPerm permVP a)

theorem psPerm_permVP_permVP (a : PS) : psPerm permVP (psPerm permVP a) = a := by
  have h : permVP * permVP = 1 := by decide
  change (psPerm permVP * psPerm permVP) a = a
  rw [← psPerm_mul, h]
  rfl

theorem lorVP_involutive : Function.Involutive lorVP := by
  intro lor
  funext a
  simp [lorVP, psPerm_permVP_permVP]

theorem sum_reindexVP (F G : (FV → Fin 4) → (FV → Fin 4) → (PS → Fin 4) → ℂ) (c : ℂ)
    (h : ∀ α β lor, F (swapVP (α, β)).1 (swapVP (α, β)).2 (lorVP lor) = c * G α β lor) :
    ∑ α, ∑ β, ∑ lor, F α β lor = c * ∑ α, ∑ β, ∑ lor, G α β lor := by
  have e1 : ∀ α β, ∑ lor, F α β lor = ∑ lor, F α β (lorVP lor) := fun α β =>
    (Equiv.sum_comp (lorVP_involutive.toPerm _) _).symm
  simp only [e1]
  rw [← Fintype.sum_prod_type' (f := fun α β => ∑ lor, F α β (lorVP lor)),
    ← Fintype.sum_prod_type' (f := fun α β => ∑ lor, G α β lor),
    ← Equiv.sum_comp (swapVP_involutive.toPerm _), Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_congr _ _ fun lor => h x.1 x.2 lor

theorem fvPerm_permVP (t : FV) :
    fvPerm permVP t = ⟨permVP t.1, fun h => Wick.VertexKind.noConfusion h⟩ :=
  rfl

theorem permVP_vals : permVP 0 = 2 ∧ permVP 1 = 1 ∧ permVP 2 = 0 ∧ permVP 3 = 4 ∧
    permVP 4 = 3 := by decide

theorem lorVP_ps (lor : PS → Fin 4) :
    lorVP lor ⟨0, ⟨0, Nat.one_pos⟩⟩ = lor ⟨2, ⟨0, Nat.one_pos⟩⟩ ∧
      lorVP lor ⟨1, ⟨0, Nat.one_pos⟩⟩ = lor ⟨1, ⟨0, Nat.one_pos⟩⟩ ∧
      lorVP lor ⟨2, ⟨0, Nat.one_pos⟩⟩ = lor ⟨0, ⟨0, Nat.one_pos⟩⟩ ∧
      lorVP lor ⟨3, ⟨0, Nat.one_pos⟩⟩ = lor ⟨4, ⟨0, Nat.one_pos⟩⟩ ∧
      lorVP lor ⟨4, ⟨0, Nat.one_pos⟩⟩ = lor ⟨3, ⟨0, Nat.one_pos⟩⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem iff_indicator_VP (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, cV.1.1 (.inl i) = .inr t → (swapVP (α, β)).1 t = ccIdx (βIn i)) ∧
        (∀ t i, cV.1.1 (.inr t) = .inl i → (swapVP (α, β)).2 t = ccIdx (αOut i)) ∧
        (∀ j a, cV.1.2 (.inl j) = .inr a → lorVP lor a = μ j)) ↔
      ((∀ i t, cV.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, cV.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, cV.1.2 (.inl j) = .inr a → lor a = μ j)) := by
  simp only [NestedVP.cV_inl, NestedVP.cV_inr_inl, NestedVP.cV_photon_inl, Fin.forall_fin_one,
    forall_eq]
  simp only [ps5, lorVP_ps]
  simp only [swapVP, fvPerm_permVP, fv5, permVP_vals, ccIdx_injective.eq_iff]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

/-! ### The amplitude and the value -/

open scoped Classical in
/-- **Charge conjugation of the `VP` amplitude** (T₇), for each loop flavour. -/
theorem contractionAmplitude₂_cc_VP (P : Params) (f : Fin 3)
    (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ) (k' : Line cV → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cV (flavV f) pIn' kIn' k' (fun i => ccIdx (βIn i))
        (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionAmplitude₂ P cV (flavV f) pIn kIn (corrVP.pull k') αOut βIn μ := by
  obtain ⟨t0, t1, t2, t3⟩ := NestedVP.tail_lineV
  obtain ⟨v0, v1, v2, v3⟩ := NestedVP.val_lineV
  obtain ⟨g0, g1⟩ := NestedVP.val_photV
  obtain ⟨g0', g1'⟩ := NestedVP.head_photV
  obtain ⟨fl0, fl1, fl2, fl3, fl4⟩ := NestedVP.flavV_apply f
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pull_corrVP k'
  unfold contractionAmplitude₂
  refine sum_reindexVP _ _ _ fun α β lor => ?_
  beta_reduce
  conv_rhs => rw [mul_left_comm]
  have hiff := iff_indicator_VP α β lor αOut βIn μ
  split_ifs with h1 h2 h2
  · have ha : α ⟨2, fun h => Wick.VertexKind.noConfusion h⟩ = αOut 0 := by
      simpa [fv5] using h2.1 0 _ ((NestedVP.cV_inl 0 _).mpr rfl)
    have hb : β ⟨0, fun h => Wick.VertexKind.noConfusion h⟩ = βIn 0 := by
      simpa [fv5] using h2.2.1 _ 0 ((NestedVP.cV_inr_inl _ 0).mpr rfl)
    rw [one_mul, one_mul]
    simp only [Relabel.vertexFactor_gauges, Fin.prod_univ_five, NestedVP.prod_fermionLine,
      NestedVP.prod_photonLine, t0, t1, t2, t3, v0, v1, v2, v3, g0, g1, g0', g1', fl1, fl2, fl3,
      fl4, p0, p1, p2, p3, p4, p5]
    obtain ⟨l0, l1, l2, l3, l4⟩ := lorVP_ps lor
    simp only [ps5, l0, l1, l2, l3, l4]
    simp only [swapVP, fvPerm_permVP, fv5, permVP_vals]
    rw [gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx, gamma_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx,
      QED.OneLoop.electronPropagator_ccIdx, QED.OneLoop.electronPropagator_ccIdx, ← ha, ← hb]
    ring_nf
    simp only [ccSign_sq]
    ring
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · simp

open scoped Classical in
/-- **Charge conjugation of the `VP` regulated amplitude** (T₈): the loop flavours and their
regulator weights are unchanged. -/
theorem regulatedAmplitude₂_cc_VP (P : Params) (pIn kIn pIn' kIn' : Fin 1 → Fin 4 → ℝ)
    (k' : Line cV → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cV pIn' kIn' k' (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        regulatedAmplitude₂ P cV pIn kIn (corrVP.pull k') αOut βIn μ := by
  rw [regulatedAmplitude₂, regulatedAmplitude₂, NestedVP.sum_preserves, NestedVP.sum_preserves,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [contractionAmplitude₂_cc_VP P f pIn kIn]
  ring

theorem externalMomentum_cc_VP (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cV (fun i => -pIn i) (fun i => -pOut i) kIn (corrVP.vtx v) =
      externalMomentum cV pOut pIn kIn v := by
  change externalMomentum cV _ _ _ (permVP v) = _
  rw [NestedVP.externalMomentum_cV, NestedVP.externalMomentum_cV]
  fin_cases v <;> simp [permVP_vals]

/-- **Charge conjugation of the `VP` values** (T₁₀). -/
theorem contractionValue₂_cc_VP (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.VP.rep (fun i => -pIn i) (fun i => -pOut i) kIn
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
      -(ccSign (αOut 0) * ccSign (βIn 0)) *
        contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ := by
  have hP := rep_isOnePI .VP
  have hsum : ∑ v, externalMomentum cV pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hP.1]
    simp only [Fin.sum_univ_one, hmom, sub_self]
  obtain ⟨M, hMdet, a, h⟩ := exists_routing_change_of_ext corrVP hP.2.1 hP.2.1
    (externalMomentum_cc_VP pOut pIn kIn) hsum (loopCount_rep .VP) (loopCount_rep .VP)
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .VP),
    contractionValue₂_eq_of_loopCount P (loopCount_rep .VP)]
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cV (fun i => -pOut i) kIn
        (lineMomentum₂ cV (fun i => -pIn i) (fun i => -pOut i) kIn ℓ)
        (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ) =
      fun ℓ => -(ccSign (αOut 0) * ccSign (βIn 0)) *
        ((fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P cV pIn kIn (lineMomentum₂ cV pOut pIn kIn ℓ') αOut βIn μ)
          ((fun s => ∑ r, M s r • ℓ r) + a)) := by
    funext ℓ
    beta_reduce
    rw [regulatedAmplitude₂_cc_VP P pIn kIn (fun i => -pOut i) kIn, h]
    exact mul_left_comm _ _ _
  rw [e, jointEnergyFirstIntegral_const_mul]
  exact congrArg _
    (JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
      (fun ℓ' : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cV pIn kIn (lineMomentum₂ cV pOut pIn kIn ℓ') αOut βIn μ) M hMdet a)

theorem isChargeConjPair_VP : IsChargeConjPair .VP .VP :=
  fun P _ _ _ hmom αOut βIn μ => contractionValue₂_cc_VP P hmom αOut βIn μ

/-! ### The limit -/

/-- **The `VP` limits exist at every on-shell pair with `q² ≥ 0`**, of either energy sign, under
the Pauli–Villars conditions. -/
theorem hasClassLimit_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) : HasClassLimit .VP P p' p := fun μ a b => by
  obtain ⟨Q, -, -, h⟩ := ClassLimit.tendsto_contractionValue₂_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) (by simp) hp hp' hq
    (fun _ => a) (fun _ => b) (fun _ => μ)
  exact ⟨_, h⟩

/-- **The `VP` class limit is mirror symmetric**, given its covariance under the reflection
`R_K`. For `m, m_γ, Λ > 0`, the Pauli–Villars conditions and on-shell `p, p'` with `q² > 0`. -/
theorem isMirrorSymmetric_classLimit_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (hcov : IsReflCovariantAt (classLimit .VP P) p' p) :
    IsMirrorSymmetric p' p (classLimit .VP P p' p) := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  have hp'n : Minkowski.dot (-p') (-p') = -P.m ^ 2 := by simpa [Minkowski.dot] using hp'
  have hpn : Minkowski.dot (-p) (-p) = -P.m ^ 2 := by simpa [Minkowski.dot] using hp
  have hqn : 0 ≤ Minkowski.dot (-p - -p') (-p - -p') := by
    rw [show -p - -p' = p' - p by abel]
    exact hq.le
  refine isMirrorSymmetric_of_chargeConj (W' := classLimit .VP P (-p) (-p'))
    (fun μ => chargeConj_classLimit_of_pair isChargeConjPair_VP P
      (hasClassLimit_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp' hp hq.le)
      (hasClassLimit_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hpn hp'n hqn) μ) (fun μ => ?_)
  have h1 := hcov μ
  rwa [hRp, hRp'] at h1

/-- **The mirror identity of the order-`e⁵` limit, from the `R_K` covariance of the class limits
and the mirror identity of the counterterm part.** In the shape of the headline (HV₃): for the
parameters of `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline`, an on-shell
positive-energy pair with `q² > 0` and the limit `V`, if the limits of the seven classes
`L, X, C₊, C₋, S₊, S₋, VP` are covariant under the reflection `R_K` in `K = p + p'` and the
counterterm part is mirror symmetric, then `V` is mirror symmetric. -/
theorem isMirrorSymmetric_headline_of_cov (P₀ : Params) (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ)
    (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V)
    (hcov : ∀ c ∈ Furry.nonFurry, IsReflCovariantAt (classLimit c
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ }) p' p)
    (hct : IsMirrorSymmetric p' p (ctPart
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p)) :
    IsMirrorSymmetric p' p V :=
  isMirrorSymmetric_headline_of_parts P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ d₁ d₂ dm d₃
    p' p hp' hp hp0' hp0 hq V hV (fun c hc => hcov c (by revert c; decide))
    (isMirrorSymmetric_classLimit_VP
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂ hp' hp hq
      (hcov _ (by decide)))
    hct

end QED.TwoLoop.LimitMirror

end
