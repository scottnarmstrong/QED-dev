/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0OneCtVertex
public import QED.GradedProof.X0Sep

/-!
# (X₀): (T₉′) of a one-loop contraction amplitude with counterterm vertices

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the one-loop
contractions with a counterterm vertex and no closed fermion loop. Let every line carry the
momentum `k_l = c_l ℓ + e_l` (`oneMom`, integer `c_l`). Let `L_f` (`L_g`) be the number of
fermion (photon) lines with `c_l ≠ 0`, `n = L_f + 2 L_g` the number of loop denominators (the
regulated photon propagator has two), and `d = L_f + ∑_t vDeg t` the degree of the numerator. If
`d ≤ 4` and `4 + d < 2 n`, the amplitude (T₇) satisfies (T₉′) for `ε > 0` and any masses
(`jointEnergyFirstIntegrable_oneCt`).

## Proof
Expand the index sums. In each term the lines with `c_l = 0` are constant; a loop fermion line
is `(1/i)(M - k̸)` (affine) times its denominator, and a loop photon line is a constant times its
two denominators. The numerator is then an `AffPoly` of degree `d`
(`affPoly_vertexFactor`, `electronNumerator_affine`), and
`jointEnergyFirstIntegrable_oneLoop_affPoly'` applies with the loop denominators indexed by
`{f // c_f ≠ 0} ⊕ ({g // c_g ≠ 0} × Fin 2)`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel
open QED.TwoLoop.Bridge (propDenom electronNumerator electronPropagator_apply
  photonPropagator_eq_mul)

/-- A product of `x a` over `p a`, written over the subtype. -/
theorem prod_ite_one_eq_subtype {T : Type*} [Fintype T] (p : T → Prop) [DecidablePred p]
    (x : T → ℂ) : ∏ a, (if p a then x a else 1) = ∏ a : {a // p a}, x a := by
  rw [← Finset.prod_filter]
  exact Finset.prod_subtype _ (by simp) _

/-- A fermion propagator entry at `c ℓ + e`: a numerator factor times a denominator factor. -/
theorem oneCt_fermion_factor (M ε : ℝ) (c : ℤ) (e k : Fin 4 → ℝ) (a b : Fin 4) :
    (1 / I) * QED.OneLoop.electronPropagator M ε ((c : ℝ) • k + e) a b =
      (if c ≠ 0 then (1 / I) * electronNumerator M ((c : ℝ) • k + e) a b
        else (1 / I) * QED.OneLoop.electronPropagator M ε e a b) *
      (if c ≠ 0 then (propDenom M ε ((c : ℝ) • k + e))⁻¹ else 1) := by
  by_cases hc : c = 0
  · simp [hc]
  · simp only [ne_eq, hc, not_false_eq_true, ite_true, electronPropagator_apply]
    ring

/-- A photon propagator entry at `c ℓ + e`: a constant times two denominator factors. -/
theorem oneCt_photon_factor (mγ Λ : ℝ) {ε : ℝ} (hε : ε ≠ 0) (c : ℤ) (e k : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε ((c : ℝ) • k + e) μ ν =
      (if c ≠ 0 then (1 / I) * ((Minkowski.metric μ ν * (Λ ^ 2 - mγ ^ 2) : ℝ) : ℂ)
        else (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε e μ ν) *
      (if c ≠ 0 then (propDenom mγ ε ((c : ℝ) • k + e))⁻¹ *
        (propDenom Λ ε ((c : ℝ) • k + e))⁻¹ else 1) := by
  by_cases hc : c = 0
  · simp [hc]
  · simp only [ne_eq, hc, not_false_eq_true, ite_true, photonPropagator_eq_mul _ _ hε]
    ring

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The number of fermion lines with nonzero loop coefficient. -/
def loopFermionCount {C : Contraction nf nA κ} (c : Line C → ℤ) : ℕ :=
  (Finset.univ.filter fun f : FermionLine C => c (.inl f) ≠ 0).card

/-- The number of photon lines with nonzero loop coefficient. -/
def loopPhotonCount {C : Contraction nf nA κ} (c : Line C → ℤ) : ℕ :=
  (Finset.univ.filter fun g : PhotonLine C => c (.inr g) ≠ 0).card

/-- The numerator degree `L_f + ∑_t vDeg t`. -/
def oneDeg {C : Contraction nf nA κ} (c : Line C → ℤ) : ℕ :=
  loopFermionCount c + ∑ t, vDeg c t

/-- **(T₉′) of a one-loop contraction amplitude** (any vertex kinds, masses, `ε > 0`). -/
theorem jointEnergyFirstIntegrable_oneCt (P : Params) (hε : 0 < P.ε)
    (C : Contraction nf nA κ) (φ : Flavoring κ) (c : Line C → ℤ) (ext : Line C → Fin 4 → ℝ)
    (hd : oneDeg c ≤ 4) (hn : 4 + oneDeg c < 2 * (loopFermionCount c + 2 * loopPhotonCount c))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      z * contractionAmplitude₂ P C φ pIn kIn (oneMom c ext (ℓ 0)) αOut βIn μ := by
  classical
  simp only [contractionAmplitude₂, Finset.mul_sum]
  refine jointEnergyFirstIntegrable_sum' _ fun α _ => jointEnergyFirstIntegrable_sum' _
    fun β _ => jointEnergyFirstIntegrable_sum' _ fun lor _ => ?_
  set ind : ℂ := if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0
  set V : Fin N → (Fin 4 → ℝ) → ℂ := fun t k => Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m
    α β lor (psiMomentum₂ C pIn (oneMom c ext k)) (photonMomentum₂ C kIn (oneMom c ext k)) t
  set Fe : FermionLine C → (Fin 4 → ℝ) → ℂ := fun f k =>
    if c (.inl f) ≠ 0 then (1 / I) * electronNumerator (P.mass (φ.1 f.1))
        ((c (.inl f) : ℝ) • k + ext (.inl f)) (β f.1) (α f.tail)
      else (1 / I) * QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (ext (.inl f))
        (β f.1) (α f.tail)
  set Fg : PhotonLine C → (Fin 4 → ℝ) → ℂ := fun g _ =>
    if c (.inr g) ≠ 0 then
        (1 / I) * ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)
      else (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ext (.inr g)) (lor g.1)
        (lor g.head)
  have hV : AffPoly (∑ t, vDeg c t) fun k => ∏ t, V t k :=
    AffPoly.prod _ _ fun t _ => affPoly_vertexFactor _ _ _ _ _ _ α β lor c ext pIn kIn t
  have hFe : AffPoly (∑ f : FermionLine C, if c (.inl f) ≠ 0 then 1 else 0)
      fun k => ∏ f, Fe f k := by
    refine AffPoly.prod _ _ fun f _ => ?_
    by_cases hf : c (.inl f) = 0
    · simp only [Fe, hf, ne_eq, not_true_eq_false, ite_false]
      exact AffPoly.const _
    · simp only [Fe, hf, ne_eq, not_false_eq_true, ite_true]
      exact (AffPoly.comp_affine (electronNumerator_affine _ _ _) _ _).const_mul _
  have hFg : AffPoly (∑ _g : PhotonLine C, 0) fun k => ∏ g, Fg g k :=
    AffPoly.prod _ _ fun g _ => AffPoly.const _
  have hN := (AffPoly.const (z * ind)).mul ((hV.mul hFe).mul hFg)
  have hdeg : 0 + (∑ t, vDeg c t + ∑ f : FermionLine C, (if c (.inl f) ≠ 0 then 1 else 0) +
      ∑ _g : PhotonLine C, 0) = oneDeg c := by
    simp only [Finset.sum_boole, Finset.sum_const_zero, oneDeg, loopFermionCount]
    simp
    ring
  rw [hdeg] at hN
  have hcard : Fintype.card ({f : FermionLine C // c (.inl f) ≠ 0} ⊕
      ({g : PhotonLine C // c (.inr g) ≠ 0} × Fin 2)) =
      loopFermionCount c + 2 * loopPhotonCount c := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_subtype, Fintype.card_fin,
      loopFermionCount, loopPhotonCount]
    ring
  have h := jointEnergyFirstIntegrable_oneLoop_affPoly'
    (ι := {f : FermionLine C // c (.inl f) ≠ 0} ⊕ ({g : PhotonLine C // c (.inr g) ≠ 0} × Fin 2))
    (Sum.elim (fun f => (c (.inl f.1) : ℝ)) fun x => (c (.inr x.1.1) : ℝ))
    (fun i => match i with
      | .inl f => by simpa using f.2
      | .inr x => by simpa using x.1.2)
    (Sum.elim (fun f => ext (.inl f.1)) fun x => ext (.inr x.1.1))
    (Sum.elim (fun f => P.mass (φ.1 f.1.1)) fun x => if x.2 = 0 then P.mγ else P.Λ) hε hd
    (by rw [hcard]; exact hn) hN
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fin.prod_univ_two, Sum.elim_inl,
    Sum.elim_inr, Fin.isValue, ite_true, one_ne_zero, ite_false]
  rw [← prod_ite_one_eq_subtype (fun f : FermionLine C => c (.inl f) ≠ 0)
      (fun f => (propDenom (P.mass (φ.1 f.1)) P.ε ((c (.inl f) : ℝ) • ℓ 0 + ext (.inl f)))⁻¹),
    ← prod_ite_one_eq_subtype (fun g : PhotonLine C => c (.inr g) ≠ 0)
      (fun g => (propDenom P.mγ P.ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹ *
        (propDenom P.Λ P.ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹)]
  have hfe : ∀ f : FermionLine C, (1 / I) * QED.OneLoop.electronPropagator
      (P.mass (φ.1 f.1)) P.ε (oneMom c ext (ℓ 0) (.inl f)) (β f.1) (α f.tail) =
      Fe f (ℓ 0) * (if c (.inl f) ≠ 0 then
        (propDenom (P.mass (φ.1 f.1)) P.ε ((c (.inl f) : ℝ) • ℓ 0 + ext (.inl f)))⁻¹ else 1) :=
    fun f => oneCt_fermion_factor _ _ _ _ _ _ _
  have hfg : ∀ g : PhotonLine C, (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
      (oneMom c ext (ℓ 0) (.inr g)) (lor g.1) (lor g.head) =
      Fg g (ℓ 0) * (if c (.inr g) ≠ 0 then
        (propDenom P.mγ P.ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹ *
        (propDenom P.Λ P.ε ((c (.inr g) : ℝ) • ℓ 0 + ext (.inr g)))⁻¹ else 1) :=
    fun g => oneCt_photon_factor _ _ hε.ne' _ _ _ _ _
  simp only [hfe, hfg, Finset.prod_mul_distrib]
  ring

end QED.GradedProof.X0

end
