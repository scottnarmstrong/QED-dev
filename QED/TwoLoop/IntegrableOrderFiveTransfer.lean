/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVP
public import QED.TwoLoop.RelabelCountertermValue
public import QED.TwoLoop.CountertermLimitProduct

/-!
# Transfer of (T₉′) along relabellings, to one loop, and out of products

Tools for the integrability of every term of the order-`e⁵` vertex (HV₀, obligation O2-7,
decision D-44 item 2). Throughout, (T₉′) is `QED.TwoLoop.jointEnergyFirstIntegrable`: both
stages of the joint energy-first integral (T₉) converge absolutely.

* `jointEnergyFirstIntegrable_relabel`, `jointEnergyFirstIntegrable_relabelK`: (T₉′) for the
  value integrand of a 1PI contraction passes to every relabelling of its vertices (for gauge
  vertices, and across kind sequences), under momentum conservation. The proof is that of the
  relabelling invariance of the value: the line correspondence gives an integer unimodular affine
  change of loop momenta (`LineCorr.exists_routing_change`), under which (T₉′) is invariant
  (`QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add`).
* `jointEnergyFirstIntegrable_one_sub`: at one loop, (T₉′) of `ℓ ↦ G(ℓ₀ - s)` follows from the
  integrability of both stages of the energy-first integral (D) of `G`.
* `energyFirst_of_jointEnergyFirstIntegrable_mul`: if `F(ℓ₀) H(ℓ₁)` satisfies (T₉′) at two loops,
  with `H` and the energy integrals of `H` nowhere zero, then both stages of the energy-first
  integral of `F` converge absolutely. This brings one-loop integrands into the scope of the
  two-loop criterion, through an auxiliary loop `H(k) = (k² + M² - iε)⁻³`
  (`energyFirst_of_jointEnergyFirstIntegrable_mul_aux`).
-/

public section

open MeasureTheory Complex

namespace QED.TwoLoop.IntegrableOrderFive

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

/-! ### Affine changes of loop momenta -/

/-- Transport of (T₉′) along an integer unimodular affine change of loop momenta, at any number
of loops. -/
theorem jointEnergyFirstIntegrable_of_matAct {L : ℕ} {G H : (Fin L → Fin 4 → ℝ) → ℂ}
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) (a : Fin L → Fin 4 → ℝ)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable L G) (hH : ∀ ℓ, H ℓ = G (matAct M ℓ + a)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L H := by
  have h := NestedVP.jointEnergyFirstIntegrable_comp_matrix_add L G M hM a hG
  rwa [show H = fun ℓ => G ((fun s => ∑ r, M s r • ℓ r) + a) from funext hH]

/-! ### Relabelling -/

section Relabel

variable {nf nA N : ℕ}

/-- **(T₉′) is invariant under relabelling the gauge vertices** of a 1PI contraction, under
momentum conservation. -/
theorem jointEnergyFirstIntegrable_relabel (P : Params) (π : Equiv.Perm (Fin N))
    {C : Contraction nf nA (gauges N)} (hC : IsOnePI C) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4)
    (h : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount (relabel π C)) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount (relabel π C)) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (relabel π C) pIn kIn (lineMomentum₂ (relabel π C) pOut pIn kIn ℓ)
          αOut βIn μ := by
  have hV := hC.2.1
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hC.1, hmom, sub_self]
  have hV' := (verticesConnected_relabel_iff π C).mpr hV
  have hL' := loopCount_relabel π C hV
  obtain ⟨M, hM, a, hr⟩ := (relabelCorr π C).exists_routing_change hV hV'
    (externalMomentum_relabel π C pOut pIn kIn) hsum rfl hL'
  rw [hL']
  exact jointEnergyFirstIntegrable_of_matAct M hM a h fun ℓ => by
    rw [regulatedAmplitude₂_relabel, hr]

/-- **(T₉′) is invariant under relabelling the vertices across kind sequences** (counterterm
vertices included) of a 1PI contraction, under momentum conservation. -/
theorem jointEnergyFirstIntegrable_relabelK (P : Params) {κ κ' : Fin N → Wick.VertexKind}
    (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction nf nA κ}
    (hC : IsOnePI C) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4)
    (h : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount (relabelK π hκ C)) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount (relabelK π hκ C)) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (relabelK π hκ C) pIn kIn
          (lineMomentum₂ (relabelK π hκ C) pOut pIn kIn ℓ) αOut βIn μ := by
  have hV := hC.2.1
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hC.1, hmom, sub_self]
  have hV' := (verticesConnected_relabelK_iff π hκ C).mpr hV
  have hL' := loopCount_relabelK π hκ C hV
  obtain ⟨M, hM, a, hr⟩ := (relabelCorrK π hκ C).exists_routing_change hV hV'
    (externalMomentum_relabelK π hκ C pOut pIn kIn) hsum rfl hL'
  rw [hL']
  exact jointEnergyFirstIntegrable_of_matAct M hM a h fun ℓ => by
    rw [regulatedAmplitude₂_relabelK, hr]

end Relabel

/-! ### One loop -/

/-- **(T₉′) at one loop from the one-loop stages.** If both stages of the energy-first integral
(D) of `G` converge absolutely, then `ℓ ↦ G(ℓ₀ - s)` satisfies (T₉′) with one loop momentum. -/
theorem jointEnergyFirstIntegrable_one_sub {G : (Fin 4 → ℝ) → ℂ}
    (h₁ : ∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => G (Fin.cons t v))
    (h₂ : Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v)) (s : Fin 4 → ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => G (ℓ 0 - s) := by
  have h0 : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => G (ℓ 0) := by
    refine ⟨fun v => ?_, ?_⟩
    · exact ((volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_emb
        (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
        (g := fun t : ℝ => G (Fin.cons t (v 0)))).mpr (h₁ (v 0))
    · have hin : ∀ v : Fin 1 → Fin 3 → ℝ, ∫ t : Fin 1 → ℝ, G (Fin.cons (t 0) (v 0)) =
          ∫ t : ℝ, G (Fin.cons t (v 0)) := fun v =>
        (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
          (g := fun t : ℝ => G (Fin.cons t (v 0)))
      simp_rw [hin]
      exact ((volume_preserving_funUnique (Fin 1) (Fin 3 → ℝ)).integrable_comp_emb
        (MeasurableEquiv.funUnique (Fin 1) (Fin 3 → ℝ)).measurableEmbedding
        (g := fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v))).mpr h₂
  refine jointEnergyFirstIntegrable_of_matAct 1 (by simp) (fun _ => -s) h0 fun ℓ => ?_
  simp only [matAct, Matrix.one_apply, Fin.sum_univ_one, Fin.isValue, ↓reduceIte, one_smul,
    Pi.add_apply, sub_eq_add_neg]

/-! ### Products with an auxiliary loop -/

/-- If `x ↦ f(x₀) g(x₁)` is integrable on `X²` and `g` vanishes nowhere, then `f` is
integrable. -/
theorem integrable_of_integrable_finTwo_mul {X : Type*} [MeasureSpace X]
    [SigmaFinite (volume : Measure X)] (hX : (volume : Measure X) ≠ 0) {f g : X → ℂ}
    (hg : ∀ y, g y ≠ 0) (h : Integrable fun x : Fin 2 → X => f (x 0) * g (x 1)) :
    Integrable f := by
  have hp : Integrable (fun y : X × X => f y.1 * g y.2) (volume.prod volume) :=
    ((measurePreserving_finTwoArrow (volume : Measure X)).symm _).integrable_comp_emb
      MeasurableEquiv.finTwoArrow.symm.measurableEmbedding
      (g := fun x : Fin 2 → X => f (x 0) * g (x 1)) |>.mpr h
  have : (ae (volume : Measure X)).NeBot := ae_neBot.mpr hX
  obtain ⟨y, hy⟩ := hp.prod_left_ae.exists
  refine (hy.mul_const (g y)⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_assoc, mul_inv_cancel₀ (hg y), mul_one]

/-- **One-loop integrability out of a two-loop product.** If `F(ℓ₀) H(ℓ₁)` satisfies (T₉′) at two
loops, `H` vanishes nowhere and so do its energy integrals, then both stages of the energy-first
integral (D) of `F` converge absolutely. -/
theorem energyFirst_of_jointEnergyFirstIntegrable_mul {F H : (Fin 4 → ℝ) → ℂ}
    (hH : ∀ k, H k ≠ 0) (hHt : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, H (Fin.cons t v) ≠ 0)
    (hJ : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F (ℓ 0) * H (ℓ 1)) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v) := by
  obtain ⟨h₁, h₂⟩ := hJ
  refine ⟨fun v => ?_, ?_⟩
  · exact integrable_of_integrable_finTwo_mul (f := fun t => F (Fin.cons t v))
      (g := fun t => H (Fin.cons t v)) (NeZero.ne _) (fun t => hH _) (h₁ fun _ => v)
  · have hin : ∀ w : Fin 2 → Fin 3 → ℝ,
        ∫ t : Fin 2 → ℝ, F (Fin.cons (t 0) (w 0)) * H (Fin.cons (t 1) (w 1)) =
          (∫ t : ℝ, F (Fin.cons t (w 0))) * ∫ t : ℝ, H (Fin.cons t (w 1)) := fun w =>
      CountertermLimit.integral_finTwo_mul (fun t => F (Fin.cons t (w 0)))
        (fun t => H (Fin.cons t (w 1)))
    have h₂' : Integrable fun w : Fin 2 → Fin 3 → ℝ =>
        (∫ t : ℝ, F (Fin.cons t (w 0))) * ∫ t : ℝ, H (Fin.cons t (w 1)) := by
      simp_rw [← hin]
      exact h₂
    exact integrable_of_integrable_finTwo_mul (NeZero.ne _) hHt h₂'

/-- The auxiliary loop `H(k) = (k² + M² - iε)⁻³` vanishes nowhere at `ε ≠ 0`. -/
theorem aux_ne_zero' (M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    ((Bridge.propDenom M ε k)⁻¹) ^ 3 ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero (Bridge.propDenom_ne_zero hε k))

/-- The energy integrals of the auxiliary loop vanish nowhere at `ε > 0`. -/
theorem integral_aux_ne_zero (M : ℝ) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, ((Bridge.propDenom M ε (Fin.cons t v))⁻¹) ^ 3 ≠ 0 := by
  rw [CountertermLimit.integral_aux_time M hε, CountertermLimit.auxSpatial, neg_ne_zero]
  refine mul_ne_zero (by exact_mod_cast (by positivity : (3 * Real.pi / 8 : ℝ) ≠ 0)) ?_
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  left
  intro h
  have := congrArg Complex.im h
  rw [CountertermLimit.im_neg_aux, zero_im] at this
  exact hε.ne' this

/-- **One-loop integrability out of a product with the auxiliary loop**, at `ε > 0`. -/
theorem energyFirst_of_jointEnergyFirstIntegrable_mul_aux {F : (Fin 4 → ℝ) → ℂ} (M : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hJ : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      F (ℓ 0) * ((Bridge.propDenom M ε (ℓ 1))⁻¹) ^ 3) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v) :=
  energyFirst_of_jointEnergyFirstIntegrable_mul (H := fun k => ((Bridge.propDenom M ε k)⁻¹) ^ 3)
    (aux_ne_zero' M hε.ne') (integral_aux_ne_zero M hε) hJ

end QED.TwoLoop.IntegrableOrderFive

end
