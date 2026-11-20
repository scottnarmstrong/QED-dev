/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecAff

/-!
# (R-Π₄) step L9, D3a: from the scaling at fixed photon regulators to `DecScaleT₀`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3a. Dilating all masses by `λ` (the photon regulators and `s` with them) leaves the class
sum unchanged (`DecDilQ`, dimensional analysis of the finite-regulator integrals; a named
hypothesis here). Since the photon-regulator limit is a joint limit (L8), the dilated regulator
pair `(λ⁻¹Λ⁻¹, λ⁻¹Λ)` has the same limit, so:

* `dec_asmPolLim_dil`: `asmPolLim (decDil λ Φ) (λ² s) = asmPolLim Φ s`, given `DecFaceGen`;
* `dec_scaleT₀`: **`DecDilQ e → DecFaceGen e → DecScaleT₀ e`**.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-- The flavour set with all masses multiplied by `λ`. -/
def decDil {F : Type} (l : ℝ) (Φ : Lepton.Flavors F) : Lepton.Flavors F :=
  ⟨fun f => l * Φ.mass f, Φ.coeff, Φ.openLine⟩

/-- **(D3a) dimensional analysis at fixed photon regulators**: dilating the masses, the photon
regulators and `s` leaves the class sum unchanged (for PV-closed flavour sets in the region). -/
def DecDilQ (e : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ),
    0 < m₀ → (∀ g, m₀ ≤ Φ.mass g) → (∀ f, rep (rep f) = rep f) →
    (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) →
    (∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) →
    ∀ l a b s : ℝ, 0 < l → 0 < a → 0 < b → -(4 * m₀ ^ 2) < s →
      qPair (decDil l Φ) rep e (l * a) (l * b) (l ^ 2 * s) = qPair Φ rep e a b s

variable {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F} {rep : F → F} {m₀ : ℝ}

/-- **D3a in the photon-regulator limit.** -/
theorem dec_asmPolLim_dil (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (P : Params) (he : P.e ≠ 0) (hQ : DecDilQ P.e) (hF : DecFaceGen P.e) {l s : ℝ} (hl : 0 < l)
    (hs : -(4 * m₀ ^ 2) < s) :
    asmPolLim (decDil l Φ) rep P.e (l ^ 2 * s) = asmPolLim Φ rep P.e s := by
  have h00 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  -- the dilated flavour set
  have hm₀' : 0 < l * m₀ := mul_pos hl hm₀
  have hmass' : ∀ g, l * m₀ ≤ (decDil l Φ).mass g := fun g =>
    mul_le_mul_of_nonneg_left (hmass g) hl.le
  have hPV₂' : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b),
      (decDil l Φ).coeff f * (decDil l Φ).mass f ^ 2 = 0 := by
    intro b hb
    simp only [decDil, mul_pow]
    rw [show (∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * (l ^ 2 * Φ.mass f ^ 2))
      = l ^ 2 * ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun f _ => by ring, hPV₂ b hb, mul_zero]
  have hs' : -(4 * (l * m₀) ^ 2) < l ^ 2 * s := by nlinarith [sq_nonneg l, pow_pos hl 2]
  have t := dec_tendsto_asmPolLim (Φ := decDil l Φ) (rep := rep) hm₀' hmass' hrep P he hPV₁
    hPV₂' hF hs'
  -- the original flavour set along the dilated regulator pair
  obtain ⟨C, hC⟩ := asm_exists_norm_sub_polLim_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he
    (S₀ := s) (S := s) hs fun s' h₀ h₁ =>
      hF F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ _ s' (by positivity)
        ((lt_min hs h00).trans_le h₀) (h₁.trans_lt (asm_max_lt_two_mul_sq s))
  have hrate : Tendsto (fun Λ : ℝ => C * (Real.sqrt (l⁻¹ * Λ⁻¹) + (l⁻¹ * Λ)⁻¹)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun Λ : ℝ => Real.sqrt (l⁻¹ * Λ⁻¹)) atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.const_mul l⁻¹
      rw [mul_zero] at h
      have := (Real.continuous_sqrt.tendsto 0).comp h
      rwa [Real.sqrt_zero] at this
    have h2 : Tendsto (fun Λ : ℝ => (l⁻¹ * Λ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (inv_pos.2 hl))
    have := (h1.add h2).const_mul C
    rwa [add_zero, mul_zero] at this
  have t' : Tendsto (fun Λ : ℝ => qPair (decDil l Φ) rep P.e Λ⁻¹ Λ (l ^ 2 * s) -
      qPair (decDil l Φ) rep P.e Λ⁻¹ Λ (l ^ 2 * 0)) atTop (𝓝 (asmPolLim Φ rep P.e s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrate
    filter_upwards [eventually_ge_atTop l, eventually_ge_atTop l⁻¹, eventually_gt_atTop 0]
      with Λ hΛl hΛl' hΛ
    have ea : l * (l⁻¹ * Λ⁻¹) = Λ⁻¹ := by field_simp
    have eb : l * (l⁻¹ * Λ) = Λ := by field_simp
    have ha : 0 < l⁻¹ * Λ⁻¹ := by positivity
    have hb : 0 < l⁻¹ * Λ := by positivity
    have q1 := hQ F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ l _ _ s hl ha hb hs
    have q0 := hQ F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ l _ _ 0 hl ha hb h00
    rw [ea, eb] at q1 q0
    rw [q1, q0]
    refine hC s le_rfl le_rfl _ _ ha ?_ ?_
    · rw [← mul_inv]
      refine inv_le_one_of_one_le₀ ?_
      have := mul_le_mul_of_nonneg_left hΛl' hl.le
      rwa [mul_inv_cancel₀ hl.ne'] at this
    · rw [← div_eq_inv_mul, le_div_iff₀ hl]; linarith
  rw [mul_zero] at t'
  exact tendsto_nhds_unique t t'

/-- **`DecScaleT₀` from the dimensional analysis at fixed photon regulators.** -/
theorem dec_scaleT₀ (P : Params) (he : P.e ≠ 0) (hQ : DecDilQ P.e) (hF : DecFaceGen P.e) :
    DecScaleT₀ P.e := by
  intro μ x s hμ hx hs
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hy : 1 ≤ x / μ ^ 2 := by rwa [le_div_iff₀ hμ2, one_mul]
  have hsq : μ * Real.sqrt (x / μ ^ 2) = Real.sqrt x := by
    rw [Real.sqrt_div' _ hμ2.le, Real.sqrt_sq hμ.le]
    field_simp
  have hmeas : DecSameMeas (decCfg μ x) (fun _ => 0) (decDil μ (decCfg 1 (x / μ ^ 2)))
      (fun _ => 0) := by
    intro g
    simp only [decCfg, decDil, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_pow, div_one, mul_one, hsq,
      mul_comm μ (Real.sqrt 2)]
  have hm : ∀ g, 1 ≤ (decCfg 1 (x / μ ^ 2)).mass g := fun g =>
    dec_cfg_mass_ge le_rfl one_pos (by rwa [one_pow]) g
  have hpv := dec_cfg_pv (μ := 1) (x := x / μ ^ 2) one_ne_zero (by positivity)
  have hs' : -(4 * 1 ^ 2) < s / μ ^ 2 := by
    rw [one_pow, mul_one, lt_div_iff₀ hμ2]; linarith
  have key := dec_asmPolLim_dil (rep := fun _ => (0 : Fin 3)) one_pos hm (fun _ => rfl) hpv.1
    hpv.2 P he hQ hF hμ hs'
  rw [show μ ^ 2 * (s / μ ^ 2) = s by field_simp] at key
  simp only [decT₀]
  rw [dec_asmPolLim_congr hmeas, key]

end QED.GradedProof.RPi4

end
