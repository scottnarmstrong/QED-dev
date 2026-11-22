/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEQuad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spatial integral of the quadratic self-energy building block at zero prescription

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (the closed form
of `QED.ChainProof.SetCRegDispSE.seProdLim`), for the quadratic numerator
`seQuad p = (p·ℓ) (ℓ̸)_{αβ}` with an arbitrary energy-squared coefficient `c` (the affine case is
`QED/ChainProof/SetCRegDispShellSESpat.lean`). At zero prescription, `n = i + 2` and a Feynman
parameter `y` with `Δ = y m² + (1 - y) M² + y (1 - y) P² > 0`, after the translation
`v⃗ ↦ v⃗ - y P⃗` the odd and mixed moments vanish, the diagonal second moments are a third of
the radial one, and

`∫ seTime(0) d³v = (-1)^{i+4} [c (K_{i+3} - K_{i+4}) e^{-iπ(i+5/2)} 4π c_i Δ^{-(i+1)}`
`  + K_{i+4} e^{-iπ(i+7/2)} (Q(-y P) 4π c_{i+1} Δ^{-(i+2)} + ⅓ (p⃗·γ⃗)_{αβ} 4π (c_i - c_{i+1})
  Δ^{-(i+1)})]`

(`K` = `energyConst`, `c_i` = `seRadC i`, `Q = seQuad p`).

* **`integral_seTime_seQuad_zero`**: the closed form above;
* **`integral_seSpatial_seQuad_zero`**: below threshold, `∫ seSpatial(0, 0) d³v` is the
  Feynman-parameter integral of that closed form;
* **`seProdLim_seAff_eq`**, **`seProdLim_seQuad_eq`**: the limit `seProdLim` of the photon
  product as a simplex integral of the Feynman-parameter integral of the closed forms.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop QED.Integration
open QED.ChainProof.SetCRegDispSE (seTime seSpatial seWt seEff seRadC neg_ofReal_cpow_neg
  integral_sum_sq_add_rpow_half integral_sum_sq_mul_sum_sq_add_rpow_half)
open QED.TwoLoop.VPHalfAtLimit (energyConst)

/-- The closed form of the spatial integral of the quadratic block at the Feynman parameter `y`
(`n = i + 2`, energy-squared coefficient `c`). -/
noncomputable def seQuadY (c : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) (m M : ℝ) (i : ℕ)
    (P : Fin 4 → ℝ) (y : ℝ) : ℂ :=
  (-1) ^ (i + 4) *
    (c * ((energyConst (i + 3) - energyConst (i + 4) : ℝ) : ℂ) *
        (exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ))) *
          ((4 * π * (seRadC i *
            selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 1))) : ℝ) : ℂ)) +
      ((energyConst (i + 4) : ℝ) : ℂ) * exp (π * I * (-(((i : ℝ) + 7 / 2 : ℝ) : ℂ))) *
        (seQuad p α β (-(y • P)) *
            ((4 * π * (seRadC (i + 1) *
              selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 2))) : ℝ) : ℂ) +
          (∑ k, (p k.succ : ℂ) * seSl α β k) *
            ((4 * π * ((seRadC i - seRadC (i + 1)) *
              selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 1))) / 3 : ℝ) :
                ℂ)))

/-- **The spatial integral of the closed form at zero prescription**, quadratic numerator,
`n = i + 2`. -/
theorem integral_seTime_seQuad_zero (c : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) (m M : ℝ) (i : ℕ)
    (P : Fin 4 → ℝ) {y : ℝ} (hΔ : 0 < selfEnergyFeynmanMass m M (Minkowski.dot P P) y) :
    ∫ v, seTime c (seQuad p α β) m M (i + 2) 0 P y v = seQuadY c p α β m M i P y := by
  set Δ := selfEnergyFeynmanMass m M (Minkowski.dot P P) y with hΔdef
  set a : Fin 3 → ℝ := fun k => y * P k.succ
  set s₁ : ℝ := (i : ℝ) + 5 / 2
  set s₂ : ℝ := (i : ℝ) + 7 / 2
  set K₃ : ℂ := (-1) ^ (i + 4) * ((energyConst (i + 3) - energyConst (i + 4) : ℝ) : ℂ)
  set K₄ : ℂ := (-1) ^ (i + 4) * ((energyConst (i + 4) : ℝ) : ℂ)
  set ph₁ : ℂ := exp (π * I * (-((s₁ : ℝ) : ℂ)))
  set ph₂ : ℂ := exp (π * I * (-((s₂ : ℝ) : ℂ)))
  set Q : ℂ := seQuad p α β (-(y • P))
  set L : Fin 3 → ℂ := seQL p α β y P
  have hs₁ : ((i + 2 : ℕ) : ℝ) + 1 / 2 = s₁ := by push_cast; simp only [s₁]; ring
  have hs₂ : ((i + 2 : ℕ) : ℝ) + 3 / 2 = s₂ := by push_cast; simp only [s₂]; ring
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  -- the integrand after the translation
  have hpt : ∀ v : Fin 3 → ℝ, seTime c (seQuad p α β) m M (i + 2) 0 P y (v - a) =
      K₃ * ph₁ * c * (((∑ k, v k ^ 2 + Δ) ^ (-s₁) : ℝ) : ℂ) +
        (K₄ * ph₂ * Q * (((∑ k, v k ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) +
          (∑ k, K₄ * ph₂ * L k * ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) +
            ∑ k, ∑ l, K₄ * ph₂ * ((p k.succ : ℂ) * seSl α β l) *
              ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ))) := by
    intro v
    have hX : 0 < ∑ k, v k ^ 2 + Δ := by positivity
    simp only [seTime]
    rw [massW_sub_shift, ← hΔdef, hs₁, hs₂]
    simp only [ofReal_zero, zero_mul, add_zero]
    rw [seQuad_cons_shift, neg_ofReal_cpow_neg hX s₁, neg_ofReal_cpow_neg hX s₂]
    simp only [K₃, K₄, ph₁, ph₂, Q, L]
    push_cast
    rw [show i + 2 + 2 = i + 4 by ring, show i + 2 + 1 = i + 3 by ring]
    simp only [Fin.sum_univ_three]
    ring
  have hint1 : Integrable fun v : Fin 3 → ℝ => (((∑ k, v k ^ 2 + Δ) ^ (-s₁) : ℝ) : ℂ) :=
    (integrable_sum_sq_add_rpow hΔ (by simp only [s₁]; linarith)).ofReal
  have hint2 : Integrable fun v : Fin 3 → ℝ => (((∑ k, v k ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) :=
    (integrable_sum_sq_add_rpow hΔ (by simp only [s₂]; linarith)).ofReal
  have hint3 : ∀ k : Fin 3, Integrable fun v : Fin 3 → ℝ =>
      ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) := fun k =>
    (integrable_coord_mul_rpow hΔ (by simp only [s₂]; linarith) k).ofReal
  have hint4 : ∀ k l : Fin 3, Integrable fun v : Fin 3 → ℝ =>
      ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) := fun k l =>
    (integrable_coord_mul_coord_mul_rpow hΔ (by simp only [s₂]; linarith) k l).ofReal
  have hodd : ∀ k : Fin 3,
      ∫ v : Fin 3 → ℝ, ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) = 0 := by
    intro k
    rw [integral_complex_ofReal]
    have h := integral_coord_smul_radial (fun x : ℝ => (x + Δ) ^ (-s₂)) k
    simp only [smul_eq_mul] at h
    rw [h, ofReal_zero]
  have hrad : ∫ v : Fin 3 → ℝ, (∑ j, v j ^ 2) * (∑ j, v j ^ 2 + Δ) ^ (-s₂) =
      4 * π * ((seRadC i - seRadC (i + 1)) * Δ ^ (-((i : ℝ) + 1))) :=
    integral_sum_sq_mul_sum_sq_add_rpow_half hΔ i
  have hsec : ∀ k l : Fin 3,
      ∫ v : Fin 3 → ℝ, ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) =
        if k = l then ((4 * π * ((seRadC i - seRadC (i + 1)) * Δ ^ (-((i : ℝ) + 1))) / 3 : ℝ) :
          ℂ) else 0 := by
    intro k l
    rw [integral_complex_ofReal,
      integral_coord_mul_coord_mul_rpow hΔ (by simp only [s₂]; linarith) k l, hrad]
    split_ifs <;> push_cast <;> ring
  have hF2 : ∫ v : Fin 3 → ℝ, (((∑ k, v k ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) =
      ((4 * π * (seRadC (i + 1) * Δ ^ (-((i : ℝ) + 2)))) : ℝ) := by
    rw [integral_complex_ofReal]
    have h := integral_sum_sq_add_rpow_half hΔ (i + 1)
    have e1 : (((i + 1 : ℕ) : ℝ) + 5 / 2) = s₂ := by push_cast; simp only [s₂]; ring
    have e2 : (((i + 1 : ℕ) : ℝ) + 1) = (i : ℝ) + 2 := by push_cast; ring
    rw [e1, e2] at h
    rw [h]
  have hF1 : ∫ v : Fin 3 → ℝ, (((∑ k, v k ^ 2 + Δ) ^ (-s₁) : ℝ) : ℂ) =
      ((4 * π * (seRadC i * Δ ^ (-((i : ℝ) + 1)))) : ℝ) := by
    rw [integral_complex_ofReal, integral_sum_sq_add_rpow_half hΔ i]
  have hS3 : Integrable fun v : Fin 3 → ℝ =>
      ∑ k, K₄ * ph₂ * L k * ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) :=
    integrable_finsetSum _ fun k _ => (hint3 k).const_mul _
  have hS4 : Integrable fun v : Fin 3 → ℝ =>
      ∑ k, ∑ l, K₄ * ph₂ * ((p k.succ : ℂ) * seSl α β l) *
        ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint4 k l).const_mul _
  rw [← integral_sub_right_eq_self _ a]
  simp_rw [hpt]
  rw [integral_add (hint1.const_mul _) ?h1, integral_add (hint2.const_mul _) ?h2,
    integral_add hS3 hS4,
    integral_finsetSum _ fun k _ => (hint3 k).const_mul _,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint4 k l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint4 _ l).const_mul _]
  simp only [integral_const_mul, hodd, hsec, hF1, hF2, mul_zero, Finset.sum_const_zero,
    mul_ite, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [seQuadY, K₃, K₄, ph₁, ph₂, Q, s₁, s₂, ← hΔdef, Fin.sum_univ_three]
  · push_cast
    ring
  all_goals first
    | exact hS3.add hS4
    | exact (hint2.const_mul _).add (hS3.add hS4)

/-- **The spatial integral of `seSpatial` at zero prescription**, quadratic numerator, below
threshold: `∫ seSpatial(0, 0) d³v = ∫₀¹ (i+3)(1-y)^{i+2} seQuadY(y) dy`. -/
theorem integral_seSpatial_seQuad_zero {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀)
    {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {M : ℝ} (hM : M₀ ≤ M) (c : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) (i : ℕ) :
    ∫ v, seSpatial c (seQuad p α β) m M (i + 2) 0 0 P v =
      ∫ y in Ioc (0 : ℝ) 1, seWt (i + 2) y * seQuadY c p α β m M i P y := by
  obtain ⟨C, hC0, hC⟩ := SetCRegDispSE.exists_norm_seTime_le hM₀ hc₀ hP c
    (norm_seQuad_le p α β) (n := i + 2) (by omega) (Or.inr (by omega))
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hm : Measurable fun q : (Fin 3 → ℝ) × ℝ =>
      seWt (i + 2) q.2 * seTime c (seQuad p α β) m M (i + 2) (seEff 0 0 q.2) P q.2 q.1 := by
    have h0 := SetCRegDispSE.measurable_seTime (continuous_seQuad p α β) c m (i + 2) 0 0 P
    have h1 : Measurable fun q : (Fin 3 → ℝ) × ℝ => (((M, q.1), q.2) : (ℝ × (Fin 3 → ℝ)) × ℝ) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have h2 := h0.comp h1
    simp only [Function.comp_def] at h2
    exact h2
  have hint : Integrable (fun q : (Fin 3 → ℝ) × ℝ =>
      seWt (i + 2) q.2 * seTime c (seQuad p α β) m M (i + 2) (seEff 0 0 q.2) P q.2 q.1)
      ((volume : Measure (Fin 3 → ℝ)).prod ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) := by
    refine Integrable.mono'
      ((SetCRegDispSE.integrable_one_add_norm_four.const_mul (((i + 2 : ℕ) : ℝ) + 1) |>.const_mul
        C).mul_prod (integrable_const (1 : ℝ))) hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).ae
      (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [h2] with q hq
    have hy := Ioc_subset_Icc_self hq
    rw [norm_mul, mul_one]
    calc ‖seWt (i + 2) q.2‖ *
          ‖seTime c (seQuad p α β) m M (i + 2) (seEff 0 0 q.2) P q.2 q.1‖
        ≤ (((i + 2 : ℕ) : ℝ) + 1) * (C * (1 + ‖q.1‖) ^ (-(4 : ℝ))) :=
          mul_le_mul (SetCRegDispSE.seWt_norm_le hy) (hC M hM _ q.2 hy q.1) (norm_nonneg _)
            (by positivity)
      _ = C * ((((i + 2 : ℕ) : ℝ) + 1) * (1 + ‖q.1‖) ^ (-(4 : ℝ))) := by ring
  unfold seSpatial
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hyI := Ioc_subset_Icc_self hy
  have hΔ : 0 < selfEnergyFeynmanMass m M (Minkowski.dot P P) y :=
    hc₀.trans_le ((hP y hyI).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hM hyI))
  rw [integral_const_mul]
  have e : seEff 0 0 y = 0 := by simp [seEff]
  rw [e, integral_seTime_seQuad_zero c p α β m M i P hΔ]

/-! ### The limit of the photon product in closed form -/

open QED.TwoLoop.VPHalfAtLimit (mixMass mixMass_ge) in
open QED.Integration.Feynman (simplexSet measurableSet_simplexSet) in
/-- **`seProdLim` of the affine numerator as a simplex and Feynman-parameter integral**. -/
theorem seProdLim_seAff_eq {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hMs : ∀ j, M₀ ≤ Ms j) (c b : ℂ) (α β : Fin 4) :
    SetCRegDispSE.seProdLim 0 (seAff c b α β) m Ms P =
      ((k + 1).factorial : ℂ) * ∫ u in simplexSet (k + 1),
        ∫ y in Ioc (0 : ℝ) 1, seWt (k + 1) y * seAffY c b α β m (mixMass Ms u) k P y := by
  unfold SetCRegDispSE.seProdLim
  congr 1
  exact setIntegral_congr_fun (measurableSet_simplexSet _) fun u hu =>
    integral_seSpatial_seAff_zero hM₀ hc₀ hP (mixMass_ge hM₀ hMs hu) c b α β k

open QED.TwoLoop.VPHalfAtLimit (mixMass mixMass_ge) in
open QED.Integration.Feynman (simplexSet measurableSet_simplexSet) in
/-- **`seProdLim` of the quadratic numerator as a simplex and Feynman-parameter integral**
(at least three photon-type denominators). -/
theorem seProdLim_seQuad_eq {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {j : ℕ} {Ms : Fin (j + 3) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (c : ℂ) (p : Fin 4 → ℝ)
    (α β : Fin 4) :
    SetCRegDispSE.seProdLim c (seQuad p α β) m Ms P =
      ((j + 2).factorial : ℂ) * ∫ u in simplexSet (j + 2),
        ∫ y in Ioc (0 : ℝ) 1, seWt (j + 2) y * seQuadY c p α β m (mixMass Ms u) j P y := by
  unfold SetCRegDispSE.seProdLim
  congr 1
  exact setIntegral_congr_fun (measurableSet_simplexSet _) fun u hu =>
    integral_seSpatial_seQuad_zero hM₀ hc₀ hP (mixMass_ge hM₀ hMs hu) c p α β j

end QED.ChainProof.SetCRegDisp

end
