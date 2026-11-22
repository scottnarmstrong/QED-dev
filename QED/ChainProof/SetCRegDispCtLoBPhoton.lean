/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBEngine
public import QED.TwoLoop.VPHalfAtLimitPhoton
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The doubled vertex with a product of photon denominators and their own prescriptions

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c). The analogue of
`QED/TwoLoop/VPHalfAtLimitPhoton.lean` for the vertex with the electron denominator of the open
line `d` doubled (`QED/ChainProof/SetCRegDispCtLoBEngine.lean`):

`F(ℓ) = N(ℓ) / (D_m(p' + ℓ; ε) D_m(p + ℓ; ε) D_m(ℓ_d; ε) ∏_j D_{M_j}(ℓ; ε_j))`
(`dblProdIntegrand`), `k + 2 ≥ 2` photon-type denominators with masses `M_j ≥ M₀ > 0` and
prescriptions `ε_j > 0`.

* **Photon superposition** (`dblProdIntegrand_eq_integral`): the photon product is
  `(k+1)! ∫_Δ D_{M(u)}(ℓ; ε(u))^{-(k+2)} du`
  (`QED.TwoLoop.VPHalfAtLimit.mixMass`, `QED.TwoLoop.VPHalfAtLimit.mixEps`).
* **Exchange with the energy-first integral** (`energyFirstIntegral_dblProdIntegrand_eq`).
* **The limit** (`tendsto_energyFirstIntegral_dblProdIntegrand`): when `ε → 0⁺` and every
  `ε_j → 0⁺`, the energy-first integral tends to `dblProdLimit`, independent of the
  prescriptions.
* **Continuity in the masses** (`tendsto_dblProdLimit`), on `M_j ≥ M₀ > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit

/-! ### Definitions -/

/-- The doubled vertex with a product of `k + 2` photon denominators. -/
noncomputable def dblProdIntegrand (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * ((denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom m ε (dblMom d p' p ℓ))⁻¹ *
    ∏ j, (denom (Ms j) (es j) ℓ)⁻¹)

/-- The limit: `(k+1)! ∫_Δ ∫ spatialW (dblWt d k)(0, 0, M(u))` (order `k + 2`). -/
noncomputable def dblProdLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ) : ℂ :=
  ((k + 1).factorial : ℂ) * ∫ u in simplexSet (k + 1),
    ∫ v, spatialW (dblWt d (k + 1)) α N m (mixMass Ms u) (k + 2) 0 0 p' p v

/-! ### Photon superposition -/

theorem dblProdIntegrand_eq_integral (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) (ε : ℝ) (d : Fin 2)
    (p' p ℓ : Fin 4 → ℝ) :
    dblProdIntegrand N m Ms es ε d p' p ℓ = ((k + 1).factorial : ℂ) *
      ∫ u in simplexSet (k + 1),
        dblIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) d p' p ℓ := by
  have ha : ∀ j, (denom (Ms j) (es j) ℓ).im < 0 := fun j => by rw [denom_im]; linarith [hes j]
  have hpt : ∀ u ∈ simplexSet (k + 1),
      dblIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) d p' p ℓ =
        N ℓ * (denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom m ε (dblMom d p' p ℓ))⁻¹ *
          (simplexComb (fun j => denom (Ms j) (es j) ℓ) u ^ (k + 1 + 1))⁻¹ := by
    intro u hu
    rw [dblIntegrand, simplexComb_denom Ms es ℓ hu, mul_inv (denom m ε (p' + ℓ) *
      denom m ε (p + ℓ) * denom m ε (dblMom d p' p ℓ))]
    ring
  rw [dblProdIntegrand, prod_inv_eq_factorial_mul_integral_simplex ha,
    setIntegral_congr_fun (measurableSet_simplexSet _) hpt, integral_const_mul]
  ring

/-! ### Exchange with the energy-first integral -/

theorem continuous_dblMom (d : Fin 2) (p' p : Fin 4 → ℝ) : Continuous (dblMom d p' p) := by
  unfold dblMom
  split_ifs <;> fun_prop

theorem measurable_dblIntegrand_mix {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m : ℝ)
    {k : ℕ} (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      dblIntegrand N m (mixMass Ms q.1.2) (k + 1) ε (mixEps es q.1.2) d p' p
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd (continuous_fst.fst)
  have hA := (continuous_denom_joint continuous_const continuous_const
    (continuous_const.add hℓ) (M := fun _ => m) (e := fun _ => ε) (X := _)
    (ℓ := fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ => p' + Fin.cons q.2 q.1.1)).measurable
  have hB := (continuous_denom_joint continuous_const continuous_const
    (continuous_const.add hℓ) (M := fun _ => m) (e := fun _ => ε) (X := _)
    (ℓ := fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ => p + Fin.cons q.2 q.1.1)).measurable
  have hL := (continuous_denom_joint continuous_const continuous_const
    ((continuous_dblMom d p' p).comp hℓ) (M := fun _ => m) (e := fun _ => ε) (X := _)
    (ℓ := fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      dblMom d p' p (Fin.cons q.2 q.1.1))).measurable
  have hC := (continuous_denom_joint ((continuous_mixMass Ms).comp continuous_fst.snd)
    ((continuous_mixEps es).comp continuous_fst.snd) hℓ).measurable
  have hN := (hNc.comp hℓ).measurable
  unfold dblIntegrand
  simp only [Function.comp_def] at hN hC
  fun_prop

/-- At fixed spatial momentum the integrand of `dblIntegrand` is bounded by `G (1 + t²)⁻¹`,
uniformly in the photon mass and in photon prescriptions `≥ e₀ > 0`. -/
theorem exists_norm_dblIntegrand_cons_le {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) (n : ℕ) {ε e₀ : ℝ} (hε : 0 < ε)
    (he₀ : 0 < e₀) (d : Fin 2) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ∃ G : ℝ, ∀ M η : ℝ, e₀ ≤ η → ∀ t : ℝ,
      ‖dblIntegrand N m M n ε η d p' p (Fin.cons t v : Fin 4 → ℝ)‖ ≤ G * (1 + t ^ 2)⁻¹ := by
  have hCN0 := nonneg_of_norm_le hNb
  set W₁ : ℝ := ∑ j : Fin 3, (v j + p' j.succ) ^ 2 + m ^ 2
  set W₂ : ℝ := ∑ j : Fin 3, (v j + p j.succ) ^ 2 + m ^ 2
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε (|p' 0| + |p 0|) (max W₁ W₂)
  refine ⟨CN * (2 * (1 + ‖v‖) ^ 2) * ((c ^ 3)⁻¹ * (e₀ ^ (n + 1))⁻¹), fun M η hη t => ?_⟩
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have hA : c * (1 + t ^ 2) ≤ ‖denom m ε (p' + (Fin.cons t v : Fin 4 → ℝ))‖ := by
    rw [denom_add_cons]
    exact hcb t _ _ (le_add_of_nonneg_right (abs_nonneg _)) (le_max_left _ _)
  have hB : c * (1 + t ^ 2) ≤ ‖denom m ε (p + (Fin.cons t v : Fin 4 → ℝ))‖ := by
    rw [denom_add_cons]
    exact hcb t _ _ (le_add_of_nonneg_left (abs_nonneg _)) (le_max_right _ _)
  have hL : c * (1 + t ^ 2) ≤ ‖denom m ε (dblMom d p' p (Fin.cons t v : Fin 4 → ℝ))‖ := by
    unfold dblMom
    split_ifs
    · exact hB
    · exact hA
  have hC : e₀ ≤ ‖denom M η (Fin.cons t v : Fin 4 → ℝ)‖ :=
    hη.trans (norm_denom_ge_eps M η _ (he₀.le.trans hη))
  have hN := norm_cons_numerator_le hNb hCN0 t v
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  rw [dblIntegrand, norm_mul, norm_inv, norm_mul, norm_mul, norm_mul, norm_pow]
  calc ‖N (Fin.cons t v : Fin 4 → ℝ)‖ *
        (‖denom m ε (p' + (Fin.cons t v : Fin 4 → ℝ))‖ *
          ‖denom m ε (p + (Fin.cons t v : Fin 4 → ℝ))‖ *
          ‖denom m ε (dblMom d p' p (Fin.cons t v : Fin 4 → ℝ))‖ *
          ‖denom M η (Fin.cons t v : Fin 4 → ℝ)‖ ^ (n + 1))⁻¹
      ≤ (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        ((c * (1 + t ^ 2)) * (c * (1 + t ^ 2)) * (c * 1) * e₀ ^ (n + 1))⁻¹ := by
        have h1 : c * 1 ≤ c * (1 + t ^ 2) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg t)) hc.le
        gcongr
        exact h1.trans hL
    _ = CN * (2 * (1 + ‖v‖) ^ 2) * ((c ^ 3)⁻¹ * (e₀ ^ (n + 1))⁻¹) * (1 + t ^ 2)⁻¹ := by
        field_simp

/-- The integrand of `dblIntegrand` at the mixed mass and prescription, as a function of
`((v, u), t)`. -/
noncomputable def mixIntegrandD (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ) : ℂ :=
  dblIntegrand N m (mixMass Ms q.1.2) (k + 1) ε (mixEps es q.1.2) d p' p
    (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)

/-- Step 1: energy × simplex at fixed spatial momentum. -/
theorem integrable_mixIntegrandD_time {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (d : Fin 2)
    (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable
      (fun q : ℝ × (Fin (k + 1) → ℝ) => mixIntegrandD N m Ms es ε d p' p ((v, q.2), q.1))
      ((volume : Measure ℝ).prod (volume.restrict (simplexSet (k + 1)))) := by
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  obtain ⟨G, hG⟩ := exists_norm_dblIntegrand_cons_le hNb m (k + 1) hε he₀ d p' p v
  have hFm : Measurable (mixIntegrandD N m Ms es ε d p' p) :=
    measurable_dblIntegrand_mix hNc m Ms es ε d p' p
  have hc : Measurable fun q : ℝ × (Fin (k + 1) → ℝ) =>
      (((v, q.2), q.1) : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ) := by fun_prop
  refine Integrable.mono' (g := fun q : ℝ × (Fin (k + 1) → ℝ) => G * (1 + q.1 ^ 2)⁻¹ * 1)
    ((integrable_inv_one_add_sq.const_mul G).mul_prod (integrable_const (1 : ℝ)))
    (hFm.comp hc).aestronglyMeasurable ?_
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := volume.restrict (simplexSet (k + 1)))).ae
    (ae_restrict_mem (measurableSet_simplexSet (k + 1)))
  filter_upwards [h2] with q hq
  rw [mul_one]
  exact hG _ _ (mixEps_ge hes₀ hq) q.1

theorem integral_time_dblProdIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (d : Fin 2)
    (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, dblProdIntegrand N m Ms es ε d p' p (Fin.cons t v : Fin 4 → ℝ) =
      ((k + 1).factorial : ℂ) * ∫ u in simplexSet (k + 1),
        ∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p ((v, u), t) := by
  simp_rw [dblProdIntegrand_eq_integral N m Ms hes ε d p' p]
  rw [integral_const_mul]
  congr 1
  exact integral_integral_swap (integrable_mixIntegrandD_time hNc hNb m Ms hes hε d p' p v)

theorem integrable_time_dblProdIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (d : Fin 2)
    (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => dblProdIntegrand N m Ms es ε d p' p (Fin.cons t v : Fin 4 → ℝ) := by
  refine ((integrable_mixIntegrandD_time hNc hNb m Ms hes hε d p' p v).integral_prod_left.const_mul
    ((k + 1).factorial : ℂ)).congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [dblProdIntegrand_eq_integral N m Ms hes ε d p' p]
  rfl

/-- Step 2: space × simplex. -/
theorem integrable_mixIntegrandD_space {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (d : Fin 2) :
    Integrable (fun x : (Fin 3 → ℝ) × (Fin (k + 1) → ℝ) =>
        ∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p (x, t))
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (simplexSet (k + 1)))) := by
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  obtain ⟨C, _, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 2)
    (by omega)
  have hFm : StronglyMeasurable (mixIntegrandD N m Ms es ε d p' p) :=
    (measurable_dblIntegrand_mix hNc m Ms es ε d p' p).stronglyMeasurable
  have hGm : StronglyMeasurable fun x : (Fin 3 → ℝ) × (Fin (k + 1) → ℝ) =>
      ∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p (x, t) :=
    hFm.integral_prod_right'
  set Cw : ℝ := ((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * ((k + 1 : ℕ) + 3)
  have hb := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (Cw * C)
  refine Integrable.mono' (hb.mul_prod (integrable_const (1 : ℝ))) hGm.aestronglyMeasurable ?_
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
    (ν := volume.restrict (simplexSet (k + 1)))).ae
    (ae_restrict_mem (measurableSet_simplexSet (k + 1)))
  filter_upwards [h2] with x hx
  rw [mul_one]
  have hs : ∫ t : ℝ, mixIntegrandD N m Ms es ε d p' p (x, t) =
      spatialW (dblWt d (k + 1)) α N m (mixMass Ms x.2) (k + 2) ε (mixEps es x.2) p' p x.1 :=
    integral_time_dblIntegrand hNc hNq hNb m (mixMass Ms x.2) (k + 1) (η := mixEps es x.2) hε
      (he₀.trans_le (mixEps_ge hes₀ hx)) d p' p x.1
  rw [hs]
  exact norm_spatialW_le (fun z hz => dblWt_norm_le d (k + 1) hz)
    (fun z hz v => hC (mixMass Ms x.2) (mixMass_ge hM₀.le hMs hx) _ z hz v) x.1

/-- **Exchange of the photon superposition with the energy-first integral** for the doubled
vertex, at fixed positive prescriptions, with both stages integrable. -/
theorem energyFirstIntegral_dblProdIntegrand_eq {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (d : Fin 2) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
        dblProdIntegrand N m Ms es ε d p' p (Fin.cons t v : Fin 4 → ℝ)) ∧
      Integrable (fun v : Fin 3 → ℝ =>
        ∫ t : ℝ, dblProdIntegrand N m Ms es ε d p' p (Fin.cons t v : Fin 4 → ℝ)) ∧
      energyFirstIntegral (dblProdIntegrand N m Ms es ε d p' p) = ((k + 1).factorial : ℂ) *
        ∫ u in simplexSet (k + 1), energyFirstIntegral
          (dblIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) d p' p) := by
  have hint2 := integrable_mixIntegrandD_space hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε d
  have hstep1 := integral_time_dblProdIntegrand hNc hNb m Ms hes hε d p' p
  refine ⟨integrable_time_dblProdIntegrand hNc hNb m Ms hes hε d p' p, ?_, ?_⟩
  · exact (hint2.integral_prod_left.const_mul ((k + 1).factorial : ℂ)).congr
      (Eventually.of_forall fun v => (hstep1 v).symm)
  · rw [energyFirstIntegral]
    simp_rw [hstep1]
    rw [integral_const_mul, integral_integral_swap hint2]
    rfl

/-! ### The limit and its continuity in the masses -/

/-- Joint measurability of the weighted closed form in `((M, v), z)`, the photon mass varying. -/
theorem measurable_timeW_mass {w : ℝ × ℝ → ℂ} (hw : Continuous w) {N : (Fin 4 → ℝ) → ℂ}
    (hNc : Continuous N) (α : ℂ) (m : ℝ) (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) =>
      w q.2 * timeP α N m q.1.1 n (effEps ε η q.2) p' p q.2 q.1.2 := by
  have h := measurable_timeP_mass hNc α m n ε η p' p
  have hW : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) => massW m q.1.1 p' p q.2 q.1.2 := by
    have h1 := continuous_shiftK p' p
    have h2 : Continuous fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) =>
        feynmanMass m q.1.1 q.2.1 q.2.2 p' p := by
      have h0 := continuous_dot_comp (continuous_shiftK p' p) (continuous_shiftK p' p)
      unfold shiftK at h0
      have h3 := h0.comp (continuous_snd : Continuous fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) => q.2)
      simp only [Function.comp_def] at h3
      unfold feynmanMass
      fun_prop
    refine Continuous.measurable ?_
    unfold massW
    fun_prop
  have hc : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) =>
      (Fin.cons (-shiftK p' p q.2 0) q.1.2 : Fin 4 → ℝ) :=
    (Continuous.finCons (A := fun _ : Fin 4 => ℝ)
      (((continuous_apply 0).comp (continuous_shiftK p' p)).neg.comp continuous_snd)
      continuous_fst.snd).measurable
  have hN : Measurable N := hNc.measurable
  have hf' : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) => w q.2 :=
    (hw.comp continuous_snd).measurable
  clear h
  unfold timeP effEps
  fun_prop

/-- The common bound on the weighted spatial integrals. -/
theorem norm_integral_spatialW_le {w : ℝ × ℝ → ℂ} {Cw : ℝ}
    (hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖w z‖ ≤ Cw) {α : ℂ} {N : (Fin 4 → ℝ) → ℂ}
    {m M : ℝ} {n : ℕ} {ε η : ℝ} {p' p : Fin 4 → ℝ} {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeP α N m M n (effEps ε η z) p' p z v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ))) :
    ‖∫ v, spatialW w α N m M n ε η p' p v‖ ≤
      ∫ v : Fin 3 → ℝ, Cw * C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun v => norm_spatialW_le hwb hC v)
  have h := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (Cw * C)
  simpa only [mul_assoc] using h

theorem stronglyMeasurable_integral_spatialW_mix {w : ℝ × ℝ → ℂ} (hw : Continuous w)
    {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ) (m : ℝ) {k : ℕ} (n : ℕ)
    (Ms : Fin (k + 2) → ℝ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    StronglyMeasurable fun u : Fin (k + 1) → ℝ =>
      ∫ v, spatialW w α N m (mixMass Ms u) n ε η p' p v := by
  have hf : Measurable fun q : ((Fin (k + 1) → ℝ) × (Fin 3 → ℝ)) × (ℝ × ℝ) =>
      w q.2 * timeP α N m (mixMass Ms q.1.1) n (effEps ε η q.2) p' p q.2 q.1.2 :=
    (measurable_timeW_mass hw hNc α m n ε η p' p).comp
      ((((continuous_mixMass Ms).comp continuous_fst.fst).prodMk
        continuous_fst.snd).measurable.prodMk measurable_snd)
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := feynmanMeasure)).integral_prod_right'

/-- **The limit of the doubled photon-product vertex**: when `ε → 0⁺` and every photon
prescription `ε_j → 0⁺`, the energy-first integral of `dblProdIntegrand` tends to
`dblProdLimit`, which does not depend on the prescriptions. -/
theorem tendsto_energyFirstIntegral_dblProdIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (d : Fin 2) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [l.NeBot] {ε : ι → ℝ} {es : ι → Fin (k + 2) → ℝ} (hε : Tendsto ε l (𝓝[>] 0))
    (hes : ∀ j, Tendsto (fun i => es i j) l (𝓝[>] 0)) :
    Tendsto (fun i => energyFirstIntegral (dblProdIntegrand N m Ms (es i) (ε i) d p' p)) l
      (𝓝 (dblProdLimit α N m Ms d p' p)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 2)
    (by omega)
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε self_mem_nhdsWithin
  have hespos : ∀ᶠ i in l, ∀ j, 0 < es i j :=
    eventually_all.2 fun j => (hes j) self_mem_nhdsWithin
  set Δ := simplexSet (k + 1)
  set Cw : ℝ := ((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * ((k + 1 : ℕ) + 3)
  set B : ℝ := ∫ v : Fin 3 → ℝ, Cw * C * (1 + ‖v‖) ^ (-(5 : ℝ))
  have hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖dblWt d (k + 1) z‖ ≤ Cw :=
    fun z hz => by simpa [Cw] using dblWt_norm_le d (k + 1) hz
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  have hes0 : Tendsto es l (𝓝 0) :=
    tendsto_pi_nhds.2 fun j => (hes j).mono_right nhdsWithin_le_nhds
  have hlim : Tendsto (fun i => ∫ u in Δ, energyFirstIntegral
      (dblIntegrand N m (mixMass Ms u) (k + 1) (ε i) (mixEps (es i) u) d p' p))
      l (𝓝 (∫ u in Δ,
        ∫ v, spatialW (dblWt d (k + 1)) α N m (mixMass Ms u) (k + 2) 0 0 p' p v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
      (integrable_const B) ?_
    · refine Eventually.of_forall fun i => ?_
      have h := ((measurable_dblIntegrand_mix hNc m Ms (es i) (ε i) d p' p).stronglyMeasurable
        |>.integral_prod_right' (ν := (volume : Measure ℝ))).integral_prod_left'
          (μ := (volume : Measure (Fin 3 → ℝ)))
      exact h.aestronglyMeasurable
    · filter_upwards [hεpos, hespos] with i h1 h2
      obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all h2
      filter_upwards [hΔ] with u hu
      rw [energyFirstIntegral_dblIntegrand_eq hNc hNq hNb m _ _ h1
        (he₀.trans_le (mixEps_ge hes₀ hu)) d p' p]
      exact norm_integral_spatialW_le hwb
        (fun z hz v => hC (mixMass Ms u) (mixMass_ge hM₀.le hMs hu) _ z hz v)
    · filter_upwards [hΔ] with u hu
      have hη : Tendsto (fun i => mixEps (es i) u) l (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := ((continuous_mixEps_eps u).tendsto 0).comp hes0
          simpa [mixEps, Function.comp_def] using this
        · filter_upwards [hespos] with i h2
          obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all h2
          exact he₀.trans_le (mixEps_ge hes₀ hu)
      exact tendsto_energyFirstIntegral_dblIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
        (k + 1) d hε hη tendsto_const_nhds
        (Eventually.of_forall fun _ => mixMass_ge hM₀.le hMs hu)
  refine (hlim.const_mul ((k + 1).factorial : ℂ)).congr' ?_
  filter_upwards [hεpos, hespos] with i h1 h2
  exact (energyFirstIntegral_dblProdIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs h2 h1
    d).2.2.symm

/-- **Continuity of the doubled limit in the photon masses**, on `M_j ≥ M₀ > 0`. -/
theorem tendsto_dblProdLimit {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} (d : Fin 2) {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {Ms : ι → Fin (k + 2) → ℝ}
    {Ms₀ : Fin (k + 2) → ℝ} (hMs : Tendsto Ms l (𝓝 Ms₀)) (hge : ∀ᶠ i in l, ∀ j, M₀ ≤ Ms i j) :
    Tendsto (fun i => dblProdLimit α N m (Ms i) d p' p) l
      (𝓝 (dblProdLimit α N m Ms₀ d p' p)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 2)
    (by omega)
  set Δ := simplexSet (k + 1)
  set Cw : ℝ := ((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * ((k + 1 : ℕ) + 3)
  set B : ℝ := ∫ v : Fin 3 → ℝ, Cw * C * (1 + ‖v‖) ^ (-(5 : ℝ))
  have hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖dblWt d (k + 1) z‖ ≤ Cw :=
    fun z hz => by simpa [Cw] using dblWt_norm_le d (k + 1) hz
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
    (integrable_const B) ?_
  · exact Eventually.of_forall fun i => (stronglyMeasurable_integral_spatialW_mix
      (continuous_dblWt d (k + 1)) hNc α m (k + 2) (Ms i) 0 0 p' p).aestronglyMeasurable
  · filter_upwards [hge] with i hi
    filter_upwards [hΔ] with u hu
    exact norm_integral_spatialW_le hwb
      (fun z hz v => hC (mixMass (Ms i) u) (mixMass_ge hM₀.le hi hu) _ z hz v)
  · filter_upwards [hΔ] with u hu
    exact tendsto_integral_spatialW (continuous_dblWt d (k + 1)) hwb hm hM₀ hp' hp hp0' hp0
      hNc α hNb (by omega) tendsto_const_nhds tendsto_const_nhds
      (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall fun _ => le_rfl)
      (((continuous_mixMass_masses u).tendsto Ms₀).comp hMs)
      (hge.mono fun i hi => mixMass_ge hM₀.le hi hu)

end QED.ChainProof.CtLoB

end
