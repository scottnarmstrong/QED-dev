/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.SelfEnergyEnergyFirst
public import QED.TwoLoop.VPHalfAtLimitEngine
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop self-energy with a power of the photon denominator: closed form and bound

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S4 of the plan (the one-loop
self-energy engine). After the integration by parts in the Feynman parameter of the inserted
vacuum polarization (`QED.ChainProof.SetCRegDisp.outerF_seVOuter_eq_spectral`), the outer
integrand of the self-energy class `V` is a combination of one-loop self-energies with **one**
electron denominator and several photon-type denominators with their own masses and
prescriptions. The vertex engine (`QED/TwoLoop/VPHalfAtLimitEngine.lean`) needs two on-shell
electron denominators; this file treats the self-energy building block

`F(ℓ) = N(ℓ) / (D_m(P + ℓ; ε) D_M(ℓ; η)^{n+1})` (`sePow`),

with `P` off shell below threshold.

* `inv_mul_pow_eq_integral_feynman`: `(X C^{n+1})⁻¹ = ∫₀¹ (n+1)(1-y)^n (yX + (1-y)C)^{-(n+2)}`.
  The combined denominator is the frozen `QED.WickModel.SelfEnergyLimit.combDen` with the
  effective prescription `y ε + (1 - y) η` (`seEff`).
* `integral_time_sePow`: the energy integral at fixed spatial momentum in closed form
  (`seSpatial`, from `QED.TwoLoop.VPHalfAtLimit.integral_quadratic_mul_shifted_pow`).
* **`exists_norm_seTime_le`, `norm_seSpatial_le`**: below threshold
  (`c₀ ≤ x m² + (1 - x) M₀² + x (1 - x) P²` on `[0, 1]`), uniformly in the photon mass `M ≥ M₀`
  and in all prescriptions, `‖seSpatial v‖ ≤ C (1 + ‖v‖)⁻⁴`, if the numerator has degree
  `d ≤ 2n - 1` and is at most linear in the energy unless `n ≥ 2`. The self-energy is one power
  worse than the vertex, so the exponent is `4`, not `5`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDispSE

open QED.OneLoop QED.Integration QED.WickModel QED.WickModel.SelfEnergyLimit
open QED.TwoLoop.VPHalfAtLimit (energyConst integral_quadratic_mul_shifted_pow
  integrable_quadratic_mul_shifted_pow neg_zpow_neg_nat norm_ofReal_sub_mul_I_mono
  nonneg_of_norm_le norm_cons_numerator_le)
open QED.OneLoop.VertexLimit (mem_slitPlane_neg_add_mul_I rpow_mul_sq_neg)

/-! ### Feynman parameters with a power of the second denominator -/

/-- **One variable**: `(X C^{n+1})⁻¹ = ∫₀¹ (n+1)(1-y)^n (yX + (1-y)C)^{-(n+2)} dy`. -/
theorem inv_mul_pow_eq_integral_feynman {X C : ℂ} (hX : X ≠ 0) (hC : C ≠ 0) (n : ℕ)
    (h : ∀ y ∈ Icc (0 : ℝ) 1, (y : ℂ) * X + (1 - y) * C ≠ 0) :
    (X * C ^ (n + 1))⁻¹ = ∫ y in (0 : ℝ)..1,
      ((n + 1 : ℂ) * (1 - (y : ℂ)) ^ n) *
        ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 2 : ℕ) : ℤ)) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  set G : ℂ → ℂ := fun w => -X⁻¹ * ((1 - w) / (w * X + (1 - w) * C)) ^ (n + 1) with hG
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => G y)
      (((n + 1 : ℂ) * (1 - (y : ℂ)) ^ n) *
        ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 2 : ℕ) : ℤ))) y := by
    intro y hy
    have hL := h y (hI ▸ hy)
    have hLd : HasDerivAt (fun w : ℂ => w * X + (1 - w) * C) (X - C) y := by
      have := ((hasDerivAt_id' (x := (y : ℂ))).mul_const X).fun_add
        (((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).mul_const C)
      convert this using 1; ring
    have hg := ((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).fun_div hLd hL
    have hG' := (hg.fun_pow (n + 1)).const_mul (-X⁻¹)
    refine HasDerivAt.comp_ofReal (e := G) ?_
    convert hG' using 1
    rw [zpow_neg, zpow_natCast]
    push_cast
    simp only [div_pow]
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => ((n + 1 : ℂ) * (1 - (y : ℂ)) ^ n) *
      ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 2 : ℕ) : ℤ))) (uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop)
      (ContinuousOn.zpow₀ (by fun_prop) _ fun y hy => Or.inl (h y (hI ▸ hy)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG, ofReal_one, ofReal_zero, sub_self, zero_div, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, mul_zero, zero_mul, zero_add,
    sub_zero, one_mul]
  simp only [div_pow, one_pow]
  field_simp
  ring

/-! ### Definitions -/

/-- The self-energy building block `N(ℓ) / (D_m(P + ℓ; ε) D_M(ℓ; η)^{n+1})`. -/
noncomputable def sePow (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ)
    (P ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * (denom m ε (P + ℓ) * denom M η ℓ ^ (n + 1))⁻¹

/-- The effective prescription `y ε + (1 - y) η`. -/
def seEff (ε η y : ℝ) : ℝ := y * ε + (1 - y) * η

/-- The Feynman weight `(n + 1)(1 - y)^n`. -/
noncomputable def seWt (n : ℕ) (y : ℝ) : ℂ := (n + 1 : ℂ) * (1 - (y : ℂ)) ^ n

/-- The integrand on `ℝ × (0, 1]` at fixed spatial momentum `v`. -/
noncomputable def seJoint (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ)
    (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) (q : ℝ × ℝ) : ℂ :=
  N (Fin.cons q.1 v : Fin 4 → ℝ) * (seWt n q.2 *
    combDen m M (seEff ε η q.2) P q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-((n + 2 : ℕ) : ℤ)))

/-- The closed-form energy integral at the Feynman parameter `y`, prescription `ε'`. -/
noncomputable def seTime (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε' : ℝ)
    (P : Fin 4 → ℝ) (y : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  (-1) ^ (n + 2) * (α * ((energyConst (n + 1) - energyConst (n + 2) : ℝ) : ℂ) *
      (-(massW m M P y v : ℂ) + ε' * I) ^ (-(((n : ℝ) + 1 / 2 : ℝ) : ℂ)) +
    N (Fin.cons (-(y * P 0)) v : Fin 4 → ℝ) * (energyConst (n + 2) : ℂ) *
      (-(massW m M P y v : ℂ) + ε' * I) ^ (-(((n : ℝ) + 3 / 2 : ℝ) : ℂ)))

/-- The energy integral after the Feynman-parameter integral. -/
noncomputable def seSpatial (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ)
    (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) : ℂ :=
  ∫ y in Ioc (0 : ℝ) 1, seWt n y * seTime α N m M n (seEff ε η y) P y v

/-! ### Elementary facts -/

theorem seEff_ge_min {ε η y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : min ε η ≤ seEff ε η y := by
  have h1 := min_le_left ε η
  have h2 := min_le_right ε η
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  unfold seEff
  nlinarith [mul_le_mul_of_nonneg_left h1 hy.1, mul_le_mul_of_nonneg_left h2 hy1]

theorem seEff_pos {ε η y : ℝ} (hε : 0 < ε) (hη : 0 < η) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 < seEff ε η y :=
  (lt_min hε hη).trans_le (seEff_ge_min hy)

theorem seWt_norm_le {n : ℕ} {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : ‖seWt n y‖ ≤ n + 1 := by
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  have hc : (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
  have hw : (1 - (y : ℂ)) ^ n = (((1 - y) ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [seWt, hc, hw, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h1 : (1 - y) ^ n ≤ 1 := pow_le_one₀ hy1 (by linarith [hy.1])
  calc (n + 1 : ℝ) * (1 - y) ^ n ≤ (n + 1) * 1 := by gcongr
    _ = _ := by ring

theorem continuous_seWt (n : ℕ) : Continuous (seWt n) := by
  unfold seWt; fun_prop

theorem feynman_combo_eq_combDen (m M ε η : ℝ) (P : Fin 4 → ℝ) (y : ℝ) (ℓ : Fin 4 → ℝ) :
    (y : ℂ) * denom m ε (P + ℓ) + (1 - y) * denom M η ℓ = combDen m M (seEff ε η y) P y ℓ := by
  simp only [combDen, denom, seEff]
  push_cast
  ring

/-! ### Step 1: Feynman parameters -/

theorem sePow_eq_integral_seJoint (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (P : Fin 4 → ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    sePow N m M n ε η P (Fin.cons t v : Fin 4 → ℝ) =
      ∫ y in Ioc (0 : ℝ) 1, seJoint N m M n ε η P v (t, y) := by
  set ℓ : Fin 4 → ℝ := Fin.cons t v
  have hA : (denom m ε (P + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hC : (denom M η ℓ).im < 0 := by rw [denom_im]; linarith
  rw [sePow, inv_mul_pow_eq_integral_feynman (ne_zero_of_im_neg hA) (ne_zero_of_im_neg hC) n
    (fun y hy => convex_combo_ne_zero hA hC hy), intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [seJoint, seWt, feynman_combo_eq_combDen, ℓ]

/-! ### Step 2: joint integrability and the energy integral -/

theorem combDen_cons_eq_neg (m M ε : ℝ) (P : Fin 4 → ℝ) (y t : ℝ) (v : Fin 3 → ℝ) :
    combDen m M ε P y (Fin.cons t v : Fin 4 → ℝ) =
      -(((t : ℂ) + (y * P 0 : ℝ)) ^ 2 + (-(massW m M P y v : ℂ) + ε * I)) := by
  rw [combDen_cons]
  ring

theorem continuousOn_seJoint {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m M : ℝ) (n : ℕ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ContinuousOn (seJoint N m M n ε η P v) (univ ×ˢ Icc (0 : ℝ) 1) := by
  have hN : Continuous fun q : ℝ × ℝ => N (Fin.cons q.1 v : Fin 4 → ℝ) :=
    hNc.comp (Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_fst continuous_const)
  have hW := (continuous_massW m M P v).comp (continuous_snd : Continuous fun q : ℝ × ℝ => q.2)
  have hD : Continuous fun q : ℝ × ℝ =>
      combDen m M (seEff ε η q.2) P q.2 (Fin.cons q.1 v : Fin 4 → ℝ) := by
    simp_rw [combDen_cons]
    simp only [Function.comp_def] at hW
    unfold seEff
    fun_prop
  have hw := (continuous_seWt n).comp (continuous_snd : Continuous fun q : ℝ × ℝ => q.2)
  refine hN.continuousOn.mul (hw.continuousOn.mul (hD.continuousOn.zpow₀ _ fun q hq => ?_))
  left
  intro h0
  have him := combDen_im m M (seEff ε η q.2) P q.2 (Fin.cons q.1 v : Fin 4 → ℝ)
  rw [h0, zero_im] at him
  have := seEff_pos hε hη hq.2
  linarith

theorem integrable_seJoint {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable (seJoint N m M n ε η P v)
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hCN0 := nonneg_of_norm_le hNb
  obtain ⟨CW, hCW⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_massW m M P v).continuousOn (s := Icc (0 : ℝ) 1)
  set ε₀ := min ε η
  have hε₀ : 0 < ε₀ := lt_min hε hη
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε₀ |P 0| CW
  set G : ℝ := CN * (2 * (1 + ‖v‖) ^ 2) * (n + 1) * (c ^ (n + 2))⁻¹
  have hmeas : AEStronglyMeasurable (seJoint N m M n ε η P v)
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict]
    exact ((continuousOn_seJoint hNc m M n hε hη P v).mono
      (prod_mono subset_rfl Ioc_subset_Icc_self)).aestronglyMeasurable
      (MeasurableSet.univ.prod measurableSet_Ioc)
  refine Integrable.mono' (g := fun q : ℝ × ℝ => G * (1 + q.1 ^ 2)⁻¹ * 1) ?_ hmeas
    ((ae_prod_restrict_Ioc (volume : Measure ℝ)).mono fun q hq => ?_)
  · exact (integrable_inv_one_add_sq.const_mul G).mul_prod (integrable_const (1 : ℝ))
  obtain ⟨t, y⟩ := q
  simp only at hq ⊢
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hq
  have ha : |y * P 0| ≤ |P 0| := by
    rw [abs_mul, abs_of_nonneg hyI.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hyI.2
  have hW : massW m M P y v ≤ CW :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCW y hyI)
  have hZ : c * (1 + t ^ 2) ≤
      ‖combDen m M (seEff ε η y) P y (Fin.cons t v : Fin 4 → ℝ)‖ := by
    refine (hcb t _ _ ha hW).trans ?_
    rw [combDen_cons]
    have e : ∀ a : ℝ, -((t : ℂ) + (y * P 0 : ℝ)) ^ 2 + (massW m M P y v : ℂ) - a * I =
        ((-(t + y * P 0) ^ 2 + massW m M P y v : ℝ) : ℂ) - a * I := fun a => by
      push_cast; ring
    rw [← add_sub_assoc, e, e]
    exact norm_ofReal_sub_mul_I_mono hε₀.le (seEff_ge_min hyI)
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  have hD : ‖combDen m M (seEff ε η y) P y (Fin.cons t v : Fin 4 → ℝ) ^
      (-((n + 2 : ℕ) : ℤ))‖ ≤ (c ^ (n + 2))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow]
    calc (‖combDen m M (seEff ε η y) P y (Fin.cons t v : Fin 4 → ℝ)‖ ^ (n + 2))⁻¹
        ≤ ((c * (1 + t ^ 2)) ^ (n + 2))⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hZ _)
      _ = (c ^ (n + 2))⁻¹ * ((1 + t ^ 2) ^ (n + 2))⁻¹ := by rw [mul_pow, mul_inv]
      _ ≤ (c ^ (n + 2))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹ := by
          gcongr
          · exact le_add_of_nonneg_right (sq_nonneg t)
          · omega
  have hN := norm_cons_numerator_le hNb hCN0 t v
  have hw := seWt_norm_le (n := n) hyI
  rw [seJoint, norm_mul, norm_mul, mul_one]
  calc ‖N (Fin.cons t v : Fin 4 → ℝ)‖ * (‖seWt n y‖ *
        ‖combDen m M (seEff ε η y) P y (Fin.cons t v : Fin 4 → ℝ) ^ (-((n + 2 : ℕ) : ℤ))‖)
      ≤ (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        ((n + 1) * ((c ^ (n + 2))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹)) := by
        gcongr
    _ = G * (1 + t ^ 2)⁻¹ := by
        simp only [G]; field_simp

/-- **The energy integral at a fixed Feynman parameter**, in closed form. -/
theorem integral_time_seJoint {N : (Fin 4 → ℝ) → ℂ} {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ t : ℝ, seJoint N m M n ε η P v (t, y) =
      seWt n y * seTime α N m M n (seEff ε η y) P y v := by
  obtain ⟨β, γ, h⟩ := hNq v
  have hε' := seEff_pos hε hη hy
  set Z : ℂ := -(massW m M P y v : ℂ) + (seEff ε η y : ℂ) * I with hZ
  have hZs : Z ∈ slitPlane := mem_slitPlane_neg_add_mul_I hε' _
  set a : ℝ := y * P 0
  have hpt : ∀ t : ℝ, seJoint N m M n ε η P v (t, y) =
      (seWt n y * (-1) ^ (n + 2)) *
        ((α * (t : ℂ) ^ 2 + β * t + γ) * (((t : ℂ) + a) ^ 2 + Z) ^ (-((n + 2 : ℕ) : ℤ))) := by
    intro t
    simp only [seJoint]
    rw [combDen_cons_eq_neg, neg_zpow_neg_nat, h t]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_quadratic_mul_shifted_pow hZs n a α β γ]
  have hNa : N (Fin.cons (-a) v : Fin 4 → ℝ) = α * (a : ℂ) ^ 2 - β * a + γ := by
    rw [h (-a)]; push_cast; ring
  have e1 : (3 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ) = -(((n : ℝ) + 1 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : (1 / 2 : ℂ) - ((n + 2 : ℕ) : ℂ) = -(((n : ℝ) + 3 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2, seTime, ← hZ, hNa]
  ring

/-- **The energy integral of the building block**, at fixed spatial momentum. -/
theorem integral_time_sePow {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, sePow N m M n ε η P (Fin.cons t v : Fin 4 → ℝ) =
      seSpatial α N m M n ε η P v := by
  simp_rw [sePow_eq_integral_seJoint N m M n hε hη P _ v]
  rw [integral_integral_swap (f := fun t y => seJoint N m M n ε η P v (t, y))
    (integrable_seJoint hNc hNb m M n hε hη P v)]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  exact integral_time_seJoint hNq m M n hε hη P v (Ioc_subset_Icc_self hy)

theorem integrable_time_sePow {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => sePow N m M n ε η P (Fin.cons t v : Fin 4 → ℝ) :=
  (integrable_seJoint hNc hNb m M n hε hη P v).integral_prod_left.congr
    (Eventually.of_forall fun t => (sePow_eq_integral_seJoint N m M n hε hη P t v).symm)

/-! ### Step 3: the bound, uniform in the prescriptions and the photon mass -/

theorem selfEnergyFeynmanMass_mono {m M₀ M s y : ℝ} (hM₀ : 0 ≤ M₀) (hM : M₀ ≤ M)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    selfEnergyFeynmanMass m M₀ s y ≤ selfEnergyFeynmanMass m M s y := by
  have h := pow_le_pow_left₀ hM₀ hM 2
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  unfold selfEnergyFeynmanMass
  nlinarith [mul_le_mul_of_nonneg_left h hy1]

/-- **The uniform bound on the closed form**: below threshold, for photon masses `M ≥ M₀`, every
prescription and `y ∈ [0, 1]`, `‖seTime … y v‖ ≤ C (1 + ‖v‖)⁻⁴`, if the numerator has degree
`d ≤ 2n - 1` and its energy-squared coefficient `α` vanishes unless `n ≥ 2`. -/
theorem exists_norm_seTime_le {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    (α : ℂ) {N : (Fin 4 → ℝ) → ℂ} {n d : ℕ} {CN : ℝ}
    (hNd : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ d) (hd : d + 1 ≤ 2 * n) (hα : α = 0 ∨ 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, M₀ ≤ M → ∀ ε' : ℝ, ∀ y ∈ Icc (0 : ℝ) 1,
      ∀ v : Fin 3 → ℝ, ‖seTime α N m M n ε' P y v‖ ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  have hCN0 : 0 ≤ CN := by
    have := hNd 0
    have h1 : 0 < (1 + ‖(0 : Fin 4 → ℝ)‖) ^ d := by positivity
    by_contra h
    nlinarith [norm_nonneg (N 0), not_le.mp h]
  set A0 : ℝ := ‖P‖ with hA0_def
  have hA0 : 0 ≤ A0 := by positivity
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) A0 hc₀
  set s1 : ℝ := (n : ℝ) + 1 / 2
  set s2 : ℝ := (n : ℝ) + 3 / 2
  set K1 : ℝ := ‖α‖ * |energyConst (n + 1) - energyConst (n + 2)|
  set K2 : ℝ := CN * (1 + A0) ^ d * |energyConst (n + 2)|
  refine ⟨K1 * c1 ^ (-s1) + K2 * c1 ^ (-s2), by positivity, fun M hM ε' y hy v => ?_⟩
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  set W : ℝ := massW m M P y v
  have hD : c₀ ≤ selfEnergyFeynmanMass m M (Minkowski.dot P P) y :=
    (hP y hy).trans (selfEnergyFeynmanMass_mono hM₀ hM hy)
  have hb : ‖(fun k : Fin 3 => y * P k.succ)‖ ≤ A0 := by
    refine (pi_norm_le_iff_of_nonneg hA0).2 fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1]
    calc y * |P k.succ| ≤ 1 * |P k.succ| := by gcongr; exact hy.2
      _ ≤ A0 := by rw [one_mul, ← Real.norm_eq_abs]; exact norm_le_pi_norm P _
  have hW : c1 * u ^ 2 ≤ W := hcoer v _ _ hb hD
  have hpos : 0 < c1 * u ^ 2 := by positivity
  have hW0 : 0 < W := hpos.trans_le hW
  have hs1 : 0 ≤ s1 := by positivity
  have hs2 : 0 ≤ s2 := by positivity
  have hWs : ∀ s : ℝ, 0 ≤ s → W ^ (-s) ≤ c1 ^ (-s) * u ^ (-(2 * s)) := fun s hs =>
    calc W ^ (-s) ≤ (c1 * u ^ 2) ^ (-s) := Real.rpow_le_rpow_of_nonpos hpos hW (by linarith)
      _ = c1 ^ (-s) * u ^ (-(2 * s)) := rpow_mul_sq_neg hc1.le hu0
  have r1 : ‖α‖ * W ^ (-s1) ≤ ‖α‖ * (c1 ^ (-s1) * u ^ (-(4 : ℝ))) := by
    rcases hα with h0 | hn
    · rw [h0, norm_zero, zero_mul, zero_mul]
    · gcongr
      refine (hWs s1 hs1).trans ?_
      gcongr
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      simp only [s1]; linarith
  have r2 : u ^ d * W ^ (-s2) ≤ c1 ^ (-s2) * u ^ (-(4 : ℝ)) := by
    have h2 : u ^ d * u ^ (-(2 * s2)) ≤ u ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast u d, ← Real.rpow_add (by linarith)]
      refine Real.rpow_le_rpow_of_exponent_le hu1 ?_
      have : ((d : ℕ) : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hd
      simp only [s2]; linarith
    calc u ^ d * W ^ (-s2) ≤ u ^ d * (c1 ^ (-s2) * u ^ (-(2 * s2))) := by
          gcongr; exact hWs s2 hs2
      _ = c1 ^ (-s2) * (u ^ d * u ^ (-(2 * s2))) := by ring
      _ ≤ c1 ^ (-s2) * u ^ (-(4 : ℝ)) := by gcongr
  have hNt : ‖N (Fin.cons (-(y * P 0)) v : Fin 4 → ℝ)‖ ≤ CN * (1 + A0) ^ d * u ^ d := by
    refine (hNd _).trans ?_
    have ha : |-(y * P 0)| ≤ A0 := by
      rw [abs_neg, abs_mul, abs_of_nonneg hy.1]
      calc y * |P 0| ≤ 1 * |P 0| := by gcongr; exact hy.2
        _ ≤ A0 := by rw [one_mul, ← Real.norm_eq_abs]; exact norm_le_pi_norm P _
    have h1 := norm_finCons_le (-(y * P 0)) v
    have h2 : 1 + ‖(Fin.cons (-(y * P 0)) v : Fin 4 → ℝ)‖ ≤ (1 + A0) * u := by
      simp only [u]; nlinarith [norm_nonneg v]
    calc CN * (1 + ‖(Fin.cons (-(y * P 0)) v : Fin 4 → ℝ)‖) ^ d
        ≤ CN * ((1 + A0) * u) ^ d := by gcongr
      _ = CN * (1 + A0) ^ d * u ^ d := by rw [mul_pow]; ring
  have hc1' := norm_cpow_neg_add_mul_I_le (ε := ε') hW0 hs1
  have hc2' := norm_cpow_neg_add_mul_I_le (ε := ε') hW0 hs2
  have hK : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [seTime, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hK, hK]
  calc ‖α‖ * |energyConst (n + 1) - energyConst (n + 2)| *
        ‖(-(W : ℂ) + ε' * I) ^ (-((s1 : ℝ) : ℂ))‖ +
      ‖N (Fin.cons (-(y * P 0)) v : Fin 4 → ℝ)‖ * |energyConst (n + 2)| *
        ‖(-(W : ℂ) + ε' * I) ^ (-((s2 : ℝ) : ℂ))‖
      ≤ |energyConst (n + 1) - energyConst (n + 2)| * (‖α‖ * W ^ (-s1)) +
        |energyConst (n + 2)| * (CN * (1 + A0) ^ d) * (u ^ d * W ^ (-s2)) := by
        have e1 : ‖α‖ * |energyConst (n + 1) - energyConst (n + 2)| *
            ‖(-(W : ℂ) + ε' * I) ^ (-((s1 : ℝ) : ℂ))‖ ≤
            |energyConst (n + 1) - energyConst (n + 2)| * (‖α‖ * W ^ (-s1)) := by
          rw [mul_comm ‖α‖, mul_assoc]; gcongr
        have e2 : ‖N (Fin.cons (-(y * P 0)) v : Fin 4 → ℝ)‖ * |energyConst (n + 2)| *
            ‖(-(W : ℂ) + ε' * I) ^ (-((s2 : ℝ) : ℂ))‖ ≤
            (CN * (1 + A0) ^ d * u ^ d) * |energyConst (n + 2)| * W ^ (-s2) := by
          gcongr
        nlinarith [e1, e2]
    _ ≤ |energyConst (n + 1) - energyConst (n + 2)| * (‖α‖ * (c1 ^ (-s1) * u ^ (-(4 : ℝ)))) +
        |energyConst (n + 2)| * (CN * (1 + A0) ^ d) * (c1 ^ (-s2) * u ^ (-(4 : ℝ))) := by
        gcongr
    _ = (K1 * c1 ^ (-s1) + K2 * c1 ^ (-s2)) * u ^ (-(4 : ℝ)) := by
        simp only [K1, K2]; ring

theorem norm_seSpatial_le {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M : ℝ} {n : ℕ} {ε η : ℝ}
    {P : Fin 4 → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖seTime α N m M n (seEff ε η y) P y v‖ ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ)))
    (v : Fin 3 → ℝ) :
    ‖seSpatial α N m M n ε η P v‖ ≤ (n + 1) * C * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  have hfin : volume (Ioc (0 : ℝ) 1) < ⊤ := measure_Ioc_lt_top
  have h := norm_setIntegral_le_of_norm_le_const hfin
    (f := fun y => seWt n y * seTime α N m M n (seEff ε η y) P y v)
    (C := (n + 1) * (C * (1 + ‖v‖) ^ (-(4 : ℝ)))) fun y hy => by
      have hyI := Ioc_subset_Icc_self hy
      have hC0 : 0 ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ)) := (norm_nonneg _).trans (hC y hyI v)
      rw [norm_mul]
      exact mul_le_mul (seWt_norm_le hyI) (hC y hyI v) (norm_nonneg _) (by positivity)
  rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero, mul_one] at h
  refine h.trans (le_of_eq ?_)
  ring

end QED.ChainProof.SetCRegDispSE

end
