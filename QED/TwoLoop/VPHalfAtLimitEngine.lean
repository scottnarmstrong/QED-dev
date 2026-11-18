/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitFeynman
public import QED.OneLoop.VertexEnergyFirst
public import QED.Integration.LoopBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop vertex with a power of the photon denominator and its own prescription

The analytic engine for the `ε → 0⁺` limit of the vacuum-polarization class in closed form
(`QED.TwoLoop.VPHalfAt.contractionValue₂_VP_eq_closedForm`, obligation O2-8 at the `ε → 0` level).
After the inner loop and the integration by parts in its Feynman parameter, every piece of the
outer integrand is an outer one-loop vertex whose photon factor is a product of photon
denominators with different masses **and different prescriptions** (`ε` on the model's photon
lines, `ε/(x(1-x))` on the spectral line). Feynman parameters over the photon denominators reduce
every such factor to a superposition of single photon denominators raised to a power `n + 1 ≥ 2`.
This file treats that building block, uniformly in the prescriptions.

Fix on-shell positive-energy `p, p'`, a numerator `N` quadratic in the loop energy with constant
leading coefficient `α` and of quadratic growth, `n ≥ 1`, and

`F_{ε,η}(ℓ) = N(ℓ) / (D_m(p' + ℓ; ε) D_m(p + ℓ; ε) D_M(ℓ; η)^{n+1})` (`powIntegrand`),

with electron prescription `ε > 0` and photon prescription `η > 0`.

* **Parametric form** (`powIntegrand_eq_integral_jointP`): Feynman parameters on the square
  (`QED.TwoLoop.VPHalfAtLimit.inv_mul_mul_pow_eq_integral_feynmanMeasure`). The combined
  denominator is the frozen `combDen` with the single effective prescription
  `y ε + (1 - y) η` (`effEps`): in parametric form the two prescriptions combine into one
  positive imaginary part.
* **Energy integral in closed form** (`integral_time_jointP`, `timeP`), from
  `QED.TwoLoop.VPHalfAtLimit.integral_quadratic_mul_shifted_pow`, and the energy-first integral as
  the spatial integral of `spatialP` (`energyFirstIntegral_powIntegrand_eq`), with both stages
  integrable.
* **A bound uniform in the prescriptions and in the photon mass** `M ≥ M₀ > 0`
  (`exists_norm_timeP_le`, `norm_spatialP_le`): `‖spatialP v‖ ≤ C (1 + ‖v‖)⁻⁵`. No
  Pauli–Villars cancellation is needed, since the photon power is at least two.
* **The limit** (`tendsto_energyFirstIntegral_powIntegrand`): along any countably generated
  filter on which `ε → 0⁺`, `η → 0⁺` and `M → M_* ` with `M ≥ M₀`, the energy-first integral tends
  to `∫ spatialP(ε = η = 0, M_*)`. In particular the limit does not depend on how the two
  prescriptions go to zero, and it is continuous in the photon mass.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtLimit

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration

/-! ### Definitions -/

/-- The integrand `N(ℓ) / (D_m(p' + ℓ; ε) D_m(p + ℓ; ε) D_M(ℓ; η)^{n+1})`. -/
noncomputable def powIntegrand (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ)
    (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * (denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom M η ℓ ^ (n + 1))⁻¹

/-- The effective prescription `y ε + (1 - y) η` at the Feynman parameters `z = (x, y)`. -/
def effEps (ε η : ℝ) (z : ℝ × ℝ) : ℝ := z.2 * ε + (1 - z.2) * η

/-- The Feynman weight `(n+1)(n+2) y (1-y)^n`. -/
noncomputable def feynWt (n : ℕ) (z : ℝ × ℝ) : ℂ :=
  ((n + 1) * (n + 2) : ℂ) * ((z.2 : ℂ) * (1 - z.2) ^ n)

/-- The integrand on `ℝ × [0,1]²` at fixed spatial momentum `v`. -/
noncomputable def jointP (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  N (Fin.cons q.1 v : Fin 4 → ℝ) * (feynWt n q.2 *
    combDen m M (effEps ε η q.2) p' p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-((n + 3 : ℕ) : ℤ)))

/-- The closed-form energy integral at Feynman parameters `z`, effective prescription `ε'`. -/
noncomputable def timeP (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε' : ℝ)
    (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (v : Fin 3 → ℝ) : ℂ :=
  (-1) ^ (n + 3) * (α * ((energyConst (n + 2) - energyConst (n + 3) : ℝ) : ℂ) *
      (-(massW m M p' p z v : ℂ) + ε' * I) ^ (-(((n : ℝ) + 3 / 2 : ℝ) : ℂ)) +
    N (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) * (energyConst (n + 3) : ℂ) *
      (-(massW m M p' p z v : ℂ) + ε' * I) ^ (-(((n : ℝ) + 5 / 2 : ℝ) : ℂ)))

/-- The energy integral after the Feynman-parameter integral. -/
noncomputable def spatialP (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ)
    (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) : ℂ :=
  ∫ z, feynWt n z * timeP α N m M n (effEps ε η z) p' p z v ∂feynmanMeasure

/-! ### Elementary facts -/

theorem feynman_combo_eq_combDen (m M ε η : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ)
    (ℓ : Fin 4 → ℝ) :
    (z.2 : ℂ) * ((z.1 : ℂ) * denom m ε (p' + ℓ) + (1 - z.1) * denom m ε (p + ℓ)) +
        (1 - z.2) * denom M η ℓ = combDen m M (effEps ε η z) p' p z ℓ := by
  simp only [combDen, denom, effEps]
  push_cast
  ring

theorem effEps_ge_min {ε η : ℝ} {z : ℝ × ℝ} (hy : z.2 ∈ Icc (0 : ℝ) 1) :
    min ε η ≤ effEps ε η z := by
  have h1 := min_le_left ε η
  have h2 := min_le_right ε η
  have hy0 := hy.1
  have hy1 : 0 ≤ 1 - z.2 := by linarith [hy.2]
  unfold effEps
  nlinarith [mul_le_mul_of_nonneg_left h1 hy0, mul_le_mul_of_nonneg_left h2 hy1]

theorem effEps_pos {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) {z : ℝ × ℝ}
    (hy : z.2 ∈ Icc (0 : ℝ) 1) : 0 < effEps ε η z :=
  (lt_min hε hη).trans_le (effEps_ge_min hy)

theorem effEps_nonneg {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) {z : ℝ × ℝ}
    (hy : z.2 ∈ Icc (0 : ℝ) 1) : 0 ≤ effEps ε η z :=
  (le_min hε hη).trans (effEps_ge_min hy)

theorem norm_ofReal_sub_mul_I_mono {X a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖(X : ℂ) - a * I‖ ≤ ‖(X : ℂ) - b * I‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  simp only [normSq_apply, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, mul_im]
  nlinarith

theorem feynWt_norm_le {n : ℕ} {z : ℝ × ℝ} (hy : z.2 ∈ Icc (0 : ℝ) 1) :
    ‖feynWt n z‖ ≤ (n + 1) * (n + 2) := by
  have hy0 := hy.1
  have hy1 : 0 ≤ 1 - z.2 := by linarith [hy.2]
  have hc : ((n + 1) * (n + 2) : ℂ) = (((n + 1) * (n + 2) : ℝ) : ℂ) := by push_cast; ring
  have hw : ((z.2 : ℂ) * (1 - z.2) ^ n) = ((z.2 * (1 - z.2) ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [feynWt, hc, hw, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h1 : z.2 * (1 - z.2) ^ n ≤ 1 := by
    have := pow_le_one₀ hy1 (by linarith [hy.1] : 1 - z.2 ≤ 1) (n := n)
    calc z.2 * (1 - z.2) ^ n ≤ 1 * 1 := by gcongr; exact hy.2
      _ = 1 := by ring
  calc (n + 1) * (n + 2) * (z.2 * (1 - z.2) ^ n) ≤ (n + 1) * (n + 2) * 1 := by gcongr
    _ = _ := by ring

theorem continuous_feynWt (n : ℕ) : Continuous (feynWt n) := by
  unfold feynWt; fun_prop

theorem norm_cons_numerator_le {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (hCN : 0 ≤ CN) (t : ℝ) (v : Fin 3 → ℝ) :
    ‖N (Fin.cons t v : Fin 4 → ℝ)‖ ≤ CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2) := by
  refine (hNb _).trans ?_
  have h1 := norm_finCons_le t v
  have h2 : (1 + ‖(Fin.cons t v : Fin 4 → ℝ)‖) ^ 2 ≤ 2 * (1 + ‖v‖) ^ 2 * (1 + t ^ 2) := by
    have h3 : (1 + ‖(Fin.cons t v : Fin 4 → ℝ)‖) ^ 2 ≤ (1 + (|t| + ‖v‖)) ^ 2 := by
      gcongr
    have h4 : |t| ^ 2 = t ^ 2 := sq_abs t
    have h5 : 1 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg v]
    nlinarith [norm_nonneg v, abs_nonneg t, sq_nonneg (1 + ‖v‖ - |t|),
      mul_nonneg (sq_nonneg t) (sub_nonneg.2 h5)]
  calc CN * (1 + ‖(Fin.cons t v : Fin 4 → ℝ)‖) ^ 2
      ≤ CN * (2 * (1 + ‖v‖) ^ 2 * (1 + t ^ 2)) := by gcongr
    _ = CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2) := by ring

theorem nonneg_of_norm_le {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) : 0 ≤ CN := by
  have := hNb 0
  have h1 : 0 < (1 + ‖(0 : Fin 4 → ℝ)‖) ^ 2 := by positivity
  by_contra h
  nlinarith [norm_nonneg (N 0), not_le.mp h]

/-! ### Step 1: Feynman parameters -/

theorem powIntegrand_eq_integral_jointP (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    powIntegrand N m M n ε η p' p (Fin.cons t v : Fin 4 → ℝ) =
      ∫ z, jointP N m M n ε η p' p v (t, z) ∂feynmanMeasure := by
  set ℓ : Fin 4 → ℝ := Fin.cons t v
  have hA : (denom m ε (p' + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hB : (denom m ε (p + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hC : (denom M η ℓ).im < 0 := by rw [denom_im]; linarith
  rw [powIntegrand, inv_mul_mul_pow_eq_integral_feynmanMeasure hA hB hC n,
    ← integral_const_mul]
  congr 1
  ext z
  simp only [jointP, feynWt, feynman_combo_eq_combDen]
  ring

/-! ### Step 2: joint integrability and the energy integral -/

theorem combDen_cons_eq_neg (m M ε : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (t : ℝ)
    (v : Fin 3 → ℝ) :
    combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ) =
      -(((t : ℂ) + shiftK p' p z 0) ^ 2 + (-(massW m M p' p z v : ℂ) + ε * I)) := by
  rw [combDen_cons]
  ring

theorem mem_slitPlane_of_pos {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    -(W : ℂ) + ε * I ∈ slitPlane := mem_slitPlane_neg_add_mul_I hε W

theorem norm_combDen_cons_ge {m M ε ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) (h : ε₀ ≤ ε) (p' p : Fin 4 → ℝ)
    (z : ℝ × ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    ‖-((t : ℂ) + shiftK p' p z 0) ^ 2 + (massW m M p' p z v : ℂ) - ε₀ * I‖ ≤
      ‖combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ)‖ := by
  rw [combDen_cons, ← add_sub_assoc]
  have e : ∀ a : ℝ, -((t : ℂ) + shiftK p' p z 0) ^ 2 + (massW m M p' p z v : ℂ) - a * I =
      ((-(t + shiftK p' p z 0) ^ 2 + massW m M p' p z v : ℝ) : ℂ) - a * I := fun a => by
    push_cast; ring
  rw [e, e]
  exact norm_ofReal_sub_mul_I_mono hε₀ h

theorem continuousOn_jointP {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m M : ℝ) (n : ℕ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ContinuousOn (jointP N m M n ε η p' p v) (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  have hN : Continuous fun q : ℝ × (ℝ × ℝ) => N (Fin.cons q.1 v : Fin 4 → ℝ) :=
    hNc.comp (Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_fst continuous_const)
  have hD : Continuous fun q : ℝ × (ℝ × ℝ) =>
      combDen m M (effEps ε η q.2) p' p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) := by
    simp_rw [combDen_cons]
    have h1 := (continuous_apply 0).comp ((continuous_shiftK p' p).comp
      (continuous_snd : Continuous fun q : ℝ × (ℝ × ℝ) => q.2))
    have h2 := (continuous_massW m M p' p v).comp
      (continuous_snd : Continuous fun q : ℝ × (ℝ × ℝ) => q.2)
    simp only [Function.comp_def] at h1 h2
    unfold effEps
    fun_prop
  have hW := (continuous_feynWt n).comp (continuous_snd : Continuous fun q : ℝ × (ℝ × ℝ) => q.2)
  refine (hN.continuousOn.mul (hW.continuousOn.mul (hD.continuousOn.zpow₀ _ fun q hq => ?_)))
  left
  intro h0
  have him := combDen_cons_im m M (effEps ε η q.2) p' p q.2 q.1 v
  rw [h0, zero_im] at him
  have := effEps_pos hε hη hq.2.2
  linarith

theorem aestronglyMeasurable_jointP {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m M : ℝ)
    (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    AEStronglyMeasurable (jointP N m M n ε η p' p v)
      ((volume : Measure ℝ).prod feynmanMeasure) := by
  rw [volume_prod_feynmanMeasure]
  exact ((continuousOn_jointP hNc m M n hε hη p' p v).mono
    (prod_mono subset_rfl Ioc_prod_subset)).aestronglyMeasurable
    (MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Ioc))

theorem integrable_jointP {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable (jointP N m M n ε η p' p v) ((volume : Measure ℝ).prod feynmanMeasure) := by
  have hCN0 := nonneg_of_norm_le hNb
  obtain ⟨CW, hCW⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_massW m M p' p v).continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  set ε₀ := min ε η
  have hε₀ : 0 < ε₀ := lt_min hε hη
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε₀ (‖p'‖ + ‖p‖) CW
  set G : ℝ := CN * (2 * (1 + ‖v‖) ^ 2) * ((n + 1) * (n + 2)) * (c ^ (n + 3))⁻¹
  refine Integrable.mono' (g := fun q : ℝ × (ℝ × ℝ) => G * (1 + q.1 ^ 2)⁻¹ * 1) ?_
    (aestronglyMeasurable_jointP hNc m M n hε hη p' p v)
    (ae_volume_prod_feynmanMeasure.mono fun q hq => ?_)
  · exact (integrable_inv_one_add_sq.const_mul G).mul_prod (integrable_const (1 : ℝ))
  obtain ⟨t, z⟩ := q
  simp only at hq ⊢
  have hzI : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := Ioc_prod_subset hq
  have ha : |shiftK p' p z 0| ≤ ‖p'‖ + ‖p‖ :=
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans (norm_shiftK_le p' p hzI)
  have hW : massW m M p' p z v ≤ CW :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCW z hzI)
  have hZ : c * (1 + t ^ 2) ≤
      ‖combDen m M (effEps ε η z) p' p z (Fin.cons t v : Fin 4 → ℝ)‖ :=
    (hcb t _ _ ha hW).trans (norm_combDen_cons_ge hε₀.le (effEps_ge_min hzI.2) p' p z t v)
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  have hD : ‖combDen m M (effEps ε η z) p' p z (Fin.cons t v : Fin 4 → ℝ) ^
      (-((n + 3 : ℕ) : ℤ))‖ ≤ (c ^ (n + 3))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow]
    calc (‖combDen m M (effEps ε η z) p' p z (Fin.cons t v : Fin 4 → ℝ)‖ ^ (n + 3))⁻¹
        ≤ ((c * (1 + t ^ 2)) ^ (n + 3))⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hZ _)
      _ = (c ^ (n + 3))⁻¹ * ((1 + t ^ 2) ^ (n + 3))⁻¹ := by rw [mul_pow, mul_inv]
      _ ≤ (c ^ (n + 3))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹ := by
          gcongr
          · exact le_add_of_nonneg_right (sq_nonneg t)
          · omega
  have hN := norm_cons_numerator_le hNb hCN0 t v
  have hw := feynWt_norm_le (n := n) hzI.2
  rw [jointP, norm_mul, norm_mul, mul_one]
  calc ‖N (Fin.cons t v : Fin 4 → ℝ)‖ * (‖feynWt n z‖ *
        ‖combDen m M (effEps ε η z) p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-((n + 3 : ℕ) : ℤ))‖)
      ≤ (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        (((n + 1) * (n + 2)) * ((c ^ (n + 3))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹)) := by
        gcongr
    _ = G * (1 + t ^ 2)⁻¹ := by
        simp only [G]; field_simp

theorem neg_zpow_neg_nat (Y : ℂ) (k : ℕ) :
    (-Y) ^ (-(k : ℤ)) = (-1) ^ k * Y ^ (-(k : ℤ)) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, neg_pow, mul_inv]
  congr 1
  rcases neg_one_pow_eq_or ℂ k with h | h <;> rw [h] <;> norm_num

/-- **The energy integral at fixed Feynman parameters**, in closed form. -/
theorem integral_time_jointP {N : (Fin 4 → ℝ) → ℂ} {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ∫ t : ℝ, jointP N m M n ε η p' p v (t, z) =
      feynWt n z * timeP α N m M n (effEps ε η z) p' p z v := by
  obtain ⟨β, γ, h⟩ := hNq v
  have hε' := effEps_pos hε hη hz.2
  set Z : ℂ := -(massW m M p' p z v : ℂ) + (effEps ε η z : ℂ) * I with hZ
  have hZs : Z ∈ slitPlane := mem_slitPlane_of_pos hε' _
  set a : ℝ := shiftK p' p z 0
  have hpt : ∀ t : ℝ, jointP N m M n ε η p' p v (t, z) =
      (feynWt n z * (-1) ^ (n + 3)) *
        ((α * (t : ℂ) ^ 2 + β * t + γ) * (((t : ℂ) + a) ^ 2 + Z) ^ (-((n + 1 + 2 : ℕ) : ℤ))) := by
    intro t
    simp only [jointP]
    rw [combDen_cons_eq_neg, neg_zpow_neg_nat, h t]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_quadratic_mul_shifted_pow hZs (n + 1) a α β γ]
  have hNa : N (Fin.cons (-a) v : Fin 4 → ℝ) = α * (a : ℂ) ^ 2 - β * a + γ := by
    rw [h (-a)]; push_cast; ring
  have e1 : (3 / 2 : ℂ) - ((n + 1 + 2 : ℕ) : ℂ) = -(((n : ℝ) + 3 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : (1 / 2 : ℂ) - ((n + 1 + 2 : ℕ) : ℂ) = -(((n : ℝ) + 5 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2, timeP, ← hZ, hNa]
  ring

theorem integrable_time_jointP_slice {N : (Fin 4 → ℝ) → ℂ} {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    Integrable fun t : ℝ => jointP N m M n ε η p' p v (t, z) := by
  obtain ⟨β, γ, h⟩ := hNq v
  have hε' := effEps_pos hε hη hz.2
  have hZs := mem_slitPlane_of_pos hε' (massW m M p' p z v)
  refine ((integrable_quadratic_mul_shifted_pow hZs (n + 1) (shiftK p' p z 0) α β γ).const_mul
    (feynWt n z * (-1) ^ (n + 3))).congr (Eventually.of_forall fun t => ?_)
  simp only [jointP]
  rw [combDen_cons_eq_neg, neg_zpow_neg_nat, h t]
  ring

/-- **The energy integral of the integrand**, at fixed spatial momentum. -/
theorem integral_time_powIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, powIntegrand N m M n ε η p' p (Fin.cons t v : Fin 4 → ℝ) =
      spatialP α N m M n ε η p' p v := by
  simp_rw [powIntegrand_eq_integral_jointP N m M n hε hη p' p _ v]
  rw [integral_integral_swap (f := fun t z => jointP N m M n ε η p' p v (t, z))
    (integrable_jointP hNc hNb m M n hε hη p' p v)]
  refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
  exact integral_time_jointP hNq m M n hε hη p' p v (Ioc_prod_subset hz)

theorem integrable_time_powIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => powIntegrand N m M n ε η p' p (Fin.cons t v : Fin 4 → ℝ) :=
  (integrable_jointP hNc hNb m M n hε hη p' p v).integral_prod_left.congr
    (Eventually.of_forall fun t => (powIntegrand_eq_integral_jointP N m M n hε hη p' p t v).symm)

theorem continuous_powIntegrand_cons {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m M : ℝ)
    (n : ℕ) {ε η : ℝ} (hε : ε ≠ 0) (hη : η ≠ 0) (p' p : Fin 4 → ℝ) :
    Continuous fun q : (Fin 3 → ℝ) × ℝ =>
      powIntegrand N m M n ε η p' p (Fin.cons q.2 q.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : (Fin 3 → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst
  have hd : ∀ (M e : ℝ), e ≠ 0 → ∀ (k : (Fin 3 → ℝ) × ℝ → Fin 4 → ℝ), Continuous k →
      Continuous fun q => denom M e (k q) := by
    intro M e _ k hk
    unfold denom
    have := continuous_dot_comp hk hk
    fun_prop
  have hne : ∀ (M e : ℝ), e ≠ 0 → ∀ ℓ, denom M e ℓ ≠ 0 := fun M e he ℓ h => by
    have := denom_im M e ℓ
    rw [h, zero_im] at this
    exact he (by linarith)
  unfold powIntegrand
  refine (hNc.comp hℓ).mul (Continuous.inv₀ ?_ fun q => ?_)
  · exact ((hd m ε hε _ (continuous_const.add hℓ)).mul (hd m ε hε _ (continuous_const.add hℓ))).mul
      ((hd M η hη _ hℓ).pow _)
  · exact mul_ne_zero (mul_ne_zero (hne m ε hε _) (hne m ε hε _)) (pow_ne_zero _ (hne M η hη _))

theorem aestronglyMeasurable_spatialP {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) :
    AEStronglyMeasurable (spatialP α N m M n ε η p' p) volume := by
  have h := (continuous_powIntegrand_cons hNc m M n hε.ne' hη.ne' p' p).stronglyMeasurable
    |>.integral_prod_right' (ν := (volume : Measure ℝ))
  exact h.aestronglyMeasurable.congr (Eventually.of_forall fun v =>
    integral_time_powIntegrand hNc hNq hNb m M n hε hη p' p v)

/-! ### Step 3: the bound, uniform in the prescriptions and the photon mass -/

/-- **The uniform bound on the closed form**: for `n ≥ 1`, photon masses `M ≥ M₀ > 0`, every
effective prescription and Feynman parameters in the square,
`‖timeP … z v‖ ≤ C (1 + ‖v‖)⁻⁵`. -/
theorem exists_norm_timeP_le {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (α : ℂ) {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, M₀ ≤ M → ∀ ε' : ℝ, ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ∀ v : Fin 3 → ℝ, ‖timeP α N m M n ε' p' p z v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  have hCN0 := nonneg_of_norm_le hNb
  set c0 : ℝ := 3 / 4 * min (M₀ ^ 2) (m ^ 2) with hc0_def
  have hc0 : 0 < c0 := by positivity
  set A0 : ℝ := ‖p'‖ + ‖p‖ with hA0_def
  have hA0 : 0 ≤ A0 := by positivity
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) A0 hc0
  set s1 : ℝ := (n : ℝ) + 3 / 2
  set s2 : ℝ := (n : ℝ) + 5 / 2
  set K1 : ℝ := ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)|
  set K2 : ℝ := CN * (1 + A0) ^ 2 * |energyConst (n + 3)|
  refine ⟨K1 * c1 ^ (-s1) + K2 * c1 ^ (-s2), by positivity, fun M hM ε' z hz v => ?_⟩
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  set W : ℝ := massW m M p' p z v
  have hM0 : M₀ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM₀.le hM 2
  have hD : c0 ≤ feynmanMass m M z.1 z.2 p' p := by
    refine le_trans ?_ (feynmanMass_pos hp' hp hp0' hp0 hz.1 hz.2)
    simp only [c0]
    gcongr
  have hb : ‖(fun k : Fin 3 => shiftK p' p z k.succ)‖ ≤ A0 :=
    (pi_norm_le_iff_of_nonneg hA0).2 fun k =>
      (norm_le_pi_norm (shiftK p' p z) k.succ).trans (norm_shiftK_le p' p hz)
  have hW : c1 * u ^ 2 ≤ W := hcoer v _ _ hb hD
  have hpos : 0 < c1 * u ^ 2 := by positivity
  have hW0 : 0 < W := hpos.trans_le hW
  have hs1 : 0 ≤ s1 := by positivity
  have hs2 : 0 ≤ s2 := by positivity
  have r1 : W ^ (-s1) ≤ c1 ^ (-s1) * u ^ (-(5 : ℝ)) := by
    calc W ^ (-s1) ≤ (c1 * u ^ 2) ^ (-s1) := Real.rpow_le_rpow_of_nonpos hpos hW (by linarith)
      _ = c1 ^ (-s1) * u ^ (-(2 * s1)) := rpow_mul_sq_neg hc1.le hu0
      _ ≤ c1 ^ (-s1) * u ^ (-(5 : ℝ)) := by
          gcongr
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          simp only [s1]; linarith
  have r2 : u ^ 2 * W ^ (-s2) ≤ c1 ^ (-s2) * u ^ (-(5 : ℝ)) := by
    have h1 : W ^ (-s2) ≤ c1 ^ (-s2) * u ^ (-(2 * s2)) := by
      calc W ^ (-s2) ≤ (c1 * u ^ 2) ^ (-s2) := Real.rpow_le_rpow_of_nonpos hpos hW (by linarith)
        _ = c1 ^ (-s2) * u ^ (-(2 * s2)) := rpow_mul_sq_neg hc1.le hu0
    have h2 : u ^ 2 * u ^ (-(2 * s2)) ≤ u ^ (-(5 : ℝ)) := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_add (by linarith)]
      refine Real.rpow_le_rpow_of_exponent_le hu1 ?_
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      simp only [s2]; push_cast; linarith
    calc u ^ 2 * W ^ (-s2) ≤ u ^ 2 * (c1 ^ (-s2) * u ^ (-(2 * s2))) := by gcongr
      _ = c1 ^ (-s2) * (u ^ 2 * u ^ (-(2 * s2))) := by ring
      _ ≤ c1 ^ (-s2) * u ^ (-(5 : ℝ)) := by gcongr
  have hNt : ‖N (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ CN * (1 + A0) ^ 2 * u ^ 2 := by
    refine (hNb _).trans ?_
    have ha : |-shiftK p' p z 0| ≤ A0 := by
      rw [abs_neg]
      exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans
        (norm_shiftK_le p' p hz)
    have h1 := norm_finCons_le (-shiftK p' p z 0) v
    have h2 : 1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ (1 + A0) * u := by
      simp only [u]; nlinarith [norm_nonneg v]
    calc CN * (1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖) ^ 2
        ≤ CN * ((1 + A0) * u) ^ 2 := by gcongr
      _ = CN * (1 + A0) ^ 2 * u ^ 2 := by ring
  have hc1' := norm_cpow_neg_add_mul_I_le (ε := ε') hW0 hs1
  have hc2' := norm_cpow_neg_add_mul_I_le (ε := ε') hW0 hs2
  have hK : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [timeP, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hK, hK]
  calc ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| *
        ‖(-(W : ℂ) + ε' * I) ^ (-((s1 : ℝ) : ℂ))‖ +
      ‖N (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ * |energyConst (n + 3)| *
        ‖(-(W : ℂ) + ε' * I) ^ (-((s2 : ℝ) : ℂ))‖
      ≤ K1 * (c1 ^ (-s1) * u ^ (-(5 : ℝ))) +
        (CN * (1 + A0) ^ 2 * u ^ 2) * |energyConst (n + 3)| * W ^ (-s2) := by
        gcongr
        · exact hc1'.trans r1
    _ = K1 * (c1 ^ (-s1) * u ^ (-(5 : ℝ))) + K2 * (u ^ 2 * W ^ (-s2)) := by
        simp only [K2]; ring
    _ ≤ K1 * (c1 ^ (-s1) * u ^ (-(5 : ℝ))) + K2 * (c1 ^ (-s2) * u ^ (-(5 : ℝ))) := by
        gcongr
    _ = (K1 * c1 ^ (-s1) + K2 * c1 ^ (-s2)) * u ^ (-(5 : ℝ)) := by ring

theorem feynmanMeasure_real_univ : feynmanMeasure.real univ = 1 := by
  rw [Measure.real, feynmanMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
  simp

theorem norm_spatialP_le {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M : ℝ} {n : ℕ} {ε η : ℝ}
    {p' p : Fin 4 → ℝ} {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeP α N m M n (effEps ε η z) p' p z v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ)))
    (v : Fin 3 → ℝ) :
    ‖spatialP α N m M n ε η p' p v‖ ≤ (n + 1) * (n + 2) * C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  have h := norm_integral_le_of_norm_le_const (μ := feynmanMeasure)
    (f := fun z => feynWt n z * timeP α N m M n (effEps ε η z) p' p z v)
    (C := (n + 1) * (n + 2) * (C * (1 + ‖v‖) ^ (-(5 : ℝ))))
    (ae_feynmanMeasure.mono fun z hz => by
      have hzI := Ioc_prod_subset hz
      rw [norm_mul]
      exact mul_le_mul (feynWt_norm_le hzI.2) (hC z hzI v) (norm_nonneg _) (by positivity))
  rw [feynmanMeasure_real_univ, mul_one] at h
  refine h.trans (le_of_eq ?_)
  ring

/-! ### Step 4: the energy-first integral and its limit -/

/-- **The energy-first integral in parametric form**, with both stages integrable. -/
theorem energyFirstIntegral_powIntegrand_eq {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N)
    {α : ℂ} (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) :
    energyFirstIntegral (powIntegrand N m M n ε η p' p) = ∫ v, spatialP α N m M n ε η p' p v :=
  integral_congr_ae (Eventually.of_forall fun v =>
    integral_time_powIntegrand hNc hNq hNb m M n hε hη p' p v)

theorem integrable_spatialP {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {n : ℕ} (hn : 1 ≤ n) {M : ℝ}
    (hM : M₀ ≤ M) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    Integrable (spatialP α N m M n ε η p' p) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb hn
  have h := integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5) (by simp; norm_num)
  exact (h.const_mul ((n + 1) * (n + 2) * C)).mono'
    (aestronglyMeasurable_spatialP hNc hNq hNb m M n hε hη p' p)
    (Eventually.of_forall fun v => norm_spatialP_le
      (fun z hz v => hC M hM _ z hz v) v)

/-- `(-W + ε i)^s → (-W₀)^s` when `W → W₀ > 0` and `ε → 0` with `ε ≥ 0`. -/
theorem tendsto_cpow_neg_add_mul_I_of {ι : Type*} {l : Filter ι} {W e : ι → ℝ} {W₀ : ℝ}
    (hW₀ : 0 < W₀) (hW : Tendsto W l (𝓝 W₀)) (he : Tendsto e l (𝓝 0))
    (he0 : ∀ᶠ i in l, 0 ≤ e i) (s : ℂ) :
    Tendsto (fun i => (-(W i : ℂ) + e i * I) ^ s) l (𝓝 ((-(W₀ : ℂ)) ^ s)) := by
  have hre : (-(W₀ : ℂ)).re < 0 := by simp [hW₀]
  have him : (-(W₀ : ℂ)).im = 0 := by simp
  have hpath : Tendsto (fun i => -(W i : ℂ) + e i * I) l
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(W₀ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun i => -(W i : ℂ) + e i * I) l (𝓝 (-(W₀ : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
        ((continuous_ofReal.tendsto _).comp hW).neg.add
          (((continuous_ofReal.tendsto _).comp he).mul_const I)
      rwa [ofReal_zero, zero_mul, add_zero] at h
    · filter_upwards [he0] with i hi
      simpa using hi
  have hWpos : ∀ᶠ i in l, 0 < W i := hW.eventually (lt_mem_nhds hW₀)
  have hlog := (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto.comp hpath
  have hexp := (continuous_exp.tendsto _).comp (hlog.mul_const s)
  rw [cpow_def_of_ne_zero (by simpa using hW₀.ne')]
  refine hexp.congr' (hWpos.mono fun i hi => ?_)
  simp only [Function.comp_apply]
  have hne : -(W i : ℂ) + e i * I ≠ 0 := fun h => by
    have := congrArg re h
    simp at this
    linarith
  rw [cpow_def_of_ne_zero hne]

theorem continuous_massW_mass (m : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (v : Fin 3 → ℝ) :
    Continuous fun M => massW m M p' p z v := by
  unfold massW feynmanMass
  fun_prop

theorem continuous_massW_joint (m M : ℝ) (p' p : Fin 4 → ℝ) :
    Continuous fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => massW m M p' p q.2 q.1 := by
  have h1 := continuous_shiftK p' p
  have h2 := continuous_feynmanMass m M p' p
  unfold massW
  fun_prop

/-- Joint measurability of the closed form in `(v, z)`, for every `ε, η`. -/
theorem measurable_timeP {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ) (m M : ℝ)
    (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      feynWt n q.2 * timeP α N m M n (effEps ε η q.2) p' p q.2 q.1 := by
  have hW := continuous_massW_joint m M p' p
  have hW' : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => massW m M p' p q.2 q.1 := hW.measurable
  have hc : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      (Fin.cons (-shiftK p' p q.2 0) q.1 : Fin 4 → ℝ) :=
    (Continuous.finCons (A := fun _ : Fin 4 => ℝ)
      (((continuous_apply 0).comp (continuous_shiftK p' p)).neg.comp continuous_snd)
      continuous_fst).measurable
  have hN : Measurable N := hNc.measurable
  have hf' : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => feynWt n q.2 :=
    ((continuous_feynWt n).comp continuous_snd).measurable
  unfold timeP effEps
  fun_prop

/-- Joint measurability of the closed form in `((M, v), z)`, the photon mass varying. -/
theorem measurable_timeP_mass {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ) (m : ℝ)
    (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) =>
      feynWt n q.2 * timeP α N m q.1.1 n (effEps ε η q.2) p' p q.2 q.1.2 := by
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
  have hf' : Measurable fun q : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) => feynWt n q.2 :=
    ((continuous_feynWt n).comp continuous_snd).measurable
  unfold timeP effEps
  fun_prop

theorem aestronglyMeasurable_spatialP' {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ)
    (m M : ℝ) (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    AEStronglyMeasurable (spatialP α N m M n ε η p' p) volume :=
  ((measurable_timeP hNc α m M n ε η p' p).aestronglyMeasurable
    (μ := (volume : Measure (Fin 3 → ℝ)).prod feynmanMeasure)).integral_prod_right'

/-- **Convergence of the spatial integral**: along any countably generated filter on which
`ε, η → 0` with `ε, η ≥ 0` and `M → M_*` with `M ≥ M₀ > 0`, `∫ spatialP(ε, η, M)` tends to
`∫ spatialP(0, 0, M_*)`. In particular the limit is continuous in the photon mass. -/
theorem tendsto_integral_spatialP {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {n : ℕ} (hn : 1 ≤ n)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε η M : ι → ℝ} {Ms : ℝ}
    (hε : Tendsto ε l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (hε0 : ∀ᶠ i in l, 0 ≤ ε i)
    (hη0 : ∀ᶠ i in l, 0 ≤ η i) (hM : Tendsto M l (𝓝 Ms)) (hMge : ∀ᶠ i in l, M₀ ≤ M i) :
    Tendsto (fun i => ∫ v, spatialP α N m (M i) n (ε i) (η i) p' p v) l
      (𝓝 (∫ v, spatialP α N m Ms n 0 0 p' p v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb hn
  have hMs : M₀ ≤ Ms := ge_of_tendsto hM hMge
  have hMspos : 0 < Ms := hM₀.trans_le hMs
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul ((n + 1) * (n + 2) * C)
  -- the pointwise limit in `v`
  have hpt : ∀ v : Fin 3 → ℝ, Tendsto (fun i => spatialP α N m (M i) n (ε i) (η i) p' p v) l
      (𝓝 (spatialP α N m Ms n 0 0 p' p v)) := by
    intro v
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (n + 1) * (n + 2) * C)
      ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun i =>
        ((measurable_timeP hNc α m (M i) n (ε i) (η i) p' p).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [hMge] with i hi
      refine ae_feynmanMeasure.mono fun z hz => ?_
      have hzI := Ioc_prod_subset hz
      have hu : (1 + ‖v‖) ^ (-(5 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
      rw [norm_mul]
      calc ‖feynWt n z‖ * ‖timeP α N m (M i) n (effEps (ε i) (η i) z) p' p z v‖
          ≤ ((n + 1) * (n + 2)) * (C * 1) :=
            mul_le_mul (feynWt_norm_le hzI.2) ((hC (M i) hi _ z hzI v).trans
              (mul_le_mul_of_nonneg_left hu hC0)) (norm_nonneg _) (by positivity)
        _ = (n + 1) * (n + 2) * C := by ring
    · refine ae_feynmanMeasure.mono fun z hz => ?_
      have hzI := Ioc_prod_subset hz
      have hW₀ := massW_pos hm hMspos hp' hp hp0' hp0 hzI v
      have hWt : Tendsto (fun i => massW m (M i) p' p z v) l (𝓝 (massW m Ms p' p z v)) :=
        ((continuous_massW_mass m p' p z v).tendsto Ms).comp hM
      have he : Tendsto (fun i => effEps (ε i) (η i) z) l (𝓝 0) := by
        have := (hε.const_mul z.2).add (hη.const_mul (1 - z.2))
        simpa [effEps] using this
      have he0 : ∀ᶠ i in l, 0 ≤ effEps (ε i) (η i) z := by
        filter_upwards [hε0, hη0] with i h1 h2
        exact effEps_nonneg h1 h2 hzI.2
      have l1 := tendsto_cpow_neg_add_mul_I_of hW₀ hWt he he0 (-(((n : ℝ) + 3 / 2 : ℝ) : ℂ))
      have l2 := tendsto_cpow_neg_add_mul_I_of hW₀ hWt he he0 (-(((n : ℝ) + 5 / 2 : ℝ) : ℂ))
      have h0 : timeP α N m Ms n (effEps 0 0 z) p' p z v =
          (-1) ^ (n + 3) * (α * ((energyConst (n + 2) - energyConst (n + 3) : ℝ) : ℂ) *
            (-(massW m Ms p' p z v : ℂ)) ^ (-(((n : ℝ) + 3 / 2 : ℝ) : ℂ)) +
          N (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) * (energyConst (n + 3) : ℂ) *
            (-(massW m Ms p' p z v : ℂ)) ^ (-(((n : ℝ) + 5 / 2 : ℝ) : ℂ))) := by
        simp [timeP, effEps]
      rw [h0]
      unfold timeP
      exact (((l1.const_mul _).add (l2.const_mul _)).const_mul _).const_mul _
  -- dominated convergence in `v`
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbnd
    (Eventually.of_forall hpt)
  · exact Eventually.of_forall fun i => aestronglyMeasurable_spatialP' hNc α m (M i) n _ _ p' p
  · filter_upwards [hMge] with i hi
    exact Eventually.of_forall fun v => norm_spatialP_le
      (fun z hz v => hC (M i) hi _ z hz v) v

/-- **The limit**: along any countably generated filter on which `ε → 0⁺`, `η → 0⁺` and
`M → M_*` with `M ≥ M₀ > 0` eventually, the energy-first integral of `powIntegrand` tends to
`∫ spatialP(ε = η = 0, M_*)`. -/
theorem tendsto_energyFirstIntegral_powIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {n : ℕ} (hn : 1 ≤ n)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε η M : ι → ℝ} {Ms : ℝ}
    (hε : Tendsto ε l (𝓝[>] 0)) (hη : Tendsto η l (𝓝[>] 0)) (hM : Tendsto M l (𝓝 Ms))
    (hMge : ∀ᶠ i in l, M₀ ≤ M i) :
    Tendsto (fun i => energyFirstIntegral (powIntegrand N m (M i) n (ε i) (η i) p' p)) l
      (𝓝 (∫ v, spatialP α N m Ms n 0 0 p' p v)) := by
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε (self_mem_nhdsWithin)
  have hηpos : ∀ᶠ i in l, 0 < η i := hη (self_mem_nhdsWithin)
  have hlim := tendsto_integral_spatialP hm hM₀ hp' hp hp0' hp0 hNc α hNb hn
    (hε.mono_right nhdsWithin_le_nhds) (hη.mono_right nhdsWithin_le_nhds)
    (hεpos.mono fun _ h => h.le) (hηpos.mono fun _ h => h.le) hM hMge
  refine hlim.congr' ?_
  filter_upwards [hεpos, hηpos] with i h1 h2
  exact (energyFirstIntegral_powIntegrand_eq hNc hNq hNb m (M i) n h1 h2 p' p).symm

end QED.TwoLoop.VPHalfAtLimit

end
