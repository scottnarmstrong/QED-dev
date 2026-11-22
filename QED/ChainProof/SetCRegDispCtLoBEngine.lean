/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitEngine
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop vertex with a doubled electron denominator: the `ε → 0⁺` engine

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c) (placements
`k = 0, 1`). On the open line `d` the mass part of the self-energy insertion is
`b ∂S/∂m_d = b (1/D - 2m A/D²)`, so its outer one-loop vertex has the electron denominator of
the line `d` **twice**:

`F(ℓ) = N(ℓ) / (D_m(p' + ℓ; ε) D_m(p + ℓ; ε) D_m(ℓ_d; ε) D_M(ℓ; η)^{n+1})` (`dblIntegrand`),

`ℓ_d = p + ℓ` (`d = 0`, incoming) or `p' + ℓ` (`d = 1`, outgoing). This file is the analogue of
`QED/TwoLoop/VPHalfAtLimitEngine.lean` for `F`.

**Reduction.** Feynman parameters give the same combined denominator `combDen` as for the
undoubled vertex, to the power `n + 4` instead of `n + 3`, with the weight
`(n+1)(n+2)(n+3) x_d y² (1-y)^n` (`dblWt`; `x_1 = x`, `x_0 = 1 - x`) instead of
`(n+1)(n+2) y (1-y)^n`. The energy integral at fixed parameters is therefore the closed form
`QED.TwoLoop.VPHalfAtLimit.timeP` **of order `n + 1`**, whose uniform bound
`QED.TwoLoop.VPHalfAtLimit.exists_norm_timeP_le` needs `1 ≤ n + 1` only: a single photon
denominator is allowed. All later steps of the engine only use that the weight is continuous and
bounded on the square; they are restated here for any such weight (`jointW`, `spatialW`).

## Main statements

* `inv_sq_mul_eq_integral_feynman_out`, `inv_mul_sq_eq_integral_feynman_in`,
  `inv_cube_mul_pow_eq_integral_feynman`: the one-variable Feynman identities;
* **`inv_dbl_eq_integral_feynmanMeasure`**: `1/(A B L_d C^{n+1})` against `feynmanMeasure`;
* `integral_time_jointW`, `integrable_jointW`, `norm_spatialW_le`, **`tendsto_integral_spatialW`**:
  the engine for a continuous bounded weight;
* **`integral_time_dblIntegrand`**: the energy integral of `dblIntegrand` is
  `spatialW (dblWt d n) … (n + 1)`;
* **`tendsto_energyFirstIntegral_dblIntegrand`**: along any countably generated filter with
  `ε, η → 0⁺` and `M → M_*`, `M ≥ M₀ > 0`, the energy-first integral of `dblIntegrand` tends to
  `∫ spatialW (dblWt d n) (ε = η = 0, M_*)`, for every `n` (including `n = 0`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit

/-! ### One-variable Feynman identities -/

/-- **The outgoing line doubled**: `1/(A² B) = ∫₀¹ 2x (xA + (1-x)B)⁻³ dx`. -/
theorem inv_sq_mul_eq_integral_feynman_out {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, (x : ℂ) * A + (1 - x) * B ≠ 0) :
    (A ^ 2 * B)⁻¹ = ∫ x in (0 : ℝ)..1, (2 * (x : ℂ)) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  set G : ℂ → ℂ := fun w => (w / (w * A + (1 - w) * B)) ^ 2 / B with hG
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => G x)
      ((2 * (x : ℂ)) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ)) x := by
    intro x hx
    have hL := h x (hI ▸ hx)
    have hLd : HasDerivAt (fun w : ℂ => w * A + (1 - w) * B) (A - B) x := by
      have := ((hasDerivAt_id' (x := (x : ℂ))).mul_const A).fun_add
        (((hasDerivAt_id' (x := (x : ℂ))).const_sub 1).mul_const B)
      convert this using 1; ring
    have hL2 : (x : ℂ) * A - x * B + B ≠ 0 := by
      rwa [show (x : ℂ) * A - x * B + B = (x : ℂ) * A + (1 - x) * B by ring]
    have hg := (hasDerivAt_id' (x := (x : ℂ))).fun_div hLd hL
    have hG' := (hg.fun_pow 2).div_const B
    refine HasDerivAt.comp_ofReal (e := G) ?_
    convert hG' using 1
    rw [zpow_neg, zpow_ofNat]
    simp only [div_pow]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => (2 * (x : ℂ)) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ))
      (uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop)
      (ContinuousOn.zpow₀ (by fun_prop) _ fun x hx => Or.inl (h x (hI ▸ hx)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG, ofReal_one, ofReal_zero, sub_self, zero_mul, one_mul, add_zero, zero_div,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  field_simp

/-- **The incoming line doubled**: `1/(A B²) = ∫₀¹ 2(1-x) (xA + (1-x)B)⁻³ dx`. -/
theorem inv_mul_sq_eq_integral_feynman_in {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, (x : ℂ) * A + (1 - x) * B ≠ 0) :
    (A * B ^ 2)⁻¹ =
      ∫ x in (0 : ℝ)..1, (2 * (1 - (x : ℂ))) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  set G : ℂ → ℂ := fun w => -((1 - w) / (w * A + (1 - w) * B)) ^ 2 / A with hG
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => G x)
      ((2 * (1 - (x : ℂ))) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ)) x := by
    intro x hx
    have hL := h x (hI ▸ hx)
    have hLd : HasDerivAt (fun w : ℂ => w * A + (1 - w) * B) (A - B) x := by
      have := ((hasDerivAt_id' (x := (x : ℂ))).mul_const A).fun_add
        (((hasDerivAt_id' (x := (x : ℂ))).const_sub 1).mul_const B)
      convert this using 1; ring
    have hL2 : (x : ℂ) * A - x * B + B ≠ 0 := by
      rwa [show (x : ℂ) * A - x * B + B = (x : ℂ) * A + (1 - x) * B by ring]
    have hg := ((hasDerivAt_id' (x := (x : ℂ))).const_sub 1).fun_div hLd hL
    have hG' := ((hg.fun_pow 2).fun_neg).div_const A
    refine HasDerivAt.comp_ofReal (e := G) ?_
    convert hG' using 1
    rw [zpow_neg, zpow_ofNat]
    simp only [div_pow]
    field_simp
    ring
  have hcont : ContinuousOn
      (fun x : ℝ => (2 * (1 - (x : ℂ))) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ)) (uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop)
      (ContinuousOn.zpow₀ (by fun_prop) _ fun x hx => Or.inl (h x (hI ▸ hx)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG, ofReal_one, ofReal_zero, sub_self, zero_mul, one_mul, zero_add, sub_zero,
    zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero]
  field_simp
  ring

/-- **A cube against a power**:
`1/(X³ C^{n+1}) = ((n+1)(n+2)(n+3)/2) ∫₀¹ y² (1-y)^n (yX + (1-y)C)^{-(n+4)} dy`. -/
theorem inv_cube_mul_pow_eq_integral_feynman {X C : ℂ} (hX : X ≠ 0) (hC : C ≠ 0) (n : ℕ)
    (h : ∀ y ∈ Icc (0 : ℝ) 1, (y : ℂ) * X + (1 - y) * C ≠ 0) :
    (X ^ 3 * C ^ (n + 1))⁻¹ = ∫ y in (0 : ℝ)..1,
      ((n + 1) * (n + 2) * (n + 3) / 2 : ℂ) * ((y : ℂ) ^ 2 * (1 - y) ^ n) *
        ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 4 : ℕ) : ℤ)) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hn3 : (n : ℂ) + 3 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 2)
  set G : ℂ → ℂ := fun w => ((n + 1) * (n + 2) * (n + 3) / 2 : ℂ) * (X ^ 3)⁻¹ *
    (-((1 - w) / (w * X + (1 - w) * C)) ^ (n + 1) / (n + 1) +
      2 * C * ((1 - w) / (w * X + (1 - w) * C)) ^ (n + 2) / (n + 2) -
      C ^ 2 * ((1 - w) / (w * X + (1 - w) * C)) ^ (n + 3) / (n + 3)) with hG
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => G y)
      (((n + 1) * (n + 2) * (n + 3) / 2 : ℂ) * ((y : ℂ) ^ 2 * (1 - y) ^ n) *
        ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 4 : ℕ) : ℤ))) y := by
    intro y hy
    have hL := h y (hI ▸ hy)
    have hLd : HasDerivAt (fun w : ℂ => w * X + (1 - w) * C) (X - C) y := by
      have := ((hasDerivAt_id' (x := (y : ℂ))).mul_const X).fun_add
        (((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).mul_const C)
      convert this using 1; ring
    have hg := ((hasDerivAt_id' (x := (y : ℂ))).const_sub 1).fun_div hLd hL
    have hG' := (((((hg.fun_pow (n + 1)).fun_neg).div_const ((n : ℂ) + 1)).fun_add
      (((hg.fun_pow (n + 2)).const_mul (2 * C)).div_const ((n : ℂ) + 2))).fun_sub
      (((hg.fun_pow (n + 3)).const_mul (C ^ 2)).div_const ((n : ℂ) + 3))).const_mul
      (((n + 1) * (n + 2) * (n + 3) / 2 : ℂ) * (X ^ 3)⁻¹)
    refine HasDerivAt.comp_ofReal (e := G) ?_
    convert hG' using 1
    rw [zpow_neg, zpow_natCast]
    push_cast
    simp only [div_pow]
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => ((n + 1) * (n + 2) * (n + 3) / 2 : ℂ) *
      ((y : ℂ) ^ 2 * (1 - y) ^ n) *
      ((y : ℂ) * X + (1 - y) * C) ^ (-((n + 4 : ℕ) : ℤ))) (uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop)
      (ContinuousOn.zpow₀ (by fun_prop) _ fun y hy => Or.inl (h y (hI ▸ hy)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG, ofReal_one, ofReal_zero, sub_self, zero_div, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, neg_zero, zero_add,
    sub_zero, zero_mul, one_mul]
  simp only [inv_pow, one_div]
  field_simp
  ring

/-! ### Two parameters -/

/-- The weight `x_d` of the doubled line: `x` for the outgoing line `d = 1`, `1 - x` for the
incoming line `d = 0`. -/
def dblLineWt (d : Fin 2) (x : ℝ) : ℝ := if d = 0 then 1 - x else x

/-- The momentum `ℓ_d` of the doubled line: `p + ℓ` (`d = 0`) or `p' + ℓ` (`d = 1`). -/
def dblMom (d : Fin 2) (p' p ℓ : Fin 4 → ℝ) : Fin 4 → ℝ := if d = 0 then p + ℓ else p' + ℓ

/-- The Feynman weight `(n+1)(n+2)(n+3) x_d y² (1-y)^n` of the doubled vertex. -/
noncomputable def dblWt (d : Fin 2) (n : ℕ) (z : ℝ × ℝ) : ℂ :=
  ((n + 1) * (n + 2) * (n + 3) : ℂ) * (dblLineWt d z.1 : ℂ) * ((z.2 : ℂ) ^ 2 * (1 - z.2) ^ n)

theorem continuous_dblWt (d : Fin 2) (n : ℕ) : Continuous (dblWt d n) := by
  unfold dblWt dblLineWt
  split_ifs <;> fun_prop

theorem dblLineWt_mem_Icc (d : Fin 2) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    dblLineWt d x ∈ Icc (0 : ℝ) 1 := by
  unfold dblLineWt
  split_ifs
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · exact hx

theorem dblWt_norm_le (d : Fin 2) (n : ℕ) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ‖dblWt d n z‖ ≤ (n + 1) * (n + 2) * (n + 3) := by
  have hy0 := hz.2.1
  have hy1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hx := dblLineWt_mem_Icc d hz.1
  have e : dblWt d n z = (((n + 1) * (n + 2) * (n + 3) *
      (dblLineWt d z.1 * (z.2 ^ 2 * (1 - z.2) ^ n)) : ℝ) : ℂ) := by
    simp only [dblWt]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
    have := hx.1; positivity)]
  have h1 : z.2 ^ 2 * (1 - z.2) ^ n ≤ 1 := by
    have a := pow_le_one₀ hy1 (by linarith [hz.2.1] : 1 - z.2 ≤ 1) (n := n)
    have b := pow_le_one₀ hy0 hz.2.2 (n := 2)
    calc z.2 ^ 2 * (1 - z.2) ^ n ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have h2 : dblLineWt d z.1 * (z.2 ^ 2 * (1 - z.2) ^ n) ≤ 1 := by
    calc dblLineWt d z.1 * (z.2 ^ 2 * (1 - z.2) ^ n) ≤ 1 * 1 :=
          mul_le_mul hx.2 h1 (by positivity) zero_le_one
      _ = 1 := by ring
  calc (n + 1) * (n + 2) * (n + 3) * (dblLineWt d z.1 * (z.2 ^ 2 * (1 - z.2) ^ n))
      ≤ (n + 1) * (n + 2) * (n + 3) * 1 := by gcongr
    _ = _ := by ring

/-- `1/(A B L_d)` as an interval integral, `L_1 = A`, `L_0 = B`. -/
theorem inv_dbl_eq_integral_feynman_two {A B : ℂ} (hA : A.im < 0) (hB : B.im < 0) (d : Fin 2) :
    (A * B * (if d = 0 then B else A))⁻¹ = ∫ x in (0 : ℝ)..1,
      (2 * (dblLineWt d x : ℂ)) * ((x : ℂ) * A + (1 - x) * B) ^ (-3 : ℤ) := by
  have hc : ∀ x ∈ Icc (0 : ℝ) 1, (x : ℂ) * A + (1 - x) * B ≠ 0 :=
    fun x hx => convex_combo_ne_zero hA hB hx
  by_cases hd : d = 0
  · simp only [hd, ↓reduceIte, dblLineWt]
    rw [show A * B * B = A * B ^ 2 by ring,
      inv_mul_sq_eq_integral_feynman_in (ne_zero_of_im_neg hA) (ne_zero_of_im_neg hB) hc]
    push_cast
    rfl
  · simp only [hd, ↓reduceIte, dblLineWt]
    rw [show A * B * A = A ^ 2 * B by ring,
      inv_sq_mul_eq_integral_feynman_out (ne_zero_of_im_neg hA) (ne_zero_of_im_neg hB) hc]

/-- The doubled Feynman integrand is integrable against `feynmanMeasure`. -/
theorem integrable_feynmanMeasure_dbl {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) (d : Fin 2) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => dblWt d n z *
      ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-((n + 4 : ℕ) : ℤ)))
      feynmanMeasure := by
  have hcont : ContinuousOn (fun z : ℝ × ℝ => dblWt d n z *
      ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-((n + 4 : ℕ) : ℤ)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.mul (continuous_dblWt d n).continuousOn
      (ContinuousOn.zpow₀ (by fun_prop) _ fun z hz =>
        Or.inl (ne_zero_of_im_neg (im_feynman_combo_neg hA hB hC hz)))
  rw [feynmanMeasure_eq]
  exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- **The doubled vertex in Feynman parameters**, against `feynmanMeasure`:
`1/(A B L_d C^{n+1}) = ∫ dblWt d n z (y(xA + (1-x)B) + (1-y)C)^{-(n+4)}`. -/
theorem inv_dbl_eq_integral_feynmanMeasure {A B C : ℂ} (hA : A.im < 0) (hB : B.im < 0)
    (hC : C.im < 0) (d : Fin 2) (n : ℕ) :
    (A * B * (if d = 0 then B else A) * C ^ (n + 1))⁻¹ = ∫ z, dblWt d n z *
      ((z.2 : ℂ) * ((z.1 : ℂ) * A + (1 - z.1) * B) + (1 - z.2) * C) ^ (-((n + 4 : ℕ) : ℤ))
        ∂feynmanMeasure := by
  have hint := integrable_feynmanMeasure_dbl hA hB hC d n
  rw [feynmanMeasure] at hint ⊢
  rw [integral_prod _ hint, mul_inv, inv_dbl_eq_integral_feynman_two hA hB d,
    ← intervalIntegral.integral_mul_const]
  simp_rw [← intervalIntegral.integral_of_le zero_le_one]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hL := im_convex_combo_neg hA hB hx
  have e := inv_cube_mul_pow_eq_integral_feynman (ne_zero_of_im_neg hL) (ne_zero_of_im_neg hC) n
    fun y hy => convex_combo_ne_zero hL hC hy
  rw [zpow_neg, zpow_ofNat, mul_assoc, ← mul_inv, e, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [dblWt]
  ring

/-! ### The engine for a continuous bounded weight -/

section Weight

variable (w : ℝ × ℝ → ℂ)

/-- The integrand on `ℝ × [0,1]²` with weight `w`, at fixed spatial momentum `v`. -/
noncomputable def jointW (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  N (Fin.cons q.1 v : Fin 4 → ℝ) * (w q.2 *
    combDen m M (effEps ε η q.2) p' p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-((n + 3 : ℕ) : ℤ)))

/-- The energy integral after the Feynman-parameter integral, with weight `w`. -/
noncomputable def spatialW (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ)
    (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) : ℂ :=
  ∫ z, w z * timeP α N m M n (effEps ε η z) p' p z v ∂feynmanMeasure

variable {w}

theorem continuousOn_jointW (hw : Continuous w) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N)
    (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ContinuousOn (jointW w N m M n ε η p' p v)
      (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
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
  have hW := hw.comp (continuous_snd : Continuous fun q : ℝ × (ℝ × ℝ) => q.2)
  refine (hN.continuousOn.mul (hW.continuousOn.mul (hD.continuousOn.zpow₀ _ fun q hq => ?_)))
  left
  intro h0
  have him := combDen_cons_im m M (effEps ε η q.2) p' p q.2 q.1 v
  rw [h0, zero_im] at him
  have := effEps_pos hε hη hq.2.2
  linarith

theorem aestronglyMeasurable_jointW (hw : Continuous w) {N : (Fin 4 → ℝ) → ℂ}
    (hNc : Continuous N) (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    AEStronglyMeasurable (jointW w N m M n ε η p' p v)
      ((volume : Measure ℝ).prod feynmanMeasure) := by
  rw [volume_prod_feynmanMeasure]
  exact ((continuousOn_jointW hw hNc m M n hε hη p' p v).mono
    (prod_mono subset_rfl Ioc_prod_subset)).aestronglyMeasurable
    (MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Ioc))

theorem integrable_jointW (hw : Continuous w) {Cw : ℝ}
    (hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖w z‖ ≤ Cw) {N : (Fin 4 → ℝ) → ℂ}
    (hNc : Continuous N) {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable (jointW w N m M n ε η p' p v) ((volume : Measure ℝ).prod feynmanMeasure) := by
  have hCN0 := nonneg_of_norm_le hNb
  obtain ⟨CW, hCW⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_massW m M p' p v).continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  set ε₀ := min ε η
  have hε₀ : 0 < ε₀ := lt_min hε hη
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε₀ (‖p'‖ + ‖p‖) CW
  set G : ℝ := CN * (2 * (1 + ‖v‖) ^ 2) * Cw * (c ^ (n + 3))⁻¹
  refine Integrable.mono' (g := fun q : ℝ × (ℝ × ℝ) => G * (1 + q.1 ^ 2)⁻¹ * 1) ?_
    (aestronglyMeasurable_jointW hw hNc m M n hε hη p' p v)
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
  have hwz := hwb z hzI
  rw [jointW, norm_mul, norm_mul, mul_one]
  calc ‖N (Fin.cons t v : Fin 4 → ℝ)‖ * (‖w z‖ *
        ‖combDen m M (effEps ε η z) p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-((n + 3 : ℕ) : ℤ))‖)
      ≤ (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        (Cw * ((c ^ (n + 3))⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹)) := by
        gcongr
        exact (norm_nonneg _).trans hwz
    _ = G * (1 + t ^ 2)⁻¹ := by
        simp only [G]; field_simp

/-- **The energy integral at fixed Feynman parameters**, in closed form, with weight `w`. -/
theorem integral_time_jointW {N : (Fin 4 → ℝ) → ℂ} {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ∫ t : ℝ, jointW w N m M n ε η p' p v (t, z) =
      w z * timeP α N m M n (effEps ε η z) p' p z v := by
  obtain ⟨β, γ, h⟩ := hNq v
  have hε' := effEps_pos hε hη hz.2
  set Z : ℂ := -(massW m M p' p z v : ℂ) + (effEps ε η z : ℂ) * I with hZ
  have hZs : Z ∈ slitPlane := mem_slitPlane_of_pos hε' _
  set a : ℝ := shiftK p' p z 0
  have hpt : ∀ t : ℝ, jointW w N m M n ε η p' p v (t, z) =
      (w z * (-1) ^ (n + 3)) *
        ((α * (t : ℂ) ^ 2 + β * t + γ) * (((t : ℂ) + a) ^ 2 + Z) ^ (-((n + 1 + 2 : ℕ) : ℤ))) := by
    intro t
    simp only [jointW]
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

/-- Joint measurability of the weighted closed form in `(v, z)`. -/
theorem measurable_timeW (hw : Continuous w) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N)
    (α : ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      w q.2 * timeP α N m M n (effEps ε η q.2) p' p q.2 q.1 := by
  have hW := continuous_massW_joint m M p' p
  have hW' : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => massW m M p' p q.2 q.1 := hW.measurable
  have hc : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      (Fin.cons (-shiftK p' p q.2 0) q.1 : Fin 4 → ℝ) :=
    (Continuous.finCons (A := fun _ : Fin 4 => ℝ)
      (((continuous_apply 0).comp (continuous_shiftK p' p)).neg.comp continuous_snd)
      continuous_fst).measurable
  have hN : Measurable N := hNc.measurable
  have hf' : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => w q.2 :=
    (hw.comp continuous_snd).measurable
  unfold timeP effEps
  fun_prop

theorem aestronglyMeasurable_spatialW (hw : Continuous w) {N : (Fin 4 → ℝ) → ℂ}
    (hNc : Continuous N) (α : ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    AEStronglyMeasurable (spatialW w α N m M n ε η p' p) volume :=
  ((measurable_timeW hw hNc α m M n ε η p' p).aestronglyMeasurable
    (μ := (volume : Measure (Fin 3 → ℝ)).prod feynmanMeasure)).integral_prod_right'

theorem norm_spatialW_le {Cw : ℝ} (hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖w z‖ ≤ Cw)
    {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M : ℝ} {n : ℕ} {ε η : ℝ} {p' p : Fin 4 → ℝ} {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeP α N m M n (effEps ε η z) p' p z v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ)))
    (v : Fin 3 → ℝ) :
    ‖spatialW w α N m M n ε η p' p v‖ ≤ Cw * C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  have h := norm_integral_le_of_norm_le_const (μ := feynmanMeasure)
    (f := fun z => w z * timeP α N m M n (effEps ε η z) p' p z v)
    (C := Cw * (C * (1 + ‖v‖) ^ (-(5 : ℝ))))
    (ae_feynmanMeasure.mono fun z hz => by
      have hzI := Ioc_prod_subset hz
      rw [norm_mul]
      exact mul_le_mul (hwb z hzI) (hC z hzI v) (norm_nonneg _)
        ((norm_nonneg _).trans (hwb z hzI)))
  rw [feynmanMeasure_real_univ, mul_one] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Convergence of the spatial integral with weight `w`**: along any countably generated
filter on which `ε, η → 0` with `ε, η ≥ 0` and `M → M_*` with `M ≥ M₀ > 0`, the integral of
`spatialW w (ε, η, M)` tends to that of `spatialW w (0, 0, M_*)`. -/
theorem tendsto_integral_spatialW (hw : Continuous w) {Cw : ℝ}
    (hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖w z‖ ≤ Cw) {m M₀ : ℝ} (hm : 0 < m)
    (hM₀ : 0 < M₀) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {n : ℕ} (hn : 1 ≤ n)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε η M : ι → ℝ} {Ms : ℝ}
    (hε : Tendsto ε l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (hε0 : ∀ᶠ i in l, 0 ≤ ε i)
    (hη0 : ∀ᶠ i in l, 0 ≤ η i) (hM : Tendsto M l (𝓝 Ms)) (hMge : ∀ᶠ i in l, M₀ ≤ M i) :
    Tendsto (fun i => ∫ v, spatialW w α N m (M i) n (ε i) (η i) p' p v) l
      (𝓝 (∫ v, spatialW w α N m Ms n 0 0 p' p v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb hn
  have hMs : M₀ ≤ Ms := ge_of_tendsto hM hMge
  have hMspos : 0 < Ms := hM₀.trans_le hMs
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (Cw * C)
  have hpt : ∀ v : Fin 3 → ℝ, Tendsto (fun i => spatialW w α N m (M i) n (ε i) (η i) p' p v) l
      (𝓝 (spatialW w α N m Ms n 0 0 p' p v)) := by
    intro v
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Cw * C)
      ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun i =>
        ((measurable_timeW hw hNc α m (M i) n (ε i) (η i) p' p).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [hMge] with i hi
      refine ae_feynmanMeasure.mono fun z hz => ?_
      have hzI := Ioc_prod_subset hz
      have hu : (1 + ‖v‖) ^ (-(5 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
      rw [norm_mul]
      calc ‖w z‖ * ‖timeP α N m (M i) n (effEps (ε i) (η i) z) p' p z v‖
          ≤ Cw * (C * 1) :=
            mul_le_mul (hwb z hzI) ((hC (M i) hi _ z hzI v).trans
              (mul_le_mul_of_nonneg_left hu hC0)) (norm_nonneg _)
              ((norm_nonneg _).trans (hwb z hzI))
        _ = Cw * C := by ring
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
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbnd
    (Eventually.of_forall hpt)
  · exact Eventually.of_forall fun i => aestronglyMeasurable_spatialW hw hNc α m (M i) n _ _ p' p
  · filter_upwards [hMge] with i hi
    exact Eventually.of_forall fun v => norm_spatialW_le hwb
      (fun z hz v => hC (M i) hi _ z hz v) v

end Weight

/-! ### The doubled vertex -/

/-- **The vertex with the electron denominator of the line `d` doubled**:
`N(ℓ) / (D_m(p' + ℓ; ε) D_m(p + ℓ; ε) D_m(ℓ_d; ε) D_M(ℓ; η)^{n+1})`. -/
noncomputable def dblIntegrand (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) (ε η : ℝ) (d : Fin 2)
    (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * (denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom m ε (dblMom d p' p ℓ) *
    denom M η ℓ ^ (n + 1))⁻¹

/-- **Feynman parameters for the doubled vertex**: the weight `dblWt d n` and the combined
denominator of the undoubled vertex, to the power `n + 4` (order `n + 1` of `jointW`). -/
theorem dblIntegrand_eq_integral_jointW (N : (Fin 4 → ℝ) → ℂ) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (d : Fin 2) (p' p : Fin 4 → ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    dblIntegrand N m M n ε η d p' p (Fin.cons t v : Fin 4 → ℝ) =
      ∫ z, jointW (dblWt d n) N m M (n + 1) ε η p' p v (t, z) ∂feynmanMeasure := by
  set ℓ : Fin 4 → ℝ := Fin.cons t v
  have hA : (denom m ε (p' + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hB : (denom m ε (p + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hC : (denom M η ℓ).im < 0 := by rw [denom_im]; linarith
  have hd : denom m ε (dblMom d p' p ℓ) =
      if d = 0 then denom m ε (p + ℓ) else denom m ε (p' + ℓ) := by
    unfold dblMom; split_ifs <;> rfl
  rw [dblIntegrand, hd, inv_dbl_eq_integral_feynmanMeasure hA hB hC d n, ← integral_const_mul]
  congr 1
  ext z
  simp only [jointW, feynman_combo_eq_combDen]
  ring

theorem integrable_jointW_dbl {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (d : Fin 2) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable (jointW (dblWt d n) N m M (n + 1) ε η p' p v)
      ((volume : Measure ℝ).prod feynmanMeasure) :=
  integrable_jointW (continuous_dblWt d n) (fun _ hz => dblWt_norm_le d n hz) hNc hNb m M
    (n + 1) hε hη p' p v

/-- **The energy integral of the doubled vertex**, at fixed spatial momentum: the weighted closed
form of order `n + 1`. -/
theorem integral_time_dblIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (d : Fin 2) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, dblIntegrand N m M n ε η d p' p (Fin.cons t v : Fin 4 → ℝ) =
      spatialW (dblWt d n) α N m M (n + 1) ε η p' p v := by
  simp_rw [dblIntegrand_eq_integral_jointW N m M n hε hη d p' p _ v]
  rw [integral_integral_swap (f := fun t z => jointW (dblWt d n) N m M (n + 1) ε η p' p v (t, z))
    (integrable_jointW_dbl hNc hNb m M n hε hη d p' p v)]
  refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
  exact integral_time_jointW hNq m M (n + 1) hε hη p' p v (Ioc_prod_subset hz)

theorem integrable_time_dblIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (d : Fin 2) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => dblIntegrand N m M n ε η d p' p (Fin.cons t v : Fin 4 → ℝ) :=
  (integrable_jointW_dbl hNc hNb m M n hε hη d p' p v).integral_prod_left.congr
    (Eventually.of_forall fun t =>
      (dblIntegrand_eq_integral_jointW N m M n hε hη d p' p t v).symm)

/-- **The energy-first integral of the doubled vertex in parametric form.** -/
theorem energyFirstIntegral_dblIntegrand_eq {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N)
    {α : ℂ} (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m M : ℝ) (n : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (d : Fin 2) (p' p : Fin 4 → ℝ) :
    energyFirstIntegral (dblIntegrand N m M n ε η d p' p) =
      ∫ v, spatialW (dblWt d n) α N m M (n + 1) ε η p' p v :=
  integral_congr_ae (Eventually.of_forall fun v =>
    integral_time_dblIntegrand hNc hNq hNb m M n hε hη d p' p v)

/-- **The limit of the doubled vertex**: along any countably generated filter on which
`ε → 0⁺`, `η → 0⁺` and `M → M_*` with `M ≥ M₀ > 0` eventually, the energy-first integral of
`dblIntegrand` tends to `∫ spatialW (dblWt d n) (ε = η = 0, M_*)`; any `n`, including a single
photon denominator (`n = 0`). -/
theorem tendsto_energyFirstIntegral_dblIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (n : ℕ) (d : Fin 2)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε η M : ι → ℝ} {Ms : ℝ}
    (hε : Tendsto ε l (𝓝[>] 0)) (hη : Tendsto η l (𝓝[>] 0)) (hM : Tendsto M l (𝓝 Ms))
    (hMge : ∀ᶠ i in l, M₀ ≤ M i) :
    Tendsto (fun i => energyFirstIntegral (dblIntegrand N m (M i) n (ε i) (η i) d p' p)) l
      (𝓝 (∫ v, spatialW (dblWt d n) α N m Ms (n + 1) 0 0 p' p v)) := by
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε (self_mem_nhdsWithin)
  have hηpos : ∀ᶠ i in l, 0 < η i := hη (self_mem_nhdsWithin)
  have hlim := tendsto_integral_spatialW (continuous_dblWt d n)
    (fun _ hz => dblWt_norm_le d n hz) hm hM₀ hp' hp hp0' hp0 hNc α hNb (by omega : 1 ≤ n + 1)
    (hε.mono_right nhdsWithin_le_nhds) (hη.mono_right nhdsWithin_le_nhds)
    (hεpos.mono fun _ h => h.le) (hηpos.mono fun _ h => h.le) hM hMge
  refine hlim.congr' ?_
  filter_upwards [hεpos, hηpos] with i h1 h2
  exact (energyFirstIntegral_dblIntegrand_eq hNc hNq hNb m (M i) n h1 h2 d p' p).symm

end QED.ChainProof.CtLoB

end
