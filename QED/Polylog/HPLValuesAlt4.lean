/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLAlt4Rel
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import QED.Polylog.HPLLowWeight
import QED.Polylog.LiCalculus
import QED.Polylog.LiHalf

/-!
# Harmonic polylogarithms at `1`: the alternating words of weight four

The values `H(w; 1)` of all 36 words `w` of weight four over `{0, 1, -1}` with first letter
not `1` and no trailing zero, in the basis
`π⁴, log 2 · ζ(3), Li₄(1/2), log⁴ 2, π² log² 2` (`ζ(3) = zeta3`).

Two inputs are analytic: `H(-1, 1, 1, 1; 1) = Li₄(1/2)`
(`QED.Polylog.HPL.hpl_negOne_one_one_one_at_one`) and the closed form of
`H(0, -1, -1, -1; x) = ∫₀ˣ log³(1 + t) / (6t) dt` through `Li_k(1/(1 + x))`
(`QED.Polylog.HPL.hpl_zero_negOne_negOne_negOne_at_one`). Every other value is a rational
linear combination of the double shuffle and distribution relations of
`QED.Polylog.HPLAlt4Rel` (coefficients found by exact linear algebra over `ℚ`, checked here by
`linear_combination`).
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- The closed form of `H(0, -1, -1, -1; x)` with `ℓ = log (1 + x)`, `u = 1 / (1 + x)`:
`(-3ℓ⁴/4 + ℓ³ log x - 3ℓ² Li₂ u - 6ℓ Li₃ u - 6 Li₄ u + 6 ζ(4)) / 6`. -/
noncomputable def hplZNNNForm (x : ℝ) : ℝ :=
  (-3 / 4 * log (1 + x) ^ 4 + log (1 + x) ^ 3 * log x - 3 * (log (1 + x) ^ 2 * Li 2 (1 + x)⁻¹) -
    6 * (log (1 + x) * Li 3 (1 + x)⁻¹) - 6 * Li 4 (1 + x)⁻¹ + 6 * Li 4 1) / 6

theorem hasDerivAt_hplZNNNForm {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt hplZNNNForm (x⁻¹ * (log (1 + x) ^ 3 / 6)) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have h1x : (1 + x) ≠ 0 := by linarith [hx.1]
  have hu : |(1 + x)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith [hx.1])]
    exact inv_lt_one_of_one_lt₀ (by linarith [hx.1])
  have hu0 : (1 + x)⁻¹ ≠ 0 := inv_ne_zero h1x
  have dA : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have dU := dA.inv h1x
  have dLi := fun (k : ℕ) (hk : 1 ≤ k) => (hasDerivAt_Li hk hu hu0).comp x dU
  have dl : HasDerivAt (fun y : ℝ => log (1 + y)) (1 / (1 + x)) x := by
    simpa using dA.log h1x
  have dL : HasDerivAt log x⁻¹ x := hasDerivAt_log hx0
  have h := (((((((dl.pow 4).const_mul (-3 / 4)).add ((dl.pow 3).mul dL)).sub
    (((dl.pow 2).mul (dLi 2 (by norm_num))).const_mul 3)).sub
    ((dl.mul (dLi 3 (by norm_num))).const_mul 6)).sub ((dLi 4 (by norm_num)).const_mul 6)).add
    (hasDerivAt_const x (6 * Li 4 1))).div_const 6
  convert h using 1
  · funext y
    simp only [hplZNNNForm, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply,
      Function.comp_apply]
  have hlog : Li 1 (1 + x)⁻¹ = log (1 + x) - log x := by
    rw [Li_one hu, show (1 : ℝ) - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring,
      log_div hx0 h1x]
    ring
  simp only [show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    show (4 : ℕ) - 1 = 3 from rfl, hlog, Nat.cast_ofNat, Pi.pow_apply, pow_one,
    Function.comp_apply, Pi.inv_apply]
  field_simp
  ring

theorem tendsto_Li_inv_one_add {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun x : ℝ => Li k (1 + x)⁻¹) (𝓝[>] 0) (𝓝 (Li k 1)) := by
  have hc := (continuousOn_Li hk) 1 ⟨by norm_num, le_rfl⟩
  refine hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝 0) (𝓝 (1 + 0)⁻¹) :=
      ((tendsto_const_nhds.add tendsto_id).inv₀ (by norm_num))
    rw [add_zero, inv_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    refine ⟨by linarith [inv_pos.2 (by linarith : (0 : ℝ) < 1 + x)], ?_⟩
    exact inv_le_one_of_one_le₀ (by linarith)

theorem tendsto_hplZNNNForm_zero : Tendsto hplZNNNForm (𝓝[>] 0) (𝓝 0) := by
  have tl : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => log (1 + x)) (𝓝 0) (𝓝 (log (1 + 0))) :=
      ((continuousAt_const.add continuousAt_id).log (by norm_num)).tendsto
    rw [add_zero, log_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have tLL : Tendsto (fun x : ℝ => log (1 + x) ^ 3 * log x) (𝓝[>] 0) (𝓝 0) := by
    have := (tl.pow 2).mul tendsto_log_mul_log_one_add_zero
    rw [zero_pow (by norm_num), zero_mul] at this
    refine this.congr fun x => ?_
    ring
  have h := (((((((tl.pow 4).const_mul (-3 / 4)).add tLL).sub
    (((tl.pow 2).mul (tendsto_Li_inv_one_add (k := 2) (by norm_num))).const_mul 3)).sub
    ((tl.mul (tendsto_Li_inv_one_add (k := 3) (by norm_num))).const_mul 6)).sub
    ((tendsto_Li_inv_one_add (k := 4) (by norm_num)).const_mul 6)).add
    (tendsto_const_nhds (x := 6 * Li 4 1))).div_const 6
  convert h using 2
  · rfl
  · ring

theorem continuousAt_Li_inv_one_add {k : ℕ} (hk : 1 ≤ k) :
    ContinuousAt (fun x : ℝ => Li k (1 + x)⁻¹) 1 := by
  have h := (hasDerivAt_Li hk (x := (1 + 1 : ℝ)⁻¹) (by norm_num [abs_of_pos])
    (by norm_num)).continuousAt
  exact h.comp (f := fun x : ℝ => (1 + x)⁻¹)
    ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num))

theorem tendsto_hplZNNNForm_one : Tendsto hplZNNNForm (𝓝[<] 1) (𝓝 (hplZNNNForm 1)) := by
  have cl : ContinuousAt (fun x : ℝ => log (1 + x)) 1 :=
    (continuousAt_const.add continuousAt_id).log (by norm_num)
  have cL : ContinuousAt log 1 := continuousAt_log one_ne_zero
  have c := (((((((cl.pow 4).const_mul (-3 / 4)).add ((cl.pow 3).mul cL)).sub
    (((cl.pow 2).mul (continuousAt_Li_inv_one_add (k := 2) (by norm_num))).const_mul 3)).sub
    ((cl.mul (continuousAt_Li_inv_one_add (k := 3) (by norm_num))).const_mul 6)).sub
    ((continuousAt_Li_inv_one_add (k := 4) (by norm_num)).const_mul 6)).add
    (continuousAt_const (y := 6 * Li 4 1))).div_const 6
  refine (c.tendsto.mono_left nhdsWithin_le_nhds).congr' (Eventually.of_forall fun y => ?_)
    |>.trans ?_
  · simp only [hplZNNNForm, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  · simp only [hplZNNNForm, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    exact le_rfl

/-- `H(0, -1, -1, -1; 1) = ∫₀¹ log³(1 + t) / (6t) dt
= (π⁴/15 + π² log² 2 / 4 - log⁴ 2 / 4 - 6 Li₄(1/2) - 21/4 ζ(3) log 2) / 6`. -/
theorem hpl_zero_negOne_negOne_negOne_at_one :
    hpl [zero, negOne, negOne, negOne] 1 = (π ^ 4 / 15 + π ^ 2 * log 2 ^ 2 / 4 - log 2 ^ 4 / 4 -
      6 * Li 4 (1 / 2) - 21 / 4 * zeta3 * log 2) / 6 := by
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, hpl [zero, negOne, negOne, negOne] x = hplZNNNForm x :=
    eq_hpl_cons_of_hasDerivAt (by decide) (fun x hx => by
      rw [kernel_zero, hpl_negOne_negOne_negOne hx]
      exact hasDerivAt_hplZNNNForm hx) tendsto_hplZNNNForm_zero
  rw [hpl_one_eq_of_tendsto (by decide) hF tendsto_hplZNNNForm_one, hplZNNNForm,
    show (1 + 1 : ℝ) = 2 by norm_num, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, log_one,
    Li_two_one_half, Li_three_one_half, Li_four_one]
  ring

theorem hpl_zero_zero_one_negOne_at_one :
    hpl [zero, zero, one, negOne] 1 =
      7 / 4 * log 2 * zeta3 - 19 / 1440 * π ^ 4 := by
  linear_combination (-4) * rel4_sh_0 + (3) * rel4_st_0 + (7) * rel4_sh_1 + (-3) * rel4_st_1 +
    (2) * rel4_sh_3 + (-1) * rel4_st_3 + (2) * rel4_sh_4 + (-2) * rel4_st_4 + (4) * rel4_st_5 +
    (-2) * rel4_sh_7 + (1) * rel4_st_7 + (1) * rel4_sh_12 + (-2) * rel4_sh_14 + (-4) * rel4_st_15 +
    (-5 / 2) * rel4_sh_16 + (3) * rel4_dist_4

theorem hpl_zero_zero_negOne_one_at_one :
    hpl [zero, zero, negOne, one] 1 =
      2 * Li 4 (1 / 2) + 1 / 12 * log 2 ^ 4 - 1 / 12 * log 2 ^ 2 * π ^ 2 - 1 / 180 * π ^ 4 := by
  linear_combination (4) * rel4_sh_0 + (-3) * rel4_st_0 + (-7) * rel4_sh_1 + (3) * rel4_st_1 +
    (2 / 3) * rel4_sh_2 + (-2 / 3) * rel4_st_2 + (-7 / 3) * rel4_sh_3 + (4 / 3) * rel4_st_3 +
    (-7 / 3) * rel4_sh_4 + (7 / 3) * rel4_st_4 + (2 / 3) * rel4_sh_5 + (-14 / 3) * rel4_st_5 +
    (2) * rel4_sh_7 + (-1) * rel4_st_7 + (-7 / 6) * rel4_sh_12 + (2 / 3) * rel4_sh_13 +
    (2) * rel4_sh_14 + (4) * rel4_st_15 + (7 / 3) * rel4_sh_16 + (-3) * rel4_dist_4 +
    (-2) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_zero_negOne_negOne_at_one :
    hpl [zero, zero, negOne, negOne] 1 =
      2 * Li 4 (1 / 2) + 1 / 12 * log 2 ^ 4 - 1 / 12 * log 2 ^ 2 * π ^ 2
      + 7 / 4 * log 2 * zeta3 - 1 / 48 * π ^ 4 := by
  linear_combination (-3 / 2) * rel4_sh_0 + (1 / 2) * rel4_st_0 + (5 / 2) * rel4_sh_1 +
    (-1) * rel4_st_1 + (2 / 3) * rel4_sh_2 + (-2 / 3) * rel4_st_2 + (2 / 3) * rel4_sh_3 +
    (-1 / 6) * rel4_st_3 + (2 / 3) * rel4_sh_4 + (-2 / 3) * rel4_st_4 + (2 / 3) * rel4_sh_5 +
    (4 / 3) * rel4_st_5 + (-1) * rel4_sh_7 + (1 / 2) * rel4_st_7 + (1 / 3) * rel4_sh_12 +
    (1 / 6) * rel4_sh_13 + (1 / 2) * rel4_st_13 + (-1) * rel4_sh_14 + (-2) * rel4_st_15 +
    (-2 / 3) * rel4_sh_16 + (1) * rel4_dist_4 + (-2) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_one_zero_negOne_at_one :
    hpl [zero, one, zero, negOne] 1 =
      -4 * Li 4 (1 / 2) - 1 / 6 * log 2 ^ 4 + 1 / 6 * log 2 ^ 2 * π ^ 2
      - 7 / 2 * log 2 * zeta3 + 71 / 1440 * π ^ 4 := by
  linear_combination (-1) * rel4_sh_0 + (1) * rel4_st_0 + (1) * rel4_sh_1 + (-1) * rel4_st_1 +
    (-4 / 3) * rel4_sh_2 + (4 / 3) * rel4_st_2 + (2 / 3) * rel4_sh_3 + (-2 / 3) * rel4_st_3 +
    (2 / 3) * rel4_sh_4 + (-2 / 3) * rel4_st_4 + (-4 / 3) * rel4_sh_5 + (4 / 3) * rel4_st_5 +
    (1 / 3) * rel4_sh_12 + (-1 / 3) * rel4_sh_13 + (-1 / 6) * rel4_sh_16 + (1) * rel4_dist_4 +
    (4) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_one_one_negOne_at_one :
    hpl [zero, one, one, negOne] 1 =
      Li 4 (1 / 2) + 1 / 24 * log 2 ^ 4 + 1 / 12 * log 2 ^ 2 * π ^ 2 + 7 / 8 * log 2 * zeta3
      - 1 / 80 * π ^ 4 := by
  linear_combination (1) * rel4_sh_0 + (-1) * rel4_st_0 + (-2) * rel4_sh_1 + (1) * rel4_st_1 +
    (4 / 3) * rel4_sh_2 + (-1 / 3) * rel4_st_2 + (-2 / 3) * rel4_sh_3 + (2 / 3) * rel4_st_3 +
    (-2 / 3) * rel4_sh_4 + (2 / 3) * rel4_st_4 + (1 / 3) * rel4_sh_5 + (-4 / 3) * rel4_st_5 +
    (1 / 2) * rel4_sh_7 + (-1 / 3) * rel4_sh_12 + (1 / 3) * rel4_sh_13 + (1) * rel4_st_15 +
    (2 / 3) * rel4_sh_16 + (-1) * rel4_dist_4 + (-1) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_one_negOne_one_at_one :
    hpl [zero, one, negOne, one] 1 =
      -3 * Li 4 (1 / 2) - 1 / 8 * log 2 ^ 4 - 1 / 8 * log 2 ^ 2 * π ^ 2 + 7 / 288 * π ^ 4 := by
  linear_combination (-311 / 96) * rel4_sh_0 + (89 / 32) * rel4_st_0 + (383 / 96) * rel4_sh_1 +
    (-83 / 32) * rel4_st_1 + (-37 / 24) * rel4_sh_2 + (89 / 96) * rel4_st_2 + (4 / 3) * rel4_sh_3 +
    (-5 / 3) * rel4_st_3 + (17 / 8) * rel4_sh_4 + (-71 / 48) * rel4_st_4 + (-5 / 6) * rel4_sh_5 +
    (15 / 4) * rel4_st_5 + (1 / 4) * rel4_sh_6 + (1 / 96) * rel4_st_6 + (-2 / 3) * rel4_sh_7 +
    (31 / 48) * rel4_st_7 + (1 / 4) * rel4_sh_8 + (-1 / 48) * rel4_st_8 + (-1 / 32) * rel4_sh_9 +
    (1 / 16) * rel4_st_9 + (-1 / 6) * rel4_sh_10 + (11 / 96) * rel4_st_10 + (-1 / 2) * rel4_st_11 +
    (15 / 16) * rel4_sh_12 + (7 / 32) * rel4_st_12 + (-49 / 96) * rel4_sh_13 +
    (-13 / 32) * rel4_st_13 + (-65 / 48) * rel4_sh_14 + (-39 / 32) * rel4_st_15 +
    (-35 / 24) * rel4_sh_16 + (19 / 8) * rel4_dist_4 + (-1 / 2) * rel4_dist_211 +
    (1) * hpl_zero_one_one_one_at_one + (-1) * hpl_negOne_one_one_one_at_one +
    (2) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_one_negOne_negOne_at_one :
    hpl [zero, one, negOne, negOne] 1 =
      -2 * Li 4 (1 / 2) - 1 / 12 * log 2 ^ 4 + 5 / 24 * log 2 ^ 2 * π ^ 2
      - 21 / 8 * log 2 * zeta3 + 7 / 288 * π ^ 4 := by
  linear_combination (3 / 2) * rel4_sh_0 + (-1 / 2) * rel4_st_0 + (-7 / 2) * rel4_sh_1 +
    (1) * rel4_st_1 + (-2 / 3) * rel4_sh_2 + (2 / 3) * rel4_st_2 + (-2 / 3) * rel4_sh_3 +
    (1 / 6) * rel4_st_3 + (-2 / 3) * rel4_sh_4 + (2 / 3) * rel4_st_4 + (-2 / 3) * rel4_sh_5 +
    (-4 / 3) * rel4_st_5 + (3 / 2) * rel4_sh_7 + (-1 / 2) * rel4_st_7 + (-1 / 3) * rel4_sh_12 +
    (-1 / 6) * rel4_sh_13 + (-1 / 2) * rel4_st_13 + (1) * rel4_sh_14 + (3) * rel4_st_15 +
    (7 / 6) * rel4_sh_16 + (-1) * rel4_dist_4 + (2) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_negOne_zero_one_at_one :
    hpl [zero, negOne, zero, one] 1 =
      1 / 480 * π ^ 4 := by
  linear_combination (1) * rel4_sh_0 + (-1) * rel4_st_0 + (-1) * rel4_sh_1 + (1) * rel4_st_1 +
    (1 / 2) * rel4_sh_16 + (-1) * rel4_dist_4

theorem hpl_zero_negOne_zero_negOne_at_one :
    hpl [zero, negOne, zero, negOne] 1 =
      -4 * Li 4 (1 / 2) - 1 / 6 * log 2 ^ 4 + 1 / 6 * log 2 ^ 2 * π ^ 2
      - 7 / 2 * log 2 * zeta3 + 13 / 288 * π ^ 4 := by
  linear_combination (3) * rel4_sh_0 + (-1) * rel4_st_0 + (-5) * rel4_sh_1 + (2) * rel4_st_1 +
    (-4 / 3) * rel4_sh_2 + (4 / 3) * rel4_st_2 + (-4 / 3) * rel4_sh_3 + (1 / 3) * rel4_st_3 +
    (-4 / 3) * rel4_sh_4 + (4 / 3) * rel4_st_4 + (-4 / 3) * rel4_sh_5 + (-8 / 3) * rel4_st_5 +
    (2) * rel4_sh_7 + (-1) * rel4_st_7 + (-2 / 3) * rel4_sh_12 + (-1 / 3) * rel4_sh_13 +
    (-1) * rel4_st_13 + (2) * rel4_sh_14 + (4) * rel4_st_15 + (11 / 6) * rel4_sh_16 +
    (-2) * rel4_dist_4 + (4) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_negOne_one_one_at_one :
    hpl [zero, negOne, one, one] 1 =
      3 * Li 4 (1 / 2) + 1 / 8 * log 2 ^ 4 - 11 / 720 * π ^ 4 := by
  linear_combination (95 / 48) * rel4_sh_0 + (-25 / 16) * rel4_st_0 + (-95 / 48) * rel4_sh_1 +
    (23 / 16) * rel4_st_1 + (3 / 4) * rel4_sh_2 + (-25 / 48) * rel4_st_2 + (-1 / 2) * rel4_sh_3 +
    (11 / 12) * rel4_st_3 + (-13 / 12) * rel4_sh_4 + (19 / 24) * rel4_st_4 + (1 / 3) * rel4_sh_5 +
    (-13 / 6) * rel4_st_5 + (-1 / 2) * rel4_sh_6 + (-1 / 48) * rel4_st_6 + (1 / 3) * rel4_sh_7 +
    (-13 / 24) * rel4_st_7 + (-1 / 2) * rel4_sh_8 + (1 / 24) * rel4_st_8 + (1 / 16) * rel4_sh_9 +
    (-1 / 8) * rel4_st_9 + (1 / 3) * rel4_sh_10 + (-11 / 48) * rel4_st_10 + (1) * rel4_st_11 +
    (-13 / 24) * rel4_sh_12 + (-3 / 16) * rel4_st_12 + (3 / 16) * rel4_sh_13 +
    (5 / 16) * rel4_st_13 + (29 / 24) * rel4_sh_14 + (7 / 16) * rel4_st_15 + (3 / 4) * rel4_sh_16 +
    (-5 / 4) * rel4_dist_4 + (-1) * hpl_zero_one_one_one_at_one +
    (2) * hpl_negOne_one_one_one_at_one + (-1) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_zero_negOne_one_negOne_at_one :
    hpl [zero, negOne, one, negOne] 1 =
      -1 / 4 * log 2 ^ 2 * π ^ 2 + 21 / 8 * log 2 * zeta3 - 7 / 720 * π ^ 4 := by
  linear_combination (-4) * rel4_sh_0 + (3) * rel4_st_0 + (5) * rel4_sh_1 + (-3) * rel4_st_1 +
    (1) * rel4_sh_3 + (-1) * rel4_st_3 + (2) * rel4_sh_4 + (-1) * rel4_st_4 + (4) * rel4_st_5 +
    (-1) * rel4_sh_7 + (1) * rel4_st_7 + (1) * rel4_sh_12 + (-2) * rel4_sh_14 + (-2) * rel4_st_15 +
    (-2) * rel4_sh_16 + (3) * rel4_dist_4

theorem hpl_zero_negOne_negOne_one_at_one :
    hpl [zero, negOne, negOne, one] 1 =
      2 * Li 4 (1 / 2) + 1 / 12 * log 2 ^ 4 + 1 / 24 * log 2 ^ 2 * π ^ 2 - 1 / 80 * π ^ 4 := by
  linear_combination (215 / 96) * rel4_sh_0 + (-73 / 32) * rel4_st_0 + (-143 / 96) * rel4_sh_1 +
    (59 / 32) * rel4_st_1 + (29 / 24) * rel4_sh_2 + (-19 / 32) * rel4_st_2 + (-1 / 6) * rel4_sh_3 +
    (3 / 4) * rel4_st_3 + (-23 / 24) * rel4_sh_4 + (5 / 16) * rel4_st_4 + (1 / 2) * rel4_sh_5 +
    (-29 / 12) * rel4_st_5 + (-1 / 4) * rel4_sh_6 + (-1 / 96) * rel4_st_6 + (-1 / 3) * rel4_sh_7 +
    (-19 / 48) * rel4_st_7 + (-1 / 4) * rel4_sh_8 + (1 / 48) * rel4_st_8 + (1 / 32) * rel4_sh_9 +
    (-1 / 16) * rel4_st_9 + (1 / 6) * rel4_sh_10 + (-11 / 96) * rel4_st_10 + (1 / 2) * rel4_st_11 +
    (-29 / 48) * rel4_sh_12 + (1 / 32) * rel4_st_12 + (17 / 96) * rel4_sh_13 +
    (13 / 32) * rel4_st_13 + (41 / 48) * rel4_sh_14 + (-25 / 32) * rel4_st_15 +
    (19 / 24) * rel4_sh_16 + (-15 / 8) * rel4_dist_4 + (1 / 2) * rel4_dist_211 +
    (-1) * hpl_zero_one_one_one_at_one + (1) * hpl_negOne_one_one_one_at_one +
    (-1) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_zero_zero_one_at_one :
    hpl [negOne, zero, zero, one] 1 =
      -2 * Li 4 (1 / 2) - 1 / 12 * log 2 ^ 4 + 1 / 12 * log 2 ^ 2 * π ^ 2
      - 3 / 4 * log 2 * zeta3 + 1 / 60 * π ^ 4 := by
  linear_combination (1) * rel4_st_0 + (1) * rel4_sh_1 + (-1) * rel4_st_1 + (-2 / 3) * rel4_sh_2 +
    (2 / 3) * rel4_st_2 + (1 / 3) * rel4_sh_3 + (-1 / 3) * rel4_st_3 + (1 / 3) * rel4_sh_4 +
    (-1 / 3) * rel4_st_4 + (-2 / 3) * rel4_sh_5 + (2 / 3) * rel4_st_5 + (1 / 6) * rel4_sh_12 +
    (-2 / 3) * rel4_sh_13 + (-1 / 3) * rel4_sh_16 + (1) * rel4_dist_4 +
    (2) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_zero_zero_negOne_at_one :
    hpl [negOne, zero, zero, negOne] 1 =
      3 / 4 * log 2 * zeta3 - 1 / 288 * π ^ 4 := by
  linear_combination (1) * rel4_sh_1 + (-1 / 2) * rel4_sh_16

theorem hpl_negOne_zero_one_one_at_one :
    hpl [negOne, zero, one, one] 1 =
      -Li 4 (1 / 2) - 1 / 24 * log 2 ^ 4 + 1 / 24 * log 2 ^ 2 * π ^ 2
      + 1 / 8 * log 2 * zeta3 + 1 / 288 * π ^ 4 := by
  linear_combination (25 / 96) * rel4_sh_0 + (-7 / 32) * rel4_st_0 + (-1 / 96) * rel4_sh_1 +
    (5 / 32) * rel4_st_1 + (11 / 24) * rel4_sh_2 + (-7 / 96) * rel4_st_2 + (-1 / 6) * rel4_sh_3 +
    (1 / 12) * rel4_st_3 + (-3 / 8) * rel4_sh_4 + (1 / 48) * rel4_st_4 + (1 / 6) * rel4_sh_5 +
    (-1 / 4) * rel4_st_5 + (1 / 4) * rel4_sh_6 + (1 / 96) * rel4_st_6 + (-1 / 6) * rel4_sh_7 +
    (-5 / 48) * rel4_st_7 + (1 / 4) * rel4_sh_8 + (-1 / 48) * rel4_st_8 + (-1 / 32) * rel4_sh_9 +
    (1 / 16) * rel4_st_9 + (-1 / 6) * rel4_sh_10 + (11 / 96) * rel4_st_10 + (-1 / 2) * rel4_st_11 +
    (-1 / 16) * rel4_sh_12 + (-1 / 32) * rel4_st_12 + (-1 / 96) * rel4_sh_13 +
    (3 / 32) * rel4_st_13 + (7 / 48) * rel4_sh_14 + (-7 / 32) * rel4_st_15 + (1 / 24) * rel4_sh_16 +
    (-1 / 8) * rel4_dist_4 + (1 / 2) * rel4_dist_211 + (-1) * hpl_negOne_one_one_one_at_one

theorem hpl_negOne_zero_one_negOne_at_one :
    hpl [negOne, zero, one, negOne] 1 =
      4 * Li 4 (1 / 2) + 1 / 6 * log 2 ^ 4 + 1 / 12 * log 2 ^ 2 * π ^ 2
      + 13 / 8 * log 2 * zeta3 - 7 / 180 * π ^ 4 := by
  linear_combination (1) * rel4_sh_0 + (-2) * rel4_st_0 + (2) * rel4_sh_1 + (1) * rel4_st_1 +
    (4 / 3) * rel4_sh_2 + (-4 / 3) * rel4_st_2 + (4 / 3) * rel4_sh_3 + (2 / 3) * rel4_st_3 +
    (-2 / 3) * rel4_sh_4 + (-1 / 3) * rel4_st_4 + (4 / 3) * rel4_sh_5 + (-4 / 3) * rel4_st_5 +
    (-2) * rel4_sh_7 + (-1 / 3) * rel4_sh_12 + (1 / 3) * rel4_sh_13 + (1) * rel4_st_13 +
    (-4) * rel4_st_15 + (-1 / 3) * rel4_sh_16 + (-1) * rel4_dist_4 +
    (-4) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_zero_negOne_one_at_one :
    hpl [negOne, zero, negOne, one] 1 =
      -4 * Li 4 (1 / 2) - 1 / 6 * log 2 ^ 4 - 1 / 12 * log 2 ^ 2 * π ^ 2 - log 2 * zeta3
      + 5 / 144 * π ^ 4 := by
  linear_combination (-23 / 48) * rel4_sh_0 + (25 / 16) * rel4_st_0 + (-97 / 48) * rel4_sh_1 +
    (-11 / 16) * rel4_st_1 + (-29 / 12) * rel4_sh_2 + (19 / 16) * rel4_st_2 + (-2 / 3) * rel4_sh_3 +
    (-1 / 2) * rel4_st_3 + (11 / 12) * rel4_sh_4 + (3 / 8) * rel4_st_4 + (-1) * rel4_sh_5 +
    (5 / 6) * rel4_st_5 + (1 / 2) * rel4_sh_6 + (1 / 48) * rel4_st_6 + (5 / 3) * rel4_sh_7 +
    (-5 / 24) * rel4_st_7 + (1 / 2) * rel4_sh_8 + (-1 / 24) * rel4_st_8 + (-1 / 16) * rel4_sh_9 +
    (1 / 8) * rel4_st_9 + (-1 / 3) * rel4_sh_10 + (11 / 48) * rel4_st_10 + (-1) * rel4_st_11 +
    (5 / 24) * rel4_sh_12 + (-1 / 16) * rel4_st_12 + (-17 / 48) * rel4_sh_13 +
    (-13 / 16) * rel4_st_13 + (7 / 24) * rel4_sh_14 + (57 / 16) * rel4_st_15 +
    (5 / 12) * rel4_sh_16 + (3 / 4) * rel4_dist_4 + (-1) * rel4_dist_211 +
    (2) * hpl_zero_one_one_one_at_one + (-2) * hpl_negOne_one_one_one_at_one +
    (2) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_zero_negOne_negOne_at_one :
    hpl [negOne, zero, negOne, negOne] 1 =
      3 * Li 4 (1 / 2) + 1 / 8 * log 2 ^ 4 - 1 / 8 * log 2 ^ 2 * π ^ 2
      + 11 / 4 * log 2 * zeta3 - 1 / 30 * π ^ 4 := by
  linear_combination (1) * rel4_sh_5 + (-3) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_one_zero_one_at_one :
    hpl [negOne, one, zero, one] 1 =
      -Li 4 (1 / 2) - 1 / 24 * log 2 ^ 4 - 1 / 24 * log 2 ^ 2 * π ^ 2
      - 1 / 4 * log 2 * zeta3 + 19 / 1440 * π ^ 4 := by
  linear_combination (-119 / 96) * rel4_sh_0 + (25 / 32) * rel4_st_0 + (-1 / 96) * rel4_sh_1 +
    (-19 / 32) * rel4_st_1 + (-7 / 8) * rel4_sh_2 + (25 / 96) * rel4_st_2 + (-1 / 3) * rel4_st_3 +
    (19 / 24) * rel4_sh_4 + (-7 / 48) * rel4_st_4 + (-1 / 6) * rel4_sh_5 + (13 / 12) * rel4_st_5 +
    (1 / 4) * rel4_sh_6 + (1 / 96) * rel4_st_6 + (1 / 3) * rel4_sh_7 + (31 / 48) * rel4_st_7 +
    (1 / 4) * rel4_sh_8 + (-1 / 48) * rel4_st_8 + (-1 / 32) * rel4_sh_9 + (1 / 16) * rel4_st_9 +
    (-1 / 6) * rel4_sh_10 + (11 / 96) * rel4_st_10 + (-1 / 2) * rel4_st_11 +
    (13 / 48) * rel4_sh_12 + (7 / 32) * rel4_st_12 + (5 / 32) * rel4_sh_13 +
    (-13 / 32) * rel4_st_13 + (-17 / 48) * rel4_sh_14 + (25 / 32) * rel4_st_15 +
    (-1 / 8) * rel4_sh_16 + (3 / 8) * rel4_dist_4 + (-1 / 2) * rel4_dist_211 +
    (1) * hpl_zero_one_one_one_at_one + (-1) * hpl_negOne_one_one_one_at_one

theorem hpl_negOne_one_zero_negOne_at_one :
    hpl [negOne, one, zero, negOne] 1 =
      -4 * Li 4 (1 / 2) - 1 / 6 * log 2 ^ 4 + 1 / 8 * log 2 ^ 2 * π ^ 2
      - 13 / 4 * log 2 * zeta3 + 11 / 240 * π ^ 4 := by
  linear_combination (-1) * rel4_sh_0 + (3 / 2) * rel4_st_0 + (-1) * rel4_sh_1 + (-1) * rel4_st_1 +
    (-4 / 3) * rel4_sh_2 + (4 / 3) * rel4_st_2 + (-1 / 3) * rel4_sh_3 + (-2 / 3) * rel4_st_3 +
    (2 / 3) * rel4_sh_4 + (-1 / 6) * rel4_st_4 + (-4 / 3) * rel4_sh_5 + (4 / 3) * rel4_st_5 +
    (1 / 2) * rel4_st_6 + (1) * rel4_sh_7 + (1 / 3) * rel4_sh_12 + (-1 / 3) * rel4_sh_13 +
    (-1 / 2) * rel4_st_13 + (2) * rel4_st_15 + (1 / 3) * rel4_sh_16 + (1) * rel4_dist_4 +
    (4) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_one_one_negOne_at_one :
    hpl [negOne, one, one, negOne] 1 =
      1 / 24 * log 2 ^ 4 - 1 / 24 * log 2 ^ 2 * π ^ 2 + 7 / 8 * log 2 * zeta3
      - 1 / 288 * π ^ 4 := by
  linear_combination (-1 / 8) * rel4_sh_0 + (1 / 8) * rel4_st_0 + (-3 / 8) * rel4_sh_1 +
    (1 / 2) * rel4_sh_2 + (-1 / 8) * rel4_st_2 + (-1 / 2) * rel4_sh_3 + (1 / 8) * rel4_st_3 +
    (1 / 4) * rel4_st_4 + (-1 / 8) * rel4_st_6 + (1 / 2) * rel4_sh_7 + (1 / 8) * rel4_st_7 +
    (1 / 4) * rel4_st_8 + (3 / 8) * rel4_sh_9 + (-3 / 8) * rel4_st_10 + (1 / 8) * rel4_sh_13 +
    (-1 / 8) * rel4_st_13 + (-1 / 4) * rel4_sh_14 + (5 / 8) * rel4_st_15

theorem hpl_negOne_one_negOne_one_at_one :
    hpl [negOne, one, negOne, one] 1 =
      1 / 24 * log 2 ^ 4 - 1 / 24 * log 2 ^ 2 * π ^ 2 + 1 / 4 * log 2 * zeta3
      + 1 / 1440 * π ^ 4 := by
  linear_combination (-1) * rel4_sh_0 + (1 / 2) * rel4_st_0 + (3 / 2) * rel4_sh_1 +
    (-5 / 8) * rel4_st_1 + (1 / 2) * rel4_sh_3 + (-3 / 8) * rel4_st_3 + (1 / 2) * rel4_sh_4 +
    (-1 / 2) * rel4_st_4 + (1) * rel4_st_5 + (-1 / 2) * rel4_sh_7 + (3 / 8) * rel4_st_7 +
    (-1 / 4) * rel4_st_9 + (1 / 4) * rel4_sh_12 + (1 / 8) * rel4_st_12 + (-1 / 2) * rel4_sh_14 +
    (-1) * rel4_st_15 + (-1 / 2) * rel4_sh_16 + (1 / 2) * rel4_dist_4

theorem hpl_negOne_one_negOne_negOne_at_one :
    hpl [negOne, one, negOne, negOne] 1 =
      -3 * Li 4 (1 / 2) - 1 / 6 * log 2 ^ 4 + 1 / 6 * log 2 ^ 2 * π ^ 2
      - 23 / 8 * log 2 * zeta3 + 1 / 30 * π ^ 4 := by
  linear_combination (1 / 8) * rel4_sh_0 + (3 / 8) * rel4_st_0 + (-13 / 8) * rel4_sh_1 +
    (-1 / 2) * rel4_sh_2 + (5 / 8) * rel4_st_2 + (-1 / 2) * rel4_sh_3 + (-1 / 8) * rel4_st_3 +
    (1 / 4) * rel4_st_4 + (-1) * rel4_sh_5 + (1 / 8) * rel4_st_6 + (1) * rel4_sh_7 +
    (-1 / 8) * rel4_st_7 + (-1 / 4) * rel4_st_8 + (1 / 8) * rel4_sh_9 + (-1 / 8) * rel4_st_10 +
    (-1 / 8) * rel4_sh_13 + (-3 / 8) * rel4_st_13 + (1 / 4) * rel4_sh_14 + (15 / 8) * rel4_st_15 +
    (1 / 2) * rel4_sh_16 + (3) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_negOne_zero_one_at_one :
    hpl [negOne, negOne, zero, one] 1 =
      1 / 12 * log 2 ^ 2 * π ^ 2 - 5 / 8 * log 2 * zeta3 + 1 / 480 * π ^ 4 := by
  linear_combination (-25 / 96) * rel4_sh_0 + (7 / 32) * rel4_st_0 + (1 / 96) * rel4_sh_1 +
    (-5 / 32) * rel4_st_1 + (13 / 24) * rel4_sh_2 + (7 / 96) * rel4_st_2 + (-1 / 3) * rel4_sh_3 +
    (-1 / 12) * rel4_st_3 + (-1 / 8) * rel4_sh_4 + (-1 / 48) * rel4_st_4 + (-1 / 6) * rel4_sh_5 +
    (1 / 4) * rel4_st_5 + (1 / 4) * rel4_sh_6 + (-1 / 96) * rel4_st_6 + (1 / 6) * rel4_sh_7 +
    (5 / 48) * rel4_st_7 + (-1 / 4) * rel4_sh_8 + (1 / 48) * rel4_st_8 + (1 / 32) * rel4_sh_9 +
    (-1 / 16) * rel4_st_9 + (1 / 6) * rel4_sh_10 + (-11 / 96) * rel4_st_10 + (1 / 2) * rel4_st_11 +
    (1 / 16) * rel4_sh_12 + (1 / 32) * rel4_st_12 + (1 / 96) * rel4_sh_13 + (-3 / 32) * rel4_st_13 +
    (-7 / 48) * rel4_sh_14 + (7 / 32) * rel4_st_15 + (-1 / 24) * rel4_sh_16 +
    (1 / 8) * rel4_dist_4 + (1 / 2) * rel4_dist_211 + (-1) * hpl_zero_one_one_one_at_one +
    (1) * hpl_negOne_one_one_one_at_one + (1) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_negOne_zero_negOne_at_one :
    hpl [negOne, negOne, zero, negOne] 1 =
      -3 * Li 4 (1 / 2) - 1 / 8 * log 2 ^ 4 + 1 / 6 * log 2 ^ 2 * π ^ 2
      - 23 / 8 * log 2 * zeta3 + 1 / 30 * π ^ 4 := by
  linear_combination (-1) * rel4_sh_5 + (1 / 2) * rel4_sh_7 +
    (3) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_negOne_one_one_at_one :
    hpl [negOne, negOne, one, one] 1 =
      1 / 24 * log 2 ^ 4 - 1 / 8 * log 2 * zeta3 + 1 / 720 * π ^ 4 := by
  linear_combination (9 / 16) * rel4_sh_0 + (-5 / 16) * rel4_st_0 + (-9 / 16) * rel4_sh_1 +
    (5 / 16) * rel4_st_1 + (-1 / 4) * rel4_sh_2 + (1 / 16) * rel4_st_2 + (1 / 8) * rel4_st_3 +
    (-1 / 4) * rel4_sh_4 + (1 / 8) * rel4_st_4 + (-1 / 2) * rel4_st_5 + (1 / 16) * rel4_st_6 +
    (-1 / 4) * rel4_st_7 + (1 / 2) * rel4_sh_8 + (-1 / 8) * rel4_st_8 + (-3 / 16) * rel4_sh_9 +
    (1 / 8) * rel4_st_9 + (3 / 16) * rel4_st_10 + (-1 / 8) * rel4_sh_12 + (-1 / 16) * rel4_st_12 +
    (-1 / 16) * rel4_sh_13 + (1 / 16) * rel4_st_13 + (3 / 8) * rel4_sh_14 + (3 / 16) * rel4_st_15 +
    (1 / 4) * rel4_sh_16 + (-1 / 4) * rel4_dist_4

theorem hpl_negOne_negOne_one_negOne_at_one :
    hpl [negOne, negOne, one, negOne] 1 =
      3 * Li 4 (1 / 2) + 1 / 12 * log 2 ^ 4 - 1 / 8 * log 2 ^ 2 * π ^ 2
      + 11 / 4 * log 2 * zeta3 - 1 / 30 * π ^ 4 := by
  linear_combination (-1 / 8) * rel4_sh_0 + (-3 / 8) * rel4_st_0 + (13 / 8) * rel4_sh_1 +
    (1 / 2) * rel4_sh_2 + (-5 / 8) * rel4_st_2 + (1 / 2) * rel4_sh_3 + (1 / 8) * rel4_st_3 +
    (-1 / 4) * rel4_st_4 + (1) * rel4_sh_5 + (-1 / 8) * rel4_st_6 + (-1) * rel4_sh_7 +
    (1 / 8) * rel4_st_7 + (1 / 4) * rel4_st_8 + (3 / 8) * rel4_sh_9 + (1 / 8) * rel4_st_10 +
    (1 / 8) * rel4_sh_13 + (3 / 8) * rel4_st_13 + (-1 / 4) * rel4_sh_14 + (-15 / 8) * rel4_st_15 +
    (-1 / 2) * rel4_sh_16 + (-3) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_negOne_negOne_one_at_one :
    hpl [negOne, negOne, negOne, one] 1 =
      -Li 4 (1 / 2) - 1 / 12 * log 2 ^ 4 + 1 / 24 * log 2 ^ 2 * π ^ 2
      - 7 / 8 * log 2 * zeta3 + 1 / 90 * π ^ 4 := by
  linear_combination (1 / 24) * rel4_sh_0 + (1 / 8) * rel4_st_0 + (-13 / 24) * rel4_sh_1 +
    (-1 / 6) * rel4_sh_2 + (5 / 24) * rel4_st_2 + (-1 / 6) * rel4_sh_3 + (-1 / 24) * rel4_st_3 +
    (1 / 12) * rel4_st_4 + (-1 / 3) * rel4_sh_5 + (1 / 24) * rel4_st_6 + (1 / 3) * rel4_sh_7 +
    (-1 / 24) * rel4_st_7 + (-1 / 12) * rel4_st_8 + (-1 / 8) * rel4_sh_9 + (1 / 3) * rel4_sh_10 +
    (-1 / 24) * rel4_st_10 + (-1 / 24) * rel4_sh_13 + (-1 / 8) * rel4_st_13 +
    (1 / 12) * rel4_sh_14 + (5 / 8) * rel4_st_15 + (1 / 6) * rel4_sh_16 +
    (1) * hpl_zero_negOne_negOne_negOne_at_one

theorem hpl_negOne_negOne_negOne_negOne_at_one :
    hpl [negOne, negOne, negOne, negOne] 1 =
      1 / 24 * log 2 ^ 4 := by
  linear_combination (1 / 4) * rel4_sh_11

end QED.Polylog.HPL
