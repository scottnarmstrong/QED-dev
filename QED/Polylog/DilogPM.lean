/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
import QED.Polylog.LiCalculus
import QED.Polylog.Landen
import QED.Polylog.Reflection
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Dilogarithms of the alphabet `{u, 1 - u, 1 + u}`

For `0 < u < 1`, the dilogarithm of every argument built from the letters `u, 1 - u, 1 + u, 2`
that is used by the sixth-order vacuum-polarization integrals reduces to the three functions
`Li 2 u`, `Li 2 (-u)`, `Li 2 ((1 - u) / 2)` and products of logarithms. Write
`t = (1 - u)/(1 + u)`.

## Main results

* `QED.Polylog.Li_two_one_sub'`: `Li 2 (1 - u)` (Euler reflection).
* `QED.Polylog.Li_two_div_one_add`: `Li 2 (u/(1+u)) = -Li 2 (-u) - ½ log² (1+u)` (Landen).
* `QED.Polylog.Li_two_inv_one_add`: `Li 2 (1/(1+u))`.
* `QED.Polylog.Li_two_neg_ksT`: `Li 2 (-t) = -Li 2 ((1-u)/2) - ½ log² ((1+u)/2)` (Landen).
* `QED.Polylog.Li_two_one_add_div_two`: `Li 2 ((1+u)/2)` (reflection).
* `QED.Polylog.Li_two_ksT`: `Li 2 t`, the one genuinely two-term identity, proved by
  differentiation.
* `QED.Polylog.Li_two_two_mul_div`: `Li 2 (2u/(1+u))`; `QED.Polylog.Li_two_sq'`: `Li 2 (u²)`;
  `QED.Polylog.Li_two_one_sub_sq`: `Li 2 (1 - u²)`; `QED.Polylog.Li_two_ksT_sq`: `Li 2 (t²)`.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog

variable {u : ℝ}

/-- Euler reflection in the form `Li 2 (1 - u) = π²/6 - log u log (1 - u) - Li 2 u`. -/
theorem Li_two_one_sub' (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (1 - u) = π ^ 2 / 6 - log u * log (1 - u) - Li 2 u := by
  have h := Li₂_add_Li₂_one_sub hu.1.le hu.2.le
  rw [Li_two]
  linarith

/-- Landen: `Li 2 (u/(1+u)) = -Li 2 (-u) - ½ log² (1+u)`. -/
theorem Li_two_div_one_add (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (u / (1 + u)) = -Li 2 (-u) - log (1 + u) ^ 2 / 2 := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  have h := Li₂_one_sub_inv_add_Li₂_one_sub (x := 1 / (1 + u))
    (by rw [le_div_iff₀ hp]; linarith) (by rw [div_le_one hp]; linarith)
  rw [one_div, inv_inv, show 1 - (1 + u) = -u by ring,
    show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring, Real.log_inv, neg_sq] at h
  rw [Li_two]
  linarith

/-- `Li 2 (1/(1+u)) = π²/6 + log u log (1+u) - ½ log² (1+u) + Li 2 (-u)`. -/
theorem Li_two_inv_one_add (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (1 / (1 + u)) =
      π ^ 2 / 6 + log u * log (1 + u) - log (1 + u) ^ 2 / 2 + Li 2 (-u) := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  have h := Li₂_add_Li₂_one_sub (x := u / (1 + u)) (by positivity)
    (by rw [div_le_one hp]; linarith)
  rw [show 1 - u / (1 + u) = 1 / (1 + u) by field_simp; ring, log_div h0.ne' hp.ne',
    one_div, Real.log_inv, ← one_div] at h
  have h2 := Li_two_div_one_add ⟨h0, h1⟩
  rw [Li_two] at h2 ⊢
  linarith

/-- Landen: `Li 2 (-(1-u)/(1+u)) = -Li 2 ((1-u)/2) - ½ (log (1+u) - log 2)²`. -/
theorem Li_two_neg_ksT (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (-((1 - u) / (1 + u))) = -Li 2 ((1 - u) / 2) - (log (1 + u) - log 2) ^ 2 / 2 := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  have h := Li₂_one_sub_inv_add_Li₂_one_sub (x := (1 + u) / 2) (by linarith) (by linarith)
  rw [show 1 - ((1 + u) / 2)⁻¹ = -((1 - u) / (1 + u)) by field_simp; ring,
    show 1 - (1 + u) / 2 = (1 - u) / 2 by ring, log_div hp.ne' (by norm_num)] at h
  rw [Li_two]
  linarith

/-- Reflection: `Li 2 ((1+u)/2) = π²/6 - (log (1-u) - log 2)(log (1+u) - log 2)
- Li 2 ((1-u)/2)`. -/
theorem Li_two_one_add_div_two (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 ((1 + u) / 2) =
      π ^ 2 / 6 - (log (1 - u) - log 2) * (log (1 + u) - log 2) - Li 2 ((1 - u) / 2) := by
  obtain ⟨h0, h1⟩ := hu
  have h := Li₂_add_Li₂_one_sub (x := (1 - u) / 2) (by linarith) (by linarith)
  rw [show 1 - (1 - u) / 2 = (1 + u) / 2 by ring, log_div (by linarith) (by norm_num),
    log_div (by linarith) (by norm_num)] at h
  rw [Li_two]
  linarith

/-! ### The two-term identity for `Li 2 ((1-u)/(1+u))` -/

/-- The combination that `Li_two_ksT` shows to be constant. -/
private noncomputable def ksTComb (x : ℝ) : ℝ :=
  Li 2 ((1 - x) / (1 + x)) + Li 2 x - Li 2 (-x) + Li 2 ((1 - x) / 2) + log x * log (1 - x) -
    log x * log (1 + x) + log (1 + x) ^ 2 / 2 - log (1 + x) * log 2

private lemma hasDerivAt_ksTComb {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt ksTComb 0 x := by
  obtain ⟨h0, h1⟩ := hx
  have hm : 0 < 1 - x := by linarith
  have hp : 0 < 1 + x := by linarith
  have ht0 : 0 < (1 - x) / (1 + x) := by positivity
  have ht1 : (1 - x) / (1 + x) < 1 := by rw [div_lt_one hp]; linarith
  have hT : HasDerivAt (fun y : ℝ => (1 - y) / (1 + y)) (-2 / (1 + x) ^ 2) x := by
    have := ((hasDerivAt_id x).const_sub 1).div ((hasDerivAt_id x).const_add 1) hp.ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hH : HasDerivAt (fun y : ℝ => (1 - y) / 2) (-1 / 2) x := by
    have := ((hasDerivAt_id' x).const_sub 1).div_const 2
    simpa using this
  have e1 := hasDerivAt_Li_two_comp hT (abs_lt.2 ⟨by linarith, ht1⟩) ht0.ne'
  have e2 := hasDerivAt_Li_two_comp (hasDerivAt_id' x) (abs_lt.2 ⟨by linarith, h1⟩) h0.ne'
  have e3 := hasDerivAt_Li_two_comp (hasDerivAt_neg x) (abs_lt.2 ⟨by linarith, by linarith⟩)
    (by simp only [ne_eq, neg_eq_zero]; exact h0.ne')
  have e4 := hasDerivAt_Li_two_comp hH (abs_lt.2 ⟨by linarith, by linarith⟩)
    (show (1 - x) / 2 ≠ 0 by positivity)
  have l0 := Real.hasDerivAt_log h0.ne'
  have l1 := ((hasDerivAt_id' x).const_sub 1).log hm.ne'
  have lp := ((hasDerivAt_id' x).const_add 1).log hp.ne'
  have h := ((((((e1.add e2).sub e3).add e4).add (l0.mul l1)).sub (l0.mul lp)).add
    ((lp.pow 2).div_const 2)).sub (lp.mul_const (log 2))
  refine h.congr_deriv ?_
  rw [show 1 - (1 - x) / (1 + x) = 2 * x / (1 + x) by field_simp; ring,
    show 1 - (1 - x) / 2 = (1 + x) / 2 by ring, sub_neg_eq_add,
    log_div (by positivity) hp.ne', log_mul (by norm_num) h0.ne',
    log_div hp.ne' (by norm_num)]
  field_simp
  ring

/-- `log x · log (1 + x) → 0` as `x → 0⁺`. -/
theorem tendsto_log_mul_log_one_add_zero :
    Tendsto (fun x => log x * log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_mul_log_zero.mul tendsto_log_one_add_div_zero
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  field_simp

private lemma tendsto_ksTComb :
    Tendsto ksTComb (𝓝[>] 0) (𝓝 (π ^ 2 / 4 - log 2 ^ 2 / 2)) := by
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have hc : ∀ {g : ℝ → ℝ} {a : ℝ}, ContinuousAt g 0 → g 0 = a →
      Tendsto g (𝓝[>] 0) (𝓝 a) := fun hg ha => ha ▸ hg.tendsto.mono_left nhdsWithin_le_nhds
  have t1 := tendsto_Li_comp (k := 2) le_rfl (a := 1) (by norm_num)
    (hc (g := fun y : ℝ => (1 - y) / (1 + y))
      ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
        (by norm_num)) (by norm_num)) (hev.mono fun y hy => by
      have hp : 0 < 1 + y := by linarith [hy.1]
      refine ⟨by rw [le_div_iff₀ hp]; linarith [hy.2], by rw [div_le_one hp]; linarith [hy.1]⟩)
  have t2 := tendsto_Li_comp (k := 2) le_rfl (a := 0) (by norm_num)
    (hc (g := fun y : ℝ => y) continuousAt_id rfl) (hev.mono fun y hy => ⟨by linarith [hy.1],
      hy.2.le⟩)
  have t3 := tendsto_Li_comp (k := 2) le_rfl (a := 0) (by norm_num)
    (hc (g := fun y : ℝ => -y) continuousAt_neg (by norm_num)) (hev.mono fun y hy =>
      ⟨by linarith [hy.2], by linarith [hy.1]⟩)
  have t4 := tendsto_Li_comp (k := 2) le_rfl (a := 1 / 2) (by norm_num)
    (hc (g := fun y : ℝ => (1 - y) / 2) (by fun_prop) (by norm_num)) (hev.mono fun y hy =>
      ⟨by linarith [hy.2], by linarith [hy.1]⟩)
  have t6 := tendsto_log_one_add_zero
  have h := (((((((t1.add t2).sub t3).add t4).add tendsto_log_mul_log_one_sub_zero).sub
    tendsto_log_mul_log_one_add_zero).add ((t6.pow 2).div_const 2)).sub (t6.mul_const (log 2)))
  rw [show Li 2 1 = π ^ 2 / 6 from Li₂_one, show Li 2 (1 / 2) = _ from Li₂_one_half] at h
  unfold ksTComb
  convert h using 2
  simp only [Li_zero]
  ring

/-- The two-term identity `Li 2 ((1-u)/(1+u)) = π²/4 - ½ log² 2 - Li 2 u + Li 2 (-u)
- Li 2 ((1-u)/2) - log u log (1-u) + log u log (1+u) - ½ log² (1+u) + log (1+u) log 2`. -/
theorem Li_two_ksT (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 ((1 - u) / (1 + u)) = π ^ 2 / 4 - log 2 ^ 2 / 2 - Li 2 u + Li 2 (-u) -
      Li 2 ((1 - u) / 2) - log u * log (1 - u) + log u * log (1 + u) -
      log (1 + u) ^ 2 / 2 + log (1 + u) * log 2 := by
  have h := eq_of_hasDerivAt_zero_of_tendsto zero_lt_one (fun x hx => hasDerivAt_ksTComb hx)
    tendsto_ksTComb u hu
  unfold ksTComb at h
  linarith

/-- Reflection of `Li_two_ksT`: `Li 2 (2u/(1+u))`. -/
theorem Li_two_two_mul_div (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (2 * u / (1 + u)) = Li 2 u - Li 2 (-u) + Li 2 ((1 - u) / 2) +
      log (1 - u) * log (1 + u) - log (1 - u) * log 2 - log (1 + u) ^ 2 / 2 + log 2 ^ 2 / 2 -
      π ^ 2 / 12 := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  have h := Li₂_add_Li₂_one_sub (x := (1 - u) / (1 + u)) (by apply div_nonneg <;> linarith)
    (by rw [div_le_one hp]; linarith)
  rw [show 1 - (1 - u) / (1 + u) = 2 * u / (1 + u) by field_simp; ring,
    log_div (by linarith) hp.ne', log_div (by positivity) hp.ne',
    log_mul (by norm_num) h0.ne'] at h
  have h2 := Li_two_ksT ⟨h0, h1⟩
  rw [Li_two] at h2 ⊢
  linarith

/-- Duplication: `Li 2 (u²) = 2 Li 2 u + 2 Li 2 (-u)`. -/
theorem Li_two_sq' (hu : u ∈ Ioo (0 : ℝ) 1) : Li 2 (u ^ 2) = 2 * Li 2 u + 2 * Li 2 (-u) := by
  have h := Li₂_add_Li₂_neg (x := u) (by rw [abs_of_pos hu.1]; exact hu.2.le)
  rw [Li_two]
  linarith

/-- Reflection and duplication: `Li 2 (1 - u²)`. -/
theorem Li_two_one_sub_sq (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (1 - u ^ 2) =
      π ^ 2 / 6 - 2 * Li 2 u - 2 * Li 2 (-u) - 2 * log u * (log (1 - u) + log (1 + u)) := by
  obtain ⟨h0, h1⟩ := hu
  have h := Li₂_add_Li₂_one_sub (x := u ^ 2) (by positivity) (by nlinarith)
  rw [log_pow, show 1 - u ^ 2 = (1 - u) * (1 + u) by ring,
    log_mul (by linarith) (by linarith)] at h
  have h2 := Li_two_sq' ⟨h0, h1⟩
  rw [Li_two] at h2 ⊢
  rw [show 1 - u ^ 2 = (1 - u) * (1 + u) by ring]
  push_cast at h
  linarith

/-- Duplication of `Li_two_ksT`: `Li 2 (((1-u)/(1+u))²)`. -/
theorem Li_two_ksT_sq (hu : u ∈ Ioo (0 : ℝ) 1) :
    Li 2 (((1 - u) / (1 + u)) ^ 2) = π ^ 2 / 2 - 2 * log 2 ^ 2 - 2 * Li 2 u + 2 * Li 2 (-u) -
      4 * Li 2 ((1 - u) / 2) - 2 * log u * log (1 - u) + 2 * log u * log (1 + u) -
      2 * log (1 + u) ^ 2 + 4 * log (1 + u) * log 2 := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  have h := Li₂_add_Li₂_neg (x := (1 - u) / (1 + u)) (by
    rw [abs_le]; constructor
    · rw [le_div_iff₀ hp]; linarith
    · rw [div_le_one hp]; linarith)
  have h2 := Li_two_ksT ⟨h0, h1⟩
  have h3 := Li_two_neg_ksT ⟨h0, h1⟩
  rw [Li_two] at h2 h3 ⊢
  linarith

end QED.Polylog
