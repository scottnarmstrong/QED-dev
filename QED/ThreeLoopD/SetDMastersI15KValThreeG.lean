/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.Polylog.ExtraIntegrals
import QED.Polylog.HPLCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Set (d), master `I₁₅`: calculus for the weight-three primitives of `F₃`

The inner integrals of `F₃` have primitives built from

* `G(X) = Li₃ X - Li₂ X log X`, whose derivative `log X log (1 - X) X'/X` is a product of
  logarithms (the `Li₂` terms cancel), and `Li₂ X`, at arguments `X ∈ (0, 1)`;
* polynomials in `t`, a logarithm `L` singular at `t = 0` and three functions `a, b, c`
  vanishing at `t = 0` (`QED.ThreeLoopD.i15TPoly`, a list of monomials).

This file gives the derivatives of these building blocks, with the logarithms of the arguments
supplied as hypotheses, and the limit of such a polynomial at `0⁺` when `L = log t`,
`|a|, |b|, |c| ≤ C t` and no monomial is a pure power of `L`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15TG_comp`, `QED.ThreeLoopD.hasDerivAt_i15TLi₂_comp`.
* `QED.ThreeLoopD.hasDerivAt_i15TPoly`, `QED.ThreeLoopD.tendsto_i15TPoly_zero`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- `G(X) = Li₃ X - Li₂ X log X`. -/
noncomputable def i15TG (x : ℝ) : ℝ := Li₃ x - Li₂ x * log x

theorem hasDerivAt_i15TG_comp {X : ℝ → ℝ} {d a b y : ℝ} (hX : HasDerivAt X (X y * d) y)
    (hm : X y ∈ Ioo (0 : ℝ) 1) (ha : log (X y) = a) (hb : log (1 - X y) = b) :
    HasDerivAt (fun t => i15TG (X t)) (a * b * d) y := by
  have h0 : X y ≠ 0 := hm.1.ne'
  have h := ((hasDerivAt_Li₃' hm).comp y hX).sub
    (((hasDerivAt_Li₂' hm).comp y hX).mul (hX.log h0))
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [← ha, ← hb]
  field_simp
  ring

theorem hasDerivAt_i15TLi₂_comp {X : ℝ → ℝ} {d b y : ℝ} (hX : HasDerivAt X (X y * d) y)
    (hm : X y ∈ Ioo (0 : ℝ) 1) (hb : log (1 - X y) = b) :
    HasDerivAt (fun t => Li₂ (X t)) (-b * d) y := by
  have h0 : X y ≠ 0 := hm.1.ne'
  refine ((hasDerivAt_Li₂' hm).comp y hX).congr_deriv ?_
  rw [← hb]
  field_simp

theorem continuousOn_i15TG : ContinuousOn i15TG (Ioc 0 1) := by
  refine (continuousOn_Li₃.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩).sub
    ((continuousOn_Li₂.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩).mul ?_)
  exact continuousOn_log.mono fun x hx => hx.1.ne'

theorem i15TG_one : i15TG 1 = zeta3 := by simp [i15TG, Li₃_one]

theorem tendsto_i15TG_zero : Tendsto i15TG (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_Li₃_zero_right.sub (tendsto_log_mul_Li₂_zero)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards with x
  simp only [i15TG]
  ring

/-! ### Polynomials in `t`, a logarithm and three small functions -/

/-- The monomial `t ^ e₀ L ^ e₁ a ^ e₂ b ^ e₃ c ^ e₄`. -/
def i15TMono (e : ℕ × ℕ × ℕ × ℕ × ℕ) (t L a b c : ℝ) : ℝ :=
  t ^ e.1 * L ^ e.2.1 * a ^ e.2.2.1 * b ^ e.2.2.2.1 * c ^ e.2.2.2.2

/-- The derivative of `QED.ThreeLoopD.i15TMono` along `(1, L', a', b', c')`. -/
def i15TMonoD (e : ℕ × ℕ × ℕ × ℕ × ℕ) (t L a b c dL da db dc : ℝ) : ℝ :=
  (e.1 : ℝ) * t ^ (e.1 - 1) * L ^ e.2.1 * a ^ e.2.2.1 * b ^ e.2.2.2.1 * c ^ e.2.2.2.2 +
    t ^ e.1 * ((e.2.1 : ℝ) * L ^ (e.2.1 - 1) * dL) * a ^ e.2.2.1 * b ^ e.2.2.2.1 *
      c ^ e.2.2.2.2 +
    t ^ e.1 * L ^ e.2.1 * ((e.2.2.1 : ℝ) * a ^ (e.2.2.1 - 1) * da) * b ^ e.2.2.2.1 *
      c ^ e.2.2.2.2 +
    t ^ e.1 * L ^ e.2.1 * a ^ e.2.2.1 * ((e.2.2.2.1 : ℝ) * b ^ (e.2.2.2.1 - 1) * db) *
      c ^ e.2.2.2.2 +
    t ^ e.1 * L ^ e.2.1 * a ^ e.2.2.1 * b ^ e.2.2.2.1 *
      ((e.2.2.2.2 : ℝ) * c ^ (e.2.2.2.2 - 1) * dc)

/-- A polynomial: the sum of `cₘ · monomial` over a list. -/
def i15TPoly (P : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ))) (t L a b c : ℝ) : ℝ :=
  (P.map fun m => m.1 * i15TMono m.2 t L a b c).sum

/-- The derivative of `QED.ThreeLoopD.i15TPoly`. -/
def i15TPolyD (P : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ))) (t L a b c dL da db dc : ℝ) : ℝ :=
  (P.map fun m => m.1 * i15TMonoD m.2 t L a b c dL da db dc).sum

theorem hasDerivAt_i15TMono (e : ℕ × ℕ × ℕ × ℕ × ℕ) {L a b c : ℝ → ℝ} {dL da db dc y : ℝ}
    (hL : HasDerivAt L dL y) (ha : HasDerivAt a da y) (hb : HasDerivAt b db y)
    (hc : HasDerivAt c dc y) :
    HasDerivAt (fun t => i15TMono e t (L t) (a t) (b t) (c t))
      (i15TMonoD e y (L y) (a y) (b y) (c y) dL da db dc) y := by
  have h := (((((hasDerivAt_id y).pow e.1).mul (hL.pow e.2.1)).mul (ha.pow e.2.2.1)).mul
    (hb.pow e.2.2.2.1)).mul (hc.pow e.2.2.2.2)
  refine h.congr_deriv ?_
  simp only [i15TMonoD, Pi.mul_apply, Pi.pow_apply, id]
  ring

theorem hasDerivAt_i15TPoly (P : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ))) {L a b c : ℝ → ℝ}
    {dL da db dc y : ℝ} (hL : HasDerivAt L dL y) (ha : HasDerivAt a da y)
    (hb : HasDerivAt b db y) (hc : HasDerivAt c dc y) :
    HasDerivAt (fun t => i15TPoly P t (L t) (a t) (b t) (c t))
      (i15TPolyD P y (L y) (a y) (b y) (c y) dL da db dc) y := by
  induction P with
  | nil => simpa [i15TPoly, i15TPolyD] using hasDerivAt_const y (0 : ℝ)
  | cons m P ih =>
    have h := ((hasDerivAt_i15TMono m.2 hL ha hb hc).const_mul m.1).add ih
    simp only [i15TPoly, i15TPolyD, List.map_cons, List.sum_cons] at h ⊢
    exact h

/-- `|x| ≤ M t` for each factor gives `|∏ xᵢ ^ nᵢ| ≤ (M t) ^ (∑ nᵢ)`. -/
theorem i15T_abs_mono_le {t L a b c M : ℝ} (e : ℕ × ℕ × ℕ × ℕ × ℕ) (ht : |t| ≤ M * t)
    (ha : |a| ≤ M * t) (hb : |b| ≤ M * t) (hc : |c| ≤ M * t) :
    |i15TMono e t L a b c| ≤
      (M * t) ^ (e.1 + e.2.2.1 + e.2.2.2.1 + e.2.2.2.2) * |L| ^ e.2.1 := by
  simp only [i15TMono, abs_mul, abs_pow, pow_add]
  have h1 := pow_le_pow_left₀ (abs_nonneg _) ht e.1
  have h2 := pow_le_pow_left₀ (abs_nonneg _) ha e.2.2.1
  have h3 := pow_le_pow_left₀ (abs_nonneg _) hb e.2.2.2.1
  have h4 := pow_le_pow_left₀ (abs_nonneg _) hc e.2.2.2.2
  have hL := pow_nonneg (abs_nonneg L) e.2.1
  have hM := (abs_nonneg t).trans ht
  have p1 := pow_nonneg hM e.1
  have p2 := pow_nonneg hM e.2.2.1
  have p3 := pow_nonneg hM e.2.2.2.1
  have q1 := pow_nonneg (abs_nonneg t) e.1
  have q2 := pow_nonneg (abs_nonneg a) e.2.2.1
  have q3 := pow_nonneg (abs_nonneg b) e.2.2.2.1
  have q4 := pow_nonneg (abs_nonneg c) e.2.2.2.2
  calc |t| ^ e.1 * |L| ^ e.2.1 * |a| ^ e.2.2.1 * |b| ^ e.2.2.2.1 * |c| ^ e.2.2.2.2
      = (|t| ^ e.1 * |a| ^ e.2.2.1 * |b| ^ e.2.2.2.1 * |c| ^ e.2.2.2.2) * |L| ^ e.2.1 := by
        ring
    _ ≤ ((M * t) ^ e.1 * (M * t) ^ e.2.2.1 * (M * t) ^ e.2.2.2.1 * (M * t) ^ e.2.2.2.2) *
        |L| ^ e.2.1 := by
        refine mul_le_mul_of_nonneg_right ?_ hL
        refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 q2 p1) h3 q3 (mul_nonneg p1 p2)) h4 q4
          (mul_nonneg (mul_nonneg p1 p2) p3)
    _ = _ := by ring

theorem tendsto_i15TMono_zero (e : ℕ × ℕ × ℕ × ℕ × ℕ) {a b c : ℝ → ℝ} {C : ℝ}
    (ha : ∀ t ∈ Ioo (0 : ℝ) 1, |a t| ≤ C * t) (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |b t| ≤ C * t)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, |c t| ≤ C * t)
    (he : e.2.1 ≠ 0 → e.1 + e.2.2.1 + e.2.2.2.1 + e.2.2.2.2 ≠ 0) :
    Tendsto (fun t => i15TMono e t (log t) (a t) (b t) (c t)) (𝓝[>] 0)
      (𝓝 (i15TMono e 0 1 0 0 0)) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := e
  simp only at he ⊢
  by_cases hs : e0 + e2 + e3 + e4 = 0
  · have h1 : e1 = 0 := by_contra fun h => he h hs
    obtain ⟨⟨⟨h0, h2⟩, h3⟩, h4⟩ : ((e0 = 0 ∧ e2 = 0) ∧ e3 = 0) ∧ e4 = 0 := by omega
    subst h0 h1 h2 h3 h4
    simp [i15TMono]
  · set s := e0 + e2 + e3 + e4 with hs_def
    have hv : i15TMono (e0, e1, e2, e3, e4) 0 1 0 0 0 = 0 := by
      simp only [i15TMono]
      rcases Nat.eq_zero_or_pos e0 with h0 | h0
      · rcases Nat.eq_zero_or_pos e2 with h2 | h2
        · rcases Nat.eq_zero_or_pos e3 with h3 | h3
          · have h4 : e4 ≠ 0 := by omega
            simp [zero_pow h4]
          · simp [zero_pow h3.ne']
        · simp [zero_pow h2.ne']
      · simp [zero_pow h0.ne']
    rw [hv]
    obtain ⟨K, hK0, hK⟩ := HPL.abs_log_pow_le e1 (by norm_num : (0 : ℝ) < 1 / 2)
    set M := max C 1
    refine HPL.tendsto_zero_of_abs_le_rpow (C := M ^ s * K) (r := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) fun t ht => ?_
    have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
    have hM1 : 1 ≤ M := le_max_right _ _
    have hM : ∀ x : ℝ, |x| ≤ C * t → |x| ≤ M * t := fun x hx =>
      hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht1.1.le)
    have htt : |t| ≤ M * t := by
      rw [abs_of_pos ht1.1]; nlinarith [ht1.1]
    have hb' := i15T_abs_mono_le (L := log t) (e0, e1, e2, e3, e4) htt (hM _ (ha t ht1))
      (hM _ (hb t ht1)) (hM _ (hc t ht1))
    simp only at hb'
    rw [← hs_def] at hb'
    have hlog := hK t ⟨ht1.1, ht1.2.le⟩
    have hts : t ^ s ≤ t := by
      calc t ^ s ≤ t ^ 1 := pow_le_pow_of_le_one ht1.1.le ht1.2.le (by omega)
        _ = t := pow_one t
    have hrp : t * t ^ (-(1 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' ht1.1.le (by norm_num)]
      · norm_num
    calc |i15TMono (e0, e1, e2, e3, e4) t (log t) (a t) (b t) (c t)|
        ≤ (M * t) ^ s * |log t| ^ e1 := hb'
      _ = M ^ s * t ^ s * |log t| ^ e1 := by rw [mul_pow]
      _ ≤ M ^ s * t * (K * t ^ (-(1 / 2 : ℝ))) := by
        have hMs : 0 ≤ M ^ s := pow_nonneg (by linarith) s
        exact mul_le_mul (mul_le_mul_of_nonneg_left hts hMs) hlog
          (pow_nonneg (abs_nonneg _) _) (mul_nonneg hMs ht1.1.le)
      _ = M ^ s * K * (t * t ^ (-(1 / 2 : ℝ))) := by ring
      _ = M ^ s * K * t ^ (1 / 2 : ℝ) := by rw [hrp]

/-- The value at `0⁺` of a polynomial with no pure powers of the logarithm. -/
theorem tendsto_i15TPoly_zero (P : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ))) {a b c : ℝ → ℝ} {C : ℝ}
    (ha : ∀ t ∈ Ioo (0 : ℝ) 1, |a t| ≤ C * t) (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |b t| ≤ C * t)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, |c t| ≤ C * t)
    (hP : ∀ m ∈ P, m.2.2.1 ≠ 0 → m.2.1 + m.2.2.2.1 + m.2.2.2.2.1 + m.2.2.2.2.2 ≠ 0) :
    Tendsto (fun t => i15TPoly P t (log t) (a t) (b t) (c t)) (𝓝[>] 0)
      (𝓝 (i15TPoly P 0 1 0 0 0)) := by
  induction P with
  | nil => simp [i15TPoly]
  | cons m P ih =>
    have h1 := (tendsto_i15TMono_zero m.2 ha hb hc (hP m (by simp))).const_mul m.1
    have h2 := ih fun m' hm' => hP m' (by simp [hm'])
    simpa [i15TPoly] using h1.add h2

/-- `QED.ThreeLoopD.tendsto_i15TPoly_zero` with the condition on the exponent list alone. -/
theorem tendsto_i15TPoly_zero' (P : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ))) {a b c : ℝ → ℝ} {C : ℝ}
    (ha : ∀ t ∈ Ioo (0 : ℝ) 1, |a t| ≤ C * t) (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |b t| ≤ C * t)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, |c t| ≤ C * t)
    (hP : ∀ e ∈ P.map Prod.snd, e.2.1 ≠ 0 → e.1 + e.2.2.1 + e.2.2.2.1 + e.2.2.2.2 ≠ 0) :
    Tendsto (fun t => i15TPoly P t (log t) (a t) (b t) (c t)) (𝓝[>] 0)
      (𝓝 (i15TPoly P 0 1 0 0 0)) :=
  tendsto_i15TPoly_zero P ha hb hc fun m hm => hP m.2 (List.mem_map_of_mem hm)

/-! ### Arguments given through their logarithms -/

/-- A positive function whose logarithm `ℓ` is differentiable has derivative `X · ℓ'`. -/
theorem i15T_hasDerivAt_of_log {X ℓ : ℝ → ℝ} {d y : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 y)
    (hX : ∀ t ∈ s, 0 < X t ∧ log (X t) = ℓ t) (hℓ : HasDerivAt ℓ d y) :
    HasDerivAt X (X y * d) y := by
  have he : (fun t => exp (ℓ t)) =ᶠ[𝓝 y] X := by
    filter_upwards [hs] with t ht
    rw [← (hX t ht).2, exp_log (hX t ht).1]
  have h := hℓ.exp
  rw [← (hX y (mem_of_mem_nhds hs)).2, exp_log (hX y (mem_of_mem_nhds hs)).1] at h
  exact h.congr_of_eventuallyEq he.symm

theorem i15T_tendsto_TG {X : ℝ → ℝ} (hc : ContinuousAt X 0) (hX0 : X 0 ∈ Ioc (0 : ℝ) 1)
    (hX : ∀ u ∈ Ioo (0 : ℝ) 1, X u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun u => i15TG (X u)) (𝓝[>] 0) (𝓝 (i15TG (X 0))) := by
  have h1 : Tendsto X (𝓝[>] 0) (𝓝[Ioc 0 1] (X 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
    exact ⟨(hX u hu).1, (hX u hu).2.le⟩
  exact (continuousOn_i15TG _ hX0).tendsto.comp h1

theorem i15T_tendsto_TG_zero {X : ℝ → ℝ} (hc : ContinuousAt X 0) (hX0 : X 0 = 0)
    (hX : ∀ u ∈ Ioo (0 : ℝ) 1, X u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun u => i15TG (X u)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto X (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [hX0] at this
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
      exact (hX u hu).1
  exact tendsto_i15TG_zero.comp h1

theorem i15T_tendsto_Li₂ {X : ℝ → ℝ} (hc : ContinuousAt X 0) (hX0 : X 0 ∈ Icc (0 : ℝ) 1)
    (hX : ∀ u ∈ Ioo (0 : ℝ) 1, X u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun u => Li₂ (X u)) (𝓝[>] 0) (𝓝 (Li₂ (X 0))) := by
  refine tendsto_Li₂_comp ⟨by linarith [hX0.1], hX0.2⟩
    (hc.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
  exact ⟨by linarith [(hX u hu).1], (hX u hu).2.le⟩

end QED.ThreeLoopD
