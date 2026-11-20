/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

/-!
# (R-Π₄) step L9, D3e: the scaling form of a dilation-covariant functional

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3e. Model-free. A functional of Pauli–Villars-closed measures on `x = M² > 0` is
recorded by its values `T x s` on `ν_x = δ_x + (x - 2) δ_1 + (1 - x) δ_2`; it is invariant under
the dilations `(x, s) ↦ (Λ x, Λ s)` iff `DecDil T` holds. Then:

* `dec_eq_decR_decGt`: `T = decR g` with the raw profile `g σ = T(1/|σ|, sign σ)`, where
  `decR G x s = G(s/x) + (x - 2) G(s) + (1 - x) G(s/2)` (the scaling form on `ν_x`); `g` is
  determined only up to `p + q/σ` on each half line, and need not be regular at `0`;
* `decSer`: the dilation series `∑_{j ≥ 0} w_j f(σ / 4^{j+1})`, summable and Lipschitz near `0`
  for `f` Lipschitz near `0` with `f 0 = 0`;
* `dec_exists_scal`: **if `T x ·` is continuous at `0` with value `0` for every `x > 0`, and
  `T 4 ·`, `T 8 ·` are Lipschitz near `0`, then `T = decR G` for the regular profile
  `G = -∑_{j ≥ 1} α(4^{-j} σ) - ∑_{j ≥ 1} 4^{-j} β(4^{-j} σ)`**, with `G 0 = 0` and `G`
  Lipschitz near `0` (`α`, `β`: the values at the two fixed configurations of masses
  `1, 2, 4, 8`).
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.RPi4

/-- **The scaling form on `ν_x = δ_x + (x - 2) δ_1 + (1 - x) δ_2`**:
`G(s/x) + (x - 2) G(s) + (1 - x) G(s/2)`. -/
noncomputable def decR (G : ℝ → ℂ) (x s : ℝ) : ℂ :=
  G (s / x) + ((x - 2 : ℝ) : ℂ) * G s + ((1 - x : ℝ) : ℂ) * G (s / 2)

/-- **Dilation covariance** of a functional recorded on the measures `ν_x`: its value on
`Λ_* ν_x = δ_{Λx} + (x - 2) δ_Λ + (1 - x) δ_{2Λ}` at `Λ s` is its value on `ν_x` at `s`. -/
def DecDil (T : ℝ → ℝ → ℂ) : Prop :=
  ∀ Λ x s : ℝ, 0 < Λ → 0 < x → -(4 * min 1 x) < s → -(4 * min 1 Λ) < Λ * s →
    T (Λ * x) (Λ * s) + ((x - 2 : ℝ) : ℂ) * T Λ (Λ * s) +
      ((1 - x : ℝ) : ℂ) * T (2 * Λ) (Λ * s) = T x s

/-- **The raw profile** `g σ = T(1/|σ|, sign σ)`, `g 0 = 0`. -/
noncomputable def decGt (T : ℝ → ℝ → ℂ) (σ : ℝ) : ℂ :=
  if 0 < σ then T σ⁻¹ 1 else if σ < 0 then T (-σ)⁻¹ (-1) else 0

theorem decR_sub (G H : ℝ → ℂ) (x s : ℝ) :
    decR G x s - decR H x s = decR (fun σ => G σ - H σ) x s := by
  simp only [decR]
  ring

/-- **Every dilation-covariant functional has a scaling form** (with the raw profile). -/
theorem dec_eq_decR_decGt {T : ℝ → ℝ → ℂ} (hdil : DecDil T) (h0 : ∀ x, 0 < x → T x 0 = 0)
    {x s : ℝ} (hx : 0 < x) (hs : -(4 * min 1 x) < s) : T x s = decR (decGt T) x s := by
  rcases lt_trichotomy s 0 with hneg | rfl | hpos
  · have hns : 0 < -s := by linarith
    have hΛ : 0 < (-s)⁻¹ := inv_pos.2 hns
    have h4 : -s < 4 := by have := min_le_left 1 x; linarith
    have hq : (4 : ℝ)⁻¹ < (-s)⁻¹ := (inv_lt_inv₀ (by norm_num) hns).2 h4
    have hm1 : (-s)⁻¹ * s = -1 := by
      have h := inv_mul_cancel₀ hns.ne'
      linear_combination -h
    have hc : -(4 * min 1 (-s)⁻¹) < (-s)⁻¹ * s := by
      rw [hm1]
      have : (4 : ℝ)⁻¹ < min 1 (-s)⁻¹ := lt_min (by norm_num) hq
      linarith
    rw [← hdil _ x s hΛ hx hs hc]
    have hsx : s / x < 0 := div_neg_of_neg_of_pos hneg hx
    simp only [decR, decGt, hsx, hneg, show s / 2 < 0 by linarith, not_lt.2 hsx.le,
      not_lt.2 hneg.le, not_lt.2 (show s / 2 ≤ 0 by linarith), ite_false, ite_true]
    rw [hm1, show (-(s / x))⁻¹ = (-s)⁻¹ * x by field_simp,
      show (-(s / 2))⁻¹ = 2 * (-s)⁻¹ by field_simp]
  · simp [decR, decGt, h0 x hx]
  · have hΛ : 0 < s⁻¹ := inv_pos.2 hpos
    have hc : -(4 * min 1 s⁻¹) < s⁻¹ * s := by
      rw [inv_mul_cancel₀ hpos.ne']
      have := lt_min zero_lt_one hΛ
      linarith
    rw [← hdil _ x s hΛ hx hs hc]
    have hsx : 0 < s / x := div_pos hpos hx
    simp only [decR, decGt, hsx, hpos, show 0 < s / 2 by linarith, ite_true]
    rw [inv_mul_cancel₀ hpos.ne', show (s / x)⁻¹ = s⁻¹ * x by field_simp,
      show (s / 2)⁻¹ = 2 * s⁻¹ by field_simp]

/-! ### The dilation series -/

/-- **The dilation series** `∑_{j ≥ 0} w_j f(σ / 4^{j+1})`. -/
noncomputable def decSer (f : ℝ → ℂ) (w : ℕ → ℝ) (σ : ℝ) : ℂ :=
  ∑' j : ℕ, (w j : ℂ) * f (σ / 4 ^ (j + 1))

theorem dec_abs_div_four_pow (σ : ℝ) (j : ℕ) :
    |σ / 4 ^ (j + 1)| = |σ| * (4 : ℝ)⁻¹ ^ (j + 1) := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (j + 1)), inv_pow, div_eq_mul_inv]

theorem dec_hasSum_geom (C : ℝ) :
    HasSum (fun j : ℕ => C * (4 : ℝ)⁻¹ ^ (j + 1)) (C / 3) := by
  have h := (hasSum_geometric_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
    (C * 4⁻¹)
  convert h using 1
  · funext j
    ring
  · norm_num
    ring

variable {f : ℝ → ℂ} {w : ℕ → ℝ} {δ L : ℝ}

theorem dec_summable_ser (hf0 : f 0 = 0) (hδ : 0 < δ)
    (hf : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'|)
    (hw : ∀ j, |w j| ≤ 1) (σ : ℝ) :
    Summable fun j : ℕ => (w j : ℂ) * f (σ / 4 ^ (j + 1)) := by
  have hg : Summable fun j : ℕ => L * |σ| * (4 : ℝ)⁻¹ ^ (j + 1) :=
    (dec_hasSum_geom (L * |σ|)).summable
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have ht : Tendsto (fun j : ℕ => |σ| * (4 : ℝ)⁻¹ ^ (j + 1)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num)
      (by norm_num)).comp (tendsto_add_atTop_nat 1)).const_mul |σ|
    simpa using this
  filter_upwards [ht.eventually_le_const hδ] with j hj
  have hj' : |σ / 4 ^ (j + 1)| ≤ δ := by rwa [dec_abs_div_four_pow]
  have h1 := hf _ 0 hj' (by simpa using hδ.le)
  rw [hf0, sub_zero, sub_zero, dec_abs_div_four_pow] at h1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hL : 0 ≤ L * (|σ| * (4 : ℝ)⁻¹ ^ (j + 1)) := (norm_nonneg _).trans h1
  calc |w j| * ‖f (σ / 4 ^ (j + 1))‖ ≤ 1 * (L * (|σ| * (4 : ℝ)⁻¹ ^ (j + 1))) :=
        mul_le_mul (hw j) h1 (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem decSer_zero (hf0 : f 0 = 0) : decSer f w 0 = 0 := by
  simp [decSer, hf0]

/-- **The dilation series is Lipschitz near `0`**, with a third of the constant. -/
theorem decSer_lip (hf0 : f 0 = 0) (hδ : 0 < δ)
    (hf : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'|)
    (hw : ∀ j, |w j| ≤ 1) {σ σ' : ℝ} (hσ : |σ| ≤ 4 * δ) (hσ' : |σ'| ≤ 4 * δ) :
    ‖decSer f w σ - decSer f w σ'‖ ≤ L / 3 * |σ - σ'| := by
  unfold decSer
  rw [← (dec_summable_ser hf0 hδ hf hw σ).tsum_sub (dec_summable_ser hf0 hδ hf hw σ')]
  have hb : ∀ j : ℕ, ‖(w j : ℂ) * f (σ / 4 ^ (j + 1)) - (w j : ℂ) * f (σ' / 4 ^ (j + 1))‖ ≤
      L * |σ - σ'| * (4 : ℝ)⁻¹ ^ (j + 1) := by
    intro j
    have hq : (4 : ℝ)⁻¹ ^ (j + 1) ≤ 4⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num)
      (Nat.succ_ne_zero j)
    have hq0 : (0 : ℝ) ≤ 4⁻¹ ^ (j + 1) := by positivity
    have hle : ∀ τ : ℝ, |τ| ≤ 4 * δ → |τ / 4 ^ (j + 1)| ≤ δ := by
      intro τ hτ
      rw [dec_abs_div_four_pow]
      nlinarith [abs_nonneg τ]
    have h1 := hf _ _ (hle σ hσ) (hle σ' hσ')
    rw [show σ / 4 ^ (j + 1) - σ' / 4 ^ (j + 1) = (σ - σ') / 4 ^ (j + 1) by ring,
      dec_abs_div_four_pow] at h1
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hL : 0 ≤ L * (|σ - σ'| * (4 : ℝ)⁻¹ ^ (j + 1)) := (norm_nonneg _).trans h1
    calc |w j| * ‖f (σ / 4 ^ (j + 1)) - f (σ' / 4 ^ (j + 1))‖ ≤
          1 * (L * (|σ - σ'| * (4 : ℝ)⁻¹ ^ (j + 1))) :=
          mul_le_mul (hw j) h1 (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have := tsum_of_norm_bounded (dec_hasSum_geom (L * |σ - σ'|)) hb
  calc _ ≤ L * |σ - σ'| / 3 := this
    _ = _ := by ring

/-- **The dilation series under `σ ↦ 4σ`**: the first term splits off. -/
theorem decSer_four_mul (hf0 : f 0 = 0) (hδ : 0 < δ)
    (hf : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖f t - f t'‖ ≤ L * |t - t'|)
    (hw : ∀ j, |w j| ≤ 1) (σ : ℝ) :
    decSer f w (4 * σ) = (w 0 : ℂ) * f σ + decSer f (fun j => w (j + 1)) σ := by
  unfold decSer
  rw [(dec_summable_ser hf0 hδ hf hw (4 * σ)).tsum_eq_zero_add]
  congr 1
  · congr 2
    ring
  · refine tsum_congr fun j => ?_
    congr 2
    rw [pow_succ]
    field_simp

/-! ### The regular profile -/

/-- The value at the configuration `-2δ_1 + δ_2 + 2δ_4 - δ_8` (at `4t`). -/
def decα (T : ℝ → ℝ → ℂ) (t : ℝ) : ℂ := 2 * T 4 (4 * t) - T 8 (4 * t)

/-- The value at the configuration `4δ_1 - 4δ_2 - δ_4 + δ_8` (at `4t`). -/
def decβ (T : ℝ → ℝ → ℂ) (t : ℝ) : ℂ := T 8 (4 * t) - T 4 (4 * t)

/-- The weights `4^{-(j+1)}`. -/
noncomputable def decW4 (j : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ (j + 1)

/-- **The regular profile** `G(σ) = -∑_{j ≥ 1} α(4^{-j} σ) - ∑_{j ≥ 1} 4^{-j} β(4^{-j} σ)`. -/
noncomputable def decGreg (T : ℝ → ℝ → ℂ) (σ : ℝ) : ℂ :=
  -(decSer (decα T) (fun _ => 1) σ + decSer (decβ T) decW4 σ)

theorem dec_abs_decW4_le (j : ℕ) : |decW4 j| ≤ 1 := by
  rw [decW4, abs_of_nonneg (by positivity)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- If `P + 4ⁿ Q → 0` then `P = Q = 0`. -/
theorem dec_eq_zero_of_tendsto {P Q : ℂ}
    (h : Tendsto (fun n : ℕ => P + (4 : ℂ) ^ n * Q) atTop (𝓝 0)) : P = 0 ∧ Q = 0 := by
  have hr : Tendsto (fun n : ℕ => ((4 : ℂ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have h1 := (hr.mul h)
  rw [mul_zero] at h1
  have h2 : Tendsto (fun n : ℕ => ((4 : ℂ)⁻¹) ^ n * P + Q) atTop (𝓝 (0 * P + Q)) :=
    (hr.mul_const P).add_const Q
  have hQ : Q = 0 := by
    rw [zero_mul, zero_add] at h2
    refine tendsto_nhds_unique h2 (h1.congr fun n => ?_)
    rw [mul_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, one_mul]
  subst hQ
  simp only [mul_zero, add_zero] at h
  exact ⟨tendsto_nhds_unique tendsto_const_nhds h, rfl⟩

/-- A function vanishing at `0` and Lipschitz on `[-δ, δ]` tends to `0` at `0`. -/
theorem dec_tendsto_of_lip {G : ℝ → ℂ} (hG0 : G 0 = 0) (hδ : 0 < δ)
    (hG : ∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|) :
    Tendsto G (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun σ : ℝ => L * |σ| := by fun_prop
  refine squeeze_zero_norm' ?_ (hc.tendsto' 0 0 (by simp))
  filter_upwards [Icc_mem_nhds (neg_lt_zero.2 hδ) hδ] with σ hσ
  have := hG σ 0 (abs_le.2 hσ) (by simpa using hδ.le)
  rwa [hG0, sub_zero, sub_zero] at this

variable {T : ℝ → ℝ → ℂ}

theorem dec_lip_decα
    (h4 : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖T 4 t - T 4 t'‖ ≤ L * |t - t'|)
    (h8 : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖T 8 t - T 8 t'‖ ≤ L * |t - t'|)
    (t t' : ℝ) (ht : |t| ≤ δ / 4) (ht' : |t'| ≤ δ / 4) :
    ‖decα T t - decα T t'‖ ≤ 12 * L * |t - t'| ∧ ‖decβ T t - decβ T t'‖ ≤ 12 * L * |t - t'| := by
  have e : ∀ τ : ℝ, |τ| ≤ δ / 4 → |4 * τ| ≤ δ := fun τ hτ => by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have a4 := h4 _ _ (e t ht) (e t' ht')
  have a8 := h8 _ _ (e t ht) (e t' ht')
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at a4 a8
  have hL : 0 ≤ L * (4 * |t - t'|) := (norm_nonneg _).trans a4
  have hd : 0 ≤ |t - t'| := abs_nonneg _
  constructor
  · calc ‖decα T t - decα T t'‖ = ‖2 * (T 4 (4 * t) - T 4 (4 * t')) -
          (T 8 (4 * t) - T 8 (4 * t'))‖ := by simp only [decα]; ring_nf
      _ ≤ ‖(2 : ℂ)‖ * ‖T 4 (4 * t) - T 4 (4 * t')‖ + ‖T 8 (4 * t) - T 8 (4 * t')‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 2 * (L * (4 * |t - t'|)) + L * (4 * |t - t'|) := by
          rw [show ‖(2 : ℂ)‖ = 2 by norm_num]; gcongr
      _ ≤ _ := by nlinarith
  · calc ‖decβ T t - decβ T t'‖ = ‖(T 8 (4 * t) - T 8 (4 * t')) -
          (T 4 (4 * t) - T 4 (4 * t'))‖ := by simp only [decβ]; ring_nf
      _ ≤ ‖T 8 (4 * t) - T 8 (4 * t')‖ + ‖T 4 (4 * t) - T 4 (4 * t')‖ := norm_sub_le _ _
      _ ≤ L * (4 * |t - t'|) + L * (4 * |t - t'|) := add_le_add a8 a4
      _ ≤ _ := by nlinarith

/-- The `a`-part of a profile: `-2 g(u) + g(u/2)`. -/
noncomputable def decA₁ (g : ℝ → ℂ) (u : ℝ) : ℂ := -2 * g u + g (u / 2)

/-- The `b`-part of a profile: `g(u) - g(u/2)`. -/
noncomputable def decB₁ (g : ℝ → ℂ) (u : ℝ) : ℂ := g u - g (u / 2)

/-- The `4`-invariant part of the difference of the raw and regular profiles. -/
noncomputable def decAA (T : ℝ → ℝ → ℂ) (u : ℝ) : ℂ :=
  decSer (decα T) (fun _ => 1) u - decA₁ (decGt T) u

/-- The part of the difference of the raw and regular profiles of degree `-1`. -/
noncomputable def decBB (T : ℝ → ℝ → ℂ) (u : ℝ) : ℂ :=
  decSer (decβ T) decW4 u - decB₁ (decGt T) u

theorem decGt_sub_decGreg (u : ℝ) : decGt T u - decGreg T u = decAA T u + decBB T u := by
  simp only [decGreg, decAA, decBB, decA₁, decB₁]
  ring

theorem dec_lt_div_four_pow {σ : ℝ} (hσ : -4 < σ) (n : ℕ) : -1 < σ / 4 ^ (n + 1) := by
  rw [lt_div_iff₀ (by positivity)]
  have : (4 : ℝ) ≤ 4 ^ (n + 1) := le_self_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  nlinarith

theorem dec_four_mul_div_pow (σ : ℝ) (n : ℕ) : 4 * (σ / 4 ^ (n + 1)) = σ / 4 ^ n := by
  rw [pow_succ]
  field_simp

/-- **D3e: the regular scaling form.** A dilation-covariant `T`, continuous at `s = 0` with value
`0` at every `x > 0` and Lipschitz near `0` at `x = 4, 8`, is `decR G` with `G 0 = 0` and `G`
Lipschitz near `0`. -/
theorem dec_exists_scal (hdil : DecDil T) (h0 : ∀ x, 0 < x → T x 0 = 0)
    (hc : ∀ x, 0 < x → Tendsto (T x) (𝓝 0) (𝓝 0)) (hδ : 0 < δ)
    (h4 : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖T 4 t - T 4 t'‖ ≤ L * |t - t'|)
    (h8 : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖T 8 t - T 8 t'‖ ≤ L * |t - t'|) :
    ∃ G : ℝ → ℂ, G 0 = 0 ∧
      (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ 8 * L * |σ - σ'|) ∧
      ∀ x s : ℝ, 0 < x → -(4 * min 1 x) < s → T x s = decR G x s := by
  have hδ4 : 0 < δ / 4 := by positivity
  have hα0 : decα T 0 = 0 := by simp [decα, h0 4 (by norm_num), h0 8 (by norm_num)]
  have hβ0 : decβ T 0 = 0 := by simp [decβ, h0 4 (by norm_num), h0 8 (by norm_num)]
  have hα := fun t t' ht ht' => (dec_lip_decα h4 h8 t t' ht ht').1
  have hβ := fun t t' ht ht' => (dec_lip_decα h4 h8 t t' ht ht').2
  have hw1 : ∀ _ : ℕ, |(1 : ℝ)| ≤ 1 := fun _ => by norm_num
  have hG0 : decGreg T 0 = 0 := by simp [decGreg, decSer_zero hα0, decSer_zero hβ0]
  have hGlip : ∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ →
      ‖decGreg T σ - decGreg T σ'‖ ≤ 8 * L * |σ - σ'| := by
    intro σ σ' hσ hσ'
    have e4 : 4 * (δ / 4) = δ := by ring
    have l1 := decSer_lip hα0 hδ4 hα hw1 (σ := σ) (σ' := σ') (by rwa [e4]) (by rwa [e4])
    have l2 := decSer_lip hβ0 hδ4 hβ dec_abs_decW4_le (σ := σ) (σ' := σ') (by rwa [e4])
      (by rwa [e4])
    calc ‖decGreg T σ - decGreg T σ'‖ = ‖(decSer (decα T) (fun _ => 1) σ -
          decSer (decα T) (fun _ => 1) σ') +
          (decSer (decβ T) decW4 σ - decSer (decβ T) decW4 σ')‖ := by
          rw [decGreg, decGreg, ← norm_neg]; ring_nf
      _ ≤ 12 * L / 3 * |σ - σ'| + 12 * L / 3 * |σ - σ'| := (norm_add_le _ _).trans
          (add_le_add l1 l2)
      _ = _ := by ring
  refine ⟨decGreg T, hG0, hGlip, fun x s hx hs => ?_⟩
  have hrep := fun {y t : ℝ} (hy : 0 < y) (ht : -(4 * min 1 y) < t) =>
    dec_eq_decR_decGt hdil h0 hy ht
  have r48 : ∀ t : ℝ, -1 < t → T 4 (4 * t) = decR (decGt T) 4 (4 * t) ∧
      T 8 (4 * t) = decR (decGt T) 8 (4 * t) := fun t ht =>
    ⟨hrep (by norm_num) (by rw [min_eq_left (by norm_num)]; linarith),
      hrep (by norm_num) (by rw [min_eq_left (by norm_num)]; linarith)⟩
  have hαg : ∀ t : ℝ, -1 < t → decα T t = decA₁ (decGt T) (4 * t) - decA₁ (decGt T) t := by
    intro t ht
    rw [decα, (r48 t ht).1, (r48 t ht).2]
    simp only [decR, decA₁]
    rw [show 4 * t / 4 = t by ring, show 4 * t / 8 = t / 2 by ring]
    push_cast
    ring
  have hβg : ∀ t : ℝ, -1 < t →
      decβ T t = 4 * decB₁ (decGt T) (4 * t) - decB₁ (decGt T) t := by
    intro t ht
    rw [decβ, (r48 t ht).1, (r48 t ht).2]
    simp only [decR, decB₁]
    rw [show 4 * t / 4 = t by ring, show 4 * t / 8 = t / 2 by ring]
    push_cast
    ring
  have hA4 : ∀ τ : ℝ, -1 < τ → decAA T (4 * τ) = decAA T τ := by
    intro τ hτ
    rw [decAA, decAA, decSer_four_mul hα0 hδ4 hα hw1, hαg τ hτ]
    push_cast
    ring
  have hB4 : ∀ τ : ℝ, -1 < τ → decBB T (4 * τ) = decBB T τ / 4 := by
    intro τ hτ
    have e : (fun j : ℕ => decW4 (j + 1)) = fun j => 4⁻¹ * decW4 j := by
      funext j
      simp only [decW4, pow_succ]
      ring
    have hs : decSer (decβ T) (fun j => 4⁻¹ * decW4 j) τ = 4⁻¹ * decSer (decβ T) decW4 τ := by
      simp only [decSer]
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      push_cast
      ring
    rw [decBB, decBB, decSer_four_mul hβ0 hδ4 hβ dec_abs_decW4_le, e, hs, hβg τ hτ]
    simp only [decW4]
    push_cast
    ring
  -- iterate towards `0`
  have hAn : ∀ σ : ℝ, -4 < σ → ∀ n : ℕ, decAA T (σ / 4 ^ n) = decAA T σ := by
    intro σ hσ n
    induction n with
    | zero => simp
    | succ n ih => rw [← ih, ← hA4 _ (dec_lt_div_four_pow hσ n), dec_four_mul_div_pow]
  have hBn : ∀ σ : ℝ, -4 < σ → ∀ n : ℕ, decBB T (σ / 4 ^ n) = 4 ^ n * decBB T σ := by
    intro σ hσ n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hB4 _ (dec_lt_div_four_pow hσ n)
      rw [dec_four_mul_div_pow, ih] at h
      rw [pow_succ (4 : ℂ) n]
      linear_combination -4 * h
  have hs4 : -4 < s := by have := min_le_left 1 x; linarith
  have hsx : -4 < s / x := by
    rw [lt_div_iff₀ hx]
    have := min_le_right 1 x
    linarith
  have hs2 : -4 < s / 2 := by linarith
  -- the error along `s / 4ⁿ`
  have hE : ∀ n : ℕ, T x (s / 4 ^ n) - decR (decGreg T) x (s / 4 ^ n) =
      decR (decAA T) x s + (4 : ℂ) ^ n * decR (decBB T) x s := by
    intro n
    have hsn : -(4 * min 1 x) < s / 4 ^ n := by
      rcases le_or_gt 0 s with h | h
      · have : 0 ≤ s / 4 ^ n := by positivity
        have := lt_min zero_lt_one hx
        linarith
      · have h1 : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        rw [lt_div_iff₀ (by positivity)]
        have hm : 0 < min 1 x := lt_min zero_lt_one hx
        nlinarith
    rw [hrep hx hsn, decR_sub]
    simp only [decGt_sub_decGreg, decR]
    rw [show s / 4 ^ n / x = s / x / 4 ^ n by ring, show s / 4 ^ n / 2 = s / 2 / 4 ^ n by ring,
      hAn _ hsx, hAn _ hs4, hAn _ hs2, hBn _ hsx, hBn _ hs4, hBn _ hs2]
    push_cast
    ring
  have hlim : Tendsto (fun n : ℕ => T x (s / 4 ^ n) - decR (decGreg T) x (s / 4 ^ n)) atTop
      (𝓝 0) := by
    have hsn : Tendsto (fun n : ℕ => s / 4 ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num)
        (by norm_num)).const_mul s
      simpa [div_eq_mul_inv, inv_pow] using this
    have hGt := dec_tendsto_of_lip hG0 hδ hGlip
    have hR : Tendsto (decR (decGreg T) x) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => t / x) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_id.div_const x).tendsto (0 : ℝ))
      have h2 : Tendsto (fun t : ℝ => t / 2) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_id.div_const 2).tendsto (0 : ℝ))
      have := ((hGt.comp h1).add ((hGt.const_mul ((x - 2 : ℝ) : ℂ)))).add
        ((hGt.comp h2).const_mul ((1 - x : ℝ) : ℂ))
      rw [mul_zero, mul_zero, add_zero, add_zero] at this
      exact this
    have := ((hc x hx).comp hsn).sub (hR.comp hsn)
    rw [sub_zero] at this
    exact this
  obtain ⟨hP, hQ⟩ := dec_eq_zero_of_tendsto (hlim.congr hE)
  have := hE 0
  simp only [pow_zero, div_one, one_mul, hP, hQ, add_zero] at this
  exact sub_eq_zero.1 this

end QED.GradedProof.RPi4

end
