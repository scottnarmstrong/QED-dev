/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P0Lines
public import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₂`: the line parameters of `∫ log (𝒰 / σ) / 𝒰²`

`P'(0) = ∫ (1 - w) L / 𝒰²` with `L = 4 log 𝒰 - 3 log ℱ = log 𝒰 - 3 log (ℱ / 𝒰)`. On the domain
`𝒰 ≥ σ = A B + (A + B) C` (its value at `y₄ = y₇ = y₈ = 0`), so `log (𝒰 / σ) / 𝒰² ≥ 0` and its
three line-parameter integrals are lower integrals computed by the fundamental theorem of
calculus on `(0, ∞)`, as for `P(0)` in `QED.ThreeLoopD.SetDMastersI2P0Lines`:

* `y₈`: `∫₀^∞ log (t / s) / t² dy₈ = (1 + log (Q / s)) / (p Q)`, `t = b p + q`, `Q = B p + q`;
* `y₇`: with `z = c² / ((B + c)(a + c))`, `1 - z = Q / ((B + c)(a + c))`, the primitive is
  a combination of `log`, `log²` and `Li₂ z`, giving `QED.ThreeLoopD.i2P1UV7`;
* `y₄`: the primitive is `QED.ThreeLoopD.i2P1UTheta`, symmetric in `A, B, C`.

The `y₄`-primitive comes from Euler's relation for the degree-`(-1)` homogeneous function
`∫ log 𝒰 / 𝒰²`; it is checked here by differentiation (`QED.ThreeLoopD.hasDerivAt_i2P1UTheta`)
and its limit at infinity (`QED.ThreeLoopD.tendsto_i2P1UTheta`).

## Main results

* `QED.ThreeLoopD.i2P1U_lint_y8`, `QED.ThreeLoopD.i2P1U_lint_y7`, `QED.ThreeLoopD.i2P1U_lint_y4`.
* `QED.ThreeLoopD.i2P1U_inner`: the three line integrals of `(1 - w) log (𝒰 / σ) / 𝒰²` equal
  `(1 - w) (Θ(A, B, C) - log σ Ψ(A, B, C))`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The `y₈`-integral:
`∫₀^∞ k log (((y + B) p + q) / s) / ((y + B) p + q)² dy
  = k (1 + log ((B p + q) / s)) / (p (B p + q))` for `s ≤ B p + q`. -/
theorem i2P1U_lint_y8 {k p q B s : ℝ} (hk : 0 ≤ k) (hp : 0 < p) (hs : 0 < s)
    (hsq : s ≤ B * p + q) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (k * log (((y + B) * p + q) / s) / ((y + B) * p + q) ^ 2) =
      ENNReal.ofReal (k * (1 + log ((B * p + q) / s)) / (p * (B * p + q))) := by
  have hQ : 0 < B * p + q := by linarith
  have hge : ∀ y ∈ Ici (0 : ℝ), s ≤ (y + B) * p + q := fun y hy => by
    have : (0 : ℝ) ≤ y := hy
    nlinarith
  have hpos : ∀ y ∈ Ici (0 : ℝ), 0 < (y + B) * p + q := fun y hy => by linarith [hge y hy]
  rw [i3V_lintegral_Ioi_eq (g := fun y => -(k / p) * ((1 + log (((y + B) * p + q) / s)) /
    ((y + B) * p + q))) (l := -(k / p) * 0)]
  · congr 1
    rw [show ((0 : ℝ) + B) * p + q = B * p + q by ring]
    field_simp
    ring
  · intro y hy
    have ht := hpos y hy
    have hf : HasDerivAt (fun y => (y + B) * p + q) p y := by
      simpa using (((hasDerivAt_id y).add_const B).mul_const p).add_const q
    have hl := (hf.div_const s).log (div_pos ht hs).ne'
    refine ((hl.const_add 1).div hf ht.ne' |>.const_mul (-(k / p))).congr_deriv ?_
    generalize (y + B) * p + q = t at ht ⊢
    have := ht.ne'
    have := hp.ne'
    have := hs.ne'
    field_simp
    ring
  · intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
    have h1 := hge y hy0
    have h2 := hpos y hy0
    have : 0 ≤ log (((y + B) * p + q) / s) := log_nonneg ((one_le_div hs).2 h1)
    positivity
  · refine Tendsto.const_mul _ ?_
    have ht : Tendsto (fun y : ℝ => (y + B) * p + q) atTop atTop :=
      tendsto_atTop_add_const_right _ q
        ((tendsto_atTop_add_const_right _ B tendsto_id).atTop_mul_const hp)
    have h1 := tendsto_inv_atTop_zero.comp ht
    have h2 := i3V_tendsto_log_div (α := p / s) (β := (B * p + q) / s) (γ := p) (δ := B * p + q)
      (div_pos hp hs) hp
    have e1 : ∀ y : ℝ, p / s * y + (B * p + q) / s = ((y + B) * p + q) / s := fun y => by
      field_simp
      ring
    have e2 : ∀ y : ℝ, p * y + (B * p + q) = (y + B) * p + q := fun y => by ring
    simp only [e1, e2] at h2
    have h := h1.add h2
    rw [add_zero] at h
    refine h.congr fun y => ?_
    simp only [Function.comp, add_div, one_div]

/-- The value of the `y₇`-integral, `(1 - log s) ℓ + ((l_A + l_B)² - log² σ) / 2 + Li₂ z` over
`c²`, with `l_A = log (A + c)`, `l_B = log (B + c)`, `σ = A B + (A + B) c`,
`ℓ = l_A + l_B - log σ` and `z = c² / ((A + c)(B + c))`. -/
noncomputable def i2P1UV7 (A B c s : ℝ) : ℝ :=
  ((1 - log s) * (log (A + c) + log (B + c) - log (A * B + (A + B) * c)) +
    ((log (A + c) + log (B + c)) ^ 2 - log (A * B + (A + B) * c) ^ 2) / 2 +
    Li₂ (c ^ 2 / ((A + c) * (B + c)))) / c ^ 2

/-- The `y₇`-primitive (up to the factor `k / c²`). -/
noncomputable def i2P1UG7 (A B c s y : ℝ) : ℝ :=
  (1 - log s) * (log ((y + A) * (B + c) + B * c) - log (y + A + c)) +
    (log ((y + A) * (B + c) + B * c) ^ 2 - (log (B + c) + log (y + A + c)) ^ 2) / 2 -
    Li₂ (c ^ 2 / ((B + c) * (y + A + c)))

theorem hasDerivAt_i2P1UG7 {A B c s y : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (hs : 0 < s)
    (hy : 0 ≤ y) :
    HasDerivAt (i2P1UG7 A B c s) (c ^ 2 * (1 + log (((y + A) * (B + c) + B * c) / s)) /
      ((y + A + c) * ((y + A) * (B + c) + B * c))) y := by
  have ha : 0 < y + A + c := by linarith
  have hQ : 0 < (y + A) * (B + c) + B * c := by positivity
  have hBc : 0 < B + c := by linarith
  have dQ : HasDerivAt (fun y => (y + A) * (B + c) + B * c) (B + c) y := by
    simpa using (((hasDerivAt_id y).add_const A).mul_const (B + c)).add_const (B * c)
  have da : HasDerivAt (fun y => y + A + c) 1 y := by
    simpa using ((hasDerivAt_id y).add_const A).add_const c
  have dlQ := dQ.log hQ.ne'
  have dla := da.log ha.ne'
  have hz : c ^ 2 / ((B + c) * (y + A + c)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one (by positivity)).2 (by nlinarith)⟩
  have dz : HasDerivAt (fun y => c ^ 2 / ((B + c) * (y + A + c)))
      (-(c ^ 2 * (B + c)) / ((B + c) * (y + A + c)) ^ 2) y := by
    have := (hasDerivAt_const y (c ^ 2)).div (da.const_mul (B + c)) (by positivity)
    refine this.congr_deriv ?_
    ring
  have dL := (hasDerivAt_Li₂' hz).comp y dz
  have h := (((dlQ.sub dla).const_mul (1 - log s)).add
    (((dlQ.pow 2).sub ((dla.const_add (log (B + c))).pow 2)).div_const 2)).sub dL
  refine h.congr_deriv ?_
  have e : 1 - c ^ 2 / ((B + c) * (y + A + c)) =
      ((y + A) * (B + c) + B * c) / ((B + c) * (y + A + c)) := by
    field_simp
    ring
  rw [e, log_div hQ.ne' (by positivity), log_mul hBc.ne' ha.ne', log_div hQ.ne' hs.ne']
  field_simp
  ring

theorem tendsto_i2P1UG7 {A B c s : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) :
    Tendsto (i2P1UG7 A B c s) atTop (𝓝 ((1 - log s) * log (B + c))) := by
  have hBc : 0 < B + c := by linarith
  -- the three pieces
  have hX : Tendsto (fun y : ℝ => (B + c) * (y + A + c)) atTop atTop :=
    (tendsto_atTop_add_const_right _ c
      (tendsto_atTop_add_const_right _ A tendsto_id)).const_mul_atTop hBc
  have hr := i3V_tendsto_ratio (α := B + c) (β := A * (B + c) + B * c) (γ := 1) (δ := A + c)
    one_pos
  have h1 : Tendsto (fun y => log ((y + A) * (B + c) + B * c) - log (y + A + c)) atTop
      (𝓝 (log (B + c))) := by
    have hl := ((continuousAt_log (by positivity : (B + c) / 1 ≠ 0)).tendsto).comp hr
    rw [div_one] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    rw [← log_div (by positivity) (by positivity)]
    congr 1
    rw [show (B + c) * y + (A * (B + c) + B * c) = (y + A) * (B + c) + B * c by ring,
      show 1 * y + (A + c) = y + A + c by ring]
  -- `log² Q - (log (B + c) + log (y + A + c))² → 0`
  have h2 : Tendsto (fun y => log ((y + A) * (B + c) + B * c) ^ 2 -
      (log (B + c) + log (y + A + c)) ^ 2) atTop (𝓝 0) := by
    have hq1 := i3V_tendsto_log_div (α := B + c) (β := A * (B + c) + B * c) (γ := B + c)
      (δ := A * (B + c) + B * c) hBc hBc
    have hq2 := i3V_tendsto_log_div (α := 1) (β := A + c) (γ := B + c)
      (δ := A * (B + c) + B * c) one_pos hBc
    have hq3 : Tendsto (fun y : ℝ => log (B + c) / ((B + c) * y + (A * (B + c) + B * c)))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
        (tendsto_id.const_mul_atTop hBc))
    have hS := ((hq1.add (hq3.add hq2)).abs).const_mul (c ^ 2)
    simp only [add_zero, abs_zero, mul_zero] at hS
    refine squeeze_zero_norm' ?_ hS
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hQ : 0 < (y + A) * (B + c) + B * c := by positivity
    have ha : 0 < y + A + c := by linarith
    set Q := (y + A) * (B + c) + B * c with hQdef
    set X := (B + c) * (y + A + c) with hXdef
    have hQX : X = Q + c ^ 2 := by rw [hXdef, hQdef]; ring
    have hlX : log (B + c) + log (y + A + c) = log X := by
      rw [hXdef, log_mul hBc.ne' ha.ne']
    rw [hlX]
    have hD0 : log Q - log X ≤ 0 := by
      have := log_le_log hQ (by rw [hQX]; nlinarith : Q ≤ X)
      linarith
    have hD1 : log X - log Q ≤ c ^ 2 / Q := by
      rw [← log_div (by positivity) hQ.ne']
      have := log_le_sub_one_of_pos (div_pos (by positivity : 0 < X) hQ)
      rw [hQX] at this ⊢
      have e : (Q + c ^ 2) / Q - 1 = c ^ 2 / Q := by field_simp; ring
      linarith
    have e1 : log Q ^ 2 - log X ^ 2 = (log Q - log X) * (log Q + log X) := by ring
    rw [e1, Real.norm_eq_abs, abs_mul]
    have eQ : (B + c) * y + (A * (B + c) + B * c) = Q := by rw [hQdef]; ring
    have eQ' : 1 * y + (A + c) = y + A + c := by ring
    rw [eQ, eQ']
    have hsum : log Q / Q + (log (B + c) / Q + log (y + A + c) / Q) = (log Q + log X) / Q := by
      rw [hXdef, log_mul hBc.ne' ha.ne']
      ring
    rw [hsum, abs_div, abs_of_pos hQ]
    have habs : |log Q - log X| ≤ c ^ 2 / Q := by
      rw [abs_of_nonpos hD0]
      linarith
    calc |log Q - log X| * |log Q + log X| ≤ c ^ 2 / Q * |log Q + log X| :=
          mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = c ^ 2 * (|log Q + log X| / Q) := by ring
  have h3 : Tendsto (fun y => Li₂ (c ^ 2 / ((B + c) * (y + A + c)))) atTop (𝓝 0) := by
    have hz : Tendsto (fun y => c ^ 2 / ((B + c) * (y + A + c))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hX
    have := tendsto_Li₂_comp (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hz ?_
    · simpa using this
    filter_upwards [eventually_gt_atTop 0] with y hy
    have ha : 0 < y + A + c := by linarith
    have : c ^ 2 / ((B + c) * (y + A + c)) < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
    exact ⟨by linarith [show 0 ≤ c ^ 2 / ((B + c) * (y + A + c)) by positivity], this.le⟩
  have h := ((h1.const_mul (1 - log s)).add (h2.div_const 2)).sub h3
  simp only [zero_div, add_zero, sub_zero] at h
  exact h

/-- The `y₇`-integral of the `y₈`-value. -/
theorem i2P1U_lint_y7 {k A B c s : ℝ} (hk : 0 ≤ k) (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    (hs : 0 < s) (hsQ : s ≤ A * B + (A + B) * c) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (k * (1 + log (((y + A) * (B + c) + B * c) / s)) /
        ((y + A + c) * ((y + A) * (B + c) + B * c))) =
      ENNReal.ofReal (k * i2P1UV7 A B c s) := by
  rw [i3V_lintegral_Ioi_eq (g := fun y => k / c ^ 2 * i2P1UG7 A B c s y)
    (l := k / c ^ 2 * ((1 - log s) * log (B + c)))]
  · congr 1
    simp only [i2P1UG7, i2P1UV7]
    rw [show ((0 : ℝ) + A) * (B + c) + B * c = A * B + (A + B) * c by ring,
      show (0 : ℝ) + A + c = A + c by ring, show (B + c) * (A + c) = (A + c) * (B + c) by ring]
    field_simp
    ring
  · intro y hy
    refine ((hasDerivAt_i2P1UG7 hA hB hc hs hy).const_mul (k / c ^ 2)).congr_deriv ?_
    field_simp
  · intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hQ : s ≤ (y + A) * (B + c) + B * c := by nlinarith
    have : 0 ≤ log (((y + A) * (B + c) + B * c) / s) := log_nonneg ((one_le_div hs).2 hQ)
    have : 0 < (y + A) * (B + c) + B * c := by linarith
    positivity
  · exact (tendsto_i2P1UG7 hA hB hc).const_mul _

/-- `V₇ ≥ 0`: it is the integral of a nonnegative function over `(0, ∞)`. -/
theorem i2P1UV7_nonneg {A B c s : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (hs : 0 < s)
    (hsQ : s ≤ A * B + (A + B) * c) : 0 ≤ i2P1UV7 A B c s := by
  have hd : ∀ y ∈ Ici (0 : ℝ), HasDerivAt (fun y => 1 / c ^ 2 * i2P1UG7 A B c s y)
      ((1 + log (((y + A) * (B + c) + B * c) / s)) /
        ((y + A + c) * ((y + A) * (B + c) + B * c))) y := fun y hy =>
    ((hasDerivAt_i2P1UG7 hA hB hc hs hy).const_mul (1 / c ^ 2)).congr_deriv (by field_simp)
  have hpos : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ (1 + log (((y + A) * (B + c) + B * c) / s)) /
      ((y + A + c) * ((y + A) * (B + c) + B * c)) := fun y hy => by
    have hy0 : (0 : ℝ) < y := hy
    have hQ : s ≤ (y + A) * (B + c) + B * c := by nlinarith
    have : 0 ≤ log (((y + A) * (B + c) + B * c) / s) := log_nonneg ((one_le_div hs).2 hQ)
    have : 0 < (y + A) * (B + c) + B * c := by linarith
    positivity
  have hl := (tendsto_i2P1UG7 (s := s) hA hB hc).const_mul (1 / c ^ 2)
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hl
  have h2 := setIntegral_nonneg (μ := volume) measurableSet_Ioi hpos
  rw [h] at h2
  have e : 1 / c ^ 2 * ((1 - log s) * log (B + c)) - 1 / c ^ 2 * i2P1UG7 A B c s 0 =
      i2P1UV7 A B c s := by
    simp only [i2P1UG7, i2P1UV7]
    rw [show ((0 : ℝ) + A) * (B + c) + B * c = A * B + (A + B) * c by ring,
      show (0 : ℝ) + A + c = A + c by ring, show (B + c) * (A + c) = (A + c) * (B + c) by ring]
    field_simp
    ring
  linarith

/-- **The `y₄`-primitive** `Θ(A, B, C)`, symmetric in `A, B, C`: with `σ = A B + (A + B) C`,
`Θ = 3 Ψ + Σ_P (((log (P + Q) + log (P + R))² - log² σ) / 2 + Li₂ (P² / ((P + Q)(P + R)))) / P`
over the cyclic permutations `(P, Q, R)` of `(A, B, C)`. -/
noncomputable def i2P1UTheta (A B C : ℝ) : ℝ :=
  3 * i2P0Psi A B C +
    (((log (A + B) + log (A + C)) ^ 2 - log (A * B + (A + B) * C) ^ 2) / 2 +
      Li₂ (A ^ 2 / ((A + B) * (A + C)))) / A +
    (((log (A + B) + log (B + C)) ^ 2 - log (A * B + (A + B) * C) ^ 2) / 2 +
      Li₂ (B ^ 2 / ((A + B) * (B + C)))) / B +
    (((log (A + C) + log (B + C)) ^ 2 - log (A * B + (A + B) * C) ^ 2) / 2 +
      Li₂ (C ^ 2 / ((A + C) * (B + C)))) / C

theorem hasDerivAt_i2P1UTheta {A B c s : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) :
    HasDerivAt (fun c => i2P1UTheta A B c - log s * i2P0Psi A B c) (-i2P1UV7 A B c s) c := by
  have hAc : 0 < A + c := by linarith
  have hBc : 0 < B + c := by linarith
  have hAB : 0 < A + B := by linarith
  have hσ : 0 < A * B + (A + B) * c := by positivity
  have dAc : HasDerivAt (fun c => log (A + c)) (1 / (A + c)) c := by
    simpa [one_div] using ((hasDerivAt_id c).const_add A).log hAc.ne'
  have dBc : HasDerivAt (fun c => log (B + c)) (1 / (B + c)) c := by
    simpa [one_div] using ((hasDerivAt_id c).const_add B).log hBc.ne'
  have dσ : HasDerivAt (fun c => log (A * B + (A + B) * c)) ((A + B) / (A * B + (A + B) * c)) c :=
    by simpa using (((hasDerivAt_id c).const_mul (A + B)).const_add (A * B)).log hσ.ne'
  have dP := hasDerivAt_i2P0Psi hA hB hc
  have zA : A ^ 2 / ((A + B) * (A + c)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one (by positivity)).2 (by nlinarith)⟩
  have zB : B ^ 2 / ((A + B) * (B + c)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one (by positivity)).2 (by nlinarith)⟩
  have zC : c ^ 2 / ((A + c) * (B + c)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one (by positivity)).2 (by nlinarith)⟩
  have dzA : HasDerivAt (fun c => A ^ 2 / ((A + B) * (A + c)))
      (-(A ^ 2 * (A + B)) / ((A + B) * (A + c)) ^ 2) c := by
    have := (hasDerivAt_const c (A ^ 2)).div (((hasDerivAt_id' c).const_add A).const_mul (A + B))
      (mul_pos hAB hAc).ne'
    refine this.congr_deriv ?_
    ring
  have dzB : HasDerivAt (fun c => B ^ 2 / ((A + B) * (B + c)))
      (-(B ^ 2 * (A + B)) / ((A + B) * (B + c)) ^ 2) c := by
    have := (hasDerivAt_const c (B ^ 2)).div (((hasDerivAt_id' c).const_add B).const_mul (A + B))
      (mul_pos hAB hBc).ne'
    refine this.congr_deriv ?_
    ring
  have dzC : HasDerivAt (fun c => c ^ 2 / ((A + c) * (B + c)))
      ((2 * c * ((A + c) * (B + c)) - c ^ 2 * ((B + c) + (A + c))) / ((A + c) * (B + c)) ^ 2) c :=
    by
    have hd : HasDerivAt (fun c => (A + c) * (B + c)) ((B + c) + (A + c)) c :=
      (((hasDerivAt_id' c).const_add A).mul ((hasDerivAt_id' c).const_add B)).congr_deriv
        (by ring)
    have := (hasDerivAt_pow 2 c).div hd (mul_pos hAc hBc).ne'
    refine this.congr_deriv ?_
    norm_num
  have lA := (hasDerivAt_Li₂' zA).comp c dzA
  have lB := (hasDerivAt_Li₂' zB).comp c dzB
  have lC := (hasDerivAt_Li₂' zC).comp c dzC
  have tA := ((((dAc.const_add (log (A + B))).pow 2).sub (dσ.pow 2)).div_const 2 |>.add lA)
    |>.div_const A
  have tB := ((((dBc.const_add (log (A + B))).pow 2).sub (dσ.pow 2)).div_const 2 |>.add lB)
    |>.div_const B
  have tC := ((((dAc.add dBc).pow 2).sub (dσ.pow 2)).div_const 2 |>.add lC).div
    (hasDerivAt_id' c) hc.ne'
  have h := ((((dP.const_mul 3).add tA).add tB).add tC).sub (dP.const_mul (log s))
  unfold i2P1UTheta
  refine h.congr_deriv ?_
  have eA : 1 - A ^ 2 / ((A + B) * (A + c)) = (A * B + (A + B) * c) / ((A + B) * (A + c)) := by
    field_simp
    ring
  have eB : 1 - B ^ 2 / ((A + B) * (B + c)) = (A * B + (A + B) * c) / ((A + B) * (B + c)) := by
    field_simp
    ring
  have eC : 1 - c ^ 2 / ((A + c) * (B + c)) = (A * B + (A + B) * c) / ((A + c) * (B + c)) := by
    field_simp
    ring
  rw [eA, eB, eC, log_div hσ.ne' (by positivity), log_div hσ.ne' (by positivity),
    log_div hσ.ne' (by positivity), log_mul hAB.ne' hAc.ne', log_mul hAB.ne' hBc.ne',
    log_mul hAc.ne' hBc.ne']
  simp only [i2P1UV7, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Function.comp]
  field_simp
  ring

/-- `log² X - log² Q → 0` when `X = Q + κ` and `log (Q X) / Q → 0`. -/
theorem i2P1U_tendsto_log_sq_sub {Q X : ℝ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hQ : ∀ᶠ y in atTop, 0 < Q y) (hX : ∀ y, X y = Q y + κ)
    (hS : Tendsto (fun y => (log (Q y) + log (X y)) / Q y) atTop (𝓝 0)) :
    Tendsto (fun y => log (X y) ^ 2 - log (Q y) ^ 2) atTop (𝓝 0) := by
  have h := (hS.abs).const_mul κ
  simp only [abs_zero, mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hQ] with y hy
  have hXp : 0 < X y := by rw [hX]; linarith
  have hD0 : 0 ≤ log (X y) - log (Q y) := by
    have := log_le_log hy (by rw [hX]; linarith : Q y ≤ X y)
    linarith
  have hD1 : log (X y) - log (Q y) ≤ κ / Q y := by
    rw [← log_div hXp.ne' hy.ne']
    have := log_le_sub_one_of_pos (div_pos hXp hy)
    have e : X y / Q y - 1 = κ / Q y := by rw [hX]; field_simp; ring
    linarith
  rw [show log (X y) ^ 2 - log (Q y) ^ 2 = (log (X y) - log (Q y)) * (log (Q y) + log (X y)) by
    ring, Real.norm_eq_abs, abs_mul, abs_of_nonneg hD0, abs_div, abs_of_pos hy]
  calc (log (X y) - log (Q y)) * |log (Q y) + log (X y)| ≤ κ / Q y * |log (Q y) + log (X y)| :=
        mul_le_mul_of_nonneg_right hD1 (abs_nonneg _)
    _ = κ * (|log (Q y) + log (X y)| / Q y) := by ring

/-- `log (α c + β) / (A B + (A + B) c) → 0`. -/
theorem i2P1U_tendsto_log_div_sigma {A B α β : ℝ} (hAB : 0 < A + B) (hα : 0 < α) :
    Tendsto (fun c => log (α * c + β) / (A * B + (A + B) * c)) atTop (𝓝 0) := by
  have h := i3V_tendsto_log_div (α := α) (β := β) (γ := A + B) (δ := A * B) hα hAB
  refine h.congr fun c => ?_
  rw [show (A + B) * c + A * B = A * B + (A + B) * c by ring]

theorem tendsto_i2P1UTheta {A B s : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun c => i2P1UTheta A B c - log s * i2P0Psi A B c) atTop (𝓝 0) := by
  have hAB : 0 < A + B := by linarith
  have hP := tendsto_i2P0Psi hA hB
  have hσt : Tendsto (fun c => A * B + (A + B) * c) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hAB)
  have hev : ∀ᶠ c in atTop, 0 < A * B + (A + B) * c := hσt.eventually_gt_atTop 0
  -- `log (P + c) / σ`, `log σ / σ`, `const / σ`
  have lσ : Tendsto (fun c => log (A * B + (A + B) * c) / (A * B + (A + B) * c)) atTop (𝓝 0) := by
    have := i2P1U_tendsto_log_div_sigma (α := A + B) (β := A * B) hAB hAB
    refine this.congr fun c => ?_
    rw [show (A + B) * c + A * B = A * B + (A + B) * c by ring]
  have lA : Tendsto (fun c => log (A + c) / (A * B + (A + B) * c)) atTop (𝓝 0) := by
    have := i2P1U_tendsto_log_div_sigma (α := 1) (β := A) hAB one_pos
    refine this.congr fun c => ?_
    rw [show 1 * c + A = A + c by ring]
  have lB : Tendsto (fun c => log (B + c) / (A * B + (A + B) * c)) atTop (𝓝 0) := by
    have := i2P1U_tendsto_log_div_sigma (α := 1) (β := B) hAB one_pos
    refine this.congr fun c => ?_
    rw [show 1 * c + B = B + c by ring]
  have lK : Tendsto (fun c => log (A + B) / (A * B + (A + B) * c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hσt
  -- the `A` and `B` terms
  have sqA := i2P1U_tendsto_log_sq_sub (Q := fun c => A * B + (A + B) * c)
    (X := fun c => (A + B) * (A + c)) (κ := A ^ 2) (sq_nonneg A) hev (fun c => by ring) (by
      have := lσ.add (lK.add lA)
      rw [add_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with c hc
      rw [log_mul hAB.ne' (by linarith)]
      ring)
  have sqB := i2P1U_tendsto_log_sq_sub (Q := fun c => A * B + (A + B) * c)
    (X := fun c => (A + B) * (B + c)) (κ := B ^ 2) (sq_nonneg B) hev (fun c => by ring) (by
      have := lσ.add (lK.add lB)
      rw [add_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with c hc
      rw [log_mul hAB.ne' (by linarith)]
      ring)
  have zA : Tendsto (fun c => Li₂ (A ^ 2 / ((A + B) * (A + c)))) atTop (𝓝 0) := by
    have hz : Tendsto (fun c => A ^ 2 / ((A + B) * (A + c))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_atTop_add_const_left _ A tendsto_id).const_mul_atTop
        hAB)
    have := tendsto_Li₂_comp (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hz ?_
    · simpa using this
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact ⟨by linarith [show 0 ≤ A ^ 2 / ((A + B) * (A + c)) by positivity],
      ((div_lt_one (by positivity)).2 (by nlinarith)).le⟩
  have zB : Tendsto (fun c => Li₂ (B ^ 2 / ((A + B) * (B + c)))) atTop (𝓝 0) := by
    have hz : Tendsto (fun c => B ^ 2 / ((A + B) * (B + c))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_atTop_add_const_left _ B tendsto_id).const_mul_atTop
        hAB)
    have := tendsto_Li₂_comp (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hz ?_
    · simpa using this
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact ⟨by linarith [show 0 ≤ B ^ 2 / ((A + B) * (B + c)) by positivity],
      ((div_lt_one (by positivity)).2 (by nlinarith)).le⟩
  have tA : Tendsto (fun c => (((log (A + B) + log (A + c)) ^ 2 -
      log (A * B + (A + B) * c) ^ 2) / 2 + Li₂ (A ^ 2 / ((A + B) * (A + c)))) / A) atTop
      (𝓝 0) := by
    have := ((sqA.div_const 2).add zA).div_const A
    rw [zero_div, add_zero, zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    rw [log_mul hAB.ne' (by linarith)]
  have tB : Tendsto (fun c => (((log (A + B) + log (B + c)) ^ 2 -
      log (A * B + (A + B) * c) ^ 2) / 2 + Li₂ (B ^ 2 / ((A + B) * (B + c)))) / B) atTop
      (𝓝 0) := by
    have := ((sqB.div_const 2).add zB).div_const B
    rw [zero_div, add_zero, zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    rw [log_mul hAB.ne' (by linarith)]
  -- the `C` term: every piece is `o(c)`
  have p2 : ∀ {α : ℝ}, Tendsto (fun c => log (α + c) ^ 2 / c) atTop (𝓝 0) := fun {α} => by
    have := (tendsto_pow_log_div_mul_add_atTop 1 (-α) 2 one_ne_zero).comp
      (tendsto_atTop_add_const_left _ α tendsto_id)
    refine this.congr fun c => ?_
    simp only [Function.comp, id]
    congr 1
    ring
  have pσ : Tendsto (fun c => log (A * B + (A + B) * c) ^ 2 / c) atTop (𝓝 0) := by
    have := (tendsto_pow_log_div_mul_add_atTop (1 / (A + B)) (-(A * B / (A + B))) 2
      (by positivity)).comp hσt
    refine this.congr fun c => ?_
    simp only [Function.comp]
    congr 1
    field_simp
    ring
  have pAB : Tendsto (fun c => (log (A + c) + log (B + c)) ^ 2 / c) atTop (𝓝 0) := by
    have h := ((p2 (α := A)).add (p2 (α := B))).const_mul 2
    rw [add_zero, mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [eventually_gt_atTop 0] with c hc
      positivity
    · filter_upwards [eventually_gt_atTop 0] with c hc
      rw [← add_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (log (A + c) - log (B + c))])
        hc.le
  have pL : Tendsto (fun c => Li₂ (c ^ 2 / ((A + c) * (B + c))) / c) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (π ^ 2 / 6)
    rw [mul_zero] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop 0] with c hc
    have hm : c ^ 2 / ((A + c) * (B + c)) ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [show 0 ≤ c ^ 2 / ((A + c) * (B + c)) by positivity],
        ((div_lt_one (by positivity)).2 (by nlinarith)).le⟩
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_Li₂_le_of_mem hm) (by positivity)
  have tC : Tendsto (fun c => (((log (A + c) + log (B + c)) ^ 2 -
      log (A * B + (A + B) * c) ^ 2) / 2 + Li₂ (c ^ 2 / ((A + c) * (B + c)))) / c) atTop
      (𝓝 0) := by
    have := ((pAB.sub pσ).div_const 2).add pL
    rw [sub_zero, zero_div, add_zero] at this
    refine this.congr fun c => ?_
    ring
  have h := (((((hP.const_mul 3).add tA).add tB).add tC).sub (hP.const_mul (log s)))
  simp only [mul_zero, add_zero, sub_zero] at h
  exact h

/-- **The `y₄`-integral**: `∫₀^∞ k V₇(A, B, y + C, s) dy = k (Θ(A, B, C) - log s Ψ(A, B, C))`. -/
theorem i2P1U_lint_y4 {k A B C s : ℝ} (hk : 0 ≤ k) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hs : 0 < s) (hsC : s ≤ A * B + (A + B) * C) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (k * i2P1UV7 A B (y + C) s) =
      ENNReal.ofReal (k * (i2P1UTheta A B C - log s * i2P0Psi A B C)) := by
  rw [i3V_lintegral_Ioi_eq
    (g := fun y => -(k * (i2P1UTheta A B (y + C) - log s * i2P0Psi A B (y + C))))
    (l := -(k * 0))]
  · congr 1
    simp
  · intro y hy
    have hy0 : (0 : ℝ) ≤ y := hy
    have := (((hasDerivAt_i2P1UTheta (s := s) hA hB (by linarith : 0 < y + C)).comp_add_const y
      C).const_mul k).neg
    refine this.congr_deriv ?_
    ring
  · intro y hy
    have hy0 : (0 : ℝ) < y := hy
    exact mul_nonneg hk (i2P1UV7_nonneg hA hB (by linarith) hs (by nlinarith))
  · exact ((tendsto_i2P1UTheta hA hB).comp
      (tendsto_atTop_add_const_right _ C tendsto_id)).const_mul k |>.neg

/-- **The three line-parameter integrals** of `(1 - w) log (𝒰 / σ) / 𝒰²`, `σ = A B + (A + B) C`. -/
theorem i2P1U_inner {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ y₄ in Ioi (0 : ℝ), ∫⁻ y₇ in Ioi (0 : ℝ), ∫⁻ y₈ in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - w) * log (i2U x w y₄ y₇ y₈ /
        (w * (1 - w) * x * (w * (1 - w) * (1 - x)) + (w * (1 - w) * x + w * (1 - w) * (1 - x)) *
          ((1 - w) ^ 2 * x * (1 - x)))) / i2U x w y₄ y₇ y₈ ^ 2) =
      ENNReal.ofReal ((1 - w) * (i2P1UTheta (w * (1 - w) * x) (w * (1 - w) * (1 - x))
        ((1 - w) ^ 2 * x * (1 - x)) - log (w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
          (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x))) *
        i2P0Psi (w * (1 - w) * x) (w * (1 - w) * (1 - x)) ((1 - w) ^ 2 * x * (1 - x)))) := by
  obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hx hw
  set A := w * (1 - w) * x
  set B := w * (1 - w) * (1 - x)
  set C := (1 - w) ^ 2 * x * (1 - x)
  have hk : 0 ≤ 1 - w := by linarith [hw.2]
  have hs : 0 < A * B + (A + B) * C := by positivity
  rw [← i2P1U_lint_y4 hk hA hB hC hs le_rfl]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₄ (h4 : 0 < y₄) => ?_
  rw [← i2P1U_lint_y7 hk hA hB (by linarith) hs (by nlinarith)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₇ (h7 : 0 < y₇) => ?_
  have hsq : A * B + (A + B) * C ≤ B * (y₇ + A + (y₄ + C)) + (y₇ + A) * (y₄ + C) := by nlinarith
  rw [show (y₇ + A) * (B + (y₄ + C)) + B * (y₄ + C) =
    B * (y₇ + A + (y₄ + C)) + (y₇ + A) * (y₄ + C) by ring, show y₇ + A + (y₄ + C) =
    y₇ + A + (y₄ + C) from rfl, ← i2P1U_lint_y8 hk (by linarith) hs hsq]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₈ _ => ?_
  have e : i2U x w y₄ y₇ y₈ = (y₈ + B) * (y₇ + A + (y₄ + C)) + (y₇ + A) * (y₄ + C) := by
    simp only [i2U, i2LineA, i2LineB, i2LineC, A, B, C]
    ring
  rw [e]

end QED.ThreeLoopD
