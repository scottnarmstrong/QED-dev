/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2Analytic
public import QED.ThreeLoopD.SetDMastersI3FValPhoton

/-!
# Set (d), master `I₂`: the three line parameters of `P(0)`

At `ε = 0` the integrand of `QED.ThreeLoopD.i2PInt` is `(1 - w) / 𝒰²`, `𝒰 = a b + b c + c a`
with `a = y₇ + A`, `b = y₈ + B`, `c = y₄ + C`, `A = w (1 - w) x`, `B = w (1 - w)(1 - x)`,
`C = (1 - w)² x (1 - x)`. The integrand is nonnegative, so we work with lower integrals and
Tonelli's theorem, and integrate the line parameters one at a time by the fundamental theorem
of calculus on `(0, ∞)` (`QED.ThreeLoopD.i3V_lintegral_Ioi_eq`):

* `y₈`: `𝒰 = b (a + c) + a c`, so `∫₀^∞ dy₈ / 𝒰² = 1 / ((a + c)(B (a + c) + a c))`;
* `y₇`: partial fractions in `a` give
  `(log (A + c) + log (B + c) - log (A B + (A + B) c)) / c²`;
* `y₄`: the primitive in `c` is `-Ψ(A, B, c)` (`QED.ThreeLoopD.i2P0Psi`), with `Ψ → 0` at
  infinity.

Hence `P(0) = ∫₀¹ ∫₀¹ (1 - w) Ψ(A, B, C) dw dx` (`QED.ThreeLoopD.i2PInt_zero_eq_lintegral`).

## Main results

* `QED.ThreeLoopD.i2P0_inner`, `QED.ThreeLoopD.i2P0Psi_nonneg`.
* `QED.ThreeLoopD.i2PInt_zero_eq_lintegral`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The `y₈`-integral: `∫₀^∞ k / ((y + B) p + q)² dy = k / (p (B p + q))`. -/
theorem i2P0_lint_y8 {k p q B : ℝ} (hp : 0 < p) (hq : 0 < q) (hB : 0 ≤ B) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (k / ((y + B) * p + q) ^ 2) =
      ENNReal.ofReal (k / (p * (B * p + q))) := by
  by_cases hk : 0 ≤ k
  swap
  · have hk' : k / (p * (B * p + q)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [ENNReal.ofReal_of_nonpos hk']
    refine (setLIntegral_eq_zero_iff measurableSet_Ioi (by fun_prop)).2 ?_
    filter_upwards with y _
    exact ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have hpos : ∀ y ∈ Ici (0 : ℝ), 0 < (y + B) * p + q := fun y hy => by
    have : (0 : ℝ) ≤ y := hy
    have : 0 ≤ y + B := by linarith
    positivity
  rw [i3V_lintegral_Ioi_eq (g := fun y => -(k / p) / ((y + B) * p + q)) (l := 0)]
  · congr 1
    have := hpos 0 (mem_Ici.2 le_rfl)
    field_simp
    ring_nf
  · intro y hy
    have hf : HasDerivAt (fun y => (y + B) * p + q) p y := by
      simpa using (((hasDerivAt_id y).add_const B).mul_const p).add_const q
    refine ((hasDerivAt_const y (-(k / p))).div hf (hpos y hy).ne').congr_deriv ?_
    have := (hpos y hy).ne'
    field_simp
    ring
  · intro y hy
    exact div_nonneg hk (sq_nonneg _)
  · refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ q
      ((tendsto_atTop_add_const_right _ B tendsto_id).atTop_mul_const hp)

/-- The `y₇`-integral:
`∫₀^∞ k / ((y + A + c)(B (y + A + c) + (y + A) c)) dy
  = k (log (A + c) + log (B + c) - log (A B + (A + B) c)) / c²`. -/
theorem i2P0_lint_y7 {k A B c : ℝ} (hk : 0 ≤ k) (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) :
    ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (k / ((y + A + c) * (B * (y + A + c) + (y + A) * c))) =
      ENNReal.ofReal (k * (log (A + c) + log (B + c) - log (A * B + (A + B) * c)) / c ^ 2) := by
  have hBc : 0 < B + c := by linarith
  rw [i3V_lintegral_Ioi_eq
    (g := fun y => k / c ^ 2 * (log ((B + c) * y + ((B + c) * A + B * c)) - log (1 * y + (A + c))))
    (l := k / c ^ 2 * log ((B + c) / 1))]
  · congr 1
    rw [show (B + c) * 0 + ((B + c) * A + B * c) = A * B + (A + B) * c by ring,
      show (1 : ℝ) * 0 + (A + c) = A + c by ring, div_one]
    ring
  · intro y hy
    have hy0 : (0 : ℝ) ≤ y := hy
    have h1 : 0 < (B + c) * y + ((B + c) * A + B * c) := by positivity
    have h2 : 0 < 1 * y + (A + c) := by positivity
    have d1 : HasDerivAt (fun y => (B + c) * y + ((B + c) * A + B * c)) (B + c) y := by
      simpa using ((hasDerivAt_id y).const_mul (B + c)).add_const ((B + c) * A + B * c)
    have d2 : HasDerivAt (fun y => 1 * y + (A + c)) 1 y := by
      simpa using ((hasDerivAt_id y).const_mul 1).add_const (A + c)
    refine (((d1.log h1.ne').sub (d2.log h2.ne')).const_mul (k / c ^ 2)).congr_deriv ?_
    have h3 : 0 < y + A + c := by positivity
    have h4 : 0 < B * (y + A + c) + (y + A) * c := by positivity
    field_simp
    ring
  · intro y hy
    have hy0 : (0 : ℝ) < y := hy
    positivity
  · refine Tendsto.const_mul _ ?_
    have hr := i3V_tendsto_ratio (α := B + c) (β := (B + c) * A + B * c) (δ := A + c) one_pos
    have hl := ((continuousAt_log (by positivity : (B + c) / 1 ≠ 0)).tendsto).comp hr
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    rw [log_div (by positivity) (by positivity)]

/-- `Ψ(A, B, C) = ∫_C^∞ (log (A + c) + log (B + c) - log (A B + (A + B) c)) / c² dc`. -/
noncomputable def i2P0Psi (A B C : ℝ) : ℝ :=
  (1 / A + 1 / C) * log (A + C) + (1 / B + 1 / C) * log (B + C) -
    ((A + B) / (A * B) + 1 / C) * log (A * B + (A + B) * C) + (A + B) * log (A + B) / (A * B)

theorem hasDerivAt_i2P0Psi {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) :
    HasDerivAt (fun c => i2P0Psi A B c)
      (-(log (A + c) + log (B + c) - log (A * B + (A + B) * c)) / c ^ 2) c := by
  have h1 : 0 < A + c := by linarith
  have h2 : 0 < B + c := by linarith
  have h3 : 0 < A * B + (A + B) * c := by positivity
  have dl1 : HasDerivAt (fun c => log (A + c)) (1 / (A + c)) c := by
    simpa [one_div] using ((hasDerivAt_id c).const_add A).log h1.ne'
  have dl2 : HasDerivAt (fun c => log (B + c)) (1 / (B + c)) c := by
    simpa [one_div] using ((hasDerivAt_id c).const_add B).log h2.ne'
  have dl3 : HasDerivAt (fun c => log (A * B + (A + B) * c)) ((A + B) / (A * B + (A + B) * c)) c :=
    by simpa using (((hasDerivAt_id c).const_mul (A + B)).const_add (A * B)).log h3.ne'
  have di : HasDerivAt (fun c : ℝ => 1 / c) (-1 / c ^ 2) c := by
    have := hasDerivAt_inv hc.ne'
    simp only [one_div]
    convert this using 1
    ring
  have d := ((((di.const_add (1 / A)).mul dl1).add ((di.const_add (1 / B)).mul dl2)).sub
    ((di.const_add ((A + B) / (A * B))).mul dl3)).add_const ((A + B) * log (A + B) / (A * B))
  refine d.congr_deriv ?_
  field_simp
  ring

/-- `Ψ(A, B, c) → 0` as `c → ∞`. -/
theorem tendsto_i2P0Psi {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun c => i2P0Psi A B c) atTop (𝓝 0) := by
  have hAB : 0 < A + B := by linarith
  have hr1 := i3V_tendsto_ratio (α := 1) (β := A) (γ := A + B) (δ := A * B) hAB
  have hr2 := i3V_tendsto_ratio (α := 1) (β := B) (γ := A + B) (δ := A * B) hAB
  have hl1 := ((continuousAt_log (by positivity : 1 / (A + B) ≠ 0)).tendsto).comp hr1
  have hl2 := ((continuousAt_log (by positivity : 1 / (A + B) ≠ 0)).tendsto).comp hr2
  have hq1 := i3V_tendsto_log_div (α := 1) (β := A) (γ := 1) (δ := 0) one_pos one_pos
  have hq2 := i3V_tendsto_log_div (α := 1) (β := B) (γ := 1) (δ := 0) one_pos one_pos
  have hq3 := i3V_tendsto_log_div (α := A + B) (β := A * B) (γ := 1) (δ := 0) hAB one_pos
  have h := (((hl1.const_mul (1 / A)).add (hl2.const_mul (1 / B))).add
    ((hq1.add hq2).sub hq3)).add_const ((A + B) * log (A + B) / (A * B))
  have e : 1 / A * log (1 / (A + B)) + 1 / B * log (1 / (A + B)) + (0 + 0 - 0) +
      (A + B) * log (A + B) / (A * B) = 0 := by
    rw [one_div (A + B), log_inv]
    field_simp
    ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  simp only [Function.comp, i2P0Psi]
  have h1 : 0 < A + c := by linarith
  have h2 : 0 < B + c := by linarith
  have h3 : 0 < A * B + (A + B) * c := by positivity
  rw [log_div (by positivity) (by positivity), log_div (by positivity) (by positivity)]
  rw [show 1 * c + A = A + c by ring, show 1 * c + B = B + c by ring,
    show (A + B) * c + A * B = A * B + (A + B) * c by ring, show 1 * c + 0 = c by ring]
  field_simp
  ring

theorem i2P0_y7val_nonneg {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) :
    0 ≤ (log (A + c) + log (B + c) - log (A * B + (A + B) * c)) / c ^ 2 := by
  have h3 : 0 < A * B + (A + B) * c := by positivity
  rw [← log_mul (by positivity) (by positivity)]
  refine div_nonneg (sub_nonneg.2 (log_le_log h3 (by nlinarith))) (sq_nonneg _)

/-- The `y₄`-integral: `∫₀^∞ k v(y + C) dy = k Ψ(A, B, C)`. -/
theorem i2P0_lint_y4 {k A B C : ℝ} (hk : 0 ≤ k) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (k * (log (A + (y + C)) + log (B + (y + C)) -
        log (A * B + (A + B) * (y + C))) / (y + C) ^ 2) =
      ENNReal.ofReal (k * i2P0Psi A B C) := by
  rw [i3V_lintegral_Ioi_eq (g := fun y => -(k * i2P0Psi A B (y + C))) (l := -(k * 0))]
  · congr 1
    simp
  · intro y hy
    have hy0 : (0 : ℝ) ≤ y := hy
    have := (((hasDerivAt_i2P0Psi hA hB (by linarith : 0 < y + C)).comp_add_const y C).const_mul
      k).neg
    refine this.congr_deriv ?_
    ring
  · intro y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [mul_div_assoc]
    exact mul_nonneg hk (i2P0_y7val_nonneg hA hB (by linarith))
  · exact ((tendsto_i2P0Psi hA hB).comp
      (tendsto_atTop_add_const_right _ C tendsto_id)).const_mul k |>.neg

/-- `Ψ ≥ 0`: it is the integral of a nonnegative function over `(C, ∞)`. -/
theorem i2P0Psi_nonneg {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    0 ≤ i2P0Psi A B C := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := C) (l := -0)
    (g := fun c => -i2P0Psi A B c)
    (g' := fun c => (log (A + c) + log (B + c) - log (A * B + (A + B) * c)) / c ^ 2)
    (fun c (hc : C ≤ c) => (hasDerivAt_i2P0Psi hA hB (by linarith)).neg.congr_deriv (by ring))
    (fun c (hc : C < c) => i2P0_y7val_nonneg hA hB (by linarith))
    (tendsto_i2P0Psi hA hB).neg
  have h2 := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (fun c (hc : C < c) => i2P0_y7val_nonneg hA hB (by linarith : 0 < c))
  rw [h] at h2
  linarith

/-- The integrand of `P(0)` after the three line parameters: `(1 - w) Ψ(A, B, C)`. -/
noncomputable def i2P0Q (x w : ℝ) : ℝ :=
  (1 - w) * i2P0Psi (w * (1 - w) * x) (w * (1 - w) * (1 - x)) ((1 - w) ^ 2 * x * (1 - x))

/-- **The three line-parameter integrals** of `(1 - w) / 𝒰²`. -/
theorem i2P0_inner {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ y₄ in Ioi (0 : ℝ), ∫⁻ y₇ in Ioi (0 : ℝ), ∫⁻ y₈ in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - w) / i2U x w y₄ y₇ y₈ ^ 2) = ENNReal.ofReal (i2P0Q x w) := by
  obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hx hw
  have hk : 0 ≤ 1 - w := by linarith [hw.2]
  rw [i2P0Q, ← i2P0_lint_y4 hk hA hB hC]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₄ (h4 : 0 < y₄) => ?_
  rw [← i2P0_lint_y7 hk hA hB (by linarith)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₇ (h7 : 0 < y₇) => ?_
  rw [← i2P0_lint_y8 (by positivity) (by positivity) hB.le]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₈ _ => ?_
  congr 2
  unfold i2U i2LineA i2LineB i2LineC
  ring

/-- **`P(0)` as a double integral** of `(1 - w) Ψ(A, B, C)`. -/
theorem i2PInt_zero_eq_lintegral :
    i2PInt 0 = (((∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (i2P0Q x w)).toReal : ℝ) : ℂ) := by
  set g : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun z =>
    (1 - z.2.1) / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 with hg
  have hgm : Measurable g := by rw [hg]; unfold i2U i2LineA i2LineB i2LineC; fun_prop
  have hI : ∀ z, i2Integrand 0 z = (g z : ℂ) := by
    intro z
    simp only [i2Integrand, hg, mul_zero, add_zero, Complex.cpow_zero, mul_one]
    rw [show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    ring
  rw [i2PInt_eq]
  simp_rw [hI]
  rw [integral_complex_ofReal]
  congr 1
  have hS : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  have hpos : 0 ≤ᵐ[volume.restrict i2Dom] g := by
    filter_upwards [ae_restrict_mem hS] with z hz
    have hw : 0 ≤ 1 - z.2.1 := by linarith [hz.2.1.2]
    simp only [Pi.zero_apply, hg]
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae hpos hgm.aestronglyMeasurable]
  congr 1
  rw [i2Dom, volume_restrict_prod5, lintegral_prod _ hgm.ennreal_ofReal.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have m1 : Measurable fun y : ℝ × ℝ × ℝ × ℝ => ENNReal.ofReal (g (x, y)) := by fun_prop
  rw [lintegral_prod _ m1.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
  have m2 : Measurable fun y : ℝ × ℝ × ℝ => ENNReal.ofReal (g (x, w, y)) := by fun_prop
  rw [lintegral_prod _ m2.aemeasurable, ← i2P0_inner hx hw]
  refine lintegral_congr fun y₄ => ?_
  have m3 : Measurable fun y : ℝ × ℝ => ENNReal.ofReal (g (x, w, y₄, y)) := by fun_prop
  rw [lintegral_prod _ m3.aemeasurable]

end QED.ThreeLoopD
