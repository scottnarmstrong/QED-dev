/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SpatialIntegralSix
import QED.Integration.TwoLoopMoments
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# The spatial shell integral, polynomially in the external momentum

Helper level for the set (a) headline (HA₆), obligation (N), step NL for `VA`, `VB`, `VC`.
For `ε > 0`, `|V| ≤ K`, `b ≥ 1` and `j + 4 ≤ n`,

`∫_{ℝ⁶} (b + ‖x‖²)^j ‖(‖x‖² + V - iε)^{-n}‖ dx ≤ π³ (b + 2K + 1)^{j+2} (π/(2ε^{n-1}) + 2^n/2)`.

The point is the power of `b + 2K + 1`: the mass shell `‖x‖² = -V` has radius up to `√K`, and a
shell of thickness `ε` there has volume of order `K² ε`, so the bound grows like `K^{j+2}`, not
like the `(K + 1)^n` of the uniform comparison `QED.Integration.TwoLoop.exists_delta`. The proof
is radial: on `r² ≤ 2K + 1` the integrand is at most a multiple of `r/((r² + V)² + ε²)`
(antiderivative `arctan((r² + V)/ε)/(2ε)`), beyond it a multiple of `r/(1 + r²)²`.

* `integral_shell_le`, `integral_tail_le`: the two radial majorants;
* `radial_le`: the pointwise radial comparison;
* `integral_euclidean_shell_le`: the bound in `ℝ⁶`;
* **`integral_quadForm_shell_le`**: the bound against a weight of polynomial growth in a shifted
  quadratic form `(v + σ)ᵀ A (v + σ)`, with the factor `(det A)^{-3/2}`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetANestV

open QED.Integration.Spatial (quadForm)

/-! ### The radial majorants -/

theorem hasDerivAt_shell {V ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (fun r : ℝ => Real.arctan ((r ^ 2 + V) / ε) / (2 * ε))
      (r / ((r ^ 2 + V) ^ 2 + ε ^ 2)) r := by
  have h1 : HasDerivAt (fun r : ℝ => (r ^ 2 + V) / ε) (2 * r / ε) r := by
    have := ((hasDerivAt_pow 2 r).add_const V).div_const ε
    simpa using this
  have h2 := (h1.arctan).div_const (2 * ε)
  convert h2 using 1
  have hD : 0 < (r ^ 2 + V) ^ 2 + ε ^ 2 := by positivity
  field_simp
  ring

/-- **The shell majorant**: `∫_{r > 0} r/((r² + V)² + ε²) ≤ π/(2ε)`. -/
theorem integral_shell_le {V ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r / ((r ^ 2 + V) ^ 2 + ε ^ 2)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), r / ((r ^ 2 + V) ^ 2 + ε ^ 2) ≤ π / (2 * ε) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => Real.arctan ((r ^ 2 + V) / ε) / (2 * ε))
      (r / ((r ^ 2 + V) ^ 2 + ε ^ 2)) r := fun r _ => hasDerivAt_shell hε r
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r / ((r ^ 2 + V) ^ 2 + ε ^ 2) := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hlim : Tendsto (fun r : ℝ => Real.arctan ((r ^ 2 + V) / ε) / (2 * ε)) atTop
      (𝓝 ((π / 2) / (2 * ε))) := by
    refine (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_ |>.div_const _
    refine Tendsto.atTop_div_const hε ?_
    exact tendsto_atTop_add_const_right _ V (tendsto_pow_atTop two_ne_zero)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim]
  have ha := Real.neg_pi_div_two_lt_arctan ((0 ^ 2 + V) / ε)
  have e : π / (2 * ε) = π / 2 / (2 * ε) + π / 2 / (2 * ε) := by ring
  rw [e, sub_eq_add_neg, ← neg_div]
  gcongr
  linarith

theorem hasDerivAt_tail (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(1 / (2 * (1 + r ^ 2)))) (r / (1 + r ^ 2) ^ 2) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * (1 + r ^ 2)) (2 * (2 * r)) r := by
    have := ((hasDerivAt_pow 2 r).const_add 1).const_mul 2
    simpa using this
  have hne : 2 * (1 + r ^ 2) ≠ 0 := by positivity
  have h2 := (h1.inv hne).neg
  convert h2 using 1
  · funext r; simp [one_div]
  · field_simp

/-- **The tail majorant**: `∫_{r > 0} r/(1 + r²)² = 1/2`. -/
theorem integral_tail_le :
    IntegrableOn (fun r : ℝ => r / (1 + r ^ 2) ^ 2) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), r / (1 + r ^ 2) ^ 2 ≤ 1 / 2 := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => -(1 / (2 * (1 + r ^ 2))))
      (r / (1 + r ^ 2) ^ 2) r := fun r _ => hasDerivAt_tail r
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r / (1 + r ^ 2) ^ 2 := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hlim : Tendsto (fun r : ℝ => -(1 / (2 * (1 + r ^ 2)))) atTop (𝓝 (-0)) := by
    refine Tendsto.neg ?_
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    refine Tendsto.const_mul_atTop (by norm_num) ?_
    exact tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim]
  norm_num

/-! ### The pointwise radial comparison -/

theorem norm_shell_sq (q V ε : ℝ) :
    ‖(q : ℂ) + ((V : ℂ) - (ε : ℂ) * I)‖ ^ 2 = (q + V) ^ 2 + ε ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- **The pointwise radial comparison.** For `r > 0`, `b ≥ 1`, `|V| ≤ K`, `ε > 0`, `j + 4 ≤ n`:
`r⁵ (b + r²)^j ‖(r² + V - iε)^{-n}‖` is at most
`(b + 2K + 1)^{j+2} ε^{2-n} · r/((r² + V)² + ε²) + 2^n b^j · r/(1 + r²)²`. -/
theorem radial_le {b K V ε : ℝ} (hb : 1 ≤ b) (hV : |V| ≤ K) (hε : 0 < ε) {j n : ℕ}
    (hjn : j + 4 ≤ n) {r : ℝ} (hr : 0 < r) :
    r ^ 5 * ((b + r ^ 2) ^ j * ‖((((r ^ 2 : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖) ≤
      (b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ * (r / ((r ^ 2 + V) ^ 2 + ε ^ 2)) +
        2 ^ n * b ^ j * (r / (1 + r ^ 2) ^ 2) := by
  set q := r ^ 2 with hq
  set N := ‖(q : ℂ) + ((V : ℂ) - (ε : ℂ) * I)‖ with hN
  have hN2 : N ^ 2 = (q + V) ^ 2 + ε ^ 2 := norm_shell_sq q V ε
  have hN0 : 0 ≤ N := norm_nonneg _
  have hq0 : 0 ≤ q := sq_nonneg r
  have hK0 : 0 ≤ K := (abs_nonneg V).trans hV
  have hVl : -K ≤ V := by linarith [neg_abs_le V]
  have hNε : ε ≤ N := by
    have : ε ^ 2 ≤ N ^ 2 := by rw [hN2]; nlinarith [sq_nonneg (q + V)]
    exact (pow_le_pow_iff_left₀ hε.le hN0 two_ne_zero).mp this
  have hNpos : 0 < N := hε.trans_le hNε
  rw [norm_inv, norm_pow, ← hN]
  have hr5 : r ^ 5 = r * q ^ 2 := by rw [hq]; ring
  have hR0 : 0 ≤ 2 * K + 1 := by linarith
  have h1 : 0 ≤ r / ((q + V) ^ 2 + ε ^ 2) := by positivity
  have h2 : 0 ≤ r / (1 + q) ^ 2 := by positivity
  rcases le_or_gt q (2 * K + 1) with hqR | hqR
  · -- the shell
    have hle : (b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ * (r / ((q + V) ^ 2 + ε ^ 2)) ≤
        (b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ * (r / ((q + V) ^ 2 + ε ^ 2)) +
          2 ^ n * b ^ j * (r / (1 + q) ^ 2) := le_add_of_nonneg_right (by positivity)
    refine le_trans ?_ hle
    obtain ⟨l, rfl⟩ : ∃ l, n = l + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add, hN2]
    have hbq : b + q ≤ b + 2 * K + 1 := by linarith
    have hqb : q ≤ b + 2 * K + 1 := by linarith
    have hεl : ε ^ l ≤ N ^ l := pow_le_pow_left₀ hε.le hNε l
    have hD : 0 < (q + V) ^ 2 + ε ^ 2 := by positivity
    have e : (b + 2 * K + 1) ^ (j + 2) * (ε ^ l)⁻¹ * (r / ((q + V) ^ 2 + ε ^ 2)) =
        r * ((b + 2 * K + 1) ^ 2 * (b + 2 * K + 1) ^ j) * (ε ^ l * ((q + V) ^ 2 + ε ^ 2))⁻¹ := by
      rw [pow_add]; field_simp
    rw [hr5, e]
    have hεpos : 0 < ε ^ l := pow_pos hε l
    calc r * q ^ 2 * ((b + q) ^ j * (N ^ l * ((q + V) ^ 2 + ε ^ 2))⁻¹)
        = r * (q ^ 2 * (b + q) ^ j) * (N ^ l * ((q + V) ^ 2 + ε ^ 2))⁻¹ := by ring
      _ ≤ r * ((b + 2 * K + 1) ^ 2 * (b + 2 * K + 1) ^ j) *
          (ε ^ l * ((q + V) ^ 2 + ε ^ 2))⁻¹ := by
        gcongr
  · -- the tail
    have hle : 2 ^ n * b ^ j * (r / (1 + q) ^ 2) ≤
        (b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ * (r / ((q + V) ^ 2 + ε ^ 2)) +
          2 ^ n * b ^ j * (r / (1 + q) ^ 2) := le_add_of_nonneg_left (by positivity)
    refine le_trans ?_ hle
    have hNq : (1 + q) / 2 ≤ N := by
      have h : (1 + q) / 2 ≤ q + V := by linarith
      have h' : ((1 + q) / 2) ^ 2 ≤ N ^ 2 := by
        rw [hN2]; nlinarith [sq_nonneg ε]
      exact (pow_le_pow_iff_left₀ (by positivity) hN0 two_ne_zero).mp h'
    have hbq : b + q ≤ b * (1 + q) := by nlinarith
    have hq1 : 1 ≤ 1 + q := by linarith
    have hq2 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
    have hbqj : (b + q) ^ j ≤ b ^ j * (1 + q) ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hbq j
    have hNinv : (N ^ n)⁻¹ ≤ 2 ^ n * ((1 + q) ^ n)⁻¹ := by
      have h := pow_le_pow_left₀ (by positivity) hNq n
      rw [div_pow] at h
      calc (N ^ n)⁻¹ ≤ ((1 + q) ^ n / 2 ^ n)⁻¹ := inv_anti₀ (by positivity) h
        _ = 2 ^ n * ((1 + q) ^ n)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have hpow : (1 + q) ^ (j + 4) ≤ (1 + q) ^ n := pow_le_pow_right₀ hq1 hjn
    have hlast : (1 + q) ^ (j + 2) * ((1 + q) ^ n)⁻¹ ≤ ((1 + q) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
        le_div_iff₀ (by positivity), ← pow_add]
      exact hpow.trans_eq' (by ring_nf)
    rw [hr5]
    calc r * q ^ 2 * ((b + q) ^ j * (N ^ n)⁻¹)
        = r * (q ^ 2 * (b + q) ^ j) * (N ^ n)⁻¹ := by ring
      _ ≤ r * ((1 + q) ^ 2 * (b ^ j * (1 + q) ^ j)) * (2 ^ n * ((1 + q) ^ n)⁻¹) := by
        gcongr
      _ = 2 ^ n * b ^ j * r * ((1 + q) ^ (j + 2) * ((1 + q) ^ n)⁻¹) := by ring
      _ ≤ 2 ^ n * b ^ j * r * ((1 + q) ^ 2)⁻¹ := by gcongr
      _ = 2 ^ n * b ^ j * (r / (1 + q) ^ 2) := by ring

/-! ### The bound in `ℝ⁶` -/

/-- The constant of the shell bound,
`π³ ((b + 2K + 1)^{j+2} ε^{2-n} π/(2ε) + 2^n b^j / 2)`. -/
noncomputable def shellConst (b K ε : ℝ) (j n : ℕ) : ℝ :=
  π ^ 3 * ((b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ * (π / (2 * ε)) + 2 ^ n * b ^ j * (1 / 2))

theorem volume_real_ball_six :
    (volume : Measure (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))).real (Metric.ball 0 1) = π ^ 3 / 6 := by
  rw [measureReal_def, EuclideanSpace.volume_ball]
  have hG : Real.Gamma ((Fintype.card (Fin 3 ⊕ Fin 3) : ℝ) / 2 + 1) = 6 := by
    rw [show ((Fintype.card (Fin 3 ⊕ Fin 3) : ℝ) / 2 + 1) = ((3 : ℕ) : ℝ) + 1 by simp; norm_num,
      Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hs : Real.sqrt π ^ Fintype.card (Fin 3 ⊕ Fin 3) = π ^ 3 := by
    rw [show Fintype.card (Fin 3 ⊕ Fin 3) = 2 * 3 by simp, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hG, hs, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity)]

theorem continuous_shellNorm {w : ℂ} (hw : w.im < 0) (b : ℝ) (j n : ℕ) :
    Continuous fun r : ℝ => (b + r ^ 2) ^ j * ‖((((r ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹‖ :=
  ((continuous_const.add (continuous_pow 2)).pow j).mul
    ((QED.Integration.TwoLoop.continuous_inv_add_pow hw n).comp (continuous_pow 2)).norm

/-- **The shell bound in `ℝ⁶`.** -/
theorem integral_euclidean_shell_le {b K V ε : ℝ} (hb : 1 ≤ b) (hV : |V| ≤ K) (hε : 0 < ε)
    {j n : ℕ} (hjn : j + 4 ≤ n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3) =>
        (b + ‖x‖ ^ 2) ^ j * ‖((((‖x‖ ^ 2 : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖) ∧
      ∫ x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3),
          (b + ‖x‖ ^ 2) ^ j * ‖((((‖x‖ ^ 2 : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖ ≤
        shellConst b K ε j n := by
  set w : ℂ := (V : ℂ) - (ε : ℂ) * I with hw
  have hwi : w.im < 0 := by simp [hw]; linarith
  set f : ℝ → ℝ := fun r => (b + r ^ 2) ^ j * ‖((((r ^ 2 : ℝ) : ℂ) + w) ^ n)⁻¹‖ with hf
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) = 6 := by simp
  set A₁ := (b + 2 * K + 1) ^ (j + 2) * (ε ^ (n - 2))⁻¹ with hA₁def
  set A₂ := (2 : ℝ) ^ n * b ^ j with hA₂def
  have hK0 : 0 ≤ K := (abs_nonneg V).trans hV
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  obtain ⟨i₁, b₁⟩ := integral_shell_le (V := V) hε
  obtain ⟨i₂, b₂⟩ := integral_tail_le
  have hg : IntegrableOn (fun r : ℝ => A₁ * (r / ((r ^ 2 + V) ^ 2 + ε ^ 2)) +
      A₂ * (r / (1 + r ^ 2) ^ 2)) (Ioi 0) := (i₁.const_mul A₁).add (i₂.const_mul A₂)
  have hpt : ∀ r ∈ Ioi (0 : ℝ), r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) - 1) •
      f r ≤ A₁ * (r / ((r ^ 2 + V) ^ 2 + ε ^ 2)) + A₂ * (r / (1 + r ^ 2) ^ 2) := fun r hr => by
    rw [hdim, smul_eq_mul, hA₁def, hA₂def]
    have := radial_le hb hV hε hjn (r := r) hr
    have e : r ^ (6 - 1) * f r = r ^ 5 * ((b + r ^ 2) ^ j *
        ‖((((r ^ 2 : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖) := by
      simp only [hf, hw]
    rw [e]
    exact this
  have hcont : Continuous fun r : ℝ =>
      r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) - 1) • f r :=
    (continuous_pow _).smul (continuous_shellNorm hwi b j n)
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) - 1) •
      f r := fun r hr => by
    have : (0 : ℝ) < r := hr
    simp only [hf, smul_eq_mul]
    positivity
  have hI : IntegrableOn (fun r : ℝ =>
      r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) - 1) • f r) (Ioi 0) := by
    refine hg.mono' hcont.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_of_nonneg (hnn r hr)]
    exact hpt r hr
  refine ⟨(integrable_fun_norm_addHaar volume (f := f)).mpr hI, ?_⟩
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))) f
  simp only [hf] at h
  rw [h, volume_real_ball_six, hdim, nsmul_eq_mul, smul_eq_mul]
  have hle := setIntegral_mono_on hI hg measurableSet_Ioi hpt
  rw [hdim, integral_add (i₁.const_mul A₁) (i₂.const_mul A₂), integral_const_mul,
    integral_const_mul] at hle
  have hle' : ∫ r in Ioi (0 : ℝ), r ^ (6 - 1) • f r ≤ A₁ * (π / (2 * ε)) + A₂ * (1 / 2) :=
    hle.trans (add_le_add (mul_le_mul_of_nonneg_left b₁ hA₁) (mul_le_mul_of_nonneg_left b₂ hA₂))
  unfold shellConst
  have e : ((6 : ℕ) : ℝ) * (π ^ 3 / 6) = π ^ 3 := by push_cast; ring
  rw [← mul_assoc, e]
  exact mul_le_mul_of_nonneg_left hle' (by positivity)

/-! ### The bound against a shifted quadratic form -/

/-- **The shell bound against a weight of polynomial growth** in the shifted quadratic form
`(v + σ)ᵀ A (v + σ)`: for `‖f v‖ ≤ C (b + (v + σ)ᵀ A (v + σ))^j`, `b ≥ 1`, `|V| ≤ K`, `ε > 0`
and `j + 4 ≤ n`, the product with `((v + σ)ᵀ A (v + σ) + V - iε)^{-n}` is integrable, with
absolute integral at most `C · shellConst b K ε j n · (det A)^{-3/2}`. -/
theorem integral_quadForm_shell_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {b K V ε : ℝ} (hb : 1 ≤ b) (hV : |V| ≤ K) (hε : 0 < ε) {j n : ℕ} (hjn : j + 4 ≤ n)
    (σ : Fin 2 → Fin 3 → ℝ) {f : (Fin 2 → Fin 3 → ℝ) → ℂ} (hf : AEStronglyMeasurable f)
    {C : ℝ} (hbd : ∀ v, ‖f v‖ ≤ C * (b + quadForm A (v + σ)) ^ j) :
    Integrable (fun v => f v *
        ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹) ∧
      ∫ v, ‖f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖ ≤
        C * (shellConst b K ε j n * (Real.sqrt A.det ^ 3)⁻¹) := by
  set w : ℂ := (V : ℂ) - (ε : ℂ) * I with hw
  have hwi : w.im < 0 := by simp [hw]; linarith
  set g : ℝ → ℝ := fun s => (b + s) ^ j * ‖(((s : ℂ) + w) ^ n)⁻¹‖ with hg
  have hgn : ∀ s, 0 ≤ s → 0 ≤ g s := fun s hs => by
    simp only [hg]
    have : 0 ≤ b + s := by linarith
    positivity
  obtain ⟨hE, hEb⟩ := integral_euclidean_shell_le hb hV hε hjn
  -- the integrability and integral of `g ∘ quadForm`
  have hiff := QED.Integration.Spatial.integrable_quadForm_iff hA (h := fun s => ((g s : ℝ) : ℂ))
  have hEc : Integrable fun x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3) => ((g (‖x‖ ^ 2) : ℝ) : ℂ) :=
    hE.ofReal
  have hQc := hiff.mpr hEc
  have hQ : Integrable fun v : Fin 2 → Fin 3 → ℝ => g (quadForm A v) := by
    refine hQc.norm.congr (Eventually.of_forall fun v => ?_)
    simp only [norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (hgn _ (QED.Integration.TwoLoop.quadForm_nonneg hA v))
  have hEq := QED.Integration.Spatial.integral_quadForm_eq hA (fun s => ((g s : ℝ) : ℂ))
  rw [integral_complex_ofReal, integral_complex_ofReal] at hEq
  have hQint : ∫ v, g (quadForm A v) =
      (Real.sqrt A.det ^ 3)⁻¹ * ∫ x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3), g (‖x‖ ^ 2) := by
    exact_mod_cast hEq
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg (f 0)).trans (hbd 0)
    have hp : 0 < (b + quadForm A (0 + σ)) ^ j :=
      pow_pos (by linarith [QED.Integration.TwoLoop.quadForm_nonneg hA (0 + σ)]) j
    exact nonneg_of_mul_nonneg_left h0 hp
  have hcq : Continuous fun v : Fin 2 → Fin 3 → ℝ => quadForm A (v + σ) := by
    simp only [QED.Integration.Spatial.quadForm_eq_sum]
    fun_prop
  have hmeas : AEStronglyMeasurable (fun v => f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + w) ^ n)⁻¹)
      volume :=
    hf.mul ((QED.Integration.TwoLoop.continuous_inv_add_pow hwi n).comp hcq).aestronglyMeasurable
  have hpt : ∀ v, ‖f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + w) ^ n)⁻¹‖ ≤
      C * g (quadForm A (v + σ)) := fun v => by
    rw [norm_mul, hg, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbd v) (norm_nonneg _)
  have hshift : Integrable fun v : Fin 2 → Fin 3 → ℝ => g (quadForm A (v + σ)) :=
    hQ.comp_add_right σ
  refine ⟨(hshift.const_mul C).mono' hmeas (Eventually.of_forall hpt), ?_⟩
  calc ∫ v, ‖f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + w) ^ n)⁻¹‖
      ≤ ∫ v, C * g (quadForm A (v + σ)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          (hshift.const_mul C) (Eventually.of_forall hpt)
    _ = C * ∫ v, g (quadForm A v) := by
        rw [integral_const_mul, integral_add_right_eq_self (fun v => g (quadForm A v)) σ]
    _ ≤ C * (shellConst b K ε j n * (Real.sqrt A.det ^ 3)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [hQint, mul_comm]
        exact mul_le_mul_of_nonneg_right hEb (by positivity)

end QED.ChainProof.SetANestV

end
