/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import QED.Integration.PacketMomentInversion

/-!
# The first position moment of a two-momentum Fourier integral

For a smooth, compactly supported amplitude `F(k, k')` on `ℝ³ × ℝ³` we study the two-momentum
Fourier integral
`packetFourier F x = ∫ d³k ∫ d³k' F(k, k') e^{i (k - k')·x}`
and prove that its first position moment converges absolutely and equals
`∫ d³x x_i packetFourier F x = (2π)³ (i/2) ∫ d³P (∂_{k_i} F - ∂_{k'_i} F)(P, P)`.

## Main definitions

* `QED.packetFourier`: the two-momentum Fourier integral.
* `QED.packetCoordAmplitude`: the amplitude `-i ∂_{k'_i} F`, which represents multiplication
  by `x_i` on the Fourier side.
* `QED.packetProfile`: the off-diagonal profile `h(Q) = ∫ d³k' F(Q + k', k')`.

## Main statements

* `QED.coord_mul_packetFourier`: `x_i packetFourier F x = packetFourier (-i ∂_{k'_i} F) x`.
* `QED.packetFourier_eq_integral_packetProfile`:
  `packetFourier F x = ∫ d³Q h(Q) e^{i Q·x}`.
* `QED.integrable_packetFourier`: `packetFourier F` is integrable.
* `QED.integrable_mul_packetFourier`: `x_i packetFourier F x` is integrable.
* `QED.integral_mul_packetFourier`: the value of the first moment.

## Implementation notes

Integration by parts in `k'_i` gives `x_i packetFourier F = packetFourier (-i ∂_{k'_i} F)`.
Iterating it four times in each coordinate bounds `packetFourier F` by a multiple of
`(1 + ‖x‖)^{-4}`, which is integrable on `ℝ³`. For the value, the translation `k = Q + k'` and
Fubini's theorem write `packetFourier F` as the Fourier integral of the profile `h`, and Fourier
inversion at the origin (`QED.Integration.integral_integral_mul_cexp_eq`) gives
`∫ packetFourier F = (2π)³ h(0) = (2π)³ ∫ F(P, P) dP`. Finally, the derivative of
`P ↦ F(P, P)` integrates to zero, so `-i ∫ ∂_{k'_i} F(P, P) dP` equals the symmetric form
`(i/2) ∫ (∂_{k_i} F - ∂_{k'_i} F)(P, P) dP`.
-/

@[expose] public section

open MeasureTheory Complex
open scoped ContDiff

namespace QED

/-- The two-momentum Fourier integral `∫ d³k ∫ d³k' F(k, k') e^{i (k - k')·x}`. -/
noncomputable def packetFourier (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∫ k, ∫ k', F k k' * Complex.exp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ))

/-- The amplitude `-i ∂_{k'_i} F`. Multiplying `packetFourier F` by the coordinate `x_i` gives
`packetFourier` of this amplitude (`QED.coord_mul_packetFourier`). -/
noncomputable def packetCoordAmplitude (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ) (i : Fin 3) :
    (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ :=
  fun k k' => -I * fderiv ℝ (Function.uncurry F) (k, k') (0, Pi.single i 1)

/-- The off-diagonal profile `h(Q) = ∫ d³k' F(Q + k', k')` of a two-momentum amplitude. -/
noncomputable def packetProfile (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ) (Q : Fin 3 → ℝ) : ℂ :=
  ∫ k', F (Q + k') k'

variable {F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ}

/-! ### Compact support bookkeeping -/

/-- A function vanishing outside a closed ball has compact support. -/
private lemma hasCompactSupport_of_forall_le_norm {α E : Type*} [NormedAddCommGroup α]
    [ProperSpace α] [Zero E] {f : α → E} {R : ℝ} (h : ∀ x, R ≤ ‖x‖ → f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx =>
    h x (le_of_lt (by simpa using hx))

/-- The sections `k' ↦ φ(k, k')` of a compactly supported function have compact support. -/
private lemma hasCompactSupport_section {E : Type*} [NormedAddCommGroup E]
    {φ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → E} (hφ : HasCompactSupport φ) (k : Fin 3 → ℝ) :
    HasCompactSupport fun k' => φ (k, k') := by
  obtain ⟨R, -, hR⟩ := hφ.exists_pos_le_norm
  exact hasCompactSupport_of_forall_le_norm fun k' hk' => hR _ (hk'.trans (norm_snd_le (k, k')))

/-- The diagonal restriction `P ↦ φ(P, P)` of a compactly supported function has compact
support. -/
private lemma hasCompactSupport_diag {E : Type*} [NormedAddCommGroup E]
    {φ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → E} (hφ : HasCompactSupport φ) :
    HasCompactSupport fun P => φ (P, P) := by
  obtain ⟨R, -, hR⟩ := hφ.exists_pos_le_norm
  exact hasCompactSupport_of_forall_le_norm fun P hP => hR _ (hP.trans (norm_snd_le (P, P)))

/-! ### Integration by parts -/

/-- The line derivative of the plane wave `k' ↦ e^{i (k - k')·x}` in the direction `e_i`. -/
private lemma hasLineDerivAt_cexp_dot (k k' x : Fin 3 → ℝ) (i : Fin 3) :
    HasLineDerivAt ℝ (fun k' : Fin 3 → ℝ => cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ)))
      (cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ)) * (-I * x i)) k' (Pi.single i 1) := by
  have hsum : ∀ t : ℝ, (∑ j, (k j - (k' + t • Pi.single i (1 : ℝ) : Fin 3 → ℝ) j) * x j) =
      (∑ j, (k j - k' j) * x j) - t * x i := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : ∀ j, (k j - (k' j + t * (Pi.single i (1 : ℝ) : Fin 3 → ℝ) j)) * x j =
        (k j - k' j) * x j - t * ((Pi.single i (1 : ℝ) : Fin 3 → ℝ) j * x j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Pi.single_apply]
  unfold HasLineDerivAt
  simp only [hsum]
  set a := ∑ j, (k j - k' j) * x j
  have h1 : HasDerivAt (fun t : ℝ => ((a - t * x i : ℝ) : ℂ)) (((-(x i)) : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (x i)).const_sub a
    simpa using this.ofReal_comp
  have h2 := (h1.const_mul I).cexp
  convert h2 using 1
  simp only [zero_mul, sub_zero, Complex.ofReal_neg]
  ring

/-- Integration by parts in `k'_i`: `x_i ∫ d³k' F(k, k') e^{i (k - k')·x}` equals
`∫ d³k' (-i ∂_{k'_i} F)(k, k') e^{i (k - k')·x}`. -/
theorem coord_mul_integral_mul_cexp (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) (i : Fin 3) (k x : Fin 3 → ℝ) :
    (x i : ℂ) * ∫ k', F k k' * cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ)) =
      ∫ k', packetCoordAmplitude F i k k' * cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ)) := by
  set v : Fin 3 → ℝ := Pi.single i 1
  set e : (Fin 3 → ℝ) → ℂ := fun k' => cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ))
  have he_cont : Continuous e := by fun_prop
  have hmk : Continuous fun k' : Fin 3 → ℝ => (k, k') := continuous_const.prodMk continuous_id
  have hcontF : Continuous fun k' => F k k' := hF.continuous.comp hmk
  have hcontF' : Continuous fun k' => fderiv ℝ (Function.uncurry F) (k, k') (0, v) :=
    ((hF.continuous_fderiv (by simp)).comp hmk).clm_apply continuous_const
  have hsec : HasCompactSupport fun k' => F k k' := hasCompactSupport_section hFc k
  have hsec' : HasCompactSupport fun k' => fderiv ℝ (Function.uncurry F) (k, k') (0, v) :=
    hasCompactSupport_section (hFc.fderiv_apply (𝕜 := ℝ) (0, v)) k
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := v)
    (f := fun k' => F k k') (f' := fun k' => fderiv ℝ (Function.uncurry F) (k, k') (0, v))
    (g := e) (g' := fun k' => e k' * (-I * x i)) ?_ ?_ ?_ ?_ ?_
  rotate_left
  · simp only [ContinuousLinearMap.mul_apply']
    exact (hcontF'.mul he_cont).integrable_of_hasCompactSupport hsec'.mul_right
  · simp only [ContinuousLinearMap.mul_apply']
    exact (hcontF.mul (he_cont.mul continuous_const)).integrable_of_hasCompactSupport
      hsec.mul_right
  · simp only [ContinuousLinearMap.mul_apply']
    exact (hcontF.mul he_cont).integrable_of_hasCompactSupport hsec.mul_right
  · intro k' _
    have hd : HasFDerivAt (fun k' => F k k')
        ((fderiv ℝ (Function.uncurry F) (k, k')).comp (ContinuousLinearMap.inr ℝ _ _)) k' :=
      ((hF.differentiable (by simp)).differentiableAt.hasFDerivAt).comp k'
        (hasFDerivAt_prodMk_right k k')
    simpa using hd.hasLineDerivAt v
  · intro k' _
    exact hasLineDerivAt_cexp_dot k k' x i
  simp only [ContinuousLinearMap.mul_apply'] at key
  have hl : ∀ k', F k k' * (e k' * (-I * x i)) = (-I * x i) * (F k k' * e k') := fun k' => by
    ring
  simp_rw [hl, integral_const_mul] at key
  simp only [packetCoordAmplitude, mul_assoc]
  rw [integral_const_mul]
  linear_combination I * key + (x i : ℂ) * (∫ k', F k k' * e k') * I_sq

/-- Multiplication by a coordinate on the position side: `x_i packetFourier F x` equals
`packetFourier (-i ∂_{k'_i} F) x`. -/
theorem coord_mul_packetFourier (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) (i : Fin 3) (x : Fin 3 → ℝ) :
    (x i : ℂ) * packetFourier F x = packetFourier (packetCoordAmplitude F i) x := by
  unfold packetFourier
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
    coord_mul_integral_mul_cexp hF hFc i k x)

/-- The amplitude `-i ∂_{k'_i} F` of a smooth amplitude is smooth. -/
theorem contDiff_packetCoordAmplitude (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Fin 3) :
    ContDiff ℝ ∞ (Function.uncurry (packetCoordAmplitude F i)) :=
  contDiff_const.mul (((contDiff_infty_iff_fderiv.1 hF).2).clm_apply contDiff_const)

/-- The amplitude `-i ∂_{k'_i} F` of a compactly supported amplitude has compact support. -/
theorem hasCompactSupport_packetCoordAmplitude (hFc : HasCompactSupport (Function.uncurry F))
    (i : Fin 3) : HasCompactSupport (Function.uncurry (packetCoordAmplitude F i)) :=
  (hFc.fderiv_apply (𝕜 := ℝ) ((0 : Fin 3 → ℝ), (Pi.single i 1 : Fin 3 → ℝ))).mul_left
    (f := fun _ => -I)

/-! ### Reduction to a single Fourier integral -/

/-- The off-diagonal profile of a continuous, compactly supported amplitude is continuous. -/
theorem continuous_packetProfile (hF : Continuous (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) : Continuous (packetProfile F) := by
  obtain ⟨R, -, hR⟩ := hFc.exists_pos_le_norm
  have h : packetProfile F =
      fun Q => ∫ k' in Metric.closedBall (0 : Fin 3 → ℝ) R, F (Q + k') k' := by
    ext Q
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    intro k' hk'
    exact hR (Q + k', k') ((by simpa using hk' : R < ‖k'‖).le.trans (norm_snd_le (Q + k', k')))
  rw [h]
  exact continuous_parametric_integral_of_continuous (f := fun Q k' => F (Q + k') k')
    (hF.comp ((continuous_fst.add continuous_snd).prodMk continuous_snd)) (isCompact_closedBall _ _)

/-- The off-diagonal profile of a compactly supported amplitude has compact support. -/
theorem hasCompactSupport_packetProfile (hFc : HasCompactSupport (Function.uncurry F)) :
    HasCompactSupport (packetProfile F) := by
  obtain ⟨R, hR0, hR⟩ := hFc.exists_pos_le_norm
  refine hasCompactSupport_of_forall_le_norm (R := 2 * R) fun Q hQ => ?_
  have hzero : ∀ k', F (Q + k') k' = 0 := by
    intro k'
    by_cases hk : R ≤ ‖k'‖
    · exact hR (Q + k', k') (hk.trans (norm_snd_le (Q + k', k')))
    · have h1 : ‖Q‖ ≤ ‖Q + k'‖ + ‖k'‖ := by simpa using norm_sub_le (Q + k') k'
      exact hR (Q + k', k') (le_trans (by linarith) (norm_fst_le (Q + k', k')))
  simp [packetProfile, hzero]

/-- The off-diagonal profile of a continuous, compactly supported amplitude is integrable. -/
theorem integrable_packetProfile (hF : Continuous (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) : Integrable (packetProfile F) :=
  (continuous_packetProfile hF hFc).integrable_of_hasCompactSupport
    (hasCompactSupport_packetProfile hFc)

/-- After the translation `k = Q + k'` and Fubini's theorem, the two-momentum Fourier integral is
the Fourier integral of the off-diagonal profile: `packetFourier F x = ∫ d³Q h(Q) e^{i Q·x}`. -/
theorem packetFourier_eq_integral_packetProfile (hF : Continuous (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) (x : Fin 3 → ℝ) :
    packetFourier F x = ∫ Q, packetProfile F Q * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ)) := by
  obtain ⟨R, hR0, hR⟩ := hFc.exists_pos_le_norm
  unfold packetFourier
  have hint1 : Integrable (Function.uncurry fun k k' : Fin 3 → ℝ =>
      F k k' * cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ))) (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hF.mul (by fun_prop)
    · refine hasCompactSupport_of_forall_le_norm (R := R) fun p hp => ?_
      show F p.1 p.2 * _ = 0
      rw [show F p.1 p.2 = 0 from hR p hp, zero_mul]
  rw [integral_integral_swap hint1]
  have htr : ∀ k' : Fin 3 → ℝ,
      ∫ k, F k k' * cexp (I * ((∑ j, (k j - k' j) * x j : ℝ) : ℂ)) =
        ∫ Q, F (Q + k') k' * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ)) := by
    intro k'
    rw [← integral_add_right_eq_self _ k']
    congr 1
    ext Q
    simp only [Pi.add_apply, add_sub_cancel_right]
  simp_rw [htr]
  have hint2 : Integrable (Function.uncurry fun k' Q : Fin 3 → ℝ =>
      F (Q + k') k' * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ))) (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hF.comp ((continuous_snd.add continuous_fst).prodMk continuous_fst)).mul
        (by fun_prop)
    · refine hasCompactSupport_of_forall_le_norm (R := 2 * R) fun p hp => ?_
      show F (p.2 + p.1) p.1 * _ = 0
      suffices F (p.2 + p.1) p.1 = 0 by rw [this, zero_mul]
      have hp' : 2 * R ≤ max ‖p.1‖ ‖p.2‖ := hp
      by_cases hk : R ≤ ‖p.1‖
      · exact hR (p.2 + p.1, p.1) (hk.trans (norm_snd_le (p.2 + p.1, p.1)))
      · have h1 : ‖p.2‖ ≤ ‖p.2 + p.1‖ + ‖p.1‖ := by simpa using norm_sub_le (p.2 + p.1) p.1
        have h2 : 2 * R ≤ ‖p.2‖ := by
          rcases le_max_iff.1 hp' with h | h
          · linarith
          · exact h
        exact hR (p.2 + p.1, p.1) (le_trans (by linarith) (norm_fst_le (p.2 + p.1, p.1)))
  rw [integral_integral_swap hint2]
  congr 1
  ext Q
  rw [integral_mul_const]
  rfl

/-! ### Continuity, boundedness and decay -/

/-- The two-momentum Fourier integral of a continuous, compactly supported amplitude is
continuous. -/
theorem continuous_packetFourier (hF : Continuous (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) : Continuous (packetFourier F) := by
  have h : packetFourier F =
      fun x => ∫ Q, packetProfile F Q * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ)) :=
    funext (packetFourier_eq_integral_packetProfile hF hFc)
  rw [h]
  have hc := continuous_packetProfile hF hFc
  refine continuous_of_dominated (bound := fun Q => ‖packetProfile F Q‖) (fun x => ?_)
    (fun x => ?_) (integrable_packetProfile hF hFc).norm ?_
  · exact (hc.mul (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun Q => ?_
    rw [norm_mul, norm_exp_I_mul_ofReal, mul_one]
  · exact Filter.Eventually.of_forall fun Q => continuous_const.mul (by fun_prop)

/-- The two-momentum Fourier integral is bounded by the `L¹` norm of the off-diagonal profile. -/
theorem norm_packetFourier_le (hF : Continuous (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) (x : Fin 3 → ℝ) :
    ‖packetFourier F x‖ ≤ ∫ Q, ‖packetProfile F Q‖ := by
  rw [packetFourier_eq_integral_packetProfile hF hFc]
  refine norm_integral_le_of_norm_le (integrable_packetProfile hF hFc).norm
    (Filter.Eventually.of_forall fun Q => ?_)
  rw [norm_mul, norm_exp_I_mul_ofReal, mul_one]

/-- `(1 + a)⁴ ≤ 8 (1 + a⁴)` for `a ≥ 0`. -/
private lemma one_add_pow_four_le {a : ℝ} (ha : 0 ≤ a) : (1 + a) ^ 4 ≤ 8 * (1 + a ^ 4) := by
  have h : 8 * (1 + a ^ 4) - (1 + a) ^ 4 = (a - 1) ^ 2 * (7 * a ^ 2 + 10 * a + 7) := by ring
  have h2 : 0 ≤ 7 * a ^ 2 + 10 * a + 7 := by
    have := sq_nonneg a
    linarith
  have h3 : 0 ≤ (a - 1) ^ 2 * (7 * a ^ 2 + 10 * a + 7) := mul_nonneg (sq_nonneg _) h2
  linarith

/-- The sup norm on `Fin 3 → ℝ` is attained at a coordinate. -/
private lemma exists_norm_eq_norm_apply (x : Fin 3 → ℝ) : ∃ j, ‖x‖ = ‖x j‖ := by
  obtain ⟨j, hj⟩ := Finite.exists_max fun b => ‖x b‖
  exact ⟨j, le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj) (norm_le_pi_norm x j)⟩

/-- The two-momentum Fourier integral of a smooth, compactly supported amplitude is integrable:
four integrations by parts in each coordinate bound it by a multiple of `(1 + ‖x‖)^{-4}`. -/
theorem integrable_packetFourier (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) : Integrable (packetFourier F) := by
  set D4 : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ := fun j =>
    packetCoordAmplitude (packetCoordAmplitude
      (packetCoordAmplitude (packetCoordAmplitude F j) j) j) j with hD4_def
  have hD : ∀ (G : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ) (j : Fin 3),
      ContDiff ℝ ∞ (Function.uncurry G) ∧ HasCompactSupport (Function.uncurry G) →
      ContDiff ℝ ∞ (Function.uncurry (packetCoordAmplitude G j)) ∧
        HasCompactSupport (Function.uncurry (packetCoordAmplitude G j)) :=
    fun G j hG => ⟨contDiff_packetCoordAmplitude hG.1 j,
      hasCompactSupport_packetCoordAmplitude hG.2 j⟩
  have h0 : ContDiff ℝ ∞ (Function.uncurry F) ∧ HasCompactSupport (Function.uncurry F) :=
    ⟨hF, hFc⟩
  have hpow : ∀ j x, (x j : ℂ) ^ 4 * packetFourier F x = packetFourier (D4 j) x := by
    intro j x
    have h1 := hD _ j h0
    have h2 := hD _ j h1
    have h3 := hD _ j h2
    simp only [hD4_def]
    rw [← coord_mul_packetFourier h3.1 h3.2, ← coord_mul_packetFourier h2.1 h2.2,
      ← coord_mul_packetFourier h1.1 h1.2, ← coord_mul_packetFourier hF hFc]
    ring
  have hD4 : ∀ j, ContDiff ℝ ∞ (Function.uncurry (D4 j)) ∧
      HasCompactSupport (Function.uncurry (D4 j)) :=
    fun j => hD _ j (hD _ j (hD _ j (hD _ j h0)))
  set M0 := ∫ Q, ‖packetProfile F Q‖
  set M : Fin 3 → ℝ := fun j => ∫ Q, ‖packetProfile (D4 j) Q‖
  have hM : ∀ j, 0 ≤ M j := fun j => integral_nonneg fun _ => norm_nonneg _
  set C := 8 * (M0 + ∑ j, M j) with hC_def
  have hbound : ∀ x, ‖packetFourier F x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
    intro x
    obtain ⟨j, hj⟩ := exists_norm_eq_norm_apply x
    have hb0 : ‖packetFourier F x‖ ≤ M0 := norm_packetFourier_le hF.continuous hFc x
    have hbj : ‖x j‖ ^ 4 * ‖packetFourier F x‖ ≤ M j := by
      have := norm_packetFourier_le (hD4 j).1.continuous (hD4 j).2 x
      rw [← hpow j x, norm_mul, norm_pow, Complex.norm_real] at this
      exact this
    have hMj : M j ≤ ∑ j, M j := Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ j)
    have hpos : 0 < (1 + ‖x‖) ^ 4 := by positivity
    have hkey : (1 + ‖x‖) ^ 4 * ‖packetFourier F x‖ ≤ C := by
      have h8 := one_add_pow_four_le (norm_nonneg x)
      rw [hj] at h8 ⊢
      calc (1 + ‖x j‖) ^ 4 * ‖packetFourier F x‖
          ≤ 8 * (1 + ‖x j‖ ^ 4) * ‖packetFourier F x‖ :=
            mul_le_mul_of_nonneg_right h8 (norm_nonneg _)
        _ = 8 * (‖packetFourier F x‖ + ‖x j‖ ^ 4 * ‖packetFourier F x‖) := by ring
        _ ≤ C := by rw [hC_def]; linarith
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  refine Integrable.mono' ((integrable_one_add_norm (μ := volume) (E := Fin 3 → ℝ) (r := 4)
    (by norm_num [Module.finrank_fin_fun])).const_mul C)
    (continuous_packetFourier hF.continuous hFc).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- **Absolute convergence of the first position moment.** For a smooth, compactly supported
amplitude `F`, the function `x ↦ x_i packetFourier F x` is integrable on `ℝ³`. -/
theorem integrable_mul_packetFourier (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) (i : Fin 3) :
    Integrable fun x : Fin 3 → ℝ => (x i : ℂ) * packetFourier F x :=
  (integrable_packetFourier (contDiff_packetCoordAmplitude hF i)
    (hasCompactSupport_packetCoordAmplitude hFc i)).congr
    (Filter.Eventually.of_forall fun x => (coord_mul_packetFourier hF hFc i x).symm)

/-! ### The value of the first moment -/

/-- The derivative of the diagonal restriction `P ↦ Φ(P, P)` of a smooth, compactly supported
function integrates to zero: `∫ d³P DΦ(P, P)(v, v) = 0`. -/
private lemma integral_fderiv_diag_eq_zero {Φ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) (v : Fin 3 → ℝ) :
    ∫ P, fderiv ℝ Φ (P, P) (v, v) = 0 := by
  have hdiag : Continuous fun P : Fin 3 → ℝ => (P, P) := continuous_id.prodMk continuous_id
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := v)
    (f := fun _ => (1 : ℂ)) (f' := fun _ => 0)
    (g := fun P => Φ (P, P)) (g' := fun P => fderiv ℝ Φ (P, P) (v, v)) ?_ ?_ ?_ ?_ ?_
  rotate_left
  · simp only [ContinuousLinearMap.mul_apply', zero_mul]
    exact integrable_zero _ _ _
  · simp only [ContinuousLinearMap.mul_apply', one_mul]
    exact ((((hΦ.continuous_fderiv (by simp)).comp hdiag).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
      (hasCompactSupport_diag (hΦc.fderiv_apply (𝕜 := ℝ) (v, v)))
  · simp only [ContinuousLinearMap.mul_apply', one_mul]
    exact (hΦ.continuous.comp hdiag).integrable_of_hasCompactSupport (hasCompactSupport_diag hΦc)
  · intro P _
    simpa using (hasFDerivAt_const (1 : ℂ) P).hasLineDerivAt v
  · intro P _
    have hd : HasFDerivAt (fun P => Φ (P, P))
        ((fderiv ℝ Φ (P, P)).comp ((ContinuousLinearMap.id ℝ _).prod
          (ContinuousLinearMap.id ℝ _))) P :=
      ((hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp P
        ((hasFDerivAt_id P).prodMk (hasFDerivAt_id P))
    simpa using hd.hasLineDerivAt v
  simpa using key

/-- **The first position moment of the two-momentum Fourier integral.** For a smooth, compactly
supported amplitude `F`,
`∫ d³x x_i packetFourier F x = (2π)³ (i/2) ∫ d³P (∂_{k_i} F - ∂_{k'_i} F)(P, P)`. -/
theorem integral_mul_packetFourier (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hFc : HasCompactSupport (Function.uncurry F)) (i : Fin 3) :
    ∫ x : Fin 3 → ℝ, (x i : ℂ) * packetFourier F x =
      (2 * Real.pi) ^ 3 * (I / 2) *
        ∫ P : Fin 3 → ℝ, (fderiv ℝ (Function.uncurry F) (P, P) (Pi.single i 1, 0)
          - fderiv ℝ (Function.uncurry F) (P, P) (0, Pi.single i 1)) := by
  have hG := contDiff_packetCoordAmplitude hF i
  have hGc := hasCompactSupport_packetCoordAmplitude hFc i
  have h1 : ∫ x : Fin 3 → ℝ, (x i : ℂ) * packetFourier F x =
      ∫ x, packetFourier (packetCoordAmplitude F i) x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => coord_mul_packetFourier hF hFc i x)
  have h2 : ∫ x, packetFourier (packetCoordAmplitude F i) x =
      (2 * Real.pi) ^ 3 * packetProfile (packetCoordAmplitude F i) 0 := by
    have hrep := funext (packetFourier_eq_integral_packetProfile hG.continuous hGc)
    rw [hrep]
    refine QED.Integration.integral_integral_mul_cexp_eq
      (continuous_packetProfile hG.continuous hGc) (integrable_packetProfile hG.continuous hGc) ?_
    rw [← hrep]
    exact integrable_packetFourier hG hGc
  have h3 : packetProfile (packetCoordAmplitude F i) 0 =
      -I * ∫ P, fderiv ℝ (Function.uncurry F) (P, P) (0, Pi.single i 1) := by
    simp only [packetProfile, packetCoordAmplitude, zero_add]
    exact integral_const_mul _ _
  have hcd : ∀ w, Integrable fun P : Fin 3 → ℝ => fderiv ℝ (Function.uncurry F) (P, P) w :=
    fun w => (((hF.continuous_fderiv (by simp)).comp
      (continuous_id.prodMk continuous_id)).clm_apply
        continuous_const).integrable_of_hasCompactSupport
      (hasCompactSupport_diag (hFc.fderiv_apply (𝕜 := ℝ) w))
  have hsum := integral_fderiv_diag_eq_zero hF hFc (Pi.single i 1)
  have hsplit : ∫ P : Fin 3 → ℝ,
      fderiv ℝ (Function.uncurry F) (P, P)
        ((Pi.single i 1 : Fin 3 → ℝ), (Pi.single i 1 : Fin 3 → ℝ)) =
      (∫ P, fderiv ℝ (Function.uncurry F) (P, P) (Pi.single i 1, 0)) +
        ∫ P, fderiv ℝ (Function.uncurry F) (P, P) (0, Pi.single i 1) := by
    rw [← integral_add (hcd _) (hcd _)]
    congr 1
    ext P
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [h1, h2, h3, integral_sub (hcd _) (hcd _)]
  linear_combination -(2 * (Real.pi : ℂ)) ^ 3 * (I / 2) * (hsplit.symm.trans hsum)

end QED
