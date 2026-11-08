/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.PacketAmplitude
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The sharp-packet limit of the source magnetic moment

This module supplies the analytic steps that turn the moment formula for the wave-packet
current density into the response magnetic moment as the packet width `λ → 0⁺` (packet 4b,
theorem (W₄)). Write `F(k, k') = w(k') w(k) M(k', k)` for the packet amplitude and
`M̃(k, k') = M(k', k)`.

* On the diagonal the derivatives of the two weights cancel, because both are the same real
  function: `(∂_k - ∂_{k'}) F (P, P) = w(P)² (∂_k - ∂_{k'}) M̃ (P, P)`.
* The packet weight `ρ_λ(P) = w(P)² (2π)³ 2ω_P` is nonnegative, has integral `⟨e|e⟩ > 0`, and
  vanishes outside a ball of radius `O(λ)`; hence `ρ_λ`-averages of a continuous function `g`
  tend to `g(0)`.
* At Breit momenta `k = -t e₁`, `k' = t e₁`, the response definition (R₀) gives
  `M̃(-t e₁, t e₁) = 4 i m μ t + o(t)`, so `(∂_k - ∂_{k'}) M̃ (0, 0) = -4 i m μ`.

## Main statements

* `QED.OneLoop.fderiv_packetAmplitude_diag_sub`: the diagonal derivative of `F`.
* `QED.OneLoop.packetNormSq_pos`: the squared norm of the packet is positive.
* `QED.OneLoop.tendsto_packetAverage`: the sharp-packet limit of a weighted average.
* `QED.OneLoop.fderiv_packetMatrixElement_breit`: the Breit identification of `μ`.
* `QED.OneLoop.tendsto_integral_fderiv_packetAmplitude_div_packetNormSq`: the combination; the
  right side of the moment formula, divided by `⟨e|e⟩`, tends to `μ` as `λ → 0⁺`.
-/

public section

open Filter Topology MeasureTheory Complex

namespace QED.OneLoop

/-! ### The diagonal derivative of the packet amplitude -/

/-- On the diagonal `k = k' = P`, the derivatives of the two packet weights cancel in
`(∂_{k_i} - ∂_{k'_i}) F`, leaving `w(P)² (∂_{k_i} - ∂_{k'_i}) M̃`. -/
theorem fderiv_packetAmplitude_diag_sub (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (φ : ℝ → ℝ) (lam : ℝ) (P : Fin 3 → ℝ) (i : Fin 3)
    (hw : DifferentiableAt ℝ (packetWeight m φ lam) P)
    (hM : DifferentiableAt ℝ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) (P, P)) :
    fderiv ℝ (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) (P, P)
        (Pi.single i 1, 0)
      - fderiv ℝ (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) (P, P)
        (0, Pi.single i 1)
    = ((packetWeight m φ lam P ^ 2 : ℝ) : ℂ) *
      (fderiv ℝ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) (P, P) (Pi.single i 1, 0)
        - fderiv ℝ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) (P, P) (0, Pi.single i 1)) := by
  set w := packetWeight m φ lam
  set G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℂ := fun kk =>
    packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1
  have hF : Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam) =
      fun kk => ((w kk.2 * w kk.1 : ℝ) : ℂ) * G kk := rfl
  have hw1 : HasFDerivAt (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => w kk.1)
      ((fderiv ℝ w P).comp (ContinuousLinearMap.fst ℝ _ _)) (P, P) := by
    have h : HasFDerivAt w (fderiv ℝ w P) ((P, P) : (Fin 3 → ℝ) × (Fin 3 → ℝ)).1 :=
      hw.hasFDerivAt
    exact h.comp (P, P) hasFDerivAt_fst
  have hw2 : HasFDerivAt (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) => w kk.2)
      ((fderiv ℝ w P).comp (ContinuousLinearMap.snd ℝ _ _)) (P, P) := by
    have h : HasFDerivAt w (fderiv ℝ w P) ((P, P) : (Fin 3 → ℝ) × (Fin 3 → ℝ)).2 :=
      hw.hasFDerivAt
    exact h.comp (P, P) hasFDerivAt_snd
  have hcast := ofRealCLM.hasFDerivAt.comp (P, P) (hw2.fun_mul hw1)
  have hfull : HasFDerivAt (fun kk => ((w kk.2 * w kk.1 : ℝ) : ℂ) * G kk) _ (P, P) :=
    hcast.fun_mul hM.hasFDerivAt
  rw [hF, hfull.fderiv]
  simp
  ring

/-! ### The packet weight -/

/-- A compactly supported function on `ℝ` vanishes on `(R, ∞)` for some `R ≥ 1`. -/
private lemma exists_one_le_forall_lt_eq_zero {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) :
    ∃ R, 1 ≤ R ∧ ∀ t, R < t → φ t = 0 := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, le_max_right _ _, fun t ht => ?_⟩
  by_contra h
  have hmem : t ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ h)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  linarith [le_abs_self t, le_max_left R 1]

/-- If `φ` vanishes on `(R, ∞)` with `R ≥ 1`, then the profile `φ(|k|²/λ²)` vanishes unless
every coordinate of `k` is at most `λ R` in absolute value. -/
private lemma norm_le_of_profile_ne_zero {φ : ℝ → ℝ} {R lam : ℝ} (hR1 : 1 ≤ R)
    (hR : ∀ t, R < t → φ t = 0) (hlam : 0 < lam) {k : Fin 3 → ℝ}
    (hk : φ ((∑ j, k j ^ 2) / lam ^ 2) ≠ 0) : ‖k‖ ≤ lam * R := by
  have hlR : 0 ≤ lam * R := by positivity
  refine (pi_norm_le_iff_of_nonneg hlR).2 fun j => ?_
  rw [Real.norm_eq_abs]
  by_contra hj
  rw [not_le] at hj
  have h1 : (lam * R) ^ 2 < k j ^ 2 := by
    rw [← sq_abs (k j)]
    exact pow_lt_pow_left₀ hj hlR two_ne_zero
  have h2 : k j ^ 2 ≤ ∑ i, k i ^ 2 :=
    Finset.single_le_sum (f := fun i => k i ^ 2) (fun i _ => sq_nonneg (k i)) (Finset.mem_univ j)
  have h3 : R * lam ^ 2 ≤ (lam * R) ^ 2 := by
    have : 0 ≤ lam ^ 2 * (R * (R - 1)) := by
      apply mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
    nlinarith
  apply hk (hR _ _)
  rw [lt_div_iff₀ (by positivity)]
  linarith

private lemma continuous_oneParticleMomentum_zero (m : ℝ) :
    Continuous fun k : Fin 3 → ℝ => oneParticleMomentum m k 0 := by
  simp only [oneParticleMomentum, Fin.cons_zero]
  fun_prop

private lemma packetDenom_pos {m : ℝ} (hm : 0 < m) (k : Fin 3 → ℝ) :
    0 < (2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0) := by
  have := oneParticleMomentum_pos hm k
  positivity

private lemma continuous_packetWeight {m : ℝ} (hm : 0 < m) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (lam : ℝ) : Continuous (packetWeight m φ lam) := by
  unfold packetWeight
  refine Continuous.div (hφ.comp (by fun_prop)) ?_ fun k => (packetDenom_pos hm k).ne'
  exact continuous_const.mul (continuous_const.mul (continuous_oneParticleMomentum_zero m))

/-- The squared norm of the packet is positive. -/
theorem packetNormSq_pos {m : ℝ} (hm : 0 < m) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) {lam : ℝ} (hlam : 0 < lam) :
    0 < packetNormSq m φ lam := by
  obtain ⟨R, hR1, hR⟩ := exists_one_le_forall_lt_eq_zero hφc
  obtain ⟨t, ht, hφt⟩ := hφ0
  unfold packetNormSq
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := Pi.single 0 (lam * Real.sqrt t)) ?_ ?_ ?_ ?_
  · refine Continuous.div ((hφ.comp (by fun_prop)).pow 2) ?_ fun k => (packetDenom_pos hm k).ne'
    exact continuous_const.mul (continuous_const.mul (continuous_oneParticleMomentum_zero m))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) (lam * R))
      fun k hk => ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hk
    have h : φ ((∑ j, k j ^ 2) / lam ^ 2) = 0 := by
      by_contra h
      exact hk (norm_le_of_profile_ne_zero hR1 hR hlam h)
    simp [h]
  · exact fun k => div_nonneg (sq_nonneg _) (packetDenom_pos hm k).le
  · have hsum : (∑ j, (Pi.single 0 (lam * Real.sqrt t) : Fin 3 → ℝ) j ^ 2) / lam ^ 2 = t := by
      simp [Fin.sum_univ_three, mul_pow, Real.sq_sqrt ht, hlam.ne']
    rw [hsum]
    exact div_ne_zero (pow_ne_zero 2 hφt) (packetDenom_pos hm _).ne'

/-- As the packet becomes sharply peaked at rest (`λ → 0⁺`), the average of a continuous
function `g` against the normalized packet weight `w(P)² (2π)³ 2ω_P / ⟨e|e⟩` tends to
`g(0)`. -/
theorem tendsto_packetAverage {m : ℝ} (hm : 0 < m) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0)
    {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g) :
    Tendsto (fun lam : ℝ =>
      (∫ P : Fin 3 → ℝ, ((packetWeight m φ lam P ^ 2 *
          ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m P 0)) : ℝ) : ℂ) * g P)
        / (packetNormSq m φ lam : ℂ)) (𝓝[>] 0) (𝓝 (g 0)) := by
  obtain ⟨R, hR1, hR⟩ := exists_one_le_forall_lt_eq_zero hφc
  set ρ : ℝ → (Fin 3 → ℝ) → ℝ := fun lam P =>
    packetWeight m φ lam P ^ 2 * ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m P 0))
    with hρ
  have hρ_cont : ∀ lam, Continuous (ρ lam) := fun lam =>
    ((continuous_packetWeight hm hφ lam).pow 2).mul
      (continuous_const.mul (continuous_const.mul (continuous_oneParticleMomentum_zero m)))
  have hρ_nonneg : ∀ lam P, 0 ≤ ρ lam P := fun lam P =>
    mul_nonneg (sq_nonneg _) (packetDenom_pos hm P).le
  have hρ_supp : ∀ lam, 0 < lam → ∀ P, ρ lam P ≠ 0 → ‖P‖ ≤ lam * R := by
    intro lam hlam P hP
    refine norm_le_of_profile_ne_zero hR1 hR hlam fun h => hP ?_
    simp [hρ, packetWeight, h]
  have hρ_cs : ∀ lam, 0 < lam → HasCompactSupport (ρ lam) := by
    intro lam hlam
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) (lam * R))
      fun P hP => ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hP
    by_contra h
    exact hP (hρ_supp lam hlam P h)
  have hρ_int : ∀ lam, 0 < lam → Integrable (ρ lam) := fun lam hlam =>
    (hρ_cont lam).integrable_of_hasCompactSupport (hρ_cs lam hlam)
  have hN : ∀ lam, packetNormSq m φ lam = ∫ P, ρ lam P := fun lam => packetNormSq_eq m φ lam
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.1 hg.continuousAt (ε / 2) (half_pos hε)
  refine ⟨δ / R, div_pos hδ (by linarith), fun {lam} hlam hdist => ?_⟩
  have hl : 0 < lam := hlam
  have hlR : lam * R < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hl, lt_div_iff₀ (by linarith)] at hdist
    exact hdist
  have hNpos : 0 < packetNormSq m φ lam := packetNormSq_pos hm hφ hφc hφ0 hl
  have hNC : (packetNormSq m φ lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hNpos.ne'
  have hρC : Integrable fun P => ((ρ lam P : ℝ) : ℂ) := (hρ_int lam hl).ofReal
  have hint1 : Integrable fun P => ((ρ lam P : ℝ) : ℂ) * g P :=
    ((continuous_ofReal.comp (hρ_cont lam)).mul hg).integrable_of_hasCompactSupport
      ((hρ_cs lam hl).comp_left ofReal_zero).mul_right
  have hint0 : Integrable fun P => ((ρ lam P : ℝ) : ℂ) * g 0 := hρC.mul_const _
  have hkey : (∫ P, ((ρ lam P : ℝ) : ℂ) * g P) / (packetNormSq m φ lam : ℂ) - g 0 =
      (∫ P, ((ρ lam P : ℝ) : ℂ) * (g P - g 0)) / (packetNormSq m φ lam : ℂ) := by
    have h0 : ∫ P, ((ρ lam P : ℝ) : ℂ) * g 0 = (packetNormSq m φ lam : ℂ) * g 0 := by
      rw [integral_mul_const, integral_complex_ofReal, ← hN]
    simp_rw [mul_sub]
    rw [integral_sub hint1 hint0, h0]
    field_simp
  have hbound : ‖∫ P, ((ρ lam P : ℝ) : ℂ) * (g P - g 0)‖ ≤ ∫ P, ρ lam P * (ε / 2) := by
    refine norm_integral_le_of_norm_le ((hρ_int lam hl).mul_const _)
      (Eventually.of_forall fun P => ?_)
    rw [norm_mul, norm_real, Real.norm_of_nonneg (hρ_nonneg lam P)]
    by_cases h : ρ lam P = 0
    · simp [h]
    · refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg lam P)
      have hP := hρ_supp lam hl P h
      rw [← dist_eq_norm]
      exact (hgδ (by rw [dist_zero_right]; linarith)).le
  rw [integral_mul_const, ← hN] at hbound
  rw [dist_eq_norm, hkey, norm_div, norm_real, Real.norm_of_nonneg hNpos.le,
    div_lt_iff₀ hNpos]
  nlinarith

/-! ### The Breit identification of the response magnetic moment -/

/-- If `μ` is a response magnetic moment (R₀) and `M̃(k, k') = M(k', k)` is differentiable at
the origin, then `(∂_{k_1} - ∂_{k'_1}) M̃ (0, 0) = -4 i m μ`. Along the Breit momenta
`k = -t e₁`, `k' = t e₁` (momentum transfer `q = 2t`), (R₀) gives
`M̃(-t e₁, t e₁) = 4 i m μ t + o(t)` as `t → 0⁺`, while the derivative of `M̃` along this line is
`-(∂_{k_1} - ∂_{k'_1}) M̃ (0, 0)`. -/
theorem fderiv_packetMatrixElement_breit (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ)
    (hM : DifferentiableAt ℝ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) (0, 0))
    {μ : ℝ} (hμ : IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ) :
    fderiv ℝ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) (0, 0) (Pi.single 0 1, 0)
      - fderiv ℝ (fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1) (0, 0) (0, Pi.single 0 1)
    = -4 * I * m * μ := by
  set G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℂ := fun kk =>
    packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1 with hG
  set L := fderiv ℝ G (0, 0)
  set v : (Fin 3 → ℝ) × (Fin 3 → ℝ) := (-Pi.single 0 1, Pi.single 0 1) with hv
  set f : ℝ → ℂ := fun t => G (t • v) - 4 * I * m * μ * t with hf
  -- `f` is differentiable at `0` with derivative `L v - 4 i m μ`.
  have hfd : HasDerivAt f (L v - 4 * I * m * μ) 0 := by
    have hGd : HasFDerivAt G L ((0 : ℝ) • v) := by
      rw [zero_smul]
      exact hM.hasFDerivAt
    have hpath : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have h1 : HasDerivAt (G ∘ fun t : ℝ => t • v) (L v) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := G) (0 : ℝ) hGd hpath
    have h2 : HasDerivAt (fun t : ℝ => 4 * I * m * μ * (t : ℂ)) (4 * I * m * μ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (4 * I * m * μ)
    exact h1.sub h2
  -- The response definition, read along the Breit line.
  have hresp : ∀ η > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ‖f t‖ ≤ η * t := by
    intro η hη
    obtain ⟨δ, hδ, h⟩ := hμ (η / 2) (half_pos hη)
    refine ⟨δ / 2, half_pos hδ, fun t ht htδ => ?_⟩
    have e1 : ∀ k : Fin 3 → ℝ, oneParticleMomentum m k 1 = k 0 := fun k => rfl
    have e2 : ∀ k : Fin 3 → ℝ, oneParticleMomentum m k 2 = k 1 := fun k => rfl
    have e3 : ∀ k : Fin 3 → ℝ, oneParticleMomentum m k 3 = k 2 := fun k => rfl
    have hb := h (2 * t) (oneParticleMomentum m (t • v).2) (oneParticleMomentum m (t • v).1)
      (dot_oneParticleMomentum m _) (dot_oneParticleMomentum m _)
      (oneParticleMomentum_pos hm _) (oneParticleMomentum_pos hm _)
      (by linarith) (by linarith)
      (by rw [e1]; simp [hv]) (by rw [e1]; simp [hv]) (by rw [e2]; simp [hv])
      (by rw [e2]; simp [hv]) (by rw [e3]; simp [hv]) (by rw [e3]; simp [hv])
    calc ‖f t‖ = ‖packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ (t • v).2 (t • v).1
          - 2 * I * m * μ * ((2 * t : ℝ) : ℂ)‖ := by
          simp only [hf, hG]
          congr 2
          push_cast
          ring
      _ ≤ η / 2 * (2 * t) := hb
      _ = η * t := by ring
  -- Hence `f(t) → 0` as `t → 0⁺`, so `f 0 = 0`.
  have hf0 : f 0 = 0 := by
    have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, h⟩ := hresp 1 one_pos
      refine ⟨min δ ε, lt_min hδ hε, fun {t} ht hdist => ?_⟩
      have ht0 : 0 < t := ht
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at hdist
      rw [dist_zero_right]
      calc ‖f t‖ ≤ 1 * t := h t ht0 (lt_of_lt_of_le hdist (min_le_left _ _))
        _ < ε := by linarith [min_le_right δ ε]
    exact tendsto_nhds_unique (hfd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
  -- And the slope `f(t)/t → 0`, so the derivative vanishes.
  have hLv : L v - 4 * I * m * μ = 0 := by
    have hslope : Tendsto (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0)) (𝓝[>] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, h⟩ := hresp (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun {t} ht hdist => ?_⟩
      have ht0 : 0 < t := ht
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at hdist
      rw [dist_zero_right, zero_add, hf0, sub_zero, norm_smul, norm_inv, Real.norm_of_nonneg ht0.le]
      calc t⁻¹ * ‖f t‖ ≤ t⁻¹ * (ε / 2 * t) :=
            mul_le_mul_of_nonneg_left (h t ht0 hdist) (inv_nonneg.2 ht0.le)
        _ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
    exact tendsto_nhds_unique hfd.tendsto_slope_zero_right hslope
  have hvsplit : v = -((Pi.single 0 1 : Fin 3 → ℝ), (0 : Fin 3 → ℝ)) +
      ((0 : Fin 3 → ℝ), (Pi.single 0 1 : Fin 3 → ℝ)) := by
    simp [hv]
  rw [hvsplit, map_add, map_neg] at hLv
  linear_combination (-1 : ℂ) * hLv

/-! ### Combination -/

/-- The integrand `(2π)³ (i/2) w(P)² D` of the moment formula equals the packet weight
`w(P)² (2π)³ 2ω_P` times `g = i D / (4 ω_P)`. -/
theorem packetMoment_integrand_eq {m : ℝ} (hm : 0 < m) (φ : ℝ → ℝ) (lam : ℝ)
    (P : Fin 3 → ℝ) (D : ℂ) :
    ((2 * Real.pi) ^ 3 : ℂ) * (I / 2) * (((packetWeight m φ lam P ^ 2 : ℝ) : ℂ) * D) =
      ((packetWeight m φ lam P ^ 2 *
          ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m P 0)) : ℝ) : ℂ)
        * (I * D / (4 * oneParticleMomentum m P 0)) := by
  have hω : (oneParticleMomentum m P 0 : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (oneParticleMomentum_pos hm P).ne'
  push_cast
  field_simp
  ring

/-- At rest `ω₀ = m`, so the Breit value `D = -4 i m μ` gives `i D / (4 ω₀) = μ`. -/
theorem I_mul_div_four_oneParticleMomentum_zero {m : ℝ} (hm : 0 < m) (μ : ℝ) :
    I * (-4 * I * m * μ) / (4 * oneParticleMomentum m 0 0) = μ := by
  have hω : oneParticleMomentum m 0 0 = m := by
    simp [oneParticleMomentum, Real.sqrt_sq hm.le]
  have hm' : (m : ℂ) ≠ 0 := ofReal_ne_zero.2 hm.ne'
  rw [hω]
  field_simp
  rw [I_sq]
  ring

/-- **The sharp-packet limit of the moment formula.** Assume that the packet weight is
differentiable and that `M̃(k, k') = M(k', k)` is `C¹`. If `μ` is a response magnetic moment,
then `(2π)³ (i/2) ∫ (∂_{k_1} - ∂_{k'_1}) F (P, P) d³P / ⟨e|e⟩ → μ` as `λ → 0⁺`. -/
theorem tendsto_integral_fderiv_packetAmplitude_div_packetNormSq (e Z₁ m mγ Λ : ℝ)
    (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0)
    (hw : ∀ lam, 0 < lam → Differentiable ℝ (packetWeight m φ lam))
    (hM : ContDiff ℝ 1 fun kk : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1)
    {μ : ℝ} (hμ : IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ) :
    Tendsto (fun lam : ℝ =>
      ((2 * Real.pi) ^ 3 : ℂ) * (I / 2) *
        (∫ P : Fin 3 → ℝ,
          (fderiv ℝ (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) (P, P)
              (Pi.single 0 1, 0)
            - fderiv ℝ (Function.uncurry (packetAmplitude e Z₁ m mγ Λ hm hmγ hΛ φ lam)) (P, P)
              (0, Pi.single 0 1)))
        / (packetNormSq m φ lam : ℂ)) (𝓝[>] 0) (𝓝 (μ : ℂ)) := by
  set G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℂ := fun kk =>
    packetMatrixElement e Z₁ m mγ Λ hm hmγ hΛ kk.2 kk.1 with hG
  set D : (Fin 3 → ℝ) → ℂ := fun P =>
    fderiv ℝ G (P, P) (Pi.single 0 1, 0) - fderiv ℝ G (P, P) (0, Pi.single 0 1) with hD
  set g : (Fin 3 → ℝ) → ℂ := fun P => I * D P / (4 * oneParticleMomentum m P 0) with hg
  have hGd : Differentiable ℝ G := hM.differentiable one_ne_zero
  have hDc : Continuous D := by
    have h : Continuous fun P : Fin 3 → ℝ => fderiv ℝ G (P, P) :=
      (hM.continuous_fderiv one_ne_zero).comp (continuous_id.prodMk continuous_id)
    exact (h.clm_apply continuous_const).sub (h.clm_apply continuous_const)
  have hgc : Continuous g := by
    refine Continuous.div (continuous_const.mul hDc) ?_ fun P => ?_
    · exact continuous_const.mul
        (continuous_ofReal.comp (continuous_oneParticleMomentum_zero m))
    · exact mul_ne_zero (by norm_num) (ofReal_ne_zero.2 (oneParticleMomentum_pos hm P).ne')
  have hg0 : g 0 = μ := by
    simp only [hg, hD, hG]
    rw [fderiv_packetMatrixElement_breit e Z₁ m mγ Λ hm hmγ hΛ (hGd _) hμ]
    exact I_mul_div_four_oneParticleMomentum_zero hm μ
  rw [← hg0]
  refine (tendsto_packetAverage hm hφ hφc hφ0 hgc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam (hlam : 0 < lam)
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext P
  rw [fderiv_packetAmplitude_diag_sub e Z₁ m mγ Λ hm hmγ hΛ φ lam P 0 (hw lam hlam P) (hGd _),
    packetMoment_integrand_eq hm]

end QED.OneLoop

end
