/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import QED.Integration.TwoLoopEnergyIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The six-dimensional spatial integral

After the Feynman parametrization and the two loop-energy integrals, the two-loop spatial
integral has the form `∫_{ℝ⁶} (vᵀ A v + w)^{-k} d⁶v`, with `A` the positive definite `2 × 2`
matrix `(U_{st})` acting componentwise on `v = (v₁, v₂) ∈ (ℝ³)²` and `Im w < 0`
(`docs/TWO-LOOP-DERIVATION.md`, section 4.4, obligation O2-10). For integer `k ≥ 4`,
`∫_{ℝ⁶} (vᵀ A v + w)^{-k} d⁶v = π³ Γ(k-3)/Γ(k) (det A)^{-3/2} w^{3-k}`,
with `Γ(k-3)/Γ(k) = 1/((k-1)(k-2)(k-3))`. The exponents are integers, so there is no branch
choice; the formula holds for every `w` off the closed negative real axis
(`w ∈ Complex.slitPlane`), which contains both `Im w < 0` and `w > 0`.

## Main statements

* `QED.Integration.Spatial.exists_lower_bound_ofReal_add`: `‖s + w‖ ≥ c (1 + s)` for `s ≥ 0`.
* `QED.Integration.Spatial.integral_Ioi_pow_five_mul_inv_sq_add_pow`: the radial integral
  `∫₀^∞ r⁵ (r² + w)^{-k} dr = w^{3-k} / ((k-1)(k-2)(k-3))`.
* `QED.Integration.Spatial.integral_euclidean_inv_norm_sq_add_pow`: the case `A = 1` on the
  Euclidean space `ℝ^{Fin 3 ⊕ Fin 3}`, by `integral_fun_norm_addHaar` and the volume `π³/3!` of
  the unit ball of `ℝ⁶`.
* `QED.Integration.Spatial.quadForm`: `vᵀ A v = ∑_c (v_{·c})ᵀ A v_{·c}` on `Fin L → Fin 3 → ℝ`,
  with `quadForm_eq_sum : vᵀ A v = ∑_{s,t} A_{st} (v_s · v_t)`.
* `QED.Integration.Spatial.integral_quadForm_eq` and `integrable_quadForm_iff`: for any
  `h : ℝ → ℂ`, `∫_{(ℝ³)²} h(vᵀ A v) dv = (det A)^{-3/2} ∫_{ℝ⁶} h(‖x‖²) dx` (and the same for
  integrability), by the linear change of variables with the Cholesky factor of `A` acting
  componentwise (`blockCholesky`, of determinant `(det A)^{3/2}`).
* `QED.Integration.Spatial.integrable_inv_quadForm_add_pow` and
  `QED.Integration.Spatial.integral_inv_quadForm_add_pow`: integrability and the formula
  `π³ / ((k-1)(k-2)(k-3)) · (det A)^{-3/2} · w^{3-k}`; `integral_inv_quadForm_add_pow_Gamma` is
  the Gamma-function form and `integral_inv_quadForm_add_pow_of_im_neg` the case `Im w < 0`.

The integrals are Bochner integrals for Lebesgue measure (`volume`) on `Fin 2 → Fin 3 → ℝ`,
the spatial part of the measure the joint energy-first integral uses for `L = 2`.
-/

public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.Integration.Spatial

variable {w : ℂ}

/-! ### The radial integral -/

/-- For `w` off the closed negative real axis, `‖s + w‖ ≥ c (1 + s)` uniformly for real
`s ≥ 0`. -/
theorem exists_lower_bound_ofReal_add (hw : w ∈ slitPlane) :
    ∃ c > 0, ∀ s : ℝ, 0 ≤ s → c * (1 + s) ≤ ‖(s : ℂ) + w‖ := by
  rcases mem_slitPlane_iff.mp hw with hre | him
  · refine ⟨min 1 w.re, lt_min one_pos hre, fun s hs => ?_⟩
    have h := Complex.re_le_norm ((s : ℂ) + w)
    simp only [add_re, ofReal_re] at h
    nlinarith [min_le_left 1 w.re, min_le_right 1 w.re]
  · rcases him.lt_or_gt with hneg | hpos
    · obtain ⟨c, hc, h⟩ :=
        QED.Integration.TwoLoop.exists_lower_bound_neg_add (w := -(starRingEnd ℂ w))
          (by simpa using hneg)
      refine ⟨c, hc, fun s hs => (h s hs).trans_eq ?_⟩
      calc ‖-(s : ℂ) + -(starRingEnd ℂ w)‖ = ‖starRingEnd ℂ ((s : ℂ) + w)‖ := by
            rw [← norm_neg]
            congr 1
            simp [add_comm]
        _ = ‖(s : ℂ) + w‖ := Complex.norm_conj _
    · obtain ⟨c, hc, h⟩ :=
        QED.Integration.TwoLoop.exists_lower_bound_neg_add (w := -w) (by simpa using hpos)
      refine ⟨c, hc, fun s hs => (h s hs).trans_eq ?_⟩
      rw [← norm_neg]
      congr 1
      ring

/-- `s + w ≠ 0` for real `s ≥ 0` when `w ∈ slitPlane`. -/
theorem ofReal_add_ne_zero (hw : w ∈ slitPlane) {s : ℝ} (hs : 0 ≤ s) : (s : ℂ) + w ≠ 0 := by
  obtain ⟨c, hc, h⟩ := exists_lower_bound_ofReal_add hw
  intro h0
  have := h s hs
  rw [h0, norm_zero] at this
  nlinarith

/-- The radial integrand `r⁵ (r² + w)^{-k}` is integrable on `(0, ∞)` for `k ≥ 4`. -/
theorem integrableOn_pow_five_mul_inv_sq_add_pow (hw : w ∈ slitPlane) {k : ℕ} (hk : 4 ≤ k) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ 5 * ((((r ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹) (Ioi 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  obtain ⟨c, hc, hbd⟩ := exists_lower_bound_ofReal_add hw
  refine ((integrable_inv_one_add_sq.const_mul (c ^ (j + 4))⁻¹).integrableOn).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop) fun r _ => ?_)
    exact pow_ne_zero _ (ofReal_add_ne_zero hw (sq_nonneg r))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 < r := hr
    have h1 : 0 < 1 + r ^ 2 := by positivity
    rw [norm_mul, norm_inv, norm_pow, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hD := hbd (r ^ 2) (sq_nonneg r)
    have key : r ^ 5 ≤ (1 + r ^ 2) ^ (j + 3) := by
      calc r ^ 5 ≤ (1 + r ^ 2) ^ 3 := by
            nlinarith [mul_nonneg (pow_nonneg hr0.le 4) (sq_nonneg (r - 1)), pow_nonneg hr0.le 4,
              pow_nonneg hr0.le 2, pow_nonneg hr0.le 6]
        _ ≤ (1 + r ^ 2) ^ (j + 3) := pow_le_pow_right₀ (by nlinarith) (by omega)
    calc r ^ 5 * (‖((r ^ 2 : ℝ) : ℂ) + w‖ ^ (j + 4))⁻¹
        ≤ r ^ 5 * ((c * (1 + r ^ 2)) ^ (j + 4))⁻¹ := by
          gcongr
      _ = (c ^ (j + 4))⁻¹ * (r ^ 5 / (1 + r ^ 2) ^ (j + 4)) := by
          rw [mul_pow]; field_simp
      _ ≤ (c ^ (j + 4))⁻¹ * ((1 + r ^ 2) ^ (j + 3) / (1 + r ^ 2) ^ (j + 4)) := by
          gcongr
      _ = (c ^ (j + 4))⁻¹ * (1 + r ^ 2)⁻¹ := by
          congr 1
          field_simp
          ring

/-- **The radial integral.** For `w ∈ slitPlane` and `k ≥ 4`,
`∫₀^∞ r⁵ (r² + w)^{-k} dr = w^{3-k} / ((k-1)(k-2)(k-3))`. -/
theorem integral_Ioi_pow_five_mul_inv_sq_add_pow (hw : w ∈ slitPlane) {k : ℕ} (hk : 4 ≤ k) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 5 * ((((r ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ * (w ^ (k - 3))⁻¹ := by
  have hint := integrableOn_pow_five_mul_inv_sq_add_pow hw hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  have hsub : j + 4 - 3 = j + 1 := by omega
  rw [hsub]
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  set D : ℝ → ℂ := fun r => ((r ^ 2 : ℝ) : ℂ) + w with hD
  have hDne : ∀ r, D r ≠ 0 := fun r => ofReal_add_ne_zero hw (sq_nonneg r)
  have hj1 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hj2 : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (j + 1)
  have hj3 : (j : ℂ) + 3 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (j + 2)
  set G : ℝ → ℂ := fun r => (1 / 2) * (-(D r ^ (j + 1))⁻¹ / ((j : ℂ) + 1) +
    2 * w * (D r ^ (j + 2))⁻¹ / ((j : ℂ) + 2) - w ^ 2 * (D r ^ (j + 3))⁻¹ / ((j : ℂ) + 3))
    with hG
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt G ((r : ℂ) ^ 5 * (D r ^ (j + 4))⁻¹) r := by
    intro r _
    have h1 : HasDerivAt D (2 * (r : ℂ)) r := by
      have := ((hasDerivAt_pow 2 r).ofReal_comp).add_const w
      convert this using 1
      push_cast
      ring
    have hr := hDne r
    have hinv : ∀ n : ℕ, HasDerivAt (fun x => (D x ^ (n + 1))⁻¹)
        (-(((n : ℂ) + 1) * D r ^ n * (2 * (r : ℂ))) / (D r ^ (n + 1)) ^ 2) r := by
      intro n
      have := (h1.fun_pow (n + 1)).fun_inv (pow_ne_zero _ hr)
      convert this using 2
      simp
    have h2 := ((((hinv j).neg.div_const ((j : ℂ) + 1)).add
      (((hinv (j + 1)).const_mul (2 * w)).div_const ((j : ℂ) + 2))).sub
      (((hinv (j + 2)).const_mul (w ^ 2)).div_const ((j : ℂ) + 3))).const_mul (1 / 2 : ℂ)
    convert h2 using 1
    have hrD : (r : ℂ) ^ 2 = D r - w := by simp [hD]
    have h5 : (r : ℂ) ^ 5 = r * (D r - w) ^ 2 := by rw [← hrD]; ring
    rw [h5]
    push_cast
    field_simp
    ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    obtain ⟨c, hc, hbd⟩ := exists_lower_bound_ofReal_add hw
    have hnorm : Tendsto (fun r => ‖D r‖) atTop atTop := by
      refine tendsto_atTop_mono' _ ?_ ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop hc)
      filter_upwards with r
      have := hbd (r ^ 2) (sq_nonneg r)
      nlinarith
    have h0 : ∀ n : ℕ, Tendsto (fun r => (D r ^ (n + 1))⁻¹) atTop (𝓝 0) := by
      intro n
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp hnorm).inv_tendsto_atTop
      refine this.congr fun r => ?_
      simp only [Function.comp_apply, Pi.inv_apply, norm_inv, norm_pow]
    have := ((((h0 j).neg.div_const ((j : ℂ) + 1)).add
      (((h0 (j + 1)).const_mul (2 * w)).div_const ((j : ℂ) + 2))).sub
      (((h0 (j + 2)).const_mul (w ^ 2)).div_const ((j : ℂ) + 3))).const_mul (1 / 2 : ℂ)
    simpa [hG, neg_div, mul_div_assoc] using this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [hG, hD, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ofReal_zero,
    zero_add]
  have e1 : ((j + 4 : ℕ) : ℂ) - 1 = (j : ℂ) + 3 := by push_cast; ring
  have e2 : ((j + 4 : ℕ) : ℂ) - 2 = (j : ℂ) + 2 := by push_cast; ring
  have e3 : ((j + 4 : ℕ) : ℂ) - 3 = (j : ℂ) + 1 := by push_cast; ring
  rw [e1, e2, e3]
  field_simp
  ring

/-! ### The radial integral in `ℝ⁶` -/

/-- **The case `A = 1`.** On the Euclidean space `ℝ^{Fin 3 ⊕ Fin 3}` (that is, `ℝ⁶`), for
`w ∈ slitPlane` and `k ≥ 4`, `∫ (‖x‖² + w)^{-k} dx = π³ w^{3-k} / ((k-1)(k-2)(k-3))`. -/
theorem integral_euclidean_inv_norm_sq_add_pow (hw : w ∈ slitPlane) {k : ℕ} (hk : 4 ≤ k) :
    ∫ x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3), ((((‖x‖ ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (π : ℂ) ^ 3 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ * (w ^ (k - 3))⁻¹ := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)))
    (fun r : ℝ => ((((r ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹)
  rw [h]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) = 6 := by simp
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3))).real (Metric.ball 0 1) =
      π ^ 3 / 6 := by
    rw [measureReal_def, EuclideanSpace.volume_ball]
    have hG : Real.Gamma ((Fintype.card (Fin 3 ⊕ Fin 3) : ℝ) / 2 + 1) = 6 := by
      rw [show ((Fintype.card (Fin 3 ⊕ Fin 3) : ℝ) / 2 + 1) = ((3 : ℕ) : ℝ) + 1 by simp; norm_num,
        Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    have hs : Real.sqrt π ^ Fintype.card (Fin 3 ⊕ Fin 3) = π ^ 3 := by
      rw [show Fintype.card (Fin 3 ⊕ Fin 3) = 2 * 3 by simp, pow_mul,
        Real.sq_sqrt Real.pi_pos.le]
    rw [hG, hs, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity)]
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) - 1) •
      ((((y ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹ =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ 5 * ((((y ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹ := by
    rw [hdim]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp [Complex.real_smul]
  rw [hrad, integral_Ioi_pow_five_mul_inv_sq_add_pow hw hk, hdim, hball, nsmul_eq_mul,
    Complex.real_smul]
  push_cast
  ring

/-! ### The quadratic form and the change of variables -/

/-- The quadratic form `vᵀ A v = ∑_{s,t} A_{st} (v_s · v_t)` on `(ℝ³)^L`: the matrix `A` acts on
the `Fin L` index, componentwise in the `Fin 3` index. -/
def quadForm {L : ℕ} (A : Matrix (Fin L) (Fin L) ℝ) (v : Fin L → Fin 3 → ℝ) : ℝ :=
  ∑ c : Fin 3, (fun s => v s c) ⬝ᵥ A *ᵥ (fun s => v s c)

theorem quadForm_eq_sum {L : ℕ} (A : Matrix (Fin L) (Fin L) ℝ) (v : Fin L → Fin 3 → ℝ) :
    quadForm A v = ∑ s, ∑ t, A s t * ∑ c, v s c * v t c := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun c _ => by ring

/-- For a positive definite `2 × 2` matrix `A = !![a, b; b, c]`,
`(x, y)ᵀ A (x, y) = (√a x + (b/√a) y)² + (√(det A / a) y)²` (completing the square; the
upper-triangular Cholesky factor). -/
theorem dotProduct_mulVec_vecTwo_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (x y : ℝ) :
    ![x, y] ⬝ᵥ A *ᵥ ![x, y] =
      (Real.sqrt (A 0 0) * x + A 0 1 / Real.sqrt (A 0 0) * y) ^ 2 +
        (Real.sqrt (A.det / A 0 0) * y) ^ 2 := by
  have ha : 0 < A 0 0 := hA.diag_pos
  have hd : 0 < A.det := hA.det_pos
  have hsym : A 1 0 = A 0 1 := by simpa using hA.isHermitian.apply 0 1
  have hsa : Real.sqrt (A 0 0) ^ 2 = A 0 0 := Real.sq_sqrt ha.le
  have hsa0 : Real.sqrt (A 0 0) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsd : Real.sqrt (A.det / A 0 0) ^ 2 = A.det / A 0 0 := Real.sq_sqrt (by positivity)
  simp only [dotProduct, mulVec, Fin.sum_univ_two, cons_val_zero, cons_val_one]
  rw [mul_pow, hsd, det_fin_two, hsym]
  set sa := Real.sqrt (A 0 0)
  rw [← hsa]
  field_simp
  ring

/-- The upper-triangular Cholesky factor `!![√a, b/√a; 0, √(det A / a)]` of a `2 × 2` matrix
`A = !![a, b; b, c]`, acting componentwise on `(ℝ³)²`, written as a block matrix on
`Fin 3 ⊕ Fin 3`. -/
noncomputable def blockCholesky (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks (Real.sqrt (A 0 0) • 1) ((A 0 1 / Real.sqrt (A 0 0)) • 1) 0
    (Real.sqrt (A.det / A 0 0) • 1)

theorem det_blockCholesky {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    (blockCholesky A).det = Real.sqrt A.det ^ 3 := by
  have ha : 0 < A 0 0 := hA.diag_pos
  rw [blockCholesky, det_fromBlocks_zero₂₁, det_smul, det_smul, det_one, Fintype.card_fin,
    mul_one, mul_one, ← mul_pow, ← Real.sqrt_mul ha.le, mul_div_cancel₀ _ ha.ne']

/-- The pair `(v₁, v₂) ∈ (ℝ³)²` with coordinates `u : Fin 3 ⊕ Fin 3 → ℝ`. -/
def pairOfSum (u : Fin 3 ⊕ Fin 3 → ℝ) : Fin 2 → Fin 3 → ℝ :=
  MeasurableEquiv.finTwoArrow.symm (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ) u)

theorem quadForm_pairOfSum {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (u : Fin 3 ⊕ Fin 3 → ℝ) :
    quadForm A (pairOfSum u) = ∑ i, (blockCholesky A *ᵥ u) i ^ 2 := by
  have hcol : ∀ c : Fin 3, (fun s => pairOfSum u s c) = ![u (Sum.inl c), u (Sum.inr c)] := by
    intro c
    funext s
    fin_cases s <;> rfl
  simp only [quadForm, hcol, dotProduct_mulVec_vecTwo_eq hA, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [blockCholesky, fromBlocks_mulVec, smul_mulVec, one_mulVec]

theorem measurePreserving_pairOfSum : MeasurePreserving pairOfSum := by
  exact (MeasurePreserving.symm _ (volume_preserving_finTwoArrow (Fin 3 → ℝ))).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ))

theorem measurableEmbedding_pairOfSum : MeasurableEmbedding pairOfSum :=
  (MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)).measurableEmbedding

/-- Linear change of variables by an invertible matrix. -/
theorem integral_comp_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Matrix ι ι ℝ}
    (hN : N.det ≠ 0) (g : (ι → ℝ) → ℂ) :
    ∫ u, g (N *ᵥ u) = (|N.det|⁻¹ : ℝ) • ∫ u, g u := by
  have h0 : LinearMap.det (Matrix.toLin' N) ≠ 0 := by rwa [LinearMap.det_toLin']
  let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
    ((Matrix.toLin' N).equivOfDetNeZero h0).toContinuousLinearEquiv
  have he : (e : (ι → ℝ) → (ι → ℝ)) = Matrix.toLin' N := rfl
  have hemb : MeasurableEmbedding (e : (ι → ℝ) → (ι → ℝ)) := e.toHomeomorph.measurableEmbedding
  have hmap : Measure.map e volume =
      ENNReal.ofReal |(LinearMap.det (Matrix.toLin' N))⁻¹| • volume := by
    rw [he]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume h0
  have := hemb.integral_map (μ := volume) g
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), LinearMap.det_toLin',
    abs_inv] at this
  rw [this]
  rfl

theorem integrable_comp_mulVec_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Matrix ι ι ℝ}
    (hN : N.det ≠ 0) {g : (ι → ℝ) → ℂ} :
    Integrable (fun u => g (N *ᵥ u)) ↔ Integrable g := by
  have h0 : LinearMap.det (Matrix.toLin' N) ≠ 0 := by rwa [LinearMap.det_toLin']
  let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
    ((Matrix.toLin' N).equivOfDetNeZero h0).toContinuousLinearEquiv
  have he : (e : (ι → ℝ) → (ι → ℝ)) = Matrix.toLin' N := rfl
  have hemb : MeasurableEmbedding (e : (ι → ℝ) → (ι → ℝ)) := e.toHomeomorph.measurableEmbedding
  have hmap : Measure.map e volume =
      ENNReal.ofReal |(LinearMap.det (Matrix.toLin' N))⁻¹| • volume := by
    rw [he]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume h0
  have := hemb.integrable_map_iff (μ := volume) (g := g)
  rw [hmap, integrable_smul_measure (by simpa using h0) ENNReal.ofReal_ne_top] at this
  exact this.symm

/-- Passing from `ι → ℝ` to the Euclidean space `ℝ^ι`. -/
theorem integral_sum_sq_eq_integral_euclidean {ι : Type*} [Fintype ι] (h : ℝ → ℂ) :
    ∫ u : ι → ℝ, h (∑ i, u i ^ 2) = ∫ x : EuclideanSpace ℝ ι, h (‖x‖ ^ 2) := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integral_comp'
    (fun u : ι → ℝ => h (∑ i, u i ^ 2))]
  congr 1
  funext x
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem integrable_sum_sq_iff_integrable_euclidean {ι : Type*} [Fintype ι] {h : ℝ → ℂ} :
    Integrable (fun u : ι → ℝ => h (∑ i, u i ^ 2)) ↔
      Integrable fun x : EuclideanSpace ℝ ι => h (‖x‖ ^ 2) := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- **Reduction to `A = 1`.** For a positive definite real `2 × 2` matrix `A` and any
`h : ℝ → ℂ`, `∫_{(ℝ³)²} h(vᵀ A v) dv = (det A)^{-3/2} ∫_{ℝ⁶} h(‖x‖²) dx`. -/
theorem integral_quadForm_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (h : ℝ → ℂ) :
    ∫ v : Fin 2 → Fin 3 → ℝ, h (quadForm A v) =
      ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * ∫ x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3), h (‖x‖ ^ 2) := by
  have hdet : (blockCholesky A).det ≠ 0 := by
    rw [det_blockCholesky hA]
    exact pow_ne_zero _ (Real.sqrt_pos.mpr hA.det_pos).ne'
  rw [← measurePreserving_pairOfSum.integral_comp measurableEmbedding_pairOfSum]
  simp only [quadForm_pairOfSum hA]
  rw [integral_comp_mulVec hdet (fun u => h (∑ i, u i ^ 2)),
    integral_sum_sq_eq_integral_euclidean, det_blockCholesky hA,
    abs_of_pos (pow_pos (Real.sqrt_pos.mpr hA.det_pos) 3), Complex.real_smul]
  push_cast
  ring

theorem integrable_quadForm_iff {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) {h : ℝ → ℂ} :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => h (quadForm A v)) ↔
      Integrable fun x : EuclideanSpace ℝ (Fin 3 ⊕ Fin 3) => h (‖x‖ ^ 2) := by
  have hdet : (blockCholesky A).det ≠ 0 := by
    rw [det_blockCholesky hA]
    exact pow_ne_zero _ (Real.sqrt_pos.mpr hA.det_pos).ne'
  rw [← measurePreserving_pairOfSum.integrable_comp_emb measurableEmbedding_pairOfSum,
    ← integrable_sum_sq_iff_integrable_euclidean,
    ← integrable_comp_mulVec_iff hdet (g := fun u => h (∑ i, u i ^ 2))]
  refine integrable_congr (Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply, quadForm_pairOfSum hA]

/-! ### The six-dimensional formula -/

/-- **Integrability.** For a positive definite real `2 × 2` matrix `A`, `w ∈ slitPlane` and
`k ≥ 4`, the integrand `(vᵀ A v + w)^{-k}` is integrable on `(ℝ³)²`. -/
theorem integrable_inv_quadForm_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (hw : w ∈ slitPlane) {k : ℕ} (hk : 4 ≤ k) :
    Integrable fun v : Fin 2 → Fin 3 → ℝ => ((((quadForm A v : ℝ) : ℂ) + w) ^ k)⁻¹ := by
  rw [integrable_quadForm_iff hA (h := fun s : ℝ => (((s : ℂ) + w) ^ k)⁻¹)]
  have := (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)))
    (f := fun r : ℝ => ((((r ^ 2 : ℝ) : ℂ) + w) ^ k)⁻¹)).mpr ?_
  · exact this
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) = 6 := by simp
  rw [hdim]
  refine (integrableOn_pow_five_mul_inv_sq_add_pow hw hk).congr_fun (fun y _ => ?_)
    measurableSet_Ioi
  simp [Complex.real_smul]

/-- **The six-dimensional spatial formula** (`docs/TWO-LOOP-DERIVATION.md`, section 4.4;
obligation O2-10). For a positive definite real `2 × 2` matrix `A` acting componentwise on
`(ℝ³)²`, `w` off the closed negative real axis (in particular `Im w < 0`, or `w > 0`) and an
integer `k ≥ 4`,
`∫_{ℝ⁶} (vᵀ A v + w)^{-k} d⁶v = π³ / ((k-1)(k-2)(k-3)) · (det A)^{-3/2} · w^{3-k}`. -/
theorem integral_inv_quadForm_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (hw : w ∈ slitPlane) {k : ℕ} (hk : 4 ≤ k) :
    ∫ v : Fin 2 → Fin 3 → ℝ, ((((quadForm A v : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (π : ℂ) ^ 3 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ *
        ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 3))⁻¹ := by
  rw [integral_quadForm_eq hA (fun s : ℝ => (((s : ℂ) + w) ^ k)⁻¹),
    integral_euclidean_inv_norm_sq_add_pow hw hk]
  ring

/-- `Γ(k-3)/Γ(k) = 1/((k-1)(k-2)(k-3))` for `k ≥ 4`. -/
theorem Gamma_sub_three_div_Gamma {k : ℕ} (hk : 4 ≤ k) :
    Real.Gamma ((k : ℝ) - 3) / Real.Gamma k =
      (((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3))⁻¹ := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have h3 : (k : ℝ) - 3 ≠ 0 := by linarith
  have h2 : (k : ℝ) - 2 ≠ 0 := by linarith
  have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have hG : Real.Gamma k =
      ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3) * Real.Gamma ((k : ℝ) - 3) := by
    rw [show (k : ℝ) = ((k : ℝ) - 1) + 1 by ring, Real.Gamma_add_one h1,
      show (k : ℝ) - 1 = ((k : ℝ) - 2) + 1 by ring, Real.Gamma_add_one h2,
      show (k : ℝ) - 2 = ((k : ℝ) - 3) + 1 by ring, Real.Gamma_add_one h3]
    ring_nf
  have hpos : 0 < Real.Gamma ((k : ℝ) - 3) := Real.Gamma_pos_of_pos (by linarith)
  rw [hG]
  field_simp

/-- The six-dimensional formula in the Gamma-function form of the source:
`∫_{ℝ⁶} (vᵀ A v + w)^{-k} d⁶v = π³ Γ(k-3)/Γ(k) (det A)^{-3/2} w^{3-k}`. -/
theorem integral_inv_quadForm_add_pow_Gamma {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (hw : w ∈ slitPlane) {k : ℕ} (hk : 4 ≤ k) :
    ∫ v : Fin 2 → Fin 3 → ℝ, ((((quadForm A v : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (π : ℂ) ^ 3 * ((Real.Gamma ((k : ℝ) - 3) / Real.Gamma k : ℝ) : ℂ) *
        ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 3))⁻¹ := by
  rw [integral_inv_quadForm_add_pow hA hw hk, Gamma_sub_three_div_Gamma hk]
  push_cast
  ring

/-- The formula for `Im w < 0`, the case produced by the `-iε` prescription. -/
theorem integral_inv_quadForm_add_pow_of_im_neg {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (hw : w.im < 0) {k : ℕ} (hk : 4 ≤ k) :
    ∫ v : Fin 2 → Fin 3 → ℝ, ((((quadForm A v : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (π : ℂ) ^ 3 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ *
        ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 3))⁻¹ :=
  integral_inv_quadForm_add_pow hA (mem_slitPlane_iff.mpr (Or.inr hw.ne)) hk

end QED.Integration.Spatial

end
