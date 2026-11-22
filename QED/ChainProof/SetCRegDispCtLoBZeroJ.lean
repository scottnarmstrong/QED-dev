/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBPow
public import QED.ChainProof.SetCRegDispCtLoBMatch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The power-weighted mass part at zero momentum transfer

Helper level for `QED.ChainProof.SetCRegDisp.CBLoBEq` (set (c), layer 5). The `K^j`-weighted
version of `QED.ChainProof.CtLoB.integral_comb_zero_deriv`:

* **`integral_combJ_zero_deriv`**: for `j ≤ k`, at `s = 0`,
  `∫ (undKernJ j - 2m² dblKernJ j) = ∫₀¹ 6 y (K^(j+1) g)'(K) dy`, `K = y² m²/(1-y)`,
  `g = ∏_i (K + M_i²)⁻¹`;
* `tendsto_integral_undKernJ`, `tendsto_integral_dblKernJ`: the kernel integrals are continuous
  in `s = q²` at `s = 0` from above (dominated convergence);
* **`vpInsertW_eq_comb`**: `K R(K) = (b-a)² K³ g(K)` with the five masses `msW a b c`, so
  `vpInsertW c a b = (b-a)²/6 ∫ (undKernJ 2 - 2 dblKernJ 2)` (`m = 1`, `s = 0`).

So the Pauli value of the merged insertion acts on any photon function `G` built from the
weights `K^j g` by `G ↦ ∫₀¹ 6 y (K G)'(K) dy`, the shape of `QED.ChainProof.SetCRegDisp.vpInsertW`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ChainProof.CtLoB

open QED.Integration QED.TwoLoop.VPUnitNested QED.OneLoop QED.OneLoop.VertexLimit

theorem kC_zero_eq (m : ℝ) {z : ℝ × ℝ} (hy : z.2 ≠ 1) : kC m 0 z = (1 - z.2) * radKY m z.2 := by
  have h : 1 - z.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  unfold kC radKY
  field_simp
  ring

theorem hasDerivAt_pow_mul_phf (j : ℕ) {n : ℕ} (Ms : Fin n → ℝ) {K : ℝ}
    (hK : ∀ i, K + Ms i ^ 2 ≠ 0) :
    HasDerivAt (fun K => K ^ (j + 1) * phf Ms K)
      ((j + 1) * K ^ j * phf Ms K - K ^ (j + 1) * phf Ms K * ∑ i, (K + Ms i ^ 2)⁻¹) K := by
  convert (hasDerivAt_pow (j + 1) K).mul (hasDerivAt_phf Ms hK) using 1
  push_cast
  ring

/-- The inner (`x`) integral of the `K^j`-weighted combination at `s = 0`, for `0 < y < 1`. -/
theorem inner_combJ_zero {m : ℝ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, 0 < Ms i)
    (d : Fin 2) {j : ℕ} (hj : j ≤ k) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioc (0 : ℝ) 1,
        (undKernJ m 0 j Ms (x, y) - 2 * m ^ 2 * dblKernJ m 0 j Ms d (x, y)) =
      6 * y * ((j + 1) * radKY m y ^ j * phf Ms (radKY m y) -
        radKY m y ^ (j + 1) * phf Ms (radKY m y) * ∑ i, (radKY m y + Ms i ^ 2)⁻¹) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy1' : y ≠ 1 := by linarith
  have h1 : (1 - y) ≠ 0 := by linarith
  have hK : 0 ≤ radKY m y := radKY_nonneg m hy1.le
  set K := radKY m y with hKdef
  have hP : ∀ i, K + Ms i ^ 2 ≠ 0 := fun i =>
    (by have := hMs i; positivity : 0 < K + Ms i ^ 2).ne'
  set P := ∏ i, (K + Ms i ^ 2) with hPdef
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hP i
  set S := ∑ i, (K + Ms i ^ 2)⁻¹ with hSdef
  have hD : ∀ x : ℝ, ∏ i, kDen m (Ms i) 0 (x, y) = (1 - y) ^ (k + 2) * P := by
    intro x
    rw [Finset.prod_congr rfl fun i _ => kDen_zero_eq m (Ms i) (z := (x, y)) hy1',
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hS : ∀ x : ℝ, ∑ i, (kDen m (Ms i) 0 (x, y))⁻¹ = (1 - y)⁻¹ * S := by
    intro x
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kDen_zero_eq m (Ms i) (z := (x, y)) hy1', mul_inv]
  have hC : ∀ x : ℝ, kC m 0 (x, y) = (1 - y) * K := fun x => kC_zero_eq m (z := (x, y)) hy1'
  have hphf : phf Ms K = P⁻¹ := by
    rw [phf, hPdef, Finset.prod_inv_distrib]
  have hm2 : m ^ 2 = (1 - y) * K / y ^ 2 := by
    rw [hKdef, radKY]
    field_simp
  have hpt : ∀ x : ℝ, undKernJ m 0 j Ms (x, y) - 2 * m ^ 2 * dblKernJ m 0 j Ms d (x, y) =
      6 * y * K ^ j * P⁻¹ -
        dblLineWt d x * (2 * (6 * y * K * (K ^ j * S - j * K ^ (j - 1)) * P⁻¹)) := by
    intro x
    unfold undKernJ dblKernJ dblKernA dblKernB
    rw [hD x, hS x, hC x, hm2]
    obtain ⟨n, hn⟩ : ∃ n, k + 2 = n + j := ⟨k + 2 - j, by omega⟩
    rw [hn, Nat.add_sub_cancel, pow_add, mul_pow]
    cases j with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, sub_zero, mul_one]
      field_simp
      ring
    | succ j =>
      simp only [Nat.add_sub_cancel, mul_pow, pow_succ]
      push_cast
      field_simp
  simp_rw [hpt]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((by unfold dblLineWt; split_ifs <;> fun_prop : Continuous (dblLineWt d)).intervalIntegrable
        _ _ |>.mul_const _),
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_of_le zero_le_one, integral_dblLineWt, hphf]
  cases j with
  | zero => simp; ring
  | succ j => simp; ring

/-- **The `K^j`-weighted combination at zero momentum transfer**, `j ≤ k`. -/
theorem integral_combJ_zero {m : ℝ} (hm : 0 < m) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, 0 < Ms i) (d : Fin 2) {j : ℕ} (hj : j ≤ k) :
    ∫ z, (undKernJ m 0 j Ms z - 2 * m ^ 2 * dblKernJ m 0 j Ms d z) ∂feynmanMeasure =
      ∫ y in (0 : ℝ)..1, 6 * y * ((j + 1) * radKY m y ^ j * phf Ms (radKY m y) -
        radKY m y ^ (j + 1) * phf Ms (radKY m y) * ∑ i, (radKY m y + Ms i ^ 2)⁻¹) := by
  obtain ⟨M₀, hM₀, hle⟩ : ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ i, M₀ ≤ Ms i :=
    ⟨Finset.univ.inf' Finset.univ_nonempty Ms,
      (Finset.lt_inf'_iff _).2 fun i _ => hMs i, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  have hint : Integrable (fun z => undKernJ m 0 j Ms z - 2 * m ^ 2 * dblKernJ m 0 j Ms d z)
      feynmanMeasure :=
    (integrable_undKernJ hm le_rfl hM₀ (by omega) hle).sub
      ((integrable_dblKernJ hm le_rfl hM₀ (by omega) hle d).const_mul _)
  rw [feynmanMeasure] at hint ⊢
  rw [integral_prod_symm _ hint, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun y hy => inner_combJ_zero hMs d hj hy

/-- **The `K^j`-weighted combination at zero transfer as a derivative**:
`∫₀¹ 6 y (K^(j+1) g)'(K) dy`. -/
theorem integral_combJ_zero_deriv {m : ℝ} (hm : 0 < m) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, 0 < Ms i) (d : Fin 2) {j : ℕ} (hj : j ≤ k) :
    ∫ z, (undKernJ m 0 j Ms z - 2 * m ^ 2 * dblKernJ m 0 j Ms d z) ∂feynmanMeasure =
      ∫ y in (0 : ℝ)..1, 6 * y * deriv (fun K => K ^ (j + 1) * phf Ms K) (radKY m y) := by
  rw [integral_combJ_zero hm hMs d hj]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le zero_le_one] at hy
  have hK : ∀ i, radKY m y + Ms i ^ 2 ≠ 0 := fun i =>
    (add_pos_of_nonneg_of_pos (radKY_nonneg m hy.2) (pow_pos (hMs i) 2)).ne'
  rw [(hasDerivAt_pow_mul_phf j Ms hK).deriv]

/-! ### Continuity in the momentum transfer -/

theorem continuousAt_kC_s (m : ℝ) (z : ℝ × ℝ) (s : ℝ) : ContinuousAt (fun s => kC m s z) s := by
  unfold kC
  fun_prop

theorem tendsto_integral_undKernJ {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {k j : ℕ}
    (hj : j ≤ k + 2) {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) :
    Filter.Tendsto (fun s => ∫ z, undKernJ m s j Ms z ∂feynmanMeasure) (nhdsWithin 0 (Ici 0))
      (nhds (∫ z, undKernJ m 0 j Ms z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 6 / min (M₀ ^ 2) 1 ^ (k + 2))
    (Filter.Eventually.of_forall fun s => (measurable_undKernJ m s j Ms).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs]
    exact abs_undKernJ_le hm hs hM₀ hMs (Ioc_prod_subset hz) hj
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDz : ∀ i, kDen m (Ms i) 0 z ≠ 0 := fun i => kDen_ne_zero_of_le hm le_rfl hM₀ (hMs i) hz
    have hc : ContinuousAt (fun s => undKernJ m s j Ms z) 0 := by
      unfold undKernJ
      exact ContinuousAt.div (((continuousAt_const.mul continuousAt_const).mul
        ((continuousAt_kC_s m z 0).pow j)).mul continuousAt_const)
        (tendsto_finsetProd _ fun i _ => continuousAt_kDen_s m (Ms i) z 0)
        (Finset.prod_ne_zero_iff.2 fun i _ => hDz i)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_integral_dblKernJ {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {k j : ℕ}
    (hj : j ≤ k + 2) {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (d : Fin 2) :
    Filter.Tendsto (fun s => ∫ z, dblKernJ m s j Ms d z ∂feynmanMeasure) (nhdsWithin 0 (Ici 0))
      (nhds (∫ z, dblKernJ m 0 j Ms d z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => 6 * (k + 2) / (min (M₀ ^ 2) 1 ^ (k + 3) * (3 / 4 * min (1 ^ 2) (m ^ 2))) +
      6 * j / (min (M₀ ^ 2) 1 ^ (k + 2) * (3 / 4 * min (1 ^ 2) (m ^ 2))))
    (Filter.Eventually.of_forall fun s =>
      (measurable_dblKernJ m s j Ms d).aestronglyMeasurable) ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans
      (add_le_add (abs_dblKernA_le hm hs hM₀ hMs (Ioc_prod_subset hz) hj d)
        (abs_dblKernB_le hm hs hM₀ hMs (Ioc_prod_subset hz) hj d))
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDz : ∀ i, kDen m (Ms i) 0 z ≠ 0 := fun i => kDen_ne_zero_of_le hm le_rfl hM₀ (hMs i) hz
    have hP : ContinuousAt (fun s => ∏ i, kDen m (Ms i) s z) 0 :=
      tendsto_finsetProd _ fun i _ => continuousAt_kDen_s m (Ms i) z 0
    have hP0 : ∏ i, kDen m (Ms i) 0 z ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hDz i
    have hc : ContinuousAt (fun s => dblKernJ m s j Ms d z) 0 := by
      unfold dblKernJ dblKernA dblKernB
      refine ContinuousAt.sub (ContinuousAt.div (ContinuousAt.mul
        (continuousAt_const.mul ((continuousAt_kC_s m z 0).pow j)) ?_) hP hP0)
        (ContinuousAt.div (continuousAt_const.mul
          (continuousAt_const.mul ((continuousAt_kC_s m z 0).pow (j - 1)))) hP hP0)
      exact tendsto_finsetSum _ fun i _ =>
        ContinuousAt.inv₀ (continuousAt_kDen_s m (Ms i) z 0) (hDz i)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-! ### The target kernel as a `j = 2` combination -/

/-- The five photon masses `(√a, √b, √a, √b, √c)` of `K R(K) = (b-a)² K³ g(K)`. -/
noncomputable def msW (a b c : ℝ) : Fin 5 → ℝ :=
  ![Real.sqrt a, Real.sqrt b, Real.sqrt a, Real.sqrt b, Real.sqrt c]

theorem wKerK_eq_phf {a b c K : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 ≤ K) :
    QED.ChainProof.SetCRegDisp.wKerK c a b K = (b - a) ^ 2 *
      (3 * K ^ 2 * phf (msW a b c) K -
        K ^ 3 * phf (msW a b c) K * ∑ i, (K + msW a b c i ^ 2)⁻¹) := by
  have h1 : K + a ≠ 0 := by positivity
  have h2 : K + b ≠ 0 := by positivity
  have h3 : K + c ≠ 0 := by positivity
  simp only [phf, msW, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_univ_zero,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Real.sq_sqrt ha.le,
    Real.sq_sqrt hb.le, Real.sq_sqrt hc.le]
  unfold QED.ChainProof.SetCRegDisp.wKerK
  field_simp
  ring

/-- **The target kernel from the Pauli values**: with `m = 1` and the five masses `msW a b c`,
`vpInsertW c a b = (b-a)²/6 ∫ (undKernJ 2 - 2 dblKernJ 2)` at zero momentum transfer. -/
theorem vpInsertW_eq_comb {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d : Fin 2) :
    QED.ChainProof.SetCRegDisp.vpInsertW c a b = (b - a) ^ 2 / 6 *
      ∫ z, (undKernJ 1 0 2 (msW a b c) z - 2 * 1 ^ 2 * dblKernJ 1 0 2 (msW a b c) d z)
        ∂feynmanMeasure := by
  have hpos : ∀ i, 0 < msW a b c i := by
    intro i
    fin_cases i <;> simp [msW, Real.sqrt_pos, ha, hb, hc]
  rw [integral_combJ_zero (k := 3) one_pos hpos d (by norm_num),
    ← intervalIntegral.integral_const_mul]
  unfold QED.ChainProof.SetCRegDisp.vpInsertW QED.ChainProof.SetCRegDisp.wKer
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hK : 0 ≤ x ^ 2 / (1 - x) := div_nonneg (by positivity) (by linarith [hx.2])
  have hr : radKY 1 x = x ^ 2 / (1 - x) := by simp [radKY]
  simp only [hr]
  rw [wKerK_eq_phf ha hb hc hK]
  push_cast
  ring

end QED.ChainProof.CtLoB

end
