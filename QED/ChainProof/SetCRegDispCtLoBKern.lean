/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBPauli
public import QED.ChainProof.HCBB2Value
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The value of the Pauli-projected doubled vertex for any list of photon masses

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan. The doubled-vertex analogue of `QED/ChainProof/HCBB2Value.lean`: for the Pauli-projected
Feynman-gauge chain, the limit `QED.ChainProof.CtLoB.dblProdLimit` of the doubled vertex with
photon denominators of masses `M_0, …, M_{k+1}` is an explicit integral over the Feynman square.
With `Δ_M = kDen m M q² z = (1-y) M² + y² (m² + x(1-x) q²)` the kernel is

`dblKern = 6 x_d y² (x₃ - x₃²) (1-y)^{k+1} (Σ_i Δ_{M_i}⁻¹) / ∏_i Δ_{M_i}`,

i.e. `6 x_d y² (x₃ - x₃²) (1-y)⁻² (-f'(K))` for the photon function `f(K) = ∏_i (K + M_i²)⁻¹`
at `K = Δ/(1-y) - M²`: the doubled line acts as `-∂/∂M²` of every photon factor at once.

* `kDen_ge_min`: `Δ_M ≥ (3/4) min(M₀², m²)` on the square, for `q² ≥ 0` and `M ≥ M₀`;
* `dblKern_drop`: the partial fraction `(M₁² - M₀²) dblKern = dblKern(drop M₁) - dblKern(drop M₀)`;
* `dblVal`: the value; `dblProdLimit_two_eq`: two distinct masses, from
  `QED.ChainProof.CtLoB.dblOneLimit_pauliChain`; `dblProdLimit_inj`: distinct squared masses;
* `tendsto_dblVal_pert`: continuity of the value in the masses;
* **`dblProdLimit_pauliChain_eq`**: `dblProdLimit α (pauliChain e) Ms d = dblVal Ms d` for all
  positive masses, on-shell positive-energy momenta with `q² > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.HCBB2 (pert tendsto_pert eventually_pert_inj dropOne)

/-! ### The kernel -/

/-- The doubled kernel `6 x_d y² (x₃ - x₃²) (1-y)^{k+1} (Σ_i Δ_i⁻¹) / ∏_i Δ_i`. -/
noncomputable def dblKern (m s : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2) (z : ℝ × ℝ) :
    ℝ :=
  6 * dblLineWt d z.1 * z.2 ^ 2 * ((1 - z.2) - (1 - z.2) ^ 2) * (1 - z.2) ^ (k + 1) *
    (∑ i, (kDen m (Ms i) s z)⁻¹) / ∏ i, kDen m (Ms i) s z

theorem kDen_ge_min {m s M₀ M : ℝ} (hs : 0 ≤ s) (hM₀ : 0 ≤ M₀) (hM : M₀ ≤ M) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    3 / 4 * min (M₀ ^ 2) (m ^ 2) ≤ kDen m M s z := by
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hz
  have h1 : (1 - z.2) * M₀ ^ 2 ≤ (1 - z.2) * M ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM₀ hM 2) (by linarith)
  have h2 : z.2 ^ 2 * m ^ 2 ≤ z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s) := by
    have : 0 ≤ z.1 * (1 - z.1) * s := mul_nonneg (mul_nonneg hx0 (by linarith)) hs
    nlinarith [sq_nonneg z.2]
  have hmin1 := min_le_left (M₀ ^ 2) (m ^ 2)
  have hmin2 := min_le_right (M₀ ^ 2) (m ^ 2)
  have h3 : 3 / 4 * min (M₀ ^ 2) (m ^ 2) ≤ (1 - z.2) * M₀ ^ 2 + z.2 ^ 2 * m ^ 2 := by
    have hc : 0 ≤ min (M₀ ^ 2) (m ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hmin1 (by linarith : (0 : ℝ) ≤ 1 - z.2),
      mul_le_mul_of_nonneg_left hmin2 (sq_nonneg z.2), mul_nonneg hc (sq_nonneg (z.2 - 1 / 2))]
  unfold kDen kC
  linarith

/-- **The partial fraction of the kernel.** -/
theorem dblKern_drop (m s : ℝ) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) (d : Fin 2) {z : ℝ × ℝ}
    (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    (Ms 1 ^ 2 - Ms 0 ^ 2) * dblKern m s Ms d z =
      dblKern m s (dropOne Ms) d z - dblKern m s (Fin.tail Ms) d z := by
  set D0 := kDen m (Ms 0) s z
  set D1 := kDen m (Ms 1) s z
  set S := ∑ i : Fin (k + 1), (kDen m (Ms i.succ.succ) s z)⁻¹
  set R := ∏ i : Fin (k + 1), kDen m (Ms i.succ.succ) s z
  set c := 6 * dblLineWt d z.1 * z.2 ^ 2 * ((1 - z.2) - (1 - z.2) ^ 2)
  have h0 : D0 ≠ 0 := hD 0
  have h1 : D1 ≠ 0 := hD 1
  have hR : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD _
  have hS3 : ∑ i, (kDen m (Ms i) s z)⁻¹ = D0⁻¹ + D1⁻¹ + S := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact (add_assoc _ _ _).symm
  have hP3 : ∏ i, kDen m (Ms i) s z = D0 * D1 * R := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    exact (mul_assoc _ _ _).symm
  have hSd : ∑ i, (kDen m (dropOne Ms i) s z)⁻¹ = D0⁻¹ + S := by
    rw [Fin.sum_univ_succ]
    rfl
  have hPd : ∏ i, kDen m (dropOne Ms i) s z = D0 * R := by
    rw [Fin.prod_univ_succ]
    rfl
  have hSt : ∑ i, (kDen m (Fin.tail Ms i) s z)⁻¹ = D1⁻¹ + S := by
    rw [Fin.sum_univ_succ]
    rfl
  have hPt : ∏ i, kDen m (Fin.tail Ms i) s z = D1 * R := by
    rw [Fin.prod_univ_succ]
    rfl
  have hd : (1 - z.2) * (Ms 1 ^ 2 - Ms 0 ^ 2) = D1 - D0 := by
    simp only [D0, D1, kDen]
    ring
  unfold dblKern
  rw [hS3, hP3, hSd, hPd, hSt, hPt, pow_succ (1 - z.2) (k + 1)]
  rw [show (Ms 1 ^ 2 - Ms 0 ^ 2) * (c * ((1 - z.2) ^ (k + 1) * (1 - z.2)) * (D0⁻¹ + D1⁻¹ + S) /
      (D0 * D1 * R)) = c * (1 - z.2) ^ (k + 1) * ((1 - z.2) * (Ms 1 ^ 2 - Ms 0 ^ 2)) *
        (D0⁻¹ + D1⁻¹ + S) / (D0 * D1 * R) by ring, hd]
  field_simp
  ring

theorem measurable_dblKern (m s : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (d : Fin 2) :
    Measurable (dblKern m s Ms d) := by
  unfold dblKern dblLineWt kDen kC
  split_ifs
  all_goals
    refine Measurable.div (Measurable.mul (by fun_prop)
      (Finset.measurable_sum _ fun i _ => (by fun_prop : Measurable _).inv))
      (Finset.measurable_prod _ fun i _ => by fun_prop)

theorem abs_dblKern_le {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k : ℕ}
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (d : Fin 2) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    |dblKern m s Ms d z| ≤ 6 * (k + 2) / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 3) := by
  set c₀ := 3 / 4 * min (M₀ ^ 2) (m ^ 2)
  have hc₀ : 0 < c₀ := by positivity
  have hD : ∀ i, c₀ ≤ kDen m (Ms i) s z := fun i => kDen_ge_min hs hM₀.le (hMs i) hz
  have hDp : ∀ i, 0 < kDen m (Ms i) s z := fun i => hc₀.trans_le (hD i)
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hz
  have hw : 0 ≤ dblLineWt d z.1 ∧ dblLineWt d z.1 ≤ 1 := by
    unfold dblLineWt
    split_ifs <;> constructor <;> linarith
  have hy1' : 0 ≤ 1 - z.2 := by linarith
  set A := 6 * dblLineWt d z.1 * z.2 ^ 2 * ((1 - z.2) - (1 - z.2) ^ 2) * (1 - z.2) ^ (k + 1)
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (1 - z.2) - (1 - z.2) ^ 2 := by nlinarith
    have := hw.1
    positivity
  have hA1 : A ≤ 6 := by
    have h1 : (1 - z.2) - (1 - z.2) ^ 2 ≤ 1 := by nlinarith
    have h2 : (1 - z.2) ^ (k + 1) ≤ 1 := pow_le_one₀ hy1' (by linarith)
    have h3 : z.2 ^ 2 ≤ 1 := by nlinarith
    have h4 : 0 ≤ (1 - z.2) - (1 - z.2) ^ 2 := by nlinarith
    calc A ≤ 6 * 1 * 1 * 1 * 1 := by
          simp only [A]
          gcongr
          · exact hw.2
      _ = 6 := by ring
  have hS0 : 0 ≤ ∑ i, (kDen m (Ms i) s z)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.2 (hDp i)).le
  have hS1 : ∑ i, (kDen m (Ms i) s z)⁻¹ ≤ (k + 2) / c₀ := by
    calc ∑ i, (kDen m (Ms i) s z)⁻¹ ≤ ∑ _i : Fin (k + 2), c₀⁻¹ :=
          Finset.sum_le_sum fun i _ => inv_anti₀ hc₀ (hD i)
      _ = (k + 2) / c₀ := by simp [div_eq_mul_inv]
  have hP : c₀ ^ (k + 2) ≤ ∏ i, kDen m (Ms i) s z := by
    calc c₀ ^ (k + 2) = ∏ _i : Fin (k + 2), c₀ := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc₀.le) fun i _ => hD i
  have hPp : 0 < ∏ i, kDen m (Ms i) s z := (pow_pos hc₀ _).trans_le hP
  unfold dblKern
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hA0 hS0) hPp.le), div_le_div_iff₀ hPp (by positivity)]
  calc A * (∑ i, (kDen m (Ms i) s z)⁻¹) * c₀ ^ (k + 3)
      ≤ 6 * ((k + 2) / c₀) * c₀ ^ (k + 3) := by gcongr
    _ = 6 * (k + 2) * c₀ ^ (k + 2) := by rw [pow_succ]; field_simp
    _ ≤ 6 * (k + 2) * ∏ i, kDen m (Ms i) s z := by gcongr

theorem integrable_dblKern {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k : ℕ}
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (d : Fin 2) :
    Integrable (dblKern m s Ms d) feynmanMeasure := by
  refine Integrable.mono'
    (integrable_const (6 * (k + 2) / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 3)))
    (measurable_dblKern m s Ms d).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs]
  exact abs_dblKern_le hm hs hM₀ hMs d (Ioc_prod_subset hz)

/-! ### The value -/

/-- The value `i (π²/6) κ_e 4 m q² (4m² + q²)² ∫ dblKern`. -/
noncomputable def dblVal (e m : ℝ) (p' p : Fin 4 → ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    (d : Fin 2) : ℂ :=
  I * ((π ^ 2 / 6 : ℝ) : ℂ) * kappa e *
    (4 * (m : ℂ) * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
      (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) *
    ((∫ z, dblKern m (Minkowski.dot (p' - p) (p' - p)) Ms d z ∂feynmanMeasure : ℝ) : ℂ)

theorem dblVal_drop (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ)
    (hpos : ∀ i, 0 < Ms i) (d : Fin 2) :
    ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) * dblVal e m p' p Ms d =
      dblVal e m p' p (dropOne Ms) d - dblVal e m p' p (Fin.tail Ms) d := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hD : ∀ i, M₀ ≤ dropOne Ms i := fun i => by
    cases i using Fin.cases with
    | zero => exact hMs 0
    | succ i => exact hMs _
  have hT : ∀ i, M₀ ≤ Fin.tail Ms i := fun i => hMs _
  have e1 : (Ms 1 ^ 2 - Ms 0 ^ 2) * ∫ z, dblKern m q Ms d z ∂feynmanMeasure =
      (∫ z, dblKern m q (dropOne Ms) d z ∂feynmanMeasure) -
        ∫ z, dblKern m q (Fin.tail Ms) d z ∂feynmanMeasure := by
    rw [← integral_const_mul, ← integral_sub (integrable_dblKern hm hq hM₀ hD d)
      (integrable_dblKern hm hq hM₀ hT d)]
    refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
    exact dblKern_drop m q Ms d fun i =>
      ((by positivity : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2)).trans_le
        (kDen_ge_min hq hM₀.le (hMs i) (Ioc_prod_subset hz))).ne'
  unfold dblVal
  rw [← mul_sub, ← ofReal_sub, ← e1]
  push_cast
  ring

theorem tendsto_dblVal_pert (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hpos : ∀ i, 0 < Ms i) (d : Fin 2) :
    Tendsto (fun δ => dblVal e m p' p (pert Ms δ) d) (𝓝[>] 0) (𝓝 (dblVal e m p' p Ms d)) := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hge : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, M₀ ≤ pert Ms δ i := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
    have : 0 ≤ δ * ((i : ℕ) + 1) := by positivity
    simp only [pert]
    linarith [hMs i]
  have hc₀ : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2) := by positivity
  have hI : Tendsto (fun δ => ∫ z, dblKern m q (pert Ms δ) d z ∂feynmanMeasure) (𝓝[>] 0)
      (𝓝 (∫ z, dblKern m q Ms d z ∂feynmanMeasure)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => 6 * (k + 2) / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 3))
      (Eventually.of_forall fun δ => (measurable_dblKern m q _ d).aestronglyMeasurable) ?_
      (integrable_const _) ?_
    · filter_upwards [hge] with δ hδ
      filter_upwards [ae_feynmanMeasure] with z hz
      rw [Real.norm_eq_abs]
      exact abs_dblKern_le hm hq hM₀ hδ d (Ioc_prod_subset hz)
    · filter_upwards [ae_feynmanMeasure] with z hz
      have hDz : ∀ i, kDen m (Ms i) q z ≠ 0 := fun i =>
        (hc₀.trans_le (kDen_ge_min hq hM₀.le (hMs i) (Ioc_prod_subset hz))).ne'
      have hc : ContinuousAt (fun M : Fin (k + 2) → ℝ => dblKern m q M d z) Ms := by
        unfold dblKern
        refine ContinuousAt.div (continuousAt_const.mul ?_) ?_
          (Finset.prod_ne_zero_iff.2 fun i _ => hDz i)
        · refine tendsto_finsetSum _ fun i _ => ContinuousAt.inv₀ ?_ (hDz i)
          unfold kDen
          exact ((continuous_const.mul ((continuous_apply i).pow 2)).add
            continuous_const).continuousAt
        · refine (continuous_finsetProd _ fun i _ => ?_).continuousAt
          unfold kDen
          exact (continuous_const.mul ((continuous_apply i).pow 2)).add continuous_const
      exact hc.tendsto.comp (tendsto_pert Ms)
  unfold dblVal
  exact ((Complex.continuous_ofReal.tendsto _).comp hI).const_mul _

section Value

variable {e m : ℝ} {p' p : Fin 4 → ℝ} (hm : 0 < m) (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
  (hq : 0 < Minkowski.dot (p' - p) (p' - p))
  {α : ℂ} (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
    pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
include hm hp' hp hp0' hp0 hq hα

/-- **Two distinct masses.** -/
theorem dblProdLimit_two_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 ≠ b ^ 2)
    (d : Fin 2) :
    dblProdLimit α (pauliChain e m p' p) m ![a, b] d p' p = dblVal e m p' p ![a, b] d := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  have hM₀ : 0 < min a b := lt_min ha hb
  have hMs : ∀ j, min a b ≤ (![a, b] : Fin 2 → ℝ) j := by
    intro j
    fin_cases j
    exacts [min_le_left _ _, min_le_right _ _]
  set q := Minkowski.dot (p' - p) (p' - p)
  rw [dblProdLimit_two hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) hα hCN hMs hab d]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [dblOneLimit_pauliChain e hm ha hp' hp hp0' hp0 hq d hα,
    dblOneLimit_pauliChain e hm hb hp' hp hp0' hp0 hq d hα]
  set F : ℝ → ℝ × ℝ → ℂ := fun M z => dblWt d 0 z * (((1 - z.2) - (1 - z.2) ^ 2 : ℝ) : ℂ) /
    (feynmanMass m M z.1 z.2 p' p : ℂ) ^ 2
  have hF : ∀ M, 0 < M → Integrable (F M) feynmanMeasure := fun M hM =>
    integrable_feynmanMeasure_of_continuousOn
      (ContinuousOn.div (((continuous_dblWt d 0).mul (by fun_prop)).continuousOn)
        ((Complex.continuous_ofReal.comp (continuous_feynmanMass m M p' p)).pow 2).continuousOn
        fun z hz => pow_ne_zero 2 (ofReal_ne_zero.2
          (feynmanMass_pos_of_pos hm hM hp' hp hp0' hp0 hz).ne'))
  have hab' : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hab.symm
  have e1 : ((b ^ 2 - a ^ 2 : ℝ) : ℂ)⁻¹ *
      ((∫ z, F a z ∂feynmanMeasure) - ∫ z, F b z ∂feynmanMeasure)
      = ((∫ z, dblKern m q ![a, b] d z ∂feynmanMeasure : ℝ) : ℂ) := by
    rw [← integral_sub (hF a ha) (hF b hb), ← integral_const_mul, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
    have hz' := Ioc_prod_subset hz
    have hA := feynmanMass_pos_of_pos hm ha hp' hp hp0' hp0 hz'
    have hB := feynmanMass_pos_of_pos hm hb hp' hp hp0' hp0 hz'
    set Fa := feynmanMass m a z.1 z.2 p' p
    set Fb := feynmanMass m b z.1 z.2 p' p
    have eA : kDen m a q z = Fa := by
      simp only [Fa]; rw [feynmanMass_onShell hp' hp]; rfl
    have eB : kDen m b q z = Fb := by
      simp only [Fb]; rw [feynmanMass_onShell hp' hp]; rfl
    have hd : Fb - Fa = (1 - z.2) * (b ^ 2 - a ^ 2) := by
      simp only [Fa, Fb]
      rw [feynmanMass_onShell hp' hp, feynmanMass_onShell hp' hp]
      ring
    have hab'' : b ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.2 hab.symm
    set c := 6 * dblLineWt d z.1 * z.2 ^ 2 * ((1 - z.2) - (1 - z.2) ^ 2)
    have key : dblKern m q ![a, b] d z = (b ^ 2 - a ^ 2)⁻¹ * (c / Fa ^ 2 - c / Fb ^ 2) := by
      have hsum : ∑ i, (kDen m ((![a, b] : Fin 2 → ℝ) i) q z)⁻¹ = Fa⁻¹ + Fb⁻¹ := by
        rw [Fin.sum_univ_two, ← eA, ← eB]
        rfl
      have hprod : ∏ i, kDen m ((![a, b] : Fin 2 → ℝ) i) q z = Fa * Fb := by
        rw [Fin.prod_univ_two, ← eA, ← eB]
        rfl
      have h1y : (1 - z.2) ^ (0 + 1) = (Fb - Fa) / (b ^ 2 - a ^ 2) := by
        rw [hd]
        field_simp
        ring
      unfold dblKern
      rw [hsum, hprod, h1y]
      field_simp
      ring
    dsimp only
    rw [key]
    simp only [F, dblWt, c]
    push_cast
    ring
  unfold dblVal
  rw [← e1]
  simp only [F]
  ring

/-- **Distinct squared masses.** -/
theorem dblProdLimit_inj (k : ℕ) (Ms : Fin (k + 2) → ℝ) (hpos : ∀ i, 0 < Ms i)
    (hinj : ∀ i l, i ≠ l → Ms i ^ 2 ≠ Ms l ^ 2) (d : Fin 2) :
    dblProdLimit α (pauliChain e m p' p) m Ms d p' p = dblVal e m p' p Ms d := by
  induction k with
  | zero =>
    have h : Ms = ![Ms 0, Ms 1] := by
      funext i; fin_cases i <;> rfl
    rw [h]
    exact dblProdLimit_two_eq hm hp' hp hp0' hp0 hq hα (hpos 0) (hpos 1) (hinj 0 1 (by decide)) d
  | succ k ih =>
    obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
    obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
    have hc : ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.2 (hinj 1 0 (by simp))
    have h1 := ih (dropOne Ms) (fun i => by
        cases i using Fin.cases with
        | zero => exact hpos 0
        | succ i => exact hpos _)
      (fun i l hil => by
        cases i using Fin.cases with
        | zero =>
          cases l using Fin.cases with
          | zero => exact absurd rfl hil
          | succ l => exact hinj _ _ (Fin.succ_ne_zero _).symm
        | succ i =>
          cases l using Fin.cases with
          | zero => exact hinj _ _ (Fin.succ_ne_zero _)
          | succ l =>
            exact hinj _ _ fun h => hil (Fin.ext (by
              have := congrArg Fin.val h
              simp at this
              simp
              omega)))
    have h2 := ih (Fin.tail Ms) (fun i => hpos _)
      (fun i l hil => hinj _ _ fun h => hil (Fin.succ_inj.1 h))
    rw [dblProdLimit_pf hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) hα hCN hMs
      (hinj 0 1 (by simp)) d]
    rw [show (Fin.cons (Ms 0) (Fin.tail (Fin.tail Ms)) : Fin (k + 2) → ℝ) = dropOne Ms from rfl,
      h1, h2, ← dblVal_drop e hm p' p hq.le Ms hpos d]
    field_simp

/-- **The value of the Pauli-projected doubled vertex**, for all positive photon masses. -/
theorem dblProdLimit_pauliChain_eq {k : ℕ} (Ms : Fin (k + 2) → ℝ) (hpos : ∀ i, 0 < Ms i)
    (d : Fin 2) :
    dblProdLimit α (pauliChain e m p' p) m Ms d p' p = dblVal e m p' p Ms d := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  have hge : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, M₀ ≤ pert Ms δ i := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
    have : 0 ≤ δ * ((i : ℕ) + 1) := by positivity
    simp only [pert]
    linarith [hMs i]
  have L1 := tendsto_dblProdLimit hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) α hCN
    d (tendsto_pert Ms) hge
  have heq : (fun δ => dblProdLimit α (pauliChain e m p' p) m (pert Ms δ) d p' p) =ᶠ[𝓝[>] 0]
      fun δ => dblVal e m p' p (pert Ms δ) d := by
    filter_upwards [eventually_pert_inj hpos] with δ ⟨h1, h2⟩
    exact dblProdLimit_inj hm hp' hp hp0' hp0 hq hα k _ h1 h2 d
  exact tendsto_nhds_unique (L1.congr' heq) (tendsto_dblVal_pert e hm p' p hq.le hpos d)

end Value

end QED.ChainProof.CtLoB

end
