/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBUndChain
public import QED.ChainProof.SetCRegDispCtLoBKern
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The value of the undoubled chain with the identity on the doubled line, any photon masses

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan; the companion of `QED/ChainProof/SetCRegDispCtLoBKern.lean` for the undoubled part
`QED.ChainProof.CtLoB.undChain` of the merged insertion. With `Δ_M = kDen m M q² z`, the engine
limit with photon masses `M_0, …, M_{k+1}` is `i (π²/6) 4 κ_e q² (4m² + q²)² ∫ undKern`,

`undKern = 6 y (1-y)^{k+2} / ∏_i Δ_{M_i}`,

i.e. `6 y f(K)` for the photon function `f(K) = ∏_i (K + M_i²)⁻¹`.

* `prodLimit_drop_gen`: the partial fraction of the engine limit for any numerator;
* `undKern_drop`, `abs_undKern_le`, `integrable_undKern`, `undVal_drop`, `tendsto_undVal_pert`;
* **`prodLimit_undChain_eq`**: `prodLimit 0 (undChain e m d p' p) m Ms = undVal Ms` for all
  positive masses, on-shell positive-energy momenta with `q² > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit QED.TwoLoop.VPHalfAtAssembly
open QED.ChainProof.HCBB2 (pert tendsto_pert eventually_pert_inj dropOne)

/-! ### The engine partial fraction for any numerator -/

/-- `(M₁² - M₀²) prodLimit = prodLimit (drop M₁) - prodLimit (drop M₀)`, any numerator. -/
theorem prodLimit_drop_gen {m : ℝ} (hm : 0 < m) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hCN : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2)
    {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) (hpos : ∀ i, 0 < Ms i) :
    ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) * prodLimit α N m Ms p' p =
      prodLimit α N m (dropOne Ms) p' p - prodLimit α N m (Fin.tail Ms) p' p := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  have hD : ∀ i, M₀ ≤ dropOne Ms i := fun i => by
    cases i using Fin.cases with
    | zero => exact hMs 0
    | succ i => exact hMs _
  have hT : ∀ i, M₀ ≤ Fin.tail Ms i := fun i => hMs _
  have T0 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hα hCN hMs
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  have T1 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hα hCN hD
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  have T2 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hα hCN hT
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id fun _ => tendsto_id
  refine tendsto_nhds_unique (T0.const_mul _) ((T1.sub T2).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have i1 := energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hα hCN hD
    (fun _ => hε) hε
  have i2 := energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hα hCN hT
    (fun _ => hε) hε
  simp only [id]
  rw [← efi_sub ⟨i1.1, i1.2.1⟩ ⟨i2.1, i2.2.1⟩, ← efi_const_mul]
  congr 1
  funext ℓ
  simp only [prodIntegrand, Fin.prod_univ_succ, dropOne, Fin.tail, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_zero_eq_one]
  have h0 := denom_ne_zero_of_pos (M := Ms 0) hε ℓ
  have h1 := denom_ne_zero_of_pos (M := Ms 1) hε ℓ
  have hd : denom (Ms 1) ε ℓ - denom (Ms 0) ε ℓ = ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) := by
    simp only [denom]; push_cast; ring
  rw [← hd]
  field_simp

/-! ### The kernel -/

/-- The undoubled kernel `6 y (1-y)^{k+2} / ∏_i Δ_i`. -/
noncomputable def undKern (m s : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (z : ℝ × ℝ) : ℝ :=
  6 * z.2 * (1 - z.2) ^ (k + 2) / ∏ i, kDen m (Ms i) s z

theorem undKern_drop (m s : ℝ) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ) {z : ℝ × ℝ}
    (hD : ∀ i, kDen m (Ms i) s z ≠ 0) :
    (Ms 1 ^ 2 - Ms 0 ^ 2) * undKern m s Ms z =
      undKern m s (dropOne Ms) z - undKern m s (Fin.tail Ms) z := by
  set D0 := kDen m (Ms 0) s z
  set D1 := kDen m (Ms 1) s z
  set R := ∏ i : Fin (k + 1), kDen m (Ms i.succ.succ) s z
  have h0 : D0 ≠ 0 := hD 0
  have h1 : D1 ≠ 0 := hD 1
  have hR : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD _
  have hP3 : ∏ i, kDen m (Ms i) s z = D0 * D1 * R := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    exact (mul_assoc _ _ _).symm
  have hPd : ∏ i, kDen m (dropOne Ms i) s z = D0 * R := by
    rw [Fin.prod_univ_succ]
    rfl
  have hPt : ∏ i, kDen m (Fin.tail Ms i) s z = D1 * R := by
    rw [Fin.prod_univ_succ]
    rfl
  have hd : (1 - z.2) * (Ms 1 ^ 2 - Ms 0 ^ 2) = D1 - D0 := by
    simp only [D0, D1, kDen]
    ring
  unfold undKern
  rw [hP3, hPd, hPt, show (1 - z.2) ^ (k + 1 + 2) = (1 - z.2) ^ (k + 2) * (1 - z.2) by ring]
  rw [show (Ms 1 ^ 2 - Ms 0 ^ 2) * (6 * z.2 * ((1 - z.2) ^ (k + 2) * (1 - z.2)) /
      (D0 * D1 * R)) = 6 * z.2 * (1 - z.2) ^ (k + 2) * ((1 - z.2) * (Ms 1 ^ 2 - Ms 0 ^ 2)) /
        (D0 * D1 * R) by ring, hd]
  field_simp

theorem measurable_undKern (m s : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    Measurable (undKern m s Ms) := by
  unfold undKern kDen kC
  exact Measurable.div (by fun_prop) (Finset.measurable_prod _ fun i _ => by fun_prop)

theorem abs_undKern_le {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k : ℕ}
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    |undKern m s Ms z| ≤ 6 / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 2) := by
  set c₀ := 3 / 4 * min (M₀ ^ 2) (m ^ 2)
  have hc₀ : 0 < c₀ := by positivity
  have hD : ∀ i, c₀ ≤ kDen m (Ms i) s z := fun i => kDen_ge_min hs hM₀.le (hMs i) hz
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hz
  have hy1' : 0 ≤ 1 - z.2 := by linarith
  have hA0 : 0 ≤ 6 * z.2 * (1 - z.2) ^ (k + 2) := by positivity
  have hA1 : 6 * z.2 * (1 - z.2) ^ (k + 2) ≤ 6 := by
    have h2 : (1 - z.2) ^ (k + 2) ≤ 1 := pow_le_one₀ hy1' (by linarith)
    calc 6 * z.2 * (1 - z.2) ^ (k + 2) ≤ 6 * 1 * 1 := by gcongr
      _ = 6 := by ring
  have hP : c₀ ^ (k + 2) ≤ ∏ i, kDen m (Ms i) s z := by
    calc c₀ ^ (k + 2) = ∏ _i : Fin (k + 2), c₀ := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc₀.le) fun i _ => hD i
  have hPp : 0 < ∏ i, kDen m (Ms i) s z := (pow_pos hc₀ _).trans_le hP
  unfold undKern
  rw [abs_of_nonneg (div_nonneg hA0 hPp.le)]
  calc 6 * z.2 * (1 - z.2) ^ (k + 2) / ∏ i, kDen m (Ms i) s z ≤ 6 / ∏ i, kDen m (Ms i) s z :=
        div_le_div_of_nonneg_right hA1 hPp.le
    _ ≤ 6 / c₀ ^ (k + 2) := div_le_div_of_nonneg_left (by norm_num) (pow_pos hc₀ _) hP

theorem integrable_undKern {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {k : ℕ}
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) :
    Integrable (undKern m s Ms) feynmanMeasure := by
  refine Integrable.mono' (integrable_const (6 / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 2)))
    (measurable_undKern m s Ms).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs]
  exact abs_undKern_le hm hs hM₀ hMs (Ioc_prod_subset hz)

/-! ### The value -/

/-- The value `i (π²/6) 4 κ_e q² (4m² + q²)² ∫ undKern`. -/
noncomputable def undVal (e m : ℝ) (p' p : Fin 4 → ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) : ℂ :=
  I * ((π ^ 2 / 6 : ℝ) : ℂ) * (4 * kappa e * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
    (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) *
    ((∫ z, undKern m (Minkowski.dot (p' - p) (p' - p)) Ms z ∂feynmanMeasure : ℝ) : ℂ)

theorem undVal_drop (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {k : ℕ} (Ms : Fin (k + 1 + 2) → ℝ)
    (hpos : ∀ i, 0 < Ms i) :
    ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) * undVal e m p' p Ms =
      undVal e m p' p (dropOne Ms) - undVal e m p' p (Fin.tail Ms) := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hD : ∀ i, M₀ ≤ dropOne Ms i := fun i => by
    cases i using Fin.cases with
    | zero => exact hMs 0
    | succ i => exact hMs _
  have hT : ∀ i, M₀ ≤ Fin.tail Ms i := fun i => hMs _
  have e1 : (Ms 1 ^ 2 - Ms 0 ^ 2) * ∫ z, undKern m q Ms z ∂feynmanMeasure =
      (∫ z, undKern m q (dropOne Ms) z ∂feynmanMeasure) -
        ∫ z, undKern m q (Fin.tail Ms) z ∂feynmanMeasure := by
    rw [← integral_const_mul, ← integral_sub (integrable_undKern hm hq hM₀ hD)
      (integrable_undKern hm hq hM₀ hT)]
    refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
    exact undKern_drop m q Ms fun i =>
      ((by positivity : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2)).trans_le
        (kDen_ge_min hq hM₀.le (hMs i) (Ioc_prod_subset hz))).ne'
  unfold undVal
  rw [← mul_sub, ← ofReal_sub, ← e1]
  push_cast
  ring

theorem tendsto_undVal_pert (e : ℝ) {m : ℝ} (hm : 0 < m) (p' p : Fin 4 → ℝ)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hpos : ∀ i, 0 < Ms i) :
    Tendsto (fun δ => undVal e m p' p (pert Ms δ)) (𝓝[>] 0) (𝓝 (undVal e m p' p Ms)) := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  set q := Minkowski.dot (p' - p) (p' - p)
  have hge : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, M₀ ≤ pert Ms δ i := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
    have : 0 ≤ δ * ((i : ℕ) + 1) := by positivity
    simp only [pert]
    linarith [hMs i]
  have hc₀ : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2) := by positivity
  have hI : Tendsto (fun δ => ∫ z, undKern m q (pert Ms δ) z ∂feynmanMeasure) (𝓝[>] 0)
      (𝓝 (∫ z, undKern m q Ms z ∂feynmanMeasure)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => 6 / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 2))
      (Eventually.of_forall fun δ => (measurable_undKern m q _).aestronglyMeasurable) ?_
      (integrable_const _) ?_
    · filter_upwards [hge] with δ hδ
      filter_upwards [ae_feynmanMeasure] with z hz
      rw [Real.norm_eq_abs]
      exact abs_undKern_le hm hq hM₀ hδ (Ioc_prod_subset hz)
    · filter_upwards [ae_feynmanMeasure] with z hz
      have hDz : ∀ i, kDen m (Ms i) q z ≠ 0 := fun i =>
        (hc₀.trans_le (kDen_ge_min hq hM₀.le (hMs i) (Ioc_prod_subset hz))).ne'
      have hc : ContinuousAt (fun M : Fin (k + 2) → ℝ => undKern m q M z) Ms := by
        unfold undKern
        refine ContinuousAt.div continuousAt_const ?_
          (Finset.prod_ne_zero_iff.2 fun i _ => hDz i)
        refine (continuous_finsetProd _ fun i _ => ?_).continuousAt
        unfold kDen
        exact (continuous_const.mul ((continuous_apply i).pow 2)).add continuous_const
      exact hc.tendsto.comp (tendsto_pert Ms)
  unfold undVal
  exact ((Complex.continuous_ofReal.tendsto _).comp hI).const_mul _

section Value

variable {e m : ℝ} {p' p : Fin 4 → ℝ} (hm : 0 < m) (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
  (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hm hp' hp hp0' hp0 hq

theorem prodLimit_undChain_two_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (d : Fin 2) :
    prodLimit 0 (undChain e m d p' p) m ![a, b] p' p = undVal e m p' p ![a, b] := by
  rw [prodLimit_undChain_two e hm ha hb hp' hp hp0' hp0 hq d, undVal, ← integral_complex_ofReal]
  congr 1
  refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
  have hz' := Ioc_prod_subset hz
  have eA : kDen m a (Minkowski.dot (p' - p) (p' - p)) z = feynmanMass m a z.1 z.2 p' p := by
    rw [feynmanMass_onShell hp' hp]; rfl
  have eB : kDen m b (Minkowski.dot (p' - p) (p' - p)) z = feynmanMass m b z.1 z.2 p' p := by
    rw [feynmanMass_onShell hp' hp]; rfl
  have hP : ∏ i, kDen m ((![a, b] : Fin 2 → ℝ) i) (Minkowski.dot (p' - p) (p' - p)) z =
      feynmanMass m a z.1 z.2 p' p * feynmanMass m b z.1 z.2 p' p := by
    rw [Fin.prod_univ_two, ← eA, ← eB]
    rfl
  simp only [undKern, hP, feynWt]
  push_cast
  ring

/-- **Distinct squared masses.** -/
theorem prodLimit_undChain_inj (k : ℕ) (Ms : Fin (k + 2) → ℝ) (hpos : ∀ i, 0 < Ms i)
    (hinj : ∀ i l, i ≠ l → Ms i ^ 2 ≠ Ms l ^ 2) (d : Fin 2) :
    prodLimit 0 (undChain e m d p' p) m Ms p' p = undVal e m p' p Ms := by
  induction k with
  | zero =>
    have h : Ms = ![Ms 0, Ms 1] := by
      funext i; fin_cases i <;> rfl
    rw [h]
    exact prodLimit_undChain_two_eq hm hp' hp hp0' hp0 hq (hpos 0) (hpos 1) d
  | succ k ih =>
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
    apply mul_left_cancel₀ hc
    rw [undChain_eq_affN, prodLimit_drop_gen hm hp' hp hp0' hp0 (continuous_affN _ _)
      (affN_cons _ _) (norm_affN_le _ _) Ms hpos, ← undChain_eq_affN, h1, h2,
      undVal_drop e hm p' p hq.le Ms hpos]

/-- **The value of the undoubled chain**, for all positive photon masses. -/
theorem prodLimit_undChain_eq {k : ℕ} (Ms : Fin (k + 2) → ℝ) (hpos : ∀ i, 0 < Ms i)
    (d : Fin 2) :
    prodLimit 0 (undChain e m d p' p) m Ms p' p = undVal e m p' p Ms := by
  obtain ⟨M₀, hM₀, hMs⟩ := exists_pos_le_all hpos
  have hge : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, M₀ ≤ pert Ms δ i := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
    have : 0 ≤ δ * ((i : ℕ) + 1) := by positivity
    simp only [pert]
    linarith [hMs i]
  have L1 := tendsto_prodLimit hm hM₀ hp' hp hp0' hp0 (continuous_affN (undC₀ e m d p' p)
    (undC e m p' p)) 0 (norm_affN_le _ _) (tendsto_pert Ms) hge
  rw [← undChain_eq_affN] at L1
  have heq : (fun δ => prodLimit 0 (undChain e m d p' p) m (pert Ms δ) p' p) =ᶠ[𝓝[>] 0]
      fun δ => undVal e m p' p (pert Ms δ) := by
    filter_upwards [eventually_pert_inj hpos] with δ ⟨h1, h2⟩
    exact prodLimit_undChain_inj hm hp' hp hp0' hp0 hq k _ h1 h2 d
  exact tendsto_nhds_unique (L1.congr' heq) (tendsto_undVal_pert e hm p' p hq.le hpos)

end Value

end QED.ChainProof.CtLoB

end
