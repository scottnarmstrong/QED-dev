/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBZeroJ
public import QED.TwoLoop.VPHalfSub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spectral side of the mass part

Helper level for `QED.ChainProof.SetCRegDisp.CBLoBEq` (set (c), layers 5-6). The fixed-`q`
value of the mass part is expected (as for the undifferentiated bubble,
`QED.TwoLoop.VPHalf.specFlavour`) to be a `ρ`-superposition over the spectral variable `v` of
the Pauli values of the merged insertion with the photon masses `(m_γ, Λ, m_γ, Λ, μ_v)`,
`μ_v = √(4M²/(1-v²))` (`QED.TwoLoop.VPHalf.specMass`), weight `K²` (`j = 2`).

* `combKern`, `combW`: the kernel `undKernJ 2 - 2m² dblKernJ 2` of five photon masses and its
  Feynman-parameter integral; `abs_combKern_le`: a bound `C/μ²` in the last mass, uniform in
  `s = q² ≥ 0` and in the other masses `≥ M₀ > 0`;
* `specFlavourW m M m_γ Λ s d`: `∫₀¹ ρ(v) (Λ² - m_γ²)²/6 combW m s (m_γ, Λ, m_γ, Λ, μ_v) d dv`;
* **`specFlavourW_one_zero`**: at `m = 1`, `s = 0` it is `vpFlavourW M m_γ Λ`
  (`QED.ChainProof.CtLoB.vpInsertW_eq_comb`);
* **`tendsto_specFlavourW_zero`**: continuity at `s = 0` from above (dominated convergence in
  `v`, with `ρ(v)/μ_v² ≤ 1/(4M²)`);
* **`specFlavourW_zero_eq`**: mass scaling, `specFlavourW m M m_γ Λ 0 d =
  m⁻² vpFlavourW (M/m) (m_γ/m) (Λ/m)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPUnitNested

/-! ### A bound decaying in the spectral mass -/

/-- The combination `undKernJ 2 - 2m² dblKernJ 2` of five photon masses. -/
noncomputable def combKern (m s : ℝ) (Ms : Fin (3 + 2) → ℝ) (d : Fin 2) (z : ℝ × ℝ) : ℝ :=
  undKernJ m s 2 Ms z - 2 * m ^ 2 * dblKernJ m s 2 Ms d z

section Bound

variable {m s M₀ : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hM₀ : 0 < M₀) {Ms : Fin (3 + 2) → ℝ}
  (hMs : ∀ i, M₀ ≤ Ms i) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
include hm hs hM₀ hMs hz

theorem combKern_bound_aux :
    let μ := min (M₀ ^ 2) 1
    let T := (1 - z.2) + kC m s z
    0 < μ ∧ 0 < T ∧ 3 / 4 * min (1 ^ 2) (m ^ 2) ≤ T ∧
      (μ * T) ^ 4 ≤ ∏ i : Fin 4, kDen m (Ms (Fin.castSucc i)) s z ∧
      (1 - z.2) * Ms 4 ^ 2 ≤ kDen m (Ms 4) s z ∧
      ∏ i, kDen m (Ms i) s z =
        (∏ i : Fin 4, kDen m (Ms (Fin.castSucc i)) s z) * kDen m (Ms 4) s z := by
  intro μ T
  have hμ : 0 < μ := lt_min (by positivity) one_pos
  have hc₁ : 0 < 3 / 4 * min (1 ^ 2 : ℝ) (m ^ 2) := by positivity
  have hT1 : 3 / 4 * min (1 ^ 2) (m ^ 2) ≤ T := tSum_ge hs hz
  have hT : 0 < T := hc₁.trans_le hT1
  refine ⟨hμ, hT, hT1, ?_, ?_, Fin.prod_univ_castSucc _⟩
  · calc (μ * T) ^ 4 = ∏ _i : Fin 4, μ * T := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => (mul_pos hμ hT).le) fun i _ =>
          kDen_ge_mu hs hM₀.le (hMs _) hz
  · have := kC_nonneg (m := m) hs hz
    unfold kDen
    linarith

/-- **The bound `C/μ²`** in the last (spectral) mass `μ = Ms 4`. -/
theorem abs_combKern_le (d : Fin 2) :
    |combKern m s Ms d z| ≤
      (6 / min (M₀ ^ 2) 1 ^ 4 + 2 * m ^ 2 * (30 / (min (M₀ ^ 2) 1 ^ 5 *
        (3 / 4 * min (1 ^ 2) (m ^ 2))) + 12 / (min (M₀ ^ 2) 1 ^ 4 *
          (3 / 4 * min (1 ^ 2) (m ^ 2))))) / Ms 4 ^ 2 := by
  obtain ⟨hμ, hT, hT1, hP4, hD4, hsplit⟩ := combKern_bound_aux hm hs hM₀ hMs hz
  set μ := min (M₀ ^ 2) 1
  set T := (1 - z.2) + kC m s z
  set c₁ := 3 / 4 * min (1 ^ 2 : ℝ) (m ^ 2)
  set P4 := ∏ i : Fin 4, kDen m (Ms (Fin.castSucc i)) s z
  set D4 := kDen m (Ms 4) s z
  have hc₁ : 0 < c₁ := by positivity
  have hc := kC_nonneg (m := m) hs hz
  have hμ4 : 0 < Ms 4 := hM₀.trans_le (hMs 4)
  have hD : ∀ i, μ * T ≤ kDen m (Ms i) s z := fun i => kDen_ge_mu hs hM₀.le (hMs i) hz
  have hP4p : 0 < P4 := (pow_pos (mul_pos hμ hT) 4).trans_le hP4
  have hD4p : 0 < D4 := (mul_pos hμ hT).trans_le (hD 4)
  have hPp : 0 < P4 * D4 := mul_pos hP4p hD4p
  have hw : 0 ≤ dblLineWt d z.1 ∧ dblLineWt d z.1 ≤ 1 := dblLineWt_mem_Icc d hz.1
  obtain ⟨-, hy0, hy1⟩ := hz
  have hy : 0 ≤ 1 - z.2 := by linarith
  have hyT : 1 - z.2 ≤ T := by linarith
  have hcT : kC m s z ≤ T := by linarith
  have hS1 : ∑ i, (kDen m (Ms i) s z)⁻¹ ≤ 5 / (μ * T) := by
    calc ∑ i, (kDen m (Ms i) s z)⁻¹ ≤ ∑ _i : Fin (3 + 2), (μ * T)⁻¹ :=
          Finset.sum_le_sum fun i _ => inv_anti₀ (mul_pos hμ hT) (hD i)
      _ = 5 / (μ * T) := by simp [div_eq_mul_inv]
  have hS0 : 0 ≤ ∑ i, (kDen m (Ms i) s z)⁻¹ :=
    Finset.sum_nonneg fun i _ => (inv_pos.2 ((mul_pos hμ hT).trans_le (hD i))).le
  have hK2 : kC m s z ^ 2 * (1 - z.2) ^ 2 * μ ^ 4 ≤ P4 := by
    calc kC m s z ^ 2 * (1 - z.2) ^ 2 * μ ^ 4 ≤ T ^ 2 * T ^ 2 * μ ^ 4 := by gcongr
      _ = (μ * T) ^ 4 := by ring
      _ ≤ P4 := hP4
  have hK1 : kC m s z * (1 - z.2) ^ 2 * c₁ * μ ^ 4 ≤ P4 := by
    calc kC m s z * (1 - z.2) ^ 2 * c₁ * μ ^ 4 ≤ T * T ^ 2 * T * μ ^ 4 := by gcongr
      _ = (μ * T) ^ 4 := by ring
      _ ≤ P4 := hP4
  have hw3 : 6 * dblLineWt d z.1 * z.2 ^ 3 ≤ 6 := by
    have : z.2 ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
    have := hw.1
    nlinarith [mul_le_mul hw.2 this (by positivity) zero_le_one]
  have hw0 : 0 ≤ 6 * dblLineWt d z.1 * z.2 ^ 3 := by have := hw.1; positivity
  -- the three pieces
  have hU : |undKernJ m s 2 Ms z| ≤ 6 / μ ^ 4 / Ms 4 ^ 2 := by
    unfold undKernJ
    rw [hsplit, show 3 + 2 - 2 = 3 from rfl, abs_of_nonneg (div_nonneg (by positivity) hPp.le),
      div_div, div_le_div_iff₀ hPp (by positivity)]
    calc 6 * z.2 * kC m s z ^ 2 * (1 - z.2) ^ 3 * (μ ^ 4 * Ms 4 ^ 2)
        = 6 * z.2 * (kC m s z ^ 2 * (1 - z.2) ^ 2 * μ ^ 4) * ((1 - z.2) * Ms 4 ^ 2) := by ring
      _ ≤ 6 * 1 * P4 * D4 := by gcongr
      _ = 6 * (P4 * D4) := by ring
  have hA : |dblKernA m s 2 Ms d z| ≤ 30 / (μ ^ 5 * c₁) / Ms 4 ^ 2 := by
    unfold dblKernA
    rw [hsplit, show 3 + 2 - 2 = 3 from rfl, abs_of_nonneg (div_nonneg (by positivity) hPp.le),
      div_div, div_le_div_iff₀ hPp (by positivity)]
    have hSc : (∑ i, (kDen m (Ms i) s z)⁻¹) * (μ * c₁) ≤ 5 := by
      calc (∑ i, (kDen m (Ms i) s z)⁻¹) * (μ * c₁) ≤ 5 / (μ * T) * (μ * T) := by gcongr
        _ = 5 := by field_simp
    calc 6 * dblLineWt d z.1 * z.2 ^ 3 * (1 - z.2) ^ 3 * kC m s z ^ 2 *
          (∑ i, (kDen m (Ms i) s z)⁻¹) * (μ ^ 5 * c₁ * Ms 4 ^ 2)
        = (6 * dblLineWt d z.1 * z.2 ^ 3) * (kC m s z ^ 2 * (1 - z.2) ^ 2 * μ ^ 4) *
          ((1 - z.2) * Ms 4 ^ 2) * ((∑ i, (kDen m (Ms i) s z)⁻¹) * (μ * c₁)) := by ring
      _ ≤ 6 * P4 * D4 * 5 := by gcongr
      _ = 30 * (P4 * D4) := by ring
  have hB : |dblKernB m s 2 Ms d z| ≤ 12 / (μ ^ 4 * c₁) / Ms 4 ^ 2 := by
    unfold dblKernB
    rw [hsplit, show 3 + 2 - 2 = 3 from rfl, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
      abs_of_nonneg (div_nonneg (by positivity) hPp.le), div_div,
      div_le_div_iff₀ hPp (by positivity)]
    push_cast
    calc 6 * dblLineWt d z.1 * z.2 ^ 3 * (1 - z.2) ^ 3 * (2 * kC m s z) * (μ ^ 4 * c₁ * Ms 4 ^ 2)
        = 2 * (6 * dblLineWt d z.1 * z.2 ^ 3) * (kC m s z * (1 - z.2) ^ 2 * c₁ * μ ^ 4) *
          ((1 - z.2) * Ms 4 ^ 2) := by ring
      _ ≤ 2 * 6 * P4 * D4 := by gcongr
      _ = 12 * (P4 * D4) := by ring
  unfold combKern dblKernJ
  calc |undKernJ m s 2 Ms z - 2 * m ^ 2 * (dblKernA m s 2 Ms d z - dblKernB m s 2 Ms d z)|
      ≤ |undKernJ m s 2 Ms z| +
          2 * m ^ 2 * (|dblKernA m s 2 Ms d z| + |dblKernB m s 2 Ms d z|) := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m ^ 2)]
        gcongr
        exact abs_sub _ _
    _ ≤ 6 / μ ^ 4 / Ms 4 ^ 2 + 2 * m ^ 2 * (30 / (μ ^ 5 * c₁) / Ms 4 ^ 2 +
          12 / (μ ^ 4 * c₁) / Ms 4 ^ 2) := by gcongr
    _ = _ := by ring

end Bound

/-! ### The spectral side -/

/-- The Feynman-parameter integral of `combKern`. -/
noncomputable def combW (m s : ℝ) (Ms : Fin (3 + 2) → ℝ) (d : Fin 2) : ℝ :=
  ∫ z, combKern m s Ms d z ∂feynmanMeasure

/-- The photon masses `(m_γ, Λ, m_γ, Λ, μ)` of one spectral insertion. -/
noncomputable def specMs (mγ Λ μ : ℝ) : Fin (3 + 2) → ℝ := ![mγ, Λ, mγ, Λ, μ]

/-- **One flavour of the spectral side of the mass part at `q² = s`**: the `ρ`-superposition
of the values of `undKernJ 2 - 2m² dblKernJ 2` with the photon masses `specMs m_γ Λ μ_v`. -/
noncomputable def specFlavourW (m M mγ Λ s : ℝ) (d : Fin 2) : ℝ :=
  ∫ v in (0 : ℝ)..1, QED.TwoLoop.VPUnit.rho v *
    ((Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * combW m s (specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M v)) d)

theorem msW_eq_specMs {M mγ Λ v : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    msW (mγ ^ 2) (Λ ^ 2) (M ^ 2 * QED.ChainProof.SetCK.setCKSpecMass v) =
      specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M v) := by
  have e : M ^ 2 * QED.ChainProof.SetCK.setCKSpecMass v = 4 * M ^ 2 / (1 - v ^ 2) := by
    unfold QED.ChainProof.SetCK.setCKSpecMass
    ring
  funext i
  fin_cases i <;>
    simp [msW, specMs, QED.TwoLoop.VPHalf.specMass, e, Real.sqrt_sq hmγ.le, Real.sqrt_sq hΛ.le]

/-- **At `m = 1`, `s = 0` one flavour of the spectral side is `vpFlavourW`.** -/
theorem specFlavourW_one_zero {M mγ Λ : ℝ} (hM : 0 < M) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d : Fin 2) :
    specFlavourW 1 M mγ Λ 0 d = QED.ChainProof.SetCRegDisp.vpFlavourW M mγ Λ := by
  unfold specFlavourW QED.ChainProof.SetCRegDisp.vpFlavourW
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hc : 0 < M ^ 2 * QED.ChainProof.SetCK.setCKSpecMass v := by
    unfold QED.ChainProof.SetCK.setCKSpecMass
    positivity
  rw [vpInsertW_eq_comb (by positivity) (by positivity) hc d, msW_eq_specMs hmγ hΛ]
  unfold combW combKern QED.ChainProof.SetCK.setCKSpecRho QED.TwoLoop.VPUnit.rho
  ring

/-! ### Continuity at `q² = 0`, uniformly in the spectral variable -/

theorem two_mul_le_specMass {M v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    2 * M ≤ QED.TwoLoop.VPHalf.specMass M v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have h2 : 1 - v ^ 2 ≤ 1 := by nlinarith [hv.1]
  unfold QED.TwoLoop.VPHalf.specMass
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ h1]
  nlinarith [sq_nonneg M]

theorem measurable_combKern_spec (m s M mγ Λ : ℝ) (d : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) =>
      combKern m s (specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M p.1)) d p.2 := by
  have hMi : ∀ i, Measurable fun v : ℝ => specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M v) i := by
    intro i
    fin_cases i <;> simp [specMs, QED.TwoLoop.VPHalf.specMass]
    fun_prop
  have hk : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) =>
      kDen m (specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M p.1) i) s p.2 := by
    intro i
    have : Measurable fun p : ℝ × (ℝ × ℝ) =>
        specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M p.1) i := (hMi i).comp measurable_fst
    unfold kDen kC
    fun_prop
  have hP := Finset.measurable_prod Finset.univ fun i _ => hk i
  have hS := Finset.measurable_sum Finset.univ fun i _ => (hk i).inv
  unfold combKern undKernJ dblKernJ dblKernA dblKernB dblLineWt kC
  split_ifs
  all_goals
    refine Measurable.sub (Measurable.div (by fun_prop) hP)
      (Measurable.mul measurable_const (Measurable.sub
        (Measurable.div (Measurable.mul (by fun_prop) hS) hP) (Measurable.div (by fun_prop) hP)))

theorem tendsto_combW_zero {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {Ms : Fin (3 + 2) → ℝ}
    (hMs : ∀ i, M₀ ≤ Ms i) (d : Fin 2) :
    Tendsto (fun s => combW m s Ms d) (𝓝[≥] 0) (𝓝 (combW m 0 Ms d)) := by
  have hsplit : ∀ s, 0 ≤ s → combW m s Ms d = (∫ z, undKernJ m s 2 Ms z ∂feynmanMeasure) -
      2 * m ^ 2 * ∫ z, dblKernJ m s 2 Ms d z ∂feynmanMeasure := fun s hs => by
    rw [combW, ← integral_const_mul, ← integral_sub
      (integrable_undKernJ hm hs hM₀ (by norm_num) hMs)
      ((integrable_dblKernJ hm hs hM₀ (by norm_num) hMs d).const_mul _)]
    rfl
  rw [hsplit 0 le_rfl]
  refine Tendsto.congr' ?_ ((tendsto_integral_undKernJ hm hM₀ (by norm_num) hMs).sub
    ((tendsto_integral_dblKernJ hm hM₀ (by norm_num) hMs d).const_mul (2 * m ^ 2)))
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
  exact (hsplit s hs).symm

/-- **The spectral side is continuous at `q² = 0` from the right.** -/
theorem tendsto_specFlavourW_zero {m M mγ Λ : ℝ} (hm : 0 < m) (hM : 0 < M) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (d : Fin 2) :
    Tendsto (fun s => specFlavourW m M mγ Λ s d) (𝓝[≥] 0)
      (𝓝 (specFlavourW m M mγ Λ 0 d)) := by
  set M₀ := min (min mγ Λ) (2 * M)
  have hM₀ : 0 < M₀ := lt_min (lt_min hmγ hΛ) (by positivity)
  have hMs : ∀ v ∈ Ioo (0 : ℝ) 1, ∀ i,
      M₀ ≤ specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M v) i := by
    intro v hv i
    have h1 : M₀ ≤ mγ := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : M₀ ≤ Λ := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : M₀ ≤ 2 * M := min_le_right _ _
    have h4 := two_mul_le_specMass (M := M) hv
    fin_cases i <;> simp [specMs] <;> linarith
  set C₀ := 6 / min (M₀ ^ 2) 1 ^ 4 + 2 * m ^ 2 * (30 / (min (M₀ ^ 2) 1 ^ 5 *
    (3 / 4 * min (1 ^ 2) (m ^ 2))) + 12 / (min (M₀ ^ 2) 1 ^ 4 *
      (3 / 4 * min (1 ^ 2) (m ^ 2))))
  set C := C₀ * feynmanMeasure.real univ
  have hC : 0 ≤ C := by positivity
  unfold specFlavourW
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * C * (1 / (4 * M ^ 2))) ?_ ?_
    intervalIntegrable_const ?_
  · refine Eventually.of_forall fun s => ?_
    have hint := (measurable_combKern_spec m s M mγ Λ d).stronglyMeasurable.integral_prod_right'
      (ν := feynmanMeasure)
    have hrho : Measurable QED.TwoLoop.VPUnit.rho := by
      unfold QED.TwoLoop.VPUnit.rho; fun_prop
    exact (hrho.mul (hint.measurable.const_mul _)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with v hv1 hv
    rw [uIoc_of_le zero_le_one] at hv
    have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩
    have hμ := QED.TwoLoop.VPHalf.specMass_pos hM.ne' hvI
    set μ := QED.TwoLoop.VPHalf.specMass M v
    have hW : |combW m s (specMs mγ Λ μ) d| ≤ C / μ ^ 2 := by
      have hb : ∀ᵐ z ∂feynmanMeasure, ‖combKern m s (specMs mγ Λ μ) d z‖ ≤ C₀ / μ ^ 2 := by
        filter_upwards [ae_feynmanMeasure] with z hz
        rw [Real.norm_eq_abs]
        have := abs_combKern_le hm hs hM₀ (hMs v hvI) (Ioc_prod_subset hz) d
        have e4 : specMs mγ Λ μ 4 = μ := rfl
        rw [e4] at this
        exact this
      have := norm_integral_le_of_norm_le_const hb
      rw [combW, ← Real.norm_eq_abs]
      refine this.trans (le_of_eq ?_)
      simp only [C]
      ring
    have hr := QED.TwoLoop.VPHalf.rho_mul_inv_specMass_sq hM.ne' hvI
    have hrho0 : 0 ≤ QED.TwoLoop.VPUnit.rho v := by
      unfold QED.TwoLoop.VPUnit.rho
      have : 0 ≤ 1 - v ^ 2 / 3 := by nlinarith [hvI.1, hvI.2]
      have : 0 < 1 - v ^ 2 := by nlinarith [hvI.1, hvI.2]
      positivity
    have hv2 : v ^ 2 * (1 - v ^ 2 / 3) ≤ 1 := by nlinarith [hvI.1, hvI.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrho0, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Λ ^ 2 - mγ ^ 2) ^ 2 / 6)]
    calc QED.TwoLoop.VPUnit.rho v * ((Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * |combW m s (specMs mγ Λ μ) d|)
        ≤ QED.TwoLoop.VPUnit.rho v * ((Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * (C / μ ^ 2)) := by gcongr
      _ = (Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * C * (QED.TwoLoop.VPUnit.rho v * (μ ^ 2)⁻¹) := by ring
      _ = (Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * C * (v ^ 2 * (1 - v ^ 2 / 3) / (4 * M ^ 2)) := by rw [hr]
      _ ≤ (Λ ^ 2 - mγ ^ 2) ^ 2 / 6 * C * (1 / (4 * M ^ 2)) := by gcongr
  · have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with v hv1 hv
    rw [uIoc_of_le zero_le_one] at hv
    have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩
    exact ((tendsto_combW_zero hm hM₀ (hMs v hvI) d).const_mul _).const_mul _

/-! ### Mass scaling -/

theorem combKern_zero_scale {m : ℝ} (hm : 0 < m) (Ms : Fin (3 + 2) → ℝ) (d : Fin 2)
    (z : ℝ × ℝ) :
    combKern m 0 Ms d z = (m ^ 6)⁻¹ * combKern 1 0 (fun i => Ms i / m) d z := by
  have hm0 : m ≠ 0 := hm.ne'
  have hk : ∀ M, kDen m M 0 z = m ^ 2 * kDen 1 (M / m) 0 z := fun M => by
    unfold kDen kC
    field_simp
    ring
  have hc : kC m 0 z = m ^ 2 * kC 1 0 z := by
    unfold kC
    ring
  have hP : ∏ i, kDen m (Ms i) 0 z = m ^ 10 * ∏ i, kDen 1 (Ms i / m) 0 z := by
    rw [Finset.prod_congr rfl fun i _ => hk (Ms i), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hS : ∑ i, (kDen m (Ms i) 0 z)⁻¹ = (m ^ 2)⁻¹ * ∑ i, (kDen 1 (Ms i / m) 0 z)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hk, mul_inv]
  unfold combKern undKernJ dblKernJ dblKernA dblKernB
  rw [hP, hS, hc]
  generalize ∏ i, kDen 1 (Ms i / m) 0 z = P
  generalize ∑ i, (kDen 1 (Ms i / m) 0 z)⁻¹ = S
  generalize kC 1 0 z = c
  simp only [show 3 + 2 - 2 = 3 from rfl, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  field_simp

theorem combW_zero_scale {m : ℝ} (hm : 0 < m) (Ms : Fin (3 + 2) → ℝ) (d : Fin 2) :
    combW m 0 Ms d = (m ^ 6)⁻¹ * combW 1 0 (fun i => Ms i / m) d := by
  unfold combW
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun z => combKern_zero_scale hm Ms d z)

theorem specMass_div {m : ℝ} (hm : 0 < m) (M v : ℝ) :
    QED.TwoLoop.VPHalf.specMass M v / m = QED.TwoLoop.VPHalf.specMass (M / m) v := by
  unfold QED.TwoLoop.VPHalf.specMass
  rw [show 4 * (M / m) ^ 2 / (1 - v ^ 2) = 4 * M ^ 2 / (1 - v ^ 2) / m ^ 2 by
      field_simp, Real.sqrt_div' _ (sq_nonneg m), Real.sqrt_sq hm.le]

/-- **Mass scaling of the spectral side at `q² = 0`**: in units of `m`. -/
theorem specFlavourW_zero_scale {m : ℝ} (hm : 0 < m) (M mγ Λ : ℝ) (d : Fin 2) :
    specFlavourW m M mγ Λ 0 d = (m ^ 2)⁻¹ * specFlavourW 1 (M / m) (mγ / m) (Λ / m) 0 d := by
  unfold specFlavourW
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  have hs : (fun i => specMs mγ Λ (QED.TwoLoop.VPHalf.specMass M v) i / m) =
      specMs (mγ / m) (Λ / m) (QED.TwoLoop.VPHalf.specMass (M / m) v) := by
    funext i
    fin_cases i <;> simp [specMs, specMass_div hm]
  rw [combW_zero_scale hm, hs]
  field_simp

/-- **The spectral side at `q² = 0` is `vpFlavourW` in units of `m`.** -/
theorem specFlavourW_zero_eq {m M mγ Λ : ℝ} (hm : 0 < m) (hM : 0 < M) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (d : Fin 2) :
    specFlavourW m M mγ Λ 0 d =
      (m ^ 2)⁻¹ * QED.ChainProof.SetCRegDisp.vpFlavourW (M / m) (mγ / m) (Λ / m) := by
  rw [specFlavourW_zero_scale hm, specFlavourW_one_zero (div_pos hM hm) (div_pos hmγ hm)
    (div_pos hΛ hm)]

end QED.ChainProof.CtLoB

end
