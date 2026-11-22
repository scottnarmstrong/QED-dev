/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKGen

/-!
# Set (c), the bubble classes: dispersive limits with their values

Helper level for the open link `QED.ChainProof.SetCMainB.MainBKKLinkP`, which needs the limit of
the longitudinal dispersive part in explicit form. `KKVal w H` strengthens
`QED.ChainProof.SetCMainB.KKLim w H`: besides the two stages of (T₉) for the `x`-integral, at
every `x ∈ (0, 1)` the integrand `H_ε(x, ·)` is integrable in both stages, the joint integral
commutes with the `x`-integral, the values are bounded uniformly in `x` and `ε ∈ (0, 1]` and have
`ε → 0⁺` limits. Then the limit of the `x`-integral is the `x`-integral of the pointwise limits.

* `KKVal`, `KKVal.toKKLim`, **`KKVal.tendsto`**: the limit `∫₀¹ w(x) lim_ε J(H_ε(x, ·)) dx`;
* `KKVal.add`, `KKVal.coef` (a coefficient with a limit, bounded on `(0, 1]`),
  `KKVal.const_mul`, `KKVal.congr`;
* **`kkVal_kkInt`**: every graph with the spectral line is one.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCUnitM
open QED.Integration.TwoLoop (symanzikU symanzikV LoopQuartic NoSubdivergenceRefined
  RefinedBound jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)

/-- The pointwise `ε → 0⁺` limit of the joint integral of `H_ε(x, ·)`. -/
noncomputable def kkLimX (H : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) (x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)

/-- **A family with a dispersive limit and its value.** -/
def KKVal (w : ℝ → ℂ) (H : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop :=
  IntegrableOn w (Ioo 0 1) ∧
    (∀ ε : ℝ, 0 < ε → ∀ ℓ, IntegrableOn (fun x => w x * H ε x ℓ) (Ioo 0 1)) ∧
    (∀ ε : ℝ, 0 < ε → QED.TwoLoop.jointEnergyFirstIntegrable 2
      (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, QED.TwoLoop.jointEnergyFirstIntegrable 2 (H ε x)) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → QED.TwoLoop.jointEnergyFirstIntegral 2
      (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ) =
        ∫ x in Ioo (0 : ℝ) 1, w x * QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)) ∧
    (∀ ε : ℝ, 0 < ε → AEStronglyMeasurable
      (fun x => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)) (volume.restrict (Ioo 0 1))) ∧
    (∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x ∈ Ioo (0 : ℝ) 1,
      ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)‖ ≤ C) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∃ L : ℂ,
      Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)) (𝓝[>] 0) (𝓝 L))

namespace KKVal

variable {w : ℝ → ℂ} {H H₁ H₂ : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem tendsto_limX (h : KKVal w H) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)) (𝓝[>] 0)
      (𝓝 (kkLimX H x)) :=
  tendsto_nhds_limUnder (h.2.2.2.2.2.2.2 x hx)

/-- At `ε ∈ (0, 1]` the weighted values are integrable in `x`. -/
theorem integrableOn_val (h : KKVal w H) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (fun x => w x * QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x)) (Ioo 0 1) := by
  obtain ⟨hw, -, -, -, -, hM, ⟨C, hC⟩, -⟩ := h
  refine (hw.norm.mul_const C).mono' (hw.aestronglyMeasurable.mul (hM ε hε))
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC ε hε hε1 x hx) (norm_nonneg _)

/-- **The limit of the `x`-integral** is the `x`-integral of the pointwise limits
(dominated convergence). -/
theorem tendsto (h : KKVal w H) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ)) (𝓝[>] 0)
      (𝓝 (∫ x in Ioo (0 : ℝ) 1, w x * kkLimX H x)) := by
  have h' := h
  obtain ⟨hw, -, -, -, hF, hM, ⟨C, hC⟩, -⟩ := h
  refine (tendsto_integral_filter_of_dominated_convergence
    (F := fun ε x => w x * QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x))
    (fun x => ‖w x‖ * C) ?_ ?_
    (hw.norm.mul_const _) ?_).congr' ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hw.aestronglyMeasurable.mul (hM ε hε)
  · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC ε hε.1 hε.2 x hx) (norm_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    exact (h'.tendsto_limX hx).const_mul (w x)
  · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
    exact (hF ε hε.1 hε.2).symm

theorem toKKLim (h : KKVal w H) : KKLim w H :=
  ⟨h.2.1, h.2.2.1, _, h.tendsto⟩

theorem add (h₁ : KKVal w H₁) (h₂ : KKVal w H₂) :
    KKVal w (fun ε x ℓ => H₁ ε x ℓ + H₂ ε x ℓ) := by
  obtain ⟨i₁, j₁, Y₁, -⟩ := h₁.toKKLim
  obtain ⟨i₂, j₂, Y₂, -⟩ := h₂.toKKLim
  have hK := h₁.toKKLim.add h₂.toKKLim
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨hw, -, -, e₁, f₁, m₁, ⟨C₁, b₁⟩, l₁⟩ := h₁
  obtain ⟨-, -, -, e₂, f₂, m₂, ⟨C₂, b₂⟩, l₂⟩ := h₂
  have hJ : ∀ ε, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1,
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => H₁ ε x ℓ + H₂ ε x ℓ) =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (H₁ ε x) +
          QED.TwoLoop.jointEnergyFirstIntegral 2 (H₂ ε x) := fun ε hε x hx =>
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (e₁ ε hε x hx) (e₂ ε hε x hx)
  refine ⟨hw, hK.1, hK.2.1, fun ε hε x hx =>
    QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add (e₁ ε hε x hx) (e₂ ε hε x hx),
    fun ε hε hε1 => ?_, fun ε hε => ?_, ⟨C₁ + C₂, fun ε hε hε1 x hx => ?_⟩, fun x hx => ?_⟩
  · have e : (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * (H₁ ε x ℓ + H₂ ε x ℓ)) = fun ℓ =>
        (∫ x in Ioo (0 : ℝ) 1, w x * H₁ ε x ℓ) + ∫ x in Ioo (0 : ℝ) 1, w x * H₂ ε x ℓ :=
      funext fun ℓ => by simp_rw [mul_add]; exact integral_add (i₁ ε hε ℓ) (i₂ ε hε ℓ)
    rw [e, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (j₁ ε hε) (j₂ ε hε),
      f₁ ε hε hε1, f₂ ε hε hε1, ← integral_add (h₁'.integrableOn_val hε hε1)
        (h₂'.integrableOn_val hε hε1)]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [hJ ε hε x hx, mul_add]
  · exact ((m₁ ε hε).add (m₂ ε hε)).congr ((ae_restrict_iff' measurableSet_Ioo).2
      (ae_of_all _ fun x hx => (hJ ε hε x hx).symm))
  · rw [hJ ε hε x hx]
    exact (norm_add_le _ _).trans (add_le_add (b₁ ε hε hε1 x hx) (b₂ ε hε hε1 x hx))
  · obtain ⟨L₁, hL₁⟩ := l₁ x hx
    obtain ⟨L₂, hL₂⟩ := l₂ x hx
    refine ⟨L₁ + L₂, (hL₁.add hL₂).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (hJ ε hε x hx).symm

/-- A coefficient with an `ε → 0⁺` limit, bounded on `(0, 1]`. -/
theorem coef (a : ℝ → ℂ) {a₀ : ℂ} (ha : Tendsto a (𝓝[>] 0) (𝓝 a₀)) {A : ℝ}
    (hA : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖a ε‖ ≤ A) (h : KKVal w H) :
    KKVal w (fun ε x ℓ => a ε * H ε x ℓ) := by
  have hK := h.toKKLim.coef a ha
  have h' := h
  obtain ⟨hw, i, j, e, f, m, ⟨C, b⟩, l⟩ := h
  have hJ : ∀ ε x, QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => a ε * H ε x ℓ) =
      a ε * QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x) := fun ε x =>
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul _ _
  refine ⟨hw, hK.1, hK.2.1, fun ε hε x hx =>
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ (e ε hε x hx),
    fun ε hε hε1 => ?_, fun ε hε => ?_, ⟨|A| * |C|, fun ε hε hε1 x hx => ?_⟩, fun x hx => ?_⟩
  · have e' : (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * (a ε * H ε x ℓ)) =
        fun ℓ => a ε * ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ := funext fun ℓ => by
      simp_rw [mul_left_comm (w _)]; exact integral_const_mul _ _
    rw [e', QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul, f ε hε hε1,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp only [hJ]
    ring
  · simp only [hJ]
    exact (m ε hε).const_mul (a ε)
  · rw [hJ, norm_mul]
    exact mul_le_mul ((hA ε hε hε1).trans (le_abs_self A)) ((b ε hε hε1 x hx).trans
      (le_abs_self C)) (norm_nonneg _) (abs_nonneg _)
  · obtain ⟨L, hL⟩ := l x hx
    exact ⟨a₀ * L, (ha.mul hL).congr fun ε => (hJ ε x).symm⟩

theorem const_mul (c : ℂ) (h : KKVal w H) : KKVal w (fun ε x ℓ => c * H ε x ℓ) :=
  coef (fun _ => c) tendsto_const_nhds (A := ‖c‖) (fun _ _ _ => le_rfl) h

theorem congr (h : KKVal w H)
    (hH : ∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ℓ, H ε x ℓ = H₁ ε x ℓ) : KKVal w H₁ := by
  have hK := h.toKKLim.congr hH
  have hF : ∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, H ε x = H₁ ε x := fun ε hε x hx =>
    funext (hH ε hε x hx)
  obtain ⟨hw, -, -, e, f, m, ⟨C, b⟩, l⟩ := h
  refine ⟨hw, hK.1, hK.2.1, fun ε hε x hx => hF ε hε x hx ▸ e ε hε x hx, fun ε hε hε1 => ?_,
    fun ε hε => ?_, ⟨C, fun ε hε hε1 x hx => hF ε hε x hx ▸ b ε hε hε1 x hx⟩, fun x hx => ?_⟩
  · have e' : (fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H₁ ε x ℓ) =
        fun ℓ => ∫ x in Ioo (0 : ℝ) 1, w x * H ε x ℓ := funext fun ℓ =>
      setIntegral_congr_fun measurableSet_Ioo fun x hx => by simp only [hH ε hε x hx ℓ]
    rw [e', f ε hε hε1]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [hF ε hε x hx]
  · exact (m ε hε).congr ((ae_restrict_iff' measurableSet_Ioo).2
      (ae_of_all _ fun x hx => by simp only [hF ε hε x hx]))
  · obtain ⟨L, hL⟩ := l x hx
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [hF ε hε x hx]

end KKVal

section Term

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {p : Fin (m + 1) → Fin 4 → ℝ} {j₀ : Fin (m + 1)}
  {Q : LoopQuartic} {M : Fin (m + 1) → ℝ} {kx : ℝ → ℝ} {E : Finset (Fin (m + 1))}

/-- **A graph with the spectral line has a dispersive limit with its value**, under the
hypotheses of `QED.ChainProof.SetCMainB.kkLim_kkInt`. -/
theorem kkVal_kkInt (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) (hE : E.card + 4 ≤ m + 1) (hj₀ : j₀ ∉ E)
    {μ₀ c : ℝ} (hμ₀ : 0 < μ₀) (hc : 0 < c) (hcμ : c ≤ μ₀ ^ 2) (hM0 : μ₀ ≤ M j₀)
    (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
    (hkx : Continuous kx) (hkx01 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < kx x ∧ kx x ≤ 1)
    {t : ℝ} (ht : μ₀ ≤ t) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    KKVal w (fun ε x ℓ => kkInt α p j₀ Q M (kx x) t ε ℓ) := by
  have ht0 : 0 < t := hμ₀.trans_le ht
  have hK := kkLim_kkInt hm hcrit hB hE hj₀ hμ₀ hc hcμ hM0 hV hkx hkx01 ht hw
  obtain ⟨C, hC⟩ := exists_norm_kkInt_le hm hcrit hB hμ₀ hc hM0 hV hj₀ ht
  refine ⟨hw, hK.1, hK.2.1, fun ε hε x hx => ?_, fun ε hε _ =>
    (jointEnergyFirstIntegral_setIntegral_kkInt hm hcrit hB hj₀ hkx hkx01 hE ht0 hε hw).2,
    fun ε hε => (stronglyMeasurable_jointEnergyFirstIntegral
      (continuous_kkInt hkx t hε.ne')).aestronglyMeasurable,
    ⟨C, fun ε hε _ x hx => hC _ ε (hkx01 x hx).1 (hkx01 x hx).2 hε⟩,
    fun x hx => tendsto_kkInt hm hcrit hB hμ₀ hc hM0 hV hcμ (hkx01 x hx).1 (hkx01 x hx).2 ht⟩
  exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q _ _ _
    (by omega) hε (kk_crit hcrit (hkx01 x hx).1.ne') (kk_bound hB (kkSig_succ _))

end Term

end QED.ChainProof.SetCMainB

end
