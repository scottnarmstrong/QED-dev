/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVANode

/-!
# Set (a), stage D: the photon-mass integral of the `VA` class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). The cutoff photon-mass
integral of the nested `VA` integral is swapped with the outer node integral: the integrand
`x⁻¹ ∫_σ ksDYA` is dominated by `Ka · x⁻¹ ∫_σ ksDLin(·, 1, 1)` (`|a₀| + |a₁| ≤ Ka`), which is
nonnegative, and whose photon-mass integral is the node difference with moments `(1, 1)`,
bounded by `C (1 + x^{-1/2} + (1 - x)^{-1/2})` (`ksU_abs_ksUNodeD_le`). So for `Λ ≥ 0`

  `∫_{(0, Λ]} ksDNestA Φ u s du = ∫_{x ∈ (0, 1)} ∑_f c_f ∫_{σ ∈ (0, 1)} ksUDA (m_f) s Λ x σ`,

`ksUDA M s Λ x σ = ksUPhi(ksDb M Λ x) - ksUPhi(ksDb M 0 x)` at the node's moments. No `a → 0`
limit is needed: the node slope at `u = 0` is `b₀ = M²x/(1 - x) > 0`.

Main results:

* `ksU_integrable_ksUH`: the dominating function is integrable on `(0, Λ] × (0, 1)`;
* `ksU_integrable_ksUh`: so is the `VA` integrand of one flavour;
* **`ksU_integral_ksDNestA`**: the interchange for the flavour sum, with the integrability of
  `u ↦ ksDNestA Φ u s` on `(0, Λ]` and of each flavour's node integral on `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open QED.GradedProof.RPi4 (decCfg)

namespace QED.ChainProof.SetAKS

/-- The photon-mass difference of the `VA` antiderivative at the node `(x, σ)`. -/
noncomputable def ksUDA (M s Λ x σ : ℝ) : ℝ := ksUNodeD M s x (ksDa0 M x s σ) (ksDa1 x σ) Λ σ

/-- The `σ`-integrated `VA` integrand `x⁻¹ ∫_σ ksDLin` with moment functions `α`, `β`. -/
noncomputable def ksUh (M s : ℝ) (α β : ℝ → ℝ → ℝ) (u x : ℝ) : ℝ :=
  x⁻¹ * ∫ σ in Ioo (0 : ℝ) 1, ksDLin (ksDA M s σ) (ksDb M u x) (1 - σ) (α x σ) (β x σ)

/-- The moment bound `Ka = 16(4M² + |s|) + 8 ≥ |a₀| + |a₁|`. -/
noncomputable def ksUKa (M s : ℝ) : ℝ := 16 * (4 * M ^ 2 + |s|) + 8

theorem ksU_moments_le {M x s σ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    |ksDa0 M x s σ| + |ksDa1 x σ| ≤ ksUKa M s := by
  have := ksU_abs_ksDa0_le (M := M) (s := s) hx hσ
  have := ksU_abs_ksDa1_le hx hσ
  unfold ksUKa
  linarith

theorem ksU_measurable_ksUh {M s : ℝ} {α β : ℝ → ℝ → ℝ}
    (hα : Measurable (Function.uncurry α)) (hβ : Measurable (Function.uncurry β)) :
    Measurable fun p : ℝ × ℝ => ksUh M s α β p.1 p.2 := by
  have hf : Measurable fun q : (ℝ × ℝ) × ℝ =>
      ksDLin (ksDA M s q.2) (ksDb M q.1.1 q.1.2) (1 - q.2) (α q.1.2 q.2) (β q.1.2 q.2) :=
    ksU_measurable_ksDLin (by unfold ksDA; fun_prop) (by unfold ksDb; fun_prop) (by fun_prop)
      (hα.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2)))
      (hβ.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2)))
  exact (measurable_snd.inv).mul
    (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

/-- At a fixed outer node `x`, `u ↦ ksUh` is integrable on `(0, Λ]` with integral the
`σ`-integral of the node difference. -/
theorem ksU_ksUh_slice {M s x Λ K : ℝ} {α β : ℝ → ℝ → ℝ} (hM : 0 < M)
    (hs : -(4 * M ^ 2) < s) (hx : x ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ)
    (hα : Measurable (α x)) (hβ : Measurable (β x))
    (hK : ∀ σ ∈ Icc (0 : ℝ) 1, |α x σ| + |β x σ| ≤ K) :
    IntegrableOn (fun u => ksUh M s α β u x) (Ioc (0 : ℝ) Λ) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksUh M s α β u x =
        ∫ σ in Ioo (0 : ℝ) 1, ksUNodeD M s x (α x σ) (β x σ) Λ σ := by
  have heq : (fun u => ksUh M s α β u x) =
      fun u => ∫ σ in Ioo (0 : ℝ) 1, ksUNodeF M s x (α x) (β x) u σ := by
    funext u
    simp only [ksUh, ksUNodeF, MeasureTheory.integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact (ksU_integrable_ksUNodeF (Λ := Λ) hM hs hx hα hβ hK).integral_prod_left
  · rw [heq]
    exact ksU_node_swap hM hs hx hΛ hα hβ hK

/-- **The dominating function is integrable**: `x⁻¹ ∫_σ ksDLin(·, 1, 1)` on `(0, Λ] × (0, 1)`. -/
theorem ksU_integrable_ksUH {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hΛ : 0 ≤ Λ) :
    Integrable (fun p : ℝ × ℝ => ksUh M s (fun _ _ => 1) (fun _ _ => 1) p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hmeas := ksU_measurable_ksUh (M := M) (s := s) (α := fun _ _ => 1) (β := fun _ _ => 1)
    measurable_const measurable_const
  have hK : ∀ σ ∈ Icc (0 : ℝ) 1, |(fun (_ _ : ℝ) => (1 : ℝ)) 0 σ| +
      |(fun (_ _ : ℝ) => (1 : ℝ)) 0 σ| ≤ 2 := fun σ _ => by norm_num
  set C := 160 * (|(1 : ℝ)| + |(1 : ℝ)|) * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 *
    (2 + 2 * M + Real.sqrt Λ) with hC
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
    (ksU_ksUh_slice hM hs hx hΛ measurable_const measurable_const (K := 2)
      (fun σ _ => by norm_num)).1, ?_⟩
  refine Integrable.mono' (g := fun x => C * ksUg x) (ksU_integrableOn_ksUg.const_mul C)
    (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
  obtain ⟨-, hval⟩ := ksU_ksUh_slice (Λ := Λ) hM hs hx hΛ (α := fun _ _ => 1)
    (β := fun _ _ => 1) measurable_const measurable_const (K := 2) (fun σ _ => by norm_num)
  have hnn : ∀ u ∈ Ioc (0 : ℝ) Λ,
      ‖ksUh M s (fun _ _ => 1) (fun _ _ => 1) u x‖ =
        ksUh M s (fun _ _ => 1) (fun _ _ => 1) u x := fun u hu => by
    refine Real.norm_of_nonneg (mul_nonneg (inv_pos.2 hx.1).le
      (setIntegral_nonneg measurableSet_Ioo fun σ hσ => ?_))
    exact ksU_ksDLin_nonneg (ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hσ))
      (ksU_ksDb_pos hM hx hu.1.le) (by linarith [hσ.2]) zero_le_one zero_le_one
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
    setIntegral_congr_fun measurableSet_Ioc hnn, hval]
  have hint := ksU_integrableOn_ksUNodeD (Λ := Λ) hM hs hx hΛ (α := fun _ => 1)
    (β := fun _ => 1) measurable_const measurable_const (K := 2) (fun σ _ => by norm_num)
  calc ∫ σ in Ioo (0 : ℝ) 1, ksUNodeD M s x 1 1 Λ σ
      ≤ ∫ σ in Ioo (0 : ℝ) 1, C * ksUg x :=
        setIntegral_mono_on hint
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioo fun σ hσ =>
          (le_abs_self _).trans (ksU_abs_ksUNodeD_le 1 1 hM hs hx hσ hΛ)
    _ = C * ksUg x := by simp

/-- **The `VA` integrand of one flavour is integrable** on `(0, Λ] × (0, 1)`. -/
theorem ksU_integrable_ksUh {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hΛ : 0 ≤ Λ) :
    Integrable (fun p : ℝ × ℝ => ksUh M s (fun x σ => ksDa0 M x s σ) ksDa1 p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hmeas := ksU_measurable_ksUh (M := M) (s := s) (α := fun x σ => ksDa0 M x s σ)
    (β := ksDa1) (by unfold Function.uncurry ksDa0; fun_prop)
    (by unfold Function.uncurry ksDa1; fun_prop)
  refine Integrable.mono' ((ksU_integrable_ksUH hM hs hΛ).const_mul (ksUKa M s))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ksU_ae_mem_prod] with p hp
  obtain ⟨⟨hu0, -⟩, hx⟩ := hp
  have hxI : p.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hb := ksU_ksDb_pos hM hx hu0.le
  have hkA := ksU_ksUkA_pos hM hs
  have hL11 : Integrable (fun σ => ksDLin (ksDA M s σ) (ksDb M p.1 p.2) (1 - σ) 1 1)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine Integrable.of_bound (ksU_measurable_ksDLin (by unfold ksDA; fun_prop)
      measurable_const (by fun_prop) measurable_const measurable_const).aestronglyMeasurable
      ((1 + (ksUkA M s)⁻¹) ^ 2) (ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_)
    have hσI : σ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hσ
    have hA := ksD_ksDA_pos hM hs hσI
    have hAi : (ksDA M s σ)⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
    rw [Real.norm_of_nonneg (ksU_ksDLin_nonneg hA hb (by linarith [hσ.2]) zero_le_one
      zero_le_one)]
    exact (ksU_ksDLin_one_one_le hA hb (by linarith [hσ.2]) (by linarith [hσ.1])).trans
      (pow_le_pow_left₀ (by have := inv_pos.2 hA; positivity) (by linarith) 2)
  have hx0 : 0 < p.2 := hx.1
  simp only [ksUh, norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hx0]
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hx0).le
  rw [← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hL11.const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_)
  have hσI : σ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hσ
  have hA := ksD_ksDA_pos hM hs hσI
  have hY : 0 ≤ 1 - σ := by linarith [hσ.2]
  rw [Real.norm_eq_abs]
  exact (ksU_abs_ksDLin_le _ _ hA hb hY).trans (mul_le_mul_of_nonneg_right
    (ksU_moments_le hxI hσI) (ksU_ksDLin_nonneg hA hb hY zero_le_one zero_le_one))

theorem ksU_ksUh_slice_VA {M s x Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksUh M s (fun x σ => ksDa0 M x s σ) ksDa1 u x) (Ioc (0 : ℝ) Λ) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksUh M s (fun x σ => ksDa0 M x s σ) ksDa1 u x =
        ∫ σ in Ioo (0 : ℝ) 1, ksUDA M s Λ x σ :=
  ksU_ksUh_slice hM hs hx hΛ (by unfold ksDa0; fun_prop) (by unfold ksDa1; fun_prop)
    fun σ hσ => ksU_moments_le (Ioo_subset_Icc_self hx) hσ

/-- At `u > 0` the nested `VA` integral is the flavour sum of the `ksUh`. -/
theorem ksU_ksDNestA_eq {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {u s : ℝ}
    (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s) (hu : 0 < u) :
    ksDNestA Φ u s = ∫ x in Ioo (0 : ℝ) 1,
      ∑ f, Φ.coeff f * ksUh (Φ.mass f) s (fun x σ => ksDa0 (Φ.mass f) x s σ) ksDa1 u x := by
  rw [ksD_ksDNestA Φ hM hs hu]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [intervalIntegral.integral_finsetSum fun f _ =>
      ((ksD_continuousOn_ksDYA (hM f) (hs f) hx hu).intervalIntegrable_of_Icc
        zero_le_one).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  simp only [ksUh, ksDYA]
  ring

/-- **The photon-mass integral of the `VA` class**: for flavours of positive mass, `s` above
every threshold and `Λ ≥ 0`, `u ↦ ksDNestA Φ u s` is integrable on `(0, Λ]`, every flavour's
node integral `x ↦ ∫_σ ksUDA` is integrable on `(0, 1)`, and
`∫_{(0, Λ]} ksDNestA Φ u s = ∫_{(0, 1)} ∑_f c_f ∫_{(0, 1)} ksUDA (m_f) s Λ x σ dσ dx`. -/
theorem ksU_integral_ksDNestA {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {s Λ : ℝ}
    (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksDNestA Φ u s) (Ioc (0 : ℝ) Λ) ∧
      (∀ f, IntegrableOn (fun x => ∫ σ in Ioo (0 : ℝ) 1, ksUDA (Φ.mass f) s Λ x σ)
        (Ioo (0 : ℝ) 1)) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksDNestA Φ u s = ∫ x in Ioo (0 : ℝ) 1,
        ∑ f, Φ.coeff f * ∫ σ in Ioo (0 : ℝ) 1, ksUDA (Φ.mass f) s Λ x σ := by
  set h : F → ℝ → ℝ → ℝ := fun f u x =>
    ksUh (Φ.mass f) s (fun x σ => ksDa0 (Φ.mass f) x s σ) ksDa1 u x with hh
  have hint : ∀ f, Integrable (fun p : ℝ × ℝ => h f p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    fun f => ksU_integrable_ksUh (hM f) (hs f) hΛ
  have hG : Integrable (Function.uncurry fun u x => ∑ f, Φ.coeff f * h f u x)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    integrable_finsetSum _ fun f _ => (hint f).const_mul (Φ.coeff f)
  have hL : EqOn (fun u => ksDNestA Φ u s)
      (fun u => ∫ x in Ioo (0 : ℝ) 1, ∑ f, Φ.coeff f * h f u x) (Ioc (0 : ℝ) Λ) :=
    fun u hu => ksU_ksDNestA_eq Φ hM hs hu.1
  refine ⟨?_, fun f => ?_, ?_⟩
  · exact IntegrableOn.congr_fun hG.integral_prod_left hL.symm measurableSet_Ioc
  · refine IntegrableOn.congr_fun (hint f).integral_prod_right (fun x hx => ?_)
      measurableSet_Ioo
    exact (ksU_ksUh_slice_VA (hM f) (hs f) hx hΛ).2
  · rw [setIntegral_congr_fun measurableSet_Ioc hL, integral_integral_swap hG]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [integral_finsetSum _ fun f _ =>
      ((ksU_ksUh_slice_VA (hM f) (hs f) hx hΛ).1).const_mul (Φ.coeff f)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [MeasureTheory.integral_const_mul, (ksU_ksUh_slice_VA (hM f) (hs f) hx hΛ).2]

/-- The same at the configuration `decCfg μ x`, for `s > -4μ²`. -/
theorem ksU_integral_ksDNestA_cfg {μ x s Λ : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksDNestA (decCfg μ x) u s) (Ioc (0 : ℝ) Λ) ∧
      (∀ f, IntegrableOn (fun x' => ∫ σ in Ioo (0 : ℝ) 1,
        ksUDA ((decCfg μ x).mass f) s Λ x' σ) (Ioo (0 : ℝ) 1)) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksDNestA (decCfg μ x) u s = ∫ x' in Ioo (0 : ℝ) 1,
        ∑ f, (decCfg μ x).coeff f * ∫ σ in Ioo (0 : ℝ) 1,
          ksUDA ((decCfg μ x).mass f) s Λ x' σ := by
  refine ksU_integral_ksDNestA _ (fun f => hμ.trans_le (ksK_mass hμ hx f)) (fun f => ?_) hΛ
  have h := ksK_mass hμ hx f
  nlinarith

end QED.ChainProof.SetAKS

end
