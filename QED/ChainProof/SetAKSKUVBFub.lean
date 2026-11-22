/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBBnd

/-!
# Set (a), stage D: the photon-mass integral of the `VB` class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). In the coordinates `(ρ, β)`
of the inner vertex (`SetAKSKUVBCov`) the nested `VB` integral is
`ksDNestB Φ u s = ∫_{(0,1)²} ∑_f c_f ∫_w ksDYB`, and its cutoff photon-mass integral is
swapped with the node integrals: the integrand is dominated by the `VB` integrand with absolute
coefficients, whose photon-mass integral `ksUDBa` is at most `C ksUg ρ`. So for `Λ ≥ 0`

  `∫_{(0, Λ]} ksDNestB Φ u s du = ∫_{(0,1)²} ∑_f c_f ∫_{w ∈ (0, 1)} ksUDB (m_f) s Λ ρ β w`,

`ksUDB = ρ (Ψ(b₀ + Λ/ρ) - Ψ(b₀))` the node difference of the antiderivative `ksUPsiB`.

Main results:

* `ksU_nodeB_swap`: the interchange at a fixed node `(ρ, β)`;
* `ksU_ksUDBa_le`: the node bound;
* **`ksU_integral_ksDNestB`** (and `_cfg`): the interchange for the flavour sum.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open QED.GradedProof.RPi4 (decCfg)

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint)

/-- `τ = x₂(1 - x₂)` at the node `(ρ, β)`. -/
noncomputable def ksUtB (ρ β : ℝ) : ℝ := ksUPtB ρ β 2 * (1 - ksUPtB ρ β 2)

theorem ksU_ksUtB_eq (ρ β : ℝ) : ksUtB ρ β = (1 - ρ) * ρ := by
  rw [ksUtB, ksU_ksUPtB_two]; simp [ksUPtB]

theorem ksU_ksUtB_pos {ρ β : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) : 0 < ksUtB ρ β := by
  rw [ksU_ksUtB_eq]; exact mul_pos (by linarith [hρ.2]) hρ.1

/-- The `VB` integrand at the node `(ρ, β, w)` with coefficient data `(c, E, H)`. -/
noncomputable def ksUgB (M s ρ β : ℝ) (c : ℝ → ℝ) (E H : ℝ → Fin 3 → ℝ) (u w : ℝ) : ℝ :=
  ksUYBg (ksDA M s w) (ksDbB M u (ksUPtB ρ β) s) (ksDYmax β w) (ksUtB ρ β) (c w) (E w) (H w)

/-- `ρ` times the node difference of the antiderivative, with coefficient data `(c, E, H)`. -/
noncomputable def ksUDg (M s Λ ρ β : ℝ) (c : ℝ → ℝ) (E H : ℝ → Fin 3 → ℝ) (w : ℝ) : ℝ :=
  ρ * (ksUPsiB (ksDA M s w) (ksDYmax β w) (ksUtB ρ β) (c w) (E w) (H w)
      (ksDbB M Λ (ksUPtB ρ β) s) -
    ksUPsiB (ksDA M s w) (ksDYmax β w) (ksUtB ρ β) (c w) (E w) (H w) (ksDbB M 0 (ksUPtB ρ β) s))

/-- The `VB` coefficient data at `(ρ, β)`. -/
noncomputable def ksUcB (w : ℝ) : ℝ := 16 * w * (w - 1)

/-- The node difference of the `VB` class. -/
noncomputable def ksUDB (M s Λ ρ β w : ℝ) : ℝ :=
  ksUDg M s Λ ρ β ksUcB (ksDEc M (ksUPtB ρ β)) (ksDHc (ksUPtB ρ β)) w

/-- The same with absolute coefficients. -/
noncomputable def ksUDBa (M s Λ ρ β w : ℝ) : ℝ :=
  ksUDg M s Λ ρ β (fun w => |ksUcB w|) (fun w i => |ksDEc M (ksUPtB ρ β) w i|)
    (fun w i => |ksDHc (ksUPtB ρ β) w i|) w

theorem ksU_ksDYB_ptB {M s u ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ksDYB M u (ksUPtB ρ β) s w =
      ksUgB M s ρ β ksUcB (ksDEc M (ksUPtB ρ β)) (ksDHc (ksUPtB ρ β)) u w := by
  rw [ksU_ksDYB_eq, ksU_ksUPtB_beta' hρ]; rfl

/-! ### The interchange at a fixed node -/

section Node

variable {M s ρ β Λ K : ℝ} {c : ℝ → ℝ} {E H : ℝ → Fin 3 → ℝ}

theorem ksU_measurable_ksUgB (hc : Measurable c) (hE : ∀ i, Measurable fun w => E w i)
    (hH : ∀ i, Measurable fun w => H w i) :
    Measurable (Function.uncurry (ksUgB M s ρ β c E H)) := by
  have hA : Measurable fun z : ℝ × ℝ => ksDA M s z.2 := by unfold ksDA; fun_prop
  have hb : Measurable fun z : ℝ × ℝ => ksDbB M z.1 (ksUPtB ρ β) s := by
    unfold ksDbB ksNEB; fun_prop
  have hY : Measurable fun z : ℝ × ℝ => ksDYmax β z.2 := by unfold ksDYmax; fun_prop
  have J := ksU_measurable_J hA hb hY
  have hc' : Measurable fun z : ℝ × ℝ => c z.2 := hc.comp measurable_snd
  have hE' : ∀ i, Measurable fun z : ℝ × ℝ => E z.2 i := fun i => (hE i).comp measurable_snd
  have hH' : ∀ i, Measurable fun z : ℝ × ℝ => H z.2 i := fun i => (hH i).comp measurable_snd
  have J10 := (J 0).1; have J11 := (J 1).1; have J12 := (J 2).1; have J13 := (J 3).1
  have J21 := (J 1).2; have J22 := (J 2).2; have J23 := (J 3).2
  have E0 := hE' 0; have E1 := hE' 1; have E2 := hE' 2
  have H0 := hH' 0; have H1 := hH' 1; have H2 := hH' 2
  unfold Function.uncurry ksUgB ksUYBg
  fun_prop

theorem ksU_ae_mem_prod_B :
    ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))),
      p ∈ Ioc (0 : ℝ) Λ ×ˢ Ioo (0 : ℝ) 1 := ksU_ae_mem_prod

variable (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
  (hβ : β ∈ Ioo (0 : ℝ) 1) (hc : Measurable c) (hE : ∀ i, Measurable fun w => E w i)
  (hH : ∀ i, Measurable fun w => H w i)
  (hK : ∀ w ∈ Ioo (0 : ℝ) 1,
    |E w 0| + |E w 1| + |E w 2| + |H w 0| + |H w 1| + |H w 2| + |c w| ≤ K)
include hM hs hρ hβ hc hE hH hK

theorem ksU_integrable_ksUgB :
    Integrable (Function.uncurry (ksUgB M s ρ β c E H))
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  refine Integrable.of_bound (ksU_measurable_ksUgB hc hE hH).aestronglyMeasurable
    (((ksUtB ρ β)⁻¹ + 1) * K * (1 + (ksUkA M s)⁻¹) ^ 2) ?_
  filter_upwards [ksU_ae_mem_prod_B] with p hp
  obtain ⟨⟨hu0, -⟩, hw⟩ := hp
  have hwI : p.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hw
  have hA := ksD_ksDA_pos hM hs hwI
  have hb := ksU_ksDbB_ptB_pos hM hs hρ hβ hu0.le (u := p.1)
  have hτ := ksU_ksUtB_pos (β := β) hρ
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := p.2)
  rw [Real.norm_eq_abs]
  refine (ksU_abs_ksUYBg_le hA hb hY.le hτ).trans
    ((ksU_ksUYBa_le (ksU_ksUkA_pos hM hs) (ksU_kA_le_ksDA hwI) hb hY.le hY1 hτ).trans ?_)
  have := hK p.2 hw
  have : 0 ≤ (ksUtB ρ β)⁻¹ + 1 := by have := inv_pos.2 hτ; positivity
  gcongr

omit hc hE hH hK in
theorem ksU_integral_ksUgB_u {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) :
    ∫ u in Ioc (0 : ℝ) Λ, ksUgB M s ρ β c E H u w = ksUDg M s Λ ρ β c E H w := by
  have hwI : w ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hw
  rw [← intervalIntegral.integral_of_le hΛ]
  have hb₀ := ksU_ksDbB_zero_pos hM hs hρ hβ
  have h := ksU_integral_ksUYBg (Y := ksDYmax β w) (ksUtB ρ β) (c w) (E w) (H w)
    (ksD_ksDA_pos hM hs hwI) hb₀ hρ.1 (ksU_ksDYmax_pos hβ hw) hΛ
  simp only [ksUgB, ksUDg]
  rw [← ksU_ksDbB_ptB hρ] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [ksU_ksDbB_ptB hρ, ← mul_assoc, mul_inv_cancel₀ hρ.1.ne', one_mul]

/-- **The interchange at a fixed node `(ρ, β)`.** -/
theorem ksU_nodeB_swap (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ∫ w in Ioo (0 : ℝ) 1, ksUgB M s ρ β c E H u w) (Ioc (0 : ℝ) Λ) ∧
      IntegrableOn (ksUDg M s Λ ρ β c E H) (Ioo (0 : ℝ) 1) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ∫ w in Ioo (0 : ℝ) 1, ksUgB M s ρ β c E H u w =
        ∫ w in Ioo (0 : ℝ) 1, ksUDg M s Λ ρ β c E H w := by
  have hI := ksU_integrable_ksUgB (Λ := Λ) hM hs hρ hβ hc hE hH hK
  refine ⟨hI.integral_prod_left, ?_, ?_⟩
  · refine IntegrableOn.congr_fun hI.integral_prod_right (fun w hw => ?_) measurableSet_Ioo
    exact ksU_integral_ksUgB_u hM hs hρ hβ hw hΛ
  · rw [integral_integral_swap hI]
    exact setIntegral_congr_fun measurableSet_Ioo fun w hw =>
      ksU_integral_ksUgB_u hM hs hρ hβ hw hΛ

end Node

/-! ### The node bound -/

theorem ksU_measurable_ksUYBg {γ : Type*} [MeasurableSpace γ] {A b Y τ c : γ → ℝ}
    {E H : γ → Fin 3 → ℝ} (hA : Measurable A) (hb : Measurable b) (hY : Measurable Y)
    (hτ : Measurable τ) (hc : Measurable c) (hE : ∀ i, Measurable fun z => E z i)
    (hH : ∀ i, Measurable fun z => H z i) :
    Measurable fun z => ksUYBg (A z) (b z) (Y z) (τ z) (c z) (E z) (H z) := by
  have J := ksU_measurable_J hA hb hY
  have J10 := (J 0).1; have J11 := (J 1).1; have J12 := (J 2).1; have J13 := (J 3).1
  have J21 := (J 1).2; have J22 := (J 2).2; have J23 := (J 3).2
  have E0 := hE 0; have E1 := hE 1; have E2 := hE 2
  have H0 := hH 0; have H1 := hH 1; have H2 := hH 2
  unfold ksUYBg
  fun_prop

theorem ksU_abs_ksUcB_le {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) : |ksUcB w| ≤ 4 := by
  unfold ksUcB
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (w - 1 / 2), hw.1, hw.2]

theorem ksU_continuous_ksDEc (M : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    Continuous fun w => ksDEc M x w i := by
  fin_cases i <;> simp [ksDEc, ksDcv, ksDc0] <;> fun_prop

theorem ksU_continuous_ksDHc (x : Fin 3 → ℝ) (i : Fin 3) :
    Continuous fun w => ksDHc x w i := by
  fin_cases i <;> simp [ksDHc, ksDcv, ksDc0] <;> fun_prop

/-- The coefficient sum bound `KB` of the `VB` data. -/
noncomputable def ksUKs (M : ℝ) : ℝ := 3 * (5600 * M ^ 2) + 3 * 8000 + 4

theorem ksU_coef_sum_le {M ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    |ksDEc M (ksUPtB ρ β) w 0| + |ksDEc M (ksUPtB ρ β) w 1| + |ksDEc M (ksUPtB ρ β) w 2| +
      |ksDHc (ksUPtB ρ β) w 0| + |ksDHc (ksUPtB ρ β) w 1| + |ksDHc (ksUPtB ρ β) w 2| +
      |ksUcB w| ≤ ksUKs M := by
  have h0 := ksU_coef_le (M := M) hρ hβ hw 0
  have h1 := ksU_coef_le (M := M) hρ hβ hw 1
  have h2 := ksU_coef_le (M := M) hρ hβ hw 2
  have := ksU_abs_ksUcB_le hw
  unfold ksUKs
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- **The node bound**: `ksUDBa ≤ C ksUg ρ` on the open cube. -/
theorem ksU_ksUDBa_le {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hΛ : 0 ≤ Λ) :
    ∃ C, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      ksUDBa M s Λ ρ β w ≤ C * ksUg ρ := by
  set kA := ksUkA M s
  have hkA : 0 < kA := ksU_ksUkA_pos hM hs
  set KG := 5600 * M ^ 2 + 8000 * (M ^ 2 + |s|) with hKG
  set Kb := M ^ 2 + |s| with hKb
  refine ⟨3 * KG * (4 * kA⁻¹) + 12000 * (4 * Real.sqrt (Λ / kA)) +
    4 * (18 + 16 * Real.sqrt (Kb / kA) + 16 * Real.sqrt (Λ / kA)), fun ρ hρ β hβ w hw => ?_⟩
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hwI : w ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hw
  have hβI : β ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hβ
  set A := ksDA M s w
  have hA := ksD_ksDA_pos hM hs hwI
  have hkAA : kA ≤ A := ksU_kA_le_ksDA hwI
  have hAle : A ≤ M ^ 2 + |s| := ksU_ksDA_le hwI
  set Y := ksDYmax β w
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 : Y ≤ 1 := ksU_ksDYmax_le_one hβ
  set b₀ := ksDbB M 0 (ksUPtB ρ β) s with hb₀d
  have hb₀e : b₀ = ρ * ksDA M s β / (1 - ρ) := ksU_ksDbB_zero_ptB ⟨r0, r1⟩
  have hb₀ : 0 < b₀ := ksU_ksDbB_zero_pos hM hs ⟨r0, r1⟩ hβ
  have hb₀lo : ρ * kA / (1 - ρ) ≤ b₀ := by
    rw [hb₀e]; gcongr; exact ksU_kA_le_ksDA hβI
  have hb₀hi : b₀ ≤ Kb / (1 - ρ) := by
    rw [hb₀e]
    have := ksU_ksDA_le (M := M) (s := s) hβI
    have := (ksD_ksDA_pos hM hs hβI).le
    rw [div_le_div_iff_of_pos_right h1]
    nlinarith
  have hB : ksDbB M Λ (ksUPtB ρ β) s = b₀ + Λ / ρ := ksU_ksDbB_ptB ⟨r0, r1⟩
  set Ea := fun i => |ksDEc M (ksUPtB ρ β) w i|
  set Ha := fun i => |ksDHc (ksUPtB ρ β) w i|
  have hcoef := fun i => ksU_coef_le (M := M) ⟨r0, r1⟩ hβ hw i
  have hτ : ksUtB ρ β = (1 - ρ) * ρ := ksU_ksUtB_eq ρ β
  -- the moment part
  have hG : ∀ i : Fin 3, |ksUGc A Ea Ha i| ≤ KG := fun i => by
    have hE := (hcoef i).1
    have hH := (hcoef i).2
    unfold ksUGc
    have hd : 0 < 2 * (((i : ℕ) : ℝ) + 1) := by positivity
    have hd1 : 1 ≤ 2 * (((i : ℕ) : ℝ) + 1) := by
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hq : |Ha i * A / (2 * (((i : ℕ) : ℝ) + 1))| ≤ 8000 * (M ^ 2 + |s|) := by
      rw [abs_div, abs_mul, abs_abs, abs_of_pos hA, abs_of_pos hd, div_le_iff₀ hd]
      have h8 : |ksDHc (ksUPtB ρ β) w i| * A ≤ 8000 * (M ^ 2 + |s|) :=
        mul_le_mul hH hAle hA.le (by norm_num)
      nlinarith [abs_nonneg (ksDHc (ksUPtB ρ β) w i), mul_nonneg (abs_nonneg
        (ksDHc (ksUPtB ρ β) w i)) hA.le, abs_nonneg s]
    have := abs_sub (Ea i) (Ha i * A / (2 * (((i : ℕ) : ℝ) + 1)))
    simp only [Ea, abs_abs] at this ⊢
    rw [hKG]; linarith
  have hmom : ∀ i : Fin 3, ρ * (ksUtB ρ β)⁻¹ * (ksUGc A Ea Ha i *
      (ksDJ1 A b₀ Y i - ksDJ1 A (b₀ + Λ / ρ) Y i)) ≤ KG * (4 * kA⁻¹ * ksUg ρ) := fun i => by
    have hj0 := ksU_J1_nonneg hA (by positivity : 0 < b₀ + Λ / ρ) hY.le i
    have hj1 := ksU_J1_anti (B := b₀ + Λ / ρ) hA hb₀
      (by have := div_nonneg hΛ r0.le; linarith) hY.le i
    have hw' := ksU_wt_moment ⟨r0, r1⟩ hkA hkAA hb₀lo hY.le hY1 i
    have e : ρ * (ksUtB ρ β)⁻¹ = (1 - ρ)⁻¹ := by rw [hτ]; field_simp
    rw [e]
    have hd : ksUGc A Ea Ha i * (ksDJ1 A b₀ Y i - ksDJ1 A (b₀ + Λ / ρ) Y i) ≤
        KG * ksDJ1 A b₀ Y i := by
      have := le_abs_self (ksUGc A Ea Ha i)
      have hdd : 0 ≤ ksDJ1 A b₀ Y i - ksDJ1 A (b₀ + Λ / ρ) Y i := by linarith
      calc _ ≤ |ksUGc A Ea Ha i| * (ksDJ1 A b₀ Y i - ksDJ1 A (b₀ + Λ / ρ) Y i) :=
            mul_le_mul_of_nonneg_right this hdd
        _ ≤ KG * ksDJ1 A b₀ Y i := mul_le_mul (hG i) (by linarith) hdd (by positivity)
    calc (1 - ρ)⁻¹ * (ksUGc A Ea Ha i * (ksDJ1 A b₀ Y i - ksDJ1 A (b₀ + Λ / ρ) Y i))
        ≤ (1 - ρ)⁻¹ * (KG * ksDJ1 A b₀ Y i) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = KG * ((1 - ρ)⁻¹ * ksDJ1 A b₀ Y i) := by ring
      _ ≤ KG * (4 * kA⁻¹ * ksUg ρ) := mul_le_mul_of_nonneg_left hw' (by positivity)
  -- the logarithm part
  have hP0 : 0 ≤ ksUPY Y Ha := by unfold ksUPY; simp only [Ha]; positivity
  have hP : ksUPY Y Ha ≤ 24000 := by
    unfold ksUPY
    simp only [Ha]
    have := (hcoef 0).2; have := (hcoef 1).2; have := (hcoef 2).2
    have : Y ^ 2 ≤ 1 := pow_le_one₀ hY.le hY1
    have : Y ^ 3 ≤ 1 := pow_le_one₀ hY.le hY1
    nlinarith [abs_nonneg (ksDHc (ksUPtB ρ β) w 0), abs_nonneg (ksDHc (ksUPtB ρ β) w 1),
      abs_nonneg (ksDHc (ksUPtB ρ β) w 2), mul_le_mul_of_nonneg_left hY1
        (abs_nonneg (ksDHc (ksUPtB ρ β) w 0))]
  have hlogd : Real.log (A + (b₀ + Λ / ρ) * Y) - Real.log (A + b₀ * Y) =
      Real.log (1 + Λ / ρ * Y / (A + b₀ * Y)) := by
    have hD : 0 < A + b₀ * Y := by positivity
    rw [← Real.log_div (by positivity) hD.ne']
    congr 1
    field_simp
    ring
  have hlog : ρ * ((2 * ksUtB ρ β)⁻¹ * ksUPY Y Ha *
      (Real.log (A + (b₀ + Λ / ρ) * Y) - Real.log (A + b₀ * Y))) ≤
      12000 * (4 * Real.sqrt (Λ / kA) * ksUg ρ) := by
    rw [hlogd, hτ]
    have hw' := ksU_wt_log ⟨r0, r1⟩ hkA hkAA hb₀lo hY.le hY1 hΛ
    have e : ρ * ((2 * ((1 - ρ) * ρ))⁻¹ * ksUPY Y Ha * Real.log (1 + Λ / ρ * Y / (A + b₀ * Y)))
        = ksUPY Y Ha / 2 * ((1 - ρ)⁻¹ * Real.log (1 + Λ / ρ * Y / (A + b₀ * Y))) := by
      field_simp
    rw [e]
    have hl0 : 0 ≤ (1 - ρ)⁻¹ * Real.log (1 + Λ / ρ * Y / (A + b₀ * Y)) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by
        have : 0 ≤ Λ / ρ * Y / (A + b₀ * Y) := by positivity
        linarith))
    calc ksUPY Y Ha / 2 * ((1 - ρ)⁻¹ * Real.log (1 + Λ / ρ * Y / (A + b₀ * Y)))
        ≤ 12000 * ((1 - ρ)⁻¹ * Real.log (1 + Λ / ρ * Y / (A + b₀ * Y))) :=
          mul_le_mul_of_nonneg_right (by linarith) hl0
      _ ≤ _ := mul_le_mul_of_nonneg_left hw' (by norm_num)
  -- the dilogarithm part
  have hK : ρ * (|ksUcB w| * (ksUK ((b₀ + Λ / ρ) * Y / A) - ksUK (b₀ * Y / A))) ≤
      4 * (18 + 16 * Real.sqrt (Kb / kA) + 16 * Real.sqrt (Λ / kA)) * ksUg ρ := by
    have hk0 : 0 ≤ ksUK (b₀ * Y / A) := ksU_ksUK_nonneg (by positivity)
    have hk1 : 0 ≤ ksUK ((b₀ + Λ / ρ) * Y / A) := ksU_ksUK_nonneg (by
      have := div_nonneg hΛ r0.le; positivity)
    have hw' := ksU_wt_K ⟨r0, r1⟩ hkA hkAA hb₀.le hb₀hi hY.le hY1 hΛ (by positivity)
    have hc := ksU_abs_ksUcB_le hw
    have hc0 := abs_nonneg (ksUcB w)
    calc ρ * (|ksUcB w| * (ksUK ((b₀ + Λ / ρ) * Y / A) - ksUK (b₀ * Y / A)))
        ≤ ρ * (|ksUcB w| * ksUK ((b₀ + Λ / ρ) * Y / A)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hc0) r0.le
      _ ≤ 1 * (4 * ksUK ((b₀ + Λ / ρ) * Y / A)) :=
          mul_le_mul r1.le (mul_le_mul_of_nonneg_right hc hk1) (by positivity) zero_le_one
      _ ≤ _ := by rw [mul_assoc 4, one_mul]; exact mul_le_mul_of_nonneg_left hw' (by norm_num)
  -- assemble
  have hm0 := hmom 0
  have hm1 := hmom 1
  have hm2 := hmom 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hm0 hm1 hm2
  simp only [ksUDBa, ksUDg]
  rw [ksU_ksUPsiB_sub, hB]
  change ρ * ((ksUtB ρ β)⁻¹ * (ksUGc A Ea Ha 0 * (ksDJ1 A b₀ Y 0 - ksDJ1 A (b₀ + Λ / ρ) Y 0) +
      ksUGc A Ea Ha 1 * (ksDJ1 A b₀ Y 1 - ksDJ1 A (b₀ + Λ / ρ) Y 1) +
      ksUGc A Ea Ha 2 * (ksDJ1 A b₀ Y 2 - ksDJ1 A (b₀ + Λ / ρ) Y 2)) +
    (2 * ksUtB ρ β)⁻¹ * ksUPY Y Ha *
      (Real.log (A + (b₀ + Λ / ρ) * Y) - Real.log (A + b₀ * Y)) +
    |ksUcB w| * (ksUK ((b₀ + Λ / ρ) * Y / A) - ksUK (b₀ * Y / A))) ≤ _
  have hsplit : ∀ a1 a2 a3 l k : ℝ, ρ * ((ksUtB ρ β)⁻¹ * (a1 + a2 + a3) + l + k) =
      ρ * (ksUtB ρ β)⁻¹ * a1 + ρ * (ksUtB ρ β)⁻¹ * a2 + ρ * (ksUtB ρ β)⁻¹ * a3 + ρ * l +
        ρ * k := fun _ _ _ _ _ => by ring
  rw [hsplit]
  have hg := ksU_one_le_ksUg ⟨r0, r1⟩
  nlinarith

/-! ### The interchange over the inner vertex -/

/-- The unit square measure in the coordinates `(ρ, β)`. -/
local notation "ksUνB" =>
  Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1))

/-- The `w`-integrated `VB` integrand of one flavour at the node `p = (ρ, β)`. -/
noncomputable def ksUhB (M s u : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ w in Ioo (0 : ℝ) 1, ksUgB M s p.1 p.2 ksUcB (ksDEc M (ksUPtB p.1 p.2))
    (ksDHc (ksUPtB p.1 p.2)) u w

/-- The same with absolute coefficients (the dominating function). -/
noncomputable def ksUHB (M s u : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ w in Ioo (0 : ℝ) 1, ksUgB M s p.1 p.2 (fun w => |ksUcB w|)
    (fun w i => |ksDEc M (ksUPtB p.1 p.2) w i|) (fun w i => |ksDHc (ksUPtB p.1 p.2) w i|) u w

theorem ksU_measurable_ksDEc_ptB {γ : Type*} [MeasurableSpace γ] (M : ℝ) {ρ β w : γ → ℝ}
    (hρ : Measurable ρ) (hβ : Measurable β) (hw : Measurable w) (i : Fin 3) :
    Measurable fun z => ksDEc M (ksUPtB (ρ z) (β z)) (w z) i := by
  fin_cases i <;> simp [ksDEc, ksDcv, ksDc0, ksDc1, ksUPtB] <;> fun_prop

theorem ksU_measurable_ksDHc_ptB {γ : Type*} [MeasurableSpace γ] {ρ β w : γ → ℝ}
    (hρ : Measurable ρ) (hβ : Measurable β) (hw : Measurable w) (i : Fin 3) :
    Measurable fun z => ksDHc (ksUPtB (ρ z) (β z)) (w z) i := by
  fin_cases i <;> simp [ksDHc, ksDcv, ksDc0, ksDc1, ksUPtB] <;> fun_prop

theorem ksU_measurable_joint (M s : ℝ) (abs : Bool) :
    Measurable fun z : (ℝ × (ℝ × ℝ)) × ℝ =>
      ksUgB M s z.1.2.1 z.1.2.2 (fun w => if abs then |ksUcB w| else ksUcB w)
        (fun w i => if abs then |ksDEc M (ksUPtB z.1.2.1 z.1.2.2) w i|
          else ksDEc M (ksUPtB z.1.2.1 z.1.2.2) w i)
        (fun w i => if abs then |ksDHc (ksUPtB z.1.2.1 z.1.2.2) w i|
          else ksDHc (ksUPtB z.1.2.1 z.1.2.2) w i) z.1.1 z.2 := by
  have hρ : Measurable fun z : (ℝ × (ℝ × ℝ)) × ℝ => z.1.2.1 := by fun_prop
  have hβ : Measurable fun z : (ℝ × (ℝ × ℝ)) × ℝ => z.1.2.2 := by fun_prop
  have hw : Measurable fun z : (ℝ × (ℝ × ℝ)) × ℝ => z.2 := by fun_prop
  have hE := fun i => ksU_measurable_ksDEc_ptB M hρ hβ hw i
  have hH := fun i => ksU_measurable_ksDHc_ptB hρ hβ hw i
  refine ksU_measurable_ksUYBg (by unfold ksDA; fun_prop)
    (by unfold ksDbB ksNEB; simp only [ksUPtB]; simp; fun_prop) (by unfold ksDYmax; fun_prop)
    (by unfold ksUtB; simp [ksUPtB]; fun_prop) ?_ (fun i => ?_) (fun i => ?_)
  · cases abs <;> simp only [ksUcB] <;> fun_prop
  · cases abs
    · exact hE i
    · exact continuous_abs.measurable.comp (hE i)
  · cases abs
    · exact hH i
    · exact continuous_abs.measurable.comp (hH i)

theorem ksU_measurable_ksUhB (M s : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) => ksUhB M s q.1 q.2 :=
  ((ksU_measurable_joint M s false).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

theorem ksU_measurable_ksUHB (M s : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) => ksUHB M s q.1 q.2 :=
  ((ksU_measurable_joint M s true).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

theorem ksU_ae_mem_sq : ∀ᵐ p ∂ksUνB, p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

theorem ksU_integrable_ksUg_fst :
    Integrable (fun p : ℝ × ℝ => ksUg p.1) ksUνB := by
  have h := ksU_integrableOn_ksUg.mul_prod (integrableOn_const (μ := volume) (s := Ioo (0 : ℝ) 1)
    (C := (1 : ℝ)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
  simpa using h

section Flavour

variable {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
include hM hs

theorem ksU_nodeB_swap_VB {p : ℝ × ℝ} (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksUhB M s u p) (Ioc (0 : ℝ) Λ) ∧
      IntegrableOn (ksUDB M s Λ p.1 p.2) (Ioo (0 : ℝ) 1) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksUhB M s u p = ∫ w in Ioo (0 : ℝ) 1, ksUDB M s Λ p.1 p.2 w :=
  ksU_nodeB_swap hM hs hp.1 hp.2 (by unfold ksUcB; fun_prop)
    (fun i => (ksU_continuous_ksDEc M _ i).measurable)
    (fun i => (ksU_continuous_ksDHc _ i).measurable)
    (fun w hw => ksU_coef_sum_le hp.1 hp.2 hw) hΛ

theorem ksU_nodeB_swap_abs {p : ℝ × ℝ} (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
    (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksUHB M s u p) (Ioc (0 : ℝ) Λ) ∧
      IntegrableOn (ksUDBa M s Λ p.1 p.2) (Ioo (0 : ℝ) 1) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksUHB M s u p = ∫ w in Ioo (0 : ℝ) 1, ksUDBa M s Λ p.1 p.2 w :=
  ksU_nodeB_swap hM hs hp.1 hp.2 (by unfold ksUcB; fun_prop)
    (fun i => (ksU_continuous_ksDEc M _ i).abs.measurable)
    (fun i => (ksU_continuous_ksDHc _ i).abs.measurable)
    (fun w hw => by simpa only [abs_abs] using ksU_coef_sum_le (M := M) hp.1 hp.2 hw) hΛ

theorem ksU_ksUHB_nonneg {u : ℝ} (hu : 0 < u) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : 0 ≤ ksUHB M s u p := by
  refine setIntegral_nonneg measurableSet_Ioo fun w hw => ?_
  exact ksU_ksUYBa_nonneg (ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw))
    (ksU_ksDbB_ptB_pos hM hs hp.1 hp.2 hu.le) (ksU_ksDYmax_pos hp.2 hw).le
    (ksU_ksUtB_pos hp.1)

/-- **The dominating function is integrable** on `(0, Λ] × (0, 1)²`. -/
theorem ksU_integrable_ksUHB (hΛ : 0 ≤ Λ) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => ksUHB M s q.1 q.2)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod ksUνB) := by
  have hmeas := ksU_measurable_ksUHB M s
  obtain ⟨C, hC⟩ := ksU_ksUDBa_le hM hs hΛ
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ksU_ae_mem_sq] with p hp
    exact (ksU_nodeB_swap_abs hM hs hp hΛ).1
  refine Integrable.mono' (g := fun p => C * ksUg p.1) (ksU_integrable_ksUg_fst.const_mul C)
    (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
  filter_upwards [ksU_ae_mem_sq] with p hp
  obtain ⟨-, hint, hval⟩ := ksU_nodeB_swap_abs hM hs hp hΛ
  have hnn : ∀ u ∈ Ioc (0 : ℝ) Λ, ‖ksUHB M s u p‖ = ksUHB M s u p := fun u hu =>
    Real.norm_of_nonneg (ksU_ksUHB_nonneg hM hs hu.1 hp)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
    setIntegral_congr_fun measurableSet_Ioc hnn, hval]
  calc ∫ w in Ioo (0 : ℝ) 1, ksUDBa M s Λ p.1 p.2 w
      ≤ ∫ w in Ioo (0 : ℝ) 1, C * ksUg p.1 :=
        setIntegral_mono_on hint
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioo fun w hw => hC p.1 hp.1 p.2 hp.2 w hw
    _ = C * ksUg p.1 := by simp

/-- **The `VB` integrand of one flavour is integrable** on `(0, Λ] × (0, 1)²`. -/
theorem ksU_integrable_ksUhB (hΛ : 0 ≤ Λ) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => ksUhB M s q.1 q.2)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod ksUνB) := by
  refine Integrable.mono' (ksU_integrable_ksUHB hM hs hΛ)
    (ksU_measurable_ksUhB M s).aestronglyMeasurable ?_
  have hae : ∀ᵐ q ∂((volume.restrict (Ioc (0 : ℝ) Λ)).prod ksUνB),
      q ∈ Ioc (0 : ℝ) Λ ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod (measurableSet_Ioo.prod measurableSet_Ioo))
  filter_upwards [hae] with q hq
  obtain ⟨hu, hp⟩ := hq
  have hτ := ksU_ksUtB_pos (β := q.2.2) hp.1
  have hint : Integrable (fun w => ksUgB M s q.2.1 q.2.2 (fun w => |ksUcB w|)
      (fun w i => |ksDEc M (ksUPtB q.2.1 q.2.2) w i|)
      (fun w i => |ksDHc (ksUPtB q.2.1 q.2.2) w i|) q.1 w) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine Integrable.of_bound ((ksU_measurable_joint M s true).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (((ksUtB q.2.1 q.2.2)⁻¹ + 1) * ksUKs M * (1 + (ksUkA M s)⁻¹) ^ 2)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_)
    have hwI : w ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hw
    have hb := ksU_ksDbB_ptB_pos hM hs hp.1 hp.2 hu.1.le
    rw [Real.norm_eq_abs]
    refine (ksU_abs_ksUYBg_le (ksD_ksDA_pos hM hs hwI) hb (ksU_ksDYmax_pos hp.2 hw).le
      hτ).trans ((ksU_ksUYBa_le (ksU_ksUkA_pos hM hs) (ksU_kA_le_ksDA hwI) hb
        (ksU_ksDYmax_pos hp.2 hw).le (ksU_ksDYmax_le_one hp.2) hτ).trans ?_)
    have := ksU_coef_sum_le (M := M) hp.1 hp.2 hw
    simp only [abs_abs]
    have : 0 ≤ (ksUtB q.2.1 q.2.2)⁻¹ + 1 := by have := inv_pos.2 hτ; positivity
    gcongr
  simp only [ksUhB]
  refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioo
    fun w hw => ?_)
  rw [Real.norm_eq_abs]
  exact ksU_abs_ksUYBg_le (ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hw))
    (ksU_ksDbB_ptB_pos hM hs hp.1 hp.2 hu.1.le) (ksU_ksDYmax_pos hp.2 hw).le hτ

end Flavour

theorem ksU_setIntegral_sq (f : ℝ × ℝ → ℝ) :
    ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f p = ∫ p, f p ∂ksUνB := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

/-- At `u > 0` the nested `VB` integral is the flavour sum of the `ksUhB` over `(0, 1)²`. -/
theorem ksU_ksDNestB_eq {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {u s : ℝ}
    (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s) (hu : 0 < u) :
    ksDNestB Φ u s = ∫ p, ∑ f, Φ.coeff f * ksUhB (Φ.mass f) s u p ∂ksUνB := by
  rw [ksD_ksDNestB Φ hM hs hu, ksU_integral_simplex_eq (fun x => (1 - x 2)⁻¹ *
    ∑ f, Φ.coeff f * ∫ w in (0 : ℝ)..1, ksDYB (Φ.mass f) u x s w), ← ksU_setIntegral_sq]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
  rw [ksU_ksUPtB_two, ← mul_assoc, mul_inv_cancel₀ hp.1.1.ne', one_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ksUhB]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioo fun w _ => ksU_ksDYB_ptB hp.1

/-- **The photon-mass integral of the `VB` class**: for flavours of positive mass, `s` above
every threshold and `Λ ≥ 0`, `u ↦ ksDNestB Φ u s` is integrable on `(0, Λ]`, every flavour's
node integral `p ↦ ∫_w ksUDB` is integrable on `(0, 1)²`, and
`∫_{(0, Λ]} ksDNestB Φ u s = ∫_{(0,1)²} ∑_f c_f ∫_{(0, 1)} ksUDB (m_f) s Λ ρ β w dw`. -/
theorem ksU_integral_ksDNestB {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {s Λ : ℝ}
    (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksDNestB Φ u s) (Ioc (0 : ℝ) Λ) ∧
      (∀ f, Integrable (fun p : ℝ × ℝ => ∫ w in Ioo (0 : ℝ) 1, ksUDB (Φ.mass f) s Λ p.1 p.2 w)
        ksUνB) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksDNestB Φ u s = ∫ p, ∑ f, Φ.coeff f *
        (∫ w in Ioo (0 : ℝ) 1, ksUDB (Φ.mass f) s Λ p.1 p.2 w) ∂ksUνB := by
  set h : F → ℝ → ℝ × ℝ → ℝ := fun f u p => ksUhB (Φ.mass f) s u p with hh
  have hint : ∀ f, Integrable (fun q : ℝ × (ℝ × ℝ) => h f q.1 q.2)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod ksUνB) :=
    fun f => ksU_integrable_ksUhB (hM f) (hs f) hΛ
  have hG : Integrable (Function.uncurry fun u p => ∑ f, Φ.coeff f * h f u p)
      ((volume.restrict (Ioc (0 : ℝ) Λ)).prod ksUνB) :=
    integrable_finsetSum _ fun f _ => (hint f).const_mul (Φ.coeff f)
  have hL : EqOn (fun u => ksDNestB Φ u s)
      (fun u => ∫ p, ∑ f, Φ.coeff f * h f u p ∂ksUνB) (Ioc (0 : ℝ) Λ) :=
    fun u hu => ksU_ksDNestB_eq Φ hM hs hu.1
  refine ⟨?_, fun f => ?_, ?_⟩
  · exact IntegrableOn.congr_fun hG.integral_prod_left hL.symm measurableSet_Ioc
  · refine (hint f).integral_prod_right.congr ?_
    filter_upwards [ksU_ae_mem_sq] with p hp
    exact (ksU_nodeB_swap_VB (hM f) (hs f) hp hΛ).2.2
  · rw [setIntegral_congr_fun measurableSet_Ioc hL, integral_integral_swap hG]
    refine integral_congr_ae ?_
    filter_upwards [ksU_ae_mem_sq] with p hp
    rw [integral_finsetSum _ fun f _ =>
      ((ksU_nodeB_swap_VB (hM f) (hs f) hp hΛ).1).const_mul (Φ.coeff f)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [MeasureTheory.integral_const_mul, (ksU_nodeB_swap_VB (hM f) (hs f) hp hΛ).2.2]

/-- The same at the configuration `decCfg μ x`, for `s > -4μ²`. -/
theorem ksU_integral_ksDNestB_cfg {μ x s Λ : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun u => ksDNestB (decCfg μ x) u s) (Ioc (0 : ℝ) Λ) ∧
      (∀ f, Integrable (fun p : ℝ × ℝ => ∫ w in Ioo (0 : ℝ) 1,
        ksUDB ((decCfg μ x).mass f) s Λ p.1 p.2 w) ksUνB) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksDNestB (decCfg μ x) u s = ∫ p, ∑ f, (decCfg μ x).coeff f *
        (∫ w in Ioo (0 : ℝ) 1, ksUDB ((decCfg μ x).mass f) s Λ p.1 p.2 w) ∂ksUνB := by
  refine ksU_integral_ksDNestB _ (fun f => hμ.trans_le (ksK_mass hμ hx f)) (fun f => ?_) hΛ
  have h := ksK_mass hμ hx f
  nlinarith

end QED.ChainProof.SetAKS

end
