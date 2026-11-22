/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVAFub

/-!
# Set (a), stage D: the cutoff expansion of the `VA` class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). For one flavour `M` and one
`s > -4M²` the cutoff photon-mass integral of the `VA` class,
`I(Λ) = ∫_x ∫_σ ksUDA M s Λ x σ`, has the expansion

  `I(Λ) = c₂ log²Λ + c₁ log Λ + F + O((1 + log Λ)/√Λ)`   (`Λ ≥ 1`),

with `c₂ = ∫∫ a₁Y`, `c₁ = ∫∫ (a₀Y/A - 2a₁Y + 2a₁Y(log Y - log A - log x))` and
`F = ∫∫ (ksUPhiInf(-log x) - ksUPhi(b₀))`. At a node the error is
`ksUPhi(B) - ksUPhiInf(log B)` (`ksU_abs_ksUPhi_sub_le`, `B ≥ Λ`) plus the shift
`ksUPhiInf(log B) - ksUPhiInf(log Λ - log x)` by `η = log(1 + x b₀/Λ) ≤ 2√(x b₀/Λ)`; all node
quantities are dominated by `ksUg x · ksUg σ`, which is integrable on the unit square.

Main results:

* `ksU_measurable_ksUK`: `K` is measurable;
* `ksU_abs_log_le`, `ksU_log_sq_le`: `|log x| ≤ 2x^{-1/2}`, `log² x ≤ 16x^{-1/2}` on `(0, 1]`;
* **`ksU_abs_ksUDA_sub_le`**: the node error bound;
* **`ksU_VA_expansion`**: the expansion of `I(Λ)`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-! ### Measurability and elementary bounds -/

@[fun_prop]
theorem ksU_measurable_ksUK : Measurable ksUK := by
  have hI : ∀ (S : ℝ → ℝ → Prop), MeasurableSet {q : ℝ × ℝ | S q.1 q.2} →
      Measurable fun z => ∫ t, {q : ℝ × ℝ | S q.1 q.2}.indicator (ksUKer ∘ Prod.snd) (z, t) :=
    fun S hS => ((ksU_measurable_ksUKer.comp measurable_snd).indicator
      hS).stronglyMeasurable.integral_prod_right'.measurable
  have h1 := hI (fun z t => 0 < t ∧ t ≤ z)
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst))
  have h2 := hI (fun z t => z < t ∧ t ≤ 0)
    ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
  have heq : ksUK = fun z =>
      (∫ t, {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1}.indicator (ksUKer ∘ Prod.snd) (z, t)) -
        ∫ t, {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ 0}.indicator (ksUKer ∘ Prod.snd) (z, t) := by
    funext z
    have e1' : (fun t => {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1}.indicator
        (ksUKer ∘ Prod.snd) (z, t)) = (Ioc 0 z).indicator ksUKer := by
      funext t; simp [indicator, mem_Ioc]
    have e2 : (fun t => {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ 0}.indicator
        (ksUKer ∘ Prod.snd) (z, t)) = (Ioc z 0).indicator ksUKer := by
      funext t; simp [indicator, mem_Ioc]
    rw [e1', e2, MeasureTheory.integral_indicator measurableSet_Ioc,
      MeasureTheory.integral_indicator measurableSet_Ioc]
    rfl
  rw [heq]
  exact h1.sub h2

theorem ksU_abs_log_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log x| ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
  have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hr : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
  have h := Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow hx] at h
  rw [abs_of_nonpos hl]
  linarith

theorem ksU_log_sq_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ^ 2 ≤ 16 * x ^ (-(1 / 2 : ℝ)) := by
  have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hr : 0 < x ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hx _
  have h := Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow hx] at h
  have h0 : 0 ≤ -(1 / 4) * Real.log x := by nlinarith
  have hsq : (x ^ (-(1 / 4 : ℝ))) ^ 2 = x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have : (-(1 / 4) * Real.log x) ^ 2 ≤ (x ^ (-(1 / 4 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ h0 (by linarith) 2
  rw [hsq] at this
  nlinarith

theorem ksU_one_le_ksUg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 1 ≤ ksUg x := by
  have := Real.rpow_nonneg hx.1.le (-(1 / 2 : ℝ))
  have := Real.rpow_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x) (-(1 / 2 : ℝ))
  unfold ksUg
  linarith

theorem ksU_rpow_le_ksUg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x ^ (-(1 / 2 : ℝ)) ≤ ksUg x ∧ (1 - x) ^ (-(1 / 2 : ℝ)) ≤ ksUg x := by
  have := Real.rpow_nonneg hx.1.le (-(1 / 2 : ℝ))
  have := Real.rpow_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x) (-(1 / 2 : ℝ))
  unfold ksUg
  constructor <;> linarith

/-- The logarithms at a node are dominated by `G = ksUg x · ksUg σ`. -/
theorem ksU_logs_le {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    1 ≤ ksUg x * ksUg σ ∧ |Real.log x| ≤ 2 * (ksUg x * ksUg σ) ∧
      |Real.log (1 - σ)| ≤ 2 * (ksUg x * ksUg σ) ∧
      Real.log x ^ 2 ≤ 16 * (ksUg x * ksUg σ) ∧
      Real.log (1 - σ) ^ 2 ≤ 16 * (ksUg x * ksUg σ) ∧
      (1 - x) ^ (-(1 / 2 : ℝ)) ≤ ksUg x * ksUg σ := by
  have gx := ksU_one_le_ksUg hx
  have gs := ksU_one_le_ksUg hσ
  have rx := ksU_rpow_le_ksUg hx
  have rs := ksU_rpow_le_ksUg hσ
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hY1 : 1 - σ ≤ 1 := by linarith [hσ.1]
  have hgx : ksUg x ≤ ksUg x * ksUg σ := le_mul_of_one_le_right (by linarith) gs
  have hgs : ksUg σ ≤ ksUg x * ksUg σ := le_mul_of_one_le_left (by linarith) gx
  have l1 := ksU_abs_log_le hx.1 hx.2.le
  have l2 := ksU_abs_log_le hY hY1
  have l3 := ksU_log_sq_le hx.1 hx.2.le
  have l4 := ksU_log_sq_le hY hY1
  refine ⟨by nlinarith, by linarith [rx.1], by linarith [rs.2], by linarith [rx.1],
    by linarith [rs.2], by linarith [rx.2]⟩

theorem ksU_integrable_ksUg_mul :
    Integrable (fun p : ℝ × ℝ => ksUg p.1 * ksUg p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
  ksU_integrableOn_ksUg.mul_prod ksU_integrableOn_ksUg

theorem ksU_abs_ksDa1_le' {x σ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    |ksDa1 x σ| ≤ 8 * (1 - x) := by
  obtain ⟨x0, x1⟩ := hx
  obtain ⟨h0, h1⟩ := hσ
  have hp : |σ * (4 * σ - 3)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (σ - 3 / 8)]
  simp only [ksDa1]
  rw [show -8 * (1 - x) * σ * (4 * σ - 3) = -8 * (1 - x) * (σ * (4 * σ - 3)) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x),
    show |(-8 : ℝ)| = 8 by norm_num]
  nlinarith [abs_nonneg (σ * (4 * σ - 3))]

theorem ksU_abs_log_le_add_inv {A : ℝ} (hA : 0 < A) : |Real.log A| ≤ A + A⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hA
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hA)
  rw [Real.log_inv] at h2
  have := inv_pos.2 hA
  rw [abs_le]; constructor <;> linarith

/-! ### The node expansion -/

/-- The coefficient of `log² Λ` at a node: `a₁ Y`. -/
def ksUal2 (x σ : ℝ) : ℝ := ksDa1 x σ * (1 - σ)

/-- The coefficient of `log Λ` at a node. -/
noncomputable def ksUal1 (M s x σ : ℝ) : ℝ :=
  ksDa0 M x s σ * (1 - σ) / ksDA M s σ - 2 * ksDa1 x σ * (1 - σ) +
    2 * ksDa1 x σ * (1 - σ) * (Real.log (1 - σ) - Real.log (ksDA M s σ) - Real.log x)

/-- The finite part at a node: `ksUPhiInf(-log x) - ksUPhi(b₀)`. -/
noncomputable def ksUQ (M s x σ : ℝ) : ℝ :=
  ksUPhiInf (ksDA M s σ) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) (-Real.log x) -
    ksUPhi (ksDA M s σ) (ksDb M 0 x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ)

/-- The constant of the node error bound. -/
noncomputable def ksUCE (M s : ℝ) : ℝ :=
  8 * ksUKa M s * (1 + (M ^ 2 + |s|)) * (1 + (ksUkA M s)⁻¹) +
    2 * M * ksUKa M s * (ksUkA M s)⁻¹ + 192 * M + 32 * M * (M ^ 2 + |s| + (ksUkA M s)⁻¹) +
      32 * M ^ 2

theorem ksU_ksUPhiInf_add (A Y a₀ a₁ L m : ℝ) :
    ksUPhiInf A Y a₀ a₁ (L + m) = a₁ * Y * L ^ 2 +
      (a₀ * Y / A - 2 * a₁ * Y + 2 * a₁ * Y * (Real.log Y - Real.log A + m)) * L +
        ksUPhiInf A Y a₀ a₁ m := by
  unfold ksUPhiInf
  ring

theorem ksU_log_one_add_le {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ 2 * Real.sqrt t := by
  have h1 : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.2 (by linarith)
  have h := Real.log_le_sub_one_of_pos h1
  rw [Real.log_sqrt (by linarith)] at h
  have h2 := ksU_sqrt_add_le zero_le_one ht
  rw [Real.sqrt_one] at h2
  linarith


/-- The shift `η = log(1 + x b₀/Λ)` of the large-slope variable and its bounds. -/
theorem ksU_eta_le {M x Λ : ℝ} (hM : 0 < M) (hx : x ∈ Ioo (0 : ℝ) 1) (hΛ : 1 ≤ Λ) :
    Real.log (ksDb M Λ x) =
        Real.log Λ - Real.log x + Real.log (1 + x * ksDb M 0 x / Λ) ∧
      0 ≤ Real.log (1 + x * ksDb M 0 x / Λ) ∧
      Real.log (1 + x * ksDb M 0 x / Λ) ≤
        2 * M * ((Real.sqrt Λ)⁻¹ * (1 - x) ^ (-(1 / 2 : ℝ))) ∧
      (1 - x) * Real.log (1 + x * ksDb M 0 x / Λ) ^ 2 ≤ 4 * M ^ 2 * (Real.sqrt Λ)⁻¹ := by
  have hx0 := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hΛ0 : 0 < Λ := by linarith
  have hb0pos : 0 < ksDb M 0 x := ksU_ksDb_pos hM hx le_rfl
  have hb0 : ksDb M 0 x = M ^ 2 * x / (1 - x) := ksU_ksDb_zero hx
  set t := x * ksDb M 0 x / Λ with ht
  have ht0 : 0 ≤ t := by positivity
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  have hr1 : (Real.sqrt Λ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by rw [Real.one_le_sqrt]; exact hΛ)
  have hrr : ((Real.sqrt Λ)⁻¹) ^ 2 = Λ⁻¹ := by rw [inv_pow, Real.sq_sqrt hΛ0.le]
  have htle : t ≤ M ^ 2 / Λ / (1 - x) := by
    rw [ht, hb0, show x * (M ^ 2 * x / (1 - x)) / Λ = M ^ 2 / Λ / (1 - x) * (x * x) by
      field_simp]
    exact mul_le_of_le_one_right (by positivity) (by nlinarith [hx.2])
  have hlog := ksU_log_one_add_le ht0
  refine ⟨?_, Real.log_nonneg (by linarith), ?_, ?_⟩
  · have : ksDb M Λ x = Λ / x * (1 + t) := by
      rw [ksU_ksDb_eq, ht]; field_simp
    rw [this, Real.log_mul (by positivity) (by positivity), Real.log_div hΛ0.ne' hx0.ne']
  · refine hlog.trans ?_
    have := (Real.sqrt_le_sqrt htle).trans (ksU_sqrt_le_mul_rpow (by positivity) h1x)
    have hc : Real.sqrt (M ^ 2 / Λ) = M * (Real.sqrt Λ)⁻¹ := by
      rw [Real.sqrt_div' _ hΛ0.le, Real.sqrt_sq hM.le, div_eq_mul_inv]
    rw [hc] at this
    linarith
  · have h1 : Real.log (1 + t) ^ 2 ≤ 4 * t := by
      have : Real.log (1 + t) ^ 2 ≤ (2 * Real.sqrt t) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 2
      rw [mul_pow, Real.sq_sqrt ht0] at this; linarith
    have h2 : (1 - x) * t ≤ M ^ 2 * (Real.sqrt Λ)⁻¹ := by
      have := mul_le_mul_of_nonneg_left htle h1x.le
      rw [show (1 - x) * (M ^ 2 / Λ / (1 - x)) = M ^ 2 * ((Real.sqrt Λ)⁻¹) ^ 2 by
        rw [hrr]; field_simp] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg M))
      have := (inv_pos.2 hsΛ).le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 h1x.le]

theorem ksU_one_sub_mul_rpow_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) * (1 - x) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hp0 : 0 ≤ (1 - x) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg h1x.le _
  have hsq := ksU_rpow_neg_half_sq h1x
  have : ((1 - x) * (1 - x) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ 1 := by
    rw [mul_pow, hsq, sq, mul_assoc, mul_inv_cancel₀ h1x.ne', mul_one]; linarith [hx.1]
  nlinarith [mul_nonneg h1x.le hp0]

/-- The bound of the shift term (abstract form). -/
theorem ksU_shift_le {a₀ a₁ A Y η ℓ₀ c d Ka kAi M r x L lx cA : ℝ} (hη0 : 0 ≤ η)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hA : 0 < A) (ha₀ : |a₀| ≤ Ka) (hAi : A⁻¹ ≤ kAi)
    (ha₁8 : |a₁| ≤ 8 * (1 - x)) (hx0 : 0 ≤ x) (ha₁η : |a₁| * η ≤ 16 * M * r)
    (hη2 : (1 - x) * η ^ 2 ≤ 4 * M ^ 2 * r) (hℓ₀ : |ℓ₀| ≤ L + lx) (hd : |d| ≤ cA) :
    |η * (a₀ * Y / A - 2 * a₁ * Y + a₁ * Y * (2 * (ℓ₀ + c - d) + η))| ≤
      η * (Ka * kAi) + 32 * M * r + 32 * M * r * (L + lx) + 16 * η * (|c| + cA) +
        32 * M ^ 2 * r := by
  rw [abs_mul, abs_of_nonneg hη0]
  have hKa : 0 ≤ Ka := (abs_nonneg _).trans ha₀
  have e1 : |a₀ * Y / A| ≤ Ka * kAi := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_nonneg hY0, div_eq_mul_inv]
    have := inv_pos.2 hA
    calc |a₀| * Y * A⁻¹ ≤ Ka * 1 * kAi := by gcongr
      _ = _ := by ring
  have e2 : |a₁ * Y| ≤ |a₁| := by
    rw [abs_mul, abs_of_nonneg hY0]; nlinarith [abs_nonneg a₁]
  have e3 : |2 * (ℓ₀ + c - d) + η| ≤ 2 * (L + lx) + 2 * (|c| + cA) + η := by
    have := abs_add_le (2 * (ℓ₀ + c - d)) η
    have h2 : |2 * (ℓ₀ + c - d)| ≤ 2 * (|ℓ₀| + |c| + |d|) := by
      rw [abs_mul, abs_two]
      have := abs_sub (ℓ₀ + c) d
      have := abs_add_le ℓ₀ c
      linarith
    rw [abs_of_nonneg hη0] at this
    linarith
  have h3 : |2 * a₁ * Y| ≤ 2 * |a₁| := by
    rw [mul_assoc, abs_mul, abs_two]; linarith
  have h4 : |a₁ * Y * (2 * (ℓ₀ + c - d) + η)| ≤ |a₁| * (2 * (L + lx) + 2 * (|c| + cA) + η) := by
    rw [abs_mul]
    exact mul_le_mul e2 e3 (abs_nonneg _) (abs_nonneg _)
  have hbr : |a₀ * Y / A - 2 * a₁ * Y + a₁ * Y * (2 * (ℓ₀ + c - d) + η)| ≤
      Ka * kAi + 2 * |a₁| + |a₁| * (2 * (L + lx) + 2 * (|c| + cA) + η) := by
    have h1 := abs_add_le (a₀ * Y / A - 2 * a₁ * Y) (a₁ * Y * (2 * (ℓ₀ + c - d) + η))
    have h2 := abs_sub (a₀ * Y / A) (2 * a₁ * Y)
    linarith
  have hfin := mul_le_mul_of_nonneg_left hbr hη0
  have hLl : 0 ≤ L + lx := le_trans (abs_nonneg _) hℓ₀
  have hc : 0 ≤ |c| + cA := add_nonneg (abs_nonneg _) ((abs_nonneg _).trans hd)
  have ha8 : |a₁| ≤ 8 := by linarith
  have k2 : η * (|a₁| * (2 * (L + lx))) ≤ 32 * M * r * (L + lx) := by
    have h := mul_le_mul_of_nonneg_right ha₁η hLl
    have e : η * (|a₁| * (2 * (L + lx))) = 2 * (|a₁| * η * (L + lx)) := by ring
    linarith
  have k3 : η * (|a₁| * (2 * (|c| + cA))) ≤ 16 * η * (|c| + cA) := by
    have h := mul_le_mul_of_nonneg_right ha8 (mul_nonneg hη0 hc)
    have e : η * (|a₁| * (2 * (|c| + cA))) = 2 * (|a₁| * (η * (|c| + cA))) := by ring
    linarith
  have k4 : η * (|a₁| * η) ≤ 32 * M ^ 2 * r := by
    have h := mul_le_mul_of_nonneg_right ha₁8 (sq_nonneg η)
    have e : η * (|a₁| * η) = |a₁| * η ^ 2 := by ring
    linarith
  have e : η * (Ka * kAi + 2 * |a₁| + |a₁| * (2 * (L + lx) + 2 * (|c| + cA) + η)) =
      η * (Ka * kAi) + 2 * (|a₁| * η) + η * (|a₁| * (2 * (L + lx))) +
        η * (|a₁| * (2 * (|c| + cA))) + η * (|a₁| * η) := by ring
  linarith

/-- The first error term: `ksUPhi(B) - ksUPhiInf(log B)` at `B = ksDb M Λ x ≥ Λ`. -/
theorem ksU_far_le {M s x σ Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) (hΛ : 1 ≤ Λ) :
    |ksUPhi (ksDA M s σ) (ksDb M Λ x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) -
        ksUPhiInf (ksDA M s σ) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) (Real.log (ksDb M Λ x))| ≤
      8 * ksUKa M s * (1 + (M ^ 2 + |s|)) * (1 + (ksUkA M s)⁻¹) * (Real.sqrt Λ)⁻¹ := by
  have hσI : σ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hσ
  have hA := ksD_ksDA_pos hM hs hσI
  have hkA := ksU_ksUkA_pos hM hs
  have hΛ0 : 0 < Λ := by linarith
  have hBΛ : Λ ≤ ksDb M Λ x := by
    have : Λ ≤ Λ / x := le_div_self hΛ0.le hx.1 hx.2.le
    rw [ksU_ksDb_eq]; linarith [ksU_ksDb_pos hM hx le_rfl]
  refine (ksU_abs_ksUPhi_sub_le _ _ hA (hΛ.trans hBΛ) (by linarith [hσ.2])
    (by linarith [hσ.1])).trans ?_
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  have hiB : (Real.sqrt (ksDb M Λ x))⁻¹ ≤ (Real.sqrt Λ)⁻¹ :=
    inv_anti₀ hsΛ (Real.sqrt_le_sqrt hBΛ)
  have hAi : (ksDA M s σ)⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
  have hAhi := ksU_ksDA_le (M := M) (s := s) hσI
  have hKa := ksU_moments_le (M := M) (s := s) (Ioo_subset_Icc_self hx) hσI
  have := inv_pos.2 hA
  have : 0 ≤ ksUKa M s := by unfold ksUKa; positivity
  rw [div_eq_mul_inv]
  gcongr

/-- The final arithmetic of the node error bound (abstract form). -/
theorem ksU_assemble {M L r p gx gs qx qs lx lY η Ka kAi H T1 T2 : ℝ} (hM : 0 ≤ M)
    (hKa : 0 ≤ Ka) (hkAi : 0 ≤ kAi) (hH : 0 ≤ H) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (gx1 : 1 ≤ gx) (gs1 : 1 ≤ gs) (hqx : qx ≤ gx) (hpx : p ≤ gx) (hqs : qs ≤ gs)
    (hlx : lx ≤ 2 * qx) (hlY0 : 0 ≤ lY) (hlY : lY ≤ 2 * qs)
    (hη : η ≤ 2 * M * (r * p)) (hT1 : T1 ≤ 8 * Ka * (1 + H) * (1 + kAi) * r)
    (hT2 : T2 ≤ η * (Ka * kAi) + 32 * M * r + 32 * M * r * (L + lx) +
      16 * η * (lY + (H + kAi)) + 32 * M ^ 2 * r) :
    T1 + T2 ≤ (8 * Ka * (1 + H) * (1 + kAi) + 2 * M * Ka * kAi + 192 * M +
      32 * M * (H + kAi) + 32 * M ^ 2) * ((1 + L) * r * (gx * gs)) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (1 + L) * r * (gx * gs) := ⟨_, rfl⟩
  rw [← hZ]
  have hG : 1 ≤ gx * gs := by nlinarith
  have hLG : 1 ≤ (1 + L) * (gx * gs) := by nlinarith
  have z1 : r ≤ Z := by
    have := mul_le_mul_of_nonneg_left hLG hr
    rw [hZ]; linarith
  have z2 : r * p ≤ Z := by
    have h1 : p ≤ gx * gs := by nlinarith
    have : p ≤ (1 + L) * (gx * gs) := by nlinarith
    have := mul_le_mul_of_nonneg_left this hr
    rw [hZ]; linarith
  have z3 : r * (L + lx) ≤ 3 * Z := by
    have h1 : lx ≤ 2 * (gx * gs) := by nlinarith
    have h2 : L ≤ L * (gx * gs) := by nlinarith
    have : L + lx ≤ 3 * ((1 + L) * (gx * gs)) := by nlinarith
    have := mul_le_mul_of_nonneg_left this hr
    rw [hZ]; linarith
  have z4 : r * (p * lY) ≤ 2 * Z := by
    have h1 : p * lY ≤ gx * (2 * gs) := mul_le_mul hpx (by linarith) hlY0 (by linarith)
    have : p * lY ≤ 2 * ((1 + L) * (gx * gs)) := by nlinarith
    have := mul_le_mul_of_nonneg_left this hr
    rw [hZ]; linarith
  have hcK : 0 ≤ Ka * kAi := mul_nonneg hKa hkAi
  have hcH : 0 ≤ H + kAi := add_nonneg hH hkAi
  have w1 : η * (Ka * kAi) ≤ 2 * M * Ka * kAi * Z := by
    have := mul_le_mul_of_nonneg_right hη hcK
    have := mul_le_mul_of_nonneg_left z2 (by positivity : (0 : ℝ) ≤ 2 * M * (Ka * kAi))
    linarith
  have w2 : η * lY ≤ 4 * M * Z := by
    have := mul_le_mul_of_nonneg_right hη hlY0
    have := mul_le_mul_of_nonneg_left z4 (by positivity : (0 : ℝ) ≤ 2 * M)
    linarith
  have w3 : η * (H + kAi) ≤ 2 * M * (H + kAi) * Z := by
    have := mul_le_mul_of_nonneg_right hη hcH
    have := mul_le_mul_of_nonneg_left z2 (by positivity : (0 : ℝ) ≤ 2 * M * (H + kAi))
    linarith
  have w4 : 32 * M * r * (L + lx) ≤ 96 * M * Z := by
    have := mul_le_mul_of_nonneg_left z3 (by positivity : (0 : ℝ) ≤ 32 * M)
    linarith
  have w5 := mul_le_mul_of_nonneg_left z1 (by positivity : (0 : ℝ) ≤ 32 * M)
  have w6 := mul_le_mul_of_nonneg_left z1 (by positivity : (0 : ℝ) ≤ 32 * M ^ 2)
  have w7 := mul_le_mul_of_nonneg_left z1
    (by positivity : (0 : ℝ) ≤ 8 * Ka * (1 + H) * (1 + kAi))
  linarith

/-- **The node error bound of the cutoff expansion**: for `x, σ ∈ (0, 1)` and `Λ ≥ 1`,
`|ksUDA - (α₂ log²Λ + α₁ log Λ + Q)| ≤ CE (1 + log Λ)/√Λ · ksUg x ksUg σ`. -/
theorem ksU_abs_ksUDA_sub_le {M s x σ Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) (hΛ : 1 ≤ Λ) :
    |ksUDA M s Λ x σ - (ksUal2 x σ * Real.log Λ ^ 2 + ksUal1 M s x σ * Real.log Λ +
      ksUQ M s x σ)| ≤
      ksUCE M s * (1 + Real.log Λ) / Real.sqrt Λ * (ksUg x * ksUg σ) := by
  have hσI : σ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hσ
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hA := ksD_ksDA_pos hM hs hσI
  have hkA := ksU_ksUkA_pos hM hs
  have hΛ0 : 0 < Λ := by linarith
  have hL : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  obtain ⟨hlogB, hη0, hηle, hη2⟩ := ksU_eta_le hM hx hΛ
  have hT1 := ksU_far_le hM hs hx hσ hΛ
  have hpx := ksU_one_sub_mul_rpow_le hx
  have hr0 : 0 ≤ (Real.sqrt Λ)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg Λ)
  have hp0 : 0 ≤ (1 - x) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith [hx.2]) _
  have ha₁8 := ksU_abs_ksDa1_le' hxI hσI
  have ha₁η : |ksDa1 x σ| * Real.log (1 + x * ksDb M 0 x / Λ) ≤ 16 * M * (Real.sqrt Λ)⁻¹ := by
    have h := mul_le_mul ha₁8 hηle hη0 (by linarith [hx.2])
    have e : 8 * (1 - x) * (2 * M * ((Real.sqrt Λ)⁻¹ * (1 - x) ^ (-(1 / 2 : ℝ)))) =
      16 * M * (Real.sqrt Λ)⁻¹ * ((1 - x) * (1 - x) ^ (-(1 / 2 : ℝ))) := by ring
    rw [e] at h
    nlinarith [mul_le_mul_of_nonneg_left hpx (by positivity : (0 : ℝ) ≤ 16 * M *
      (Real.sqrt Λ)⁻¹)]
  have hlA : |Real.log (ksDA M s σ)| ≤ M ^ 2 + |s| + (ksUkA M s)⁻¹ := by
    have := ksU_abs_log_le_add_inv hA
    have := ksU_ksDA_le (M := M) (s := s) hσI
    have := inv_anti₀ hkA (ksU_kA_le_ksDA (M := M) (s := s) hσI)
    linarith
  have hℓ₀ : |Real.log Λ - Real.log x| ≤ Real.log Λ + |Real.log x| := by
    refine (abs_sub _ _).trans ?_; rw [abs_of_nonneg hL]
  have hT2 := ksU_shift_le (a₀ := ksDa0 M x s σ) (Ka := ksUKa M s) (A := ksDA M s σ) (Y := 1 - σ)
    (c := Real.log (1 - σ)) hη0 (by linarith [hσ.2]) (by linarith [hσ.1]) hA
    (by have := ksU_moments_le (M := M) (s := s) hxI hσI; linarith [abs_nonneg (ksDa1 x σ)])
    (inv_anti₀ hkA (ksU_kA_le_ksDA hσI)) ha₁8 hx.1.le ha₁η hη2 hℓ₀ hlA
  have hsplit : ksUDA M s Λ x σ - (ksUal2 x σ * Real.log Λ ^ 2 + ksUal1 M s x σ * Real.log Λ +
      ksUQ M s x σ) =
      (ksUPhi (ksDA M s σ) (ksDb M Λ x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) -
        ksUPhiInf (ksDA M s σ) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ)
          (Real.log (ksDb M Λ x))) +
      Real.log (1 + x * ksDb M 0 x / Λ) * (ksDa0 M x s σ * (1 - σ) / ksDA M s σ -
        2 * ksDa1 x σ * (1 - σ) + ksDa1 x σ * (1 - σ) * (2 * (Real.log Λ - Real.log x +
          Real.log (1 - σ) - Real.log (ksDA M s σ)) + Real.log (1 + x * ksDb M 0 x / Λ))) := by
    simp only [ksUDA, ksUNodeD, ksUal2, ksUal1, ksUQ, hlogB]
    unfold ksUPhiInf
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  -- the atoms against `Z = (1 + L) G r`
  have gx := ksU_one_le_ksUg hx
  have gs := ksU_one_le_ksUg hσ
  have rx := ksU_rpow_le_ksUg hx
  have rs := ksU_rpow_le_ksUg hσ
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hlx := ksU_abs_log_le hx.1 hx.2.le
  have hlY := ksU_abs_log_le hY (by linarith [hσ.1])
  have hKa0 : 0 ≤ ksUKa M s := by unfold ksUKa; positivity
  have h := ksU_assemble hM.le hKa0 (inv_pos.2 hkA).le (by positivity : (0 : ℝ) ≤ M ^ 2 + |s|)
    hL hr0 gx gs rx.1 rx.2 rs.2 hlx (abs_nonneg _) hlY hηle hT1 hT2
  refine h.trans_eq ?_
  unfold ksUCE
  rw [div_eq_mul_inv]
  ring

/-! ### Integration over the nodes -/

/-- The unit square measure in the outer node `x` and the inner node `σ`. -/
local notation "ksUν" =>
  Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1))

theorem ksU_integrable_of_le {f : ℝ × ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ σ ∈ Ioo (0 : ℝ) 1, |f (x, σ)| ≤ C * (ksUg x * ksUg σ)) :
    Integrable f ksUν := by
  refine Integrable.mono' (ksU_integrable_ksUg_mul.const_mul C) hf.aestronglyMeasurable ?_
  have hae : ∀ᵐ p ∂ksUν, p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hae] with p hp
  exact h p.1 hp.1 p.2 hp.2

theorem ksU_measurable_ksUDA (M s Λ : ℝ) : Measurable fun p : ℝ × ℝ => ksUDA M s Λ p.1 p.2 := by
  unfold ksUDA ksUNodeD ksUPhi ksDA ksDb ksDa0 ksDa1
  fun_prop

theorem ksU_integrable_ksUDA {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hΛ : 0 ≤ Λ) :
    Integrable (fun p : ℝ × ℝ => ksUDA M s Λ p.1 p.2) ksUν := by
  refine ksU_integrable_of_le (ksU_measurable_ksUDA M s Λ)
    (160 * ksUKa M s * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 * (2 + 2 * M + Real.sqrt Λ))
    fun x hx σ hσ => ?_
  refine (ksU_abs_ksUNodeD_le _ _ hM hs hx hσ hΛ).trans ?_
  have hK := ksU_moments_le (M := M) (s := s) (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hσ)
  have gx := ksU_one_le_ksUg hx
  have gs := ksU_one_le_ksUg hσ
  have : 0 ≤ ksUKa M s := by unfold ksUKa; positivity
  have h0 : 0 ≤ 160 * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 * (2 + 2 * M + Real.sqrt Λ) := by
    have := Real.sqrt_nonneg Λ; positivity
  calc 160 * (|ksDa0 M x s σ| + |ksDa1 x σ|) * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 *
        (2 + 2 * M + Real.sqrt Λ) * ksUg x
      = 160 * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 * (2 + 2 * M + Real.sqrt Λ) *
          ((|ksDa0 M x s σ| + |ksDa1 x σ|) * (ksUg x * 1)) := by ring
    _ ≤ 160 * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 * (2 + 2 * M + Real.sqrt Λ) *
          (ksUKa M s * (ksUg x * ksUg σ)) := by gcongr
    _ = _ := by ring

theorem ksU_integrable_ksUal2 : Integrable (fun p : ℝ × ℝ => ksUal2 p.1 p.2) ksUν := by
  refine ksU_integrable_of_le (by unfold ksUal2 ksDa1; fun_prop) 8 fun x hx σ hσ => ?_
  have h := ksU_abs_ksDa1_le (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hσ)
  have hG := (ksU_logs_le hx hσ).1
  unfold ksUal2
  rw [abs_mul, abs_of_pos (by linarith [hσ.2] : (0 : ℝ) < 1 - σ)]
  nlinarith [abs_nonneg (ksDa1 x σ), hσ.1]

theorem ksU_integrable_ksUal1 {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) :
    Integrable (fun p : ℝ × ℝ => ksUal1 M s p.1 p.2) ksUν := by
  have hkA := ksU_ksUkA_pos hM hs
  set cA := M ^ 2 + |s| + (ksUkA M s)⁻¹
  refine ksU_integrable_of_le (by unfold ksUal1 ksDa0 ksDa1 ksDA; fun_prop)
    (ksUKa M s * (ksUkA M s)⁻¹ + 80 + 16 * cA) fun x hx σ hσ => ?_
  have hσI := Ioo_subset_Icc_self hσ
  have hxI := Ioo_subset_Icc_self hx
  have hA := ksD_ksDA_pos hM hs hσI
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hY1 : 1 - σ ≤ 1 := by linarith [hσ.1]
  obtain ⟨hG, hlx, hlY, -, -, -⟩ := ksU_logs_le hx hσ
  have hK := ksU_moments_le (M := M) (s := s) hxI hσI
  have ha₁ := ksU_abs_ksDa1_le hxI hσI
  have hAi : (ksDA M s σ)⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
  have hlA : |Real.log (ksDA M s σ)| ≤ cA := by
    have := ksU_abs_log_le_add_inv hA
    have := ksU_ksDA_le (M := M) (s := s) hσI
    linarith
  have hcA : 0 ≤ cA := (abs_nonneg _).trans hlA
  have hKa0 : 0 ≤ ksUKa M s := by unfold ksUKa; positivity
  have e1 : |ksDa0 M x s σ * (1 - σ) / ksDA M s σ| ≤ ksUKa M s * (ksUkA M s)⁻¹ := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hY, div_eq_mul_inv]
    have := inv_pos.2 hA
    calc |ksDa0 M x s σ| * (1 - σ) * (ksDA M s σ)⁻¹ ≤ ksUKa M s * 1 * (ksUkA M s)⁻¹ := by
          gcongr; linarith [abs_nonneg (ksDa1 x σ)]
      _ = _ := by ring
  have e2 : |ksDa1 x σ * (1 - σ)| ≤ 8 := by
    rw [abs_mul, abs_of_pos hY]; nlinarith [abs_nonneg (ksDa1 x σ)]
  have e3 : |Real.log (1 - σ) - Real.log (ksDA M s σ) - Real.log x| ≤
      4 * (ksUg x * ksUg σ) + cA := by
    have := abs_sub (Real.log (1 - σ) - Real.log (ksDA M s σ)) (Real.log x)
    have := abs_sub (Real.log (1 - σ)) (Real.log (ksDA M s σ))
    linarith
  unfold ksUal1
  have t1 := abs_add_le (ksDa0 M x s σ * (1 - σ) / ksDA M s σ - 2 * ksDa1 x σ * (1 - σ))
    (2 * ksDa1 x σ * (1 - σ) * (Real.log (1 - σ) - Real.log (ksDA M s σ) - Real.log x))
  have t2 := abs_sub (ksDa0 M x s σ * (1 - σ) / ksDA M s σ) (2 * ksDa1 x σ * (1 - σ))
  have t3 : |2 * ksDa1 x σ * (1 - σ)| ≤ 16 := by
    rw [mul_assoc, abs_mul, abs_two]; linarith
  have t4 : |2 * ksDa1 x σ * (1 - σ) * (Real.log (1 - σ) - Real.log (ksDA M s σ) -
      Real.log x)| ≤ 16 * (4 * (ksUg x * ksUg σ) + cA) := by
    rw [abs_mul]
    exact mul_le_mul t3 e3 (abs_nonneg _) (by norm_num)
  have hc0 : 0 ≤ ksUKa M s * (ksUkA M s)⁻¹ := by have := inv_pos.2 hkA; positivity
  nlinarith

theorem ksU_abs_ksUPhiInf_le {M s x σ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |ksUPhiInf (ksDA M s σ) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) (-Real.log x)| ≤
      (4 * ksUKa M s * (ksUkA M s)⁻¹ + 96 + 24 * (32 + (M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2)) *
        (ksUg x * ksUg σ) := by
  have hkA := ksU_ksUkA_pos hM hs
  have hσI := Ioo_subset_Icc_self hσ
  have hxI := Ioo_subset_Icc_self hx
  have hA := ksD_ksDA_pos hM hs hσI
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hY1 : 1 - σ ≤ 1 := by linarith [hσ.1]
  obtain ⟨hG, hlx, hlY, hlx2, hlY2, -⟩ := ksU_logs_le hx hσ
  have hK := ksU_moments_le (M := M) (s := s) hxI hσI
  have ha₁ := ksU_abs_ksDa1_le hxI hσI
  have hAi : (ksDA M s σ)⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
  obtain ⟨cA, hcAdef⟩ : ∃ c, c = M ^ 2 + |s| + (ksUkA M s)⁻¹ := ⟨_, rfl⟩
  rw [← hcAdef]
  have hlA : |Real.log (ksDA M s σ)| ≤ cA := by
    have := ksU_abs_log_le_add_inv hA
    have := ksU_ksDA_le (M := M) (s := s) hσI
    rw [hcAdef]; linarith
  obtain ⟨G, hGdef⟩ : ∃ G, G = ksUg x * ksUg σ := ⟨_, rfl⟩
  rw [← hGdef] at hG hlx hlY hlx2 hlY2 ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = Real.log x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.log (1 - σ) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.log (ksDA M s σ) := ⟨_, rfl⟩
  rw [← ha] at hlx hlx2
  rw [← hb] at hlY hlY2
  rw [← hc] at hlA
  have hu1 : |-a + b| ≤ 4 * G := by
    have := abs_add_le (-a) b; rw [abs_neg] at this; linarith
  have hu2 : (-a + b - c) ^ 2 ≤ (3 * (32 + cA ^ 2)) * G := by
    have hsq : (-a + b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b + c)]
    have hA2 : c ^ 2 ≤ cA ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hlA 2
    have := mul_le_mul_of_nonneg_left hG (sq_nonneg cA)
    linarith
  have hK1 := ksU_ksUK_one_le
  have hK10 := ksU_ksUK_nonneg zero_le_one
  have hKa0 : 0 ≤ ksUKa M s := by unfold ksUKa; positivity
  have hq0 : 0 ≤ (-a + b - c) ^ 2 / 2 + 2 * ksUK 1 := by
    have := sq_nonneg (-a + b - c); linarith
  have e1 : |ksDa0 M x s σ * ((1 - σ) / ksDA M s σ) * (-a + b)| ≤
      ksUKa M s * (ksUkA M s)⁻¹ * (4 * G) := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hY, abs_of_pos hA, div_eq_mul_inv]
    have := inv_pos.2 hA
    have ha0 : |ksDa0 M x s σ| ≤ ksUKa M s := by linarith [abs_nonneg (ksDa1 x σ)]
    calc |ksDa0 M x s σ| * ((1 - σ) * (ksDA M s σ)⁻¹) * |-a + b|
        ≤ ksUKa M s * (1 * (ksUkA M s)⁻¹) * (4 * G) := by gcongr
      _ = _ := by ring
  have hin : |-((1 - σ) * (-a + b)) + (1 - σ) * ((-a + b - c) ^ 2 / 2 + 2 * ksUK 1)| ≤
      4 * G + (3 * (32 + cA ^ 2)) * G / 2 + 2 := by
    have h1 := abs_add_le (-((1 - σ) * (-a + b))) ((1 - σ) * ((-a + b - c) ^ 2 / 2 + 2 * ksUK 1))
    rw [abs_neg, abs_mul, abs_of_pos hY, abs_mul, abs_of_pos hY, abs_of_nonneg hq0] at h1
    have i1 : (1 - σ) * |-a + b| ≤ 4 * G := by
      have := mul_le_of_le_one_left (abs_nonneg (-a + b)) hY1; linarith
    have i2 : (1 - σ) * ((-a + b - c) ^ 2 / 2 + 2 * ksUK 1) ≤
        (3 * (32 + cA ^ 2)) * G / 2 + 2 := by
      have := mul_le_of_le_one_left hq0 hY1
      linarith [hK1]
    linarith
  have e2 : |2 * ksDa1 x σ * (-((1 - σ) * (-a + b)) + (1 - σ) * ((-a + b - c) ^ 2 / 2 +
      2 * ksUK 1))| ≤ 16 * (4 * G + (3 * (32 + cA ^ 2)) * G / 2 + 2) := by
    rw [abs_mul, abs_mul, abs_two]
    have := abs_nonneg (-((1 - σ) * (-a + b)) + (1 - σ) * ((-a + b - c) ^ 2 / 2 + 2 * ksUK 1))
    calc 2 * |ksDa1 x σ| * |-((1 - σ) * (-a + b)) + (1 - σ) * ((-a + b - c) ^ 2 / 2 +
          2 * ksUK 1)| ≤ 2 * 8 * (4 * G + (3 * (32 + cA ^ 2)) * G / 2 + 2) := by gcongr
      _ = _ := by ring
  have hPI : ksUPhiInf (ksDA M s σ) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ) (-a) =
      ksDa0 M x s σ * ((1 - σ) / ksDA M s σ) * (-a + b) + 2 * ksDa1 x σ *
        (-((1 - σ) * (-a + b)) + (1 - σ) * ((-a + b - c) ^ 2 / 2 + 2 * ksUK 1)) := by
    rw [hb, hc]; unfold ksUPhiInf; ring
  rw [← ha, hPI]
  refine (abs_add_le _ _).trans ?_
  linarith

theorem ksU_abs_ksUPhi_b0_le {M s x σ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    |ksUPhi (ksDA M s σ) (ksDb M 0 x) (1 - σ) (ksDa0 M x s σ) (ksDa1 x σ)| ≤
      160 * ksUKa M s * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 * (1 + M) *
        (ksUg x * ksUg σ) := by
  have hkA := ksU_ksUkA_pos hM hs
  have hσI := Ioo_subset_Icc_self hσ
  have hxI := Ioo_subset_Icc_self hx
  have hA := ksD_ksDA_pos hM hs hσI
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hY1 : 1 - σ ≤ 1 := by linarith [hσ.1]
  obtain ⟨hG, -, -, -, -, hpG⟩ := ksU_logs_le hx hσ
  have hK := ksU_moments_le (M := M) (s := s) hxI hσI
  have hAi : (ksDA M s σ)⁻¹ ≤ (ksUkA M s)⁻¹ := inv_anti₀ hkA (ksU_kA_le_ksDA hσI)
  have hAhi := ksU_ksDA_le (M := M) (s := s) hσI
  have hKa0 : 0 ≤ ksUKa M s := by unfold ksUKa; positivity
  have hb0 := ksU_ksDb_pos hM hx le_rfl
  refine (ksU_abs_ksUPhi_le _ _ hA hb0 hY hY1).trans ?_
  have h1 := ksU_one_add_log_sq_le hb0.le
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hsb : Real.sqrt (ksDb M 0 x) ≤ M * (ksUg x * ksUg σ) := by
    rw [ksU_ksDb_zero hx]
    refine (Real.sqrt_le_sqrt (?_ : M ^ 2 * x / (1 - x) ≤ M ^ 2 / (1 - x))).trans ?_
    · gcongr; nlinarith [sq_nonneg M, hx.2]
    · refine (ksU_sqrt_le_mul_rpow (sq_nonneg M) h1x).trans ?_
      rw [Real.sqrt_sq hM.le]
      exact mul_le_mul_of_nonneg_left hpG hM.le
  have hW : (2 + ksDA M s σ + (ksDA M s σ)⁻¹) ^ 2 ≤ (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by have := inv_pos.2 hA; positivity) (by linarith) 2
  have hW0 : 0 ≤ (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 := sq_nonneg _
  have hL0 : 0 ≤ (1 + Real.log (1 + ksDb M 0 x)) ^ 2 := sq_nonneg _
  have hL1 : (1 + Real.log (1 + ksDb M 0 x)) ^ 2 ≤ 16 * (1 + M) * (ksUg x * ksUg σ) := by
    have : 1 + M * (ksUg x * ksUg σ) ≤ (1 + M) * (ksUg x * ksUg σ) := by linarith
    linarith
  calc 10 * (|ksDa0 M x s σ| + |ksDa1 x σ|) * (2 + ksDA M s σ + (ksDA M s σ)⁻¹) ^ 2 *
        (1 + Real.log (1 + ksDb M 0 x)) ^ 2
      ≤ 10 * ksUKa M s * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 *
          (16 * (1 + M) * (ksUg x * ksUg σ)) := by gcongr
    _ = _ := by ring

theorem ksU_integrable_ksUQ {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) :
    Integrable (fun p : ℝ × ℝ => ksUQ M s p.1 p.2) ksUν := by
  refine ksU_integrable_of_le (by unfold ksUQ ksUPhiInf ksUPhi ksDA ksDb ksDa0 ksDa1; fun_prop)
    (4 * ksUKa M s * (ksUkA M s)⁻¹ + 96 + 24 * (32 + (M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2) +
      160 * ksUKa M s * (2 + M ^ 2 + |s| + (ksUkA M s)⁻¹) ^ 2 * (1 + M)) fun x hx σ hσ => ?_
  have h1 := ksU_abs_ksUPhiInf_le hM hs hx hσ
  have h2 := ksU_abs_ksUPhi_b0_le hM hs hx hσ
  unfold ksUQ
  refine (abs_sub _ _).trans ?_
  linarith

/-- The integral of the node weight `ksUg x · ksUg σ` over the unit square. -/
noncomputable def ksUGint : ℝ := ∫ p, ksUg p.1 * ksUg p.2 ∂ksUν

/-- The coefficient of `log² Λ`. -/
noncomputable def ksUc2 : ℝ := ∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo (0 : ℝ) 1, ksUal2 x σ

/-- The coefficient of `log Λ`. -/
noncomputable def ksUc1 (M s : ℝ) : ℝ := ∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo (0 : ℝ) 1, ksUal1 M s x σ

/-- The finite part. -/
noncomputable def ksUF (M s : ℝ) : ℝ := ∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo (0 : ℝ) 1, ksUQ M s x σ

/-- **The cutoff expansion of the `VA` class** (one flavour, one `s`): for `Λ ≥ 1`,
`|I(Λ) - (c₂ log²Λ + c₁ log Λ + F)| ≤ CE · ∫∫ ksUg ksUg · (1 + log Λ)/√Λ`. -/
theorem ksU_VA_expansion {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hΛ : 1 ≤ Λ) :
    |(∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo (0 : ℝ) 1, ksUDA M s Λ x σ) -
        (ksUc2 * Real.log Λ ^ 2 + ksUc1 M s * Real.log Λ + ksUF M s)| ≤
      ksUCE M s * ksUGint * (1 + Real.log Λ) / Real.sqrt Λ := by
  have hD := ksU_integrable_ksUDA hM hs (Λ := Λ) (by linarith)
  have h2 := ksU_integrable_ksUal2
  have h1 := ksU_integrable_ksUal1 hM hs
  have hQ := ksU_integrable_ksUQ hM hs
  have hG := ksU_integrable_ksUg_mul
  set L := Real.log Λ
  have hE : ∫ p, (ksUDA M s Λ p.1 p.2 - (ksUal2 p.1 p.2 * L ^ 2 + ksUal1 M s p.1 p.2 * L +
      ksUQ M s p.1 p.2)) ∂ksUν = (∫ p, ksUDA M s Λ p.1 p.2 ∂ksUν) -
        ((∫ p, ksUal2 p.1 p.2 ∂ksUν) * L ^ 2 + (∫ p, ksUal1 M s p.1 p.2 ∂ksUν) * L +
          ∫ p, ksUQ M s p.1 p.2 ∂ksUν) := by
    have h21 : Integrable (fun p : ℝ × ℝ => ksUal2 p.1 p.2 * L ^ 2 + ksUal1 M s p.1 p.2 * L)
        ksUν := (h2.mul_const _).add (h1.mul_const _)
    have hsum : Integrable (fun p : ℝ × ℝ => ksUal2 p.1 p.2 * L ^ 2 + ksUal1 M s p.1 p.2 * L +
        ksUQ M s p.1 p.2) ksUν := h21.add hQ
    rw [integral_sub hD hsum, integral_add h21 hQ, integral_add (h2.mul_const _) (h1.mul_const _),
      MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
  rw [ksUc2, ksUc1, ksUF, ← integral_prod _ hD, ← integral_prod _ h2, ← integral_prod _ h1,
    ← integral_prod _ hQ, ← hE]
  have hb : ∀ᵐ p ∂ksUν, ‖ksUDA M s Λ p.1 p.2 - (ksUal2 p.1 p.2 * L ^ 2 +
      ksUal1 M s p.1 p.2 * L + ksUQ M s p.1 p.2)‖ ≤
      ksUCE M s * (1 + L) / Real.sqrt Λ * (ksUg p.1 * ksUg p.2) := by
    have hae : ∀ᵐ p ∂ksUν, p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    filter_upwards [hae] with p hp
    exact ksU_abs_ksUDA_sub_le hM hs hp.1 hp.2 hΛ
  refine (norm_integral_le_of_norm_le (hG.const_mul _) hb).trans_eq ?_
  rw [MeasureTheory.integral_const_mul, ksUGint]
  ring

end QED.ChainProof.SetAKS
