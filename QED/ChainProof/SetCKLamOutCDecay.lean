/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKLamOutCBd

/-!
# Set (c), Stage K: the outer-massive corner at a large inner photon mass, decay

Helper level (no frozen statement). With the inner photon of the corner at mass `Λ` (outer photon
of mass² `t > 0`), the corner integrand with its inner subdivergence added back,

`lamOutCE t Λ Y y₃ x = cornerGm (√t) Λ y₃ (Y - y₃) x + ℓ_C log M_Λ(Y)`,

`ℓ_C = c₀/h_t`, `M_Λ = Y² + (1-Y) Λ²` (the mass function of the inner photon line, as in the
corner counterterm), differs from the bound of `SetCKLamOutCBd` by
`ℓ_C log(m_Λ/M_Λ) ∈ [0, 1/8]` (`lamOutCCorr_bounds`). Hence:

* **`abs_lamOutCE_le`**: `|lamOutCE t Λ Y y₃ x| ≤ 2 scOutCDom t Y y₃ x` for every `Λ` with
  `M_Λ - t y₃ (Y - y₃) ≠ 0`;
* **`tendsto_lamOutCE`**: `lamOutCE t Λ Y y₃ x → 0` as `Λ → ∞` at every point of the domain
  (the three terms vanish as `m_Λ → ∞`, `lamOutCTerms_tendsto`, and so does `log(m_Λ/M_Λ)`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-! ### Decay of the three terms -/

/-- `log(A + δ + c) - log(A + δ) → 0` as `δ → ∞`. -/
theorem lamOut_tendsto_log_sub {A : ℝ} (hA : 0 < A) (c : ℝ) :
    Tendsto (fun δ => log (A + δ + c) - log (A + δ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun δ => 1 + c / (A + δ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := c)).div_atTop (tendsto_atTop_add_const_left _ A tendsto_id)
    simpa using this.const_add 1
  have h2 := ((continuousAt_log one_ne_zero).tendsto.comp h1)
  rw [log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop |c|] with δ hδ
  have hc := neg_abs_le c
  have hAδ : 0 < A + δ := by linarith [abs_nonneg c]
  simp only [Function.comp]
  rw [← log_div (by linarith) hAδ.ne']
  congr 1
  field_simp

/-- `log(1 + M/z)/M → 0` as `M → ∞`. -/
theorem lamOut_tendsto_J {z : ℝ} (hz : 0 < z) :
    Tendsto (fun M => log (1 + M / z) / M) atTop (𝓝 0) := by
  have hy : Tendsto (fun M => 1 + M / z) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.atTop_div_const hz)
  refine ((tendsto_pow_log_div_mul_add_atTop z (-z) 1 hz.ne').comp hy).congr fun M => ?_
  simp only [Function.comp, pow_one]
  congr 1
  field_simp
  ring

theorem lamOut_tendsto_add_atTop (m c : ℝ) : Tendsto (fun δ : ℝ => m + δ + c) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b - m - c, fun δ hδ => by linarith⟩

/-- **The three terms vanish as `m → ∞`.** -/
theorem lamOutCTerms_tendsto {Ac Aa c₀ m e w s u : ℝ} (hm : 0 < m) (hu : 0 < u)
    (hse : 0 < s + e) :
    Tendsto (fun δ => lamOutCTerms Ac Aa c₀ (m + δ) e w s u) atTop (𝓝 0) := by
  have hz : 0 < (s + e) * u := mul_pos hse hu
  have h1 : Tendsto (fun δ => Ac * (log (1 + (m + δ - e * u) / ((s + e) * u)) /
      (m + δ - e * u))) atTop (𝓝 0) := by
    have := ((lamOut_tendsto_J hz).comp (lamOut_tendsto_add_atTop m (-(e * u)))).const_mul Ac
    rw [mul_zero] at this
    refine this.congr fun δ => ?_
    simp only [Function.comp, ← sub_eq_add_neg]
  have h2 : Tendsto (fun δ => Aa * (w / u) * (1 / (m + δ + s * u))) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (lamOut_tendsto_add_atTop m (s * u))).const_mul (Aa * (w / u))
    rwa [mul_zero] at this
  have h3 : Tendsto (fun δ => |c₀| * w * ((log (m + δ + s * u) - log (m + δ)) / u)) atTop
      (𝓝 0) := by
    have := ((lamOut_tendsto_log_sub hm (s * u)).div_const u).const_mul (|c₀| * w)
    rwa [zero_div, mul_zero] at this
  have := (h1.add h2).add h3
  rw [add_zero, add_zero] at this
  exact this

theorem lamOut_tendsto_sq_mul {Y : ℝ} (hY : Y < 1) :
    Tendsto (fun Lam : ℝ => (1 - Y) * Lam ^ 2) atTop atTop :=
  (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by linarith)

/-- **The three terms vanish as `Λ → ∞`**, at every point. -/
theorem tendsto_lamOutCPt {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun Lam => lamOutCPt t Lam Y y3 x) atTop (𝓝 0) := by
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 (by linarith [h3.2])
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have hse : 0 < scOutCs Y y3 x + y3 * (Y - y3) := by
    have := scOutCs_nonneg (Y := Y) (y3 := y3) hx
    linarith
  exact (lamOutCTerms_tendsto (scOutCm_pos hY h3 hx) hu hse).comp
    (lamOut_tendsto_sq_mul hY.2)

/-! ### The corner with its inner subdivergence put back -/

/-- **The corner integrand at inner mass `Λ` with `ℓ_C log M_Λ` added**
(`M_Λ = Y² + (1-Y) Λ²`, the mass of the inner photon line). -/
noncomputable def lamOutCE (t Lam Y y3 x : ℝ) : ℝ :=
  cornerGm (√t) Lam y3 (Y - y3) x + cornerC0 x / hOut t x * log (ladderInnerMass 1 Lam Y)

/-- The difference `ℓ_C (log m_Λ - log M_Λ)`. -/
noncomputable def lamOutCCorr (t Lam Y y3 x : ℝ) : ℝ :=
  cornerC0 x / hOut t x * (log (regScOutCm Lam Y y3 x) - log (ladderInnerMass 1 Lam Y))

theorem lamOutCE_eq (t Lam Y y3 x : ℝ) :
    lamOutCE t Lam Y y3 x = (cornerGm (√t) Lam y3 (Y - y3) x +
      cornerC0 x / hOut t x * log (regScOutCm Lam Y y3 x)) - lamOutCCorr t Lam Y y3 x := by
  unfold lamOutCE lamOutCCorr
  ring

theorem lamOutCm_eq_mass (Lam Y y3 x : ℝ) :
    regScOutCm Lam Y y3 x = ladderInnerMass 1 Lam Y + y3 * (Y - y3) * setCKQ x := by
  unfold regScOutCm scOutCm ladderInnerMass
  ring

theorem lamOutCCorr_bounds {t Lam Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lamOutCCorr t Lam Y y3 x ∧ lamOutCCorr t Lam Y y3 x ≤ 1 / 8 := by
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 (by linarith [h3.2])
  have he4 : y3 * (Y - y3) ≤ Y ^ 2 / 4 := by nlinarith [sq_nonneg (Y - 2 * y3)]
  have hQ0 : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hu : 0 < setCKQ x + t := by linarith
  have hMi : Y ^ 2 ≤ ladderInnerMass 1 Lam Y := ladderInnerMass_one_ge hY.2.le
  have hMi0 : 0 < ladderInnerMass 1 Lam Y := lt_of_lt_of_le (by have := hY.1; positivity) hMi
  have hc0 : cornerC0 x * scOutRho x = x ^ 2 / 2 := by
    have : 0 < 1 - x := by linarith [hx.2]
    rw [cornerC0, scOutRho]
    field_simp
  unfold lamOutCCorr
  rw [lamOutC_ell_eq ht hx, hc0, lamOutCm_eq_mass]
  set Mi := ladderInnerMass 1 Lam Y
  set eQ := y3 * (Y - y3) * setCKQ x
  have heQ : 0 ≤ eQ := mul_nonneg he.le hQ0
  have hl0 : 0 ≤ log (Mi + eQ) - log Mi := by
    have := log_le_log hMi0 (by linarith : Mi ≤ Mi + eQ)
    linarith
  have hl1 : log (Mi + eQ) - log Mi ≤ eQ / Mi := by
    rw [← log_div (by linarith) hMi0.ne']
    have := log_le_sub_one_of_pos (div_pos (by linarith : 0 < Mi + eQ) hMi0)
    have e : (Mi + eQ) / Mi - 1 = eQ / Mi := by field_simp; ring
    linarith
  have hk : 0 ≤ x ^ 2 / 2 * (1 / (setCKQ x + t)) := by positivity
  refine ⟨mul_nonneg hk hl0, ?_⟩
  refine (mul_le_mul_of_nonneg_left hl1 hk).trans ?_
  have e : x ^ 2 / 2 * (1 / (setCKQ x + t)) * (eQ / Mi) =
      x ^ 2 / 2 * (setCKQ x / (setCKQ x + t)) * (y3 * (Y - y3) / Mi) := by
    simp only [eQ]
    field_simp
  rw [e]
  have hx2 : x ^ 2 / 2 ≤ 1 / 2 := by nlinarith [hx.1, hx.2]
  have hq : setCKQ x / (setCKQ x + t) ≤ 1 := by rw [div_le_one hu]; linarith
  have hr : y3 * (Y - y3) / Mi ≤ 1 / 4 := by
    rw [div_le_iff₀ hMi0]; linarith
  have hq0 : 0 ≤ setCKQ x / (setCKQ x + t) := by positivity
  have hr0 : 0 ≤ y3 * (Y - y3) / Mi := by positivity
  calc x ^ 2 / 2 * (setCKQ x / (setCKQ x + t)) * (y3 * (Y - y3) / Mi) ≤
        1 / 2 * 1 * (1 / 4) := by gcongr
    _ ≤ 1 / 8 := by norm_num

/-- **The domination of the corner at inner mass `Λ`, uniform in `Λ`** (`M_Λ ≠ 0`). -/
theorem abs_lamOutCE_le {t Lam Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : cornerMass (√t) Lam y3 (Y - y3) ≠ 0) :
    |lamOutCE t Lam Y y3 x| ≤ 2 * scOutCDom t Y y3 x := by
  rw [lamOutCE_eq]
  have h1 := (abs_lamOutCG_le ht hY h3 hx hM).trans (lamOutCPt_le ht hY h3 hx hM)
  have h2 := lamOutCCorr_bounds (Lam := Lam) ht hY h3 hx
  have h3' := lamOutC_scOutCDom_ge ht hY ⟨h3.1, h3.2.trans hY.2⟩ hx
  have := abs_sub _ _ |>.trans (add_le_add h1 (le_of_eq (abs_of_nonneg h2.1)))
  linarith [h2.2]

/-- **The corner at inner mass `Λ` with `ℓ_C log M_Λ` added vanishes as `Λ → ∞`**, at every
point. -/
theorem tendsto_lamOutCE {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun Lam => lamOutCE t Lam Y y3 x) atTop (𝓝 0) := by
  have hδ := lamOut_tendsto_sq_mul hY.2
  have hMt : Tendsto (fun Lam => cornerMass (√t) Lam y3 (Y - y3)) atTop atTop := by
    have := (lamOut_tendsto_add_atTop (Y ^ 2) (-(t * (y3 * (Y - y3))))).comp hδ
    refine this.congr fun Lam => ?_
    simp only [Function.comp]
    rw [regMass_eq ht.le]
    ring
  have hcorr : Tendsto (fun Lam => lamOutCCorr t Lam Y y3 x) atTop (𝓝 0) := by
    have := ((lamOut_tendsto_log_sub (pow_pos hY.1 2) (y3 * (Y - y3) * setCKQ x)).comp
      hδ).const_mul (cornerC0 x / hOut t x)
    rw [mul_zero] at this
    refine this.congr fun Lam => ?_
    simp only [Function.comp]
    unfold lamOutCCorr
    rw [lamOutCm_eq_mass]
    unfold ladderInnerMass
    ring_nf
  have hsum := (tendsto_lamOutCPt ht hY h3 hx).add hcorr
  rw [add_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [hMt.eventually_gt_atTop 0] with Lam hM
  rw [Real.norm_eq_abs, lamOutCE_eq]
  have h1 := abs_lamOutCG_le ht hY h3 hx hM.ne'
  have h2 := lamOutCCorr_bounds (Lam := Lam) ht hY h3 hx
  have := abs_sub _ _ |>.trans (add_le_add h1 (le_of_eq (abs_of_nonneg h2.1)))
  exact this

end QED.ChainProof.SetCK
