/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegCOut

/-!
# Set (c), Stage K: the outer-massive corner at a large inner photon mass, bounds

Helper level (no frozen statement). In the corner with the outer photon of mass² `t > 0` and the
inner photon at a Pauli–Villars mass `Λ`, the `(u + v)⁻²`-representation of `SetCKRegCOutBd`
(`regCornerGm_out_eq`, generic in the inner mass) has the pole `P/u = -ℓ_C log m_Λ`,
`ℓ_C = c₀/h_t = x²/(2u)`, `m_Λ = Y² + e Q + (1-Y) Λ²`: the inner subdivergence. Without it,

`|cornerGm (√t) Λ y₃ (Y - y₃) x + ℓ_C log m_Λ| ≤ T₁ + T₂ + T₃` (**`abs_lamOutCG_le`**,
`lamOutCPt`, `M_Λ = m_Λ - e u ≠ 0`),

the threshold, `κ` and beyond-threshold terms of the session-11 bound (`lamOutCTerms`). Each term
decreases in `m_Λ` (`lamOut_J1_mono`, `lamOut_log_ratio_mono`; the threshold term through the
master bound `log(1 + M/z)/M ≤ 2 (1 + log(1 + a/z))/a`, `a = M + z`), so at `m₀` the session-11
chain applies and, uniformly in `Λ` (**`lamOutCPt_le`**),

`T₁ + T₂ + T₃ ≤ scOutCDom t Y y₃ x`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The three terms of the corner bound without the pole `P/u`. -/
noncomputable def lamOutCTerms (Ac Aa c₀ m e w s u : ℝ) : ℝ :=
  Ac * (log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u)) +
    Aa * (w / u) * (1 / (m + s * u)) + |c₀| * w * ((log (m + s * u) - log m) / u)

section Generic

variable {m e w s u : ℝ}

/-- **The corner bound without the pole**: `|∫ T/(u + v)² + P/u|` is at most the threshold, `κ`
and beyond-threshold terms. -/
theorem lamOutC_abs_noPole_le (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u)
    (hs : 0 ≤ s) (hM : m - e * u ≠ 0) (a₀ a₁ a₂ c₀ c₁ c₂ c₃ : ℝ) :
    |(∫ v in Ioi 0, scOutCTg a₀ a₁ a₂ c₀ c₁ c₂ c₃ m e w s v / (u + v) ^ 2) +
        c₀ * w * log m * (1 / u)| ≤
      lamOutCTerms (|c₁| + |c₂| / (w * (s + e)) + |c₃| / (w * (s + e)) ^ 2)
        (|a₀| + |a₁| / (w * (s + e)) + |a₂| / (w * (s + e)) ^ 2) c₀ m e w s u := by
  rw [(scOutCTg_integral hm he hw hu hs hM a₀ a₁ a₂ c₀ c₁ c₂ c₃).2]
  have hkI : IntegrableOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|) (Ioi 0) :=
    Integrable.abs (scOutC_k_int hm he hw hu hs hM c₀ c₁ c₂ c₃).1
  have hS : IntegrableOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|)
      (scOutCS m s) := hkI.mono_set fun v hv => hv.1
  have hR : IntegrableOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|)
      (scOutCR m s) := hkI.mono_set fun v hv => hv.1
  have hsplit : ∫ v in Ioi 0, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| =
      (∫ v in scOutCS m s, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|) +
        ∫ v in scOutCR m s, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| := by
    rw [← scOutCS_union, setIntegral_union scOutCS_disjoint (measurableSet_scOutCR m s) hS hR]
  have h1 := scOutC_abs_k_S hm he hw hu hs hM c₀ c₁ c₂ c₃
  have h3 := scOutC_abs_k_R (e := e) hm hw hu hs c₀ c₁ c₂ c₃
  have h2 := scOutC_abs_kap hm he hw hu hs hM a₀ a₁ a₂
  have hk' : |∫ v in Ioi 0, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| ≤
      ∫ v in Ioi 0, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| := abs_integral_le_integral_abs
  have hκ' : |∫ v in Ioi 0, scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2| ≤
      ∫ v in Ioi 0, |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2| := abs_integral_le_integral_abs
  have hadd := abs_add_le (∫ v in Ioi 0, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v))
    (∫ v in Ioi 0, scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2)
  have e1 : (∫ v in Ioi 0, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) +
      (∫ v in Ioi 0, scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2) +
      -(c₀ * w * log m) * (1 / u) + c₀ * w * log m * (1 / u) =
      (∫ v in Ioi 0, scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)) +
        ∫ v in Ioi 0, scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2 := by ring
  rw [e1]
  unfold lamOutCTerms
  linarith

end Generic

/-! ### Monotonicity in the mass -/

/-- `2 (1 + log(1 + a/z))/a` decreases in `a > 0`. -/
theorem lamOut_J1_mono {a₀ a z : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (hz : 0 < z) :
    2 * (1 + log (1 + a / z)) / a ≤ 2 * (1 + log (1 + a₀ / z)) / a₀ := by
  have ha0 : 0 < a := ha₀.trans_le ha
  have hp₀ : 0 < 1 + a₀ / z := by positivity
  have hp : 0 < 1 + a / z := by positivity
  have hL₀ : 0 ≤ log (1 + a₀ / z) :=
    log_nonneg (by have : 0 ≤ a₀ / z := (by positivity); linarith)
  have hk : (1 + a / z) * a₀ ≤ (1 + a₀ / z) * a := by
    have e : a / z * a₀ = a₀ / z * a := by ring
    nlinarith
  have hlog : log (1 + a / z) + log a₀ ≤ log (1 + a₀ / z) + log a := by
    rw [← log_mul hp.ne' ha₀.ne', ← log_mul hp₀.ne' ha0.ne']
    exact log_le_log (by positivity) hk
  have hr : log a - log a₀ ≤ (a - a₀) / a₀ := by
    rw [← log_div ha0.ne' ha₀.ne']
    have := log_le_sub_one_of_pos (div_pos ha0 ha₀)
    have e : a / a₀ - 1 = (a - a₀) / a₀ := by field_simp
    linarith
  rw [div_le_div_iff₀ ha0 ha₀]
  have e : (a - a₀) / a₀ * a₀ = a - a₀ := by field_simp
  have h1 : log (1 + a / z) * a₀ ≤ log (1 + a₀ / z) * a₀ + (a - a₀) := by
    have : log (1 + a / z) ≤ log (1 + a₀ / z) + (a - a₀) / a₀ := by linarith
    nlinarith
  nlinarith [mul_nonneg hL₀ (sub_nonneg.2 ha)]

/-- `log(m + c) - log m` decreases in `m > 0`. -/
theorem lamOut_log_ratio_mono {m₀ m c : ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ m) (hc : 0 ≤ c) :
    log (m + c) - log m ≤ log (m₀ + c) - log m₀ := by
  have hm0 : 0 < m := hm₀.trans_le hm
  have h : log (m + c) + log m₀ ≤ log (m₀ + c) + log m := by
    rw [← log_mul (by linarith) hm₀.ne', ← log_mul (by linarith) hm0.ne']
    exact log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hm hc])
  linarith

/-- Term 1 of the corner bound from the master form `2 (1 + log(1 + a/z))/a`. -/
theorem lamOutC_T1 {Ac x a z Y g ly lx l1 : ℝ} (hx : 0 < x)
    (hAc : Ac ≤ 3 * x) (hz : 0 < z) (ha0 : 0 < a) (haY : a ≤ Y ^ 2 + z) (hY1 : Y ^ 2 ≤ 1)
    (hg : 0 < g) (hgz : g * x ≤ z) (hgx1 : g * x ≤ 1) (hlog : log (g * x) = -(ly + l1 + lx)) :
    Ac * (2 * (1 + log (1 + a / z)) / a) ≤ 6 * x * (3 + ly + lx + l1) / a := by
  have hgx0 : 0 < g * x := mul_pos hg hx
  have hlog3 : log 3 ≤ 2 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlogaz : log (1 + a / z) ≤ log 3 + ly + l1 + lx := by
    have h1 : 1 + a / z ≤ 3 / (g * x) := by
      have e1 : a / z ≤ 1 + Y ^ 2 / z := by
        rw [div_le_iff₀ hz, add_mul, one_mul, div_mul_cancel₀ _ hz.ne']; linarith
      have e2 : Y ^ 2 / z ≤ 1 / (g * x) := by
        rw [div_le_div_iff₀ hz hgx0]; nlinarith
      have e3 : 2 ≤ 2 / (g * x) := by rw [le_div_iff₀ hgx0]; linarith
      have : 3 / (g * x) = 2 / (g * x) + 1 / (g * x) := by ring
      linarith
    calc log (1 + a / z) ≤ log (3 / (g * x)) := log_le_log (by positivity) h1
      _ = log 3 + ly + l1 + lx := by rw [log_div (by norm_num) hgx0.ne', hlog]; ring
  have hJb0 : 0 ≤ 2 * (1 + log (1 + a / z)) / a := by
    have h0 : 0 ≤ a / z := by positivity
    have : 0 ≤ log (1 + a / z) := log_nonneg (by linarith)
    positivity
  calc Ac * (2 * (1 + log (1 + a / z)) / a) ≤ 3 * x * (2 * (1 + log (1 + a / z)) / a) :=
        mul_le_mul_of_nonneg_right hAc hJb0
    _ ≤ 3 * x * (2 * (1 + (log 3 + ly + l1 + lx)) / a) := by gcongr
    _ ≤ 3 * x * (2 * (1 + (2 + ly + l1 + lx)) / a) := by gcongr
    _ = 6 * x * (3 + ly + lx + l1) / a := by ring

/-! ### The corner at inner mass `Λ` -/

/-- The bound `lamOutCTerms` at the point `(Y, y₃, x)` and inner photon mass `Λ`. -/
noncomputable def lamOutCPt (t Lam Y y3 x : ℝ) : ℝ :=
  lamOutCTerms
    (|cornerC1 x y3 (Y - y3)| + |cornerC2 x y3 (Y - y3)| /
        (scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3))) +
      |cornerC3 x y3 (Y - y3)| / (scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3))) ^ 2)
    (|cornerA0 x y3 (Y - y3)| + |cornerA1 x y3 (Y - y3)| /
        (scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3))) +
      |cornerA2 x y3 (Y - y3)| / (scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3))) ^ 2)
    (cornerC0 x) (regScOutCm Lam Y y3 x) (y3 * (Y - y3)) (scOutRho x) (scOutCs Y y3 x)
    (setCKQ x + t)

theorem lamOutC_ell_eq {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    cornerC0 x / hOut t x = cornerC0 x * scOutRho x * (1 / (setCKQ x + t)) := by
  have hρ := scOutRho_pos hx
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  rw [hOut_eq_div_scOutRho ht.le hx]
  field_simp

/-- **The corner at inner mass `Λ` with the pole `ℓ_C log m_Λ` put back**, bounded by the three
terms (`M_Λ ≠ 0`). -/
theorem abs_lamOutCG_le {t Lam Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : cornerMass (√t) Lam y3 (Y - y3) ≠ 0) :
    |cornerGm (√t) Lam y3 (Y - y3) x + cornerC0 x / hOut t x * log (regScOutCm Lam Y y3 x)| ≤
      lamOutCPt t Lam Y y3 x := by
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 (by linarith [h3.2])
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have hM' : regScOutCm Lam Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by
    rw [← regScOutC_mass_eq ht.le]; exact hM
  have key := lamOutC_abs_noPole_le (regScOutCm_pos hY h3 hx Lam) he (scOutRho_pos hx) hu
    (scOutCs_nonneg (Y := Y) (y3 := y3) hx) hM' (cornerA0 x y3 (Y - y3)) (cornerA1 x y3 (Y - y3))
    (cornerA2 x y3 (Y - y3)) (cornerC0 x) (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3))
    (cornerC3 x y3 (Y - y3))
  rw [regCornerGm_out_eq ht hY h3 hx hM, lamOutC_ell_eq ht hx,
    mul_right_comm (cornerC0 x * scOutRho x)]
  exact key

theorem lamOutC_scOutCDom_ge {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) : 1 ≤ scOutCDom t Y y3 x := by
  obtain ⟨hyy, hyy1, -⟩ := scOutC_root hY
  obtain ⟨hb, hb1, -⟩ := scOutC_root h3
  obtain ⟨hzz, hzz1, -⟩ := scOutC_root hx
  have hF := scOutC_one_le_F0 hyy hyy1 hb hb1 hzz hzz1
  have hS : 0 ≤ 1 / √(1 - Y) := by positivity
  have h1 : 1 / (Y ^ ((1 : ℝ) / 12)) ^ 8 * (1 / (y3 ^ ((1 : ℝ) / 12)) ^ 10) *
      (1 / (x ^ ((1 : ℝ) / 12)) ^ 8) ≤
      (1 / (Y ^ ((1 : ℝ) / 12)) ^ 8 + 1 / √(1 - Y)) * (1 / (y3 ^ ((1 : ℝ) / 12)) ^ 10) *
        (1 / (x ^ ((1 : ℝ) / 12)) ^ 8) := by
    gcongr
    linarith
  have h2 : (1 : ℝ) ≤ 200 * (1 + 1 / t) := by
    have : 0 < 1 / t := by positivity
    nlinarith
  unfold scOutCDom
  nlinarith

/-- Term 1 at `a₀ + δ` from the bound at `a₀`. -/
theorem lamOutC_T1_full {Ac M z a₀ δ B : ℝ} (hAc0 : 0 ≤ Ac) (hz : 0 < z) (ha0 : 0 < a₀)
    (hδ : 0 ≤ δ) (haL : M + z = a₀ + δ) (hM : M ≠ 0)
    (hB : Ac * (2 * (1 + log (1 + a₀ / z)) / a₀) ≤ B) :
    Ac * (log (1 + M / z) / M) ≤ B := by
  have hJ := scOutC_J1_le hz (by rw [haL]; linarith) hM
  rw [haL] at hJ
  have hmono := lamOut_J1_mono ha0 (le_add_of_nonneg_right hδ) hz
  exact (mul_le_mul_of_nonneg_left (hJ.trans hmono) hAc0).trans hB

/-- Term 2 at `a₀ + δ` from the bound at `a₀`. -/
theorem lamOutC_T2_full {K a₀ a δ B : ℝ} (hK : 0 ≤ K) (ha0 : 0 < a₀) (hδ : 0 ≤ δ)
    (ha : a = a₀ + δ) (hB : K * (1 / a₀) ≤ B) : K * (1 / a) ≤ B := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hK) hB
  exact one_div_le_one_div_of_le ha0 (by rw [ha]; linarith)

/-- Term 3 at `m + δ` from the bound at `m`. -/
theorem lamOutC_T3_full {k u m δ c P C : ℝ} (hk : 0 ≤ k) (hu : 0 < u) (hm : 0 < m)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hB : k * ((log (m + c) - log m) / u) + P ≤ C) (hP : 0 ≤ P) :
    k * ((log (m + δ + c) - log (m + δ)) / u) ≤ C := by
  have hr := lamOut_log_ratio_mono hm (le_add_of_nonneg_right hδ) hc
  have : k * ((log (m + δ + c) - log (m + δ)) / u) ≤ k * ((log (m + c) - log m) / u) := by
    gcongr
  linarith

theorem lamOutC_combine {A₁ A₂ A₃ B₁ B₂ C R : ℝ} (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) (h₃ : A₃ ≤ C)
    (h : B₁ + B₂ + C ≤ R) : A₁ + A₂ + A₃ ≤ R := by linarith

/-- **The three terms are dominated uniformly in `Λ`**: they decrease in `m_Λ = m₀ + (1-Y) Λ²`,
and at `m₀` the session-11 chain bounds them by `scOutCDom`. -/
theorem lamOutCPt_le {t Lam Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : cornerMass (√t) Lam y3 (Y - y3) ≠ 0) : lamOutCPt t Lam Y y3 x ≤ scOutCDom t Y y3 x := by
  have hY4 : 0 < Y - y3 := by linarith [h3.2]
  have hY21 : Y ^ 2 ≤ 1 := by nlinarith [hY.1, hY.2]
  have hY21' : Y ^ 2 + 0 ≤ 1 := by linarith
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 hY4
  have hm0 := scOutCm_pos hY h3 hx
  have hδ0 : 0 ≤ (1 - Y) * Lam ^ 2 := mul_nonneg (by linarith [hY.2]) (sq_nonneg Lam)
  have hw : 0 < scOutRho x := scOutRho_pos hx
  have hQ0 : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hu : 0 < setCKQ x + t := by linarith
  have hs : 0 ≤ scOutCs Y y3 x := scOutCs_nonneg hx
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x =
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) := by
    unfold scOutCs
    field_simp
    ring
  have hM' : regScOutCm Lam Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by
    rw [← regScOutC_mass_eq ht.le]; exact hM
  have hQ : setCKQ x = x * scOutRho x := by
    rw [setCKQ, scOutRho]; field_simp
  have hg : cornerG y3 (Y - y3) = y3 * (1 - Y) := by rw [cornerG]; ring
  have hg0 : 0 < cornerG y3 (Y - y3) := by rw [hg]; exact mul_pos h3.1 (by linarith [hY.2])
  have hgβ : cornerG y3 (Y - y3) ≤ betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x :=
    le_max_left _ _
  unfold lamOutCPt lamOutCTerms
  rw [← hβ]
  have hYs : y3 + (Y - y3) ≤ 1 := by linarith only [hY.2]
  have hAc := scOutC_Ac_le hx.1.le hx.2.le h3.1.le hY4.le hYs hg0 hgβ
  have hAa := scOutC_Aa_le hx.1.le hx.2.le h3.1.le hY4.le hYs hg0 hgβ
  have hβw : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ≤
      cornerG y3 (Y - y3) + y3 * (Y - y3) * scOutRho x := by
    refine max_le (le_add_of_nonneg_right (by positivity)) ?_
    rw [scOutRho, mul_div_assoc]
    exact le_add_of_nonneg_left hg0.le
  have hc0 : |cornerC0 x| * scOutRho x = x ^ 2 / 2 := by
    have : 0 < 1 - x := by linarith [hx.2]
    rw [cornerC0, abs_of_pos (by have := hx.1; positivity), scOutRho]
    field_simp
  rw [hc0]
  have hmdef : regScOutCm Lam Y y3 x = scOutCm Y y3 x + (1 - Y) * Lam ^ 2 := rfl
  have hm0def : scOutCm Y y3 x = Y ^ 2 + y3 * (Y - y3) * setCKQ x + 0 := by
    rw [scOutCm]; ring
  rw [hmdef] at hM' ⊢
  have hρ : scOutRho x = x / (1 - x) := rfl
  have hlogg : log (cornerG y3 (Y - y3) * x) = -(-log y3 + -log (1 - Y) + -log x) := by
    rw [hg, log_mul (mul_pos h3.1 (by linarith [hY.2])).ne' hx.1.ne',
      log_mul h3.1.ne' (by linarith [hY.2])]
    ring
  -- the twelfth roots
  obtain ⟨hyy, hyy1, hYe⟩ := scOutC_root hY
  obtain ⟨hb, hb1, h3e⟩ := scOutC_root ⟨h3.1, h3.2.trans hY.2⟩
  obtain ⟨hzz, hzz1, hxe⟩ := scOutC_root hx
  have hly : -log y3 ≤ 12 / y3 ^ ((1 : ℝ) / 12) := scOutC_neg_log_le h3.1
  have hlx : -log x ≤ 12 / x ^ ((1 : ℝ) / 12) := scOutC_neg_log_le hx.1
  have hlY : -log Y ≤ 12 / Y ^ ((1 : ℝ) / 12) := scOutC_neg_log_le hY.1
  have hS : 0 < √(1 - Y) := sqrt_pos.2 (by linarith [hY.2])
  have hl1 : -log (1 - Y) ≤ 2 * (Y ^ ((1 : ℝ) / 12)) ^ 6 / √(1 - Y) := by
    have hsq : √Y = (Y ^ ((1 : ℝ) / 12)) ^ 6 := by
      conv_lhs => rw [hYe]
      rw [show (Y ^ ((1 : ℝ) / 12)) ^ 12 = ((Y ^ ((1 : ℝ) / 12)) ^ 6) ^ 2 by ring,
        sqrt_sq (by positivity)]
    rw [← hsq]
    exact scOutC_neg_log_one_sub_le hY
  have hly0 : 0 ≤ -log y3 := by
    have := log_nonpos h3.1.le (h3.2.trans hY.2).le; linarith
  have hlx0 : 0 ≤ -log x := by have := log_nonpos hx.1.le hx.2.le; linarith
  have hl10 : 0 ≤ -log (1 - Y) := by
    have := log_nonpos (by linarith [hY.2] : (0 : ℝ) ≤ 1 - Y) (by linarith [hY.1]); linarith
  have hlY0 : 0 ≤ -log Y := by have := log_nonpos hY.1.le hY.2.le; linarith
  unfold scOutCDom
  -- forget the definitions
  generalize scOutCs Y y3 x = s at *
  generalize scOutCm Y y3 x = m at *
  generalize (1 - Y) * Lam ^ 2 = δ at *
  generalize betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = β at *
  generalize cornerG y3 (Y - y3) = g at *
  generalize setCKQ x = Q at *
  generalize scOutRho x = w at *
  generalize Y ^ ((1 : ℝ) / 12) = yy at *
  generalize y3 ^ ((1 : ℝ) / 12) = b at *
  generalize x ^ ((1 : ℝ) / 12) = zz at *
  obtain ⟨hY2, hxy, haz2, hgz, haz, hmY, hm1, hgx1⟩ :=
    regScOutC_geom (e := y3 * (Y - y3)) (u := Q + t) ht hY h3 hx rfl hQ hm0def rfl hβ hg hgβ hs
      hw le_rfl hY21'
  have hβpos : 0 < β := hg0.trans_le hgβ
  have ha0 : 0 < m + s * (Q + t) := lt_of_lt_of_le (by have := hY.1; positivity) hY2
  have hz : 0 < (s + y3 * (Y - y3)) * (Q + t) := by positivity
  have hAc0 : 0 ≤ |cornerC1 x y3 (Y - y3)| + |cornerC2 x y3 (Y - y3)| / β +
      |cornerC3 x y3 (Y - y3)| / β ^ 2 := add_nonneg (add_nonneg (abs_nonneg _)
    (div_nonneg (abs_nonneg _) hβpos.le)) (div_nonneg (abs_nonneg _) (pow_nonneg hβpos.le 2))
  have hAa0 : 0 ≤ |cornerA0 x y3 (Y - y3)| + |cornerA1 x y3 (Y - y3)| / β +
      |cornerA2 x y3 (Y - y3)| / β ^ 2 := add_nonneg (add_nonneg (abs_nonneg _)
    (div_nonneg (abs_nonneg _) hβpos.le)) (div_nonneg (abs_nonneg _) (pow_nonneg hβpos.le 2))
  -- term 1: the master bound at `a_Λ`, monotonicity down to `a₀`, the chain at `a₀`
  have hT1 := lamOutC_T1 (Y := Y) hx.1 hAc hz ha0
    (by linarith only [haz2]) hY21 hg0 hgz hgx1 hlogg
  have hT1' := lamOutC_T1_full hAc0 hz ha0 hδ0 (by ring) hM' hT1
  -- term 2
  have hT2 := scOutC_T2 (u := Q + t) hx.1 hAa hw (by linarith only [ht, hQ]) ha0
  have hT2' := lamOutC_T2_full (a := m + δ + s * (Q + t)) (by positivity) ha0 hδ0 (by ring) hT2
  -- term 3
  have hm0p : 0 < m := lt_of_lt_of_le (by have := hY.1; positivity) hmY
  have hsu : 0 ≤ s * (Q + t) := by positivity
  have hloga : log (m + s * (Q + t)) ≤ (s + y3 * (Y - y3)) * (Q + t) := by
    have h1 := log_le_sub_one_of_pos ha0
    linarith only [h1, hY21, haz2]
  have hlogm := scOutC_abs_log_m hY hu.le hmY hm1
  have hxz : x ^ 2 / 2 * ((s + y3 * (Y - y3)) * (Q + t) / (Q + t)) ≤ 1 := by
    have e : (s + y3 * (Y - y3)) * (Q + t) / (Q + t) = β / w := by
      rw [hβ]; field_simp
    rw [e]
    have hg1 : g ≤ 1 := by
      rw [hg]; exact scOutC_mul_le_one (h3.2.trans hY.2).le (by linarith only [hY.2])
        (by linarith only [hY.1])
    have he1 : y3 * (Y - y3) ≤ 1 :=
      scOutC_mul_le_one (h3.2.trans hY.2).le hY4.le (by linarith only [hY.2, h3.1])
    exact scOutC_xz hx hρ hβw hg1 he1
  have hT34 := scOutC_T34 hx ht (by linarith only [hQ0]) hloga hlogm hlY0 hxz
  have hT3' := lamOutC_T3_full (k := x ^ 2 / 2) (by positivity) hu hm0p hδ0 hsu hT34
    (by positivity)
  -- the algebra
  have hxy0 : 0 ≤ x * y3 := (mul_pos hx.1 h3.1).le
  have ha1 : yy ^ 6 * zz ^ 9 * b ^ 9 ≤ m + s * (Q + t) := by
    have h4 : (yy ^ 6 * zz ^ 9 * b ^ 9) ^ 4 ≤ (m + s * (Q + t)) ^ 4 := by
      have e : (yy ^ 6 * zz ^ 9 * b ^ 9) ^ 4 = (yy ^ 12) ^ 2 * (zz ^ 12 * b ^ 12) ^ 3 := by ring
      rw [e, ← hYe, ← hxe, ← h3e]
      calc Y ^ 2 * (x * y3) ^ 3 ≤ (m + s * (Q + t)) * (m + s * (Q + t)) ^ 3 :=
            mul_le_mul hY2 (pow_le_pow_left₀ hxy0 hxy 3) (by positivity) ha0.le
        _ = (m + s * (Q + t)) ^ 4 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) ha0.le (by norm_num)).1 h4
  have ha2 : yy ^ 8 * zz ^ 8 * b ^ 8 ≤ m + s * (Q + t) := by
    have h4 : (yy ^ 8 * zz ^ 8 * b ^ 8) ^ 3 ≤ (m + s * (Q + t)) ^ 3 := by
      have e : (yy ^ 8 * zz ^ 8 * b ^ 8) ^ 3 = (yy ^ 12) ^ 2 * (zz ^ 12 * b ^ 12) ^ 2 := by ring
      rw [e, ← hYe, ← hxe, ← h3e]
      calc Y ^ 2 * (x * y3) ^ 2 ≤ (m + s * (Q + t)) * (m + s * (Q + t)) ^ 2 :=
            mul_le_mul hY2 (pow_le_pow_left₀ hxy0 hxy 2) (by positivity) ha0.le
        _ = (m + s * (Q + t)) ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) ha0.le (by norm_num)).1 h4
  have halg := scOutC_dom_alg hyy hyy1 hb hb1 hzz hzz1 hS ht ha1 ha2 hly0 hly hlx0 hlx hl10
    hl1 hlY
  rw [← hxe] at halg
  exact lamOutC_combine hT1' hT2' hT3' halg

end QED.ChainProof.SetCK
