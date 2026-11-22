/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellConv

/-!
# Set (c): the shell slope of the one-loop self-energy of the VP-inserted photon

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values`. The companion of
`QED.ChainProof.SetCRegDisp.shellKer₀_eq_shellValue` for the slope: `shellKer₁` is `e²/(4π²)`
times the derivative at `z = -m` of `Σ(z) = A_{R_T}(-z²) z + B_{R_T}(-z²) m`
(`QED.GradedProof.GEx2.shellFun`), with `A_R`, `B_R` the one-loop coefficients `seCoefA`,
`seCoefB` of the photon function `R_T = vpPhotonT`.

The proof differentiates under `∫₀¹ dx`. Below the shell the photon argument
`a(s, x) = x(m² + (1-x)s)/(1-x)` dips below `0` (by at most `-m² - s`), so `R_T` is controlled on
`[-δ, ∞)` with the margin `δ = min(m_γ², Λ², T m²)/2` (`vpMargin`), where
`0 ≤ R_T ≤ R_max` (`vpPhotonMax`). The tail `∫_a^∞ R_T` has derivative `-R_T(a)` for `a > -2δ`.

## Main statements

* `vpPhotonT_bound`: `0 ≤ R_T(a) ≤ R_max` for `a ≥ -δ`;
* `photonTail_eq_Ioi`, `hasDerivAt_photonTail_vp`: `∂ₐ ∫_a^∞ R_T = -R_T(a)` for `a > -2δ`;
* `hasDerivAt_seArg`, `seArg_gt`: `∂ₛ a = x`, and `a > -δ` for `s > -m² - δ`;
* `hasDerivAt_integral_tail_vp`: differentiation of `∫₀¹ w(x) Tail(a(s, x)) dx` at `s = -m²`;
* **`hasDerivAt_shellFun_seCoef`**: the slope of `shellFun A_{R_T} B_{R_T} m` at `-m` is
  `(e²/8π²) seShellSlope R_T m`;
* **`hasDerivAt_shellFun_shellKer₁`**: `shellKer₁ P₀ m_γ Λ T` is the slope at `-m` of the
  self-energy `(e²/4π²) (A_{R_T}, B_{R_T})`.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

/-! ### The photon function below `0` -/

/-- The margin `δ = min(m_γ², Λ², T m²)/2` below `0` on which `R_T` stays regular. -/
noncomputable def vpMargin (m mγ Λ T : ℝ) : ℝ := min (min (mγ ^ 2) (Λ ^ 2)) (T * m ^ 2) / 2

/-- The bound `R_max = (Λ² - m_γ²)²/((T m²/2)(Λ²/2)²)` of `R_T` on `[-δ, ∞)`. -/
noncomputable def vpPhotonMax (m mγ Λ T : ℝ) : ℝ :=
  (Λ ^ 2 - mγ ^ 2) ^ 2 / (T * m ^ 2 / 2 * (Λ ^ 2 / 2) ^ 2)

section Below

variable {m mγ Λ T : ℝ}

theorem vpMargin_pos (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) :
    0 < vpMargin m mγ Λ T := by
  unfold vpMargin
  have : 0 < min (min (mγ ^ 2) (Λ ^ 2)) (T * m ^ 2) :=
    lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  linarith

theorem vpMargin_le (m mγ Λ T : ℝ) :
    2 * vpMargin m mγ Λ T ≤ mγ ^ 2 ∧ 2 * vpMargin m mγ Λ T ≤ Λ ^ 2 ∧
      2 * vpMargin m mγ Λ T ≤ T * m ^ 2 := by
  unfold vpMargin
  have h1 := min_le_left (min (mγ ^ 2) (Λ ^ 2)) (T * m ^ 2)
  have h2 := min_le_right (min (mγ ^ 2) (Λ ^ 2)) (T * m ^ 2)
  have h3 := min_le_left (mγ ^ 2) (Λ ^ 2)
  have h4 := min_le_right (mγ ^ 2) (Λ ^ 2)
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The photon function on `[-δ, ∞)`**: `0 ≤ R_T(a) ≤ R_max`. -/
theorem vpPhotonT_bound (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m) {a : ℝ}
    (ha : -vpMargin m mγ Λ T ≤ a) :
    0 ≤ vpPhotonT m mγ Λ T a ∧ vpPhotonT m mγ Λ T a ≤ vpPhotonMax m mγ Λ T := by
  obtain ⟨d1, d2, d3⟩ := vpMargin_le m mγ Λ T
  have hδ := vpMargin_pos hmγ hΛ hT hm
  have p1 : mγ ^ 2 / 2 ≤ a + mγ ^ 2 := by linarith
  have p2 : Λ ^ 2 / 2 ≤ a + Λ ^ 2 := by linarith
  have p3 : T * m ^ 2 / 2 ≤ a + T * m ^ 2 := by linarith
  have q1 : 0 < a + mγ ^ 2 := lt_of_lt_of_le (by positivity) p1
  have q2 : 0 < a + Λ ^ 2 := lt_of_lt_of_le (by positivity) p2
  have q3 : 0 < a + T * m ^ 2 := lt_of_lt_of_le (by positivity) p3
  have e : vpPhotonT m mγ Λ T a =
      (a / (a + mγ ^ 2)) ^ 2 * ((Λ ^ 2 - mγ ^ 2) ^ 2 / ((a + T * m ^ 2) * (a + Λ ^ 2) ^ 2)) := by
    unfold vpPhotonT QED.TwoLoop.UnitVPLink.photonD
    field_simp
    ring
  have h2a : 0 ≤ 2 * a + mγ ^ 2 := by linarith
  have hq : (a / (a + mγ ^ 2)) ^ 2 ≤ 1 := by
    rw [div_pow]
    exact div_le_one_of_le₀ (by nlinarith [mul_nonneg (sq_nonneg mγ) h2a]) (by positivity)
  have hden : T * m ^ 2 / 2 * (Λ ^ 2 / 2) ^ 2 ≤ (a + T * m ^ 2) * (a + Λ ^ 2) ^ 2 :=
    mul_le_mul p3 (pow_le_pow_left₀ (by positivity) p2 2) (by positivity) (by positivity)
  have hR : (Λ ^ 2 - mγ ^ 2) ^ 2 / ((a + T * m ^ 2) * (a + Λ ^ 2) ^ 2) ≤
      vpPhotonMax m mγ Λ T :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  rw [e]
  refine ⟨by positivity, ?_⟩
  calc (a / (a + mγ ^ 2)) ^ 2 * ((Λ ^ 2 - mγ ^ 2) ^ 2 / ((a + T * m ^ 2) * (a + Λ ^ 2) ^ 2))
      ≤ 1 * ((Λ ^ 2 - mγ ^ 2) ^ 2 / ((a + T * m ^ 2) * (a + Λ ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ _ := by rw [one_mul]; exact hR

theorem continuousAt_vpPhotonT {a : ℝ} (h1 : a + T * m ^ 2 ≠ 0) (h2 : a + mγ ^ 2 ≠ 0)
    (h3 : a + Λ ^ 2 ≠ 0) : ContinuousAt (vpPhotonT m mγ Λ T) a := by
  unfold vpPhotonT QED.TwoLoop.UnitVPLink.photonD
  fun_prop (disch := assumption)

/-- The tail as an integral over `(a, ∞)`. -/
theorem photonTail_eq_Ioi (R : ℝ → ℝ) (a : ℝ) : photonTail R a = ∫ u in Ioi a, R u := by
  have h := (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) R (Ioi a)
  have hpre : (fun x => a + x) ⁻¹' Ioi a = Ioi 0 := by
    ext x
    simp
  rw [hpre] at h
  exact h

/-- **The derivative of the tail**: `∂ₐ ∫_a^∞ R_T = -R_T(a)` for `a > -2δ`. -/
theorem hasDerivAt_photonTail_vp (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m)
    {a : ℝ} (ha : -2 * vpMargin m mγ Λ T < a) :
    HasDerivAt (photonTail (vpPhotonT m mγ Λ T)) (-vpPhotonT m mγ Λ T a) a := by
  set R := vpPhotonT m mγ Λ T with hRdef
  obtain ⟨d1, d2, d3⟩ := vpMargin_le m mγ Λ T
  have hδ := vpMargin_pos hmγ hΛ hT hm
  have hI0 : IntegrableOn R (Ioi 0) := by
    simpa using integrableOn_vpPhotonT_shift hmγ hΛ hT hm (le_refl (0 : ℝ))
  have hmeas : Measurable R :=
    (measurable_vpPhotonT m mγ Λ).comp (measurable_const.prodMk measurable_id)
  have hcont : ∀ b, -2 * vpMargin m mγ Λ T < b → ContinuousAt R b := fun b hb =>
    continuousAt_vpPhotonT (by linarith) (by linarith) (by linarith)
  have hII : ∀ b, -2 * vpMargin m mγ Λ T < b → IntervalIntegrable R volume b 0 := by
    intro b hb
    refine ContinuousOn.intervalIntegrable fun t ht => (hcont t ?_).continuousWithinAt
    exact lt_of_lt_of_le (lt_inf_iff.2 ⟨hb, by linarith⟩) ht.1
  have heq : ∀ᶠ b in 𝓝 a, photonTail R b = (∫ u in b..0, R u) + ∫ u in Ioi 0, R u := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    rw [photonTail_eq_Ioi, intervalIntegral.integral_interval_add_Ioi' (hII b hb) hI0]
  have hd := (intervalIntegral.integral_hasDerivAt_left (hII a ha)
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (hcont a ha)).add_const
    (∫ u in Ioi 0, R u)
  exact hd.congr_of_eventuallyEq heq

theorem hasDerivAt_seArg (m : ℝ) {x : ℝ} (hx : x ≠ 1) (s : ℝ) :
    HasDerivAt (fun s => seArg m s x) x s := by
  have h1 : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have h := ((hasDerivAt_id s).const_mul x).const_add (x * m ^ 2 / (1 - x))
  convert h using 1
  · funext s
    unfold seArg
    field_simp
    simp only [id]
  · ring

theorem measurable_seArg (m s : ℝ) : Measurable fun x => seArg m s x := by
  unfold seArg
  fun_prop

/-- Below the shell the photon argument stays above `-δ`. -/
theorem seArg_gt {δ s x : ℝ} (hδ : 0 < δ) (hx : x ∈ Ioo (0 : ℝ) 1) (hs : -m ^ 2 - δ < s) :
    -δ < seArg m s x := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 0 < 1 - x := by linarith
  rw [seArg, lt_div_iff₀ h1x]
  have h1 : (1 - x) * (-m ^ 2 - δ) < (1 - x) * s := mul_lt_mul_of_pos_left hs h1x
  have h2 : x * (x * m ^ 2 - (1 - x) * δ) < x * (m ^ 2 + (1 - x) * s) :=
    mul_lt_mul_of_pos_left (by linarith) hx0
  nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg m), mul_nonneg (mul_nonneg h1x.le h1x.le) hδ.le]

/-- **Differentiation under `∫₀¹ dx` of a weighted tail** at the shell `s = -m²`. -/
theorem hasDerivAt_integral_tail_vp (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hm : 0 < m)
    {w : ℝ → ℝ} (hw : Measurable w) (hw1 : ∀ x ∈ Ioc (0 : ℝ) 1, ‖w x‖ ≤ 1) :
    IntervalIntegrable (fun x => w x * (-vpPhotonT m mγ Λ T (shellArg m x) * x)) volume 0 1 ∧
      HasDerivAt (fun s => ∫ x in (0 : ℝ)..1, w x * photonTail (vpPhotonT m mγ Λ T) (seArg m s x))
        (∫ x in (0 : ℝ)..1, w x * (-vpPhotonT m mγ Λ T (shellArg m x) * x)) (-m ^ 2) := by
  set R := vpPhotonT m mγ Λ T with hRdef
  set δ := vpMargin m mγ Λ T with hδdef
  have hδ : 0 < δ := vpMargin_pos hmγ hΛ hT hm
  have hmR : Measurable R :=
    (measurable_vpPhotonT m mγ Λ).comp (measurable_const.prodMk measurable_id)
  have hball : ∀ s ∈ Metric.ball (-m ^ 2) δ, -m ^ 2 - δ < s := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    linarith [hs.1]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (bound := fun _ => vpPhotonMax m mγ Λ T)
    (F := fun s x => w x * photonTail R (seArg m s x))
    (F' := fun s x => w x * (-R (seArg m s x) * x)) (x₀ := -m ^ 2)
    (s := Metric.ball (-m ^ 2) δ) (Metric.ball_mem_nhds _ hδ)
    (Eventually.of_forall fun s => (hw.mul ((measurable_photonTail_vp m mγ Λ).comp
      (measurable_const.prodMk (measurable_seArg m s)))).aestronglyMeasurable)
    (by
      simp only [seArg_shell]
      exact intervalIntegrable_tail_vp hmγ hΛ hT hm hw hw1)
    ((hw.mul (((hmR.comp (measurable_seArg m _)).neg).mul measurable_id)).aestronglyMeasurable)
    (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht1 ht s hs
      rw [uIoc_of_le zero_le_one] at ht
      have hta : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
      have hR := vpPhotonT_bound hmγ hΛ hT hm (seArg_gt hδ hta (hball s hs)).le
      simp only [norm_mul, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg hR.1, abs_of_nonneg ht.1.le]
      calc |w t| * (R (seArg m s t) * t) ≤ 1 * (vpPhotonMax m mγ Λ T * 1) :=
            mul_le_mul (by simpa [Real.norm_eq_abs] using hw1 t ht)
              (mul_le_mul hR.2 ht.2 ht.1.le (hR.1.trans hR.2)) (mul_nonneg hR.1 ht.1.le)
              zero_le_one
        _ = _ := by ring)
    intervalIntegrable_const
    (by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht1 ht s hs
      rw [uIoc_of_le zero_le_one] at ht
      have hta : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
      have hgt := seArg_gt hδ hta (hball s hs)
      exact ((hasDerivAt_photonTail_vp hmγ hΛ hT hm (by linarith)).comp s
        (hasDerivAt_seArg m ht1 s)).const_mul (w t))
  simp only [seArg_shell] at key
  exact key

/-! ### The slope -/

/-- **The shell slope of the one-loop self-energy of `R_T`**: the derivative at `z = -m` of
`A_{R_T}(-z²) z + B_{R_T}(-z²) m` is `(e²/8π²) ∫₀¹ (2m² x(1+x) R_T(a₀) - (1-x) Tail(a₀)) dx`. -/
theorem hasDerivAt_shellFun_seCoef (e : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T)
    (hm : 0 < m) :
    HasDerivAt (QED.GradedProof.GEx2.shellFun
        (fun s => (seCoefA e m (vpPhotonT m mγ Λ T) s : ℂ))
        (fun s => (seCoefB e m (vpPhotonT m mγ Λ T) s : ℂ)) m)
      ((e ^ 2 / (8 * Real.pi ^ 2) * seShellSlope (vpPhotonT m mγ Λ T) m : ℝ) : ℂ) (-m) := by
  set R := vpPhotonT m mγ Λ T with hRdef
  have hw1A : ∀ x ∈ Ioc (0 : ℝ) 1, ‖(1 : ℝ) - x‖ ≤ 1 := fun x hx => by
    rw [Real.norm_of_nonneg (by linarith [hx.2])]
    linarith [hx.1]
  have hmA : Measurable fun x : ℝ => 1 - x := measurable_const.sub measurable_id
  obtain ⟨iA, dA⟩ := hasDerivAt_integral_tail_vp hmγ hΛ hT hm hmA hw1A
  obtain ⟨iB, dB⟩ := hasDerivAt_integral_tail_vp hmγ hΛ hT hm (w := fun _ => 1)
    measurable_const fun x _ => by simp
  have hA := intervalIntegrable_tail_vp hmγ hΛ hT hm hmA hw1A
  set IA := ∫ x in (0 : ℝ)..1, (1 - x) * photonTail R (shellArg m x) with hIA
  set JA := ∫ x in (0 : ℝ)..1, (1 - x) * (-R (shellArg m x) * x) with hJA
  set JB := ∫ x in (0 : ℝ)..1, (fun _ => (1 : ℝ)) x * (-R (shellArg m x) * x) with hJB
  have dA' : HasDerivAt (seCoefA e m R) (-(e ^ 2 / (8 * Real.pi ^ 2)) * JA) (-m ^ 2) :=
    dA.const_mul _
  have dB' : HasDerivAt (seCoefB e m R) (-(e ^ 2 / (4 * Real.pi ^ 2)) * JB) (-m ^ 2) := by
    have h := dB.const_mul (-(e ^ 2 / (4 * Real.pi ^ 2)))
    simp only [one_mul] at h ⊢
    exact h
  have hz : HasDerivAt (fun z : ℝ => -z ^ 2) (2 * m) (-m) := by
    convert (hasDerivAt_pow 2 (-m)).neg using 1
    ring
  have hzv : -m ^ 2 = -(-m) ^ 2 := by ring
  have gA := (dA'.comp_of_eq (-m) hz hzv).mul (hasDerivAt_id (-m))
  have gB := (dB'.comp_of_eq (-m) hz hzv).mul_const m
  have g := (gA.add gB).ofReal_comp
  have hval : seCoefA e m R (-m ^ 2) = -(e ^ 2 / (8 * Real.pi ^ 2)) * IA := by
    simp only [seCoefA, seArg_shell, hIA]
  have hslope : seShellSlope R m = 2 * m ^ 2 * JA - 4 * m ^ 2 * JB - IA := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (iA.const_mul _) (iB.const_mul _),
      ← intervalIntegral.integral_sub ((iA.const_mul _).sub (iB.const_mul _)) hA]
    unfold seShellSlope
    congr 1
    funext x
    ring
  convert g using 1
  · funext z
    simp only [QED.GradedProof.GEx2.shellFun, Function.comp_apply, Pi.mul_apply, Pi.add_apply,
      id_eq]
    push_cast
    ring
  · simp only [Function.comp, id]
    rw [← hzv, hval, hslope]
    push_cast
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

end Below

/-- **`shellKer₁` is the shell slope of the one-loop self-energy with photon function
`(e²/4π²) R_T`**: the companion of `shellKer₀_eq_shellValue`. -/
theorem hasDerivAt_shellFun_shellKer₁ (P₀ : Params) {mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hT : 0 < T) (hm : 0 < P₀.m) :
    HasDerivAt (QED.GradedProof.GEx2.shellFun
        (fun s => ((P₀.e ^ 2 / (4 * Real.pi ^ 2) *
          seCoefA P₀.e P₀.m (vpPhotonT P₀.m mγ Λ T) s : ℝ) : ℂ))
        (fun s => ((P₀.e ^ 2 / (4 * Real.pi ^ 2) *
          seCoefB P₀.e P₀.m (vpPhotonT P₀.m mγ Λ T) s : ℝ) : ℂ)) P₀.m)
      (shellKer₁ P₀ mγ Λ T) (-P₀.m) := by
  have h := (hasDerivAt_shellFun_seCoef P₀.e hmγ hΛ hT hm).const_mul
    ((P₀.e ^ 2 / (4 * Real.pi ^ 2) : ℝ) : ℂ)
  convert h using 1
  · funext z
    simp only [QED.GradedProof.GEx2.shellFun]
    push_cast
    ring
  · unfold shellKer₁
    push_cast
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

end QED.ChainProof.SetCRegDisp

end
