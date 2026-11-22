/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellKer
public import QED.WickModel.SelfEnergyLimit

/-!
# Set (c): the one-loop self-energy of a photon function, anchored to the frozen self-energy

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values`. This file fixes the convention of the
kernels `shellKer₀`, `shellKer₁` of `QED/ChainProof/SetCRegDispShellKer.lean` against the frozen
one-loop self-energy.

For a photon function `R` put `a(s, x) = x(m² + (1-x)s)/(1-x)` (`seArg`) and
`A_R(s) = -(e²/8π²) ∫₀¹ (1-x) Tail_R(a) dx`, `B_R(s) = -(e²/4π²) ∫₀¹ Tail_R(a) dx` (`seCoefA`,
`seCoefB`), `Tail_R(a) = ∫_a^∞ R`.

* `photonTail_photonD`: `∫_a^∞ D = log((a + Λ²)/(a + m_γ²))` for the Pauli–Villars photon;
* **`seCoefA_photonD`**, **`seCoefB_photonD`**: for `R = D` these are the frozen coefficients
  `QED.WickModel.selfEnergyLoopA`, `QED.WickModel.selfEnergyLoopB` (for `s ≥ -m²`): the one-loop
  limit is `i (A p̸ + B m)` and the graded order-`2` limit is `A p̸ + B m` with the same `A, B`
  (minus `δ₂`, `δ_m`), the convention of `QED.GradedProof.GEx2.shellFun`;
* `seArg_shell`: on the shell `a(-m², x) = m² x²/(1-x)`;
* **`shellValue_seCoef`**: the shell value `A_R(-m²)(-m) + B_R(-m²) m` is
  `-(e² m/8π²) ∫₀¹ (1+x) Tail_R(a₀)`;
* **`shellKer₀_eq_shellValue`**: `shellKer₀ P₀ m_γ Λ T` is `e²/(4π²)` times the shell value of
  the one-loop self-energy (charge `e`) with photon function `R_T`.

Not proved here: the slope (`HasDerivAt` of `shellFun A_R B_R m` at `-m` with value
`(e²/8π²) seShellSlope R m`), which needs differentiation under `∫₀¹ dx` near the shell.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitVPLink (photonVar photonD)

/-- The photon argument `a(s, x) = x(m² + (1-x)s)/(1-x)` of the one-loop self-energy. -/
noncomputable def seArg (m s x : ℝ) : ℝ := x * (m ^ 2 + (1 - x) * s) / (1 - x)

/-- The `p̸` coefficient `A_R(s) = -(e²/8π²) ∫₀¹ (1-x) Tail_R(a(s,x)) dx` of the one-loop
self-energy with photon function `R`. -/
noncomputable def seCoefA (e m : ℝ) (R : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(e ^ 2 / (8 * Real.pi ^ 2)) * ∫ x in (0 : ℝ)..1, (1 - x) * photonTail R (seArg m s x)

/-- The `m` coefficient `B_R(s) = -(e²/4π²) ∫₀¹ Tail_R(a(s,x)) dx` of the one-loop self-energy
with photon function `R`. -/
noncomputable def seCoefB (e m : ℝ) (R : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(e ^ 2 / (4 * Real.pi ^ 2)) * ∫ x in (0 : ℝ)..1, photonTail R (seArg m s x)

theorem seArg_shell (m x : ℝ) : seArg m (-m ^ 2) x = shellArg m x := by
  unfold seArg shellArg photonVar
  ring

/-! ### The Pauli–Villars photon -/

/-- **The tail of the Pauli–Villars photon** is the paired logarithm. -/
theorem photonTail_photonD {mγ Λ a : ℝ} (h₁ : 0 < a + mγ ^ 2) (hle : mγ ^ 2 ≤ Λ ^ 2) :
    photonTail (photonD mγ Λ) a = Real.log ((a + Λ ^ 2) / (a + mγ ^ 2)) := by
  have h₂ : 0 < a + Λ ^ 2 := by linarith
  set g : ℝ → ℝ := fun u => Real.log (a + u + mγ ^ 2) - Real.log (a + u + Λ ^ 2) with hg
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (photonD mγ Λ (a + u)) u := by
    intro u hu
    have p1 : 0 < a + u + mγ ^ 2 := by linarith
    have p2 : 0 < a + u + Λ ^ 2 := by linarith
    have d1 := (((hasDerivAt_id u).const_add a).add_const (mγ ^ 2)).log p1.ne'
    have d2 := (((hasDerivAt_id u).const_add a).add_const (Λ ^ 2)).log p2.ne'
    convert d1.sub d2 using 1
    · rw [hg]
      rfl
    · simp only [photonD, id]
  have hpos : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ photonD mγ Λ (a + u) := by
    intro u hu
    have hu' : 0 < u := hu
    unfold photonD
    exact sub_nonneg.2 (one_div_le_one_div_of_le (by linarith) (by linarith))
  have hinv : Tendsto (fun u : ℝ => (a + u + Λ ^ 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_left _ _ tendsto_id)).inv_tendsto_atTop
  have hr : Tendsto (fun u : ℝ => (a + u + mγ ^ 2) / (a + u + Λ ^ 2)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul (Λ ^ 2 - mγ ^ 2))
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    have : a + u + Λ ^ 2 ≠ 0 := by linarith
    field_simp
    ring
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
    rw [Real.log_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    have p1 : a + u + mγ ^ 2 ≠ 0 := by linarith
    have p2 : a + u + Λ ^ 2 ≠ 0 := by linarith
    simp only [Function.comp, hg]
    rw [Real.log_div p1 p2]
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hderiv 0 le_rfl).continuousAt.continuousWithinAt) (fun u hu => hderiv u (le_of_lt hu))
    hpos hlim
  unfold photonTail
  rw [h, Real.log_div h₂.ne' h₁.ne']
  simp only [hg, add_zero]
  ring

/-- The Feynman mass term is `(1-x)(a + M²)`. -/
theorem selfEnergyFeynmanMass_eq_seArg (m M s : ℝ) {x : ℝ} (hx : x ≠ 1) :
    QED.WickModel.selfEnergyFeynmanMass m M s x = (1 - x) * (seArg m s x + M ^ 2) := by
  have : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  unfold QED.WickModel.selfEnergyFeynmanMass seArg
  field_simp
  ring

theorem seArg_nonneg {m s x : ℝ} (hs : -m ^ 2 ≤ s) (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 ≤ seArg m s x := by
  obtain ⟨hx0, hx1⟩ := hx
  have h : 0 ≤ m ^ 2 + (1 - x) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 1 - x), sq_nonneg m]
  exact div_nonneg (mul_nonneg hx0.le h) (by linarith)

theorem tail_photonD_eq_log (P : Params) (hmγ : 0 < P.mγ) (hle : P.mγ ≤ P.Λ) {s : ℝ}
    (hs : -P.m ^ 2 ≤ s) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hx1 : x ≠ 1) :
    photonTail (photonD P.mγ P.Λ) (seArg P.m s x) =
      Real.log (QED.WickModel.selfEnergyFeynmanMass P.m P.Λ s x /
        QED.WickModel.selfEnergyFeynmanMass P.m P.mγ s x) := by
  have ha := seArg_nonneg hs hx
  have h1 : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx1)
  rw [photonTail_photonD (by positivity) (pow_le_pow_left₀ hmγ.le hle 2),
    selfEnergyFeynmanMass_eq_seArg _ _ _ hx1, selfEnergyFeynmanMass_eq_seArg _ _ _ hx1,
    mul_div_mul_left _ _ h1]

/-- **The anchor, `p̸` part**: for the Pauli–Villars photon, `A_R` is the frozen coefficient. -/
theorem seCoefA_photonD (P : Params) (hmγ : 0 < P.mγ) (hle : P.mγ ≤ P.Λ) {s : ℝ}
    (hs : -P.m ^ 2 ≤ s) :
    (seCoefA P.e P.m (photonD P.mγ P.Λ) s : ℂ) = QED.WickModel.selfEnergyLoopA P s := by
  have key : ∫ x in (0 : ℝ)..1, (1 - x) * photonTail (photonD P.mγ P.Λ) (seArg P.m s x) =
      ∫ x in (0 : ℝ)..1, (1 - x) * Real.log (QED.WickModel.selfEnergyFeynmanMass P.m P.Λ s x /
        QED.WickModel.selfEnergyFeynmanMass P.m P.mγ s x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [tail_photonD_eq_log P hmγ hle hs hx hx1]
  unfold seCoefA QED.WickModel.selfEnergyLoopA
  rw [key]

/-- **The anchor, `m` part**: for the Pauli–Villars photon, `B_R` is the frozen coefficient. -/
theorem seCoefB_photonD (P : Params) (hmγ : 0 < P.mγ) (hle : P.mγ ≤ P.Λ) {s : ℝ}
    (hs : -P.m ^ 2 ≤ s) :
    (seCoefB P.e P.m (photonD P.mγ P.Λ) s : ℂ) = QED.WickModel.selfEnergyLoopB P s := by
  have key : ∫ x in (0 : ℝ)..1, photonTail (photonD P.mγ P.Λ) (seArg P.m s x) =
      ∫ x in (0 : ℝ)..1, Real.log (QED.WickModel.selfEnergyFeynmanMass P.m P.Λ s x /
        QED.WickModel.selfEnergyFeynmanMass P.m P.mγ s x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [tail_photonD_eq_log P hmγ hle hs hx hx1]
  unfold seCoefB QED.WickModel.selfEnergyLoopB
  rw [key]

/-! ### The shell value -/

/-- **The shell value of the one-loop self-energy of `R`**:
`A_R(-m²)(-m) + B_R(-m²) m = -(e² m/8π²) ∫₀¹ (1+x) Tail_R(a₀) dx`. -/
theorem shellValue_seCoef (e m : ℝ) (R : ℝ → ℝ)
    (hA : IntervalIntegrable (fun x => (1 - x) * photonTail R (shellArg m x)) volume 0 1)
    (hB : IntervalIntegrable (fun x => photonTail R (shellArg m x)) volume 0 1) :
    seCoefA e m R (-m ^ 2) * (-m) + seCoefB e m R (-m ^ 2) * m =
      -(e ^ 2 * m / (8 * Real.pi ^ 2)) * seShellVal R m := by
  have e1 : seShellVal R m = 2 * (∫ x in (0 : ℝ)..1, photonTail R (shellArg m x)) -
      ∫ x in (0 : ℝ)..1, (1 - x) * photonTail R (shellArg m x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hB.const_mul 2) hA]
    unfold seShellVal
    congr 1
    funext x
    ring
  simp only [seCoefA, seCoefB, seArg_shell]
  rw [e1]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem intervalIntegrable_tail_vp {m mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T)
    (hm : 0 < m) {w : ℝ → ℝ} (hw : Measurable w) (hw1 : ∀ x ∈ Ioc (0 : ℝ) 1, ‖w x‖ ≤ 1) :
    IntervalIntegrable (fun x => w x * photonTail (vpPhotonT m mγ Λ T) (shellArg m x)) volume
      0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hmeas : Measurable fun x => w x * photonTail (vpPhotonT m mγ Λ T) (shellArg m x) :=
    hw.mul ((measurable_photonTail_vp m mγ Λ).comp
      (measurable_const.prodMk (measurable_shellArg m)))
  refine Measure.integrableOn_of_bounded (M := photonK mγ Λ / (T * m ^ 2) * Real.pi)
    (by simp) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
  have ha := shellArg_nonneg m (Ioc_subset_Icc_self hx)
  have h0 := photonTail_nonneg hmγ hΛ hT hm ha
  rw [norm_mul, Real.norm_of_nonneg h0]
  calc ‖w x‖ * photonTail (vpPhotonT m mγ Λ T) (shellArg m x) ≤
        1 * (photonK mγ Λ / (T * m ^ 2) * Real.pi) :=
        mul_le_mul (hw1 x hx) (photonTail_le hmγ hΛ hT hm ha) h0 zero_le_one
    _ = _ := one_mul _

/-- **`shellKer₀` is the shell value of the one-loop self-energy with photon function
`(e²/4π²) R_T`**: `shellKer₀ P₀ m_γ Λ T = (e²/4π²) (A_{R_T}(-m²)(-m) + B_{R_T}(-m²) m)`. -/
theorem shellKer₀_eq_shellValue (P₀ : Params) {mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hT : 0 < T) (hm : 0 < P₀.m) :
    shellKer₀ P₀ mγ Λ T = ((P₀.e ^ 2 / (4 * Real.pi ^ 2) *
      (seCoefA P₀.e P₀.m (vpPhotonT P₀.m mγ Λ T) (-P₀.m ^ 2) * (-P₀.m) +
        seCoefB P₀.e P₀.m (vpPhotonT P₀.m mγ Λ T) (-P₀.m ^ 2) * P₀.m) : ℝ) : ℂ) := by
  have hA := intervalIntegrable_tail_vp hmγ hΛ hT hm (w := fun x => 1 - x)
    (measurable_const.sub measurable_id) fun x hx => by
      rw [Real.norm_of_nonneg (by linarith [hx.2])]
      linarith [hx.1]
  have hB := intervalIntegrable_tail_vp hmγ hΛ hT hm (w := fun _ => 1) measurable_const
    fun x _ => by simp
  simp only [one_mul] at hB
  rw [shellValue_seCoef _ _ _ hA hB]
  unfold shellKer₀
  congr 1
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end QED.ChainProof.SetCRegDisp

end
