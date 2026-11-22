/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitCov
public import QED.TwoLoop.PauliZeroExplicitOpen

/-!
# Two-loop vertex units with a free mass on each photon line: the `q² → 0⁺` Pauli value

Helper level for set (c) (stage L1). The explicit `q² → 0⁺` limit of the Phase 4 open-line
classes (`QED.TwoLoop.PauliZeroExplicit.tendsto_open_explicit`, value `openZero c P`) uses the
curve engine `QED.TwoLoop.PauliZeroExplicit.tendsto_piece_explicit`, which is generic in the line
masses. This file runs it at the masses `unitMasses m a A b B`.

Along the curve `p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`, `p = (m, 0, 0, 0)`:

* `unitCurve`: the parametric data of the unit along the curve (`V ≥ (3/4) min(m²/4, μ₀²)`);
* `unitPauliZero c P a A b B = ∫_{Δ₇} c₂[N_c(x, ·)] / V_c(x)⁴ dx`, the Phase 4 formula with the
  masses of the unit (`unitPauliZero_pvMasses`: it is `openZero c P` at `a = b = m_γ`,
  `A = B = Λ`);
* **`tendsto_unit_explicit`**: `(S(u) + S(-u))/(2u²) → unitPauliZero` for `S(u)` (`unitPauliS`)
  the Pauli numerator of the unit limit along the curve;
* `unitPauliS_neg`: `S` is even (reflection covariance, `unitLimitV_map`), so
  `S(u)/u² → unitPauliZero` (`tendsto_unitPauliS_div`);
* **`tendsto_formFactorProj₂_unit`**: the Pauli projection of the unit limit at the canonical pair
  with `q² = Q` tends, as `Q → 0⁺`, to `unitPauliZero / (64 e m⁵)`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.ChainProof.SetCUnit

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV
  symanzikV symanzikU pvLines)

/-- The parametric data of the two-mass unit along the curve. -/
noncomputable def unitCurve {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) : CurveData where
  m := 7
  α := castLoopMatrix (class5LoopMatrixPV c)
  mom u := pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)
  M := unitMasses P.m a A b B
  E := {0, 1, 2, 3}
  hm := by norm_num
  hcrit := noSubdivergenceRefined_unit hc
  c := unitConst P.m μ₀
  hc := unitConst_pos hm hμ₀
  hV := fun u hu _ hz hz1 hU => symanzikV_unit_ge hc hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hz
    hz1 hU
  hmom := fun i μ => isUPoly_ext_curve P.m
    (fun p' => extMomenta c (restMomentum P.m) p' (pvLines i)) (by
      rcases extMomenta_cases c (restMomentum P.m) (pvLines i) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) μ
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h (castLoopMatrix (class5LoopMatrixPV c))
      (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)) (unitMasses P.m a A b B) z
    rw [← QED.TwoLoop.ReflCovariance.pvMomentaE_map, reflectMatrix_restMomentum,
      reflectMatrix_curveMomentum] at e
    exact e

/-- The Pauli-projected parametric numerator of the unit along the curve. -/
noncomputable def unitPauliNum (c : Class5) (P : Params) (M : Fin 8 → ℝ) (x : Fin 7 → ℝ) (u : ℝ) :
    ℂ :=
  ∑ j : Idx, pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
    (-((π : ℂ) ^ 4) * paramNumOf (openF c P (curveMomentum P.m u) j)
      (castLoopMatrix (class5LoopMatrixPV c))
      (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)) M x)

/-- The second Symanzik function of the unit at `q = 0`. -/
noncomputable def unitV0 (c : Class5) (P : Params) (M : Fin 8 → ℝ) (x : Fin 7 → ℝ) : ℝ :=
  symanzikV (castLoopMatrix (class5LoopMatrixPV c))
    (pvMomentaE c (restMomentum P.m) (restMomentum P.m)) M (simplexPoint x)

/-- **The `q → 0` value of the two-mass unit**: `∫_{Δ₇} c₂[N_c(x, ·)] / V_c(x)⁴ dx` at the masses
`unitMasses m a A b B`. -/
noncomputable def unitPauliZero (c : Class5) (P : Params) (a A b B : ℝ) : ℂ :=
  ∫ x in simplexSet 7, secondCoeff (unitPauliNum c P (unitMasses P.m a A b B) x) /
    ((unitV0 c P (unitMasses P.m a A b B) x : ℝ) : ℂ) ^ 4

/-- **Phase 4 recovered**: at equal masses the unit value is `openZero c P`. -/
theorem unitPauliZero_pvMasses (c : Class5) (P : Params) :
    unitPauliZero c P P.mγ P.Λ P.mγ P.Λ = openZero c P := rfl

/-- The Pauli numerator of the unit limit along the curve. -/
noncomputable def unitPauliS (c : Class5) (P : Params) (a A b B u : ℝ) : ℂ :=
  pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
    (unitLimitV c P (unitMasses P.m a A b B) (restMomentum P.m) (curveMomentum P.m u))

section Pauli

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {μ₀ a A b B : ℝ}
  (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
include hc hm hμ₀ hM

/-- **The explicit second-order limit of the two-mass unit.** -/
theorem tendsto_unit_explicit :
    Tendsto (fun u : ℝ => (unitPauliS c P a A b B u + unitPauliS c P a A b B (-u)) /
      (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 (unitPauliZero c P a A b B)) := by
  have hF : ∀ (p' : Fin 4 → ℝ) (j : Idx),
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) =
        fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => restMomentum P.m)
          (fun _ => p' - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1) ℓ :=
    fun p' j => funext fun ℓ => by simp only [Matrix.smul_apply, classNumM, Matrix.of_apply,
      smul_eq_mul]
  have hB : ∀ (p' : Fin 4 → ℝ) (j : Idx), RefinedBound (castLoopMatrix (class5LoopMatrixPV c))
      {0, 1, 2, 3} 4
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) :=
    fun p' j => by
      rw [hF]
      exact (refinedBound_classNumeratorE hc P _ _ _ _ _ _).const_mul _
  have hL := tendsto_piece_explicit (unitCurve hc P hm hμ₀ hM) (J := Idx) (D := 8) (n := 4)
    (r := 4) (Dω := 8)
    (fun u j ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) (curveMomentum P.m u) j.1 ℓ)
      j.2.1 j.2.2)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (fun u _ j => by
      rw [hF]
      exact ((isLoopPoly_classNumeratorE hc P _ _ _ _ _ _).const_mul _).exists_loopQuartic)
    (fun u _ j => hB _ j)
    (fun u j => unitLimitV c P (unitMasses P.m a A b B) (restMomentum P.m)
      (curveMomentum P.m u) j.1 j.2.1 j.2.2)
    (fun u hu j => by
      obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_unitLimitV hc P hm hμ₀ hM
        (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) j.1 j.2.1 j.2.2
      exact ⟨Q, hQ, hB _ j, hv⟩)
    (fun u j => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
  have hval : (∫ x in simplexSet (unitCurve hc P hm hμ₀ hM).m,
      secondCoeff (projNum (unitCurve hc P hm hμ₀ hM)
        (fun u (j : Idx) ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m)
          (curveMomentum P.m u) j.1 ℓ) j.2.1 j.2.2)
        (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
        x) /
        (((unitCurve hc P hm hμ₀ hM).vfun x 0 : ℝ) : ℂ) ^ ((unitCurve hc P hm hμ₀ hM).m - 3)) =
      unitPauliZero c P a A b B := by
    simp only [unitPauliZero, unitV0, CurveData.vfun, unitCurve, curveMomentum_zero]
    rfl
  rw [hval] at hL
  exact hL.congr fun u => by simp only [unitPauliS, pauliNum_eq_sum_idx]

/-- **The Pauli numerator of the unit limit along the curve is even in `u`.** -/
theorem unitPauliS_neg {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    unitPauliS c P a A b B (-u) = unitPauliS c P a A b B u := by
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
    (by rw [dot_axisOne]; exact one_ne_zero)
  have hW := unitLimitV_map hc P hm hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) h
  have e := pauliNum_map h P.m (curveMomentum P.m u) (restMomentum P.m) hW
  rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum] at e
  exact e

/-- `S(u)/u² → unitPauliZero` as `u → 0`, `u ≠ 0`. -/
theorem tendsto_unitPauliS_div :
    Tendsto (fun u => unitPauliS c P a A b B u / (u : ℂ) ^ 2) (𝓝[≠] 0)
      (𝓝 (unitPauliZero c P a A b B)) := by
  refine (tendsto_unit_explicit hc P hm hμ₀ hM).congr' ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0] with u hu
  rw [unitPauliS_neg hc P hm hμ₀ hM hu]
  by_cases hu0 : (u : ℂ) = 0
  · simp [hu0]
  · field_simp
    ring

end Pauli

/-! ### From the curve to `q² → 0⁺` -/

/-- **The Pauli projection along the curve** for any vertex function `W` of the outgoing momentum:
`P₂ = m (1-u²)³ N(u) / (64 e m⁶ u²)`, `N` the Pauli numerator of `W` along the curve. -/
theorem formFactorProj₂_curveQ {m : ℝ} (hm : 0 < m) (e : ℝ)
    (W : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    QED.OneLoop.formFactorProj₂ e m (boostMomentum m (curveQ m u)) (restMomentum m)
        (W (boostMomentum m (curveQ m u))) =
      (m : ℂ) * ((1 - u ^ 2 : ℝ) : ℂ) ^ 3 / ((e : ℂ) * 64 * (m : ℂ) ^ 6) *
        (pauliNum m (curveMomentum m u) (restMomentum m) (W (curveMomentum m u)) /
          (u : ℂ) ^ 2) := by
  have hu : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hu1⟩
  have hw := (one_sub_sq_pos hu).ne'
  have hw' : (1 - (u : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hw
  have hu' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
  have hm' : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  rw [boostMomentum_curveQ hm hu0.le hu1, formFactorProj₂_eq_pauliNum,
    dot_curveMomentum_sub m hu]
  unfold curveQ
  push_cast
  by_cases he : e = 0
  · subst he
    simp
  have he' : (e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  have hD : 4 * (m : ℂ) ^ 2 + 4 * (m : ℂ) ^ 2 * (u : ℂ) ^ 2 / (1 - (u : ℂ) ^ 2) =
      4 * (m : ℂ) ^ 2 / (1 - (u : ℂ) ^ 2) := by
    field_simp
    ring
  rw [hD]
  field_simp
  ring

/-- **From `N(u)/u² → L` to the `q² → 0⁺` limit of the Pauli projection**, for any vertex function
`W` of the outgoing momentum: `P₂(Q) → L / (64 e m⁵)`. -/
theorem tendsto_formFactorProj₂_of {m : ℝ} (hm : 0 < m) (e : ℝ)
    (W : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) {L : ℂ}
    (hL : Tendsto (fun u => pauliNum m (curveMomentum m u) (restMomentum m)
      (W (curveMomentum m u)) / (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 L)) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e m (boostMomentum m Q) (restMomentum m)
        (W (boostMomentum m Q))) (𝓝[>] 0) (𝓝 (L / (64 * (e : ℂ) * (m : ℂ) ^ 5))) := by
  set K : ℝ → ℂ := fun u => (m : ℂ) * ((1 - u ^ 2 : ℝ) : ℂ) ^ 3 /
    ((e : ℂ) * 64 * (m : ℂ) ^ 6) with hK_def
  have hK : Tendsto K (𝓝[>] 0) (𝓝 (K 0)) := by
    have hc : Continuous K := by
      simp only [hK_def]
      fun_prop
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hL' : Tendsto (fun u => pauliNum m (curveMomentum m u) (restMomentum m)
      (W (curveMomentum m u)) / (u : ℂ) ^ 2) (𝓝[>] 0) (𝓝 L) :=
    hL.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have hF : Tendsto (fun u => QED.OneLoop.formFactorProj₂ e m (boostMomentum m (curveQ m u))
      (restMomentum m) (W (boostMomentum m (curveQ m u)))) (𝓝[>] 0) (𝓝 (K 0 * L)) := by
    refine (hK.mul hL').congr' ?_
    have h1 : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h1] with u hu0 hu1
    exact (formFactorProj₂_curveQ hm e W hu0 hu1).symm
  have hm2 : 0 < 4 * m ^ 2 := by positivity
  set uQ : ℝ → ℝ := fun Q => Real.sqrt (Q / (4 * m ^ 2 + Q)) with huQ_def
  have huQc : Tendsto uQ (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun Q : ℝ => Q / (4 * m ^ 2 + Q)) 0 :=
      ContinuousAt.div continuousAt_id (by fun_prop) (by simp; positivity)
    have h := (Real.continuous_sqrt.continuousAt.comp hc).tendsto
    simp only [Function.comp_def, zero_div, Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have huQ : Tendsto uQ (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨huQc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
    exact Real.sqrt_pos.mpr (div_pos hQ (by positivity))
  have hcq : ∀ Q : ℝ, 0 < Q → curveQ m (uQ Q) = Q := fun Q hQ => by
    have hr : 0 ≤ Q / (4 * m ^ 2 + Q) := (div_pos hQ (by positivity)).le
    simp only [huQ_def, curveQ, Real.sq_sqrt hr]
    have h4 : (4 * m ^ 2 + Q) ≠ 0 := by positivity
    have h5 : 1 - Q / (4 * m ^ 2 + Q) = 4 * m ^ 2 / (4 * m ^ 2 + Q) := by
      field_simp
      ring
    rw [h5]
    field_simp
  have hval : K 0 * L = L / (64 * (e : ℂ) * (m : ℂ) ^ 5) := by
    have hm' : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
    simp only [hK_def]
    by_cases he : (e : ℂ) = 0
    · simp [he]
    · push_cast
      field_simp
      ring
  rw [← hval]
  refine (hF.comp huQ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
  simp only [Function.comp_apply, hcq Q hQ]

/-- **The `q² → 0⁺` Pauli value of the two-mass unit**: at the canonical pair with `q² = Q`, the
Pauli projection of the unit limit tends to `unitPauliZero c P a A b B / (64 e m⁵)` as `Q → 0⁺`. -/
theorem tendsto_formFactorProj₂_unit {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) (e : ℝ) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
        (unitLimitV c P (unitMasses P.m a A b B) (restMomentum P.m) (boostMomentum P.m Q)))
      (𝓝[>] 0) (𝓝 (unitPauliZero c P a A b B / (64 * (e : ℂ) * (P.m : ℂ) ^ 5))) :=
  tendsto_formFactorProj₂_of hm e
    (fun p' => unitLimitV c P (unitMasses P.m a A b B) (restMomentum P.m) p')
    (tendsto_unitPauliS_div hc P hm hμ₀ hM)

end QED.ChainProof.SetCUnit

end
