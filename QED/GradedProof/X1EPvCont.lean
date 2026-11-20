/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DParamCont
public import QED.GradedProof.X1DVPert
public import QED.GradedProof.RPi4VJV

/-!
# (X₁) piece E: parametric values are continuous at zero external momentum

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece E (the photon legs). The `ε → 0⁺` limits of the vacuum-polarization
classes are parametric values `QED.GradedProof.RPi4.pvOf` of numerators at line momenta `cᵢ k`.
At `k = 0` every line momentum vanishes, so `V = ∑ᵢ zᵢ Mᵢ²` (no threshold condition) and
`V ≥ c / 2` near `k = 0` (`QED.GradedProof.X1D.eventually_symanzikV_ge`).

* `continuousAt_pvOf_zero`: for a numerator polynomial in `k` at fixed loop momenta, with a
  quartic with integrable parametric numerators at every `k`, and all masses with `Mᵢ² ≥ c > 0`,
  `k ↦ pvOf (N k) α (cᵢ k) M` is continuous at `k = 0`. The proof is that of
  `QED.GradedProof.X1D.exists_tendsto_cont` (tensor interpolation in `k`, linearity of the
  parametric integrand in the quartic, dominated convergence), with the integrability of the
  parametric numerators as a hypothesis in place of the refined criterion.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.PauliZeroLimit (paramNum paramIntegrand_zero_eq)
open QED.TwoLoop.LimitCovariance (qsum eval_qsum paramIntegrand_qsum)

namespace QED.GradedProof.X1E

open QED.GradedProof.X1D QED.GradedProof.RPi4

/-- **`V ≥ c` at zero external momentum** when every mass has `Mᵢ² ≥ c`. -/
theorem symanzikV_zero_ge {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ)
    (M : Fin (m + 1) → ℝ) {c : ℝ} (hM : ∀ i, c ≤ M i ^ 2) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) :
    c ≤ symanzikV α (fun i => cs i • (0 : Fin 4 → ℝ)) M z := by
  rw [QED.GradedProof.SE2.symanzikV_smul_null α cs (by simp [Minkowski.dot_eq]) M z]
  calc c = ∑ i, z i * c := by rw [← Finset.sum_mul, hz1, one_mul]
    _ ≤ ∑ i, z i * M i ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hz i)

/-- **The parametric value is continuous at zero momentum.** -/
theorem continuousAt_pvOf_zero {m : ℕ} (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) (cs : Fin (m + 1) → ℝ)
    (M : Fin (m + 1) → ℝ) {c : ℝ} (hc : 0 < c) (hM : ∀ i, c ≤ M i ^ 2)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (paramNum Q α q M) (simplexSet m)) :
    ContinuousAt (fun k => pvOf (N k) α (fun i => cs i • k) M) 0 := by
  classical
  have hm0 : 0 < m := by omega
  set μS : Measure (Fin m → ℝ) := volume.restrict (simplexSet m) with hμS
  set mom : (Fin 1 → Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ := fun y i => cs i • y 0 with hmom_def
  have hmom : ∀ i ν, IsLoopPoly 1 1 fun y => ((mom y i ν : ℝ) : ℂ) := fun i ν => by
    have h := (IsLoopPoly.coord (L := 1) (n := 1) 0 ν le_rfl).const_mul (cs i : ℂ)
    refine (show (fun y : Fin 1 → Fin 4 → ℝ => ((mom y i ν : ℝ) : ℂ)) =
      fun y => (cs i : ℂ) * ((y 0 ν : ℝ) : ℂ) from funext fun y => ?_) ▸ h
    simp [hmom_def]
  have hmomc : Continuous mom :=
    continuous_pi fun i => (continuous_apply 0).const_smul (cs i)
  have hmom0 : mom 0 = fun i => cs i • (0 : Fin 4 → ℝ) := by
    funext i
    simp [hmom_def]
  -- `V ≥ c / 2` near `0`
  have hV := eventually_symanzikV_ge (α := α) hmomc.continuousAt M hc fun z hz hz1 _ => by
    rw [hmom0]
    exact symanzikV_zero_ge α cs M hM hz hz1
  have hVae : ∀ᶠ y in 𝓝 (0 : Fin 1 → Fin 4 → ℝ), ∀ᵐ x ∂μS,
      c / 2 ≤ symanzikV α (mom y) M (simplexPoint x) := by
    filter_upwards [hV] with y hy
    exact ae_le_symanzikV α M hm0 hspan hy
  have hc2 : 0 < c / 2 := half_pos hc
  -- the grid quartics
  choose Qf hQe hQi using hQ
  set Qk : (Fin 1 × Fin 4 → Fin (d + 1)) → LoopQuartic := fun κ => Qf (gridPt d κ 0) with hQk
  set Qy : (Fin 1 → Fin 4 → ℝ) → LoopQuartic := fun y =>
    qsum Finset.univ (fun κ => gridWt d κ y) Qk with hQy
  have hQyeval : ∀ y, (Qy y).eval = N (y 0) := fun y => by
    funext ℓ
    rw [hQy, eval_qsum, IsLoopPoly.eq_grid (hpoly ℓ) y]
    exact Finset.sum_congr rfl fun κ _ => by rw [hQk, hQe]
  have hVm : ∀ y, AEStronglyMeasurable
      (fun x => ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ)) μS := fun y =>
    (continuous_ofReal.measurable.comp ((measurable_symanzikV α (mom y) M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  -- the pieces
  set I : (Fin 1 × Fin 4 → Fin (d + 1)) → (Fin 1 → Fin 4 → ℝ) → ℂ := fun κ y =>
    ∫ x, paramNum (Qk κ) α (mom y) M x /
      ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3) ∂μS with hI
  have hdec : ∀ᶠ y in 𝓝 (0 : Fin 1 → Fin 4 → ℝ), pvOf (N (y 0)) α (mom y) M =
      -((π : ℂ) ^ 4) * ∑ κ, gridWt d κ y * I κ y := by
    filter_upwards [hVae] with y hy
    rw [pvOf_eq (hQyeval y)]
    congr 1
    have hint : ∀ κ, Integrable (fun x => gridWt d κ y * (paramNum (Qk κ) α (mom y) M x /
        ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3))) μS := fun κ => by
      refine Integrable.const_mul ?_ _
      have hb : ∀ᵐ x ∂μS, ‖(((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3))⁻¹‖ ≤
          ((c / 2) ^ (m - 3))⁻¹ := by
        filter_upwards [hy] with x hx
        rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hc2.trans_le hx)]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc2.le hx _)
      have hmeas : Measurable fun x =>
          (((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3))⁻¹ :=
        ((continuous_ofReal.measurable.comp ((measurable_symanzikV α (mom y) M).comp
          continuous_simplexPoint'.measurable)).pow_const _).inv
      have := Integrable.mul_bdd (f := fun x => paramNum (Qk κ) α (mom y) M x)
        (hQi (gridPt d κ 0) (mom y)) hmeas.aestronglyMeasurable hb
      simpa only [div_eq_mul_inv] using this
    have e1 : ∑ κ, gridWt d κ y * I κ y = ∫ x, ∑ κ, gridWt d κ y *
        (paramNum (Qk κ) α (mom y) M x /
          ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3)) ∂μS := by
      rw [integral_finsetSum _ fun κ _ => hint κ]
      exact Finset.sum_congr rfl fun κ _ => (integral_const_mul _ _).symm
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [hy] with x hx
    have hVx : symanzikV α (mom y) M (simplexPoint x) ≠ 0 := (hc2.trans_le hx).ne'
    simp only [hQy, paramIntegrand_qsum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [paramIntegrand_zero_eq (Qk κ) α (mom y) M hm hVx]
  have hcont : Tendsto (fun y => -((π : ℂ) ^ 4) * ∑ κ, gridWt d κ y * I κ y)
      (𝓝 (0 : Fin 1 → Fin 4 → ℝ)) (𝓝 (-((π : ℂ) ^ 4) * ∑ κ, gridWt d κ 0 * I κ 0)) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun κ _ => ?_)
    refine ((continuous_gridWt d κ).tendsto 0).mul ?_
    exact tendsto_integral_poly_div (μ := μS) (N := m - 3)
      (A := fun x y => paramNum (Qk κ) α (mom y) M x)
      (V := fun x y => symanzikV α (mom y) M (simplexPoint x))
      (fun x => isLoopPoly_paramNum (Qk κ) α mom M hmom x)
      (fun _ => hQi _ _) hc2 hVae
      (Eventually.of_forall fun x => by
        have h := IsLoopPoly.continuous (isLoopPoly_symanzikV α mom M (simplexPoint x) hmom)
        have h' : Continuous fun y => symanzikV α (mom y) M (simplexPoint x) := by
          have := continuous_re.comp h
          simpa [Function.comp_def] using this
        exact h'.continuousAt)
      (Eventually.of_forall hVm)
  have hy : ContinuousAt (fun y : Fin 1 → Fin 4 → ℝ => pvOf (N (y 0)) α (mom y) M) 0 := by
    refine (hcont.congr' (hdec.mono fun y hy => hy.symm)).trans (le_of_eq ?_)
    exact congrArg 𝓝 hdec.self_of_nhds.symm
  have hemb : Continuous fun k : Fin 4 → ℝ => (fun _ : Fin 1 => k) := continuous_pi fun _ =>
    continuous_id
  have h := ContinuousAt.comp (g := fun y : Fin 1 → Fin 4 → ℝ => pvOf (N (y 0)) α (mom y) M)
    (f := fun k : Fin 4 → ℝ => fun _ : Fin 1 => k) (x := 0) (by exact hy) hemb.continuousAt
  exact h

end QED.GradedProof.X1E

end
