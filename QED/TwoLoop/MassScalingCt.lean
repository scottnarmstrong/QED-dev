/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingBasic
public import QED.TwoLoop.PauliZeroExplicitCt
public import QED.TwoLoop.PauliZeroCovariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Mass scaling of the counterterm class values

For `s > 0` and all masses multiplied by `s` (`massScale s P`):

* `auxLimit_mul`: the auxiliary loop `∫ d³v (-(v² + M²))^{-5/2}` scales as `M⁻²`;
* `kindsZero_massScale`: a class of product data whose numerator is homogeneous of degree `d`,
  with `d + 2 = 2(m - 3)` for `m + 1` lines, scales by `s⁵`;
* `d2InZero_massScale`, `d2OutZero_massScale` (`d = 6`, eight lines), `d3Zero_massScale`
  (`d = 8`, nine lines);
* `oneLoopPauliZero_massScale`: the one-loop Pauli integral at `q² = 0` is invariant, hence
  `d1Zero_massScale`: `d1Zero (massScale s P) = s⁵ d1Zero P`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.Relabel
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix IntNoSubdivergenceRefined)

/-! ### The auxiliary loop -/

theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) (x : ℂ) {w : ℂ} (hw : w ≠ 0) :
    ((r : ℂ) * x) ^ w = (r : ℂ) ^ w * x ^ w := by
  by_cases hx : x = 0
  · simp [hx, zero_cpow hw]
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr' hx), cpow_def_of_ne_zero hr', cpow_def_of_ne_zero hx,
    log_ofReal_mul hr hx, ← exp_add, ← ofReal_log hr.le]
  ring_nf

theorem ofReal_sq_cpow {s : ℝ} (hs : 0 < s) :
    ((s ^ 2 : ℝ) : ℂ) ^ (-(5 / 2 : ℂ)) = ((s : ℂ) ^ 5)⁻¹ := by
  have h : ((s ^ 2 : ℝ) : ℂ) ^ (-(5 / 2 : ℂ)) = (((s ^ 2) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]
    norm_num
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  norm_num

theorem auxSpatial_mul {s : ℝ} (hs : 0 < s) (M : ℝ) (v : Fin 3 → ℝ) :
    auxSpatial (s * M) 0 (s • v) = ((s : ℂ) ^ 5)⁻¹ * auxSpatial M 0 v := by
  have e : -((((∑ k, (s • v) k ^ 2 + (s * M) ^ 2 : ℝ)) : ℂ) - ((0 : ℝ) : ℂ) * I) =
      ((s ^ 2 : ℝ) : ℂ) * -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - ((0 : ℝ) : ℂ) * I) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    push_cast
    ring
  simp only [auxSpatial]
  rw [e, ofReal_mul_cpow (by positivity) _ (by norm_num), ofReal_sq_cpow hs]
  ring

/-- **The auxiliary loop scales as `M⁻²`**: `auxLimit (s M) = s⁻² auxLimit M` for `s > 0`. -/
theorem auxLimit_mul {s : ℝ} (hs : 0 < s) (M : ℝ) :
    auxLimit (s * M) = ((s : ℂ) ^ 2)⁻¹ * auxLimit M := by
  have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Fin 3 → ℝ))
    (fun v => auxSpatial (s * M) 0 v) s
  simp only [auxSpatial_mul hs, integral_const_mul, Module.finrank_fin_fun] at h
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  unfold auxLimit
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  have h' : ∫ v : Fin 3 → ℝ, auxSpatial (s * M) 0 v =
      (s : ℂ) ^ 3 * (((s : ℂ) ^ 5)⁻¹ * ∫ v : Fin 3 → ℝ, auxSpatial M 0 v) := by
    rw [h]
    push_cast
    field_simp
  rw [h']
  field_simp

/-! ### Product data -/

theorem lineKind_mom_smul (κ : LineKind) (s : ℝ) (p p' : Fin 4 → ℝ) :
    κ.mom (s • p) (s • p') = s • κ.mom p p' := by
  cases κ <;> simp [LineKind.mom]

theorem kindsNum_massScale {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    (P : Params) (num num' : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    {d : ℕ} {s : ℝ} (hs : s ≠ 0)
    (hnum : ∀ p' μ k, num' (s • p') μ k = (s : ℂ) ^ d • num p' μ (s⁻¹ • k))
    (hF : ∀ p' μ i j, ∃ Q : LoopQuartic, Q.eval = fun ℓ => num p' μ (ℓ 0) i j)
    (x : Fin m → ℝ) (u : ℝ) :
    kindsNum κ (s • Ms) (massScale s P) num' x u =
      (s : ℂ) ^ (5 + d) * kindsNum κ Ms P num x u := by
  simp only [kindsNum, massScale_m, curveMomentum_smul, restMomentum_smul, pauliWt_smul,
    lineKind_mom_smul, hnum, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := paramNumOf_smul (hF (curveMomentum P.m u) j.1 j.2.1 j.2.2) ((s : ℂ) ^ d) hs
    (castLoopMatrix fun i => (κ i).dir)
    (fun i => (κ i).mom (restMomentum P.m) (curveMomentum P.m u)) Ms x
  simp only [Pi.smul_apply] at h
  rw [show (fun i => s • (κ i).mom (restMomentum P.m) (curveMomentum P.m u)) =
    s • fun i => (κ i).mom (restMomentum P.m) (curveMomentum P.m u) from rfl, h]
  ring

theorem kindsV_massScale {m : ℕ} (κ : Fin (m + 1) → LineKind) (Ms : Fin (m + 1) → ℝ)
    (P : Params) (s : ℝ) (x : Fin m → ℝ) :
    kindsV κ (s • Ms) (massScale s P) x = s ^ 2 * kindsV κ Ms P x := by
  simp only [kindsV, massScale_m, restMomentum_smul, lineKind_mom_smul]
  exact symanzikV_smul _ _ _ _ s

/-- **Mass scaling of a class of product data**: if the numerator is homogeneous of degree `d`
with `d + 2 = 2 (m - 3)`, the class value scales by `s⁵`. -/
theorem kindsZero_massScale {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = P.m ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (num num' : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hpoly : ∀ μ i j k, IsLoopPoly 1 4 fun y => num (y 0) μ k i j)
    (hF : ∀ p' μ i j, ∃ Q : LoopQuartic, Q.eval = fun ℓ => num p' μ (ℓ 0) i j)
    {d : ℕ} (hd : d + 2 = 2 * (m - 3)) {s : ℝ} (hs : 0 < s)
    (hnum : ∀ p' μ k, num' (s • p') μ k = (s : ℂ) ^ d • num p' μ (s⁻¹ • k)) :
    kindsZero κ (s • Ms) (massScale s P) num' = (s : ℂ) ^ 5 * kindsZero κ Ms P num := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hsc : ∀ x : Fin m → ℝ, ∀ a : ℂ, secondCoeff (fun u => a * kindsNum κ Ms P num x u) =
      a * secondCoeff (kindsNum κ Ms P num x) := fun x a => by
    have hpn : kindsNum κ Ms P num x = projNum (kindsCurve hm7 κ Ms P hm hμ₀ hMe hMp hcrit)
        (fun u (j : Idx) ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2)
        (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1
          j.2.2) x := rfl
    rw [hpn]
    exact secondCoeff_const_mul_projNum (kindsCurve hm7 κ Ms P hm hμ₀ hMe hMp hcrit) (D := 8)
      (n := 4) (r := 4) (Dω := 8)
      (fun u (j : Idx) ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2)
      (fun j => isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => num (y 0) j.1 (ℓ 0) j.2.1 j.2.2)
        (fun ℓ => hpoly j.1 j.2.1 j.2.2 (ℓ 0))
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν)
      (fun u _ j => hF _ j.1 j.2.1 j.2.2)
      (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
      (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m) x a
  unfold kindsZero
  rw [massScale_m, auxLimit_mul hs]
  have hI : ∫ x in simplexSet m, secondCoeff (kindsNum κ (s • Ms) (massScale s P) num' x) /
      ((kindsV κ (s • Ms) (massScale s P) x : ℝ) : ℂ) ^ (m - 3) =
      ((s : ℂ) ^ 2)⁻¹ * ((s : ℂ) ^ 5 * ∫ x in simplexSet m,
        secondCoeff (kindsNum κ Ms P num x) / ((kindsV κ Ms P x : ℝ) : ℂ) ^ (m - 3)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hN : kindsNum κ (s • Ms) (massScale s P) num' x =
        fun u => (s : ℂ) ^ (5 + d) * kindsNum κ Ms P num x u :=
      funext (kindsNum_massScale κ Ms P num num' hs.ne' hnum hF x)
    simp only [hN, kindsV_massScale, hsc]
    have hV : ((s ^ 2 * kindsV κ Ms P x : ℝ) : ℂ) ^ (m - 3) =
        (s : ℂ) ^ (d + 2) * ((kindsV κ Ms P x : ℝ) : ℂ) ^ (m - 3) := by
      rw [hd]
      push_cast
      ring
    have hq : (s : ℂ) ^ (5 + d) / (s : ℂ) ^ (d + 2) = ((s : ℂ) ^ 2)⁻¹ * (s : ℂ) ^ 5 := by
      field_simp
      ring
    rw [hV, mul_div_mul_comm, hq]
    ring
  rw [hI]
  by_cases h0 : auxLimit P.m = 0
  · simp [h0]
  field_simp

/-! ### `δ₂`, `δ₃` -/

theorem fermionCtMatrix_smul (δ₂ δm s m : ℝ) (k : Fin 4 → ℝ) :
    fermionCtMatrix δ₂ δm (s * m) (s • k) = (s : ℂ) • fermionCtMatrix δ₂ δm m k := by
  simp only [fermionCtMatrix, slash_smul, smul_add, smul_smul, ofReal_mul]
  congr 2
  · ring
  · ring

theorem pvPhotonNum_mul (s mγ Λ : ℝ) :
    pvPhotonNum (s * mγ) (s * Λ) = fun ν ρ => (s : ℂ) ^ 2 * pvPhotonNum mγ Λ ν ρ := by
  funext ν ρ
  simp only [pvPhotonNum]
  push_cast
  ring

theorem vertexChain_smul (e : ℝ) (μ : Fin 4) (a b c : ℂ) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ (a • A) (b • B) (fun ν ρ => c * D ν ρ) =
      (a * b * c) • vertexChain e μ A B D := by
  simp only [vertexChain, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  congr 1
  ring

theorem insertion_smul (P : Params) (s : ℝ) (k : Fin 4 → ℝ) :
    -(electronNumerator (s * P.m) (s • k) * fermionCtMatrix P.δ₂ P.δm (s * P.m) (s • k) *
      electronNumerator (s * P.m) (s • k)) =
    ((s : ℂ) ^ 3) • -(electronNumerator P.m k * fermionCtMatrix P.δ₂ P.δm P.m k *
      electronNumerator P.m k) := by
  rw [electronNumerator_smul, fermionCtMatrix_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_neg]
  congr 2
  ring

theorem numD2In_massScale (s : ℝ) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    numD2In (massScale s P) (s • p') (s • p) μ (s • k) = (s : ℂ) ^ 6 • numD2In P p' p μ k := by
  have e1 : s • p' + s • k = s • (p' + k) := (smul_add s p' k).symm
  have e2 : s • p + s • k = s • (p + k) := (smul_add s p k).symm
  simp only [numD2In, massScale_m, massScale_e, massScale_δ₂, massScale_δm, massScale_mγ,
    massScale_Λ, e1, e2, electronNumerator_smul, fermionCtMatrix_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← smul_neg, pvPhotonNum_mul, vertexChain_smul]
  congr 1
  ring

theorem numD2Out_massScale (s : ℝ) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 4 → ℝ) :
    numD2Out (massScale s P) (s • p') (s • p) μ (s • k) = (s : ℂ) ^ 6 • numD2Out P p' p μ k := by
  have e1 : s • p' + s • k = s • (p' + k) := (smul_add s p' k).symm
  have e2 : s • p + s • k = s • (p + k) := (smul_add s p k).symm
  simp only [numD2Out, massScale_m, massScale_e, massScale_δ₂, massScale_δm, massScale_mγ,
    massScale_Λ, e1, e2, electronNumerator_smul, fermionCtMatrix_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← smul_neg, pvPhotonNum_mul, vertexChain_smul]
  congr 1
  ring

theorem photonCtFactor_smul (δ₃ s : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    photonCtFactor δ₃ (s • k) a b = (s : ℂ) ^ 2 * photonCtFactor δ₃ k a b := by
  simp only [photonCtFactor, dot_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem photonNum_mul (δ₃ s mγ Λ : ℝ) (k : Fin 4 → ℝ) :
    photonNum δ₃ (s * mγ) (s * Λ) (s • k) = fun ν ρ => (s : ℂ) ^ 6 * photonNum δ₃ mγ Λ k ν ρ := by
  funext ν ρ
  simp only [photonNum, pvPhotonNum_mul, photonCtFactor_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem numD3_massScale (s : ℝ) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    numD3 (massScale s P) (s • p') (s • p) μ (s • k) = (s : ℂ) ^ 8 • numD3 P p' p μ k := by
  have e1 : s • p' + s • k = s • (p' + k) := (smul_add s p' k).symm
  have e2 : s • p + s • k = s • (p + k) := (smul_add s p k).symm
  simp only [numD3, massScale_m, massScale_e, massScale_δ₃, massScale_mγ, massScale_Λ, e1, e2,
    electronNumerator_smul, photonNum_mul, vertexChain_smul]
  congr 1
  ring

theorem massesD2In_massScale (s : ℝ) (P : Params) :
    massesD2In (massScale s P) = s • massesD2In P := by
  funext i
  fin_cases i <;> simp [massesD2In]

theorem massesD3_massScale (s : ℝ) (P : Params) : massesD3 (massScale s P) = s • massesD3 P := by
  funext i
  fin_cases i <;> simp [massesD3]

/-- A numerator homogeneous in the form used by `kindsZero_massScale`. -/
theorem hnum_of_scale {s : ℝ} (hs : s ≠ 0) {d : ℕ}
    (N N' : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ p' p μ k, N' (s • p') (s • p) μ (s • k) = (s : ℂ) ^ d • N p' p μ k)
    (p : Fin 4 → ℝ) (p' : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    N' (s • p') (s • p) μ k = (s : ℂ) ^ d • N p' p μ (s⁻¹ • k) := by
  have hk : k = s • (s⁻¹ • k) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  conv_lhs => rw [hk]
  exact hN _ _ _ _

theorem d2InZero_massScale (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ}
    (hs : 0 < s) : d2InZero (massScale s P) = (s : ℂ) ^ 5 * d2InZero P := by
  unfold d2InZero
  rw [massesD2In_massScale]
  refine kindsZero_massScale (by norm_num) kindsD2In (massesD2In P) P hm (lt_min hmγ hΛ)
    (QED.TwoLoop.ReflCovariance.massesD2In_sq_of_ne_pho P)
    (QED.TwoLoop.ReflCovariance.min_sq_le_massesD2In_sq P hmγ hΛ)
    QED.TwoLoop.ReflCovariance.intNoSubdivergenceRefined_kindsD2In
    (fun p' μ k => numD2In P p' (restMomentum P.m) μ k) _
    (fun μ i j k => isLoopPoly_numD2In_out P _ μ i j k)
    (fun p' μ i j => (isLoopPoly_numD2In P p' _ μ i j).exists_loopQuartic) (d := 6) (by norm_num)
    hs (fun p' μ k => ?_)
  rw [massScale_m, restMomentum_smul]
  exact hnum_of_scale hs.ne' (numD2In P) (numD2In (massScale s P))
    (numD2In_massScale s P) _ _ _ _

theorem d2OutZero_massScale (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ}
    (hs : 0 < s) : d2OutZero (massScale s P) = (s : ℂ) ^ 5 * d2OutZero P := by
  unfold d2OutZero
  rw [massesD2In_massScale]
  refine kindsZero_massScale (by norm_num) kindsD2Out (massesD2In P) P hm (lt_min hmγ hΛ)
    (QED.TwoLoop.PauliZero.massesD2In_sq_of_ne_pho_out P)
    (QED.TwoLoop.PauliZero.min_sq_le_massesD2In_sq_out P hmγ hΛ)
    QED.TwoLoop.PauliZero.intNoSubdivergenceRefined_kindsD2Out
    (fun p' μ k => numD2Out P p' (restMomentum P.m) μ k) _
    (fun μ i j k => isLoopPoly_numD2Out_out P _ μ i j k)
    (fun p' μ i j => (isLoopPoly_numD2Out P p' _ μ i j).exists_loopQuartic) (d := 6)
    (by norm_num) hs (fun p' μ k => ?_)
  rw [massScale_m, restMomentum_smul]
  exact hnum_of_scale hs.ne' (numD2Out P) (numD2Out (massScale s P))
    (numD2Out_massScale s P) _ _ _ _

theorem d3Zero_massScale (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ}
    (hs : 0 < s) : d3Zero (massScale s P) = (s : ℂ) ^ 5 * d3Zero P := by
  unfold d3Zero
  rw [massesD3_massScale]
  refine kindsZero_massScale (by norm_num) kindsD3 (massesD3 P) P hm (lt_min hmγ hΛ)
    (QED.TwoLoop.ReflCovariance.massesD3_sq_of_ne_pho P)
    (QED.TwoLoop.ReflCovariance.min_sq_le_massesD3_sq P hmγ hΛ)
    QED.TwoLoop.ReflCovariance.intNoSubdivergenceRefined_kindsD3
    (fun p' μ k => numD3 P p' (restMomentum P.m) μ k) _
    (fun μ i j k => isLoopPoly_numD3_out P _ μ i j k)
    (fun p' μ i j => (isLoopPoly_numD3 P p' _ μ i j).exists_loopQuartic) (d := 8) (by norm_num)
    hs (fun p' μ k => ?_)
  rw [massScale_m, restMomentum_smul]
  exact hnum_of_scale hs.ne' (numD3 P) (numD3 (massScale s P)) (numD3_massScale s P) _ _ _ _

/-! ### `δ₁` -/

theorem pauliIntegrand_mul {s : ℝ} (hs : s ≠ 0) (m mγ Λ : ℝ) (z : ℝ × ℝ) :
    QED.OneLoop.VertexLimit.pauliIntegrand (s * m) (s * mγ, s * Λ, 0) z =
      QED.OneLoop.VertexLimit.pauliIntegrand m (mγ, Λ, 0) z := by
  simp only [QED.OneLoop.VertexLimit.pauliIntegrand, mul_zero, add_zero]
  set X := (1 - z.2) * mγ ^ 2 + z.2 ^ 2 * m ^ 2
  set Y := (1 - z.2) * Λ ^ 2 + z.2 ^ 2 * m ^ 2
  have hX : (1 - z.2) * (s * mγ) ^ 2 + z.2 ^ 2 * (s * m) ^ 2 = s ^ 2 * X := by ring
  have hY : (1 - z.2) * (s * Λ) ^ 2 + z.2 ^ 2 * (s * m) ^ 2 = s ^ 2 * Y := by ring
  have h1 : s ^ 2 * (s ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hs)
  rw [hX, hY, mul_inv, mul_inv]
  linear_combination (2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 * (X⁻¹ - Y⁻¹)) * h1

theorem oneLoopPauliZero_massScale (P : Params) {s : ℝ} (hs : s ≠ 0) :
    oneLoopPauliZero (massScale s P) = oneLoopPauliZero P := by
  simp only [oneLoopPauliZero, massScale_m, massScale_mγ, massScale_Λ, pauliIntegrand_mul hs]

theorem d1Zero_massScale (P : Params) {s : ℝ} (hs : 0 < s) :
    d1Zero (massScale s P) = (s : ℂ) ^ 5 * d1Zero P := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  simp only [d1Zero, oneLoopPauliZero_massScale P hs.ne', massScale_m, massScale_e, massScale_δ₁]
  push_cast
  by_cases hm : (P.m : ℂ) = 0
  · simp [hm]
  field_simp

end QED.TwoLoop.MassScaling

end
