/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBZeroJ
public import QED.ChainProof.SetCPauliAtCD
public import QED.TwoLoop.VPHalfAtLimitPauli
public import QED.TwoLoop.VPUnitNestedAlgebra
import Mathlib.Tactic.Ring

/-!
# The doubled `CD` pieces of the mass part: fixed-`q` values and `q → 0` limits

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 6. At
`Q = cbBParams …` the classes `CD1 t`, `CD0 t` have a piece with the inserted electron line
doubled (`numIn₂`, `numOut₂`). Its photon numerator is the `δ₃` insertion, so its Pauli projection
is `c k² Pg(k)` (the longitudinal part drops out exactly, `pauliNum_longitudinal`), and the piece
is the power-weighted doubled vertex `dblPowInt` with `j = 1` and photon masses
`(m_γ, Λ, m_γ, Λ)`.

* `pauliNum_numIn₂`, `pauliNum_numOut₂`: the Pauli projections, `cdCoeff Q · k² · Pg(k)`;
* **`pauliNum_pieceLim_in`**, **`pauliNum_pieceLim_out`**: at fixed on-shell `p', p` with
  `q² > 0`, the Pauli projection of the limit `pieceLim` is `cdCoeff Q · dblValJ … 1 (phMs Q) d`
  (linearity and uniqueness of parametric values, no integrability needed);
* `tendsto_evenQuot_cd`: the even quotient along the curve tends to `cdZeroVal Q d`;
* **`kindsZero_in_eq`**, **`kindsZero_out_eq`**: Phase 4's `kindsZero` of the two doubled pieces
  equals the explicit `cdZeroVal Q d`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open QED.WickModel (Params)

namespace QED.ChainProof.CtLoB

open QED.Dirac QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPUnitNested QED.ChainProof.SetCPauli QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.PauliZeroExplicit

/-- The coefficient of `k² Pg(k)` in the Pauli projection of the doubled `CD` numerators. -/
noncomputable def cdCoeff (P : Params) : ℂ :=
  mergeC P.m P.δ₂ P.δm * ((P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ)

/-- The Pauli projection of the doubled `CD1` numerator is `cdCoeff P · k² · Pg(k)`. -/
theorem pauliNum_numIn₂ (P : Params) (hm : P.m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => numIn₂ P p' p μ k) =
      cdCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * pauliChain P.e P.m p' p k := by
  simp only [numIn₂, photonNum_eq, ← neg_smul, vertexChain_smul_in, vertexChain_add_photon,
    vertexChain_smul_photon, smul_smul]
  rw [QED.TwoLoop.PauliZeroLimit.pauliNum_add, pauliNum_smul, pauliNum_smul,
    pauliNum_longitudinal P.e hm hp' hp hq k, pauliChain, cdCoeff]
  ring

/-- The Pauli projection of the doubled `CD0` numerator is `cdCoeff P · k² · Pg(k)`. -/
theorem pauliNum_numOut₂ (P : Params) (hm : P.m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => numOut₂ P p' p μ k) =
      cdCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * pauliChain P.e P.m p' p k := by
  simp only [numOut₂, photonNum_eq, ← neg_smul, vertexChain_smul_out, vertexChain_add_photon,
    vertexChain_smul_photon, smul_smul]
  rw [QED.TwoLoop.PauliZeroLimit.pauliNum_add, pauliNum_smul, pauliNum_smul,
    pauliNum_longitudinal P.e hm hp' hp hq k, pauliChain, cdCoeff]
  ring

/-- The four photon masses `(m_γ, Λ, m_γ, Λ)` of the `δ₃` insertion. -/
noncomputable def phMs (P : Params) : Fin (2 + 2) → ℝ := ![P.mγ, P.Λ, P.mγ, P.Λ]

theorem denIn₂_mul_eq (P : Params) (p' p : Fin 4 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ) :
    denIn₂ P p' p ε k * (cdCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * pauliChain P.e P.m p' p k) =
      cdCoeff P * dblPowInt (pauliChain P.e P.m p' p) P.m 1 (phMs P) (fun _ => ε) ε 0 p' p k := by
  simp only [denIn₂, phDen, dblPowInt, dblProdIntegrand, dblMom, Fin.prod_univ_succ,
    Fin.prod_univ_zero, phMs, mul_inv, pow_one, propDenom, QED.OneLoop.denom]
  simp
  ring

theorem denOut₂_mul_eq (P : Params) (p' p : Fin 4 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ) :
    denOut₂ P p' p ε k * (cdCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * pauliChain P.e P.m p' p k) =
      cdCoeff P * dblPowInt (pauliChain P.e P.m p' p) P.m 1 (phMs P) (fun _ => ε) ε 1 p' p k := by
  simp only [denOut₂, phDen, dblPowInt, dblProdIntegrand, dblMom, Fin.prod_univ_succ,
    Fin.prod_univ_zero, phMs, mul_inv, pow_one, propDenom, QED.OneLoop.denom]
  simp
  ring

theorem le_phMs (P : Params) (i : Fin (2 + 2)) : min P.mγ P.Λ ≤ phMs P i := by
  fin_cases i <;> simp [phMs]

theorem phMs_pos (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (i : Fin (2 + 2)) :
    0 < phMs P i :=
  (lt_min hmγ hΛ).trans_le (le_phMs P i)

theorem efi_const_mul' (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => c * F ℓ) =
      c * QED.OneLoop.energyFirstIntegral F := by
  simp only [QED.OneLoop.energyFirstIntegral, MeasureTheory.integral_const_mul]

section Fixed

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
  (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp' hp hp0' hp0 hq

/-- The engine limit of the doubled `CD` pieces. -/
theorem tendsto_efi_cd (d : Fin 2) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral
        (dblPowInt (pauliChain P.e P.m p' p) P.m 1 (phMs P) (fun _ => ε) ε d p' p))
      (𝓝[>] 0) (𝓝 (dblValJ P.e P.m p' p 1 (phMs P) d)) := by
  obtain ⟨α, hα⟩ := pauliChain_quadratic P.e P.m p' p
  obtain ⟨CN, hCN⟩ := pauliChain_bound P.e P.m p' p
  have h := tendsto_efi_dblPowInt (M₀ := min P.mγ P.Λ) hm (lt_min hmγ hΛ) hp' hp hp0' hp0
    (continuous_pauliChain P.e P.m p' p) hα hCN d (l := 𝓝[>] (0 : ℝ)) (ε := id) tendsto_id 1 2
    (by norm_num) (phMs P) (fun t _ => t) (le_phMs P) (fun _ => tendsto_id)
  rwa [dblPowLimit_pauliChain_eq hm hp' hp hp0' hp0 hq hα 1 (phMs P) (by norm_num)
    (phMs_pos P hmγ hΛ) d] at h

/-- **The Pauli projection of the doubled `CD1` piece at fixed `q² > 0`.** -/
theorem pauliNum_pieceLim_in :
    pauliNum P.m p' p (pieceLim (denIn₂ P p' p) (numIn₂ P p' p)) =
      cdCoeff P * dblValJ P.e P.m p' p 1 (phMs P) 0 := by
  classical
  have hN : ∀ μ i j, IsLoopPoly 2 4 fun ℓ => numIn₂ P p' p μ (ℓ 0) i j :=
    fun μ i j => (affMat_numIn₂ P p' p μ i j).isLoopPoly
  choose v hv _hT hV using fun x : Idx => pieceLim_entry (by norm_num) kindsIn₂ (massesD₂ P) hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_in P) (min_sq_le_massesD₂_sq_in P hmγ hΛ)
    intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide) hp hp' hq.le (denIn₂ P p' p)
    (numIn₂ P p' p) hN (fun ε _ ℓ => denIn₂_fac P p p' ε ℓ) x.1 x.2.1 x.2.2
  set w : Idx → ℂ := fun x => pauliWt P.m p' p x.1 x.2.1 x.2.2
  have hsum := IsParamValue.sum Finset.univ w fun x _ => hv x
  set Np : (Fin 4 → ℝ) → ℂ := fun k => ∑ x : Idx, w x * numIn₂ P p' p x.1 k x.2.1 x.2.2
  have hNp : IsLoopPoly 2 4 fun ℓ => Np (ℓ 0) :=
    IsLoopPoly.sum _ fun x _ => (hN _ _ _).const_mul _
  obtain ⟨u, hu, hTu⟩ := exists_paramValue_of_kinds (by norm_num) kindsIn₂ (massesD₂ P) hm
    (lt_min hmγ hΛ) hp hp' hq.le (massesD₂_sq_of_ne_pho_in P)
    (min_sq_le_massesD₂_sq_in P hmγ hΛ) intNoSubdivergenceRefined_kindsIn₂ (by decide)
    (by decide) Np hNp (fun ε k => denIn₂ P p' p ε k * Np k)
    (fun ε _ ℓ => by rw [denIn₂_fac P p p' ε ℓ]; ring)
  have huv : u = ∑ x, w x * v x := hu.unique hsum
  have hval : pauliNum P.m p' p (pieceLim (denIn₂ P p' p) (numIn₂ P p' p)) =
      u / auxLimit P.m := by
    rw [pauliNum_eq_sum_idx, huv, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hV x, mul_div_assoc]
  have hNpe : ∀ k, Np k = cdCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * pauliChain P.e P.m p' p k :=
    fun k => by
      rw [← pauliNum_numIn₂ P hm.ne' hp' hp hq k, pauliNum_eq_sum_idx]
  have hE := (tendsto_efi_cd P hm hmγ hΛ hp' hp hp0' hp0 hq 0).const_mul (cdCoeff P)
  have he : (fun ε => QED.OneLoop.energyFirstIntegral fun k => denIn₂ P p' p ε k * Np k) =
      fun ε => cdCoeff P * QED.OneLoop.energyFirstIntegral
        (dblPowInt (pauliChain P.e P.m p' p) P.m 1 (phMs P) (fun _ => ε) ε 0 p' p) := by
    funext ε
    rw [← efi_const_mul']
    congr 1
    funext k
    rw [hNpe, denIn₂_mul_eq]
  rw [he] at hTu
  rw [hval]
  exact tendsto_nhds_unique hTu hE

/-- **The Pauli projection of the doubled `CD0` piece at fixed `q² > 0`.** -/
theorem pauliNum_pieceLim_out :
    pauliNum P.m p' p (pieceLim (denOut₂ P p' p) (numOut₂ P p' p)) =
      cdCoeff P * dblValJ P.e P.m p' p 1 (phMs P) 1 := by
  classical
  have hN : ∀ μ i j, IsLoopPoly 2 4 fun ℓ => numOut₂ P p' p μ (ℓ 0) i j :=
    fun μ i j => (affMat_numOut₂ P p' p μ i j).isLoopPoly
  choose v hv _hT hV using fun x : Idx => pieceLim_entry (by norm_num) kindsOut₂ (massesD₂ P) hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_out P) (min_sq_le_massesD₂_sq_out P hmγ hΛ)
    intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide) hp hp' hq.le (denOut₂ P p' p)
    (numOut₂ P p' p) hN (fun ε _ ℓ => denOut₂_fac P p p' ε ℓ) x.1 x.2.1 x.2.2
  set w : Idx → ℂ := fun x => pauliWt P.m p' p x.1 x.2.1 x.2.2
  have hsum := IsParamValue.sum Finset.univ w fun x _ => hv x
  set Np : (Fin 4 → ℝ) → ℂ := fun k => ∑ x : Idx, w x * numOut₂ P p' p x.1 k x.2.1 x.2.2
  have hNp : IsLoopPoly 2 4 fun ℓ => Np (ℓ 0) :=
    IsLoopPoly.sum _ fun x _ => (hN _ _ _).const_mul _
  obtain ⟨u, hu, hTu⟩ := exists_paramValue_of_kinds (by norm_num) kindsOut₂ (massesD₂ P) hm
    (lt_min hmγ hΛ) hp hp' hq.le (massesD₂_sq_of_ne_pho_out P)
    (min_sq_le_massesD₂_sq_out P hmγ hΛ) intNoSubdivergenceRefined_kindsOut₂ (by decide)
    (by decide) Np hNp (fun ε k => denOut₂ P p' p ε k * Np k)
    (fun ε _ ℓ => by rw [denOut₂_fac P p p' ε ℓ]; ring)
  have huv : u = ∑ x, w x * v x := hu.unique hsum
  have hval : pauliNum P.m p' p (pieceLim (denOut₂ P p' p) (numOut₂ P p' p)) =
      u / auxLimit P.m := by
    rw [pauliNum_eq_sum_idx, huv, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hV x, mul_div_assoc]
  have hNpe : ∀ k, Np k = cdCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * pauliChain P.e P.m p' p k :=
    fun k => by
      rw [← pauliNum_numOut₂ P hm.ne' hp' hp hq k, pauliNum_eq_sum_idx]
  have hE := (tendsto_efi_cd P hm hmγ hΛ hp' hp hp0' hp0 hq 1).const_mul (cdCoeff P)
  have he : (fun ε => QED.OneLoop.energyFirstIntegral fun k => denOut₂ P p' p ε k * Np k) =
      fun ε => cdCoeff P * QED.OneLoop.energyFirstIntegral
        (dblPowInt (pauliChain P.e P.m p' p) P.m 1 (phMs P) (fun _ => ε) ε 1 p' p) := by
    funext ε
    rw [← efi_const_mul']
    congr 1
    funext k
    rw [hNpe, denOut₂_mul_eq]
  rw [he] at hTu
  rw [hval]
  exact tendsto_nhds_unique hTu hE

end Fixed

/-! ### `q → 0` along the curve -/

/-- The `q → 0` value of the even quotient of the doubled `CD` piece on the line `d`. -/
noncomputable def cdZeroVal (P : Params) (d : Fin 2) : ℂ :=
  cdCoeff P * (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * QED.OneLoop.VertexLimit.kappa P.e *
    (4 * (P.m : ℂ) * (4 * (P.m : ℂ) ^ 2 * (4 * (P.m : ℂ) ^ 2) ^ 2)) *
    ((∫ z, dblKernJ P.m 0 1 (phMs P) d z ∂QED.Integration.feynmanMeasure : ℝ) : ℂ))

theorem tendsto_curveQ_nhdsGE (m : ℝ) :
    Tendsto (curveQ m) (𝓝[≠] 0) (𝓝[≥] 0) := by
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun u hu => curveQ_nonneg m hu⟩
  have hc : ContinuousAt (curveQ m) 0 := by
    unfold curveQ
    exact ((continuousAt_const.mul (continuousAt_id.pow 2)).div
      (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num))
  have h0 : curveQ m 0 = 0 := by simp [curveQ]
  have h := hc.tendsto
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_curveQ_div (m : ℝ) :
    Tendsto (fun u => curveQ m u / u ^ 2) (𝓝[≠] 0) (𝓝 (4 * m ^ 2)) := by
  have hc : ContinuousAt (fun u : ℝ => 4 * m ^ 2 / (1 - u ^ 2)) 0 :=
    continuousAt_const.div (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
  unfold curveQ
  field_simp

/-- **The even quotient of the doubled `CD` piece along the curve.** -/
theorem tendsto_evenQuot_cd (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (d : Fin 2) (S : ℝ → ℂ) (hS : ∀ u ∈ Ioo (-1 : ℝ) 1, u ≠ 0 →
      S u = cdCoeff P * dblValJ P.e P.m (curveMomentum P.m u) (restMomentum P.m) 1 (phMs P) d) :
    Tendsto (evenQuot S) (𝓝[≠] 0) (𝓝 (cdZeroVal P d)) := by
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  set g : ℝ → ℂ := fun u => cdCoeff P * (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) *
    QED.OneLoop.VertexLimit.kappa P.e *
    (4 * (P.m : ℂ) * (((curveQ P.m u / u ^ 2 : ℝ) : ℂ) *
      (4 * (P.m : ℂ) ^ 2 + (curveQ P.m u : ℂ)) ^ 2)) *
    ((∫ z, dblKernJ P.m (curveQ P.m u) 1 (phMs P) d z ∂QED.Integration.feynmanMeasure : ℝ) : ℂ))
  have hI := ((tendsto_integral_dblKernJ hm (lt_min hmγ hΛ) (j := 1) (by norm_num)
    (le_phMs P) d).comp (tendsto_curveQ_nhdsGE P.m))
  have hq0 : Tendsto (fun u => curveQ P.m u) (𝓝[≠] 0) (𝓝 0) :=
    (tendsto_curveQ_nhdsGE P.m).mono_right nhdsWithin_le_nhds
  have hg : Tendsto g (𝓝[≠] 0) (𝓝 (cdZeroVal P d)) := by
    have h1 := (Complex.continuous_ofReal.tendsto _).comp (tendsto_curveQ_div P.m)
    have h2 := (Complex.continuous_ofReal.tendsto _).comp hq0
    have h3 := (Complex.continuous_ofReal.tendsto _).comp hI
    have h := (tendsto_const_nhds (x := cdCoeff P * (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) *
      QED.OneLoop.VertexLimit.kappa P.e * (4 * (P.m : ℂ))))).mul ((h1.mul
        (((tendsto_const_nhds (x := 4 * (P.m : ℂ) ^ 2)).add h2).pow 2)).mul h3)
    convert h using 2
    · simp only [g, Function.comp]
      ring
    · simp only [cdZeroVal]
      push_cast
      ring
  refine hg.congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [evenQuot, hS u hu hu0, hS (-u) hu' (neg_ne_zero.2 hu0), dblValJ, dblValJ,
    dot_curveMomentum_sub P.m hu, dot_curveMomentum_sub P.m hu', curveQ_neg]
  simp only [g]
  have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hu0)
  push_cast
  field_simp
  ring

theorem curveQ_pos (m : ℝ) (hm : 0 < m) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    0 < curveQ m u := by
  have h := one_sub_sq_pos hu
  have hu2 : 0 < u ^ 2 := by positivity
  unfold curveQ
  positivity

/-! ### The `q → 0` values as `kindsZero` -/

section Zero

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
include hm hmγ hΛ

/-- **The `q → 0` value of the doubled `CD1` piece**, explicitly. -/
theorem kindsZero_in_eq :
    kindsZero kindsIn₂ (massesD₂ P) P (fun p' => numIn₂ P p' (restMomentum P.m)) =
      cdZeroVal P 0 := by
  have h₂ := tendsto_evenQuot_pieceLim (by norm_num) kindsIn₂ (massesD₂ P) P hm (lt_min hmγ hΛ)
    (massesD₂_sq_of_ne_pho_in P) (min_sq_le_massesD₂_sq_in P hmγ hΛ)
    intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide)
    (fun p' => denIn₂ P p' (restMomentum P.m)) (fun p' => numIn₂ P p' (restMomentum P.m))
    (fun p' μ i j => (affMat_numIn₂ P p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numIn₂_out P _ μ i j k)
    (fun p' ε _ ℓ => denIn₂_fac P _ p' ε ℓ)
  refine tendsto_nhds_unique h₂ (tendsto_evenQuot_cd P hm hmγ hΛ 0 _ fun u hu hu0 => ?_)
  exact pauliNum_pieceLim_in P hm hmγ hΛ (dot_curveMomentum P.m hu) (dot_restMomentum (m := P.m))
    (curveMomentum_pos hm hu) (restMomentum_pos hm)
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_pos P.m hm hu hu0)

/-- **The `q → 0` value of the doubled `CD0` piece**, explicitly. -/
theorem kindsZero_out_eq :
    kindsZero kindsOut₂ (massesD₂ P) P (fun p' => numOut₂ P p' (restMomentum P.m)) =
      cdZeroVal P 1 := by
  have h₂ := tendsto_evenQuot_pieceLim (by norm_num) kindsOut₂ (massesD₂ P) P hm
    (lt_min hmγ hΛ) (massesD₂_sq_of_ne_pho_out P) (min_sq_le_massesD₂_sq_out P hmγ hΛ)
    intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide)
    (fun p' => denOut₂ P p' (restMomentum P.m)) (fun p' => numOut₂ P p' (restMomentum P.m))
    (fun p' μ i j => (affMat_numOut₂ P p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numOut₂_out P _ μ i j k)
    (fun p' ε _ ℓ => denOut₂_fac P _ p' ε ℓ)
  refine tendsto_nhds_unique h₂ (tendsto_evenQuot_cd P hm hmγ hΛ 1 _ fun u hu hu0 => ?_)
  exact pauliNum_pieceLim_out P hm hmγ hΛ (dot_curveMomentum P.m hu) (dot_restMomentum (m := P.m))
    (curveMomentum_pos hm hu) (restMomentum_pos hm)
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_pos P.m hm hu hu0)

end Zero

end QED.ChainProof.CtLoB

end
