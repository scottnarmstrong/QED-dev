/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPUnitNestedAlgebra
public import QED.TwoLoop.VPUnitNestedKernel
public import QED.TwoLoop.ReflCovarianceCounterterm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The `δ₃` class with four distinct photon masses, through the frozen one-loop vertex

Part of the nested-form identity of the VP unit (`QED.TwoLoop.UnitVPLink.VPUnitNested`), `δ₃`
half. Fix on-shell positive-energy `p, p'` with `q² > 0`. Replace the doubled photon pair
`(m_γ, Λ, m_γ, Λ)` of the `δ₃` class product data by `(a, b, c, d) = (m_γ, Λ, c, d)` with four
distinct squared masses (`massesD3c`), keeping the Pauli-projected class numerator
`N(k) = pauliNum (numD3 k)`. At fixed `ε > 0`:

* `N(k) = -(δ₃/2)(Λ² - m_γ²)² k² Pg(k)` (`QED.TwoLoop.VPUnitNested.pauliNum_numD3`: the
  longitudinal part drops out exactly);
* `k² ∏ D⁻¹` splits into Pauli–Villars pairs `(a, x)`, `x ∈ {b, c, d}`
  (`QED.TwoLoop.VPUnitNested.pf_four`), and the Pauli projection of the frozen one-loop integrand
  with masses `(a, x)` is `(x² - a²) Pg(k) / (D D D_a D_x)`.

So the energy-first integral of `N ∏ D⁻¹` is a combination of energy-first integrals of the
Pauli-projected frozen integrands (`EFInt`: integrability in both stages), whose limits are
`i · pauliNum (vertexOneLoop)` (`tendsto_efi_pauliVI`). The parametric value of the product data
(with the auxiliary loop) is therefore

`(-π⁴ ∫_Δ paramIntegrand) / auxLimit m = -(δ₃/2)(Λ² - m_γ²)² · i · (e q² (4m² + q²)²/m) ·
  (e²/(8π²)) ∫ kern4 m a b c d q²`

(`paramValue_d3_four`), with the partial-fraction kernel of
`QED/TwoLoop/VPUnitNestedKernel.lean`.
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPUnitNested

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix symanzikV symanzikU
  noSubdivergenceRefined_castLoopMatrix_iff)
open QED.Integration (feynmanMeasure)

/-! ### Integrability in both stages of the energy-first integral -/

/-- Integrability of `F` in both stages of the energy-first integral: in the energy at every
spatial momentum, and of the energy integral in the spatial momentum. -/
def EFInt (F : (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v : Fin 4 → ℝ)) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)

theorem EFInt.add {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) (hG : EFInt G) :
    EFInt fun ℓ => F ℓ + G ℓ :=
  ⟨fun v => (hF.1 v).add (hG.1 v), (hF.2.add hG.2).congr
    (Eventually.of_forall fun v => (integral_add (hF.1 v) (hG.1 v)).symm)⟩

theorem EFInt.const_mul {F : (Fin 4 → ℝ) → ℂ} (c : ℂ) (hF : EFInt F) :
    EFInt fun ℓ => c * F ℓ :=
  ⟨fun v => (hF.1 v).const_mul c, (hF.2.const_mul c).congr
    (Eventually.of_forall fun _ => (integral_const_mul c _).symm)⟩

theorem EFInt.sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, EFInt (F i)) : EFInt fun ℓ => ∑ i ∈ s, F i ℓ :=
  ⟨fun _ => integrable_finsetSum s fun i hi => (h i hi).1 _,
    (integrable_finsetSum s fun i hi => (h i hi).2).congr
      (Eventually.of_forall fun v => (integral_finsetSum s fun i hi => (h i hi).1 v).symm)⟩

theorem efi_add {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) (hG : EFInt G) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => F ℓ + G ℓ) =
      QED.OneLoop.energyFirstIntegral F + QED.OneLoop.energyFirstIntegral G := by
  unfold QED.OneLoop.energyFirstIntegral
  rw [← integral_add hF.2 hG.2]
  exact integral_congr_ae (Eventually.of_forall fun v => integral_add (hF.1 v) (hG.1 v))

theorem efi_const_mul (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => c * F ℓ) =
      c * QED.OneLoop.energyFirstIntegral F := by
  unfold QED.OneLoop.energyFirstIntegral
  simp only [integral_const_mul]

theorem efi_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, EFInt (F i)) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => ∑ i ∈ s, F i ℓ) =
      ∑ i ∈ s, QED.OneLoop.energyFirstIntegral (F i) := by
  unfold QED.OneLoop.energyFirstIntegral
  rw [← integral_finsetSum s fun i hi => (h i hi).2]
  exact integral_congr_ae (Eventually.of_forall fun v => integral_finsetSum s fun i hi =>
    (h i hi).1 v)

/-! ### The Pauli-projected frozen one-loop integrand -/

section OneLoop

variable {e m a x : ℝ} (hm : 0 < m) (ha : 0 < a) (hx : 0 < x) {p' p : Fin 4 → ℝ}
  (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
  (hp0 : 0 < p 0)
include hm ha hx hp' hp hp0' hp0

theorem efInt_vertexIntegrand (μ i j : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    EFInt fun ℓ => QED.OneLoop.vertexIntegrand e m a x ε p' p μ ℓ i j :=
  ⟨fun v => QED.OneLoop.VertexLimit.integrable_time_vertexIntegrand hε e m a x p' p μ i j v,
    (QED.OneLoop.VertexLimit.integrable_spatialG hm ha hx hp' hp hp0' hp0 μ i j hε).congr
      (Eventually.of_forall fun v =>
        (QED.OneLoop.VertexLimit.integral_vertexIntegrand_time hε e m a x p' p μ i j v).symm)⟩

omit hm ha hx hp' hp hp0' hp0 in
theorem pauliVI_eq_sum (ε : ℝ) (k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a x ε p' p μ k) =
      ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 *
        QED.OneLoop.vertexIntegrand e m a x ε p' p j.1 k j.2.1 j.2.2 :=
  pauliNum_eq_sum_idx m p' p _

theorem efInt_pauliVI {ε : ℝ} (hε : 0 < ε) :
    EFInt fun k => pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a x ε p' p μ k) := by
  have h := EFInt.sum Finset.univ (F := fun (j : Idx) k => pauliWt m p' p j.1 j.2.1 j.2.2 *
    QED.OneLoop.vertexIntegrand e m a x ε p' p j.1 k j.2.1 j.2.2)
    fun j _ => (efInt_vertexIntegrand hm ha hx hp' hp hp0' hp0 _ _ _ hε).const_mul _
  simpa only [pauliVI_eq_sum] using h

/-- **The limit of the Pauli-projected frozen integrand**: `i · pauliNum (vertexOneLoop)`. -/
theorem tendsto_efi_pauliVI :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun k =>
        pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a x ε p' p μ k)) (𝓝[>] 0)
      (𝓝 (I * pauliNum m p' p
        (QED.OneLoop.vertexOneLoop e m a x hm ha hx p' p hp' hp hp0' hp0))) := by
  have hlim : Tendsto (fun ε => ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 *
      QED.OneLoop.energyFirstIntegral fun k =>
        QED.OneLoop.vertexIntegrand e m a x ε p' p j.1 k j.2.1 j.2.2) (𝓝[>] 0)
      (𝓝 (∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 *
        ∫ v, QED.OneLoop.VertexLimit.spatialG e m a x 0 p' p j.1 j.2.1 j.2.2 v)) :=
    tendsto_finsetSum _ fun j _ =>
      (QED.OneLoop.VertexLimit.tendsto_energyFirstIntegral_vertexIntegrand hm ha hx hp' hp hp0'
        hp0 _ _ _).const_mul _
  have hval : ∑ j : Idx, pauliWt m p' p j.1 j.2.1 j.2.2 *
      ∫ v, QED.OneLoop.VertexLimit.spatialG e m a x 0 p' p j.1 j.2.1 j.2.2 v =
      I * pauliNum m p' p
        (QED.OneLoop.vertexOneLoop e m a x hm ha hx p' p hp' hp hp0' hp0) := by
    rw [pauliNum_eq_sum_idx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [QED.OneLoop.VertexLimit.vertexOneLoop_eq_limit hm ha hx hp' hp hp0' hp0, Matrix.of_apply]
    field_simp
  rw [← hval]
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  simp only [pauliVI_eq_sum]
  rw [efi_sum _ fun j _ => (efInt_vertexIntegrand hm ha hx hp' hp hp0' hp0 _ _ _ hε).const_mul _]
  simp only [efi_const_mul]

end OneLoop

/-! ### The `δ₃` class with four photon masses -/

/-- The line masses of the `δ₃` product data with the second photon pair replaced by `(c, d)`. -/
def massesD3c (P : Params) (c d : ℝ) : Fin 9 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, c, d, P.m, P.m, P.m]

theorem massesD3c_self (P : Params) : massesD3c P P.mγ P.Λ = massesD3 P := rfl

theorem propDenom_eq_add (M ε : ℝ) (k : Fin 4 → ℝ) :
    propDenom M ε k = (((Minkowski.dot k k : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) := by
  simp only [propDenom]
  push_cast
  ring

/-- **The class integrand with four photon masses as Pauli–Villars pairs**, at `ε > 0`. -/
theorem classIntegrand_eq (P : Params) (hm : P.m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {c d ε : ℝ} (hε : ε ≠ 0)
    (hab : P.mγ ^ 2 ≠ P.Λ ^ 2) (hac : P.mγ ^ 2 ≠ c ^ 2) (had : P.mγ ^ 2 ≠ d ^ 2)
    (hbc : P.Λ ^ 2 ≠ c ^ 2) (hbd : P.Λ ^ 2 ≠ d ^ 2) (hcd : c ^ 2 ≠ d ^ 2) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => numD3 P p' p μ k) *
        ((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹ * (propDenom P.mγ ε k)⁻¹ *
          (propDenom P.Λ ε k)⁻¹ * (propDenom c ε k)⁻¹ * (propDenom d ε k)⁻¹) =
      (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ) *
        (((((P.mγ ^ 2 - P.Λ ^ 2) * (c ^ 2 - P.Λ ^ 2) * (d ^ 2 - P.Λ ^ 2) : ℝ) : ℂ)⁻¹ *
            ((P.Λ ^ 2 : ℝ) - (ε : ℂ) * I) *
            pauliNum P.m p' p (fun μ => QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ ε p' p μ k) +
          (((P.mγ ^ 2 - c ^ 2) * (P.Λ ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) : ℝ) : ℂ)⁻¹ *
            ((c ^ 2 : ℝ) - (ε : ℂ) * I) *
            pauliNum P.m p' p (fun μ => QED.OneLoop.vertexIntegrand P.e P.m P.mγ c ε p' p μ k)) +
          (((P.mγ ^ 2 - d ^ 2) * (P.Λ ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) : ℝ) : ℂ)⁻¹ *
            ((d ^ 2 : ℝ) - (ε : ℂ) * I) *
            pauliNum P.m p' p
              (fun μ => QED.OneLoop.vertexIntegrand P.e P.m P.mγ d ε p' p μ k)) := by
  rw [pauliNum_numD3 P hm hp' hp hq k, pauliNum_vertexIntegrand _ _ _ _ hε,
    pauliNum_vertexIntegrand _ _ _ _ hε, pauliNum_vertexIntegrand _ _ _ _ hε]
  set w : ℂ := ((Minkowski.dot k k : ℝ) : ℂ) - (ε : ℂ) * I
  have hD : ∀ M : ℝ, propDenom M ε k = w + ((M ^ 2 : ℝ) : ℂ) := fun M => propDenom_eq_add M ε k
  have hne : ∀ M : ℝ, w + ((M ^ 2 : ℝ) : ℂ) ≠ 0 := fun M => by
    rw [← hD]; exact propDenom_ne_zero hε k
  have hcast : ∀ {u v : ℝ}, u ≠ v → ((u : ℝ) : ℂ) ≠ ((v : ℝ) : ℂ) := fun h => by exact_mod_cast h
  have hpf := pf_four (w := w) (e := (ε : ℂ) * I) (hne P.mγ) (hne P.Λ) (hne c) (hne d)
    (hcast hab) (hcast hac) (hcast had) (hcast hbc) (hcast hbd) (hcast hcd)
  have hk : ((Minkowski.dot k k : ℝ) : ℂ) = w + (ε : ℂ) * I := by simp only [w]; ring
  rw [hD P.mγ, hD P.Λ, hD c, hD d, hk]
  set Pg := pauliChain P.e P.m p' p k
  set E := (propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹
  push_cast at hpf ⊢
  linear_combination (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * Pg * E : ℂ) * hpf

theorem tendsto_sub_mul_I (r : ℂ) :
    Tendsto (fun ε : ℝ => r - (ε : ℂ) * I) (𝓝[>] 0) (𝓝 r) := by
  have h : Tendsto (fun ε : ℝ => r - (ε : ℂ) * I) (𝓝 0) (𝓝 (r - ((0 : ℝ) : ℂ) * I)) :=
    ((continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
  simpa using h.mono_left nhdsWithin_le_nhds

/-- **The parametric value of the `δ₃` class with four distinct photon masses**, through the
frozen one-loop vertex: `(-π⁴ ∫_Δ paramIntegrand) / auxLimit m =
-(δ₃/2)(Λ² - m_γ²)² · i · (e q² (4m² + q²)²/m) · (e²/(8π²)) ∫ kern4 m m_γ Λ c d q²`. -/
theorem paramValue_d3_four (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    {c d μ₀ : ℝ} (hμ₀ : 0 < μ₀) (h1 : μ₀ ≤ P.mγ) (h2 : μ₀ ≤ P.Λ) (h3 : μ₀ ≤ c) (h4 : μ₀ ≤ d)
    (hab : P.mγ ^ 2 ≠ P.Λ ^ 2) (hac : P.mγ ^ 2 ≠ c ^ 2) (had : P.mγ ^ 2 ≠ d ^ 2)
    (hbc : P.Λ ^ 2 ≠ c ^ 2) (hbd : P.Λ ^ 2 ≠ d ^ 2) (hcd : c ^ 2 ≠ d ^ 2)
    (Q : LoopQuartic)
    (hQ : Q.eval = fun ℓ => pauliNum P.m p' p (fun μ => numD3 P p' p μ (ℓ 0)))
    (hB : RefinedBound (castLoopMatrix fun i => (kindsD3 i).dir) {0, 1, 2, 3} 4 Q.eval) :
    (-((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 8,
        paramIntegrand Q (castLoopMatrix fun i => (kindsD3 i).dir)
          (fun i => (kindsD3 i).mom p p') (massesD3c P c d) 0 x) / auxLimit P.m =
      (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ) * I *
        ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 2 / (8 * π ^ 2) *
          ∫ z, kern4 P.m P.mγ P.Λ c d (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) :
            ℂ) := by
  have hc : 0 < c := hμ₀.trans_le h3
  have hd : 0 < d := hμ₀.trans_le h4
  have s1 := pow_le_pow_left₀ hμ₀.le h1 2
  have s2 := pow_le_pow_left₀ hμ₀.le h2 2
  have s3 := pow_le_pow_left₀ hμ₀.le h3 2
  have s4 := pow_le_pow_left₀ hμ₀.le h4 2
  have hMe : ∀ i, kindsD3 i ≠ .pho → massesD3c P c d i ^ 2 = P.m ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD3, massesD3c]
  have hMp : ∀ i, kindsD3 i = .pho → μ₀ ^ 2 ≤ massesD3c P c d i ^ 2 := fun i hi => by
    fin_cases i <;> simp_all [kindsD3, massesD3c]
  set F : ℝ → (Fin 4 → ℝ) → ℂ := fun ε k => pauliNum P.m p' p (fun μ => numD3 P p' p μ k) *
    ((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹ * (propDenom P.mγ ε k)⁻¹ *
      (propDenom P.Λ ε k)⁻¹ * (propDenom c ε k)⁻¹ * (propDenom d ε k)⁻¹) with hF
  have hT := tendsto_energyFirstIntegral_of_product' (by norm_num : 7 ≤ 8) _ _ (massesD3c P c d) Q
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr
      QED.TwoLoop.ReflCovariance.intNoSubdivergenceRefined_kindsD3) hB
    (c := 3 / 4 * min (P.m ^ 2) (μ₀ ^ 2)) (by positivity)
    (fun z hz hz1 hU => symanzikV_kinds_ge kindsD3 (massesD3c P c d) hp hp' hq.le hMe hMp hz hz1
      hU) hm F
    (fun ε hε ℓ => by
      rw [hQ, prod_lineDenom_kinds]
      simp only [F, Fin.prod_univ_succ, Fin.prod_univ_zero, kindsD3, massesD3c, LineKind.lineMom,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  set K : ℂ := -(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2
  set cb : ℂ := (((P.mγ ^ 2 - P.Λ ^ 2) * (c ^ 2 - P.Λ ^ 2) * (d ^ 2 - P.Λ ^ 2) : ℝ) : ℂ)⁻¹
  set cc : ℂ := (((P.mγ ^ 2 - c ^ 2) * (P.Λ ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) : ℝ) : ℂ)⁻¹
  set cd : ℂ := (((P.mγ ^ 2 - d ^ 2) * (P.Λ ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) : ℝ) : ℂ)⁻¹
  have hT2 : Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0)
      (𝓝 (K * ((cb * ((P.Λ ^ 2 : ℝ) : ℂ) * (I * pauliNum P.m p' p
          (QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0)) +
        cc * ((c ^ 2 : ℝ) : ℂ) * (I * pauliNum P.m p' p
          (QED.OneLoop.vertexOneLoop P.e P.m P.mγ c hm hmγ hc p' p hp' hp hp0' hp0))) +
        cd * ((d ^ 2 : ℝ) : ℂ) * (I * pauliNum P.m p' p
          (QED.OneLoop.vertexOneLoop P.e P.m P.mγ d hm hmγ hd p' p hp' hp hp0' hp0))))) := by
    have l1 := ((tendsto_sub_mul_I ((P.Λ ^ 2 : ℝ) : ℂ)).const_mul cb).mul
      (tendsto_efi_pauliVI (e := P.e) hm hmγ hΛ hp' hp hp0' hp0)
    have l2 := ((tendsto_sub_mul_I ((c ^ 2 : ℝ) : ℂ)).const_mul cc).mul
      (tendsto_efi_pauliVI (e := P.e) hm hmγ hc hp' hp hp0' hp0)
    have l3 := ((tendsto_sub_mul_I ((d ^ 2 : ℝ) : ℂ)).const_mul cd).mul
      (tendsto_efi_pauliVI (e := P.e) hm hmγ hd hp' hp hp0' hp0)
    have hlim := ((l1.add l2).add l3).const_mul K
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    have hFε : F ε = fun k => K * ((cb * (((P.Λ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum P.m p' p (fun μ => QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ ε p' p μ k) +
        cc * (((c ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum P.m p' p (fun μ => QED.OneLoop.vertexIntegrand P.e P.m P.mγ c ε p' p μ k)) +
        cd * (((d ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum P.m p' p (fun μ => QED.OneLoop.vertexIntegrand P.e P.m P.mγ d ε p' p μ k)) :=
      funext fun k => classIntegrand_eq P hm.ne' hp' hp hq hε.ne' hab hac had hbc hbd hcd k
    have i1 := (efInt_pauliVI (e := P.e) hm hmγ hΛ hp' hp hp0' hp0 hε).const_mul
      (cb * (((P.Λ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
    have i2 := (efInt_pauliVI (e := P.e) hm hmγ hc hp' hp hp0' hp0 hε).const_mul
      (cc * (((c ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
    have i3 := (efInt_pauliVI (e := P.e) hm hmγ hd hp' hp hp0' hp0 hε).const_mul
      (cd * (((d ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
    show _ = QED.OneLoop.energyFirstIntegral (F ε)
    rw [hFε, efi_const_mul, efi_add (i1.add i2) i3, efi_add i1 i2, efi_const_mul, efi_const_mul,
      efi_const_mul]
  rw [tendsto_nhds_unique hT hT2]
  have hq0 := hq.le
  rw [pauliNum_vertexOneLoop P.e hm hmγ hΛ hp' hp hp0' hp0 hq,
    pauliNum_vertexOneLoop P.e hm hmγ hc hp' hp hp0' hp0 hq,
    pauliNum_vertexOneLoop P.e hm hmγ hd hp' hp hp0' hp0 hq,
    QED.OneLoop.VertexLimit.formFactorB_eq hp' hp, QED.OneLoop.VertexLimit.formFactorB_eq hp' hp,
    QED.OneLoop.VertexLimit.formFactorB_eq hp' hp,
    ← sum_mul_integral_pauliIntegrand_eq hm hq0 hab hac had hbc hbd hcd]
  simp only [K, cb, cc, cd]
  push_cast
  ring

end QED.TwoLoop.VPUnitNested

end
