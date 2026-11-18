/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPUnitNestedOneLoop
public import QED.TwoLoop.VPUnitNestedParam
public import QED.TwoLoop.UnitVPLink
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The `δ₃` half of the nested-form identity of the VP unit

The VP unit is `unitF2 .VP P = (1/(64 m⁵)) (1/i) (-vpZero P + 2 d3Zero P)`
(`QED.TwoLoop.UnitsRegulated.unitF2`), and its nested form `VPUnitNested P` asks it to equal the
outer one-loop functional `outerF2 ((Π_loop - δ₃) s D(s)²)` (`QED.TwoLoop.UnitVPLink`). This file
proves the `δ₃` part: at `m = 1`, for all `m_γ, Λ > 0` and every `δ₃`,

`(1/(64 m⁵)) (1/i) (2 d3Zero P) = e³ outerF2 (s ↦ -δ₃ s D(s)²)`

(`unit_d3Zero`), with no condition on the regulator fermions. It is the analogue of
`QED.TwoLoop.UnitVPLink.unit_d1Zero`.

## Proof

* **At fixed on-shell positive-energy `p, p'` with `q² > 0`** (`pauliNum_ctLimitV_d3`): the
  Pauli numerator of the `δ₃` class limit is
  `-(δ₃/2)(Λ² - m_γ²)² · i · (e q² (4m² + q²)²/m) · (e²/(8π²)) ∫ kernD3 m m_γ Λ q²`.
  The class limit is the parametric value of the product data divided by `auxLimit m`
  (`QED.TwoLoop.ReflCovariance.ctLimitV_d3Slot0_entry`). Move the second photon pair to
  `(m_γ + t, Λ + t)`: for small `t > 0` the four squared masses are distinct and the parametric
  value is given by the frozen one-loop vertex
  (`QED.TwoLoop.VPUnitNested.paramValue_d3_four`); as `t → 0⁺` the parametric integral is
  continuous in the masses (`tendsto_integral_paramIntegrand_of_masses`) and the kernel integral
  converges (`tendsto_integral_kern4`).
* **Along the curve** `p'(u)` (`d3Zero_eq`): the Pauli numerator is `u² Φ(u)` with `Φ` continuous
  at `0`, so `d3Zero P = Φ(0)` by uniqueness of limits with
  `QED.TwoLoop.PauliZeroExplicit.tendsto_d3Slot0_explicit`.
* **At `q² = 0`, `m = 1`**: `(Λ² - m_γ²)² kernD3 1 m_γ Λ 0 (x, y) = 2 y² s D(s)²` with
  `s = y²/(1-y)` (`kernD3_one_zero_mul`), which is the outer integrand of `outerF2`.
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPUnitNested

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance QED.TwoLoop.ClassLimit
open QED.TwoLoop.ReflCovariance QED.TwoLoop.UnitVPLink QED.TwoLoop.PauliZero
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix symanzikV symanzikU
  noSubdivergenceRefined_castLoopMatrix_iff)
open QED.Integration (feynmanMeasure)

/-! ### At fixed external momenta -/

theorem photonNum_self (δ₃ M : ℝ) (k : Fin 4 → ℝ) : photonNum δ₃ M M k = fun _ _ => 0 := by
  funext ν ρ
  simp [photonNum, pvPhotonNum]

/-- **The Pauli numerator of the `δ₃` class limit at fixed on-shell positive-energy `p, p'` with
`q² > 0`.** -/
theorem pauliNum_ctLimitV_d3 (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    pauliNum P.m p' p (ctLimitV .d3Slot0 P p p') =
      (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ) * I *
        ((P.e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (P.m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 2 / (8 * π ^ 2) *
          ∫ z, kernD3 P.m P.mγ P.Λ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) :
            ℂ) := by
  set D := d3Data P hm hmγ hΛ hp hp' hq.le
  -- the entries as parametric values
  choose v hv hV using fun (j : Idx) => ctLimitV_d3Slot0_entry P hm hmγ hΛ hp hp' hq.le j.1 j.2.1
    j.2.2
  have hsum := IsParamValue.sum (D := D) Finset.univ
    (fun j : Idx => pauliWt P.m p' p j.1 j.2.1 j.2.2)
    (fun j _ => hv j)
  have hpn : pauliNum P.m p' p (ctLimitV .d3Slot0 P p p') =
      (∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 * v j) / auxLimit P.m := by
    rw [pauliNum_eq_sum_idx, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [hV j, mul_div_assoc]
  obtain ⟨Q, hQ, hB, hval⟩ := hsum
  have hQ' : Q.eval = fun ℓ => pauliNum P.m p' p (fun μ => numD3 P p' p μ (ℓ 0)) := by
    rw [hQ]
    funext ℓ
    rw [pauliNum_eq_sum_idx]
  have hval' : ∑ j : Idx, pauliWt P.m p' p j.1 j.2.1 j.2.2 * v j =
      -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 8,
        paramIntegrand Q (castLoopMatrix fun i => (kindsD3 i).dir)
          (fun i => (kindsD3 i).mom p p') (massesD3 P) 0 x := hval
  rw [hpn, hval']
  have hBQ : RefinedBound D.α D.E 4 Q.eval := by rw [hQ]; exact hB
  have hB' : RefinedBound (castLoopMatrix fun i => (kindsD3 i).dir) {0, 1, 2, 3} 4 Q.eval := hBQ
  rcases eq_or_ne P.mγ P.Λ with hab | hab
  · -- equal photon masses: the class numerator vanishes
    have hz : Q.eval = fun _ => 0 := by
      rw [hQ']
      funext ℓ
      simp only [numD3, hab, photonNum_self]
      rw [pauliNum_eq_sum]
      refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun i _ =>
        Finset.sum_eq_zero fun j _ => ?_
      simp [vertexChain]
    have h0 : IsParamValue D (fun _ => 0) 0 := by
      simpa using IsParamValue.sum (D := D) (∅ : Finset Idx) (fun _ => 0)
        (F := fun _ _ => 0) (v := fun _ => 0) (fun j hj => absurd hj (Finset.notMem_empty j))
    have h1 : IsParamValue D (fun _ => 0) (-((π : ℂ) ^ 4) * ∫ x in
        QED.Integration.Feynman.simplexSet 8, paramIntegrand Q
          (castLoopMatrix fun i => (kindsD3 i).dir) (fun i => (kindsD3 i).mom p p')
          (massesD3 P) 0 x) := ⟨Q, hz, hz ▸ hBQ, rfl⟩
    rw [h1.unique h0, hab]
    simp
  -- distinct photon masses: move the second pair to `(m_γ + t, Λ + t)`
  set a := P.mγ
  set b := P.Λ
  obtain ⟨μ₀, hμ₀, hμa, hμb⟩ : ∃ μ₀ : ℝ, 0 < μ₀ ∧ μ₀ ≤ a ∧ μ₀ ≤ b :=
    ⟨min a b, lt_min hmγ hΛ, min_le_left _ _, min_le_right _ _⟩
  have hadd : ∀ r : ℝ, Tendsto (fun t : ℝ => r + t) (𝓝[>] 0) (𝓝 r) := fun r => by
    have h : Tendsto (fun t : ℝ => r + t) (𝓝 0) (𝓝 (r + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hδ : 0 < |b - a| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hab))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < |b - a| :=
    (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ht).and
      (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  set Vf : ℝ → ℂ := fun t => -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 8,
    paramIntegrand Q (castLoopMatrix fun i => (kindsD3 i).dir) (fun i => (kindsD3 i).mom p p')
      (massesD3c P (a + t) (b + t)) 0 x
  set q2 := Minkowski.dot (p' - p) (p' - p)
  set K : ℂ := -(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2
  set E : ℂ := (P.e : ℂ) * (q2 : ℂ) * (4 * (P.m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / P.m
  -- the explicit value for small `t > 0`
  have hexp : ∀ᶠ t in 𝓝[>] (0 : ℝ), Vf t / auxLimit P.m =
      K * I * E * ((P.e ^ 2 / (8 * π ^ 2) *
        ∫ z, kern4 P.m a b (a + t) (b + t) q2 z ∂feynmanMeasure : ℝ) : ℂ) := by
    filter_upwards [hev] with t ⟨ht0, htδ⟩
    have hab2 : a ^ 2 ≠ b ^ 2 := fun h => hab (by
      have := (sq_eq_sq₀ hmγ.le hΛ.le).1 h; exact this)
    have hsq : ∀ {u w : ℝ}, 0 < u → 0 < w → u ≠ w → u ^ 2 ≠ w ^ 2 := fun hu hw h h2 =>
      h ((sq_eq_sq₀ hu.le hw.le).1 h2)
    have hta : a + t ≠ b := fun h => by
      rcases lt_or_gt_of_ne hab with h' | h'
      · rw [abs_of_pos (sub_pos.2 h')] at htδ; linarith
      · linarith
    have htb : b + t ≠ a := fun h => by
      rcases lt_or_gt_of_ne hab with h' | h'
      · linarith
      · rw [abs_of_neg (sub_neg.2 h')] at htδ; linarith
    exact paramValue_d3_four P hm hmγ hΛ hp hp' hp0 hp0' hq hμ₀ hμa hμb (by linarith)
      (by linarith) hab2
      (hsq hmγ (by linarith) (by linarith)) (hsq hmγ (by linarith) (Ne.symm htb))
      (hsq hΛ (by linarith) (Ne.symm hta)) (hsq hΛ (by linarith) (by linarith))
      (hsq (by linarith) (by linarith) (fun h => hab (by linarith))) Q hQ' hB'
  -- the parametric value is continuous in the masses
  have hMp : ∀ t, 0 ≤ t → ∀ i, kindsD3 i = .pho → μ₀ ^ 2 ≤ massesD3c P (a + t) (b + t) i ^ 2 := by
    intro t ht i hi
    have s1 := pow_le_pow_left₀ hμ₀.le hμa 2
    have s2 := pow_le_pow_left₀ hμ₀.le hμb 2
    have s3 := pow_le_pow_left₀ hμ₀.le (hμa.trans (by linarith : a ≤ a + t)) 2
    have s4 := pow_le_pow_left₀ hμ₀.le (hμb.trans (by linarith : b ≤ b + t)) 2
    fin_cases i <;> simp [kindsD3] at hi <;> simpa [massesD3c] using ‹_›
  have hMe : ∀ t, ∀ i, kindsD3 i ≠ .pho → massesD3c P (a + t) (b + t) i ^ 2 = P.m ^ 2 := by
    intro t i hi
    fin_cases i <;> simp_all [kindsD3, massesD3c]
  have hcont : Tendsto Vf (𝓝[>] 0) (𝓝 (-((π : ℂ) ^ 4) * ∫ x in
      QED.Integration.Feynman.simplexSet 8, paramIntegrand Q
        (castLoopMatrix fun i => (kindsD3 i).dir) (fun i => (kindsD3 i).mom p p')
        (massesD3 P) 0 x)) := by
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_paramIntegrand_of_masses Q _ _ (fun t => massesD3c P (a + t) (b + t))
      (massesD3 P) (fun i => ?_) (by norm_num)
      ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr intNoSubdivergenceRefined_kindsD3) hB'
      (c := 3 / 4 * min (P.m ^ 2) (μ₀ ^ 2)) (by positivity) ?_ ?_
    · fin_cases i <;> simp only [massesD3c, massesD3] <;>
        first | exact tendsto_const_nhds | exact hadd _
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact fun z hz hz1 hU => symanzikV_kinds_ge kindsD3 _ hp hp' hq.le (hMe t) (hMp t ht.le)
        hz hz1 hU
    · intro z hz hz1 hU
      have h := symanzikV_kinds_ge kindsD3 _ hp hp' hq.le (hMe 0) (hMp 0 le_rfl) hz hz1 hU
      simpa [massesD3c, massesD3] using h
  -- the kernel integral converges
  have hker : Tendsto (fun t => K * I * E * ((P.e ^ 2 / (8 * π ^ 2) *
        ∫ z, kern4 P.m a b (a + t) (b + t) q2 z ∂feynmanMeasure : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (K * I * E * ((P.e ^ 2 / (8 * π ^ 2) *
        ∫ z, kernD3 P.m a b q2 z ∂feynmanMeasure : ℝ) : ℂ))) := by
    have hk := tendsto_integral_kern4 hmγ hΛ hm hq.le (fun t => a + t) (fun t => b + t) (hadd a)
      (hadd b)
    exact ((Complex.continuous_ofReal.tendsto _).comp (hk.const_mul _)).const_mul _
  exact tendsto_nhds_unique ((hcont.div_const _)) (hker.congr' (hexp.mono fun t ht => ht.symm))

/-! ### Along the curve: the `q → 0` value -/

/-- **The `q → 0` value of a `δ₃` class**:
`d3Zero P = -(δ₃/2)(Λ² - m_γ²)² · i · (e (4m²)³/m) · (e²/(8π²)) ∫ kernD3 m m_γ Λ 0`. -/
theorem d3Zero_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    QED.TwoLoop.PauliZeroExplicit.d3Zero P =
      (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ) * I *
        ((P.e : ℂ) * (4 * (P.m : ℂ) ^ 2) ^ 3 / P.m) *
        ((P.e ^ 2 / (8 * π ^ 2) * ∫ z, kernD3 P.m P.mγ P.Λ 0 z ∂feynmanMeasure : ℝ) : ℂ) := by
  set K : ℂ := -(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2
  set Ψ : ℝ → ℝ := fun s => ∫ z, kernD3 P.m P.mγ P.Λ s z ∂feynmanMeasure with hΨ_def
  set Φ : ℝ → ℂ := fun u => K * I * ((P.e : ℂ) * ((4 * P.m ^ 2 / (1 - u ^ 2) : ℝ) : ℂ) *
    (4 * (P.m : ℂ) ^ 2 + (curveQ P.m u : ℂ)) ^ 2 / P.m) *
      ((P.e ^ 2 / (8 * π ^ 2) * Ψ (curveQ P.m u) : ℝ) : ℂ) with hΦ
  have hcq : ContinuousAt (curveQ P.m) 0 := by
    unfold curveQ
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hcq0 : curveQ P.m 0 = 0 := by simp [curveQ]
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hcqT : Tendsto (curveQ P.m) (𝓝[≠] 0) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hcq.tendsto
      rw [hcq0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [h0] with u hu
      exact curveQ_nonneg P.m hu
  have hΨT : Tendsto (fun u => Ψ (curveQ P.m u)) (𝓝[≠] 0) (𝓝 (Ψ 0)) :=
    (tendsto_integral_kernD3_zero hmγ hΛ hm).comp hcqT
  have hden : Tendsto (fun u : ℝ => 4 * P.m ^ 2 / (1 - u ^ 2)) (𝓝[≠] 0)
      (𝓝 (4 * P.m ^ 2 / (1 - 0 ^ 2))) :=
    (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hcqC : Tendsto (fun u => (curveQ P.m u : ℂ)) (𝓝[≠] 0) (𝓝 ((0 : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp
      (hcq.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ))))
    rw [hcq0] at this
    exact this
  have hΦT : Tendsto Φ (𝓝[≠] 0) (𝓝 (K * I * ((P.e : ℂ) *
      ((4 * P.m ^ 2 / (1 - 0 ^ 2) : ℝ) : ℂ) * (4 * (P.m : ℂ) ^ 2 + ((0 : ℝ) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 2 / (8 * π ^ 2) * Ψ 0 : ℝ) : ℂ))) := by
    have c1 := (Complex.continuous_ofReal.tendsto _).comp hden
    have c3 := (Complex.continuous_ofReal.tendsto _).comp (hΨT.const_mul (P.e ^ 2 / (8 * π ^ 2)))
    exact (tendsto_const_nhds.mul ((((tendsto_const_nhds.mul c1).mul
      ((tendsto_const_nhds.add hcqC).pow 2)).div_const _))).mul c3
  have hS : ∀ w (hw : w ∈ Ioo (-1 : ℝ) 1), w ≠ 0 →
      pauliNum P.m (curveMomentum P.m w) (restMomentum P.m)
        (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m w)) = (w : ℂ) ^ 2 * Φ w := by
    intro w hw hw0
    have hqpos : 0 < curveQ P.m w := by
      have := one_sub_sq_pos hw
      unfold curveQ
      have : 0 < w ^ 2 := by positivity
      positivity
    rw [pauliNum_ctLimitV_d3 P hm hmγ hΛ (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hw)
      (restMomentum_pos hm) (curveMomentum_pos hm hw) ((dot_curveMomentum_sub P.m hw).symm ▸ hqpos),
      dot_curveMomentum_sub P.m hw]
    have hw1 := (one_sub_sq_pos hw).ne'
    have hQw : ((curveQ P.m w : ℝ) : ℂ) =
        (w : ℂ) ^ 2 * ((4 * P.m ^ 2 / (1 - w ^ 2) : ℝ) : ℂ) := by
      rw [← ofReal_pow, ← ofReal_mul]
      congr 1
      unfold curveQ
      field_simp
    simp only [hΦ, hΨ_def]
    generalize (∫ z, kernD3 P.m P.mγ P.Λ (curveQ P.m w) z ∂feynmanMeasure) = G
    rw [hQw]
    ring
  have hEv : Tendsto (fun u : ℝ =>
      (pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
          (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m u)) +
        pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
          (ctLimitV .d3Slot0 P (restMomentum P.m) (curveMomentum P.m (-u)))) /
            (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 (K * I * ((P.e : ℂ) *
      ((4 * P.m ^ 2 / (1 - 0 ^ 2) : ℝ) : ℂ) * (4 * (P.m : ℂ) ^ 2 + ((0 : ℝ) : ℂ)) ^ 2 / P.m) *
        ((P.e ^ 2 / (8 * π ^ 2) * Ψ 0 : ℝ) : ℂ))) := by
    refine hΦT.congr' ?_
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 ∧ u ≠ 0 := h0.and self_mem_nhdsWithin
    filter_upwards [h1] with u ⟨hu, hu0⟩
    have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [hS u hu hu0, hS (-u) hu' (neg_ne_zero.mpr hu0)]
    have hΦn : Φ (-u) = Φ u := by simp only [hΦ, curveQ_neg, neg_sq]
    rw [hΦn]
    have hu0' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0
    push_cast
    field_simp
    ring
  rw [tendsto_nhds_unique (QED.TwoLoop.PauliZeroExplicit.tendsto_d3Slot0_explicit P hm hmγ hΛ) hEv]
  simp only [K, hΨ_def]
  push_cast
  ring

/-! ### At `m = 1`: the outer functional -/

/-- The `δ₃` kernel at `q² = 0`, `m = 1`, as a function of `y`. -/
noncomputable def kernD3One (a b y : ℝ) : ℝ :=
  2 * y ^ 4 * (1 - y) ^ 3 /
    (((1 - y) * a ^ 2 + y ^ 2) ^ 2 * ((1 - y) * b ^ 2 + y ^ 2) ^ 2)

theorem kernD3_one_zero (a b : ℝ) (z : ℝ × ℝ) : kernD3 1 a b 0 z = kernD3One a b z.2 := by
  simp only [kernD3, kern4, kDen, kC, kernD3One]
  ring

theorem integral_kernD3_one_zero (a b : ℝ) :
    ∫ z, kernD3 1 a b 0 z ∂feynmanMeasure = ∫ y in (0 : ℝ)..1, kernD3One a b y := by
  simp_rw [kernD3_one_zero]
  unfold QED.Integration.feynmanMeasure
  rw [integral_fun_snd (f := fun y => kernD3One a b y)]
  have h1 : (volume.restrict (Ioc (0 : ℝ) 1)).real univ = 1 := by
    simp [Measure.real]
  rw [h1, one_smul, ← intervalIntegral.integral_of_le zero_le_one]

/-- **The `δ₃` kernel at `q² = 0` is the outer integrand**: for `0 < y < 1`,
`(Λ² - m_γ²)² kernD3One m_γ Λ y = 2 y² s D(s)²` with `s = y²/(1-y)`, `D = photonD m_γ Λ`. -/
theorem kernD3One_mul {a b y : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : y ∈ Ioo (0 : ℝ) 1) :
    (b ^ 2 - a ^ 2) ^ 2 * kernD3One a b y =
      2 * (y ^ 2 * (photonVar y * photonD a b (photonVar y) ^ 2)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : 1 - y ≠ 0 := by linarith
  have h1' : 0 < 1 - y := by linarith
  have hA : (1 - y) * a ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hB : (1 - y) * b ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hsA : y ^ 2 / (1 - y) + a ^ 2 ≠ 0 := by positivity
  have hsB : y ^ 2 / (1 - y) + b ^ 2 ≠ 0 := by positivity
  simp only [kernD3One, photonVar, photonD]
  field_simp
  ring

/-- **The `δ₃` half of the nested form of the VP unit** (at `m = 1`): the two `δ₃` classes of the
VP unit give `e³` times the outer one-loop functional of the photon function `-δ₃ s D(s)²`,
`(1/(64 m⁵)) (1/i) (2 d3Zero P) = e³ outerF2 (s ↦ -δ₃ s D(s)²)`, for all `m_γ, Λ > 0` and every
`δ₃`. -/
theorem unit_d3Zero (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (2 * QED.TwoLoop.PauliZeroExplicit.d3Zero P)) =
      ((P.e ^ 3 * outerF2 (fun s => -P.δ₃ * s * photonD P.mγ P.Λ s ^ 2) : ℝ) : ℂ) := by
  have hm0 : 0 < P.m := by rw [hm]; norm_num
  rw [d3Zero_eq P hm0 hmγ hΛ, hm, integral_kernD3_one_zero]
  have hint : ∫ y in (0 : ℝ)..1,
      y ^ 2 * (-P.δ₃ * photonVar y * photonD P.mγ P.Λ (photonVar y) ^ 2) =
      -P.δ₃ / 2 * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ∫ y in (0 : ℝ)..1, kernD3One P.mγ P.Λ y) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one, (ae_ne_one.mono fun x hx => hx) ] with y hy _ hy01
    rw [uIoc_of_le zero_le_one] at hy01
    have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨hy01.1, lt_of_le_of_ne hy01.2 hy⟩
    have h := kernD3One_mul hmγ hΛ hyI
    rw [← mul_assoc, h]
    ring
  unfold outerF2
  rw [hint]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

end QED.TwoLoop.VPUnitNested

end
