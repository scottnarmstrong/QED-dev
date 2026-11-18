/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitVP
public import QED.TwoLoop.PauliZeroLimitCt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Obligation O2-22 at fixed regulators: the `q² → 0⁺` limit of the Pauli coefficient

Obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). For `m, m_γ, Λ > 0`,
`M₁, M₂ ≥ m` with the Pauli–Villars conditions and any counterterms, the Pauli projection
`pauliAt P e Q` of the `ε → 0⁺` limit of the order-`e⁵` vertex at the canonical pair with
`q² = Q` has a limit as `Q → 0⁺` (`exists_tendsto_pauliAt`). Hence there is exactly one number
`a` with the uniform property of O2-22 (`existsUnique_isUniformPauliLimit`). The number is
`pauliZeroLimit P e` (defined as the limit), with the characterization
`isUniformPauliLimit_pauliZeroLimit` and the formula `pauliZeroLimit_eq`:
`a = lim_{u→0} N(u)/u² / (64 e m⁵)`, `N` the Pauli numerator of the vertex limit along the curve.
An explicit Feynman-parameter integral for `a` is not derived here.

## Proof

Along the curve `p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`, `q² = 4m²u²/(1-u²)`,
`P₂ = m (1-u²)³ N(u) / (64 e m⁶ u²)` with `N` the Pauli numerator of the vertex limit
(`pauliAt_curveQ`). `N` is even in `u` (`QED.TwoLoop.PauliZeroLimit.pauliNum_vertexLimit_neg`), so
`N(u)/u² = (N(u) + N(-u))/(2u²)`, and this is a linear combination over the fourteen classes of
the corresponding quantities, each of which converges as `u → 0`, `u ≠ 0`:
`tendsto_open` (six open classes), `tendsto_VP`, `tendsto_d2In`, `tendsto_d2Out`,
`tendsto_d3Slot0` (also `δ₃` slot `1`), `tendsto_d1` (three `δ₁` classes). Finally
`Q ↦ u = √(Q/(4m²+Q))` carries `Q → 0⁺` to `u → 0⁺`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real

namespace QED.TwoLoop.PauliZeroLimit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

/-! ### Linearity of the Pauli numerator -/

theorem pauliNum_add (m : ℝ) (p' p : Fin 4 → ℝ) (V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p (fun μ => V μ + W μ) = pauliNum m p' p V + pauliNum m p' p W := by
  simp only [pauliNum_eq_sum, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem pauliNum_sum {ι : Type*} (s : Finset ι) (m : ℝ) (p' p : Fin 4 → ℝ)
    (F : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p (fun μ => ∑ c ∈ s, F c μ) = ∑ c ∈ s, pauliNum m p' p (F c) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [pauliNum_eq_sum]
    simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [pauliNum_add, ih]

/-! ### The class decomposition along the curve -/

section Assembly

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)

/-- The Pauli numerator of the class `c` of five gauge vertices along the curve. -/
noncomputable def classNum (c : Class5) (u : ℝ) : ℂ :=
  pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
    (classLimitV c P (restMomentum P.m) (curveMomentum P.m u))

/-- The Pauli numerator of the counterterm class `c` along the curve. -/
noncomputable def ctNum (c : CtClass) (u : ℝ) : ℂ :=
  pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
    (ctLimitV c P (restMomentum P.m) (curveMomentum P.m u))

/-- The Pauli numerator of the vertex limit along the curve. -/
noncomputable def vertexNum (u : ℝ) : ℂ :=
  pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
    (vertexLimitAt P (curveMomentum P.m u) (restMomentum P.m))

include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

theorem vertexNum_eq {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    vertexNum P u = (1 / I) * ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classNum P c u) +
      ∑ c : CtClass, ctNum P c u) := by
  have hV := eq_classLimits_of_isVertexOrderFiveLimit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu) (restMomentum_pos hm)
    (curveMomentum_pos hm hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu)
    (isVertexOrderFiveLimit_curve P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu)
  unfold vertexNum classNum ctNum
  rw [hV, pauliNum_smul, pauliNum_add, pauliNum_sum, pauliNum_sum]
  simp only [pauliNum_smul, one_mul]

/-- The even part over `u²`. -/
noncomputable def evenQuot (S : ℝ → ℂ) (u : ℝ) : ℂ := (S u + S (-u)) / (2 * (u : ℂ) ^ 2)

theorem exists_tendsto_classNum {c : Class5} (hc : c ∈ Furry.nonFurry) :
    ∃ L, Tendsto (evenQuot (classNum P c)) (𝓝[≠] 0) (𝓝 L) := by
  by_cases hVP : c = .VP
  · subst hVP
    exact tendsto_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
  · exact tendsto_open (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP) P hm hmγ hΛ

omit hM₁ hM₂ hc₁ hc₂ in
theorem exists_tendsto_ctNum (c : CtClass) :
    ∃ L, Tendsto (evenQuot (ctNum P c)) (𝓝[≠] 0) (𝓝 L) := by
  cases c
  · exact tendsto_d2In P hm hmγ hΛ
  · exact tendsto_d2Out P hm hmγ hΛ
  · exact tendsto_d3Slot0 P hm hmγ hΛ
  · have e : ctNum P .d3Slot1 = ctNum P .d3Slot0 := funext fun u => by
      simp only [ctNum, ctLimitV_d3Slot1_eq]
    rw [e]
    exact tendsto_d3Slot0 P hm hmγ hΛ
  · exact tendsto_d1 (Or.inl rfl) P hm hmγ hΛ
  · exact tendsto_d1 (Or.inr (Or.inl rfl)) P hm hmγ hΛ
  · exact tendsto_d1 (Or.inr (Or.inr rfl)) P hm hmγ hΛ

/-- **`N(u)/u²` converges as `u → 0`, `u ≠ 0`.** -/
theorem exists_tendsto_vertexNum_div :
    ∃ L, Tendsto (fun u => vertexNum P u / (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 L) := by
  have h₁ : ∀ c : Class5, ∃ L, c ∈ Furry.nonFurry →
      Tendsto (evenQuot (classNum P c)) (𝓝[≠] 0) (𝓝 L) := fun c => by
    by_cases hc : c ∈ Furry.nonFurry
    · obtain ⟨L, hL⟩ := exists_tendsto_classNum P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hc
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose L₁ hL₁ using h₁
  choose L₂ hL₂ using fun c : CtClass => exists_tendsto_ctNum P hm hmγ hΛ c
  have hT := ((tendsto_finsetSum Furry.nonFurry fun c hc => (hL₁ c hc).const_mul
    (c.sign : ℂ)).add (tendsto_finsetSum Finset.univ fun c _ => hL₂ c)).const_mul (1 / I)
  refine ⟨_, hT.congr' ?_⟩
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0.and self_mem_nhdsWithin] with u ⟨hu, hu0⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hu0' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0
  have hev : vertexNum P (-u) = vertexNum P u :=
    pauliNum_vertexLimit_neg P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu
  have e1 : vertexNum P u / (u : ℂ) ^ 2 = evenQuot (vertexNum P) u := by
    unfold evenQuot
    rw [hev]
    field_simp
    ring
  rw [e1]
  unfold evenQuot
  rw [vertexNum_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu, vertexNum_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu']
  set D : ℂ := 2 * (u : ℂ) ^ 2
  have k1 : ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * ((classNum P c u + classNum P c (-u)) / D) =
      ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classNum P c u) +
        ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classNum P c (-u)) / D := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => by ring
  have k2 : ∑ c : CtClass, (ctNum P c u + ctNum P c (-u)) / D =
      ((∑ c : CtClass, ctNum P c u) + ∑ c : CtClass, ctNum P c (-u)) / D := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [k1, k2]
  ring

omit hmγ hΛ hM₁ hM₂ hc₁ hc₂ in
/-- **The Pauli projection along the curve**: `P₂ = m (1-u²)³ N(u) / (64 e m⁶ u²)`. -/
theorem pauliAt_curveQ (e : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    pauliAt P e (curveQ P.m u) = (P.m : ℂ) * ((1 - u ^ 2 : ℝ) : ℂ) ^ 3 /
      ((e : ℂ) * 64 * (P.m : ℂ) ^ 6) * (vertexNum P u / (u : ℂ) ^ 2) := by
  have hu : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hu1⟩
  have hw := (one_sub_sq_pos hu).ne'
  have hw' : (1 - (u : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hw
  have hu' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
  have hm' : (P.m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  unfold pauliAt vertexNum
  rw [boostMomentum_curveQ hm hu0.le hu1, formFactorProj₂_eq_pauliNum,
    dot_curveMomentum_sub P.m hu]
  unfold curveQ
  push_cast
  by_cases he : e = 0
  · subst he
    simp
  have he' : (e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  have hD : 4 * (P.m : ℂ) ^ 2 + 4 * (P.m : ℂ) ^ 2 * (u : ℂ) ^ 2 / (1 - (u : ℂ) ^ 2) =
      4 * (P.m : ℂ) ^ 2 / (1 - (u : ℂ) ^ 2) := by
    field_simp
    ring
  rw [hD]
  field_simp
  ring

omit hmγ hΛ hM₁ hM₂ hc₁ hc₂ in
/-- `P₂` converges to `m/(64 e m⁶)` times the limit of `N(u)/u²`. -/
theorem tendsto_pauliAt_of (e : ℝ) {L : ℂ}
    (hL : Tendsto (fun u => vertexNum P u / (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 L)) :
    Tendsto (pauliAt P e) (𝓝[>] 0)
      (𝓝 ((P.m : ℂ) * ((1 - (0 : ℝ) ^ 2 : ℝ) : ℂ) ^ 3 / ((e : ℂ) * 64 * (P.m : ℂ) ^ 6) * L)) := by
  set K : ℝ → ℂ := fun u => (P.m : ℂ) * ((1 - u ^ 2 : ℝ) : ℂ) ^ 3 /
    ((e : ℂ) * 64 * (P.m : ℂ) ^ 6) with hK_def
  have hK : Tendsto K (𝓝[>] 0) (𝓝 (K 0)) := by
    have hc : Continuous K := by
      simp only [hK_def]
      fun_prop
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hL' : Tendsto (fun u => vertexNum P u / (u : ℂ) ^ 2) (𝓝[>] 0) (𝓝 L) :=
    hL.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have hF : Tendsto (fun u => pauliAt P e (curveQ P.m u)) (𝓝[>] 0) (𝓝 (K 0 * L)) := by
    refine (hK.mul hL').congr' ?_
    have h1 : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h1] with u hu0 hu1
    exact (pauliAt_curveQ P hm e hu0 hu1).symm
  -- the change of variable `u = √(Q / (4m² + Q))`
  have hm2 : 0 < 4 * P.m ^ 2 := by positivity
  set uQ : ℝ → ℝ := fun Q => Real.sqrt (Q / (4 * P.m ^ 2 + Q)) with huQ_def
  have huQc : Tendsto uQ (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun Q : ℝ => Q / (4 * P.m ^ 2 + Q)) 0 :=
      ContinuousAt.div continuousAt_id (by fun_prop) (by simp; positivity)
    have h := (Real.continuous_sqrt.continuousAt.comp hc).tendsto
    simp only [Function.comp_def, zero_div, Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have huQ : Tendsto uQ (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨huQc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
    exact Real.sqrt_pos.mpr (div_pos hQ (by positivity))
  have hcq : ∀ Q : ℝ, 0 < Q → curveQ P.m (uQ Q) = Q := fun Q hQ => by
    have hr : 0 ≤ Q / (4 * P.m ^ 2 + Q) := (div_pos hQ (by positivity)).le
    simp only [huQ_def, curveQ, Real.sq_sqrt hr]
    have h4 : (4 * P.m ^ 2 + Q) ≠ 0 := by positivity
    have h5 : 1 - Q / (4 * P.m ^ 2 + Q) = 4 * P.m ^ 2 / (4 * P.m ^ 2 + Q) := by
      field_simp
      ring
    rw [h5]
    field_simp
  refine (hF.comp huQ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
  simp only [Function.comp_apply, hcq Q hQ]

/-- **O2-22 at fixed regulators: the Pauli projection has a limit as `q² → 0⁺`.** For
`m, m_γ, Λ > 0`, `M₁, M₂ ≥ m` with the Pauli–Villars conditions and any counterterms, the Pauli
projection `pauliAt P e Q` of the `ε → 0⁺` limit of the order-`e⁵` vertex at the canonical pair
with `q² = Q` converges as `Q → 0⁺`. -/
theorem exists_tendsto_pauliAt (e : ℝ) : ∃ a, Tendsto (pauliAt P e) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨L, hL⟩ := exists_tendsto_vertexNum_div P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
  exact ⟨_, tendsto_pauliAt_of P hm e hL⟩

/-- **The `q² → 0⁺` limit of the Pauli projection** (O2-22 at fixed regulators), defined from
`exists_tendsto_pauliAt`. -/
noncomputable def pauliZeroLimit (P : Params) (e : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (pauliAt P e)

theorem tendsto_pauliZeroLimit (e : ℝ) :
    Tendsto (pauliAt P e) (𝓝[>] 0) (𝓝 (pauliZeroLimit P e)) := by
  obtain ⟨a, ha⟩ := exists_tendsto_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e
  unfold pauliZeroLimit
  rw [ha.limUnder_eq]
  exact ha

/-- **Characterization**: `pauliZeroLimit P e` is the value with the uniform property of O2-22. -/
theorem isUniformPauliLimit_pauliZeroLimit (e : ℝ) :
    IsUniformPauliLimit P e (pauliZeroLimit P e) :=
  (uniform_iff_tendsto_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e _).mpr
    (tendsto_pauliZeroLimit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e)

/-- **The limit through the Pauli numerator along the curve**: `a = lim_{u→0} N(u)/u² / (64 e m⁵)`,
with `N(u)` the Pauli numerator `m D T₁ + (q² - 2m²) T₂` of the vertex limit at
`p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`, `p = (m, 0, 0, 0)`. -/
theorem pauliZeroLimit_eq (e : ℝ) :
    pauliZeroLimit P e = (P.m : ℂ) / ((e : ℂ) * 64 * (P.m : ℂ) ^ 6) *
      limUnder (𝓝[≠] (0 : ℝ)) (fun u => vertexNum P u / (u : ℂ) ^ 2) := by
  obtain ⟨L, hL⟩ := exists_tendsto_vertexNum_div P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
  have h := tendsto_pauliAt_of P hm e hL
  unfold pauliZeroLimit
  rw [h.limUnder_eq, hL.limUnder_eq]
  simp


/-- **O2-22 at fixed regulators, `∃!` form.** There is exactly one `a` such that for every
`η > 0` there is `q₀ > 0` with `‖P₂ V - a‖ < η` for every `ε → 0⁺` limit `V` of the order-`e⁵`
vertex at every on-shell positive-energy pair with `0 < q² < q₀`. -/
theorem existsUnique_isUniformPauliLimit (e : ℝ) : ∃! a, IsUniformPauliLimit P e a :=
  (existsUnique_uniform_iff P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e).mpr
    (exists_tendsto_pauliAt P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e)

end Assembly

end QED.TwoLoop.PauliZeroLimit

end
