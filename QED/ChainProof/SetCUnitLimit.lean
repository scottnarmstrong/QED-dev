/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitCovarianceClasses

/-!
# Two-loop vertex units with a free mass on each photon line: the `ε → 0⁺` limit

Helper level for set (c) (stage L1 of `docs/campaign/SETC-KERNEL-PLAN.md`). The Phase 4 open-line
classes `c ∈ {L, X, C₊, C₋, S₊, S₋}` are stated at one photon mass: in their parametric form
(`QED.TwoLoop.ClassLimit.contractionValue₂_open_eq_classRouting`) both photon lines carry the pair
of denominators with masses `(m_γ, Λ)`, the masses `pvMasses P = classPVMasses m m_γ m_γ Λ Λ`.
The parametric engine (`QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined`) and
the positivity bounds (`QED.Integration.TwoLoop.symanzikV_classLPV_ge`, …) are already generic in
the eight line masses, so the generalization is a reparametrization, not a copy.

**The unit.** `unitValue c P M ε p p' μ i j` is the joint energy-first integral of
`(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹`, with the class numerator `N = classNumeratorE c P …` and the line
denominators of the Pauli–Villars loop matrix `class5LoopMatrixPV c` at the masses `M`. With
`M = unitMasses m a A b B`, the photon line in slot `4` (the internal photon at vertex `0`) has the
denominators of masses `a, A` (lines `4`, `6`), the one in slot `5` has `b, B` (lines `5`, `7`):

| class | slot `4` (`a, A`) | slot `5` (`b, B`) |
| --- | --- | --- |
| `L` | `(0 4)`, outer | `(1 3)`, inner |
| `X` | `(0 3)` | `(1 4)` |
| `C₊` | `(0 3)`, outer | `(2 4)`, inner |
| `C₋` | `(0 2)`, inner | `(1 4)`, outer |
| `S₊` | `(0 4)`, outer | `(2 3)`, inner |
| `S₋` | `(0 4)`, outer | `(1 2)`, inner |

The numerator does not depend on `M`; it carries the Phase 4 photon constant `(Λ² - m_γ²)²` of `P`
(take `P.mγ = 0`, `P.Λ = 1` for the bare product of denominators). Phase 4 is the case
`M = pvMasses P` (`unitValue_pvMasses`, `unitLimitV_pvMasses`).

**Results.** For masses `a, A, b, B ≥ μ₀ > 0`, `m > 0`, on-shell `p, p'` with `q² ≥ 0`:

* `symanzikV_unit_ge`: `V ≥ (3/4) min(m²/4, μ₀²)` off `U = 0`, uniformly in the masses;
* **`tendsto_unitValue`**: the `ε → 0⁺` limit exists and is the parametric integral at `ε = 0`
  for every quartic `Q` with the values of the numerator (chosen independently of the masses,
  `exists_unitQuartic`); `unitLimitV_eq` identifies the limit vertex `unitLimitV`;
* generic engine facts (any number of lines): `norm_integral_paramIntegrand_zero_le` (a bound by
  `∫ g` with `g` independent of the masses) and `continuousOn_integral_paramIntegrand_zero`
  (continuity in the masses, by dominated convergence);
* **`norm_unitLimitV_le`**: a bound on `unitLimitV` uniform in all masses `≥ μ₀` (no growth),
  and **`continuousOn_unitLimitV`**: continuity along any family of masses `≥ μ₀`, e.g.
  `b = √t` on `[t₀, ∞)` as needed for a dispersion integral in the bubble mass.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnit

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrixPV RefinedBound
  LoopQuartic NoSubdivergenceRefined symanzikU symanzikV classPVMasses symanzikMatrix)
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Generic engine facts: bounds and continuity in the masses -/

section Engine

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)

/-- The dominating function of the parametric integrand at `V ≥ c`; it does not involve the
masses. -/
noncomputable def domFun (c : ℝ) (x : Fin m → ℝ) : ℝ :=
  ‖coeffOne Q α p x‖ * (c ^ (m - 3))⁻¹ + ‖coeffTwo Q α p x‖ * (c ^ (m - 4))⁻¹ +
    ‖coeffThree Q α x‖ * (c ^ (m - 5))⁻¹

variable {Q α p}

theorem integrableOn_domFun (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) (c : ℝ) :
    IntegrableOn (domFun Q α p c) (simplexSet m) := by
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff Q α p hm hcrit hB
  exact ((hT₁.norm.mul_const _).add (hT₂.norm.mul_const _)).add (hT₃.norm.mul_const _)

theorem ae_norm_paramIntegrand_le (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) {c : ℝ} (hc : 0 < c) {M : Fin (m + 1) → ℝ}
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) (ε : ℝ) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)), ‖paramIntegrand Q α p M ε x‖ ≤ domFun Q α p c x := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    QED.Integration.TwoLoop.NoSubdivergence.span (α := α) fun i => by
      have := hcrit.noSubdivergenceOfOrder i; omega
  filter_upwards [QED.Integration.TwoLoop.ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  exact norm_paramIntegrand_le Q α p M hc ε (hV _ hz.1 hz.2 hPD.det_pos.ne')

/-- **A bound uniform in the masses**: wherever `V ≥ c`, the parametric integral at `ε = 0` is
bounded by `∫ g` with `g = domFun Q α p c`, which does not involve the masses. -/
theorem norm_integral_paramIntegrand_zero_le (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) {c : ℝ}
    (hc : 0 < c) {M : Fin (m + 1) → ℝ}
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    ‖∫ x in simplexSet m, paramIntegrand Q α p M 0 x‖ ≤
      ∫ x in simplexSet m, domFun Q α p c x :=
  norm_integral_le_of_norm_le (integrableOn_domFun hm hcrit hB c)
    (ae_norm_paramIntegrand_le hm hcrit hc hV 0)

/-- **Continuity in the masses.** Along a family of masses `Ms t`, continuous on `s`, with
`V ≥ c > 0` for every `t ∈ s`, the parametric integral at `ε = 0` is continuous on `s`
(dominated convergence with the mass-independent `domFun`). -/
theorem continuousOn_integral_paramIntegrand_zero {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (hm : 7 ≤ m)
    {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c) {s : Set X} (Ms : X → Fin (m + 1) → ℝ)
    (hMs : ∀ i, ContinuousOn (fun t => Ms t i) s)
    (hV : ∀ t ∈ s, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Ms t) z) :
    ContinuousOn (fun t => ∫ x in simplexSet m, paramIntegrand Q α p (Ms t) 0 x) s := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    QED.Integration.TwoLoop.NoSubdivergence.span (α := α) fun i => by
      have := hcrit.noSubdivergenceOfOrder i; omega
  refine continuousOn_of_dominated (bound := domFun Q α p c) (fun t ht => ?_)
    (fun t ht => ae_norm_paramIntegrand_le hm hcrit hc (hV t ht) 0)
    (integrableOn_domFun hm hcrit hB c) ?_
  · exact (integrableOn_paramIntegrand_zero Q α p (Ms t) hm hcrit hB hc
      (hV t ht)).aestronglyMeasurable
  · filter_upwards [QED.Integration.TwoLoop.ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hVt : ∀ t ∈ s, c ≤ symanzikV α p (Ms t) (simplexPoint x) :=
      fun t ht => hV t ht _ hz.1 hz.2 hPD.det_pos.ne'
    have hVc : ContinuousOn (fun t => symanzikV α p (Ms t) (simplexPoint x)) s := by
      unfold symanzikV
      exact (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
        (((hMs i).pow 2).add continuousOn_const)).sub continuousOn_const
    have hW : ContinuousOn (fun t => wBase α p (Ms t) 0 x) s := by
      unfold wBase
      exact (continuous_ofReal.comp_continuousOn hVc).sub continuousOn_const
    have hW0 : ∀ t ∈ s, wBase α p (Ms t) 0 x ≠ 0 := fun t ht h => by
      have h' := norm_wBase_ge α p (Ms t) 0 x
      rw [h, norm_zero] at h'
      linarith [hVt t ht]
    have hpow : ∀ k : ℕ, ContinuousOn (fun t => (wBase α p (Ms t) 0 x ^ k)⁻¹) s := fun k =>
      (hW.pow k).inv₀ fun t ht => pow_ne_zero k (hW0 t ht)
    simp only [paramIntegrand_eq]
    exact ((continuousOn_const.mul (hpow _)).add (continuousOn_const.mul (hpow _))).add
      (continuousOn_const.mul (hpow _))

end Engine

/-! ### The unit -/

/-- The masses of the unit: electrons `m`; photon slot `4` the pair `(a, A)` (lines `4, 6`), photon
slot `5` the pair `(b, B)` (lines `5, 7`). -/
def unitMasses (m a A b B : ℝ) : Fin 8 → ℝ := classPVMasses m a b A B

theorem unitMasses_pvMasses (P : Params) : unitMasses P.m P.mγ P.Λ P.mγ P.Λ = pvMasses P := rfl

/-- The numerator `(2π)⁻⁸ N^μ_{ij}(ℓ)` of the unit at the pair `(p, p')`; it does not involve the
line masses. -/
noncomputable def unitNum (c : Class5) (P : Params) (p p' : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
    (fun _ => j) (fun _ => μ) ℓ

/-- The integrand of the unit at masses `M` and prescription `ε`. -/
noncomputable def unitIntegrand (c : Class5) (P : Params) (M : Fin 8 → ℝ) (ε : ℝ)
    (p p' : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  unitNum c P p p' μ i j ℓ *
    ∏ k : Fin 8, (lineDenom (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') M ε k ℓ)⁻¹

/-- **The unit value** at masses `M` and prescription `ε`: the joint energy-first integral of
`unitIntegrand`. -/
noncomputable def unitValue (c : Class5) (P : Params) (M : Fin 8 → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ)
    (μ i j : Fin 4) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral 2 (unitIntegrand c P M ε p p' μ i j)

/-- **The unit limit vertex**: the entrywise `ε → 0⁺` limits of `unitValue`. -/
noncomputable def unitLimitV (c : Class5) (P : Params) (M : Fin 8 → ℝ) (p p' : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => limUnder (𝓝[>] (0 : ℝ)) fun ε => unitValue c P M ε p p' μ i j

/-- **Phase 4 as the equal-mass case**: at `M = pvMasses P` and `ε ≠ 0` the unit value is the
class value (T₁₀). -/
theorem unitValue_pvMasses {c : Class5} (hc : c ∈ openClasses) (P : Params) {ε : ℝ} (hε : ε ≠ 0)
    (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    unitValue c P (pvMasses P) ε p p' μ i j =
      contractionValue₂ { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [contractionValue₂_open_eq_classRouting hc { P with ε := ε } hε hmom]
  unfold unitValue
  congr 1
  funext ℓ
  simp only [unitIntegrand, unitNum, mul_assoc]
  rfl

/-- The numerator values are those of a `LoopQuartic`, independent of the masses. -/
theorem exists_unitQuartic {c : Class5} (hc : c ∈ openClasses) (P : Params) (p p' : Fin 4 → ℝ)
    (μ i j : Fin 4) : ∃ Q : LoopQuartic, Q.eval = unitNum c P p p' μ i j :=
  ((isLoopPoly_classNumeratorE hc P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
    (fun _ => j) (fun _ => μ)).const_mul twoLoopNorm).exists_loopQuartic

theorem refinedBound_unitNum {c : Class5} (hc : c ∈ openClasses) (P : Params) (p p' : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4
      (unitNum c P p p' μ i j) :=
  (refinedBound_classNumeratorE hc P _ _ _ _ _ _).const_mul _

theorem noSubdivergenceRefined_unit {c : Class5} (hc : c ∈ openClasses) :
    NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (class5LoopMatrixPV c)) :=
  (QED.Integration.TwoLoop.noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc

/-- The positivity constant `(3/4) min(m²/4, μ₀²)`. -/
noncomputable def unitConst (m μ₀ : ℝ) : ℝ := 3 / 4 * min (m ^ 2 / 4) (μ₀ ^ 2)

theorem unitConst_pos {m μ₀ : ℝ} (hm : 0 < m) (hμ₀ : 0 < μ₀) : 0 < unitConst m μ₀ :=
  mul_pos (by norm_num) (lt_min (by positivity) (pow_pos hμ₀ 2))

/-- The hypotheses on the masses: all four photon masses at least `μ₀`. -/
def MassesGe (μ₀ a A b B : ℝ) : Prop := μ₀ ≤ a ∧ μ₀ ≤ A ∧ μ₀ ≤ b ∧ μ₀ ≤ B

/-- **Positivity of `V` for the unit, uniform in the masses `≥ μ₀`.** -/
theorem symanzikV_unit_ge {c : Class5} (hc : c ∈ openClasses) {m μ₀ a A b B : ℝ}
    (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV c)) z ≠ 0) :
    unitConst m μ₀ ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p')
        (unitMasses m a A b B) z := by
  obtain ⟨ha, hA, hb, hB⟩ := hM
  have sq : ∀ {x : ℝ}, μ₀ ≤ x → μ₀ ^ 2 ≤ x ^ 2 := fun h => pow_le_pow_left₀ hμ₀.le h 2
  have h₁ := sq ha
  have h₂ := sq hb
  have h₃ := sq hA
  have h₄ := sq hB
  have hle : 3 / 4 * min (m ^ 2 / 4) (μ₀ ^ 2) ≤ 3 / 4 * min (m ^ 2) (μ₀ ^ 2) := by
    have : m ^ 2 / 4 ≤ m ^ 2 := by nlinarith [sq_nonneg m]
    exact mul_le_mul_of_nonneg_left (min_le_min this le_rfl) (by norm_num)
  unfold unitConst unitMasses
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hle.trans (QED.Integration.TwoLoop.symanzikV_classLPV_ge hp hp' hq h₁ h₂ h₃ h₄
      hz hz1 hU)
  · exact QED.Integration.TwoLoop.symanzikV_classXPV_ge hp hp' hq h₁ h₂ h₃ h₄ hz hz1 hU
  · exact QED.Integration.TwoLoop.symanzikV_classCpPV_ge hp hp' hq h₁ h₂ h₃ h₄ hz hz1 hU
  · exact QED.Integration.TwoLoop.symanzikV_classCmPV_ge hp hp' hq h₁ h₂ h₃ h₄ hz hz1 hU
  · exact hle.trans (QED.Integration.TwoLoop.symanzikV_classSpPV_ge hp hp' hq h₁ h₂ h₃ h₄
      hz hz1 hU)
  · exact hle.trans (QED.Integration.TwoLoop.symanzikV_classSmPV_ge hp hp' hq h₁ h₂ h₃ h₄
      hz hz1 hU)

section Limit

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {μ₀ a A b B : ℝ}
  (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hμ₀ hM hp hp' hq

/-- **The `ε → 0⁺` limit of the two-mass unit**, for every quartic `Q` with the values of the
numerator: the parametric integral at `ε = 0` over the eight lines at the masses
`unitMasses m a A b B`; the limit integrand is integrable. -/
theorem tendsto_unitValue (μ i j : Fin 4) {Q : LoopQuartic} (hQ : Q.eval = unitNum c P p p' μ i j) :
    IntegrableOn (paramIntegrand Q (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p')
        (unitMasses P.m a A b B) 0) (simplexSet 7) ∧
      Tendsto (fun ε => unitValue c P (unitMasses P.m a A b B) ε p p' μ i j) (𝓝[>] 0)
        (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet 7, paramIntegrand Q
          (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') (unitMasses P.m a A b B) 0
          x)) := by
  have hB : RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitNum hc P p p' μ i j
  have hV := fun z hz hz1 hU => symanzikV_unit_ge hc hμ₀ hM hp hp' hq (z := z) hz hz1 hU
  refine ⟨integrableOn_paramIntegrand_zero Q _ _ _ (by norm_num) (noSubdivergenceRefined_unit hc)
    hB (unitConst_pos hm hμ₀) hV, ?_⟩
  have h := tendsto_jointEnergyFirstIntegral_of_refined Q (castLoopMatrix (class5LoopMatrixPV c))
    (pvMomentaE c p p') (unitMasses P.m a A b B) (by norm_num) (noSubdivergenceRefined_unit hc) hB
    (unitConst_pos hm hμ₀) hV
  refine h.congr fun ε => ?_
  unfold unitValue unitIntegrand
  rw [hQ]

/-- **The unit limit vertex in parametric form.** -/
theorem unitLimitV_eq (μ i j : Fin 4) {Q : LoopQuartic} (hQ : Q.eval = unitNum c P p p' μ i j) :
    unitLimitV c P (unitMasses P.m a A b B) p p' μ i j =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet 7, paramIntegrand Q
        (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') (unitMasses P.m a A b B) 0 x :=
  (tendsto_unitValue hc P hm hμ₀ hM hp hp' hq μ i j hQ).2.limUnder_eq

theorem tendsto_unitLimitV (μ i j : Fin 4) :
    Tendsto (fun ε => unitValue c P (unitMasses P.m a A b B) ε p p' μ i j) (𝓝[>] 0)
      (𝓝 (unitLimitV c P (unitMasses P.m a A b B) p p' μ i j)) := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  rw [unitLimitV_eq hc P hm hμ₀ hM hp hp' hq μ i j hQ]
  exact (tendsto_unitValue hc P hm hμ₀ hM hp hp' hq μ i j hQ).2

end Limit

/-- **Phase 4 recovered**: at `M = pvMasses P` the unit limit vertex is the class limit vertex. -/
theorem unitLimitV_pvMasses {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    unitLimitV c P (pvMasses P) p p' = QED.TwoLoop.LimitCovariance.classLimitV c P p p' := by
  funext μ
  ext i j
  have hM : MassesGe (min P.mγ P.Λ) P.mγ P.Λ P.mγ P.Λ :=
    ⟨min_le_left _ _, min_le_right _ _, min_le_left _ _, min_le_right _ _⟩
  have hT := tendsto_unitLimitV hc P hm (lt_min hmγ hΛ) hM hp hp' hq μ i j
  rw [unitMasses_pvMasses] at hT
  have hT' : Tendsto (fun ε => contractionValue₂ { P with ε := ε } c.rep (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) (𝓝[>] 0)
      (𝓝 (unitLimitV c P (pvMasses P) p p' μ i j)) := by
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact unitValue_pvMasses hc P hε.ne' p p' μ i j
  simp only [QED.TwoLoop.LimitCovariance.classLimitV, Matrix.of_apply]
  exact hT'.limUnder_eq.symm

/-! ### Uniformity in the masses -/

/-- **A bound uniform in the masses**: for fixed class, parameters, pair and indices, the unit
limit is bounded by one constant for all photon masses `≥ μ₀`. -/
theorem norm_unitLimitV_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ a A b B : ℝ, MassesGe μ₀ a A b B →
      ‖unitLimitV c P (unitMasses P.m a A b B) p p' μ i j‖ ≤ C := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hB : RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitNum hc P p p' μ i j
  refine ⟨π ^ 4 * ∫ x in simplexSet 7, domFun Q (castLoopMatrix (class5LoopMatrixPV c))
    (pvMomentaE c p p') (unitConst P.m μ₀) x, fun a A b B hM => ?_⟩
  rw [unitLimitV_eq hc P hm hμ₀ hM hp hp' hq μ i j hQ, norm_mul, norm_neg, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  exact mul_le_mul_of_nonneg_left (norm_integral_paramIntegrand_zero_le (by norm_num)
    (noSubdivergenceRefined_unit hc) hB (unitConst_pos hm hμ₀)
    fun z hz hz1 hU => symanzikV_unit_ge hc hμ₀ hM hp hp' hq hz hz1 hU) (by positivity)

/-- **Continuity in the masses**: along any family of photon masses `≥ μ₀`, continuous on `s`, the
unit limit is continuous on `s` (for instance `b = √t`, `t ∈ [t₀, ∞)`, the other masses fixed). -/
theorem continuousOn_unitLimitV {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {s : Set X} {a A b B : X → ℝ} (ha : ContinuousOn a s) (hA : ContinuousOn A s)
    (hb : ContinuousOn b s) (hB : ContinuousOn B s)
    (hM : ∀ t ∈ s, MassesGe μ₀ (a t) (A t) (b t) (B t)) (μ i j : Fin 4) :
    ContinuousOn (fun t => unitLimitV c P (unitMasses P.m (a t) (A t) (b t) (B t)) p p' μ i j)
      s := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hQB : RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitNum hc P p p' μ i j
  have hMs : ∀ k, ContinuousOn (fun t => unitMasses P.m (a t) (A t) (b t) (B t) k) s := by
    intro k
    fin_cases k <;> simp [unitMasses, classPVMasses, continuousOn_const, ha, hA, hb, hB]
  have h := continuousOn_integral_paramIntegrand_zero (Q := Q)
    (α := castLoopMatrix (class5LoopMatrixPV c)) (p := pvMomentaE c p p') (by norm_num)
    (noSubdivergenceRefined_unit hc) hQB (unitConst_pos hm hμ₀)
    (fun t => unitMasses P.m (a t) (A t) (b t) (B t)) hMs
    fun t ht z hz hz1 hU => symanzikV_unit_ge hc hμ₀ (hM t ht) hp hp' hq hz hz1 hU
  refine ((continuousOn_const (c := -((π : ℂ) ^ 4))).mul h).congr fun t ht => ?_
  exact unitLimitV_eq hc P hm hμ₀ (hM t ht) hp hp' hq μ i j hQ

end QED.ChainProof.SetCUnit

end
