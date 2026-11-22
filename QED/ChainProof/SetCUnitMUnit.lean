/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMLines

/-!
# Multi-denominator two-loop vertex units: the `ε → 0⁺` limit

Helper level for set (c) (stage L2). The two-mass unit of `QED/ChainProof/SetCUnitLimit.lean`
(eight lines, `class5LoopMatrixPV c`, masses `unitMasses m a A b B`) is extended by `r` extra
lines, each repeating one photon line `s ∈ {4, …, 7}` of the unit, line `8 + j` with its momentum
scaled by `κⱼ ∈ (0, 1]` and mass `csⱼ ≥ μ₀`:

`D_{8+j}(ℓ) = κⱼ² k(ℓ)² + csⱼ² - iε`, `k` the momentum of line `s`.

With `κⱼ = 1` this is a further photon-type denominator of the element line; with
`κⱼ² = x(1-x)`, `csⱼ² = M² ` it is the spectral factor `M² + x(1-x) k² - iε` of the one-loop vacuum
polarization (so the mixed prescription `ε/(x(1-x))` is covered, `inv_spectral_eq`). The value
also carries a power `(k²)ⁿ` of the element momentum (`unitMValue … n …`); this file treats `n = 0`,
`QED/ChainProof/SetCUnitMPow.lean` the powers.

* `unitMMatrix`, `unitMMomenta`, `unitMMasses`, `unitME`: the `r + 8` lines;
* `noSubdivergenceRefined_unitM`, `refinedBound_unitM`: the engine hypotheses, transferred from
  the two-mass unit;
* **`symanzikV_unitM_ge`**: `V ≥ (3/4) min(m²/4, μ₀²)` off `U = 0`, uniformly in the masses;
* **`tendsto_unitMValue`**: the `ε → 0⁺` limit at `n = 0` is the parametric integral at `ε = 0`;
  `jointEnergyFirstIntegrable_unitM`: both stages are integrable at every `ε > 0`;
* **`norm_unitMLimitV_le`**, **`continuousOn_unitMLimitV`**: a bound uniform in all masses
  `≥ μ₀` and continuity along any family of masses `≥ μ₀` (the scales `κ` fixed).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrixPV
  RefinedBound LoopQuartic NoSubdivergenceRefined symanzikU symanzikV classPVMasses
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {r : ℕ}

/-! ### The lines -/

/-- An eight-line family extended by `r` extra lines. -/
def mExt {X : Type*} (x : Fin 8 → X) (y : Fin r → X) (i : Fin (r + 8)) : X :=
  if h : (i : ℕ) < 8 then x ⟨i, h⟩ else y ⟨i - 8, by have := i.isLt; omega⟩

/-- The eight lines of the two-mass unit inside the `r + 8` lines. -/
def mEmb (r : ℕ) : Fin 8 ↪ Fin (r + 8) := Fin.castLEEmb (by omega)

/-- The extra line `8 + j`. -/
def mExtra (r : ℕ) (j : Fin r) : Fin (r + 8) := ⟨j + 8, by omega⟩

theorem mExt_mEmb {X : Type*} (x : Fin 8 → X) (y : Fin r → X) (j : Fin 8) :
    mExt x y (mEmb r j) = x j := by
  simp [mExt, mEmb, j.isLt]

theorem mExt_mExtra {X : Type*} (x : Fin 8 → X) (y : Fin r → X) (j : Fin r) :
    mExt x y (mExtra r j) = y j := by
  simp [mExt, mExtra]

theorem mem_mEmb_or_mExtra (i : Fin (r + 8)) : (∃ j, i = mEmb r j) ∨ ∃ j, i = mExtra r j := by
  by_cases h : (i : ℕ) < 8
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext (by simp [mEmb])⟩
  · exact Or.inr ⟨⟨i - 8, by have := i.isLt; omega⟩, Fin.ext (by simp [mExtra]; omega)⟩

/-- The line map: the unit lines are themselves, the extra lines repeat line `s`. -/
def mLine (s : Fin 8) : Fin (r + 8) → Fin 8 := mExt id fun _ => s

/-- The momentum scales: `1` on the unit lines, `κ` on the extra lines. -/
def mScale (κ : Fin r → ℝ) : Fin (r + 8) → ℝ := mExt (fun _ => 1) κ

theorem mScale_ne_zero {κ : Fin r → ℝ} (hκ : ∀ j, κ j ≠ 0) (i : Fin (r + 8)) :
    mScale κ i ≠ 0 := by
  rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [mScale, mExt_mEmb]
  · simpa [mScale, mExt_mExtra] using hκ j

/-- The loop matrix of the multi-denominator unit. -/
def unitMMatrix (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) : Fin (r + 8) → Fin 2 → ℝ :=
  fun i => mScale κ i • castLoopMatrix (class5LoopMatrixPV c) (mLine s i)

/-- The external line momenta of the multi-denominator unit. -/
def unitMMomenta (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (p p' : Fin 4 → ℝ) :
    Fin (r + 8) → Fin 4 → ℝ :=
  fun i => mScale κ i • pvMomentaE c p p' (mLine s i)

/-- The masses: those of the two-mass unit and `cs` on the extra lines. -/
def unitMMasses (m a A b B : ℝ) (cs : Fin r → ℝ) : Fin (r + 8) → ℝ :=
  mExt (unitMasses m a A b B) cs

/-- The numerator lines: the four electron lines. -/
def unitME (r : ℕ) : Finset (Fin (r + 8)) := ({0, 1, 2, 3} : Finset (Fin 8)).map (mEmb r)

theorem unitMMatrix_mEmb (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (j : Fin 8) :
    unitMMatrix c s κ (mEmb r j) = castLoopMatrix (class5LoopMatrixPV c) j := by
  simp [unitMMatrix, mScale, mLine, mExt_mEmb]

/-- The element momentum `k(ℓ)`, the momentum of line `s` of the two-mass unit. -/
def elemMom (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') s ℓ

/-- **The extra lines**: `D_{8+j} = κⱼ² k² + csⱼ² - iε`. -/
theorem lineDenom_unitM_mExtra (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (p p' : Fin 4 → ℝ)
    (m a A b B : ℝ) (cs : Fin r → ℝ) (ε : ℝ) (j : Fin r) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) ε
        (mExtra r j) ℓ =
      ((κ j ^ 2 * Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) + cs j ^ 2 : ℝ) :
        ℂ) - (ε : ℂ) * I := by
  have h := lineDenom_scale (mScale κ)
    (fun i => castLoopMatrix (class5LoopMatrixPV c) (mLine s i))
    (fun i => pvMomentaE c p p' (mLine s i)) (unitMMasses m a A b B cs) ε (mExtra r j) ℓ
  simp only [mScale, mLine, unitMMasses, mExt_mExtra] at h
  exact h

/-! ### The engine hypotheses -/

theorem noSubdivergenceRefined_unitM {c : Class5} (hc : c ∈ openClasses) (s : Fin 8)
    {κ : Fin r → ℝ} (hκ : ∀ j, κ j ≠ 0) :
    NoSubdivergenceRefined 2 (unitME r) (unitMMatrix c s κ) :=
  noSubdivergenceRefined_scale_comp (noSubdivergenceRefined_unit hc) (mLine s) (mEmb r)
    (fun j => by simp [mLine, mExt_mEmb]) (mScale κ) (mScale_ne_zero hκ)

theorem refinedBound_unitM {c : Class5} (hc : c ∈ openClasses) (P : Params) (s : Fin 8)
    (κ : Fin r → ℝ) (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    RefinedBound (unitMMatrix c s κ) (unitME r) 4 (unitNum c P p p' μ i j) :=
  refinedBound_map (mEmb r) (fun e _ => unitMMatrix_mEmb c s κ e)
    (refinedBound_unitNum hc P p p' μ i j)

theorem unitConst_le_sq {m μ₀ : ℝ} : unitConst m μ₀ ≤ μ₀ ^ 2 := by
  unfold unitConst
  have := min_le_right (m ^ 2 / 4) (μ₀ ^ 2)
  nlinarith [sq_nonneg μ₀]

/-- The hypotheses on the extra lines: scales in `(0, 1]`, masses at least `μ₀`. -/
def ExtraGe (μ₀ : ℝ) (κ cs : Fin r → ℝ) : Prop := ∀ j, 0 < κ j ∧ κ j ≤ 1 ∧ μ₀ ≤ cs j

theorem ExtraGe.ne_zero {μ₀ : ℝ} {κ cs : Fin r → ℝ} (h : ExtraGe μ₀ κ cs) (j : Fin r) :
    κ j ≠ 0 :=
  (h j).1.ne'

/-- **Positivity of `V` for the multi-denominator unit, uniform in the masses.** -/
theorem symanzikV_unitM_ge {c : Class5} (hc : c ∈ openClasses) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {m μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B) {κ cs : Fin r → ℝ}
    (hX : ExtraGe μ₀ κ cs) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin (r + 8) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (unitMMatrix c s κ) z ≠ 0) :
    unitConst m μ₀ ≤
      symanzikV (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) z := by
  have hM0 : MassesGe μ₀ μ₀ μ₀ μ₀ μ₀ := ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hc0 := unitConst_le_sq (m := m) (μ₀ := μ₀)
  refine le_symanzikV_scale_comp_of (σ := mLine s) (M := unitMasses m μ₀ μ₀ μ₀ μ₀)
    (fun w hw hw1 hUw => symanzikV_unit_ge hc hμ₀ hM0 hp hp' hq hw hw1 hUw)
    (mScale_ne_zero hX.ne_zero) (fun i => ?_) hz hz1 hU
  obtain ⟨ha, hA, hb, hB⟩ := hM
  have sq : ∀ {x : ℝ}, μ₀ ≤ x → μ₀ ^ 2 ≤ x ^ 2 := fun h => pow_le_pow_left₀ hμ₀.le h 2
  rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [mScale, mLine, unitMMasses, mExt_mEmb, id]
    fin_cases j <;> simp [unitMasses, classPVMasses, sq ha, sq hA, sq hb, sq hB]
  · simp only [mScale, mLine, unitMMasses, mExt_mExtra]
    have hsμ : unitMasses m μ₀ μ₀ μ₀ μ₀ s = μ₀ := by
      fin_cases s <;> simp_all [unitMasses, classPVMasses]
    rw [hsμ]
    obtain ⟨hκ0, hκ1, hcs⟩ := hX j
    have h1 : κ j ^ 2 ≤ 1 := by nlinarith
    have h2 := sq hcs
    nlinarith [sq_nonneg (κ j)]

/-! ### The unit and its limit -/

/-- The momentum square `k²` of the element line, as a complex number. -/
noncomputable def elemSq (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ℂ :=
  ((Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) : ℝ) : ℂ)

/-- The integrand of the multi-denominator unit with the power `(k²)ⁿ`. -/
noncomputable def unitMIntegrand (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  unitNum c P p p' μ i j ℓ * elemSq c s p p' ℓ ^ n *
    ∏ k, (lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') M ε k ℓ)⁻¹

/-- **The multi-denominator unit value**: the joint energy-first integral of `unitMIntegrand`. -/
noncomputable def unitMValue (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral 2 (unitMIntegrand c P s κ M ε p p' n μ i j)

/-- **The multi-denominator unit limit vertex**: the entrywise `ε → 0⁺` limits. -/
noncomputable def unitMLimitV (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (p p' : Fin 4 → ℝ) (n : ℕ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j =>
    limUnder (𝓝[>] (0 : ℝ)) fun ε => unitMValue c P s κ M ε p p' n μ i j

theorem unitMIntegrand_zero (c : Class5) (P : Params) (s : Fin 8) (κ : Fin r → ℝ)
    (M : Fin (r + 8) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    unitMIntegrand c P s κ M ε p p' 0 μ i j = fun ℓ => unitNum c P p p' μ i j ℓ *
      ∏ k, (lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') M ε k ℓ)⁻¹ := by
  funext ℓ
  simp [unitMIntegrand]

/-- **Integrability at fixed `ε > 0`** of both stages, at `n = 0`, for any masses. -/
theorem jointEnergyFirstIntegrable_unitM {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (s : Fin 8) {κ : Fin r → ℝ} (hκ : ∀ j, κ j ≠ 0) (M : Fin (r + 8) → ℝ) (p p' : Fin 4 → ℝ)
    {ε : ℝ} (hε : 0 < ε) (μ i j : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s κ M ε p p' 0 μ i j) := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hB : RefinedBound (unitMMatrix c s κ) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s κ p p' μ i j
  rw [unitMIntegrand_zero, ← hQ]
  exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q _ _ _ (m := r + 7) (by omega) hε (noSubdivergenceRefined_unitM hc s hκ) hB

section Limit

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
  {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hM hX hp hp' hq

/-- **The `ε → 0⁺` limit of the multi-denominator unit** at `n = 0`, for every quartic `Q` with
the values of the numerator: the parametric integral at `ε = 0` over the `r + 8` lines. -/
theorem tendsto_unitMValue (μ i j : Fin 4) {Q : LoopQuartic}
    (hQ : Q.eval = unitNum c P p p' μ i j) :
    IntegrableOn (paramIntegrand Q (unitMMatrix c s κ) (unitMMomenta c s κ p p')
        (unitMMasses P.m a A b B cs) 0) (simplexSet (r + 7)) ∧
      Tendsto (fun ε => unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' 0 μ i j)
        (𝓝[>] 0)
        (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet (r + 7), paramIntegrand Q (unitMMatrix c s κ)
          (unitMMomenta c s κ p p') (unitMMasses P.m a A b B cs) 0 x)) := by
  have hB : RefinedBound (unitMMatrix c s κ) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s κ p p' μ i j
  have hV := fun z hz hz1 hU => symanzikV_unitM_ge hc hs hμ₀ hM hX hp hp' hq (z := z) hz hz1 hU
  have hcrit := noSubdivergenceRefined_unitM hc s hX.ne_zero (κ := κ)
  refine ⟨integrableOn_paramIntegrand_zero Q _ _ _ (m := r + 7) (by omega) hcrit hB
    (unitConst_pos hm hμ₀) hV, ?_⟩
  have h := tendsto_jointEnergyFirstIntegral_of_refined Q (unitMMatrix c s κ)
    (unitMMomenta c s κ p p') (unitMMasses P.m a A b B cs) (m := r + 7) (by omega) hcrit hB
    (unitConst_pos hm hμ₀) hV
  refine h.congr fun ε => ?_
  unfold unitMValue
  rw [unitMIntegrand_zero, hQ]

/-- **The multi-denominator unit limit in parametric form** (`n = 0`). -/
theorem unitMLimitV_eq (μ i j : Fin 4) {Q : LoopQuartic} (hQ : Q.eval = unitNum c P p p' μ i j) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' 0 μ i j =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet (r + 7), paramIntegrand Q (unitMMatrix c s κ)
        (unitMMomenta c s κ p p') (unitMMasses P.m a A b B cs) 0 x :=
  (tendsto_unitMValue hc P hm hs hμ₀ hM hX hp hp' hq μ i j hQ).2.limUnder_eq

theorem tendsto_unitMLimitV (μ i j : Fin 4) :
    Tendsto (fun ε => unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' 0 μ i j) (𝓝[>] 0)
      (𝓝 (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' 0 μ i j)) := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  rw [unitMLimitV_eq hc P hm hs hμ₀ hM hX hp hp' hq μ i j hQ]
  exact (tendsto_unitMValue hc P hm hs hμ₀ hM hX hp hp' hq μ i j hQ).2

end Limit

/-! ### Uniformity in the masses -/

/-- **A bound uniform in the masses** (`n = 0`, the scales `κ` fixed): one constant for all
photon and extra masses `≥ μ₀`. -/
theorem norm_unitMLimitV_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ : Fin r → ℝ}
    (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      ‖unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' 0 μ i j‖ ≤ C := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hB : RefinedBound (unitMMatrix c s κ) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s κ p p' μ i j
  have hκ0 : ∀ j, κ j ≠ 0 := fun j => (hκ j).1.ne'
  refine ⟨π ^ 4 * ∫ x in simplexSet (r + 7), domFun Q (unitMMatrix c s κ)
    (unitMMomenta c s κ p p') (unitConst P.m μ₀) x, fun a A b B cs hM hcs => ?_⟩
  have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
  rw [unitMLimitV_eq hc P hm hs hμ₀ hM hX hp hp' hq μ i j hQ, norm_mul, norm_neg, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  exact mul_le_mul_of_nonneg_left (norm_integral_paramIntegrand_zero_le (m := r + 7) (by omega)
    (noSubdivergenceRefined_unitM hc s hκ0) hB (unitConst_pos hm hμ₀)
    fun z hz hz1 hU => symanzikV_unitM_ge hc hs hμ₀ hM hX hp hp' hq hz hz1 hU) (by positivity)

/-- **Continuity in the masses** (`n = 0`, the scales `κ` fixed): along any family of photon and
extra masses `≥ μ₀`, continuous on `s'`, the unit limit is continuous on `s'` (for instance one
extra mass `√t`, `t ∈ [t₀, ∞)`, as in a dispersion integral). -/
theorem continuousOn_unitMLimitV {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
    (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ : Fin r → ℝ} (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {s' : Set X} {a A b B : X → ℝ} {cs : X → Fin r → ℝ} (ha : ContinuousOn a s')
    (hA : ContinuousOn A s') (hb : ContinuousOn b s') (hB : ContinuousOn B s')
    (hcs : ∀ j, ContinuousOn (fun t => cs t j) s')
    (hM : ∀ t ∈ s', MassesGe μ₀ (a t) (A t) (b t) (B t)) (hcs0 : ∀ t ∈ s', ∀ j, μ₀ ≤ cs t j)
    (μ i j : Fin 4) :
    ContinuousOn (fun t =>
      unitMLimitV c P s κ (unitMMasses P.m (a t) (A t) (b t) (B t) (cs t)) p p' 0 μ i j) s' := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hQB : RefinedBound (unitMMatrix c s κ) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s κ p p' μ i j
  have hκ0 : ∀ j, κ j ≠ 0 := fun j => (hκ j).1.ne'
  have hX : ∀ t ∈ s', ExtraGe μ₀ κ (cs t) := fun t ht j => ⟨(hκ j).1, (hκ j).2, hcs0 t ht j⟩
  have hMs : ∀ k, ContinuousOn
      (fun t => unitMMasses P.m (a t) (A t) (b t) (B t) (cs t) k) s' := by
    intro k
    rcases mem_mEmb_or_mExtra k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [unitMMasses, mExt_mEmb]
      fin_cases j <;> simp [unitMasses, classPVMasses, continuousOn_const, ha, hA, hb, hB]
    · simp only [unitMMasses, mExt_mExtra]
      exact hcs j
  have h := continuousOn_integral_paramIntegrand_zero (Q := Q) (α := unitMMatrix c s κ)
    (p := unitMMomenta c s κ p p') (m := r + 7) (by omega) (noSubdivergenceRefined_unitM hc s hκ0)
    hQB (unitConst_pos hm hμ₀) (fun t => unitMMasses P.m (a t) (A t) (b t) (B t) (cs t)) hMs
    fun t ht z hz hz1 hU => symanzikV_unitM_ge hc hs hμ₀ (hM t ht) (hX t ht) hp hp' hq hz hz1 hU
  refine ((continuousOn_const (c := -((π : ℂ) ^ 4))).mul h).congr fun t ht => ?_
  exact unitMLimitV_eq hc P hm hs hμ₀ (hM t ht) (hX t ht) hp hp' hq μ i j hQ

end QED.ChainProof.SetCUnitM

end
