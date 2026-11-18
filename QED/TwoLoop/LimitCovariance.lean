/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitCovarianceCounterterm
public import QED.TwoLoop.VertexLimit

/-!
# The `ε → 0⁺` limit of the order-`e⁵` vertex is little-group covariant

Obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), its analytic half. For the
parameters of `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline` (`m, m_γ, Λ > 0`,
`M₁, M₂ ≥ m` with the two Pauli–Villars conditions, any counterterms) and an on-shell
positive-energy pair `p, p'` with `q² ≥ 0`, the limit `V` of the order-`e⁵` vertex (HV₂) is
little-group covariant at `(p', p)` (`QED.Dirac.IsLittleGroupCovariant`): for every real `L`
fixing `p` and `p'` and every `S, T` with `S T = 1`, `S γ^μ T = L^μ_ν γ^ν`, one has
`S V^μ T = L^μ_ν V^ν`.

## Proof

`V = (1/i) (∑_{c ≠ F±} sign(c) V_c + ∑_{counterterm classes} V_c)` with `V_c` the vertex of limits
of the class values (`classLimitV`, `ctLimitV`), as in `QED/TwoLoop/VertexLimit.lean`. Each
`V_c` is covariant:

* the open-line classes (`isLittleGroupCovariant_classLimitV`) and the five pieces of `VP`
  (`isLittleGroupCovariant_classLimitV_VP`) are parametric integrals
  `-π⁴ ∫ paramIntegrand Q` whose numerators are covariant matrices; covariance comes from the
  linearity of the parametric value in the numerator and its invariance under `ℓ ↦ L ℓ`
  (the Symanzik data depend on the external momenta only through `L`-fixed vectors, and
  `L g Lᵀ = g` makes the contractions with `G = g ⊗ A⁻¹` invariant);
* the counterterm classes (`isLittleGroupCovariant_ctLimitV`) through the auxiliary-loop
  product (`δ₂`, `δ_m`, `δ₃`) or the one-loop closed form (`δ₁`).

The joint energy-first integral at fixed `ε > 0` is not Lorentz invariant (it singles out the
energy components), so covariance is proved on the parametric limit formulas, not before the
limit.

## Main statements

* `QED.TwoLoop.LimitCovariance.isLittleGroupCovariant_of_isVertexOrderFiveLimit`.
* `QED.TwoLoop.LimitCovariance.isLittleGroupCovariant_headline`: the same for the parameters of
  the headline (HV₃).
* `QED.TwoLoop.LimitCovariance.exists_isVertexOrderFiveLimit_and_isLittleGroupCovariant_headline`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.TwoLoop.LimitCovariance

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

theorem isLittleGroupCovariant_add {p' p : Fin 4 → ℝ} {A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsLittleGroupCovariant p' p A) (hB : IsLittleGroupCovariant p' p B) :
    IsLittleGroupCovariant p' p fun μ => A μ + B μ := by
  intro L S T hST hγ hLp hLp' μ
  rw [Matrix.mul_add, Matrix.add_mul, hA L S T hST hγ hLp hLp' μ, hB L S T hST hγ hLp hLp' μ,
    vecAct_add]

/-- **O2-20, analytic half: the `ε → 0⁺` limit of the order-`e⁵` vertex is little-group
covariant**, for `m, m_γ, Λ > 0`, `M₁, M₂ ≥ m` with the Pauli–Villars conditions, any
counterterms, and an on-shell positive-energy pair with `(p' - p)² ≥ 0`. -/
theorem isLittleGroupCovariant_of_isVertexOrderFiveLimit (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) :
    IsLittleGroupCovariant p' p V := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hVeq : V = fun μ => (1 / I) •
      ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) • classLimitV c P p p' μ) +
        ∑ c ∈ (Finset.univ : Finset CtClass), (1 : ℂ) • ctLimitV c P p p' μ) := by
    funext μ
    ext i j
    have e : ∀ ε : ℝ, vertexOrderFive { P with ε := ε } p' p μ i j = (1 / I) *
        (∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * contractionValue₂ { P with ε := ε } c.rep
            (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) +
          ∑ c : CtClass, contractionValue₂ { P with ε := ε } c.rep
            (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) :=
      fun ε => by
        rw [← onePIFunction₂_five_sub_four_eq_classes { P with ε := ε } hmom (fun _ => i)
          (fun _ => j) (fun _ => μ)]
        rfl
    have h₁ : ∀ c ∈ Furry.nonFurry, Tendsto (fun ε => (c.sign : ℂ) * contractionValue₂
        { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ)) (𝓝[>] 0) (𝓝 ((c.sign : ℂ) * classLimitV c P p p' μ i j)) :=
      fun c hc => (tendsto_nhds_limUnder (VertexLimit.exists_tendsto_contractionValue₂_nonFurry hc
        P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ (pOut := fun _ => p') (pIn := fun _ => p)
        (kIn := fun _ => p' - p) hmom hp hp' hq (fun _ => i) (fun _ => j)
        (fun _ => μ))).const_mul _
    have h₂ : ∀ c ∈ (Finset.univ : Finset CtClass), Tendsto (fun ε => contractionValue₂
        { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ)) (𝓝[>] 0) (𝓝 (ctLimitV c P p p' μ i j)) :=
      fun c _ => tendsto_nhds_limUnder (CountertermLimit.exists_tendsto_contractionValue₂_ctClass c
        P hm hmγ hΛ (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp'
        hp0 hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ))
    have hT := ((tendsto_finsetSum _ h₁).add (tendsto_finsetSum _ h₂)).const_mul (1 / I)
    have hT' := hT.congr' (Eventually.of_forall fun ε => (e ε).symm)
    rw [tendsto_nhds_unique (hV μ i j) hT']
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, smul_eq_mul, one_mul]
  rw [hVeq]
  refine isLittleGroupCovariant_smul _ (isLittleGroupCovariant_add ?_ ?_)
  · refine VertexCovariance.isLittleGroupCovariant_sum _ _ fun c hc => ?_
    by_cases hVP : c = .VP
    · subst hVP
      exact isLittleGroupCovariant_classLimitV_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hq
    · exact isLittleGroupCovariant_classLimitV (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP)
        P hm hmγ hΛ hp hp' hq
  · exact VertexCovariance.isLittleGroupCovariant_sum _ _ fun c _ =>
      isLittleGroupCovariant_ctLimitV c P hm hmγ hΛ hp hp' hp0 hp0' hq

/-- **O2-20 for the parameters of the headline (HV₃)**: every `ε → 0⁺` limit of the order-`e⁵`
vertex at `{P₀ with M₁, M₂, c₁, c₂, m_γ, Λ, δ₁ := d₁, δ₂ := d₂, δ_m := dm, δ₃ := d₃}`, under the
hypotheses of `QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline`, is little-group
covariant at `(p', p)`. -/
theorem isLittleGroupCovariant_headline (P₀ : Params) (hm : 0 < P₀.m)
    (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V) :
    IsLittleGroupCovariant p' p V :=
  isLittleGroupCovariant_of_isVertexOrderFiveLimit
    { P₀ with
      M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
      δm := dm, δ₃ := d₃ } hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂ hp hp' hp0 hp0' hq.le hV

/-- The limit of the headline exists and is little-group covariant. -/
theorem exists_isVertexOrderFiveLimit_and_isLittleGroupCovariant_headline (P₀ : Params)
    (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂)
    (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P₀.m ^ 2) (hp : Minkowski.dot p p = -P₀.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    ∃ V, IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V ∧ IsLittleGroupCovariant p' p V := by
  obtain ⟨V, hV⟩ := VertexLimit.exists_isVertexOrderFiveLimit_headline P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂
    hPV₁ hPV₂ mγ Λ hmγ hΛ d₁ d₂ dm d₃ p' p hp' hp hp0' hp0 hq
  exact ⟨V, hV, isLittleGroupCovariant_headline P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ
    d₁ d₂ dm d₃ p' p hp' hp hp0' hp0 hq V hV⟩

end QED.TwoLoop.LimitCovariance

end
