/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliAt
public import QED.ChainProof.SetCLimCtS
public import QED.ChainProof.SetCLimCtD
public import QED.ChainProof.SetCLimCtCB
public import QED.ChainProof.SetCUnitPauli
public import QED.TwoLoop.PauliZeroExplicit
public import QED.TwoLoop.PauliZeroCovariance

/-!
# Set (c): the canonical Pauli limits of the counterterm classes with a two-loop limit

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. Of the 20
counterterm and VP-share classes of `QED.ChainProof.SetCPauli.ctFam`, the limits of eleven are
T1's (Phase 4) limits at modified parameters:

* `Sₖ` (`k < 5`): `ctLimitV (sCls k)` at `sParams` (`QED.ChainProof.SetCPauli.isClassLimC_S`);
* `CDₖ t` (`2 ≤ k`): `δ₁ • ctLimitV (d3Cls t)` at `cdParams` (`isClassLimC_CD`);
* `CBₖ` (`2 ≤ k`): `-e² d₁(e⁻, 0) • classLimitV .VP` at `regParams` (`isClassLimC_CB`).

For these, Phase 4 identifies the symmetrized curve limit `(S(u) + S(-u))/(2u²)` explicitly
(`QED.TwoLoop.PauliZeroExplicit.tendsto_ctNum_explicit`, `tendsto_VP_explicit`). The Pauli
numerator is even along the curve by reflection covariance (`ctNum_neg`, `classNum_VP_neg`), so
`S(u)/u²` converges to the same value, and `QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of`
turns it into the `q² → 0⁺` limit at the canonical pair, divided by `64 e m⁵`.

## Main statements

* `tendsto_formFactorProj₂_ctLimitV`, `tendsto_formFactorProj₂_VP`: the canonical Pauli limits
  of T1's counterterm classes and of its vacuum-polarization class;
* **`setCClassPauli_S`**, **`setCClassPauli_CD`**, **`setCClassPauli_CB`**: the per-class Pauli
  limits (`QED.ChainProof.SetCPauli.SetCClassPauli`) of these eleven classes, with the values
  `ctZero (sCls k) / (64 e m⁵)`, `δ₁ ctZero (d3Cls t) / (64 e m⁵)` and
  `-e² d₁(e⁻, 0) vpZero / (64 e m⁵)`;
* **`setCClassPauli_ct`**: the per-class Pauli limits of all 20 classes (values `ctPauliVal`),
  from those of the four classes `CB0`, `CB1`, `CD0 t`, `CD1 t`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCPauli

open QED.Dirac QED.TwoLoop.Enumeration QED.TwoLoop.Relabel
open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.PauliZeroExplicit
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### T1's classes along the curve -/

theorem neg_mem_Ioo_one {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : -u ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- **The Pauli numerator of a counterterm class is even along the curve** (reflection
covariance, `QED.TwoLoop.PauliZero.ctLimitV_map`). -/
theorem ctNum_neg (c : CtClass) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : ctNum P c (-u) = ctNum P c u := by
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
    (by rw [dot_axisOne]; exact one_ne_zero)
  have hW := ctLimitV_map c P hm hmγ hΛ h (p := restMomentum P.m) (p' := curveMomentum P.m u)
    (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu) (restMomentum_pos hm)
    (curveMomentum_pos hm hu) (by rw [reflectMatrix_restMomentum]; exact restMomentum_pos hm)
    (by rw [reflectMatrix_curveMomentum]; exact curveMomentum_pos hm (neg_mem_Ioo_one hu))
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu)
  have e := pauliNum_map h P.m (curveMomentum P.m u) (restMomentum P.m) hW
  rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum] at e
  exact e

/-- **The Pauli numerator of the vacuum-polarization class is even along the curve.** -/
theorem classNum_VP_neg (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    classNum P .VP (-u) = classNum P .VP u := by
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
    (by rw [dot_axisOne]; exact one_ne_zero)
  have hW := QED.TwoLoop.ReflCovariance.classLimitV_VP_map P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ h
    (p := restMomentum P.m) (p' := curveMomentum P.m u) (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu)
  have e := pauliNum_map h P.m (curveMomentum P.m u) (restMomentum P.m) hW
  rw [reflectMatrix_curveMomentum, reflectMatrix_restMomentum] at e
  exact e

/-- An even function along the curve: `S(u)/u²` has the limit of `(S(u) + S(-u))/(2u²)`. -/
theorem tendsto_div_of_evenQuot {S : ℝ → ℂ} {L : ℂ}
    (hS : ∀ u ∈ Ioo (-1 : ℝ) 1, S (-u) = S u)
    (h : Tendsto (evenQuot S) (𝓝[≠] 0) (𝓝 L)) :
    Tendsto (fun u => S u / (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 L) := by
  refine h.congr' ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0] with u hu
  rw [evenQuot, hS u hu]
  by_cases hu0 : (u : ℂ) = 0
  · simp [hu0]
  · field_simp
    ring

/-- **The canonical Pauli limit of T1's counterterm class `c`**: at the canonical pair with
`q² = Q`, the Pauli projection of `ctLimitV c P` tends to `ctZero c P / (64 e m⁵)`. -/
theorem tendsto_formFactorProj₂_ctLimitV (c : CtClass) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (e : ℝ) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
        (ctLimitV c P (restMomentum P.m) (boostMomentum P.m Q)))
      (𝓝[>] 0) (𝓝 (ctZero c P / (64 * (e : ℂ) * (P.m : ℂ) ^ 5))) :=
  QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of hm e
    (fun p' => ctLimitV c P (restMomentum P.m) p')
    (tendsto_div_of_evenQuot (fun _ hu => ctNum_neg c P hm hmγ hΛ hu)
      (tendsto_ctNum_explicit P hm hmγ hΛ c))

/-- **The canonical Pauli limit of T1's vacuum-polarization class**: `vpZero P / (64 e m⁵)`. -/
theorem tendsto_formFactorProj₂_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (e : ℝ) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
        (classLimitV .VP P (restMomentum P.m) (boostMomentum P.m Q)))
      (𝓝[>] 0) (𝓝 (vpZero P / (64 * (e : ℂ) * (P.m : ℂ) ^ 5))) :=
  QED.ChainProof.SetCUnit.tendsto_formFactorProj₂_of hm e
    (fun p' => classLimitV .VP P (restMomentum P.m) p')
    (tendsto_div_of_evenQuot (fun _ hu => classNum_VP_neg P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu)
      (tendsto_VP_explicit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂))

/-! ### The per-class Pauli limits -/

variable {P₀ : Params}

/-- From the identified class limit and the `q² → 0⁺` limit of its Pauli projection, the
per-class Pauli limit. -/
theorem setCClassPauli_of_tendsto {r : CtIdx} {β : ClsPauliVal}
    (W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → RegCt → ℝ × ℝ × ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) →
      Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ p' p,
      IsPairQ P₀.m p' p → IsClassLimC ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p
        (W M₁ M₂ c₁ c₂ mγ Λ D s p' p))
    (hT : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      Tendsto (fun Q => QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q)
        (restMomentum P₀.m) (W M₁ M₂ c₁ c₂ mγ Λ D s (boostMomentum P₀.m Q) (restMomentum P₀.m)))
        (𝓝[>] 0) (𝓝 (β M₁ M₂ c₁ c₂ mγ Λ D s))) :
    SetCClassPauli ctFam P₀ r β := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA η hη
  have hm : 0 < P₀.m := by obtain ⟨-, -, -, -, hmγ, -, -, hm2, -⟩ := hA; linarith
  filter_upwards [Metric.tendsto_nhds.1 (hT M₁ M₂ c₁ c₂ mγ Λ D s hA) η hη,
    self_mem_nhdsWithin] with Q hQ (hQ0 : 0 < Q)
  intro Y hY
  have hpq := QED.ChainProof.HCValue.isPairQ_canonical' hm hQ0
  have eY : Y = W M₁ M₂ c₁ c₂ mγ Λ D s (boostMomentum P₀.m Q) (restMomentum P₀.m) := by
    funext μ
    ext i j
    exact tendsto_nhds_unique (hY μ i j) (hW M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hpq μ i j)
  rw [eY, ← dist_eq_norm]
  exact hQ

/-- **The canonical Pauli limits of the five VP-share classes `Sₖ`.** -/
theorem setCClassPauli_S (k : Fin 5) :
    SetCClassPauli ctFam P₀ (.inr (.inr k)) fun M₁ M₂ c₁ c₂ mγ Λ D s =>
      ctZero (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) /
        (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5) := by
  refine setCClassPauli_of_tendsto
    (fun M₁ M₂ c₁ c₂ mγ Λ D s p' p => ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) p p')
    (fun M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq => isClassLimC_S hA k hpq)
    fun M₁ M₂ c₁ c₂ mγ Λ D s hA => ?_
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  exact tendsto_formFactorProj₂_ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ hΛ
    P₀.e

/-- **The canonical Pauli limits of the six classes `CDₖ t`, `2 ≤ k`.** -/
theorem setCClassPauli_CD (k : Fin 5) (hk : 2 ≤ k) (t : Fin 2) :
    SetCClassPauli ctFam P₀ (.inr (.inl (k, t))) fun M₁ M₂ c₁ c₂ mγ Λ D s =>
      ((cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₁ : ℂ) *
        (ctZero (d3Cls t) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) /
          (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) := by
  refine setCClassPauli_of_tendsto
    (fun M₁ M₂ c₁ c₂ mγ Λ D s p' p => cdLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s t p' p)
    (fun M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq => isClassLimC_CD hA k hk t hpq)
    fun M₁ M₂ c₁ c₂ mγ Λ D s hA => ?_
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  refine ((tendsto_formFactorProj₂_ctLimitV (d3Cls t) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ
    hΛ P₀.e).const_mul ((cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₁ : ℂ)).congr fun Q => ?_
  simp only [cdLim]
  rw [formFactorProj₂_const_smul]
  rfl

/-- **The canonical Pauli limits of the three classes `CBₖ`, `2 ≤ k`.** -/
theorem setCClassPauli_CB (k : Fin 5) (hk : 2 ≤ k) :
    SetCClassPauli ctFam P₀ (.inl k) fun M₁ M₂ c₁ c₂ mγ Λ D s =>
      -cbW P₀ D s * (vpZero (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) /
        (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) := by
  refine setCClassPauli_of_tendsto
    (fun M₁ M₂ c₁ c₂ mγ Λ D s p' p => cbLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p)
    (fun M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq => isClassLimC_CB hA k hk hpq)
    fun M₁ M₂ c₁ c₂ mγ Λ D s hA => ?_
  obtain ⟨hM₁, hM₂, hc₁, hc₂, hmγ, hΛ, -, hm2, -, -⟩ := hA
  have hm : 0 < P₀.m := by linarith
  refine ((tendsto_formFactorProj₂_VP (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hmγ hΛ hM₁.le hM₂.le
    hc₁ hc₂ P₀.e).const_mul (-cbW P₀ D s)).congr fun Q => ?_
  simp only [cbLim]
  rw [formFactorProj₂_const_smul]

/-! ### The 20 counterterm and VP-share classes -/

/-- The per-class Pauli values of the 20 counterterm and VP-share classes: the explicit values
of the eleven classes above, and `βx r` for the four classes `CB0`, `CB1`, `CD0 t`, `CD1 t`. -/
noncomputable def ctPauliVal (P₀ : Params) (βx : CtIdx → ClsPauliVal) : CtIdx → ClsPauliVal
  | .inl k => if 2 ≤ k then fun M₁ M₂ c₁ c₂ mγ Λ D s =>
      -cbW P₀ D s * (vpZero (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) /
        (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) else βx (.inl k)
  | .inr (.inl (k, t)) => if 2 ≤ k then fun M₁ M₂ c₁ c₂ mγ Λ D s =>
      ((cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₁ : ℂ) *
        (ctZero (d3Cls t) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) /
          (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)) else βx (.inr (.inl (k, t)))
  | .inr (.inr k) => fun M₁ M₂ c₁ c₂ mγ Λ D s =>
      ctZero (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) / (64 * (P₀.e : ℂ) * (P₀.m : ℂ) ^ 5)

/-- **The per-class Pauli limits of the 20 counterterm and VP-share classes**, from those of
`CB0`, `CB1`, `CD0 t`, `CD1 t`. -/
theorem setCClassPauli_ct {βx : CtIdx → ClsPauliVal}
    (hCB : ∀ k : Fin 5, k < 2 → SetCClassPauli ctFam P₀ (.inl k) (βx (.inl k)))
    (hCD : ∀ (k : Fin 5) (t : Fin 2), k < 2 →
      SetCClassPauli ctFam P₀ (.inr (.inl (k, t))) (βx (.inr (.inl (k, t))))) :
    ∀ r, SetCClassPauli ctFam P₀ r (ctPauliVal P₀ βx r)
  | .inl k => by
    by_cases hk : 2 ≤ k
    · simpa only [ctPauliVal, hk, ite_true] using setCClassPauli_CB k hk
    · simpa only [ctPauliVal, hk, ite_false] using hCB k (not_le.mp hk)
  | .inr (.inl (k, t)) => by
    by_cases hk : 2 ≤ k
    · simpa only [ctPauliVal, hk, ite_true] using setCClassPauli_CD k hk t
    · simpa only [ctPauliVal, hk, ite_false] using hCD k t (not_le.mp hk)
  | .inr (.inr k) => setCClassPauli_S k

end QED.ChainProof.SetCPauli

end
