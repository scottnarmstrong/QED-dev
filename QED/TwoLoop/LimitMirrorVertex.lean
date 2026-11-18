/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitMirrorLimit
public import QED.TwoLoop.LimitMirrorClasses
public import QED.TwoLoop.VertexLimit

/-!
# The mirror identity of the order-`e⁵` limit, reduced to its parts

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The `ε → 0⁺` limit `V` of
the order-`e⁵` vertex (HV₂) is `1/i` times the signed sum of the limits of the seven classes of
five gauge vertices and of the seven counterterm classes (`eq_smul_parts`):

`V = (1/i) (W_L + W_X + (W_{C₊} + W_{C₋}) + (W_{S₊} + W_{S₋}) - W_VP + Σ_ct W_ct)`.

The six open-line classes form the self-conjugate classes `L`, `X` and the charge-conjugate pairs
`C₊ ↔ C₋`, `S₊ ↔ S₋` (`QED/TwoLoop/LimitMirror.lean`, `QED/TwoLoop/LimitMirrorClasses.lean`), so
their part is mirror symmetric once each class limit is covariant under the reflection `R_K`
(`isMirrorSymmetric_openPart`). Hence (`isMirrorSymmetric_of_parts`) `V` is mirror symmetric
given

* the `R_K` covariance of the six open-line class limits (`IsReflCovariantAt`, between `(p', p)`
  and `(R_K p', R_K p) = (-p, -p')`);
* the mirror identity of the vacuum-polarization class limit `W_VP`;
* the mirror identity of the counterterm part `Σ_ct W_ct`.

## Main statements

* `isChargeConjPair_L`, `isChargeConjPair_X`, `isChargeConjPair_Sp_Sm`.
* `isMirrorSymmetric_openPart`: the open-line part is mirror symmetric.
* `eq_smul_parts`: the decomposition of `V`.
* `isMirrorSymmetric_of_parts`, `isMirrorSymmetric_headline_of_parts`: the reduction.
-/

@[expose] public section

open Matrix Complex Filter Topology

namespace QED.TwoLoop.LimitMirror

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.Dirac QED.OneLoop

theorem isChargeConjPair_L : IsChargeConjPair .L .L :=
  fun P _ _ _ hmom αOut βIn μ => contractionValue₂_cc_L P hmom αOut βIn μ

theorem isChargeConjPair_X : IsChargeConjPair .X .X :=
  fun P _ _ _ hmom αOut βIn μ => contractionValue₂_cc_X P hmom αOut βIn μ

theorem isChargeConjPair_Sp_Sm : IsChargeConjPair .Sp .Sm :=
  fun P _ _ _ hmom αOut βIn μ => contractionValue₂_cc_S P hmom αOut βIn μ

/-! ### Linearity of the mirror identity -/

theorem isMirrorSymmetric_smul {p' p : Fin 4 → ℝ} {W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (c : ℂ) (hW : IsMirrorSymmetric p' p W) : IsMirrorSymmetric p' p (c • W) := by
  intro μ
  have e : vecAct (reflectMatrix (p' + p)) (c • W) μ =
      c • vecAct (reflectMatrix (p' + p)) W μ := vecAct_smul _ c W μ
  set S := reflSpin (p' + p)
  set T := (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p))
  have e2 : S * (chargeConj * ((c • W) μ)ᵀ * chargeConj) * T =
      c • (S * (chargeConj * (W μ)ᵀ * chargeConj) * T) := by
    rw [Pi.smul_apply, Matrix.transpose_smul, Matrix.mul_smul chargeConj, Matrix.smul_mul,
      Matrix.mul_smul S, Matrix.smul_mul]
  rw [e2, hW μ, e, smul_neg]

theorem isMirrorSymmetric_neg {p' p : Fin 4 → ℝ} {W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hW : IsMirrorSymmetric p' p W) : IsMirrorSymmetric p' p (-W) := by
  have := isMirrorSymmetric_smul (-1) hW
  rwa [neg_one_smul] at this

theorem isMirrorSymmetric_sub {p' p : Fin 4 → ℝ} {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsMirrorSymmetric p' p V) (hW : IsMirrorSymmetric p' p W) :
    IsMirrorSymmetric p' p (V - W) := by
  rw [sub_eq_add_neg]
  exact isMirrorSymmetric_add hV (isMirrorSymmetric_neg hW)

/-! ### The open-line part -/

/-- The limits of the six open-line classes, grouped by charge conjugation. -/
noncomputable def openPart (P : Params) (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  classLimit .L P p' p + classLimit .X P p' p + (classLimit .Cp P p' p + classLimit .Cm P p' p) +
    (classLimit .Sp P p' p + classLimit .Sm P p' p)

/-- **The open-line part of the order-`e⁵` limit is mirror symmetric**, given the covariance of the
six class limits under the reflection `R_K`. For `m, m_γ, Λ > 0` and on-shell `p, p'` with
`q² > 0`. -/
theorem isMirrorSymmetric_openPart (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (hL : IsReflCovariantAt (classLimit .L P) p' p) (hX : IsReflCovariantAt (classLimit .X P) p' p)
    (hCp : IsReflCovariantAt (classLimit .Cp P) p' p)
    (hCm : IsReflCovariantAt (classLimit .Cm P) p' p)
    (hSp : IsReflCovariantAt (classLimit .Sp P) p' p)
    (hSm : IsReflCovariantAt (classLimit .Sm P) p' p) :
    IsMirrorSymmetric p' p (openPart P p' p) :=
  isMirrorSymmetric_add (isMirrorSymmetric_add (isMirrorSymmetric_add
    (isMirrorSymmetric_classLimit_self P hm hmγ hΛ hp' hp hq (by decide) isChargeConjPair_L hL)
    (isMirrorSymmetric_classLimit_self P hm hmγ hΛ hp' hp hq (by decide) isChargeConjPair_X hX))
    (isMirrorSymmetric_classLimit_Cp_add_Cm P hm hmγ hΛ hp' hp hq hCp hCm))
    (isMirrorSymmetric_classLimit_pair P hm hmγ hΛ hp' hp hq (by decide) (by decide)
      isChargeConjPair_Sp_Sm hSp hSm)

/-! ### The decomposition of the limit -/

/-- The value (T₁₀) of a counterterm class at `(p', p)`, prescription `ε`. -/
noncomputable def ctValue (c : CtClass) (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4)
    (ε : ℝ) : ℂ :=
  contractionValue₂ { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => a) (fun _ => b) (fun _ => μ)

/-- The `ε → 0⁺` limit of the value of a counterterm class, as a vertex. -/
noncomputable def ctLimit (c : CtClass) (P : Params) (p' p : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun a b => limUnder (𝓝[>] 0) (ctValue c P p' p μ a b)

/-- The counterterm part: the sum of the counterterm class limits. -/
noncomputable def ctPart (P : Params) (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ c : CtClass, ctLimit c P p' p

theorem sum_nonFurry (f : Class5 → ℂ) :
    ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * f c =
      f .L + f .X + (f .Cp + f .Cm) + (f .Sp + f .Sm) - f .VP := by
  simp only [Furry.nonFurry, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Class5.sign]
  push_cast
  ring

/-- **The decomposition of the order-`e⁵` limit**: under the hypotheses of
`QED.TwoLoop.VertexLimit.exists_tendsto_vertexOrderFive`, every limit `V` (HV₂) is
`(1/i) (openPart - W_VP + ctPart)`. -/
theorem eq_smul_parts (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsVertexOrderFiveLimit P p' p V) :
    V = (1 / I) • (openPart P p' p - classLimit .VP P p' p + ctPart P p' p) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcl : ∀ c, c ∈ Furry.nonFurry → HasClassLimit c P p' p := fun c hc μ a b =>
    VertexLimit.exists_tendsto_contractionValue₂_nonFurry hc P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
      (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
      (fun _ => a) (fun _ => b) (fun _ => μ)
  have hct : ∀ (c : CtClass) μ a b,
      Tendsto (ctValue c P p' p μ a b) (𝓝[>] 0) (𝓝 (ctLimit c P p' p μ a b)) :=
    fun c μ a b => by
      obtain ⟨L, hL⟩ := CountertermLimit.exists_tendsto_contractionValue₂_ctClass c P hm hmγ hΛ
        (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hp0 hp0'
        hq (fun _ => a) (fun _ => b) (fun _ => μ)
      exact tendsto_nhds_limUnder ⟨L, hL⟩
  have t : ∀ c, c ∈ Furry.nonFurry → ∀ μ a b,
      Tendsto (classValue c P p' p μ a b) (𝓝[>] 0) (𝓝 (classLimit c P p' p μ a b)) :=
    fun c hc => tendsto_classLimit (hcl c hc)
  funext μ
  ext a b
  have e : ∀ ε : ℝ, vertexOrderFive { P with ε := ε } p' p μ a b = (1 / I) *
      (classValue .L P p' p μ a b ε + classValue .X P p' p μ a b ε +
          (classValue .Cp P p' p μ a b ε + classValue .Cm P p' p μ a b ε) +
          (classValue .Sp P p' p μ a b ε + classValue .Sm P p' p μ a b ε) -
          classValue .VP P p' p μ a b ε + ∑ c : CtClass, ctValue c P p' p μ a b ε) := fun ε => by
    rw [← sum_nonFurry (fun c => classValue c P p' p μ a b ε)]
    simp only [classValue, ctValue]
    rw [← onePIFunction₂_five_sub_four_eq_classes { P with ε := ε } hmom (fun _ => a)
      (fun _ => b) (fun _ => μ)]
    rfl
  have hlim : Tendsto (fun ε => vertexOrderFive { P with ε := ε } p' p μ a b) (𝓝[>] 0)
      (𝓝 ((1 / I) * (classLimit .L P p' p μ a b + classLimit .X P p' p μ a b +
        (classLimit .Cp P p' p μ a b + classLimit .Cm P p' p μ a b) +
        (classLimit .Sp P p' p μ a b + classLimit .Sm P p' p μ a b) -
        classLimit .VP P p' p μ a b + ∑ c : CtClass, ctLimit c P p' p μ a b))) := by
    simp only [e]
    refine Tendsto.const_mul _ (Tendsto.add (Tendsto.sub (Tendsto.add (Tendsto.add
      (Tendsto.add (t _ (by decide) μ a b) (t _ (by decide) μ a b))
      (Tendsto.add (t _ (by decide) μ a b) (t _ (by decide) μ a b)))
      (Tendsto.add (t _ (by decide) μ a b) (t _ (by decide) μ a b)))
      (t _ (by decide) μ a b)) (tendsto_finsetSum _ fun c _ => hct c μ a b))
  rw [tendsto_nhds_unique (hV μ a b) hlim]
  simp [openPart, ctPart, Matrix.sum_apply, Finset.sum_apply]

/-! ### The reduction -/

/-- **The mirror identity of the order-`e⁵` limit, reduced to its parts.** Under the hypotheses
of `QED.TwoLoop.VertexLimit.exists_tendsto_vertexOrderFive` and `q² > 0`, a limit `V` (HV₂) is
mirror symmetric if the six open-line class limits are covariant under the reflection `R_K`, the
vacuum-polarization class limit is mirror symmetric, and the counterterm part is mirror
symmetric. -/
theorem isMirrorSymmetric_of_parts (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsVertexOrderFiveLimit P p' p V)
    (hL : IsReflCovariantAt (classLimit .L P) p' p) (hX : IsReflCovariantAt (classLimit .X P) p' p)
    (hCp : IsReflCovariantAt (classLimit .Cp P) p' p)
    (hCm : IsReflCovariantAt (classLimit .Cm P) p' p)
    (hSp : IsReflCovariantAt (classLimit .Sp P) p' p)
    (hSm : IsReflCovariantAt (classLimit .Sm P) p' p)
    (hVP : IsMirrorSymmetric p' p (classLimit .VP P p' p))
    (hct : IsMirrorSymmetric p' p (ctPart P p' p)) :
    IsMirrorSymmetric p' p V := by
  rw [eq_smul_parts P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hq.le hV]
  exact isMirrorSymmetric_smul _ (isMirrorSymmetric_add (isMirrorSymmetric_sub
    (isMirrorSymmetric_openPart P hm hmγ hΛ hp' hp hq hL hX hCp hCm hSp hSm) hVP) hct)

/-- **The reduction in the shape of the headline** (HV₃): for the parameters
`{P₀ with M₁, M₂, c₁, c₂, m_γ, Λ, δ₁ := d₁, δ₂ := d₂, δ_m := dm, δ₃ := d₃}` of
`QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline`, an on-shell positive-energy pair
with `q² > 0`, and the limit `V`, the mirror identity of `V` follows from the `R_K` covariance of
the six open-line class limits and the mirror identities of the vacuum-polarization and
counterterm parts. -/
theorem isMirrorSymmetric_headline_of_parts (P₀ : Params) (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ)
    (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V)
    (hcov : ∀ c ∈ ClassIntegrable.openClasses, IsReflCovariantAt (classLimit c
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ }) p' p)
    (hVP : IsMirrorSymmetric p' p (classLimit .VP
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p))
    (hct : IsMirrorSymmetric p' p (ctPart
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p)) :
    IsMirrorSymmetric p' p V :=
  isMirrorSymmetric_of_parts
    { P₀ with
      M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
      δm := dm, δ₃ := d₃ } hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂ hp hp' hp0 hp0' hq hV
    (hcov _ (by decide)) (hcov _ (by decide)) (hcov _ (by decide)) (hcov _ (by decide))
    (hcov _ (by decide)) (hcov _ (by decide)) hVP hct

end QED.TwoLoop.LimitMirror

end
