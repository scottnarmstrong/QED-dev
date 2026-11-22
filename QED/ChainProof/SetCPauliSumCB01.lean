/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliSumReal
public import QED.ChainProof.SetCLimCtCB01Link

/-!
# Set (c): the limits of `CB0`, `CB1` are `♯`-odd

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, the last
counterterm case of the reality requirement `QED.ChainProof.SetCPauli.SetCClassSharp`
(`QED/ChainProof/SetCPauliSumReal.lean` covers the other 18 counterterm classes).

The limit of `CB0`, `CB1` is `∑ⱼ vAⱼ + c ∑ⱼ vBⱼ` with parametric values `vA`, `vB` of the
pieces of the numerator pairs `(cbEa0, cbEa2)`, `(cbEv0, cbEv2)` and the real constant
`c = mergeC` (`QED.ChainProof.SetCPauli.CB01.cb_char`). As for `VP`
(`QED.GradedProof.V5Zero.Sharp.sharp_vpE0M`):

* `sharp_cbNumM`, `sharp_cbNum2M`: the bubble-vertex numerators with `♯`-fixed open-line
  matrices are `(ie)⁵ (1/i)⁶ = -i e⁵` times `♯`-fixed chains, so `N♯ = -N`;
* `sharp_cbEa0M`, …, `sharp_cbEv2M`: the four numerator matrices are `♯`-odd (the open-line
  matrices `A`, `Y` are `♯`-fixed);
* `sharp_cbPieceM`: so are the pieces (real coefficients `vpCoeff0`, `vpCoeff2`);
* `sharp_of_cbChar`: so is a limit of the form of `cb_char`;
* **`setCClassSharp_CB01`**: the requirement for `CB0`, `CB1`; **`setCClassSharp_ct_all`**: for
  all 20 counterterm classes;
* **`setCPauliB_hsum_of_mainSharp`**: the input `hsum` from main-class inputs alone.
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCPauli

open QED.ChainProof.SetCPauli.CB01
open QED.TwoLoop.LimitCovariance (IsParamValue vpData vpCoeff0 vpCoeff2)
open QED.TwoLoop.Bridge (electronNumerator)
open QED.GradedProof.SE2Real (sharp sharp_add sharp_neg sharp_smul sharp_sum)
open QED.GradedProof.V5Zero.Sharp (sharp_chain conj_lowered conj_traceT conj_vpCoeff
  sharp_electronNumerator conj_vpCoeff0 conj_vpCoeff2 sharp_eq_smul_of_isParamValue_vertex)

/-! ### The numerators -/

theorem sharp_cbNumM (P : Params) (M : ℝ) {X1 X0 : Matrix (Fin 4) (Fin 4) ℂ}
    (h1 : sharp X1 = X1) (h0 : sharp X0 = X0) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (cbNumM P M X1 X0 μ ℓ) = -cbNumM P M X1 X0 μ ℓ := by
  rw [cbNumM_eq, sharp_smul, conj_vpCoeff, sharp_chain (conj_lowered P
    (conj_traceT (sharp_electronNumerator _ _) (sharp_electronNumerator _ _))) h1 h0, neg_smul]

theorem sharp_cbNum2M (P : Params) {X1 X0 : Matrix (Fin 4) (Fin 4) ℂ}
    (h1 : sharp X1 = X1) (h0 : sharp X0 = X0) (μ : Fin 4) :
    sharp (cbNum2M P X1 X0 μ) = -cbNum2M P X1 X0 μ := by
  rw [cbNum2M_eq, sharp_smul, conj_vpCoeff, sharp_chain (conj_lowered P
    (conj_traceT QED.GradedProof.SE2Real.sharp_one QED.GradedProof.SE2Real.sharp_one)) h1 h0,
    neg_smul]

theorem sharp_cbXa (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 2) : sharp (cbXa P d p' p ℓ i) = cbXa P d p' p ℓ i := by
  unfold cbXa
  split_ifs
  · exact sharp_mergeY _ _ _ _
  · exact sharp_electronNumerator _ _

section Num

variable (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ)

theorem sharp_cbEa0M :
    sharp (Matrix.of fun α β => cbEa0 P d p' p α β μ ℓ) =
      -Matrix.of fun α β => cbEa0 P d p' p α β μ ℓ :=
  sharp_cbNumM P 0 (sharp_cbXa P d p' p ℓ 1) (sharp_cbXa P d p' p ℓ 0) μ ℓ

theorem sharp_cbEa2M :
    sharp (Matrix.of fun α β => cbEa2 P d p' p α β μ ℓ) =
      -Matrix.of fun α β => cbEa2 P d p' p α β μ ℓ :=
  sharp_cbNum2M P (sharp_cbXa P d p' p ℓ 1) (sharp_cbXa P d p' p ℓ 0) μ

theorem sharp_cbEv0M :
    sharp (Matrix.of fun α β => cbEv0 P p' p α β μ ℓ) =
      -Matrix.of fun α β => cbEv0 P p' p α β μ ℓ :=
  sharp_cbNumM P 0 (sharp_electronNumerator _ _) (sharp_electronNumerator _ _) μ ℓ

theorem sharp_cbEv2M :
    sharp (Matrix.of fun α β => cbEv2 P p' p α β μ ℓ) =
      -Matrix.of fun α β => cbEv2 P p' p α β μ ℓ :=
  sharp_cbNum2M P (sharp_electronNumerator _ _) (sharp_electronNumerator _ _) μ

/-- **The pieces of a `♯`-odd numerator pair are `♯`-odd.** -/
theorem sharp_cbPieceM {E0 E2 : Fin 4 → Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h0 : sharp (Matrix.of fun α β => E0 α β ℓ) = -Matrix.of fun α β => E0 α β ℓ)
    (h2 : sharp (Matrix.of fun α β => E2 α β ℓ) = -Matrix.of fun α β => E2 α β ℓ) (j : Fin 5) :
    sharp (Matrix.of fun α β => cbPiece P p p' (E0 α β) (E2 α β) j ℓ) =
      (-1 : ℂ) • Matrix.of fun α β => cbPiece P p p' (E0 α β) (E2 α β) j ℓ := by
  have e : (Matrix.of fun α β => cbPiece P p p' (E0 α β) (E2 α β) j ℓ) =
      vpCoeff0 P j • Matrix.of (fun α β => E0 α β ℓ) +
        vpCoeff2 P p p' j ℓ • Matrix.of (fun α β => E2 α β ℓ) := by
    ext α β
    simp only [cbPiece_eq, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [e, sharp_add, sharp_smul, sharp_smul, conj_vpCoeff0, conj_vpCoeff2, h0, h2, neg_one_smul,
    neg_add, smul_neg, smul_neg]

end Num

/-! ### The limit -/

/-- **A limit of the form of `cb_char` is `♯`-odd.** -/
theorem sharp_of_cbChar (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (vA vB : Fin 4 → Fin 4 → Fin 4 → Fin 5 → ℂ)
    (hvA : ∀ μ i j k, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq k)
      (cbPiece P p p' (cbEa0 P d p' p i j μ) (cbEa2 P d p' p i j μ) k) (vA μ i j k))
    (hvB : ∀ μ i j k, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d k)
      (cbPiece P p p' (cbEv0 P p' p i j μ) (cbEv2 P p' p i j μ) k) (vB μ i j k))
    (hY : ∀ μ i j, Y μ i j = ∑ k, vA μ i j k + mergeC P.m P.δ₂ P.δm * ∑ k, vB μ i j k)
    (μ : Fin 4) : sharp (Y μ) = -Y μ := by
  have hA : ∀ k, sharp (Matrix.of fun i j => vA μ i j k) = (-1 : ℂ) • Matrix.of fun i j =>
      vA μ i j k := fun k =>
    sharp_eq_smul_of_isParamValue_vertex (D := vpData P hmγ hΛ hm h₁ h₂ hp hp' hq k)
      (fun μ ℓ => Matrix.of fun i j => cbPiece P p p' (cbEa0 P d p' p i j μ)
        (cbEa2 P d p' p i j μ) k ℓ) (fun μ => Matrix.of fun i j => vA μ i j k) (-1)
      (fun μ ℓ => sharp_cbPieceM P p' p ℓ (sharp_cbEa0M P d p' p μ ℓ)
        (sharp_cbEa2M P d p' p μ ℓ) k) (fun μ i j => hvA μ i j k) μ
  have hB : ∀ k, sharp (Matrix.of fun i j => vB μ i j k) = (-1 : ℂ) • Matrix.of fun i j =>
      vB μ i j k := fun k =>
    sharp_eq_smul_of_isParamValue_vertex (D := cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d k)
      (fun μ ℓ => Matrix.of fun i j => cbPiece P p p' (cbEv0 P p' p i j μ)
        (cbEv2 P p' p i j μ) k ℓ) (fun μ => Matrix.of fun i j => vB μ i j k) (-1)
      (fun μ ℓ => sharp_cbPieceM P p' p ℓ (sharp_cbEv0M P p' p μ ℓ)
        (sharp_cbEv2M P p' p μ ℓ) k) (fun μ i j => hvB μ i j k) μ
  have e : Y μ = ∑ k, (Matrix.of fun i j => vA μ i j k) +
      mergeC P.m P.δ₂ P.δm • ∑ k, (Matrix.of fun i j => vB μ i j k) := by
    ext i j
    simp only [hY, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
      smul_eq_mul]
  rw [e, sharp_add, sharp_sum, sharp_smul, sharp_sum, conj_mergeC]
  simp only [hA, hB, neg_one_smul, Finset.sum_neg_distrib, smul_neg, neg_add]

/-! ### `CB0`, `CB1` and all counterterm classes -/

variable {P₀ : Params}

/-- **`♯`-odd limits of `CB0`, `CB1`.** -/
theorem setCClassSharp_CB01 (k : Fin 5) (hk : k < 2) : SetCClassSharp ctFam P₀ (.inl k) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  have hA' := hA
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA'
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  set Pc := cbParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s 0
  have h₁ : Pc.m ^ 2 ≤ Pc.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁.le 2
  have h₂ : Pc.m ^ 2 ≤ Pc.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂.le 2
  choose vA vB hvA hvB hYe using fun μ i j => cb_char Pc hmγ hΛ hm h₁ h₂ hp hp' hq.le _ _
    (fun μ i j ε hε => ctFam_cb01_eq hA k hk p' p μ i j ε hε) hY μ i j
  exact sharp_of_cbChar Pc hmγ hΛ hm h₁ h₂ hp hp' hq.le _ vA vB hvA hvB hYe μ

/-- **`♯`-odd limits of all 20 counterterm classes.** -/
theorem setCClassSharp_ct_all (r : CtIdx) : SetCClassSharp ctFam P₀ r := by
  by_cases hr : ∃ k : Fin 5, k < 2 ∧ r = .inl k
  · obtain ⟨k, hk, rfl⟩ := hr
    exact setCClassSharp_CB01 k hk
  · exact setCClassSharp_ct r fun k hk e => hr ⟨k, hk, e⟩

/-- **The input `hsum` from main-class inputs alone**: canonical main values `βᴹ` that are the
per-class Pauli limits of main classes with limit links and `♯`-odd limits. -/
theorem setCPauliB_hsum_of_mainSharp (he : P₀.e ≠ 0) {βM : MainIdx → ClsPauliVal}
    (hcan : ∀ r, ClsCanon P₀ (βM r)) (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r)) (hSM : ∀ r, SetCClassSharp mainFam P₀ r) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s +
        ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s) = ((setCPauliB P₀ βM mγ Λ M₁ M₂ : ℝ) : ℂ) :=
  setCPauliB_hsum_of_sharp he hcan hM hPM hSM fun k hk => setCClassSharp_CB01 k hk

end QED.ChainProof.SetCPauli

end
