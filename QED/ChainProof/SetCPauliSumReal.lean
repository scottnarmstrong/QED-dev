/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliSum
public import QED.GradedProof.V5ZeroSharpCt
public import QED.GradedProof.V5ZeroSharpVP

/-!
# Set (c): the per-class Pauli values are imaginary

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, the reality half
of the input `hsum` of `QED.ChainProof.SetCPauli.isFormFactorPair_vertexSetC_pauli_limit_of_mainB`
(`QED.ChainProof.SetCPauli.setCPauliB_hsum` needs `Re (∑ βᴹ + ∑ ctPauliAll) = 0`).

The set (a) precedent (`QED.ChainProof.SetANestedAt.pol_im_eq_zero`) reads the phase of each
class limit off its parametric form (`QED.GradedProof.VP2Real.HasConjLim`). Here the same is done
with the antilinear automorphism `♯` of `QED.GradedProof.SE2Real.sharp` (`γ^μ♯ = γ^μ`), as for the
order-`e⁵` vertex (`QED.GradedProof.V5Zero.Sharp`):

* `conj_formFactorProj₂_of_sharp`: if `Y^μ♯ = -Y^μ` for every `μ`, the Pauli projection of `Y`
  at real momenta is imaginary (the trace projectors are built from `♯`-fixed factors with real
  coefficients, and `tr X♯ = conj (tr X)`);
* `SetCClassSharp V P₀ r` (the per-class reality requirement): the class limits at the admissible
  data and the on-shell pairs are `♯`-odd;
* **`re_eq_zero_of_classSharp`**: a class with a limit link, a canonical Pauli value `β` and
  `♯`-odd limits has `Re β = 0` (`β` is a limit of imaginary numbers);
* **`setCClassSharp_ct`**: the requirement holds for the counterterm classes `Sₖ`, `CDₖ t`
  (`k < 2` through the parametric form of the pieces, `QED.ChainProof.SetCPauli.pieceLim_entry`;
  `2 ≤ k` by `QED.GradedProof.V5Zero.Sharp.sharp_ctLimitV`) and `CBₖ`, `2 ≤ k`
  (`QED.GradedProof.V5Zero.Sharp.sharp_classLimitV_VP`); `CB0`, `CB1` remain a requirement;
* **`ctPauliAll_re_eq_zero`**: hence `Re ctPauliAll P₀ r = 0` for these 18 classes.
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCPauli

open QED.Dirac QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.LimitCovariance (IsParamValue ParamData)
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.GradedProof.SE2Real (sharp sharp_add sharp_sub sharp_neg sharp_smul sharp_mul sharp_one
  sharp_sum sharp_gamma sharp_slash trace_sharp)

/-! ### The Pauli projection of a `♯`-odd vertex is imaginary -/

theorem sharp_mass_sub_slash (m : ℝ) (p : Fin 4 → ℝ) :
    sharp ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash p) =
      (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash p := by
  rw [sharp_sub, sharp_smul, sharp_one, sharp_slash, Complex.conj_ofReal]

theorem sharp_gammaLower (μ : Fin 4) : sharp (gammaLower μ) = gammaLower μ := by
  simp only [gammaLower, sharp_sum, sharp_smul, sharp_gamma, Complex.conj_ofReal]

section Proj

variable {m : ℝ} {p' p : Fin 4 → ℝ} {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

theorem conj_traceGammaProj (hY : ∀ μ, sharp (Y μ) = -Y μ) :
    starRingEnd ℂ (traceGammaProj m p' p Y) = -traceGammaProj m p' p Y := by
  simp only [traceGammaProj, map_sum, ← trace_sharp, sharp_mul, sharp_mass_sub_slash,
    sharp_gammaLower, hY, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg,
    Finset.sum_neg_distrib]

theorem conj_traceVecProj (a : Fin 4 → ℝ) (hY : ∀ μ, sharp (Y μ) = -Y μ) :
    starRingEnd ℂ (traceVecProj m p' p a Y) = -traceVecProj m p' p a Y := by
  simp only [traceVecProj, map_sum, map_mul, Complex.conj_ofReal, ← trace_sharp, sharp_mul,
    sharp_mass_sub_slash, hY, Matrix.neg_mul, Matrix.trace_neg, mul_neg,
    Finset.sum_neg_distrib]

/-- **The Pauli projection of a `♯`-odd vertex is imaginary.** -/
theorem conj_formFactorProj₂_of_sharp (e : ℝ) (hY : ∀ μ, sharp (Y μ) = -Y μ) :
    starRingEnd ℂ (QED.OneLoop.formFactorProj₂ e m p' p Y) =
      -QED.OneLoop.formFactorProj₂ e m p' p Y := by
  rw [formFactorProj₂_eq_pauliNum]
  simp only [pauliNum, map_div₀, map_mul, map_add, map_sub, map_pow, map_ofNat,
    Complex.conj_ofReal, conj_traceGammaProj hY, conj_traceVecProj _ hY]
  ring

theorem re_eq_zero_of_conj_eq_neg {z : ℂ} (h : starRingEnd ℂ z = -z) : z.re = 0 := by
  have := congrArg Complex.re h
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith

theorem re_formFactorProj₂_of_sharp (e : ℝ) (hY : ∀ μ, sharp (Y μ) = -Y μ) :
    (QED.OneLoop.formFactorProj₂ e m p' p Y).re = 0 :=
  re_eq_zero_of_conj_eq_neg (conj_formFactorProj₂_of_sharp e hY)

end Proj

/-! ### The per-class reality requirement -/

variable {P₀ : Params}

/-- **The class limits are `♯`-odd** (the per-class reality requirement): at the admissible data
and every on-shell positive-energy pair with `q² > 0`, every limit `Y` of the class satisfies
`Y^μ♯ = -Y^μ`. -/
def SetCClassSharp {ι : Type} (V : ClsFam ι) (P₀ : Params) (r : ι) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ Y, IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y →
      ∀ μ, sharp (Y μ) = -Y μ

/-- **A class with `♯`-odd limits has an imaginary canonical Pauli value.** -/
theorem re_eq_zero_of_classSharp {ι : Type} {V : ClsFam ι} {r : ι} {β : ClsPauliVal}
    (hL : SetCClassLim V P₀ r) (hP : SetCClassPauli V P₀ r β) (hS : SetCClassSharp V P₀ r) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (β M₁ M₂ c₁ c₂ mγ Λ D s).re = 0 := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA
  have hm : 0 < P₀.m := by obtain ⟨-, -, -, -, hmγ, -, -, hm2, -⟩ := hA; linarith
  by_contra hne
  have hη : 0 < |(β M₁ M₂ c₁ c₂ mγ Λ D s).re| := abs_pos.mpr hne
  obtain ⟨Q, hQ, hQ0⟩ := ((hP M₁ M₂ c₁ c₂ mγ Λ D s hA _ hη).and self_mem_nhdsWithin).exists
  have hpq := QED.ChainProof.HCValue.isPairQ_canonical' hm hQ0
  obtain ⟨Y, hY⟩ := hL M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hpq
  have h1 := hQ Y hY
  have h2 := re_formFactorProj₂_of_sharp (m := P₀.m) (p' := boostMomentum P₀.m Q)
    (p := restMomentum P₀.m) P₀.e (hS M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hpq Y hY)
  have h3 : |(β M₁ M₂ c₁ c₂ mγ Λ D s).re| ≤
      ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m) Y -
        β M₁ M₂ c₁ c₂ mγ Λ D s‖ := by
    calc |(β M₁ M₂ c₁ c₂ mγ Λ D s).re|
        = |(QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m) Y -
            β M₁ M₂ c₁ c₂ mγ Λ D s).re| := by rw [Complex.sub_re, h2, zero_sub, abs_neg]
      _ ≤ _ := Complex.abs_re_le_norm _
  linarith

/-- Class limits are unique. -/
theorem isClassLimC_unique {ι : Type} {V : ClsFam ι} {r : ι} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    {s : ℝ × ℝ × ℝ} {p' p : Fin 4 → ℝ} {Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y)
    (hZ : IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Z) : Y = Z := by
  funext μ
  ext i j
  exact tendsto_nhds_unique (hY μ i j) (hZ μ i j)

/-! ### The counterterm classes -/

/-- **`♯`-odd limits of `Sₖ`.** -/
theorem setCClassSharp_S (k : Fin 5) : SetCClassSharp ctFam P₀ (.inr (.inr k)) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  rw [isClassLimC_unique hY (isClassLimC_S hA k hpq)]
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  rw [← sParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  exact QED.GradedProof.V5Zero.Sharp.sharp_ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s)
    hm hmγ hΛ hp hp' hp0 hp0' hq.le μ

/-- **`♯`-odd limits of `CDₖ t`, `2 ≤ k`.** -/
theorem setCClassSharp_CD (k : Fin 5) (hk : 2 ≤ k) (t : Fin 2) :
    SetCClassSharp ctFam P₀ (.inr (.inl (k, t))) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  rw [isClassLimC_unique hY (isClassLimC_CD hA k hk t hpq)]
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  rw [← cdParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  simp only [cdLim, Pi.smul_apply]
  rw [sharp_smul, Complex.conj_ofReal, QED.GradedProof.V5Zero.Sharp.sharp_ctLimitV (d3Cls t)
    (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm hmγ hΛ hp hp' hp0 hp0' hq.le μ, smul_neg]

/-- **`♯`-odd limits of `CBₖ`, `2 ≤ k`.** -/
theorem setCClassSharp_CB (k : Fin 5) (hk : 2 ≤ k) : SetCClassSharp ctFam P₀ (.inl k) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  rw [isClassLimC_unique hY (isClassLimC_CB hA k hk hpq)]
  obtain ⟨hM₁, hM₂, hc₁, hc₂, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  simp only [cbLim, Pi.smul_apply]
  rw [sharp_smul, QED.GradedProof.V5Zero.Sharp.sharp_classLimitV_VP
    (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm le_rfl hmγ hΛ hM₁.le hM₂.le hc₁ hc₂ hp hp' hq.le μ,
    smul_neg]
  simp only [cbW, map_neg, Complex.conj_ofReal]

/-! ### `CD0`, `CD1` -/

section CD01

open QED.TwoLoop.CountertermLimit QED.TwoLoop.ReflCovariance
open QED.GradedProof.V5Zero.Sharp (sharp_ctLimitV_of_entry sharp_vertexChain
  sharp_electronNumerator conj_photonNum)

theorem sharp_pieceLim_of {M : ℝ} (hM : 0 < M) {D : ParamData} {d : ℝ → (Fin 4 → ℝ) → ℂ}
    {N : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hN : ∀ μ k, sharp (N μ k) = N μ k)
    (hV : ∀ μ i j, ∃ v, IsParamValue D (fun ℓ => N μ (ℓ 0) i j) v ∧
      pieceLim d N μ i j = v / auxLimit M) (μ : Fin 4) :
    sharp (pieceLim d N μ) = -pieceLim d N μ :=
  sharp_ctLimitV_of_entry hM D N hN _ hV μ

theorem conj_mergeC (m δ₂ δm : ℝ) : starRingEnd ℂ (mergeC m δ₂ δm) = mergeC m δ₂ δm := by
  simp only [mergeC, map_mul, map_sub, map_ofNat, Complex.conj_ofReal]

theorem sharp_mergeY (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    sharp (mergeY m δ₂ δm k) = mergeY m δ₂ δm k := by
  simp only [mergeY, sharp_add, sharp_smul, sharp_electronNumerator, sharp_one, map_sub, map_mul,
    Complex.conj_ofReal]

variable (Q : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ)

theorem sharp_numIn₁ : sharp (numIn₁ Q p' p μ k) = numIn₁ Q p' p μ k :=
  sharp_vertexChain _ _ (conj_photonNum _ _ _ _) (sharp_electronNumerator _ _)
    (by rw [sharp_neg, sharp_mergeY])

theorem sharp_numIn₂ : sharp (numIn₂ Q p' p μ k) = numIn₂ Q p' p μ k :=
  sharp_vertexChain _ _ (conj_photonNum _ _ _ _) (sharp_electronNumerator _ _)
    (by rw [sharp_neg, sharp_smul, conj_mergeC, sharp_electronNumerator])

theorem sharp_numOut₁ : sharp (numOut₁ Q p' p μ k) = numOut₁ Q p' p μ k :=
  sharp_vertexChain _ _ (conj_photonNum _ _ _ _) (by rw [sharp_neg, sharp_mergeY])
    (sharp_electronNumerator _ _)

theorem sharp_numOut₂ : sharp (numOut₂ Q p' p μ k) = numOut₂ Q p' p μ k :=
  sharp_vertexChain _ _ (conj_photonNum _ _ _ _)
    (by rw [sharp_neg, sharp_smul, conj_mergeC, sharp_electronNumerator])
    (sharp_electronNumerator _ _)

variable {Q p' p} (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
  (hp : Minkowski.dot p p = -Q.m ^ 2) (hp' : Minkowski.dot p' p' = -Q.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp hp' hq

theorem sharp_cdInLim : sharp (cdInLim Q p' p μ) = -cdInLim Q p' p μ := by
  have h₁ := sharp_pieceLim_of hm (fun μ k => sharp_numIn₁ Q p' p μ k) (fun μ i j =>
    (pieceLim_entry (by norm_num) kindsD3 (massesD3 Q) hm (lt_min hmγ hΛ)
      (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) hp hp' hq (den₁ Q p' p)
      (numIn₁ Q p' p) (fun μ i j => (affMat_numIn₁ Q p' p μ i j).isLoopPoly)
      (fun ε _ ℓ => den₁_fac Q p p' ε ℓ) μ i j).imp fun _ h => ⟨h.1, h.2.2⟩) μ
  have h₂ := sharp_pieceLim_of hm (fun μ k => sharp_numIn₂ Q p' p μ k) (fun μ i j =>
    (pieceLim_entry (by norm_num) kindsIn₂ (massesD₂ Q) hm (lt_min hmγ hΛ)
      (massesD₂_sq_of_ne_pho_in Q) (min_sq_le_massesD₂_sq_in Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsIn₂ (by decide) (by decide) hp hp' hq (denIn₂ Q p' p)
      (numIn₂ Q p' p) (fun μ i j => (affMat_numIn₂ Q p' p μ i j).isLoopPoly)
      (fun ε _ ℓ => denIn₂_fac Q p p' ε ℓ) μ i j).imp fun _ h => ⟨h.1, h.2.2⟩) μ
  simp only [cdInLim, Pi.add_apply]
  rw [sharp_add, h₁, h₂, neg_add]

theorem sharp_cdOutLim : sharp (cdOutLim Q p' p μ) = -cdOutLim Q p' p μ := by
  have h₁ := sharp_pieceLim_of hm (fun μ k => sharp_numOut₁ Q p' p μ k) (fun μ i j =>
    (pieceLim_entry (by norm_num) kindsD3 (massesD3 Q) hm (lt_min hmγ hΛ)
      (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) hp hp' hq (den₁ Q p' p)
      (numOut₁ Q p' p) (fun μ i j => (affMat_numOut₁ Q p' p μ i j).isLoopPoly)
      (fun ε _ ℓ => den₁_fac Q p p' ε ℓ) μ i j).imp fun _ h => ⟨h.1, h.2.2⟩) μ
  have h₂ := sharp_pieceLim_of hm (fun μ k => sharp_numOut₂ Q p' p μ k) (fun μ i j =>
    (pieceLim_entry (by norm_num) kindsOut₂ (massesD₂ Q) hm (lt_min hmγ hΛ)
      (massesD₂_sq_of_ne_pho_out Q) (min_sq_le_massesD₂_sq_out Q hmγ hΛ)
      intNoSubdivergenceRefined_kindsOut₂ (by decide) (by decide) hp hp' hq (denOut₂ Q p' p)
      (numOut₂ Q p' p) (fun μ i j => (affMat_numOut₂ Q p' p μ i j).isLoopPoly)
      (fun ε _ ℓ => denOut₂_fac Q p p' ε ℓ) μ i j).imp fun _ h => ⟨h.1, h.2.2⟩) μ
  simp only [cdOutLim, Pi.add_apply]
  rw [sharp_add, h₁, h₂, neg_add]

end CD01

/-- **`♯`-odd limits of `CDₖ t`, `k < 2`.** -/
theorem setCClassSharp_CD01 (k : Fin 5) (hk : k < 2) (t : Fin 2) :
    SetCClassSharp ctFam P₀ (.inr (.inl (k, t))) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq Y hY μ
  rw [isClassLimC_unique hY (isClassLimC_CD01 hA k hk t hpq)]
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  rw [← cdParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  unfold cd01Lim
  split_ifs
  · exact sharp_cdOutLim μ hm hmγ hΛ hp hp' hq.le
  · exact sharp_cdInLim μ hm hmγ hΛ hp hp' hq.le

/-- **`♯`-odd limits of the counterterm classes other than `CB0`, `CB1`.** -/
theorem setCClassSharp_ct (r : CtIdx) (hr : ∀ k : Fin 5, k < 2 → r ≠ .inl k) :
    SetCClassSharp ctFam P₀ r := by
  rcases r with k | ⟨k, t⟩ | k
  · by_cases hk : 2 ≤ k
    · exact setCClassSharp_CB k hk
    · exact absurd rfl (hr k (not_le.mp hk))
  · by_cases hk : 2 ≤ k
    · exact setCClassSharp_CD k hk t
    · exact setCClassSharp_CD01 k (not_le.mp hk) t
  · exact setCClassSharp_S k

/-- **The counterterm Pauli values other than those of `CB0`, `CB1` are imaginary.** -/
theorem ctPauliAll_re_eq_zero (r : CtIdx) (hr : ∀ k : Fin 5, k < 2 → r ≠ .inl k) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s).re = 0 :=
  re_eq_zero_of_classSharp
    (setCClassLim_ct (setCClassLim_CB_all fun k hk => setCClassLim_CB01 k hk)
      (setCClassLim_CD_all fun k t hk => setCClassLim_CD01 k hk t) r)
    (setCClassPauli_ct_all P₀ r) (setCClassSharp_ct r hr)

/-! ### `hsum` -/

/-- **The counterterm sum is imaginary** if the values of `CB0`, `CB1` are. -/
theorem sum_ctPauliAll_re_eq_zero
    (hCB : ∀ k : Fin 5, k < 2 → ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s).re = 0)
    {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ} (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    (∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s).re = 0 := by
  rw [Complex.re_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : ∃ k : Fin 5, k < 2 ∧ r = .inl k
  · obtain ⟨k, hk, rfl⟩ := hr
    exact hCB k hk M₁ M₂ c₁ c₂ mγ Λ D s hA
  · exact ctPauliAll_re_eq_zero r (fun k hk e => hr ⟨k, hk, e⟩) M₁ M₂ c₁ c₂ mγ Λ D s hA

/-- **The input `hsum` from the per-class requirements**: for main values `βᴹ` that are canonical
(`ClsCanon`, e.g. `ClsLow`) and imaginary, and imaginary values of `CB0`, `CB1`,
`(1/i)(∑ βᴹ + ∑ ctPauliAll) = setCPauliB P₀ βᴹ` at every admissible datum. -/
theorem setCPauliB_hsum_of_re (he : P₀.e ≠ 0) {βM : MainIdx → ClsPauliVal}
    (hcan : ∀ r, ClsCanon P₀ (βM r))
    (hMre : ∀ r M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (βM r M₁ M₂ c₁ c₂ mγ Λ D s).re = 0)
    (hCB : ∀ k : Fin 5, k < 2 → ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s).re = 0) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s +
        ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s) = ((setCPauliB P₀ βM mγ Λ M₁ M₂ : ℝ) : ℂ) :=
  setCPauliB_hsum he hcan fun M₁ M₂ c₁ c₂ mγ Λ D s hA => by
    rw [Complex.add_re, sum_ctPauliAll_re_eq_zero hCB hA, Complex.re_sum,
      Finset.sum_eq_zero fun r _ => hMre r M₁ M₂ c₁ c₂ mγ Λ D s hA, add_zero]

/-- **The input `hsum` from `♯`-odd class limits**: canonical main values `βᴹ` that are the
per-class Pauli limits of main classes with limit links and `♯`-odd limits, and `♯`-odd limits
of `CB0`, `CB1`. -/
theorem setCPauliB_hsum_of_sharp (he : P₀.e ≠ 0) {βM : MainIdx → ClsPauliVal}
    (hcan : ∀ r, ClsCanon P₀ (βM r)) (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r)) (hSM : ∀ r, SetCClassSharp mainFam P₀ r)
    (hSCB : ∀ k : Fin 5, k < 2 → SetCClassSharp ctFam P₀ (.inl k)) :
    ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s +
        ∑ r, ctPauliAll P₀ r M₁ M₂ c₁ c₂ mγ Λ D s) = ((setCPauliB P₀ βM mγ Λ M₁ M₂ : ℝ) : ℂ) :=
  setCPauliB_hsum_of_re he hcan (fun r => re_eq_zero_of_classSharp (hM r) (hPM r) (hSM r))
    fun k hk => re_eq_zero_of_classSharp
      (setCClassLim_ct (setCClassLim_CB_all fun k hk => setCClassLim_CB01 k hk)
        (setCClassLim_CD_all fun k t hk => setCClassLim_CD01 k hk t) (.inl k))
      (setCClassPauli_ct_all P₀ (.inl k)) (hSCB k hk)

end QED.ChainProof.SetCPauli

end
