/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecMajT
public import QED.GradedProof.RPi4FacePerm

/-!
# (R-Π₄) step L9: the face sector of the absolute-term majorant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9. On the face sector
of a collapsed piece, `u` times the integral of the absolute-term majorant
`QED.GradedProof.RPi4.decMajF` is bounded uniformly in `u > 0` (no rate is needed):

* `FaceBr.decAbs`: the bracket with the absolute values of the coefficients; the hypotheses
  `FaceShape.FamHyp` pass to it (`FaceShape.FamHyp.decAbs`), and its rescaled integrand is real
  (`FaceShape.hJ_decAbs`, `FaceShape.decHR`);
* `FaceShape.dec_majF_join_le`: in join coordinates `ρ^p decMajF ≤ 24 · 3^{n-3} decHR` (three
  values of the bracket, `dec_abs_three_le`, and the rescaling identity `FaceBr.Rep`);
* `dec_faceCut_le`: the integral of a nonnegative function over the face cut is at most the
  `ρ`-integral of a majorant of its join form;
* **`FaceSort.dec_face_maj`**: `u ∫_{face} decMajF ≤ C` for all `u > 0`, uniformly over a family,
  from the face-sector rate of the absolute bracket (`FaceShape.face_rate`).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)
open QED.Integration.SimplexMerge (integral_simplex_comp_perm integrableOn_simplex_comp_perm_iff)

/-! ### The absolute bracket -/

namespace FaceBr

/-- **The bracket with the absolute values of the coefficients.** -/
noncomputable def decAbs {r : ℕ} (B : FaceBr r) : FaceBr r where
  d := B.d
  k := B.k
  C j ρ a b c β₀ b₁ := ((‖B.C j ρ a b c β₀ b₁‖ : ℝ) : ℂ)

theorem decAbs_meas {r : ℕ} {B : FaceBr r} (h : B.Meas) : B.decAbs.Meas := fun j =>
  Complex.measurable_ofReal.comp (h j).norm

end FaceBr

namespace FaceShape

variable {p q r : ℕ} (S : FaceShape p q) (B : FaceBr r)

theorem coefJ_decAbs (j : Fin r) {ρ : ℝ} (hρ : 0 ≤ ρ) (W : Fin (p + 1) → ℝ)
    (V : Fin (q + 1) → ℝ) : S.coefJ B.decAbs j ρ W V = ((‖S.coefJ B j ρ W V‖ : ℝ) : ℂ) := by
  have hU : ‖((S.uJ ρ W V ^ 2 : ℝ) : ℂ)⁻¹‖ = (S.uJ ρ W V ^ 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hρ' : ‖(ρ : ℂ) ^ (p - B.d)‖ = ρ ^ (p - B.d) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ]
  simp only [coefJ, FaceBr.decAbs, norm_mul, hU, hρ']
  push_cast
  ring

/-- **The real rescaled face integrand of the absolute bracket.** -/
noncomputable def decHR (ρ σ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) : ℝ :=
  W S.γ * ∑ j, ‖S.coefJ B j ρ W V‖ * ((S.vHat ρ W V + W S.γ * σ) ^ B.k j)⁻¹

theorem hJ_decAbs {ρ : ℝ} (hρ : 0 ≤ ρ) (σ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) :
    S.hJ B.decAbs ρ σ W V = (S.decHR B ρ σ W V : ℂ) := by
  simp only [hJ, decHR, coefJ_decAbs S B _ hρ]
  push_cast
  rfl

/-- The hypotheses of the `σ`-integration pass to the absolute bracket. -/
theorem FamHyp.decAbs {ι : Type*} {S : ι → FaceShape p q} {B : ι → FaceBr r} {k : Fin r → ℕ}
    {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM) :
    FamHyp S (fun s => (B s).decAbs) k ρ₀ c₁ K KM where
  hρ₀ := h.hρ₀
  hρ₁ := h.hρ₁
  hc₁ := h.hc₁
  hK := h.hK
  hKM := h.hKM
  hkc := h.hkc
  hk := h.hk
  hB s := FaceBr.decAbs_meas (h.hB s)
  hD j := by
    obtain ⟨Bb, L, hBL⟩ := h.hD j
    refine ⟨Bb, L, fun i ρ hρ hρ' => ?_⟩
    obtain ⟨h1, h2⟩ := hBL i ρ hρ hρ'
    dsimp only at h1 h2 ⊢
    rw [coefJ_decAbs _ _ _ hρ, coefJ_decAbs _ _ _ le_rfl]
    refine ⟨by rwa [Complex.norm_real, norm_norm], ?_⟩
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_norm_sub_norm_le _ _).trans h2
  hV := h.hV

/-! ### The join form of the majorant -/

/-- **The majorant in join coordinates**: `ρ^p decMajF(joinZ) ≤ 24 · 3^{n-3} decHR(ρ, ρu)`. -/
theorem dec_majF_join_le {n : ℕ} {Q : LoopQuartic} (hB : B.Rep n p Q S.α S.pp) (hn : 5 ≤ n)
    {ρ : ℝ} (hρ : 0 < ρ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) (hu : S.uJ ρ W V ≠ 0)
    (hθ : 0 ≤ W S.γ) {u : ℝ} (hv : 0 < S.vHat ρ W V + W S.γ * (ρ * u)) :
    ρ ^ p * decMajF n Q S.α S.pp S.M S.γJ u (joinZ ρ W V) ≤
      24 * 3 ^ (n - 3) * S.decHR B ρ (ρ * u) W V := by
  set v := S.vHat ρ W V + W S.γ * (ρ * u) with hvdef
  have hV : symanzikV S.α S.pp S.M (joinZ ρ W V) + joinZ ρ W V S.γJ * u = v := by
    rw [S.symanzikV_join_eq ρ W V hρ.ne' hu, S.joinZ_γJ]; ring
  have hl : ∀ l : ℝ, 1 ≤ l → ρ ^ (p + 1) * ‖paramAtV n Q S.α S.pp (joinZ ρ W V) (l * v)‖ ≤
      ∑ j, ‖S.coefJ B j ρ W V‖ * (v ^ B.k j)⁻¹ := by
    intro l hl
    have h := hB (joinZ ρ W V) ρ _ _ _ (S.b₁ W) (S.isFaceMat ρ W V) hρ.ne' hu
      (S.symanzikVector_one ρ W V) (l * v)
    rw [S.symanzikVector_zero] at h
    have e : ρ ^ (p + 1) * ‖paramAtV n Q S.α S.pp (joinZ ρ W V) (l * v)‖ =
        ‖(ρ : ℂ) ^ (p + 1) * paramAtV n Q S.α S.pp (joinZ ρ W V) (l * v)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    rw [e, h]
    simp only [FaceBr.val, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have e2 : ((uHat ρ (S.aJ ρ W V) (S.b W) (S.c W) ^ 2 : ℝ) : ℂ)⁻¹ *
        ((ρ : ℂ) ^ (p - B.d) * (B.C j ρ (S.aJ ρ W V) (S.b W) (S.c W) (S.PJ ρ W V) (S.b₁ W) *
          (((l * v : ℝ) : ℂ) ^ B.k j)⁻¹)) =
        S.coefJ B j ρ W V * (((l * v : ℝ) : ℂ) ^ B.k j)⁻¹ := by
      simp only [coefJ, uJ]; ring
    rw [e2, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hlv : 0 < l * v := mul_pos (one_pos.trans_le hl) hv
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hlv.le]
    exact inv_anti₀ (pow_pos hv _) (pow_le_pow_left₀ hv.le (le_mul_of_one_le_left hv.le hl) _)
  have hP := decMajP_le_paramAtV n Q S.α S.pp (joinZ ρ W V) hn hv
  have h1 := hl 1 le_rfl
  have h2 := hl 2 (by norm_num)
  have h3 := hl 3 (by norm_num)
  rw [one_mul] at h1
  have hρp : 0 ≤ ρ ^ (p + 1) := by positivity
  have hW : 0 ≤ W S.γ * (8 * 3 ^ (n - 3)) := by positivity
  unfold decMajF
  rw [hV, S.joinZ_γJ]
  calc ρ ^ p * (ρ * W S.γ * decMajP n Q S.α S.pp (joinZ ρ W V) v)
      = W S.γ * (ρ ^ (p + 1) * decMajP n Q S.α S.pp (joinZ ρ W V) v) := by ring
    _ ≤ W S.γ * (ρ ^ (p + 1) * (8 * 3 ^ (n - 3) *
          (‖paramAtV n Q S.α S.pp (joinZ ρ W V) v‖ +
            ‖paramAtV n Q S.α S.pp (joinZ ρ W V) (2 * v)‖ +
            ‖paramAtV n Q S.α S.pp (joinZ ρ W V) (3 * v)‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hρp) hθ
    _ = W S.γ * (8 * 3 ^ (n - 3)) *
          (ρ ^ (p + 1) * ‖paramAtV n Q S.α S.pp (joinZ ρ W V) v‖ +
            ρ ^ (p + 1) * ‖paramAtV n Q S.α S.pp (joinZ ρ W V) (2 * v)‖ +
            ρ ^ (p + 1) * ‖paramAtV n Q S.α S.pp (joinZ ρ W V) (3 * v)‖) := by ring
    _ ≤ W S.γ * (8 * 3 ^ (n - 3)) *
          ((∑ j, ‖S.coefJ B j ρ W V‖ * (v ^ B.k j)⁻¹) +
            (∑ j, ‖S.coefJ B j ρ W V‖ * (v ^ B.k j)⁻¹) +
            ∑ j, ‖S.coefJ B j ρ W V‖ * (v ^ B.k j)⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hW
    _ = 24 * 3 ^ (n - 3) * S.decHR B ρ (ρ * u) W V := by
        rw [decHR, ← hvdef]; ring

end FaceShape

/-! ### The face cut of a nonnegative function -/

section Cut

variable {p q : ℕ}

theorem dec_iter_le {F₁ F₂ : (Fin p → ℝ) → (Fin q → ℝ) → ℝ}
    (h0 : ∀ w ∈ simplexSet p, ∀ v ∈ simplexSet q, 0 ≤ F₁ w v)
    (hle : ∀ w ∈ simplexSet p, ∀ v ∈ simplexSet q, F₁ w v ≤ F₂ w v)
    (hI : IntegrableOn (fun x : (Fin p → ℝ) × (Fin q → ℝ) => F₂ x.1 x.2)
      (simplexSet p ×ˢ simplexSet q)) :
    ∫ w in simplexSet p, ∫ v in simplexSet q, F₁ w v ≤
      ∫ x in simplexSet p ×ˢ simplexSet q, F₂ x.1 x.2 := by
  have hI' : Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => F₂ x.1 x.2)
      ((volume.restrict (simplexSet p)).prod (volume.restrict (simplexSet q))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hI
  have hprod := setIntegral_prod (μ := (volume : Measure (Fin p → ℝ)))
    (ν := (volume : Measure (Fin q → ℝ))) (fun x : (Fin p → ℝ) × (Fin q → ℝ) => F₂ x.1 x.2)
    (s := simplexSet p) (t := simplexSet q) (by rw [← Measure.volume_eq_prod]; exact hI)
  rw [← Measure.volume_eq_prod] at hprod
  rw [hprod]
  refine integral_mono_of_nonneg ?_ hI'.integral_prod_left ?_
  · filter_upwards [ae_restrict_mem (measurableSet_simplexSet p)] with w hw
    exact setIntegral_nonneg (measurableSet_simplexSet q) (h0 w hw)
  · filter_upwards [hI'.prod_right_ae, ae_restrict_mem (measurableSet_simplexSet p)] with w hw hws
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (measurableSet_simplexSet q) (h0 w hws)) hw
      (ae_restrict_of_forall_mem (measurableSet_simplexSet q) (hle w hws))

/-- **The face cut of a nonnegative function**: if `ρ^p f(joinZ ρ W V) ≤ G ρ W V` on the face
sector, then `∫_{cut} f ≤ ∫₀^{ρ₀} (1 - ρ)^q ∫ G`. -/
theorem dec_faceCut_le {f : (Fin (p + 1 + q + 1) → ℝ) → ℝ}
    {G : ℝ → (Fin (p + 1) → ℝ) → (Fin (q + 1) → ℝ) → ℝ} {ρ₀ : ℝ} (hρ₁ : ρ₀ < 1)
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (p + 1 + q)))
    (hf0 : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ w ∈ simplexSet p, ∀ v ∈ simplexSet q,
      0 ≤ f (joinZ ρ (simplexPoint w) (simplexPoint v)))
    (hpt : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ w ∈ simplexSet p, ∀ v ∈ simplexSet q,
      ρ ^ p * f (joinZ ρ (simplexPoint w) (simplexPoint v)) ≤
        G ρ (simplexPoint w) (simplexPoint v))
    (hG : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → IntegrableOn (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
      G ρ (simplexPoint x.1) (simplexPoint x.2)) (simplexSet p ×ˢ simplexSet q))
    (hGρ : IntegrableOn (fun ρ => (1 - ρ) ^ q * ∫ x in simplexSet p ×ˢ simplexSet q,
      G ρ (simplexPoint x.1) (simplexPoint x.2)) (Ioc 0 ρ₀)) :
    ∫ x in simplexSet (p + 1 + q), {z | FaceShape.blockSum z ≤ ρ₀}.indicator f (simplexPoint x) ≤
      ∫ ρ in Ioc 0 ρ₀, (1 - ρ) ^ q * ∫ x in simplexSet p ×ˢ simplexSet q,
        G ρ (simplexPoint x.1) (simplexPoint x.2) := by
  have hm : MeasurableSet ((fun x : Fin (p + 1 + q) → ℝ => simplexPoint x) ⁻¹'
      {z | FaceShape.blockSum z ≤ ρ₀}) :=
    continuous_simplexPoint'.measurable (FaceShape.measurableSet_blockSum_le ρ₀)
  have hf' : IntegrableOn (fun x => {z | FaceShape.blockSum z ≤ ρ₀}.indicator f (simplexPoint x))
      (simplexSet (p + 1 + q)) := by
    have := hf.indicator hm
    refine this.congr_fun (fun x _ => ?_) (measurableSet_simplexSet _)
    by_cases hx : simplexPoint x ∈ {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀}
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ _ from hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ _ from hx)]
  set g : ℝ → ℝ := fun ρ => (1 - ρ) ^ q * ∫ x in simplexSet p ×ˢ simplexSet q,
    G ρ (simplexPoint x.1) (simplexPoint x.2) with hg
  have hb : ∀ ρ (w : Fin p → ℝ) (v : Fin q → ℝ),
      FaceShape.blockSum (p := p) (q := q) (joinZ ρ (simplexPoint w) (simplexPoint v)) = ρ :=
    fun ρ w v => FaceShape.blockSum_joinZ ρ w _
  have hR : ∫ ρ in Ioc 0 ρ₀, g ρ = ∫ ρ in Ioc (0 : ℝ) 1, (Iic ρ₀).indicator g ρ := by
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hρ₁.le]
  have hJ : ∫ x in simplexSet (p + 1 + q),
      {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀}.indicator f (simplexPoint x) =
      ∫ ρ in (0 : ℝ)..1, (ρ ^ p * (1 - ρ) ^ q) • ∫ w in simplexSet p, ∫ v in simplexSet q,
        {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀}.indicator f
          (joinZ ρ (simplexPoint w) (simplexPoint v)) := integral_simplex_join hf'
  rw [hJ, intervalIntegral.integral_of_le zero_le_one, hR]
  have hgi : IntegrableOn ((Iic ρ₀).indicator g) (Ioc 0 1) := by
    refine ((hGρ.integrable_indicator measurableSet_Ioc).integrableOn).congr_fun
      (fun ρ hρ => ?_) measurableSet_Ioc
    by_cases h : ρ ≤ ρ₀
    · rw [indicator_of_mem (show ρ ∈ Ioc 0 ρ₀ from ⟨hρ.1, h⟩),
        indicator_of_mem (show ρ ∈ Iic ρ₀ from h)]
    · rw [indicator_of_notMem (show ρ ∉ Ioc 0 ρ₀ from fun h' => h h'.2),
        indicator_of_notMem (show ρ ∉ Iic ρ₀ from h)]
  refine integral_mono_of_nonneg ?_ hgi ?_
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun ρ hρ => ?_
    have h0 : 0 ≤ ρ ^ p * (1 - ρ) ^ q := mul_nonneg (pow_nonneg hρ.1.le _)
      (pow_nonneg (by linarith [hρ.2]) _)
    refine smul_nonneg h0 (setIntegral_nonneg (measurableSet_simplexSet p) fun w hw =>
      setIntegral_nonneg (measurableSet_simplexSet q) fun v hv => ?_)
    by_cases h : ρ ≤ ρ₀
    · rw [indicator_of_mem (show joinZ ρ (simplexPoint w) (simplexPoint v) ∈
        {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀} by
          show FaceShape.blockSum (p := p) (q := q) _ ≤ ρ₀; rw [hb]; exact h)]
      exact hf0 ρ hρ.1 h w hw v hv
    · rw [indicator_of_notMem (show joinZ ρ (simplexPoint w) (simplexPoint v) ∉
        {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀} from fun h' => h (by
          have h'' : FaceShape.blockSum (p := p) (q := q) _ ≤ ρ₀ := h'
          rwa [hb] at h''))]
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun ρ hρ => ?_
    by_cases h : ρ ≤ ρ₀
    · rw [indicator_of_mem (show ρ ∈ Iic ρ₀ from h)]
      simp only [hg, smul_eq_mul]
      have hcut : ∀ w ∈ simplexSet p, ∫ v in simplexSet q,
          {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀}.indicator f
            (joinZ ρ (simplexPoint w) (simplexPoint v)) =
          ∫ v in simplexSet q, f (joinZ ρ (simplexPoint w) (simplexPoint v)) := fun w _ =>
        setIntegral_congr_fun (measurableSet_simplexSet q) fun v _ =>
          indicator_of_mem (show joinZ ρ (simplexPoint w) (simplexPoint v) ∈
            {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀} by
              show FaceShape.blockSum (p := p) (q := q) _ ≤ ρ₀; rw [hb]; exact h) f
      have hcut' : ∫ w in simplexSet p, ∫ v in simplexSet q,
          {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀}.indicator f
            (joinZ ρ (simplexPoint w) (simplexPoint v)) =
          ∫ w in simplexSet p, ∫ v in simplexSet q,
            f (joinZ ρ (simplexPoint w) (simplexPoint v)) :=
        setIntegral_congr_fun (measurableSet_simplexSet p) hcut
      have hit := dec_iter_le (F₁ := fun w v => ρ ^ p * f (joinZ ρ (simplexPoint w)
        (simplexPoint v))) (F₂ := fun w v => G ρ (simplexPoint w) (simplexPoint v))
        (fun w hw v hv => mul_nonneg (pow_nonneg hρ.1.le _) (hf0 ρ hρ.1 h w hw v hv))
        (fun w hw v hv => hpt ρ hρ.1 h w hw v hv) (hG ρ hρ.1 h)
      have hpull : ∫ w in simplexSet p, ∫ v in simplexSet q,
          ρ ^ p * f (joinZ ρ (simplexPoint w) (simplexPoint v)) =
          ρ ^ p * ∫ w in simplexSet p, ∫ v in simplexSet q,
            f (joinZ ρ (simplexPoint w) (simplexPoint v)) := by
        rw [← integral_const_mul]
        exact setIntegral_congr_fun (measurableSet_simplexSet p) fun w _ => integral_const_mul _ _
      have h1q : 0 ≤ (1 - ρ) ^ q := pow_nonneg (by linarith [hρ.2]) _
      show ρ ^ p * (1 - ρ) ^ q * _ ≤ _
      rw [hcut', mul_comm (ρ ^ p), mul_assoc, ← hpull]
      exact mul_le_mul_of_nonneg_left hit h1q
    · rw [indicator_of_notMem (show ρ ∉ Iic ρ₀ from h)]
      simp only [smul_eq_mul]
      have hz : ∫ w in simplexSet p, ∫ v in simplexSet q,
          {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀}.indicator f
            (joinZ ρ (simplexPoint w) (simplexPoint v)) = 0 := by
        refine (setIntegral_congr_fun (measurableSet_simplexSet p) fun w _ =>
          setIntegral_congr_fun (measurableSet_simplexSet q) fun v _ =>
            indicator_of_notMem (show joinZ ρ (simplexPoint w) (simplexPoint v) ∉
              {z | FaceShape.blockSum (p := p) (q := q) z ≤ ρ₀} from fun h' => h (by
                have h'' : FaceShape.blockSum (p := p) (q := q) _ ≤ ρ₀ := h'
                rwa [hb] at h'')) f).trans ?_
        simp
      rw [hz, mul_zero]

end Cut

/-! ### Relabelling the majorant -/

theorem dec_decMajF_perm {k m : ℕ} (e : Fin (k + 1) ≃ Fin (m + 1)) (n : ℕ) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (k + 1)) (u : ℝ) (z : Fin (k + 1) → ℝ) :
    decMajF n Q (fun i => α (e i)) (fun i => pp (e i)) (fun i => M (e i)) γ u z =
      decMajF n Q α pp M (e γ) u fun j => z (e.symm j) := by
  simp only [decMajF, decMajP, cOneAt, cTwoAt, cThreeAt, symanzikU_perm, symanzikMatrix_perm,
    loopShift_perm, symanzikV_perm, Equiv.symm_apply_apply]

/-! ### The face sector of a family of face shapes -/

namespace FaceShape

variable {p q r : ℕ}

theorem gJ_decAbs (S : FaceShape p q) (B : FaceBr r) {ρ : ℝ} (hρ : 0 ≤ ρ) (σ : ℝ) :
    S.gJ B.decAbs ρ σ = (((1 - ρ) ^ q * ∫ x in simplexSet p ×ˢ simplexSet q,
      S.decHR B ρ σ (simplexPoint x.1) (simplexPoint x.2) : ℝ) : ℂ) := by
  have e : ∫ x in simplexSet p ×ˢ simplexSet q, S.hJ B.decAbs ρ σ (simplexPoint x.1)
      (simplexPoint x.2) = ((∫ x in simplexSet p ×ˢ simplexSet q,
        S.decHR B ρ σ (simplexPoint x.1) (simplexPoint x.2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_prod fun x _ => hJ_decAbs S B hρ σ _ _
  rw [gJ, e]
  push_cast
  rfl

/-- **The face sector of the majorant for a family of face shapes**: `u` times the integral of
`decMajF` over the face cut is bounded uniformly in `u > 0` and over the family. -/
theorem dec_face_shape {ι : Type*} {S : ι → FaceShape (p + 1) q} {B : ι → FaceBr r}
    {k : Fin r → ℕ} {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM)
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) {n : ℕ} (hn : 5 ≤ n) {Q : ι → LoopQuartic}
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u
        (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) →
      u * ∫ x in simplexSet (p + 1 + 1 + q), {z | blockSum z ≤ ρ₀}.indicator
        (decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u) (simplexPoint x) ≤ C := by
  obtain ⟨C₀, hC₀⟩ := face_rate h.decAbs hγ
  obtain ⟨BD, LD, LV, hS⟩ := sigData h.decAbs
  set μ := volume.restrict (simplexSet (p + 1) ×ˢ simplexSet q)
  set Cu := sigK₀ c₁ BD k * ((c₁ ^ 2)⁻¹ * μ.real univ) with hCu
  set c : ℝ := 24 * 3 ^ (n - 3) with hc
  have hρ₀ := h.hρ₀
  set g : ι → ℝ → ℝ → ℝ := fun s u ρ => (1 - ρ) ^ q * ∫ x in simplexSet (p + 1) ×ˢ simplexSet q,
    (S s).decHR (B s) ρ (ρ * u) (simplexPoint x.1) (simplexPoint x.2) with hg
  have hgJ : ∀ s u ρ, 0 ≤ ρ → (S s).gJ (B s).decAbs ρ (ρ * u) = (g s u ρ : ℂ) :=
    fun s u ρ hρ => gJ_decAbs (S s) (B s) hρ _
  have hgb : ∀ s u, 0 ≤ u → ∀ ρ, 0 ≤ ρ → ρ ≤ ρ₀ →
      ‖(S s).gJ (B s).decAbs ρ (ρ * u)‖ ≤ Cu := fun s u hu ρ hρ hρ' => by
    have e : (B s).decAbs.k = k := h.hkc s
    rw [gJ_eq_sigG, e]
    exact (hS s).norm_sigG_le_unif q hρ hρ' (mul_nonneg hρ hu)
  have hgabs : ∀ s u, 0 ≤ u → ∀ ρ, 0 ≤ ρ → ρ ≤ ρ₀ → |g s u ρ| ≤ Cu := by
    intro s u hu ρ hρ hρ'
    have := hgb s u hu ρ hρ hρ'
    rwa [hgJ s u ρ hρ, Complex.norm_real, Real.norm_eq_abs] at this
  have hY : ∀ s u, (∫ ρ in (0 : ℝ)..ρ₀, (S s).gJ (B s).decAbs ρ (ρ * u)) =
      ((∫ ρ in (0 : ℝ)..ρ₀, g s u ρ : ℝ) : ℂ) := by
    intro s u
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun ρ hρ => ?_
    rw [uIcc_of_le hρ₀.le] at hρ
    exact hgJ s u ρ hρ.1
  have hI : ∀ s u, 0 ≤ u → |∫ ρ in (0 : ℝ)..ρ₀, g s u ρ| ≤ Cu * ρ₀ := by
    intro s u hu
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ρ₀) (f := g s u)
      (C := Cu) fun ρ hρ => by
        rw [uIoc_of_le hρ₀.le] at hρ
        rw [Real.norm_eq_abs]
        exact hgabs s u hu ρ hρ.1.le hρ.2
    rwa [Real.norm_eq_abs, sub_zero, abs_of_pos hρ₀] at this
  have hX : ∀ s, ‖∫ σ in Ioi 0, (S s).gJ (B s).decAbs 0 σ‖ ≤ |C₀| + Cu * ρ₀ := by
    intro s
    have h1 := hC₀ s 1 one_pos
    rw [Real.one_rpow, mul_one, one_smul, hY s 1] at h1
    set X := ∫ σ in Ioi 0, (S s).gJ (B s).decAbs 0 σ
    set Y : ℂ := ((∫ ρ in (0 : ℝ)..ρ₀, g s 1 ρ : ℝ) : ℂ)
    have hYn : ‖Y‖ ≤ Cu * ρ₀ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hI s 1 zero_le_one
    calc ‖X‖ = ‖Y - (Y - X)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Y‖ + ‖Y - X‖ := norm_sub_le _ _
      _ ≤ Cu * ρ₀ + |C₀| := add_le_add hYn (h1.trans (le_abs_self _))
      _ = _ := by ring
  have hU : ∀ s u, 0 < u → u * ∫ ρ in (0 : ℝ)..ρ₀, g s u ρ ≤ 2 * |C₀| + 2 * (Cu * ρ₀) := by
    intro s u hu
    have hCu0 : 0 ≤ Cu * ρ₀ := (abs_nonneg _).trans (hI s u hu.le)
    have hle : u * ∫ ρ in (0 : ℝ)..ρ₀, g s u ρ ≤ u * |∫ ρ in (0 : ℝ)..ρ₀, g s u ρ| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hu.le
    rcases le_total u 1 with hu1 | hu1
    · have := mul_le_mul hu1 (hI s u hu.le) (abs_nonneg _) zero_le_one
      linarith [abs_nonneg C₀]
    · have h1 := hC₀ s u hu
      rw [hY s u] at h1
      have hr : u ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
      have hr0 : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hu.le _
      set Y : ℂ := ((∫ ρ in (0 : ℝ)..ρ₀, g s u ρ : ℝ) : ℂ) with hYd
      set X := ∫ σ in Ioi 0, (S s).gJ (B s).decAbs 0 σ
      have hC : C₀ * u ^ (-(1 / 2) : ℝ) ≤ |C₀| :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) hr0).trans
          ((mul_le_mul_of_nonneg_left hr (abs_nonneg C₀)).trans_eq (mul_one _))
      have h2 : ‖u • Y‖ ≤ |C₀| + (|C₀| + Cu * ρ₀) := calc
          ‖u • Y‖ = ‖(u • Y - X) + X‖ := by rw [sub_add_cancel]
          _ ≤ ‖u • Y - X‖ + ‖X‖ := norm_add_le _ _
          _ ≤ |C₀| + (|C₀| + Cu * ρ₀) := add_le_add (h1.trans hC) (hX s)
      rw [norm_smul, Real.norm_of_nonneg hu.le, hYd, Complex.norm_real, Real.norm_eq_abs] at h2
      linarith
  refine ⟨c * (2 * |C₀| + 2 * (Cu * ρ₀)), fun s u hu hf => ?_⟩
  have hVj : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ w ∈ simplexSet (p + 1), ∀ v ∈ simplexSet q,
      c₁ ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint w) (simplexPoint v)) :=
    fun ρ hρ hρ' w hw v hv => h.hV s ρ hρ hρ' (w, v) ⟨hw, hv⟩
  have hf0 : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ w ∈ simplexSet (p + 1), ∀ v ∈ simplexSet q,
      0 ≤ decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u
        (joinZ ρ (simplexPoint w) (simplexPoint v)) := fun ρ hρ hρ' w hw v hv => by
    obtain ⟨hW0, -⟩ := simplexPoint_mem_stdSimplex hw
    have hz : 0 ≤ joinZ ρ (simplexPoint w) (simplexPoint v) (S s).γJ := by
      rw [(S s).joinZ_γJ]; exact mul_nonneg hρ.le (hW0 _)
    exact decMajF_nonneg _ _ _ _ _ hz
      (add_nonneg (h.hc₁.le.trans (hVj ρ hρ hρ' w hw v hv)) (mul_nonneg hz hu.le))
  have hpt : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ w ∈ simplexSet (p + 1), ∀ v ∈ simplexSet q,
      ρ ^ (p + 1) * decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u
        (joinZ ρ (simplexPoint w) (simplexPoint v)) ≤
      c * (S s).decHR (B s) ρ (ρ * u) (simplexPoint w) (simplexPoint v) :=
    fun ρ hρ hρ' w hw v hv => by
      obtain ⟨hW0, hW1⟩ := simplexPoint_mem_stdSimplex hw
      obtain ⟨-, hV1⟩ := simplexPoint_mem_stdSimplex hv
      have hu' : (S s).uJ ρ (simplexPoint w) (simplexPoint v) ≠ 0 := by
        have := (S s).uJ_ge ρ _ _ hW0 hW1 hV1 hρ.le
        exact ne_of_gt (by linarith [hρ'.trans_lt h.hρ₁])
      have hvh : c₁ ≤ (S s).vHat ρ (simplexPoint w) (simplexPoint v) :=
        (S s).vHat_ge h.hρ₀ h.hρ₁ (h.hV s) ⟨(w, v), ⟨hw, hv⟩⟩ hρ.le hρ'
      have hθu := mul_nonneg (hW0 (S s).γ) (mul_nonneg hρ.le hu.le)
      exact dec_majF_join_le (S s) (B s) (hRep s) hn hρ _ _ hu' (hW0 _)
        (by linarith [h.hc₁])
  have hG : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → IntegrableOn (fun x : (Fin (p + 1) → ℝ) × (Fin q → ℝ) =>
      c * (S s).decHR (B s) ρ (ρ * u) (simplexPoint x.1) (simplexPoint x.2))
      (simplexSet (p + 1) ×ˢ simplexSet q) := fun ρ hρ hρ' => by
    have hi := (integrable_hJ h.decAbs s hρ.le hρ' (mul_nonneg hρ.le hu.le)).re
    simp only [hJ_decAbs _ _ hρ.le, RCLike.re_to_complex, Complex.ofReal_re] at hi
    exact hi.const_mul c
  have e : ∀ ρ, (1 - ρ) ^ q * ∫ x in simplexSet (p + 1) ×ˢ simplexSet q,
      c * (S s).decHR (B s) ρ (ρ * u) (simplexPoint x.1) (simplexPoint x.2) = c * g s u ρ :=
    fun ρ => by rw [integral_const_mul]; simp only [hg]; ring
  have hgi : IntegrableOn (g s u) (Ioc 0 ρ₀) := by
    have hm : Measurable fun ρ => ((S s).gJ (B s).decAbs ρ (ρ * u)).re := by
      have ek : (B s).decAbs.k = k := h.hkc s
      simp only [gJ_eq_sigG, ek]
      exact Complex.measurable_re.comp (((hS s).measurable_sigG_uncurry q).comp
        (measurable_id.prodMk (measurable_id.mul_const u)))
    refine (IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable Cu ?_).congr_fun
      (fun ρ hρ => ?_) measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun ρ hρ => ?_
      rw [hgJ s u ρ hρ.1.le, Complex.ofReal_re, Real.norm_eq_abs]
      exact hgabs s u hu.le ρ hρ.1.le hρ.2
    · beta_reduce
      rw [hgJ s u ρ hρ.1.le, Complex.ofReal_re]
  have hGρ : IntegrableOn (fun ρ => (1 - ρ) ^ q * ∫ x in simplexSet (p + 1) ×ˢ simplexSet q,
      c * (S s).decHR (B s) ρ (ρ * u) (simplexPoint x.1) (simplexPoint x.2)) (Ioc 0 ρ₀) := by
    simp only [e]
    exact hgi.const_mul c
  have hcut := dec_faceCut_le (G := fun ρ W V => c * (S s).decHR (B s) ρ (ρ * u) W V)
    h.hρ₁ hf hf0 hpt hG hGρ
  simp only [e] at hcut
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hρ₀.le] at hcut
  calc u * _ ≤ u * (c * ∫ ρ in (0 : ℝ)..ρ₀, g s u ρ) := mul_le_mul_of_nonneg_left hcut hu.le
    _ = c * (u * ∫ ρ in (0 : ℝ)..ρ₀, g s u ρ) := by ring
    _ ≤ c * (2 * |C₀| + 2 * (Cu * ρ₀)) :=
        mul_le_mul_of_nonneg_left (hU s u hu) (by positivity)

end FaceShape

/-! ### The face sector of a family of sorted pieces -/

namespace FaceSort

variable {ι : Type*} {p q r : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))}

/-- **The face sector of the majorant, in the piece's own line order**: `u` times the integral
of `decMajF` over the face cut is bounded uniformly in `u > 0` and over the family (hypotheses
as in `QED.GradedProof.RPi4.FaceSort.face_rate_piece`). -/
theorem dec_face_maj (h : FaceSort p q α e) (pp : ι → Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    (M : ι → Fin (p + 1 + 1 + q + 1) → ℝ) (n : ℕ) (hn : 5 ≤ n) (Q : ι → LoopQuartic)
    (B : ι → FaceBr r) (k : Fin r → ℕ) {ρ₀ c₁ K KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1)
    (hc₁ : 0 < c₁)
    (hK : ∀ s, (h.shape (pp s) (M s)).kF ≤ K) (hKM : ∀ s, (h.shape (pp s) (M s)).kM ≤ KM)
    (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j) (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (h.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i)))
    (hV : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (gam e) ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => decMajF n (Q s) α (pp s) (M s) (gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q)) →
      u * ∫ x in simplexSet (p + 1 + 1 + q),
          {w | faceSum α w ≤ ρ₀}.indicator (decMajF n (Q s) α (pp s) (M s) (gam e) u)
            (simplexPoint x) ≤ C := by
  set S : ι → FaceShape (p + 1) q := fun s => h.shape (pp s) (M s) with hS
  have hVS : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ ≤ symanzikV (S s).α (S s).pp (S s).M
        (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)) := by
    intro s ρ hρ hρ' x hx
    obtain ⟨hW0, hW1⟩ := simplexPoint_mem_stdSimplex hx.1
    obtain ⟨hV0, hV1⟩ := simplexPoint_mem_stdSimplex hx.2
    set W := simplexPoint x.1
    set V := simplexPoint x.2
    set z := joinZ ρ W V with hz
    have hρ1 : ρ < 1 := hρ'.trans_lt hρ₁
    have hz0 : ∀ l, 0 ≤ z l := fun l => by
      refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) l
      · simp only [hz, joinZ, Fin.append_left, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg hρ.le (hW0 i)
      · simp only [hz, joinZ, Fin.append_right, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hV0 j)
    have hz1 : ∑ l, z l = 1 := by
      rw [sum_join]
      simp only [hz, joinZ, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum, hW1, hV1]
      ring
    have hU : symanzikU (S s).α z ≠ 0 := by
      rw [symanzikU, det_face ((S s).isFaceMat ρ W V)]
      have := (S s).uJ_ge ρ W V hW0 hW1 hV1 hρ.le
      exact mul_ne_zero hρ.ne' (by unfold FaceShape.uJ at this; linarith)
    have hzγ : z (S s).γJ ≤ ρ₀ := by
      rw [hz, (S s).joinZ_γJ]
      have hWγ : W (S s).γ ≤ 1 := by
        rw [← hW1]
        exact Finset.single_le_sum (fun i _ => hW0 i) (Finset.mem_univ _)
      nlinarith [hW0 (S s).γ]
    have := hV s (fun j => z (e.symm j)) (fun l => hz0 _)
      (by rw [← hz1]; exact e.symm.sum_comp z)
      (by rwa [← symanzikU_perm, ← h.shape_α (pp s) (M s)])
      (by simpa only [gam, Equiv.symm_apply_apply] using
        (show z (Fin.castAdd (q + 1) (Fin.last (p + 1))) ≤ ρ₀ from hzγ))
    rwa [← symanzikV_perm, ← h.shape_α (pp s) (M s), ← h.shape_pp (pp s) (M s),
      ← h.shape_M (pp s) (M s)] at this
  have hF : FaceShape.FamHyp S B k ρ₀ c₁ K KM :=
    ⟨hρ₀, hρ₁, hc₁, hK, hKM, hkc, hk, hB, hD, hVS⟩
  have hRep' : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp := fun s => by
    rw [hS]
    dsimp only
    rw [h.shape_α, h.shape_pp]
    exact hRep s
  obtain ⟨C, hC⟩ := FaceShape.dec_face_shape hF (fun s => rfl) hn hRep'
  refine ⟨C, fun s u hu hf => ?_⟩
  have hfU : ∀ z, decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u z =
      decMajF n (Q s) α (pp s) (M s) (gam e) u fun j => z (e.symm j) := fun z => by
    have hg : e (S s).γJ = gam e := rfl
    rw [hS]
    dsimp only
    rw [h.shape_α, h.shape_pp, h.shape_M, dec_decMajF_perm]
    rfl
  have hf' : IntegrableOn (fun x => decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u
      (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) := by
    simp only [hfU]
    exact (integrableOn_simplex_comp_perm_iff e.symm
      (decMajF n (Q s) α (pp s) (M s) (gam e) u)).mpr hf
  have hint : ∫ x in simplexSet (p + 1 + 1 + q),
      {w | faceSum α w ≤ ρ₀}.indicator (decMajF n (Q s) α (pp s) (M s) (gam e) u)
        (simplexPoint x) =
      ∫ x in simplexSet (p + 1 + 1 + q),
        {z | FaceShape.blockSum (p := p + 1) (q := q) z ≤ ρ₀}.indicator
          (decMajF n (Q s) (S s).α (S s).pp (S s).M (S s).γJ u) (simplexPoint x) := by
    rw [← integral_simplex_comp_perm e.symm]
    refine setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => ?_
    simp only [indicator, mem_ofPred_eq, h.blockSum_eq, hfU]
    rfl
  rw [hint]
  exact hC s u hu hf'

end FaceSort

end QED.GradedProof.RPi4

end
