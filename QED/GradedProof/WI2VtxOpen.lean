/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2ChainNum
public import QED.GradedProof.WI2Reroute
public import QED.TwoLoop.LimitCovarianceClasses

/-!
# Open-class vertex limits at zero photon momentum as parametric values

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7 for the six open classes `L, X, C₊, C₋, S₊, S₋`.

* `SEData.pvF_sum`: the parametric value of a function is linear on functions with admissible
  quartics (`pv_qsum`).
* `SEData.pvF_eq_const_mul_of_comp`: two parametric values are proportional when the joint
  integrands at every `ε > 0` are, up to an integer unimodular affine change of loop momenta.
* `vtxData c hc P`: the eight-line data of the Pauli–Villars form of the open class `c` at
  `p' = p` (external momentum `p` on the four electron lines), as `SEData`; `vpos_vtxData` from
  `QED.TwoLoop.ClassLimit.symanzikV_open_ge`.
* `classLimitV_eq_pvF`: the class limit at `p' = p` is the parametric value of the normalized
  class numerator.
* **`sum_lower_classLimitV_eq`**: if the contracted class numerator `∑_μ r_μ N^μ(ℓ)` is
  `κ F(Mℓ + a)` and the eight denominators are those of `D` at `Mℓ + a`, then
  `∑_μ r_μ classLimitV c P p p μ = κ · D.pvF F`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2

variable {D : SEData}

/-- Admissible quartics are closed under linear combinations. -/
theorem good_qsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) {Q : ι → LoopQuartic}
    (hQ : ∀ k, D.Good (Q k)) : D.Good (qsum s c Q) := by
  refine ⟨?_, ?_⟩
  · by_cases h7 : 7 ≤ D.m
    · exact Or.inl h7
    · exact Or.inr (quart_qsum s c Q fun k _ => ((hQ k).1.resolve_left h7))
  · have e : (qsum s c Q).eval = fun ℓ => ∑ k ∈ s, c k * (Q k).eval ℓ :=
      funext fun ℓ => eval_qsum s c Q ℓ
    rw [e]
    exact RefinedBound.sum s fun k _ => (hQ k).2.const_mul (c k)

theorem eval_qsum_eq {ι : Type*} (s : Finset ι) (c : ι → ℂ) {Q : ι → LoopQuartic}
    {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ} (he : ∀ k, (Q k).eval = F k) :
    (qsum s c Q).eval = fun ℓ => ∑ k ∈ s, c k * F k ℓ := by
  funext ℓ
  rw [eval_qsum]
  exact Finset.sum_congr rfl fun k _ => by rw [he k]

/-- Admissible quartics for a linear combination. -/
theorem exists_good_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : ∀ k, ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = F k) :
    ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = fun ℓ => ∑ k ∈ s, c k * F k ℓ := by
  choose Q hQ he using hF
  exact ⟨qsum s c Q, good_qsum s c hQ, eval_qsum_eq s c he⟩

/-- **The parametric value is linear** on functions with admissible quartics. -/
theorem pvF_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hF : ∀ k, ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = F k) {q : Fin (D.m + 1) → Fin 4 → ℝ}
    (hV : D.VPos q) :
    ∑ k ∈ s, c k * D.pvF (F k) q = D.pvF (fun ℓ => ∑ k ∈ s, c k * F k ℓ) q := by
  choose Q hQ he using hF
  rw [pvF_eq (good_qsum s c hQ) (eval_qsum_eq s c he) hV,
    pv_qsum s c Q fun k _ => integrableOn_pv (hQ k) hV]
  exact Finset.sum_congr rfl fun k _ => by rw [pvF_eq (hQ k) (he k) hV]

/-- **Proportional parametric values** from proportional joint integrands up to an integer
unimodular affine change of loop momenta. -/
theorem pvF_eq_const_mul_of_comp {D₁ D₂ : SEData} {F₁ F₂ : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h₁ : ∃ Q : LoopQuartic, D₁.Good Q ∧ Q.eval = F₁)
    (h₂ : ∃ Q : LoopQuartic, D₂.Good Q ∧ Q.eval = F₂) {q₁ : Fin (D₁.m + 1) → Fin 4 → ℝ}
    {q₂ : Fin (D₂.m + 1) → Fin 4 → ℝ} (hV₁ : D₁.VPos q₁) (hV₂ : D₂.VPos q₂)
    (R : Matrix (Fin 2) (Fin 2) ℤ) (hR : IsUnit R.det) (a : Fin 2 → Fin 4 → ℝ) (κ : ℂ)
    (h : ∀ ε, 0 < ε → ∀ ℓ, F₁ ℓ * ∏ i, (lineDenom D₁.α q₁ D₁.M ε i ℓ)⁻¹ =
      κ * (F₂ (loopAff R a ℓ) * ∏ i, (lineDenom D₂.α q₂ D₂.M ε i (loopAff R a ℓ))⁻¹)) :
    D₁.pvF F₁ q₁ = κ * D₂.pvF F₂ q₂ := by
  obtain ⟨Q₁, hg₁, he₁⟩ := h₁
  obtain ⟨Q₂, hg₂, he₂⟩ := h₂
  rw [pvF_eq hg₁ he₁ hV₁, pvF_eq hg₂ he₂ hV₂]
  refine tendsto_nhds_unique (tendsto_pv hg₁ hV₁) (((tendsto_pv hg₂ hV₂).const_mul κ).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul,
    ← jointEnergyFirstIntegral_loopAff _ R hR a]
  congr 1
  funext ℓ
  rw [he₁, he₂]
  exact (h ε hε ℓ).symm

end QED.GradedProof.SE2.SEData

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.ClassLimit
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ClassIntegrable (openClasses isLoopPoly_classNumeratorE
  refinedBound_classNumeratorE)

/-- The external momentum flows through the four electron lines of an open class at `p' = p`. -/
def csVtx : Fin 8 → ℝ := ![1, 1, 1, 1, 0, 0, 0, 0]

/-- **The eight-line data of the open class `c` at `p' = p`.** -/
def vtxData {c : Class5} (hc : c ∈ openClasses) (P : Params) : SEData where
  m := 7
  α := castLoopMatrix (class5LoopMatrixPV c)
  cs := csVtx
  M := pvMasses P
  E := {0, 1, 2, 3}
  hm := by norm_num
  hcrit := (noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc

theorem vtxData_mom {c : Class5} (hc : c ∈ openClasses) (P : Params) (p : Fin 4 → ℝ) :
    (vtxData hc P).mom p = pvMomentaE c p p := by
  funext i
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;>
    simp [SEData.mom, vtxData, csVtx, pvMomentaE, extMomenta, pvLines, classLXMomenta,
      classCpSpMomenta, classCmSmMomenta]

theorem vpos_vtxData {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) :
    (vtxData hc P).VPos ((vtxData hc P).mom p) := by
  refine ⟨3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2),
    mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2)),
    fun z hz hz1 hU => ?_⟩
  rw [vtxData_mom]
  exact symanzikV_open_ge hc P hmγ hΛ hp hp (by simp [Minkowski.dot]) hz hz1 hU

theorem good_vtxData {c : Class5} (hc : c ∈ openClasses) (P : Params) (p : Fin 4 → ℝ)
    (α β μ : Fin 4) : ∃ Q : LoopQuartic, (vtxData hc P).Good Q ∧ Q.eval = fun ℓ =>
      twoLoopNorm * classNumeratorE c P (fun _ => p) (fun _ => p) (fun _ => p - p)
        (fun _ => α) (fun _ => β) (fun _ => μ) ℓ := by
  obtain ⟨Q, hQ⟩ := ((isLoopPoly_classNumeratorE hc P (fun _ => p) (fun _ => p)
    (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ)).const_mul
    twoLoopNorm).exists_loopQuartic
  refine ⟨Q, ⟨Or.inl (by change 7 ≤ 7; norm_num), ?_⟩, hQ⟩
  rw [hQ]
  exact (refinedBound_classNumeratorE hc P _ _ _ _ _ _).const_mul _

/-- **The open-class limit at `p' = p` is a parametric value.** -/
theorem classLimitV_eq_pvF {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (μ α β : Fin 4) :
    classLimitV c P p p μ α β = (vtxData hc P).pvF (fun ℓ => twoLoopNorm * classNumeratorE c P
      (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ)
      ((vtxData hc P).mom p) := by
  obtain ⟨Q, he, -, h⟩ := tendsto_contractionValue₂_open hc P hm hmγ hΛ
    (pOut := fun _ => p) (pIn := fun _ => p) (kIn := fun _ => p - p) (by simp) hp hp
    (by simp [Minkowski.dot]) (fun _ => α) (fun _ => β) (fun _ => μ)
  have hg : (vtxData hc P).Good Q := by
    refine ⟨Or.inl (by change 7 ≤ 7; norm_num), ?_⟩
    rw [he]
    exact (refinedBound_classNumeratorE hc P _ _ _ _ _ _).const_mul _
  rw [SEData.pvF_eq hg he (vpos_vtxData hc P hm hmγ hΛ hp)]
  simp only [classLimitV, Matrix.of_apply]
  rw [h.limUnder_eq, SEData.pv, vtxData_mom]
  rfl

/-- **The contracted open-class limit at `p' = p` as a parametric value on other data**, from
the pointwise identity of the joint integrands after `ℓ ↦ Rℓ + a`. -/
theorem sum_lower_classLimitV_eq {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) {D : SEData}
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = F)
    {q : Fin (D.m + 1) → Fin 4 → ℝ} (hV : D.VPos q) (R : Matrix (Fin 2) (Fin 2) ℤ)
    (hR : IsUnit R.det) (a : Fin 2 → Fin 4 → ℝ) (κ : ℂ)
    (hnum : ∀ ℓ, ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE c P
      (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        κ * F (loopAff R a ℓ))
    (hden : ∀ ε, 0 < ε → ∀ ℓ, ∏ i, lineDenom (vtxData hc P).α ((vtxData hc P).mom p)
      (vtxData hc P).M ε i ℓ = ∏ i, lineDenom D.α q D.M ε i (loopAff R a ℓ)) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV c P p p μ α β = κ * D.pvF F q := by
  have hV₁ := vpos_vtxData hc P hm hmγ hΛ hp
  simp only [classLimitV_eq_pvF hc P hm hmγ hΛ hp]
  rw [SEData.pvF_sum _ _ (fun μ => good_vtxData hc P p α β μ) hV₁]
  refine SEData.pvF_eq_const_mul_of_comp
    (SEData.exists_good_sum _ _ fun μ => good_vtxData hc P p α β μ) hF hV₁ hV R hR a κ
    fun ε hε ℓ => ?_
  rw [hnum, Finset.prod_inv_distrib, Finset.prod_inv_distrib, hden ε hε]
  ring

end QED.GradedProof.WI2

end
