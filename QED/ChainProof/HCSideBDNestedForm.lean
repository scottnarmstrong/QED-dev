/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDOuterBound
public import QED.ChainProof.HCSideBDNested
public import QED.ChainProof.RepsIntBDInt
public import QED.ChainProof.RepsIntDBInt
public import QED.Integration.EnergyFirstShift

/-!
# The nested form of the bubble–`δ₃` and `δ₃`–bubble classes

For `s : Fin 2`, the representatives `QED.ChainProof.Enum.repBD s` and `repDB s` are in nested
form with constant `1` (`QED.ChainProof.HCSide.BDNestedForm`), hence have the nested value
`e² outerAt m q² sidePhoton`:

* `bd_nested_joint`, `db_nested_joint`: the value is the joint integral of
  `nestedF P (bdOuter …)` (resp. `dbOuter`), which is jointly integrable (the substitution
  `(ℓ₀, ℓ₁) ↦ (p - ℓ₁, ℓ₀ + ℓ₁)` of determinant `1` takes the routing of the value to the nested
  routing);
* `bdNestedForm_of_outer`: integrating the inner loop in closed form
  (`jointEnergyFirstIntegral_nestedF`) and reflecting the photon momentum gives the clause of
  `BDNestedForm` with `r = 1`;
* **`bdNestedForm_repBD`**, **`bdNestedForm_repDB`**, **`repNested_repBD`**,
  **`repNested_repDB`**.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
  QED.ChainProof.Enum QED.ChainProof.RepsInt QED.ChainProof.HCValue
open QED.TwoLoop.VPHalfAtAssembly (vpT vpT_neg)
open QED.TwoLoop.VPHalfAt (vpLoopEps vpExtraEps)
open QED.TwoLoop.VPUnitNested (EFInt)
open QED.OneLoop (energyFirstIntegral energyFirstIntegral_neg_eq_self)
open QED.TwoLoop.JointIntegralInvariance (jointEnergyFirstIntegral_comp_matrix_add)

/-! ### Reflection -/

theorem neg_finCons (t : ℝ) (v : Fin 3 → ℝ) :
    -(Fin.cons t v : Fin 4 → ℝ) = Fin.cons (-t) (-v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Both stages of the energy-first integrability are invariant under `k ↦ -k`. -/
theorem efInt_comp_neg {F : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) : EFInt fun k => F (-k) := by
  refine ⟨fun v => ?_, ?_⟩
  · simp only [neg_finCons]
    exact (hF.1 (-v)).comp_neg
  · simp only [neg_finCons]
    have h : (fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons (-t) (-v))) =
        fun v => (fun w : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t w)) (-v) :=
      funext fun v => MeasureTheory.integral_neg_eq_self (fun t : ℝ => F (Fin.cons t (-v))) _
    rw [h]
    exact hF.2.comp_neg

theorem bdChain_neg (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) :
    bdChain mγ Λ ε δ₃ A B (-k) = bdChain mγ Λ ε δ₃ A B k := by
  funext ν ρ
  simp only [bdChain, photonPropagator_neg', vpT_neg, photonCtFactor_neg]

/-! ### From the nested routing to the nested form -/

/-- **The clause of `BDNestedForm` with `r = 1`** from an outer factor in the nested routing. -/
theorem bdNestedForm_of_outer {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (P : Params) (hA : ChainAdmissible P) (p' p : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε)
    (μ α β : Fin 4) (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hval : classV C { P with ε := ε } p' p μ α β =
      (1 / I) * QED.TwoLoop.jointEnergyFirstIntegral 2 (nestedF { P with ε := ε } O))
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 (nestedF { P with ε := ε } O))
    (hc : ∀ w ρ σ, Continuous fun t => O (Fin.cons t w) ρ σ)
    (hd : ∀ w ρ σ, QED.TwoLoop.NestedVPFubiniBound.DecaysLike
      (fun t => O (Fin.cons t w) ρ σ) 10)
    (hout : ∀ k, outerF { P with ε := ε } O k =
      vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' - k))
        (QED.OneLoop.electronPropagator P.m ε (p - k))
        (bdChain P.mγ P.Λ ε P.δ₃ (I * vpLoopEps P ε (Minkowski.dot k k))
          ((ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k)) k) α β) :
    classV C { P with ε := ε } p' p μ α β =
        (((1 : ℝ) : ℂ) / I) * energyFirstIntegral (fun k => bdIntegrand P p' p μ ε k α β) ∧
      EFInt (fun k => bdIntegrand P p' p μ ε k α β) := by
  obtain ⟨hJ, hE⟩ := jointEnergyFirstIntegral_nestedF (P := { P with ε := ε }) hA.hm hA.hM₁
    hA.hM₂ hA.hPV₁ hA.hPV₂ hε O hc hd hF
  have hfun : outerF { P with ε := ε } O = fun k => bdIntegrand P p' p μ ε (-k) α β := by
    funext k
    rw [hout]
    unfold bdIntegrand
    have hk : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by simp [Minkowski.dot]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, hk, bdChain_neg]
  rw [hfun] at hJ hE
  refine ⟨?_, by simpa only [neg_neg] using efInt_comp_neg hE⟩
  rw [hval, hJ, ofReal_one]
  exact congrArg _ (energyFirstIntegral_neg_eq_self fun k => bdIntegrand P p' p μ ε k α β)

/-! ### The value in the nested routing -/

/-- The substitution from the routing of the value to the nested routing. -/
def nestMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 1]

theorem det_nestMat : IsUnit nestMat.det := by
  rw [nestMat, Matrix.det_fin_two]
  simp

theorem fin2_eta (ℓ : Fin 2 → Fin 4 → ℝ) : ℓ = ![ℓ 0, ℓ 1] := by
  funext i
  fin_cases i <;> rfl

/-- **The value of `repBD s` in the nested routing**, and its joint integrability. -/
theorem bd_nested_joint (s : Fin 2) (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    QED.WickModel.contractionValue₂ P (repBD s) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => α) (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (nestedF P (bdOuter P p (p' - p) α β μ)) ∧
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (nestedF P (bdOuter P p (p' - p) α β μ)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
    (add_sub_cancel p p').symm
  have hH : nestedF P (bdOuter P p (p' - p) α β μ) = fun ℓ =>
      (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (repBD s) (fun _ => p) (fun _ => p' - p)
          (lineMomentum₂ (repBD s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ)
          (fun _ => α) (fun _ => β) (fun _ => μ))
        ((fun s => ∑ r, nestMat s r • ℓ r) + ![p, 0]) := by
    funext ℓ
    have h1 := bd_integrand_eq s P (fun _ => p) (fun _ => p' - p) (ℓ 0) (ℓ 1) (fun _ => α)
      (fun _ => β) (fun _ => μ)
    rw [← fin2_eta] at h1
    refine h1.symm.trans ?_
    beta_reduce
    rw [lineMomentum₂_repBD (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) s
      hmom]
    congr 3
    · funext ν
      simp [nestMat, Fin.sum_univ_two]
      ring
    · funext ν
      simp [nestMat, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · refine (QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_repBD s) _ _ _ _ _
      _).trans ?_
    rw [hH]
    exact (jointEnergyFirstIntegral_comp_matrix_add 2 _ nestMat det_nestMat ![p, 0]).symm
  · have h := chainValueIntegrable_repBD P (fun _ => α) (fun _ => β) (fun _ => μ) hε hc₁ hc₂
      (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom s
    unfold ChainValueIntegrable at h
    rw [loopCount_repBD] at h
    rw [hH]
    exact QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 2 _ nestMat det_nestMat
      _ h

/-- **The value of `repDB s` in the nested routing**, and its joint integrability. -/
theorem db_nested_joint (s : Fin 2) (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    QED.WickModel.contractionValue₂ P (repDB s) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => α) (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (nestedF P (dbOuter P p (p' - p) α β μ)) ∧
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (nestedF P (dbOuter P p (p' - p) α β μ)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
    (add_sub_cancel p p').symm
  have hH : nestedF P (dbOuter P p (p' - p) α β μ) = fun ℓ =>
      (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (repDB s) (fun _ => p) (fun _ => p' - p)
          (lineMomentum₂ (repDB s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ)
          (fun _ => α) (fun _ => β) (fun _ => μ))
        ((fun s => ∑ r, nestMat s r • ℓ r) + ![p, 0]) := by
    funext ℓ
    have h1 := db_integrand_eq s P (fun _ => p) (fun _ => p' - p) (ℓ 0) (ℓ 1) (fun _ => α)
      (fun _ => β) (fun _ => μ)
    rw [← fin2_eta] at h1
    refine h1.symm.trans ?_
    beta_reduce
    rw [lineMomentum₂_repDB (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) s
      hmom]
    congr 3
    · funext ν
      simp [nestMat, Fin.sum_univ_two]
      ring
    · funext ν
      simp [nestMat, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · refine (QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_repDB s) _ _ _ _ _
      _).trans ?_
    rw [hH]
    exact (jointEnergyFirstIntegral_comp_matrix_add 2 _ nestMat det_nestMat ![p, 0]).symm
  · have h := chainValueIntegrable_repDB P (fun _ => α) (fun _ => β) (fun _ => μ) hε hc₁ hc₂
      (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom s
    unfold ChainValueIntegrable at h
    rw [loopCount_repDB] at h
    rw [hH]
    exact QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 2 _ nestMat det_nestMat
      _ h

/-! ### The nested forms -/

theorem classV_eq_contractionValue₂ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (P : Params) (p' p : Fin 4 → ℝ) (μ α β : Fin 4) :
    classV C P p' p μ α β = (1 / I) * QED.WickModel.contractionValue₂ P C (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) := by
  rw [classV, Matrix.of_apply]
  rfl

/-- **`repBD s` is in nested form with constant `1`.** -/
theorem bdNestedForm_repBD (s : Fin 2) : BDNestedForm (repBD s) 1 := by
  intro P hA p' p _
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) μ α β
  obtain ⟨hv, hF⟩ := bd_nested_joint s { P with ε := ε } hε hA.hPV₁ hA.hPV₂ p' p α β μ
  refine bdNestedForm_of_outer (repBD s) P hA p' p hε μ α β _ ?_ hF
    (fun w ρ σ => continuous_bdOuter { P with ε := ε } hε p (p' - p) α β μ w ρ σ)
    (fun w ρ σ => decaysLike_bdOuter { P with ε := ε } hε p (p' - p) α β μ w ρ σ) fun k => ?_
  · rw [classV_eq_contractionValue₂, hv]
  · rw [outerF_bdOuter, add_sub_cancel]
    rfl

/-- **`repDB s` is in nested form with constant `1`.** -/
theorem bdNestedForm_repDB (s : Fin 2) : BDNestedForm (repDB s) 1 := by
  intro P hA p' p _
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) μ α β
  obtain ⟨hv, hF⟩ := db_nested_joint s { P with ε := ε } hε hA.hPV₁ hA.hPV₂ p' p α β μ
  refine bdNestedForm_of_outer (repDB s) P hA p' p hε μ α β _ ?_ hF
    (fun w ρ σ => continuous_dbOuter { P with ε := ε } hε p (p' - p) α β μ w ρ σ)
    (fun w ρ σ => decaysLike_dbOuter { P with ε := ε } hε p (p' - p) α β μ w ρ σ) fun k => ?_
  · rw [classV_eq_contractionValue₂, hv]
  · rw [outerF_dbOuter, add_sub_cancel]
    rfl

/-- **The nested value of `repBD s`**: `e² outerAt m q² sidePhoton`. -/
theorem repNested_repBD (s : Fin 2) : RepNested (repBD s) sidePhoton := by
  have h := repNested_of_bdNestedForm (bdNestedForm_repBD s)
  simpa only [one_mul] using h

/-- **The nested value of `repDB s`**: `e² outerAt m q² sidePhoton`. -/
theorem repNested_repDB (s : Fin 2) : RepNested (repDB s) sidePhoton := by
  have h := repNested_of_bdNestedForm (bdNestedForm_repDB s)
  simpa only [one_mul] using h

end QED.ChainProof.HCSide

end
