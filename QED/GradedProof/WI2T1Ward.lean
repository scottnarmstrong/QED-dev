/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2FTwR
public import QED.GradedProof.WI2OneLoop
public import QED.GradedProof.WI2SEClass
public import QED.GradedProof.WI2P
public import QED.GradedProof.WI2VtxVP
public import QED.GradedProof.WI2VtxX
public import QED.GradedProof.WI2V
public import QED.GradedProof.V5ZeroTotal
public import QED.TwoLoop.LimitMirrorVertex
public import QED.TwoLoop.PauliZeroLimitCt

/-!
# The Ward identity of one T1 parameter set

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57). For
one admissible T1 parameter set `Q` (`V5Zero.Adm m₀ Q`) with `δ₁ = δ₂` and `e ≠ 0`, between
on-shell spinors:

`d/dt|₁ w seLim(t p) u = -(1/e) ∑_μ p_μ w vtxSum(p)^μ u`,

where `seLim` is the `ε → 0⁺` limit of the signed order-`4` class sum
(`R + X - V + F + P0 + P1 + C1 + C2`, `seClassSum`) and `vtxSum` is `i` times the order-`5` vertex
limit at zero momentum transfer (the seven non-Furry classes with their signs and the seven
counterterm classes, `V5Zero.Lim.eq_classLimits_of_isVertexOrderFiveLimit`).

The pairing is class by class: `R ↔ S₊, L, S₋`, `X ↔ C₊, X, C₋`, `V ↔ VP`, `F ↔ d₂ in/out`,
`P0, P1 ↔ d₃ slots`, and the counterterm-vertex term of `F` with `C1, C2` against the three `δ₁`
classes through the one-loop Ward identity (`WI2OneLoop`, `e_mul_twR_dF`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.TwoLoop.Relabel QED.TwoLoop.Enumeration
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion

/-- The `ε → 0⁺` limit of the T1 class sum without the two `δ₁` classes. -/
noncomputable def seLimNC (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  cRX Q * (dR Q).pvF (fun ℓ => (dR Q).chN eRX (wR Q) Q.m p ℓ α β) ((dR Q).mom p) +
    cRX Q * (dX Q).pvF (fun ℓ => (dX Q).chN eRX (wX Q) Q.m p ℓ α β) ((dX Q).mom p) -
    vPV Q p α β +
    (auxLimit Q.m)⁻¹ * (kappaSE Q.e *
      (dF Q).pvF (fun ℓ => (dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p ℓ α β)
        ((dF Q).mom p)) +
    (auxLimit Q.m)⁻¹ * (kappaSE Q.e *
      (dP Q).pvF (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β)
        ((dP Q).mom p)) +
    (auxLimit Q.m)⁻¹ * (kappaSE Q.e *
      (dP Q).pvF (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β)
        ((dP Q).mom p))

/-- **The `ε → 0⁺` limit of the T1 order-`4` class sum.** -/
noncomputable def seLim (Q : Params) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (seLimNC Q p) + (2 * (Q.δ₁ : ℂ)) • seOneLoopLimit Q p

/-- **`i` times the T1 order-`5` vertex limit at `p' = p`**, by classes. -/
noncomputable def vtxSum (Q : Params) (p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (∑ c ∈ QED.TwoLoop.Furry.nonFurry, (c.sign : ℂ) • classLimitV c Q p p μ) +
    ∑ c ∈ (Finset.univ : Finset CtClass), (1 : ℂ) • ctLimitV c Q p p μ

/-- The contraction of an open class limit. -/
noncomputable def sOpen (c : Class5) (Q : Params) (r p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV c Q p p μ α β

/-- The contraction of a counterterm class limit. -/
noncomputable def sCt (c : CtClass) (Q : Params) (r p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ctLimitV c Q p p μ α β

/-- The contraction of the one-loop vertex limit. -/
noncomputable def sOne (Q : Params) (r p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * vOne Q p μ α β

theorem sOne_def (Q : Params) (r p : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * vOne Q p μ α β = sOne Q r p α β := by
  rw [sOne]

theorem sum_ctClass_eq (f : CtClass → ℂ) :
    ∑ c, f c = f .d2In + f .d2Out + f .d3Slot0 + f .d3Slot1 + f .d1At1 + f .d1At2 + f .d1At3 := by
  rw [show (Finset.univ : Finset CtClass) =
    {.d2In, .d2Out, .d3Slot0, .d3Slot1, .d1At1, .d1At2, .d1At3} from rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  ring

theorem sum_lower_vtxSum_apply (Q : Params) (r p : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * vtxSum Q p μ α β =
      sOpen .L Q r p α β + sOpen .X Q r p α β + (sOpen .Cp Q r p α β + sOpen .Cm Q r p α β) +
        (sOpen .Sp Q r p α β + sOpen .Sm Q r p α β) - sOpen .VP Q r p α β +
        (sCt .d2In Q r p α β + sCt .d2Out Q r p α β + sCt .d3Slot0 Q r p α β +
          sCt .d3Slot1 Q r p α β + sCt .d1At1 Q r p α β + sCt .d1At2 Q r p α β +
          sCt .d1At3 Q r p α β) := by
  simp only [vtxSum, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, one_mul,
    QED.TwoLoop.LimitMirror.sum_nonFurry fun c => classLimitV c Q p p _ α β, sum_ctClass_eq,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sOpen, sCt]

/-- The `δ₁` class limits at `p' = p` are `δ₁` times the one-loop vertex limit. -/
theorem ctLimitV_d1_apply {c : CtClass} (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3)
    (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0) (μ α β : Fin 4) :
    ctLimitV c Q p p μ α β = (Q.δ₁ : ℂ) * vOne Q p μ α β := by
  rw [QED.TwoLoop.PauliZeroLimit.ctLimitV_d1_eq_vertexOneLoop hc Q hm hmγ hΛ hp hp hp0 hp0]
  simp only [Matrix.smul_apply, smul_eq_mul,
    QED.OneLoop.VertexLimit.vertexOneLoop_eq_limit hm hmγ hΛ hp hp hp0 hp0, Matrix.of_apply, vOne]
  field_simp

theorem sCt_d1 {c : CtClass} (hc : c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3)
    (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0) (r : Fin 4 → ℝ) (α β : Fin 4) :
    sCt c Q r p α β = (Q.δ₁ : ℂ) * sOne Q r p α β := by
  simp only [sCt, sOne, ctLimitV_d1_apply hc Q hm hmγ hΛ hp hp0, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The Ward derivative of the classes other than the `δ₁` ones**, entrywise. -/
theorem hasDerivAt_seLimNC (Q : Params) (he : Q.e ≠ 0) {m₀ : ℝ} (h : V5Zero.Adm m₀ Q)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0) (α β : Fin 4) :
    HasDerivAt (fun t : ℝ => seLimNC Q (t • p) α β)
      (-(1 / (Q.e : ℂ)) * (sOpen .L Q p p α β + sOpen .X Q p p α β +
        (sOpen .Cp Q p p α β + sOpen .Cm Q p p α β) + (sOpen .Sp Q p p α β + sOpen .Sm Q p p α β) -
        sOpen .VP Q p p α β + (sCt .d2In Q p p α β + sCt .d2Out Q p p α β +
          sCt .d3Slot0 Q p p α β + sCt .d3Slot1 Q p p α β)) +
        1 / (Q.e : ℂ) * (-(Q.δ₂ : ℂ) * sOne Q p p α β)) 1 := by
  have hm : 0 < Q.m := h.hm₀.trans_le h.hm
  set ν : ℝ := min (min Q.mγ Q.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min h.hmγ h.hΛ) (by linarith [h.hm₀])
  have hν : ν ≤ min Q.mγ Q.Λ := min_le_left _ _
  have hν2 : ν ≤ 2 * m₀ := min_le_right _ _
  have hν2' : ν ≤ 2 * Q.m := hν2.trans (by linarith [h.hm])
  have hr : -(Q.m + ν) ^ 2 < Minkowski.dot ((1 : ℝ) • p) ((1 : ℝ) • p) := by
    rw [one_smul, hp]
    nlinarith
  have hR := hasDerivAt_repR_wt Q hm hν0 hν p hr α β
  have hX := hasDerivAt_repX_wt Q hm hν0 hν hν2' p hr α β
  have hV := hasDerivAt_vPV_wt h.hm₀ h.hm h.hM₁ h.hM₂ hν0 hν hν2 p hr α β
  have hF := hasDerivAt_dF_wt Q hm hν0 hν p hr α β
  have hP := hasDerivAt_dP_wt Q hm hν0 hν p hr α β
  have H := (((((hR.const_mul (cRX Q)).add (hX.const_mul (cRX Q))).sub hV).add
    ((hF.const_mul (kappaSE Q.e)).const_mul (auxLimit Q.m)⁻¹)).add
    ((hP.const_mul (kappaSE Q.e)).const_mul (auxLimit Q.m)⁻¹)).add
    ((hP.const_mul (kappaSE Q.e)).const_mul (auxLimit Q.m)⁻¹)
  convert H using 1
  · rfl
  simp only [one_smul]
  have hmγ := h.hmγ
  have hΛ := h.hΛ
  simp only [sOne, vOne, Matrix.of_apply]
  rw [← e_mul_twR_dF Q hm hmγ hΛ hp hp0 p α β]
  simp only [sOpen, sCt, sum_lower_classLimitV_L Q hm hmγ hΛ hp,
    sum_lower_classLimitV_X Q hm hmγ hΛ hp,
    sum_lower_classLimitV_Cp Q hm hmγ hΛ hp, sum_lower_classLimitV_Cm Q hm hmγ hΛ hp,
    sum_lower_classLimitV_Sp Q hm hmγ hΛ hp, sum_lower_classLimitV_Sm Q hm hmγ hΛ hp,
    sum_lower_classLimitV_VP h.hc₁ h.hc₂ h.hm₀ h.hm h.hM₁ h.hM₂ hν0 hν hν2 hp,
    sum_lower_ctLimitV_d2In Q hm hmγ hΛ hp, sum_lower_ctLimitV_d2Out Q hm hmγ hΛ hp,
    sum_lower_ctLimitV_d3Slot0 Q hm hmγ hΛ hp, sum_lower_ctLimitV_d3Slot1 Q hm hmγ hΛ hp,
    Fin.sum_univ_three, Fin.sum_univ_two]
  have he : (Q.e : ℂ) ≠ 0 := by exact_mod_cast he
  field_simp
  ring

/-- A contracted family of sandwiches as a double sum over the entries. -/
theorem sum_mul_sandwich (c : Fin 4 → ℂ) (M : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (u w : Fin 4 → ℂ) :
    ∑ μ, c μ * (w ⬝ᵥ (M μ *ᵥ u)) = ∑ α, ∑ β, w α * ((∑ μ, c μ * M μ α β) * u β) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => by ring

/-- **The Ward identity of one T1 parameter set**, between on-shell spinors. -/
theorem hasDerivAt_sandwich_seLim (Q : Params) (he : Q.e ≠ 0) (hδ : Q.δ₁ = Q.δ₂) {m₀ : ℝ}
    (h : V5Zero.Adm m₀ Q) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0 : 0 < p 0)
    {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((Q.m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p = -((Q.m : ℂ) • w)) :
    HasDerivAt (fun t : ℝ => w ⬝ᵥ (seLim Q (t • p) *ᵥ u))
      (-(1 / (Q.e : ℂ)) * ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (vtxSum Q p μ *ᵥ u)))
      1 := by
  have hm : 0 < Q.m := h.hm₀.trans_le h.hm
  have hf : (fun t : ℝ => w ⬝ᵥ (seLim Q (t • p) *ᵥ u)) = fun t =>
      ∑ α, ∑ β, w α * (seLimNC Q (t • p) α β * u β) +
        2 * (Q.δ₁ : ℂ) * (w ⬝ᵥ (seOneLoopLimit Q (t • p) *ᵥ u)) := by
    funext t
    simp only [seLim, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
    congr 1
    simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [hf]
  have hNC := HasDerivAt.fun_sum (u := Finset.univ) fun α _ => HasDerivAt.fun_sum
    (u := Finset.univ) fun β _ =>
      ((hasDerivAt_seLimNC Q he h hp hp0 α β).mul_const (u β)).const_mul (w α)
  have hC := (hasDerivAt_sandwich_seOneLoopLimit_eq Q he hm h.hmγ h.hΛ hp hp0 hu hw).const_mul
    (2 * (Q.δ₁ : ℂ))
  convert hNC.add hC using 1
  rw [sum_mul_sandwich, sum_mul_sandwich (fun μ => ((Minkowski.lower p μ : ℝ) : ℂ)) (vOne Q p)]
  simp only [sum_lower_vtxSum_apply, sOne_def, sCt_d1 (Or.inl rfl) Q hm h.hmγ h.hΛ hp hp0,
    sCt_d1 (Or.inr (Or.inl rfl)) Q hm h.hmγ h.hΛ hp hp0,
    sCt_d1 (Or.inr (Or.inr rfl)) Q hm h.hmγ h.hΛ hp hp0, hδ]
  generalize sOne Q p p = S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- **The `ε → 0⁺` limit of the T1 class sum** near the shell. -/
theorem tendsto_seClassSum (Q : Params) {m₀ : ℝ} (h : V5Zero.Adm m₀ Q) {p : Fin 4 → ℝ}
    (hs : -(Q.m + min (min Q.mγ Q.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε : ℝ => seClassSum { Q with ε := ε } p α β) (𝓝[>] 0) (𝓝 (seLim Q p α β)) := by
  have hm : 0 < Q.m := h.hm₀.trans_le h.hm
  set ν : ℝ := min (min Q.mγ Q.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min h.hmγ h.hΛ) (by linarith [h.hm₀])
  have hν : ν ≤ min Q.mγ Q.Λ := min_le_left _ _
  have hν2 : ν ≤ 2 * m₀ := min_le_right _ _
  have hν2' : ν ≤ 2 * Q.m := hν2.trans (by linarith [h.hm])
  have hγ : -(Q.m + Q.mγ) ^ 2 < Minkowski.dot p p := lt_of_le_of_lt (by
    have : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
    nlinarith) hs
  have hΛ : -(Q.m + Q.Λ) ^ 2 < Minkowski.dot p p := lt_of_le_of_lt (by
    have : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
    nlinarith) hs
  have hR := (tendsto_repR_wt Q hm hν0 hν hs α β)
  have hX := (tendsto_repX_wt Q hm hν0 hν hν2' hs α β)
  have hV := tendsto_repV_wt h.hc₁ h.hc₂ h.hm₀ h.hm h.hM₁ h.hM₂ hν0 hν hν2 hs α β
  have hF := tendsto_repF_wt Q hm hν0 hν hs α β
  have hP0 := tendsto_repP0_wt Q hm hν0 hν hs α β
  have hP1 := tendsto_repP1_wt Q hm hν0 hν hs α β
  have hC1 := tendsto_contractionValue₂_repC1 hm h.hmγ h.hΛ hγ hΛ α β
  have hC2 := tendsto_contractionValue₂_repC2 hm h.hmγ h.hΛ hγ hΛ α β
  have H := ((((((hR.add hX).sub hV).add hF).add hP0).add hP1).add hC1).add hC2
  convert H using 1
  · rfl
  congr 1
  simp only [seLim, seLimNC, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end QED.GradedProof.WI2

end
