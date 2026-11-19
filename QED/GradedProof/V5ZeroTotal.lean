/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroLimCov

/-!
# Combinations of T1 vertex limits at `q = 0`

Helper level for the vertex input of (G-ex₂) (`QED.GradedProof.GEx2.VertexZeroInput`).

* `Adm m₀ S`: the hypotheses of the relaxed T1 limit (`QED/GradedProof/V5ZeroLim*.lean`): loop
  and open-line masses at least `m₀ > 0`, positive photon regulators, the two Pauli–Villars
  conditions.
* `limV S p`: the `ε → 0⁺` limit (as `limUnder`) of T1's vertex at `p' = p`; it is the limit
  (`isLimit_limV`) and covariant under spinor lifts preserving positive energy (`cov_limV`).
* `combV S a p = ∑_k a_k limV (S k) p`: a real combination; it is covariant (`cov_combV`) and the
  sandwiched vertices converge to it (`tendsto_combV`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.V5Zero

open QED.WickModel (Params)
open QED.TwoLoop.LimitCovariance (IsSpinLift)
open QED.Dirac (vecAct)

/-- The hypotheses of the relaxed T1 vertex limit. -/
structure Adm (m₀ : ℝ) (S : Params) : Prop where
  hm₀ : 0 < m₀
  hm : m₀ ≤ S.m
  hmγ : 0 < S.mγ
  hΛ : 0 < S.Λ
  hM₁ : m₀ ≤ S.M₁
  hM₂ : m₀ ≤ S.M₂
  hc₁ : 1 + S.c₁ + S.c₂ = 0
  hc₂ : S.m ^ 2 + S.c₁ * S.M₁ ^ 2 + S.c₂ * S.M₂ ^ 2 = 0

/-- The `ε → 0⁺` limit of T1's vertex at `p' = p`. -/
noncomputable def limV (S : Params) (p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j =>
    limUnder (𝓝[>] (0 : ℝ)) fun ε => QED.TwoLoop.vertexOrderFive { S with ε := ε } p p μ i j

theorem dot_sub_self (p : Fin 4 → ℝ) : Minkowski.dot (p - p) (p - p) = 0 := by
  simp [Minkowski.dot]

theorem isLimit_limV {m₀ : ℝ} {S : Params} (h : Adm m₀ S) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -S.m ^ 2) (hp0 : 0 < p 0) :
    QED.TwoLoop.IsVertexOrderFiveLimit S p p (limV S p) := by
  obtain ⟨V, hV⟩ := Lim.exists_isVertexOrderFiveLimit S h.hm₀ h.hm h.hmγ h.hΛ h.hM₁ h.hM₂ h.hc₁
    h.hc₂ hp hp hp0 hp0 (dot_sub_self p).ge
  intro μ i j
  simp only [limV, Matrix.of_apply]
  exact tendsto_nhds_limUnder ⟨_, hV μ i j⟩

theorem cov_limV {m₀ : ℝ} {S : Params} (h : Adm m₀ S) {L : Matrix (Fin 4) (Fin 4) ℝ}
    {A B : Matrix (Fin 4) (Fin 4) ℂ} (hL : IsSpinLift L A B) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -S.m ^ 2) (hp0 : 0 < p 0) (hLp0 : 0 < (L *ᵥ p) 0) (μ : Fin 4) :
    A * limV S (L *ᵥ p) μ * B = vecAct L (limV S p) μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -S.m ^ 2 := by rw [hL.dot_mulVec]; exact hp
  exact Lim.conj_vertexLimit_map S h.hm₀ h.hm h.hmγ h.hΛ h.hM₁ h.hM₂ h.hc₁ h.hc₂ hL hp hp hp0
    hp0 hLp0 hLp0 (dot_sub_self p).ge (isLimit_limV h hp hp0) (isLimit_limV h hpL hLp0) μ

/-- A real combination of T1 vertex limits. -/
noncomputable def combV {ι : Type*} [Fintype ι] (S : ι → Params) (a : ι → ℝ)
    (p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => ∑ k, (a k : ℂ) • limV (S k) p μ

theorem cov_combV {ι : Type*} [Fintype ι] {m₀ m : ℝ} {S : ι → Params} (a : ι → ℝ)
    (h : ∀ k, Adm m₀ (S k)) (hm : ∀ k, (S k).m = m) {L : Matrix (Fin 4) (Fin 4) ℝ}
    {A B : Matrix (Fin 4) (Fin 4) ℂ} (hL : IsSpinLift L A B) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (hLp0 : 0 < (L *ᵥ p) 0) (μ : Fin 4) :
    A * combV S a (L *ᵥ p) μ * B = vecAct L (combV S a p) μ := by
  have e : combV S a p = fun ν => ∑ k ∈ Finset.univ, (a k : ℂ) • limV (S k) p ν := rfl
  rw [e, QED.TwoLoop.VertexCovariance.vecAct_finset_sum]
  simp only [combV, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cov_limV (h k) hL ((hm k).symm ▸ hp) hp0 hLp0 μ]

/-- The sandwiched combination of T1 vertices converges to the sandwiched `combV`. -/
theorem tendsto_combV {ι : Type*} [Fintype ι] {m₀ m : ℝ} {S : ι → Params} (a : ι → ℝ)
    (h : ∀ k, Adm m₀ (S k)) (hm : ∀ k, (S k).m = m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4) (u w : Fin 4 → ℂ) :
    Tendsto (fun ε : ℝ => w ⬝ᵥ ((∑ k, (a k : ℂ) •
        QED.TwoLoop.vertexOrderFive { S k with ε := ε } p p μ) *ᵥ u)) (𝓝[>] 0)
      (𝓝 (w ⬝ᵥ (combV S a p μ *ᵥ u))) := by
  have hE : ∀ k, Tendsto (fun ε : ℝ => QED.TwoLoop.vertexOrderFive { S k with ε := ε } p p μ)
      (𝓝[>] 0) (𝓝 (limV (S k) p μ)) := fun k => by
    have hl := isLimit_limV (h k) ((hm k).symm ▸ hp) hp0 μ
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact hl i j
  have hS : Tendsto (fun ε : ℝ => ∑ k, (a k : ℂ) •
      QED.TwoLoop.vertexOrderFive { S k with ε := ε } p p μ) (𝓝[>] 0)
      (𝓝 (combV S a p μ)) :=
    tendsto_finsetSum _ fun k _ => (hE k).const_smul _
  have hc : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => w ⬝ᵥ (M *ᵥ u) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  exact (hc.tendsto _).comp hS

end QED.GradedProof.V5Zero

end
