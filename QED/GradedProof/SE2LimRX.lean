/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2PositivityTwo
public import QED.Integration.TwoLoopClassLimitCubic

/-!
# The classes `R`, `X`: the `ε → 0⁺` limit

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L1.

* `exists_tendsto_contractionValue₂_gggg`: for a two-loop contraction of four `gauge` vertices
  with parametric data of seven lines (as in `jointEnergyFirstIntegrable_gggg`), if `V ≥ c > 0`
  on the simplex, the value (T₁₀) converges as `ε → 0⁺`. The integrand at `ε > 0` is
  `P(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹` with the same cubic `P` for every `ε` (the amplitude numerator does not read
  `ε`), so `QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_cubic` applies.
* `exists_tendsto_contractionValue₂_repR`, `…_repX`: below the threshold `-(m + ν)²`, with
  `0 < ν ≤ min(m_γ, Λ)` (and `ν ≤ 2m` for `X`), by `symanzikV_R_ge`, `symanzikV_X_ge`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)
open Complex Filter Topology

/-- **The limit of a two-loop contraction of four `gauge` vertices from parametric data.** -/
theorem exists_tendsto_contractionValue₂_gggg (C : Contraction 1 0 k_gggg)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 2)
    (hcard : Fintype.card (FermionLine C) = 3) (a : Fin 7 → Fin 2 → ℤ)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} a) (Q : Params)
    (p : Fin 4 → ℝ) (pp : Fin 7 → Fin 4 → ℝ) (e : FermionLine C → Fin 7)
    (he : Function.Injective e) (hE : ∀ f, e f ∈ ({0, 1, 2} : Finset (Fin 7)))
    (hk : ∀ ℓ f, lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) =
      lineMomentum (castLoopMatrix a) pp (e f) ℓ)
    (hden : ∀ ε : ℝ, ∀ ℓ, amplitudeDenominator { Q with ε := ε } C (zeroFlavoring k_gggg)
      (lineMomentum₂ C ![p] ![p] ![] ℓ) =
        ∏ i, (lineDenom (castLoopMatrix a) pp (massesSE Q) ε i ℓ)⁻¹)
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin 7 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix a) z ≠ 0 → c ≤ symanzikV (castLoopMatrix a) pp (massesSE Q) z)
    (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } C ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  set κ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ with hκ
  have haff : ∀ f : FermionLine C, IsLoopAffine fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f) :=
    fun f => by
      rw [show (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ (.inl f)) =
        lineMomentum (castLoopMatrix a) pp (e f) from funext fun ℓ => hk ℓ f]
      exact isLoopAffine_lineMomentum _ _ _
  have hpoly := isLoopPoly_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
    (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ) haff ![α] ![β] ![]
  rw [hcard] at hpoly
  obtain ⟨P, hq, hP⟩ := IsLoopPoly.exists_loopQuartic_cubic (hpoly.const_mul κ)
  have hB : RefinedBound (castLoopMatrix a) {0, 1, 2} 4 P.eval := by
    rw [hP]
    have h := (refinedBound_amplitudeNumerator_gggg Q C (zeroFlavoring k_gggg) ![p] ![]
      (castLoopMatrix a) pp (fun ℓ => lineMomentum₂ C ![p] ![p] ![] ℓ) e he hk ![α] ![β]
      ![]).const_mul κ
    rw [hcard] at h
    refine h.mono ?_ (by norm_num)
    intro i hi
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hi
    exact hE f
  have hT := QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_cubic P
    (castLoopMatrix a) pp (massesSE Q) hq (le_refl 6)
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB hc hV
  refine ⟨_, hT.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold contractionValue₂
  rw [hL]
  congr 1
  funext ℓ
  have hnum : amplitudeNumerator { Q with ε := ε } C (zeroFlavoring k_gggg) ![p] ![]
      (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] =
      amplitudeNumerator Q C (zeroFlavoring k_gggg) ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] := rfl
  rw [regulatedAmplitude₂_eq_zeroFlavoring _ hcyc,
    contractionAmplitude₂_eq { Q with ε := ε } hε.ne', hden ε, hnum,
    show P.eval ℓ = κ * amplitudeNumerator Q C (zeroFlavoring k_gggg) ![p] ![]
      (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] from congrFun hP ℓ]
  ring

theorem min_one_mul_pos {s T c : ℝ} (hT : 0 < T) (hc : 0 < c) (hs : -T ^ 2 < s) :
    0 < min 1 (1 + s / T ^ 2) * c := by
  refine mul_pos (lt_min one_pos ?_) hc
  have hT2 : 0 < T ^ 2 := by positivity
  have h1 : 0 < T ^ 2 + s := by linarith
  calc (0 : ℝ) < (T ^ 2 + s) / T ^ 2 := by positivity
    _ = 1 + s / T ^ 2 := by field_simp

/-- **The limit of the rainbow class `R`** exists below threshold. -/
theorem exists_tendsto_contractionValue₂_repR {Q : Params} (hm : 0 < Q.m) {ν : ℝ}
    (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ}
    (hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repR ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨i1, i2, i3, -, -⟩ := idxR_apply
  refine exists_tendsto_contractionValue₂_gggg repR
    (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repR (by decide +kernel) aR
    intCrit_R Q p (ppR p) (fun f => idxR (.inl f)) ?_ ?_
    (fun ℓ f => by rw [lineMomentum₂_repR]; rfl)
    (fun ε ℓ => r_denominator { Q with ε := ε } p ℓ)
    (min_one_mul_pos (by positivity) (lt_min (by positivity) (by positivity)) hs)
    (fun z hz hz1 hU => symanzikV_R_ge Q hm hν0 hν hs hz hz1 hU) α β
  · intro f g h
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases r_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases r_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

/-- **The limit of the crossed class `X`** exists below threshold. -/
theorem exists_tendsto_contractionValue₂_repX {Q : Params} (hm : 0 < Q.m) {ν : ℝ}
    (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * Q.m) {p : Fin 4 → ℝ}
    (hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repX ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨i1, i2, i3, -, -⟩ := idxX_apply
  refine exists_tendsto_contractionValue₂_gggg repX
    (sameCycle_of_pow (n := 5) (by decide +kernel)) loopCount_repX (by decide +kernel) aX
    intCrit_X Q p (ppX p) (fun f => idxX (.inl f)) ?_ ?_
    (fun ℓ f => by rw [lineMomentum₂_repX]; rfl)
    (fun ε ℓ => x_denominator { Q with ε := ε } p ℓ)
    (min_one_mul_pos (by positivity) (lt_min (by positivity) (by positivity)) hs)
    (fun z hz hz1 hU => symanzikV_X_ge Q hm hν0 hν hν2 hs hz hz1 hU) α β
  · intro f g h
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;>
      rcases x_fermionLine_cases g with rfl | rfl | rfl <;>
      simp_all
  · intro f
    rcases x_fermionLine_cases f with rfl | rfl | rfl <;> simp [i1, i2, i3]

end QED.GradedProof.SE2

end
