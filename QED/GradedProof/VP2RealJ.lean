/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2RealLim
public import QED.GradedProof.VP2VGen

/-!
# Two-loop vacuum-polarization families with a conjugation phase

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `VPReal`; the phase counterpart of `QED/GradedProof/VP2VGen.lean`.

* `VPJC T d F`: `F` is `VPJ T` and, for every multiplier `h(ε)` with a real limit, the family
  `h(ε) ∫ F` has a limit with phase `d` (`HasConjLim`). Closed under sums, multiplication by
  convergent functions with real limits, real constants and pointwise equality at `ε > 0`.
* `vpjc_piece`: the pieces of `QED.GradedProof.VP2.vpj_piece` whose numerator satisfies
  `N̄ = d N` at real momenta are `VPJC (2 m₀) d`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2Real

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2 QED.GradedProof.VP2

/-- **Two-loop families with a phase-`d` limit** for every multiplier with a real limit. -/
def VPJC (T : ℝ) (d : ℂ) (F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) :
    Prop :=
  VPJ T F ∧ ∀ (h : ℝ → ℂ) (h₀ : ℝ), Tendsto h (𝓝[>] 0) (𝓝 (h₀ : ℂ)) →
    HasConjLim T d fun ε k i j => h ε * QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j

namespace VPJC

variable {T : ℝ} {d : ℂ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : VPJC T d F) (hG : VPJC T d G) :
    VPJC T d fun ε k ℓ i j => F ε k ℓ i j + G ε k ℓ i j := by
  refine ⟨hF.1.add hG.1, fun h h₀ hh => ((hF.2 h h₀ hh).add (hG.2 h h₀ hh)).congr
    fun k _ i j => ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (hF.1.2 ε hε k i j)
    (hG.1.2 ε hε k i j), mul_add]

theorem mul (hF : VPJC T d F) {c : ℝ → ℂ} {c₀ : ℝ} (hc : Tendsto c (𝓝[>] 0) (𝓝 (c₀ : ℂ))) :
    VPJC T d fun ε k ℓ i j => c ε * F ε k ℓ i j := by
  refine ⟨hF.1.mul hc, fun h h₀ hh => ?_⟩
  have hm : Tendsto (fun ε => h ε * c ε) (𝓝[>] 0) (𝓝 ((h₀ * c₀ : ℝ) : ℂ)) := by
    rw [ofReal_mul]
    exact hh.mul hc
  refine (hF.2 (fun ε => h ε * c ε) _ hm).congr fun k _ i j => ?_
  filter_upwards with ε
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul, mul_assoc]

theorem const_mul (hF : VPJC T d F) (c : ℝ) : VPJC T d fun ε k ℓ i j => (c : ℂ) * F ε k ℓ i j :=
  hF.mul (c := fun _ => (c : ℂ)) tendsto_const_nhds

theorem congr (hF : VPJC T d F)
    (e : ∀ ε : ℝ, 0 < ε → ∀ k ℓ i j, F ε k ℓ i j = G ε k ℓ i j) : VPJC T d G := by
  refine ⟨hF.1.congr e, fun h h₀ hh => (hF.2 h h₀ hh).congr fun k _ i j => ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [show (fun ℓ => F ε k ℓ i j) = fun ℓ => G ε k ℓ i j from funext (e ε hε k · i j)]

theorem zero : VPJC T d fun _ _ _ _ _ => 0 := by
  refine ⟨VPJ.zero, fun h h₀ hh => (HasConjLim.zero).congr fun k _ i j => ?_⟩
  filter_upwards with ε
  simp [QED.TwoLoop.jointEnergyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, VPJC T d (F a)) : VPJC T d fun ε k ℓ i j => ∑ a ∈ s, F a ε k ℓ i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : VPJC T d fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- The joint integral of a `VPJC` family has a limit with phase `d`. -/
theorem hasConjLim (hF : VPJC T d F) :
    HasConjLim T d fun ε k i j => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j :=
  (hF.2 (fun _ => 1) 1 (by rw [ofReal_one]; exact tendsto_const_nhds)).congr fun _ _ _ _ => by
    filter_upwards with ε
    rw [one_mul]

end VPJC

/-- **A piece over a shape of a vacuum-polarization routing with a phase-`d` numerator** is
`VPJC (2 m₀) d`. -/
theorem vpjc_piece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
      |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k i j, IsLoopPoly 2 (n - 3) fun ℓ => N k ℓ i j)
    (hB : ∀ k i j, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 fun ℓ => N k ℓ i j)
    (hcov : TCov2 N) {d : ℕ} (hk : ∀ ℓ i j, IsLoopPoly 1 d fun y => N (y 0) ℓ i j)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hf : ∀ i, sh i ≠ 4 → m₀ ≤ Ms i) (h0 : ∀ i, 0 ≤ Ms i)
    {cc : ℝ} (hc : 0 < cc) (hMc : ∀ i, cc ≤ Ms i ^ 2) {ph : ℂ}
    (hph : ∀ k ℓ i j, starRingEnd ℂ (N k ℓ i j) = ph * N k ℓ i j) :
    VPJC (2 * m₀) ph fun ε k ℓ i j => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l) ℓ))⁻¹ := by
  refine ⟨vpj_piece base c y₁ y₂ hflow hn sh Ms hcrit N hpoly hB hcov hk hm₀ hf h0 hc hMc,
    fun h h₀ hh => ?_⟩
  have hcrit' := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  have h6 : 6 ≤ n := by omega
  let D : SEData :=
    { m := n
      α := castLoopMatrix fun i => base (sh i)
      cs := fun i => c (sh i)
      M := Ms
      E := E
      hm := h6
      hcrit := hcrit' }
  have hpos : ∀ p : Fin 4 → ℝ, -(2 * m₀) ^ 2 < Minkowski.dot p p →
      0 < min 1 (1 + Minkowski.dot p p / (2 * m₀) ^ 2) * cc := fun p hs => by
    refine mul_pos (lt_min one_pos ?_) hc
    have hT2 : 0 < (2 * m₀) ^ 2 := by positivity
    have h1 : 0 < (2 * m₀) ^ 2 + Minkowski.dot p p := by linarith
    calc (0 : ℝ) < ((2 * m₀) ^ 2 + Minkowski.dot p p) / (2 * m₀) ^ 2 := by positivity
      _ = 1 + Minkowski.dot p p / (2 * m₀) ^ 2 := by field_simp
  let P : VPPiece (2 * m₀) :=
    { D := D
      N := N
      hQ := fun p i j => by
        obtain ⟨Q, hq, hb, he⟩ := good_of_poly hn (hpoly p i j) (hB p i j)
        exact ⟨Q, ⟨hq, hb⟩, he⟩
      hV := fun p hp => ⟨_, hpos p hp, fun z hz hz1 hU =>
        symanzikV_vp_ge base c y₁ y₂ hflow sh Ms hm₀ hf h0 hc hMc hp hz hz1 hU⟩
      hcov := fun a ha p ℓ μ ν => hcov.reflect ha p ℓ μ ν }
  exact VPPiece.hasConjLim P hph hh fun p _ i j => Eventually.of_forall fun ε => rfl

end QED.GradedProof.VP2Real

end
