/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Positivity
public import QED.GradedProof.VP2Kinds
public import QED.GradedProof.SE2FormRX

/-!
# Two-loop vacuum-polarization pieces with covariant limits

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, for the two-loop
classes `VA`, `VB`, `VC`.

* `VPJ T F`: a two-loop integrand family `F ε k ℓ μ ν` is integrable in both stages at `ε > 0`
  and, times any convergent multiplier, its joint integrals have a covariant, null-continuous
  limit (`HasVPLim`) below `-T²`; closed under sums, multipliers and eventual equality.
* `TCov2 N`: tensor covariance `N_{Lk}(Lℓ) = L L N_k(ℓ)` under every spinor lift.
* `vpj_piece`: a numerator with these properties over the lines of a shape `sh` of a
  vacuum-polarization routing (`base`, external coefficients `c`, a flow certificate of
  `QED.GradedProof.VP2.symanzikV_vp_ge`) is `VPJ (2 m₀)`, through
  `QED.GradedProof.VP2.VPPiece`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2

/-! ### Two-loop families with covariant limits -/

/-- Two-loop families with a covariant, null-continuous limit for every convergent multiplier,
integrable in both stages at `ε > 0`. -/
def VPJ (T : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  (∀ (h : ℝ → ℂ) (h₀ : ℂ), Tendsto h (𝓝[>] 0) (𝓝 h₀) →
    HasVPLim T fun ε k i j => h ε * QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j) ∧
  ∀ ε : ℝ, 0 < ε → ∀ k i j, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ε k ℓ i j

namespace VPJ

variable {T : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : VPJ T F) (hG : VPJ T G) : VPJ T fun ε k ℓ i j => F ε k ℓ i j + G ε k ℓ i j := by
  refine ⟨fun h h₀ hh => ((hF.1 h h₀ hh).add (hG.1 h h₀ hh)).congr fun k _ i j => ?_,
    fun ε hε k i j =>
      QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add (hF.2 ε hε k i j)
        (hG.2 ε hε k i j)⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (hF.2 ε hε k i j) (hG.2 ε hε k i j),
    mul_add]

theorem mul (hF : VPJ T F) {c : ℝ → ℂ} {c₀ : ℂ} (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀)) :
    VPJ T fun ε k ℓ i j => c ε * F ε k ℓ i j := by
  refine ⟨fun h h₀ hh => (hF.1 (fun ε => h ε * c ε) _ (hh.mul hc)).congr fun k _ i j => ?_,
    fun ε hε k i j => JEF.const_mul (hF.2 ε hε k i j) (c ε)⟩
  filter_upwards with ε
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul, mul_assoc]

theorem const_mul (hF : VPJ T F) (c : ℂ) : VPJ T fun ε k ℓ i j => c * F ε k ℓ i j :=
  hF.mul (c := fun _ => c) tendsto_const_nhds

theorem congr (hF : VPJ T F)
    (e : ∀ ε : ℝ, 0 < ε → ∀ k ℓ i j, F ε k ℓ i j = G ε k ℓ i j) : VPJ T G := by
  refine ⟨fun h h₀ hh => (hF.1 h h₀ hh).congr fun k _ i j => ?_,
    fun ε hε k i j => JEF.congr (hF.2 ε hε k i j) (e ε hε k · i j)⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [show (fun ℓ => F ε k ℓ i j) = fun ℓ => G ε k ℓ i j from funext (e ε hε k · i j)]

theorem zero : VPJ T fun _ _ _ _ _ => 0 := by
  refine ⟨fun h h₀ hh => (HasVPLim.zero).congr fun k _ i j => ?_, fun _ _ _ _ _ => JEF.zero⟩
  filter_upwards with ε
  simp [QED.TwoLoop.jointEnergyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, VPJ T (F a)) : VPJ T fun ε k ℓ i j => ∑ a ∈ s, F a ε k ℓ i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : VPJ T fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- The joint integral of a `VPJ` family has a covariant, null-continuous limit. -/
theorem hasVPLim (hF : VPJ T F) :
    HasVPLim T fun ε k i j => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j :=
  (hF.1 (fun _ => 1) 1 tendsto_const_nhds).congr fun _ _ _ _ => by
    filter_upwards with ε
    rw [one_mul]

end VPJ

/-! ### Covariance of two-loop numerators -/

/-- A two-loop tensor family `N_k(ℓ)^{μν}` is **covariant** under every spinor lift. -/
def TCov2 (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S S' →
    ∀ k ℓ, N (L *ᵥ k) (loopAct L ℓ) = upperAct L (N k ℓ)

namespace TCov2

variable {N N' : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem loopAct_loopAct {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopAct (QED.Dirac.reflectMatrix a) (loopAct (QED.Dirac.reflectMatrix a) ℓ) = ℓ := by
  funext s
  exact reflectMatrix_mulVec_mulVec ha (ℓ s)

/-- The reflection form of covariance used by `VPPiece`. -/
theorem reflect (hN : TCov2 N) {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    N k ℓ μ ν = ∑ α, ∑ β, ((QED.Dirac.reflectMatrix a μ α : ℝ) : ℂ) *
      ((QED.Dirac.reflectMatrix a ν β : ℝ) : ℂ) *
        N (QED.Dirac.reflect a k) (loopAct (QED.Dirac.reflectMatrix a) ℓ) α β := by
  have h := hN _ _ _ (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha)
    (QED.Dirac.reflect a k) (loopAct (QED.Dirac.reflectMatrix a) ℓ)
  rw [← QED.Dirac.reflectMatrix_mulVec a k, reflectMatrix_mulVec_mulVec ha,
    loopAct_loopAct ha] at h
  rw [QED.Dirac.reflectMatrix_mulVec] at h
  rw [h]
  rfl

theorem add (h : TCov2 N) (h' : TCov2 N') : TCov2 fun k ℓ i j => N k ℓ i j + N' k ℓ i j := by
  intro L S S' hL k ℓ
  funext i j
  simp only [h L S S' hL k ℓ, h' L S S' hL k ℓ, upperAct, mul_add, Finset.sum_add_distrib]

/-- Multiplying by an invariant scalar keeps a tensor covariant. -/
theorem mul_inv (h : TCov2 N) {c : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hc : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S S' →
      ∀ k ℓ, c (L *ᵥ k) (loopAct L ℓ) = c k ℓ) :
    TCov2 fun k ℓ i j => c k ℓ * N k ℓ i j := by
  intro L S S' hL k ℓ
  funext i j
  simp only [h L S S' hL k ℓ, hc L S S' hL k ℓ, upperAct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem const_mul (h : TCov2 N) (c : ℂ) : TCov2 fun k ℓ i j => c * N k ℓ i j :=
  h.mul_inv (c := fun _ _ => c) fun _ _ _ _ _ _ => rfl

theorem sub (h : TCov2 N) (h' : TCov2 N') : TCov2 fun k ℓ i j => N k ℓ i j - N' k ℓ i j := by
  have := h.add (h'.const_mul (-1))
  simpa [sub_eq_add_neg] using this

theorem sum {ι : Type*} (s : Finset ι)
    {N : ι → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ a ∈ s, TCov2 (N a)) : TCov2 fun k ℓ i j => ∑ a ∈ s, N a k ℓ i j := by
  intro L S S' hL k ℓ
  funext i j
  simp only [upperAct, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a ha => congrFun (congrFun (h a ha L S S' hL k ℓ) i) j]
  simp only [upperAct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

end TCov2

/-- The propagator denominator at a line momentum is invariant. -/
theorem propDenom_lineMomentum_inv (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (M ε : ℝ)
    (r : Fin 5) (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ)
    (hL : IsSpinLift L S S') (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    propDenom M ε (lineMomentum (castLoopMatrix base) (fun j => c j • (L *ᵥ k)) r
      (loopAct L ℓ)) =
      propDenom M ε (lineMomentum (castLoopMatrix base) (fun j => c j • k) r ℓ) := by
  rw [lineMomentum_loopAct_smul, propDenom_mulVec' hL]

/-- A line momentum is affine in the external momentum at fixed loop momenta. -/
theorem isLoopAffine_lineMomentum_k (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (r : Fin 5)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ =>
      lineMomentum (castLoopMatrix base) (fun j => c j • y 0) r ℓ := by
  refine ⟨![c r], lineMomentum (castLoopMatrix base) 0 r ℓ, fun y => ?_⟩
  funext μ
  simp [lineMomentum]
  ring

/-! ### Pieces -/

theorem good_of_poly {n : ℕ} (hn : n = 6 ∨ n = 7) {α : Fin (n + 1) → Fin 2 → ℝ}
    {E : Finset (Fin (n + 1))} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hP : IsLoopPoly 2 (n - 3) F)
    (hB : RefinedBound α E 4 F) :
    ∃ Q : LoopQuartic, (7 ≤ n ∨ Q.quart = 0) ∧ RefinedBound α E 4 Q.eval ∧ Q.eval = F := by
  rcases hn with rfl | rfl
  · obtain ⟨Q, hq, hQ⟩ := IsLoopPoly.exists_loopQuartic_cubic hP
    exact ⟨Q, Or.inr hq, hQ ▸ hB, hQ⟩
  · obtain ⟨Q, hQ⟩ := IsLoopPoly.exists_loopQuartic hP
    exact ⟨Q, Or.inl le_rfl, hQ ▸ hB, hQ⟩

/-- **A piece over a shape of a vacuum-polarization routing** is `VPJ (2 m₀)`. -/
theorem vpj_piece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
      |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k i j, IsLoopPoly 2 (n - 3) fun ℓ => N k ℓ i j)
    (hB : ∀ k i j, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 fun ℓ => N k ℓ i j)
    (hcov : TCov2 N) {d : ℕ} (hk : ∀ ℓ i j, IsLoopPoly 1 d fun y => N (y 0) ℓ i j)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hf : ∀ i, sh i ≠ 4 → m₀ ≤ Ms i) (h0 : ∀ i, 0 ≤ Ms i)
    {cc : ℝ} (hc : 0 < cc) (hMc : ∀ i, cc ≤ Ms i ^ 2) :
    VPJ (2 * m₀) fun ε k ℓ i j => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l) ℓ))⁻¹ := by
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
  refine ⟨fun h h₀ hh => P.hasVPLim (by nlinarith) hk hh fun p _ i j => ?_,
    fun ε hε k i j => ?_⟩
  · exact Eventually.of_forall fun ε => rfl
  · obtain ⟨Q, hq, hb, he⟩ := good_of_poly hn (hpoly k i j) (hB k i j)
    have h := (show QED.TwoLoop.jointEnergyFirstIntegrable 2
        (fun ℓ => Q.eval ℓ * ∏ l, (lineDenom (castLoopMatrix fun i => base (sh i))
          (fun l => c (sh l) • k) Ms ε l ℓ)⁻¹) from by
      rcases hq with h7 | hq
      · exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q _ _ _
          h7 hε hcrit' hb
      · exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic Q _ _ _
          hq h6 hε hcrit' hb)
    rw [he] at h
    exact h

end QED.GradedProof.VP2

end
