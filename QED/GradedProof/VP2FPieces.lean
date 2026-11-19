/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FCov

/-!
# The inserted bubble at three masses: a covariant, null-continuous limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, classes `F0`,
`F1`.

* `VPF T F`: the one-loop integrand family `F ε k q μ ν` is integrable in both stages at every
  `ε > 0`, and for every convergent multiplier `h` the family `h ε ∫ F` has a covariant,
  null-continuous limit (`HasVPLim`) on `k² > -T²`. It is closed under sums, multiplication by
  convergent functions of `ε`, and pointwise equality at `ε > 0`.
* `vpf_five`, `vpf_four`, `vpf_three`: pieces with an `ε`-independent covariant numerator over five,
  four, three propagators at `q` or `k + q` (`hasVPLim_five`, …, `ef5`, `ef4`, `ef3`).
* `insTriple_eq`: the three-flavour inserted bubble is `(X² - M²)(Y² - M²)` times ten pieces with
  the numerators `E₀ = n₀ + iε n₁ + (iε)² n₂`, `E₂ = n₁ + 2 iε n₂`, `E₄ = n₂` (the identity
  behind `QED.GradedProof.VP2.ef_insTriple`).
* `vpf_insTriple`: the three-flavour inserted bubble at the gamma matrices `γ^μ, γ^ν` (`sw =
  false`) or `γ^ν, γ^μ` (`sw = true`) satisfies `VPF (m₀ + m₀)` when all masses are at least `m₀`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- One-loop families with a covariant, null-continuous limit for every convergent multiplier,
integrable in both stages at `ε > 0`. -/
def VPF (T : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  (∀ (h : ℝ → ℂ) (h₀ : ℂ), Tendsto h (𝓝[>] 0) (𝓝 h₀) →
    HasVPLim T fun ε k i j => h ε * QED.OneLoop.energyFirstIntegral fun q => F ε k q i j) ∧
  ∀ ε : ℝ, 0 < ε → ∀ k i j, EF fun q => F ε k q i j

namespace VPF

variable {T : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : VPF T F) (hG : VPF T G) : VPF T fun ε k q i j => F ε k q i j + G ε k q i j := by
  refine ⟨fun h h₀ hh => ((hF.1 h h₀ hh).add (hG.1 h h₀ hh)).congr fun k _ i j => ?_,
    fun ε hε k i j => (hF.2 ε hε k i j).add (hG.2 ε hε k i j)⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [efi_add (hF.2 ε hε k i j) (hG.2 ε hε k i j), mul_add]

theorem mul (hF : VPF T F) {c : ℝ → ℂ} {c₀ : ℂ} (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀)) :
    VPF T fun ε k q i j => c ε * F ε k q i j := by
  refine ⟨fun h h₀ hh => (hF.1 (fun ε => h ε * c ε) _ (hh.mul hc)).congr fun k _ i j => ?_,
    fun ε hε k i j => (hF.2 ε hε k i j).const_mul (c ε)⟩
  filter_upwards with ε
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, mul_assoc]

theorem const_mul (hF : VPF T F) (c : ℂ) : VPF T fun ε k q i j => c * F ε k q i j :=
  hF.mul (c := fun _ => c) tendsto_const_nhds

theorem congr (hF : VPF T F)
    (e : ∀ ε : ℝ, 0 < ε → ∀ k q i j, F ε k q i j = G ε k q i j) : VPF T G := by
  refine ⟨fun h h₀ hh => (hF.1 h h₀ hh).congr fun k _ i j => ?_,
    fun ε hε k i j => (hF.2 ε hε k i j).congr (e ε hε k · i j)⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [show (fun q => F ε k q i j) = fun q => G ε k q i j from funext (e ε hε k · i j)]

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, VPF T (F a)) (_hT : -T ^ 2 < 0) :
    VPF T fun ε k q i j => ∑ a ∈ s, F a ε k q i j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨fun h h₀ hh => (HasVPLim.zero).congr fun k _ i j => ?_,
      fun ε _ k i j => EF.zero⟩
    filter_upwards with ε
    simp [QED.OneLoop.energyFirstIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- The energy-first integral of a `VPF` family has a covariant, null-continuous limit. -/
theorem hasVPLim (hF : VPF T F) :
    HasVPLim T fun ε k i j => QED.OneLoop.energyFirstIntegral fun q => F ε k q i j :=
  (hF.1 (fun _ => 1) 1 tendsto_const_nhds).congr fun _ _ _ _ => by
    filter_upwards with ε
    rw [one_mul]

end VPF

/-! ### Pieces -/

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀)
include hm₀

theorem vpf_five (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) :
    VPF (m₀ + m₀) fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹ *
      (propDenom m3 ε (zk k c3 q))⁻¹ * (propDenom m4 ε (zk k c4 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  refine ⟨fun h h₀ hh => ?_, fun ε hε k i j => ef5 k hε _ (hN k i j) _ _ _ _ _ _ _ _ _ _⟩
  refine (hasVPLim_five hm₀ ![m0, m1, m2, m3, m4] (fun l => by fin_cases l <;> assumption)
    ![c0, c1, c2, c3, c4] N hN hcov hpoly hh).congr fun k _ i j => ?_
  filter_upwards with ε
  simp only [Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rfl

theorem vpf_four (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) :
    VPF (m₀ + m₀) fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹ *
      (propDenom m3 ε (zk k c3 q))⁻¹) := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  refine ⟨fun h h₀ hh => ?_, fun ε hε k i j => ef4 k hε _ (hN k i j) _ _ _ _ _ _ _ _⟩
  refine (hasVPLim_four hm₀ ![m0, m1, m2, m3] (fun l => by fin_cases l <;> assumption)
    ![c0, c1, c2, c3] N hN hcov hpoly hh).congr fun k _ i j => ?_
  filter_upwards with ε
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  rfl

theorem vpf_three (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2)
    (c0 c1 c2 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 0 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) :
    VPF (m₀ + m₀) fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹) := by
  obtain ⟨h0, h1, h2⟩ := hm
  refine ⟨fun h h₀ hh => ?_, fun ε hε k i j => ef3 k hε _ (hN k i j) _ _ _ _ _ _⟩
  refine (hasVPLim_three hm₀ ![m0, m1, m2] (fun l => by fin_cases l <;> assumption)
    ![c0, c1, c2] N hN hcov hpoly hh).congr fun k _ i j => ?_
  filter_upwards with ε
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  rfl

end Pieces

end QED.GradedProof.VP2

end
