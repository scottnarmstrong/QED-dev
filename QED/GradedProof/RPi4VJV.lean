/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VGen
public import QED.TwoLoop.PauliZeroExplicitQuartic

/-!
# (R-Π₄) step L6a: two-loop families with a named parametric limit

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6a. The predicate
`QED.GradedProof.VP2.VPJ` of (G-Π₂) says that the joint integrals of a two-loop family converge,
without naming the limit. For the regulator limits (steps L6d, L7) the limit of each class at a
photon pair must be an explicit parametric integral. This file carries the value along.

* `pvOf F α p M`: the parametric value `-π⁴ ∫_Δ paramIntegrand` of a numerator *function* `F`
  (through the canonical quartic `numQuartic F`); `pvOf_eq`: it is the value of every quartic with
  the values of `F`.
* `VPJV T F W`: `F` is `VPJ T` and its joint integrals converge to `W k i j` on the region
  `k² > -T²`; closed under sums, convergent multipliers, constants and eventual equality.
* `pieceVal`: the parametric value of a piece over a shape of a vacuum-polarization routing;
  `vpjv_piece`: the piece of `QED.GradedProof.VP2.vpj_piece` converges to `pieceVal`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic paramIntegrand_congr)
open QED.Integration.Feynman (simplexSet)

/-! ### The parametric value of a numerator function -/

/-- **The parametric value of a numerator function** `F`:
`-π⁴ ∫_Δ paramIntegrand (numQuartic F) α p M 0`. -/
noncomputable def pvOf {m : ℕ} (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ∫ x in simplexSet m, paramIntegrand (numQuartic F) α p M 0 x

/-- `pvOf F` is the parametric value of every quartic with the values of `F`. -/
theorem pvOf_eq {m : ℕ} {Q : LoopQuartic} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hQ : Q.eval = F)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) :
    pvOf F α p M = -((π : ℂ) ^ 4) * ∫ x in simplexSet m, paramIntegrand Q α p M 0 x := by
  have h : ∀ x, paramIntegrand (numQuartic F) α p M 0 x = paramIntegrand Q α p M 0 x :=
    fun x => paramIntegrand_congr α p M ((eval_numQuartic ⟨Q, hQ⟩).trans hQ.symm) 0 x
  simp only [pvOf, h]

/-! ### Families with a named limit -/

/-- **A `VPJ` family whose joint integrals converge to `W`** on the region `k² > -T²`. -/
def VPJV (T : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  VPJ T F ∧ ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ i j : Fin 4,
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j) (𝓝[>] 0)
      (𝓝 (W k i j))

namespace VPJV

variable {T : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
  {W V : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : VPJV T F W) (hG : VPJV T G V) :
    VPJV T (fun ε k ℓ i j => F ε k ℓ i j + G ε k ℓ i j) fun k i j => W k i j + V k i j := by
  refine ⟨hF.1.add hG.1, fun k hk i j => ((hF.2 k hk i j).add (hG.2 k hk i j)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (hF.1.2 ε hε k i j)
    (hG.1.2 ε hε k i j)).symm

theorem mul (hF : VPJV T F W) {c : ℝ → ℂ} {c₀ : ℂ} (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀)) :
    VPJV T (fun ε k ℓ i j => c ε * F ε k ℓ i j) fun k i j => c₀ * W k i j := by
  refine ⟨hF.1.mul hc, fun k hk i j => (hc.mul (hF.2 k hk i j)).congr fun ε => ?_⟩
  exact (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul _ _).symm

theorem const_mul (hF : VPJV T F W) (c : ℂ) :
    VPJV T (fun ε k ℓ i j => c * F ε k ℓ i j) fun k i j => c * W k i j :=
  hF.mul (c := fun _ => c) tendsto_const_nhds

theorem congr (hF : VPJV T F W) (e : ∀ ε : ℝ, 0 < ε → ∀ k ℓ i j, F ε k ℓ i j = G ε k ℓ i j) :
    VPJV T G W := by
  refine ⟨hF.1.congr e, fun k hk i j => (hF.2 k hk i j).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [show (fun ℓ => F ε k ℓ i j) = fun ℓ => G ε k ℓ i j from funext (e ε hε k · i j)]

theorem congr_val (hF : VPJV T F W)
    (e : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ i j, W k i j = V k i j) :
    VPJV T F V :=
  ⟨hF.1, fun k hk i j => e k hk i j ▸ hF.2 k hk i j⟩

theorem zero : VPJV T (fun _ _ _ _ _ => 0) fun _ _ _ => 0 := by
  refine ⟨VPJ.zero, fun k _ i j => tendsto_const_nhds.congr fun ε => ?_⟩
  simp [QED.TwoLoop.jointEnergyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {W : ι → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hF : ∀ a ∈ s, VPJV T (F a) (W a)) :
    VPJV T (fun ε k ℓ i j => ∑ a ∈ s, F a ε k ℓ i j) fun k i j => ∑ a ∈ s, W a k i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : VPJV T (fun _ _ _ _ _ => 0) fun _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end VPJV

/-! ### Pieces -/

/-- **The parametric value of a piece** over the shape `sh` (masses `Ms`, numerator `N`) of a
vacuum-polarization routing (`base`, external coefficients `c`), at the momentum `k`. -/
noncomputable def pieceVal (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {n : ℕ}
    (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) (i j : Fin 4) :
    ℂ :=
  pvOf (fun ℓ => N k ℓ i j) (castLoopMatrix fun l => base (sh l)) (fun l => c (sh l) • k) Ms

/-- **A piece converges to its parametric value** (`vpj_piece` with the limit named). -/
theorem vpjv_piece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
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
    VPJV (2 * m₀) (fun ε k ℓ i j => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l) ℓ))⁻¹)
      (pieceVal base c sh Ms N) := by
  refine ⟨vpj_piece base c y₁ y₂ hflow hn sh Ms hcrit N hpoly hB hcov hk hm₀ hf h0 hc hMc,
    fun k hk' i j => ?_⟩
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
  have hpos : 0 < min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * cc := by
    refine mul_pos (lt_min one_pos ?_) hc
    have hT2 : 0 < (2 * m₀) ^ 2 := by positivity
    have h1 : 0 < (2 * m₀) ^ 2 + Minkowski.dot k k := by linarith
    calc (0 : ℝ) < ((2 * m₀) ^ 2 + Minkowski.dot k k) / (2 * m₀) ^ 2 := by positivity
      _ = 1 + Minkowski.dot k k / (2 * m₀) ^ 2 := by field_simp
  have hV : D.VPos (D.mom k) := ⟨_, hpos, fun z hz hz1 hU =>
    symanzikV_vp_ge base c y₁ y₂ hflow sh Ms hm₀ hf h0 hc hMc hk' hz hz1 hU⟩
  obtain ⟨Q, hq, hb, he⟩ := good_of_poly hn (hpoly k i j) (hB k i j)
  have h := SEData.tendsto_pv (D := D) ⟨hq, hb⟩ hV
  rw [he] at h
  rw [pieceVal, pvOf_eq he]
  exact h

end QED.GradedProof.RPi4

end
