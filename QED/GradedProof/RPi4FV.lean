/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FTriple
public import QED.GradedProof.RPi4VJV

/-!
# (R-Π₄) step L6a′: one-loop families with a named parametric limit

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6a′. The predicate
`QED.GradedProof.VP2.VPF` says that the energy-first integrals of a one-loop family have a
covariant limit, without naming it. For the regulator limits the limit of the mass-insertion
classes must be an explicit parametric integral. This file carries the value along, as
`QED.GradedProof.RPi4.VPJV` does for the two-loop classes.

* `VPFV T F W`: `F` is `VPF T` and its energy-first integrals converge to `W k i j` on the region
  `k² > -T²`; closed under sums, convergent multipliers, constants and eventual equality, and a
  `VPF` family times a multiplier tending to `0` has the value `0` (`VPFV.of_mul_zero`).
* `tendsto_kinds`: the value of a one-loop integrand through product data (the limit inside
  `QED.GradedProof.VP2.hasVPLim_kinds`): the parametric value of the padded two-loop data divided
  by the auxiliary loop `auxLimit`.
* `fVal5`: the value of five lines at `q` or `k + q` (masses `m₀` on the three auxiliary lines);
  `vpfv_five`, `vpfv_four`, `vpfv_three`: the pieces of `QED.GradedProof.VP2.vpf_five`, …, with
  their values. Four and three lines are padded by repeating the first line with the numerator
  multiplied by its `ε = 0` denominator (`padN`); the `iε` remainder has the value `0`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-! ### Families with a named limit -/

/-- **A `VPF` family whose energy-first integrals converge to `W`** on the region `k² > -T²`. -/
def VPFV (T : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  VPF T F ∧ ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ i j : Fin 4,
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q => F ε k q i j) (𝓝[>] 0)
      (𝓝 (W k i j))

namespace VPFV

variable {T : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
  {W V : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : VPFV T F W) (hG : VPFV T G V) :
    VPFV T (fun ε k q i j => F ε k q i j + G ε k q i j) fun k i j => W k i j + V k i j := by
  refine ⟨hF.1.add hG.1, fun k hk i j => ((hF.2 k hk i j).add (hG.2 k hk i j)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (efi_add (hF.1.2 ε hε k i j) (hG.1.2 ε hε k i j)).symm

theorem mul (hF : VPFV T F W) {c : ℝ → ℂ} {c₀ : ℂ} (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀)) :
    VPFV T (fun ε k q i j => c ε * F ε k q i j) fun k i j => c₀ * W k i j := by
  refine ⟨hF.1.mul hc, fun k hk i j => (hc.mul (hF.2 k hk i j)).congr fun ε => ?_⟩
  exact (QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul _ _).symm

theorem const_mul (hF : VPFV T F W) (c : ℂ) :
    VPFV T (fun ε k q i j => c * F ε k q i j) fun k i j => c * W k i j :=
  hF.mul (c := fun _ => c) tendsto_const_nhds

theorem congr (hF : VPFV T F W)
    (e : ∀ ε : ℝ, 0 < ε → ∀ k q i j, F ε k q i j = G ε k q i j) : VPFV T G W := by
  refine ⟨hF.1.congr e, fun k hk i j => (hF.2 k hk i j).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [show (fun q => F ε k q i j) = fun q => G ε k q i j from funext (e ε hε k · i j)]

theorem congr_val (hF : VPFV T F W)
    (e : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ i j, W k i j = V k i j) :
    VPFV T F V :=
  ⟨hF.1, fun k hk i j => e k hk i j ▸ hF.2 k hk i j⟩

theorem zero : VPFV T (fun _ _ _ _ _ => 0) fun _ _ _ => 0 := by
  refine ⟨⟨fun h h₀ hh => (HasVPLim.zero).congr fun k _ i j => ?_, fun ε _ k i j => EF.zero⟩,
    fun k _ i j => tendsto_const_nhds.congr fun ε => ?_⟩
  · filter_upwards with ε
    simp [QED.OneLoop.energyFirstIntegral]
  · simp [QED.OneLoop.energyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {W : ι → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hF : ∀ a ∈ s, VPFV T (F a) (W a)) :
    VPFV T (fun ε k q i j => ∑ a ∈ s, F a ε k q i j) fun k i j => ∑ a ∈ s, W a k i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : VPFV T (fun _ _ _ _ _ => 0) fun _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- A `VPF` family times a multiplier tending to `0` has the value `0`. -/
theorem of_mul_zero (hF : VPF T F) {c : ℝ → ℂ} (hc : Tendsto c (𝓝[>] 0) (𝓝 0)) :
    VPFV T (fun ε k q i j => c ε * F ε k q i j) fun _ _ _ => 0 := by
  obtain ⟨W, hW, -, -⟩ := hF.hasVPLim
  exact (mul ⟨hF, hW⟩ hc).congr_val fun _ _ _ _ => zero_mul _

end VPFV

/-! ### The value of a one-loop integrand through product data -/

/-- **The limit of a one-loop integrand through product data** (the value inside
`QED.GradedProof.VP2.hasVPLim_kinds`): the parametric value of the joint data divided by the
auxiliary loop. -/
theorem tendsto_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {mass : ℝ} (hmass : 0 < mass) {me μ : ℝ}
    (hme : 0 < me) (hμ : 0 < μ)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ p (ℓ : Fin 2 → Fin 4 → ℝ) i j,
      N p (ℓ 0) i j * ∏ k, (propDenom (Ms k) ε ((κ k).lineMom p p ℓ))⁻¹ =
        F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3)
    {p : Fin 4 → ℝ} (hp : -(me + μ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q => F ε p q i j) (𝓝[>] 0)
      (𝓝 ((auxLimit mass)⁻¹ * pvOf (fun ℓ => N p (ℓ 0) i j)
        (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p) Ms)) := by
  set D := kindsData hm7 κ Ms hcrit
  have hmom := kindsData_mom hm7 κ hκ Ms hcrit
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hc : 0 < min 1 (1 + Minkowski.dot p p / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) := by
    refine mul_pos (lt_min one_pos ?_) (lt_min (by positivity) (by positivity))
    have hT2 : 0 < (me + μ) ^ 2 := by positivity
    have h1 : 0 < (me + μ) ^ 2 + Minkowski.dot p p := by linarith
    calc (0 : ℝ) < ((me + μ) ^ 2 + Minkowski.dot p p) / (me + μ) ^ 2 := by positivity
      _ = 1 + Minkowski.dot p p / (me + μ) ^ 2 := by field_simp
  obtain ⟨Q, hQ⟩ := (hN p i j).exists_loopQuartic
  have hgood : D.Good Q := ⟨Or.inl hm7, refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
    simp only [hQ, Matrix.cons_val_zero]⟩
  have hV : D.VPos (D.mom p) := ⟨_, hc, fun z hz hz1 hU => by
    rw [hmom p]
    exact symanzikV_kinds_se_ge κ hκ Ms hme hμ hp hMe hMp hz hz1 hU⟩
  have h := SEData.tendsto_pv hgood hV
  have hH := tendsto_energyFirstIntegral_aux hmass
  have hH0 := auxLimit_ne_zero hmass
  have hval : D.pv Q (D.mom p) = pvOf (fun ℓ => N p (ℓ 0) i j)
      (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p) Ms := by
    rw [pvOf_eq hQ, hmom p]
    rfl
  rw [← hval]
  refine ((hH.inv₀ hH0).mul h).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  have e : (fun ℓ => Q.eval ℓ * ∏ k, (lineDenom D.α (D.mom p) D.M ε k ℓ)⁻¹) =
      fun ℓ => F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := by
    funext ℓ
    rw [hQ]
    show N p (ℓ 0) i j * ∏ k, (lineDenom (castLoopMatrix fun i => (κ i).dir) (D.mom p) Ms ε k
      ℓ)⁻¹ = _
    rw [hmom p, prod_lineDenom_kinds]
    exact hfac ε hε p ℓ i j
  rw [e, jointEnergyFirstIntegral_two_mul (fun q => F ε p q i j)
    (fun k => ((propDenom mass ε k)⁻¹) ^ 3)]
  generalize (QED.OneLoop.energyFirstIntegral fun k => ((propDenom mass ε k)⁻¹) ^ 3) = A at hne ⊢
  field_simp

/-! ### Five, four and three lines -/

/-- **The value of five lines at `q` or `k + q`** (masses `Ms`, `k`-flags `b`, numerator `N`):
the parametric value of the eight-line data with three auxiliary lines of mass `m₀`, divided by
the auxiliary loop. -/
noncomputable def fVal5 (m₀ : ℝ) (Ms : Fin 5 → ℝ) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  (auxLimit m₀)⁻¹ * pvOf (fun ℓ => N k (ℓ 0) i j) (castLoopMatrix fun l => (kinds5 b l).dir)
    (fun l => (kinds5 b l).mom k k) ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀]

/-- The numerator padded by the `ε = 0` denominator of the line `(m, c)`. -/
noncomputable def padN (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (m : ℝ) (c : Bool)
    (k q : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  N k q i j * propDenom m 0 (zk k c q)

theorem tendsto_negEpsI : Tendsto (fun ε : ℝ => -((ε : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_epsI.neg

section Lines

variable {m₀ : ℝ} (hm₀ : 0 < m₀)
include hm₀

/-- **Five lines with their value.** -/
theorem vpfv_five (m0 m1 m2 m3 m4 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) :
    VPFV (m₀ + m₀) (fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹ *
      (propDenom m3 ε (zk k c3 q))⁻¹ * (propDenom m4 ε (zk k c4 q))⁻¹))
      (fVal5 m₀ ![m0, m1, m2, m3, m4] ![c0, c1, c2, c3, c4] N) := by
  refine ⟨vpf_five hm₀ m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 N hN hcov hpoly, fun k hk i j => ?_⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  have hsq : ∀ l, m₀ ^ 2 ≤ (![m0, m1, m2, m3, m4] : Fin 5 → ℝ) l ^ 2 := fun l =>
    pow_le_pow_left₀ hm₀.le (by fin_cases l <;> assumption) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![m0, m1, m2, m3, m4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i
    exacts [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, le_rfl, le_rfl, le_rfl]
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  have h := tendsto_kinds (by norm_num) (kinds5 ![c0, c1, c2, c3, c4]) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![m0, m1, m2, m3, m4, m₀, m₀, m₀] hm₀ hm₀ hm₀ (fun i _ => hM i) (fun i _ => hM i)
    (crit_kinds5 _) (by decide) (ne_aux_kinds5 _) N hN (fun ε k q i j => N k q i j *
      ((propDenom m0 ε (zk k c0 q))⁻¹ * (propDenom m1 ε (zk k c1 q))⁻¹ *
        (propDenom m2 ε (zk k c2 q))⁻¹ * (propDenom m3 ε (zk k c3 q))⁻¹ *
        (propDenom m4 ε (zk k c4 q))⁻¹)) (fun ε _ p ℓ i j => ?_) hk i j
  · exact h
  have hk5 : kinds5 ![c0, c1, c2, c3, c4] =
      ![kd c0, kd c1, kd c2, kd c3, kd c4, .aux, .aux, .aux] := rfl
  rw [hk5]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, zk]
  rcases c0 <;> rcases c1 <;> rcases c2 <;> rcases c3 <;> rcases c4 <;>
    simp only [kd, LineKind.lineMom, ite_true, Bool.false_eq_true, ite_false, add_comm p] <;>
    ring

/-- **Four lines with their value**, padded to five by repeating the first line. -/
theorem vpfv_four (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) :
    VPFV (m₀ + m₀) (fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹ *
      (propDenom m3 ε (zk k c3 q))⁻¹))
      (fVal5 m₀ ![m0, m0, m1, m2, m3] ![c0, c0, c1, c2, c3] (padN N m0 c0)) := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => padN N m0 c0 p (ℓ 0) i j := fun p i j =>
    ((hN p i j).mul ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' : ∀ q i j, IsLoopPoly 1 (d + 2) fun y => padN N m0 c0 (y 0) q i j := fun q i j =>
    (hpoly q i j).mul ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  have A := vpfv_five hm₀ m0 m0 m1 m2 m3 ⟨h0, h0, h1, h2, h3⟩ c0 c0 c1 c2 c3 (padN N m0 c0) hN'
    (hcov.mul_propDenom m0 0 c0) hpoly'
  have B := (vpfv_five hm₀ m0 m0 m1 m2 m3 ⟨h0, h0, h1, h2, h3⟩ c0 c0 c1 c2 c3 N
    (fun p i j => (hN p i j).mono (by norm_num)) hcov hpoly).mul tendsto_negEpsI
  refine ((A.add B).congr fun ε hε k q i j => ?_).congr_val fun k _ i j => by
    rw [zero_mul, add_zero]
  simp only [padN]
  have hd := propDenom_ne_zero (M := m0) hε.ne' (zk k c0 q)
  have h0 : propDenom m0 0 (zk k c0 q) = propDenom m0 ε (zk k c0 q) + ε * I := by
    simp only [propDenom]; push_cast; ring
  rw [h0]
  generalize propDenom m0 ε (zk k c0 q) = D at hd ⊢
  generalize (propDenom m1 ε (zk k c1 q))⁻¹ = r1
  generalize (propDenom m2 ε (zk k c2 q))⁻¹ = r2
  generalize (propDenom m3 ε (zk k c3 q))⁻¹ = r3
  field_simp
  ring

/-- **Three lines with their value**, padded to four by repeating the first line. -/
theorem vpfv_three (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 0 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) :
    VPFV (m₀ + m₀) (fun ε k q i j => N k q i j * ((propDenom m0 ε (zk k c0 q))⁻¹ *
      (propDenom m1 ε (zk k c1 q))⁻¹ * (propDenom m2 ε (zk k c2 q))⁻¹))
      (fVal5 m₀ ![m0, m0, m0, m1, m2] ![c0, c0, c0, c1, c2] (padN (padN N m0 c0) m0 c0)) := by
  obtain ⟨h0, h1, h2⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 2 fun ℓ => padN N m0 c0 p (ℓ 0) i j := fun p i j =>
    ((hN p i j).mul ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' : ∀ q i j, IsLoopPoly 1 (d + 2) fun y => padN N m0 c0 (y 0) q i j := fun q i j =>
    (hpoly q i j).mul ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  have A := vpfv_four hm₀ m0 m0 m1 m2 ⟨h0, h0, h1, h2⟩ c0 c0 c1 c2 (padN N m0 c0) hN'
    (hcov.mul_propDenom m0 0 c0) hpoly'
  have B := (vpfv_four hm₀ m0 m0 m1 m2 ⟨h0, h0, h1, h2⟩ c0 c0 c1 c2 N
    (fun p i j => (hN p i j).mono (by norm_num)) hcov hpoly).mul tendsto_negEpsI
  refine ((A.add B).congr fun ε hε k q i j => ?_).congr_val fun k _ i j => by
    rw [zero_mul, add_zero]
  simp only [padN]
  have hd := propDenom_ne_zero (M := m0) hε.ne' (zk k c0 q)
  have h0 : propDenom m0 0 (zk k c0 q) = propDenom m0 ε (zk k c0 q) + ε * I := by
    simp only [propDenom]; push_cast; ring
  rw [h0]
  generalize propDenom m0 ε (zk k c0 q) = D at hd ⊢
  generalize (propDenom m1 ε (zk k c1 q))⁻¹ = r1
  generalize (propDenom m2 ε (zk k c2 q))⁻¹ = r2
  field_simp
  ring

end Lines

end QED.GradedProof.RPi4

end
