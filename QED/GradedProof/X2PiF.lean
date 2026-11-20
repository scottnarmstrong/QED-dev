/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X2PvCont
public import QED.GradedProof.RPi4UnifF

/-!
# (X₂) piece D: the mass-insertion classes of `Π⁽⁴⁾` are continuous at spacelike momentum

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece D. The
statements and proofs of `QED.GradedProof.X1E.continuousAt_fbVal` and its chain, at a spacelike
base point `k₀` (`k₀² ≥ 0`) in place of `k = 0`, with
`QED.GradedProof.X2.continuousAt_pvOf_of_spacelike` in place of
`QED.GradedProof.X1E.continuousAt_pvOf_zero`.

* `continuousAt_kinds`: eight-line kinds data with positive masses;
* `continuousAt_fVal5`, `continuousAt_eVal0/2/4`, `continuousAt_insVal`, `continuousAt_fbVal`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.X2

open QED.GradedProof.VP2 QED.GradedProof.SE2 QED.GradedProof.RPi4
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.PauliZeroLimit (paramNum)
open QED.Graded (Counterterms)

variable {k₀ : Fin 4 → ℝ} (hk₀ : 0 ≤ Minkowski.dot k₀ k₀)
include hk₀


/-- **The parametric value of eight-line kinds is continuous at a spacelike `k₀`**, for positive
masses. -/
theorem continuousAt_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {c : ℝ} (hc : 0 < c) (hM : ∀ i, c ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) (i j : Fin 4) :
    ContinuousAt (fun k => pvOf (fun ℓ => N k (ℓ 0) i j) (castLoopMatrix fun i => (κ i).dir)
      (fun l => (κ l).mom k k) Ms) k₀ := by
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
  have hspan : ∃ a b, D.α a 0 * D.α b 1 - D.α a 1 * D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := D.α) fun k => by
      have := D.hcrit.noSubdivergenceOfOrder k; have := D.hm; omega
  have hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = (fun ℓ => N k (ℓ 0) i j) ∧
      ∀ q, IntegrableOn (paramNum Q D.α q D.M) (simplexSet D.m) := fun k => by
    obtain ⟨Q, hQ⟩ := (hN k i j).exists_loopQuartic
    have hgood : D.Good Q := ⟨Or.inl hm7, refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
      simp only [hQ, Matrix.cons_val_zero]⟩
    exact ⟨Q, hQ, fun q => integrableOn_paramNum_good hgood q⟩
  have h := continuousAt_pvOf_of_spacelike (by have := D.hm; omega) D.α hspan D.cs D.M hc hM
    (fun k ℓ => N k (ℓ 0) i j) (fun ℓ => hpoly (ℓ 0) i j) hQ hk₀
  refine h.congr (Eventually.of_forall fun k => ?_)
  show pvOf _ D.α (D.mom k) D.M = _
  rw [hmom]
  rfl

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀)
include hm₀

theorem continuousAt_fVal5 (Ms : Fin 5 → ℝ) (hMs : ∀ l, m₀ ≤ Ms l) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) (i j : Fin 4) :
    ContinuousAt (fun k => fVal5 m₀ Ms b N k i j) k₀ := by
  have hsq : ∀ l, m₀ ^ 2 ≤ Ms l ^ 2 := fun l => pow_le_pow_left₀ hm₀.le (hMs l) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i
    exacts [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, le_rfl, le_rfl, le_rfl]
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  have h := continuousAt_kinds hk₀ (by norm_num) (kinds5 b) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] (by positivity) hM
    (crit_kinds5 _) (by decide) (ne_aux_kinds5 _) N hN hpoly i j
  exact h.const_mul (auxLimit m₀)⁻¹

variable (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)

theorem continuousAt_eVal0 (m0 m1 m2 m3 m4 : ℝ)
    (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4)
    (c0 c1 c2 c3 c4 : Bool) (i j : Fin 4) :
    ContinuousAt (fun k => eVal0 m₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 c0 c1 c2 c3 c4 k i j) k₀ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  exact continuousAt_fVal5 hk₀ hm₀ _ (fun l => by fin_cases l <;> assumption) _ _
    (isLoopPoly_tnS0 sw d₂ dm bx bY) (isLoopPoly_tnS_k sw 0 d₂ dm bx bY) i j

theorem continuousAt_eVal2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (i j : Fin 4) :
    ContinuousAt (fun k => eVal2 m₀ sw d₂ dm bx bY m0 m1 m2 m3 c0 c1 c2 c3 k i j) k₀ := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => padN (tnS sw 1 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS1 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 1 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact continuousAt_fVal5 hk₀ hm₀ _ (fun l => by fin_cases l <;> assumption) _ _ hN' hpoly' i j

theorem continuousAt_eVal4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2)
    (c0 c1 c2 : Bool) (i j : Fin 4) :
    ContinuousAt (fun k => eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2 k i j) k₀ := by
  obtain ⟨h0, h1, h2⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 2 fun ℓ => padN (tnS sw 2 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS2 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hN'' : ∀ p i j, IsLoopPoly 2 4 fun ℓ =>
      padN (padN (tnS sw 2 d₂ dm bx bY) m0 c0) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((hN' p i j).mul ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono
      (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 2 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  have hpoly'' := fun q i j => (hpoly' q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact continuousAt_fVal5 hk₀ hm₀ _ (fun l => by fin_cases l <;> assumption) _ _ hN'' hpoly'' i j

theorem continuousAt_insVal (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (i j : Fin 4) : ContinuousAt (fun k => insVal m₀ sw d₂ dm bx bY M X Y k i j) k₀ := by
  have E0 := fun m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 =>
    continuousAt_eVal0 hk₀ hm₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 i j
  have E2 := fun m0 m1 m2 m3 hm c0 c1 c2 c3 =>
    continuousAt_eVal2 hk₀ hm₀ sw d₂ dm bx bY m0 m1 m2 m3 hm c0 c1 c2 c3 i j
  have E4 := continuousAt_eVal4 hk₀ hm₀ sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx i j
  exact ((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add E4).const_mul _

end Pieces

/-- **The value of the block-summed inserted bubble is continuous at a spacelike `k₀`.** -/
theorem continuousAt_fbVal (P : QED.WickModel.Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (sw bx bY : Bool) (i j : Fin 4) :
    ContinuousAt (fun k => fbVal P Φ D rep m₀ sw bx bY k i j) k₀ := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  unfold fbVal
  refine tendsto_finsetSum _ fun f _ => ?_
  exact (continuousAt_insVal hk₀ hm₀ sw _ _ bx bY (Φ.mass f) (auxX Φ) (auxX Φ + 1) (hmass f)
    (by linarith [hlt f, hmass f]) (by linarith [hlt f, hmass f]) i j).const_mul _

end QED.GradedProof.X2

end
