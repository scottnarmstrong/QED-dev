/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FV
public import QED.GradedProof.VP2FWardEF

/-!
# (R-Π₄) step L6d3: the value of a four-line one-loop integrand with a cubic numerator

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.
`QED.GradedProof.RPi4.tendsto_kinds` names the limit of a one-loop integrand with at least five
lines (eight with the auxiliary loop). The face rests of the six- and seven-line pieces have four
lines; their numerators are cubic. This file gives the same statement for seven lines in all
with a cubic numerator (the cubic criterion with the three numerator lines `{0, 1, 2}`), so the
four-line rests need no padding.

* `faceIdKData`: the product data with numerator lines `{0, 1, 2}` (six or more lines);
* **`faceId_tendsto_kinds_cubic`**: the limit of the energy-first integrals is the parametric value
  of the joint data divided by the auxiliary loop.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

/-- **Product data with the numerator lines `{0, 1, 2}`** (seven or more lines). -/
noncomputable def faceIdKData {m : ℕ} (hm : 6 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} fun i => (κ i).dir) :
    SEData where
  m := m
  α := castLoopMatrix fun i => (κ i).dir
  cs := fun i => if κ i = .inn then 1 else 0
  M := Ms
  E := {0, 1, 2}
  hm := hm
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit

theorem faceId_kData_mom {m : ℕ} (hm : 6 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} fun i => (κ i).dir) (p : Fin 4 → ℝ) :
    (faceIdKData hm κ Ms hcrit).mom p = fun i => (κ i).mom p p := by
  funext i
  have := hκ i
  simp only [SEData.mom, faceIdKData]
  rcases h : κ i with _ | _ | _ | _ <;> simp_all [LineKind.mom]

/-- **The limit of a one-loop integrand with a cubic numerator through product data** (seven or
more lines in all): the parametric value of the joint data divided by the auxiliary loop. -/
theorem faceId_tendsto_kinds_cubic {m : ℕ} (hm6 : 6 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {mass : ℝ} (hmass : 0 < mass) {me μ : ℝ}
    (hme : 0 < me) (hμ : 0 < μ)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} fun i => (κ i).dir)
    (hcard : ({0, 1, 2} : Finset (Fin (m + 1))).card = 3)
    (hE : ∀ e ∈ ({0, 1, 2} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 3 fun ℓ => N p (ℓ 0) i j)
    (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ p (ℓ : Fin 2 → Fin 4 → ℝ) i j,
      N p (ℓ 0) i j * ∏ k, (propDenom (Ms k) ε ((κ k).lineMom p p ℓ))⁻¹ =
        F ε p (ℓ 0) i j * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3)
    {p : Fin 4 → ℝ} (hp : -(me + μ) ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q => F ε p q i j) (𝓝[>] 0)
      (𝓝 ((auxLimit mass)⁻¹ * pvOf (fun ℓ => N p (ℓ 0) i j)
        (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p) Ms)) := by
  set D := faceIdKData hm6 κ Ms hcrit
  have hmom := faceId_kData_mom hm6 κ hκ Ms hcrit
  have hα : ∀ e ∈ ({0, 1, 2} : Finset (Fin (m + 1))),
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
  obtain ⟨Q, hq, hQ⟩ := SE2.IsLoopPoly.exists_loopQuartic_cubic (hN p i j)
  have hgood : D.Good Q := ⟨Or.inr hq, refinedBound_of_dependsOnZero_cubic _ hcard hα Q hq
    fun ℓ => by simp only [hQ, Matrix.cons_val_zero]⟩
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

end QED.GradedProof.RPi4

end
