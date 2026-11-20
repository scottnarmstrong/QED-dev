/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2RX
public import QED.GradedProof.SE2LimV

/-!
# The class `V` in the Ward–Takahashi routing: the data

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the vacuum-polarization class `V`. The frozen routing of `repV` (`baseA`, `basePP`:
open line `ℓ₀`, bubble `ℓ₁`, `p - ℓ₀ + ℓ₁`, photons `p - ℓ₀`, `ℓ₀ - p`) sends the external
momentum through the bubble and the photons. The change `ℓ₀ ↦ p - ℓ₀` (`mV`, shift `![p, 0]`)
gives the Ward–Takahashi routing `awV`, `csV`: open line `p - ℓ₀`, bubble `ℓ₁`, `ℓ₀ + ℓ₁`,
photons `ℓ₀`, `-ℓ₀`, so that `p` flows only through the open line.

* `vData`: the self-energy data of a piece of shape `sh` in that routing.
* `rr_awV`, `rr_csV`: the data are the frozen data rerouted by `mV`, `![p, 0]`.
* `vpos_vData`: positivity of `V` below threshold (`symanzikV_vShape_ge`, `symanzikV_rr_ge`).
* `lineMomentum_vData`, `lineDenom_vData`: the line momenta and denominators are the frozen ones
  at `loopAff mV ![p, 0] ℓ`; `bm_loopAff_mV`: the momenta of the five rows there.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel

/-- The Ward–Takahashi rows of `V`: open line `-ℓ₀`, bubble `ℓ₁`, `ℓ₀ + ℓ₁`, photons `ℓ₀`,
`-ℓ₀`. -/
def awV : Fin 5 → Fin 2 → ℤ := ![![-1, 0], ![0, 1], ![1, 1], ![1, 0], ![-1, 0]]

/-- The external momentum of the rows of `V` in the Ward–Takahashi routing. -/
def csV : Fin 5 → ℝ := ![1, 0, 0, 0, 0]

/-- The change of loop momenta `ℓ₀ ↦ -ℓ₀` (with the shift `![p, 0]`: `ℓ₀ ↦ p - ℓ₀`). -/
def mV : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

theorem det_mV : IsUnit mV.det := by
  simp [mV, Matrix.det_fin_two]

theorem rr_awV {n : ℕ} (sh : Fin (n + 1) → Fin 5) :
    castLoopMatrix (fun i => awV (sh i)) = rrAlpha (castLoopMatrix fun i => baseA (sh i)) mV := by
  funext i r
  simp only [castLoopMatrix, rrAlpha]
  generalize sh i = j
  fin_cases j <;> fin_cases r <;> simp [awV, baseA, mV, Fin.sum_univ_two]

theorem rr_csV {n : ℕ} (sh : Fin (n + 1) → Fin 5) (p : Fin 4 → ℝ) :
    (fun i => csV (sh i) • p) =
      rrMom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) ![p, 0] := by
  funext i μ
  simp only [rrMom, castLoopMatrix]
  generalize sh i = j
  fin_cases j <;> simp [csV, baseA, basePP, Fin.sum_univ_two]

/-- **The self-energy data of a piece of `V` in the Ward–Takahashi routing.** -/
def vData {n : ℕ} (hn : 6 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    (E : Finset (Fin (n + 1))) (hw : IntNoSubdivergenceRefined 2 E fun i => awV (sh i)) :
    SEData where
  m := n
  α := castLoopMatrix fun i => awV (sh i)
  cs := fun i => csV (sh i)
  M := Ms
  E := E
  hm := hn
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hw

theorem crit_shw : IntNoSubdivergenceRefined 2 {0, 1, 2} (fun i => awV (sh1 i)) ∧
    IntNoSubdivergenceRefined 2 {0, 1, 2} (fun i => awV (sh2 i)) ∧
    IntNoSubdivergenceRefined 2 {0, 1, 2} (fun i => awV (sh3 i)) ∧
    IntNoSubdivergenceRefined 2 {0} (fun i => awV (sh4 i)) ∧
    IntNoSubdivergenceRefined 2 {0} (fun i => awV (sh5 i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

variable {n : ℕ} (hn : 6 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
  (E : Finset (Fin (n + 1))) (hw : IntNoSubdivergenceRefined 2 E fun i => awV (sh i))

theorem lineMomentum_vData (p : Fin 4 → ℝ) (i : Fin (n + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom p) i ℓ =
      bm p (loopAff mV ![p, 0] ℓ) (sh i) := by
  change lineMomentum (castLoopMatrix fun i => awV (sh i)) (fun i => csV (sh i) • p) i ℓ = _
  rw [rr_awV, rr_csV, lineMomentum_rr]
  rfl

theorem lineDenom_vData (p : Fin 4 → ℝ) (ε : ℝ) (i : Fin (n + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom p) (vData hn sh Ms E hw).M ε i
      ℓ = lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms ε i
        (loopAff mV ![p, 0] ℓ) := by
  change lineDenom (castLoopMatrix fun i => awV (sh i)) (fun i => csV (sh i) • p) Ms ε i ℓ = _
  rw [rr_awV, rr_csV, lineDenom_rr]

theorem bm_loopAff_mV (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    bm p (loopAff mV ![p, 0] ℓ) 0 = p - ℓ 0 ∧ bm p (loopAff mV ![p, 0] ℓ) 1 = ℓ 1 ∧
      bm p (loopAff mV ![p, 0] ℓ) 2 = ℓ 0 + ℓ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext μ <;>
    simp [bm, Integration.TwoLoop.lineMomentum, castLoopMatrix, baseA, basePP, loopAff, mV,
      Fin.sum_univ_two] <;>
    ring

/-- **Positivity of `V` for the Ward–Takahashi data of a piece of `V`.** -/
theorem vpos_vData {m m₀ ν : ℝ} (hm : 0 < m) (hm0 : 0 < m₀) (hmm : m₀ ≤ m) (hν0 : 0 < ν)
    (hν2 : ν ≤ 2 * m₀) (h0 : ∀ i, sh i = 0 → m ≤ Ms i)
    (h12 : ∀ i, sh i = 1 ∨ sh i = 2 → m₀ ≤ Ms i) (h34 : ∀ i, sh i = 3 ∨ sh i = 4 → ν ≤ Ms i)
    {p : Fin 4 → ℝ} (hs : -(m + ν) ^ 2 < Minkowski.dot p p) :
    (vData hn sh Ms E hw).VPos ((vData hn sh Ms E hw).mom p) := by
  have hc : 0 < min (m₀ ^ 2) (ν ^ 2) := lt_min (by positivity) (by positivity)
  have hMc : ∀ i, min (m₀ ^ 2) (ν ^ 2) ≤ Ms i ^ 2 := by
    intro i
    rcases (by decide : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) (sh i) with
      h | h | h | h | h
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (hmm.trans (h0 i h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inl h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inr h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inl h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inr h)) 2)
  refine ⟨_, min_one_mul_pos (by positivity) hc hs, ?_⟩
  change ∀ z : Fin (n + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
    symanzikU (castLoopMatrix fun i => awV (sh i)) z ≠ 0 →
      _ ≤ symanzikV (castLoopMatrix fun i => awV (sh i)) (fun i => csV (sh i) • p) Ms z
  rw [rr_awV, rr_csV]
  exact symanzikV_rr_ge (fun z hz hz1 hU => symanzikV_vShape_ge sh Ms hm hν0 hν2 h0 h12 h34 hc
    hMc hs hz hz1 hU) det_mV _

end QED.GradedProof.WI2

end
