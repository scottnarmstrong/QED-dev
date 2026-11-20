/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2ChainWard
public import QED.GradedProof.WI2Reroute
public import QED.GradedProof.SE2FormRX

/-!
# The classes `R` and `X` in the Ward–Takahashi routing: data

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes `R` and `X`. The frozen routings of `QED.GradedProof.SE2` (`aR`, `aX`
with external momenta `ppR`, `ppX`) put `p` on photon lines. The change `ℓ ↦ -ℓ + (p, p)`
(`loopAff (-1) ![p, p]`) gives the **Ward–Takahashi routing** (`wtData aRw`, `wtData aXw`): the
electron lines carry `p - ℓ₀, p - ℓ₁, p - ℓ₀` (`R`) and `p - ℓ₀, p - ℓ₁, p + ℓ₀ - ℓ₁` (`X`), the
photon lines `ℓ₀`, `ℓ₁ - ℓ₀`, so `p` flows only through the open electron line (`cswRX`).

* `rr_aR`, `rr_aX`, `rr_ppR`, `rr_ppX`: the new data are the rerouted frozen data
  (`QED.GradedProof.WI2.rrAlpha`, `rrMom`).
* `vpos_wtData`: positivity of `V` transfers from the frozen data (`symanzikV_rr_ge`).
* `lineMomentum_wtData`, `lineDenom_wtData`: the line momenta and denominators are the frozen
  ones at `loopAff (-1) ![p, p] ℓ`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop

/-- The Ward–Takahashi loop matrix of `R` (minus `aR`). -/
def aRw : Fin 7 → Fin 2 → ℤ :=
  ![![-1, 0], ![0, -1], ![-1, 0], ![1, 0], ![1, 0], ![-1, 1], ![-1, 1]]

/-- The Ward–Takahashi loop matrix of `X` (minus `aX`). -/
def aXw : Fin 7 → Fin 2 → ℤ :=
  ![![-1, 0], ![0, -1], ![1, -1], ![1, 0], ![1, 0], ![-1, 1], ![-1, 1]]

/-- The external momentum flows through the three electron lines only. -/
def cswRX : Fin 7 → ℝ := ![1, 1, 1, 0, 0, 0, 0]

theorem intCrit_Rw : IntNoSubdivergenceRefined 2 {0, 1, 2} aRw := by decide

theorem intCrit_Xw : IntNoSubdivergenceRefined 2 {0, 1, 2} aXw := by decide

/-- **The self-energy data of a seven-line class in the Ward–Takahashi routing.** -/
def wtData (aw : Fin 7 → Fin 2 → ℤ) (hw : IntNoSubdivergenceRefined 2 {0, 1, 2} aw)
    (Q : QED.WickModel.Params) : SEData where
  m := 6
  α := castLoopMatrix aw
  cs := cswRX
  M := massesSE Q
  E := {0, 1, 2}
  hm := le_refl _
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hw

/-- The three electron lines. -/
def eRX : Fin 3 → Fin 7 := ![0, 1, 2]

theorem eRX_injective : Function.Injective eRX := by decide

theorem det_neg_one : IsUnit (-1 : Matrix (Fin 2) (Fin 2) ℤ).det := by
  simp [Matrix.det_fin_two]

theorem rr_aR : castLoopMatrix aRw = rrAlpha (castLoopMatrix aR) (-1) := by
  funext i r
  fin_cases i <;> fin_cases r <;> simp [castLoopMatrix, aRw, aR, rrAlpha, Fin.sum_univ_two]

theorem rr_aX : castLoopMatrix aXw = rrAlpha (castLoopMatrix aX) (-1) := by
  funext i r
  fin_cases i <;> fin_cases r <;> simp [castLoopMatrix, aXw, aX, rrAlpha, Fin.sum_univ_two]

theorem rr_ppR (p : Fin 4 → ℝ) :
    (fun i => cswRX i • p) = rrMom (castLoopMatrix aR) (ppR p) ![p, p] := by
  funext i
  fin_cases i <;> simp [cswRX, ppR, rrMom, castLoopMatrix, aR, Fin.sum_univ_two]

theorem rr_ppX (p : Fin 4 → ℝ) :
    (fun i => cswRX i • p) = rrMom (castLoopMatrix aX) (ppX p) ![p, p] := by
  funext i
  fin_cases i <;> simp [cswRX, ppX, rrMom, castLoopMatrix, aX, Fin.sum_univ_two]

variable {aw : Fin 7 → Fin 2 → ℤ} (hw : IntNoSubdivergenceRefined 2 {0, 1, 2} aw)
  (Q : QED.WickModel.Params)

/-- **Positivity of `V` for the Ward–Takahashi data** from that of the frozen data. -/
theorem vpos_wtData {a : Fin 7 → Fin 2 → ℤ} {pp : Fin 7 → Fin 4 → ℝ} {p : Fin 4 → ℝ}
    (hα : castLoopMatrix aw = rrAlpha (castLoopMatrix a) (-1))
    (hq : (fun i => cswRX i • p) = rrMom (castLoopMatrix a) pp ![p, p]) {c : ℝ} (hc : 0 < c)
    (h : ∀ z : Fin 7 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU (castLoopMatrix a) z ≠ 0 →
      c ≤ symanzikV (castLoopMatrix a) pp (massesSE Q) z) :
    (wtData aw hw Q).VPos ((wtData aw hw Q).mom p) := by
  refine ⟨c, hc, ?_⟩
  change ∀ z : Fin 7 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
    symanzikU (castLoopMatrix aw) z ≠ 0 →
      c ≤ symanzikV (castLoopMatrix aw) (fun i => cswRX i • p) (massesSE Q) z
  rw [hα, hq]
  exact symanzikV_rr_ge h det_neg_one _

theorem lineMomentum_wtData {a : Fin 7 → Fin 2 → ℤ} {pp : Fin 7 → Fin 4 → ℝ} {p : Fin 4 → ℝ}
    (hα : castLoopMatrix aw = rrAlpha (castLoopMatrix a) (-1))
    (hq : (fun i => cswRX i • p) = rrMom (castLoopMatrix a) pp ![p, p]) (i : Fin 7)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (wtData aw hw Q).α ((wtData aw hw Q).mom p) i ℓ =
      lineMomentum (castLoopMatrix a) pp i (loopAff (-1) ![p, p] ℓ) := by
  change lineMomentum (castLoopMatrix aw) (fun i => cswRX i • p) i ℓ = _
  rw [hα, hq, lineMomentum_rr]

theorem lineDenom_wtData {a : Fin 7 → Fin 2 → ℤ} {pp : Fin 7 → Fin 4 → ℝ} {p : Fin 4 → ℝ}
    (hα : castLoopMatrix aw = rrAlpha (castLoopMatrix a) (-1))
    (hq : (fun i => cswRX i • p) = rrMom (castLoopMatrix a) pp ![p, p]) (ε : ℝ) (i : Fin 7)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (wtData aw hw Q).α ((wtData aw hw Q).mom p) (wtData aw hw Q).M ε i ℓ =
      lineDenom (castLoopMatrix a) pp (massesSE Q) ε i (loopAff (-1) ![p, p] ℓ) := by
  change lineDenom (castLoopMatrix aw) (fun i => cswRX i • p) (massesSE Q) ε i ℓ = _
  rw [hα, hq, lineDenom_rr]

end QED.GradedProof.WI2

end
