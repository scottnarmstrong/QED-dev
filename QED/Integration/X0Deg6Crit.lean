/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.X0Deg6One
public import QED.GradedProof.X0OneCtCrit

/-!
# The doubled-line criterion for one-loop open-line contractions

Helper level for the Phase 5 Stage 3 goals (HA₀) and (HS₀) (decision D-58). `DblCrit` is the
one-loop test `QED.GradedProof.X0.OneCrit` with the degree bound `4` raised to `6`: with `L_f`
(`L_g`) loop fermion (photon) edges and `D = ∑ vDegE`, `L_f + D ≤ 6` and
`4 + L_f + D < 2 (L_f + 2 L_g)`. It is decidable on the line data (`lineData`) and gives the
hypotheses of `jointEnergyFirstIntegrable_oneCtDbl` (`dblCrit_bounds`). For a one-loop open-line
contraction with a doubled fermion line at a `fermionCt` vertex, `DblCrit` gives (T₉′) of the
graded integrand at the zero grading (`jointEnergyFirstIntegrable_openCtDbl`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0Deg6

open QED.WickModel QED.GradedProof.X0
open QED.Graded (Counterterms regulatedAmplitude)
open QED.TwoLoop.Enumeration (lineData)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The doubled-line test**: `L_f + D ≤ 6` and `4 + L_f + D < 2 (L_f + 2 L_g)`. -/
def DblCrit (E : Multiset (ℕ × Fin N × Fin N)) (κ : Fin N → Wick.VertexKind) : Prop :=
  edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) + ∑ t, vDegE E κ t ≤ 6 ∧
    4 + (edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) + ∑ t, vDegE E κ t) <
      2 * (edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) +
        2 * edgeCount E false (fun y => edgeCoeff E y 0 ≠ 0))

instance (E : Multiset (ℕ × Fin N × Fin N)) (κ : Fin N → Wick.VertexKind) :
    Decidable (DblCrit E κ) := by
  unfold DblCrit; infer_instance

/-- `DblCrit` gives the counts of `jointEnergyFirstIntegrable_oneCtDbl`. -/
theorem dblCrit_bounds {C : Contraction nf nA κ} (h : DblCrit (lineData C) κ) :
    oneDeg (fun l => loopCoeff C l 0) ≤ 6 ∧
      4 + oneDeg (fun l => loopCoeff C l 0) <
        2 * (loopFermionCount (fun l => loopCoeff C l 0) +
          2 * loopPhotonCount (fun l => loopCoeff C l 0)) := by
  have hF : loopFermionCount (fun l => loopCoeff C l 0) =
      edgeCount (lineData C) true (fun y => edgeCoeff (lineData C) y 0 ≠ 0) :=
    card_filter_fermion (C := C) (fun y => edgeCoeff (lineData C) y 0 ≠ 0)
  have hG : loopPhotonCount (fun l => loopCoeff C l 0) =
      edgeCount (lineData C) false (fun y => edgeCoeff (lineData C) y 0 ≠ 0) :=
    card_filter_photon (C := C) (fun y => edgeCoeff (lineData C) y 0 ≠ 0)
  have hV : ∑ t, vDeg (fun l => loopCoeff C l 0) t ≤ ∑ t, vDegE (lineData C) κ t :=
    Finset.sum_le_sum fun t _ => vDeg_le_vDegE t
  unfold oneDeg
  obtain ⟨h1, h2⟩ := h
  omega

/-- **(T₉′) of the graded integrand of a one-loop open-line contraction with a doubled fermion
line**, at the zero grading, under `DblCrit`. The lines `fi`, `fo` around the `fermionCt` vertex
`fo.1` carry the same loop coefficient (nonzero) and the same external part. -/
theorem jointEnergyFirstIntegrable_openCtDbl (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (hε : 0 < P.ε)
    (C : Contraction 1 1 κ) (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0))
    (hL : loopCount C = 1) (hcrit : DblCrit (lineData C) κ) (fi fo : FermionLine C)
    (hs : fi.tail = fo.1) (hct : κ fo.1.1 = .fermionCt) (hfi : fi.1 ≠ fo.1)
    (hfo : fo.tail ≠ fo.1) (hc : loopCoeff C (.inl fi) 0 = loopCoeff C (.inl fo) 0)
    (hc0 : loopCoeff C (.inl fo) 0 ≠ 0) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (he : extPart C pOut pIn kIn (.inl fi) = extPart C pOut pIn kIn (.inl fo))
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_zero_eq_openCt P Φ D C hcyc, lineMomentum₂_eq_oneMom]
  obtain ⟨hd, hn⟩ := dblCrit_bounds hcrit
  exact jointEnergyFirstIntegrable_oneCtDbl (openCtParams P Φ D) hε C _ _ _ fi fo hs hct hfi
    hfo hc hc0 he rfl hd hn pIn kIn αOut βIn μ _

end QED.GradedProof.X0Deg6

end
