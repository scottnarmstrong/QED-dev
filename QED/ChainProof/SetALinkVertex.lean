/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkSum
public import QED.GradedProof.VP2WeightsRelabel
public import QED.Frozen.Graded.FamilyVertex

/-!
# The set (a) vertex as the signed sum of nine class values

Helper for the Phase 5 Stage 3a goal (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(decision D-58), step 1 of its proof graph: the enumeration.

* `QED.ChainProof.SetALink.familyVertex_setA_eq_classes`: at any flavour data `Φ` and counterterm
  data `D`, with incoming photon momentum `p' - p`, the family vertex (Gf₁) of the set (a)
  selection at graded order `7` is `(1/i)` times the signed sum of the graded values (G₅) of the
  nine representatives at their gradings, each with coefficient one: `+` the two `photonCt`
  pairings (level `1`, one loop), `-` the two `gaugeCt` and two `fermionCt` classes (level `0`, two
  loops) and the three two-loop-bubble classes (three loops). The `1/N!` of (G₆) is cancelled by
  the `N!` relabellings of each representative (`QED.ChainProof.SetALink.sum_setA`), which have the
  same value (`QED.GradedProof.VP2.contractionValue_relabelK`).
* `QED.ChainProof.SetALink.isOnePI_of_isSetA_seven`: at graded order `7`, (A₁) implies one-particle
  irreducibility, so the `IsOnePI` clause of the selection of (HA₆) is redundant there.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **(A₁) at graded order `7` implies one-particle irreducibility.** -/
theorem isOnePI_of_isSetA_seven (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    {C : Contraction 1 1 κ} (hC : QED.ThreeLoop.IsSetA C) : IsOnePI C := by
  obtain ⟨R, hR, π, hκ, rfl, -⟩ := exists_rep_setA g hg hC
  exact (isOnePI_relabelK_iff _ _ _).mpr (repsA_props R hR).1

theorem repsA_lt_four (h : N < 4) : repsA N = [] :=
  repsA_eq_nil (by omega) (by omega) (by omega) (by omega)

/-- **The set (a) vertex by vertex number**, at any flavour and counterterm data: `(1/i)` times,
over the numbers of vertices `N ≤ 7`, the signed sum of the graded values of the representatives
with `N` vertices at their gradings, each with coefficient one. -/
theorem familyVertex_setA_eq_reps (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Graded.familyVertex P Φ D (fun C _ => IsOnePI C ∧ QED.ThreeLoop.IsSetA C) 7 p' p μ =
      Matrix.of fun α β => (1 / I) * ∑ N ∈ Finset.range (7 + 1),
        ((repsA N).map fun R => ((fermionSign R.rep : ℤ) : ℂ) *
          Graded.contractionValue P Φ D R.rep R.grad (fun _ => p') (fun _ => p)
            (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)).sum := by
  ext α β
  simp only [Graded.familyVertex, Graded.selectedPart, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  have hmom : ∑ i : Fin 1, (fun _ => p') i =
      ∑ i : Fin 1, (fun _ => p) i + ∑ j : Fin 1, (fun _ => p' - p) j := by
    simp
  have key := sum_setA (N := N) (instF := fun _ => inferInstance)
    (instCF := fun _ => inferInstance) (instCE := fun _ => Classical.decEq _)
    (instG := fun _ => Classical.decPred _) (instC := fun _ => Classical.decPred _)
    (fun C g => Graded.contractionValue P Φ D C g (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ))
    (fun π hκ C g hC => QED.GradedProof.VP2.contractionValue_relabelK P Φ D π hκ hC g hmom _ _ _)
  have hN : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  rw [show (N.factorial : ℂ)⁻¹ * _ = (N.factorial : ℂ)⁻¹ * ((N.factorial : ℂ) *
      ∑ i : Fin (repsA N).length, ((fermionSign ((repsA N).get i).rep : ℤ) : ℂ) *
        Graded.contractionValue P Φ D ((repsA N).get i).rep ((repsA N).get i).grad
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
          (fun _ => μ)) from congrArg _ (by convert key), ← mul_assoc, inv_mul_cancel₀ hN,
    one_mul]
  simp only [List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem (repsA N) fun R => ((fermionSign R.rep : ℤ) : ℂ) *
    Graded.contractionValue P Φ D R.rep R.grad (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ)

/-- **The set (a) vertex is the signed sum of the nine class values, each with coefficient
one**, at any flavour data `Φ` and counterterm data `D`: for all momenta `p'`, `p` (incoming
photon momentum `p' - p`), the family vertex (Gf₁) of the selection `IsOnePI ∧ IsSetA` at graded
order `7` is `(1/i)` times
`V(P₀) + V(P₁) - V(GW) - V(GU) - V(FA) - V(FB) - V(VA) - V(VB) - V(VC)`, with `V` the graded
value (G₅) of the representative at its grading (`gradP`, level `1`, for the `photonCt` classes;
`0` otherwise). -/
theorem familyVertex_setA_eq_classes (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Graded.familyVertex P Φ D (fun C _ => IsOnePI C ∧ QED.ThreeLoop.IsSetA C) 7 p' p μ =
      Matrix.of fun α β =>
        let V := fun {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
            (g : Graded.Grading κ) =>
          Graded.contractionValue P Φ D C g (fun _ => p') (fun _ => p) (fun _ => p' - p)
            (fun _ => α) (fun _ => β) (fun _ => μ)
        (1 / I) * (V (repP 0) gradP + V (repP 1) gradP - V repGW 0 - V repGU 0 - V repFA 0 -
          V repFB 0 - V repVA 0 - V repVB 0 - V repVC 0) := by
  rw [familyVertex_setA_eq_reps]
  ext α β
  simp only [Matrix.of_apply]
  congr 1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  rw [repsA_lt_four (by norm_num : 0 < 4), repsA_lt_four (by norm_num : 1 < 4),
    repsA_lt_four (by norm_num : 2 < 4), repsA_lt_four (by norm_num : 3 < 4)]
  simp only [repsA, repsA4, repsA5, repsA6, repsA7, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fermionSign_repP, fermionSign_repGW, fermionSign_repGU, fermionSign_repFA,
    fermionSign_repFB, fermionSign_repVA, fermionSign_repVB, fermionSign_repVC]
  push_cast
  ring

end QED.ChainProof.SetALink

end
