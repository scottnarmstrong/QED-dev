/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkSum
public import QED.GradedProof.VP2WeightsRelabel
public import QED.Frozen.Graded.FamilyVertex

/-!
# The set (c) vertex as the signed sum of the 56 orbit values

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step.

* `QED.ChainProof.SetCLink.familyVertex_setC_eq_classes`: at any flavour data `Φ` and counterterm
  data `D`, with incoming photon momentum `p' - p`, the family vertex (Gf₁) of the selection
  `IsOnePI ∧ IsSetC` at graded order `7` is `(1/i)` times the signed sum of the graded values (G₅)
  of the 56 representatives at their gradings, each with coefficient one: `-` the 12 bubble
  graphs, `+` the 24 `δ₃` graphs, `-` the 5 one-loop graphs with a counterterm and a bubble, `+`
  the 10 with a counterterm and a `δ₃`, `+` the 5 VP-share counterterm graphs (level `1`). The
  `1/N!` of (G₆) is cancelled by the `N!` relabellings of each representative
  (`QED.ChainProof.SetCLink.sum_setC`), which have the same value
  (`QED.GradedProof.VP2.contractionValue_relabelK`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum

theorem sum_flatMap_C {α : Type*} (l : List α) (f : α → List ℂ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem repsC_lt_three {N : ℕ} (h : N < 3) : repsC N = [] := by
  rw [repsC, repsCZ_eq_nil (by omega) (by omega) (by omega) (by omega),
    repsCS_eq_nil (by omega) (by omega)]
  rfl

/-- **The set (c) vertex by vertex number**, at any flavour and counterterm data: `(1/i)` times,
over the numbers of vertices `N ≤ 7`, the signed sum of the graded values of the representatives
with `N` vertices at their gradings, each with coefficient one. -/
theorem familyVertex_setC_eq_reps (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Graded.familyVertex P Φ D (fun C g => IsOnePI C ∧ QED.ThreeLoop.IsSetC C g) 7 p' p μ =
      Matrix.of fun α β => (1 / I) * ∑ N ∈ Finset.range (7 + 1),
        ((repsC N).map fun R => ((fermionSign R.rep : ℤ) : ℂ) *
          Graded.contractionValue P Φ D R.rep R.grad (fun _ => p') (fun _ => p)
            (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)).sum := by
  ext α β
  simp only [Graded.familyVertex, Graded.selectedPart, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  have hmom : ∑ i : Fin 1, (fun _ => p') i =
      ∑ i : Fin 1, (fun _ => p) i + ∑ j : Fin 1, (fun _ => p' - p) j := by
    simp
  have key := sum_setC (N := N) (instF := fun _ => inferInstance)
    (instCF := fun _ => inferInstance) (instCE := fun _ => Classical.decEq _)
    (instG := fun _ => Classical.decPred _) (instC := fun _ _ => Classical.decPred _)
    (fun C g => Graded.contractionValue P Φ D C g (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ))
    (fun π hκ C g hC => QED.GradedProof.VP2.contractionValue_relabelK P Φ D π hκ hC g hmom _ _ _)
  have hN : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  rw [show (N.factorial : ℂ)⁻¹ * _ = (N.factorial : ℂ)⁻¹ * ((N.factorial : ℂ) *
      ∑ i : Fin (repsC N).length, ((fermionSign ((repsC N).get i).rep : ℤ) : ℂ) *
        Graded.contractionValue P Φ D ((repsC N).get i).rep ((repsC N).get i).grad
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
          (fun _ => μ)) from congrArg _ (by convert key), ← mul_assoc, inv_mul_cancel₀ hN,
    one_mul]
  simp only [List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem (repsC N) fun R => ((fermionSign R.rep : ℤ) : ℂ) *
    Graded.contractionValue P Φ D R.rep R.grad (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ)

/-- **The set (c) vertex is the signed sum of the 56 orbit values, each with coefficient one**,
at any flavour data `Φ` and counterterm data `D`: for all momenta `p'`, `p` (incoming photon
momentum `p' - p`), the family vertex (Gf₁) of the selection `IsOnePI ∧ IsSetC` at graded order
`7` is `(1/i)` times
`-∑ᵢ V(Bᵢ) + ∑ᵢ ∑ₛ V(Dᵢₛ) - ∑ₖ V(CBₖ) + ∑ₖ ∑ₛ V(CDₖₛ) + ∑ₖ V(Sₖ)`, with `V` the graded value
(G₅) of the representative at its grading (`0` except `gOne`, level `1`, for the VP-share
counterterm graphs `Sₖ`). -/
theorem familyVertex_setC_eq_classes (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Graded.familyVertex P Φ D (fun C g => IsOnePI C ∧ QED.ThreeLoop.IsSetC C g) 7 p' p μ =
      Matrix.of fun α β =>
        let V := fun {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
            (g : Graded.Grading κ) =>
          Graded.contractionValue P Φ D C g (fun _ => p') (fun _ => p) (fun _ => p' - p)
            (fun _ => α) (fun _ => β) (fun _ => μ)
        (1 / I) * (-(∑ i : Fin 12, V (repB i) 0) + ∑ i : Fin 12, ∑ s : Fin 2, V (repD i s) 0 -
          (V repCB0 0 + V repCB1 0 + V repCB2 0 + V repCB3 0 + V repCB4 0) +
          ∑ s : Fin 2, (V (repCD0 s) 0 + V (repCD1 s) 0 + V (repCD2 s) 0 + V (repCD3 s) 0 +
            V (repCD4 s) 0) +
          (V repS0 (gOne _) + V repS1 (gOne _) + V repS2 (gOne _) + V repS3 (gOne _) +
            V repS4 (gOne _))) := by
  rw [familyVertex_setC_eq_reps]
  ext α β
  simp only [Matrix.of_apply]
  congr 1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  rw [repsC_lt_three (by norm_num : 0 < 3), repsC_lt_three (by norm_num : 1 < 3),
    repsC_lt_three (by norm_num : 2 < 3)]
  simp only [repsC, repsCZ, repsCS, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.map_append, List.sum_append, List.map_map, List.map_flatMap, sum_flatMap_C,
    Function.comp_def, ← Fin.sum_univ_def, fermionSign_repB, fermionSign_repD,
    fermionSign_repCB0, fermionSign_repCB1, fermionSign_repCB2, fermionSign_repCB3,
    fermionSign_repCB4, fermionSign_repCD0, fermionSign_repCD1, fermionSign_repCD2,
    fermionSign_repCD3, fermionSign_repCD4, fermionSign_repS0, fermionSign_repS1,
    fermionSign_repS2, fermionSign_repS3, fermionSign_repS4, Fin.sum_univ_two]
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_one_mul, one_mul]
  ring

end QED.ChainProof.SetCLink

end
