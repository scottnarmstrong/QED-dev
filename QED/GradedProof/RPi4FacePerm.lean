/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRate

/-!
# (R-Π₄) step L6d2: the face sector of a collapsed piece in its own line order

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. The face results
of `RPi4FaceRate` are stated for a `FaceShape`, whose lines are sorted face block first with the
photon last in the face block. A collapsed piece comes with its own line order; a permutation `e`
of the lines that sorts it (`FaceSort`) turns it into a `FaceShape` (`FaceSort.shape`), and the
face sector of the piece, cut by the weight of its face lines (`faceSum`: the lines whose loop row
is not `(1, 0)`), is the face sector of that shape:

* `paramAtV_perm`, `symanzikV_perm`, `symanzikU_perm` (relabelling the lines);
* `pieceF` (the collapsed integrand `z_γ paramAtV(V₀ + z_γ u)` of a piece), `faceSum`;
* `FaceSort`, `FaceSort.shape`, `FaceSort.fU_eq`, `FaceSort.blockSum_eq`;
* **`FaceSort.face_rate_piece`**: the face-sector rate `u^{-1/2}` for a family of pieces, in the
  piece's own line order, uniformly over the family.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)
open QED.Integration.SimplexMerge (integral_simplex_comp_perm integrableOn_simplex_comp_perm_iff)

/-! ### Relabelling the lines -/

section Perm

variable {k m : ℕ} (e : Fin (k + 1) ≃ Fin (m + 1)) (α : Fin (m + 1) → Fin 2 → ℝ)
  (pp : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (k + 1) → ℝ)

theorem sum_mul_perm (f : Fin (m + 1) → ℝ) :
    ∑ i, z i * f (e i) = ∑ j, z (e.symm j) * f j := by
  rw [← e.sum_comp (fun j => z (e.symm j) * f j)]
  simp

theorem symanzikMatrix_perm :
    symanzikMatrix (fun i => α (e i)) z = symanzikMatrix α fun j => z (e.symm j) := by
  ext s t
  simp only [symanzikMatrix, Matrix.of_apply, mul_assoc]
  exact sum_mul_perm e z fun j => α j s * α j t

theorem symanzikU_perm : symanzikU (fun i => α (e i)) z = symanzikU α fun j => z (e.symm j) := by
  rw [symanzikU, symanzikMatrix_perm, symanzikU]

theorem symanzikVector_perm :
    symanzikVector (fun i => α (e i)) (fun i => pp (e i)) z =
      symanzikVector α pp fun j => z (e.symm j) := by
  funext s μ
  simp only [symanzikVector, mul_assoc]
  exact sum_mul_perm e z fun j => α j s * pp j μ

theorem loopShift_perm :
    loopShift (fun i => α (e i)) (fun i => pp (e i)) z = loopShift α pp fun j => z (e.symm j) := by
  funext s μ
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply, QED.TwoLoop.LimitCovariance.loopShift_apply,
    symanzikMatrix_perm]
  have h : ∀ t, ∑ i, z i * α (e i) t * pp (e i) μ =
      ∑ j, z (e.symm j) * α j t * pp j μ := fun t => by
    simp only [mul_assoc]
    exact sum_mul_perm e z fun j => α j t * pp j μ
  simp only [h]

/-- **Relabelling the lines leaves the integrand unchanged.** -/
theorem paramAtV_perm (n : ℕ) (Q : LoopQuartic) (v : ℝ) :
    paramAtV n Q (fun i => α (e i)) (fun i => pp (e i)) z v =
      paramAtV n Q α pp (fun j => z (e.symm j)) v := by
  simp only [paramAtV, symanzikU_perm, symanzikMatrix_perm, loopShift_perm]

/-- **Relabelling the lines leaves `V` unchanged.** -/
theorem symanzikV_perm (M : Fin (m + 1) → ℝ) :
    symanzikV (fun i => α (e i)) (fun i => pp (e i)) (fun i => M (e i)) z =
      symanzikV α pp M fun j => z (e.symm j) := by
  rw [symanzikV, symanzikV, symanzikMatrix_perm, symanzikVector_perm,
    sum_mul_perm e z fun j => M j ^ 2 + Minkowski.dot (pp j) (pp j)]

end Perm

/-! ### The collapsed integrand of a piece and its face weight -/

/-- **The collapsed integrand of a piece**: `z_γ paramAtV(V₀(z) + z_γ u)` (photon line `γ`). -/
noncomputable def pieceF {m : ℕ} (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ)
    (z : Fin (m + 1) → ℝ) : ℂ :=
  (z γ : ℂ) * paramAtV n Q α pp z (symanzikV α pp M z + z γ * u)

/-- **The face weight of a piece**: the sum of the weights of the lines whose loop row is not
`(1, 0)` (for a loop-`1` face these are the lines of the face block). -/
noncomputable def faceSum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => α l ≠ ![1, 0]), z l

theorem measurable_faceSum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) :
    Measurable (faceSum α) := by
  unfold faceSum
  fun_prop

theorem row01_ne : (![0, 1] : Fin 2 → ℝ) ≠ ![1, 0] := fun h => by
  have := congrFun h 0
  simp at this

theorem row1m1_ne : (![1, -1] : Fin 2 → ℝ) ≠ ![1, 0] := fun h => by
  have := congrFun h 1
  norm_num at this

/-! ### Sorting a piece face block first -/

/-- **A permutation sorting a piece face block first**: the first `p + 2` lines (in the order of
`e`) have loop rows `(0, 1)` or `(1, -1)`, the last `q + 1` have row `(1, 0)`. -/
structure FaceSort (p q : ℕ) (α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ)
    (e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))) : Prop where
  hF : ∀ i : Fin (p + 1 + 1), α (e (Fin.castAdd (q + 1) i)) = ![0, 1] ∨
    α (e (Fin.castAdd (q + 1) i)) = ![1, -1]
  hR : ∀ j : Fin (q + 1), α (e (Fin.natAdd (p + 1 + 1) j)) = ![1, 0]

namespace FaceSort

variable {p q : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))} (h : FaceSort p q α e)

/-- The photon line of a sorted piece: the last line of the face block. -/
def gam (e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))) : Fin (p + 1 + 1 + q + 1) :=
  e (Fin.castAdd (q + 1) (Fin.last (p + 1)))

/-- **The face shape of a sorted piece.** -/
def shape (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (p + 1 + 1 + q + 1) → ℝ) :
    FaceShape (p + 1) q where
  αF i := α (e (Fin.castAdd (q + 1) i))
  pF i := pp (e (Fin.castAdd (q + 1) i))
  MF i := M (e (Fin.castAdd (q + 1) i))
  pR j := pp (e (Fin.natAdd (p + 1 + 1) j))
  MR j := M (e (Fin.natAdd (p + 1 + 1) j))
  γ := Fin.last (p + 1)
  hF := h.hF

variable (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (p + 1 + 1 + q + 1) → ℝ)

theorem shape_γ : (h.shape pp M).γ = Fin.last (p + 1) := rfl

theorem shape_α : (h.shape pp M).α = fun i => α (e i) := by
  funext i
  refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) i
  · simp [FaceShape.α, joinA, shape]
  · simp [FaceShape.α, joinA, shape, h.hR j]

theorem shape_pp : (h.shape pp M).pp = fun i => pp (e i) := by
  funext i
  refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) i <;>
    simp [FaceShape.pp, joinA, shape]

theorem shape_M : (h.shape pp M).M = fun i => M (e i) := by
  funext i
  refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) i <;>
    simp [FaceShape.M, joinA, shape]

/-- **The collapsed integrand of the shape is that of the piece**, relabelled. -/
theorem fU_eq (h : FaceSort p q α e) (n : ℕ) (Q : LoopQuartic) (u : ℝ)
    (z : Fin (p + 1 + 1 + q + 1) → ℝ) :
    (h.shape pp M).fU n Q u z = pieceF n Q α pp M (gam e) u fun j => z (e.symm j) := by
  have hg : z (e.symm (gam e)) = z (h.shape pp M).γJ := by
    simp [gam, FaceShape.γJ, shape]
  rw [FaceShape.fU, pieceF, hg, h.shape_α, h.shape_pp, h.shape_M, paramAtV_perm,
    symanzikV_perm]

/-- **The weight of the face block is the face weight of the piece**, relabelled. -/
theorem blockSum_eq (h : FaceSort p q α e) (z : Fin (p + 1 + 1 + q + 1) → ℝ) :
    FaceShape.blockSum (p := p + 1) (q := q) z = faceSum α fun j => z (e.symm j) := by
  rw [faceSum, Finset.sum_filter]
  rw [← Equiv.sum_comp e (fun l => if α l ≠ ![1, 0] then z (e.symm l) else 0)]
  simp only [Equiv.symm_apply_apply]
  rw [sum_join (p := p + 1) (q := q), FaceShape.blockSum]
  have h1 : ∀ i : Fin (p + 1 + 1), α (e (Fin.castAdd (q + 1) i)) ≠ ![1, 0] := fun i => by
    rcases h.hF i with hi | hi <;> rw [hi]
    · exact row01_ne
    · exact row1m1_ne
  simp only [h1, h.hR, ne_eq, not_true_eq_false, ite_false, ite_true, not_false_eq_true,
    Finset.sum_const_zero, add_zero]

end FaceSort

/-! ### The face rate of a family of sorted pieces -/

namespace FaceSort

variable {ι : Type*} {p q r : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))}

/-- **The face sector of a family of pieces, in the piece's own line order, with rate
`u^{-1/2}` uniform over the family.** The hypotheses on the shapes (`kF`, `kM` bounds and the
uniform Lipschitz bounds `hD` of the bracket coefficients) are those of `FaceShape.FamHyp`; the
lower bound on `V₀` is asked in the piece's own coordinates, on the part of the simplex where
the photon weight is at most `ρ₀` and `U ≠ 0`. -/
theorem face_rate_piece (h : FaceSort p q α e) (pp : ι → Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ)
    (M : ι → Fin (p + 1 + 1 + q + 1) → ℝ) (n : ℕ) (Q : ι → LoopQuartic) (B : ι → FaceBr r)
    (k : Fin r → ℕ) {ρ₀ c₁ K KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hK : ∀ s, (h.shape (pp s) (M s)).kF ≤ K) (hKM : ∀ s, (h.shape (pp s) (M s)).kM ≤ KM)
    (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j) (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (h.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i)))
    (hV : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (gam e) ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) (gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) (gam e) u)
            (simplexPoint x)) -
        ∫ σ in Ioi 0, (h.shape (pp s) (M s)).gJ (B s) 0 σ‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
  set S : ι → FaceShape (p + 1) q := fun s => h.shape (pp s) (M s) with hS
  have hVS : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ ≤ symanzikV (S s).α (S s).pp (S s).M
        (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)) := by
    intro s ρ hρ hρ' x hx
    obtain ⟨hW0, hW1⟩ := simplexPoint_mem_stdSimplex hx.1
    obtain ⟨hV0, hV1⟩ := simplexPoint_mem_stdSimplex hx.2
    set W := simplexPoint x.1
    set V := simplexPoint x.2
    set z := joinZ ρ W V with hz
    have hρ1 : ρ < 1 := hρ'.trans_lt hρ₁
    have hz0 : ∀ l, 0 ≤ z l := fun l => by
      refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) l
      · simp only [hz, joinZ, Fin.append_left, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg hρ.le (hW0 i)
      · simp only [hz, joinZ, Fin.append_right, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hV0 j)
    have hz1 : ∑ l, z l = 1 := by
      rw [sum_join]
      simp only [hz, joinZ, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum, hW1, hV1]
      ring
    have hU : symanzikU (S s).α z ≠ 0 := by
      rw [symanzikU, det_face ((S s).isFaceMat ρ W V)]
      have := (S s).uJ_ge ρ W V hW0 hW1 hV1 hρ.le
      exact mul_ne_zero hρ.ne' (by unfold FaceShape.uJ at this; linarith)
    have hzγ : z (S s).γJ ≤ ρ₀ := by
      rw [hz, (S s).joinZ_γJ]
      have hWγ : W (S s).γ ≤ 1 := by
        rw [← hW1]
        exact Finset.single_le_sum (fun i _ => hW0 i) (Finset.mem_univ _)
      nlinarith [hW0 (S s).γ]
    have := hV s (fun j => z (e.symm j)) (fun l => hz0 _)
      (by rw [← hz1]; exact e.symm.sum_comp z)
      (by rwa [← symanzikU_perm, ← h.shape_α (pp s) (M s)])
      (by simpa only [gam, Equiv.symm_apply_apply] using
        (show z (Fin.castAdd (q + 1) (Fin.last (p + 1))) ≤ ρ₀ from hzγ))
    rwa [← symanzikV_perm, ← h.shape_α (pp s) (M s), ← h.shape_pp (pp s) (M s),
      ← h.shape_M (pp s) (M s)] at this
  have hF : FaceShape.FamHyp S B k ρ₀ c₁ K KM :=
    ⟨hρ₀, hρ₁, hc₁, hK, hKM, hkc, hk, hB, hD, hVS⟩
  have hRep' : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp := fun s => by
    rw [hS]
    dsimp only
    rw [h.shape_α, h.shape_pp]
    exact hRep s
  obtain ⟨C, hC⟩ := FaceShape.face_sector_rate hF (fun s => rfl) hRep'
  refine ⟨C, fun s u hu hf => ?_⟩
  have hfU : ∀ z, (S s).fU n (Q s) u z =
      pieceF n (Q s) α (pp s) (M s) (gam e) u fun j => z (e.symm j) := fun z =>
    h.fU_eq (pp s) (M s) n (Q s) u z
  have hf' : IntegrableOn (fun x => (S s).fU n (Q s) u (simplexPoint x))
      (simplexSet (p + 1 + 1 + q)) := by
    simp only [hfU]
    exact (integrableOn_simplex_comp_perm_iff e.symm
      (pieceF n (Q s) α (pp s) (M s) (gam e) u)).mpr hf
  have hint : ∫ x in simplexSet (p + 1 + 1 + q),
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) (gam e) u)
        (simplexPoint x) =
      ∫ x in simplexSet (p + 1 + 1 + q),
        {z | FaceShape.blockSum (p := p + 1) (q := q) z ≤ ρ₀}.indicator ((S s).fU n (Q s) u)
          (simplexPoint x) := by
    rw [← integral_simplex_comp_perm e.symm]
    refine setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => ?_
    simp only [indicator, mem_ofPred_eq, h.blockSum_eq, hfU]
    rfl
  rw [hint]
  exact hC s u hu hf'

end FaceSort

end QED.GradedProof.RPi4

end
