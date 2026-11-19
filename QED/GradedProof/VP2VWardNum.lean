/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VPin
public import QED.GradedProof.VP2FWardAlg

/-!
# The two-loop Ward identity at the integrand level

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. For a class whose
vertex matrices are `γ^μ, B₀, B₁, B₂` in trace order and whose line `3` carries the momentum of
line `0` plus `k`, the identity `N(k + p) k̸ N(p) = D(k + p) N(p) - D(p) N(k + p) + iε k̸` turns the
`k`-contracted integrand of one flavour into two three-line loops (`pN`, the lines `0, 1, 2` and
`1, 2, 3`) and `iε` times the contracted remainder (`ward_gH`).

* `pN`: the numerator of a three-line loop, summed against the photon factor `kV`;
  `pN_eq`, degrees and bounds;
* `ward_trace`: the identity for one trace;
* `ward_gH`: the identity for the integrand of one flavour.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Numerators of three-line loops -/

section PNum

variable (e mγ Λ : ℝ) (Bt : Fin 4 → Fin 4 → Fin 3 → Mat) (base : Fin 5 → Fin 2 → ℤ)
  (pp : Fin 5 → Fin 4 → ℝ) (r : Fin 3 → Fin 4)

/-- The numerator of a three-line loop on the rows `r`, summed against the photon factor. -/
noncomputable def pN (M : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * tr3 (Bt ρ σ) (fun l => electronNumerator M (fm base pp (r l) ℓ))

/-- The coefficient of `M⁰` in `pN`. -/
noncomputable def pNE0 (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * p3E0 (Bt ρ σ) (fun l => fm base pp (r l) ℓ)

/-- The coefficient of `M²` in `pN`. -/
noncomputable def pNE2 (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * p3E2 (Bt ρ σ) (fun l => fm base pp (r l) ℓ)

theorem pN_eq (hB : ∀ ρ σ l, IsOddG (Bt ρ σ l)) (M : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    pN e mγ Λ Bt base pp r M ℓ =
      pNE0 e mγ Λ Bt base pp r ℓ + (M : ℂ) ^ 2 * pNE2 e mγ Λ Bt base pp r ℓ := by
  simp only [pN, pNE0, pNE2, tr3_eq (hB _ _), Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isLoopPoly_pN (M : ℝ) : IsLoopPoly 2 3 (pN e mγ Λ Bt base pp r M) := by
  refine IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ => IsLoopPoly.const_mul _ ?_
  have N := fun l => isLoopPolyMat_fm base pp (r l) M
  have C := fun l => IsLoopPolyMat.const (L := 2) (Bt ρ σ l)
  exact (((((((C 0).mul (N 0)).mul (C 1)).mul (N 1)).mul (C 2)).mul (N 2)).trace).mono
    (by norm_num)

theorem isLoopPoly_pNE2 : IsLoopPoly 2 1 (pNE2 e mγ Λ Bt base pp r) := by
  refine IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ => IsLoopPoly.const_mul _ ?_
  have N := fun l => isLoopPolyMat_fm base pp (r l) 0
  have C := fun l => IsLoopPolyMat.const (L := 2) (Bt ρ σ l)
  unfold p3E2
  refine ((?_ : IsLoopPoly 2 1 _).add ?_).add ?_
  · exact ((C 0).mul ((C 1).mul ((C 2).mul (N 2)))).trace.mono (by norm_num)
  · exact ((C 0).mul ((C 1).mul ((N 1).mul (C 2)))).trace.mono (by norm_num)
  · exact ((C 0).mul ((N 0).mul ((C 1).mul (C 2)))).trace.mono (by norm_num)

/-- The bound of a three-line numerator on the three lines carrying its momenta. -/
theorem rb_pN {m : ℕ} (sh : Fin (m + 1) → Fin 5) (e3 : Fin 3 → Fin (m + 1))
    (he : ∀ l, sh (e3 l) = (r l).castSucc) (h01 : e3 0 ≠ e3 1) (h02 : e3 0 ≠ e3 2)
    (h12 : e3 1 ≠ e3 2) (M : ℝ) :
    RefinedBound (castLoopMatrix fun k => base (sh k)) {e3 0, e3 1, e3 2} 3
      (pN e mγ Λ Bt base pp r M) := by
  refine RefinedBound.sum _ fun ρ _ => RefinedBound.sum _ fun σ _ => RefinedBound.const_mul _ ?_
  have N := fun l => rbm_fm base pp sh (e3 l) (r l) (he l) M
  have h0 : RefinedBoundMat (castLoopMatrix fun k => base (sh k)) ∅ 0 fun _ => Bt ρ σ 0 :=
    RefinedBoundMat.const _
  have h := RefinedBoundMat.trace (RBM.mulN (RBM.mulC (RBM.mulN (RBM.mulC (RBM.mulN h0 (N 0)
    (Finset.notMem_empty _)) (Bt ρ σ 1)) (N 1) (by simp [h01.symm])) (Bt ρ σ 2)) (N 2)
    (by simp [h02.symm, h12.symm]))
  refine h.mono (fun x hx => ?_) le_rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/-- The bound of the `M²` coefficient on the three lines carrying its momenta. -/
theorem rb_pNE2 {m : ℕ} (sh : Fin (m + 1) → Fin 5) (e3 : Fin 3 → Fin (m + 1))
    (he : ∀ l, sh (e3 l) = (r l).castSucc) :
    RefinedBound (castLoopMatrix fun k => base (sh k)) {e3 0, e3 1, e3 2} 1
      (pNE2 e mγ Λ Bt base pp r) := by
  refine RefinedBound.sum _ fun ρ _ => RefinedBound.sum _ fun σ _ => RefinedBound.const_mul _ ?_
  have N := fun l => rbm_fm base pp sh (e3 l) (r l) (he l) 0
  have h1 := RefinedBoundMat.trace
    (RBM.cMul (Bt ρ σ 0) (RBM.cMul (Bt ρ σ 1) (RBM.cMul (Bt ρ σ 2) (N 2))))
  have h2 := RefinedBoundMat.trace
    (RBM.cMul (Bt ρ σ 0) (RBM.cMul (Bt ρ σ 1) (RBM.mulC (N 1) (Bt ρ σ 2))))
  have h3 := RefinedBoundMat.trace
    (RBM.cMul (Bt ρ σ 0) (RBM.mulC (N 0) (Bt ρ σ 1 * Bt ρ σ 2)))
  have s : ∀ l, ({e3 l} : Finset (Fin (m + 1))) ⊆ {e3 0, e3 1, e3 2} := fun l => by
    fin_cases l <;> simp
  exact ((h1.mono (s 2) le_rfl).add (h2.mono (s 1) le_rfl)).add (h3.mono (s 0) le_rfl)

end PNum

/-! ### The identity -/

theorem sum_lower_trace_left (k : Fin 4 → ℝ) (R : Mat) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * (Dirac.gamma μ * R).trace =
      (Dirac.slash k * R).trace := by
  simpa using sum_lower_trace k 1 R

/-- **The Ward identity for one trace.** -/
theorem ward_trace (B : Fin 3 → Mat) (M ε : ℝ) (k y0 y1 y2 : Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        vT ![Dirac.gamma μ, B 0, B 1, B 2] M ![y0, y1, y2, k + y0] =
      propDenom M ε (k + y0) * tr3 ![B 2, B 0, B 1]
          ![electronNumerator M y0, electronNumerator M y1, electronNumerator M y2] -
        propDenom M ε y0 * tr3 B
          ![electronNumerator M y1, electronNumerator M y2, electronNumerator M (k + y0)] +
        (ε : ℂ) * I * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          rT ![Dirac.gamma μ, B 0, B 1, B 2] M y1 y2 := by
  set N0 := electronNumerator M y0
  set N1 := electronNumerator M y1
  set N2 := electronNumerator M y2
  set N3 := electronNumerator M (k + y0)
  set R := B 0 * N1 * B 1 * N2 * B 2
  have hv : ∀ μ, vT ![Dirac.gamma μ, B 0, B 1, B 2] M ![y0, y1, y2, k + y0] =
      (Dirac.gamma μ * (N0 * R * N3)).trace := fun μ => by
    simp only [vT, R, Matrix.cons_val, Matrix.mul_assoc]; rfl
  have hr : ∀ μ, rT ![Dirac.gamma μ, B 0, B 1, B 2] M y1 y2 = (Dirac.gamma μ * R).trace :=
    fun μ => by simp only [rT, R, Matrix.cons_val, Matrix.mul_assoc]; rfl
  simp only [hv, hr, sum_lower_trace_left]
  have hw := wardF_num M ε k y0
  have e1 : (Dirac.slash k * (N0 * R * N3)).trace = (N3 * Dirac.slash k * N0 * R).trace := by
    rw [show Dirac.slash k * (N0 * R * N3) = (Dirac.slash k * N0 * R) * N3 by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have e2 : tr3 ![B 2, B 0, B 1] ![N0, N1, N2] = (N0 * R).trace := by
    simp only [tr3, R, Matrix.cons_val]
    rw [show B 2 * N0 * B 0 * N1 * B 1 * N2 = B 2 * (N0 * B 0 * N1 * B 1 * N2) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have e3 : tr3 B ![N1, N2, N3] = (N3 * R).trace := by
    simp only [tr3, R, Matrix.cons_val]
    rw [show B 0 * N1 * B 1 * N2 * B 2 * N3 = (B 0 * N1 * B 1 * N2 * B 2) * N3 by rfl,
      Matrix.trace_mul_comm]
  rw [e1, hw, e2, e3]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rfl

section Ward

variable (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
  (B : Fin 4 → Fin 4 → Fin 4 → Fin 3 → Mat) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

/-- The vertex matrices of the first pinched loop (lines `0, 1, 2`). -/
def bt1 (ν : Fin 4) : Fin 4 → Fin 4 → Fin 3 → Mat := fun ρ σ =>
  ![B ν ρ σ 2, B ν ρ σ 0, B ν ρ σ 1]

theorem sum_lower_gH (k : Fin 4 → ℝ) (C P : ℂ) (g : Fin 4 → Fin 4 → ℂ)
    (f : Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * (C * ((∑ ρ, ∑ σ, g ρ σ * f μ ρ σ) * P)) =
      ∑ ρ, ∑ σ, C * g ρ σ * P * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * f μ ρ σ := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ => by ring

theorem sum_form (C P : ℂ) (g f : Fin 4 → Fin 4 → ℂ) :
    C * ((∑ ρ, ∑ σ, g ρ σ * f ρ σ) * P) = ∑ ρ, ∑ σ, C * g ρ σ * P * f ρ σ := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The Ward identity for the integrand of one flavour.** -/
theorem ward_gH (hA : ∀ μ ν ρ σ, A μ ν ρ σ = ![Dirac.gamma μ, B ν ρ σ 0, B ν ρ σ 1, B ν ρ σ 2])
    (hl : ∀ k ℓ, fm base (ppc c k) 3 ℓ = k + fm base (ppc c k) 0 ℓ) (M : ℝ) {ε : ℝ}
    (hε : ε ≠ 0) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (ν : Fin 4) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        gH base c (vNum e mγ Λ A base c) mγ Λ M ε k ℓ μ ν =
      g3 base (ppc c k) ![0, 1, 2] (pN e mγ Λ (bt1 B ν) base (ppc c k) ![0, 1, 2]) mγ Λ M ε ℓ -
        g3 base (ppc c k) ![1, 2, 3] (pN e mγ Λ (B ν) base (ppc c k) ![1, 2, 3]) mγ Λ M ε ℓ +
        (ε : ℂ) * I * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          gH base c (rNum e mγ Λ A base c) mγ Λ M ε k ℓ μ ν := by
  have hy3 : fm base (ppc c k) 3 ℓ = k + fm base (ppc c k) 0 ℓ := hl k ℓ
  have hy4 : (fun l => fm base (ppc c k) l ℓ) = ![fm base (ppc c k) 0 ℓ,
      fm base (ppc c k) 1 ℓ, fm base (ppc c k) 2 ℓ, k + fm base (ppc c k) 0 ℓ] := by
    funext l
    fin_cases l <;> simp [hy3]
  have ht : ∀ ρ σ, ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        vT (A μ ν ρ σ) M (fun l => fm base (ppc c k) l ℓ) =
      propDenom M ε (fm base (ppc c k) 3 ℓ) * tr3 (bt1 B ν ρ σ)
          (fun l => electronNumerator M (fm base (ppc c k) (![0, 1, 2] l) ℓ)) -
        propDenom M ε (fm base (ppc c k) 0 ℓ) * tr3 (B ν ρ σ)
          (fun l => electronNumerator M (fm base (ppc c k) (![1, 2, 3] l) ℓ)) +
        (ε : ℂ) * I * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          rT (A μ ν ρ σ) M (fm base (ppc c k) 1 ℓ) (fm base (ppc c k) 2 ℓ) := fun ρ σ => by
    have f1 : (fun l : Fin 3 => electronNumerator M (fm base (ppc c k) (![0, 1, 2] l) ℓ)) =
        ![electronNumerator M (fm base (ppc c k) 0 ℓ),
          electronNumerator M (fm base (ppc c k) 1 ℓ),
          electronNumerator M (fm base (ppc c k) 2 ℓ)] := by
      funext l
      fin_cases l <;> rfl
    have f2 : (fun l : Fin 3 => electronNumerator M (fm base (ppc c k) (![1, 2, 3] l) ℓ)) =
        ![electronNumerator M (fm base (ppc c k) 1 ℓ),
          electronNumerator M (fm base (ppc c k) 2 ℓ),
          electronNumerator M (k + fm base (ppc c k) 0 ℓ)] := by
      funext l
      fin_cases l <;> simp [hy3]
    simp only [hA]
    rw [hy4, ward_trace (B ν ρ σ) M ε k _ _ _, f1, f2, hy3]
    rfl
  have d := fun l => propDenom_ne_zero (M := M) hε (fm base (ppc c k) l ℓ)
  simp only [gH, vNum, rNum, sum_lower_gH]
  simp only [ht]
  simp only [g3, pN, sum_form]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum _ _ ((ε : ℂ) * I), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum _ _ ((ε : ℂ) * I), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val]
  have d0 := d 0
  have d3 := d 3
  field_simp

end Ward

end QED.GradedProof.VP2

end
