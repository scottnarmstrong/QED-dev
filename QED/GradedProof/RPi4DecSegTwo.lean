/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecTwoInt

/-!
# (R-Π₄) step L9: parametric values have bounded second differences along a segment

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`). The second-order counterpart of `QED.GradedProof.RPi4.DecSegLip`.

* `DecSegTwo k₀ w G`: `u ↦ G(k(u))` is of class `QED.GradedProof.RPi4.DecTwoReg` on
  `[-1/2, 1/2]`; closed under sums, constants and agreement on the segment.
* `dec_segTwo_pvOf_line`: the parametric value along a segment (hypotheses as in
  `QED.GradedProof.RPi4.dec_segLip_pvOf_line`).
* `dec_segTwo_kinds`: eight-line kinds along a segment below threshold.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Polynomial
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Second differences along the segment -/

/-- `u ↦ G(k(u))` along the segment `lineK k₀ w u` is of class `DecTwoReg` on `[-1/2, 1/2]`. -/
def DecSegTwo (k₀ w : Fin 4 → ℝ) (G : (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ M L K : ℝ, DecTwoReg (-(1 / 2)) (1 / 2) (fun u => G (lineK k₀ w u)) M L K

namespace DecSegTwo

variable {k₀ w : Fin 4 → ℝ} {G H : (Fin 4 → ℝ) → ℂ}

theorem add (hG : DecSegTwo k₀ w G) (hH : DecSegTwo k₀ w H) :
    DecSegTwo k₀ w fun k => G k + H k := by
  obtain ⟨_, _, _, h₁⟩ := hG
  obtain ⟨_, _, _, h₂⟩ := hH
  exact ⟨_, _, _, h₁.add h₂⟩

theorem const_mul (hG : DecSegTwo k₀ w G) (a : ℂ) : DecSegTwo k₀ w fun k => a * G k := by
  obtain ⟨_, _, _, h⟩ := hG
  exact ⟨_, _, _, h.const_mul a⟩

theorem zero : DecSegTwo k₀ w fun _ => 0 := ⟨_, _, _, DecTwoReg.zero⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, DecSegTwo k₀ w (G i)) : DecSegTwo k₀ w fun k => ∑ i ∈ s, G i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : DecSegTwo k₀ w fun _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : DecSegTwo k₀ w G)
    (e : ∀ u : ℝ, |u| ≤ 1 / 2 → G (lineK k₀ w u) = H (lineK k₀ w u)) :
    DecSegTwo k₀ w H := by
  obtain ⟨_, _, _, h⟩ := hG
  exact ⟨_, _, _, h.congr fun u hu => e u (abs_le.mpr hu)⟩

end DecSegTwo

/-! ### Parametric values along a line of momenta -/


/-- **Second differences of the parametric value along a line of momenta** (hypotheses as in
`dec_segCont_pvOf_line`, plus the span condition for the bound on `V`). -/
theorem dec_segTwo_pvOf_line {m : ℕ} (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (paramNum Q α q M) (simplexSet m))
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ u : ℝ, |u| ≤ 1 / 2 →
      c ≤ symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x)) :
    DecSegTwo k₀ w fun k => pvOf (N k) α (fun i => cs i • k) M := by
  classical
  set mom : ℝ → Fin (m + 1) → Fin 4 → ℝ := fun u i => cs i • lineK k₀ w u with hmom_def
  have hmom : ∀ i ν, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i ν : ℝ) : ℂ) :=
    fun i ν => isUPoly_lineK (cs i) k₀ w ν
  choose Qf hQe hQi using hQ
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => N (lineK k₀ w u) ℓ
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hpoly ℓ) (ι := Unit)
      (ℓ := fun _ u _ => lineK k₀ w u) fun _ ν => by
        simpa using isUPoly_lineK (ι := Unit) 1 k₀ w ν
    exact h ()
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun k => Qf (lineK k₀ w (node (2 * d) k))
  have hQk : ∀ k, (Qk k).eval = F (node (2 * d) k) := fun k => hQe _
  set J : ℝ → LoopQuartic := fun u => jointQuartic (2 * d) d Qk u
  have hJe : ∀ u ∈ Ioo (-1 : ℝ) 1, (J u).eval = F u := fun u hu => eval_jointQuartic hF hQk hu
  set A : (Fin m → ℝ) → ℝ → ℂ := fun x u => ∑ k, (wt (node (2 * d) k) ^ d *
    (lbasis (2 * d) k).eval (u : ℂ)) * (wt u ^ 4 * paramNum (Qk k) α (mom u) M x)
  have hA : IsUPoly (2 * d + 8) A :=
    IsUPoly.sum _ fun k _ => ((isUPoly_lbasis (2 * d) k).const_mul _).mul
      (isUPoly_paramNum (Qk k) α M mom hmom)
  have hAi : ∀ k, Integrable (fun x => A x (node (2 * d + 8) k))
      (volume.restrict (simplexSet m)) := fun k => by
    refine integrable_finsetSum _ fun l _ => Integrable.const_mul ?_ _
    exact (hQi _ _).const_mul _
  set V : ℝ → (Fin m → ℝ) → ℝ := fun u x => symanzikV α (mom u) M (simplexPoint x) with hVdef
  have hVm : ∀ u, AEStronglyMeasurable (V u) (volume.restrict (simplexSet m)) := fun u =>
    ((measurable_symanzikV α (mom u) M).comp
      continuous_simplexPoint'.measurable).aestronglyMeasurable
  obtain ⟨MV, LV, KV, hVt⟩ := dec_symanzikV_line_two (by omega) α hspan cs M k₀ w
  obtain ⟨MI, LI, KI, hI⟩ := dec_two_integral_upoly (a := d + 4) (N := m - 3) hA hAi hc hVm
    (by filter_upwards [hV, hVt] with x hx hx' using ⟨hx, hx'⟩)
  have hval : ∀ u : ℝ, |u| ≤ 1 / 2 → pvOf (N (lineK k₀ w u)) α (mom u) M =
      -((π : ℂ) ^ 4) * ∫ x, A x u / (wt u ^ (d + 4) * ((V u x : ℝ) : ℂ) ^ (m - 3))
        ∂(volume.restrict (simplexSet m)) := fun u hu' => by
    have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    rw [pvOf_eq (hJe u hu1)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hV] with x hx
    have hVx : symanzikV α (mom u) M (simplexPoint x) ≠ 0 := (hc.trans_le (hx u hu')).ne'
    have hVx' : ((symanzikV α (mom u) M (simplexPoint x) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr hVx
    have hw := wt_ne_zero hu1
    simp only [J, jointQuartic, paramIntegrand_qsum, A, Finset.sum_div, hVdef]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk k) α (mom u) M hm hVx]
    simp only [lam]
    field_simp
    ring
  exact ⟨_, _, _, (hI.const_mul (-((π : ℂ) ^ 4))).congr fun u hu =>
    (hval u (abs_le.mpr hu)).symm⟩


/-- **Second differences of eight-line kinds along a segment below threshold.** -/
theorem dec_segTwo_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (hκ : ∀ i, κ i ≠ .out) (Ms : Fin (m + 1) → ℝ) {me μ : ℝ} (hme : 0 < me) (hμ : 0 < μ)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j)
    {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(me + μ) ^ 2 < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    (i j : Fin 4) :
    DecSegTwo k₀ w fun k => pvOf (fun ℓ => N k (ℓ 0) i j)
      (castLoopMatrix fun i => (κ i).dir) (fun l => (κ l).mom k k) Ms := by
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
  have hT : 0 < (me + μ) ^ 2 := by positivity
  have hc1 : 0 < 1 + S₀ / (me + μ) ^ 2 := by
    have : -1 < S₀ / (me + μ) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hc : 0 < min 1 (1 + S₀ / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) :=
    mul_pos (lt_min one_pos hc1) (lt_min (by positivity) (by positivity))
  have hm0 : 0 < D.m := by have := D.hm; omega
  have hspan : ∃ a b, D.α a 0 * D.α b 1 - D.α a 1 * D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := D.α) fun k => by
      have := D.hcrit.noSubdivergenceOfOrder k; have := D.hm; omega
  have hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = (fun ℓ => N k (ℓ 0) i j) ∧
      ∀ q, IntegrableOn (paramNum Q D.α q D.M) (simplexSet D.m) := fun k => by
    obtain ⟨Q, hQ⟩ := (hN k i j).exists_loopQuartic
    have hgood : D.Good Q := ⟨Or.inl hm7, refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by
      simp only [hQ, Matrix.cons_val_zero]⟩
    exact ⟨Q, hQ, fun q => integrableOn_paramNum_good hgood q⟩
  have hV : ∀ᵐ x ∂(volume.restrict (simplexSet D.m)), ∀ u : ℝ, |u| ≤ 1 / 2 →
      min 1 (1 + S₀ / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) ≤
        symanzikV D.α (fun i => D.cs i • lineK k₀ w u) D.M (simplexPoint x) := by
    filter_upwards [ae_posDef D.α hm0 hspan] with x ⟨hxS, hPD⟩ u hu
    have hs := hseg u hu
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hb := symanzikV_kinds_se_ge κ hκ Ms hme hμ (p := lineK k₀ w u) (by linarith) hMe hMp
      hz.1 hz.2 hPD.det_pos.ne'
    rw [show (fun i => D.cs i • lineK k₀ w u) = D.mom (lineK k₀ w u) from rfl, hmom]
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_min_left _ ?_) (by positivity)) hb
    have := div_le_div_of_nonneg_right hs hT.le
    linarith
  have h := dec_segTwo_pvOf_line (by have := D.hm; omega) D.α hspan D.cs D.M k₀ w
    (fun k ℓ => N k (ℓ 0) i j) (fun ℓ => hpoly (ℓ 0) i j) hQ hc hV
  refine h.congr fun u _ => ?_
  rw [show (fun i => D.cs i • lineK k₀ w u) = D.mom (lineK k₀ w u) from rfl, hmom]
  rfl

end QED.GradedProof.RPi4

end
