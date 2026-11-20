/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4UnifF

/-!
# (R-Π₄) step L9: parametric values are continuous along a segment of momenta

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (continuity of the
per-flavour function at `s = 0`). The continuity counterpart of `QED.GradedProof.RPi4.SegBdd`:
along the segment `lineK k₀ w u`, `|u| ≤ 1/2`, the parametric values are polynomial in `u` over a
power of `V ≥ c > 0`, so dominated convergence (with the majorant of
`QED.GradedProof.RPi4.exists_norm_integral_upoly_le`) gives continuity in `u`.

* `DecSegCont k₀ w G`: `u ↦ G (lineK k₀ w u)` is continuous on `[-1/2, 1/2]`; closed under sums,
  constants and agreement on the segment.
* `dec_continuousOn_integral_upoly`: `u ↦ ∫ A(·, u) / ((1 - u²)ᵃ V(u)ᴺ)` is continuous for
  polynomial families `A` with integrable node values and `V ≥ c > 0` continuous in `u`.
* `dec_segCont_pvOf_line`: the parametric value along a segment, under the hypotheses of
  `QED.GradedProof.RPi4.exists_norm_pvOf_line_le` (lower bound uniform in `u` off a null set).
* `dec_segCont_kinds`: eight-line kinds along a segment below threshold.
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

/-! ### Continuous along the segment -/

/-- `G` is continuous along the segment `lineK k₀ w u`, `|u| ≤ 1/2`. -/
def DecSegCont (k₀ w : Fin 4 → ℝ) (G : (Fin 4 → ℝ) → ℂ) : Prop :=
  ContinuousOn (fun u => G (lineK k₀ w u)) (Icc (-(1 / 2)) (1 / 2))

theorem dec_mem_Icc_half {u : ℝ} : u ∈ Icc (-(1 / 2) : ℝ) (1 / 2) ↔ |u| ≤ 1 / 2 := by
  rw [abs_le, mem_Icc]

namespace DecSegCont

variable {k₀ w : Fin 4 → ℝ} {G H : (Fin 4 → ℝ) → ℂ}

theorem add (hG : DecSegCont k₀ w G) (hH : DecSegCont k₀ w H) :
    DecSegCont k₀ w fun k => G k + H k :=
  ContinuousOn.add hG hH

theorem const_mul (hG : DecSegCont k₀ w G) (a : ℂ) : DecSegCont k₀ w fun k => a * G k :=
  ContinuousOn.mul continuousOn_const hG

theorem zero : DecSegCont k₀ w fun _ => 0 := continuousOn_const

theorem sum {ι : Type*} (s : Finset ι) {G : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, DecSegCont k₀ w (G i)) : DecSegCont k₀ w fun k => ∑ i ∈ s, G i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : DecSegCont k₀ w fun _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : DecSegCont k₀ w G)
    (e : ∀ u : ℝ, |u| ≤ 1 / 2 → G (lineK k₀ w u) = H (lineK k₀ w u)) :
    DecSegCont k₀ w H :=
  ContinuousOn.congr hG fun u hu => (e u (dec_mem_Icc_half.mp hu)).symm

end DecSegCont

/-! ### Continuity of integrals of polynomial families -/

section Integral

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

theorem dec_continuousOn_tpar : ContinuousOn tpar (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  refine ContinuousOn.div continuousOn_id (by fun_prop) fun u hu => ?_
  have h := dec_mem_Icc_half.mp hu
  have : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  linarith

theorem dec_continuousOn_lineK (k₀ w : Fin 4 → ℝ) :
    ContinuousOn (lineK k₀ w) (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  unfold lineK
  exact continuousOn_const.add (dec_continuousOn_tpar.smul continuousOn_const)

/-- **Continuity of `∫ A(·, u) / ((1 - u²)ᵃ V(u)ᴺ)`** for polynomial families `A` with integrable
values at the nodes and `V ≥ c > 0`, continuous in `u`, off a null set. -/
theorem dec_continuousOn_integral_upoly {D a N : ℕ} {A : ι → ℝ → ℂ} (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) {c : ℝ} (hc : 0 < c)
    {V : ℝ → ι → ℝ} (hVm : ∀ u, AEStronglyMeasurable (V u) μ)
    (hV : ∀ᵐ x ∂μ, ContinuousOn (fun u => V u x) (Icc (-(1 / 2)) (1 / 2)) ∧
      ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2), c ≤ V u x) :
    ContinuousOn (fun u => ∫ x, A x u / (wt u ^ a * (V u x : ℂ) ^ N) ∂μ)
      (Icc (-(1 / 2)) (1 / 2)) := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  set K : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ with hK
  have hKi : Integrable K μ := integrable_finsetSum _ fun j _ => (hcf j).norm
  have hK0 : ∀ x, 0 ≤ K x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hIoo : ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2), u ∈ Ioo (-1 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set F : ℝ → ι → ℂ := fun u x =>
    (interp D A x).eval (u : ℂ) / (wt u ^ a * (V u x : ℂ) ^ N) with hF
  refine ContinuousOn.congr (f := fun u => ∫ x, F u x ∂μ) ?_ fun u hu => ?_
  · refine continuousOn_of_dominated (bound := fun x => K x / ((3 / 4 : ℝ) ^ a * c ^ N))
      (fun u _ => ?_) (fun u hu => ?_) (hKi.div_const _) ?_
    · have hP : AEStronglyMeasurable (fun x => (interp D A x).eval (u : ℂ)) μ := by
        have e : (fun x => (interp D A x).eval (u : ℂ)) =
            fun x => ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (u : ℂ) ^ j :=
          funext fun x => eval_interp_eq_sum x _
        rw [e]
        exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
          (hcf j).aestronglyMeasurable.mul_const _
      have hVc : AEStronglyMeasurable (fun x => ((V u x : ℝ) : ℂ)) μ :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable (hVm u)
      exact hP.div₀ ((hVc.pow N).const_mul _)
    · filter_upwards [hV] with x hx
      have hVx := hx.2 u hu
      have hu' : |u| ≤ 1 / 2 := dec_mem_Icc_half.mp hu
      have hAn : ‖(interp D A x).eval (u : ℂ)‖ ≤ K x := by
        rw [eval_interp_eq_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (abs_nonneg u) (hu'.trans (by norm_num)))
      have hw := norm_wt_ge hu'
      simp only [hF]
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hc.trans_le hVx)]
      exact div_le_div₀ (hK0 x) hAn (by positivity)
        (mul_le_mul (pow_le_pow_left₀ (by norm_num) hw a) (pow_le_pow_left₀ hc.le hVx N)
          (by positivity) (by positivity))
    · filter_upwards [hV] with x hx
      have h1 : ContinuousOn (fun u : ℝ => (interp D A x).eval (u : ℂ))
          (Icc (-(1 / 2)) (1 / 2)) := by
        simp only [eval_interp_eq_sum]
        fun_prop
      have h2 : ContinuousOn (fun u : ℝ => wt u ^ a) (Icc (-(1 / 2)) (1 / 2)) := by
        unfold wt
        fun_prop
      have h3 : ContinuousOn (fun u => ((V u x : ℝ) : ℂ) ^ N) (Icc (-(1 / 2)) (1 / 2)) :=
        (Complex.continuous_ofReal.comp_continuousOn hx.1).pow N
      refine h1.div (h2.mul h3) fun u hu => mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
      · have := norm_wt_ge (dec_mem_Icc_half.mp hu)
        intro h0
        rw [h0, norm_zero] at this
        norm_num at this
      · exact ofReal_ne_zero.mpr (hc.trans_le (hx.2 u hu)).ne'
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF, hA.eq_interp x u (hIoo u hu)]

end Integral

/-! ### Parametric values along a line of momenta -/

/-- **The parametric value along a line of momenta is continuous**, under the hypotheses of
`exists_norm_pvOf_line_le` with the lower bound `V ≥ c` holding for all `|u| ≤ 1/2` off one null
set. -/
theorem dec_segCont_pvOf_line {m : ℕ} (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (paramNum Q α q M) (simplexSet m))
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ u : ℝ, |u| ≤ 1 / 2 →
      c ≤ symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x)) :
    DecSegCont k₀ w fun k => pvOf (N k) α (fun i => cs i • k) M := by
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
  have hVc : ∀ x, ContinuousOn (fun u => V u x) (Icc (-(1 / 2)) (1 / 2)) := fun x => by
    have hl := dec_continuousOn_lineK k₀ w
    have hcoord : ∀ i ν, ContinuousOn (fun u => mom u i ν) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
      fun i ν => continuousOn_const.mul ((continuous_apply ν).comp_continuousOn hl)
    simp only [hVdef, symanzikV, symanzikVector, Minkowski.dot]
    fun_prop
  have hint := dec_continuousOn_integral_upoly (a := d + 4) (N := m - 3) hA hAi hc hVm
    (by filter_upwards [hV] with x hx using
      ⟨hVc x, fun u hu => hx u (dec_mem_Icc_half.mp hu)⟩)
  refine ContinuousOn.congr (hint.const_mul (-((π : ℂ) ^ 4))) fun u hu => ?_
  have hu' := dec_mem_Icc_half.mp hu
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  show pvOf (N (lineK k₀ w u)) α (mom u) M = _
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

/-! ### Eight-line kinds along the segment -/

/-- **The parametric value of eight-line kinds is continuous along a segment below threshold.** -/
theorem dec_segCont_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
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
    DecSegCont k₀ w fun k => pvOf (fun ℓ => N k (ℓ 0) i j)
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
  have h := dec_segCont_pvOf_line (by have := D.hm; omega) D.α D.cs D.M k₀ w
    (fun k ℓ => N k (ℓ 0) i j) (fun ℓ => hpoly (ℓ 0) i j) hQ hc hV
  refine h.congr fun u _ => ?_
  rw [show (fun i => D.cs i • lineK k₀ w u) = D.mom (lineK k₀ w u) from rfl, hmom]
  rfl

end QED.GradedProof.RPi4

end
