/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecLipBase

/-!
# (R-Π₄) step L9: parametric values are Lipschitz along a segment of momenta

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (Lipschitz bounds
near `s = 0`). The Lipschitz counterpart of `QED.GradedProof.RPi4.DecSegCont`.

* `DecSegLip k₀ w G`: `‖G(k(u)) - G(k(u'))‖ ≤ L |u - u'|` for `|u|, |u'| ≤ 1/2`; closed under sums,
  constants and agreement on the segment.
* `dec_symanzikV_line_bound`: along a line of momenta, `V` is bounded and Lipschitz in `u`,
  uniformly off a null set (`(1 - u²)² V` is a polynomial of degree `4` in `u` whose node values
  are bounded by `QED.Integration.TwoLoop.abs_symanzikV_le`).
* `dec_segLip_pvOf_line`: the parametric value along a segment (hypotheses as in
  `QED.GradedProof.RPi4.dec_segCont_pvOf_line`).
* `dec_segLip_kinds`: eight-line kinds along a segment below threshold.
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

/-! ### Lipschitz along the segment -/

/-- `G` is Lipschitz along the segment `lineK k₀ w u`, `|u| ≤ 1/2`. -/
def DecSegLip (k₀ w : Fin 4 → ℝ) (G : (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ L : ℝ, ∀ u u' : ℝ, |u| ≤ 1 / 2 → |u'| ≤ 1 / 2 →
    ‖G (lineK k₀ w u) - G (lineK k₀ w u')‖ ≤ L * |u - u'|

namespace DecSegLip

variable {k₀ w : Fin 4 → ℝ} {G H : (Fin 4 → ℝ) → ℂ}

theorem add (hG : DecSegLip k₀ w G) (hH : DecSegLip k₀ w H) :
    DecSegLip k₀ w fun k => G k + H k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  refine ⟨C + D, fun u u' hu hu' => ?_⟩
  have e : G (lineK k₀ w u) + H (lineK k₀ w u) - (G (lineK k₀ w u') + H (lineK k₀ w u')) =
      (G (lineK k₀ w u) - G (lineK k₀ w u')) + (H (lineK k₀ w u) - H (lineK k₀ w u')) := by ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC u u' hu hu') (hD u u' hu hu'))

theorem const_mul (hG : DecSegLip k₀ w G) (a : ℂ) : DecSegLip k₀ w fun k => a * G k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖a‖ * C, fun u u' hu hu' => ?_⟩
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u u' hu hu') (norm_nonneg _)

theorem zero : DecSegLip k₀ w fun _ => 0 := ⟨0, fun u u' _ _ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, DecSegLip k₀ w (G i)) : DecSegLip k₀ w fun k => ∑ i ∈ s, G i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : DecSegLip k₀ w fun _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : DecSegLip k₀ w G)
    (e : ∀ u : ℝ, |u| ≤ 1 / 2 → G (lineK k₀ w u) = H (lineK k₀ w u)) :
    DecSegLip k₀ w H := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun u u' hu hu' => e u hu ▸ e u' hu' ▸ hC u u' hu hu'⟩

end DecSegLip

/-! ### `V` along a line of momenta -/

theorem dec_norm_wt_le_one' {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : ‖wt u‖ ≤ 1 := by
  have e : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [hu.1, hu.2]

/-- **`V` is bounded and Lipschitz along a line of momenta**, uniformly off a null set. -/
theorem dec_symanzikV_line_bound {m : ℕ} (hm0 : 0 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) (cs : Fin (m + 1) → ℝ)
    (M : Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ) :
    ∃ B L : ℝ, 1 ≤ B ∧ ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ u u' : ℝ,
      |u| ≤ 1 / 2 → |u'| ≤ 1 / 2 →
        symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x) ≤ B ∧
        |symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x) -
          symanzikV α (fun i => cs i • lineK k₀ w u') M (simplexPoint x)| ≤ L * |u - u'| := by
  set mom : ℝ → Fin (m + 1) → Fin 4 → ℝ := fun u i => cs i • lineK k₀ w u with hmom_def
  have hmom : ∀ i ν, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i ν : ℝ) : ℂ) :=
    fun i ν => isUPoly_lineK (cs i) k₀ w ν
  have hW := isUPoly_symanzikV α mom M (fun x => simplexPoint x) hmom
  set Bn : ℝ := ∑ k : Fin 5, ∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2) with hBn
  have hBk : ∀ k : Fin 5, ∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2) ≤ Bn := fun k =>
    Finset.single_le_sum (f := fun k : Fin 5 => ∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2))
      (fun k _ => by positivity) (Finset.mem_univ k)
  have hBn0 : 0 ≤ Bn := by positivity
  have hβ₀ : 0 ≤ decLagβ₀ 4 := by unfold decLagβ₀; positivity
  have hβ : 0 ≤ decLagβ 4 := by unfold decLagβ; positivity
  set q : ℝ := 16 / 9
  refine ⟨max 1 (q * (Bn * decLagβ₀ 4)), q * (Bn * decLagβ 4) + q ^ 2 * (Bn * decLagβ₀ 4 * 2),
    le_max_left _ _, ?_⟩
  filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩ u u' hu hu'
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  have hnode : ∀ k : Fin 5, ‖wt (node 4 k) ^ 2 *
      ((symanzikV α (mom (node 4 k)) M (simplexPoint x) : ℝ) : ℂ)‖ ≤ Bn := fun k => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_symanzikV_le α (mom (node 4 k)) M hz.1 hz.2 hPD.det_pos.ne'
    have h2 : ‖wt (node 4 k)‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (dec_norm_wt_le_one' (node_mem 4 k))
    calc ‖wt (node 4 k)‖ ^ 2 * |symanzikV α (mom (node 4 k)) M (simplexPoint x)|
        ≤ 1 * (∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2)) :=
          mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
      _ ≤ Bn := by rw [one_mul]; exact hBk k
  have hW1 := dec_norm_upoly_le_of_nodes hW x hnode hu
  have hW1' := dec_norm_upoly_le_of_nodes hW x hnode hu'
  have hW2 := dec_norm_upoly_sub_le_of_nodes hW x hnode hu hu'
  set V : ℝ → ℝ := fun u => symanzikV α (mom u) M (simplexPoint x) with hV
  have hw : ∀ u : ℝ, |u| ≤ 1 / 2 → (9 / 16 : ℝ) ≤ ‖wt u ^ 2‖ := fun u hu => by
    rw [norm_pow]
    have := norm_wt_ge hu
    nlinarith
  have hw0 : ∀ u : ℝ, |u| ≤ 1 / 2 → wt u ^ 2 ≠ 0 := fun u hu =>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hw u hu))
  have hVe : ∀ u : ℝ, |u| ≤ 1 / 2 →
      ((V u : ℝ) : ℂ) = wt u ^ 2 * ((V u : ℝ) : ℂ) / wt u ^ 2 := fun u hu => by
    rw [mul_div_cancel_left₀ _ (hw0 u hu)]
  have hVb : ∀ u : ℝ, |u| ≤ 1 / 2 → ‖wt u ^ 2 * ((V u : ℝ) : ℂ)‖ ≤ Bn * decLagβ₀ 4 →
      |V u| ≤ q * (Bn * decLagβ₀ 4) := fun u hu hb => by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hVe u hu, norm_div]
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hw u hu))]
    have := hw u hu
    have h0 : 0 ≤ Bn * decLagβ₀ 4 := by positivity
    simp only [q]
    nlinarith
  refine ⟨((le_abs_self _).trans (hVb u hu hW1)).trans (le_max_right _ _), ?_⟩
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_sub, hVe u hu, hVe u' hu']
  have hww : ‖wt u ^ 2 - wt u' ^ 2‖ ≤ 2 * |u - u'| := by
    have := dec_norm_pow_sub_pow_le le_rfl (dec_norm_wt_le_one hu) (dec_norm_wt_le_one hu') 2
    simp only [one_pow, mul_one, Nat.cast_ofNat] at this
    exact this.trans (mul_le_mul_of_nonneg_left (dec_norm_wt_sub_le hu hu') (by norm_num))
  refine (dec_norm_div_sub_div_le (hw0 u hu) (hw0 u' hu')).trans ?_
  have hd : (9 / 16 : ℝ) * (9 / 16) ≤ ‖wt u ^ 2‖ * ‖wt u' ^ 2‖ :=
    mul_le_mul (hw u hu) (hw u' hu') (by norm_num) (le_trans (by norm_num) (hw u hu))
  have hu0 := abs_nonneg (u - u')
  have e1 : ‖wt u ^ 2 * ((V u : ℝ) : ℂ) - wt u' ^ 2 * ((V u' : ℝ) : ℂ)‖ / ‖wt u ^ 2‖ ≤
      Bn * decLagβ 4 * |u - u'| / (9 / 16) :=
    div_le_div₀ (by positivity) hW2 (by norm_num) (hw u hu)
  have e2 : ‖wt u' ^ 2 * ((V u' : ℝ) : ℂ)‖ * ‖wt u ^ 2 - wt u' ^ 2‖ /
      (‖wt u ^ 2‖ * ‖wt u' ^ 2‖) ≤ Bn * decLagβ₀ 4 * (2 * |u - u'|) / ((9 / 16) * (9 / 16)) :=
    div_le_div₀ (by positivity) (mul_le_mul hW1' hww (norm_nonneg _) (by positivity))
      (by norm_num) hd
  refine (add_le_add e1 e2).trans (le_of_eq ?_)
  simp only [q]
  ring

/-! ### Parametric values along a line of momenta -/

/-- **The parametric value along a line of momenta is Lipschitz** (hypotheses as in
`dec_segCont_pvOf_line`, plus the span condition for the bound on `V`). -/
theorem dec_segLip_pvOf_line {m : ℕ} (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (paramNum Q α q M) (simplexSet m))
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ u : ℝ, |u| ≤ 1 / 2 →
      c ≤ symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x)) :
    DecSegLip k₀ w fun k => pvOf (N k) α (fun i => cs i • k) M := by
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
  obtain ⟨B, L, hB, hBL⟩ := dec_symanzikV_line_bound (by omega) α hspan cs M k₀ w
  obtain ⟨C, hC⟩ := dec_lip_integral_upoly (a := d + 4) (N := m - 3) hA hAi hc hB hVm
    (by
      filter_upwards [hV, hBL] with x hx hx' u u' hu hu'
      exact ⟨hx u hu, (hx' u u' hu hu').1, (hx' u u' hu hu').2⟩)
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
  refine ⟨‖-((π : ℂ) ^ 4)‖ * C, fun u u' hu hu' => ?_⟩
  show ‖pvOf (N (lineK k₀ w u)) α (mom u) M - pvOf (N (lineK k₀ w u')) α (mom u') M‖ ≤ _
  rw [hval u hu, hval u' hu', ← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u u' hu hu') (norm_nonneg _)

/-! ### Eight-line kinds along the segment -/

/-- **The parametric value of eight-line kinds is Lipschitz along a segment below threshold.** -/
theorem dec_segLip_kinds {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
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
    DecSegLip k₀ w fun k => pvOf (fun ℓ => N k (ℓ 0) i j)
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
  have h := dec_segLip_pvOf_line (by have := D.hm; omega) D.α hspan D.cs D.M k₀ w
    (fun k ℓ => N k (ℓ 0) i j) (fun ℓ => hpoly (ℓ 0) i j) hQ hc hV
  refine h.congr fun u _ => ?_
  rw [show (fun i => D.cs i • lineK k₀ w u) = D.mom (lineK k₀ w u) from rfl, hmom]
  rfl

end QED.GradedProof.RPi4

end
