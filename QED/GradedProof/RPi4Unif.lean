/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Cov
public import QED.GradedProof.RPi4VJV

/-!
# (R-Π₄): parametric values bounded uniformly along a segment of momenta

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), uniformity in `s`. The
frozen statement needs bounds uniform for `s` in a compact `[S₀, S]` below threshold. By
`QED.GradedProof.RPi4.projS_eq_tilt` the projection at `s` is an entry at the tilted vector
`k'(s) = (√(2c² - s), 0, c, c)`, and these vectors fill a segment of momenta. Along a segment
the parametric numerators are polynomial in the parameter with integrable coefficients (the
interpolation of `QED.GradedProof.SE2.SEPiece.tendsto_nullVec`), so the abstract integrable
majorants become uniform.

* `exists_norm_integral_upoly_le`: `‖∫ A(·, u) / ((1 - u²)ᵃ Vᴺ)‖ ≤ C` for polynomial families,
  uniformly for `|u| ≤ 1/2` and every `V ≥ c > 0`.
* `lineK k₀ w u = k₀ + t(u) w`, `t(u) = u / (1 - u²)`.
* `exists_norm_pvOf_line_le`: `‖pvOf (N k(u)) α (cᵢ k(u)) M‖ ≤ C` for `|u| ≤ 1/2`, if `N` is
  polynomial in `k`, each `N k` has a quartic with integrable parametric numerators, and
  `V ≥ c > 0` along the segment. No `Good` condition and no covariance are needed.
* `exists_tiltVec_eq_lineK`, `dot_lineK_tilt_mem`: the tilted vectors of `[S₀, S]` are the points
  `|u| ≤ 1/2` of one segment (`tiltBase`, `tiltDir`), and the segment stays in `S₀ ≤ k² ≤ S`.
-/

@[expose] public section
open Complex Filter Topology MeasureTheory Set Polynomial
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.GradedProof.SE2 (tpar upar tpar_upar isUPoly_tpar_smul)

/-! ### A uniform bound for integrals of polynomial families -/

section Bound

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **A uniform bound on `∫ A(·, u) / ((1 - u²)ᵃ Vᴺ)`** for polynomial families `A` with
integrable values at the nodes, uniformly for `|u| ≤ 1/2` and every `V ≥ c > 0`. -/
theorem exists_norm_integral_upoly_le {D a N : ℕ} {A : ι → ℝ → ℂ} (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ V : ι → ℝ, (∀ᵐ x ∂μ, c ≤ V x) →
      ‖∫ x, A x u / (wt u ^ a * (V x : ℂ) ^ N) ∂μ‖ ≤ C := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  set K : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ with hK
  have hKi : Integrable K μ := integrable_finsetSum _ fun j _ => (hcf j).norm
  have hK0 : ∀ x, 0 ≤ K x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨∫ x, K x / ((3 / 4 : ℝ) ^ a * c ^ N) ∂μ, fun u hu V hV => ?_⟩
  refine norm_integral_le_of_norm_le (hKi.div_const _) ?_
  filter_upwards [hV] with x hx
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have hAn : ‖A x u‖ ≤ K x := by
    rw [hA.eq_interp x u hu1, eval_interp_eq_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (abs_nonneg u) (hu.trans (by norm_num)))
  have hw := norm_wt_ge hu
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hc.trans_le hx)]
  exact div_le_div₀ (hK0 x) hAn (by positivity)
    (mul_le_mul (pow_le_pow_left₀ (by norm_num) hw a) (pow_le_pow_left₀ hc.le hx N)
      (by positivity) (by positivity))

end Bound

/-! ### Parametric values along a line of momenta -/

/-- The line `k₀ + t(u) w` of momenta, `t(u) = u / (1 - u²)`. -/
noncomputable def lineK (k₀ w : Fin 4 → ℝ) (u : ℝ) : Fin 4 → ℝ := k₀ + tpar u • w

theorem isUPoly_lineK {ι : Type*} (a : ℝ) (k₀ w : Fin 4 → ℝ) (ν : Fin 4) :
    IsUPoly (ι := ι) 2 fun _ u => wt u * (((a • lineK k₀ w u) ν : ℝ) : ℂ) := by
  refine (((isUPoly_wt (ι := ι)).const_mul fun _ => ((a * k₀ ν : ℝ) : ℂ)).add
    (isUPoly_tpar_smul a w ν)).congr fun _ u _ => ?_
  simp only [lineK, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  push_cast
  ring

/-- **A uniform bound for the parametric value along a line of momenta.** The numerator `N k` is
polynomial in `k` at fixed loop momenta, each `N k` has a quartic with integrable parametric
numerators, and `V ≥ c > 0` along the line for `|u| ≤ 1/2`. -/
theorem exists_norm_pvOf_line_le {m : ℕ} (hm : 5 ≤ m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (paramNum Q α q M) (simplexSet m))
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      c ≤ symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x)) :
    ∃ C : ℝ, ∀ u : ℝ, |u| ≤ 1 / 2 →
      ‖pvOf (N (lineK k₀ w u)) α (fun i => cs i • lineK k₀ w u) M‖ ≤ C := by
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
  obtain ⟨C, hC⟩ := exists_norm_integral_upoly_le (a := d + 4) (N := m - 3) hA hAi hc
  refine ⟨‖-((π : ℂ) ^ 4)‖ * C, fun u hu => ?_⟩
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have hval : pvOf (N (lineK k₀ w u)) α (mom u) M = -((π : ℂ) ^ 4) *
      ∫ x in simplexSet m, A x u /
        (wt u ^ (d + 4) * ((symanzikV α (mom u) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3)) := by
    rw [pvOf_eq (hJe u hu1)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hV u hu] with x hx
    have hVx : symanzikV α (mom u) M (simplexPoint x) ≠ 0 := (hc.trans_le hx).ne'
    have hVx' : ((symanzikV α (mom u) M (simplexPoint x) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr hVx
    have hw := wt_ne_zero hu1
    simp only [J, jointQuartic, paramIntegrand_qsum, A, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk k) α (mom u) M hm hVx]
    simp only [lam]
    field_simp
    ring
  rw [hval, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC u hu _ (hV u hu)) (norm_nonneg _)

/-! ### The tilted vectors of a compact interval lie on one segment -/

theorem abs_tpar_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |tpar u| ≤ 2 / 3 := by
  have h1 : 3 / 4 ≤ 1 - u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  rw [tpar, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - u ^ 2),
    div_le_iff₀ (by linarith)]
  nlinarith [sq_abs u, abs_nonneg u]

theorem abs_upar_le {t : ℝ} (ht : |t| ≤ 2 / 3) : |upar t| ≤ 1 / 2 := by
  have hr := Real.sqrt_nonneg (1 + 4 * t ^ 2)
  have hr2 := Real.sq_sqrt (show 0 ≤ 1 + 4 * t ^ 2 by positivity)
  rw [upar, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + Real.sqrt (1 + 4 * t ^ 2)),
    div_le_iff₀ (by linarith), abs_mul, abs_two]
  nlinarith [sq_abs t, abs_nonneg t]

/-- The base point `((τ₋ + τ₊)/2, 0, c, c)` of the tilted segment, `τ± = √(2c² - S∓)`. -/
noncomputable def tiltBase (c S₀ S : ℝ) : Fin 4 → ℝ :=
  ![(Real.sqrt (2 * c ^ 2 - S) + Real.sqrt (2 * c ^ 2 - S₀)) / 2, 0, c, c]

/-- The direction `((3/4)(τ₊ - τ₋), 0, 0, 0)` of the tilted segment. -/
noncomputable def tiltDir (c S₀ S : ℝ) : Fin 4 → ℝ :=
  ![3 / 4 * (Real.sqrt (2 * c ^ 2 - S₀) - Real.sqrt (2 * c ^ 2 - S)), 0, 0, 0]

theorem lineK_tilt (c S₀ S u : ℝ) : lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u =
    ![(Real.sqrt (2 * c ^ 2 - S) + Real.sqrt (2 * c ^ 2 - S₀)) / 2 +
      tpar u * (3 / 4 * (Real.sqrt (2 * c ^ 2 - S₀) - Real.sqrt (2 * c ^ 2 - S))), 0, c, c] := by
  funext ν
  fin_cases ν <;> simp [lineK, tiltBase, tiltDir]

/-- **Every tilted vector of `[S₀, S]` is on the segment** `|u| ≤ 1/2`. -/
theorem exists_tiltVec_eq_lineK {c S₀ S s : ℝ} (h₀ : S₀ ≤ s) (h₁ : s ≤ S) :
    ∃ u, |u| ≤ 1 / 2 ∧ tiltVec c s = lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u := by
  set lo := Real.sqrt (2 * c ^ 2 - S)
  set hi := Real.sqrt (2 * c ^ 2 - S₀)
  set τ := Real.sqrt (2 * c ^ 2 - s)
  have hlo : lo ≤ τ := Real.sqrt_le_sqrt (by linarith)
  have hhi : τ ≤ hi := Real.sqrt_le_sqrt (by linarith)
  set w := 3 / 4 * (hi - lo)
  set t := (τ - (lo + hi) / 2) / w
  have hwd : w = 3 / 4 * (hi - lo) := rfl
  have hw0 : 0 ≤ w := by linarith
  have ht : |t| ≤ 2 / 3 := by
    rcases hw0.eq_or_lt with h | h
    · simp only [t, ← h, div_zero, abs_zero]
      norm_num
    · rw [abs_div, abs_of_pos h, div_le_iff₀ h, abs_le]
      constructor <;> linarith
  have htw : (lo + hi) / 2 + t * w = τ := by
    rcases hw0.eq_or_lt with h | h
    · have : hi = lo := by simp only [w] at h; linarith
      simp only [t, ← h, div_zero, zero_mul, add_zero]
      linarith
    · simp only [t]
      field_simp
      ring
  refine ⟨upar t, abs_upar_le ht, ?_⟩
  rw [lineK_tilt, tpar_upar]
  funext ν
  fin_cases ν <;> simp [tiltVec]
  exact htw.symm

/-- **The segment stays in `[S₀, S]`**: `S₀ ≤ k(u)² ≤ S` for `|u| ≤ 1/2`. -/
theorem dot_lineK_tilt_mem {c S₀ S u : ℝ} (hS : S < 2 * c ^ 2) (hS₀ : S₀ ≤ S)
    (hu : |u| ≤ 1 / 2) :
    S₀ ≤ Minkowski.dot (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u)
        (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u) ∧
      Minkowski.dot (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u)
        (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u) ≤ S := by
  have hlo := Real.sqrt_nonneg (2 * c ^ 2 - S)
  have hlo2 := Real.sq_sqrt (show 0 ≤ 2 * c ^ 2 - S by linarith)
  have hhi2 := Real.sq_sqrt (show 0 ≤ 2 * c ^ 2 - S₀ by linarith)
  have hle : Real.sqrt (2 * c ^ 2 - S) ≤ Real.sqrt (2 * c ^ 2 - S₀) :=
    Real.sqrt_le_sqrt (by linarith)
  have ht := abs_le.mp (abs_tpar_le hu)
  rw [lineK_tilt]
  simp only [Minkowski.dot_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  set lo := Real.sqrt (2 * c ^ 2 - S)
  set hi := Real.sqrt (2 * c ^ 2 - S₀)
  set τ := (lo + hi) / 2 + tpar u * (3 / 4 * (hi - lo))
  have h1 : lo ≤ τ := by simp only [τ]; nlinarith
  have h2 : τ ≤ hi := by simp only [τ]; nlinarith
  constructor <;> nlinarith

end QED.GradedProof.RPi4

end
