/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightBd
public import QED.GradedProof.RPi4LightInt
public import QED.GradedProof.RPi4Unif
public import Mathlib.Topology.Algebra.Polynomial

/-!
# (R-Π₄) step L7: a parametric value at a light comparable photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7 (light photon
pair). The parametric value of a piece with seven or eight lines, whose two photon lines carry
the masses `a ≤ b ≤ 2a`, is `O(1 + 1/b)` along a segment of external momenta. The simplex is
split by the sum `y` of the fermion parameters:

* `y ≥ 1/2`: `V ≥ c₀/2`; the coefficients `T₁, T₂` of the joint quartics have integrable
  majorants uniform along the segment (`exists_upoly_majorant`, `exists_coeff_line_majorant`,
  from the polynomial dependence on the segment parameter), and `T₃` does not depend on it;
* `y < 1/2`: the explicit corner bound `QED.GradedProof.RPi4.norm_paramIntegrand_le_corner`
  with `V² ≥ (c₀ y)^{3/2} b/√8` (`one_div_corner_le`) gives `y^{-(m-3/2)} / b`, integrable by
  `QED.GradedProof.RPi4.integrableOn_headSum_rpow`.

The main statement is `exists_norm_pvOf_light_le`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Polynomial
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.GradedProof.SE2 (tpar)

/-! ### Integrable majorants of polynomial families -/

/-- **A polynomial family with integrable node values has an integrable majorant** on
`|u| ≤ 1/2`. -/
theorem exists_upoly_majorant {ι : Type*} [MeasurableSpace ι] {μ : Measure ι} {D : ℕ}
    {A : ι → ℝ → ℂ} (hA : IsUPoly D A) (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) :
    ∃ K : ι → ℝ, Integrable K μ ∧ (∀ x, 0 ≤ K x) ∧ ∀ x u, |u| ≤ 1 / 2 → ‖A x u‖ ≤ K x := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  refine ⟨fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖,
    integrable_finsetSum _ fun j _ => (hcf j).norm,
    fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _, fun x u hu => ?_⟩
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [hA.eq_interp x u hu1, eval_interp_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (abs_nonneg u) (hu.trans (by norm_num)))

theorem norm_le_of_wt_pow {u : ℝ} (hu : |u| ≤ 1 / 2) {T : ℂ} {K : ℝ} (n : ℕ)
    (h : ‖wt u ^ n * T‖ ≤ K) : ‖T‖ ≤ (4 / 3) ^ n * K := by
  have hw := norm_wt_ge hu
  rw [norm_mul, norm_pow] at h
  have h1 : (3 / 4 : ℝ) ^ n * ‖T‖ ≤ K :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hw n) (norm_nonneg _)).trans h
  calc ‖T‖ = (4 / 3) ^ n * ((3 / 4) ^ n * ‖T‖) := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ (4 / 3) ^ n * K := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The first two coefficients of a fixed quartic have integrable majorants along a line of
momenta**, uniformly for `|u| ≤ 1/2`. -/
theorem exists_coeff_line_majorant {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ)
    (hmom : ∀ i μ, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i μ : ℝ) : ℂ))
    (h1 : ∀ q, IntegrableOn (coeffOne Q α q) (simplexSet m))
    (h2 : ∀ q, IntegrableOn (coeffTwo Q α q) (simplexSet m)) :
    ∃ K₁ K₂ : (Fin m → ℝ) → ℝ, IntegrableOn K₁ (simplexSet m) ∧
      IntegrableOn K₂ (simplexSet m) ∧ (∀ x, 0 ≤ K₁ x) ∧ (∀ x, 0 ≤ K₂ x) ∧
      ∀ x u, |u| ≤ 1 / 2 → ‖coeffOne Q α (mom u) x‖ ≤ K₁ x ∧ ‖coeffTwo Q α (mom u) x‖ ≤ K₂ x := by
  have hS := isUPoly_loopShift α mom (fun x => simplexPoint x) hmom
  have hX : ∀ a : LoopIndex, IsUPoly 2 fun (x : Fin m → ℝ) u =>
      wt u * loopComp (-loopShift α (mom u) (simplexPoint x)) a := fun a => by
    have e : ∀ (x : Fin m → ℝ) u, wt u * loopComp (-loopShift α (mom u) (simplexPoint x)) a =
        -(wt u * ((loopShift α (mom u) (simplexPoint x) a.1 a.2 : ℝ) : ℂ)) := by
      intro x u
      simp [loopComp]
    exact (hS a.1 a.2).neg.congr fun x u _ => (e x u).symm
  have hA1 : IsUPoly 8 fun x u => wt u ^ 4 * coeffOne Q α (mom u) x :=
    ((isUPoly_evalC Q _ hX).const_mul (fun x =>
      ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * ((m - 4).factorial : ℂ))).congr
      fun x u _ => by simp only [coeffOne, LoopQuartic.eval]; ring
  have hA2 : IsUPoly 4 fun x u => wt u ^ 2 * coeffTwo Q α (mom u) x :=
    ((isUPoly_contractTwo Q _ (fun x => symanzikMatrix α (simplexPoint x)) hX).const_mul
      (fun x => ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 5).factorial : ℂ) / 2))).congr
      fun x u _ => by simp only [coeffTwo]; ring
  obtain ⟨K₁, hK₁, hK₁0, hb₁⟩ := exists_upoly_majorant (μ := volume.restrict (simplexSet m)) hA1
    fun k => (h1 _).const_mul _
  obtain ⟨K₂, hK₂, hK₂0, hb₂⟩ := exists_upoly_majorant (μ := volume.restrict (simplexSet m)) hA2
    fun k => (h2 _).const_mul _
  exact ⟨fun x => (4 / 3) ^ 4 * K₁ x, fun x => (4 / 3) ^ 2 * K₂ x, hK₁.const_mul _,
    hK₂.const_mul _, fun x => mul_nonneg (by positivity) (hK₁0 x),
    fun x => mul_nonneg (by positivity) (hK₂0 x),
    fun x u hu => ⟨norm_le_of_wt_pow hu 4 (hb₁ x u hu), norm_le_of_wt_pow hu 2 (hb₂ x u hu)⟩⟩

/-- The interpolation weights are bounded on `|u| ≤ 1/2`. -/
theorem exists_norm_lam_le (D n : ℕ) :
    ∃ L : ℝ, ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ k, ‖lam D n u k‖ ≤ L := by
  have hB : ∀ k : Fin (D + 1), ∃ B, ∀ u ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ‖(lbasis D k).eval (u : ℂ)‖ ≤ B := fun k =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((Polynomial.continuous _).comp continuous_ofReal).continuousOn
  choose B hB using hB
  refine ⟨∑ k, (4 / 3) ^ n * ‖wt (node D k) ^ n‖ * |B k|, fun u hu k => ?_⟩
  have hu' : u ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨by linarith [neg_abs_le u], by
    linarith [le_abs_self u]⟩
  have hw := norm_wt_ge hu
  have hinv : ‖(wt u ^ n)⁻¹‖ ≤ (4 / 3) ^ n := by
    rw [norm_inv, norm_pow, ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  refine le_trans ?_ (Finset.single_le_sum (f := fun k : Fin (D + 1) =>
    (4 / 3 : ℝ) ^ n * ‖wt (node D k) ^ n‖ * |B k|) (fun k _ => by positivity)
    (Finset.mem_univ k))
  simp only [lam, norm_mul]
  calc ‖(wt u ^ n)⁻¹‖ * (‖wt (node D k) ^ n‖ * ‖(lbasis D k).eval (u : ℂ)‖)
      ≤ (4 / 3) ^ n * (‖wt (node D k) ^ n‖ * |B k|) :=
        mul_le_mul hinv (mul_le_mul_of_nonneg_left ((hB k u hu').trans (le_abs_self _))
          (norm_nonneg _)) (by positivity) (by positivity)
    _ = _ := by ring

/-! ### The corner majorant -/

/-- `1 / (yⁿ V²) ≤ (√8 / c₀^{3/2}) y^{-(n + 3/2)} / b` when `V ≥ c₀ y` and `V ≥ b²/8`. -/
theorem one_div_corner_le {y V b c₀ : ℝ} (n : ℕ) (hy : 0 < y) (hb : 0 < b) (hc₀ : 0 < c₀)
    (h1 : c₀ * y ≤ V) (h2 : b ^ 2 / 8 ≤ V) :
    1 / (y ^ n * V ^ 2) ≤ Real.sqrt 8 / c₀ ^ (3 / 2 : ℝ) * (y ^ (-((n : ℝ) + 3 / 2)) / b) := by
  have hV : 0 < V := lt_of_lt_of_le (by positivity) h1
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hc32 : 0 < c₀ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hc₀ _
  have hy32 : 0 < y ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hy _
  have e1 : V ^ 2 = V ^ (3 / 2 : ℝ) * Real.sqrt V := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hV]
    norm_num
  have e2 : y ^ (-((n : ℝ) + 3 / 2)) = 1 / (y ^ n * y ^ (3 / 2 : ℝ)) := by
    rw [Real.rpow_neg hy.le, Real.rpow_add hy, Real.rpow_natCast, one_div]
  have h3 : c₀ ^ (3 / 2 : ℝ) * y ^ (3 / 2 : ℝ) ≤ V ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow hc₀.le hy.le]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h4 : b / Real.sqrt 8 ≤ Real.sqrt V := by
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_sq hb.le] at this
  have h5 : c₀ ^ (3 / 2 : ℝ) * y ^ (3 / 2 : ℝ) * (b / Real.sqrt 8) ≤ V ^ 2 := by
    rw [e1]
    exact mul_le_mul h3 h4 (by positivity) (by positivity)
  rw [e2, one_div_le (by positivity) (by positivity)]
  have e3 : 1 / (Real.sqrt 8 / c₀ ^ (3 / 2 : ℝ) * (1 / (y ^ n * y ^ (3 / 2 : ℝ)) / b)) =
      y ^ n * (c₀ ^ (3 / 2 : ℝ) * y ^ (3 / 2 : ℝ) * (b / Real.sqrt 8)) := by
    field_simp
  rw [e3]
  exact mul_le_mul_of_nonneg_left h5 (by positivity)

theorem headSum_le_one {m n : ℕ} {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i ≤ 1) :
    headSum n x ≤ 1 :=
  (Finset.sum_le_sum fun i _ => by split_ifs <;> simp [hx i]).trans hx1

theorem norm_lineK_apply_le {k₀ w : Fin 4 → ℝ} {u : ℝ} (hu : |u| ≤ 1 / 2) (μ : Fin 4) :
    |lineK k₀ w u μ| ≤ ∑ ν, (|k₀ ν| + |w ν|) := by
  have ht := abs_tpar_le hu
  have h1 : |lineK k₀ w u μ| ≤ |k₀ μ| + |w μ| := by
    simp only [lineK, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    nlinarith [abs_nonneg (w μ)]
  exact h1.trans (Finset.single_le_sum (f := fun ν => |k₀ ν| + |w ν|)
    (fun ν _ => by positivity) (Finset.mem_univ μ))

/-! ### A piece at a light photon pair -/

/-- **A parametric value at a light comparable photon pair** is `O(1 + 1/b)` along a segment of
momenta. The masses `Ms a b` depend on the photon pair `(a, b)`; the hypotheses are the corner
lower bound `U ≥ (1 - y) y` for the sum `y` of the first `m - 1` (fermion) parameters and
`V ≥ c₀ y + (1 - y) a²`. Away from the corner (`y ≥ 1/2`) the abstract integrable majorants of
the coefficients apply with `V ≥ c₀/2`; near it the explicit bound
`norm_paramIntegrand_le_corner` gives `(B √8 / c₀^{3/2}) y^{-(m-3/2)} / b`. -/
theorem exists_norm_pvOf_light_le {m : ℕ} (hm : m = 6 ∨ m = 7) (α : Fin (m + 1) → Fin 2 → ℝ)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (cs : Fin (m + 1) → ℝ) (Ms : ℝ → ℝ → Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ (7 ≤ m ∨ Q.quart = 0) ∧
      ∀ q, IntegrableOn (coeffOne Q α q) (simplexSet m) ∧
        IntegrableOn (coeffTwo Q α q) (simplexSet m) ∧
        IntegrableOn (coeffThree Q α) (simplexSet m))
    (hU : ∀ x ∈ simplexSet m,
      (1 - headSum (m - 1) x) * headSum (m - 1) x ≤ symanzikU α (simplexPoint x))
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hV : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ simplexSet m,
      symanzikU α (simplexPoint x) ≠ 0 →
      c₀ * headSum (m - 1) x + (1 - headSum (m - 1) x) * a ^ 2 ≤
        symanzikV α (fun i => cs i • lineK k₀ w u) (Ms a b) (simplexPoint x)) :
    ∃ C₁ C₂ : ℝ, ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
      ‖pvOf (N (lineK k₀ w u)) α (fun i => cs i • lineK k₀ w u) (Ms a b)‖ ≤ C₁ + C₂ / b := by
  classical
  have hm6 : 6 ≤ m := by omega
  have hm0 : 0 < m := by omega
  set mom : ℝ → Fin (m + 1) → Fin 4 → ℝ := fun u i => cs i • lineK k₀ w u with hmom_def
  have hmom : ∀ i ν, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i ν : ℝ) : ℂ) :=
    fun i ν => isUPoly_lineK (cs i) k₀ w ν
  choose Qf hQe hQq hQi using hQ
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
  -- the ingredients, node by node
  have hmaj := fun k => exists_coeff_line_majorant (Qk k) α mom hmom
    (fun q => (hQi _ q).1) (fun q => (hQi _ q).2.1)
  choose K₁ K₂ hK₁ hK₂ hK₁0 hK₂0 hKb using hmaj
  obtain ⟨L, hL⟩ := exists_norm_lam_le (2 * d) d
  obtain ⟨CS, hCS0, hCS⟩ := exists_abs_loopShift_smul_le α cs
  set Kk := ∑ ν, (|k₀ ν| + |w ν|)
  have hKk : 0 ≤ Kk := by positivity
  set K := CS * Kk
  have hK0 : 0 ≤ K := mul_nonneg hCS0 hKk
  set τ := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2)
  set c := c₀ / 2
  have hc : 0 < c := by positivity
  set q : ℝ := ((m - 3 : ℕ) : ℝ) + 3 / 2
  set H : (Fin m → ℝ) → ℝ := fun x => headSum (m - 1) x ^ (-q)
  have hH : IntegrableOn H (simplexSet m) := by
    refine integrableOn_headSum_rpow (by omega) (by omega) (by positivity) ?_
    have : ((m - 3 : ℕ) : ℝ) + 2 = ((m - 1 : ℕ) : ℝ) := by
      rw [show m - 1 = (m - 3) + 2 by omega]; push_cast; ring
    simp only [q]
    linarith
  set β : Fin (2 * d + 1) → ℝ := fun k =>
    lightB (Qk k) K τ c₀ * (Real.sqrt 8 / c₀ ^ (3 / 2 : ℝ))
  set G : Fin (2 * d + 1) → (Fin m → ℝ) → ℝ := fun k x =>
    K₁ k x / c ^ (m - 3) + K₂ k x / c ^ (m - 4) + ‖coeffThree (Qk k) α x‖ / c ^ (m - 5)
  have hG : ∀ k, IntegrableOn (G k) (simplexSet m) := fun k =>
    (((hK₁ k).div_const _).add ((hK₂ k).div_const _)).add
      (((hQi _ 0).2.2.norm).div_const _)
  have hG0 : ∀ k x, 0 ≤ G k x := fun k x => by
    have := hK₁0 k x; have := hK₂0 k x; positivity
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by
    have h1 := lqNorm_nonneg (Qk k); have h2 := lqHess_nonneg (Qk k)
    have h3 := lqQuart_nonneg (Qk k)
    have hτ : 0 ≤ τ := by positivity
    simp only [β, lightB]
    positivity
  -- the pointwise bound, node by node
  have hae0 : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ i : Fin m, x i ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_all_iff]
    exact fun i => Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) i 0
  have hpt : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
      ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ k,
        ‖paramIntegrand (Qk k) α (mom u) (Ms a b) 0 x‖ ≤ G k x + β k * H x / b := by
    intro u hu a b ha hab hb2
    have hb : 0 < b := ha.trans_le hab
    filter_upwards [ae_posDef α hm0 hspan, hae0] with x ⟨hxS, hPD⟩ hx0 k
    have hxle := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le hm0 x).mp hxS
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hU0 : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
    set y := headSum (m - 1) x with hy_def
    have hy1 : y ≤ 1 := headSum_le_one hxle.1 hxle.2
    have hy0 : 0 < y := by
      have h0 : 0 < x ⟨0, hm0⟩ := lt_of_le_of_ne (hxle.1 _) (hx0 _).symm
      exact h0.trans_le (le_headSum hxle.1 (by simp; omega))
    set V := symanzikV α (mom u) (Ms a b) (simplexPoint x)
    have hVx : c₀ * y + (1 - y) * a ^ 2 ≤ V := hV u hu a b ha hab x hxS hU0.ne'
    have ha2 : 0 ≤ (1 - y) * a ^ 2 := mul_nonneg (by linarith) (sq_nonneg a)
    have hHb : 0 ≤ β k * H x / b :=
      div_nonneg (mul_nonneg (hβ0 k) (Real.rpow_nonneg hy0.le _)) hb.le
    by_cases hyc : 1 / 2 ≤ y
    · -- away from the corner
      have hVc : c ≤ V := by simp only [c]; nlinarith
      have hV0 : 0 < V := hc.trans_le hVc
      have hW : ∀ n : ℕ, ‖(wBase α (mom u) (Ms a b) 0 x ^ n)⁻¹‖ ≤ 1 / c ^ n := fun n => by
        simp only [wBase, zero_mul, ofReal_zero, sub_zero, norm_inv, norm_pow,
          Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos hV0, one_div]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hVc n)
      obtain ⟨h1, h2⟩ := hKb k x u hu
      rw [paramIntegrand_eq]
      refine (norm_add₃_le).trans (le_trans ?_ (le_add_of_nonneg_right hHb))
      simp only [norm_mul, G]
      have e : ∀ (t K : ℝ) (n : ℕ), 0 ≤ t → t ≤ K → ∀ W : ℂ, ‖(W ^ n)⁻¹‖ ≤ 1 / c ^ n →
          t * ‖(W ^ n)⁻¹‖ ≤ K / c ^ n := fun t K n ht htK W hW' => by
        rw [div_eq_mul_one_div]
        exact mul_le_mul htK hW' (norm_nonneg _) (ht.trans htK)
      exact add_le_add (add_le_add (e _ _ _ (norm_nonneg _) h1 _ (hW _))
        (e _ _ _ (norm_nonneg _) h2 _ (hW _))) (e _ _ _ (norm_nonneg _) le_rfl _ (hW _))
    · -- near the corner
      replace hyc := not_le.mp hyc
      have hUy : y / 2 ≤ symanzikU α (simplexPoint x) := by
        have := hU x hxS
        nlinarith
      have htr := trace_symanzikMatrix_le α hz.1 hz.2
      have hX : ∀ a', ‖loopComp (-loopShift α (mom u) (simplexPoint x)) a'‖ ≤ K := fun a' => by
        simp only [loopComp, Pi.neg_apply, ofReal_neg, norm_neg, Complex.norm_real,
          Real.norm_eq_abs]
        exact (hCS _ hz.1 hU0.ne' _ a'.1 a'.2).trans
          (mul_le_mul_of_nonneg_left (norm_lineK_apply_le hu _) hCS0)
      have hcy : c₀ * y ≤ V := by linarith
      have hb8 : b ^ 2 / 8 ≤ V := by nlinarith
      have h1 := norm_paramIntegrand_le_corner (Qk k) α (mom u) (Ms a b) hm (hQq _) x hy0 hK0 hc₀
        hPD hUy htr hX hcy
      have h2 := one_div_corner_le (m - 3) hy0 hb hc₀ hcy hb8
      refine h1.trans (le_trans ?_ (le_add_of_nonneg_left (hG0 k x)))
      have hB0 : 0 ≤ lightB (Qk k) K τ c₀ := by
        have := hβ0 k
        simp only [β] at this
        exact nonneg_of_mul_nonneg_left this (by positivity)
      calc lightB (Qk k) K τ c₀ / (y ^ (m - 3) * V ^ 2)
          = lightB (Qk k) K τ c₀ * (1 / (y ^ (m - 3) * V ^ 2)) := by ring
        _ ≤ lightB (Qk k) K τ c₀ *
            (Real.sqrt 8 / c₀ ^ (3 / 2 : ℝ) * (y ^ (-q) / b)) :=
            mul_le_mul_of_nonneg_left h2 hB0
        _ = β k * H x / b := by simp only [β, H]; ring
  -- integrate
  set g : ℝ → (Fin m → ℝ) → ℝ := fun b x =>
    ∑ k, (L * G k x + L * β k * H x * b⁻¹)
  have hg : ∀ b, IntegrableOn (g b) (simplexSet m) := fun b =>
    integrable_finsetSum _ fun k _ =>
      ((hG k).const_mul L).add ((hH.const_mul (L * β k)).mul_const b⁻¹)
  refine ⟨π ^ 4 * ∑ k, L * ∫ x in simplexSet m, G k x,
    π ^ 4 * ∑ k, L * β k * ∫ x in simplexSet m, H x, fun u hu a b ha hab hb2 => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL u hu 0)
  rw [pvOf_eq (hJe u hu1), norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hint : ‖∫ x in simplexSet m, paramIntegrand (J u) α (mom u) (Ms a b) 0 x‖ ≤
      ∫ x in simplexSet m, g b x := by
    refine norm_integral_le_of_norm_le (hg b) ?_
    filter_upwards [hpt u hu a b ha hab hb2] with x hx
    simp only [J, jointQuartic, paramIntegrand_qsum, g]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    calc ‖lam (2 * d) d u k‖ * ‖paramIntegrand (Qk k) α (mom u) (Ms a b) 0 x‖
        ≤ L * (G k x + β k * H x / b) :=
          mul_le_mul (hL u hu k) (hx k) (norm_nonneg _) hL0
      _ = L * G k x + L * β k * H x * b⁻¹ := by ring
  have hgi : ∫ x in simplexSet m, g b x = (∑ k, L * ∫ x in simplexSet m, G k x) +
      (∑ k, L * β k * ∫ x in simplexSet m, H x) / b := by
    simp only [g]
    rw [integral_finsetSum (f := fun k x => L * G k x + L * β k * H x * b⁻¹) _ fun k _ =>
      ((hG k).const_mul L).add ((hH.const_mul (L * β k)).mul_const b⁻¹)]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add ((hG k).const_mul L) ((hH.const_mul (L * β k)).mul_const b⁻¹),
      integral_const_mul, integral_mul_const, integral_const_mul]
    ring
  rw [hgi] at hint
  calc π ^ 4 * ‖∫ x in simplexSet m, paramIntegrand (J u) α (mom u) (Ms a b) 0 x‖
      ≤ π ^ 4 * ((∑ k, L * ∫ x in simplexSet m, G k x) +
        (∑ k, L * β k * ∫ x in simplexSet m, H x) / b) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

end QED.GradedProof.RPi4

end
