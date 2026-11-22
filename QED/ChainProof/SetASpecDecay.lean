/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtGenSpec
public import Mathlib.MeasureTheory.Integral.Pi
import QED.Integration.TwoLoopParametricAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (a): large-mass decay of the photon-product vertex

Helper level for the fixed-`ε` spectral form of the two-loop vacuum polarization (set (a)
headline (HA₆)). The one-loop vertex with a product of `k + 2` photon-type denominators,
`QED.TwoLoop.VPHalfAtLimit.prodIntegrand`, is `GoodEF` with a constant uniform in the masses
`≥ M₀` and in all prescriptions (`QED.TwoLoop.VPHalfAtAssembly.exists_goodEF_prodIntegrand`).
This file shows that when the first `r ≤ k` masses are at least `μ`, the constant decays like
`μ^{-2r}`, uniformly in everything else:

* `saDec_integral_rpow_le`, `saDec_integral_pow_mul_rpow_le`: one-dimensional integrals
  `∫₀¹ tⁿ (A + tX)^{-s} dt ≤ C A^{n+1-s} (A + X)^{-(n+1)}`, `s > n + 1`;
* `saDec_setIntegral_simplex_le`: `∫_Δ (A + (u₀ + ⋯ + u_{r-1}) Y)^{-q} ≤ C A^{r-q} Y^{-r}`,
  `q > r`, by bounding the integrand by a product over the first `r` coordinates;
* `saDec_exists_norm_timeP_le`, `saDec_exists_norm_spatialP_le`: the closed-form energy integral
  of `QED.TwoLoop.VPHalfAtLimit.powIntegrand` is at most
  `C (1 + ‖v‖)⁻¹ ((1 + ‖v‖)² + M²)^{-(n+1)}`, from the vertex mass `(1 - y) M²` and the Feynman
  weight `y (1 - y)ⁿ`;
* **`saDec_exists_goodEF_prodIntegrand`**: the decay `K μ^{-2r}` of the `GoodEF` constant.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly

/-! ### One-dimensional integrals -/

theorem saDec_integral_rpow_le {A Y σ : ℝ} (hA : 0 < A) (hY : 0 < Y) (hσ : 1 < σ) :
    ∫ t in (0 : ℝ)..1, (A + t * Y) ^ (-σ) ≤ A ^ (1 - σ) / ((σ - 1) * Y) := by
  have e : (fun t : ℝ => (A + t * Y) ^ (-σ)) = fun t => (fun x : ℝ => x ^ (-σ)) (Y * t + A) := by
    funext t
    show _ = (Y * t + A) ^ (-σ)
    ring_nf
  rw [e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ (-σ)) hY.ne' A]
  simp only [mul_zero, zero_add, mul_one]
  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
  · have h1 : -σ + 1 = 1 - σ := by ring
    have hpos : 0 ≤ (Y + A) ^ (1 - σ) := Real.rpow_nonneg (by linarith) _
    have hs : (1 : ℝ) - σ ≠ 0 := by linarith
    rw [h1, smul_eq_mul]
    have e2 : Y⁻¹ * (((Y + A) ^ (1 - σ) - A ^ (1 - σ)) / (1 - σ)) =
        (A ^ (1 - σ) - (Y + A) ^ (1 - σ)) / ((σ - 1) * Y) := by
      field_simp
      ring
    rw [e2]
    exact div_le_div_of_nonneg_right (by linarith) (by nlinarith)
  · rw [mem_uIcc]
    rintro (⟨h, -⟩ | ⟨h, -⟩) <;> linarith

theorem saDec_continuousOn_rpow {A X : ℝ} (hA : 0 < A) (hX : 0 ≤ X) (s : ℝ) :
    ContinuousOn (fun t : ℝ => (A + t * X) ^ (-s)) (Icc 0 1) := by
  refine ContinuousOn.rpow_const (by fun_prop) fun t ht => Or.inl ?_
  have := ht.1
  have : 0 < A + t * X := by positivity
  exact this.ne'

theorem saDec_inv_pow_le {A X : ℝ} (hA : 0 < A) (hXA : X ≤ A) (hX : 0 ≤ X) (n : ℕ) :
    (A ^ n)⁻¹ ≤ 2 ^ n * ((X + A) ^ n)⁻¹ := by
  have h1 : (A ^ n)⁻¹ = 2 ^ n * ((2 * A) ^ n)⁻¹ := by
    rw [mul_pow]
    field_simp
  rw [h1]
  gcongr
  linarith

/-- `∫₀¹ tⁿ (A + tX)^{-s} dt ≤ 2ⁿ⁺¹ (1 + (s-n-1)⁻¹) A^{n+1-s} (A + X)^{-(n+1)}`. -/
theorem saDec_integral_pow_mul_rpow_le {A X s : ℝ} (n : ℕ) (hA : 0 < A) (hX : 0 ≤ X)
    (hs : (n : ℝ) + 1 < s) :
    ∫ t in (0 : ℝ)..1, t ^ n * (A + t * X) ^ (-s) ≤
      2 ^ (n + 1) * (1 + (s - n - 1)⁻¹) * A ^ ((n : ℝ) + 1 - s) * ((A + X) ^ (n + 1))⁻¹ := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ n * (A + t * X) ^ (-s)) volume 0 1 :=
    ((continuousOn_pow n).mul (saDec_continuousOn_rpow hA hX s)).intervalIntegrable_of_Icc
      zero_le_one
  have hsn : 0 < s - n - 1 := by linarith
  have hc : 1 ≤ 1 + (s - n - 1)⁻¹ := by have := inv_pos.2 hsn; linarith
  have hAX : 0 < A + X := by linarith
  set e : ℝ := (n : ℝ) + 1 - s
  have hAe : 0 < A ^ e := Real.rpow_pos_of_pos hA _
  rcases le_or_gt X A with hXA | hXA
  · have h1 : ∫ t in (0 : ℝ)..1, t ^ n * (A + t * X) ^ (-s) ≤ ∫ _ in (0 : ℝ)..1, A ^ (-s) := by
      refine intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
        fun t ht => ?_
      have ht1 : t ^ n ≤ 1 := pow_le_one₀ ht.1 ht.2
      have ht0 : 0 ≤ t := ht.1
      have h2 : (A + t * X) ^ (-s) ≤ A ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hA (by nlinarith) (by linarith)
      have h3 : 0 ≤ (A + t * X) ^ (-s) := Real.rpow_nonneg (by positivity) _
      calc t ^ n * (A + t * X) ^ (-s) ≤ 1 * A ^ (-s) := by gcongr
        _ = A ^ (-s) := one_mul _
    rw [intervalIntegral.integral_const, sub_zero, one_smul] at h1
    refine h1.trans ?_
    have hsplit : A ^ (-s) = A ^ e * (A ^ (n + 1))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hA.le, ← Real.rpow_add hA]
      congr 1
      simp only [e]
      push_cast
      ring
    rw [hsplit]
    have h4 := saDec_inv_pow_le hA hXA hX (n + 1)
    rw [add_comm X A] at h4
    calc A ^ e * (A ^ (n + 1))⁻¹ ≤ A ^ e * (2 ^ (n + 1) * ((A + X) ^ (n + 1))⁻¹) := by gcongr
      _ = 2 ^ (n + 1) * 1 * A ^ e * ((A + X) ^ (n + 1))⁻¹ := by ring
      _ ≤ 2 ^ (n + 1) * (1 + (s - n - 1)⁻¹) * A ^ e * ((A + X) ^ (n + 1))⁻¹ := by gcongr
  · have hX0 : 0 < X := hA.trans hXA
    have hint2 : IntervalIntegrable (fun t : ℝ => (X ^ n)⁻¹ * (A + t * X) ^ (-(s - n)))
        volume 0 1 :=
      ((saDec_continuousOn_rpow hA hX (s - n)).intervalIntegrable_of_Icc zero_le_one).const_mul _
    have h1 : ∫ t in (0 : ℝ)..1, t ^ n * (A + t * X) ^ (-s) ≤
        ∫ t in (0 : ℝ)..1, (X ^ n)⁻¹ * (A + t * X) ^ (-(s - n)) := by
      refine intervalIntegral.integral_mono_on zero_le_one hint hint2 fun t ht => ?_
      have ht0 : 0 ≤ t := ht.1
      have hB : 0 < A + t * X := by positivity
      have hsplit : (A + t * X) ^ (-s) = (A + t * X) ^ (-(s - n)) * ((A + t * X) ^ n)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_neg hB.le, ← Real.rpow_add hB]
        congr 1
        ring
      rw [hsplit]
      have hp : 0 ≤ (A + t * X) ^ (-(s - n)) := Real.rpow_nonneg hB.le _
      have hq : t ^ n * ((A + t * X) ^ n)⁻¹ ≤ (X ^ n)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
          le_div_iff₀ (by positivity), ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) n
      calc t ^ n * ((A + t * X) ^ (-(s - n)) * ((A + t * X) ^ n)⁻¹)
          = (t ^ n * ((A + t * X) ^ n)⁻¹) * (A + t * X) ^ (-(s - n)) := by ring
        _ ≤ (X ^ n)⁻¹ * (A + t * X) ^ (-(s - n)) := by gcongr
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 := saDec_integral_rpow_le hA hX0 (σ := s - n) (by linarith)
    have h3 : 1 - (s - n) = e := by simp only [e]; ring
    rw [h3] at h2
    have h5 : (X ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * ((A + X) ^ (n + 1))⁻¹ :=
      saDec_inv_pow_le hX0 hXA.le hA.le (n + 1)
    calc (X ^ n)⁻¹ * ∫ t in (0 : ℝ)..1, (A + t * X) ^ (-(s - n))
        ≤ (X ^ n)⁻¹ * (A ^ e / ((s - n - 1) * X)) := by gcongr
      _ = (s - n - 1)⁻¹ * A ^ e * (X ^ (n + 1))⁻¹ := by
          rw [pow_succ]
          have : s - ↑n - 1 ≠ 0 := hsn.ne'
          field_simp
      _ ≤ (s - n - 1)⁻¹ * A ^ e * (2 ^ (n + 1) * ((A + X) ^ (n + 1))⁻¹) := by gcongr
      _ = 2 ^ (n + 1) * (0 + (s - n - 1)⁻¹) * A ^ e * ((A + X) ^ (n + 1))⁻¹ := by ring
      _ ≤ 2 ^ (n + 1) * (1 + (s - n - 1)⁻¹) * A ^ e * ((A + X) ^ (n + 1))⁻¹ := by
          gcongr
          norm_num

/-! ### The simplex integral -/

/-- The sum `u₀ + ⋯ + u_{r-1}` of the first `r` coordinates. -/
def saHeavySum {d : ℕ} (r : ℕ) (u : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, if (i : ℕ) < r then u i else 0

theorem saDec_nonneg_of_mem {d : ℕ} {u : Fin d → ℝ} (hu : u ∈ simplexSet d) (i : Fin d) :
    0 ≤ u i :=
  (simplexSet_subset_Icc d hu).1 i

theorem saHeavySum_nonneg {d r : ℕ} {u : Fin d → ℝ} (hu : u ∈ simplexSet d) :
    0 ≤ saHeavySum r u :=
  Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact saDec_nonneg_of_mem hu i
    · exact le_rfl

theorem le_saHeavySum {d r : ℕ} {u : Fin d → ℝ} (hu : u ∈ simplexSet d) {i : Fin d}
    (hi : (i : ℕ) < r) : u i ≤ saHeavySum r u := by
  have h := Finset.single_le_sum (f := fun j : Fin d => if (j : ℕ) < r then u j else 0)
    (fun j _ => by
      split_ifs
      · exact saDec_nonneg_of_mem hu j
      · exact le_rfl) (Finset.mem_univ i)
  simp only [hi, ite_true] at h
  exact h

theorem continuous_saHeavySum {d : ℕ} (r : ℕ) : Continuous (saHeavySum (d := d) r) := by
  unfold saHeavySum
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

theorem saDec_le_one_of_mem {d : ℕ} {u : Fin d → ℝ} (hu : u ∈ simplexSet d) (i : Fin d) :
    u i ≤ 1 :=
  (simplexSet_subset_Icc d hu).2 i

theorem saDec_integrableOn_simplex {d r q : ℕ} {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) :
    IntegrableOn (fun u : Fin d → ℝ => ((A + saHeavySum r u * Y) ^ q)⁻¹) (simplexSet d) := by
  refine ContinuousOn.integrableOn_compact (isCompact_simplexSet d) ?_
  refine ContinuousOn.inv₀ ((continuous_const.add
    ((continuous_saHeavySum r).mul continuous_const)).pow q).continuousOn fun u hu => ?_
  have := saHeavySum_nonneg (r := r) hu
  positivity

/-- **The simplex integral**: `∫_Δ (A + (u₀ + ⋯ + u_{r-1}) Y)^{-q} ≤ (A^{1-ρ}/((ρ-1) Y))^r`,
`ρ = q/r > 1`. -/
theorem saDec_setIntegral_simplex_le {d r q : ℕ} (hr : 1 ≤ r) (hrd : r ≤ d) (hq : r < q)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) :
    ∫ u in simplexSet d, ((A + saHeavySum r u * Y) ^ q)⁻¹ ≤
      (A ^ (1 - (q : ℝ) / r) / (((q : ℝ) / r - 1) * Y)) ^ r := by
  set ρ : ℝ := (q : ℝ) / r with hρ_def
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hρ : 1 < ρ := by
    rw [hρ_def, one_lt_div hr0]
    exact_mod_cast hq
  have hρr : ρ * r = q := by rw [hρ_def]; field_simp
  set f : Fin d → ℝ → ℝ := fun i x => if (i : ℕ) < r then (A + x * Y) ^ (-ρ) else 1 with hf
  set g : (Fin d → ℝ) → ℝ := fun u => ∏ i, f i (u i) with hg
  set cube : Set (Fin d → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1
  have hcard : (Finset.univ.filter fun i : Fin d => (i : ℕ) < r).card = r := by
    rw [Fin.card_filter_val_lt]
    exact min_eq_right hrd
  -- the pointwise bound
  have hpt : ∀ u ∈ simplexSet d, ((A + saHeavySum r u * Y) ^ q)⁻¹ ≤ g u := by
    intro u hu
    have hS := saHeavySum_nonneg (r := r) hu
    have hB : 0 < A + saHeavySum r u * Y := by positivity
    have e1 : ((A + saHeavySum r u * Y) ^ q)⁻¹ =
        ∏ i : Fin d, (if (i : ℕ) < r then (A + saHeavySum r u * Y) ^ (-ρ) else 1) := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hcard,
        ← Real.rpow_natCast (_ ^ (-ρ)) r, ← Real.rpow_mul hB.le, ← Real.rpow_natCast _ q,
        ← Real.rpow_neg hB.le, neg_mul, hρr]
    rw [e1]
    refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
    · split_ifs
      · exact Real.rpow_nonneg hB.le _
      · exact zero_le_one
    · simp only [hf]
      split_ifs with hi
      · have hui := le_saHeavySum hu hi (r := r)
        have h0 := saDec_nonneg_of_mem hu i
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
      · exact le_rfl
  -- integrability of the bound on the cube
  have hfi : ∀ i, Integrable (f i) (volume.restrict (Icc (0 : ℝ) 1)) := by
    intro i
    simp only [hf]
    split_ifs
    · exact (saDec_continuousOn_rpow hA hY.le ρ).integrableOn_compact isCompact_Icc
    · exact integrable_const _
  have hvol : (volume : Measure (Fin d → ℝ)).restrict cube =
      Measure.pi fun _ => volume.restrict (Icc (0 : ℝ) 1) := by
    rw [← Measure.restrict_pi_pi]
    rfl
  have hgi : IntegrableOn g cube := by
    rw [IntegrableOn, hvol]
    exact Integrable.fintype_prod hfi
  have hsub : simplexSet d ⊆ cube := fun u hu i _ =>
    ⟨saDec_nonneg_of_mem hu i, saDec_le_one_of_mem hu i⟩
  have hg0 : ∀ u ∈ cube, 0 ≤ g u := fun u hu => Finset.prod_nonneg fun i _ => by
    simp only [hf]
    split_ifs
    · exact Real.rpow_nonneg (by have := (hu i (mem_univ i)).1; positivity) _
    · exact zero_le_one
  have step1 : ∫ u in simplexSet d, ((A + saHeavySum r u * Y) ^ q)⁻¹ ≤ ∫ u in simplexSet d, g u :=
    setIntegral_mono_on (saDec_integrableOn_simplex hA hY.le) (hgi.mono_set hsub)
      (measurableSet_simplexSet d) hpt
  have step2 : ∫ u in simplexSet d, g u ≤ ∫ u in cube, g u :=
    setIntegral_mono_set hgi
      ((ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).2
        (Eventually.of_forall hg0))
      (Eventually.of_forall hsub)
  have step3 : ∫ u in cube, g u = (∫ x in (0 : ℝ)..1, (A + x * Y) ^ (-ρ)) ^ r := by
    rw [hvol, integral_fintype_prod_eq_prod]
    have e : ∀ i : Fin d, ∫ x, f i x ∂(volume.restrict (Icc (0 : ℝ) 1)) =
        if (i : ℕ) < r then ∫ x in (0 : ℝ)..1, (A + x * Y) ^ (-ρ) else 1 := by
      intro i
      simp only [hf]
      split_ifs
      · rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
      · simp
    simp_rw [e]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  have hI0 : 0 ≤ ∫ x in (0 : ℝ)..1, (A + x * Y) ^ (-ρ) :=
    intervalIntegral.integral_nonneg zero_le_one fun x hx =>
      Real.rpow_nonneg (by have := hx.1; positivity) _
  calc _ ≤ ∫ u in cube, g u := step1.trans step2
    _ = _ := step3
    _ ≤ _ := pow_le_pow_left₀ hI0 (saDec_integral_rpow_le hA hY hρ) r

/-! ### The closed-form energy integral -/

theorem saDec_norm_feynWt_le {n : ℕ} {z : ℝ × ℝ} (hy : z.2 ∈ Icc (0 : ℝ) 1) :
    ‖feynWt n z‖ ≤ (n + 1) * (n + 2) * (1 - z.2) ^ n := by
  have hy0 := hy.1
  have hy1 : 0 ≤ 1 - z.2 := by linarith [hy.2]
  have hc : ((n + 1) * (n + 2) : ℂ) = (((n + 1) * (n + 2) : ℝ) : ℂ) := by push_cast; ring
  have hw : ((z.2 : ℂ) * (1 - z.2) ^ n) = ((z.2 * (1 - z.2) ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [feynWt, hc, hw, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hp := pow_nonneg hy1 n
  have : z.2 * (1 - z.2) ^ n ≤ (1 - z.2) ^ n := by nlinarith [hy.2]
  gcongr

/-- **The closed form decays in the photon mass**: with `B = (1 + ‖v‖)² + (1 - y) M²`,
`‖timeP … z v‖ ≤ K B^{-(n + 3/2)}`. -/
theorem saDec_exists_norm_timeP_le {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (α : ℂ) {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, M₀ ≤ M → ∀ ε' : ℝ, ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ∀ v : Fin 3 → ℝ, ‖timeP α N m M n ε' p' p z v‖ ≤
        K * ((1 + ‖v‖) ^ 2 + (1 - z.2) * M ^ 2) ^ (-((n : ℝ) + 3 / 2)) := by
  have hCN0 := nonneg_of_norm_le hNb
  set c0 : ℝ := 3 / 4 * min (M₀ ^ 2) (m ^ 2) with hc0_def
  have hc0 : 0 < c0 := by positivity
  set A0 : ℝ := ‖p'‖ + ‖p‖ with hA0_def
  have hA0 : 0 ≤ A0 := by positivity
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) A0 hc0
  set c : ℝ := min c1 1 / 2 with hc_def
  have hc : 0 < c := by positivity
  set s1 : ℝ := (n : ℝ) + 3 / 2
  set s2 : ℝ := (n : ℝ) + 5 / 2
  set K1 : ℝ := ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| * c ^ (-s1)
  set K2 : ℝ := CN * (1 + A0) ^ 2 * |energyConst (n + 3)| * c ^ (-s2)
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  refine ⟨K1 + K2, by positivity, fun M hM ε' z hz v => ?_⟩
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  have hy1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hyM : 0 ≤ (1 - z.2) * M ^ 2 := by positivity
  set B : ℝ := u ^ 2 + (1 - z.2) * M ^ 2 with hB_def
  have hu2 : u ^ 2 ≤ B := by simp only [B]; linarith
  have hB : 0 < B := by nlinarith
  set W : ℝ := massW m M p' p z v
  have hD : c0 ≤ feynmanMass m M z.1 z.2 p' p := by
    refine le_trans ?_ (feynmanMass_pos hp' hp hp0' hp0 hz.1 hz.2)
    have hM0 : M₀ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM₀.le hM 2
    simp only [c0]
    gcongr
  have hb : ‖(fun k : Fin 3 => shiftK p' p z k.succ)‖ ≤ A0 :=
    (pi_norm_le_iff_of_nonneg hA0).2 fun k =>
      (norm_le_pi_norm (shiftK p' p z) k.succ).trans (norm_shiftK_le p' p hz)
  have hW1 : c1 * u ^ 2 ≤ W := hcoer v _ _ hb hD
  have hW2 : (1 - z.2) * M ^ 2 ≤ W := by
    have h1 := feynmanMass_ge (M := M) (y := z.2) hp' hp hp0' hp0 hz.1
    have h2 : 0 ≤ ∑ k : Fin 3, (v k + shiftK p' p z k.succ) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h3 : 0 ≤ z.2 ^ 2 * m ^ 2 := by positivity
    simp only [W, massW]
    linarith
  have hcB : c * B ≤ W := by
    have e1 : c * u ^ 2 ≤ c1 / 2 * u ^ 2 :=
      mul_le_mul_of_nonneg_right (by simp only [c]; linarith [min_le_left c1 1]) (sq_nonneg u)
    have e2 : c * ((1 - z.2) * M ^ 2) ≤ 1 / 2 * ((1 - z.2) * M ^ 2) :=
      mul_le_mul_of_nonneg_right (by simp only [c]; linarith [min_le_right c1 1]) hyM
    have e3 : c * B = c * u ^ 2 + c * ((1 - z.2) * M ^ 2) := by simp only [B]; ring
    linarith
  have hcBpos : 0 < c * B := by positivity
  have hW0 : 0 < W := hcBpos.trans_le hcB
  have hs1 : 0 ≤ s1 := by positivity
  have hs2 : 0 ≤ s2 := by positivity
  have r1 : W ^ (-s1) ≤ c ^ (-s1) * B ^ (-s1) := by
    rw [← Real.mul_rpow hc.le hB.le]
    exact Real.rpow_le_rpow_of_nonpos hcBpos hcB (by linarith)
  have hBs : u ^ 2 * B ^ (-s2) ≤ B ^ (-s1) := by
    have e : B ^ (-s1) = B * B ^ (-s2) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [← Real.rpow_one_add' hB.le (by simp only [s2]; intro h; linarith)]
      congr 1
      simp only [s1, s2]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hu2 (Real.rpow_nonneg hB.le _)
  have r2 : u ^ 2 * W ^ (-s2) ≤ c ^ (-s2) * B ^ (-s1) := by
    have h1 : W ^ (-s2) ≤ c ^ (-s2) * B ^ (-s2) := by
      rw [← Real.mul_rpow hc.le hB.le]
      exact Real.rpow_le_rpow_of_nonpos hcBpos hcB (by linarith)
    calc u ^ 2 * W ^ (-s2) ≤ u ^ 2 * (c ^ (-s2) * B ^ (-s2)) := by gcongr
      _ = c ^ (-s2) * (u ^ 2 * B ^ (-s2)) := by ring
      _ ≤ c ^ (-s2) * B ^ (-s1) := by gcongr
  have hNt : ‖N (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ CN * (1 + A0) ^ 2 * u ^ 2 := by
    refine (hNb _).trans ?_
    have ha : |-shiftK p' p z 0| ≤ A0 := by
      rw [abs_neg]
      exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans
        (norm_shiftK_le p' p hz)
    have h1 := norm_finCons_le (-shiftK p' p z 0) v
    have h2 : 1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ (1 + A0) * u := by
      simp only [u]; nlinarith [norm_nonneg v]
    calc CN * (1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖) ^ 2
        ≤ CN * ((1 + A0) * u) ^ 2 := by gcongr
      _ = CN * (1 + A0) ^ 2 * u ^ 2 := by ring
  have hc1' := norm_cpow_neg_add_mul_I_le (ε := ε') hW0 hs1
  have hc2' := norm_cpow_neg_add_mul_I_le (ε := ε') hW0 hs2
  have hK : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [timeP, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hK, hK]
  have hE1 : 0 ≤ ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| := by positivity
  have hE3 : 0 ≤ CN * (1 + A0) ^ 2 * |energyConst (n + 3)| := by positivity
  calc ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| *
        ‖(-(W : ℂ) + ε' * I) ^ (-((s1 : ℝ) : ℂ))‖ +
      ‖N (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ * |energyConst (n + 3)| *
        ‖(-(W : ℂ) + ε' * I) ^ (-((s2 : ℝ) : ℂ))‖
      ≤ ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| * (c ^ (-s1) * B ^ (-s1)) +
        (CN * (1 + A0) ^ 2 * u ^ 2) * |energyConst (n + 3)| * W ^ (-s2) := by
        gcongr
        exact hc1'.trans r1
    _ = ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| * (c ^ (-s1) * B ^ (-s1)) +
        CN * (1 + A0) ^ 2 * |energyConst (n + 3)| * (u ^ 2 * W ^ (-s2)) := by ring
    _ ≤ ‖α‖ * |energyConst (n + 2) - energyConst (n + 3)| * (c ^ (-s1) * B ^ (-s1)) +
        CN * (1 + A0) ^ 2 * |energyConst (n + 3)| * (c ^ (-s2) * B ^ (-s1)) := by gcongr
    _ = (K1 + K2) * B ^ (-s1) := by simp only [K1, K2]; ring

/-- **The energy integral decays in the photon mass**:
`‖spatialP v‖ ≤ C ((1 + ‖v‖)²)^{-1/2} ((1 + ‖v‖)² + M²)^{-(n+1)}`. -/
theorem saDec_exists_norm_spatialP_le {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (α : ℂ) {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, M₀ ≤ M → ∀ ε η : ℝ, ∀ v : Fin 3 → ℝ,
      ‖spatialP α N m M n ε η p' p v‖ ≤
        C * ((1 + ‖v‖) ^ 2) ^ (-(1 / 2 : ℝ)) * (((1 + ‖v‖) ^ 2 + M ^ 2) ^ (n + 1))⁻¹ := by
  obtain ⟨K, hK, hT⟩ := saDec_exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb n
  set s : ℝ := (n : ℝ) + 3 / 2 with hs_def
  set L : ℝ := 2 ^ (n + 1) * (1 + (s - n - 1)⁻¹)
  have hL : 0 ≤ L := by
    have : 0 < s - n - 1 := by simp only [s]; linarith
    positivity
  refine ⟨((n : ℝ) + 1) * ((n : ℝ) + 2) * K * L, by positivity, fun M hM ε η v => ?_⟩
  set A : ℝ := (1 + ‖v‖) ^ 2 with hA_def
  have hA : 0 < A := by positivity
  set X : ℝ := M ^ 2
  have hX : 0 ≤ X := sq_nonneg M
  set H : ℝ → ℝ := fun t => ((n : ℝ) + 1) * ((n : ℝ) + 2) * K * (t ^ n * (A + t * X) ^ (-s))
  have hHi : IntervalIntegrable H volume 0 1 :=
    (((continuousOn_pow n).mul (saDec_continuousOn_rpow hA hX s)).intervalIntegrable_of_Icc
      zero_le_one).const_mul _
  have hH1 : IntegrableOn (fun y => H (1 - y)) (Ioc (0 : ℝ) 1) := by
    have h := hHi.comp_sub_left 1
    simp only [sub_zero, sub_self] at h
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h.symm
  have hpt : ∀ᵐ z ∂feynmanMeasure,
      ‖feynWt n z * timeP α N m M n (effEps ε η z) p' p z v‖ ≤ 1 * H (1 - z.2) := by
    filter_upwards [ae_feynmanMeasure] with z hz
    have hzI := Ioc_prod_subset hz
    rw [norm_mul, one_mul]
    have h1 := saDec_norm_feynWt_le (n := n) hzI.2
    have h2 := hT M hM (effEps ε η z) z hzI v
    have hy : 0 ≤ 1 - z.2 := by linarith [hzI.2.2]
    calc ‖feynWt n z‖ * ‖timeP α N m M n (effEps ε η z) p' p z v‖
        ≤ ((n + 1) * (n + 2) * (1 - z.2) ^ n) * (K * (A + (1 - z.2) * X) ^ (-s)) := by
          gcongr
      _ = H (1 - z.2) := by simp only [H]; ring
  have hint : Integrable (fun z : ℝ × ℝ => 1 * H (1 - z.2)) feynmanMeasure :=
    (integrable_const (1 : ℝ)).mul_prod hH1
  have hval : ∫ z, 1 * H (1 - z.2) ∂feynmanMeasure = ∫ t in (0 : ℝ)..1, H t := by
    rw [feynmanMeasure, integral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun y => H (1 - y))]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_mul]
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_left (fun t => H t) 1]
    simp
  have hmain : ‖spatialP α N m M n ε η p' p v‖ ≤ ∫ t in (0 : ℝ)..1, H t := by
    rw [spatialP, ← hval]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint hpt
  refine hmain.trans ?_
  simp only [H]
  rw [intervalIntegral.integral_const_mul]
  have hL1 := saDec_integral_pow_mul_rpow_le n hA hX (s := s) (by simp only [s]; linarith)
  have he : (n : ℝ) + 1 - s = -(1 / 2) := by simp only [s]; ring
  rw [he] at hL1
  calc ((n : ℝ) + 1) * ((n : ℝ) + 2) * K * ∫ t in (0 : ℝ)..1, t ^ n * (A + t * X) ^ (-s)
      ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * K *
          (2 ^ (n + 1) * (1 + (s - n - 1)⁻¹) * A ^ (-(1 / 2 : ℝ)) * ((A + X) ^ (n + 1))⁻¹) := by
        gcongr
    _ = _ := by simp only [L]; ring

/-! ### The photon-product vertex -/

/-- When the first `r` photon masses are at least `μ`, `M(u)² ≥ (u₀ + ⋯ + u_{r-1}) μ²`. -/
theorem saDec_mixMassSq_ge {k r : ℕ} {Ms : Fin (k + 2) → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hheavy : ∀ j : Fin (k + 2), (j : ℕ) < r → μ ≤ Ms j) {u : Fin (k + 1) → ℝ}
    (hu : u ∈ simplexSet (k + 1)) : saHeavySum r u * μ ^ 2 ≤ mixMassSq Ms u := by
  unfold mixMassSq saHeavySum
  rw [Finset.sum_mul, Fin.sum_univ_castSucc (f := fun j => simplexPoint u j * Ms j ^ 2)]
  have hlast : 0 ≤ simplexPoint u (Fin.last (k + 1)) * Ms (Fin.last (k + 1)) ^ 2 :=
    mul_nonneg ((simplexPoint_mem_stdSimplex hu).1 _) (sq_nonneg _)
  have h : ∑ i : Fin (k + 1), (if (i : ℕ) < r then u i else 0) * μ ^ 2 ≤
      ∑ i : Fin (k + 1), simplexPoint u (Fin.castSucc i) * Ms (Fin.castSucc i) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hpt : simplexPoint u (Fin.castSucc i) = u i :=
      QED.Integration.TwoLoop.simplexPoint_castSucc u i
    rw [hpt]
    have h0 := saDec_nonneg_of_mem hu i
    split_ifs with hi
    · have h1 := hheavy (Fin.castSucc i) (by simpa using hi)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ h1 2) h0
    · rw [zero_mul]
      exact mul_nonneg h0 (sq_nonneg _)
  linarith

/-- **Large-mass decay of the photon-product vertex**: when the first `r ≤ k` of the `k + 2`
photon masses are at least `μ`, the vertex is `GoodEF` with constant `K μ^{-2r}`, `K`
independent of the masses `≥ M₀`, of `μ` and of all prescriptions. -/
theorem saDec_exists_goodEF_prodIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : ℝ, 0 < μ → ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) →
      (∀ j, 0 < es j) → (∀ j : Fin (k + 2), (j : ℕ) < r → μ ≤ Ms j) → ∀ ε : ℝ, 0 < ε →
      GoodEF (prodIntegrand N m Ms es ε p' p) (K * ((μ ^ 2) ^ r)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := saDec_exists_norm_spatialP_le hm hM₀ hp' hp hp0' hp0 α hNb (k + 1)
  set ρ : ℝ := ((k + 2 : ℕ) : ℝ) / r with hρ_def
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hρ : 1 < ρ := by
    rw [hρ_def, one_lt_div hr0]
    exact_mod_cast (by omega : r < k + 2)
  have hρ1 : 0 < ρ - 1 := by linarith
  refine ⟨((k + 1).factorial : ℝ) * C * ((ρ - 1)⁻¹) ^ r, by positivity,
    fun μ hμ Ms es hMs hes hheavy ε hε => ?_⟩
  refine ⟨efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε, fun v => ?_⟩
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  set A : ℝ := (1 + ‖v‖) ^ 2 with hA_def
  have hA1 : 1 ≤ A := by
    have := norm_nonneg v
    simp only [A]
    nlinarith
  have hA : 0 < A := by linarith
  have hμ2 : 0 < μ ^ 2 := by positivity
  rw [integral_time_prodIntegrand hNc hNb m Ms hes hε p' p v, norm_mul, Complex.norm_natCast]
  set g : (Fin (k + 1) → ℝ) → ℝ := fun u =>
    C * A ^ (-(1 / 2 : ℝ)) * ((A + saHeavySum r u * μ ^ 2) ^ (k + 2))⁻¹
  have hbd : ∀ u ∈ simplexSet (k + 1),
      ‖∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t)‖ ≤ g u := by
    intro u hu
    have hs : ∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t) =
        spatialP α N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p v :=
      integral_time_powIntegrand hNc hNq hNb m (mixMass Ms u) (k + 1) (η := mixEps es u) hε
        (he₀.trans_le (mixEps_ge hes₀ hu)) p' p v
    rw [hs]
    refine (hC (mixMass Ms u) (mixMass_ge hM₀.le hMs hu) ε (mixEps es u) v).trans ?_
    have hsq : mixMass Ms u ^ 2 = mixMassSq Ms u := Real.sq_sqrt (mixMassSq_nonneg Ms hu)
    rw [hsq]
    have h1 := saDec_mixMassSq_ge hμ.le hheavy hu
    have h2 := saHeavySum_nonneg (r := r) hu
    have h3 : 0 < A + saHeavySum r u * μ ^ 2 := by positivity
    simp only [g]
    gcongr
  have hgi : IntegrableOn g (simplexSet (k + 1)) :=
    (saDec_integrableOn_simplex hA hμ2.le).const_mul (C * A ^ (-(1 / 2 : ℝ)))
  have hI := saDec_setIntegral_simplex_le (d := k + 1) (q := k + 2) hr (by omega) (by omega)
    hA hμ2
  have hmain : ‖∫ u in simplexSet (k + 1), ∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t)‖
      ≤ C * A ^ (-(1 / 2 : ℝ)) * (A ^ (1 - ρ) / ((ρ - 1) * μ ^ 2)) ^ r := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hgi
      ((ae_restrict_iff' (measurableSet_simplexSet _)).2 (Eventually.of_forall hbd))).trans ?_
    simp only [g]
    rw [integral_const_mul]
    have hc : 0 ≤ C * A ^ (-(1 / 2 : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hI hc
  have hexp : A ^ (-(1 / 2 : ℝ)) * (A ^ (1 - ρ)) ^ r ≤ (1 + ‖v‖) ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast (A ^ (1 - ρ)) r, ← Real.rpow_mul hA.le, ← Real.rpow_add hA]
    have e5 : (1 + ‖v‖) ^ (-(5 : ℝ)) = A ^ (-(5 / 2 : ℝ)) := by
      simp only [A]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [e5]
    refine Real.rpow_le_rpow_of_exponent_le hA1 ?_
    have e6 : (1 - ρ) * r = r - (k + 2) := by
      simp only [hρ_def]
      field_simp
      push_cast
      ring
    rw [e6]
    have : (r : ℝ) ≤ k := by exact_mod_cast hrk
    linarith
  have hfac : (0 : ℝ) ≤ ((k + 1).factorial : ℝ) := by positivity
  calc ((k + 1).factorial : ℝ) *
        ‖∫ u in simplexSet (k + 1), ∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t)‖
      ≤ ((k + 1).factorial : ℝ) * (C * A ^ (-(1 / 2 : ℝ)) *
          (A ^ (1 - ρ) / ((ρ - 1) * μ ^ 2)) ^ r) := by gcongr
    _ = ((k + 1).factorial : ℝ) * C * ((ρ - 1)⁻¹) ^ r * ((μ ^ 2) ^ r)⁻¹ *
          (A ^ (-(1 / 2 : ℝ)) * (A ^ (1 - ρ)) ^ r) := by
        rw [div_pow, mul_pow, inv_pow]
        field_simp
    _ ≤ ((k + 1).factorial : ℝ) * C * ((ρ - 1)⁻¹) ^ r * ((μ ^ 2) ^ r)⁻¹ *
          (1 + ‖v‖) ^ (-(5 : ℝ)) := by gcongr

end QED.ChainProof.SetASpec

end
