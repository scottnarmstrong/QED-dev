/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FacePerm
public import QED.GradedProof.RPi4LightVP

/-!
# Set (a), stage B2: merging a doubled fermion line in closed form

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B2 (undoing the
auxiliary-mass partial fractions of the class densities). The pieces of a class density are
collapsed integrands `pieceF` (`z_γ paramAtV(V(z) + z_γ u)`, photon line `γ`) of line data in
which a fermion line `i` occurs twice, with two masses `a = Mᵢ` and `b`. Merging the two
parameters of the doubled line (`QED.Integration.SimplexMerge.integral_simplex_splitAt`) and
integrating the split parameter in closed form gives the partial fraction
`1/((D + a²)(D + b²)) = (1/(D + b²) - 1/(D + a²))/(a² - b²)` in parametric form:

* `ksB_integral_seg`: `∫₀^z E₁(V₀ + t a + (z - t) b) dt = (E₀(V₀ + z b) - E₀(V₀ + z a))/(a - b)`
  for `E₀' = -E₁` on the positive half line (the fundamental theorem of calculus);
* `ksB_hasDerivAt_ehat_five`: `∂_W Ê₅ = -Ê₆` when the quartic contraction vanishes (the
  general `QED.GradedProof.WI2.hasDerivAt_ehat` starts at `Ê₆`);
* `ksB_pieceF_dbl_splitAt`, `ksB_integral_pieceF_dbl`: the integrand of the doubled data at a
  split point, and its integral over the split parameter;
* **`ksB_merge`**: `∫_{Δₘ₊₁} pieceF(doubled data) = ∫_{Δₘ} (pieceF(Mᵢ ↦ b) - pieceF(M))/(a² - b²)`,
  the right side integrable as a difference (no integrability of the two terms separately is
  claimed: for the five-line data each term alone has a log-divergent fermion subloop);
* `ksB_pieceF_perm`, `ksB_integral_pieceF_perm`: relabelling the lines.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.GradedProof.RPi4
open QED.GradedProof.WI2 (dbl ehat hasDerivAt_ehat hasDerivAt_inv_pow symanzikU_dbl
  symanzikMatrix_dbl loopShift_dbl)
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-! ### The segment integral -/

/-- **The segment integral.** If `E₀' = -E₁` on the positive half line, then for `z ≥ 0`,
`a ≠ b` and `V₀ + z a, V₀ + z b > 0`:
`∫₀^z E₁(V₀ + t a + (z - t) b) dt = (E₀(V₀ + z b) - E₀(V₀ + z a))/(a - b)`. -/
theorem ksB_integral_seg {E₀ E₁ : ℂ → ℂ}
    (hd : ∀ w : ℝ, 0 < w → HasDerivAt E₀ (-E₁ w) (w : ℂ))
    (hc : ∀ w : ℝ, 0 < w → ContinuousAt E₁ (w : ℂ)) {V₀ a b z : ℝ} (hz : 0 ≤ z) (hab : a ≠ b)
    (ha : 0 < V₀ + z * a) (hb : 0 < V₀ + z * b) :
    IntervalIntegrable (fun t : ℝ => E₁ ((V₀ + t * a + (z - t) * b : ℝ) : ℂ)) volume 0 z ∧
    ∫ t in (0 : ℝ)..z, E₁ ((V₀ + t * a + (z - t) * b : ℝ) : ℂ) =
      (E₀ ((V₀ + z * b : ℝ) : ℂ) - E₀ ((V₀ + z * a : ℝ) : ℂ)) / ((a - b : ℝ) : ℂ) := by
  set φ : ℝ → ℝ := fun t => V₀ + t * a + (z - t) * b with hφ
  have hpos : ∀ t ∈ uIcc (0 : ℝ) z, 0 < φ t := by
    intro t ht
    rw [uIcc_of_le hz] at ht
    obtain ⟨h0, h1⟩ := ht
    rcases hz.eq_or_lt with hz0 | hz0
    · subst hz0
      have : t = 0 := le_antisymm h1 h0
      subst this
      simpa [hφ] using ha
    · have key : z * φ t = (z - t) * (V₀ + z * b) + t * (V₀ + z * a) := by
        simp only [hφ]; ring
      have : 0 < z * φ t := by
        rw [key]
        rcases h0.eq_or_lt with ht0 | ht0
        · subst ht0; simp only [sub_zero, zero_mul, add_zero]; positivity
        · have := mul_pos ht0 ha
          have := mul_nonneg (sub_nonneg.2 h1) hb.le
          linarith
      exact pos_of_mul_pos_right this hz0.le
  have hφd : ∀ t, HasDerivAt φ (a - b) t := fun t => by
    have h := ((hasDerivAt_id t).mul_const (a - b)).const_add (V₀ + z * b)
    convert h using 1
    · funext s; simp only [hφ, id]; ring
    · simp
  have hder : ∀ t ∈ uIcc (0 : ℝ) z, HasDerivAt (fun t => E₀ (φ t : ℂ))
      ((a - b) • -E₁ (φ t : ℂ)) t := fun t ht =>
    ((hd (φ t) (hpos t ht)).comp_ofReal).scomp t (hφd t)
  have hcont : ContinuousOn (fun t => E₁ (φ t : ℂ)) (uIcc 0 z) := fun t ht =>
    (ContinuousAt.comp (g := E₁) (f := fun s => (φ s : ℂ)) (hc (φ t) (hpos t ht))
      ((continuous_ofReal.continuousAt).comp (hφd t).continuousAt)).continuousWithinAt
  have hint := hcont.intervalIntegrable (μ := volume)
  refine ⟨hint, ?_⟩
  have hint' : IntervalIntegrable (fun t => (a - b) • -E₁ (φ t : ℂ)) volume 0 z :=
    (hint.neg).smul (a - b)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint'
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_neg] at hF
  have hab' : ((a - b : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (sub_ne_zero.2 hab)
  have e0 : φ 0 = V₀ + z * b := by simp only [hφ]; ring
  have ez : φ z = V₀ + z * a := by simp only [hφ]; ring
  rw [e0, ez] at hF
  rw [eq_div_iff hab', mul_comm]
  have : ((a - b : ℝ) : ℂ) * ∫ t in (0 : ℝ)..z, E₁ (φ t : ℂ) =
      -((a - b) • -∫ t in (0 : ℝ)..z, E₁ (φ t : ℂ)) := by
    rw [real_smul, neg_mul_eq_mul_neg, neg_neg]
  rw [this, hF]
  ring

/-! ### Differentiating the moment functional -/

/-- **`∂_W Ê₅ = -Ê₆`** when the quartic contraction vanishes. -/
theorem ksB_hasDerivAt_ehat_five (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) (hC : P.contractFour A = 0) {W : ℂ} (hW : W ≠ 0) :
    HasDerivAt (fun w => ehat 5 P A X w) (-ehat 6 P A X W) W := by
  have e5 : (fun w => ehat 5 P A X w) = fun w =>
      (w ^ 2)⁻¹ * P.evalC X + 1 / 2 * (w ^ 1)⁻¹ * P.contractTwo A X := by
    funext w
    simp [ehat, hC]
  have e6 : ehat 6 P A X W = 2 * (W ^ 3)⁻¹ * P.evalC X + 1 / 2 * (W ^ 2)⁻¹ * P.contractTwo A X := by
    simp [ehat, hC]
  rw [e5, e6]
  have h := ((hasDerivAt_inv_pow (k := 2) hW).mul_const (P.evalC X)).add
    (((hasDerivAt_inv_pow (k := 1) hW).const_mul (1 / 2 : ℂ)).mul_const (P.contractTwo A X))
  convert h using 1
  ring

theorem ksB_continuousAt_ehat (n : ℕ) (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) {W : ℂ} (hW : W ≠ 0) : ContinuousAt (ehat (n + 6) P A X) W :=
  (hasDerivAt_ehat n P A X hW).continuousAt

/-! ### The integrand of a doubled line at a split point -/

variable {m : ℕ}

/-- `V` with the mass `c` on line `i` is `V` with mass `0` there plus `zᵢ c²`. -/
theorem ksB_symanzikV_update (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)
    (M z : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (c : ℝ) :
    symanzikV α pp (Function.update M i c) z =
      symanzikV α pp (Function.update M i 0) z + z i * c ^ 2 := by
  have h := symanzikV_sub_mass α pp (Function.update M i c) (Function.update M i 0) z
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Function.update_of_ne hj])
    (by simp)] at h
  simp only [Function.update_self] at h
  linarith

theorem ksB_symanzikV_self (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)
    (M z : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    symanzikV α pp M z = symanzikV α pp (Function.update M i 0) z + z i * M i ^ 2 := by
  conv_lhs => rw [← Function.update_eq_self i M]
  exact ksB_symanzikV_update α pp M z i (M i)

/-- **The integrand of the doubled data at a split point.** -/
theorem ksB_pieceF_dbl_splitAt (n : ℕ) (Q : LoopQuartic) {i γ : Fin (m + 1)} (hγ : γ ≠ i)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (b u : ℝ) (z : Fin (m + 1) → ℝ) (t : ℝ) :
    pieceF n Q (dbl i α) (dbl i pp) (Fin.snoc M b) γ.castSucc u (splitAt i z t) =
      (z γ : ℂ) * (((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
        ehat n Q (symanzikMatrix α z) (loopComp (-loopShift α pp z))
          (((symanzikV α pp (Function.update M i 0) z + z γ * u) + t * M i ^ 2 +
            (z i - t) * b ^ 2 : ℝ) : ℂ)) := by
  simp only [pieceF, splitAt_castSucc, Function.update_of_ne hγ, symanzikV_pair, paramAtV,
    symanzikU_dbl, symanzikMatrix_dbl, loopShift_dbl]
  congr 4
  ring

/-- **The split parameter integrated in closed form.** -/
theorem ksB_integral_pieceF_dbl (n : ℕ) (Q : LoopQuartic)
    (hd : ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (w : ℝ), 0 < w →
      HasDerivAt (ehat n Q A X) (-ehat (n + 1) Q A X w) (w : ℂ))
    (hc : ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (w : ℝ), 0 < w →
      ContinuousAt (ehat (n + 1) Q A X) (w : ℂ))
    {i γ : Fin (m + 1)} (hγ : γ ≠ i) (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {b : ℝ} (hab : M i ^ 2 ≠ b ^ 2)
    (u : ℝ) (z : Fin (m + 1) → ℝ) (hz : 0 ≤ z i)
    (hpos : symanzikU α z ≠ 0 → 0 < symanzikV α pp M z + z γ * u ∧
      0 < symanzikV α pp (Function.update M i b) z + z γ * u) :
    IntervalIntegrable (fun t => pieceF (n + 1) Q (dbl i α) (dbl i pp) (Fin.snoc M b)
      γ.castSucc u (splitAt i z t)) volume 0 (z i) ∧
    ∫ t in (0 : ℝ)..z i, pieceF (n + 1) Q (dbl i α) (dbl i pp) (Fin.snoc M b) γ.castSucc u
        (splitAt i z t) =
      (pieceF n Q α pp (Function.update M i b) γ u z - pieceF n Q α pp M γ u z) /
        ((M i ^ 2 - b ^ 2 : ℝ) : ℂ) := by
  simp only [ksB_pieceF_dbl_splitAt (n + 1) Q hγ]
  by_cases hU : symanzikU α z = 0
  · simp [pieceF, paramAtV, hU]
  obtain ⟨ha, hb⟩ := hpos hU
  set V₀ := symanzikV α pp (Function.update M i 0) z + z γ * u with hV₀
  have eA : symanzikV α pp M z + z γ * u = V₀ + z i * M i ^ 2 := by
    rw [hV₀, ksB_symanzikV_self α pp M z i]; ring
  have eB : symanzikV α pp (Function.update M i b) z + z γ * u = V₀ + z i * b ^ 2 := by
    rw [hV₀, ksB_symanzikV_update α pp M z i b]; ring
  rw [eA] at ha
  rw [eB] at hb
  obtain ⟨h1, h2⟩ := ksB_integral_seg (hd (symanzikMatrix α z) (loopComp (-loopShift α pp z)))
    (hc (symanzikMatrix α z) (loopComp (-loopShift α pp z))) hz hab ha hb
  refine ⟨(h1.const_mul _).const_mul _, ?_⟩
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h2]
  simp only [pieceF, paramAtV]
  rw [eA, eB]
  ring

/-! ### Merging the doubled line on the simplex -/

section Merge

variable {ι : Type*} (s : Finset ι) (n : ℕ) (Q : ι → LoopQuartic) {i γ : Fin (m + 1)}
  (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (w : ι → ℂ)
  (M : ι → Fin (m + 1) → ℝ) (b : ι → ℝ) (u : ℝ)

/-- **Merging a doubled fermion line** in a finite combination of collapsed integrands that
share the line data (line `i` doubled, photon line `γ ≠ i`): term `r` has numerator `Q r`,
masses `M r` with `aᵣ = (M r)ᵢ` on line `i` and `bᵣ` on the appended copy, `aᵣ² ≠ bᵣ²`. For an
integrable combination with `V > 0` at both masses of each term:
`∫_{Δₘ₊₁} ∑ᵣ wᵣ pieceF_r = ∫_{Δₘ} ∑ᵣ wᵣ (pieceF_r(Mᵢ ↦ bᵣ) - pieceF_r)/(aᵣ² - bᵣ²)`, and the right
integrand is integrable (as a whole: the terms need not be). -/
theorem ksB_merge (hm : 0 < m)
    (hd : ∀ r ∈ s, ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (w : ℝ), 0 < w →
      HasDerivAt (ehat n (Q r) A X) (-ehat (n + 1) (Q r) A X w) (w : ℂ))
    (hc : ∀ r ∈ s, ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (w : ℝ), 0 < w →
      ContinuousAt (ehat (n + 1) (Q r) A X) (w : ℂ))
    (hγ : γ ≠ i) (hab : ∀ r ∈ s, M r i ^ 2 ≠ b r ^ 2)
    (hI : IntegrableOn (fun x => ∑ r ∈ s, w r * pieceF (n + 1) (Q r) (dbl i α) (dbl i pp)
      (Fin.snoc (M r) (b r)) γ.castSucc u (simplexPoint x)) (simplexSet (m + 1)))
    (hpos : ∀ r ∈ s, ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      0 < symanzikV α pp (M r) (simplexPoint y) + simplexPoint y γ * u ∧
      0 < symanzikV α pp (Function.update (M r) i (b r)) (simplexPoint y) +
        simplexPoint y γ * u) :
    IntegrableOn (fun y => ∑ r ∈ s, w r *
      ((pieceF n (Q r) α pp (Function.update (M r) i (b r)) γ u (simplexPoint y) -
        pieceF n (Q r) α pp (M r) γ u (simplexPoint y)) / ((M r i ^ 2 - b r ^ 2 : ℝ) : ℂ)))
      (simplexSet m) ∧
    ∫ x in simplexSet (m + 1), ∑ r ∈ s, w r * pieceF (n + 1) (Q r) (dbl i α) (dbl i pp)
        (Fin.snoc (M r) (b r)) γ.castSucc u (simplexPoint x) =
      ∫ y in simplexSet m, ∑ r ∈ s, w r *
        ((pieceF n (Q r) α pp (Function.update (M r) i (b r)) γ u (simplexPoint y) -
          pieceF n (Q r) α pp (M r) γ u (simplexPoint y)) / ((M r i ^ 2 - b r ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := integral_simplex_splitAt hm i
    (f := fun z' => ∑ r ∈ s, w r * pieceF (n + 1) (Q r) (dbl i α) (dbl i pp)
      (Fin.snoc (M r) (b r)) γ.castSucc u z') hI
  have hEq : EqOn (fun y => ∫ t in (0 : ℝ)..simplexPoint y i, ∑ r ∈ s, w r *
      pieceF (n + 1) (Q r) (dbl i α) (dbl i pp) (Fin.snoc (M r) (b r)) γ.castSucc u
        (splitAt i (simplexPoint y) t))
      (fun y => ∑ r ∈ s, w r *
        ((pieceF n (Q r) α pp (Function.update (M r) i (b r)) γ u (simplexPoint y) -
          pieceF n (Q r) α pp (M r) γ u (simplexPoint y)) / ((M r i ^ 2 - b r ^ 2 : ℝ) : ℂ)))
      (simplexSet m) := fun y hy => by
    have hr := fun r (hr : r ∈ s) => ksB_integral_pieceF_dbl n (Q r) (hd r hr) (hc r hr) hγ α
      pp (M r) (hab r hr) u (simplexPoint y) ((simplexPoint_mem_stdSimplex hy).1 i)
      (hpos r hr y hy)
    simp only
    rw [intervalIntegral.integral_finsetSum fun r hr' => (hr r hr').1.const_mul (w r)]
    refine Finset.sum_congr rfl fun r hr' => ?_
    rw [intervalIntegral.integral_const_mul, (hr r hr').2]
  exact ⟨h1.congr_fun hEq (measurableSet_simplexSet m),
    h2.trans (setIntegral_congr_fun (measurableSet_simplexSet m) hEq)⟩

end Merge

/-! ### Relabelling the lines -/

/-- **Relabelling the lines of a collapsed integrand.** -/
theorem ksB_pieceF_perm (e : Equiv.Perm (Fin (m + 1))) (n : ℕ) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) :
    pieceF n Q (fun l => α (e l)) (fun l => pp (e l)) (fun l => M (e l)) γ u z =
      pieceF n Q α pp M (e γ) u (fun j => z (e.symm j)) := by
  simp only [pieceF, paramAtV_perm, symanzikV_perm, Equiv.symm_apply_apply]

/-- **Relabelling the lines of a finite combination of collapsed integrands under the simplex
integral.** -/
theorem ksB_integral_pieceF_perm {ι : Type*} (s : Finset ι) (e : Equiv.Perm (Fin (m + 1)))
    (n : ℕ) (Q : ι → LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)
    (w : ι → ℂ) (M : ι → Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ) :
    (IntegrableOn (fun x => ∑ r ∈ s, w r * pieceF n (Q r) (fun l => α (e l))
      (fun l => pp (e l)) (fun l => M r (e l)) γ u (simplexPoint x)) (simplexSet m) ↔
      IntegrableOn (fun x => ∑ r ∈ s, w r * pieceF n (Q r) α pp (M r) (e γ) u (simplexPoint x))
        (simplexSet m)) ∧
    ∫ x in simplexSet m, ∑ r ∈ s, w r * pieceF n (Q r) (fun l => α (e l)) (fun l => pp (e l))
        (fun l => M r (e l)) γ u (simplexPoint x) =
      ∫ x in simplexSet m, ∑ r ∈ s, w r * pieceF n (Q r) α pp (M r) (e γ) u (simplexPoint x) := by
  have h : ∀ z : Fin (m + 1) → ℝ, (∑ r ∈ s, w r * pieceF n (Q r) (fun l => α (e l))
      (fun l => pp (e l)) (fun l => M r (e l)) γ u z) =
      (fun z' => ∑ r ∈ s, w r * pieceF n (Q r) α pp (M r) (e γ) u z') (z ∘ e.symm) :=
    fun z => by simp only [ksB_pieceF_perm]; rfl
  simp only [h]
  exact ⟨integrableOn_simplex_comp_perm_iff e.symm
      (fun z' => ∑ r ∈ s, w r * pieceF n (Q r) α pp (M r) (e γ) u z'),
    integral_simplex_comp_perm e.symm
      (fun z' => ∑ r ∈ s, w r * pieceF n (Q r) α pp (M r) (e γ) u z')⟩

end QED.ChainProof.SetAKS

end
