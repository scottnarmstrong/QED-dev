/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMDisp

/-!
# Multi-denominator units: the `q → 0` bound uniform in one heavy photon mass

Helper level for set (c) (stage L2). `QED.ChainProof.SetCUnitM.norm_unitMPauliZero_le` bounds the
`q → 0` value of a unit by `C (1 + ∑ᵢ Mᵢ²)²`: it bounds `|V|` at the interpolation nodes by one
constant `K` and `V` from below by one constant `c`. Both are lossy for one heavy line: `V` is
affine in the squared masses, `V = V₀ + zₕ (t² - μ²)` (`symanzikV_sub`), so at each Feynman point
`|V| ≤ K₀ + zₕ δ` and `V ≥ c + zₕ δ`, `δ = t² - μ²`, and the numerator growth `(1 + |V|)²` is
absorbed by `V²` pointwise. This gives a bound uniform in the heavy mass.

* **`norm_evenQuot_le_of`**: the even quotient bounded by `∫ G / (3/4)ᵃ` for any integrable `G`
  with `lagConst D ∑ₖ ‖A(x, node k)‖ ≤ G(x) V(x, u)ᴺ` (a pointwise form of
  `QED.ChainProof.SetCUnitM.norm_evenQuot_le`);
* `pieceA`, `norm_pieceA_le`: the interpolated numerator of a piece and its node bound;
* **`norm_evenQuot_piece_le_var`**: the piece bound with pointwise `K(x)`, `c(x)`,
  `(1 + K)² ≤ L c²`: `L · pieceConst / ((3/4)ᵃ cᴺ⁻²)`;
* `symanzikV_sub`: `V(M) - V(M') = ∑ᵢ zᵢ (Mᵢ² - M'ᵢ²)`;
* **`norm_unitMPauliQuot_slot_le`**, **`norm_unitMPauliZero_slot_le`**,
  **`norm_unitMPauliZeroPow_slot_le`**: with the mass of the element line `s` replaced by any
  `t ≥ μ_s`, the bounds `C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²` hold with the light masses `Mᵢ`, uniformly in `t`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Integration.TwoLoop (LoopQuartic RefinedBound symanzikV)
open QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.PauliZeroExplicit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The even quotient with a pointwise majorant -/

section Bound

variable {ι : Type*} {D : ℕ} {A : ι → ℝ → ℂ}
variable [MeasurableSpace ι] {μ : Measure ι} {a N : ℕ} {V : ι → ℝ → ℝ} {c : ℝ}
  {f : ℝ → ι → ℂ}

/-- **The even quotient with a pointwise majorant**: for `0 < |u| ≤ 1/2`, under the hypotheses of
`tendsto_even_div_sq`, `‖(∫ f(u) + ∫ f(-u))/(2u²)‖ ≤ ∫ G / (3/4)ᵃ` for every integrable `G` with
`lagConst D ∑ₖ ‖A(x, node k)‖ ≤ G(x) V(x, u)ᴺ`. -/
theorem norm_evenQuot_le_of (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hA0 : ∀ᵐ x ∂μ, A x 0 = 0)
    (hc : 0 < c) (hV : ∀ᵐ x ∂μ, ∀ u ∈ Ioo (-1 : ℝ) 1, c ≤ V x u)
    (hVeven : ∀ᵐ x ∂μ, ∀ u, V x (-u) = V x u) (hVcont : ∀ᵐ x ∂μ, ContinuousAt (V x) 0)
    (hVmeas : ∀ u, AEStronglyMeasurable (fun x => V x u) μ)
    (hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂μ, f u x = A x u / (wt u ^ a * (V x u : ℂ) ^ N))
    {u : ℝ} (hu0 : u ≠ 0) (hu : |u| ≤ 1 / 2) {G : ι → ℝ} (hG : Integrable G μ)
    (hGb : ∀ᵐ x ∂μ, lagConst D * ∑ k : Fin (D + 1), ‖A x (node D k)‖ ≤ G x * V x u ^ N) :
    ‖((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2)‖ ≤
      (∫ x, G x ∂μ) / (3 / 4 : ℝ) ^ a := by
  have hfi := (tendsto_even_div_sq hA hAi hA0 hc hV hVeven hVcont hVmeas hf).1
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
  have hAeq : ∀ x, ∀ v ∈ Ioo (-1 : ℝ) 1,
      A x v = ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (v : ℂ) ^ j := fun x v hv => by
    rw [hA.eq_interp x v hv, eval_interp_eq_sum]
  set B : ι → ℂ := fun x =>
    ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * evenCoeff j u with hB
  have h0 : ∀ᵐ x ∂μ, (interp D A x).coeff 0 = 0 := by
    filter_upwards [hA0] with x hx
    have := hA.eq_interp x 0 ⟨by norm_num, by norm_num⟩
    rw [hx, ofReal_zero, ← coeff_zero_eq_eval_zero] at this
    exact this.symm
  have hsym : ((∫ x, f u x ∂μ) + ∫ x, f (-u) x ∂μ) / (2 * (u : ℂ) ^ 2) =
      ∫ x, B x / (wt u ^ a * (V x u : ℂ) ^ N) ∂μ := by
    rw [← integral_add (hfi u hu1) (hfi (-u) hu'), div_eq_mul_inv, mul_comm,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hf u hu1, hf (-u) hu', hVeven, h0] with x hx hx' hev hx0
    rw [hx, hx', hev, wt_neg]
    have hsum : A x u + A x (-u) = 2 * (u : ℂ) ^ 2 * B x := by
      rw [hAeq x u hu1, hAeq x (-u) hu', ← Finset.sum_add_distrib]
      simp only [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_add, pow_add_neg_pow]
      split_ifs with hj
      · subst hj
        rw [hx0]
        ring
      · ring
    have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hu0)
    have h2u : (2 * (u : ℂ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hu2
    rw [← add_div, hsum, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ h2u, one_mul]
  rw [hsym, ← integral_div]
  refine norm_integral_le_of_norm_le (hG.div_const _) ?_
  filter_upwards [hV, hGb] with x hx hgx
  have hcx := hx u hu1
  have hVp : 0 < V x u := hc.trans_le hcx
  have hBn : ‖B x‖ ≤ G x * V x u ^ N := by
    refine le_trans ?_ ((sum_norm_interp_coeff_le x).trans hgx)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_evenCoeff_le j (hu.trans (by norm_num)))
  have hw := norm_wt_ge hu
  have hVN : 0 < V x u ^ N := pow_pos hVp N
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hVp]
  calc ‖B x‖ / (‖wt u‖ ^ a * V x u ^ N)
      ≤ G x * V x u ^ N / ((3 / 4 : ℝ) ^ a * V x u ^ N) :=
        div_le_div₀ ((norm_nonneg _).trans hBn) hBn (by positivity)
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hw a) hVN.le)
    _ = G x / (3 / 4 : ℝ) ^ a := by
        rw [mul_div_mul_right _ _ hVN.ne']

end Bound

/-! ### The piece bound with pointwise constants -/

section Generic

/-- The interpolated numerator `A(x, u)` of a piece (as in
`QED.ChainProof.SetCUnitM.norm_evenQuot_piece_le`). -/
noncomputable def pieceA {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {J : Type*} [Fintype J]
    (D n r : ℕ) (Qk : J → Fin (D + 1) → LoopQuartic) (ω : ℝ → J → ℂ) (x : Fin m → ℝ) (u : ℝ) :
    ℂ :=
  ∑ j, (wt u ^ r * ω u j) * (-((π : ℂ) ^ 4) *
    ∑ k, (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)) *
      (wt u ^ 4 * paramNum (Qk j k) α (mom u) M x))

/-- **The node bound of a piece**: with `|V(x, w)| ≤ K`,
`‖A(x, w)‖ ≤ pieceDom(w, x) (1 + K)²`. -/
theorem norm_pieceA_le {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {J : Type*} [Fintype J]
    (D n r : ℕ) (Qk : J → Fin (D + 1) → LoopQuartic) (ω : ℝ → J → ℂ) (x : Fin m → ℝ) (w : ℝ)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : |symanzikV α (mom w) M (simplexPoint x)| ≤ K) :
    ‖pieceA α mom M D n r Qk ω x w‖ ≤ pieceDom α mom D n r Qk ω w x * (1 + K) ^ 2 := by
  have hP : ∀ j k, ‖paramNum (Qk j k) α (mom w) M x‖ ≤
      (‖coeffOne (Qk j k) α (mom w) x‖ + ‖coeffTwo (Qk j k) α (mom w) x‖ +
        ‖coeffThree (Qk j k) α x‖) * (1 + K) ^ 2 := fun j k =>
    norm_paramNum_le (Qk j k) α (mom w) M x hK0 hK
  simp only [pieceA, pieceDom, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul (wt w ^ r * ω w j), norm_mul (-((π : ℂ) ^ 4)), norm_neg, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hsum : ‖∑ k, wt (node D k) ^ n * (lbasis D k).eval (w : ℂ) *
      (wt w ^ 4 * paramNum (Qk j k) α (mom w) M x)‖ ≤
      ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ * (‖wt w ^ 4‖ *
        ((‖coeffOne (Qk j k) α (mom w) x‖ + ‖coeffTwo (Qk j k) α (mom w) x‖ +
          ‖coeffThree (Qk j k) α x‖) * (1 + K) ^ 2)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul (wt w ^ 4)]
    gcongr
    exact hP j k
  have e : ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ * (‖wt w ^ 4‖ *
        ((‖coeffOne (Qk j k) α (mom w) x‖ + ‖coeffTwo (Qk j k) α (mom w) x‖ +
          ‖coeffThree (Qk j k) α x‖) * (1 + K) ^ 2)) =
      (∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ * (‖wt w ^ 4‖ *
        (‖coeffOne (Qk j k) α (mom w) x‖ + ‖coeffTwo (Qk j k) α (mom w) x‖ +
          ‖coeffThree (Qk j k) α x‖))) * (1 + K) ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc _ ≤ ‖wt w ^ r * ω w j‖ * (π ^ 4 * ∑ k, ‖wt (node D k) ^ n * (lbasis D k).eval (w : ℂ)‖ *
        (‖wt w ^ 4‖ * ((‖coeffOne (Qk j k) α (mom w) x‖ +
          ‖coeffTwo (Qk j k) α (mom w) x‖ + ‖coeffThree (Qk j k) α x‖) * (1 + K) ^ 2))) := by
        gcongr
    _ = _ := by rw [e]; ring

variable (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}

/-- **The even quotient of a piece with pointwise constants.** If at almost every Feynman point
`x` the node values satisfy `|V(x, node)| ≤ K(x)` and `c ≤ c(x) ≤ V(x, u)` for all `u`, with
`(1 + K(x))² ≤ L c(x)²`, then for `0 < |u| ≤ 1/2`
`‖(S(u) + S(-u))/(2u²)‖ ≤ L · pieceConst / ((3/4)ᵃ cᵐ⁻⁵)`. -/
theorem norm_evenQuot_piece_le_var (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (Qk : J → Fin (D + 1) → LoopQuartic) (hQk : ∀ j k, (Qk j k).eval = F (node D k) j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (v : ℝ → J → ℂ)
    (hv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu) (F u j) (v u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) {K cx : (Fin C.m → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L)
    (hK : ∀ t : Fin (Dω + (D + 8) + 1), ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      0 ≤ K x ∧ |C.vfun x (node (Dω + (D + 8)) t)| ≤ K x)
    (hcx : ∀ᵐ x ∂(volume.restrict (simplexSet C.m)), C.c ≤ cx x ∧
      (∀ u ∈ Ioo (-1 : ℝ) 1, cx x ≤ C.vfun x u) ∧ (1 + K x) ^ 2 ≤ L * cx x ^ 2)
    {u : ℝ} (hu0 : u ≠ 0) (hu : |u| ≤ 1 / 2) :
    ‖((∑ j, ω u j * v u j) + ∑ j, ω (-u) j * v (-u) j) / (2 * (u : ℂ) ^ 2)‖ ≤
      L * pieceConst C.α C.mom D n r Dω Qk ω /
        ((3 / 4 : ℝ) ^ (r + n + 4) * C.c ^ (C.m - 5)) := by
  have hnode : ∀ k : Fin (D + 1), node D k ∈ Ioo (-1 : ℝ) 1 := node_mem D
  have hBk : ∀ j k, RefinedBound C.α C.E 4 (Qk j k).eval := fun j k => by
    rw [hQk]
    exact hFB _ (hnode k) j
  set f : ℝ → (Fin C.m → ℝ) → ℂ := fun u x => ∑ j, ω u j * (-((π : ℂ) ^ 4) *
    ∑ k, lam D n u k * paramIntegrand (Qk j k) C.α (C.mom u) C.M 0 x) with hf_def
  set A : (Fin C.m → ℝ) → ℝ → ℂ := pieceA C.α C.mom C.M D n r Qk ω with hA_def
  have hA : IsUPoly (Dω + (D + 8)) A :=
    IsUPoly.sum _ fun j _ => (hω j).mul (IsUPoly.const_mul _ (IsUPoly.sum _ fun k _ =>
      ((isUPoly_lbasis D k).const_mul _).mul (isUPoly_paramNum (Qk j k) C.α C.M C.mom C.hmom)))
  have hAi : ∀ t, Integrable (fun x => A x (node (Dω + (D + 8)) t))
      (volume.restrict (simplexSet C.m)) := fun t => by
    refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum (Qk j k) C.α _ C.M C.hm C.hcrit (hBk j k)).const_mul _
  have hA0 : ∀ x, A x 0 = 0 := fun x => by
    simp only [hA_def, pieceA, wt_zero, one_pow, one_mul]
    exact hω0 _
  have hf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      f u x = A x u / (wt u ^ (r + n + 4) * ((C.vfun x u : ℝ) : ℂ) ^ (C.m - 3)) := by
    intro u hu
    filter_upwards [C.ae_le_vfun] with x hx
    have hV0 : C.vfun x u ≠ 0 := (C.hc.trans_le (hx u hu)).ne'
    have hV0' : ((C.vfun x u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV0
    have hw := wt_ne_zero hu
    simp only [hf_def, hA_def, pieceA, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk j k) C.α (C.mom u) C.M (by have := C.hm; omega) hV0]
    simp only [lam, CurveData.vfun] at hV0' ⊢
    field_simp
    ring
  have hS : ∀ u ∈ Ioo (-1 : ℝ) 1, ∑ j, ω u j * v u j = ∫ x in simplexSet C.m, f u x := by
    intro u hu
    have hI : ∀ j k, IntegrableOn (paramIntegrand (Qk j k) C.α (C.mom u) C.M 0)
        (simplexSet C.m) := fun j k =>
      integrableOn_paramIntegrand_zero (Qk j k) C.α (C.mom u) C.M C.hm C.hcrit (hBk j k) C.hc
        (C.hV u hu)
    have hvj : ∀ j, v u j = -((π : ℂ) ^ 4) * ∫ x in simplexSet C.m,
        ∑ k, lam D n u k * paramIntegrand (Qk j k) C.α (C.mom u) C.M 0 x := fun j => by
      have h' : IsParamValue (C.toParamData hu) (F u j) (-((π : ℂ) ^ 4) *
          ∫ x in simplexSet C.m,
            paramIntegrand (jointQuartic D n (Qk j) u) C.α (C.mom u) C.M 0 x) :=
        ⟨jointQuartic D n (Qk j) u, eval_jointQuartic (hFpoly j) (hQk j) hu, hFB u hu j, rfl⟩
      rw [(hv u hu j).unique h', jointQuartic]
      simp only [paramIntegrand_qsum]
    simp only [hvj, hf_def]
    rw [integral_finsetSum _ fun j _ => (((integrable_finsetSum _ fun k _ =>
      (hI j k).const_mul _).const_mul _).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul]
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
  rw [hS u hu1, hS (-u) hu']
  set Dt := Dω + (D + 8)
  set P : (Fin C.m → ℝ) → ℝ := fun x => lagConst Dt * ∑ t : Fin (Dt + 1),
    pieceDom C.α C.mom D n r Qk ω (node Dt t) x with hP
  have hPi : Integrable P (volume.restrict (simplexSet C.m)) :=
    (integrable_finsetSum _ fun t _ => integrableOn_pieceDom C Qk hBk ω _).const_mul _
  have hP0 : ∀ x, 0 ≤ P x := fun x => mul_nonneg (lagConst_nonneg _)
    (Finset.sum_nonneg fun t _ => by unfold pieceDom; positivity)
  have hc0 := C.hc
  have hm5 : C.m - 3 = 2 + (C.m - 5) := by have := C.hm; omega
  refine (norm_evenQuot_le_of (μ := volume.restrict (simplexSet C.m)) hA hAi
    (ae_of_all _ hA0) C.hc C.ae_le_vfun (ae_of_all _ fun x u => C.hVeven u _)
    (ae_of_all _ C.continuousAt_vfun) (fun u => (C.measurable_vfun u).aestronglyMeasurable) hf
    hu0 hu (G := fun x => L / C.c ^ (C.m - 5) * P x) (hPi.const_mul _) ?_).trans (le_of_eq ?_)
  · filter_upwards [hcx, ae_all_iff.2 hK] with x ⟨hc1, hc2, hc3⟩ hKx
    have hVu := hc2 u hu1
    have hcx0 : 0 < cx x := hc0.trans_le hc1
    have hnode : ∑ t : Fin (Dt + 1), ‖A x (node Dt t)‖ ≤
        (∑ t : Fin (Dt + 1), pieceDom C.α C.mom D n r Qk ω (node Dt t) x) * (L * cx x ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun t _ => ?_
      refine (norm_pieceA_le C.α C.mom C.M D n r Qk ω x _ (hKx t).1 (hKx t).2).trans ?_
      exact mul_le_mul_of_nonneg_left hc3 (by unfold pieceDom; positivity)
    have hVN : cx x ^ 2 * C.c ^ (C.m - 5) ≤ C.vfun x u ^ (C.m - 3) := by
      rw [hm5, pow_add]
      exact mul_le_mul (pow_le_pow_left₀ hcx0.le hVu 2)
        (pow_le_pow_left₀ hc0.le (hc1.trans hVu) _) (by positivity) (by positivity)
    have hcm : 0 < C.c ^ (C.m - 5) := by positivity
    calc lagConst Dt * ∑ t : Fin (Dt + 1), ‖A x (node Dt t)‖
        ≤ L / C.c ^ (C.m - 5) * P x * (cx x ^ 2 * C.c ^ (C.m - 5)) := by
          rw [hP]
          field_simp
          have := mul_le_mul_of_nonneg_left hnode (lagConst_nonneg Dt)
          nlinarith [this]
      _ ≤ L / C.c ^ (C.m - 5) * P x * C.vfun x u ^ (C.m - 3) :=
          mul_le_mul_of_nonneg_left hVN (mul_nonneg (div_nonneg hL0 hcm.le) (hP0 x))
  · rw [integral_const_mul, hP, integral_const_mul, integral_finsetSum _ fun t _ =>
      integrableOn_pieceDom C Qk hBk ω _]
    unfold pieceConst
    field_simp
    rfl

end Generic

/-! ### One heavy photon mass -/

/-- **`V` is affine in the squared masses**: `V(M) - V(M') = ∑ᵢ zᵢ (Mᵢ² - M'ᵢ²)`. -/
theorem symanzikV_sub {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M M' : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikV α p M z - symanzikV α p M' z = ∑ i, z i * (M i ^ 2 - M' i ^ 2) := by
  simp only [symanzikV, mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

section Unit

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero QED.ChainProof.SetCUnit

variable {r : ℕ}

theorem le_unitMasses {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ m a A b B : ℝ}
    (hM : MassesGe μ₀ a A b B) : μ₀ ≤ unitMasses m a A b B s := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  revert hs
  fin_cases s <;> simp [unitMasses, QED.Integration.TwoLoop.classPVMasses] <;> assumption

/-- The heavy masses differ from the light ones only on the element line `s`:
`V(heavy) = V(light) + z_s (t² - μ_s²)`. -/
theorem symanzikV_unitM_slot {s : Fin 8} (hs : 4 ≤ (s : ℕ)) (α : Fin (r + 8) → Fin 2 → ℝ)
    (q : Fin (r + 8) → Fin 4 → ℝ) (m a A b B t : ℝ) (cs : Fin r → ℝ) (z : Fin (r + 8) → ℝ) :
    symanzikV α q (unitMMasses m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs)
        z =
      symanzikV α q (unitMMasses m a A b B cs) z +
        z (mEmb r s) * (t ^ 2 - unitMasses m a A b B s ^ 2) := by
  rw [← sub_eq_iff_eq_add', symanzikV_sub, Finset.sum_eq_single (mEmb r s)]
  · simp only [unitMMasses_mEmb, unitMasses_slot hs, ite_true]
  · intro i _ hi
    rw [unitMMasses_slot hs m a A b B t cs i hi, sub_self, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The `q → 0` even quotient with a heavy element line, bounded uniformly in its mass**
(`n = 0`, the scales fixed): one constant `C` with
`‖(S(u) + S(-u))/(2u²)‖ ≤ C (1 + ∑ᵢ Mᵢ²)²` for `0 < |u| ≤ 1/2`, where the unit has the mass of
line `s` replaced by any `t ≥ μ_s` and `Mᵢ` are the masses before the replacement. -/
theorem norm_unitMPauliQuot_slot_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ : Fin r → ℝ}
    (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) :
    ∃ C : ℝ, ∀ (a A b B t : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      unitMasses P.m a A b B s ≤ t → ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 →
        ‖(unitMPauliS c P s κ (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b)
              (slotMB s t B) cs) 0 u +
            unitMPauliS c P s κ (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b)
              (slotMB s t B) cs) 0 (-u)) / (2 * (u : ℂ) ^ 2)‖ ≤
          C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ 2 := by
  set Km := unitMMomK c P s κ with hKm
  have hKm0 : 0 ≤ Km := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  set c₀ := unitConst P.m μ₀
  have hc0 : 0 < c₀ := unitConst_pos hm hμ₀
  refine ⟨unitMPauliConst hc P s κ * ((1 + Km + c₀) / c₀) ^ 2 /
    ((3 / 4 : ℝ) ^ (4 + 4 + 4) * c₀ ^ (r + 7 - 5)),
    fun a A b B t cs hM hcs ht u hu0 hu => ?_⟩
  have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
  have hμs := le_unitMasses (m := P.m) hs hM
  have hM' := massesGe_slot (s := s) hM (hμs.trans ht)
  set Cd := unitMCurve hc P hm hs hμ₀ hM' hX with hCd
  set Cd₀ := unitMCurve hc P hm hs hμ₀ hM hX with hCd₀
  set μs := unitMasses P.m a A b B s
  set δ := t ^ 2 - μs ^ 2 with hδ
  have hδ0 : 0 ≤ δ := by
    have := hμ₀.trans_le hμs
    rw [hδ]; nlinarith
  set S := ∑ i, unitMMasses P.m a A b B cs i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set K₀ : ℝ := S + Km with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set z : (Fin Cd.m → ℝ) → ℝ := fun x => simplexPoint x (mEmb r s) with hz
  have hVs : ∀ (x : Fin (r + 7) → ℝ) u, symanzikV (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u))
      (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs)
      (simplexPoint x) = symanzikV (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u))
      (unitMMasses P.m a A b B cs) (simplexPoint x) + simplexPoint x (mEmb r s) * δ :=
    fun x u => symanzikV_unitM_slot hs _ _ P.m a A b B t cs _
  have hV₁ : ∀ (x : Fin Cd.m → ℝ) u, Cd.vfun x u = symanzikV (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u))
      (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs)
      (simplexPoint x) := fun x u => rfl
  have hV₀ : ∀ (x : Fin Cd.m → ℝ) u, Cd₀.vfun x u = symanzikV (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u))
      (unitMMasses P.m a A b B cs) (simplexPoint x) := fun x u => rfl
  have hV : ∀ (x : Fin Cd.m → ℝ) u, Cd.vfun x u = Cd₀.vfun x u + z x * δ := fun x u => by
    rw [hV₁, hV₀]
    exact hVs x u
  have hz0 : ∀ᵐ x ∂(volume.restrict (simplexSet Cd.m)), 0 ≤ z x := by
    filter_upwards [ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet _)]
      with x hx
    exact (QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx).1 _
  set L : ℝ := ((1 + K₀) / c₀ + 1) ^ 2 with hL
  have hKb : ∀ t' : Fin (8 + (8 + 8) + 1), ∀ᵐ x ∂(volume.restrict (simplexSet Cd.m)),
      0 ≤ K₀ + z x * δ ∧ |Cd.vfun x (node (8 + (8 + 8)) t')| ≤ K₀ + z x * δ := fun t' => by
    filter_upwards [ae_abs_symanzikV_le (α := Cd₀.α) (p := Cd₀.mom (node (8 + (8 + 8)) t'))
      (M := Cd₀.M) (by have := Cd₀.hm; omega) Cd₀.hspan, hz0] with x hx hzx
    have hzδ : 0 ≤ z x * δ := mul_nonneg hzx hδ0
    refine ⟨by positivity, ?_⟩
    rw [hV]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hzδ]
    refine add_le_add ((show |Cd₀.vfun x (node (8 + (8 + 8)) t')| ≤ _ from hx).trans ?_) le_rfl
    have h1 : ∑ i, ∑ μ, Cd₀.mom (node (8 + (8 + 8)) t') i μ ^ 2 ≤ Km :=
      Finset.single_le_sum (f := fun t : Fin (8 + (8 + 8) + 1) => ∑ i, ∑ μ,
        unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m (node (8 + (8 + 8)) t)) i μ ^ 2)
        (fun t _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.mem_univ t')
    rw [Finset.sum_add_distrib]
    have h2 : ∑ i, Cd₀.M i ^ 2 = S := rfl
    linarith
  have hcx : ∀ᵐ x ∂(volume.restrict (simplexSet Cd.m)), Cd.c ≤ c₀ + z x * δ ∧
      (∀ u ∈ Ioo (-1 : ℝ) 1, c₀ + z x * δ ≤ Cd.vfun x u) ∧
      (1 + (K₀ + z x * δ)) ^ 2 ≤ L * (c₀ + z x * δ) ^ 2 := by
    filter_upwards [Cd₀.ae_le_vfun, hz0] with x hx hzx
    have hzδ : 0 ≤ z x * δ := mul_nonneg hzx hδ0
    refine ⟨le_add_of_nonneg_right hzδ, fun u hu => ?_, ?_⟩
    · rw [hV]
      exact add_le_add (hx u hu) le_rfl
    · rw [hL, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      have e : ((1 + K₀) / c₀ + 1) * (c₀ + z x * δ) =
          (1 + K₀) + (1 + K₀) / c₀ * (z x * δ) + c₀ + z x * δ := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ (1 + K₀) / c₀ * (z x * δ) := by positivity
      linarith
  have h := norm_evenQuot_piece_le_var Cd (J := Idx) (D := 8) (n := 4) (r := 4) (Dω := 8)
    (unitMPauliF c P)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [unitMPauliF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (unitMQk hc P)
    (fun j k => Classical.choose_spec (exists_quartic_unitMPauliF hc P (node 8 k) j))
    (fun u _ j => by
      rw [unitMPauliF_eq]
      exact refinedBound_unitM hc P s κ _ _ _ _ _)
    (fun u j => unitMLimitV c P s κ (unitMMasses P.m (slotMa s t a) (slotMA s t A)
      (slotMb s t b) (slotMB s t B) cs) (restMomentum P.m) (curveMomentum P.m u) 0 j.1 j.2.1 j.2.2)
    (fun u hu j => by
      obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_unitMLimitV hc P hm hs hμ₀ hM'
        (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) hX j.1 j.2.1 j.2.2
      refine ⟨Q, hQ, ?_, hv⟩
      rw [unitMPauliF_eq]
      exact refinedBound_unitM hc P s κ _ _ _ _ _)
    (unitMPauliW P) (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
    (K := fun x => K₀ + z x * δ) (cx := fun x => c₀ + z x * δ) (by positivity) hKb hcx hu0 hu
  set M₁ := unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs
  have eS : ∀ u, unitMPauliS c P s κ M₁ 0 u =
      ∑ j : Idx, unitMPauliW P u j * unitMLimitV c P s κ M₁
        (restMomentum P.m) (curveMomentum P.m u) 0 j.1 j.2.1 j.2.2 := fun u => by
    simp only [unitMPauliS, pauliNum_eq_sum_idx, unitMPauliW]
  rw [eS u, eS (-u)]
  refine h.trans ?_
  have hpc := pieceConst_nonneg (unitMMatrix c s κ)
    (fun u => unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u)) 8 4 4 8
    (unitMQk hc P) (unitMPauliW P)
  have hLb : L ≤ ((1 + Km + c₀) / c₀) ^ 2 * (1 + S) ^ 2 := by
    rw [hL, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [div_add_one hc0.ne', div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hc0.le
    rw [hK₀]
    nlinarith
  have hden : 0 < (3 / 4 : ℝ) ^ (4 + 4 + 4) * c₀ ^ (r + 7 - 5) := by positivity
  change L * unitMPauliConst hc P s κ / ((3 / 4 : ℝ) ^ (4 + 4 + 4) * c₀ ^ (r + 7 - 5)) ≤ _
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden, mul_comm L, mul_assoc]
  exact mul_le_mul_of_nonneg_left hLb hpc

/-- **The `q → 0` value with a heavy element line, bounded uniformly in its mass** (`n = 0`):
`‖unitMPauliZero‖ ≤ C (1 + ∑ᵢ Mᵢ²)²` with the masses `Mᵢ` before the replacement. -/
theorem norm_unitMPauliZero_slot_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ : Fin r → ℝ}
    (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) :
    ∃ C : ℝ, ∀ (a A b B t : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      unitMasses P.m a A b B s ≤ t →
        ‖unitMPauliZero c P s κ (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b)
            (slotMB s t B) cs)‖ ≤ C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ 2 := by
  obtain ⟨C, hC⟩ := norm_unitMPauliQuot_slot_le hc P hm hs hμ₀ hκ
  refine ⟨C, fun a A b B t cs hM hcs ht => ?_⟩
  have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
  have hM' := massesGe_slot (s := s) hM ((le_unitMasses (m := P.m) hs hM).trans ht)
  have hT := (tendsto_unitM_explicit hc P hm hs hμ₀ hM' hX).norm
  refine le_of_tendsto hT ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| ≤ 1 / 2 :=
    Filter.Eventually.mono (nhdsWithin_le_nhds (Icc_mem_nhds
      (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)))
      fun u hu => abs_le.2 hu
  filter_upwards [h0, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  exact hC a A b B t cs hM hcs ht u hu0 hu

/-- **The `q → 0` values with powers of `k²` and a heavy element line**: if the last `n ≤ r`
extra lines are unscaled, one constant `C` with `‖unitMPauliZeroPow n‖ ≤ C (1 + ∑ᵢ Mᵢ²)ⁿ⁺²`,
uniformly in the mass `t ≥ μ_s` of line `s` (`Mᵢ` the masses before the replacement). -/
theorem norm_unitMPauliZeroPow_slot_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (n : ℕ) :
    ∀ {r : ℕ} {κ : Fin r → ℝ}, n ≤ r → TrailOne n κ → (∀ j, 0 < κ j ∧ κ j ≤ 1) →
    ∃ C : ℝ, ∀ (a A b B t : ℝ) (cs : Fin r → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      unitMasses P.m a A b B s ≤ t →
      ‖unitMPauliZeroPow c P s κ (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b)
          (slotMB s t B) cs) n‖ ≤ C * (1 + ∑ i, unitMMasses P.m a A b B cs i ^ 2) ^ (n + 2) := by
  induction n with
  | zero =>
    intro r κ _ _ hκ
    obtain ⟨C, hC⟩ := norm_unitMPauliZero_slot_le hc P hm hs hμ₀ hκ
    refine ⟨C, fun a A b B t cs hM hcs ht => ?_⟩
    have hM' := massesGe_slot (s := s) hM ((le_unitMasses (m := P.m) hs hM).trans ht)
    rw [unitMPauliZeroPow_zero hc P hm hs hμ₀ hM' fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩]
    exact hC a A b B t cs hM hcs ht
  | succ n ih =>
    intro r κ hnr hT hκ
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨C₁, hC₁⟩ := ih (r := r) (κ := Fin.init κ) (by omega) hT.init fun j => hκ _
    obtain ⟨C₂, hC₂⟩ := ih (r := r + 1) (κ := κ) (by omega) hT.of_succ hκ
    refine ⟨|C₁| + |C₂|, fun a A b B t cs hM hcs ht => ?_⟩
    have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
    have hM' := massesGe_slot (s := s) hM ((le_unitMasses (m := P.m) hs hM).trans ht)
    rw [unitMPauliZeroPow_succ hc P hm hs hμ₀ hM' hnr hT hX]
    set S := ∑ i, unitMMasses P.m a A b B cs i ^ 2 with hS
    have hS₁ := sum_sq_unitMMasses_succ P.m a A b B cs
    rw [← hS] at hS₁
    have hS₁0 : 0 ≤ ∑ i, unitMMasses P.m a A b B (Fin.init cs) i ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hl0 : 0 ≤ cs (Fin.last r) ^ 2 := sq_nonneg _
    have h1 := hC₁ a A b B t (Fin.init cs) hM (fun j => hcs _) ht
    have h2 := hC₂ a A b B t cs hM hcs ht
    have hpow₁ : (1 + ∑ i, unitMMasses P.m a A b B (Fin.init cs) i ^ 2) ^ (n + 2) ≤
        (1 + S) ^ (n + 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have hpow : (1 + S) ^ (n + 2) ≤ (1 + S) ^ (n + 1 + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hP0 : 0 ≤ (1 + S) ^ (n + 2) := pow_nonneg (by linarith) _
    have hn1 := h1.trans ((mul_le_mul_of_nonneg_left hpow₁ (abs_nonneg _)).trans'
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by positivity) _)) |>.trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
    have hn2 : ‖((cs (Fin.last r) ^ 2 : ℝ) : ℂ) * unitMPauliZeroPow c P s κ
        (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs) n‖ ≤
          |C₂| * (1 + S) ^ (n + 1 + 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0,
        show n + 1 + 2 = n + 2 + 1 by omega, pow_succ]
      have h3 : C₂ * (1 + S) ^ (n + 2) ≤ |C₂| * (1 + S) ^ (n + 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hP0
      have h4 : cs (Fin.last r) ^ 2 ≤ 1 + S := by linarith
      calc cs (Fin.last r) ^ 2 * ‖unitMPauliZeroPow c P s κ
            (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs) n‖
          ≤ (1 + S) * (|C₂| * (1 + S) ^ (n + 2)) :=
            mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by linarith)
        _ = |C₂| * ((1 + S) ^ (n + 2) * (1 + S)) := by ring
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + S) ^ (n + 1 + 2) + |C₂| * (1 + S) ^ (n + 1 + 2) := add_le_add hn1 hn2
      _ = (|C₁| + |C₂|) * (1 + S) ^ (n + 1 + 2) := by ring

end Unit

end QED.ChainProof.SetCUnitM

end
