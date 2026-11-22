/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellYId
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c): bounds on the dressed photon below `0` decaying like `1/U`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. With `A, B, U > 0` and
`w ≥ -δ`, `2δ ≤ min(A, B, U)`, the functions `Q = bubQ`, `R = w Q`, the closed tail
`quadTailVP` of `Q` and the tail of the dressed photon are bounded by constants depending on
`A, B` only, divided by `U`:

* `abs_bubQ_le_qMax`: `|Q(w)| ≤ qMax A B / U`;
* `abs_mul_bubQ_le_rMax`: `|w Q(w)| ≤ rMax A B / U`;
* `abs_quadTailVP_le_tMax`: `|∫_w^∞ Q| ≤ tMax A B / U` (distinct `A, B, U`);
* `photonTail_vp_mem_Icc`: `0 ≤ Tail(w) ≤ bubKQ A B / U` for the dressed photon.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCRegDisp

/-- `4 (A - B)²/B`. -/
noncomputable def bubKQ (A B : ℝ) : ℝ := 4 * (A - B) ^ 2 / B

/-- `2 (A - B)²`. -/
noncomputable def bubKR (A B : ℝ) : ℝ := 2 * (A - B) ^ 2

/-- The bound of `U Q`. -/
noncomputable def qMax (A B : ℝ) : ℝ := bubKQ A B / (A / 2) ^ 2

/-- The bound of `U R`, `R = w Q`. -/
noncomputable def rMax (A B : ℝ) : ℝ := bubKR A B / (B / 2) ^ 2

/-- The bound of `U` times the closed tail of `Q`. -/
noncomputable def tMax (A B : ℝ) : ℝ := 2 * bubKQ A B / A

/-- **A function with nonnegative derivative tending to `0` is nonpositive.** -/
theorem le_zero_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a : ℝ}
    (hd : ∀ t, a ≤ t → HasDerivAt f (f' t) t) (h0 : ∀ t, a ≤ t → 0 ≤ f' t)
    (hL : Tendsto f atTop (𝓝 0)) {t : ℝ} (ht : a ≤ t) : f t ≤ 0 := by
  have hmono : MonotoneOn f (Ici a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici a)
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt)
      fun v hv => ?_
    rw [(hd v (interior_subset hv)).deriv]
    exact h0 v (interior_subset hv)
  refine ge_of_tendsto hL ?_
  filter_upwards [eventually_ge_atTop t] with v hv
  exact hmono (mem_Ici.2 ht) (mem_Ici.2 (ht.trans hv)) hv

/-- **Comparison of tails**: if `f' = -g`, `|g(t)| ≤ c/(t + b)²` and `f → 0`, then
`|f(t)| ≤ c/(t + b)`. -/
theorem abs_le_of_hasDerivAt_tail {f g : ℝ → ℝ} {a b c : ℝ} (hab : 0 < a + b)
    (hd : ∀ t, a ≤ t → HasDerivAt f (-g t) t) (hg : ∀ t, a ≤ t → |g t| ≤ c / (t + b) ^ 2)
    (hL : Tendsto f atTop (𝓝 0)) {t : ℝ} (ht : a ≤ t) : |f t| ≤ c / (t + b) := by
  have hpos : ∀ t, a ≤ t → 0 < t + b := fun t ht => by linarith
  have hG : ∀ t, a ≤ t → HasDerivAt (fun t => c * (t + b)⁻¹) (-(c / (t + b) ^ 2)) t :=
    fun t ht => by
      have h := (((hasDerivAt_id t).add_const b).inv (hpos t ht).ne').const_mul c
      convert h using 1
      · funext y
        simp only [id, Pi.inv_apply]
      · simp only [id]
        have := (hpos t ht).ne'
        field_simp
  have hGL : Tendsto (fun t => c * (t + b)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => (t + b)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop b tendsto_id)
    simpa only [mul_zero] using h1.const_mul c
  have up := le_zero_of_hasDerivAt_nonneg (f := fun t => f t - c * (t + b)⁻¹)
    (fun t ht => (hd t ht).sub (hG t ht)) (fun t ht => by
      have := (abs_le.1 (hg t ht)).2
      linarith) (by simpa only [sub_zero] using hL.sub hGL) ht
  have lo := le_zero_of_hasDerivAt_nonneg (f := fun t => -(f t + c * (t + b)⁻¹))
    (fun t ht => ((hd t ht).add (hG t ht)).neg) (fun t ht => by
      have := (abs_le.1 (hg t ht)).1
      linarith) (by simpa only [add_zero, neg_zero] using (hL.add hGL).neg) ht
  rw [abs_le, div_eq_mul_inv]
  constructor <;> linarith

section Bound

variable {A B U δ w : ℝ} (hδ : 0 < δ) (hδA : 2 * δ ≤ A) (hδB : 2 * δ ≤ B) (hδU : 2 * δ ≤ U)

include hδ in
theorem abs_div_add_le_one_of_margin {c : ℝ} (hc : 2 * δ ≤ c) (hw : -δ ≤ w) :
    |w / (w + c)| ≤ 1 := by
  have h : 0 < w + c := by linarith
  rw [abs_div, abs_of_pos h, div_le_one h, abs_le]
  constructor <;> linarith

include hδ in
theorem one_div_add_le_of_margin {c : ℝ} (hc : 2 * δ ≤ c) (hw : -δ ≤ w) :
    |1 / (w + c)| ≤ 2 / c := by
  have h : c / 2 ≤ w + c := by linarith
  have h0 : 0 < c / 2 := by linarith
  rw [abs_of_pos (one_div_pos.2 (by linarith)), show 2 / c = 1 / (c / 2) by
    field_simp]
  exact one_div_le_one_div_of_le h0 h

include hδ hδA hδB hδU in
/-- `|Q(w)| ≤ bubKQ/U/(w + A)²`. -/
theorem abs_bubQ_le (hw : -δ ≤ w) : |bubQ A B U w| ≤ bubKQ A B / U / (w + A) ^ 2 := by
  have hA : 0 < w + A := by linarith
  have hB : 0 < w + B := by linarith
  have hU : 0 < U := by linarith
  have hB0 : 0 < B := by linarith
  have e : bubQ A B U w =
      1 / (w + U) * (w / (w + B)) * (1 / (w + B)) * ((A - B) ^ 2 / (w + A) ^ 2) := by
    unfold bubQ
    field_simp
    ring
  have h1 := one_div_add_le_of_margin hδ hδU hw
  have h2 := abs_div_add_le_one_of_margin hδ hδB hw
  have h3 := one_div_add_le_of_margin hδ hδB hw
  have hX : 0 ≤ (A - B) ^ 2 / (w + A) ^ 2 := by positivity
  rw [e, abs_mul, abs_mul, abs_mul, abs_of_nonneg hX]
  calc |1 / (w + U)| * |w / (w + B)| * |1 / (w + B)| * ((A - B) ^ 2 / (w + A) ^ 2) ≤
      2 / U * 1 * (2 / B) * ((A - B) ^ 2 / (w + A) ^ 2) := by
        gcongr
    _ = bubKQ A B / U / (w + A) ^ 2 := by
        unfold bubKQ
        field_simp
        ring

include hδ hδA hδB hδU in
theorem abs_bubQ_le_qMax (hw : -δ ≤ w) : |bubQ A B U w| ≤ qMax A B / U := by
  have hA : A / 2 ≤ w + A := by linarith
  have hA0 : 0 < A / 2 := by linarith
  have hU : 0 < U := by linarith
  have hk : 0 ≤ bubKQ A B := div_nonneg (by positivity) (by linarith)
  refine (abs_bubQ_le hδ hδA hδB hδU hw).trans ?_
  unfold qMax
  rw [div_div, div_div, mul_comm U]
  exact div_le_div_of_nonneg_left hk (by positivity)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0.le hA 2) hU.le)

include hδ hδA hδB hδU in
/-- `|w Q(w)| ≤ bubKR/U/(w + B)²`. -/
theorem abs_mul_bubQ_le (hw : -δ ≤ w) : |w * bubQ A B U w| ≤ bubKR A B / U / (w + B) ^ 2 := by
  have hA : 0 < w + A := by linarith
  have hB : 0 < w + B := by linarith
  have hU : 0 < U := by linarith
  have e : w * bubQ A B U w =
      1 / (w + U) * (w / (w + A)) ^ 2 * ((A - B) ^ 2 / (w + B) ^ 2) := by
    unfold bubQ
    field_simp
    ring
  have h1 := one_div_add_le_of_margin hδ hδU hw
  have h2 := abs_div_add_le_one_of_margin hδ hδA hw
  have h2' : |(w / (w + A)) ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) h2
  have hX : 0 ≤ (A - B) ^ 2 / (w + B) ^ 2 := by positivity
  rw [e, abs_mul, abs_mul, abs_of_nonneg hX]
  calc |1 / (w + U)| * |(w / (w + A)) ^ 2| * ((A - B) ^ 2 / (w + B) ^ 2) ≤
      2 / U * 1 * ((A - B) ^ 2 / (w + B) ^ 2) := by
        gcongr
    _ = bubKR A B / U / (w + B) ^ 2 := by
        unfold bubKR
        field_simp

include hδ hδA hδB hδU in
theorem abs_mul_bubQ_le_rMax (hw : -δ ≤ w) : |w * bubQ A B U w| ≤ rMax A B / U := by
  have hB : B / 2 ≤ w + B := by linarith
  have hB0 : 0 < B / 2 := by linarith
  have hU : 0 < U := by linarith
  have hk : 0 ≤ bubKR A B := by unfold bubKR; positivity
  refine (abs_mul_bubQ_le hδ hδA hδB hδU hw).trans ?_
  unfold rMax
  rw [div_div, div_div, mul_comm U]
  exact div_le_div_of_nonneg_left hk (by positivity)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB0.le hB 2) hU.le)

include hδ hδA hδB hδU in
/-- **The closed tail of `Q` below `0`**: `|∫_w^∞ Q| ≤ tMax A B / U`. -/
theorem abs_quadTailVP_le_tMax (hAB : A ≠ B) (hAU : A ≠ U) (hBU : B ≠ U) (hw : -δ ≤ w) :
    |quadTailVP A B U w| ≤ tMax A B / U := by
  have hU : 0 < U := by linarith
  have hk : 0 ≤ bubKQ A B := div_nonneg (by positivity) (by linarith)
  have h := abs_le_of_hasDerivAt_tail (g := bubQ A B U) (c := bubKQ A B / U) (b := A)
    (by linarith) (fun t ht => hasDerivAt_quadTailVP hAB hAU hBU (by linarith) (by linarith)
      (by linarith)) (fun t ht => abs_bubQ_le hδ hδA hδB hδU ht)
    (tendsto_quadTailVP_atTop hAB hAU hBU) hw
  refine h.trans ?_
  have hA : A / 2 ≤ w + A := by linarith
  have hA0 : 0 < A / 2 := by linarith
  unfold tMax
  rw [show 2 * bubKQ A B / A / U = bubKQ A B / U / (A / 2) by field_simp]
  exact div_le_div_of_nonneg_left (by positivity) hA0 hA

end Bound

/-! ### The tail of the dressed photon below `0` -/

section Tail

variable {m mγ Λ T δ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hδ : 0 < δ)
  (hδA : 2 * δ ≤ mγ ^ 2) (hδB : 2 * δ ≤ Λ ^ 2) (hδU : 2 * δ ≤ T * m ^ 2)

include hδA hδB hδU in
theorem le_vpMargin : δ ≤ vpMargin m mγ Λ T := by
  unfold vpMargin
  rw [le_div_iff₀ two_pos]
  exact le_min (le_min (by linarith) (by linarith)) (by linarith)

include hm hmγ hΛ hT hδ hδA hδB hδU in
/-- **The tail of the dressed photon below `0`**: `0 ≤ Tail(w) ≤ bubKQ/U` for `w ≥ -δ`. -/
theorem photonTail_vp_mem_Icc (hab : mγ ^ 2 ≠ Λ ^ 2) (hac : mγ ^ 2 ≠ T * m ^ 2)
    (hbc : Λ ^ 2 ≠ T * m ^ 2) {w : ℝ} (hw : -δ ≤ w) :
    0 ≤ photonTail (vpPhotonT m mγ Λ T) w ∧
      photonTail (vpPhotonT m mγ Λ T) w ≤ bubKQ (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2) := by
  have hle := le_vpMargin (m := m) (mγ := mγ) (Λ := Λ) (T := T) hδA hδB hδU
  have hR : ∀ u, -δ ≤ u → 0 ≤ vpPhotonT m mγ Λ T u := fun u hu =>
    (vpPhotonT_bound hmγ hΛ hT hm (by linarith)).1
  have hU : 0 < T * m ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [photonTail_eq_Ioi]
    exact setIntegral_nonneg measurableSet_Ioi fun u hu => hR u (by
      have : w < u := hu
      linarith)
  · have h := abs_le_of_hasDerivAt_tail (g := vpPhotonT m mγ Λ T)
      (c := bubKR (mγ ^ 2) (Λ ^ 2) / (T * m ^ 2)) (b := Λ ^ 2) (by linarith)
      (fun t ht => hasDerivAt_photonTail_vp hmγ hΛ hT hm (by linarith)) (fun t ht => by
        rw [vpPhotonT_eq_mul_bubQ]
        exact abs_mul_bubQ_le hδ hδA hδB hδU ht)
      (tendsto_photonTail_vp_atTop hab hac hbc hmγ hΛ hU) hw
    refine (le_abs_self _).trans (h.trans ?_)
    have hB : Λ ^ 2 / 2 ≤ w + Λ ^ 2 := by linarith
    have hB0 : 0 < Λ ^ 2 / 2 := by positivity
    have hk : 0 ≤ bubKR (mγ ^ 2) (Λ ^ 2) := by unfold bubKR; positivity
    refine (div_le_div_of_nonneg_left (by positivity) hB0 hB).trans_eq ?_
    unfold bubKQ bubKR
    field_simp
    ring

end Tail

end QED.ChainProof.SetCRegDisp

end
