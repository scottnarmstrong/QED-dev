/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Sectors

/-!
# (R-Π₄) step L9: the absolute-term majorant of the collapsed integrand

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`, the class inputs `QED.GradedProof.RPi4.DecVTwo`). The second-difference
constants of the collapsed integrand at a Feynman point are controlled by the sum of the absolute
values of its three terms, `decMajP = ∑ⱼ ‖cⱼ‖ v^{-kⱼ}` (`kⱼ = n - 3, n - 4, n - 5`), and its
photon-weighted form `decMajF = z_γ decMajP(V₀ + z_γ u)`.

* `dec_abs_three_le`: the three absolute terms of `P(v) = a v^{-f-2} + b v^{-f-1} + c v^{-f}`
  are at most `8 · 3^{f+2} (‖P(v)‖ + ‖P(2v)‖ + ‖P(3v)‖)` (Vandermonde inversion); hence
  `decMajP_le_paramAtV`;
* `decMajP_le_of_coeff`, `decMajP_congr`, `decMajF_eq_zero_of_U`, `integrableOn_decMajF`;
* the pointwise sector bounds of `decMajF`: on the loop-UV corner `≤ E u⁻¹ ferSum^{-(n-2)}`
  for every `u > 0` (`dec_majF_le_corner`, with `V₀ ≥ c₀ ferSum`), on the bulk
  `≤ z_γ D (c₁ + z_γ u)^{-2}` (`dec_majF_le_bulk`).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

variable {m : ℕ}

/-- **The absolute-term majorant** of the parametric integrand at the value `v`. -/
noncomputable def decMajP (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) (v : ℝ) : ℝ :=
  ‖cOneAt n Q α p z‖ * (v ^ (n - 3))⁻¹ + ‖cTwoAt n Q α p z‖ * (v ^ (n - 4))⁻¹ +
    ‖cThreeAt n Q α z‖ * (v ^ (n - 5))⁻¹

/-- **The absolute-term majorant of the collapsed integrand** `z_γ decMajP(V₀ + z_γ u)`. -/
noncomputable def decMajF (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ)
    (z : Fin (m + 1) → ℝ) : ℝ :=
  z γ * decMajP n Q α pp z (symanzikV α pp M z + z γ * u)

/-! ### Three terms from three values -/

/-- **Vandermonde inversion**: the three absolute terms of
`P(w) = a w^{-(f+2)} + b w^{-(f+1)} + c w^{-f}` at `v > 0` are controlled by `‖P‖` at
`v, 2v, 3v`. -/
theorem dec_abs_three_le {f : ℕ} {v : ℝ} (hv : 0 < v) (a b c : ℂ) (P : ℝ → ℂ)
    (hP : ∀ w : ℝ, P w = a * ((w : ℂ) ^ (f + 2))⁻¹ + b * ((w : ℂ) ^ (f + 1))⁻¹ +
      c * ((w : ℂ) ^ f)⁻¹) :
    ‖a‖ * (v ^ (f + 2))⁻¹ + ‖b‖ * (v ^ (f + 1))⁻¹ + ‖c‖ * (v ^ f)⁻¹ ≤
      8 * 3 ^ (f + 2) * (‖P v‖ + ‖P (2 * v)‖ + ‖P (3 * v)‖) := by
  have hv' : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv.ne'
  set b₁ : ℂ := a * ((v : ℂ) ^ (f + 2))⁻¹
  set b₂ : ℂ := b * ((v : ℂ) ^ (f + 1))⁻¹
  set b₃ : ℂ := c * ((v : ℂ) ^ f)⁻¹
  have hy : ∀ l : ℝ, l ≠ 0 →
      ((l : ℂ) ^ (f + 2)) * P (l * v) = b₁ + l * b₂ + l ^ 2 * b₃ := fun l hl => by
    have hl' : (l : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl
    rw [hP]
    simp only [b₁, b₂, b₃]
    push_cast
    field_simp
    ring
  have y1 := hy 1 one_ne_zero
  have y2 := hy 2 two_ne_zero
  have y3 := hy 3 three_ne_zero
  simp only [ofReal_one, one_pow, one_mul] at y1
  set Y₁ := P v
  set Y₂ := P (2 * v)
  set Y₃ := P (3 * v)
  push_cast at y2 y3
  have e1 : b₁ = 3 * Y₁ - 3 * (2 ^ (f + 2) * Y₂) + 3 ^ (f + 2) * Y₃ := by
    linear_combination (-3) * y1 + 3 * y2 - y3
  have e2 : b₂ = (-5 * Y₁ + 8 * (2 ^ (f + 2) * Y₂) - 3 * (3 ^ (f + 2) * Y₃)) / 2 := by
    linear_combination (5 / 2) * y1 - 4 * y2 + (3 / 2) * y3
  have e3 : b₃ = (Y₁ - 2 * (2 ^ (f + 2) * Y₂) + 3 ^ (f + 2) * Y₃) / 2 := by
    linear_combination (-1 / 2) * y1 + y2 - (1 / 2) * y3
  have nb : ∀ (x : ℂ) (k : ℕ), ‖x * ((v : ℂ) ^ k)⁻¹‖ = ‖x‖ * (v ^ k)⁻¹ := fun x k => by
    rw [norm_mul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg hv.le]
  have n2 : ‖(2 : ℂ) ^ (f + 2) * Y₂‖ ≤ 3 ^ (f + 2) * ‖Y₂‖ := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
      (norm_nonneg _)
  have n3 : ‖(3 : ℂ) ^ (f + 2) * Y₃‖ = 3 ^ (f + 2) * ‖Y₃‖ := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have h3f : (1 : ℝ) ≤ 3 ^ (f + 2) := one_le_pow₀ (by norm_num)
  have nY1 : ‖Y₁‖ ≤ 3 ^ (f + 2) * ‖Y₁‖ := le_mul_of_one_le_left (norm_nonneg _) h3f
  have k1 : ‖b₁‖ ≤ 3 * ‖Y₁‖ + 3 * (3 ^ (f + 2) * ‖Y₂‖) + 3 ^ (f + 2) * ‖Y₃‖ := by
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [n3]
    refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
    rw [norm_mul, norm_mul (3 : ℂ), Complex.norm_ofNat]
    linarith
  have k2 : ‖b₂‖ ≤ (5 * ‖Y₁‖ + 8 * (3 ^ (f + 2) * ‖Y₂‖) + 3 * (3 ^ (f + 2) * ‖Y₃‖)) / 2 := by
    rw [e2, norm_div, Complex.norm_ofNat]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · rw [norm_mul, norm_neg, Complex.norm_ofNat]
    · rw [norm_mul, Complex.norm_ofNat]; linarith
    · rw [norm_mul, Complex.norm_ofNat, n3]
  have k3 : ‖b₃‖ ≤ (‖Y₁‖ + 2 * (3 ^ (f + 2) * ‖Y₂‖) + 3 ^ (f + 2) * ‖Y₃‖) / 2 := by
    rw [e3, norm_div, Complex.norm_ofNat]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl ?_))
      (le_of_eq n3))
    rw [norm_mul, Complex.norm_ofNat]; linarith
  rw [← nb a, ← nb b, ← nb c]
  have hY2 := norm_nonneg Y₂
  have hY3 := norm_nonneg Y₃
  have hY1 := norm_nonneg Y₁
  nlinarith

variable (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (z : Fin (m + 1) → ℝ)

/-- **The majorant from three values of the integrand** (`n ≥ 5`, `v > 0`). -/
theorem decMajP_le_paramAtV (hn : 5 ≤ n) {v : ℝ} (hv : 0 < v) :
    decMajP n Q α p z v ≤ 8 * 3 ^ (n - 3) * (‖paramAtV n Q α p z v‖ +
      ‖paramAtV n Q α p z (2 * v)‖ + ‖paramAtV n Q α p z (3 * v)‖) := by
  obtain ⟨f, rfl⟩ : ∃ f, n = f + 5 := ⟨n - 5, by omega⟩
  have e3 : f + 5 - 3 = f + 2 := by omega
  have e4 : f + 5 - 4 = f + 1 := by omega
  have e5 : f + 5 - 5 = f := by omega
  have h := dec_abs_three_le hv (cOneAt (f + 5) Q α p z) (cTwoAt (f + 5) Q α p z)
    (cThreeAt (f + 5) Q α z) (paramAtV (f + 5) Q α p z) fun w => by
      rw [paramAtV_eq, e3, e4, e5]
  rw [decMajP, e3, e4, e5]
  exact h

/-- The majorant from bounds on the three coefficients. -/
theorem decMajP_le_of_coeff {v a b c : ℝ} (hv : 0 < v) (h1 : ‖cOneAt n Q α p z‖ ≤ a)
    (h2 : ‖cTwoAt n Q α p z‖ ≤ b) (h3 : ‖cThreeAt n Q α z‖ ≤ c) :
    decMajP n Q α p z v ≤ a * (v ^ (n - 3))⁻¹ + b * (v ^ (n - 4))⁻¹ + c * (v ^ (n - 5))⁻¹ := by
  unfold decMajP
  have := fun k : ℕ => inv_nonneg.mpr (pow_nonneg hv.le k)
  gcongr

theorem decMajP_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ decMajP n Q α p z v := by
  unfold decMajP
  positivity

/-- The majorant depends on the numerator only through its values. -/
theorem decMajP_congr {Q' : LoopQuartic} (h : Q.eval = Q'.eval) (v : ℝ) :
    decMajP n Q α p z v = decMajP n Q' α p z v := by
  have h1 : Q.evalC (loopComp (-loopShift α p z)) = Q'.evalC (loopComp (-loopShift α p z)) :=
    congrFun h _
  simp only [decMajP, cOneAt, cTwoAt, cThreeAt, h1,
    QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractTwo_congr h
      (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose α _),
    QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractFour_congr h
      (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose α _)]

theorem decMajF_congr {Q' : LoopQuartic} (h : Q.eval = Q'.eval) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) : decMajF n Q α p M γ u z = decMajF n Q' α p M γ u z := by
  simp only [decMajF, decMajP_congr n Q α p z h]

theorem decMajF_eq_zero_of_U {M : Fin (m + 1) → ℝ} {γ : Fin (m + 1)} {u : ℝ}
    (h : symanzikU α z = 0) : decMajF n Q α p M γ u z = 0 := by
  simp [decMajF, decMajP, cOneAt, cTwoAt, cThreeAt, h]

theorem decMajF_nonneg {M : Fin (m + 1) → ℝ} {γ : Fin (m + 1)} {u : ℝ} (hz : 0 ≤ z γ)
    (hv : 0 ≤ symanzikV α p M z + z γ * u) : 0 ≤ decMajF n Q α p M γ u z :=
  mul_nonneg hz (decMajP_nonneg n Q α p z hv)

/-- **Integrability of the majorant** from that of the photon-weighted coefficients and a lower
bound `v ≥ c > 0` of the shifted `V` where `U ≠ 0`. -/
theorem integrableOn_decMajF {n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
    {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ} {γ₀ : Fin (m + 1)} {u c : ℝ}
    (hc : 0 < c)
    (k1 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k2 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k3 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y))
      (simplexSet m))
    (hV : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      c ≤ symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u) :
    IntegrableOn (fun y => decMajF n Q α pp M γ₀ u (simplexPoint y)) (simplexSet m) := by
  set V : (Fin m → ℝ) → ℝ := fun y => symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u
  have hzm : Measurable fun y : Fin m → ℝ => simplexPoint y γ₀ :=
    (continuous_apply γ₀).measurable.comp continuous_simplexPoint'.measurable
  have hVm : Measurable V :=
    ((measurable_symanzikV α pp M).comp continuous_simplexPoint'.measurable).add
      (hzm.mul measurable_const)
  have term : ∀ (g : (Fin m → ℝ) → ℂ) (k : ℕ), IntegrableOn g (simplexSet m) →
      (∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) = 0 → g y = 0) →
      IntegrableOn (fun y => ‖g y‖ * (V y ^ k)⁻¹) (simplexSet m) := fun g k hg hg0 => by
    refine (hg.norm.mul_const (c ^ k)⁻¹).mono' (hg.norm.aestronglyMeasurable.mul
      ((hVm.pow_const k).inv.aestronglyMeasurable)) ?_
    refine ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy => ?_
    rw [norm_mul, norm_norm]
    by_cases hU : symanzikU α (simplexPoint y) = 0
    · rw [hg0 y hy hU, norm_zero, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hcv := hV y hy hU
      rw [norm_inv, norm_pow, Real.norm_of_nonneg (hc.le.trans hcv)]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hcv k)
  have hI := ((term _ (n - 3) k1 fun y _ hU => by simp [cOneAt, hU]).add
    (term _ (n - 4) k2 fun y _ hU => by simp [cTwoAt, hU])).add
    (term _ (n - 5) k3 fun y _ hU => by simp [cThreeAt, hU])
  refine hI.congr_fun (fun y hy => ?_) (measurableSet_simplexSet m)
  have hz := (simplexPoint_mem_stdSimplex hy).1 γ₀
  simp only [Pi.add_apply, decMajF, decMajP, V, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hz]
  ring

/-! ### The corner and the bulk -/

/-- The scalar power-counting step of the corner: `X^j w^{i+1} ≤ G^{j+i+1} u⁻¹ y^{-(j+i)}` for
`X ≤ G/y`, `w ≤ G/u`, `w ≤ G/y`. -/
theorem dec_corner_term {X w G u y : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ G * y⁻¹) (hw0 : 0 ≤ w)
    (hwu : w ≤ G * u⁻¹) (hwy : w ≤ G * y⁻¹) (j i : ℕ) :
    X ^ j * w ^ (i + 1) ≤ G ^ (j + i + 1) * u⁻¹ * (y ^ (j + i))⁻¹ := by
  have hG : 0 ≤ G * y⁻¹ := hX0.trans hX
  have h1 : X ^ j ≤ (G * y⁻¹) ^ j := pow_le_pow_left₀ hX0 hX j
  have h2 : w ^ i ≤ (G * y⁻¹) ^ i := pow_le_pow_left₀ hw0 hwy i
  have h3 : X ^ j * w ^ i ≤ (G * y⁻¹) ^ j * (G * y⁻¹) ^ i :=
    mul_le_mul h1 h2 (by positivity) (pow_nonneg hG _)
  have h4 := mul_le_mul h3 hwu hw0 (mul_nonneg (pow_nonneg hG _) (pow_nonneg hG _))
  calc X ^ j * w ^ (i + 1) = X ^ j * w ^ i * w := by ring
    _ ≤ (G * y⁻¹) ^ j * (G * y⁻¹) ^ i * (G * u⁻¹) := h4
    _ = G ^ (j + i + 1) * u⁻¹ * (y ^ (j + i))⁻¹ := by rw [← inv_pow]; ring

/-- **The majorant on the corner, for every photon mass**: `decMajF ≤ E u⁻¹ ferSum^{-(n-2)}` for
`u > 0`, with `E` uniform over the family (momenta `cs • k`, `|k| ≤ KP`), where
`V₀ ≥ c₀ ferSum`. -/
theorem dec_majF_le_corner {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP c₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₀ : 0 < c₀) (hk : ∀ s μ, |k s μ| ≤ KP) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ cornerSet α ρ₀ →
      (symanzikU α z ≠ 0 → c₀ * ferSum α z ≤ symanzikV α (fun i => cs i • k s) (M s) z) →
      ∀ u : ℝ, 0 < u →
      decMajF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u z ≤
        E * u⁻¹ * (ferSum α z ^ (n - 2))⁻¹ := by
  have hγ : α γ₀ = ![1, -1] := (huniq γ₀).mpr rfl
  obtain ⟨C, hC0, hC⟩ := exists_abs_loopShift_smul_le α cs
  set B' := max BQ 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hQ' : LQBdd Q B' := ⟨fun i => (hQ.const i).trans (le_max_left _ _),
    fun i a => (hQ.lin i a).trans (le_max_left _ _),
    fun i a b => (hQ.quad i a b).trans (le_max_left _ _),
    fun i a b c => (hQ.cub i a b c).trans (le_max_left _ _),
    fun i a b c d => (hQ.quart i a b c d).trans (le_max_left _ _)⟩
  set K : ℝ := C * max KP 0 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ := 6 * (4681 * B' * (1 + K) ^ 4)
  set b : ℝ := 26176 * B' * (1 + (K + K ^ 2))
  set c : ℝ := 4096 * B' * 3
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  set ε : ℝ := 1 - ρ₀ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  set G : ℝ := ε⁻¹ + c₀⁻¹ with hG
  have hG0 : 0 ≤ G := by positivity
  have hE : 0 ≤ (a + b + c) * G ^ (n - 1) := by positivity
  refine ⟨(a + b + c) * G ^ (n - 1), hE, fun s z hz hz1 hcorner hV u hu => ?_⟩
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • k s
  set y := ferSum α z with hy
  have hy0 : 0 ≤ y := Finset.sum_nonneg fun l _ => hz l
  have hq3 : 3 ≤ n - 3 := by rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num
  rcases hy0.eq_or_lt with hy0' | hypos
  · rw [decMajF_eq_zero_of_U n (Q s) α pp z (symanzikU_eq_zero_of_ferSum hrow hz hy0'.symm)]
    exact mul_nonneg (mul_nonneg hE (inv_nonneg.2 hu.le)) (inv_nonneg.2 (pow_nonneg hy0 _))
  have ht : z γ₀ = 1 - y := by rw [hy, ferSum_eq_one_sub huniq hz1]; ring
  have htε : ε ≤ z γ₀ := by rw [ht, hε]; linarith [show y ≤ ρ₀ from hcorner]
  have hU1 := symanzikU_ge_corner hγ hrow hz (z := z)
  have hεy : 0 < ε * y := mul_pos hε0 hypos
  have hUε : ε * y ≤ symanzikU α z := (mul_le_mul_of_nonneg_right htε hy0).trans hU1
  have hU : 0 < symanzikU α z := hεy.trans_le hUε
  set X := (symanzikU α z)⁻¹ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXP : X ≤ (ε * y)⁻¹ := inv_anti₀ hεy hUε
  have hgent : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ X := fun r t => by
    refine (abs_inv_le_chain (α := α) (hα := hrow) (hz := hz) (hU := hU.ne') r t).trans ?_
    rw [← sum_chain hrow z, hz1, one_div]
  have hX : ∀ a, ‖loopComp (-loopShift α pp z) a‖ ≤ K := fun a => by
    simp only [loopComp, Complex.norm_real, Real.norm_eq_abs, Pi.neg_apply, abs_neg]
    refine (hC z hz hU.ne' (k s) a.1 a.2).trans ?_
    exact mul_le_mul_of_nonneg_left ((hk s a.2).trans (le_max_left _ _)) hC0
  have hn7 : (n - 4).factorial ≤ (6 : ℝ) ∧ ((n - 5).factorial : ℝ) / 2 ≤ 1 := by
    rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num [Nat.factorial]
  have eU : ∀ x : ℝ, x / symanzikU α z ^ 2 = x * X ^ 2 := fun x => by
    rw [hXdef, inv_pow, div_eq_mul_inv]
  have h1 : ‖cOneAt n (Q s) α pp z‖ ≤ a * X ^ 2 := by
    refine (norm_cOneAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)).trans ?_
    rw [eU]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul hn7.1 (mul_le_mul_of_nonneg_right (lqNorm_le hQ' s) (by positivity))
      (mul_nonneg (lqNorm_nonneg _) (by positivity)) (by norm_num)
  have h2 : ‖cTwoAt n (Q s) α pp z‖ ≤ b * X ^ 3 := by
    refine (norm_cTwoAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)
      (hg := hgent)).trans ?_
    rw [eU]
    have e : ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * X) ≤
        1 * (26176 * B' * (1 + (K + K ^ 2)) * X) :=
      mul_le_mul hn7.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lqHess_le hQ' s) (by positivity)) hX0)
        (mul_nonneg (mul_nonneg (lqHess_nonneg _) (by positivity)) hX0) (by norm_num)
    calc ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * X) * X ^ 2
        ≤ 1 * (26176 * B' * (1 + (K + K ^ 2)) * X) * X ^ 2 :=
          mul_le_mul_of_nonneg_right e (by positivity)
      _ = b * X ^ 3 := by ring
  have hV0 : c₀ * y ≤ symanzikV α pp (M s) z := hV hU.ne'
  have hzu : 0 ≤ z γ₀ * u := mul_nonneg (hz γ₀) hu.le
  have hv1 : ε * u ≤ symanzikV α pp (M s) z + z γ₀ * u := by
    have := mul_le_mul_of_nonneg_right htε hu.le
    have : 0 ≤ c₀ * y := mul_nonneg hc₀.le hy0
    linarith
  have hv2 : c₀ * y ≤ symanzikV α pp (M s) z + z γ₀ * u := by linarith
  have hvp : 0 < symanzikV α pp (M s) z + z γ₀ * u :=
    (mul_pos hε0 hu).trans_le hv1
  set v := symanzikV α pp (M s) z + z γ₀ * u with hvdef
  set w := v⁻¹ with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hwu : w ≤ G * u⁻¹ := by
    refine (inv_anti₀ (mul_pos hε0 hu) hv1).trans ?_
    rw [mul_inv]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  have hwy : w ≤ G * y⁻¹ := by
    refine (inv_anti₀ (mul_pos hc₀ hypos) hv2).trans ?_
    rw [mul_inv]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
  have hXy : X ≤ G * y⁻¹ := by
    refine hXP.trans ?_
    rw [mul_inv]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  have ew : ∀ j, (v ^ j)⁻¹ = w ^ j := fun j => by rw [hwdef, inv_pow]
  set Z := G ^ (n - 1) * u⁻¹ * (y ^ (n - 2))⁻¹ with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have T : ∀ j i : ℕ, j + i + 1 = n - 1 → X ^ j * w ^ (i + 1) ≤ Z := fun j i hji => by
    have := dec_corner_term hX0 hXy hw0 hwu hwy j i
    rwa [hji, show j + i = n - 2 by omega] at this
  have hpar : decMajP n (Q s) α pp z v ≤ (a + b + c) * Z := by
    rcases hn with hn7 | ⟨hn6, hq0⟩
    · have h3 : ‖cThreeAt n (Q s) α z‖ ≤ c * X ^ 4 := by
        refine (norm_cThreeAt_le (n := n) (α := α) (z := z) (hU := hU) (hg := hgent)).trans ?_
        rw [eU, show n - 6 = 1 by omega]
        have hq := lqQuart_le hQ' s
        have hBX : 0 ≤ B' * X ^ 4 := mul_nonneg hB0 (pow_nonneg hX0 4)
        have e : ((Nat.factorial 1 : ℕ) : ℝ) / 4 * (lqQuart (Q s) * (3 * X ^ 2)) * X ^ 2 =
            3 / 4 * (lqQuart (Q s) * X ^ 4) := by
          norm_num [Nat.factorial]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_right hq (pow_nonneg hX0 4)
        linarith
      refine (decMajP_le_of_coeff n (Q s) α pp z hvp h1 h2 h3).trans ?_
      rw [ew, ew, ew, show n - 3 = 3 + 1 by omega, show n - 4 = 2 + 1 by omega,
        show n - 5 = 1 + 1 by omega]
      have f1 := mul_le_mul_of_nonneg_left (T 2 3 (by omega)) ha
      have f2 := mul_le_mul_of_nonneg_left (T 3 2 (by omega)) hb
      have f3 := mul_le_mul_of_nonneg_left (T 4 1 (by omega)) hc
      calc a * X ^ 2 * w ^ (3 + 1) + b * X ^ 3 * w ^ (2 + 1) + c * X ^ 4 * w ^ (1 + 1)
          = a * (X ^ 2 * w ^ (3 + 1)) + b * (X ^ 3 * w ^ (2 + 1)) +
            c * (X ^ 4 * w ^ (1 + 1)) := by ring
        _ ≤ a * Z + b * Z + c * Z := add_le_add (add_le_add f1 f2) f3
        _ = (a + b + c) * Z := by ring
    · have h3 : ‖cThreeAt n (Q s) α z‖ ≤ 0 := by
        refine (norm_cThreeAt_le (n := n) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (le_of_eq ?_)
        simp [lqQuart, hq0 s]
      refine (decMajP_le_of_coeff n (Q s) α pp z hvp h1 h2 h3).trans ?_
      rw [ew, ew, ew, show n - 3 = 2 + 1 by omega, show n - 4 = 1 + 1 by omega]
      have f1 := mul_le_mul_of_nonneg_left (T 2 2 (by omega)) ha
      have f2 := mul_le_mul_of_nonneg_left (T 3 1 (by omega)) hb
      have f3 : 0 ≤ c * Z := mul_nonneg hc hZ0
      calc a * X ^ 2 * w ^ (2 + 1) + b * X ^ 3 * w ^ (1 + 1) + 0 * w ^ (n - 5)
          = a * (X ^ 2 * w ^ (2 + 1)) + b * (X ^ 3 * w ^ (1 + 1)) := by ring
        _ ≤ a * Z + b * Z := add_le_add f1 f2
        _ ≤ (a + b + c) * Z := by nlinarith
  have ht1 : z γ₀ ≤ 1 := by rw [ht]; linarith
  have hP0 : 0 ≤ decMajP n (Q s) α pp z v := decMajP_nonneg n (Q s) α pp z hvp.le
  calc decMajF n (Q s) α pp (M s) γ₀ u z = z γ₀ * decMajP n (Q s) α pp z v := rfl
    _ ≤ 1 * ((a + b + c) * Z) := mul_le_mul ht1 hpar hP0 zero_le_one
    _ = _ := by rw [hZ]; ring

/-- **The majorant on the bulk**: `decMajF ≤ z_γ D (c₁ + z_γ u)^{-2}` for `u ≥ 0`. -/
theorem dec_majF_le_bulk {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP : ℝ} (hρ₀ : 0 < ρ₀) (hc₁ : 0 < c₁) (hP : ∀ s l, ‖pp s l‖ ≤ KP) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ bulkSet α ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) z → ∀ u : ℝ, 0 ≤ u →
      decMajF n (Q s) α (pp s) (M s) γ₀ u z ≤ z γ₀ * (D * ((c₁ + z γ₀ * u) ^ 2)⁻¹) := by
  set B' := max BQ 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hQ' : LQBdd Q B' := ⟨fun i => (hQ.const i).trans (le_max_left _ _),
    fun i a => (hQ.lin i a).trans (le_max_left _ _),
    fun i a b => (hQ.quad i a b).trans (le_max_left _ _),
    fun i a b c => (hQ.cub i a b c).trans (le_max_left _ _),
    fun i a b c d => (hQ.quart i a b c d).trans (le_max_left _ _)⟩
  set g : ℝ := (ρ₀ ^ 3)⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  set K : ℝ := 2 * g * max KP 0 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ := 6 * (4681 * B' * (1 + K) ^ 4) * g ^ 2
  set b : ℝ := 26176 * B' * (1 + (K + K ^ 2)) * g * g ^ 2
  set c : ℝ := 4096 * B' * (3 * g ^ 2) * g ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  refine ⟨(a + b + c) * (1 + c₁⁻¹) ^ 2, by positivity, fun s z hz hz1 hbulk hV u hu => ?_⟩
  have hU3 := symanzikU_ge_bulk hrow z hρ₀ hz hz1 hbulk
  have hU : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hU3
  have hUi : (symanzikU α z ^ 2)⁻¹ ≤ g ^ 2 := by
    rw [hg, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hU3 2)
  have hgent : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g := fun r t => by
    refine (abs_inv_le_chain (α := α) (hα := hrow) (hz := hz) (hU := hU.ne') r t).trans ?_
    rw [← sum_chain hrow z, hz1, hg, one_div]
    exact inv_anti₀ (by positivity) hU3
  have hP' : ∀ l, ‖pp s l‖ ≤ max KP 0 := fun l => (hP s l).trans (le_max_left _ _)
  have hX : ∀ a, ‖loopComp (-loopShift α (pp s) z) a‖ ≤ K := fun a => by
    simp only [loopComp, Complex.norm_real, Real.norm_eq_abs, Pi.neg_apply, abs_neg]
    exact abs_loopShift_le_bulk hrow hz hz1 hP' hgent a.1 a.2
  have key : ∀ {x y : ℝ}, 0 ≤ y → x ≤ y → x / symanzikU α z ^ 2 ≤ y * g ^ 2 := fun hy hxy => by
    rw [div_eq_mul_inv]
    exact mul_le_mul hxy hUi (by positivity) hy
  have hn7 : (n - 4).factorial ≤ (6 : ℝ) ∧ ((n - 5).factorial : ℝ) / 2 ≤ 1 := by
    rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num [Nat.factorial]
  have h1 : ‖cOneAt n (Q s) α (pp s) z‖ ≤ a := by
    refine (norm_cOneAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)).trans
      (key (by positivity) ?_)
    exact mul_le_mul hn7.1 (mul_le_mul_of_nonneg_right (lqNorm_le hQ' s) (by positivity))
      (mul_nonneg (lqNorm_nonneg _) (by positivity)) (by norm_num)
  have h2 : ‖cTwoAt n (Q s) α (pp s) z‖ ≤ b := by
    refine (norm_cTwoAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)
      (hg := hgent)).trans (key (by positivity) ?_)
    have e : ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * g) ≤
        1 * (26176 * B' * (1 + (K + K ^ 2)) * g) :=
      mul_le_mul hn7.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lqHess_le hQ' s) (by positivity)) hg0)
        (mul_nonneg (mul_nonneg (lqHess_nonneg _) (by positivity)) hg0) (by norm_num)
    linarith
  have hv0 : 0 < c₁ + z γ₀ * u := by have := hz γ₀; positivity
  have hv : c₁ + z γ₀ * u ≤ symanzikV α (pp s) (M s) z + z γ₀ * u := by linarith
  have hvp : 0 < symanzikV α (pp s) (M s) z + z γ₀ * u := hv0.trans_le hv
  set v := symanzikV α (pp s) (M s) z + z γ₀ * u with hvdef
  have hcv : c₁ ≤ v := by have := hz γ₀; nlinarith
  have hpar : decMajP n (Q s) α (pp s) z v ≤ (a + b + c) * (1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹ := by
    rcases hn with rfl | ⟨rfl, hq0⟩
    · have h3 : ‖cThreeAt 7 (Q s) α z‖ ≤ c := by
        refine (norm_cThreeAt_le (n := 7) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (key (by positivity) ?_)
        have := lqQuart_le hQ' s
        norm_num [Nat.factorial]
        nlinarith [sq_nonneg g, lqQuart_nonneg (Q s)]
      refine (decMajP_le_of_coeff 7 (Q s) α (pp s) z hvp h1 h2 h3).trans ?_
      have e4 := inv_pow_le_sq hc₁ hcv (k := 7 - 3) (by norm_num) (by norm_num)
      have e3 := inv_pow_le_sq hc₁ hcv (k := 7 - 4) (by norm_num) (by norm_num)
      have e2 := inv_pow_le_sq hc₁ hcv (k := 7 - 5) (by norm_num) (by norm_num)
      have f4 := mul_le_mul_of_nonneg_left e4 ha
      have f3 := mul_le_mul_of_nonneg_left e3 hb
      have f2 := mul_le_mul_of_nonneg_left e2 hc
      rw [mul_assoc]
      have : (a + b + c) * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) = a * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) +
          b * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) + c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := by ring
      linarith
    · have h3 : ‖cThreeAt 6 (Q s) α z‖ ≤ 0 := by
        refine (norm_cThreeAt_le (n := 6) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (le_of_eq ?_)
        simp [lqQuart, hq0 s]
      refine (decMajP_le_of_coeff 6 (Q s) α (pp s) z hvp h1 h2 h3).trans ?_
      have e3 := inv_pow_le_sq hc₁ hcv (k := 6 - 3) (by norm_num) (by norm_num)
      have e2 := inv_pow_le_sq hc₁ hcv (k := 6 - 4) (by norm_num) (by norm_num)
      have hw : 0 ≤ (1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹ := by positivity
      have f3 := mul_le_mul_of_nonneg_left e3 ha
      have f2 := mul_le_mul_of_nonneg_left e2 hb
      have fc : 0 ≤ c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := mul_nonneg hc hw
      rw [mul_assoc, zero_mul, add_zero]
      have : (a + b + c) * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) = a * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) +
          b * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) + c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := by ring
      linarith
  have hvv : (v ^ 2)⁻¹ ≤ ((c₁ + z γ₀ * u) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hv0.le hv 2)
  show z γ₀ * decMajP n (Q s) α (pp s) z v ≤ _
  refine mul_le_mul_of_nonneg_left (hpar.trans ?_) (hz γ₀)
  exact mul_le_mul_of_nonneg_left hvv (by positivity)

end QED.GradedProof.RPi4

end
