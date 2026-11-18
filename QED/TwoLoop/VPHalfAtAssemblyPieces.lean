/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyBound
public import QED.WickModel.VacuumPolarizationLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spectral pieces of the vacuum-polarization class, with bounds uniform in the parameter

After the integration by parts in the Feynman parameter `x` of the inner loop
(`QED.TwoLoop.VPHalfAt.vpLoopEps_eq_spectral`), the outer integrand of the vacuum-polarization
class contains, for each flavour of mass `M`, the factor `1/(M² + x(1-x)k² - iε)` (`fDen`). For
`0 < x < 1` it is `(x(1-x))⁻¹` times the photon denominator of mass `μ_x = √(M²/(x(1-x)))`
(`specMu`) with prescription `ε/(x(1-x))` (`specEta`) (`denom_specMu`).

* `qInt j`: `(k²)ʲ N(k) / (D_{p'+k} D_{p+k} D_a D_b D_a D_b (M² + x(1-x)k² - iε))`, all model
  prescriptions `ε`.
* `qInt_eq_lim`: `qInt j = (x(1-x))⁻¹ (k²)ʲ P₅`, with `P₅` the photon-product vertex of masses
  `(a, b, a, b, μ_x)` and prescriptions `(ε, ε, ε, ε, ε/(x(1-x)))`; this form has the limit
  of the engine.
* `qInt_eq_fact`: `qInt j = (M² - iε)⁻¹ ((k²)ʲ P₄ - (k²)^{j+1} P₅)`, `P₄` the vertex of masses
  `(a, b, a, b)`: the factor `(x(1-x))⁻¹` is absorbed, `1/D_μ = (1 - k²/D_μ)/μ̃²`, and this form is
  bounded uniformly in `x`.
* `exists_good_pieces`: one constant `C` for all `ε ∈ (0, 1]`, and for each `ε` one pointwise
  bound, such that `qInt 1`, `qInt 2`, `P₄` and `k² P₄` satisfy
  `QED.TwoLoop.VPHalfAtAssembly.Good` for every flavour mass `M ≥ M_lo` and every `x ∈ (0, 1)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtAssembly

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested
open QED.WickModel (vacuumPolarizationFeynmanMass)

/-! ### Definitions -/

/-- The spectral mass `μ_x = √(M²/(x(1-x)))`. -/
noncomputable def specMu (M x : ℝ) : ℝ := Real.sqrt (M ^ 2 / (x * (1 - x)))

/-- The spectral prescription `ε/(x(1-x))`. -/
noncomputable def specEta (ε x : ℝ) : ℝ := ε / (x * (1 - x))

/-- The inner-loop denominator `M² + x(1-x)k² - iε`. -/
noncomputable def fDen (M ε x : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  ((vacuumPolarizationFeynmanMass M (Minkowski.dot ℓ ℓ) x : ℝ) : ℂ) - (ε : ℂ) * I

/-- The vertex with the model's photon pair squared, `N/(D D D_a D_b D_a D_b)`. -/
noncomputable def P4 (N : (Fin 4 → ℝ) → ℂ) (m a b ε : ℝ) (p' p : Fin 4 → ℝ) :
    (Fin 4 → ℝ) → ℂ :=
  prodIntegrand N m ![a, b, a, b] (fun _ => ε) ε p' p

/-- The vertex with a fifth photon denominator of mass `μ` and prescription `η`. -/
noncomputable def P5 (N : (Fin 4 → ℝ) → ℂ) (m a b μ ε η : ℝ) (p' p : Fin 4 → ℝ) :
    (Fin 4 → ℝ) → ℂ :=
  prodIntegrand N m ![a, b, a, b, μ] ![ε, ε, ε, ε, η] ε p' p

/-- `(k²)ʲ P₄(k) / (M² + x(1-x)k² - iε)`. -/
noncomputable def qInt (j : ℕ) (N : (Fin 4 → ℝ) → ℂ) (m a b M ε x : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    ℂ :=
  ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * P4 N m a b ε p' p ℓ / fDen M ε x ℓ

/-! ### Elementary facts -/

theorem mem_Ioo_mul_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < x * (1 - x) :=
  mul_pos hx.1 (by linarith [hx.2])

theorem mul_one_sub_le_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : x * (1 - x) ≤ 1 := by
  nlinarith [hx.1, hx.2]

theorem fDen_im (M ε x : ℝ) (ℓ : Fin 4 → ℝ) : (fDen M ε x ℓ).im = -ε := by
  simp only [fDen, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
  ring

theorem fDen_ne_zero (M : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) (ℓ : Fin 4 → ℝ) : fDen M ε x ℓ ≠ 0 := by
  intro h
  have := fDen_im M ε x ℓ
  rw [h, zero_im] at this
  linarith

theorem massShift_ne_zero (M : ℝ) {ε : ℝ} (hε : 0 < ε) : massShift M ε ≠ 0 := by
  intro h
  have : (massShift M ε).im = -ε := by
    simp only [massShift, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
    ring
  rw [h, zero_im] at this
  linarith

theorem norm_inv_massShift_le {M : ℝ} (ε : ℝ) (hM : 0 < M) :
    ‖(massShift M ε)⁻¹‖ ≤ (M ^ 2)⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ (by positivity) ?_
  have h := abs_re_le_norm (massShift M ε)
  simp only [massShift, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero] at h
  rw [abs_of_nonneg (sq_nonneg M)] at h
  exact h

theorem specMu_ge {M x : ℝ} (hM : 0 < M) (hx : x ∈ Ioo (0 : ℝ) 1) : M ≤ specMu M x := by
  have h0 := mem_Ioo_mul_pos hx
  have h1 := mul_one_sub_le_one hx
  unfold specMu
  rw [Real.le_sqrt hM.le (by positivity), le_div_iff₀ h0]
  nlinarith [sq_nonneg M]

theorem specEta_ge {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ Ioo (0 : ℝ) 1) : ε ≤ specEta ε x := by
  have h0 := mem_Ioo_mul_pos hx
  have h1 := mul_one_sub_le_one hx
  unfold specEta
  rw [le_div_iff₀ h0]
  nlinarith

/-- **The inner-loop denominator as a photon denominator** of mass `μ_x` and prescription
`ε/(x(1-x))`. -/
theorem denom_specMu {M ε x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ℓ : Fin 4 → ℝ) :
    denom (specMu M x) (specEta ε x) ℓ = fDen M ε x ℓ / ((x * (1 - x) : ℝ) : ℂ) := by
  have h0 := mem_Ioo_mul_pos hx
  have h0' : ((x * (1 - x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hx' : (x : ℂ) * (1 - x) ≠ 0 := by exact_mod_cast h0.ne'
  rw [eq_div_iff h0']
  unfold denom specMu specEta fDen vacuumPolarizationFeynmanMass
  rw [Real.sq_sqrt (by positivity)]
  push_cast
  have h1 : (M : ℂ) ^ 2 / (x * (1 - x)) * (x * (1 - x)) = M ^ 2 := div_mul_cancel₀ _ hx'
  have h2 : (ε : ℂ) / (x * (1 - x)) * (x * (1 - x)) = ε := div_mul_cancel₀ _ hx'
  linear_combination h1 - I * h2

theorem P5_eq (N : (Fin 4 → ℝ) → ℂ) (m a b μ ε η : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    P5 N m a b μ ε η p' p ℓ = P4 N m a b ε p' p ℓ * (denom μ η ℓ)⁻¹ := by
  unfold P5 P4 prodIntegrand
  rw [Fin.prod_univ_five, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The limit form**: `qInt j = (x(1-x))⁻¹ (k²)ʲ P₅(μ_x, ε/(x(1-x)))`. -/
theorem qInt_eq_lim (j : ℕ) (N : (Fin 4 → ℝ) → ℂ) (m a b M : ℝ) {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ioo (0 : ℝ) 1) (p' p ℓ : Fin 4 → ℝ) :
    qInt j N m a b M ε x p' p ℓ = ((x * (1 - x) : ℝ) : ℂ)⁻¹ *
      (((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * P5 N m a b (specMu M x) ε (specEta ε x) p' p ℓ) := by
  have h0 : ((x * (1 - x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero M hε x ℓ
  rw [qInt, P5_eq, denom_specMu hx]
  field_simp

/-- **The factored form**: `qInt j = (M² - iε)⁻¹ ((k²)ʲ P₄ - (k²)^{j+1} P₅(μ_x, ε/(x(1-x))))`. -/
theorem qInt_eq_fact (j : ℕ) (N : (Fin 4 → ℝ) → ℂ) (m a b M : ℝ) {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ioo (0 : ℝ) 1) (p' p ℓ : Fin 4 → ℝ) :
    qInt j N m a b M ε x p' p ℓ = (massShift M ε)⁻¹ *
      (((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * P4 N m a b ε p' p ℓ -
        ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ (j + 1) *
          P5 N m a b (specMu M x) ε (specEta ε x) p' p ℓ) := by
  have h0 : ((x * (1 - x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero M hε x ℓ
  have hS := massShift_ne_zero M hε
  rw [qInt, P5_eq, denom_specMu hx]
  have e : fDen M ε x ℓ =
      massShift M ε + ((x * (1 - x) : ℝ) : ℂ) * ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) := by
    simp only [fDen, massShift, vacuumPolarizationFeynmanMass]
    push_cast
    ring
  field_simp
  rw [e]
  ring

/-! ### The uniform bounds -/

section Bounds

variable {m a b Mlo : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- The arithmetic of the constants. -/
theorem const_bound {X T L c : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) (hL : 0 ≤ L) (hc : c ≤ L)
    (j : ℕ) (hj : j ≤ 2) :
    c * ((1 + T) ^ j * X + (1 + T) ^ (j + 1) * X) ≤ (1 + L) * (2 * (1 + T) ^ 3 * X) := by
  have hT1 : 1 ≤ 1 + T := by linarith
  have h1 : (1 + T) ^ j ≤ (1 + T) ^ 3 := pow_le_pow_right₀ hT1 (by omega)
  have h2 : (1 + T) ^ (j + 1) ≤ (1 + T) ^ 3 := pow_le_pow_right₀ hT1 (by omega)
  have h3 : (1 + T) ^ j * X + (1 + T) ^ (j + 1) * X ≤ 2 * (1 + T) ^ 3 * X := by
    have := mul_le_mul_of_nonneg_right h1 hX
    have := mul_le_mul_of_nonneg_right h2 hX
    linarith
  have h4 : 0 ≤ 2 * (1 + T) ^ 3 * X := by positivity
  calc c * ((1 + T) ^ j * X + (1 + T) ^ (j + 1) * X) ≤ L * (2 * (1 + T) ^ 3 * X) :=
        mul_le_mul hc h3 (by positivity) hL
    _ ≤ (1 + L) * (2 * (1 + T) ^ 3 * X) := by
        have := mul_le_mul_of_nonneg_right (by linarith : L ≤ 1 + L) h4
        linarith

/-- The factored form of `qInt j` is `Good`, from the bounds on its two terms. -/
theorem good_qInt_of {N : (Fin 4 → ℝ) → ℂ} {m a b M ε x K T L : ℝ} {p' p : Fin 4 → ℝ}
    {G : (Fin 3 → ℝ) → ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hinv : ‖(massShift M ε)⁻¹‖ ≤ L) (j : ℕ)
    (hj : j ≤ 2) (hε : 0 < ε) (hx : x ∈ Ioo (0 : ℝ) 1)
    (h4 : Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * P4 N m a b ε p' p ℓ)
      ((1 + T) ^ j * K) (fun v => (1 + T) ^ j * G v))
    (h5 : Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ (j + 1) *
        P5 N m a b (specMu M x) ε (specEta ε x) p' p ℓ)
      ((1 + T) ^ (j + 1) * K) (fun v => (1 + T) ^ (j + 1) * G v)) :
    Good (qInt j N m a b M ε x p' p) ((1 + L) * (2 * (1 + T) ^ 3 * K))
      (fun v => (1 + L) * (2 * (1 + T) ^ 3 * G v)) := by
  have hK := h4.1.nonneg_const
  have hT1 : 0 < 1 + T := by linarith
  have hK' : 0 ≤ K := (mul_nonneg_iff_of_pos_left (pow_pos hT1 j)).1 hK
  have hG : ∀ v, 0 ≤ G v := fun v => by
    have h := (norm_nonneg _).trans (h4.2 v 0)
    have h' := nonneg_of_mul_nonneg_left h (by positivity)
    exact (mul_nonneg_iff_of_pos_left (pow_pos hT1 j)).1 h'
  have h := (h4.sub h5).const_mul (massShift M ε)⁻¹
  refine (h.congr fun ℓ => (qInt_eq_fact j N m a b M hε hx p' p ℓ).symm).mono ?_ ?_
  · exact const_bound hK' hT hL hinv j hj
  · intro v
    exact const_bound (hG v) hT hL hinv j hj

/-- **The pieces are `Good` uniformly in the Feynman parameter and the flavour mass**: one
constant `C` for all `ε ∈ (0, 1]`; at each such `ε`, one pointwise bound `G`. -/
theorem exists_good_pieces (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hMlo : 0 < Mlo)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧
      Good (P4 N m a b ε p' p) C G ∧
      Good (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * P4 N m a b ε p' p ℓ) C G ∧
      ∀ M : ℝ, Mlo ≤ M → ∀ x ∈ Ioo (0 : ℝ) 1,
        Good (qInt 1 N m a b M ε x p' p) C G ∧ Good (qInt 2 N m a b M ε x p' p) C G := by
  set M₀ := min a (min b Mlo)
  have hM₀ : 0 < M₀ := lt_min ha (lt_min hb hMlo)
  have hM₀a : M₀ ≤ a := min_le_left _ _
  have hM₀b : M₀ ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hM₀M : M₀ ≤ Mlo := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K0, hK0, hK0'⟩ := exists_goodEF_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb 0
  obtain ⟨K1, hK1, hK1'⟩ := exists_goodEF_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb 1
  obtain ⟨K2, hK2, hK2'⟩ := exists_goodEF_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb 2
  obtain ⟨K3, hK3, hK3'⟩ := exists_goodEF_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb 3
  set K := K0 + K1 + K2 + K3
  have hK : 0 ≤ K := by positivity
  set T : ℝ := a ^ 2 + b ^ 2 + 1
  have hT0 : 0 ≤ T := by positivity
  set L : ℝ := (Mlo ^ 2)⁻¹
  have hL : 0 ≤ L := by positivity
  set C : ℝ := (1 + L) * (2 * (1 + T) ^ 3 * K)
  have hT1 : 1 ≤ 1 + T := by linarith
  refine ⟨C, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨G0, hG0, hG0'⟩ := exists_ptBd_prodIntegrand hNb m 0 hε hε p' p
  obtain ⟨G1, hG1, hG1'⟩ := exists_ptBd_prodIntegrand hNb m 1 hε hε p' p
  obtain ⟨G2, hG2, hG2'⟩ := exists_ptBd_prodIntegrand hNb m 2 hε hε p' p
  obtain ⟨G3, hG3, hG3'⟩ := exists_ptBd_prodIntegrand hNb m 3 hε hε p' p
  set G : (Fin 3 → ℝ) → ℝ := fun v => G0 v + G1 v + G2 v + G3 v
  have hG : ∀ v, 0 ≤ G v := fun v => by
    show 0 ≤ G0 v + G1 v + G2 v + G3 v
    linarith [hG0 v, hG1 v, hG2 v, hG3 v]
  set G' : (Fin 3 → ℝ) → ℝ := fun v => (1 + L) * (2 * (1 + T) ^ 3 * G v)
  -- every vertex with at most five photon denominators is `Good K G`
  have hall : ∀ (k : ℕ), k ≤ 3 → ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) →
      (∀ j, ε ≤ es j) → Good (prodIntegrand N m Ms es ε p' p) K G := by
    intro k hk Ms es hMs hes
    have hes' : ∀ j, 0 < es j := fun j => hε.trans_le (hes j)
    interval_cases k
    · exact (show Good _ K0 G0 from ⟨hK0' Ms es hMs hes' ε hε, hG0' Ms es hes⟩).mono
        (by show K0 ≤ K0 + K1 + K2 + K3; linarith)
        (fun v => by show G0 v ≤ G0 v + G1 v + G2 v + G3 v; linarith [hG1 v, hG2 v, hG3 v])
    · exact (show Good _ K1 G1 from ⟨hK1' Ms es hMs hes' ε hε, hG1' Ms es hes⟩).mono
        (by show K1 ≤ K0 + K1 + K2 + K3; linarith)
        (fun v => by show G1 v ≤ G0 v + G1 v + G2 v + G3 v; linarith [hG0 v, hG2 v, hG3 v])
    · exact (show Good _ K2 G2 from ⟨hK2' Ms es hMs hes' ε hε, hG2' Ms es hes⟩).mono
        (by show K2 ≤ K0 + K1 + K2 + K3; linarith)
        (fun v => by show G2 v ≤ G0 v + G1 v + G2 v + G3 v; linarith [hG0 v, hG1 v, hG3 v])
    · exact (show Good _ K3 G3 from ⟨hK3' Ms es hMs hes' ε hε, hG3' Ms es hes⟩).mono
        (by show K3 ≤ K0 + K1 + K2 + K3; linarith)
        (fun v => by show G3 v ≤ G0 v + G1 v + G2 v + G3 v; linarith [hG0 v, hG1 v, hG2 v])
  have hTa : ‖massShift a ε‖ ≤ T := by
    refine (norm_massShift_le hε.le).trans ?_
    show a ^ 2 + ε ≤ a ^ 2 + b ^ 2 + 1
    nlinarith [sq_nonneg b]
  have hTb : ‖massShift b ε‖ ≤ T := by
    refine (norm_massShift_le hε.le).trans ?_
    show b ^ 2 + ε ≤ a ^ 2 + b ^ 2 + 1
    nlinarith [sq_nonneg a]
  -- the model's four photon denominators
  have m4 : ∀ j, M₀ ≤ (![a, b, a, b] : Fin 4 → ℝ) j := by
    intro j; fin_cases j <;> simp [hM₀a, hM₀b]
  have e4 : ∀ j, ε ≤ (fun _ => ε : Fin 4 → ℝ) j := fun _ => le_rfl
  have g4 := hall 2 (by norm_num) _ _ m4 e4
  have g3 : Good (prodIntegrand N m (Fin.tail ![a, b, a, b]) (Fin.tail fun _ => ε) ε p' p) K G :=
    hall 1 (by norm_num) _ _ (fun j => m4 j.succ) (fun _ => le_rfl)
  have g2 : Good (prodIntegrand N m (Fin.tail (Fin.tail ![a, b, a, b]))
      (Fin.tail (Fin.tail fun _ => ε)) ε p' p) K G :=
    hall 0 (by norm_num) _ _ (fun j => m4 j.succ.succ) (fun _ => le_rfl)
  have s1P4 := good_s1 (k := 1) ![a, b, a, b] (fun _ => ε) hε hTa g3 g4
  have s2P4 := good_s2 (k := 0) ![a, b, a, b] (fun _ => ε) hε hε hT0 hTa hTb g2 g3 g4
  -- the bounds on the constants
  have c1 : (1 + T) * K ≤ C := by
    have : (1 + T) * K ≤ (1 + T) ^ 3 * K := by gcongr; exact le_self_pow₀ hT1 (by norm_num)
    have : (1 + T) ^ 3 * K ≤ 2 * (1 + T) ^ 3 * K := by nlinarith [pow_nonneg hT0 3]
    have : 2 * (1 + T) ^ 3 * K ≤ (1 + L) * (2 * (1 + T) ^ 3 * K) := by
      nlinarith [pow_nonneg hT0 3]
    linarith
  have c1G : ∀ v, (1 + T) * G v ≤ G' v := fun v => by
    have hv := hG v
    have h3 : 0 ≤ (1 + T) ^ 3 * G v := mul_nonneg (pow_nonneg (by linarith) 3) hv
    have : (1 + T) * G v ≤ (1 + T) ^ 3 * G v := by gcongr; exact le_self_pow₀ hT1 (by norm_num)
    have : 2 * (1 + T) ^ 3 * G v ≤ (1 + L) * (2 * (1 + T) ^ 3 * G v) :=
      le_mul_of_one_le_left (by linarith) (by linarith)
    show (1 + T) * G v ≤ (1 + L) * (2 * (1 + T) ^ 3 * G v)
    linarith
  have c0 : K ≤ C := le_trans (le_mul_of_one_le_left hK hT1) c1
  have c0G : ∀ v, G v ≤ G' v := fun v =>
    le_trans (le_mul_of_one_le_left (hG v) hT1) (c1G v)
  refine ⟨G', fun v => by have := hG v; positivity, g4.mono c0 c0G,
    s1P4.mono c1 c1G, fun M hM x hx => ?_⟩
  -- the five photon denominators
  have hMpos : 0 < M := hMlo.trans_le hM
  have m5 : ∀ j, M₀ ≤ (![a, b, a, b, specMu M x] : Fin 5 → ℝ) j := by
    intro j
    fin_cases j <;> simp [hM₀a, hM₀b]
    exact hM₀M.trans (hM.trans (specMu_ge hMpos hx))
  have e5 : ∀ j, ε ≤ (![ε, ε, ε, ε, specEta ε x] : Fin 5 → ℝ) j := by
    intro j
    fin_cases j <;> simp [specEta_ge hε hx]
  have f5 := hall 3 (by norm_num) _ _ m5 e5
  have f4 : Good (prodIntegrand N m (Fin.tail ![a, b, a, b, specMu M x])
      (Fin.tail ![ε, ε, ε, ε, specEta ε x]) ε p' p) K G :=
    hall 2 (by norm_num) _ _ (fun j => m5 j.succ) (fun j => e5 j.succ)
  have f3 : Good (prodIntegrand N m (Fin.tail (Fin.tail ![a, b, a, b, specMu M x]))
      (Fin.tail (Fin.tail ![ε, ε, ε, ε, specEta ε x])) ε p' p) K G :=
    hall 1 (by norm_num) _ _ (fun j => m5 j.succ.succ) (fun j => e5 j.succ.succ)
  have f2 : Good (prodIntegrand N m (Fin.tail (Fin.tail (Fin.tail ![a, b, a, b, specMu M x])))
      (Fin.tail (Fin.tail (Fin.tail ![ε, ε, ε, ε, specEta ε x]))) ε p' p) K G :=
    hall 0 (by norm_num) _ _ (fun j => m5 j.succ.succ.succ) (fun j => e5 j.succ.succ.succ)
  have s2P5 := good_s2 (k := 1) ![a, b, a, b, specMu M x] ![ε, ε, ε, ε, specEta ε x] hε hε hT0
    hTa hTb f3 f4 f5
  have s3P5 := good_s3 (k := 0) ![a, b, a, b, specMu M x] ![ε, ε, ε, ε, specEta ε x] hε hε hε
    hT0 hTa hTb hTa f2 f3 f4 f5
  have hinv := norm_inv_massShift_le ε hMpos
  have hLM : (M ^ 2)⁻¹ ≤ L := inv_anti₀ (by positivity) (pow_le_pow_left₀ hMlo.le hM 2)
  have hinv' : ‖(massShift M ε)⁻¹‖ ≤ L := hinv.trans hLM
  exact ⟨good_qInt_of hT0 hL hinv' 1 (by norm_num) hε hx
      (by simpa only [pow_one, P4] using s1P4) s2P5,
    good_qInt_of hT0 hL hinv' 2 (by norm_num) hε hx s2P4 s3P5⟩

end Bounds

end QED.TwoLoop.VPHalfAtAssembly

end
