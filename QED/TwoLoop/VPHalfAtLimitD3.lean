/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitPauli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The `k²`, four-photon-denominator vertex with arbitrary prescriptions, and its value

The companion of `QED/TwoLoop/VPHalfAtLimitPauli.lean` for the photon factor `k²/∏_{j<4} D_j` of
the constant (`Π_loop(0)`-type) part of the vacuum-polarization class in closed form
(obligation O2-8 at the `ε → 0` level).

* `s1Prod4Integrand`: `N(k) k² / (D_m(p'+k) D_m(p+k) ∏_{j<4} D_{M_j}(k; ε_j))`, arbitrary photon
  prescriptions. With `k² = D_{M₀} - t₀` it is `prodIntegrand (M₁, M₂, M₃) - t₀ prodIntegrand (M)`
  (`s1Prod4Integrand_eq`), so its energy-first integral tends to `s1Prod4Limit`, independent of
  the prescriptions (`tendsto_energyFirstIntegral_s1Prod4Integrand`).
* `tendsto_efi_d3Integrand`: for four distinct squared masses and a common prescription, the
  partial fractions `QED.TwoLoop.VPUnitNested.pf_four` and the frozen one-loop vertex give the
  limit `i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ kern4 m a b c d q²`.
* **The value** (`s1Prod4Limit_pauliChain_eq_kern4`, `s1Prod4Limit_pauliChain_eq_kernD3`): by
  uniqueness of limits, and for the repeated pair `(a, b, a, b)` by continuity in the masses,
  `s1Prod4Limit = i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ kernD3 m a b q²`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtLimit

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit QED.TwoLoop.Bridge QED.TwoLoop.Insertion

/-! ### Four photon denominators and `k²` -/

/-- `N(k) k² / (D_m(p'+k) D_m(p+k) ∏_{j<4} D_{M_j}(k; ε_j))`. -/
noncomputable def s1Prod4Integrand (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms es : Fin 4 → ℝ) (ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * ((denom m ε (p' + ℓ) * denom m ε (p + ℓ))⁻¹ * ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) *
    ∏ j, (denom (Ms j) (es j) ℓ)⁻¹)

theorem s1Prod4Integrand_eq (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms : Fin 4 → ℝ) {es : Fin 4 → ℝ}
    (hes : ∀ j, 0 < es j) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    s1Prod4Integrand N m Ms es ε p' p ℓ =
      prodIntegrand N m ![Ms 1, Ms 2, Ms 3] ![es 1, es 2, es 3] ε p' p ℓ
        - massShift (Ms 0) (es 0) * prodIntegrand N m Ms es ε p' p ℓ := by
  have h0 := denom_ne_zero_of_pos (M := Ms 0) (hes 0) ℓ
  have e0 := denom_eq_add_massShift (Ms 0) (es 0) ℓ
  simp only [s1Prod4Integrand, prodIntegrand]
  rw [Fin.prod_univ_four]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    mul_one]
  have hs : ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) = denom (Ms 0) (es 0) ℓ - massShift (Ms 0) (es 0) := by
    rw [e0]; ring
  rw [hs]
  field_simp

/-- The limit of the `k²`, four-denominator vertex. -/
noncomputable def s1Prod4Limit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms : Fin 4 → ℝ)
    (p' p : Fin 4 → ℝ) : ℂ :=
  prodLimit α N m ![Ms 1, Ms 2, Ms 3] p' p - ((Ms 0 ^ 2 : ℝ) : ℂ) * prodLimit α N m Ms p' p

theorem tendsto_energyFirstIntegral_s1Prod4Integrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Ms : Fin 4 → ℝ} (hMs : ∀ j, M₀ ≤ Ms j)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ}
    {es : ι → Fin 4 → ℝ} (hε : Tendsto ε l (𝓝[>] 0))
    (hes : ∀ j, Tendsto (fun i => es i j) l (𝓝[>] 0)) :
    Tendsto (fun i => energyFirstIntegral (s1Prod4Integrand N m Ms (es i) (ε i) p' p)) l
      (𝓝 (s1Prod4Limit α N m Ms p' p)) := by
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε self_mem_nhdsWithin
  have hespos : ∀ᶠ i in l, ∀ j, 0 < es i j :=
    eventually_all.2 fun j => (hes j) self_mem_nhdsWithin
  have hes0 : ∀ j, Tendsto (fun i => es i j) l (𝓝 0) := fun j =>
    (hes j).mono_right nhdsWithin_le_nhds
  have l1 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := Ms ∘ (![1, 2, 3] : Fin 3 → Fin 4)) (fun j => hMs _) hε
    (es := fun i => es i ∘ (![1, 2, 3] : Fin 3 → Fin 4)) (fun j => hes _)
  have l2 := tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    hMs hε hes
  have c1 : ∀ x : Fin 4 → ℝ, x ∘ (![1, 2, 3] : Fin 3 → Fin 4) = ![x 1, x 2, x 3] := fun x => by
    funext j; fin_cases j <;> rfl
  simp only [c1] at l1
  have hlim := l1.sub ((tendsto_massShift (Ms 0) (hes0 0)).mul l2)
  refine hlim.congr' ?_
  filter_upwards [hεpos, hespos] with i h1 h2
  have i1 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 1, Ms 2, Ms 3]) (es := ![es i 1, es i 2, es i 3])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact h2 _) h1
  have i2 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := Ms) (es := es i) hMs h2 h1
  have hF : s1Prod4Integrand N m Ms (es i) (ε i) p' p = fun ℓ =>
      prodIntegrand N m ![Ms 1, Ms 2, Ms 3] ![es i 1, es i 2, es i 3] (ε i) p' p ℓ
        + (-massShift (Ms 0) (es i 0)) * prodIntegrand N m Ms (es i) (ε i) p' p ℓ := by
    funext ℓ
    rw [s1Prod4Integrand_eq N m Ms h2 (ε i) p' p ℓ]
    ring
  rw [hF, efi_add i1 (i2.const_mul _), efi_const_mul]
  ring

/-! ### The value: comparison with the frozen one-loop vertex -/

/-- The scalar `k²`, four-mass integrand at a common prescription, in `propDenom` form. -/
noncomputable def d3Integrand (e m a b c d ε : ℝ) (p' p k : Fin 4 → ℝ) : ℂ :=
  pauliChain e m p' p k * ((Minkowski.dot k k : ℝ) : ℂ) *
    ((propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹ * (propDenom a ε k)⁻¹ *
      (propDenom b ε k)⁻¹ * (propDenom c ε k)⁻¹ * (propDenom d ε k)⁻¹)

theorem d3Integrand_eq_s1Prod4 (e m a b c d ε : ℝ) (p' p k : Fin 4 → ℝ) :
    d3Integrand e m a b c d ε p' p k =
      s1Prod4Integrand (pauliChain e m p' p) m ![a, b, c, d] (fun _ => ε) ε p' p k := by
  simp only [d3Integrand, s1Prod4Integrand, propDenom_eq_denom, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_inv]
  ring

/-- Partial fractions of the four-mass integrand into Pauli-projected frozen integrands. -/
theorem d3Integrand_eq (e m : ℝ) {a b c d ε : ℝ} (hε : ε ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2)
    (hcd : c ^ 2 ≠ d ^ 2) (p' p k : Fin 4 → ℝ) :
    d3Integrand e m a b c d ε p' p k =
      (((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2) : ℝ) : ℂ)⁻¹ *
          (((b ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a b ε p' p μ k) +
        (((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) : ℝ) : ℂ)⁻¹ *
          (((c ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a c ε p' p μ k) +
        (((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) : ℝ) : ℂ)⁻¹ *
          (((d ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a d ε p' p μ k) := by
  rw [pauliNum_vertexIntegrand _ _ _ _ hε, pauliNum_vertexIntegrand _ _ _ _ hε,
    pauliNum_vertexIntegrand _ _ _ _ hε]
  unfold d3Integrand
  set w : ℂ := ((Minkowski.dot k k : ℝ) : ℂ) - (ε : ℂ) * I
  have hD : ∀ M : ℝ, propDenom M ε k = w + ((M ^ 2 : ℝ) : ℂ) := fun M => propDenom_eq_add M ε k
  have hne : ∀ M : ℝ, w + ((M ^ 2 : ℝ) : ℂ) ≠ 0 := fun M => by
    rw [← hD]; exact propDenom_ne_zero hε k
  have hcast : ∀ {u v : ℝ}, u ≠ v → ((u : ℝ) : ℂ) ≠ ((v : ℝ) : ℂ) := fun h => by exact_mod_cast h
  have hpf := pf_four (w := w) (e := (ε : ℂ) * I) (hne a) (hne b) (hne c) (hne d)
    (hcast hab) (hcast hac) (hcast had) (hcast hbc) (hcast hbd) (hcast hcd)
  have hk : ((Minkowski.dot k k : ℝ) : ℂ) = w + (ε : ℂ) * I := by simp only [w]; ring
  rw [hD a, hD b, hD c, hD d, hk]
  set Pg := pauliChain e m p' p k
  set E := (propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹
  push_cast at hpf ⊢
  linear_combination (Pg * E : ℂ) * hpf

/-- **The `ε → 0⁺` limit of the four-mass integrand**, distinct squared masses. -/
theorem tendsto_efi_d3Integrand (e : ℝ) {m a b c d : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ^ 2 ≠ b ^ 2) (hac : a ^ 2 ≠ c ^ 2)
    (had : a ^ 2 ≠ d ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2) (hcd : c ^ 2 ≠ d ^ 2) :
    Tendsto (fun ε => energyFirstIntegral (d3Integrand e m a b c d ε p' p)) (𝓝[>] 0)
      (𝓝 (I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kern4 m a b c d (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ))) := by
  set cb : ℂ := (((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2) : ℝ) : ℂ)⁻¹
  set cc : ℂ := (((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) : ℝ) : ℂ)⁻¹
  set cd : ℂ := (((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) : ℝ) : ℂ)⁻¹
  have l1 := ((tendsto_sub_mul_I ((b ^ 2 : ℝ) : ℂ)).const_mul cb).mul
    (tendsto_efi_pauliVI (e := e) hm ha hb hp' hp hp0' hp0)
  have l2 := ((tendsto_sub_mul_I ((c ^ 2 : ℝ) : ℂ)).const_mul cc).mul
    (tendsto_efi_pauliVI (e := e) hm ha hc hp' hp hp0' hp0)
  have l3 := ((tendsto_sub_mul_I ((d ^ 2 : ℝ) : ℂ)).const_mul cd).mul
    (tendsto_efi_pauliVI (e := e) hm ha hd hp' hp hp0' hp0)
  have hlim := (l1.add l2).add l3
  have hval : cb * ((b ^ 2 : ℝ) : ℂ) * (I * pauliNum m p' p
        (QED.OneLoop.vertexOneLoop e m a b hm ha hb p' p hp' hp hp0' hp0)) +
      cc * ((c ^ 2 : ℝ) : ℂ) * (I * pauliNum m p' p
        (QED.OneLoop.vertexOneLoop e m a c hm ha hc p' p hp' hp hp0' hp0)) +
      cd * ((d ^ 2 : ℝ) : ℂ) * (I * pauliNum m p' p
        (QED.OneLoop.vertexOneLoop e m a d hm ha hd p' p hp' hp hp0' hp0)) =
      I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kern4 m a b c d (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) := by
    rw [pauliNum_vertexOneLoop e hm ha hb hp' hp hp0' hp0 hq,
      pauliNum_vertexOneLoop e hm ha hc hp' hp hp0' hp0 hq,
      pauliNum_vertexOneLoop e hm ha hd hp' hp hp0' hp0 hq,
      QED.OneLoop.VertexLimit.formFactorB_eq hp' hp, QED.OneLoop.VertexLimit.formFactorB_eq hp' hp,
      QED.OneLoop.VertexLimit.formFactorB_eq hp' hp,
      ← sum_mul_integral_pauliIntegrand_eq hm hq.le hab hac had hbc hbd hcd]
    simp only [cb, cc, cd]
    push_cast
    ring
  rw [← hval]
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  have hFε : d3Integrand e m a b c d ε p' p = fun k =>
      cb * (((b ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a b ε p' p μ k) +
        cc * (((c ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a c ε p' p μ k) +
        cd * (((d ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          pauliNum m p' p (fun μ => QED.OneLoop.vertexIntegrand e m a d ε p' p μ k) :=
    funext fun k => d3Integrand_eq e m hε.ne' hab hac had hbc hbd hcd p' p k
  have i1 := (efInt_pauliVI (e := e) hm ha hb hp' hp hp0' hp0 hε).const_mul
    (cb * (((b ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
  have i2 := (efInt_pauliVI (e := e) hm ha hc hp' hp hp0' hp0 hε).const_mul
    (cc * (((c ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
  have i3 := (efInt_pauliVI (e := e) hm ha hd hp' hp hp0' hp0 hε).const_mul
    (cd * (((d ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I))
  show _ = energyFirstIntegral (d3Integrand e m a b c d ε p' p)
  rw [hFε, efi_add (i1.add i2) i3, efi_add i1 i2, efi_const_mul, efi_const_mul, efi_const_mul]

/-- **The value for four distinct squared masses.** -/
theorem s1Prod4Limit_pauliChain_eq_kern4 (e : ℝ) {m a b c d : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ^ 2 ≠ b ^ 2)
    (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2)
    (hcd : c ^ 2 ≠ d ^ 2) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    s1Prod4Limit α (pauliChain e m p' p) m ![a, b, c, d] p' p =
      I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kern4 m a b c d (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  set M₀ := min a (min b (min c d))
  have hM₀ : 0 < M₀ := lt_min ha (lt_min hb (lt_min hc hd))
  have hMs : ∀ j, M₀ ≤ (![a, b, c, d] : Fin 4 → ℝ) j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1 := tendsto_energyFirstIntegral_s1Prod4Integrand hm hM₀ hp' hp hp0' hp0
    (continuous_pauliChain e m p' p) hα hCN hMs (l := 𝓝[>] (0 : ℝ)) (ε := id)
    (es := fun ε _ => ε) tendsto_id (fun _ => tendsto_id)
  have h2 := tendsto_efi_d3Integrand e hm ha hb hc hd hp' hp hp0' hp0 hq hab hac had hbc hbd hcd
  have hfun : ∀ ε, d3Integrand e m a b c d ε p' p =
      s1Prod4Integrand (pauliChain e m p' p) m ![a, b, c, d] (fun _ => ε) ε p' p := fun ε =>
    funext (d3Integrand_eq_s1Prod4 e m a b c d ε p' p)
  simp only [hfun] at h2
  exact tendsto_nhds_unique h1 h2

/-- **The value for the model's repeated photon pair** `(a, b, a, b)`: `∫ kernD3`. -/
theorem s1Prod4Limit_pauliChain_eq_kernD3 (e : ℝ) {m a b : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ≠ b) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    s1Prod4Limit α (pauliChain e m p' p) m ![a, b, a, b] p' p =
      I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kernD3 m a b (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  set q2 := Minkowski.dot (p' - p) (p' - p)
  set M₀ := min a b
  have hM₀ : 0 < M₀ := lt_min ha hb
  set Ms : ℝ → Fin 4 → ℝ := fun t => ![a, b, a + t, b + t]
  have hsq : ∀ {x y : ℝ}, 0 < x → 0 < y → x ≠ y → x ^ 2 ≠ y ^ 2 := fun hx hy h h2 =>
    h ((sq_eq_sq₀ hx.le hy.le).1 h2)
  set δ := |b - a|
  have hδ : 0 < δ := abs_pos.2 (sub_ne_zero.2 hab.symm)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < δ :=
    (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ht).and
      (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  have hval : ∀ᶠ t in 𝓝[>] (0 : ℝ), s1Prod4Limit α (pauliChain e m p' p) m (Ms t) p' p =
      I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) * ∫ z, kern4 m a b (a + t) (b + t) q2 z ∂feynmanMeasure : ℝ) :
          ℂ) := by
    filter_upwards [hev] with t ⟨ht0, htδ⟩
    have n1 : a + t ≠ b := fun h => by
      have : |b - a| = t := by rw [← h]; simp [abs_of_pos ht0]
      linarith
    have n2 : b + t ≠ a := fun h => by
      have : |b - a| = t := by rw [← h]; simp [abs_of_pos ht0]
      linarith
    have hat : 0 < a + t := by linarith
    have hbt : 0 < b + t := by linarith
    exact s1Prod4Limit_pauliChain_eq_kern4 e hm ha hb hat hbt hp' hp hp0' hp0 hq
      (hsq ha hb hab) (hsq ha hat (by linarith)) (hsq ha hbt n2.symm)
      (hsq hb hat n1.symm) (hsq hb hbt (by linarith))
      (hsq hat hbt (fun h => hab (by linarith))) hα
  have hadd : ∀ r : ℝ, Tendsto (fun t : ℝ => r + t) (𝓝[>] 0) (𝓝 r) := fun r => by
    have h : Tendsto (fun t : ℝ => r + t) (𝓝 0) (𝓝 (r + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hge : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, M₀ ≤ Ms t j := by
    filter_upwards [hev] with t ⟨ht0, _⟩
    intro j
    have h1 : M₀ ≤ a := min_le_left _ _
    have h2 : M₀ ≤ b := min_le_right _ _
    fin_cases j <;> simp [Ms] <;> linarith
  have hT : ∀ (k : ℕ) (τ : Fin (k + 2) → Fin 4),
      Tendsto (fun t => Ms t ∘ τ) (𝓝[>] 0) (𝓝 (![a, b, a, b] ∘ τ)) := by
    intro k τ
    refine tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_apply, Ms]
    generalize τ j = r
    fin_cases r
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact hadd a
    · exact hadd b
  have hP : ∀ (k : ℕ) (τ : Fin (k + 2) → Fin 4),
      Tendsto (fun t => prodLimit α (pauliChain e m p' p) m (Ms t ∘ τ) p' p) (𝓝[>] 0)
        (𝓝 (prodLimit α (pauliChain e m p' p) m (![a, b, a, b] ∘ τ) p' p)) :=
    fun k τ => tendsto_prodLimit hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) α hCN
      (hT k τ) (hge.mono fun t ht j => ht (τ j))
  have c1 : ∀ x : Fin 4 → ℝ, x ∘ (![1, 2, 3] : Fin 3 → Fin 4) = ![x 1, x 2, x 3] := fun x => by
    funext j; fin_cases j <;> rfl
  have l1 := hP 1 ![1, 2, 3]
  have l2 := hP 2 id
  simp only [c1, Function.comp_id] at l1 l2
  have hL : Tendsto (fun t => s1Prod4Limit α (pauliChain e m p' p) m (Ms t) p' p) (𝓝[>] 0)
      (𝓝 (s1Prod4Limit α (pauliChain e m p' p) m ![a, b, a, b] p' p)) := by
    have := l1.sub (l2.const_mul ((a ^ 2 : ℝ) : ℂ))
    simpa [s1Prod4Limit, Ms] using this
  have hK := tendsto_integral_kern4 (l := 𝓝[>] (0 : ℝ)) ha hb hm hq.le (fun t => a + t)
    (fun t => b + t) (hadd a) (hadd b)
  have hR : Tendsto (fun t => I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
      ((e ^ 2 / (8 * π ^ 2) * ∫ z, kern4 m a b (a + t) (b + t) q2 z ∂feynmanMeasure : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) * ∫ z, kernD3 m a b q2 z ∂feynmanMeasure : ℝ) : ℂ))) :=
    ((continuous_ofReal.tendsto _).comp (hK.const_mul _)).const_mul _
  exact tendsto_nhds_unique hL (hR.congr' (hval.mono fun t ht => ht.symm))

end QED.TwoLoop.VPHalfAtLimit

end
