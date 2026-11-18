/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitPhoton
public import QED.TwoLoop.VPHalfOneLoop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The spectral-component vertex with arbitrary prescriptions, and its value

The third layer of the analytic engine for the `ε → 0⁺` limit of the vacuum-polarization class
in closed form (obligation O2-8 at the `ε → 0` level), specialized to the Pauli-projected
Feynman-gauge chain `Pg(k) = QED.TwoLoop.VPUnitNested.pauliChain` of the outer one-loop vertex.

* `pauliChain_eq_sum`, `continuous_pauliChain`, `pauliChain_quadratic`, `pauliChain_bound`: `Pg` is
  a fixed linear combination of the entries of the frozen vertex numerator, so it is continuous,
  quadratic in the loop energy with constant leading coefficient, and of quadratic growth: it
  satisfies the hypotheses of the engine of `QED/TwoLoop/VPHalfAtLimitEngine.lean`.
* `s2Prod5Integrand`: `N(k) (k²)² / (D_m(p'+k) D_m(p+k) ∏_{j<5} D_{M_j}(k; ε_j))`, five photon
  denominators with **arbitrary** prescriptions `ε_j` (electron prescription `ε`). With
  `k² = D_{M_j} - t_j`, `t_j = M_j² - iε_j`, it is a combination of four products of photon
  denominators with coefficients `1, -t₀, -t₁, t₀ t₁` (`s2Prod5Integrand_eq`), so its
  energy-first integral tends to `s2Prod5Limit`, independent of the prescriptions
  (`tendsto_energyFirstIntegral_s2Prod5Integrand`).
* **The value** (`s2Prod5Limit_pauliChain_eq_kern5`): for five distinct positive squared masses,
  comparison with the frozen one-loop vertex at a common prescription
  (`QED.TwoLoop.VPHalf.tendsto_efi_perVIntegrand`) gives
  `s2Prod5Limit = i (e q² (4m² + q²)²/m) (e²/(8π²)) ∫ kern5 m a b c d μ q²`, and by continuity in
  the masses (`s2Prod5Limit_pauliChain_eq_kernVP`) the repeated photon pair `(a, b, a, b)` of the
  model gives `∫ kernVP m a b μ q²`. Repeated photon masses need no separate treatment.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtLimit

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit QED.TwoLoop.Bridge QED.TwoLoop.Insertion
open QED.TwoLoop.VPHalf (kern5 kernVP tendsto_integral_kern5)

/-! ### The Pauli-projected chain as a numerator -/

/-- `Pg(k) = ∑_{μ i j} κ w_{μij} N_{μij}(k)`, with `N` the frozen vertex numerator. -/
theorem pauliChain_eq_sum (e m : ℝ) (p' p k : Fin 4 → ℝ) :
    pauliChain e m p' p k = ∑ μ, ∑ i, ∑ j,
      (pauliWt m p' p μ i j * kappa e) * vertexNumerator m p' p μ k i j := by
  rw [pauliChain, pauliNum_eq_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  simp only [vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gPhoton,
    vertexNumerator, electronNumerator, kappa, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  ring

theorem continuous_pauliChain (e m : ℝ) (p' p : Fin 4 → ℝ) :
    Continuous (pauliChain e m p' p) := by
  have h : pauliChain e m p' p = fun k => ∑ μ, ∑ i, ∑ j,
      (pauliWt m p' p μ i j * kappa e) * vertexNumerator m p' p μ k i j :=
    funext fun k => pauliChain_eq_sum e m p' p k
  rw [h]
  exact continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_vertexNumerator m p' p μ i j)

theorem pauliChain_quadratic (e m : ℝ) (p' p : Fin 4 → ℝ) :
    ∃ α : ℂ, ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ := by
  choose α hα using fun (x : Fin 4 × Fin 4 × Fin 4) =>
    exists_vertexNumerator_quadratic m p' p x.1 x.2.1 x.2.2
  set c : Fin 4 → Fin 4 → Fin 4 → ℂ := fun μ i j => pauliWt m p' p μ i j * kappa e
  refine ⟨∑ μ, ∑ i, ∑ j, c μ i j * α (μ, i, j), fun v => ?_⟩
  choose β γ h using fun (x : Fin 4 × Fin 4 × Fin 4) => hα x v
  refine ⟨∑ μ, ∑ i, ∑ j, c μ i j * β (μ, i, j), ∑ μ, ∑ i, ∑ j, c μ i j * γ (μ, i, j),
    fun t => ?_⟩
  rw [pauliChain_eq_sum]
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [h (μ, i, j) t]
  ring

theorem pauliChain_bound (e m : ℝ) (p' p : Fin 4 → ℝ) :
    ∃ C : ℝ, ∀ ℓ : Fin 4 → ℝ, ‖pauliChain e m p' p ℓ‖ ≤ C * (1 + ‖ℓ‖) ^ 2 := by
  choose C hC using fun (x : Fin 4 × Fin 4 × Fin 4) =>
    exists_norm_vertexNumerator_le m p' p x.1 x.2.1 x.2.2
  refine ⟨∑ μ, ∑ i, ∑ j, ‖pauliWt m p' p μ i j * kappa e‖ * C (μ, i, j), fun ℓ => ?_⟩
  rw [pauliChain_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC (μ, i, j) ℓ) (norm_nonneg _)

/-! ### Five photon denominators and `(k²)²` -/

/-- `N(k) (k²)² / (D_m(p'+k) D_m(p+k) ∏_{j<5} D_{M_j}(k; ε_j))`. -/
noncomputable def s2Prod5Integrand (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms es : Fin 5 → ℝ) (ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * ((denom m ε (p' + ℓ) * denom m ε (p + ℓ))⁻¹ * ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 2 *
    ∏ j, (denom (Ms j) (es j) ℓ)⁻¹)

/-- The shift `t = M² - iε` with `k² = D_M(k; ε) - t`. -/
noncomputable def massShift (M e : ℝ) : ℂ := ((M ^ 2 : ℝ) : ℂ) - (e : ℂ) * I

theorem denom_eq_add_massShift (M e : ℝ) (ℓ : Fin 4 → ℝ) :
    denom M e ℓ = ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) + massShift M e := by
  simp only [denom, massShift]; push_cast; ring

theorem denom_ne_zero_of_pos {M e : ℝ} (he : 0 < e) (ℓ : Fin 4 → ℝ) : denom M e ℓ ≠ 0 := by
  intro h
  have := denom_im M e ℓ
  rw [h, zero_im] at this
  linarith

/-- **The reduction of `(k²)²` against the first two photon denominators.** -/
theorem s2Prod5Integrand_eq (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms : Fin 5 → ℝ) {es : Fin 5 → ℝ}
    (hes : ∀ j, 0 < es j) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    s2Prod5Integrand N m Ms es ε p' p ℓ =
      prodIntegrand N m ![Ms 2, Ms 3, Ms 4] ![es 2, es 3, es 4] ε p' p ℓ
        - massShift (Ms 0) (es 0) *
          prodIntegrand N m ![Ms 0, Ms 2, Ms 3, Ms 4] ![es 0, es 2, es 3, es 4] ε p' p ℓ
        - massShift (Ms 1) (es 1) *
          prodIntegrand N m ![Ms 1, Ms 2, Ms 3, Ms 4] ![es 1, es 2, es 3, es 4] ε p' p ℓ
        + massShift (Ms 0) (es 0) * massShift (Ms 1) (es 1) *
          prodIntegrand N m Ms es ε p' p ℓ := by
  have h0 := denom_ne_zero_of_pos (M := Ms 0) (hes 0) ℓ
  have h1 := denom_ne_zero_of_pos (M := Ms 1) (hes 1) ℓ
  have e0 := denom_eq_add_massShift (Ms 0) (es 0) ℓ
  have e1 := denom_eq_add_massShift (Ms 1) (es 1) ℓ
  simp only [s2Prod5Integrand, prodIntegrand]
  rw [Fin.prod_univ_five]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    mul_one]
  set s : ℂ := ((Minkowski.dot ℓ ℓ : ℝ) : ℂ)
  have hs : s = denom (Ms 0) (es 0) ℓ - massShift (Ms 0) (es 0) := by rw [e0]; ring
  have hs' : s = denom (Ms 1) (es 1) ℓ - massShift (Ms 1) (es 1) := by rw [e1]; ring
  have hsq : s ^ 2 = (denom (Ms 0) (es 0) ℓ - massShift (Ms 0) (es 0)) *
      (denom (Ms 1) (es 1) ℓ - massShift (Ms 1) (es 1)) := by
    rw [sq]; nth_rewrite 1 [hs]; rw [hs']
  rw [hsq]
  field_simp
  ring

theorem efInt_prodIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    EFInt (prodIntegrand N m Ms es ε p' p) :=
  ⟨(energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε).1,
    (energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε).2.1⟩

/-- The limit of the `(k²)²`, five-denominator vertex. -/
noncomputable def s2Prod5Limit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (Ms : Fin 5 → ℝ)
    (p' p : Fin 4 → ℝ) : ℂ :=
  prodLimit α N m ![Ms 2, Ms 3, Ms 4] p' p
    - ((Ms 0 ^ 2 : ℝ) : ℂ) * prodLimit α N m ![Ms 0, Ms 2, Ms 3, Ms 4] p' p
    - ((Ms 1 ^ 2 : ℝ) : ℂ) * prodLimit α N m ![Ms 1, Ms 2, Ms 3, Ms 4] p' p
    + ((Ms 0 ^ 2 : ℝ) : ℂ) * ((Ms 1 ^ 2 : ℝ) : ℂ) * prodLimit α N m Ms p' p

theorem tendsto_massShift {ι : Type*} {l : Filter ι} (M : ℝ) {e : ι → ℝ}
    (he : Tendsto e l (𝓝 0)) :
    Tendsto (fun i => massShift M (e i)) l (𝓝 ((M ^ 2 : ℝ) : ℂ)) := by
  have h : Tendsto (fun i => ((e i : ℝ) : ℂ) * I) l (𝓝 0) := by
    simpa using ((continuous_ofReal.tendsto 0).comp he).mul_const I
  have := (tendsto_const_nhds (x := ((M ^ 2 : ℝ) : ℂ))).sub h
  rw [sub_zero] at this
  exact this

/-- **The limit of the `(k²)²`, five-denominator vertex**, for arbitrary prescriptions on the
photon lines tending to `0⁺` (and `ε → 0⁺` on the electron lines). -/
theorem tendsto_energyFirstIntegral_s2Prod5Integrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Ms : Fin 5 → ℝ} (hMs : ∀ j, M₀ ≤ Ms j)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ}
    {es : ι → Fin 5 → ℝ} (hε : Tendsto ε l (𝓝[>] 0))
    (hes : ∀ j, Tendsto (fun i => es i j) l (𝓝[>] 0)) :
    Tendsto (fun i => energyFirstIntegral (s2Prod5Integrand N m Ms (es i) (ε i) p' p)) l
      (𝓝 (s2Prod5Limit α N m Ms p' p)) := by
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε self_mem_nhdsWithin
  have hespos : ∀ᶠ i in l, ∀ j, 0 < es i j :=
    eventually_all.2 fun j => (hes j) self_mem_nhdsWithin
  have hes0 : ∀ j, Tendsto (fun i => es i j) l (𝓝 0) := fun j =>
    (hes j).mono_right nhdsWithin_le_nhds
  have hsub : ∀ (k : ℕ) (σ : Fin (k + 2) → Fin 5), Tendsto
      (fun i => energyFirstIntegral (prodIntegrand N m (Ms ∘ σ) (es i ∘ σ) (ε i) p' p)) l
      (𝓝 (prodLimit α N m (Ms ∘ σ) p' p)) := fun k σ =>
    tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
      (fun j => hMs (σ j)) hε (fun j => hes (σ j))
  have l1 := hsub 1 ![2, 3, 4]
  have l2 := hsub 2 ![0, 2, 3, 4]
  have l3 := hsub 2 ![1, 2, 3, 4]
  have l4 := hsub 3 id
  have hlim := (((l1.sub ((tendsto_massShift (Ms 0) (hes0 0)).mul l2)).sub
    ((tendsto_massShift (Ms 1) (hes0 1)).mul l3)).add
    (((tendsto_massShift (Ms 0) (hes0 0)).mul (tendsto_massShift (Ms 1) (hes0 1))).mul l4))
  have c1 : ∀ x : Fin 5 → ℝ, x ∘ (![2, 3, 4] : Fin 3 → Fin 5) = ![x 2, x 3, x 4] := fun x => by
    funext j; fin_cases j <;> rfl
  have c2 : ∀ x : Fin 5 → ℝ, x ∘ (![0, 2, 3, 4] : Fin 4 → Fin 5) = ![x 0, x 2, x 3, x 4] :=
    fun x => by funext j; fin_cases j <;> rfl
  have c3 : ∀ x : Fin 5 → ℝ, x ∘ (![1, 2, 3, 4] : Fin 4 → Fin 5) = ![x 1, x 2, x 3, x 4] :=
    fun x => by funext j; fin_cases j <;> rfl
  simp only [c1, c2, c3, Function.comp_id] at hlim
  have hval : prodLimit α N m ![Ms 2, Ms 3, Ms 4] p' p
      - ((Ms 0 ^ 2 : ℝ) : ℂ) * prodLimit α N m ![Ms 0, Ms 2, Ms 3, Ms 4] p' p
      - ((Ms 1 ^ 2 : ℝ) : ℂ) * prodLimit α N m ![Ms 1, Ms 2, Ms 3, Ms 4] p' p
      + ((Ms 0 ^ 2 : ℝ) : ℂ) * ((Ms 1 ^ 2 : ℝ) : ℂ) * prodLimit α N m Ms p' p =
      s2Prod5Limit α N m Ms p' p := rfl
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hεpos, hespos] with i h1 h2
  have i1 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 2, Ms 3, Ms 4]) (es := ![es i 2, es i 3, es i 4])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact h2 _) h1
  have i2 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 0, Ms 2, Ms 3, Ms 4]) (es := ![es i 0, es i 2, es i 3, es i 4])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact h2 _) h1
  have i3 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![Ms 1, Ms 2, Ms 3, Ms 4]) (es := ![es i 1, es i 2, es i 3, es i 4])
    (fun j => by fin_cases j <;> exact hMs _) (fun j => by fin_cases j <;> exact h2 _) h1
  have i4 := efInt_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := Ms) (es := es i) hMs h2 h1
  have hF : s2Prod5Integrand N m Ms (es i) (ε i) p' p = fun ℓ =>
      ((prodIntegrand N m ![Ms 2, Ms 3, Ms 4] ![es i 2, es i 3, es i 4] (ε i) p' p ℓ
        + (-massShift (Ms 0) (es i 0)) *
          prodIntegrand N m ![Ms 0, Ms 2, Ms 3, Ms 4] ![es i 0, es i 2, es i 3, es i 4] (ε i) p' p ℓ)
        + (-massShift (Ms 1) (es i 1)) *
          prodIntegrand N m ![Ms 1, Ms 2, Ms 3, Ms 4] ![es i 1, es i 2, es i 3, es i 4] (ε i) p' p ℓ)
        + (massShift (Ms 0) (es i 0) * massShift (Ms 1) (es i 1)) *
          prodIntegrand N m Ms (es i) (ε i) p' p ℓ := by
    funext ℓ
    rw [s2Prod5Integrand_eq N m Ms h2 (ε i) p' p ℓ]
    ring
  rw [hF, efi_add (((i1.add (i2.const_mul _)).add (i3.const_mul _))) (i4.const_mul _),
    efi_add (i1.add (i2.const_mul _)) (i3.const_mul _), efi_add i1 (i2.const_mul _),
    efi_const_mul, efi_const_mul, efi_const_mul]
  ring

/-! ### The value: comparison with the frozen one-loop vertex -/

theorem propDenom_eq_denom (M ε : ℝ) (k : Fin 4 → ℝ) : propDenom M ε k = denom M ε k := by
  simp only [propDenom, denom]

theorem perVIntegrand_eq_s2Prod5 (e m a b c d μ ε : ℝ) (p' p k : Fin 4 → ℝ) :
    QED.TwoLoop.VPHalf.perVIntegrand e m a b c d μ ε p' p k =
      s2Prod5Integrand (pauliChain e m p' p) m ![a, b, c, d, μ] (fun _ => ε) ε p' p k := by
  simp only [QED.TwoLoop.VPHalf.perVIntegrand, s2Prod5Integrand, propDenom_eq_denom,
    Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, mul_inv]
  ring

/-- **The value for five distinct squared masses.** -/
theorem s2Prod5Limit_pauliChain_eq_kern5 (e : ℝ) {m a b c d μ : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hμ : 0 < μ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ^ 2 ≠ b ^ 2)
    (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2) (haμ : a ^ 2 ≠ μ ^ 2) (hbc : b ^ 2 ≠ c ^ 2)
    (hbd : b ^ 2 ≠ d ^ 2) (hbμ : b ^ 2 ≠ μ ^ 2) (hcd : c ^ 2 ≠ d ^ 2) (hcμ : c ^ 2 ≠ μ ^ 2)
    (hdμ : d ^ 2 ≠ μ ^ 2) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    s2Prod5Limit α (pauliChain e m p' p) m ![a, b, c, d, μ] p' p =
      I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kern5 m a b c d μ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  set M₀ := min a (min b (min c (min d μ)))
  have hM₀ : 0 < M₀ := lt_min ha (lt_min hb (lt_min hc (lt_min hd hμ)))
  have hMs : ∀ j, M₀ ≤ (![a, b, c, d, μ] : Fin 5 → ℝ) j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have h1 := tendsto_energyFirstIntegral_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0
    (continuous_pauliChain e m p' p) hα hCN hMs (l := 𝓝[>] (0 : ℝ)) (ε := id)
    (es := fun ε _ => ε) tendsto_id (fun _ => tendsto_id)
  have h2 := QED.TwoLoop.VPHalf.tendsto_efi_perVIntegrand e hm ha hb hc hd hμ hp' hp hp0' hp0 hq
    hab hac had haμ hbc hbd hbμ hcd hcμ hdμ
  have hfun : ∀ ε, QED.TwoLoop.VPHalf.perVIntegrand e m a b c d μ ε p' p =
      s2Prod5Integrand (pauliChain e m p' p) m ![a, b, c, d, μ] (fun _ => ε) ε p' p := fun ε =>
    funext (perVIntegrand_eq_s2Prod5 e m a b c d μ ε p' p)
  simp only [hfun] at h2
  exact tendsto_nhds_unique h1 h2

/-- **The value for the model's repeated photon pair** `(a, b, a, b)` and a spectral mass `μ`
different from `a` and `b`: `∫ kernVP`. -/
theorem s2Prod5Limit_pauliChain_eq_kernVP (e : ℝ) {m a b μ : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) (hμ : 0 < μ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ≠ b) (haμ : a ≠ μ)
    (hbμ : b ≠ μ) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    s2Prod5Limit α (pauliChain e m p' p) m ![a, b, a, b, μ] p' p =
      I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kernVP m a b μ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  set q2 := Minkowski.dot (p' - p) (p' - p)
  set M₀ := min a (min b μ)
  have hM₀ : 0 < M₀ := lt_min ha (lt_min hb hμ)
  set Ms : ℝ → Fin 5 → ℝ := fun t => ![a, b, a + t, b + t, μ]
  have hsq : ∀ {x y : ℝ}, 0 < x → 0 < y → x ≠ y → x ^ 2 ≠ y ^ 2 := fun hx hy h h2 =>
    h ((sq_eq_sq₀ hx.le hy.le).1 h2)
  -- the masses for small `t > 0`
  set δ := min |b - a| (min |μ - a| |μ - b|)
  have hδ : 0 < δ := lt_min (abs_pos.2 (sub_ne_zero.2 hab.symm))
    (lt_min (abs_pos.2 (sub_ne_zero.2 haμ.symm)) (abs_pos.2 (sub_ne_zero.2 hbμ.symm)))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < δ :=
    (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ht).and
      (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  have hδ1 : δ ≤ |b - a| := min_le_left _ _
  have hδ2 : δ ≤ |μ - a| := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ |μ - b| := (min_le_right _ _).trans (min_le_right _ _)
  have hval : ∀ᶠ t in 𝓝[>] (0 : ℝ), s2Prod5Limit α (pauliChain e m p' p) m (Ms t) p' p =
      I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) * ∫ z, kern5 m a b (a + t) (b + t) μ q2 z ∂feynmanMeasure : ℝ) :
          ℂ) := by
    filter_upwards [hev] with t ⟨ht0, htδ⟩
    have n1 : a + t ≠ b := fun h => by
      have : |b - a| = t := by rw [← h]; simp [abs_of_pos ht0]
      linarith
    have n2 : b + t ≠ a := fun h => by
      have : |b - a| = t := by rw [← h]; simp [abs_of_pos ht0]
      linarith
    have n3 : a + t ≠ μ := fun h => by
      have : |μ - a| = t := by rw [← h]; simp [abs_of_pos ht0]
      linarith
    have n4 : b + t ≠ μ := fun h => by
      have : |μ - b| = t := by rw [← h]; simp [abs_of_pos ht0]
      linarith
    have hat : 0 < a + t := by linarith
    have hbt : 0 < b + t := by linarith
    exact s2Prod5Limit_pauliChain_eq_kern5 e hm ha hb hat hbt hμ hp' hp hp0' hp0 hq
      (hsq ha hb hab) (hsq ha hat (by linarith)) (hsq ha hbt n2.symm) (hsq ha hμ haμ)
      (hsq hb hat n1.symm) (hsq hb hbt (by linarith)) (hsq hb hμ hbμ)
      (hsq hat hbt (fun h => hab (by linarith))) (hsq hat hμ n3) (hsq hbt hμ n4) hα
  -- continuity on both sides
  have hadd : ∀ r : ℝ, Tendsto (fun t : ℝ => r + t) (𝓝[>] 0) (𝓝 r) := fun r => by
    have h : Tendsto (fun t : ℝ => r + t) (𝓝 0) (𝓝 (r + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hge : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, M₀ ≤ Ms t j := by
    filter_upwards [hev] with t ⟨ht0, _⟩
    intro j
    have h1 : M₀ ≤ a := min_le_left _ _
    have h2 : M₀ ≤ b := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : M₀ ≤ μ := (min_le_right _ _).trans (min_le_right _ _)
    fin_cases j <;> simp [Ms] <;> linarith
  have hT : ∀ σ : Fin 5 → Fin 5, ∀ (k : ℕ) (τ : Fin (k + 2) → Fin 5),
      Tendsto (fun t => Ms t ∘ τ) (𝓝[>] 0) (𝓝 (![a, b, a, b, μ] ∘ τ)) := by
    intro _ k τ
    refine tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_apply, Ms]
    generalize τ j = r
    fin_cases r
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact hadd a
    · exact hadd b
    · exact tendsto_const_nhds
  have hgeσ : ∀ (k : ℕ) (τ : Fin (k + 2) → Fin 5),
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, M₀ ≤ (Ms t ∘ τ) j :=
    fun k τ => hge.mono fun t ht j => ht (τ j)
  have hP : ∀ (k : ℕ) (τ : Fin (k + 2) → Fin 5),
      Tendsto (fun t => prodLimit α (pauliChain e m p' p) m (Ms t ∘ τ) p' p) (𝓝[>] 0)
        (𝓝 (prodLimit α (pauliChain e m p' p) m (![a, b, a, b, μ] ∘ τ) p' p)) :=
    fun k τ => tendsto_prodLimit hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) α hCN
      (hT id k τ) (hgeσ k τ)
  have c1 : ∀ x : Fin 5 → ℝ, x ∘ (![2, 3, 4] : Fin 3 → Fin 5) = ![x 2, x 3, x 4] := fun x => by
    funext j; fin_cases j <;> rfl
  have c2 : ∀ x : Fin 5 → ℝ, x ∘ (![0, 2, 3, 4] : Fin 4 → Fin 5) = ![x 0, x 2, x 3, x 4] :=
    fun x => by funext j; fin_cases j <;> rfl
  have c3 : ∀ x : Fin 5 → ℝ, x ∘ (![1, 2, 3, 4] : Fin 4 → Fin 5) = ![x 1, x 2, x 3, x 4] :=
    fun x => by funext j; fin_cases j <;> rfl
  have l1 := hP 1 ![2, 3, 4]
  have l2 := hP 2 ![0, 2, 3, 4]
  have l3 := hP 2 ![1, 2, 3, 4]
  have l4 := hP 3 id
  simp only [c1, c2, c3, Function.comp_id] at l1 l2 l3 l4
  have hL : Tendsto (fun t => s2Prod5Limit α (pauliChain e m p' p) m (Ms t) p' p) (𝓝[>] 0)
      (𝓝 (s2Prod5Limit α (pauliChain e m p' p) m ![a, b, a, b, μ] p' p)) := by
    have := ((l1.sub (l2.const_mul ((a ^ 2 : ℝ) : ℂ))).sub (l3.const_mul ((b ^ 2 : ℝ) : ℂ))).add
      (l4.const_mul (((a ^ 2 : ℝ) : ℂ) * ((b ^ 2 : ℝ) : ℂ)))
    simpa [s2Prod5Limit, Ms] using this
  have hK := tendsto_integral_kern5 (μ := μ) ha hb hm hq.le (fun t => a + t) (fun t => b + t)
    (hadd a) (hadd b) (l := 𝓝[>] (0 : ℝ))
  have hR : Tendsto (fun t => I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
      ((e ^ 2 / (8 * π ^ 2) * ∫ z, kern5 m a b (a + t) (b + t) μ q2 z ∂feynmanMeasure : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP m a b μ q2 z ∂feynmanMeasure : ℝ) : ℂ))) :=
    ((continuous_ofReal.tendsto _).comp (hK.const_mul _)).const_mul _
  exact tendsto_nhds_unique hL (hR.congr' (hval.mono fun t ht => ht.symm))

end QED.TwoLoop.VPHalfAtLimit

end
