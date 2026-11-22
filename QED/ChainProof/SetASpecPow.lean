/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecDecay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (a): repeated spectral insertions in the `ε → 0⁺` engine

Helper level for the fixed-`ε` spectral form of the two-loop vacuum polarization (set (a)
headline (HA₆)). A two-loop vacuum-polarization piece is, at fixed `ε`, a superposition of
`(k²)ʲ F⁻ʳ`, `F = M² + ξ(1-ξ) k² - iε` (`QED.ChainProof.SetASpec.setASpec_piece_eq_spectral`),
with `r` up to `4` and `j ≤ 2`. The generic engine
`QED.TwoLoop.VPHalfAtGen.exists_good_specInt` needs `j + r ≤ k + 2`, which the set (a) chain
(`k + 2 = 4` photon denominators) does not meet. This file proves the bound for **`r` copies of
one factor** with only `j ≤ k`:

* `F⁻ʳ = (ξ(1-ξ))⁻ʳ D_μ⁻ʳ`, `μ² = M²/(ξ(1-ξ))`, so `specInt` with `r` equal insertions is
  `(ξ(1-ξ))⁻ʳ` times `QED.TwoLoop.VPHalfAtGen.powInt` with `r` more photon denominators of mass
  `μ` (`saPow_specInt_const_eq`);
* the `GoodEF` constant of that `powInt` decays like `μ^{-2r}`
  (`saPow_exists_goodEF_powInt`, from `QED.ChainProof.SetASpec.saDec_exists_goodEF_prodIntegrand`
  and the absorption of `k²` by the first photon denominators), and
  `(ξ(1-ξ))⁻ʳ μ^{-2r} = M^{-2r} ≤ M_lo^{-2r}`;
* **`setASpec_exists_good_specPow`**: the vertex is `Good` with constants `(1 + T)ʲ K`,
  `(1 + T)ʲ G`, uniform in `ξ ∈ (0, 1)`, in the flavour mass `≥ M_lo` and in the photon masses
  `≥ M₀`, when the first `j` shifts are bounded by `T`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly
open QED.TwoLoop.VPHalfAtGen

/-! ### Reordering and appending photon denominators -/

theorem saPow_prodIntegrand_rev (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    prodIntegrand N m (fun i => Ms (Fin.rev i)) (fun i => es (Fin.rev i)) ε p' p ℓ =
      prodIntegrand N m Ms es ε p' p ℓ := by
  unfold prodIntegrand
  congr 2
  exact Fintype.prod_equiv Fin.revPerm _ _ fun i => rfl

/-- The photon masses (or prescriptions) `Ms` followed by `r` copies of `μ`. -/
def saAppend {k : ℕ} (r : ℕ) (Ms : Fin (k + 2) → ℝ) (μ : ℝ) : Fin (k + r + 2) → ℝ :=
  fun i => if h : (i : ℕ) < k + 2 then Ms ⟨i, h⟩ else μ

theorem saAppend_of_lt {k r : ℕ} (Ms : Fin (k + 2) → ℝ) (μ : ℝ) {i : Fin (k + r + 2)}
    (h : (i : ℕ) < k + 2) : saAppend r Ms μ i = Ms ⟨i, h⟩ := by
  simp [saAppend, h]

theorem saAppend_of_le {k r : ℕ} (Ms : Fin (k + 2) → ℝ) (μ : ℝ) {i : Fin (k + r + 2)}
    (h : k + 2 ≤ (i : ℕ)) : saAppend r Ms μ i = μ := by
  simp [saAppend, not_lt.2 h]

theorem saPow_prod_append {k r : ℕ} (f : Fin (k + r + 2) → ℂ) :
    ∏ i, f i = (∏ i : Fin (k + 2), f ⟨i, by omega⟩) * ∏ i : Fin r, f ⟨k + 2 + i, by omega⟩ := by
  have e : k + r + 2 = k + 2 + r := by omega
  rw [← Fin.prod_congr' f e.symm, Fin.prod_univ_add]
  rfl

/-- **`r` equal spectral insertions are `r` photon denominators of mass `μ_ξ`**, up to the factor
`(ξ(1-ξ))⁻ʳ`. -/
theorem saPow_specInt_const_eq (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k r : ℕ}
    (Ms es : Fin (k + 2) → ℝ) {Msp ξ ε : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    (p' p ℓ : Fin 4 → ℝ) :
    specInt N m j Ms es (fun _ : Fin r => Msp) (fun _ => ξ) ε p' p ℓ =
      (((ξ * (1 - ξ) : ℝ) : ℂ)⁻¹) ^ r *
        powInt N m j (saAppend r Ms (specMu Msp ξ)) (saAppend r es (specEta ε ξ)) ε p' p ℓ := by
  have hw : ((ξ * (1 - ξ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hξ).ne'
  have hD := fDen_ne_zero Msp hε ξ ℓ
  simp only [specInt, powInt, prodIntegrand]
  rw [saPow_prod_append]
  have h1 : ∀ i : Fin (k + 2),
      (denom (saAppend r Ms (specMu Msp ξ) ⟨i, by omega⟩)
        (saAppend r es (specEta ε ξ) ⟨i, by omega⟩) ℓ)⁻¹ = (denom (Ms i) (es i) ℓ)⁻¹ := by
    intro i
    rw [saAppend_of_lt _ _ (by simp), saAppend_of_lt _ _ (by simp)]
  have h2 : ∀ i : Fin r,
      (denom (saAppend r Ms (specMu Msp ξ) ⟨k + 2 + i, by omega⟩)
        (saAppend r es (specEta ε ξ) ⟨k + 2 + i, by omega⟩) ℓ)⁻¹ =
        ((ξ * (1 - ξ) : ℝ) : ℂ) * (fDen Msp ε ξ ℓ)⁻¹ := by
    intro i
    rw [saAppend_of_le _ _ (by simp), saAppend_of_le _ _ (by simp), denom_specMu hξ]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_congr rfl fun i _ => h2 i,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [inv_pow]
  field_simp

/-! ### Large-mass decay with the photon denominators in any position -/

section Bounds

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- The decay `K μ^{-2r}` when the **last** `r ≤ k` photon masses are at least `μ`. -/
theorem saPow_exists_goodEF_prodIntegrand_last (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : ℝ, 0 < μ → ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) →
      (∀ j, 0 < es j) → (∀ j : Fin (k + 2), k + 2 ≤ (j : ℕ) + r → μ ≤ Ms j) →
      ∀ ε : ℝ, 0 < ε → GoodEF (prodIntegrand N m Ms es ε p' p) (K * ((μ ^ 2) ^ r)⁻¹) := by
  obtain ⟨K, hK, h⟩ := saDec_exists_goodEF_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    hr hrk
  refine ⟨K, hK, fun μ hμ Ms es hMs hes hheavy ε hε => ?_⟩
  have g := h μ hμ (fun i => Ms (Fin.rev i)) (fun i => es (Fin.rev i)) (fun i => hMs _)
    (fun i => hes _) (fun i hi => hheavy _ (by rw [Fin.val_rev]; omega)) ε hε
  exact g.congr fun ℓ => saPow_prodIntegrand_rev N m Ms es ε p' p ℓ

/-- **The decay of the `GoodEF` constant for `(k²)ʲ` over `k + 2` denominators**, the last `r`
of mass at least `μ`, `j + r ≤ k`: the constant is `(1 + T)ʲ K μ^{-2r}` whenever the first `j`
shifts are bounded by `T`. -/
theorem saPow_exists_goodEF_powInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {r : ℕ} (hr : 1 ≤ r) :
    ∀ (j k : ℕ), j + r ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ μ : ℝ, 0 < μ →
      ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, M₀ ≤ Ms i) → (∀ i, 0 < es i) →
      (∀ i : Fin (k + 2), k + 2 ≤ (i : ℕ) + r → μ ≤ Ms i) →
      (∀ i : Fin (k + 2), (i : ℕ) < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      ∀ ε : ℝ, 0 < ε →
      GoodEF (powInt N m j Ms es ε p' p) ((1 + T) ^ j * K * ((μ ^ 2) ^ r)⁻¹) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    obtain ⟨K, hK, h⟩ := saPow_exists_goodEF_prodIntegrand_last hm hM₀ hp' hp hp0' hp0 hNc
      hNq hNb hr (by omega : r ≤ k)
    refine ⟨K, hK, fun T _ μ hμ Ms es hMs hes hheavy _ ε hε => ?_⟩
    exact ((h μ hμ Ms es hMs hes hheavy ε hε).congr fun ℓ =>
      (powInt_zero N m Ms es ε p' p ℓ).symm).mono' (by simp)
  | succ j ih =>
    intro k hjk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨K1, hK1, h1⟩ := ih k (by omega)
    obtain ⟨K2, hK2, h2⟩ := ih (k + 1) (by omega)
    refine ⟨K1 + K2, by positivity, fun T hT μ hμ Ms es hMs hes hheavy hTs ε hε => ?_⟩
    have g1 := h1 T hT μ hμ (Fin.tail Ms) (Fin.tail es) (fun i => hMs _) (fun i => hes _)
      (fun i hi => hheavy i.succ (by simp; omega)) (fun i hi => hTs i.succ (by simp; omega))
      ε hε
    have g2 := h2 T hT μ hμ Ms es hMs hes hheavy (fun i hi => hTs i (by omega)) ε hε
    have t0 : ‖massShift (Ms 0) (es 0)‖ ≤ T := hTs 0 (by simp)
    have h := g1.sub (g2.const_mul (massShift (Ms 0) (es 0)))
    refine (h.congr fun ℓ => (powInt_succ N m j Ms es (hes 0) ε p' p ℓ).symm).mono' ?_
    set Z : ℝ := ((μ ^ 2) ^ r)⁻¹
    have hZ : 0 ≤ Z := by positivity
    have hTj : 0 ≤ (1 + T) ^ j := by positivity
    have a : ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2) ≤ T * ((1 + T) ^ j * K2) :=
      mul_le_mul_of_nonneg_right t0 (by positivity)
    have b : (1 + T) ^ j * K1 ≤ (1 + T) ^ j * ((1 + T) * K1) := by
      gcongr; nlinarith
    have c : T * ((1 + T) ^ j * K2) ≤ (1 + T) ^ j * ((1 + T) * K2) := by
      have : T * K2 ≤ (1 + T) * K2 := by nlinarith
      nlinarith
    have key : (1 + T) ^ j * K1 + ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2) ≤
        (1 + T) ^ (j + 1) * (K1 + K2) := by
      calc (1 + T) ^ j * K1 + ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2)
          ≤ (1 + T) ^ j * ((1 + T) * K1) + (1 + T) ^ j * ((1 + T) * K2) := by linarith
        _ = (1 + T) ^ (j + 1) * (K1 + K2) := by ring
    calc (1 + T) ^ j * K1 * Z + ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2 * Z)
        = ((1 + T) ^ j * K1 + ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2)) * Z := by ring
      _ ≤ (1 + T) ^ (j + 1) * (K1 + K2) * Z := mul_le_mul_of_nonneg_right key hZ

theorem saPow_norm_inv_fDen_le (M : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) (ℓ : Fin 4 → ℝ) :
    ‖(fDen M ε x ℓ)⁻¹‖ ≤ ε⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ hε ?_
  have h := abs_im_le_norm (fDen M ε x ℓ)
  rw [fDen_im, abs_neg, abs_of_pos hε] at h
  exact h

theorem saPow_specMu_sq {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    specMu M x ^ 2 = M ^ 2 / (x * (1 - x)) := by
  have h0 := mem_Ioo_mul_pos hx
  rw [specMu, Real.sq_sqrt (by positivity)]

/-- **The engine for `r` copies of one spectral insertion**: for `j ≤ k`, `specInt` with `r`
equal insertions is `Good` with constants `(1 + T)ʲ K`, `(1 + T)ʲ G`, uniform in the Feynman
parameter `ξ ∈ (0, 1)`, in the flavour mass `≥ M_lo` and in the photon masses `≥ M₀`, when the
first `j` shifts are bounded by `T`. No condition on `r`: the `r` insertions are absorbed by
the decay `μ^{-2r}` of their own photon-type denominators. -/
theorem setASpec_exists_good_specPow (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Mlo : ℝ} (hMlo : M₀ ≤ Mlo) :
    ∀ (r j k : ℕ), j ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ ε e₀ : ℝ, 0 < ε → 0 < e₀ → e₀ ≤ ε →
      ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, M₀ ≤ Ms i) → (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), (i : ℕ) < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      ∀ Msp ξ : ℝ, Mlo ≤ Msp → ξ ∈ Ioo (0 : ℝ) 1 →
      Good (specInt N m j Ms es (fun _ : Fin r => Msp) (fun _ => ξ) ε p' p)
        ((1 + T) ^ j * K) (fun v => (1 + T) ^ j * G v) := by
  intro r j k hjk
  have hMlo0 : 0 < Mlo := hM₀.trans_le hMlo
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨K, hK, h⟩ := exists_good_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb j k hjk
    refine ⟨K, hK, fun ε e₀ hε he₀ _ => ?_⟩
    obtain ⟨G, hG, hg⟩ := h ε e₀ hε he₀
    exact ⟨G, hG, fun T hT Ms es hMs hes hTs Msp ξ _ _ =>
      (hg T hT Ms es hMs hes hTs).congr fun ℓ => by simp [specInt]⟩
  obtain ⟨K1, hK1, hEF⟩ := saPow_exists_goodEF_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (r := r) hr j (k + r) (by omega)
  refine ⟨K1 * ((Mlo ^ 2) ^ r)⁻¹, by positivity, fun ε e₀ hε he₀ he₀ε => ?_⟩
  obtain ⟨G0, hG0, hPt⟩ := exists_ptBd_powInt (N := N) hNb m hε he₀ p' p j k hjk
  refine ⟨fun v => (ε⁻¹) ^ r * G0 v, fun v => by have := hG0 v; positivity,
    fun T hT Ms es hMs hes hTs Msp ξ hMsp hξ => ⟨?_, ?_⟩⟩
  · -- the `GoodEF` bound, from the decay
    have hw := mem_Ioo_mul_pos hξ
    set μ := specMu Msp ξ
    set η := specEta ε ξ
    have hμ : Mlo ≤ μ := hMsp.trans (specMu_ge (hMlo0.trans_le hMsp) hξ)
    have hη : ε ≤ η := specEta_ge hε hξ
    have g := hEF T hT μ (hMlo0.trans_le hμ) (saAppend r Ms μ) (saAppend r es η)
      (fun i => by
        by_cases h : (i : ℕ) < k + 2
        · rw [saAppend_of_lt _ _ h]; exact hMs _
        · rw [saAppend_of_le _ _ (not_lt.1 h)]; exact hMlo.trans hμ)
      (fun i => by
        by_cases h : (i : ℕ) < k + 2
        · rw [saAppend_of_lt _ _ h]; exact he₀.trans_le (hes _)
        · rw [saAppend_of_le _ _ (not_lt.1 h)]; exact hε.trans_le hη)
      (fun i hi => by rw [saAppend_of_le _ _ (by omega)])
      (fun i hi => by
        rw [saAppend_of_lt _ _ (by omega), saAppend_of_lt _ _ (by omega)]
        exact hTs _ hi)
      ε hε
    have g' := (g.const_mul ((((ξ * (1 - ξ) : ℝ) : ℂ)⁻¹) ^ r)).congr fun ℓ =>
      (saPow_specInt_const_eq N m j Ms es hξ hε p' p ℓ).symm
    refine g'.mono' ?_
    have hnorm : ‖(((ξ * (1 - ξ) : ℝ) : ℂ)⁻¹) ^ r‖ = ((ξ * (1 - ξ))⁻¹) ^ r := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    have hμsq : μ ^ 2 = Msp ^ 2 / (ξ * (1 - ξ)) := saPow_specMu_sq hξ
    have hMsp0 : 0 < Msp := hMlo0.trans_le hMsp
    have e : ((ξ * (1 - ξ))⁻¹) ^ r * ((1 + T) ^ j * K1 * ((μ ^ 2) ^ r)⁻¹) =
        (1 + T) ^ j * K1 * ((Msp ^ 2) ^ r)⁻¹ := by
      have hw' : (ξ * (1 - ξ)) ^ r ≠ 0 := pow_ne_zero _ hw.ne'
      rw [hμsq, div_pow, inv_pow]
      field_simp
    rw [hnorm, e]
    have : (Mlo ^ 2) ^ r ≤ (Msp ^ 2) ^ r := by gcongr
    calc (1 + T) ^ j * K1 * ((Msp ^ 2) ^ r)⁻¹ ≤ (1 + T) ^ j * K1 * ((Mlo ^ 2) ^ r)⁻¹ := by
          gcongr
      _ = (1 + T) ^ j * (K1 * ((Mlo ^ 2) ^ r)⁻¹) := by ring
  · -- the pointwise bound
    intro v t
    have a := hPt T hT Ms es hes hTs v t
    have hprod : ‖∏ _i : Fin r, (fDen Msp ε ξ (Fin.cons t v : Fin 4 → ℝ))⁻¹‖ ≤ (ε⁻¹) ^ r := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (saPow_norm_inv_fDen_le Msp hε ξ _) r
    simp only [specInt]
    rw [norm_mul]
    have hT1 : 0 ≤ (1 + T) ^ j := by positivity
    have hG0v := hG0 v
    calc ‖powInt N m j Ms es ε p' p (Fin.cons t v : Fin 4 → ℝ)‖ *
          ‖∏ _i : Fin r, (fDen Msp ε ξ (Fin.cons t v : Fin 4 → ℝ))⁻¹‖
        ≤ ((1 + T) ^ j * G0 v * (1 + t ^ 2)⁻¹) * (ε⁻¹) ^ r := by gcongr
      _ = (1 + T) ^ j * ((ε⁻¹) ^ r * G0 v) * (1 + t ^ 2)⁻¹ := by ring

end Bounds

end QED.ChainProof.SetASpec

end
