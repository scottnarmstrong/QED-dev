/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBBubble
public import QED.Integration.ThreeLoopRotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Factor bounds for the bubble–bubble integrand at rotated energies

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53).

* Inverse denominators: on the rectangle `QED.Integration.ThreeLoop.rotRect h`,
  `‖D⁻¹‖ ≤ K/(1 + t²)` (`norm_inv_denC_rect`), and at `z = 1 + s i`,
  `‖D⁻¹‖ ≤ 3K/(1 + |t| + |y|)²` (`norm_inv_denC_rot`); in both cases no denominator vanishes
  (`nz_rect`, `nz_rot`).
* Electron propagators: `‖S‖ ≤ C/(1 + |t|)` on the rectangle at fixed spatial momentum
  (`exists_epC_rect`), and `‖S‖ ≤ C/(1 + |t| + |y|)` at `1 + s i` (`exists_epC_rot`).
* The structural bounds of `phC`, `outerChainC`, `chainOuterC`, `vpC` and `bbC` by their factors.
-/

@[expose] public section

open Complex QED.Integration.ThreeLoop

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-! ### Inverse denominators -/

/-- The constant of `one_add_sq_le_rect`. -/
noncomputable def kRect (a Y ε : ℝ) : ℝ := 8 + 2 * (1 + 8 * (a ^ 2 + Y + ε)) / ε

/-- The constant of `one_add_sq_add_le_rot`. -/
noncomputable def kRot (s a ε : ℝ) : ℝ := 1 + 3 / s + 2 * (1 + 2 * a ^ 2) / ε

theorem kRect_pos {a Y ε : ℝ} (hY : 0 ≤ Y) (hε : 0 < ε) : 0 < kRect a Y ε := by
  unfold kRect; positivity

theorem kRot_pos {s a ε : ℝ} (hs : 0 < s) (hε : 0 < ε) : 0 < kRot s a ε := by
  unfold kRot; positivity

theorem norm_inv_le_of_le {N K S : ℝ} (hK : 0 < K) (hS : 0 < S) (h : S ≤ K * N) :
    N⁻¹ ≤ K / S := by
  have hN : 0 < N := by
    by_contra hN
    have hN' : N ≤ 0 := not_lt.mp hN
    nlinarith
  rw [inv_le_comm₀ hN (by positivity), inv_div, div_le_iff₀ hK]
  linarith

theorem norm_inv_denC_rect {z : ℂ} {h : ℝ} (hz : z ∈ rotRect h) {a ε : ℝ} (hε : 0 < ε)
    (ha : h * a ^ 2 ≤ ε / 4) (M : ℝ) (y : Fin 3 → ℝ) (t : ℝ) {X : ℂ} (hX : X = z * t + a) :
    ‖(denC M ε (mk X y))⁻¹‖ ≤ kRect a (sq3 y + M ^ 2) ε / (1 + t ^ 2) := by
  have hY : 0 ≤ sq3 y + M ^ 2 := add_nonneg (sq3_nonneg y) (sq_nonneg M)
  have key := one_add_sq_le_rect hz.1 hz.2.2.1 hz.2.2.2 hε ha hY t
  rw [norm_inv, denC_mk, hX]
  exact norm_inv_le_of_le (kRect_pos hY hε) (by positivity) key

theorem nz_rect {z : ℂ} {h : ℝ} (hz : z ∈ rotRect h) {a ε : ℝ} (hε : 0 < ε)
    (ha : h * a ^ 2 ≤ ε / 4) (y : Fin 3 → ℝ) (t : ℝ) {X : ℂ} (hX : X = z * t + a) :
    NZ ε (mk X y) := by
  intro M h0
  have hY : 0 ≤ sq3 y + M ^ 2 := add_nonneg (sq3_nonneg y) (sq_nonneg M)
  have key := one_add_sq_le_rect hz.1 hz.2.2.1 hz.2.2.2 hε ha hY t
  rw [denC_mk, hX] at h0
  rw [h0, norm_zero, mul_zero] at key
  nlinarith [sq_nonneg t]

theorem one_add_abs_add_norm_sq_le (t : ℝ) (y : Fin 3 → ℝ) (M : ℝ) :
    (1 + |t| + ‖y‖) ^ 2 ≤ 3 * (1 + t ^ 2 + (sq3 y + M ^ 2)) := by
  have h1 := norm_sq_le_sq3 y
  have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [sq_nonneg (|t| - ‖y‖), sq_nonneg (1 - |t|), sq_nonneg (1 - ‖y‖), sq_nonneg M,
    abs_nonneg t, norm_nonneg y]

theorem norm_inv_denC_rot {s a ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (ha : s * a ^ 2 ≤ ε / 4)
    (M : ℝ) (y : Fin 3 → ℝ) (t : ℝ) {X : ℂ} (hX : X = (1 + s * I) * t + a) :
    ‖(denC M ε (mk X y))⁻¹‖ ≤ 3 * kRot s a ε / (1 + |t| + ‖y‖) ^ 2 := by
  have hY : 0 ≤ sq3 y + M ^ 2 := add_nonneg (sq3_nonneg y) (sq_nonneg M)
  have key := one_add_sq_add_le_rot (Y := sq3 y + M ^ 2) hs hε ha t
  rw [norm_inv, denC_mk, hX]
  refine norm_inv_le_of_le (by have := kRot_pos (a := a) hs hε; positivity) (by positivity) ?_
  have := one_add_abs_add_norm_sq_le t y M
  unfold kRot at key ⊢
  nlinarith

theorem nz_rot {s a ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (ha : s * a ^ 2 ≤ ε / 4)
    (y : Fin 3 → ℝ) (t : ℝ) {X : ℂ} (hX : X = (1 + s * I) * t + a) : NZ ε (mk X y) := by
  intro M h0
  have hY : 0 ≤ sq3 y + M ^ 2 := add_nonneg (sq3_nonneg y) (sq_nonneg M)
  have key := one_add_sq_add_le_rot (Y := sq3 y + M ^ 2) hs hε ha t
  rw [denC_mk, hX] at h0
  rw [h0, norm_zero, mul_zero] at key
  nlinarith [sq_nonneg t]

/-! ### Electron propagators -/

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem norm_le_of_mem_rotRect {z : ℂ} {h : ℝ} (hz : z ∈ rotRect h) (hh : h ≤ 1) : ‖z‖ ≤ 3 := by
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [abs_of_pos (by linarith [hz.1]), abs_of_nonneg hz.2.2.1]
  linarith [hz.2.1, hz.2.2.2]

theorem norm_rot_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) : ‖(1 + s * I : ℂ)‖ ≤ 2 := by
  refine (norm_add_le _ _).trans ?_
  simp [abs_of_nonneg hs]
  linarith

theorem exists_epC_rect (M ε a : ℝ) (y : Fin 3 → ℝ) (hε : 0 < ε) {h : ℝ} (hh : h ≤ 1)
    (ha : h * a ^ 2 ≤ ε / 4) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ rotRect h, ∀ (t : ℝ) (X : ℂ), X = z * t + a →
      ‖epC M ε (mk X y)‖ ≤ C * (1 + |t|)⁻¹ := by
  set K := kRect a (sq3 y + M ^ 2) ε
  have hK : 0 < K := kRect_pos (add_nonneg (sq3_nonneg y) (sq_nonneg M)) hε
  set N0 := |M| * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ)‖ + 4 * gammaBound * (4 * (|a| + ‖y‖))
  set N1 := 4 * gammaBound * (4 * 3)
  have hG := gammaBound_nonneg
  have hN0 : 0 ≤ N0 := by positivity
  have hN1 : 0 ≤ N1 := by positivity
  refine ⟨2 * K * (N0 + N1), by positivity, fun z hz t X hX => ?_⟩
  have hzn := norm_le_of_mem_rotRect hz hh
  have hXn : ‖X‖ ≤ 3 * |t| + |a| := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
  have hnum : ‖numC M (mk X y)‖ ≤ N0 + N1 * |t| := by
    refine (norm_numC_le M fun ν => (norm_mk_le X y ν).trans (le_refl _)).trans ?_
    have : ‖X‖ + ‖y‖ ≤ 3 * |t| + (|a| + ‖y‖) := by linarith
    have h4 : 4 * gammaBound * (4 * (‖X‖ + ‖y‖)) ≤ 4 * gammaBound * (4 * (3 * |t| + (|a| + ‖y‖))) :=
      by gcongr
    simp only [N0, N1]
    nlinarith
  have hden := norm_inv_denC_rect hz hε ha M y t hX
  refine (norm_epC_le M ε _).trans ?_
  have ht : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_abs t, sq_nonneg (1 - |t|)]
  have hnum' : N0 + N1 * |t| ≤ (N0 + N1) * (1 + |t|) := by nlinarith [abs_nonneg t]
  calc ‖(denC M ε (mk X y))⁻¹‖ * ‖numC M (mk X y)‖ ≤ K / (1 + t ^ 2) * ((N0 + N1) * (1 + |t|)) :=
        mul_le_mul hden (hnum.trans hnum') (norm_nonneg _) (by positivity)
    _ ≤ 2 * K * (N0 + N1) * (1 + |t|)⁻¹ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have h1 : (1 + |t|)⁻¹ * (1 + |t|) = 1 := inv_mul_cancel₀ (by positivity)
        have h2 : 0 ≤ K * (N0 + N1) := by positivity
        calc K * ((N0 + N1) * (1 + |t|)) = K * (N0 + N1) * (1 + |t|) ^ 2 * (1 + |t|)⁻¹ := by
              field_simp
          _ ≤ K * (N0 + N1) * (2 * (1 + t ^ 2)) * (1 + |t|)⁻¹ := by gcongr
          _ = _ := by ring

theorem exists_epC_rot (M ε a : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε)
    (ha : s * a ^ 2 ≤ ε / 4) :
    ∃ C, 0 ≤ C ∧ ∀ (y : Fin 3 → ℝ) (t : ℝ) (X : ℂ), X = (1 + s * I) * t + a →
      ‖epC M ε (mk X y)‖ ≤ C * (1 + |t| + ‖y‖)⁻¹ := by
  set K := 3 * kRot s a ε
  have hK : 0 < K := by have := kRot_pos (a := a) hs hε; positivity
  set N := |M| * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ)‖ + 4 * gammaBound * (4 * (2 + |a|))
  have hG := gammaBound_nonneg
  have hN : 0 ≤ N := by positivity
  refine ⟨K * N, by positivity, fun y t X hX => ?_⟩
  have hXn : ‖X‖ ≤ 2 * |t| + |a| := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
    exact norm_rot_le hs.le hs1
  set σ := 1 + |t| + ‖y‖
  have hσ : 1 ≤ σ := by simp only [σ]; linarith [abs_nonneg t, norm_nonneg y]
  have hnum : ‖numC M (mk X y)‖ ≤ N * σ := by
    refine (norm_numC_le M fun ν => (norm_mk_le X y ν).trans (le_refl _)).trans ?_
    have h4 : 4 * gammaBound * (4 * (‖X‖ + ‖y‖)) ≤ 4 * gammaBound * (4 * ((2 + |a|) * σ)) := by
      gcongr
      simp only [σ]
      nlinarith [abs_nonneg t, abs_nonneg a, norm_nonneg y]
    have h5 : |M| * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ)‖ ≤
        |M| * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ)‖ * σ := le_mul_of_one_le_right (by positivity) hσ
    simp only [N]
    nlinarith
  have hden := norm_inv_denC_rot hs hε ha M y t hX
  refine (norm_epC_le M ε _).trans ?_
  calc ‖(denC M ε (mk X y))⁻¹‖ * ‖numC M (mk X y)‖ ≤ K / σ ^ 2 * (N * σ) :=
        mul_le_mul hden hnum (norm_nonneg _) (by positivity)
    _ = K * N * σ⁻¹ := by field_simp

/-! ### Structural bounds -/

theorem norm_phC_le (mγ Λ ε : ℝ) (k : Fin 4 → ℂ) (μ ν : Fin 4) :
    ‖phC mγ Λ ε k μ ν‖ ≤ ‖(denC mγ ε k)⁻¹‖ + ‖(denC Λ ε k)⁻¹‖ := by
  unfold phC
  rw [norm_mul]
  have hm : ‖(Minkowski.metric μ ν : ℂ)‖ ≤ 1 := by
    unfold Minkowski.metric
    split_ifs <;> simp
  calc _ ≤ 1 * ‖(denC mγ ε k)⁻¹ - (denC Λ ε k)⁻¹‖ :=
        mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact norm_sub_le _ _

theorem norm_outerChainC_le (P : Params) (p kext k : Fin 4 → ℂ) (μ ρ ν : Fin 4) :
    ‖outerChainC P p kext k μ ρ ν‖ ≤
      gammaBound ^ 3 * ‖epC P.m P.ε (p + kext - k)‖ * ‖epC P.m P.ε (p - k)‖ := by
  unfold outerChainC
  have g := norm_gamma_le
  calc _ ≤ ‖Dirac.gamma ν‖ * ‖epC P.m P.ε (p + kext - k)‖ * ‖Dirac.gamma μ‖ *
        ‖epC P.m P.ε (p - k)‖ * ‖Dirac.gamma ρ‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        refine (norm_mul_le _ _).trans ?_
        gcongr
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ gammaBound * ‖epC P.m P.ε (p + kext - k)‖ * gammaBound * ‖epC P.m P.ε (p - k)‖ *
        gammaBound := by gcongr <;> first | exact g _ | (unfold gammaBound; positivity)
    _ = _ := by ring

/-- The constant of `chainOuterC`. -/
noncomputable def outerConst (P : Params) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 5

theorem norm_chainOuterC_le (P : Params) (p kext : Fin 4 → ℂ) (α β μ : Fin 4) (k : Fin 4 → ℂ)
    {B1 B2 : ℝ} (hB2 : 0 ≤ B2) (h1 : ∀ ρ ν, ‖outerChainC P p kext k μ ρ ν‖ ≤ B1)
    (h2 : ∀ ρ ν, ‖phC P.mγ P.Λ P.ε k ρ ν‖ ≤ B2) (h3 : ∀ ρ ν, ‖phC P.mγ P.Λ P.ε (-k) ρ ν‖ ≤ B2)
    (a b : Fin 4 × Fin 4) :
    ‖chainOuterC P p kext α β μ k a b‖ ≤ ‖outerConst P‖ * (16 * (B1 * B2 ^ 3)) := by
  unfold chainOuterC
  rw [show (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 5 = outerConst P from rfl,
    norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l0 : Fin 4, ‖∑ l2 : Fin 4, outerChainC P p kext k μ l0 l2 α β *
        phC P.mγ P.Λ P.ε k l0 a.1 * phC P.mγ P.Λ P.ε k a.2 b.1 * phC P.mγ P.Λ P.ε (-k) l2 b.2‖
      ≤ ∑ _l0 : Fin 4, ∑ _l2 : Fin 4, B1 * B2 ^ 3 := by
        refine Finset.sum_le_sum fun l0 _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun l2 _ => ?_)
        have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (h1 l0 l2)
        rw [norm_mul, norm_mul, norm_mul]
        have e := (norm_entry_le (outerChainC P p kext k μ l0 l2) α β).trans (h1 l0 l2)
        calc _ ≤ B1 * B2 * B2 * B2 := by
              gcongr
              · exact h2 _ _
              · exact h2 _ _
              · exact h3 _ _
          _ = B1 * B2 ^ 3 := by ring
    _ = 16 * (B1 * B2 ^ 3) := by simp; ring

theorem norm_trace_epC_le (M ε : ℝ) (A B : Fin 4 → ℂ) (μ ν : Fin 4) :
    ‖Matrix.trace (epC M ε A * Dirac.gamma μ * epC M ε B * Dirac.gamma ν)‖ ≤
      4 * (gammaBound ^ 2 * ‖epC M ε A‖ * ‖epC M ε B‖) := by
  refine (norm_trace_le _).trans ?_
  gcongr
  have g := norm_gamma_le
  calc _ ≤ ‖epC M ε A‖ * ‖Dirac.gamma μ‖ * ‖epC M ε B‖ * ‖Dirac.gamma ν‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖epC M ε A‖ * gammaBound * ‖epC M ε B‖ * gammaBound := by gcongr <;> first | exact g _ | (unfold gammaBound; positivity)
    _ = _ := by ring

theorem norm_vpC_le_crude (P : Params) (k q : Fin 4 → ℂ) (μ ν : Fin 4) {E1 E2 : ℝ}
    (h1 : ∀ f, ‖epC (P.mass f) P.ε (q + k)‖ ≤ E1) (h2 : ∀ f, ‖epC (P.mass f) P.ε q‖ ≤ E2) :
    ‖vpC P k q μ ν‖ ≤
      ‖vpConst P‖ * ((∑ f, |P.loopCoeff f|) * (4 * (gammaBound ^ 2 * E1 * E2))) := by
  unfold vpC
  rw [norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  gcongr
  refine (norm_trace_epC_le _ _ _ _ _ _).trans ?_
  have hE1 : 0 ≤ E1 := (norm_nonneg _).trans (h1 f)
  have h3 := mul_le_mul (h1 f) (h2 f) (norm_nonneg _) hE1
  have hG2 : 0 ≤ gammaBound ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h3 hG2]

theorem norm_bbC_le (P : Params) (O : (Fin 4 → ℂ) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℂ)
    (ℓ : Fin 3 → Fin 4 → ℂ) {B V0 V1 : ℝ} (hB : ∀ a b, ‖O (ℓ 2) a b‖ ≤ B)
    (h0 : ∀ μ ν, ‖vpC P (ℓ 2) (ℓ 0) μ ν‖ ≤ V0) (h1 : ∀ μ ν, ‖vpC P (ℓ 2) (ℓ 1) μ ν‖ ≤ V1) :
    ‖bbC P O ℓ‖ ≤ 256 * (B * V0 * V1) := by
  unfold bbC
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a : Fin 4 × Fin 4, ‖∑ b : Fin 4 × Fin 4, O (ℓ 2) a b * vpC P (ℓ 2) (ℓ 0) a.1 a.2 *
        vpC P (ℓ 2) (ℓ 1) b.1 b.2‖ ≤ ∑ _a : Fin 4 × Fin 4, ∑ _b : Fin 4 × Fin 4, B * V0 * V1 := by
        refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_mul]
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a b)
        have hV0 : 0 ≤ V0 := (norm_nonneg _).trans (h0 a.1 a.2)
        gcongr
        · exact hB a b
        · exact h0 _ _
        · exact h1 _ _
    _ = 256 * (B * V0 * V1) := by simp; ring

end MatrixNorm

end QED.ChainProof.RepsIntBB

end
