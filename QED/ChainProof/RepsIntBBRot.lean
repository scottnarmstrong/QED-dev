/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBIntegrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The bubble–bubble integrand at the rotated energies `(1 + s i) t`

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). With
`σ(t, y) = 1 + |t| + |y|`:

* `exists_vpC_rot`: **the Pauli–Villars bubble bound** `‖Π(k, q)‖ ≤ C (σ(q + k)⁻⁵ + σ(q)⁻⁵)`,
  from `vpC_eq_sum_R` and `norm_pvR_le`; only the two Pauli–Villars conditions are used.
* `exists_chainOuterC_rot`: the outer factor is `≤ C σ(k)⁻⁶` (three photon propagators; the
  two electron propagators are bounded).
* `exists_Fz_rot`: the product bound of the whole integrand, `C σ₂⁻⁶ (σ₀₂⁻⁵ + σ₀⁻⁵)(σ₁₂⁻⁵ + σ₁⁻⁵)`.
-/

@[expose] public section

open Complex QED.Integration.ThreeLoop

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-- `σ(t, y) = 1 + |t| + |y|`. -/
noncomputable def sig (t : ℝ) (y : Fin 3 → ℝ) : ℝ := 1 + |t| + ‖y‖

theorem one_le_sig (t : ℝ) (y : Fin 3 → ℝ) : 1 ≤ sig t y := by
  unfold sig; linarith [abs_nonneg t, norm_nonneg y]

theorem sig_pos (t : ℝ) (y : Fin 3 → ℝ) : 0 < sig t y := by
  linarith [one_le_sig t y]

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem norm_mk_rot_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) (y : Fin 3 → ℝ) (ν : Fin 4) :
    ‖mk ((1 + s * I) * ↑t + ↑(0 : ℝ)) y ν‖ ≤ 2 * sig t y := by
  refine (norm_mk_le _ y ν).trans ?_
  have h2 := norm_rot_le hs hs1
  have : ‖(1 + s * I) * (t : ℂ) + ((0 : ℝ) : ℂ)‖ ≤ 2 * |t| := by
    rw [ofReal_zero, add_zero, norm_mul, norm_real, Real.norm_eq_abs]
    gcongr
  unfold sig
  linarith [abs_nonneg t, norm_nonneg y]

theorem norm_inv_denC_rot' {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (M : ℝ) (y : Fin 3 → ℝ) (t : ℝ) :
    ‖(denC M ε (mk ((1 + s * I) * ↑t + ↑(0 : ℝ)) y))⁻¹‖ ≤ 3 * kRot s 0 ε * (sig t y)⁻¹ ^ 2 := by
  have h00 : s * (0 : ℝ) ^ 2 ≤ ε / 4 := by simp; positivity
  refine (norm_inv_denC_rot hs hε h00 M y t rfl).trans (le_of_eq ?_)
  rw [div_eq_mul_inv, inv_pow, sig]

theorem norm_traceT0_le (A B : Fin 4 → ℂ) {QA QB : ℝ} (hA : ∀ ν, ‖A ν‖ ≤ QA)
    (hB : ∀ ν, ‖B ν‖ ≤ QB) (μ ν : Fin 4) :
    ‖traceT0 A B μ ν‖ ≤ 4 * ((4 * gammaBound * (4 * QA)) * gammaBound *
      (4 * gammaBound * (4 * QB)) * gammaBound) := by
  unfold traceT0
  refine (norm_trace_le _).trans ?_
  gcongr
  have g := norm_gamma_le
  have hG := gammaBound_nonneg
  have sA := norm_slashC_le hA
  have sB := norm_slashC_le hB
  have hQA : 0 ≤ QA := (norm_nonneg _).trans (hA 0)
  have hQB : 0 ≤ QB := (norm_nonneg _).trans (hB 0)
  calc _ ≤ ‖slashC A‖ * ‖Dirac.gamma μ‖ * ‖slashC B‖ * ‖Dirac.gamma ν‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ _ := by gcongr <;> exact g _

theorem norm_traceT2_le (μ ν : Fin 4) : ‖traceT2 μ ν‖ ≤ 4 * gammaBound ^ 2 := by
  unfold traceT2
  refine (norm_trace_le _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  rw [sq]
  have hG := gammaBound_nonneg
  exact mul_le_mul (norm_gamma_le μ) (norm_gamma_le ν) (norm_nonneg _) hG

/-- **The Pauli–Villars bubble bound** at the rotated energies. -/
theorem exists_vpC_rot (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (t0 t2 : ℝ) (y0 y2 : Fin 3 → ℝ) (μ ν : Fin 4),
      ‖vpC P (mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2) (mk ((1 + s * I) * ↑t0 + ↑(0 : ℝ)) y0) μ ν‖ ≤
        C * ((sig (t0 + t2) (y0 + y2))⁻¹ ^ 5 + (sig t0 y0)⁻¹ ^ 5) := by
  have h00 : s * (0 : ℝ) ^ 2 ≤ P.ε / 4 := by simp; positivity
  set K := 3 * kRot s 0 P.ε
  have hK : 0 ≤ K := by have := kRot_pos (a := 0) hs hε; positivity
  have hG := gammaBound_nonneg
  set L := 4 * ((4 * gammaBound * (4 * 2)) * gammaBound * (4 * gammaBound * (4 * 2)) *
    gammaBound) + 4 * gammaBound ^ 2
  have hL : 0 ≤ L := by positivity
  set X := ∑ f, P.mass f ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg fun f _ => sq_nonneg _
  have hXf : ∀ f, P.mass f ^ 2 ≤ X := fun f =>
    Finset.single_le_sum (f := fun f => P.mass f ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ f)
  set Cpv := L * (1 + X) * (3 * K ^ 4 + X * K ^ 5) + 2 * L * K ^ 3
  have hCpv : 0 ≤ Cpv := by positivity
  refine ⟨‖vpConst P‖ * ((∑ f, |P.loopCoeff f|) * (X ^ 2 * Cpv)), by positivity,
    fun t0 t2 y0 y2 μ ν => ?_⟩
  set q := mk ((1 + s * I) * ↑t0 + ↑(0 : ℝ)) y0
  set k := mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2
  have hqk : q + k = mk ((1 + s * I) * ↑(t0 + t2) + ↑(0 : ℝ)) (y0 + y2) := by
    simp only [q, k]; rw [mk_add]; congr 1; push_cast; ring
  have nA : NZ P.ε (q + k) := by rw [hqk]; exact nz_rot hs hε h00 _ _ rfl
  have nB : NZ P.ε q := nz_rot hs hε h00 _ _ rfl
  rw [vpC_eq_sum_R P hc₁ hc₂ k q nA nB μ ν, norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (vpConst P))
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun f _ => ?_
  set pA := (sig (t0 + t2) (y0 + y2))⁻¹
  set pB := (sig t0 y0)⁻¹
  have hpA : 0 < pA := inv_pos.2 (sig_pos _ _)
  have hpB : 0 < pB := inv_pos.2 (sig_pos _ _)
  have hpA1 : pA ≤ 1 := inv_le_one_of_one_le₀ (one_le_sig _ _)
  have hpB1 : pB ≤ 1 := inv_le_one_of_one_le₀ (one_le_sig _ _)
  have dA : ∀ M, ‖(denC M P.ε (q + k))⁻¹‖ ≤ K * pA ^ 2 := fun M => by
    rw [hqk]; exact norm_inv_denC_rot' hs hε M _ _
  have dB : ∀ M, ‖(denC M P.ε q)⁻¹‖ ≤ K * pB ^ 2 := fun M => norm_inv_denC_rot' hs hε M _ _
  have hT0 : ‖traceT0 (q + k) q μ ν‖ * (pA * pB) ≤ L := by
    have bA : ∀ ν, ‖(q + k) ν‖ ≤ 2 * sig (t0 + t2) (y0 + y2) := fun ν => by
      rw [hqk]; exact norm_mk_rot_le hs.le hs1 _ _ ν
    have bB : ∀ ν, ‖q ν‖ ≤ 2 * sig t0 y0 := fun ν => norm_mk_rot_le hs.le hs1 _ _ ν
    have b := norm_traceT0_le (q + k) q bA bB μ ν
    have e : 4 * ((4 * gammaBound * (4 * (2 * sig (t0 + t2) (y0 + y2)))) * gammaBound *
        (4 * gammaBound * (4 * (2 * sig t0 y0))) * gammaBound) * (pA * pB) =
        4 * ((4 * gammaBound * (4 * 2)) * gammaBound * (4 * gammaBound * (4 * 2)) *
          gammaBound) := by
      simp only [pA, pB]
      field_simp [(sig_pos (t0 + t2) (y0 + y2)).ne', (sig_pos t0 y0).ne']
    calc _ ≤ 4 * ((4 * gammaBound * (4 * (2 * sig (t0 + t2) (y0 + y2)))) * gammaBound *
          (4 * gammaBound * (4 * (2 * sig t0 y0))) * gammaBound) * (pA * pB) := by gcongr
      _ ≤ L := by rw [e]; simp only [L]; linarith [sq_nonneg gammaBound]
  have hT2 : ‖traceT2 μ ν‖ ≤ L := by
    refine (norm_traceT2_le μ ν).trans ?_
    simp only [L]
    have : 0 ≤ 4 * ((4 * gammaBound * (4 * 2)) * gammaBound * (4 * gammaBound * (4 * 2)) *
      gammaBound) := by positivity
    linarith
  have hx : ‖((P.mass f : ℂ) ^ 2)‖ ≤ X := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]; exact hXf f
  have bR := norm_pvR_le hpA hpB hpA1 hpB1 hK hL hX (dA 0) (dA (P.mass f)) (dB 0) (dB (P.mass f)) hT0 hT2 hx
  rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_pow]
  have hx2 : ‖((P.mass f : ℂ) ^ 2)‖ ^ 2 ≤ X ^ 2 := by
    gcongr
  calc |P.loopCoeff f| * ‖((P.mass f : ℂ) ^ 2)‖ ^ 2 * ‖pvR _ _ _ _ _ _ _‖ ≤
      |P.loopCoeff f| * X ^ 2 * (Cpv * (pA ^ 5 + pB ^ 5)) := by gcongr
    _ = |P.loopCoeff f| * (X ^ 2 * Cpv * (pA ^ 5 + pB ^ 5)) := by ring

theorem exists_chainOuterC_rot (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ)
    (α β μ : Fin 4) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha1 : s * p 0 ^ 2 ≤ P.ε / 4) (ha2 : s * (p 0 + kext 0) ^ 2 ≤ P.ε / 4) :
    ∃ C, 0 ≤ C ∧ ∀ (t2 : ℝ) (y2 : Fin 3 → ℝ) (a b : Fin 4 × Fin 4),
      ‖chainOuterC P (cv p) (cv kext) α β μ (mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2) a b‖ ≤
        C * (sig t2 y2)⁻¹ ^ 6 := by
  obtain ⟨C1, hC10, hC1⟩ := exists_epC_rot P.m P.ε (p 0 + kext 0) hs hs1 hε ha2
  obtain ⟨C2, hC20, hC2⟩ := exists_epC_rot P.m P.ε (p 0) hs hs1 hε ha1
  set K := 3 * kRot s 0 P.ε
  have hK : 0 ≤ K := by have := kRot_pos (a := 0) hs hε; positivity
  have hG := gammaBound_nonneg
  refine ⟨‖outerConst P‖ * (16 * (gammaBound ^ 3 * C1 * C2 * (2 * K) ^ 3)), by positivity,
    fun t2 y2 a b => ?_⟩
  set u := (sig t2 y2)⁻¹
  have hu : 0 < u := inv_pos.2 (sig_pos _ _)
  have le1 : ∀ (t : ℝ) (y : Fin 3 → ℝ), (1 + |t| + ‖y‖)⁻¹ ≤ 1 := fun t y =>
    inv_le_one_of_one_le₀ (one_le_sig t y)
  have hB1 : ∀ ρ ν, ‖outerChainC P (cv p) (cv kext)
      (mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2) μ ρ ν‖ ≤ gammaBound ^ 3 * C1 * C2 := by
    intro ρ ν
    refine (norm_outerChainC_le P _ _ _ μ ρ ν).trans ?_
    have e1 : cv p + cv kext - mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2 =
        mk ((1 + s * I) * ↑(-t2) + ↑(p 0 + kext 0)) (Fin.tail p + Fin.tail kext - y2) := by
      rw [cv_eq_mk, cv_eq_mk, mk_add, mk_sub]; congr 1; push_cast; ring
    have e2 : cv p - mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2 =
        mk ((1 + s * I) * ↑(-t2) + ↑(p 0)) (Fin.tail p - y2) := by
      rw [cv_eq_mk, mk_sub]; congr 1; push_cast; ring
    rw [e1, e2]
    have b1 := (hC1 (Fin.tail p + Fin.tail kext - y2) (-t2) _ rfl).trans
      (mul_le_of_le_one_right hC10 (le1 _ _))
    have b2 := (hC2 (Fin.tail p - y2) (-t2) _ rfl).trans (mul_le_of_le_one_right hC20 (le1 _ _))
    calc _ ≤ gammaBound ^ 3 * C1 * C2 := by gcongr
      _ = _ := rfl
  have hB2 : ∀ ρ ν, ‖phC P.mγ P.Λ P.ε (mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2) ρ ν‖ ≤
      2 * K * u ^ 2 := by
    intro ρ ν
    refine (norm_phC_le _ _ _ _ ρ ν).trans ?_
    have := norm_inv_denC_rot' hs hε P.mγ y2 t2
    have := norm_inv_denC_rot' hs hε P.Λ y2 t2
    simp only [u]
    linarith
  have hB3 : ∀ ρ ν, ‖phC P.mγ P.Λ P.ε (-mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2) ρ ν‖ ≤
      2 * K * u ^ 2 := by
    intro ρ ν
    have e : -mk ((1 + s * I) * ↑t2 + ↑(0 : ℝ)) y2 = mk ((1 + s * I) * ↑(-t2) + ↑(0 : ℝ)) (-y2) := by
      rw [mk_neg]; congr 1; push_cast; ring
    rw [e]
    refine (norm_phC_le _ _ _ _ ρ ν).trans ?_
    have hsig : sig (-t2) (-y2) = sig t2 y2 := by simp [sig]
    have := norm_inv_denC_rot' hs hε P.mγ (-y2) (-t2)
    have := norm_inv_denC_rot' hs hε P.Λ (-y2) (-t2)
    rw [hsig] at *
    simp only [u]
    linarith
  refine (norm_chainOuterC_le P _ _ α β μ _ (by positivity) hB1 hB2 hB3 a b).trans
    (le_of_eq ?_)
  ring

/-- **The product bound at `1 + s i`.** -/
theorem exists_Fz_rot (P : Params) (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p kext : Fin 4 → ℝ)
    (α β μ : Fin 4) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha1 : s * p 0 ^ 2 ≤ P.ε / 4) (ha2 : s * (p 0 + kext 0) ^ 2 ≤ P.ε / 4) :
    ∃ C, 0 ≤ C ∧ ∀ (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ),
      ‖Fz P p kext α β μ v (1 + s * I) τ‖ ≤
        C * ((sig (τ 2) (v 2))⁻¹ ^ 6 *
          ((sig (τ 0 + τ 2) (v 0 + v 2))⁻¹ ^ 5 + (sig (τ 0) (v 0))⁻¹ ^ 5) *
          ((sig (τ 1 + τ 2) (v 1 + v 2))⁻¹ ^ 5 + (sig (τ 1) (v 1))⁻¹ ^ 5)) := by
  obtain ⟨CO, hCO0, hCO⟩ := exists_chainOuterC_rot P hε p kext α β μ hs hs1 ha1 ha2
  obtain ⟨CV, hCV0, hCV⟩ := exists_vpC_rot P hε hc₁ hc₂ hs hs1
  refine ⟨256 * (CO * CV * CV), by positivity, fun τ v => ?_⟩
  have hB : ∀ a b, ‖chainOuterC P (cv p) (cv kext) α β μ (rl (1 + s * I) τ v 2) a b‖ ≤
      CO * (sig (τ 2) (v 2))⁻¹ ^ 6 := by
    intro a b
    rw [rl_eq]
    exact hCO (τ 2) (v 2) a b
  have hV : ∀ i : Fin 3, ∀ μ ν, ‖vpC P (rl (1 + s * I) τ v 2) (rl (1 + s * I) τ v i) μ ν‖ ≤
      CV * ((sig (τ i + τ 2) (v i + v 2))⁻¹ ^ 5 + (sig (τ i) (v i))⁻¹ ^ 5) := by
    intro i μ ν
    rw [rl_eq, rl_eq]
    exact hCV (τ i) (τ 2) (v i) (v 2) μ ν
  refine (norm_bbC_le P _ _ hB (hV 0) (hV 1)).trans (le_of_eq ?_)
  ring

end MatrixNorm

end QED.ChainProof.RepsIntBB

end
