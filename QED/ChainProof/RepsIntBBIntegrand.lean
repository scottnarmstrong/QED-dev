/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBFactors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounds for the bubble–bubble integrand at rotated energies

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). With all three loop
energies multiplied by `z` (`rl z τ v`, `Fz`):

* **on the rectangle** `rotRect h`, at fixed spatial momenta `v`
  (`exists_Fz_rect`): `‖Fz z τ‖ ≤ C (1 + |τ₀|)⁻² (1 + |τ₁|)⁻² (1 + |τ₂|)⁻⁶`, the dominating
  function of the rotation (two electron propagators and three photon propagators on the photon
  line, one power of each bubble propagator);
* the bound at `z = 1 + s i` for all momenta is `exists_Fz_rot`
  (`QED/ChainProof/RepsIntBBRot.lean`).

The rectangle bound needs `h (p⁰)², h (p⁰ + k_ext⁰)² ≤ ε/4` for the two open-line electrons, the only
denominators with a shifted energy.
-/

@[expose] public section

open Complex QED.Integration.ThreeLoop

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-! ### Rotated loop momenta -/

/-- The loop momenta with energies `z τ s` and spatial parts `v s`. -/
def rl (z : ℂ) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 4 → ℂ :=
  fun s => mk (z * τ s) (v s)

/-- The bubble–bubble integrand of the chain at rotated energies. -/
noncomputable def Fz (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (v : Fin 3 → Fin 3 → ℝ)
    (z : ℂ) (τ : Fin 3 → ℝ) : ℂ :=
  bbC P (chainOuterC P (cv p) (cv kext) α β μ) (rl z τ v)

theorem rl_one (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) :
    rl 1 τ v = fun s => cv (Fin.cons (τ s) (v s)) := by
  funext s
  rw [cv_cons, rl, one_mul]

theorem rl_smul (z : ℂ) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) (r : ℝ) :
    rl z (r • τ) v = rl (r * z) τ v := by
  funext s
  simp only [rl, Pi.smul_apply, smul_eq_mul, ofReal_mul]
  ring_nf

theorem mk_eq_rot (z X : ℂ) (y : Fin 3 → ℝ) (t a : ℝ) (h : X = z * t + a) :
    mk X y = mk (z * t + a) y := by rw [h]

theorem rl_add_eq (z : ℂ) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    rl z τ v i + rl z τ v 2 = mk (z * ↑(τ i + τ 2) + ↑(0 : ℝ)) (v i + v 2) := by
  rw [rl, rl, mk_add]
  congr 1
  push_cast
  ring

theorem rl_eq (z : ℂ) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    rl z τ v i = mk (z * ↑(τ i) + ↑(0 : ℝ)) (v i) := by
  rw [rl]
  congr 1
  push_cast
  ring

theorem neg_rl_eq (z : ℂ) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) :
    -rl z τ v 2 = mk (z * ↑(-τ 2) + ↑(0 : ℝ)) (-v 2) := by
  rw [rl, mk_neg]
  congr 1
  push_cast
  ring

theorem cv_sub_rl_eq (p : Fin 4 → ℝ) (z : ℂ) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) :
    cv p - rl z τ v 2 = mk (z * ↑(-τ 2) + ↑(p 0)) (Fin.tail p - v 2) := by
  rw [rl, cv_eq_mk, mk_sub]
  congr 1
  push_cast
  ring

theorem cv_add_sub_rl_eq (p kext : Fin 4 → ℝ) (z : ℂ) (τ : Fin 3 → ℝ)
    (v : Fin 3 → Fin 3 → ℝ) :
    cv p + cv kext - rl z τ v 2 =
      mk (z * ↑(-τ 2) + ↑(p 0 + kext 0)) (Fin.tail p + Fin.tail kext - v 2) := by
  rw [rl, cv_eq_mk, cv_eq_mk, mk_add, mk_sub]
  congr 1
  push_cast
  ring

/-- **No denominator vanishes on the rectangle.** -/
theorem goodBB_rect (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) {h : ℝ}
    (ha1 : h * p 0 ^ 2 ≤ P.ε / 4) (ha2 : h * (p 0 + kext 0) ^ 2 ≤ P.ε / 4)
    {z : ℂ} (hz : z ∈ rotRect h) (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) :
    GoodBB P (cv p) (cv kext) (rl z τ v) := by
  have h00 : h * (0 : ℝ) ^ 2 ≤ P.ε / 4 := by simp; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rl_add_eq]; exact nz_rect hz hε h00 _ _ rfl
  · rw [rl_eq]; exact nz_rect hz hε h00 _ _ rfl
  · rw [rl_add_eq]; exact nz_rect hz hε h00 _ _ rfl
  · rw [rl_eq]; exact nz_rect hz hε h00 _ _ rfl
  · rw [rl_eq]; exact nz_rect hz hε h00 _ _ rfl
  · rw [neg_rl_eq]; exact nz_rect hz hε h00 _ _ rfl
  · rw [cv_add_sub_rl_eq]; exact nz_rect hz hε ha2 _ _ rfl
  · rw [cv_sub_rl_eq]; exact nz_rect hz hε ha1 _ _ rfl

/-- **No denominator vanishes at `1 + s i`.** -/
theorem goodBB_rot (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) {s : ℝ} (hs : 0 < s)
    (ha1 : s * p 0 ^ 2 ≤ P.ε / 4) (ha2 : s * (p 0 + kext 0) ^ 2 ≤ P.ε / 4)
    (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) :
    GoodBB P (cv p) (cv kext) (rl (1 + s * I) τ v) := by
  have h00 : s * (0 : ℝ) ^ 2 ≤ P.ε / 4 := by simp; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rl_add_eq]; exact nz_rot hs hε h00 _ _ rfl
  · rw [rl_eq]; exact nz_rot hs hε h00 _ _ rfl
  · rw [rl_add_eq]; exact nz_rot hs hε h00 _ _ rfl
  · rw [rl_eq]; exact nz_rot hs hε h00 _ _ rfl
  · rw [rl_eq]; exact nz_rot hs hε h00 _ _ rfl
  · rw [neg_rl_eq]; exact nz_rot hs hε h00 _ _ rfl
  · rw [cv_add_sub_rl_eq]; exact nz_rot hs hε ha2 _ _ rfl
  · rw [cv_sub_rl_eq]; exact nz_rot hs hε ha1 _ _ rfl

/-! ### On the rectangle -/

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem inv_one_add_abs_add_le' (t τ : ℝ) : (1 + |t + τ|)⁻¹ ≤ (1 + |τ|) * (1 + |t|)⁻¹ :=
  QED.ChainProof.HCLimit.inv_one_add_abs_add_le t τ

theorem exists_vpC_rect (P : Params) (hε : 0 < P.ε) {h : ℝ} (hh : h ≤ 1)
    (y0 y2 : Fin 3 → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ rotRect h, ∀ (t0 t2 : ℝ) (μ ν : Fin 4),
      ‖vpC P (mk (z * ↑t2 + ↑(0 : ℝ)) y2) (mk (z * ↑t0 + ↑(0 : ℝ)) y0) μ ν‖ ≤
        C * ((1 + |t0 + t2|)⁻¹ * (1 + |t0|)⁻¹) := by
  have h00 : h * (0 : ℝ) ^ 2 ≤ P.ε / 4 := by simp; positivity
  choose CA hCA0 hCA using fun f : Fin 3 =>
    exists_epC_rect (P.mass f) P.ε 0 (y0 + y2) hε hh h00
  choose CB hCB0 hCB using fun f : Fin 3 => exists_epC_rect (P.mass f) P.ε 0 y0 hε hh h00
  set SA := ∑ f, CA f
  set SB := ∑ f, CB f
  have hSA : ∀ f, CA f ≤ SA := fun f =>
    Finset.single_le_sum (f := CA) (fun i _ => hCA0 i) (Finset.mem_univ f)
  have hSB : ∀ f, CB f ≤ SB := fun f =>
    Finset.single_le_sum (f := CB) (fun i _ => hCB0 i) (Finset.mem_univ f)
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun i _ => hCA0 i
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun i _ => hCB0 i
  have hG := gammaBound_nonneg
  refine ⟨‖vpConst P‖ * ((∑ f, |P.loopCoeff f|) * (4 * (gammaBound ^ 2 * SA * SB))),
    by positivity, fun z hz t0 t2 μ ν => ?_⟩
  have hq : mk (z * ↑t0 + ↑(0 : ℝ)) y0 + mk (z * ↑t2 + ↑(0 : ℝ)) y2 =
      mk (z * ↑(t0 + t2) + ↑(0 : ℝ)) (y0 + y2) := by
    rw [mk_add]; congr 1; push_cast; ring
  have hE1 : ∀ f, ‖epC (P.mass f) P.ε
      (mk (z * ↑t0 + ↑(0 : ℝ)) y0 + mk (z * ↑t2 + ↑(0 : ℝ)) y2)‖ ≤ SA * (1 + |t0 + t2|)⁻¹ := by
    intro f
    rw [hq]
    exact (hCA f z hz _ _ rfl).trans (by gcongr; exact hSA f)
  have hE2 : ∀ f, ‖epC (P.mass f) P.ε (mk (z * ↑t0 + ↑(0 : ℝ)) y0)‖ ≤ SB * (1 + |t0|)⁻¹ :=
    fun f => (hCB f z hz _ _ rfl).trans (by gcongr; exact hSB f)
  refine (norm_vpC_le_crude P _ _ μ ν hE1 hE2).trans (le_of_eq ?_)
  ring

theorem exists_chainOuterC_rect (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ)
    (α β μ : Fin 4) (y2 : Fin 3 → ℝ) {h : ℝ} (hh : h ≤ 1)
    (ha1 : h * p 0 ^ 2 ≤ P.ε / 4) (ha2 : h * (p 0 + kext 0) ^ 2 ≤ P.ε / 4) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ rotRect h, ∀ (t2 : ℝ) (a b : Fin 4 × Fin 4),
      ‖chainOuterC P (cv p) (cv kext) α β μ (mk (z * ↑t2 + ↑(0 : ℝ)) y2) a b‖ ≤
        C * ((1 + |t2|) ^ 8)⁻¹ := by
  have h00 : h * (0 : ℝ) ^ 2 ≤ P.ε / 4 := by simp; positivity
  obtain ⟨C1, hC10, hC1⟩ := exists_epC_rect P.m P.ε (p 0 + kext 0)
    (Fin.tail p + Fin.tail kext - y2) hε hh ha2
  obtain ⟨C2, hC20, hC2⟩ := exists_epC_rect P.m P.ε (p 0) (Fin.tail p - y2) hε hh ha1
  set Kp := kRect 0 (sq3 y2 + P.mγ ^ 2) P.ε + kRect 0 (sq3 y2 + P.Λ ^ 2) P.ε +
    kRect 0 (sq3 (-y2) + P.mγ ^ 2) P.ε + kRect 0 (sq3 (-y2) + P.Λ ^ 2) P.ε
  have hKp : 0 ≤ Kp := by
    have := fun M y => (kRect_pos (a := 0) (add_nonneg (sq3_nonneg y) (sq_nonneg M)) hε).le
    simp only [Kp]
    linarith [this P.mγ y2, this P.Λ y2, this P.mγ (-y2), this P.Λ (-y2)]
  have hG := gammaBound_nonneg
  refine ⟨‖outerConst P‖ * (16 * (gammaBound ^ 3 * C1 * C2 * (2 * Kp) ^ 3)), by positivity,
    fun z hz t2 a b => ?_⟩
  set u := (1 + |t2|)⁻¹
  have hu : 0 < u := by positivity
  have ht : (1 + |t2|) ^ 2 ≤ 2 * (1 + t2 ^ 2) := by
    nlinarith [sq_abs t2, sq_nonneg (1 - |t2|)]
  have hkk : mk (z * ↑t2 + ↑(0 : ℝ)) y2 = mk (z * ↑t2) y2 := by simp
  have hB1 : ∀ ρ ν, ‖outerChainC P (cv p) (cv kext) (mk (z * ↑t2 + ↑(0 : ℝ)) y2) μ ρ ν‖ ≤
      gammaBound ^ 3 * (C1 * u) * (C2 * u) := by
    intro ρ ν
    refine (norm_outerChainC_le P _ _ _ μ ρ ν).trans ?_
    have e1 : cv p + cv kext - mk (z * ↑t2 + ↑(0 : ℝ)) y2 =
        mk (z * ↑(-t2) + ↑(p 0 + kext 0)) (Fin.tail p + Fin.tail kext - y2) := by
      rw [cv_eq_mk, cv_eq_mk, mk_add, mk_sub]; congr 1; push_cast; ring
    have e2 : cv p - mk (z * ↑t2 + ↑(0 : ℝ)) y2 = mk (z * ↑(-t2) + ↑(p 0)) (Fin.tail p - y2) := by
      rw [cv_eq_mk, mk_sub]; congr 1; push_cast; ring
    rw [e1, e2]
    have b1 := hC1 z hz (-t2) _ rfl
    have b2 := hC2 z hz (-t2) _ rfl
    rw [abs_neg] at b1 b2
    gcongr
  have hden : ∀ M (y : Fin 3 → ℝ) (t : ℝ) (X : ℂ), X = z * ↑t + ↑(0 : ℝ) → |t| = |t2| →
      ‖(denC M P.ε (mk X y))⁻¹‖ ≤ kRect 0 (sq3 y + M ^ 2) P.ε * (2 * u ^ 2) := by
    intro M y t X hX htt
    refine (norm_inv_denC_rect hz hε h00 M y t hX).trans ?_
    have hK := (kRect_pos (a := 0) (add_nonneg (sq3_nonneg y) (sq_nonneg M)) hε).le
    rw [div_eq_mul_inv]
    gcongr
    have ht' : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_abs t, sq_nonneg (1 - |t|)]
    rw [htt] at ht'
    simp only [u, inv_pow]
    rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
    calc (2 : ℝ)⁻¹ * (1 + |t2|) ^ 2 ≤ (2 : ℝ)⁻¹ * (2 * (1 + t ^ 2)) := by gcongr
      _ = 1 + t ^ 2 := by ring
  have hB2 : ∀ ρ ν, ‖phC P.mγ P.Λ P.ε (mk (z * ↑t2 + ↑(0 : ℝ)) y2) ρ ν‖ ≤ 2 * Kp * u ^ 2 := by
    intro ρ ν
    refine (norm_phC_le _ _ _ _ ρ ν).trans ?_
    have := hden P.mγ y2 t2 _ rfl rfl
    have := hden P.Λ y2 t2 _ rfl rfl
    have k3 := (kRect_pos (a := 0) (add_nonneg (sq3_nonneg (-y2)) (sq_nonneg P.mγ)) hε).le
    have k4 := (kRect_pos (a := 0) (add_nonneg (sq3_nonneg (-y2)) (sq_nonneg P.Λ)) hε).le
    simp only [Kp]
    nlinarith [sq_nonneg u]
  have hB3 : ∀ ρ ν, ‖phC P.mγ P.Λ P.ε (-mk (z * ↑t2 + ↑(0 : ℝ)) y2) ρ ν‖ ≤ 2 * Kp * u ^ 2 := by
    intro ρ ν
    have e : -mk (z * ↑t2 + ↑(0 : ℝ)) y2 = mk (z * ↑(-t2) + ↑(0 : ℝ)) (-y2) := by
      rw [mk_neg]; congr 1; push_cast; ring
    rw [e]
    refine (norm_phC_le _ _ _ _ ρ ν).trans ?_
    have := hden P.mγ (-y2) (-t2) _ rfl (abs_neg t2)
    have := hden P.Λ (-y2) (-t2) _ rfl (abs_neg t2)
    have k1 := (kRect_pos (a := 0) (add_nonneg (sq3_nonneg y2) (sq_nonneg P.mγ)) hε).le
    have k2 := (kRect_pos (a := 0) (add_nonneg (sq3_nonneg y2) (sq_nonneg P.Λ)) hε).le
    simp only [Kp]
    nlinarith [sq_nonneg u]
  refine (norm_chainOuterC_le P _ _ α β μ _ (by positivity) hB1 hB2 hB3 a b).trans
    (le_of_eq ?_)
  rw [← inv_pow]
  simp only [u]
  ring

/-- **The dominating function of the rotation**, at fixed spatial momenta. -/
theorem exists_Fz_rect (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (v : Fin 3 → Fin 3 → ℝ) {h : ℝ} (hh : h ≤ 1)
    (ha1 : h * p 0 ^ 2 ≤ P.ε / 4) (ha2 : h * (p 0 + kext 0) ^ 2 ≤ P.ε / 4) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ rotRect h, ∀ τ : Fin 3 → ℝ,
      ‖Fz P p kext α β μ v z τ‖ ≤
        C * (((1 + |τ 0|) ^ 2)⁻¹ * ((1 + |τ 1|) ^ 2)⁻¹ * ((1 + |τ 2|) ^ 6)⁻¹) := by
  obtain ⟨CO, hCO0, hCO⟩ := exists_chainOuterC_rect P hε p kext α β μ (v 2) hh ha1 ha2
  obtain ⟨C0, hC00, hC0⟩ := exists_vpC_rect P hε hh (v 0) (v 2)
  obtain ⟨C1, hC10, hC1⟩ := exists_vpC_rect P hε hh (v 1) (v 2)
  refine ⟨256 * (CO * C0 * C1), by positivity, fun z hz τ => ?_⟩
  have hB : ∀ a b, ‖chainOuterC P (cv p) (cv kext) α β μ (rl z τ v 2) a b‖ ≤
      CO * ((1 + |τ 2|) ^ 8)⁻¹ := by
    intro a b
    rw [rl_eq]
    exact hCO z hz (τ 2) a b
  have hV : ∀ i : Fin 3, ∀ C : ℝ, 0 ≤ C → (∀ (t0 t2 : ℝ) (μ ν : Fin 4),
      ‖vpC P (mk (z * ↑t2 + ↑(0 : ℝ)) (v 2)) (mk (z * ↑t0 + ↑(0 : ℝ)) (v i)) μ ν‖ ≤
        C * ((1 + |t0 + t2|)⁻¹ * (1 + |t0|)⁻¹)) →
      ∀ μ ν, ‖vpC P (rl z τ v 2) (rl z τ v i) μ ν‖ ≤
        C * ((1 + |τ 2|) * (1 + |τ i|)⁻¹ * (1 + |τ i|)⁻¹) := by
    intro i C hC hb μ ν
    rw [rl_eq, rl_eq]
    refine (hb (τ i) (τ 2) μ ν).trans ?_
    have := inv_one_add_abs_add_le' (τ i) (τ 2)
    gcongr
  have hV0 := hV 0 C0 hC00 (hC0 z hz)
  have hV1 := hV 1 C1 hC10 (hC1 z hz)
  refine (norm_bbC_le P _ _ hB hV0 hV1).trans (le_of_eq ?_)
  have p0 : (1 + |τ 0|) ≠ 0 := by positivity
  have p1 : (1 + |τ 1|) ≠ 0 := by positivity
  have p2 : (1 + |τ 2|) ≠ 0 := by positivity
  field_simp

end MatrixNorm

end QED.ChainProof.RepsIntBB

end
