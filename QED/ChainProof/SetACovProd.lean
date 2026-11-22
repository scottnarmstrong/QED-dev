/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2CovPow

/-!
# Covariance of the engine limits from three photon-type masses, with no upper bound

Helper level for `QED.ChainProof.SetAPauli.SetACovLink` (covariance of the set (a) limits). The
set (b) route (`QED.ChainProof.HCBB2.covRel_specM`) reaches `prodLimit` through the absorption
recursion `powLimit (j + 1) Ms = powLimit j (tail Ms) - M₀² powLimit j Ms`, which drops one
photon-type mass per power of `k²`, and its base `QED.ChainProof.HCBB2.conj_prodLim` needs four
to eight photon-type masses. The set (a) spectral terms have four photon-type masses, any
number `r` of spectral masses and up to two powers of `k²`. This file removes both limits:

* `kindsPh_ok'`: the refined no-subdivergence criterion for the line kinds
  `[out, inn, pho^{k+2}, aux³]` holds for **every** `k ≥ 1` (three or more photon-type lines),
  proved by counting, not by `decide`;
* `conj_prodLim'`: covariance of the `prodLimit` matrices for every `k ≥ 1`, for numerators of
  degree `≤ 4`;
* `CovNum`: the hypotheses on a covariant numerator family of degree `≤ 2`;
  `CovNum.covRel_powM_zero` (base `j = 0`) and **`CovNum.covRel_powM_one`** (base `j = 1`: the
  numerator `k² N` has degree `≤ 4`, so one power of `k²` is absorbed into the numerator instead
  of into the masses);
* `covRel_powM'`: the recursion from the two bases, for `j ≤ k`;
* `covRel_specM'`, **`CovNum.covRel_specM`**: covariance of the `specLimit` matrices for
  `j ≤ k + r` and `k ≥ 1`, with no upper bound on `k` or `r`.
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology Set
open scoped Real Finset

namespace QED.ChainProof.SetACov

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPHalfAtGen
open QED.Dirac QED.ChainProof.HCBB2 QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.TwoLoop (IntNoSubdivergenceRefined intPairDet)

/-! ### The criterion for every `k ≥ 1` -/

/-- The auxiliary lines of `kindsPh k` are the last three. -/
theorem kindsPh_eq_aux_iff (k : ℕ) (e : Fin (k + 2 + 3 + 1 + 1)) :
    kindsPh k e = .aux ↔ k + 4 ≤ e.val := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.addCases (m := k + 2) (n := 3) (fun a => ?_) (fun b => ?_) i) i) e
  · simp [kindsPh]
  · simp [kindsPh]
  · simp only [kindsPh, Matrix.cons_val_succ, Fin.append_left, Fin.val_succ, Fin.val_castAdd]
    simp only [reduceCtorEq, false_iff, not_le]
    omega
  · simp only [kindsPh, Matrix.cons_val_succ, Fin.append_right, Fin.val_succ, Fin.val_natAdd,
      true_iff]
    omega

/-- Two lines are independent exactly when one of them is auxiliary. -/
theorem dir_det_ne_zero (a b : LineKind) :
    a.dir 0 * b.dir 1 - a.dir 1 * b.dir 0 ≠ 0 ↔ (a = .aux ↔ b ≠ .aux) := by
  cases a <;> cases b <;> simp [LineKind.dir]

theorem kindsPh_det_ne_zero (k : ℕ) (i j : Fin (k + 2 + 3 + 1 + 1)) :
    intPairDet (fun i => (kindsPh k i).dir) i j ≠ 0 ↔ (k + 4 ≤ i.val ↔ j.val < k + 4) := by
  rw [intPairDet, dir_det_ne_zero, kindsPh_eq_aux_iff, Ne, kindsPh_eq_aux_iff, not_le]

/-- The first four lines are distinct. -/
theorem card_four_E {n : ℕ} (hn : 3 ≤ n) : ({0, 1, 2, 3} : Finset (Fin (n + 1))).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] <;>
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
      Nat.mod_eq_of_lt (show 2 < n + 1 by omega), Nat.mod_eq_of_lt (show 3 < n + 1 by omega)]

/-- The first four lines have indices below four. -/
theorem val_lt_four_of_mem_E {n : ℕ} (hn : 3 ≤ n) :
    ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (n + 1))), e.val < 4 := by
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega), Nat.mod_eq_of_lt (show 2 < n + 1 by omega),
      Nat.mod_eq_of_lt (show 3 < n + 1 by omega)]

/-- **The refined no-subdivergence criterion for every `k ≥ 1`.** -/
theorem kindsPh_ok' (k : ℕ) (hk : 1 ≤ k) :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} (fun i => (kindsPh k i).dir) ∧
    ({0, 1, 2, 3} : Finset (Fin (k + 2 + 3 + 1 + 1))).card = 4 ∧
    ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (k + 2 + 3 + 1 + 1))), kindsPh k e ≠ .aux := by
  refine ⟨fun i => ?_, card_four_E (n := k + 6) (by omega), fun e he => by
    rw [Ne, kindsPh_eq_aux_iff]; have := val_lt_four_of_mem_E (n := k + 6) (by omega) e he; omega⟩
  have hlt : #{j : Fin (k + 6 + 1) | j.val < k + 4} = k + 4 := by
    rw [Fin.card_filter_val_lt]; omega
  have hge : #{j : Fin (k + 6 + 1) | ¬ j.val < k + 4} = 3 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (k + 6 + 1) => j.val < k + 4)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  simp only [kindsPh_det_ne_zero]
  by_cases hi : k + 4 ≤ i.val
  · simp only [hi, true_iff]
    rw [hlt]
    have := (Finset.card_filter_le ({0, 1, 2, 3} : Finset (Fin (k + 6 + 1)))
      fun e => e.val < k + 4).trans (card_four_E (n := k + 6) (by omega)).le
    omega
  · simp only [hi, false_iff]
    rw [hge]
    have : ({0, 1, 2, 3} : Finset (Fin (k + 6 + 1))).filter
        (fun e => ¬ e.val < k + 4) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he
      have := val_lt_four_of_mem_E (n := k + 6) (by omega) e he
      omega
    rw [this]
    simp

/-! ### Covariance of the `prodLimit` matrices from three photon-type masses -/

section Cov

variable {m M₀ : ℝ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- The limit of a `prodIntegrand` entry as a parametric value divided by `auxLimit m`, for at
least three photon-type masses. -/
theorem exists_paramValue_prod' (hk : 1 ≤ k) (hm : 0 < m) (hM₀ : 0 < M₀)
    (hMs : ∀ i, M₀ ≤ Ms i) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) {A : ℂ}
    (hA : Tendsto (fun ε => QED.OneLoop.energyFirstIntegral
      (prodIntegrand N m Ms (fun _ => ε) ε p' p)) (𝓝[>] 0) (𝓝 A)) :
    ∃ v, IsParamValue (kindsData (by omega) (kindsPh k) (massesPh m Ms) hm hM₀ hp hp' hq
      (massesPh_sq_of_ne_pho m Ms) (le_massesPh_sq hM₀ hMs) (kindsPh_ok' k hk).1)
      (fun ℓ => N (ℓ 0)) v ∧ A = v / auxLimit m := by
  obtain ⟨-, hcard, hE⟩ := kindsPh_ok' k hk
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by omega) (kindsPh k) (massesPh m Ms) hm hM₀
    hp hp' hq (massesPh_sq_of_ne_pho m Ms) (le_massesPh_sq hM₀ hMs) (kindsPh_ok' k hk).1
    hcard hE N hN (fun ε => prodIntegrand N m Ms (fun _ => ε) ε p' p)
    (fun ε _ ℓ => by rw [prod_kindsPh, prodIntegrand]; ring)
  exact ⟨v, hv, tendsto_nhds_unique hA hT⟩

/-- **Covariance of the limits of `prodIntegrand`** for at least three photon-type masses. -/
theorem conj_prodLim' (hk : 1 ≤ k) (hm : 0 < m) (hM₀ : 0 < M₀)
    (hMs : ∀ i, M₀ ≤ Ms i) (h : IsSpinLift L S T) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hP : ∀ p' p μ i j, IsLoopPoly 2 4 fun ℓ => Nf p' p μ (ℓ 0) i j)
    (hC : ∀ μ ℓ, S * Nf (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => Nf p' p ν ℓ) μ)
    {A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hA : ∀ μ i j, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral
      (prodIntegrand (fun ℓ => Nf p' p μ ℓ i j) m Ms (fun _ => ε) ε p' p)) (𝓝[>] 0)
      (𝓝 (A μ i j)))
    (hB : ∀ μ i j, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral
      (prodIntegrand (fun ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) m Ms (fun _ => ε) ε (L *ᵥ p')
        (L *ᵥ p))) (𝓝[>] 0) (𝓝 (B μ i j))) :
    CovRel L S T A B := by
  intro μ
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  exact conj_eq_vecAct_of_paramValue_div (kindsData (by omega) (kindsPh k) (massesPh m Ms) hm
      hM₀ hp hp' hq (massesPh_sq_of_ne_pho m Ms) (le_massesPh_sq hM₀ hMs)
      (kindsPh_ok' k hk).1) h
    (fun i => (kindsPh k i).mom (L *ᵥ p) (L *ᵥ p'))
    (funext fun i => QED.ChainProof.HCSide.lineKind_mom_map' p p' _)
    (fun μ ℓ => Nf p' p μ ℓ) (fun μ ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ) hC A B (auxLimit m)
    (fun μ i j => exists_paramValue_prod' hk hm hM₀ hMs hp hp' hq _ (hP p' p μ i j) (hA μ i j))
    (fun μ i j => by
      obtain ⟨v, hv, hW⟩ := exists_paramValue_prod' hk hm hM₀ hMs hpL hpL' hqL _
        (hP (L *ᵥ p') (L *ᵥ p) μ i j) (hB μ i j)
      obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
      exact ⟨Q, hQ, hI, hW⟩) μ

end Cov

/-! ### The base cases `j = 0, 1` -/

/-- `ℓ₀²` is a loop polynomial of degree two. -/
theorem isLoopPoly_dot : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ =>
    ((Minkowski.dot (ℓ 0) (ℓ 0) : ℝ) : ℂ) := by
  simp only [Minkowski.dot]
  push_cast
  refine IsLoopPoly.sum _ fun μ _ => IsLoopPoly.sum _ fun ν _ => ?_
  have h := (IsLoopPoly.const_mul (((Minkowski.metric μ ν : ℝ) : ℂ))
    (IsLoopPoly.coord (L := 2) (n := 1) 0 μ le_rfl)).mul (IsLoopPoly.coord 0 ν le_rfl)
  simpa only [mul_assoc] using h

theorem vecAct_smul' (L : Matrix (Fin 4) (Fin 4) ℝ) (c : ℂ)
    (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    vecAct L (fun ν => c • X ν) μ = c • vecAct L X μ := by
  simp only [vecAct, Finset.smul_sum, smul_comm c]

section Base

variable {m M₀ : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
  {p' p : Fin 4 → ℝ}
  {Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
  {α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ}

/-- The hypotheses on a covariant numerator family at `(p', p)` and `(L p', L p)`. -/
structure CovNum (m : ℝ) (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ)
    (p' p : Fin 4 → ℝ)
    (Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ) : Prop where
  pos : 0 < m
  spin : IsSpinLift L S T
  hp' : Minkowski.dot p' p' = -m ^ 2
  hp : Minkowski.dot p p = -m ^ 2
  hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)
  hp0' : 0 < p' 0
  hp0 : 0 < p 0
  h0 : 0 < (L *ᵥ p') 0
  h1 : 0 < (L *ᵥ p) 0
  poly : ∀ p' p μ i j, IsLoopPoly 2 2 fun ℓ => Nf p' p μ (ℓ 0) i j
  cov : ∀ μ ℓ, S * Nf (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => Nf p' p ν ℓ) μ
  cont : ∀ p' p μ i j, Continuous fun ℓ => Nf p' p μ ℓ i j
  bound : ∀ p' p μ i j, ∃ C : ℝ, ∀ ℓ, ‖Nf p' p μ ℓ i j‖ ≤ C * (1 + ‖ℓ‖) ^ 2
  quad : ∀ μ i j (v : Fin 3 → ℝ), ∃ β γ : ℂ, ∀ t : ℝ,
    Nf p' p μ (Fin.cons t v : Fin 4 → ℝ) i j = α μ i j * (t : ℂ) ^ 2 + β * t + γ
  quad₂ : ∀ μ i j (v : Fin 3 → ℝ), ∃ β γ : ℂ, ∀ t : ℝ,
    Nf (L *ᵥ p') (L *ᵥ p) μ (Fin.cons t v : Fin 4 → ℝ) i j = α₂ μ i j * (t : ℂ) ^ 2 + β * t + γ

namespace CovNum

variable (H : CovNum m L S T p' p Nf α α₂)
include H

theorem pL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -m ^ 2 := by
  rw [H.spin.dot_mulVec]; exact H.hp

theorem pL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -m ^ 2 := by
  rw [H.spin.dot_mulVec]; exact H.hp'

/-- The `ε → 0⁺` limit of `(ℓ²)ʲ` times a `prodIntegrand` entry is the `powM` entry. -/
theorem tendsto_powM {q' q : Fin 4 → ℝ} (hq' : Minkowski.dot q' q' = -m ^ 2)
    (hq : Minkowski.dot q q = -m ^ 2) (hq0' : 0 < q' 0) (hq0 : 0 < q 0)
    {β : Fin 4 → Fin 4 → Fin 4 → ℂ}
    (hβ : ∀ μ i j (v : Fin 3 → ℝ), ∃ b c : ℂ, ∀ t : ℝ,
      Nf q' q μ (Fin.cons t v : Fin 4 → ℝ) i j = β μ i j * (t : ℂ) ^ 2 + b * t + c)
    (hM₀ : 0 < M₀) (j : ℕ) {k : ℕ} (hjk : j ≤ k) (Ms : Fin (k + 2) → ℝ) (hMs : ∀ i, M₀ ≤ Ms i)
    (μ i i' : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (fun ℓ =>
      ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j *
        prodIntegrand (fun ℓ => Nf q' q μ ℓ i i') m Ms (fun _ => ε) ε q' q ℓ)) (𝓝[>] 0)
      (𝓝 (powM β (fun μ i j ℓ => Nf q' q μ ℓ i j) m q' q j Ms μ i i')) := by
  obtain ⟨C, hC⟩ := H.bound q' q μ i i'
  exact tendsto_efi_powInt H.pos hM₀ hq' hq hq0' hq0 (H.cont q' q μ i i') (hβ μ i i') hC
    (l := 𝓝[>] (0 : ℝ)) (ε := id) tendsto_id j k hjk Ms (fun ε _ => ε) hMs
    (fun _ => tendsto_id)

/-- **The base `j = 0`** from three photon-type masses. -/
theorem covRel_powM_zero (hM₀ : 0 < M₀) {k : ℕ} (hk : 1 ≤ k) (Ms : Fin (k + 2) → ℝ)
    (hMs : ∀ i, M₀ ≤ Ms i) :
    CovRel L S T (powM α (fun μ i j ℓ => Nf p' p μ ℓ i j) m p' p 0 Ms)
      (powM α₂ (fun μ i j ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) m (L *ᵥ p') (L *ᵥ p) 0 Ms) := by
  refine conj_prodLim' hk H.pos hM₀ hMs H.spin H.hp H.hp' H.hq Nf
    (fun p' p μ i j => (H.poly p' p μ i j).mono (by norm_num)) H.cov (fun μ i j => ?_)
    (fun μ i j => ?_)
  · simpa using H.tendsto_powM H.hp' H.hp H.hp0' H.hp0 H.quad hM₀ 0 (Nat.zero_le k) Ms hMs μ i j
  · simpa using H.tendsto_powM H.pL' H.pL H.h0 H.h1 H.quad₂ hM₀ 0 (Nat.zero_le k) Ms hMs μ i j

/-- **The base `j = 1`** from three photon-type masses: `k² N` is a numerator of degree four. -/
theorem covRel_powM_one (hM₀ : 0 < M₀) {k : ℕ} (hk : 1 ≤ k) (Ms : Fin (k + 2) → ℝ)
    (hMs : ∀ i, M₀ ≤ Ms i) :
    CovRel L S T (powM α (fun μ i j ℓ => Nf p' p μ ℓ i j) m p' p 1 Ms)
      (powM α₂ (fun μ i j ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) m (L *ᵥ p') (L *ᵥ p) 1 Ms) := by
  refine conj_prodLim' hk H.pos hM₀ hMs H.spin H.hp H.hp' H.hq
    (fun p' p μ ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) • Nf p' p μ ℓ)
    (fun p' p μ i j => ?_) (fun μ ℓ => ?_) (fun μ i j => ?_) (fun μ i j => ?_)
  · simpa only [Matrix.smul_apply, smul_eq_mul] using isLoopPoly_dot.mul (H.poly p' p μ i j)
  · rw [H.spin.dot_mulVec, Matrix.mul_smul, Matrix.smul_mul, H.cov, vecAct_smul']
  · have e := H.tendsto_powM H.hp' H.hp H.hp0' H.hp0 H.quad hM₀ 1 hk Ms hMs μ i j
    refine e.congr fun ε => congrArg _ (funext fun ℓ => ?_)
    simp only [prodIntegrand, Matrix.smul_apply, smul_eq_mul, pow_one]
    ring
  · have e := H.tendsto_powM H.pL' H.pL H.h0 H.h1 H.quad₂ hM₀ 1 hk Ms hMs μ i j
    refine e.congr fun ε => congrArg _ (funext fun ℓ => ?_)
    simp only [prodIntegrand, Matrix.smul_apply, smul_eq_mul, pow_one]
    ring

end CovNum

end Base

/-! ### Propagation to `powLimit` and `specLimit` -/

section Propagate

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
  {α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ} {E E₂ : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ}
  {m M₀ : ℝ} {q' q q₂' q₂ : Fin 4 → ℝ}

/-- **Covariance of the `powLimit` matrices** for `j ≤ k`, from the bases `j = 0, 1` at three
or more photon-type masses. -/
theorem covRel_powM' (H0 : ∀ (k : ℕ) (Ms : Fin (k + 2) → ℝ), 1 ≤ k → (∀ i, M₀ ≤ Ms i) →
      CovRel L S T (powM α E m q' q 0 Ms) (powM α₂ E₂ m q₂' q₂ 0 Ms))
    (H1 : ∀ (k : ℕ) (Ms : Fin (k + 2) → ℝ), 1 ≤ k → (∀ i, M₀ ≤ Ms i) →
      CovRel L S T (powM α E m q' q 1 Ms) (powM α₂ E₂ m q₂' q₂ 1 Ms)) :
    ∀ (j k : ℕ) (Ms : Fin (k + 2) → ℝ), j ≤ k → 1 ≤ k → (∀ i, M₀ ≤ Ms i) →
      CovRel L S T (powM α E m q' q j Ms) (powM α₂ E₂ m q₂' q₂ j Ms)
  | 0, k, Ms, _, hk, hMs => H0 k Ms hk hMs
  | 1, k, Ms, _, hk, hMs => H1 k Ms hk hMs
  | _ + 2, 0, _, h1, _, _ => absurd h1 (by omega)
  | j + 2, k + 1, Ms, h1, _, hMs => by
    rw [powM_succ, powM_succ]
    exact (covRel_powM' H0 H1 (j + 1) k (Fin.tail Ms) (by omega) (by omega)
      fun i => hMs _).sub ((covRel_powM' H0 H1 (j + 1) (k + 1) Ms (by omega) (by omega)
        hMs).smul _)

/-- **Covariance of the `specLimit` matrices** for `j ≤ k + r`, from the covariance of the
`powLimit` matrices for `j ≤ k` at three or more photon-type masses. -/
theorem covRel_specM' (hM₀ : 0 < M₀)
    (H : ∀ (j k : ℕ) (Ms : Fin (k + 2) → ℝ), j ≤ k → 1 ≤ k → (∀ i, M₀ ≤ Ms i) →
      CovRel L S T (powM α E m q' q j Ms) (powM α₂ E₂ m q₂' q₂ j Ms))
    (j : ℕ) : ∀ (r k : ℕ) (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin r → ℝ), j ≤ k + r →
      1 ≤ k → (∀ i, M₀ ≤ Ms i) → (∀ i, M₀ ≤ Msp i) → (∀ i, xs i ∈ Ioo (0 : ℝ) 1) →
      CovRel L S T (specM α E m q' q j r Ms Msp xs) (specM α₂ E₂ m q₂' q₂ j r Ms Msp xs)
  | 0, k, Ms, _, _, h1, h2, hMs, _, _ => H j k Ms h1 h2 hMs
  | r + 1, k, Ms, Msp, xs, h1, h2, hMs, hMsp, hxs => by
    rw [specM_succ, specM_succ]
    refine (covRel_specM' hM₀ H j r (k + 1) _ (Fin.tail Msp) (Fin.tail xs) (by omega)
      (by omega) (fun i => ?_) (fun i => hMsp _) (fun i => hxs _)).smul _
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]
      exact (hMsp 0).trans (specMu_ge (hM₀.trans_le (hMsp 0)) (hxs 0))
    · rw [Fin.snoc_castSucc]
      exact hMs i

end Propagate

/-- **Covariance of the `specLimit` matrices of a covariant numerator family** of degree two,
for `j ≤ k + r` and at least three photon-type masses (no upper bound on their number). -/
theorem CovNum.covRel_specM {m M₀ : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {S T : Matrix (Fin 4) (Fin 4) ℂ} {p' p : Fin 4 → ℝ}
    {Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ} (H : CovNum m L S T p' p Nf α α₂) (hM₀ : 0 < M₀)
    (j r k : ℕ) (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin r → ℝ) (hj : j ≤ k + r) (hk : 1 ≤ k)
    (hMs : ∀ i, M₀ ≤ Ms i) (hMsp : ∀ i, M₀ ≤ Msp i) (hxs : ∀ i, xs i ∈ Ioo (0 : ℝ) 1) :
    CovRel L S T (specM α (fun μ i j ℓ => Nf p' p μ ℓ i j) m p' p j r Ms Msp xs)
      (specM α₂ (fun μ i j ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ i j) m (L *ᵥ p') (L *ᵥ p) j r Ms Msp
        xs) :=
  covRel_specM' hM₀ (covRel_powM' (fun _ Ms hk hMs => H.covRel_powM_zero hM₀ hk Ms hMs)
    (fun _ Ms hk hMs => H.covRel_powM_one hM₀ hk Ms hMs)) j r k Ms Msp xs hj hk hMs hMsp hxs

end QED.ChainProof.SetACov

end
