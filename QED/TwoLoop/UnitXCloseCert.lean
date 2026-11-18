/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseNewton
public import QED.TwoLoop.UnitXGraphReduce
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Checkable certificates for the domination of the crossed-ladder integrand

A polynomial in the five group sums is stored as a list of terms `(c, n, κ)`: coefficient `c`,
exponent vector `n`, and for each index `i` the position `κ i` of a certificate in a list of
certificates. A certificate is a pair `(Θ, Φ)` of natural weight vectors with sums `N`; it gives
`p = (1/N) ∑ Θⱼ (exponents of U)` and `q = (1/N) ∑ Φⱼ (exponents of Ẽ)`. The check `termOK`
(decidable, natural-number arithmetic) asks `4 N pₖ + d N qₖ ≤ N (nₖ + [k = i]) + S` for all `k`.

* `certBound`: one checked certificate gives `zᵢ ∏ zₖ^{nₖ} / (U⁴ Ẽᵈ) ≤ ∏ zₖ^{-S/N}`;
* `listBound`: if every term of the list passes the check for every `i`, then for `z` in the open
  simplex, `(∑ |c| ∏ zₖ^{nₖ}) / (U⁴ Ẽᵈ) ≤ 5 (∑ |c|) ∏ zₖ^{-S/N}`.
-/

@[expose] public section

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph

/-- A certificate: weights `Θ` on the monomials of `U` and `Φ` on those of `Ẽ`. -/
abbrev Cert := (Fin 8 → ℕ) × (Fin 13 → ℕ)

/-- A term: coefficient, exponents, certificate positions. -/
abbrev Term := ℚ × (Fin 5 → ℕ) × (Fin 5 → ℕ)

/-- The check of one certificate for the exponent `n` and the index `i`. -/
def certOK (N S d : ℕ) (cc : Cert) (n : Fin 5 → ℕ) (i : Fin 5) : Bool :=
  (List.ofFn cc.1).sum == N && (List.ofFn cc.2).sum == N &&
    (List.finRange 5).all fun k =>
      decide (4 * (List.ofFn fun j => cc.1 j * UExp j k).sum +
          d * (List.ofFn fun j => cc.2 j * EExp j k).sum ≤
        N * (n k + if k = i then 1 else 0) + S)

/-- The check of one term, for all five indices. -/
def termOK (N S d : ℕ) (certs : List Cert) (t : Term) : Bool :=
  (List.finRange 5).all fun i => certOK N S d (certs.getD (t.2.2 i) (0, 0)) t.2.1 i

/-- The value `∑ c ∏ zₖ^{nₖ}` of a term list. -/
noncomputable def evalTerms (L : List Term) (z : Fin 5 → ℝ) : ℝ :=
  (L.map fun t => (t.1 : ℝ) * ∏ k, z k ^ t.2.1 k).sum

theorem evalTerms_append (L₁ L₂ : List Term) (z : Fin 5 → ℝ) :
    evalTerms (L₁ ++ L₂) z = evalTerms L₁ z + evalTerms L₂ z := by
  simp [evalTerms, List.map_append, List.sum_append]

/-- The value `∑ |c| ∏ zₖ^{nₖ}` of a term list. -/
noncomputable def evalAbs (L : List Term) (z : Fin 5 → ℝ) : ℝ :=
  (L.map fun t => |(t.1 : ℝ)| * ∏ k, z k ^ t.2.1 k).sum

/-- `∑ |c|`. -/
noncomputable def absSum (L : List Term) : ℝ := (L.map fun t => |(t.1 : ℝ)|).sum

theorem abs_evalTerms_le {z : Fin 5 → ℝ} (hz : ∀ k, 0 ≤ z k) (L : List Term) :
    |evalTerms L z| ≤ evalAbs L z := by
  induction L with
  | nil => simp [evalTerms, evalAbs]
  | cons t L ih =>
    simp only [evalTerms, evalAbs, List.map_cons, List.sum_cons] at ih ⊢
    have hp : 0 ≤ ∏ k, z k ^ t.2.1 k := Finset.prod_nonneg fun k _ => pow_nonneg (hz k) _
    calc _ ≤ |(t.1 : ℝ) * ∏ k, z k ^ t.2.1 k| + |(L.map fun t => (t.1 : ℝ) *
          ∏ k, z k ^ t.2.1 k).sum| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_nonneg hp]; linarith

theorem certOK_iff {N S d : ℕ} {cc : Cert} {n : Fin 5 → ℕ} {i : Fin 5} :
    certOK N S d cc n i = true ↔ (∑ j, cc.1 j = N ∧ ∑ j, cc.2 j = N) ∧
      ∀ k, 4 * ∑ j, cc.1 j * UExp j k + d * ∑ j, cc.2 j * EExp j k ≤
        N * (n k + if k = i then 1 else 0) + S := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    decide_eq_true_eq, true_implies, List.sum_ofFn]

/-- **One checked certificate.** -/
theorem certBound {A M c a b : ℝ} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hz1 : ∀ k, gz A M c a b k ≤ 1) {N S d : ℕ} (hN : 0 < N) {cc : Cert} {n : Fin 5 → ℕ}
    {i : Fin 5} (h : certOK N S d cc n i = true) :
    gz A M c a b i * (∏ k, gz A M c a b k ^ n k) / (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) ≤
      mono (gz A M c a b) (fun _ => -((S : ℝ) / N)) := by
  rw [certOK_iff] at h
  obtain ⟨⟨hΘ, hΦ⟩, hk⟩ := h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set θ : Fin 8 → ℝ := fun j => (cc.1 j : ℝ) / N
  set φ : Fin 13 → ℝ := fun j => (cc.2 j : ℝ) / N
  have hθ1 : ∑ j, θ j = 1 := by
    simp only [θ, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hNr.ne']
    exact_mod_cast hΘ
  have hφ1 : ∑ j, φ j = 1 := by
    simp only [φ, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hNr.ne']
    exact_mod_cast hΦ
  have hU := mono_le_gXU hA hM hc ha hb θ (fun j => by positivity) hθ1
  have hE := mono_le_gXEn hA hM hc ha hb φ (fun j => by positivity) hφ1
  refine term_le (gz_pos hA hM hc ha hb) hz1 hU hE d n i fun k => ?_
  have hk' : (4 * ∑ j, (cc.1 j : ℝ) * UExp j k + d * ∑ j, (cc.2 j : ℝ) * EExp j k) ≤
      N * ((n k : ℝ) + if k = i then 1 else 0) + S := by
    have := hk k
    split_ifs at this ⊢ <;> exact_mod_cast this
  have e1 : (∑ j, θ j • UExpR j) k = (∑ j, (cc.1 j : ℝ) * UExp j k) / N := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, θ, UExpR, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : (∑ j, φ j • EExpR j) k = (∑ j, (cc.2 j : ℝ) * EExp j k) / N := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, φ, EExpR, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  have key : -((S : ℝ) / N) * N ≤
      ((n k : ℝ) + (if k = i then 1 else 0) - 4 * ((∑ j, (cc.1 j : ℝ) * UExp j k) / N) -
        d * ((∑ j, (cc.2 j : ℝ) * EExp j k) / N)) * N := by
    field_simp
    linarith
  exact le_of_mul_le_mul_right key hNr

/-- `∑ᵢ zᵢ = 1` on the open simplex, so `X = ∑ᵢ zᵢ X`. -/
theorem listBound {A M c a b : ℝ} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hz1 : ∀ k, gz A M c a b k ≤ 1) (hsum : ∑ k, gz A M c a b k = 1) {N S d : ℕ} (hN : 0 < N)
    {certs : List Cert} {L : List Term} (hL : L.all (termOK N S d certs) = true) :
    evalAbs L (gz A M c a b) / (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) ≤
      5 * absSum L * mono (gz A M c a b) (fun _ => -((S : ℝ) / N)) := by
  have hz := gz_pos hA hM hc ha hb
  have hD : 0 < gXU A M c a b ^ 4 * gXEn A M c a b ^ d := by
    have := gXU_pos hA hM hc ha hb
    have : 0 < gXEn A M c a b := by unfold gXEn; positivity
    positivity
  set z := gz A M c a b
  set m := mono z (fun _ => -((S : ℝ) / N))
  -- each index `i`
  have hi : ∀ i, z i * evalAbs L z / (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) ≤ absSum L * m := by
    intro i
    induction L with
    | nil => simp [evalAbs, absSum]
    | cons t L ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hL
      have ht : certOK N S d (certs.getD (t.2.2 i) (0, 0)) t.2.1 i = true := by
        have := hL.1
        simp only [termOK, List.all_eq_true, List.mem_finRange, true_implies] at this
        exact this i
      have hb1 := certBound hA hM hc ha hb hz1 hN ht
      have ih' := ih hL.2
      simp only [evalAbs, absSum, List.map_cons, List.sum_cons] at ih' ⊢
      have e : z i * (|(t.1 : ℝ)| * ∏ k, z k ^ t.2.1 k +
          (L.map fun t => |(t.1 : ℝ)| * ∏ k, z k ^ t.2.1 k).sum) /
          (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) =
          |(t.1 : ℝ)| * (z i * (∏ k, z k ^ t.2.1 k) / (gXU A M c a b ^ 4 * gXEn A M c a b ^ d)) +
          z i * (L.map fun t => |(t.1 : ℝ)| * ∏ k, z k ^ t.2.1 k).sum /
            (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) := by
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hb1 (abs_nonneg (t.1 : ℝ))
      nlinarith
  have e : evalAbs L z / (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) =
      ∑ i, z i * evalAbs L z / (gXU A M c a b ^ 4 * gXEn A M c a b ^ d) := by
    rw [← Finset.sum_div, ← Finset.sum_mul, hsum, one_mul]
  rw [e]
  calc _ ≤ ∑ _i : Fin 5, absSum L * m := Finset.sum_le_sum fun i _ => hi i
    _ = 5 * absSum L * m := by simp; ring

end QED.TwoLoop.UnitXClose

end
