/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Cov
public import QED.GradedProof.X1DInterp

/-!
# Set (a): covariant polynomial tensors are `X(k²) g + Y(k²) k k`

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`,
the tensor form at fixed `ε` of the two-loop vacuum polarization. Let `C(k)^{μν}` be covariant under
every reflection at every momentum (`SACov`) and a polynomial of total degree at most four in `k`.
No transversality is assumed (at fixed `ε` the class tensors are not transverse). Then

`C(k) = X(k²) g + Y(k²) k k`, `X` of degree `≤ 2` and `Y` of degree `≤ 1` in `k²`,

with coefficients that are fixed linear combinations of five entries of `C` at fixed momenta
(`SACov.eq_gk`, `saXq_eq_sum`, `saYq_eq_sum`). So a family `C x` depending on a parameter has
coefficients integrable in `x` as soon as these five entries are.

## Proof

* At `s = k² ≠ 0`, covariance gives `C = A g + B k k` at `canonVec s`
  (`QED.GradedProof.RPi4.exists_gk_rest`, `…_space`, which use no transversality), transported to
  every `k` of square `s` by one or two reflections (`saForm_of_dot_eq`). The null structure
  `n₀ n̄₀ + n̄₀ n₀` is never met: the null vectors are reached by continuity.
* Along the line `k(t) = (a, t, 0, 0)` the entries `C²²(k(t)) = A(t² - a²)` and
  `C⁰¹(k(t)) = a t B(t² - a²)` are polynomials of degree `≤ 4` in `t` (`saLine_poly`). Evenness,
  resp. oddness in `t` kill half the coefficients, so `A` is a quadratic and `B` an affine function
  of `s` on `s ≥ -a²`; letting `a` grow, `A`, `B` are the interpolants of their values at
  `s = 1, 2, 3`, resp. `s = 1, 2` (`saGlueA`, `saGlueB`).
* At `k² = 0` both sides are continuous and `k` is a limit of non-null momenta.
-/

@[expose] public section

open Complex Filter Topology
open QED.Dirac
open QED.GradedProof.VP2 (rAct TCov)
open QED.GradedProof.RPi4 (gkTensor rAct_gkTensor exists_gk_rest exists_gk_space)
open QED.GradedProof.SE2 (canonVec dot_canonVec reflect_sub_self reflect_add_self
  reflect_self_neg dot_neg_neg)
open QED.TwoLoop.Bridge (IsLoopPoly)

namespace QED.ChainProof.SetASpec

variable {C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

/-! ### Polynomials along a line -/

/-- **A polynomial of degree `≤ n` in one four-vector is a polynomial of degree `≤ n` along every
line.** -/
theorem saLine_poly {n : ℕ} {F : (Fin 1 → Fin 4 → ℝ) → ℂ} (hF : IsLoopPoly 1 n F)
    (v w : Fin 4 → ℝ) : ∃ p : ℕ → ℂ, ∀ t : ℝ,
      F (fun _ => v + t • w) = ∑ i ∈ Finset.range (n + 1), p i * (t : ℂ) ^ i := by
  classical
  obtain ⟨Q, hQ, hFQ⟩ := hF
  set g : Fin 1 × Fin 4 → Polynomial ℂ := fun x =>
    Polynomial.C ((v x.2 : ℝ) : ℂ) + Polynomial.C ((w x.2 : ℝ) : ℂ) * Polynomial.X with hg
  set P : Polynomial ℂ :=
    ∑ d ∈ Q.support, Polynomial.C (Q.coeff d) * ∏ x ∈ d.support, g x ^ d x with hP
  have hg1 : ∀ x, (g x).natDegree ≤ 1 := fun x => by
    simp only [hg]
    compute_degree
  have hdeg : P.natDegree ≤ n := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ x ∈ d.support, (g x ^ d x).natDegree ≤ ∑ x ∈ d.support, d x :=
          Finset.sum_le_sum fun x _ => Polynomial.natDegree_pow_le.trans (by
            simpa using Nat.mul_le_mul_left (d x) (hg1 x))
      _ ≤ n := (MvPolynomial.le_totalDegree hd).trans hQ
  refine ⟨P.coeff, fun t => ?_⟩
  rw [← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), hFQ, MvPolynomial.eval_eq, hP]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_pow, hg, Polynomial.eval_add, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun d _ => congrArg _ (Finset.prod_congr rfl fun x _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul]
  ring

/-! ### Covariance at every momentum -/

/-- **Covariance under every reflection**, at every momentum. -/
def SACov (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ a : Fin 4 → ℝ, Minkowski.dot a a ≠ 0 → ∀ k, C (reflect a k) = rAct a (C k)

theorem SACov.tcov (h : SACov C) (T : ℝ) : TCov T C := fun a ha k _ => h a ha k

theorem SACov.reflect_gk (hcov : SACov C) {a q : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    {A B : ℂ} (hW : C q = gkTensor A B q) : C (reflect a q) = gkTensor A B (reflect a q) := by
  rw [hcov a ha q, hW, rAct_gkTensor ha]

/-- **Transport of `A g + B k k` between momenta of equal nonzero square.** -/
theorem saForm_of_dot_eq (hcov : SACov C) {c p : Fin 4 → ℝ}
    (hs : Minkowski.dot c c = Minkowski.dot p p) (hs0 : Minkowski.dot c c ≠ 0) {A B : ℂ}
    (hW : C c = gkTensor A B c) : C p = gkTensor A B p := by
  by_cases h : Minkowski.dot (c - p) (c - p) = 0
  · have hcp : Minkowski.dot (c + p) (c + p) ≠ 0 := by
      have : Minkowski.dot (c + p) (c + p) = 4 * Minkowski.dot c c := by
        simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.add_apply] at hs h ⊢
        linarith
      rw [this]
      exact mul_ne_zero (by norm_num) hs0
    have h1 := hcov.reflect_gk hcp hW
    rw [reflect_add_self hs hs0 h] at h1
    have h2 := hcov.reflect_gk (hs ▸ hs0) h1
    rwa [reflect_self_neg (hs ▸ hs0)] at h2
  · have h1 := hcov.reflect_gk h hW
    rwa [reflect_sub_self hs h] at h1

/-- At every nonzero square, a covariant tensor is `A g + B k k` with `A`, `B` depending only on
the square. -/
theorem SACov.exists_gk (hcov : SACov C) {s : ℝ} (hs : s ≠ 0) :
    ∃ A B : ℂ, ∀ k, Minkowski.dot k k = s → C k = gkTensor A B k := by
  have hT : -(|s| + 1) ^ 2 < Minkowski.dot (canonVec s) (canonVec s) := by
    rw [dot_canonVec]
    nlinarith [abs_nonneg s, neg_abs_le s]
  obtain ⟨A, B, hAB⟩ : ∃ A B : ℂ, C (canonVec s) = gkTensor A B (canonVec s) := by
    unfold canonVec at hT ⊢
    split_ifs at hT ⊢ with h1 h2
    · exact exists_gk_rest (hcov.tcov _) (Real.sqrt_ne_zero'.mpr (by linarith)) hT
    · exact exists_gk_space (hcov.tcov _) (Real.sqrt_ne_zero'.mpr h2) hT
    · exact absurd (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) hs
  exact ⟨A, B, fun k hk => saForm_of_dot_eq hcov (by rw [dot_canonVec, hk])
    (by rw [dot_canonVec]; exact hs) hAB⟩

/-! ### Gluing along lines -/

/-- **An even quartic along every line is a quadratic in `s`.** -/
theorem saGlueA {A : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c) {p : ℕ → ℂ}
    (h : ∀ t : ℝ, t ^ 2 - c ≠ 0 → A (t ^ 2 - c) = ∑ i ∈ Finset.range 5, p i * (t : ℂ) ^ i)
    {s : ℝ} (hs : -c ≤ s) (hs0 : s ≠ 0) :
    A s = A 1 * (((s : ℂ) - 2) * ((s : ℂ) - 3) / 2) - A 2 * (((s : ℂ) - 1) * ((s : ℂ) - 3)) +
      A 3 * (((s : ℂ) - 1) * ((s : ℂ) - 2) / 2) := by
  have hodd : ∀ t : ℝ, t ^ 2 - c ≠ 0 → p 1 * t + p 3 * (t : ℂ) ^ 3 = 0 := by
    intro t ht
    have h1 := h t ht
    have h2 := h (-t) (by rwa [neg_sq])
    rw [neg_sq] at h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ofReal_neg] at h1 h2
    linear_combination (h2 - h1) / 2
  have hroot : ∀ j : ℝ, 0 < j → p 1 + p 3 * ((c : ℂ) + j) = 0 := by
    intro j hj
    set t := Real.sqrt (c + j)
    have ht2 : t ^ 2 = c + j := Real.sq_sqrt (by linarith)
    have ht0 : (t : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by linarith)).ne'
    have ht2c : (t : ℂ) ^ 2 = c + j := by exact_mod_cast ht2
    have e := hodd t (by rw [ht2]; linarith)
    have e' : (t : ℂ) * (p 1 + p 3 * ((c : ℂ) + j)) = 0 := by
      rw [← ht2c]
      linear_combination e
    exact (mul_eq_zero.mp e').resolve_left ht0
  have r1 := hroot 1 one_pos
  have r2 := hroot 2 two_pos
  have hp3 : p 3 = 0 := by push_cast at r1 r2; linear_combination r2 - r1
  have hp1 : p 1 = 0 := by rw [hp3] at r1; linear_combination r1
  have hA : ∀ u : ℝ, -c ≤ u → u ≠ 0 →
      A u = p 0 + p 2 * ((u : ℂ) + c) + p 4 * ((u : ℂ) + c) ^ 2 := by
    intro u hu hu0
    set t := Real.sqrt (u + c)
    have ht2 : t ^ 2 = u + c := Real.sq_sqrt (by linarith)
    have ht2c : (t : ℂ) ^ 2 = u + c := by exact_mod_cast ht2
    have e := h t (by rw [ht2]; simpa using hu0)
    rw [show t ^ 2 - c = u by rw [ht2]; ring] at e
    rw [e]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hp1, hp3]
    rw [show (t : ℂ) ^ 4 = ((t : ℂ) ^ 2) ^ 2 by ring, ht2c]
    ring
  rw [hA s hs hs0, hA 1 (by linarith) one_ne_zero, hA 2 (by linarith) two_ne_zero,
    hA 3 (by linarith) three_ne_zero]
  push_cast
  ring

/-- **An odd quartic `a t B(t² - a²)` along every line makes `B` affine in `s`.** -/
theorem saGlueB {B : ℝ → ℂ} {a : ℝ} (ha : 0 < a) {p : ℕ → ℂ}
    (h : ∀ t : ℝ, t ^ 2 - a ^ 2 ≠ 0 →
      B (t ^ 2 - a ^ 2) * ((a : ℂ) * t) = ∑ i ∈ Finset.range 5, p i * (t : ℂ) ^ i)
    {s : ℝ} (hs : -a ^ 2 < s) (hs0 : s ≠ 0) :
    B s = B 1 * (2 - (s : ℂ)) + B 2 * ((s : ℂ) - 1) := by
  have heven : ∀ t : ℝ, t ^ 2 - a ^ 2 ≠ 0 →
      p 0 + p 2 * (t : ℂ) ^ 2 + p 4 * ((t : ℂ) ^ 2) ^ 2 = 0 := by
    intro t ht
    have h1 := h t ht
    have h2 := h (-t) (by rwa [neg_sq])
    rw [neg_sq] at h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ofReal_neg] at h1 h2
    linear_combination (-h2 - h1) / 2
  have hnode : ∀ j : ℝ, 0 < j →
      p 0 + p 2 * ((a : ℂ) ^ 2 + j) + p 4 * ((a : ℂ) ^ 2 + j) ^ 2 = 0 := by
    intro j hj
    set t := Real.sqrt (a ^ 2 + j)
    have ht2 : t ^ 2 = a ^ 2 + j := Real.sq_sqrt (by positivity)
    have ht2c : (t : ℂ) ^ 2 = (a : ℂ) ^ 2 + j := by exact_mod_cast ht2
    have e := heven t (by rw [ht2]; linarith)
    rwa [ht2c] at e
  have n1 := hnode 1 one_pos
  have n2 := hnode 2 two_pos
  have n3 := hnode 3 three_pos
  push_cast at n1 n2 n3
  have hp4 : p 4 = 0 := by linear_combination (n1 - 2 * n2 + n3) / 2
  have hp2 : p 2 = 0 := by
    rw [hp4] at n1 n2
    linear_combination n2 - n1
  have hB : ∀ u : ℝ, -a ^ 2 < u → u ≠ 0 →
      B u = (p 1 + p 3 * ((u : ℂ) + (a : ℂ) ^ 2)) / a := by
    intro u hu hu0
    set t := Real.sqrt (u + a ^ 2)
    have htp : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have ht2 : t ^ 2 = u + a ^ 2 := Real.sq_sqrt (by linarith)
    have ht2c : (t : ℂ) ^ 2 = u + (a : ℂ) ^ 2 := by exact_mod_cast ht2
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have e := h t (by rw [ht2]; simpa using hu0)
    rw [show t ^ 2 - a ^ 2 = u by rw [ht2]; ring] at e
    have ev := heven t (by rw [ht2]; simpa using hu0)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e
    have e' : (t : ℂ) * ((a : ℂ) * B u - (p 1 + p 3 * ((u : ℂ) + (a : ℂ) ^ 2))) = 0 := by
      rw [← ht2c]
      linear_combination e + ev
    have e'' := sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_left ht0)
    field_simp
    linear_combination e''
  rw [hB s (by linarith) hs0, hB 1 (by nlinarith) one_ne_zero, hB 2 (by nlinarith) two_ne_zero]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  push_cast
  ring

/-! ### The coefficients -/

/-- The line `(a, t, 0, 0)`. -/
noncomputable def saLineVec (a t : ℝ) : Fin 4 → ℝ := ![a, 0, 0, 0] + t • ![0, 1, 0, 0]

theorem saLineVec_apply (a t : ℝ) :
    saLineVec a t = ![a, t, 0, 0] := by
  funext μ
  fin_cases μ <;> simp [saLineVec]

theorem dot_saLineVec (a t : ℝ) :
    Minkowski.dot (saLineVec a t) (saLineVec a t) = t ^ 2 - a ^ 2 := by
  rw [saLineVec_apply, Minkowski.dot_eq]
  simp
  ring

/-- The value `A(j)` read at `(0, √j, 0, 0)`. -/
noncomputable def saAv (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (j : ℝ) : ℂ :=
  C (saLineVec 0 (Real.sqrt j)) 2 2

/-- The value `B(j)` read at `(1, √(j + 1), 0, 0)`. -/
noncomputable def saBv (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (j : ℝ) : ℂ :=
  C (saLineVec 1 (Real.sqrt (j + 1))) 0 1 / (Real.sqrt (j + 1) : ℂ)

/-- **The coefficient `X(s)` of `g`**: the interpolant of `A(1), A(2), A(3)`. -/
noncomputable def saXq (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (s : ℝ) : ℂ :=
  saAv C 1 * (((s : ℂ) - 2) * ((s : ℂ) - 3) / 2) - saAv C 2 * (((s : ℂ) - 1) * ((s : ℂ) - 3)) +
    saAv C 3 * (((s : ℂ) - 1) * ((s : ℂ) - 2) / 2)

/-- **The coefficient `Y(s)` of `k k`**: the interpolant of `B(1), B(2)`. -/
noncomputable def saYq (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (s : ℝ) : ℂ :=
  saBv C 1 * (2 - (s : ℂ)) + saBv C 2 * ((s : ℂ) - 1)

/-- The coefficients of `X` in the monomials `1, s, s²`. -/
noncomputable def saX (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Fin 3 → ℂ :=
  ![3 * saAv C 1 - 3 * saAv C 2 + saAv C 3, -(5 / 2) * saAv C 1 + 4 * saAv C 2 -
    (3 / 2) * saAv C 3, saAv C 1 / 2 - saAv C 2 + saAv C 3 / 2]

/-- The coefficients of `Y` in the monomials `1, s`. -/
noncomputable def saY (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Fin 2 → ℂ :=
  ![2 * saBv C 1 - saBv C 2, saBv C 2 - saBv C 1]

theorem saXq_eq_sum (s : ℝ) : saXq C s = ∑ j : Fin 3, saX C j * (s : ℂ) ^ (j : ℕ) := by
  simp only [saXq, saX, Fin.sum_univ_three]
  simp
  ring

theorem saYq_eq_sum (s : ℝ) : saYq C s = ∑ j : Fin 2, saY C j * (s : ℂ) ^ (j : ℕ) := by
  simp only [saYq, saY, Fin.sum_univ_two]
  simp
  ring

/-! ### The tensor form -/

theorem gkTensor_saLineVec_22 (A B : ℂ) (a t : ℝ) : gkTensor A B (saLineVec a t) 2 2 = A := by
  simp [gkTensor, saLineVec_apply, Minkowski.metric]

theorem gkTensor_saLineVec_01 (A B : ℂ) (a t : ℝ) :
    gkTensor A B (saLineVec a t) 0 1 = B * ((a : ℂ) * t) := by
  simp [gkTensor, saLineVec_apply, Minkowski.metric]

/-- **The tensor form off the light cone.** -/
theorem SACov.eq_gk_of_ne (hcov : SACov C) (hpoly : ∀ μ ν, IsLoopPoly 1 4 fun y => C (y 0) μ ν)
    {k : Fin 4 → ℝ} (hk : Minkowski.dot k k ≠ 0) :
    C k = gkTensor (saXq C (Minkowski.dot k k)) (saYq C (Minkowski.dot k k)) k := by
  classical
  choose! A B hAB using fun s (hs : s ≠ 0) => hcov.exists_gk hs
  set s := Minkowski.dot k k with hsdef
  have hline : ∀ a t : ℝ, t ^ 2 - a ^ 2 ≠ 0 →
      C (saLineVec a t) = gkTensor (A (t ^ 2 - a ^ 2)) (B (t ^ 2 - a ^ 2)) (saLineVec a t) :=
    fun a t ht => hAB _ ht _ (dot_saLineVec a t)
  -- the values at the nodes
  have hAv : ∀ j : ℝ, 0 < j → saAv C j = A j := by
    intro j hj
    have hj2 : Real.sqrt j ^ 2 - (0 : ℝ) ^ 2 = j := by rw [Real.sq_sqrt hj.le]; ring
    have h := hline 0 (Real.sqrt j) (by rw [hj2]; exact hj.ne')
    rw [saAv, h, gkTensor_saLineVec_22, hj2]
  have hBv : ∀ j : ℝ, 0 < j → saBv C j = B j := by
    intro j hj
    have hj2 : Real.sqrt (j + 1) ^ 2 - (1 : ℝ) ^ 2 = j := by
      rw [Real.sq_sqrt (by linarith)]; ring
    have h := hline 1 (Real.sqrt (j + 1)) (by rw [hj2]; exact hj.ne')
    have hr : (Real.sqrt (j + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by linarith)).ne'
    rw [saBv, h, gkTensor_saLineVec_01, hj2]
    field_simp
    push_cast
    ring
  -- `A` along the line through `(√|s|, 0, 0, 0)`
  have hXs : A s = saXq C s := by
    set a := Real.sqrt |s|
    have ha2 : a ^ 2 = |s| := Real.sq_sqrt (abs_nonneg s)
    obtain ⟨p, hp⟩ := saLine_poly (hpoly 2 2) ![a, 0, 0, 0] ![0, 1, 0, 0]
    have hA := saGlueA (A := A) (c := |s|) (abs_nonneg s) (p := p) (fun t ht => by
      have h := hline a t (by rwa [ha2])
      rw [ha2] at h
      have := hp t
      rw [← this, ← gkTensor_saLineVec_22 (A (t ^ 2 - |s|)) (B (t ^ 2 - |s|)) a t, ← h]
      rfl) (neg_abs_le s) hk
    rw [hA, saXq, hAv 1 one_pos, hAv 2 two_pos, hAv 3 three_pos]
  have hYs : B s = saYq C s := by
    set a := Real.sqrt (|s| + 1)
    have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = |s| + 1 := Real.sq_sqrt (by positivity)
    obtain ⟨p, hp⟩ := saLine_poly (hpoly 0 1) ![a, 0, 0, 0] ![0, 1, 0, 0]
    have hB := saGlueB (B := B) hapos (p := p) (fun t ht => by
      have h := hline a t ht
      have := hp t
      rw [← gkTensor_saLineVec_01, ← h, ← this]
      rfl) (by rw [ha2]; linarith [neg_abs_le s]) hk
    rw [hB, saYq, hBv 1 one_pos, hBv 2 two_pos]
  rw [hAB s hk k rfl, hXs, hYs]

theorem continuous_dot_self : Continuous fun k : Fin 4 → ℝ => Minkowski.dot k k := by
  simp only [Minkowski.dot_eq]
  fun_prop

theorem continuous_gkTensor_saq (μ ν : Fin 4) :
    Continuous fun k : Fin 4 → ℝ =>
      gkTensor (saXq C (Minkowski.dot k k)) (saYq C (Minkowski.dot k k)) k μ ν := by
  have hd : Continuous fun k : Fin 4 → ℝ => ((Minkowski.dot k k : ℝ) : ℂ) :=
    continuous_ofReal.comp continuous_dot_self
  simp only [gkTensor, saXq, saYq]
  have hkk : Continuous fun k : Fin 4 → ℝ => ((k μ * k ν : ℝ) : ℂ) :=
    continuous_ofReal.comp ((continuous_apply μ).mul (continuous_apply ν))
  fun_prop

/-- **Covariant tensors of degree at most four in `k` are `X(k²) g + Y(k²) k k`**, at every
momentum, with `X`, `Y` the interpolants `saXq`, `saYq` of five fixed entries. -/
theorem SACov.eq_gk (hcov : SACov C) (hpoly : ∀ μ ν, IsLoopPoly 1 4 fun y => C (y 0) μ ν)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    C k μ ν = gkTensor (saXq C (Minkowski.dot k k)) (saYq C (Minkowski.dot k k)) k μ ν := by
  by_cases hk : Minkowski.dot k k = 0
  swap
  · rw [hcov.eq_gk_of_ne hpoly hk]
  set σ : ℝ := if 0 ≤ k 2 then 1 else -1
  have hσ : σ ^ 2 = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσk : 0 ≤ σ * k 2 := by
    simp only [σ]
    split_ifs with h
    · linarith
    · linarith
  set e : Fin 4 → ℝ := ![0, 0, σ, 0]
  have hdot : ∀ t : ℝ,
      Minkowski.dot (k + t • e) (k + t • e) = 2 * t * (σ * k 2) + t ^ 2 * σ ^ 2 := by
    intro t
    have := hk
    rw [Minkowski.dot_eq] at this ⊢
    simp [e]
    linear_combination this
  have hpath : Tendsto (fun t : ℝ => k + t • e) (𝓝[>] 0) (𝓝 k) := by
    have : Continuous fun t : ℝ => k + t • e := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hCc : Continuous fun k : Fin 4 → ℝ => C k μ ν := by
    have h := QED.GradedProof.X1D.IsLoopPoly.continuous (hpoly μ ν)
    exact h.comp (continuous_pi fun _ => continuous_id)
  refine tendsto_nhds_unique ((hCc.tendsto k).comp hpath) ?_
  refine (((continuous_gkTensor_saq μ ν).tendsto k).comp hpath).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hne : Minkowski.dot (k + t • e) (k + t • e) ≠ 0 := by
    rw [hdot, hσ]
    positivity
  exact (congrFun (congrFun (hcov.eq_gk_of_ne hpoly hne) μ) ν).symm

end QED.ChainProof.SetASpec

end
