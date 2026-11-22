/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW6
public import QED.GradedProof.RPi4FaceIdRayBNum
public import QED.GradedProof.X1DInterp
public import QED.TwoLoop.LoopPolySubst
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# (R-Π₄) step L10, B-inc: the Euler numerator

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. Along the ray the numerator `N(k)(ℓ)` of a piece is differentiated
through `t ↦ N(t k)(t ℓ)`. If `N` has degree `≤ d` in `k` and `≤ e` in `ℓ`, Lagrange
interpolation in the two scales (nodes `node d i`, `node e j`) writes

`N(a k)(b ℓ) = ∑ᵢⱼ ℓᵢ(a) ℓⱼ(b) N(tᵢ k)(tⱼ ℓ)`,

so `t ↦ N(t k)(t ℓ)` is a polynomial and `½ ∂ₜ|₁ - c` of it is the **Euler numerator**
`eulerN d e c N k ℓ = ∑ᵢⱼ wᵢⱼ N(tᵢ k)(tⱼ ℓ)` with fixed weights. It keeps every hypothesis on the
numerator that the rate (B) of a merged piece uses (degree in `ℓ`, refined bound, degree in `k`,
representatives with the loop degrees), since these are closed under scaling `k` or `ℓ` and
under finite sums:

* `faceIdRayE_eq_scale`, `faceIdRayE_eq_scale₂`: interpolation in the scale(s);
* `faceIdRayE_hasDerivAt`: the derivative of `t ↦ N(t k)(t ℓ)`;
* `eulerW`, `eulerN`, `faceIdRayE_eulerN_eq`: the Euler numerator;
* `faceIdRayE_isLoopPoly_smul`, `faceIdRayE_refinedBound_smul` and the closure lemmas;
* **`faceIdRayE_vpPiece_of_nodes`**: the rate (B) of the piece with the Euler numerator.
-/

@[expose] public section

open Complex Polynomial Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit (node lbasis)
open QED.TwoLoop.MassScaling (dilateQ eval_dilateQ)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.GradedProof.X1D (sum_node_pow_mul_lbasis)

/-! ### Interpolation in the scale -/

/-- **Interpolation in the scale**: for `F` of total degree `≤ e`,
`F(b y) = ∑ⱼ ℓⱼ(b) F(tⱼ y)` with the nodes `tⱼ = node e j`. -/
theorem faceIdRayE_eq_scale {L e : ℕ} {F : (Fin L → Fin 4 → ℝ) → ℂ} (hF : IsLoopPoly L e F)
    (y : Fin L → Fin 4 → ℝ) (b : ℝ) :
    F (b • y) = ∑ j : Fin (e + 1), (lbasis e j).eval (b : ℂ) * F (node e j • y) := by
  classical
  obtain ⟨Q, hQ, hFQ⟩ := hF
  have hp : ∀ (t : ℝ) (d : Fin L × Fin 4 →₀ ℕ), ∏ v, (((t • y) v.1 v.2 : ℝ) : ℂ) ^ d v =
      (t : ℂ) ^ (∑ v, d v) * ∏ v, ((y v.1 v.2 : ℝ) : ℂ) ^ d v := fun t d => by
    simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  simp only [hFQ, MvPolynomial.eval_eq', hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ v, d v ≤ e := by
    have h := (MvPolynomial.le_totalDegree hd).trans hQ
    rwa [Finsupp.sum_fintype _ _ fun _ => rfl] at h
  rw [← sum_node_pow_mul_lbasis hdeg (b : ℂ), Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Interpolation in the two scales.** -/
theorem faceIdRayE_eq_scale₂ {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {d e : ℕ}
    (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) (hpoly : ∀ k, IsLoopPoly 2 e (N k))
    (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : ℝ) :
    N (a • k) (b • ℓ) = ∑ ij : Fin (d + 1) × Fin (e + 1),
      (lbasis d ij.1).eval (a : ℂ) * (lbasis e ij.2).eval (b : ℂ) *
        N (node d ij.1 • k) (node e ij.2 • ℓ) := by
  have h1 := faceIdRayE_eq_scale (hk (b • ℓ)) (fun _ => k) a
  simp only [Pi.smul_apply] at h1
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [faceIdRayE_eq_scale (hpoly _) ℓ b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The derivative of `t ↦ N(t k)(t ℓ)`.** -/
theorem faceIdRayE_hasDerivAt {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {d e : ℕ}
    (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) (hpoly : ∀ k, IsLoopPoly 2 e (N k))
    (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => N (s • k) (s • ℓ)) (∑ ij : Fin (d + 1) × Fin (e + 1),
      ((lbasis d ij.1).derivative.eval (t : ℂ) * (lbasis e ij.2).eval (t : ℂ) +
        (lbasis d ij.1).eval (t : ℂ) * (lbasis e ij.2).derivative.eval (t : ℂ)) *
        N (node d ij.1 • k) (node e ij.2 • ℓ)) t := by
  have hfun : (fun s : ℝ => N (s • k) (s • ℓ)) = fun s : ℝ => ∑ ij : Fin (d + 1) × Fin (e + 1),
      (lbasis d ij.1).eval (s : ℂ) * (lbasis e ij.2).eval (s : ℂ) *
        N (node d ij.1 • k) (node e ij.2 • ℓ) :=
    funext fun s => faceIdRayE_eq_scale₂ hk hpoly k ℓ s s
  rw [hfun]
  exact HasDerivAt.fun_sum fun ij _ =>
    ((((lbasis d ij.1).hasDerivAt (t : ℂ)).comp_ofReal.mul
      ((lbasis e ij.2).hasDerivAt (t : ℂ)).comp_ofReal).mul_const _)

/-! ### The Euler numerator -/

/-- The weights of the Euler numerator: `½ ∂ₜ|₁ (ℓᵢ ℓⱼ) - c ℓᵢ(1) ℓⱼ(1)`. -/
noncomputable def eulerW (d e : ℕ) (c : ℂ) (i : Fin (d + 1)) (j : Fin (e + 1)) : ℂ :=
  ((lbasis d i).derivative.eval 1 * (lbasis e j).eval 1 +
      (lbasis d i).eval 1 * (lbasis e j).derivative.eval 1) / 2 -
    c * ((lbasis d i).eval 1 * (lbasis e j).eval 1)

/-- **The Euler numerator** `∑ᵢⱼ wᵢⱼ N(tᵢ k)(tⱼ ℓ)`; it is `½ ∂ₜ|₁ N(t k)(t ℓ) - c N(k)(ℓ)`
(`faceIdRayE_eulerN_eq`). -/
noncomputable def eulerN (d e : ℕ) (c : ℂ) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ ij : Fin (d + 1) × Fin (e + 1), eulerW d e c ij.1 ij.2 * N (node d ij.1 • k) (node e ij.2 • ℓ)

/-- **The Euler numerator is `½ ∂ₜ|₁ N(t k)(t ℓ) - c N(k)(ℓ)`.** -/
theorem faceIdRayE_eulerN_eq {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {d e : ℕ}
    (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) (hpoly : ∀ k, IsLoopPoly 2 e (N k))
    (c : ℂ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    eulerN d e c N k ℓ = (∑ ij : Fin (d + 1) × Fin (e + 1),
      ((lbasis d ij.1).derivative.eval 1 * (lbasis e ij.2).eval 1 +
        (lbasis d ij.1).eval 1 * (lbasis e ij.2).derivative.eval 1) *
        N (node d ij.1 • k) (node e ij.2 • ℓ)) / 2 - c * N k ℓ := by
  have h1 := faceIdRayE_eq_scale₂ hk hpoly k ℓ 1 1
  simp only [one_smul, ofReal_one] at h1
  rw [h1, eulerN, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [eulerW]
  ring

/-! ### Closure under scaling -/

/-- Scaling the argument keeps the total degree. -/
theorem faceIdRayE_isLoopPoly_smul {L n : ℕ} {F : (Fin L → Fin 4 → ℝ) → ℂ}
    (hF : IsLoopPoly L n F) (t : ℝ) : IsLoopPoly L n fun y => F (t • y) := by
  refine hF.comp fun s ν => ?_
  have e : (fun y : Fin L → Fin 4 → ℝ => (((t • y) s ν : ℝ) : ℂ)) =
      fun y => (t : ℂ) * ((y s ν : ℝ) : ℂ) := by
    funext y
    simp
  rw [e]
  exact (IsLoopPoly.coord s ν le_rfl).const_mul _

/-- Scaling the loop momenta keeps the refined bound. -/
theorem faceIdRayE_refinedBound_smul {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    {E : Finset (Fin (m + 1))} {k : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : RefinedBound α E k F)
    (t : ℝ) : RefinedBound α E k fun ℓ => F (t • ℓ) := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨C * (1 + |t|) ^ k, by positivity, fun A hA ℓ => (hF A hA (t • ℓ)).trans ?_⟩
  have hL := loopNorm_nonneg hA ℓ
  have hs : Real.sqrt (1 + loopNorm A (t • ℓ)) ≤ (1 + |t|) * Real.sqrt (1 + loopNorm A ℓ) := by
    rw [loopNorm_smul, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + |t|),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have ht : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [ht]
    have := abs_nonneg t
    nlinarith [mul_nonneg this hL]
  have hw := lineWeight_nonneg α E A
  calc C * lineWeight α E A * Real.sqrt (1 + loopNorm A (t • ℓ)) ^ k
      ≤ C * lineWeight α E A * ((1 + |t|) * Real.sqrt (1 + loopNorm A ℓ)) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs k)
          (mul_nonneg hC hw)
    _ = _ := by rw [mul_pow]; ring

section Closure

variable {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {d e : ℕ} (c : ℂ)

theorem faceIdRayE_isLoopPoly_eulerN (hpoly : ∀ k, IsLoopPoly 2 e (N k)) (k : Fin 4 → ℝ) :
    IsLoopPoly 2 e (eulerN d e c N k) :=
  IsLoopPoly.sum _ fun ij _ =>
    (faceIdRayE_isLoopPoly_smul (hpoly _) (node e ij.2)).const_mul _

theorem faceIdRayE_refinedBound_eulerN {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    {E : Finset (Fin (m + 1))} {q : ℕ} (hB : ∀ k, RefinedBound α E q (N k)) (k : Fin 4 → ℝ) :
    RefinedBound α E q (eulerN d e c N k) :=
  RefinedBound.sum _ fun ij _ =>
    (faceIdRayE_refinedBound_smul (hB _) (node e ij.2)).const_mul _

theorem faceIdRayE_isLoopPoly_k_eulerN (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : IsLoopPoly 1 d fun y => eulerN d e c N (y 0) ℓ :=
  IsLoopPoly.sum _ fun ij _ =>
    (faceIdRayE_isLoopPoly_smul (hk (node e ij.2 • ℓ)) (node d ij.1)).const_mul _

/-- **Representatives of the Euler numerator** with the loop degrees of those of `N`. -/
theorem faceIdRayE_exists_eulerN {t : Fin 2} {d' : ℕ} {p : Prop}
    (hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe t d' Q ∧ (p ∨ Q.quart = 0))
    (k : Fin 4 → ℝ) :
    ∃ Q : LoopQuartic, Q.eval = eulerN d e c N k ∧ LoopDegLe t d' Q ∧ (p ∨ Q.quart = 0) := by
  classical
  choose Qf hQfe hQfd hQfq using hQ
  set R : Fin (d + 1) × Fin (e + 1) → LoopQuartic := fun ij =>
    dilateQ 1 ((node e ij.2 : ℝ) : ℂ) (Qf (node d ij.1 • k))
  refine ⟨qsum Finset.univ (fun ij => eulerW d e c ij.1 ij.2) R, ?_,
    loopDegLe_qsum _ _ fun ij => faceIdRayB_loopDegLe_dilateQ _ _ (hQfd _), ?_⟩
  · funext ℓ
    rw [eval_qsum, eulerN]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp only [R, eval_dilateQ, one_mul, hQfe]
  · by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr (quart_qsum_eq_zero _ _ fun ij =>
        faceIdRayB_quart_dilateQ _ _ ((hQfq _).resolve_left hp))

end Closure

/-! ### The rate (B) of a piece with the Euler numerator -/

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The rate (B) of a merged piece with the Euler numerator**, under the hypotheses of
`faceIdRayB_vpPiece_of_nodes` on `N`. -/
theorem faceIdRayE_vpPiece_of_nodes {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (m + 1 - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) {d₁ d₀ : ℕ}
    (hQ₁ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) (w : ℂ) :
    FaceIdRayRateB fun t k => pairDens (eulerN d (m + 1 - 3) w N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t :=
  faceIdRayB_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 hm sh hsh hcrit _
    (faceIdRayE_isLoopPoly_eulerN w hpoly) (faceIdRayE_refinedBound_eulerN w hB)
    (faceIdRayE_isLoopPoly_k_eulerN w hk) (faceIdRayE_exists_eulerN w hQ₁)
    (faceIdRayE_exists_eulerN w hQ₀) hd₁ hd₀ hA1 hd11 hR1 hA0 hd01 hR0 hm₀ Ms hMs hf

end Piece

end QED.GradedProof.RPi4

end
