/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW9
public import QED.GradedProof.RPi4FaceRateIncBDer

/-!
# (R-Π₄) step L10, B-inc: the scaled weights of a piece along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. Along the ray `k'(τ) = √τ k₀`, interpolation in the scales writes

`τ^{-q} N(√τ k₀)(√τ ℓ) = ∑ᵢⱼ cᵢⱼ(τ) N(tᵢ k₀)(tⱼ ℓ)`, `cᵢⱼ(τ) = τ^{-q} ℓᵢ(√τ) ℓⱼ(√τ)`.

The weights are differentiable on `τ > 0`, and their derivatives recombine into the Euler
numerator with `c = q`:

`∑ᵢⱼ cᵢⱼ'(τ) N(tᵢ k₀)(tⱼ ℓ) = τ⁻¹ ∑ᵢⱼ cᵢⱼ(τ) eulerN(tᵢ k₀)(tⱼ ℓ)`,

since both sides are `∂_τ (τ^{-q} g(√τ))` for `g(t) = N(t k₀)(t ℓ)`.

* `eulerCf`, `faceIdRayF_differentiableAt_eulerCf`;
* `faceIdRayF_sum_eulerCf`: the interpolation identity;
* **`faceIdRayF_sum_deriv_eulerCf`**: the derivative identity;
* `faceIdRayF_pieces_scaled`: the pieces at `√τ`-scaled momenta as weighted scaled pieces;
* **`faceRateIncB_vpPiece_of_nodes`**: the rate (B) of the increment (`FaceRateIncB`) of one
  merged piece, by `faceRateIncB_of_deriv` with the derivative
  `σ⁻¹ (pairDens (eulerN …) + pairDensD …)` (`faceIdRayE_hasDerivAt_scaled`).
-/

@[expose] public section

open Complex Polynomial Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.TwoLoop.PauliZeroLimit (node lbasis)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.MassScaling (dilateQ eval_dilateQ)
open QED.TwoLoop.LimitCovariance (qsum eval_qsum)
open QED.Integration.TwoLoop

/-- The scaled interpolation weights `τ^{-q} ℓᵢ(√τ) ℓⱼ(√τ)`. -/
noncomputable def eulerCf (d e q : ℕ) (ij : Fin (d + 1) × Fin (e + 1)) (τ : ℝ) : ℂ :=
  ((τ⁻¹ : ℝ) : ℂ) ^ q * (lbasis d ij.1).eval (Real.sqrt τ : ℂ) *
    (lbasis e ij.2).eval (Real.sqrt τ : ℂ)

theorem faceIdRayF_hasDerivAt_inv_pow (q : ℕ) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun τ : ℝ => ((τ⁻¹ : ℝ) : ℂ) ^ q) (-(q : ℂ) * ((τ⁻¹ : ℝ) : ℂ) *
      ((τ⁻¹ : ℝ) : ℂ) ^ q) τ := by
  have h := ((hasDerivAt_inv hτ).pow q).ofReal_comp
  have e : (fun τ : ℝ => ((τ⁻¹ : ℝ) : ℂ) ^ q) = fun τ : ℝ => (((τ⁻¹) ^ q : ℝ) : ℂ) := by
    funext τ
    push_cast
    rfl
  rw [e]
  convert h using 1
  rcases q with _ | q
  · simp
  · push_cast
    ring

theorem faceIdRayF_hasDerivAt_lb_sqrt (P : Polynomial ℂ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun τ : ℝ => P.eval (Real.sqrt τ : ℂ))
      ((1 / (2 * Real.sqrt τ)) • P.derivative.eval (Real.sqrt τ : ℂ)) τ := by
  have hP : HasDerivAt (fun t : ℝ => P.eval (t : ℂ)) (P.derivative.eval (Real.sqrt τ : ℂ))
      (Real.sqrt τ) := by
    simpa using (P.hasDerivAt (Real.sqrt τ : ℂ)).comp_ofReal
  exact hP.scomp τ (Real.hasDerivAt_sqrt hτ.ne')

theorem faceIdRayF_differentiableAt_eulerCf (d e q : ℕ) (ij : Fin (d + 1) × Fin (e + 1))
    {τ : ℝ} (hτ : 0 < τ) : DifferentiableAt ℝ (eulerCf d e q ij) τ :=
  (((faceIdRayF_hasDerivAt_inv_pow q hτ.ne').mul
    (faceIdRayF_hasDerivAt_lb_sqrt _ hτ)).mul
      (faceIdRayF_hasDerivAt_lb_sqrt _ hτ)).differentiableAt

section Interp

variable {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {d e : ℕ}
  (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) (hpoly : ∀ k, IsLoopPoly 2 e (N k))

include hk hpoly

/-- **Interpolation along the ray**: `∑ᵢⱼ cᵢⱼ(τ) N(tᵢ k₀)(tⱼ ℓ) = τ^{-q} N(√τ k₀)(√τ ℓ)`. -/
theorem faceIdRayF_sum_eulerCf (q : ℕ) (k₀ : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (τ : ℝ) :
    ∑ ij, eulerCf d e q ij τ * N (node d ij.1 • k₀) (node e ij.2 • ℓ) =
      ((τ⁻¹ : ℝ) : ℂ) ^ q * N (Real.sqrt τ • k₀) (Real.sqrt τ • ℓ) := by
  rw [faceIdRayE_eq_scale₂ hk hpoly k₀ ℓ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ij _ => by simp only [eulerCf]; ring

/-- **The derivative of the weights gives the Euler numerator**: for `τ > 0`,
`∑ᵢⱼ cᵢⱼ'(τ) N(tᵢ k₀)(tⱼ ℓ) = τ⁻¹ ∑ᵢⱼ cᵢⱼ(τ) eulerN(tᵢ k₀)(tⱼ ℓ)` with `c = q`. -/
theorem faceIdRayF_sum_deriv_eulerCf (q : ℕ) (k₀ : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) {τ : ℝ}
    (hτ : 0 < τ) :
    ∑ ij, deriv (eulerCf d e q ij) τ * N (node d ij.1 • k₀) (node e ij.2 • ℓ) =
      ((τ⁻¹ : ℝ) : ℂ) * ∑ ij, eulerCf d e q ij τ *
        eulerN d e (q : ℂ) N (node d ij.1 • k₀) (node e ij.2 • ℓ) := by
  set r := Real.sqrt τ with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hτ
  have hrr : r * r = τ := Real.mul_self_sqrt hτ.le
  set g : ℝ → ℂ := fun t => N (t • k₀) (t • ℓ) with hg
  set D : ℝ → ℂ := fun t => ∑ ij : Fin (d + 1) × Fin (e + 1),
    ((lbasis d ij.1).derivative.eval (t : ℂ) * (lbasis e ij.2).eval (t : ℂ) +
      (lbasis d ij.1).eval (t : ℂ) * (lbasis e ij.2).derivative.eval (t : ℂ)) *
      N (node d ij.1 • k₀) (node e ij.2 • ℓ) with hD
  have hgD : ∀ t, HasDerivAt g (D t) t := fun t => faceIdRayE_hasDerivAt hk hpoly k₀ ℓ t
  -- the left side is the derivative of `τ^{-q} g(√τ)`
  have hL : HasDerivAt (fun τ' => ∑ ij, eulerCf d e q ij τ' *
      N (node d ij.1 • k₀) (node e ij.2 • ℓ))
      (∑ ij, deriv (eulerCf d e q ij) τ * N (node d ij.1 • k₀) (node e ij.2 • ℓ)) τ :=
    HasDerivAt.fun_sum fun ij _ =>
      ((faceIdRayF_differentiableAt_eulerCf d e q ij hτ).hasDerivAt).mul_const _
  have hφ : HasDerivAt (fun τ' : ℝ => ((τ'⁻¹ : ℝ) : ℂ) ^ q * g (Real.sqrt τ'))
      (-(q : ℂ) * ((τ⁻¹ : ℝ) : ℂ) * ((τ⁻¹ : ℝ) : ℂ) ^ q * g r +
        ((τ⁻¹ : ℝ) : ℂ) ^ q * ((1 / (2 * r)) • D r)) τ :=
    (faceIdRayF_hasDerivAt_inv_pow q hτ.ne').mul
      ((hgD r).scomp τ (Real.hasDerivAt_sqrt hτ.ne'))
  have hLφ := hL.unique (hφ.congr_of_eventuallyEq (Eventually.of_forall fun τ' =>
    faceIdRayF_sum_eulerCf hk hpoly q k₀ ℓ τ'))
  rw [hLφ]
  -- the right side
  rw [faceIdRayF_sum_eulerCf (faceIdRayE_isLoopPoly_k_eulerN _ hk)
    (faceIdRayE_isLoopPoly_eulerN _ hpoly) q k₀ ℓ τ, faceIdRayE_eulerN_eq hk hpoly]
  set E := ∑ ij : Fin (d + 1) × Fin (e + 1),
    ((lbasis d ij.1).derivative.eval 1 * (lbasis e ij.2).eval 1 +
      (lbasis d ij.1).eval 1 * (lbasis e ij.2).derivative.eval 1) *
      N (node d ij.1 • r • k₀) (node e ij.2 • r • ℓ) with hE
  -- `E = r D(r)`: both are the derivative of `s ↦ g(s r)` at `1`
  have hE1 := faceIdRayE_hasDerivAt hk hpoly (r • k₀) (r • ℓ) 1
  have hE2 : HasDerivAt (fun s : ℝ => N (s • r • k₀) (s • r • ℓ)) (r • D r) 1 := by
    have h := (hgD (1 * r)).scomp (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).mul_const r)
    rw [one_mul] at h
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv (by simp)
    simp only [Function.comp, hg, id, smul_smul]
  have hEr : E = (r : ℂ) * D r := by
    have h := hE1.unique hE2
    simp only [Complex.ofReal_one] at h
    rw [hE, h, Complex.real_smul]
  rw [hEr]
  simp only [hg, Complex.real_smul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hτ' : ((τ⁻¹ : ℝ) : ℂ) = ((r : ℂ) * r)⁻¹ := by
    rw [← hrr]; push_cast; ring
  rw [hτ']
  push_cast
  field_simp
  ring

/-- **The pieces at `√τ`-scaled momenta** with a numerator `Q` of `N(√τ k₀)` are the weighted
sums of the pieces of the interpolating quartics `Rᵢⱼ` (of `ℓ ↦ N(tᵢ k₀)(tⱼ ℓ)`) at the scaled
data. -/
theorem faceIdRayF_pieces_scaled {m n : ℕ} (hn : 5 ≤ n) (k₀ : Fin 4 → ℝ)
    (R : Fin (d + 1) × Fin (e + 1) → LoopQuartic)
    (hR : ∀ ij, (R ij).eval = fun ℓ => N (node d ij.1 • k₀) (node e ij.2 • ℓ)) {τ : ℝ}
    (hτ : 0 < τ) {Q : LoopQuartic} (hQ : Q.eval = N (Real.sqrt τ • k₀))
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) :
    pieceF n Q α (Real.sqrt τ • p) Ms γ u z = ∑ ij, eulerCf d e (n - 3) ij τ *
      pieceF n (R ij) α p ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z ∧
    pieceFd n Q α (Real.sqrt τ • p) Ms γ u z = ∑ ij, eulerCf d e (n - 3) ij τ *
      pieceFd n (R ij) α p ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z ∧
    pieceFw (n + 1) Q α (Real.sqrt τ • p) Ms γ u z = ∑ ij, eulerCf d e (n - 3) ij τ *
      pieceFw (n + 1) (R ij) α p ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z := by
  set r := Real.sqrt τ with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hτ
  set P := qsum Finset.univ (fun ij : Fin (d + 1) × Fin (e + 1) =>
    (lbasis d ij.1).eval (r : ℂ) * (lbasis e ij.2).eval (r : ℂ)) R with hP
  have hQ' : Q.eval = (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) P).eval := by
    funext ℓ
    rw [hQ, eval_dilateQ, eval_qsum, one_mul]
    have h := faceIdRayE_eq_scale₂ hk hpoly k₀ (r⁻¹ • ℓ) r r
    rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul] at h
    rw [h]
    exact Finset.sum_congr rfl fun ij _ => by rw [hR ij]
  have hM : Ms = r • (r⁻¹ • Ms) := by rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hu : u = r ^ 2 * (u / τ) := by
    rw [hr, Real.sq_sqrt hτ.le]; field_simp
  have hκ : ((r⁻¹ : ℝ) : ℂ) ^ (2 * (n - 3)) = ((τ⁻¹ : ℝ) : ℂ) ^ (n - 3) := by
    have h2 : (r⁻¹) ^ 2 = τ⁻¹ := by rw [inv_pow, hr, Real.sq_sqrt hτ.le]
    rw [pow_mul, ← Complex.ofReal_pow, h2]
  have hsum : ∀ f : LoopQuartic → ℂ, (∀ (s : Finset (Fin (d + 1) × Fin (e + 1))) w,
      f (qsum s w R) = ∑ ij ∈ s, w ij * f (R ij)) →
      1 * ((r⁻¹ : ℝ) : ℂ) ^ (2 * (n - 3)) * f P = ∑ ij, eulerCf d e (n - 3) ij τ * f (R ij) := by
    intro f hf
    rw [hP, hf, hκ, one_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ij _ => by simp only [eulerCf, ← hr]; ring
  refine ⟨?_, ?_, ?_⟩
  · calc _ = pieceF n (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) P) α (r • p) (r • (r⁻¹ • Ms)) γ
          (r ^ 2 * (u / τ)) z := by
          rw [← hM, ← hu]; simp only [pieceF, paramAtV_congr hQ']
      _ = _ := by
          rw [faceIdRayB_pieceF_dilateQ n P 1 hr0.ne' α p z (by omega)]
          exact hsum (fun Q => pieceF n Q α p (r⁻¹ • Ms) γ (u / τ) z)
            fun s w => faceIdRayE_pieceF_qsum n s w R α p _ γ _ z
  · calc _ = pieceFd n (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) P) α (r • p) (r • (r⁻¹ • Ms)) γ
          (r ^ 2 * (u / τ)) z := by
          rw [← hM, ← hu]; simp only [pieceFd, paramAtV_congr hQ']
      _ = _ := by
          rw [faceIdRayE_pieceFd_dilateQ n P 1 hr0.ne' α p z hn]
          exact hsum (fun Q => pieceFd n Q α p (r⁻¹ • Ms) γ (u / τ) z)
            fun s w => faceIdRayE_pieceFd_qsum n s w R α p _ γ _ z
  · calc _ = pieceFw (n + 1) (dilateQ 1 ((r⁻¹ : ℝ) : ℂ) P) α (r • p) (r • (r⁻¹ • Ms)) γ
          (r ^ 2 * (u / τ)) z := by
          rw [← hM, ← hu]; simp only [pieceFw, pieceF, paramAtV_congr hQ']
      _ = _ := by
          rw [faceIdRayE_pieceFw_dilateQ n P 1 hr0.ne' α p z hn]
          exact hsum (fun Q => pieceFw (n + 1) Q α p (r⁻¹ • Ms) γ (u / τ) z)
            fun s w => faceIdRayE_pieceFw_qsum (n + 1) s w R α p _ γ _ z

end Interp

/-! ### The rate (B) of the increment of one merged piece -/

section Piece

open MeasureTheory
open QED.GradedProof.VP2 QED.GradedProof.SE2 QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The rate (B) of the increment of one merged piece** (`FaceRateIncB`), under the
hypotheses of `faceIdRayB_vpPiece_of_nodes`: the derivative along the ray is
`σ⁻¹ (pairDens (eulerN …) + pairDensD …)`, whose rate (B) is `faceIdRayE_vpPiece_of_nodes` and
`faceIdRayE_vpPieceD_of_nodes`. -/
theorem faceRateIncB_vpPiece_of_nodes {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
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
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) :
    FaceRateIncB fun t k => pairDens (N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t := by
  classical
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set cs : Fin (m + 1) → ℝ := fun l => c (sh l.castSucc) with hcs
  have hrows := castLoopMatrix_rows base hrow hrow4 fun l : Fin (m + 1) => sh l.castSucc
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ γ₀ := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, γ₀, Fin.val_last]
    have := l.isLt
    omega
  have hr10 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; simp at this
  have hr01 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 0; simp at this
  have huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀ := fun l => by
    constructor
    · intro h
      by_contra hl
      rcases (hrows l).1 ((hne l).2 hl) with h' | h'
      · exact hr10 (h'.symm.trans h)
      · exact hr01 (h'.symm.trans h)
    · intro hl
      exact (hrows l).2 (not_not.1 fun h => (hne l).1 h hl)
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  -- the scaled frame and the interpolating quartics
  set q := m + 1 - 3 with hq
  set vh := faceIdRayB_vhat with hvh
  set ph : Fin (m + 1) → Fin 4 → ℝ := fun l => cs l • vh with hph
  have hex : ∀ F, IsLoopPoly 2 q F → ∃ Q : LoopQuartic, Q.eval = F := fun F ⟨P, hP, hF⟩ =>
    IsLoopPoly.exists_loopQuartic ⟨P, hP.trans (by omega), hF⟩
  set NE := eulerN d q (q : ℂ) N with hNE
  have hpolyE : ∀ k, IsLoopPoly 2 q (NE k) := faceIdRayE_isLoopPoly_eulerN _ hpoly
  have hkE : ∀ ℓ, IsLoopPoly 1 d fun y => NE (y 0) ℓ := faceIdRayE_isLoopPoly_k_eulerN _ hk
  have hBE : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (NE k) :=
    faceIdRayE_refinedBound_eulerN _ hB
  set R : Fin (d + 1) × Fin (q + 1) → LoopQuartic := fun ij =>
    numQuartic fun ℓ => N (node d ij.1 • vh) (node q ij.2 • ℓ) with hRdef
  have hR : ∀ ij, (R ij).eval = fun ℓ => N (node d ij.1 • vh) (node q ij.2 • ℓ) := fun ij =>
    eval_numQuartic (hex _ (faceIdRayE_isLoopPoly_smul (hpoly _) _))
  set R'' : Fin (d + 1) × Fin (q + 1) → LoopQuartic := fun ij =>
    numQuartic fun ℓ => NE (node d ij.1 • vh) (node q ij.2 • ℓ) with hR''def
  have hR'' : ∀ ij, (R'' ij).eval = fun ℓ => NE (node d ij.1 • vh) (node q ij.2 • ℓ) :=
    fun ij => eval_numQuartic (hex _ (faceIdRayE_isLoopPoly_smul (hpolyE _) _))
  set cf := eulerCf d q q with hcf_def
  -- the ray
  have hkv : ∀ τ : ℝ, 0 < τ → tiltVec (Real.sqrt τ) τ = Real.sqrt τ • vh := fun τ hτ =>
    faceIdRayB_tiltVec_eq hτ.le
  have hpk : ∀ τ : ℝ, 0 < τ → (fun l => cs l • tiltVec (Real.sqrt τ) τ) = Real.sqrt τ • ph :=
    fun τ hτ => by
      funext l
      simp only [hkv τ hτ, hph, Pi.smul_apply, smul_smul, mul_comm]
  have hdot : ∀ τ : ℝ, 0 < τ →
      Minkowski.dot (tiltVec (Real.sqrt τ) τ) (tiltVec (Real.sqrt τ) τ) = τ := fun τ hτ =>
    dot_tiltVec (by rw [Real.sq_sqrt hτ.le]; linarith)
  -- P0 and `V(0) ≥ 0`
  have hV : ∀ τ : ℝ, 0 < τ → ∀ z : Fin (m + 1) → ℝ, (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      symanzikU α z ≠ 0 → m₀ ^ 2 * (1 - z γ₀) ≤ symanzikV α (Real.sqrt τ • ph) Ms z := by
    intro τ hτ z hz hz1 hU
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf (k := tiltVec (Real.sqrt τ) τ) (by rw [hdot τ hτ]; nlinarith) hz hU
    rw [← hferF, ferSum_eq_one_sub huniq hz1] at hP0
    have hmin : min 1 (1 + Minkowski.dot (tiltVec (Real.sqrt τ) τ) (tiltVec (Real.sqrt τ) τ) /
        (2 * m₀) ^ 2) = 1 := by
      rw [hdot τ hτ]
      exact min_eq_left (le_add_of_nonneg_right (by positivity))
    rw [hmin, one_mul] at hP0
    rw [← hpk τ hτ]
    linarith
  have hc₀ : 0 < min (m₀ ^ 2) 1 := lt_min (by positivity) one_pos
  have hVu : ∀ u : ℝ, 1 ≤ u → ∀ τ : ℝ, 0 < τ → ∀ y ∈ simplexSet m,
      symanzikU α (simplexPoint y) ≠ 0 →
      min (m₀ ^ 2) 1 ≤ symanzikV α (Real.sqrt τ • ph) Ms (simplexPoint y) +
        simplexPoint y γ₀ * u := by
    intro u hu τ hτ y hy hU
    have hz := simplexPoint_mem_stdSimplex hy
    have h1 := hV τ hτ _ hz.1 hz.2 hU
    have hzγ := hz.1 γ₀
    have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
      rw [← hz.2]
      exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
    have e1 := mul_le_mul_of_nonneg_right (min_le_left (m₀ ^ 2) 1) (sub_nonneg.2 hzγ1)
    have e2 := mul_le_mul_of_nonneg_right (min_le_right (m₀ ^ 2) 1) hzγ
    have e3 := mul_le_mul_of_nonneg_left hu hzγ
    nlinarith
  have hVs : ∀ u : ℝ, 1 ≤ u → ∀ τ : ℝ, 0 < τ → ∀ y ∈ simplexSet m,
      symanzikU α (simplexPoint y) ≠ 0 →
      min (m₀ ^ 2) 1 ≤ τ * (symanzikV α ph ((Real.sqrt τ)⁻¹ • Ms) (simplexPoint y) +
        simplexPoint y γ₀ * (u / τ)) := by
    intro u hu τ hτ y hy hU
    have hr0 : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
    have hM : Ms = Real.sqrt τ • ((Real.sqrt τ)⁻¹ • Ms) := by
      rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have h := hVu u hu τ hτ y hy hU
    rw [hM, QED.TwoLoop.MassScaling.symanzikV_smul, Real.sq_sqrt hτ.le] at h
    have e : τ * (simplexPoint y γ₀ * (u / τ)) = simplexPoint y γ₀ * u := by field_simp
    rw [mul_add, e]
    exact h
  have hB0 : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      0 ≤ symanzikV α ph 0 (simplexPoint y) := fun y hy hU =>
    faceIdRayD_symanzikV_zero_nonneg base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      (by rw [faceIdRayE_dot_vhat]; norm_num) (simplexPoint_mem_stdSimplex hy).1 hU
  have hB0u : ∀ τ : ℝ, 0 < τ → ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      0 ≤ symanzikV α (Real.sqrt τ • ph) 0 (simplexPoint y) := fun τ hτ y hy hU => by
    rw [← hpk τ hτ]
    exact faceIdRayD_symanzikV_zero_nonneg base c y₁ y₂ hflow
      (fun l : Fin (m + 1) => sh l.castSucc) (by rw [hdot τ hτ]; exact hτ.le)
      (simplexPoint_mem_stdSimplex hy).1 hU
  -- the coefficient integrability
  have kR : ∀ ij, _ := fun ij => faceIdRayE_coeff_int base hm sh hsh hcrit
    (faceIdRayE_isLoopPoly_smul (hpoly _) _) (faceIdRayE_refinedBound_smul (hB _) _) (hR ij) ph
  have kR'' : ∀ ij, _ := fun ij => faceIdRayE_coeff_int base hm sh hsh hcrit
    (faceIdRayE_isLoopPoly_smul (hpolyE _) _) (faceIdRayE_refinedBound_smul (hBE _) _)
    (hR'' ij) ph
  -- the unscaled integrability
  have hIu : ∀ (F : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ), (∀ k, IsLoopPoly 2 q (F k)) →
      (∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (F k)) →
      ∀ u : ℝ, 1 ≤ u → ∀ τ : ℝ, 0 < τ →
      IntegrableOn (fun y => pieceF (m + 1) (numQuartic (F (Real.sqrt τ • vh))) α
        (Real.sqrt τ • ph) Ms γ₀ u (simplexPoint y)) (simplexSet m) ∧
      IntegrableOn (fun y => pieceFd (m + 1) (numQuartic (F (Real.sqrt τ • vh))) α
        (Real.sqrt τ • ph) Ms γ₀ u (simplexPoint y)) (simplexSet m) ∧
      IntegrableOn (fun y => pieceFw (m + 1 + 1) (numQuartic (F (Real.sqrt τ • vh))) α
        (Real.sqrt τ • ph) Ms γ₀ u (simplexPoint y)) (simplexSet m) := by
    intro F hFp hFB u hu τ hτ
    obtain ⟨k1, k2, k3⟩ := faceIdRayE_coeff_int base hm sh hsh hcrit (hFp _) (hFB _)
      (eval_numQuartic (hex _ (hFp (Real.sqrt τ • vh)))) (Real.sqrt τ • ph)
    exact ⟨integrableOn_pieceF hc₀ k1 k2 k3 (hVu u hu τ hτ),
      faceIdRayE_integrableOn_pieceFdw (by omega) hc₀ (zero_le_one.trans hu) k1 k2 k3
        (hVu u hu τ hτ) (hB0u τ hτ)⟩
  -- the update is trivial
  have hupd : Function.update Ms γ₀ 0 = Ms := Function.update_eq_self_iff.2 hMs.symm
  -- the two families in the scaled frame
  have hG : ∀ u τ : ℝ, 0 < τ → pairDens (N (tiltVec (Real.sqrt τ) τ)) α
      (fun l => cs l • tiltVec (Real.sqrt τ) τ) Ms γ₀ u = -((π : ℂ) ^ 4) *
        ∫ y in simplexSet m, scaledSumF (m + 1) cf R α ph Ms γ₀ u τ (simplexPoint y) := by
    intro u τ hτ
    rw [hpk τ hτ, hkv τ hτ]
    simp only [pairDens, hupd]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact (faceIdRayF_pieces_scaled hk hpoly (n := m + 1) (by omega) vh R hR hτ
      (eval_numQuartic (hex _ (hpoly _))) α ph Ms γ₀ u (simplexPoint y)).1
  have hGd : ∀ u : ℝ, 1 ≤ u → ∀ τ : ℝ, 0 < τ →
      pairDens (NE (tiltVec (Real.sqrt τ) τ)) α (fun l => cs l • tiltVec (Real.sqrt τ) τ) Ms γ₀ u +
        pairDensD (N (tiltVec (Real.sqrt τ) τ)) α (fun l => cs l • tiltVec (Real.sqrt τ) τ) Ms
          γ₀ u = -((π : ℂ) ^ 4) *
        ∫ y in simplexSet m, scaledSumH (m + 1) cf R R'' α ph Ms γ₀ u τ (simplexPoint y) := by
    intro u hu τ hτ
    rw [hpk τ hτ, hkv τ hτ]
    simp only [pairDens, pairDensD, hupd]
    obtain ⟨iE, -, -⟩ := hIu NE hpolyE hBE u hu τ hτ
    obtain ⟨-, iN2, iN3⟩ := hIu N hpoly hB u hu τ hτ
    rw [← mul_add]
    refine congrArg _ ((integral_add iE (iN2.sub iN3)).symm.trans ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have h1 := (faceIdRayF_pieces_scaled hkE hpolyE (n := m + 1) (by omega) vh R'' hR'' hτ
      (eval_numQuartic (hex _ (hpolyE _))) α ph Ms γ₀ u (simplexPoint y)).1
    have h2 := faceIdRayF_pieces_scaled hk hpoly (n := m + 1) (by omega) vh R hR hτ
      (eval_numQuartic (hex _ (hpoly _))) α ph Ms γ₀ u (simplexPoint y)
    simp only [pieceF, Pi.sub_apply] at h1 h2 ⊢
    rw [h1, h2.2.1, h2.2.2, scaledSumH, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ij _ => by simp only [pieceF]; ring
  -- the weights
  have hcf : ∀ ij τ, 0 < τ → HasDerivAt (cf ij) (deriv (cf ij) τ) τ := fun ij τ hτ =>
    (faceIdRayF_differentiableAt_eulerCf d q q ij hτ).hasDerivAt
  have heval : ∀ τ : ℝ, 0 < τ → (qsum Finset.univ (fun ij => deriv (cf ij) τ) R).eval =
      (qsum Finset.univ (fun ij => ((τ⁻¹ : ℝ) : ℂ) * cf ij τ) R'').eval := by
    intro τ hτ
    funext ℓ
    simp only [eval_qsum, hR, hR'']
    rw [faceIdRayF_sum_deriv_eulerCf hk hpoly q vh ℓ hτ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  -- the derivative along the ray
  have hkey : ∀ u : ℝ, 1 ≤ u → ∀ σ : ℝ, 0 < σ →
      HasDerivAt (fun τ => pairDens (N (tiltVec (Real.sqrt τ) τ)) α
        (fun l => cs l • tiltVec (Real.sqrt τ) τ) Ms γ₀ u)
        (((σ⁻¹ : ℝ) : ℂ) * (pairDens (NE (tiltVec (Real.sqrt σ) σ)) α
          (fun l => cs l • tiltVec (Real.sqrt σ) σ) Ms γ₀ u +
          pairDensD (N (tiltVec (Real.sqrt σ) σ)) α (fun l => cs l • tiltVec (Real.sqrt σ) σ)
            Ms γ₀ u)) σ ∧
      ContinuousAt (fun τ => pairDens (NE (tiltVec (Real.sqrt τ) τ)) α
          (fun l => cs l • tiltVec (Real.sqrt τ) τ) Ms γ₀ u +
        pairDensD (N (tiltVec (Real.sqrt τ) τ)) α (fun l => cs l • tiltVec (Real.sqrt τ) τ)
          Ms γ₀ u) σ := by
    intro u hu σ hσ
    obtain ⟨h1, h2⟩ := faceIdRayE_hasDerivAt_scaled (n := m + 1) (by omega) cf
      (fun ij τ => deriv (cf ij) τ) R R'' α ph Ms γ₀ (zero_le_one.trans hu) hcf heval kR kR''
      hc₀ (hVs u hu) hB0 hσ
    constructor
    · refine ((h1.const_mul (-((π : ℂ) ^ 4))).congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [lt_mem_nhds hσ] with τ hτ using hG u τ hτ
      · rw [hGd u hu σ hσ]; ring
    · refine (h2.const_mul (-((π : ℂ) ^ 4))).congr ?_
      filter_upwards [lt_mem_nhds hσ] with τ hτ using (hGd u hu τ hτ).symm
  refine faceRateIncB_of_deriv ((faceIdRayE_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 hm sh
    hsh hcrit N hpoly hB hk hQ₁ hQ₀ hd₁ hd₀ hA1 hd11 hR1 hA0 hd01 hR0 hm₀ Ms hMs hf
    (q : ℂ)).add (faceIdRayE_vpPieceD_of_nodes base c y₁ y₂ hflow hrow hrow4 hm sh hsh hcrit N
    hpoly hB hk hQ₁ hQ₀ hd₁ hd₀ hA1 hd11 hR1 hA0 hd01 hR0 hm₀ Ms hf)) ?_
  refine faceRateIncDeriv_of_hasDerivAt (fun u hu σ hσ => ?_) (fun u σ h1 h2 => ?_) ?_
  · exact (hkey u hu σ (one_pos.trans_le hσ.1)).1.continuousAt.continuousWithinAt
  · exact (hkey u (h1.le.trans h2.le) σ (one_pos.trans h1)).1
  · intro s hs u hu
    refine ContinuousOn.intervalIntegrable fun σ hσ => ?_
    rw [uIcc_of_le hs] at hσ
    have hσ0 : 0 < σ := one_pos.trans_le hσ.1
    exact ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_inv₀ hσ0.ne')).mul
      (hkey u (hs.trans hu) σ hσ0).2).continuousWithinAt

end Piece

end QED.GradedProof.RPi4

end
