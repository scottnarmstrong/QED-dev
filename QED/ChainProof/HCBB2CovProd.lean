/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideDDCov
public import QED.TwoLoop.VPHalfAtLimitPhoton

/-!
# Covariance of the limits of a one-loop vertex with several photon-type denominators

Helper level, Phase 5 Stage 1a (O3-8 for `QED.ChainProof.Enum.repBB`). For a numerator family
`N(p', p)^μ(ℓ)` (matrix-valued, a loop polynomial of degree `≤ 4` in each entry) with
`S N(L p', L p)^μ(L ℓ) T = L^μ_ν N(p', p)^ν(ℓ)`, the `ε → 0⁺` limits of the energy-first
integrals of `prodIntegrand` (`QED.TwoLoop.VPHalfAtLimit.prodIntegrand`: the numerator over
the two electron denominators and `k + 2` photon-type denominators of masses `Ms`) at `(p', p)`
and at `(L p', L p)` are related by `S B^μ T = L^μ_ν A^ν`.

As for the `δ₃`–`δ₃` class (`QED.ChainProof.HCSide.conj_classLimit_repDD`), each limit is
identified as a parametric value divided by `auxLimit m`
(`QED.TwoLoop.LimitCovariance.exists_paramValue_of_kinds`, with the line kinds
`kindsPh k = [out, inn, pho^{k+2}, aux³]`) and covariance comes from
`QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue_div`. The no-subdivergence criterion is
checked by `decide` for `2 ≤ k ≤ 6` (four to eight photon-type lines).
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance QED.TwoLoop.VPHalfAtLimit QED.Dirac
open QED.Integration.TwoLoop (IntNoSubdivergenceRefined LoopQuartic)

/-! ### The line kinds and masses -/

/-- The line kinds `[out, inn, pho^{k+2}, aux³]`. -/
def kindsPh (k : ℕ) : Fin (k + 2 + 3 + 1 + 1) → LineKind :=
  Matrix.vecCons .out (Matrix.vecCons .inn
    (Fin.append (m := k + 2) (n := 3) (fun _ => LineKind.pho) fun _ => LineKind.aux))

/-- The masses `[m, m, Ms, m, m, m]`. -/
def massesPh (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) : Fin (k + 2 + 3 + 1 + 1) → ℝ :=
  Matrix.vecCons m (Matrix.vecCons m (Fin.append (m := k + 2) (n := 3) Ms fun _ => m))

theorem kindsPh_ok (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 6) :
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} (fun i => (kindsPh k i).dir) ∧
    ({0, 1, 2, 3} : Finset (Fin (k + 2 + 3 + 1 + 1))).card = 4 ∧
    ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (k + 2 + 3 + 1 + 1))), kindsPh k e ≠ .aux := by
  interval_cases k <;> decide +kernel

theorem massesPh_sq_of_ne_pho (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    ∀ i, kindsPh k i ≠ .pho → massesPh m Ms i ^ 2 = m ^ 2 := by
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.addCases (m := k + 2) (n := 3) (fun a => ?_) (fun b => ?_) i) i) i <;>
    simp [kindsPh, massesPh, Fin.append_left, Fin.append_right]

theorem le_massesPh_sq {m M₀ : ℝ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hM₀ : 0 < M₀)
    (hMs : ∀ i, M₀ ≤ Ms i) : ∀ i, kindsPh k i = .pho → M₀ ^ 2 ≤ massesPh m Ms i ^ 2 := by
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.addCases (m := k + 2) (n := 3) (fun a => ?_) (fun b => ?_) i) i) i <;>
    simp only [kindsPh, massesPh, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.append_left,
      Fin.append_right, reduceCtorEq, IsEmpty.forall_iff]
  exact fun _ => pow_le_pow_left₀ hM₀.le (hMs a) 2

theorem prod_kindsPh (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (propDenom (massesPh m Ms i) ε ((kindsPh k i).lineMom p p' ℓ))⁻¹ =
      ((QED.OneLoop.denom m ε (p' + ℓ 0) * QED.OneLoop.denom m ε (p + ℓ 0))⁻¹ *
        ∏ j, (QED.OneLoop.denom (Ms j) ε (ℓ 0))⁻¹) * ((propDenom m ε (ℓ 1))⁻¹) ^ 3 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_add (a := k + 2) (b := 3)]
  simp only [kindsPh, massesPh, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.append_left,
    Fin.append_right, LineKind.lineMom, Fin.prod_univ_three, mul_inv]
  simp only [propDenom, QED.OneLoop.denom]
  ring

/-! ### Covariance -/

section Cov

variable {m M₀ : ℝ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **The limit of a `prodIntegrand` entry as a parametric value divided by `auxLimit m`.** -/
theorem exists_paramValue_prod (hk : 2 ≤ k) (hk' : k ≤ 6) (hm : 0 < m) (hM₀ : 0 < M₀)
    (hMs : ∀ i, M₀ ≤ Ms i) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0)) {A : ℂ}
    (hA : Tendsto (fun ε => QED.OneLoop.energyFirstIntegral
      (prodIntegrand N m Ms (fun _ => ε) ε p' p)) (𝓝[>] 0) (𝓝 A)) :
    ∃ v, IsParamValue (kindsData (by omega) (kindsPh k) (massesPh m Ms) hm hM₀ hp hp' hq
      (massesPh_sq_of_ne_pho m Ms) (le_massesPh_sq hM₀ hMs) (kindsPh_ok k hk hk').1)
      (fun ℓ => N (ℓ 0)) v ∧ A = v / auxLimit m := by
  obtain ⟨-, hcard, hE⟩ := kindsPh_ok k hk hk'
  obtain ⟨v, hv, hT⟩ := exists_paramValue_of_kinds (by omega) (kindsPh k) (massesPh m Ms) hm hM₀
    hp hp' hq (massesPh_sq_of_ne_pho m Ms) (le_massesPh_sq hM₀ hMs) (kindsPh_ok k hk hk').1
    hcard hE N hN (fun ε => prodIntegrand N m Ms (fun _ => ε) ε p' p)
    (fun ε _ ℓ => by rw [prod_kindsPh, prodIntegrand]; ring)
  exact ⟨v, hv, tendsto_nhds_unique hA hT⟩

/-- **Covariance of the limits of `prodIntegrand`**, with the external momenta moved. -/
theorem conj_prodLim (hk : 2 ≤ k) (hk' : k ≤ 6) (hm : 0 < m) (hM₀ : 0 < M₀)
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
        (L *ᵥ p))) (𝓝[>] 0) (𝓝 (B μ i j)))
    (μ : Fin 4) : S * B μ * T = vecAct L A μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]; exact hq
  exact conj_eq_vecAct_of_paramValue_div (kindsData (by omega) (kindsPh k) (massesPh m Ms) hm hM₀
      hp hp' hq (massesPh_sq_of_ne_pho m Ms) (le_massesPh_sq hM₀ hMs) (kindsPh_ok k hk hk').1) h
    (fun i => (kindsPh k i).mom (L *ᵥ p) (L *ᵥ p'))
    (funext fun i => QED.ChainProof.HCSide.lineKind_mom_map' p p' _)
    (fun μ ℓ => Nf p' p μ ℓ) (fun μ ℓ => Nf (L *ᵥ p') (L *ᵥ p) μ ℓ) hC A B (auxLimit m)
    (fun μ i j => exists_paramValue_prod hk hk' hm hM₀ hMs hp hp' hq _ (hP p' p μ i j) (hA μ i j))
    (fun μ i j => by
      obtain ⟨v, hv, hW⟩ := exists_paramValue_prod hk hk' hm hM₀ hMs hpL hpL' hqL _
        (hP (L *ᵥ p') (L *ᵥ p) μ i j) (hB μ i j)
      obtain ⟨Q, hQ, hI, rfl⟩ := IsParamValue.exists_integrableOn hv
      exact ⟨Q, hQ, hI, hW⟩) μ

end Cov

end QED.ChainProof.HCBB2

end
