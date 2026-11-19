/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroSharpParam
public import QED.TwoLoop.ReflCovarianceClasses
public import QED.TwoLoop.ReflCovarianceCounterterm

/-!
# The `♯`-laws of the order-`e⁵` vertex numerators

Helper level for the reality of the order-`e⁵` vertex limit (V5Zero, part D). The numerators of
the classes are built from `γ^μ`, slashes `m - k̸` of real vectors, real tensors and complex
constants, so `♯` (`QED.GradedProof.SE2Real.sharp`) fixes every building block and conjugates the
constants:

* `sharp_electronNumerator`, `sharp_chain`, `sharp_openChain`, `sharp_chainNum`: the open-line
  chains (whose photon factors `(1/i) g (Λ² - m_γ²)` come in pairs) are `♯`-fixed;
* `conj_traceT`, `sharp_vpChainM`: the vacuum-polarization chains with real loop tensors are
  `♯`-fixed;
* `sharp_vertexChain`, `sharp_numD2In`, `sharp_numD2Out`, `sharp_numD3`: the counterterm
  numerators are `♯`-fixed (the prefactor `(ie)³ (1/i)³` is real, and so is the `δ₃` photon
  numerator `(1/i)(-i/2) δ₃ (…)`).
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.V5Zero.Sharp

open QED.Dirac QED.GradedProof.SE2Real QED.TwoLoop.LimitCovariance QED.TwoLoop.Bridge
open QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.WickModel

theorem sharp_electronNumerator (m : ℝ) (k : Fin 4 → ℝ) :
    sharp (electronNumerator m k) = electronNumerator m k := by
  rw [electronNumerator, sharp_sub, sharp_smul, sharp_one, sharp_slash, Complex.conj_ofReal]

theorem sharp_chain {D : Fin 4 → Fin 4 → ℂ} (hD : ∀ ν ρ, starRingEnd ℂ (D ν ρ) = D ν ρ)
    {A B : Matrix (Fin 4) (Fin 4) ℂ} (hA : sharp A = A) (hB : sharp B = B) (μ : Fin 4) :
    sharp (IsSpinLift.chain D A B μ) = IsSpinLift.chain D A B μ := by
  simp only [IsSpinLift.chain, sharp_sum, sharp_smul, sharp_mul, sharp_gamma, hA, hB, hD]

theorem sharp_openChain {G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hG : ∀ t, sharp (G t) = G t) (hE : ∀ i, sharp (E i) = E i) :
    sharp (openChain G E) = openChain G E := by
  simp only [openChain, sharp_mul, hG, hE]

theorem conj_pvEta (P : Params) (x y : Fin 4) :
    starRingEnd ℂ (pvEta P x y) = -pvEta P x y := by
  simp only [pvEta, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal]
  rw [div_neg, neg_mul]

theorem conj_kron (μ x : Fin 4) : starRingEnd ℂ (kron μ x) = kron μ x := by
  unfold kron
  split_ifs <;> simp

theorem sharp_chainNum (P : Params) (σ : Equiv.Perm (Fin 5))
    {E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hE : ∀ i, sharp (E i) = E i) (μ : Fin 4) :
    sharp (chainNum P σ E μ) = chainNum P σ E μ := by
  simp only [chainNum, sharp_sum, sharp_smul, map_mul, conj_kron, conj_pvEta,
    sharp_openChain (fun t => sharp_gamma _) hE, mul_neg]
  simp only [mul_assoc, neg_mul, neg_neg]

/-! ### Vacuum polarization -/

theorem conj_traceT {A B : Matrix (Fin 4) (Fin 4) ℂ} (hA : sharp A = A) (hB : sharp B = B)
    (a b : Fin 4) : starRingEnd ℂ (traceT A B a b) = traceT A B a b := by
  rw [traceT, ← trace_sharp, sharp_mul, sharp_mul, sharp_mul, sharp_gamma, sharp_gamma, hA, hB]

theorem conj_pvG (P : Params) (x y : Fin 4) : starRingEnd ℂ (pvG P x y) = pvG P x y := by
  simp only [pvG, Complex.conj_ofReal]

theorem conj_lowered (P : Params) {X : Fin 4 → Fin 4 → ℂ}
    (hX : ∀ a b, starRingEnd ℂ (X a b) = X a b) (ν ρ : Fin 4) :
    starRingEnd ℂ (lowered P X ν ρ) = lowered P X ν ρ := by
  simp only [lowered, map_sum, map_mul, conj_pvG, hX]

theorem sharp_vpChainM (P : Params) (p kext k : Fin 4 → ℝ) {X : Fin 4 → Fin 4 → ℂ}
    (hX : ∀ a b, starRingEnd ℂ (X a b) = X a b) (μ : Fin 4) :
    sharp (vpChainM P p kext k X μ) = vpChainM P p kext k X μ :=
  sharp_chain (conj_lowered P hX) (sharp_electronNumerator _ _) (sharp_electronNumerator _ _) μ

/-! ### Counterterms -/

theorem conj_vertexChain_coeff (e : ℝ) :
    starRingEnd ℂ ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) =
      (I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ := by
  have h : (I * e) ^ 3 * (1 / I) ^ 3 = (e : ℂ) ^ 3 := by
    rw [mul_pow, one_div, inv_pow, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ I_ne_zero),
      one_mul]
  rw [h, map_mul, map_inv₀, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]

theorem sharp_vertexChain (e : ℝ) (μ : Fin 4) {A B : Matrix (Fin 4) (Fin 4) ℂ}
    {D : Fin 4 → Fin 4 → ℂ} (hD : ∀ ν ρ, starRingEnd ℂ (D ν ρ) = D ν ρ) (hA : sharp A = A)
    (hB : sharp B = B) : sharp (vertexChain e μ A B D) = vertexChain e μ A B D := by
  rw [vertexChain_eq_chain, sharp_smul, conj_vertexChain_coeff, sharp_chain hD hA hB]

theorem conj_pvPhotonNum (mγ Λ : ℝ) (ν ρ : Fin 4) :
    starRingEnd ℂ (pvPhotonNum mγ Λ ν ρ) = pvPhotonNum mγ Λ ν ρ := by
  simp only [pvPhotonNum, Complex.conj_ofReal]

theorem sharp_fermionCtMatrix (δ₂ δm m : ℝ) (k : Fin 4 → ℝ) :
    sharp (fermionCtMatrix δ₂ δm m k) = fermionCtMatrix δ₂ δm m k := by
  simp only [fermionCtMatrix, sharp_add, sharp_smul, sharp_slash, sharp_one, Complex.conj_ofReal]

theorem sharp_insertionNum (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    sharp (-(electronNumerator m k * fermionCtMatrix δ₂ δm m k * electronNumerator m k)) =
      -(electronNumerator m k * fermionCtMatrix δ₂ δm m k * electronNumerator m k) := by
  rw [sharp_neg, sharp_mul, sharp_mul, sharp_electronNumerator, sharp_fermionCtMatrix]

theorem sharp_numD2In (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    sharp (numD2In P p' p μ k) = numD2In P p' p μ k :=
  sharp_vertexChain _ _ (conj_pvPhotonNum _ _) (sharp_electronNumerator _ _)
    (sharp_insertionNum _ _ _ _)

theorem sharp_numD2Out (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    sharp (numD2Out P p' p μ k) = numD2Out P p' p μ k :=
  sharp_vertexChain _ _ (conj_pvPhotonNum _ _) (sharp_insertionNum _ _ _ _)
    (sharp_electronNumerator _ _)

theorem conj_photonNum (δ₃ mγ Λ : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    starRingEnd ℂ (photonNum δ₃ mγ Λ k ν ρ) = photonNum δ₃ mγ Λ k ν ρ := by
  have h : ∀ a b, photonCtFactor δ₃ k a b =
      I * ((-(1 / 2) * (δ₃ * (Minkowski.dot k k * Minkowski.metric a b - k a * k b)) : ℝ) : ℂ) :=
    fun a b => by
      simp only [photonCtFactor]
      push_cast
      ring
  have e : photonNum δ₃ mγ Λ k ν ρ = ∑ a, ∑ b, pvPhotonNum mγ Λ ν a *
      ((-(1 / 2) * (δ₃ * (Minkowski.dot k k * Minkowski.metric a b - k a * k b)) : ℝ) : ℂ) *
        pvPhotonNum mγ Λ ρ b := by
    simp only [photonNum, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    field_simp
  rw [e]
  simp only [map_sum, map_mul, conj_pvPhotonNum, Complex.conj_ofReal]

theorem sharp_numD3 (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    sharp (numD3 P p' p μ k) = numD3 P p' p μ k :=
  sharp_vertexChain _ _ (conj_photonNum _ _ _ _) (sharp_electronNumerator _ _)
    (sharp_electronNumerator _ _)

end QED.GradedProof.V5Zero.Sharp

end
