/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecLimSum
public import QED.ChainProof.HCBB2Limit
public import QED.ChainProof.SetASpecForm

/-!
# Set (a): the outer vertex contracted with one spectral tensor term

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`,
obligation (O) of `QED.ChainProof.SetASpec.SetAOuterSpec`: the outer numerator reduction. The
fixed-`ε` spectral form of the two-loop vacuum polarization is a sum of terms
`t(k)^{ab} (k²)ʲ ∫_Δ w(x) fDen(√A(x), ε, ξ(x), k)^{-r}`, `t = g` or `k k`
(`QED.ChainProof.SetASpec.saTens`), with `j + [t = k k] ≤ 2`. This file contracts one such term,
sandwiched between the two Pauli–Villars photon propagators, with the outer one-loop vertex
chain, and writes every entry as a combination of the outer integrands
`QED.ChainProof.SetASpec.saLimTermInt` of the limit engine, over the four photon-type
denominators `(m_γ, Λ, m_γ, Λ)` (`saMs4`):

* `saSpecScalar`: the scalar `(k²)ʲ ∫_Δ w(x) fDen(√A(x), ε, ξ(x), k)^{-r}` of a term;
* `saOuterInt`: the `(i, j)` entry of the vertex chain with the photon factor
  `∑_{ab} Δ(k)_{νa} saTens t k a b · saSpecScalar · Δ(-k)_{ρb}` (the shape of the nested outer
  factor, `QED.TwoLoop.VPHalfAtAssembly.sandwich_vpT`);
* `saSandwich_false`, `saSandwich_true`: the sandwich is `d(k)² g_{νρ}` resp. `d(k)² k_ν k_ρ`
  times the scalar;
* `saLimTermInt_eq_mul`: `saLimTermInt = powInt · ∫_Δ w ∏ fDen⁻¹`;
* **`saOuterInt_false`**: for `t = g`, the entry is `κ (Λ² - m_γ²)² saLimTermInt(numG, j)`;
* **`saOuterInt_true`**: for `t = k k`, the entry is
  `κ (Λ² - m_γ²)² (saLimTermInt(numS, j+1) + saLimTermInt(numL, j+1) + saLimTermInt(numQ, j))`:
  the longitudinal part is reduced by `ℓ̸ ℓ̸ = -ℓ²`
  (`QED.ChainProof.HCBB2.longitudinal_apply`), at the cost of one power of `k²`.

The numerators `numG`, `numS`, `numL`, `numQ` (`QED/ChainProof/HCBB2Num.lean`) are those of the
set (b) bubble–bubble vertex, and they satisfy the engine hypotheses (`QED.ChainProof.HCBB2.QuadN`).
All identities hold at every `ε > 0` and every loop momentum; no integrability is needed.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.OneLoop QED.Integration.Feynman QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested
open QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPHalfAtGen QED.TwoLoop.Insertion
open QED.TwoLoop.Bridge QED.ChainProof.HCBB2

/-- The four photon-type masses `(m_γ, Λ, m_γ, Λ)` of the Pauli–Villars photon pair. -/
def saMs4 (mγ Λ : ℝ) : Fin (2 + 2) → ℝ := ![mγ, Λ, mγ, Λ]

/-- The scalar of one spectral term, `(k²)ʲ ∫_Δ w(x) fDen(√A(x), ε, ξ(x), k)^{-r}`. -/
noncomputable def saSpecScalar (j r : ℕ) {n : ℕ} (A ξ : (Fin n → ℝ) → ℝ)
    (w : (Fin n → ℝ) → ℂ) (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
    ∫ x in simplexSet n, w x * (fDen (√(A x)) ε (ξ x) k ^ r)⁻¹

/-- The photon factor of one spectral term: the term sandwiched between the two photon
propagators, `∑_{ab} Δ(k)_{νa} t(k)^{ab} S(k) Δ(-k)_{ρb}`. -/
noncomputable def saOuterPhoton (mγ Λ : ℝ) (t : Bool) (j r : ℕ) {n : ℕ}
    (A ξ : (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℂ) (ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  ∑ a, ∑ b, photonPropagator mγ Λ ε k ν a * (saTens t k a b * saSpecScalar j r A ξ w ε k) *
    photonPropagator mγ Λ ε (-k) ρ b

/-- **The outer integrand of one spectral term**: the `(i, j)` entry of the one-loop vertex
chain with the electron propagators at `p' + ℓ`, `p + ℓ` and the photon factor
`saOuterPhoton`. -/
noncomputable def saOuterInt (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (t : Bool)
    (J r : ℕ) {n : ℕ} (A ξ : (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℂ) (ε : ℝ)
    (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexChain e μ (electronPropagator m ε (p' + ℓ)) (electronPropagator m ε (p + ℓ))
    (saOuterPhoton mγ Λ t J r A ξ w ε ℓ) i j

/-! ### The sandwich -/

theorem saTens_false_eq_vpT (k : Fin 4 → ℝ) (S : ℂ) (a b : Fin 4) :
    saTens false k a b * S = vpT 0 S k a b := by
  simp only [saTens, vpT, zero_mul, zero_add]
  ring

theorem saTens_true_eq_vpT (k : Fin 4 → ℝ) (S : ℂ) (a b : Fin 4) :
    saTens true k a b * S = vpT (-S) ((Minkowski.dot k k : ℂ) * S) k a b := by
  simp only [saTens, vpT]
  push_cast
  ring

/-- The sandwich of a `g` term: `d(k)² S(k) g_{νρ}`. -/
theorem saSandwich_false (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (S : ℂ) (ν ρ : Fin 4) :
    ∑ a, ∑ b, photonPropagator mγ Λ ε k ν a * (saTens false k a b * S) *
        photonPropagator mγ Λ ε (-k) ρ b = (photonScalar mγ Λ ε k ^ 2 * S) * gPhoton ν ρ := by
  simp only [saTens_false_eq_vpT, sandwich_vpT]
  ring

/-- The sandwich of a `k k` term: `d(k)² S(k) k_ν k_ρ`. -/
theorem saSandwich_true (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (S : ℂ) (ν ρ : Fin 4) :
    ∑ a, ∑ b, photonPropagator mγ Λ ε k ν a * (saTens true k a b * S) *
        photonPropagator mγ Λ ε (-k) ρ b = (photonScalar mγ Λ ε k ^ 2 * S) *
      (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
  simp only [saTens_true_eq_vpT, sandwich_vpT]
  ring

/-! ### The outer integrand of the engine -/

/-- `saLimTermInt` is `powInt` times the parameter integral of the spectral factors. -/
theorem saLimTermInt_eq_mul (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (r : ℕ) {n : ℕ} (A ξ : (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℂ)
    (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    saLimTermInt N m j Ms r A ξ w ε p' p ℓ = powInt N m j Ms (fun _ => ε) ε p' p ℓ *
      ∫ x in simplexSet n, w x * (fDen (√(A x)) ε (ξ x) ℓ ^ r)⁻¹ := by
  unfold saLimTermInt specInt
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  ring

/-- The scalar part shared by every piece. -/
theorem saOuter_scalar (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (J : ℕ) (m : ℝ) (p' p ℓ : Fin 4 → ℝ)
    (N : (Fin 4 → ℝ) → ℂ) :
    ((propDenom m ε (p' + ℓ))⁻¹ * (propDenom m ε (p + ℓ))⁻¹) *
        (photonScalar mγ Λ ε ℓ ^ 2 * ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ J) * N ℓ =
      (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) * powInt N m J (saMs4 mγ Λ) (fun _ => ε) ε p' p ℓ := by
  rw [photonScalar_eq_prod mγ Λ hε, propDenom_eq_denom, propDenom_eq_denom]
  simp only [powInt, prodIntegrand, saMs4, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  push_cast
  ring

/-- **The outer integrand of a `g` term**, at `ε > 0`: `κ (Λ² - m_γ²)² saLimTermInt(numG, j)`. -/
theorem saOuterInt_false (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (J r : ℕ) {n : ℕ}
    (A ξ : (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℂ) {ε : ℝ} (hε : 0 < ε) (ℓ : Fin 4 → ℝ) :
    saOuterInt e m mγ Λ p' p μ i j false J r A ξ w ε ℓ =
      kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        saLimTermInt (numG m p' p μ i j) m J (saMs4 mγ Λ) r A ξ w ε p' p ℓ := by
  have hph : saOuterPhoton mγ Λ false J r A ξ w ε ℓ = fun ν ρ =>
      (photonScalar mγ Λ ε ℓ ^ 2 * saSpecScalar J r A ξ w ε ℓ) * gPhoton ν ρ := by
    funext ν ρ
    exact saSandwich_false mγ Λ ε ℓ _ ν ρ
  rw [saOuterInt, hph, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out,
    vertexChain_smul_in, vertexChain_smul_photon]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [vertexChain_gPhoton_apply, saLimTermInt_eq_mul]
  have hG := saOuter_scalar mγ Λ hε J m p' p ℓ (numG m p' p μ i j)
  simp only [saSpecScalar]
  linear_combination (kap e * ∫ x in simplexSet n, w x * (fDen (√(A x)) ε (ξ x) ℓ ^ r)⁻¹) * hG

/-- **The outer integrand of a `k k` term**, at `ε > 0`:
`κ (Λ² - m_γ²)² (saLimTermInt(numS, j+1) + saLimTermInt(numL, j+1) + saLimTermInt(numQ, j))`. -/
theorem saOuterInt_true (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (J r : ℕ) {n : ℕ}
    (A ξ : (Fin n → ℝ) → ℝ) (w : (Fin n → ℝ) → ℂ) {ε : ℝ} (hε : 0 < ε) (ℓ : Fin 4 → ℝ) :
    saOuterInt e m mγ Λ p' p μ i j true J r A ξ w ε ℓ =
      kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        (saLimTermInt (numS μ i j) m (J + 1) (saMs4 mγ Λ) r A ξ w ε p' p ℓ +
          saLimTermInt (numL m p' p μ i j) m (J + 1) (saMs4 mγ Λ) r A ξ w ε p' p ℓ +
          saLimTermInt (numQ m p' p μ i j) m J (saMs4 mγ Λ) r A ξ w ε p' p ℓ) := by
  have hph : saOuterPhoton mγ Λ true J r A ξ w ε ℓ = fun ν ρ =>
      (photonScalar mγ Λ ε ℓ ^ 2 * saSpecScalar J r A ξ w ε ℓ) *
        (((Minkowski.lower ℓ ν : ℝ) : ℂ) * ((Minkowski.lower ℓ ρ : ℝ) : ℂ)) := by
    funext ν ρ
    exact saSandwich_true mγ Λ ε ℓ _ ν ρ
  rw [saOuterInt, hph, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out,
    vertexChain_smul_in, vertexChain_smul_photon]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [vertexChain_lower_apply, saLimTermInt_eq_mul, saLimTermInt_eq_mul, saLimTermInt_eq_mul]
  have hS := saOuter_scalar mγ Λ hε (J + 1) m p' p ℓ (numS μ i j)
  have hL := saOuter_scalar mγ Λ hε (J + 1) m p' p ℓ (numL m p' p μ i j)
  have hQ := saOuter_scalar mγ Λ hε J m p' p ℓ (numQ m p' p μ i j)
  simp only [saSpecScalar]
  linear_combination (kap e * ∫ x in simplexSet n, w x * (fDen (√(A x)) ε (ξ x) ℓ ^ r)⁻¹) *
    (hS + hL + hQ)

end QED.ChainProof.SetASpec

end
