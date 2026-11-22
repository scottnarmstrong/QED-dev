/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellNest
public import QED.TwoLoop.VPHalfAtAssemblyFubini
public import QED.Algebra.Contraction
public import QED.Algebra.SandwichReduction
import Mathlib.Tactic.Module

/-!
# Set (c): the vacuum-polarization self-energy class, the outer integrand in spectral form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values`, the algebraic half of step S3. By
`QED.ChainProof.SetCRegDisp.contractionValue₂_repV_eq_outerF` the class `V` at fixed `ε` is the
energy-first integral of `outerF P (seVOuter P p α β)`. Here that integrand is written out:

* `seVOuter_contract`: contracting the outer factor with any `T^{ρσ}` sandwiches `T` between the
  two photon propagators;
* **`outerF_seVOuter`**: with `A = i Π̂_ε(k²)`, `B = ε S_ε(k²)` and the scalar photon factor
  `d(k)`,
  `outerF(k) = K d(k)² ((A k² + B) (γ^ν S_m(p - k) γ_ν)_{αβ} - A (k̸ S_m(p - k) k̸)_{αβ})`,
  `K = -(2π)⁻⁴ (ie)² (1/i)³`. The second term comes from the `k^ρ k^σ` part of the vacuum
  polarization tensor; it is absent from a photon function inserted with `g^{ρσ}` alone;
* **`outerF_seVOuter_eq_spectral`**: after the integration by parts in the Feynman parameter of
  the inner loop (`QED.TwoLoop.VPHalfAt.vpLoopEps_eq_spectral`, `vpExtraEps_eq_spectral`), the
  integrand is a constant (logarithmic) part minus `∫₀¹ seGInt … x k dx`, where `seGInt` carries
  the flavour sum `∑_f c_f (1 - 2x) k² / (M_f² + x(1 - x) k² - iε)` of propagators of mass
  `M_f²/(x(1 - x))`;
* `seChainG_eq`, `seChainK_eq`, **`outerF_seVOuter_dirac`**: by the contraction identities,
  `γ^ν S_m(q) γ_ν = (q² + m² - iε)⁻¹ (-4m - 2q̸)` and
  `k̸ S_m(q) k̸ = (q² + m² - iε)⁻¹ (-m k² - k² q̸ + 2 (q·k) k̸)`, so the integrand is
  `K d(k)² (q² + m² - iε)⁻¹ (-m (3Ak² + 4B) - (Ak² + 2B) q̸ - 2A (q·k) k̸)`, `q = p - k`;
* `neg_seChainK_eq`: the longitudinal term is `D⁻¹ k² (m + p̸) + k̸ - D⁻¹ (p² + m² - iε) k̸`,
  `D = (p - k)² + m² - iε`: odd in `k` up to terms vanishing on the shell, whose slope there is
  not zero (it gives `∫ d(k)² A(k²)` after the angular average). A photon function inserted with
  `g^{ρσ}` alone misses this contribution to the shell slope.

The exchange of `∫₀¹ dx` with the energy-first integral needs bounds on one-loop self-energy
integrands uniform in the spectral mass (step S4 of the plan) and is not done here.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.ChainProof.HCSide (outerF)
open QED.TwoLoop.VPHalfAt (vpLoopEps vpExtraEps vpRatSum)
open QED.TwoLoop.VPHalfAtAssembly (vpT cOne cTwo logSum wOne)
open QED.TwoLoop.Insertion (photonScalar)
open QED.TwoLoop.VPUnitNested (gPhoton)

/-- The constant `K = -(2π)⁻⁴ (ie)² (1/i)³` of the outer factor. -/
noncomputable def seVK (P : Params) : ℂ :=
  -(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 2 * (1 / I) ^ 3

/-- The metric contraction `γ^ν S_m(p - k) γ_ν = ∑ g_{l₀l₁} γ^{l₁} S_m(p - k) γ^{l₀}`. -/
noncomputable def seChainG (P : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l0 : Fin 4, ∑ l1 : Fin 4,
    gPhoton l0 l1 • (Dirac.gamma l1 * electronPropagator P.m P.ε (p - k) * Dirac.gamma l0)

/-- The longitudinal sandwich `k̸ S_m(p - k) k̸`. -/
noncomputable def seChainK (P : Params) (p k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.slash k * electronPropagator P.m P.ε (p - k) * Dirac.slash k

/-- **The outer factor contracted with `T`** sandwiches `T` between the photon propagators. -/
theorem seVOuter_contract (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (k : Fin 4 → ℝ)
    (T : Fin 4 → Fin 4 → ℂ) :
    ∑ ρ, ∑ σ, seVOuter P p α β k ρ σ * T ρ σ =
      seVK P * ∑ l0 : Fin 4, ∑ l1 : Fin 4,
        (Dirac.gamma l1 * electronPropagator P.m P.ε (p - k) * Dirac.gamma l0) α β *
          ∑ a, ∑ b, photonPropagator P.mγ P.Λ P.ε k l0 a * T a b *
            photonPropagator P.mγ P.Λ P.ε (-k) l1 b := by
  simp only [seVOuter, seVK, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, ρ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, l0, 2, ρ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l0]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l1 _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem seChainK_apply (P : Params) (p k : Fin 4 → ℝ) (α β : Fin 4) :
    seChainK P p k α β = ∑ l0 : Fin 4, ∑ l1 : Fin 4,
      ((Minkowski.lower k l0 : ℝ) : ℂ) * ((Minkowski.lower k l1 : ℝ) : ℂ) *
        (Dirac.gamma l1 * electronPropagator P.m P.ε (p - k) * Dirac.gamma l0) α β := by
  simp only [seChainK, Dirac.slash, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l1 _ => ?_
  ring

/-- **The outer integrand of the class `V`**: with `A = i Π̂_ε(k²)`, `B = ε S_ε(k²)`,
`outerF(k) = K d(k)² ((A k² + B) (γ^ν S γ_ν)_{αβ} - A (k̸ S k̸)_{αβ})`. -/
theorem outerF_seVOuter (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (k : Fin 4 → ℝ) :
    outerF P (seVOuter P p α β) k =
      seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2 *
        ((I * vpLoopEps P P.ε (Minkowski.dot k k) * (Minkowski.dot k k : ℂ) +
            (P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k)) * seChainG P p k α β -
          I * vpLoopEps P P.ε (Minkowski.dot k k) * seChainK P p k α β) := by
  unfold outerF
  rw [seVOuter_contract]
  simp only [QED.TwoLoop.VPHalfAtAssembly.sandwich_vpT, seChainK_apply, seChainG,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l1 _ => ?_
  ring

/-- The `x`-integrand of the outer integrand after the integration by parts. -/
noncomputable def seGInt (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ)
    (k : Fin 4 → ℝ) : ℂ :=
  seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2 * vpRatSum P P.ε (Minkowski.dot k k) x *
    (I * cOne P * wOne x *
        ((Minkowski.dot k k : ℂ) * seChainG P p k α β - seChainK P p k α β) +
      (P.ε : ℂ) * cTwo P * (x : ℂ) * seChainG P p k α β)

/-- **The outer integrand in spectral form**, for `ε > 0`: a constant part with the logarithms
`L_ε = ∑_f c_f log(M_f² - iε)`, minus `∫₀¹ seGInt … x k dx`. -/
theorem outerF_seVOuter_eq_spectral (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (α β : Fin 4)
    (k : Fin 4 → ℝ) :
    outerF P (seVOuter P p α β) k =
      seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2 *
          (I * cOne P * (1 / 6) * logSum P P.ε *
              ((Minkowski.dot k k : ℂ) * seChainG P p k α β - seChainK P p k α β) +
            (P.ε : ℂ) * cTwo P * logSum P P.ε * seChainG P p k α β) -
        ∫ x in (0 : ℝ)..1, seGInt P p α β x k := by
  set s := Minkowski.dot k k
  set G := seChainG P p k α β
  set Kk := seChainK P p k α β
  set Q := seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2
  have i1 : IntervalIntegrable (fun x => vpRatSum P P.ε s x * wOne x) volume 0 1 :=
    ((QED.TwoLoop.VPHalfAt.continuous_vpRatSum P hε s).mul
      (by unfold wOne; fun_prop)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x => vpRatSum P P.ε s x * (x : ℂ)) volume 0 1 :=
    ((QED.TwoLoop.VPHalfAt.continuous_vpRatSum P hε s).mul (by fun_prop)).intervalIntegrable 0 1
  have hg : ∫ x in (0 : ℝ)..1, seGInt P p α β x k =
      Q * (I * cOne P * ((s : ℂ) * G - Kk)) *
          (∫ x in (0 : ℝ)..1, vpRatSum P P.ε s x * wOne x) +
        Q * ((P.ε : ℂ) * cTwo P * G) * ∫ x in (0 : ℝ)..1, vpRatSum P P.ε s x * (x : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _)]
    congr 1
    funext x
    simp only [seGInt, Q, s, G, Kk]
    ring
  rw [outerF_seVOuter, QED.TwoLoop.VPHalfAt.vpLoopEps_eq_spectral P hε,
    QED.TwoLoop.VPHalfAt.vpExtraEps_eq_spectral P hε, hg]
  simp only [cOne, cTwo, logSum, wOne, Q, s, G, Kk]
  ring

/-! ### The Dirac structure of the two chains -/

/-- The scalar electron denominator `q² + m² - iε` at `q = p - k`. -/
noncomputable def seDen (P : Params) (p k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot (p - k) (p - k) + P.m ^ 2 : ℝ) : ℂ) - (P.ε : ℂ) * I

/-- **`γ^ν S_m(q) γ_ν = (q² + m² - iε)⁻¹ (-4m - 2q̸)`**, `q = p - k`. -/
theorem seChainG_eq (P : Params) (p k : Fin 4 → ℝ) :
    seChainG P p k = (seDen P p k)⁻¹ •
      ((-4 * (P.m : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (2 : ℂ) • Dirac.slash (p - k)) := by
  have h1 : seChainG P p k = ∑ μ, Dirac.gamma μ * electronPropagator P.m P.ε (p - k) *
      Dirac.gammaLower μ := by
    simp only [seChainG, Dirac.gammaLower, Matrix.mul_sum, Matrix.mul_smul, gPhoton]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Minkowski.metric_symm]
  rw [h1]
  simp only [electronPropagator, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum,
    Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, Matrix.mul_one, Dirac.contract_one,
    Dirac.contract_slash]
  rw [show seDen P p k = ((Minkowski.dot (p - k) (p - k) + P.m ^ 2 : ℝ) : ℂ) - (P.ε : ℂ) * I
    from rfl]
  congr 1
  module

/-- **`k̸ S_m(q) k̸ = (q² + m² - iε)⁻¹ (-m k² - k² q̸ + 2 (q·k) k̸)`**, `q = p - k`. -/
theorem seChainK_eq (P : Params) (p k : Fin 4 → ℝ) :
    seChainK P p k = (seDen P p k)⁻¹ •
      ((-(P.m : ℂ) * (Minkowski.dot k k : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
        (Minkowski.dot k k : ℂ) • Dirac.slash (p - k) +
        (2 * (Minkowski.dot (p - k) k : ℂ)) • Dirac.slash k) := by
  have hkk : Dirac.slash k * Dirac.slash k =
      (-(Minkowski.dot k k : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    have h := Dirac.slash_anticomm k k
    calc Dirac.slash k * Dirac.slash k
        = (1 / 2 : ℂ) • (Dirac.slash k * Dirac.slash k + Dirac.slash k * Dirac.slash k) := by
          module
      _ = _ := by rw [h, smul_smul]; push_cast; congr 1; ring
  have hqk : Dirac.slash (p - k) * Dirac.slash k =
      ((-2 * Minkowski.dot (p - k) k : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
        Dirac.slash k * Dirac.slash (p - k) := by
    rw [← Dirac.slash_anticomm (p - k) k]
    abel
  have hkqk : Dirac.slash k * Dirac.slash (p - k) * Dirac.slash k =
      ((-2 * Minkowski.dot (p - k) k : ℝ) : ℂ) • Dirac.slash k +
        (Minkowski.dot k k : ℂ) • Dirac.slash (p - k) := by
    rw [Matrix.mul_assoc, hqk, Matrix.mul_sub, ← Matrix.mul_assoc, hkk, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    module
  simp only [seChainK, electronPropagator, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, hkk, hkqk]
  rw [show seDen P p k = ((Minkowski.dot (p - k) (p - k) + P.m ^ 2 : ℝ) : ℂ) - (P.ε : ℂ) * I
    from rfl]
  congr 1
  push_cast
  module

/-- **The Dirac structure of the outer integrand**: with `A = i Π̂_ε(k²)`, `B = ε S_ε(k²)`,
`s = k²`, `q = p - k`,
`outerF(k) = K d(k)² (q² + m² - iε)⁻¹ (-m (3As + 4B) - (As + 2B) q̸ - 2A (q·k) k̸)_{αβ}`. -/
theorem outerF_seVOuter_dirac (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (k : Fin 4 → ℝ) :
    outerF P (seVOuter P p α β) k =
      seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2 * (seDen P p k)⁻¹ *
        ((-(P.m : ℂ) * (3 * (I * vpLoopEps P P.ε (Minkowski.dot k k)) *
              (Minkowski.dot k k : ℂ) + 4 * ((P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k))))
            • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
          ((I * vpLoopEps P P.ε (Minkowski.dot k k)) * (Minkowski.dot k k : ℂ) +
              2 * ((P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k))) • Dirac.slash (p - k) -
          (2 * (I * vpLoopEps P P.ε (Minkowski.dot k k)) * (Minkowski.dot (p - k) k : ℂ)) •
            Dirac.slash k) α β := by
  rw [outerF_seVOuter, seChainG_eq, seChainK_eq]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- **The longitudinal sandwich near the shell**:
`-k̸ S_m(p - k) k̸ = D⁻¹ k² (m + p̸) + k̸ - D⁻¹ (p² + m² - iε) k̸`, `D = (p - k)² + m² - iε`.
The middle term is odd in `k`; the other two vanish at `p̸ = -m`, `p² = -m²`, but their
derivatives there do not. -/
theorem neg_seChainK_eq (P : Params) (p k : Fin 4 → ℝ) (hD : seDen P p k ≠ 0) :
    -seChainK P p k =
      (seDen P p k)⁻¹ • ((Minkowski.dot k k : ℂ) •
          ((P.m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) + Dirac.slash p)) + Dirac.slash k -
        ((seDen P p k)⁻¹ * (((Minkowski.dot p p + P.m ^ 2 : ℝ) : ℂ) - (P.ε : ℂ) * I)) •
          Dirac.slash k := by
  have hdot1 : Minkowski.dot (p - k) k = Minkowski.dot p k - Minkowski.dot k k := by
    simp only [Minkowski.dot, Pi.sub_apply, Fin.sum_univ_four]; ring
  have hden : seDen P p k = ((Minkowski.dot p p + P.m ^ 2 : ℝ) : ℂ) - (P.ε : ℂ) * I -
      2 * (Minkowski.dot p k : ℂ) + (Minkowski.dot k k : ℂ) := by
    have h : Minkowski.dot (p - k) (p - k) =
        Minkowski.dot p p - 2 * Minkowski.dot p k + Minkowski.dot k k := by
      simp [Minkowski.dot, Pi.sub_apply, Fin.sum_univ_four, Minkowski.metric]; ring
    simp only [seDen, h]
    push_cast
    ring
  have hu : (seDen P p k)⁻¹ * seDen P p k = 1 := inv_mul_cancel₀ hD
  rw [seChainK_eq, Dirac.slash_sub, hdot1]
  generalize (seDen P p k)⁻¹ = u at hu ⊢
  rw [hden] at hu
  push_cast
  linear_combination (norm := module) hu • Dirac.slash k

end QED.ChainProof.SetCRegDisp

end
