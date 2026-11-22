/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSELimG
public import QED.ChainProof.SetCLinkWard
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): the photon counterterm of one T1 parameter set

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`. The limit `dPVal` of each of the
classes `P0`, `P1` and the constant part `seConstLim` of the class `V` are the same multiple of
one photon integral `seCtComb`, the limit of `efi (d(k)² (k² γ^ν S γ_ν - k̸ S k̸))`.

* `seChain_photonInsertion`: the `δ₃`-insertion chain is `-(δ₃/2) d² (k² G - K)` at `k = -q`.
* `tendsto_efi_seGK_of_lt`: the limit `seCtComb` of the photon integral, below threshold.
* **`dPVal_eq`**: `dPVal = κ_SE (-(δ₃/2)) seCtComb`.
* **`seConstLim_eq`**: `seConstLim = κ_SE (-(c₁ L/6)) seCtComb`, `c₁ = e²/(2π²)`.
* `vPV_eq`: for `m < M₁, M₂`, the class `V` limit `vPV` is `seConstLim - ∫₀¹ seGIntLim`.
* **`seVPLim_eq`**: for `m < M₁, M₂`, the limit `seVPLim` of one T1 set is
  `∫₀¹ seGIntLim + κ_SE (c₁ L/6 - δ₃) seCtComb`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAtAssembly (cOne cTwo logSum)
open QED.TwoLoop.Insertion (photonScalar photonInsertion photonInsertion_eq transversePhoton
  longitudinalPhoton)
open QED.GradedProof.SE2 (seChain kappaSE)
open QED.ChainProof.SetCRegDispSE (seProd seProdLim seL1 efi_const_mul_se)
open QED.TwoLoop.VPUnitNested (gPhoton)

/-- The photon integral of the counterterm: the limit of
`efi (d(k)² (k² γ^ν S(p - k) γ_ν - k̸ S(p - k) k̸))`. -/
noncomputable def seCtComb (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 *
    (seL1 0 (seAff (seCL P p α β) 3 α β) P.m (seMs4 P) (-p) -
      2 * seProdLim (seQuadA p α β) (seQuad p α β) P.m (seMs4 P) (-p))

theorem seVK_eq (P : Params) : seVK P = I * kappaSE P.e := by
  have h : (1 / I) ^ 3 = (1 / I) ^ 2 * (-I) := by
    rw [pow_succ, one_div, inv_I]
  rw [seVK, kappaSE, h]
  ring

/-- **The constant part of the class `V`** as a multiple of the counterterm integral. -/
theorem seConstLim_eq (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    seConstLim P p α β = kappaSE P.e * (-(cOne P * (1 / 6) * logSum P 0)) * seCtComb P p α β := by
  rw [seConstLim, seCtComb, seVK_eq]
  linear_combination (kappaSE P.e * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * cOne P * (1 / 6) *
    logSum P 0 * (seL1 0 (seAff (seCL P p α β) 3 α β) P.m (seMs4 P) (-p) -
      2 * seProdLim (seQuadA p α β) (seQuad p α β) P.m (seMs4 P) (-p))) * I_sq

theorem slash_mul_slash_eq_sum (A : Matrix (Fin 4) (Fin 4) ℂ) (q : Fin 4 → ℝ) :
    Dirac.slash q * A * Dirac.slash q = ∑ ν, ∑ ρ,
      (((Minkowski.lower q ν : ℝ) : ℂ) * ((Minkowski.lower q ρ : ℝ) : ℂ)) •
        (Dirac.gamma ρ * A * Dirac.gamma ν) := by
  simp only [Dirac.slash, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]

/-- **The `δ₃`-insertion chain** at `k = -q`: `-(δ₃/2) d(k)² (k² γ^ν S(p - k) γ_ν - k̸ S k̸)`. -/
theorem seChain_photonInsertion (P : Params) (δ : ℝ) (p q : Fin 4 → ℝ) (α β : Fin 4) :
    seChain (electronPropagator P.m P.ε (p + q)) (photonInsertion δ P.mγ P.Λ P.ε q) α β =
      (-(δ / 2 : ℂ)) * (photonScalar P.mγ P.Λ P.ε (-q) ^ 2 *
        ((Minkowski.dot (-q) (-q) : ℂ) * seChainG P p (-q) α β - seChainK P p (-q) α β)) := by
  have hpq : p - -q = p + q := sub_neg_eq_add p q
  have hd : Minkowski.dot (-q) (-q) = Minkowski.dot q q := by
    simp only [Minkowski.dot, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  have hs : photonScalar P.mγ P.Λ P.ε (-q) = photonScalar P.mγ P.Λ P.ε q :=
    QED.TwoLoop.VPHalfAtAssembly.photonScalar_neg _ _ _ q
  have hK : seChainK P p (-q) = Dirac.slash q * electronPropagator P.m P.ε (p + q) *
      Dirac.slash q := by
    simp only [seChainK, hpq, Dirac.slash_neg, neg_mul, mul_neg, neg_neg]
  have hG : seChainG P p (-q) = ∑ ν, ∑ ρ, gPhoton ν ρ •
      (Dirac.gamma ρ * electronPropagator P.m P.ε (p + q) * Dirac.gamma ν) := by
    rw [seChainG, hpq]
  have hC : seChain (electronPropagator P.m P.ε (p + q)) (photonInsertion δ P.mγ P.Λ P.ε q) =
      ∑ ν, ∑ ρ, ((-(δ / 2 : ℂ)) * transversePhoton P.mγ P.Λ P.ε q ν ρ +
        (δ / 2 : ℂ) * longitudinalPhoton P.mγ P.Λ P.ε q ν ρ) •
          (Dirac.gamma ρ * electronPropagator P.m P.ε (p + q) * Dirac.gamma ν) := by
    simp only [seChain, photonInsertion_eq]
  rw [hC, hK, hG, slash_mul_slash_eq_sum, hd, hs]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, transversePhoton, longitudinalPhoton, add_mul, gPhoton]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  ring

/-! ### The limit of the photon integral -/

section Unif

variable {P : Params} {M₀ K : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ)
  {p : Fin 4 → ℝ} {α β : Fin 4}
  (hEL : SEEngU (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) K 0)
  (hEQ : SEEngU (seQuad p α β) P.m M₀ (-p) K 1)
  (hLL : SELimU 0 (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) 0)
  (hLQ : SELimU (seQuadA p α β) (seQuad p α β) P.m M₀ (-p) 1)

include hmγ hΛ hEL hEQ hLL hLQ in
/-- **The limit of the counterterm photon integral.** -/
theorem tendsto_efi_seGK :
    Tendsto (fun ε => energyFirstIntegral fun k => photonScalar P.mγ P.Λ ε k ^ 2 *
        ((Minkowski.dot k k : ℂ) * seChainG (withEps P ε) p k α β -
          seChainK (withEps P ε) p k α β)) (𝓝[>] 0) (𝓝 (seCtComb P p α β)) := by
  have hMs4 : ∀ j, M₀ ≤ seMs4 P j := seMs4_ge hmγ hΛ
  have hes4 : ∀ j : Fin 4, Tendsto (fun ε : ℝ => (fun _ : Fin 4 => ε) j) (𝓝[>] 0) (𝓝[>] 0) :=
    fun _ => tendsto_id
  set L := seAff (seCL P p α β) 3 α β
  set Q := seQuad p α β
  set κ : ℂ := ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2
  set X : Fin 2 → ℝ → (Fin 4 → ℝ) → ℂ := ![
    fun ε ℓ => sqC ℓ * seProd L P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ,
    fun ε ℓ => seProd Q P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ] with hX
  set c : Fin 2 → ℝ → ℂ := ![fun _ => κ, fun _ => -(2 * κ)] with hc
  have hpt : ∀ ε, 0 < ε → ∀ ℓ, photonScalar P.mγ P.Λ ε ℓ ^ 2 *
      ((Minkowski.dot ℓ ℓ : ℂ) * seChainG (withEps P ε) p ℓ α β -
        seChainK (withEps P ε) p ℓ α β) = ∑ i, c i ε * X i ε ℓ := by
    intro ε hε ℓ
    rw [photonScalar_eq_mul _ _ _ hε, seChainGK_apply, seDen_eq_denom]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hX, hc, Matrix.cons_val_zero,
      Matrix.cons_val_succ, sqC, L, Q, κ, withEps_m, withEps_ε, seCL_withEps, seProd, seMs4,
      Fin.prod_univ_succ, Fin.prod_univ_zero]
    ring
  have hlim := tendsto_efi_sum (l := 𝓝[>] (0 : ℝ)) (c := c) (X := X) (c₀ := ![κ, -(2 * κ)])
    (a := ![seL1 0 L P.m (seMs4 P) (-p), seProdLim (seQuadA p α β) Q P.m (seMs4 P) (-p)])
    ?_ ?_ ?_
  · refine (hlim.congr' ?_).trans (le_of_eq ?_)
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      congr 1
      funext ℓ
      exact (hpt ε hε ℓ).symm
    · congr 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, seCtComb, κ, L, Q]
      ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h4 : ∀ j : Fin 4, 0 < (fun _ : Fin 4 => ε) j := fun _ => hε
    intro i
    fin_cases i
    · exact (goodEF4_s1' hEL (k := 1) (Nat.zero_le 1) (by norm_num) hMs4 h4 hε).1
    · exact efInt_s0 hEQ (k := 2) (by norm_num) (by norm_num) hMs4 h4 hε
  · intro i
    fin_cases i
    · exact tendsto_efi_s1 hEL hLL (k := 1) (Nat.zero_le 1) (by norm_num) hMs4 hes4
    · exact hLQ 2 (by norm_num) (by norm_num) _ hMs4 _ hes4
  · intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds

end Unif

/-- **The limit of the counterterm photon integral, below threshold.** -/
theorem tendsto_efi_seGK_of_lt {P : Params} {M₀ : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ)
    (hΛ : M₀ ≤ P.Λ) (hm : 0 < P.m) {p : Fin 4 → ℝ} (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => energyFirstIntegral fun k => photonScalar P.mγ P.Λ ε k ^ 2 *
        ((Minkowski.dot k k : ℂ) * seChainG (withEps P ε) p k α β -
          seChainK (withEps P ε) p k α β)) (𝓝[>] 0) (𝓝 (seCtComb P p α β)) := by
  have hpp : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply]; ring_nf
  obtain ⟨c₀, hc₀, hPc⟩ := exists_pos_le_selfEnergyFeynmanMass hm hM₀ (hpp ▸ hp)
  obtain ⟨KL, hKL, hL⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCL P p α β) 3 α β
  obtain ⟨KQ, hKQ, hQ⟩ := exists_seEngU_seQuad hM₀.le hc₀ hPc p α β
  exact tendsto_efi_seGK hmγ hΛ (K := KL + KQ) (hL.mono (by linarith)) (hQ.mono (by linarith))
    (seLimU_seAff hM₀.le hc₀ hPc _ _ α β) (seLimU_seQuad hM₀.le hc₀ hPc p α β)

/-! ### The limits `dPVal` and `seConstLim` -/

/-- **The limit of `P0` (and of `P1`)** as a multiple of the counterterm integral. -/
theorem dPVal_eq (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    SetCLink.dPVal Q p α β = kappaSE Q.e * (-(Q.δ₃ / 2 : ℂ)) * seCtComb Q p α β := by
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  have h1 := QED.GradedProof.WI2.tendsto_seP_dP Q hm hν0 hν hp α β
  have h2 := (tendsto_efi_seGK_of_lt hν0 hγ hΛ hm hp α β).const_mul
    (kappaSE Q.e * (-(Q.δ₃ / 2 : ℂ)))
  refine tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall fun ε => ?_))
  set G : (Fin 4 → ℝ) → ℂ := fun k => kappaSE Q.e * ((-(Q.δ₃ / 2 : ℂ)) *
    (photonScalar Q.mγ Q.Λ ε k ^ 2 * ((Minkowski.dot k k : ℂ) * seChainG (withEps Q ε) p k α β -
      seChainK (withEps Q ε) p k α β))) with hG
  have e : (fun q => kappaSE Q.e * seChain (electronPropagator Q.m ε (p + q))
      (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β) = fun q => G (-q) := by
    funext q
    exact congrArg (kappaSE Q.e * ·) (seChain_photonInsertion (withEps Q ε) Q.δ₃ p q α β)
  beta_reduce
  rw [e, QED.OneLoop.energyFirstIntegral_neg_eq_self G, hG, efi_const_mul_se, efi_const_mul_se]
  ring

/-- **The limit of the class `V` of one T1 set** with `m < M₁, M₂`, below threshold. -/
theorem vPV_eq {Q : Params} (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁) (hM₂ : Q.m < Q.M₂)
    (hγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hνm : ν ≤ Q.m) {p : Fin 4 → ℝ}
    (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    QED.GradedProof.WI2.vPV Q p α β =
      seConstLim Q p α β - ∫ x in (0 : ℝ)..1, seGIntLim Q p α β x := by
  have h1 := QED.GradedProof.WI2.tendsto_repV_wt hpv1 hpv2 (m₀ := Q.m) hm le_rfl hM₁.le hM₂.le
    hν0 hν (by linarith) hp α β
  set P' : Params := { Q with ε := 1 } with hP'
  have hA : QED.GradedProof.SE2.Adm P' :=
    ⟨one_pos, hm, hm.trans hM₁, hm.trans hM₂, hγ, hΛ, hpv1, hpv2⟩
  have hmass : ∀ f, ν ≤ P'.mass f := by
    intro f
    fin_cases f <;> simp [Params.mass, P'] <;> linarith
  have h2 := tendsto_contractionValue₂_repV hA hM₁ hM₂ hν0 (hν.trans (min_le_left _ _))
    (hν.trans (min_le_right _ _)) hmass hp α β
  exact tendsto_nhds_unique h1 h2

/-- **The limit of one T1 set** with `m < M₁, M₂`, below threshold: the `x`-integral of the
spectral part plus `κ_SE (c₁ L/6 - δ₃)` times the counterterm integral. -/
theorem seVPLim_eq {Q : Params} (hm : 0 < Q.m) (hM₁ : Q.m < Q.M₁) (hM₂ : Q.m < Q.M₂)
    (hγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hνm : ν ≤ Q.m) {p : Fin 4 → ℝ}
    (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    SetCLink.seVPLim Q p α β = (∫ x in (0 : ℝ)..1, seGIntLim Q p α β x) +
      kappaSE Q.e * (cOne Q * (1 / 6) * logSum Q 0 - Q.δ₃) * seCtComb Q p α β := by
  rw [SetCLink.seVPLim, Matrix.of_apply,
    vPV_eq hm hM₁ hM₂ hγ hΛ hpv1 hpv2 hν0 hν hνm hp α β, dPVal_eq Q hm hν0 hν hp α β,
    seConstLim_eq]
  ring

end QED.ChainProof.SetCRegDisp

end
