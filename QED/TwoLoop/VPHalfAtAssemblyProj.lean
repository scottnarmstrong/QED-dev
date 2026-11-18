/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyPieces
public import QED.TwoLoop.VPHalfAtNested
public import QED.TwoLoop.VPUnitNestedAlgebra
import QED.Integration.EnergyFirstShift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Pauli projection of the vacuum-polarization class at fixed `ε`

Step 1 (projection) and step 2 (algebraic bridge) of the assembly of the `ε → 0⁺` limit of the
class `VP` (obligation O2-8 at the `ε → 0` level). At fixed `ε > 0`, the class value is the
energy-first integral of `∑ ρ σ, vpOuter … k ρ σ · (i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g)`
(`QED.TwoLoop.VPHalfAt.contractionValue₂_VP_eq_closedForm`).

* `efInt_of_joint`: if both stages of the joint energy-first integral of a two-loop integrand are
  integrable and the Fubini condition `hG` holds at every spatial momentum, then the nested outer
  integrand is integrable in both stages. With the proved `hJ`
  (`QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_VP`) and `hG`
  (`QED.TwoLoop.NestedVPFubiniBound.integrable_nestedIntegrand_time`), every matrix entry of the
  outer integrand of `VP` is integrable in both stages (`efInt_vpOuterIntegrand`).
* `sandwich_vpT`, `vpOuter_contract`: contracted with the two photon propagators, the outer factor
  is `-(1/i)` times the one-loop vertex chain of `QED.TwoLoop.Insertion.vertexChain` with the
  photon factor `d(k)² ((A k² + B) g - A k k)`.
* `pauliNum_vpOuter_neg`: after the reflection `k ↦ -k`, the Pauli projection of the outer
  integrand is `i (Λ² - m_γ²)² P₄(k) (A k² + B)`, with `P₄` the Pauli-projected chain over the
  six denominators: the longitudinal part `k k` drops out exactly
  (`QED.TwoLoop.VPUnitNested.pauliNum_longitudinal`).
* **`pauliNum_classValue_eq`**: for `ε > 0`, the Pauli numerator of the class value is the
  energy-first integral of `i (Λ² - m_γ²)² P₄(k) (i Π̂_ε(k²) k² + ε S_ε(k²))`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtAssembly

open QED.WickModel QED.OneLoop QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAt QED.TwoLoop.Bridge

/-! ### Integrability of the nested outer integrand -/

/-- **The nested outer integrand is integrable in both stages**, given both stages of the joint
prescription and the Fubini condition at every spatial momentum of the second loop. -/
theorem efInt_of_joint (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (hF : jointEnergyFirstIntegrable 2 F)
    (hG : ∀ w₂ : Fin 3 → ℝ, Integrable fun p : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, F ![Fin.cons t₁ p.2, Fin.cons p.1 w₂]) :
    EFInt fun k => energyFirstIntegral fun q => F ![q, k] := by
  obtain ⟨hF₁, hF₂⟩ := hF
  have hin : ∀ w₁ w₂ : Fin 3 → ℝ,
      ∫ t : Fin 2 → ℝ, F (fun s => (Fin.cons (t s) (![w₁, w₂] s) : Fin 4 → ℝ)) =
        ∫ t₂ : ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂] := by
    intro w₁ w₂
    have hint := (NestedVP.integrable_finTwo_iff _).mp (hF₁ ![w₁, w₂])
    simp only [NestedVP.cons_finTwo] at hint
    rw [NestedVP.integral_finTwo]
    simp only [NestedVP.cons_finTwo]
    exact integral_prod_symm (fun p : ℝ × ℝ => F ![Fin.cons p.1 w₁, Fin.cons p.2 w₂]) hint
  have hout := (NestedVP.integrable_finTwo_iff _).mp hF₂
  simp only [hin] at hout
  refine ⟨fun w₂ => (hG w₂).integral_prod_left, ?_⟩
  refine hout.integral_prod_right.congr (Eventually.of_forall fun w₂ => ?_)
  exact integral_integral_swap (f := fun (w₁ : Fin 3 → ℝ) (t₂ : ℝ) =>
    ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂]) (hG w₂).swap

/-- The outer integrand of the class `VP` with the inner loop in closed form. -/
noncomputable def vpOuterIntegrand (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (k : Fin 4 → ℝ) : ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, NestedVP.vpOuter P p kext k α β μ ρ σ *
    (I * vpLoopEps P P.ε (Minkowski.dot k k) *
        ((Minkowski.dot k k * Minkowski.metric ρ σ - k ρ * k σ : ℝ) : ℂ)
      + (P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k) * (Minkowski.metric ρ σ : ℂ))

/-- **Every entry of the outer integrand of `VP` is integrable in both stages**, at fixed
`ε > 0`, under the mass and Pauli–Villars conditions and momentum conservation. -/
theorem efInt_vpOuterIntegrand (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε) :
    EFInt (vpOuterIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0)) := by
  have hJ := NestedVP.jointEnergyFirstIntegrable_nested P hmom αOut βIn μ
    (ClassIntegrable.jointEnergyFirstIntegrable_VP P hε hPV₁ hPV₂ hmom αOut βIn μ)
  have h := efInt_of_joint _ hJ fun w =>
    NestedVPFubiniBound.integrable_nestedIntegrand_time hm hM₁ hM₂ hPV₁ hPV₂ hε (pIn 0) (kIn 0)
      (αOut 0) (βIn 0) (μ 0) w
  have e : (fun k => energyFirstIntegral fun q =>
      NestedVP.nestedIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) ![q, k]) =
      vpOuterIntegrand P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) := by
    funext k
    rw [NestedVP.energyFirstIntegral_nestedIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hε]
    simp only [energyFirstIntegral_vacuumPolarizationIntegrand_eq hm hM₁ hM₂ hPV₁ hPV₂ hε]
    rfl
  rw [e] at h
  exact h

/-! ### The algebraic bridge -/

/-- The inserted vacuum polarization `A (k² g - k k) + B g`. -/
noncomputable def vpT (A B : ℂ) (k : Fin 4 → ℝ) (ρ σ : Fin 4) : ℂ :=
  A * ((Minkowski.dot k k * Minkowski.metric ρ σ - k ρ * k σ : ℝ) : ℂ) +
    B * (Minkowski.metric ρ σ : ℂ)

theorem photonScalar_neg (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) :
    photonScalar mγ Λ ε (-k) = photonScalar mγ Λ ε k := by
  simp only [photonScalar, CountertermMirror.dot_neg_neg]

theorem vpT_neg (A B : ℂ) (k : Fin 4 → ℝ) (ρ σ : Fin 4) : vpT A B (-k) ρ σ = vpT A B k ρ σ := by
  simp only [vpT, CountertermMirror.dot_neg_neg, Pi.neg_apply, neg_mul_neg]

/-- **The metric sandwich**:
`∑ Δ(k)_{νa} T^{ab} Δ(-k)_{ρb} = d(k)² ((A k² + B) g_{νρ} - A k_ν k_ρ)`. -/
theorem sandwich_vpT (mγ Λ ε : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    ∑ a, ∑ b, photonPropagator mγ Λ ε k ν a * vpT A B k a b * photonPropagator mγ Λ ε (-k) ρ b =
      photonScalar mγ Λ ε k ^ 2 * ((A * (Minkowski.dot k k : ℂ) + B) * gPhoton ν ρ -
        A * ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
  simp only [photonPropagator_eq_metric_mul, photonScalar_neg, vpT, gPhoton, Minkowski.lower,
    Fin.sum_univ_four, Minkowski.metric]
  fin_cases ν <;> fin_cases ρ <;> simp <;> ring

/-- **The outer factor contracted with the inserted vacuum polarization** is `-(1/i)` times the
one-loop vertex chain with the sandwiched photon factor. -/
theorem vpOuter_contract (P : Params) (p kext k : Fin 4 → ℝ) (μ : Fin 4)
    (T : Fin 4 → Fin 4 → ℂ) (α β : Fin 4) :
    ∑ ρ, ∑ σ, NestedVP.vpOuter P p kext k α β μ ρ σ * T ρ σ =
      -(1 / I) * vertexChain P.e μ (electronPropagator P.m P.ε (p + kext - k))
        (electronPropagator P.m P.ε (p - k))
        (fun ν ρ' => ∑ a, ∑ b, photonPropagator P.mγ P.Λ P.ε k ν a * T a b *
          photonPropagator P.mγ P.Λ P.ε (-k) ρ' b) α β := by
  simp only [vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, NestedVP.vpOuter,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, ρ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, l0, 2, ρ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l0]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [NestedVP.outerChain]
  ring

theorem lower_neg_mul (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    ((Minkowski.lower (-k) ν : ℝ) : ℂ) * ((Minkowski.lower (-k) ρ : ℝ) : ℂ) =
      ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ) := by
  simp only [Minkowski.lower_eq]
  fin_cases ν <;> fin_cases ρ <;> simp

/-- **The Pauli projection of the reflected outer integrand**: for `ε > 0` and on-shell `p, p'`
with `q² > 0`, `pauliNum` of `k ↦ vpOuterIntegrand(-k)` is
`i (Λ² - m_γ²)² P₄(k) (i Π̂_ε(k²) k² + ε S_ε(k²))`. -/
theorem pauliNum_vpOuter_neg (P : Params) (hε : 0 < P.ε) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hm : P.m ≠ 0) (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => Matrix.of fun i j => vpOuterIntegrand P p (p' - p) i j μ (-k)) =
      I * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ P.ε p' p k *
        (I * vpLoopEps P P.ε (Minkowski.dot k k) * (Minkowski.dot k k : ℂ) +
          (P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k)) := by
  set A : ℂ := I * vpLoopEps P P.ε (Minkowski.dot k k)
  set B : ℂ := (P.ε : ℂ) * vpExtraEps P P.ε (Minkowski.dot k k)
  set φ := photonScalar P.mγ P.Λ P.ε k
  have hent : ∀ μ i j, vpOuterIntegrand P p (p' - p) i j μ (-k) =
      -(1 / I) * vertexChain P.e μ (electronPropagator P.m P.ε (p' + k))
        (electronPropagator P.m P.ε (p + k))
        (fun ν ρ => φ ^ 2 * ((A * (Minkowski.dot k k : ℂ) + B) * gPhoton ν ρ -
          A * ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) i j := by
    intro μ i j
    have e1 : vpOuterIntegrand P p (p' - p) i j μ (-k) =
        ∑ ρ, ∑ σ, NestedVP.vpOuter P p (p' - p) (-k) i j μ ρ σ * vpT A B (-k) ρ σ := by
      simp only [vpOuterIntegrand, vpT, A, B, CountertermMirror.dot_neg_neg]
    rw [e1, vpOuter_contract]
    have e2 : p + (p' - p) - -k = p' + k := by abel
    have e3 : p - -k = p + k := by abel
    rw [e2, e3]
    congr 2
    funext ν ρ
    rw [sandwich_vpT, photonScalar_neg, CountertermMirror.dot_neg_neg, mul_assoc A,
      lower_neg_mul]
    ring
  set c : ℂ := -(1 / I) * ((propDenom P.m P.ε (p' + k))⁻¹ * (propDenom P.m P.ε (p + k))⁻¹)
  have hmat : (fun μ => Matrix.of fun i j => vpOuterIntegrand P p (p' - p) i j μ (-k)) =
      fun μ => (c * (φ ^ 2 * (A * (Minkowski.dot k k : ℂ) + B))) •
          vertexChain P.e μ (electronNumerator P.m (p' + k)) (electronNumerator P.m (p + k))
            gPhoton +
        (c * (-(φ ^ 2 * A))) •
          vertexChain P.e μ (electronNumerator P.m (p' + k)) (electronNumerator P.m (p + k))
            (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
    funext μ
    ext i j
    rw [Matrix.of_apply, hent]
    have e4 : (fun ν ρ => φ ^ 2 * ((A * (Minkowski.dot k k : ℂ) + B) * gPhoton ν ρ -
        A * ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) =
        fun ν ρ => (φ ^ 2 * (A * (Minkowski.dot k k : ℂ) + B)) * gPhoton ν ρ +
          (-(φ ^ 2 * A)) * (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
      funext ν ρ; ring
    rw [e4, CountertermLimit.electronPropagator_eq_smul,
      CountertermLimit.electronPropagator_eq_smul, vertexChain_smul_out, vertexChain_smul_in,
      vertexChain_add_photon, vertexChain_smul_photon, vertexChain_smul_photon]
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, c]
    ring
  rw [hmat, pauliNum_add, pauliNum_smul, pauliNum_smul, pauliNum_longitudinal P.e hm hp' hp hq k,
    ← pauliChain]
  have ha := denom_ne_zero_of_pos (M := P.mγ) hε k
  have hb := denom_ne_zero_of_pos (M := P.Λ) hε k
  have hφ : φ =
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ((denom P.mγ P.ε k)⁻¹ * (denom P.Λ P.ε k)⁻¹) := by
    have hd : denom P.Λ P.ε k - denom P.mγ P.ε k = (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) := by
      simp only [denom]; push_cast; ring
    simp only [φ, photonScalar]
    rw [← hd]
    change (denom P.mγ P.ε k)⁻¹ - (denom P.Λ P.ε k)⁻¹ = _
    field_simp
  unfold P4 prodIntegrand
  rw [Fin.prod_univ_four, hφ]
  simp only [propDenom_eq_denom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, A, B, c]
  push_cast
  have hI : -(1 / I) = I := by rw [one_div, Complex.inv_I, neg_neg]
  rw [hI]
  ring

/-- The Pauli-projected outer integrand: `i (Λ² - m_γ²)² P₄(k) (i Π̂_ε(k²) k² + ε S_ε(k²))`. -/
noncomputable def hInt (P : Params) (ε : ℝ) (p' p k : Fin 4 → ℝ) : ℂ :=
  I * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) * P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k *
    (I * vpLoopEps P ε (Minkowski.dot k k) * (Minkowski.dot k k : ℂ) +
      (ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k))

/-- **The Pauli numerator of the class value at fixed `ε > 0`** is the energy-first integral of the
Pauli-projected outer integrand `hInt`. -/
theorem pauliNum_classValue_eq (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    pauliNum P.m p' p (fun μ => Matrix.of fun i j =>
      contractionValue₂ { P with ε := ε } Class5.VP.rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) =
      energyFirstIntegral (hInt P ε p' p) := by
  set P' : Params := { P with ε := ε }
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hval : ∀ μ i j : Fin 4, contractionValue₂ P' Class5.VP.rep (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      energyFirstIntegral (vpOuterIntegrand P' p (p' - p) i j μ) := fun μ i j =>
    contractionValue₂_VP_eq_closedForm P' hmom (fun _ => i) (fun _ => j) (fun _ => μ) hm hM₁ hM₂
      hPV₁ hPV₂ hε
  have hint : ∀ μ i j : Fin 4, EFInt (vpOuterIntegrand P' p (p' - p) i j μ) := by
    intro μ i j
    have h := efInt_vpOuterIntegrand P' (pOut := fun _ => p') (pIn := fun _ => p)
      (kIn := fun _ => p' - p) hmom (fun _ => i) (fun _ => j) (fun _ => μ) hm hM₁ hM₂
      hPV₁ hPV₂ hε
    exact h
  have hint' : ∀ μ i j : Fin 4,
      EFInt fun k => pauliWt P.m p' p μ i j * vpOuterIntegrand P' p (p' - p) i j μ k :=
    fun μ i j => (hint μ i j).const_mul _
  rw [pauliNum_eq_sum]
  simp only [Matrix.of_apply, hval]
  have e1 : ∑ μ, ∑ i, ∑ j, pauliWt P.m p' p μ i j *
      energyFirstIntegral (vpOuterIntegrand P' p (p' - p) i j μ) =
      energyFirstIntegral fun k => pauliNum P.m p' p (fun μ => Matrix.of fun i j =>
        vpOuterIntegrand P' p (p' - p) i j μ k) := by
    simp only [pauliNum_eq_sum, Matrix.of_apply]
    rw [efi_sum _ fun μ _ => EFInt.sum _ fun i _ => EFInt.sum _ fun j _ => hint' μ i j]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [efi_sum _ fun i _ => EFInt.sum _ fun j _ => hint' μ i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [efi_sum _ fun j _ => hint' μ i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [efi_const_mul]
  rw [e1, ← energyFirstIntegral_neg_eq_self]
  congr 1
  funext k
  exact pauliNum_vpOuter_neg P' hε hp' hp hq hm.ne' k

end QED.TwoLoop.VPHalfAtAssembly

end
