/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDAlgebra
public import QED.TwoLoop.VPHalfAtGenAssembly

/-!
# The Pauli projection of the bubble–`δ₃` outer integrand as two one-insertion vertices

Helper level, Phase 5 Stage 1a (O3-6 for the classes `QED.ChainProof.Enum.repBD s`,
`QED.ChainProof.Enum.repDB s`). With the bubble integrated at fixed `ε > 0`
(`T = vpT (i Π̂_ε(k²)) (ε S_ε(k²))`), the outer integrand of a bubble–`δ₃` class is the one-loop
vertex chain with the photon chain `Δ T Δ V Δ` (`QED.ChainProof.HCSide.bdChain`; the `δ₃`–bubble
chain is the same, `QED.ChainProof.HCSide.dbChain_eq`), here `bdIntegrand`.

* `pauliNum_vertexChain_vpChain`: the Pauli projection of the vertex chain with the
  vacuum-polarization chain `Δ T Δ` is `(Λ² - m_γ²)² P₄(k) (A k² + B)`, exactly.
* `kSq_mul_photonScalar`: `k² d(k) = t_Λ/D_Λ - t_{m_γ}/D_{m_γ}`, `t_M = M² - iε`.
* **`pauliNum_bdIntegrand`**: the Pauli projection of the bubble–`δ₃` outer integrand is
  `-(i/2) δ₃ (Λ² - m_γ²)² (t_Λ hIntG(m_γ, Λ, m_γ, Λ, Λ) - t_{m_γ} hIntG(m_γ, Λ, m_γ, Λ, m_γ))`, with
  `QED.TwoLoop.VPHalfAtGen.hIntG` the one-insertion vertex over five photon-type denominators.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.VPUnitNested
open QED.TwoLoop.Bridge (propDenom electronNumerator)
open QED.TwoLoop.PauliZeroLimit QED.ChainProof.HCLimit
open QED.TwoLoop.VPHalfAtAssembly (vpT P4)
open QED.TwoLoop.VPHalfAtLimit (prodIntegrand massShift denom_eq_add_massShift
  denom_ne_zero_of_pos propDenom_eq_denom)
open QED.TwoLoop.VPHalfAtGen (hIntG PG prodIntegrand_snoc)
open QED.TwoLoop.VPHalfAt (vpLoopEps vpExtraEps)

/-- The five photon-type masses `(a, b, a, b, M)` of a bubble–`δ₃` piece. -/
noncomputable def sideMs (a b M : ℝ) : Fin (2 + 1 + 2) → ℝ :=
  Fin.snoc (![a, b, a, b] : Fin (2 + 2) → ℝ) M

/-- **The bubble–`δ₃` outer integrand**: the one-loop vertex chain with the photon chain
`Δ T Δ V Δ`, `T = vpT (i Π̂_ε(k²)) (ε S_ε(k²))`. -/
noncomputable def bdIntegrand (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ε : ℝ)
    (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
    (QED.OneLoop.electronPropagator P.m ε (p + k))
    (bdChain P.mγ P.Λ ε P.δ₃ (I * vpLoopEps P ε (Minkowski.dot k k))
      ((ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k)) k)

/-! ### The vacuum-polarization chain -/

theorem vpChain_eq_g (mγ Λ ε : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    vpChain mγ Λ ε A B k ν ρ = photonScalar mγ Λ ε k ^ 2 *
      ((A * (Minkowski.dot k k : ℂ) + B) * gPhoton ν ρ -
        A * ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
  simp only [vpChain, photonPropagator_eq_metric_mul, vpT, gPhoton, Minkowski.lower,
    Fin.sum_univ_four, Minkowski.metric]
  fin_cases ν <;> fin_cases ρ <;> simp <;> ring

theorem photonScalar_eq_denom (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) :
    photonScalar mγ Λ ε k = (QED.OneLoop.denom mγ ε k)⁻¹ - (QED.OneLoop.denom Λ ε k)⁻¹ := rfl

/-- **The Pauli projection of the vertex chain with `Δ T Δ`**: `(Λ² - m_γ²)² P₄(k) (A k² + B)`. -/
theorem pauliNum_vertexChain_vpChain (e : ℝ) {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (A B : ℂ)
    (k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + k))
        (QED.OneLoop.electronPropagator m ε (p + k)) (vpChain mγ Λ ε A B k)) =
      (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) * P4 (pauliChain e m p' p) m mγ Λ ε p' p k *
        (A * (Minkowski.dot k k : ℂ) + B) := by
  set φ := photonScalar mγ Λ ε k
  set c : ℂ := (propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹
  have hch : vpChain mγ Λ ε A B k = fun ν ρ => (φ ^ 2 * (A * (Minkowski.dot k k : ℂ) + B)) *
      gPhoton ν ρ + (-(φ ^ 2 * A)) *
        (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
    funext ν ρ
    rw [vpChain_eq_g]
    ring
  have hprop : ∀ D : Fin 4 → Fin 4 → ℂ, ∀ μ,
      vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + k))
        (QED.OneLoop.electronPropagator m ε (p + k)) D =
      c • vertexChain e μ (electronNumerator m (p' + k)) (electronNumerator m (p + k)) D := by
    intro D μ
    rw [electronPropagator_eq_smul, electronPropagator_eq_smul, vertexChain_smul_out,
      vertexChain_smul_in, smul_smul]
  simp only [hprop, pauliNum_smul]
  rw [hch]
  simp only [vertexChain_add_photon, vertexChain_smul_photon,
    QED.TwoLoop.VPUnitNested.pauliNum_add, pauliNum_smul, pauliNum_longitudinal e hm hp' hp hq k]
  rw [← pauliChain]
  have ha := QED.TwoLoop.VPHalfAtLimit.denom_ne_zero_of_pos (M := mγ) hε k
  have hb := QED.TwoLoop.VPHalfAtLimit.denom_ne_zero_of_pos (M := Λ) hε k
  have hφ : φ = (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ)) *
      ((QED.OneLoop.denom mγ ε k)⁻¹ * (QED.OneLoop.denom Λ ε k)⁻¹) := by
    have hd : QED.OneLoop.denom Λ ε k - QED.OneLoop.denom mγ ε k =
        (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ)) := by
      simp only [QED.OneLoop.denom]; push_cast; ring
    show photonScalar mγ Λ ε k = _
    rw [photonScalar_eq_denom, ← hd]
    field_simp
  unfold P4 prodIntegrand
  rw [Fin.prod_univ_four, hφ]
  simp only [propDenom_eq_denom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c]
  push_cast
  ring

/-! ### The bubble–`δ₃` integrand -/

/-- `k² d(k) = t_Λ/D_Λ - t_{m_γ}/D_{m_γ}`. -/
theorem kSq_mul_photonScalar (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    ((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k =
      massShift Λ ε * (QED.OneLoop.denom Λ ε k)⁻¹ -
        massShift mγ ε * (QED.OneLoop.denom mγ ε k)⁻¹ := by
  have ha := QED.TwoLoop.VPHalfAtLimit.denom_ne_zero_of_pos (M := mγ) hε k
  have hb := QED.TwoLoop.VPHalfAtLimit.denom_ne_zero_of_pos (M := Λ) hε k
  have ea := denom_eq_add_massShift mγ ε k
  have eb := denom_eq_add_massShift Λ ε k
  rw [photonScalar_eq_denom, ea, eb]
  rw [ea] at ha
  rw [eb] at hb
  field_simp
  ring

theorem const_eq_snoc {k : ℕ} (ε : ℝ) :
    (fun _ => ε : Fin (k + 1 + 2) → ℝ) = (Fin.snoc (fun _ => ε : Fin (k + 2) → ℝ) ε :
      Fin (k + 1 + 2) → ℝ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (Fin.snoc_last (α := fun _ => ℝ) _ _).symm
  · simp

theorem PG_sideMs (P : Params) (a b M ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    PG P (sideMs a b M) ε p' p ℓ =
      P4 (pauliChain P.e P.m p' p) P.m a b ε p' p ℓ * (QED.OneLoop.denom M ε ℓ)⁻¹ := by
  unfold PG sideMs
  rw [const_eq_snoc (k := 2) ε, prodIntegrand_snoc]
  rfl

/-- **The Pauli projection of the bubble–`δ₃` outer integrand**, exactly at `ε > 0`. -/
theorem pauliNum_bdIntegrand (P : Params) (hm : P.m ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => bdIntegrand P p' p μ ε k) =
      (-(I / 2) * P.δ₃) * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        (massShift P.Λ ε * hIntG P (sideMs P.mγ P.Λ P.Λ) ε p' p k -
          massShift P.mγ ε * hIntG P (sideMs P.mγ P.Λ P.mγ) ε p' p k) := by
  unfold bdIntegrand
  rw [pauliNum_vertexChain_bdChain P.e hm hp' hp hq,
    pauliNum_vertexChain_vpChain P.e hm hp' hp hq P.mγ P.Λ hε]
  unfold hIntG
  rw [PG_sideMs, PG_sideMs]
  have h := kSq_mul_photonScalar P.mγ P.Λ hε k
  set Q := P4 (pauliChain P.e P.m p' p) P.m P.mγ P.Λ ε p' p k
  set X := I * vpLoopEps P ε (Minkowski.dot k k) * ((Minkowski.dot k k : ℝ) : ℂ) +
    (ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k)
  linear_combination (-(I / 2) * (P.δ₃ : ℂ)) * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) * Q * X * h

end QED.ChainProof.HCSide

end
