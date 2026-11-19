/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideDD
public import QED.TwoLoop.VPHalfAtAssemblyProj

/-!
# The `δ₃` factor next to a closed-form bubble: the algebra of the bubble–`δ₃` classes

Helper level, Phase 5 Stage 1a (preparation of O3-6 for the bubble–`δ₃` and `δ₃`–bubble classes
`QED.ChainProof.Enum.repBD s`, `repDB s`). After the bubble is integrated at fixed `ε > 0`, the
inserted vacuum polarization is `T = A (k² g - k k) + B g` with `A = i Π̂_ε(k²)`, `B = ε S_ε(k²)`
(`QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`, in the notation
`QED.TwoLoop.VPHalfAtAssembly.vpT`). The photon chain of the class is then `Δ T Δ V Δ`
(bubble–`δ₃`) or `Δ V Δ T Δ` (`δ₃`–bubble), with `V` the `photonCt` factor. This file reduces
the `δ₃` factor algebraically:

* `sum_vpT_metric_photonCtFactor`, `sum_photonCtFactor_metric_vpT`: `T g V = V g T =
  -(i/2) δ₃ (k² T - B k k)`, from `(k² g - k k) g (k² g - k k) = k² (k² g - k k)`;
* `bdChain_eq`, `dbChain_eq`: **both photon chains are**
  `-(i/2) δ₃ (k² d(k) · Δ T Δ - B d(k)³ k k)`: the `k²` of the `δ₃` factor multiplies the photon
  chain of the two-loop vacuum-polarization class (`Δ T Δ`, as in
  `QED.TwoLoop.VPHalfAtAssembly.sandwich_vpT`), and the rest is longitudinal and proportional to
  `B = ε S_ε`;
* `pauliNum_vertexChain_bdChain`: **the Pauli projection** of the one-loop vertex chain with
  either photon chain is `-(i/2) δ₃ k² d(k)` times that of the vertex chain with `Δ T Δ`, exactly
  (the longitudinal part has no Pauli component,
  `QED.TwoLoop.VPUnitNested.pauliNum_longitudinal`). With
  `k² d(k) = (Λ² - m_γ²)(D_Λ⁻¹ - (m_γ² - iε) D_{m_γ}⁻¹ D_Λ⁻¹)`
  (`QED.ChainProof.HCLimit.kSq_mul_pvScalar`) the Pauli-projected outer integrand of a
  bubble–`δ₃` class is the Pauli-projected outer integrand of the two-loop vacuum-polarization
  class with one, resp. two, extra photon denominators.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.VPUnitNested
open QED.TwoLoop.Bridge (propDenom electronNumerator)
open QED.TwoLoop.PauliZeroLimit QED.ChainProof.HCLimit
open QED.TwoLoop.VPHalfAtAssembly (vpT)

/-! ### The tensor identity -/

/-- `T g V = -(i/2) δ₃ (k² T - B k k)`. -/
theorem sum_vpT_metric_photonCtFactor (A B : ℂ) (δ₃ : ℝ) (k : Fin 4 → ℝ) (x w : Fin 4) :
    ∑ y, vpT A B k x y * (Minkowski.metric y y : ℂ) * photonCtFactor δ₃ k y w =
      (-(I / 2) * δ₃) * (((Minkowski.dot k k : ℝ) : ℂ) * vpT A B k x w -
        B * ((k x * k w : ℝ) : ℂ)) := by
  simp only [vpT, photonCtFactor, Fin.sum_univ_four, Minkowski.dot_eq]
  fin_cases x <;> fin_cases w <;> simp [Minkowski.metric] <;> ring

/-- `V g T = -(i/2) δ₃ (k² T - B k k)`. -/
theorem sum_photonCtFactor_metric_vpT (A B : ℂ) (δ₃ : ℝ) (k : Fin 4 → ℝ) (x w : Fin 4) :
    ∑ y, photonCtFactor δ₃ k x y * (Minkowski.metric y y : ℂ) * vpT A B k y w =
      (-(I / 2) * δ₃) * (((Minkowski.dot k k : ℝ) : ℂ) * vpT A B k x w -
        B * ((k x * k w : ℝ) : ℂ)) := by
  simp only [vpT, photonCtFactor, Fin.sum_univ_four, Minkowski.dot_eq]
  fin_cases x <;> fin_cases w <;> simp [Minkowski.metric] <;> ring

/-! ### The photon chains -/

/-- The photon chain of the two-loop vacuum-polarization class, `Δ T Δ`. -/
noncomputable def vpChain (mγ Λ ε : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  ∑ a, ∑ b, QED.OneLoop.photonPropagator mγ Λ ε k ν a * vpT A B k a b *
    QED.OneLoop.photonPropagator mγ Λ ε k b ρ

/-- The photon chain of a bubble–`δ₃` class, `Δ T Δ V Δ`. -/
noncomputable def bdChain (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, QED.OneLoop.photonPropagator mγ Λ ε k ν a * vpT A B k a b *
    QED.OneLoop.photonPropagator mγ Λ ε k b c * photonCtFactor δ₃ k c d *
    QED.OneLoop.photonPropagator mγ Λ ε k d ρ

/-- The photon chain of a `δ₃`–bubble class, `Δ V Δ T Δ`. -/
noncomputable def dbChain (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, QED.OneLoop.photonPropagator mγ Λ ε k ν a * photonCtFactor δ₃ k a b *
    QED.OneLoop.photonPropagator mγ Λ ε k b c * vpT A B k c d *
    QED.OneLoop.photonPropagator mγ Λ ε k d ρ

theorem metric_mul_metric_mul (ν ρ : Fin 4) (k : Fin 4 → ℝ) :
    (Minkowski.metric ν ν : ℂ) * ((k ν * k ρ : ℝ) : ℂ) * (Minkowski.metric ρ ρ : ℂ) =
      ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ) := by
  simp only [Minkowski.lower_eq]
  fin_cases ν <;> fin_cases ρ <;> simp [Minkowski.metric]

theorem vpChain_eq (mγ Λ ε : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    vpChain mγ Λ ε A B k ν ρ = photonScalar mγ Λ ε k ^ 2 *
      ((Minkowski.metric ν ν : ℂ) * vpT A B k ν ρ * (Minkowski.metric ρ ρ : ℂ)) := by
  set φ := photonScalar mγ Λ ε k
  have s1 : vpChain mγ Λ ε A B k ν ρ = φ ^ 2 * ∑ a, (Minkowski.metric ν a : ℂ) *
      ∑ b, vpT A B k a b * (Minkowski.metric b ρ : ℂ) := by
    unfold vpChain
    simp only [photonPropagator_eq_metric_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [s1]
  simp only [sum_mul_metric, sum_metric_mul]
  ring

/-- **The bubble–`δ₃` photon chain**: `Δ T Δ V Δ = -(i/2) δ₃ (k² d · Δ T Δ - B d³ k k)`. -/
theorem bdChain_eq (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    bdChain mγ Λ ε δ₃ A B k ν ρ = (-(I / 2) * δ₃) *
      ((((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k) * vpChain mγ Λ ε A B k ν ρ -
        B * photonScalar mγ Λ ε k ^ 3 *
          (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) := by
  set φ := photonScalar mγ Λ ε k
  have s1 : bdChain mγ Λ ε δ₃ A B k ν ρ = φ ^ 3 * ∑ a, (Minkowski.metric ν a : ℂ) *
      ∑ b, vpT A B k a b * ∑ c, (Minkowski.metric b c : ℂ) *
        ∑ d, photonCtFactor δ₃ k c d * (Minkowski.metric d ρ : ℂ) := by
    unfold bdChain
    simp only [photonPropagator_eq_metric_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hb : ∀ a, ∑ b, vpT A B k a b * ((Minkowski.metric b b : ℂ) *
      (photonCtFactor δ₃ k b ρ * (Minkowski.metric ρ ρ : ℂ))) =
      (∑ b, vpT A B k a b * (Minkowski.metric b b : ℂ) * photonCtFactor δ₃ k b ρ) *
        (Minkowski.metric ρ ρ : ℂ) := fun a => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [s1, vpChain_eq]
  simp only [sum_mul_metric, sum_metric_mul]
  rw [hb, sum_vpT_metric_photonCtFactor, ← metric_mul_metric_mul]
  ring

/-- **The `δ₃`–bubble photon chain**: `Δ V Δ T Δ = -(i/2) δ₃ (k² d · Δ T Δ - B d³ k k)`. -/
theorem dbChain_eq (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    dbChain mγ Λ ε δ₃ A B k ν ρ = (-(I / 2) * δ₃) *
      ((((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k) * vpChain mγ Λ ε A B k ν ρ -
        B * photonScalar mγ Λ ε k ^ 3 *
          (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) := by
  set φ := photonScalar mγ Λ ε k
  have s1 : dbChain mγ Λ ε δ₃ A B k ν ρ = φ ^ 3 * ∑ a, (Minkowski.metric ν a : ℂ) *
      ∑ b, photonCtFactor δ₃ k a b * ∑ c, (Minkowski.metric b c : ℂ) *
        ∑ d, vpT A B k c d * (Minkowski.metric d ρ : ℂ) := by
    unfold dbChain
    simp only [photonPropagator_eq_metric_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hb : ∀ a, ∑ b, photonCtFactor δ₃ k a b * ((Minkowski.metric b b : ℂ) *
      (vpT A B k b ρ * (Minkowski.metric ρ ρ : ℂ))) =
      (∑ b, photonCtFactor δ₃ k a b * (Minkowski.metric b b : ℂ) * vpT A B k b ρ) *
        (Minkowski.metric ρ ρ : ℂ) := fun a => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [s1, vpChain_eq]
  simp only [sum_mul_metric, sum_metric_mul]
  rw [hb, sum_photonCtFactor_metric_vpT, ← metric_mul_metric_mul]
  ring

/-! ### The Pauli projection -/

/-- **The Pauli projection of the vertex chain with a bubble–`δ₃` photon chain** is
`-(i/2) δ₃ k² d(k)` times that with the vacuum-polarization chain `Δ T Δ`, exactly, for
on-shell `p, p'` with `q² > 0`, every prescription and every `A`, `B`. -/
theorem pauliNum_vertexChain_bdChain (e : ℝ) {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + k))
        (QED.OneLoop.electronPropagator m ε (p + k)) (bdChain mγ Λ ε δ₃ A B k)) =
      (-(I / 2) * δ₃) * (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k) *
        pauliNum m p' p (fun μ => vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + k))
          (QED.OneLoop.electronPropagator m ε (p + k)) (vpChain mγ Λ ε A B k)) := by
  set c : ℂ := (propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹
  set κ : ℂ := (-(I / 2) * δ₃) * (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k)
  set lc : ℂ := -((-(I / 2) * δ₃) * (B * photonScalar mγ Λ ε k ^ 3))
  have hch : bdChain mγ Λ ε δ₃ A B k = fun ν ρ => κ * vpChain mγ Λ ε A B k ν ρ +
      lc * (((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ)) := by
    funext ν ρ
    rw [bdChain_eq]
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
  simp only [vertexChain_add_photon, vertexChain_smul_photon, QED.TwoLoop.VPUnitNested.pauliNum_add, pauliNum_smul,
    pauliNum_longitudinal e hm hp' hp hq k]
  ring

/-- **The same for a `δ₃`–bubble photon chain.** -/
theorem pauliNum_vertexChain_dbChain (e : ℝ) {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (mγ Λ ε δ₃ : ℝ) (A B : ℂ) (k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + k))
        (QED.OneLoop.electronPropagator m ε (p + k)) (dbChain mγ Λ ε δ₃ A B k)) =
      (-(I / 2) * δ₃) * (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k) *
        pauliNum m p' p (fun μ => vertexChain e μ (QED.OneLoop.electronPropagator m ε (p' + k))
          (QED.OneLoop.electronPropagator m ε (p + k)) (vpChain mγ Λ ε A B k)) := by
  have h : dbChain mγ Λ ε δ₃ A B k = bdChain mγ Λ ε δ₃ A B k := by
    funext ν ρ
    rw [dbChain_eq, bdChain_eq]
  rw [h]
  exact pauliNum_vertexChain_bdChain e hm hp' hp hq mγ Λ ε δ₃ A B k

end QED.ChainProof.HCSide

end
