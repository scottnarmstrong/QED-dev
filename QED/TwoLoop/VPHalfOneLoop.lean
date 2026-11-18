/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPUnitNestedOneLoop
public import QED.TwoLoop.VPHalfKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# One spectral component of the VP insertion, through the frozen one-loop vertex

A tool for the bubble half `QED.TwoLoop.VPUnitNested.VPHalf` of the nested form of the VP unit.
After the Pauli projection (the longitudinal part drops out,
`QED.TwoLoop.VPUnitNested.pauliNum_longitudinal`), one spectral component of the transverse
vacuum-polarization insertion, of spectral mass `μ`, contributes the one-loop integrand

`pauliChain(k) · (k²)² / (D_{p'+k} D_{p+k} D_a D_b D_c D_d D_μ)`

(`perVIntegrand`), with `(a, b, c, d) = (m_γ, Λ, m_γ, Λ)` for the model's photon pair. This file
treats five distinct squared masses. Fix on-shell positive-energy `p, p'` with `q² > 0`.

* `pf_five`: the partial fractions of `(w + r)² / ∏_{x} (w + t_x)` (five factors) into
  Pauli–Villars pairs `(a, x)`, `x ∈ {b, c, d, μ}`, with exact coefficients (`r = iε`).
* `perVIntegrand_eq`: at `ε ≠ 0` the integrand is the combination
  `∑_x κ_x(ε) · pauliNum (vertexIntegrand (a, x))` of Pauli-projected frozen one-loop integrands,
  `κ_x(ε) = -(x² - iε)² / ∏_{y ≠ x} (y² - x²)`.
* `tendsto_efi_perVIntegrand`: **the `ε → 0⁺` limit of its energy-first integral** is
  `i · (e q² (4m² + q²)²/m) · (e²/(8π²)) ∫ kern5 m a b c d μ q²`, with the kernel of
  `QED/TwoLoop/VPHalfKernel.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalf

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.PauliZeroLimit QED.TwoLoop.VPUnitNested
open QED.Integration (feynmanMeasure)

theorem pair_eq {w ta tx : ℂ} (ha : w + ta ≠ 0) (hx : w + tx ≠ 0) :
    (tx - ta) * ((w + ta)⁻¹ * (w + tx)⁻¹) = (w + ta)⁻¹ - (w + tx)⁻¹ := by
  field_simp
  ring

/-- **Partial fractions with five factors**, with the exact shift `r` of the numerator:
`(w + r)² ∏_x (w + t_x)⁻¹` is the sum over `x ≠ a` of
`-(t_x - r)²/∏_{y ≠ x}(t_y - t_x) · (t_x - t_a)/((w + t_a)(w + t_x))`. -/
theorem pf_five {w r ta tb tc td te : ℂ} (ha : w + ta ≠ 0) (hb : w + tb ≠ 0) (hc : w + tc ≠ 0)
    (hd : w + td ≠ 0) (he : w + te ≠ 0) (hab : ta ≠ tb) (hac : ta ≠ tc) (had : ta ≠ td)
    (hae : ta ≠ te) (hbc : tb ≠ tc) (hbd : tb ≠ td) (hbe : tb ≠ te) (hcd : tc ≠ td)
    (hce : tc ≠ te) (hde : td ≠ te) :
    (w + r) ^ 2 * ((w + ta)⁻¹ * (w + tb)⁻¹ * (w + tc)⁻¹ * (w + td)⁻¹ * (w + te)⁻¹) =
      -((ta - tb) * (tc - tb) * (td - tb) * (te - tb))⁻¹ * (tb - r) ^ 2 *
          ((tb - ta) * ((w + ta)⁻¹ * (w + tb)⁻¹)) +
        -((ta - tc) * (tb - tc) * (td - tc) * (te - tc))⁻¹ * (tc - r) ^ 2 *
          ((tc - ta) * ((w + ta)⁻¹ * (w + tc)⁻¹)) +
        -((ta - td) * (tb - td) * (tc - td) * (te - td))⁻¹ * (td - r) ^ 2 *
          ((td - ta) * ((w + ta)⁻¹ * (w + td)⁻¹)) +
        -((ta - te) * (tb - te) * (tc - te) * (td - te))⁻¹ * (te - r) ^ 2 *
          ((te - ta) * ((w + ta)⁻¹ * (w + te)⁻¹)) := by
  have hs : ∀ {u v : ℂ}, u ≠ v → u - r - (v - r) ≠ 0 := fun h => by
    rw [sub_sub_sub_cancel_right]; exact sub_ne_zero.2 h
  have h := pf_kernel5 (K := ℂ) (A := 1) (B := 1) (C := w + r) (ta := ta - r) (tb := tb - r)
    (tc := tc - r) (td := td - r) (te := te - r) ha hb hc hd he (hs hab) (hs hac) (hs had)
    (hs hae) (hs (Ne.symm hbc)) (hs (Ne.symm hbd)) (hs (Ne.symm hbe)) (hs (Ne.symm hcd))
    (hs (Ne.symm hce)) (hs (Ne.symm hde)) (by ring) (by ring) (by ring) (by ring) (by ring)
  simp only [sub_sub_sub_cancel_right, one_mul, one_pow, mul_one] at h
  rw [pair_eq ha hb, pair_eq ha hc, pair_eq ha hd, pair_eq ha he]
  simp only [div_eq_mul_inv, mul_inv] at h ⊢
  linear_combination -h

/-- **The one-loop integrand of one spectral component** of the Pauli-projected VP insertion,
with five photon masses: `pauliChain(k) (k²)² / (D_{p'+k} D_{p+k} D_a D_b D_c D_d D_μ)`. -/
noncomputable def perVIntegrand (e m a b c d μ ε : ℝ) (p' p k : Fin 4 → ℝ) : ℂ :=
  pauliChain e m p' p k * ((Minkowski.dot k k : ℝ) : ℂ) ^ 2 *
    ((propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹ * (propDenom a ε k)⁻¹ *
      (propDenom b ε k)⁻¹ * (propDenom c ε k)⁻¹ * (propDenom d ε k)⁻¹ * (propDenom μ ε k)⁻¹)

/-- The coefficient `κ_x(ε)` of the pair `(a, x)`, with `y, z, u` the other three masses. -/
noncomputable def pfCoeff (a x y z u ε : ℝ) : ℂ :=
  -(((a ^ 2 - x ^ 2) * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) * (u ^ 2 - x ^ 2) : ℝ) : ℂ)⁻¹ *
    (((x ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) ^ 2

/-- **The spectral-component integrand as Pauli–Villars pairs**, at `ε ≠ 0`. -/
theorem perVIntegrand_eq (e m : ℝ) {a b c d μ ε : ℝ} (hε : ε ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2) (haμ : a ^ 2 ≠ μ ^ 2) (hbc : b ^ 2 ≠ c ^ 2)
    (hbd : b ^ 2 ≠ d ^ 2) (hbμ : b ^ 2 ≠ μ ^ 2) (hcd : c ^ 2 ≠ d ^ 2) (hcμ : c ^ 2 ≠ μ ^ 2)
    (hdμ : d ^ 2 ≠ μ ^ 2) (p' p k : Fin 4 → ℝ) :
    perVIntegrand e m a b c d μ ε p' p k =
      pfCoeff a b c d μ ε *
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a b ε p' p ν k) +
        pfCoeff a c b d μ ε *
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a c ε p' p ν k) +
        pfCoeff a d b c μ ε *
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a d ε p' p ν k) +
        pfCoeff a μ b c d ε *
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a μ ε p' p ν k) := by
  rw [pauliNum_vertexIntegrand _ _ _ _ hε, pauliNum_vertexIntegrand _ _ _ _ hε,
    pauliNum_vertexIntegrand _ _ _ _ hε, pauliNum_vertexIntegrand _ _ _ _ hε]
  unfold perVIntegrand pfCoeff
  set w : ℂ := ((Minkowski.dot k k : ℝ) : ℂ) - (ε : ℂ) * I
  have hD : ∀ M : ℝ, propDenom M ε k = w + ((M ^ 2 : ℝ) : ℂ) := fun M => propDenom_eq_add M ε k
  have hne : ∀ M : ℝ, w + ((M ^ 2 : ℝ) : ℂ) ≠ 0 := fun M => by
    rw [← hD]; exact propDenom_ne_zero hε k
  have hcast : ∀ {u v : ℝ}, u ≠ v → ((u : ℝ) : ℂ) ≠ ((v : ℝ) : ℂ) := fun h => by exact_mod_cast h
  have hpf := pf_five (w := w) (r := (ε : ℂ) * I) (hne a) (hne b) (hne c) (hne d) (hne μ)
    (hcast hab) (hcast hac) (hcast had) (hcast haμ) (hcast hbc) (hcast hbd) (hcast hbμ)
    (hcast hcd) (hcast hcμ) (hcast hdμ)
  have hk : ((Minkowski.dot k k : ℝ) : ℂ) = w + (ε : ℂ) * I := by simp only [w]; ring
  rw [hD a, hD b, hD c, hD d, hD μ, hk]
  set Pg := pauliChain e m p' p k
  set E := (propDenom m ε (p' + k))⁻¹ * (propDenom m ε (p + k))⁻¹
  push_cast at hpf ⊢
  linear_combination (Pg * E : ℂ) * hpf

theorem tendsto_pfCoeff (a x y z u : ℝ) :
    Tendsto (fun ε => pfCoeff a x y z u ε) (𝓝[>] 0)
      (𝓝 (-(((a ^ 2 - x ^ 2) * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) * (u ^ 2 - x ^ 2) : ℝ) : ℂ)⁻¹ *
        ((x ^ 2 : ℝ) : ℂ) ^ 2)) :=
  ((tendsto_sub_mul_I _).pow 2).const_mul _

/-- **The `ε → 0⁺` limit of one spectral component**, at on-shell positive-energy `p, p'` with
`q² > 0` and five distinct positive squared masses: the energy-first integral of
`perVIntegrand` tends to `i · (e q² (4m² + q²)²/m) · (e²/(8π²)) ∫ kern5 m a b c d μ q²`. -/
theorem tendsto_efi_perVIntegrand (e : ℝ) {m a b c d μ : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hμ : 0 < μ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ^ 2 ≠ b ^ 2)
    (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2) (haμ : a ^ 2 ≠ μ ^ 2) (hbc : b ^ 2 ≠ c ^ 2)
    (hbd : b ^ 2 ≠ d ^ 2) (hbμ : b ^ 2 ≠ μ ^ 2) (hcd : c ^ 2 ≠ d ^ 2) (hcμ : c ^ 2 ≠ μ ^ 2)
    (hdμ : d ^ 2 ≠ μ ^ 2) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (perVIntegrand e m a b c d μ ε p' p))
      (𝓝[>] 0)
      (𝓝 (I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kern5 m a b c d μ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) :
            ℂ))) := by
  have l1 := (tendsto_pfCoeff a b c d μ).mul (tendsto_efi_pauliVI (e := e) hm ha hb hp' hp hp0' hp0)
  have l2 := (tendsto_pfCoeff a c b d μ).mul (tendsto_efi_pauliVI (e := e) hm ha hc hp' hp hp0' hp0)
  have l3 := (tendsto_pfCoeff a d b c μ).mul (tendsto_efi_pauliVI (e := e) hm ha hd hp' hp hp0' hp0)
  have l4 := (tendsto_pfCoeff a μ b c d).mul (tendsto_efi_pauliVI (e := e) hm ha hμ hp' hp hp0' hp0)
  have hlim := ((l1.add l2).add l3).add l4
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      pfCoeff a b c d μ ε * QED.OneLoop.energyFirstIntegral (fun k =>
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a b ε p' p ν k)) +
        pfCoeff a c b d μ ε * QED.OneLoop.energyFirstIntegral (fun k =>
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a c ε p' p ν k)) +
        pfCoeff a d b c μ ε * QED.OneLoop.energyFirstIntegral (fun k =>
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a d ε p' p ν k)) +
        pfCoeff a μ b c d ε * QED.OneLoop.energyFirstIntegral (fun k =>
          pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a μ ε p' p ν k)) =
      QED.OneLoop.energyFirstIntegral (perVIntegrand e m a b c d μ ε p' p) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hF : perVIntegrand e m a b c d μ ε p' p = fun k =>
        pfCoeff a b c d μ ε *
            pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a b ε p' p ν k) +
          pfCoeff a c b d μ ε *
            pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a c ε p' p ν k) +
          pfCoeff a d b c μ ε *
            pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a d ε p' p ν k) +
          pfCoeff a μ b c d ε *
            pauliNum m p' p (fun ν => QED.OneLoop.vertexIntegrand e m a μ ε p' p ν k) :=
      funext fun k => perVIntegrand_eq e m hε.ne' hab hac had haμ hbc hbd hbμ hcd hcμ hdμ p' p k
    have i1 := (efInt_pauliVI (e := e) hm ha hb hp' hp hp0' hp0 hε).const_mul
      (pfCoeff a b c d μ ε)
    have i2 := (efInt_pauliVI (e := e) hm ha hc hp' hp hp0' hp0 hε).const_mul
      (pfCoeff a c b d μ ε)
    have i3 := (efInt_pauliVI (e := e) hm ha hd hp' hp hp0' hp0 hε).const_mul
      (pfCoeff a d b c μ ε)
    have i4 := (efInt_pauliVI (e := e) hm ha hμ hp' hp hp0' hp0 hε).const_mul
      (pfCoeff a μ b c d ε)
    rw [hF, efi_add ((i1.add i2).add i3) i4, efi_add (i1.add i2) i3, efi_add i1 i2,
      efi_const_mul, efi_const_mul, efi_const_mul, efi_const_mul]
  convert hlim.congr' hev using 2
  rw [pauliNum_vertexOneLoop e hm ha hb hp' hp hp0' hp0 hq,
    pauliNum_vertexOneLoop e hm ha hc hp' hp hp0' hp0 hq,
    pauliNum_vertexOneLoop e hm ha hd hp' hp hp0' hp0 hq,
    pauliNum_vertexOneLoop e hm ha hμ hp' hp hp0' hp0 hq,
    QED.OneLoop.VertexLimit.formFactorB_eq hp' hp, QED.OneLoop.VertexLimit.formFactorB_eq hp' hp,
    QED.OneLoop.VertexLimit.formFactorB_eq hp' hp, QED.OneLoop.VertexLimit.formFactorB_eq hp' hp,
    ← sum_mul_integral_pauliIntegrand_eq_kern5 hm hq.le hab hac had haμ hbc hbd hbμ hcd hcμ hdμ]
  push_cast
  ring

end QED.TwoLoop.VPHalf

end
