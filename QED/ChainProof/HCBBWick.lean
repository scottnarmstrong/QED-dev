/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBBAmplitude
public import QED.ChainProof.HCLimitNested
public import QED.ChainProof.HCLink
public import QED.ChainProof.HCKinematics

/-!
# The Wick step for the bubble–bubble representative of set (b)

Helper level, Phase 5 Stage 1a, obligation O3-6 for `QED.ChainProof.Enum.repBB`: the three-loop
analogue of `QED.TwoLoop.NestedVP.integrand_eq`.

* `regulatedAmplitude₂_bb`: the regulated amplitude (T₈) in the nested routing is
  `∑_{a b} c_a c_b` times the amplitude (T₇) of the bubble flavours `a`, `b`.
* **`integrand_eq`**: in the nested routing (`QED.ChainProof.HCBB.bbMom`), `(2π)⁻¹²` times the
  regulated amplitude of `repBB` is `bbIntegrand P (chainOuter P p kext · α β μ) ![q₂, q₁, k]`:
  the candidate outer factor `QED.ChainProof.HCLimit.chainOuter` (with the constants
  `(2π)⁻⁴ (ie)³ (1/i)⁵` of the three open-line vertices, the five outer propagators and the
  outer loop measure) times the two one-loop vacuum polarization integrands of (62.12), the
  Pauli–Villars flavours summed inside each. The signs of the two closed loops, carried by the two
  vacuum polarization integrands, cancel. An identity at every parameter set.
* **`contractionValue₂_repBB_eq_bb`**: under momentum conservation, the value (T₁₀) of `repBB` is
  the joint energy-first integral at three loops of that integrand, with no hypothesis.
* `contractionValue₂_repBB_chain`: the same for the value (F₇) at T1's flavours
  `QED.ChainProof.chainFlavors P`, with the external data of the chain vertex.
* `BBJointIntegrable`: the three-loop integrability of `bbIntegrand P (chainOuter …)` at admissible
  parameters (the content of (HC₀) for `repBB` in the nested routing). It is a hypothesis here;
  `QED.ChainProof.HCBB.bbJointIntegrable_of_chainValue` derives it from
  `QED.ChainProof.ChainValueIntegrable` for `repBB` in the frozen routing.
* **`contractionValue₂_repBB_eq_outer`**: with the conditional three-loop integrability
  `hF`, the value is the outer one-loop energy-first integral
  `∫_D dk ∑_{a b} chainOuter(k)_{a b} Π_ε(k)_a Π_ε(k)_b`
  (`QED.ChainProof.HCLimit.jointEnergyFirstIntegral_bbIntegrand_chainOuter`).
-/

@[expose] public section

namespace QED.ChainProof.HCBB

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.Enum QED.ChainProof.HCLimit Complex

open scoped Classical in
/-- The regulated amplitude (T₈) in the nested routing is the sum over the bubble flavours
`a`, `b` of `c_a c_b` times the amplitude (T₇). -/
theorem regulatedAmplitude₂_bb (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (q₂ q₁ k : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P repBB pIn kIn (bbMom (pIn 0) (kIn 0) q₂ q₁ k) αOut βIn μ =
      ∑ a : Fin 3, ∑ b : Fin 3, ((P.loopCoeff a * P.loopCoeff b : ℝ) : ℂ) *
        contractionAmplitude₂ P repBB (flavBB a b) pIn kIn (bbMom (pIn 0) (kIn 0) q₂ q₁ k)
          αOut βIn μ := by
  rw [regulatedAmplitude₂, sum_preserves]
  simp only [loopWeight_flavBB]

/-- Moving a sum inside six nested sums. -/
theorem sum_comm_six {ι : Type*} [Fintype ι] (F : ι → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 →
    Fin 4 → ℂ) :
    ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F i a b c d e f =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ i, F i a b c d e f := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]

/-- Moving the innermost of five nested sums outside the other four. -/
theorem sum_comm_out_four (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, F a b c d i = ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d i := by
  conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem mul_sum_sum_mul_mul (c U W : ℂ) (X : Fin 4 → Fin 4 → ℂ) :
    (c * ∑ l0, ∑ l2, X l0 l2) * U * W = ∑ l0, ∑ l2, c * X l0 l2 * U * W := by
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- **The Wick step** (O3-6 for `repBB`, at the level of integrands): in the nested routing,
`(2π)⁻¹²` times the regulated amplitude (T₈) of the bubble–bubble representative is the
bubble–bubble integrand `bbIntegrand` with the outer factor `chainOuter`, at `ℓ = (q₂, q₁, k)`.
An identity at every parameter set. -/
theorem integrand_eq (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (q₂ q₁ k : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repBB pIn kIn (bbMom (pIn 0) (kIn 0) q₂ q₁ k) αOut βIn μ =
      bbIntegrand P (fun k => chainOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0))
        ![q₂, q₁, k] := by
  rw [regulatedAmplitude₂_bb, bbIntegrand_vec]
  simp only [contractionAmplitude₂_flavBB, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => sum_comm_six _, sum_comm_six]
  simp only [Fintype.sum_prod_type]
  unfold chainOuter vacuumPolarizationIntegrand
  simp only [mul_sum_sum_mul_mul]
  conv_rhs => rw [sum_comm_out_four]
  refine Finset.sum_congr rfl fun l0 _ => ?_
  conv_rhs => rw [sum_comm_out_four]
  refine Finset.sum_congr rfl fun l2 _ => Finset.sum_congr rfl fun l6 _ =>
    Finset.sum_congr rfl fun l5 _ => Finset.sum_congr rfl fun l4 _ =>
    Finset.sum_congr rfl fun l3 _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [QED.TwoLoop.NestedVP.trace_rotate (Dirac.gamma l3),
    QED.TwoLoop.NestedVP.trace_rotate (Dirac.gamma l5),
    QED.TwoLoop.Insertion.photonPropagator_neg' _ _ _ k l4 l5,
    QED.TwoLoop.Insertion.photonPropagator_comm' _ _ _ k l4 l5]
  push_cast
  ring

theorem vec_eta (ℓ : Fin 3 → Fin 4 → ℝ) : ![ℓ 0, ℓ 1, ℓ 2] = ℓ := by
  funext i
  fin_cases i <;> rfl

/-- **The value of the bubble–bubble representative as a three-loop integral of the nested
integrand**: under momentum conservation, the value (T₁₀) of `repBB` is the joint energy-first
integral (T₉) at three loops of `bbIntegrand P (chainOuter P p kext · α β μ)`, at every parameter
set and with no integrability hypothesis. -/
theorem contractionValue₂_repBB_eq_bb (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repBB pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 3
        (bbIntegrand P fun k => chainOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0)) := by
  rw [contractionValue₂_repBB_eq_nested P hmom]
  refine congrArg _ (funext fun ℓ => ?_)
  rw [integrand_eq, vec_eta]

/-- The same for the value (F₇) at T1's flavours, with the external data of the chain vertex. -/
theorem contractionValue₂_repBB_chain (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    QED.Lepton.contractionValue₂ P (QED.ChainProof.chainFlavors P) repBB (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 3
        (bbIntegrand P fun k => chainOuter P p (p' - p) k α β μ) := by
  have hΦ : QED.ChainProof.chainFlavors P =
      (⟨P.mass, P.loopCoeff, 0⟩ : QED.Lepton.Flavors (Fin 3)) := rfl
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  rw [hΦ]
  exact contractionValue₂_repBB_eq_bb P hmom _ _ _

/-- **The three-loop integrability of the bubble–bubble integrand** (the content of the
integrability companion (HC₀) for `repBB`, transported to the nested routing; not proved here):
at admissible parameters, every `ε > 0`, every on-shell positive-energy pair with `q² > 0` and
all indices, both stages of the joint energy-first integral of
`bbIntegrand P (chainOuter P p (p' - p) · α β μ)` are integrable. -/
def BBJointIntegrable : Prop :=
  ∀ P : Params, QED.ChainProof.ChainAdmissible P → ∀ ε : ℝ, 0 < ε → ∀ p' p : Fin 4 → ℝ,
    QED.ChainProof.IsPairQ P.m p' p → ∀ α β μ : Fin 4,
      QED.TwoLoop.jointEnergyFirstIntegrable 3
        (bbIntegrand { P with ε := ε } fun k => chainOuter { P with ε := ε } p (p' - p) k α β μ)

/-- **The value of the bubble–bubble representative as an outer one-loop integral**, at fixed
`ε > 0`: under the mass and Pauli–Villars conditions and the three-loop integrability `hF`, the
value (F₇) at T1's flavours is `∫_D dk ∑_{a b} chainOuter(k)_{a b} Π_ε(k)_a Π_ε(k)_b`. -/
theorem contractionValue₂_repBB_eq_outer {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hε : 0 < P.ε)
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3
      (bbIntegrand P fun k => chainOuter P p (p' - p) k α β μ)) :
    QED.Lepton.contractionValue₂ P (QED.ChainProof.chainFlavors P) repBB (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) =
      QED.OneLoop.energyFirstIntegral fun k => ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4,
        chainOuter P p (p' - p) k α β μ a b * piEps P k a * piEps P k b := by
  rw [contractionValue₂_repBB_chain,
    jointEnergyFirstIntegral_bbIntegrand_chainOuter hm hM₁ hM₂ hPV₁ hPV₂ hε p (p' - p) α β μ hF]

end QED.ChainProof.HCBB

end
