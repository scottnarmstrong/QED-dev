/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBMassNum
public import QED.GradedProof.RPi4PairF
public import QED.GradedProof.RPi4FaceIdTriF

/-!
# Set (a), stage B4: the limit of the mass-derivative block as reduced one-loop functionals

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B4 (the mass
class). By `ksMass_dBubbleW`, at `(2, 3)` the weighted mass-derivative block `dBlockD` is the
flavour sum of convergent four-line pieces plus `∑_f C_f q²q³ D_{y,f}⁻³`. The latter is odd under
the reflection `q² ↦ -q²` and its energy-first integral vanishes; the pieces have limits through
the padded data (`QED.GradedProof.RPi4.faceId_tendsto_four`):

* `ksMass_isLoopPoly`: the cubic numerators are loop polynomials of degree three;
* `ksMassRefl`, **`ksMass_efi_odd`**: an integrand odd under `q² ↦ -q²` has energy-first
  integral `0` (no integrability needed);
* `ksMassJ`: the reduced one-loop functional `∫_{Δ₃} redBr(4, Q)` of four lines of mass `M`;
* `ksMass_tendsto_flavour`: the limit of the pieces of one flavour;
* **`ksMass_fLim_eq_param`**: if `δ (rep f) = d` for every `f`, then
  `fLim δ (k)₂₃ = ∑_f c_f d 8κ_F M_f² iπ² (J_A(M_f) + J_B(M_f))`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped Real
open QED.WickModel (Params)
open QED.Graded

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The numerators as loop polynomials -/

theorem ksMass_isLoopPoly (k : Fin 4 → ℝ) (a b c d e : ℂ) :
    IsLoopPoly 2 3 fun ℓ => ksMassN k a b c d e (ℓ 0) := by
  have hc : ∀ μ, IsLoopPoly 2 1 fun ℓ : Fin 2 → Fin 4 → ℝ => ((ℓ 0 μ : ℝ) : ℂ) := fun μ =>
    IsLoopPoly.coord 0 μ le_rfl
  have hk : IsLoopPoly 2 1 fun ℓ : Fin 2 → Fin 4 → ℝ => ((Minkowski.dot k (ℓ 0) : ℝ) : ℂ) := by
    have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => ((Minkowski.dot k (ℓ 0) : ℝ) : ℂ)) = fun ℓ =>
        (-(k 0 : ℂ)) * ((ℓ 0 0 : ℝ) : ℂ) + (k 1 : ℂ) * ((ℓ 0 1 : ℝ) : ℂ) +
          (k 2 : ℂ) * ((ℓ 0 2 : ℝ) : ℂ) + (k 3 : ℂ) * ((ℓ 0 3 : ℝ) : ℂ) := by
      funext ℓ
      simp only [Minkowski.dot_eq]
      push_cast
      ring
    rw [e]
    exact ((((hc 0).const_mul _).add ((hc 1).const_mul _)).add ((hc 2).const_mul _)).add
      ((hc 3).const_mul _)
  have hq : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => ((Minkowski.dot (ℓ 0) (ℓ 0) : ℝ) : ℂ) := by
    have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => ((Minkowski.dot (ℓ 0) (ℓ 0) : ℝ) : ℂ)) = fun ℓ =>
        (-1 : ℂ) * (((ℓ 0 0 : ℝ) : ℂ) * ((ℓ 0 0 : ℝ) : ℂ)) +
          ((ℓ 0 1 : ℝ) : ℂ) * ((ℓ 0 1 : ℝ) : ℂ) + ((ℓ 0 2 : ℝ) : ℂ) * ((ℓ 0 2 : ℝ) : ℂ) +
          ((ℓ 0 3 : ℝ) : ℂ) * ((ℓ 0 3 : ℝ) : ℂ) := by
      funext ℓ
      simp only [Minkowski.dot_eq]
      push_cast
      ring
    rw [e]
    exact (((((hc 0).mul (hc 0)).const_mul _).add ((hc 1).mul (hc 1))).add
      ((hc 2).mul (hc 2))).add ((hc 3).mul (hc 3))
  have hL : IsLoopPoly 2 1 fun ℓ : Fin 2 → Fin 4 → ℝ => ((ksMassL k (ℓ 0) : ℝ) : ℂ) := by
    have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => ((ksMassL k (ℓ 0) : ℝ) : ℂ)) = fun ℓ =>
        (k 3 : ℂ) * ((ℓ 0 2 : ℝ) : ℂ) + (k 2 : ℂ) * ((ℓ 0 3 : ℝ) : ℂ) := by
      funext ℓ
      simp only [ksMassL]
      push_cast
      ring
    rw [e]
    exact ((hc 2).const_mul _).add ((hc 3).const_mul _)
  have h23 : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => ((ℓ 0 2 * ℓ 0 3 : ℝ) : ℂ) := by
    have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => ((ℓ 0 2 * ℓ 0 3 : ℝ) : ℂ)) = fun ℓ =>
        ((ℓ 0 2 : ℝ) : ℂ) * ((ℓ 0 3 : ℝ) : ℂ) := by
      funext ℓ
      push_cast
      ring
    rw [e]
    exact (hc 2).mul (hc 3)
  have hE : (fun ℓ : Fin 2 → Fin 4 → ℝ => ksMassN k a b c d e (ℓ 0)) = fun ℓ =>
      a * (((ℓ 0 2 * ℓ 0 3 : ℝ) : ℂ) * ((Minkowski.dot k (ℓ 0) : ℝ) : ℂ)) +
        b * ((ℓ 0 2 * ℓ 0 3 : ℝ) : ℂ) + ((ksMassL k (ℓ 0) : ℝ) : ℂ) *
          (c + d * ((Minkowski.dot k (ℓ 0) : ℝ) : ℂ) +
            e * ((Minkowski.dot (ℓ 0) (ℓ 0) : ℝ) : ℂ)) := by
    funext ℓ
    simp only [ksMassN]
    push_cast
    ring
  rw [hE]
  refine ((((h23.mul hk).const_mul a).add ((h23.const_mul b).mono (by norm_num))).add
    ((hL.mul ((((IsLoopPoly.const c).add (hk.const_mul d)).mono (n' := 2) (by norm_num)).add
      (hq.const_mul e))).mono (by norm_num))).mono le_rfl

/-! ### Odd integrands -/

/-- The reflection `q² ↦ -q²`. -/
def ksMassRefl (q : Fin 4 → ℝ) : Fin 4 → ℝ := fun μ => if μ = 2 then -q μ else q μ

/-- The reflection of the second spatial coordinate (`q²` is `v 1`). -/
noncomputable def ksMassReflV : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrRight fun i => if i = 1 then MeasurableEquiv.neg ℝ else
    MeasurableEquiv.refl ℝ

theorem ksMassReflV_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    ksMassReflV v i = if i = 1 then -v i else v i := by
  by_cases h : i = 1 <;> simp [ksMassReflV, MeasurableEquiv.piCongrRight, h]

theorem ksMassReflV_preserving : MeasurePreserving ksMassReflV volume volume := by
  refine volume_preserving_pi fun i => ?_
  by_cases h : i = 1
  · simp only [h, ite_true]
    exact Measure.measurePreserving_neg _
  · simp only [h, ite_false]
    exact MeasurePreserving.id _

theorem ksMass_cons_refl (t : ℝ) (v : Fin 3 → ℝ) :
    (Fin.cons t (ksMassReflV v) : Fin 4 → ℝ) = ksMassRefl (Fin.cons t v) := by
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [ksMassRefl]
  · rw [Fin.cons_succ, ksMassReflV_apply]
    simp only [ksMassRefl, Fin.cons_succ]
    fin_cases i <;> simp

/-- **An integrand odd under `q² ↦ -q²` has energy-first integral `0`.** -/
theorem ksMass_efi_odd {F : (Fin 4 → ℝ) → ℂ} (hF : ∀ q, F (ksMassRefl q) = -F q) :
    QED.OneLoop.energyFirstIntegral F = 0 := by
  unfold QED.OneLoop.energyFirstIntegral
  set g : (Fin 3 → ℝ) → ℂ := fun v => ∫ t : ℝ, F (Fin.cons t v) with hg
  have hodd : ∀ v, g (ksMassReflV v) = -g v := fun v => by
    simp only [hg, ksMass_cons_refl, hF, integral_neg]
  have h := ksMassReflV_preserving.integral_comp' (g := g)
  simp only [hodd, integral_neg] at h
  change ∫ v, g v = 0
  linear_combination (-1 / 2 : ℂ) * h

/-! ### The pieces of one flavour -/

/-- The quartic of the piece `D_x⁻¹ D_y⁻³`. -/
noncomputable def ksMassQA (k : Fin 4 → ℝ) : LoopQuartic :=
  ksMassQ k (-8) (-4 * (Minkowski.dot k k : ℂ)) 0 0 0

/-- The quartic of the piece `D_x⁻² D_y⁻²`. -/
noncomputable def ksMassQB (k : Fin 4 → ℝ) (M : ℝ) : LoopQuartic :=
  ksMassQ k (-4) (-2 * (Minkowski.dot k k : ℂ)) ((Minkowski.dot k k : ℂ) + 2 * (M : ℂ) ^ 2) 2 2

/-- The quartic of the `iε` correction. -/
noncomputable def ksMassQL (k : Fin 4 → ℝ) : LoopQuartic := ksMassQ k 0 0 1 0 0

/-- **The reduced one-loop functional of four lines of mass `M`** with flags `b`. -/
noncomputable def ksMassJ (b : Fin 4 → Bool) (Q : LoopQuartic) (M : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ∫ w in simplexSet 3, faceIdRedBr 4 Q (faceIdX0 (faceIdP0 (faceIdBP k b) (simplexPoint w)))
    (faceIdVR (faceIdBP k b) (fun _ => M) (simplexPoint w))

section Flavour

variable {m₀ M : ℝ} (hm₀ : 0 < m₀) (hM : m₀ ≤ M) {k : Fin 4 → ℝ}
  (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)
include hm₀ hM hk

theorem ksMass_tendsto_piece (b : Fin 4 → Bool) (a₁ a₂ a₃ a₄ a₅ : ℂ) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        ksMassN k a₁ a₂ a₃ a₄ a₅ q * ksMassDen b M ε k q) (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * ksMassJ b (ksMassQ k a₁ a₂ a₃ a₄ a₅) M k)) :=
  faceId_tendsto_four b (fun _ => M) hm₀ (fun _ => hM) hk (ksMassQ_quart k a₁ a₂ a₃ a₄ a₅)
    (ksMassQ_eval k a₁ a₂ a₃ a₄ a₅) ((ksMassQ_loopDegLe k a₁ a₂ a₃ a₄ a₅).mono zero_le_one)

/-- **The limit of the pieces of one flavour.** -/
theorem ksMass_tendsto_flavour :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral (fun q =>
        ksMassNA k q * ksMassDen ksMassBA M ε k q) +
      QED.OneLoop.energyFirstIntegral (fun q => ksMassNB k M q * ksMassDen ksMassBB M ε k q) -
      2 * ((ε : ℂ) * I) *
        QED.OneLoop.energyFirstIntegral (fun q => ksMassNL k q * ksMassDen ksMassBB M ε k q))
      (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * (ksMassJ ksMassBA (ksMassQA k) M k +
        ksMassJ ksMassBB (ksMassQB k M) M k))) := by
  have hA := ksMass_tendsto_piece hm₀ hM hk ksMassBA (-8) (-4 * (Minkowski.dot k k : ℂ)) 0 0 0
  have hB := ksMass_tendsto_piece hm₀ hM hk ksMassBB (-4) (-2 * (Minkowski.dot k k : ℂ))
    ((Minkowski.dot k k : ℂ) + 2 * (M : ℂ) ^ 2) 2 2
  have hL := ksMass_tendsto_piece hm₀ hM hk ksMassBB 0 0 1 0 0
  have h := (hA.add hB).sub ((tendsto_epsI.const_mul 2).mul hL)
  simp only [mul_zero, zero_mul, sub_zero] at h
  rw [mul_add]
  exact h

end Flavour

/-! ### The limit of the weighted block -/

/-- Parameters with charge `e` (only the field `e` is read). -/
def ksMassParams (e : ℝ) : Params :=
  { e := e, δ₁ := 0, δ₂ := 0, δm := 0, δ₃ := 0, m := 1, mγ := 0, Λ := 1, ε := 0, M₁ := 2,
    M₂ := 3, c₁ := 0, c₂ := 0 }

section Block

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- The pieces of the block at `(2, 3)`. -/
noncomputable def ksMassP (e d ε : ℝ) (k q : Fin 4 → ℝ) : ℂ :=
  ∑ f, ((Φ.coeff f : ℂ) * (d : ℂ) * (8 * kF e * (Φ.mass f : ℂ) ^ 2)) *
    (ksMassNA k q * ksMassDen ksMassBA (Φ.mass f) ε k q +
      ksMassNB k (Φ.mass f) q * ksMassDen ksMassBB (Φ.mass f) ε k q +
      (-(2 * ((ε : ℂ) * I))) * (ksMassNL k q * ksMassDen ksMassBB (Φ.mass f) ε k q))

omit [DecidableEq F] in
theorem ksMass_dBlockD_sub (e : ℝ) (δ : F → ℝ) {d : ℝ} (hδ : ∀ f, δ (rep f) = d) {ε : ℝ}
    (hε : ε ≠ 0) (k q : Fin 4 → ℝ) :
    dBlockD Φ rep e δ ε k q 2 3 - ksMassP Φ e d ε k q =
      ∑ f, ((Φ.coeff f : ℂ) * (d : ℂ) * (8 * kF e * (Φ.mass f : ℂ) ^ 2)) *
        (4 * ((q 2 * q 3 : ℝ) : ℂ) * (propDenom (Φ.mass f) ε q)⁻¹ ^ 3) := by
  simp only [dBlockD, ksMassP, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hδ f]
  have h := ksMass_dBubbleW e (Φ.mass f) hε k q
  push_cast at h ⊢
  linear_combination (Φ.coeff f : ℂ) * (d : ℂ) * h

theorem ksMass_propDenom_refl (M ε : ℝ) (q : Fin 4 → ℝ) :
    propDenom M ε (ksMassRefl q) = propDenom M ε q := by
  simp only [propDenom, ksMassRefl, Minkowski.dot_eq]
  norm_num

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

theorem ksMass_efi_dBlockD {e : ℝ} (he : e ≠ 0) (δ : F → ℝ) {d : ℝ} (hδ : ∀ f, δ (rep f) = d)
    {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    QED.OneLoop.energyFirstIntegral (fun q => dBlockD Φ rep e δ ε k q 2 3) =
      ∑ f, ((Φ.coeff f : ℂ) * (d : ℂ) * (8 * kF e * (Φ.mass f : ℂ) ^ 2)) *
        (QED.OneLoop.energyFirstIntegral (fun q =>
            ksMassNA k q * ksMassDen ksMassBA (Φ.mass f) ε k q) +
          QED.OneLoop.energyFirstIntegral (fun q =>
            ksMassNB k (Φ.mass f) q * ksMassDen ksMassBB (Φ.mass f) ε k q) -
          2 * ((ε : ℂ) * I) * QED.OneLoop.energyFirstIntegral (fun q =>
            ksMassNL k q * ksMassDen ksMassBB (Φ.mass f) ε k q)) := by
  have hD : EF fun q => dBlockD Φ rep e δ ε k q 2 3 :=
    (vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ (ksMassParams e) he δ).2 ε hε k 2 3
  have ePc : ∀ (b : Fin 4 → Bool) (M : ℝ) (a₁ a₂ a₃ a₄ a₅ : ℂ),
      EF fun q => ksMassN k a₁ a₂ a₃ a₄ a₅ q * ksMassDen b M ε k q := fun b M a₁ a₂ a₃ a₄ a₅ =>
    ef_piece4c b (fun _ => M) hε k _ (ksMass_isLoopPoly k a₁ a₂ a₃ a₄ a₅)
  have eA : ∀ f, EF fun q => ksMassNA k q * ksMassDen ksMassBA (Φ.mass f) ε k q := fun f =>
    ePc _ _ _ _ _ _ _
  have eB : ∀ f, EF fun q => ksMassNB k (Φ.mass f) q * ksMassDen ksMassBB (Φ.mass f) ε k q :=
    fun f => ePc _ _ _ _ _ _ _
  have eL : ∀ f, EF fun q => ksMassNL k q * ksMassDen ksMassBB (Φ.mass f) ε k q := fun f =>
    ePc _ _ _ _ _ _ _
  have eF : ∀ f, EF fun q => ksMassNA k q * ksMassDen ksMassBA (Φ.mass f) ε k q +
      ksMassNB k (Φ.mass f) q * ksMassDen ksMassBB (Φ.mass f) ε k q +
      (-(2 * ((ε : ℂ) * I))) * (ksMassNL k q * ksMassDen ksMassBB (Φ.mass f) ε k q) := fun f =>
    ((eA f).add (eB f)).add ((eL f).const_mul _)
  have hP : EF fun q => ksMassP Φ e d ε k q :=
    EF.sum Finset.univ fun f _ => (eF f).const_mul _
  have hDP : EF fun q => dBlockD Φ rep e δ ε k q 2 3 - ksMassP Φ e d ε k q := by
    have := hD.add (hP.const_mul (-1))
    refine (congrArg EF (funext fun q => ?_)).mp this
    ring
  have hsplit : QED.OneLoop.energyFirstIntegral (fun q => dBlockD Φ rep e δ ε k q 2 3) =
      QED.OneLoop.energyFirstIntegral (fun q => dBlockD Φ rep e δ ε k q 2 3 -
        ksMassP Φ e d ε k q) + QED.OneLoop.energyFirstIntegral (fun q => ksMassP Φ e d ε k q) := by
    rw [← efi_add hDP hP]
    congr 1
    funext q
    ring
  have hodd : QED.OneLoop.energyFirstIntegral (fun q => dBlockD Φ rep e δ ε k q 2 3 -
      ksMassP Φ e d ε k q) = 0 := by
    refine ksMass_efi_odd fun q => ?_
    rw [ksMass_dBlockD_sub Φ rep e δ hδ hε.ne', ksMass_dBlockD_sub Φ rep e δ hδ hε.ne',
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksMass_propDenom_refl]
    simp only [ksMassRefl]
    norm_num
  rw [hsplit, hodd, zero_add]
  simp only [ksMassP]
  rw [faceId_efi_sum Finset.univ fun f _ => (eF f).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    efi_add ((eA f).add (eB f)) ((eL f).const_mul _), efi_add (eA f) (eB f),
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  ring

/-- **The limit of the weighted block at `(2, 3)` as reduced one-loop functionals**: if
`δ (rep f) = d` for every flavour, `fLim δ (k)₂₃ = ∑_f c_f d 8κ_F M_f² iπ² (J_A + J_B)`. -/
theorem ksMass_fLim_eq_param {e : ℝ} (he : e ≠ 0) (δ : F → ℝ) {d : ℝ}
    (hδ : ∀ f, δ (rep f) = d) {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    fLim Φ rep e δ k 2 3 =
      ∑ f, ((Φ.coeff f : ℂ) * (d : ℂ) * (8 * kF e * (Φ.mass f : ℂ) ^ 2)) *
        (I * (π : ℂ) ^ 2 * (ksMassJ ksMassBA (ksMassQA k) (Φ.mass f) k +
          ksMassJ ksMassBB (ksMassQB k (Φ.mass f)) (Φ.mass f) k)) := by
  have h := tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ (ksMassParams e) he δ hk 2 3
  have hs := tendsto_finsetSum Finset.univ fun f _ =>
    (ksMass_tendsto_flavour hm₀ (hmass f) hk).const_mul
      ((Φ.coeff f : ℂ) * (d : ℂ) * (8 * kF e * (Φ.mass f : ℂ) ^ 2))
  refine tendsto_nhds_unique h (hs.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (ksMass_efi_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ hδ hε k).symm

end Block

end QED.ChainProof.SetAKS

end
