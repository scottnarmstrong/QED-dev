/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkVEnum
public import QED.ChainProof.SetCLinkShareTree
public import QED.GradedProof.V5ZeroSplitVertex
public import QED.GradedProof.VertexTwo
public import QED.GradedProof.LoopCycle

/-!
# Set (c), model link: the selected order-`e⁵` vertex through T1 parameter sets

Helper for the input (I2) of (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell` (decision
D-58), the analogue of `QED.GradedProof.V5Zero.Split.vertexOrderFive_split` for the vertex
selection `selV` of (Sc₂).

* `familyVertex_eq_orderFiveSum`: for data `D` with no level `≥ 1`, the selected order-`5` vertex
  is `(1/i)` times the order-`5` functional `orderFiveSum` of the graded values at the zero
  grading of the contractions with `VPFam` (the nonzero gradings give `0`).
* `contractionValue_zero_vSplit`: the zero-grading value of a 1PI contraction of total order `5`
  is the flavour-model value at `vParams`, hence (`V5Zero.Split.contractionValue₂_split`) the T1
  value at `zParams Q X` plus `∑_g w_g` times the T1 values at `gParams Q Φ X g`.
* **`familyVertex_split`**: the selected order-`5` vertex is `famT1 (zParams Q X)` plus
  `∑_g w_g famT1 (gParams Q Φ X g)`, where `famT1 S = (1/i)(-value(VP) + value(d3Slot0) +
  value(d3Slot1))` is the T1 vacuum-polarization family vertex (`sum_order_five_selVal`).
-/

@[expose] public section

open Complex Finset

namespace QED.ChainProof.SetCLink

open QED.Graded QED.GradedProof
open QED.WickModel (Params Contraction IsOnePI fermionSign)
open QED.Lepton.Proof.HM (orderFiveSum orderFiveSum_congr orderFiveSum_add orderFiveSum_sum
  orderFiveSum_const_mul)

/-- The T1 vacuum-polarization family vertex. -/
noncomputable def famT1 (S : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) * vpFamValue S (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => i) (fun _ => j) (fun _ => μ)

/-- A filtered sum as a sum of `ite`, for any decidability instance. -/
theorem sum_filter_any {α : Type} {p : α → Prop} {inst : DecidablePred p} (s : Finset α)
    (f : α → ℂ) : ∑ a ∈ @Finset.filter α p inst s, f a = ∑ a ∈ s, if p a then f a else 0 := by
  let _ := inst
  exact Finset.sum_filter p f

open scoped Classical in
/-- The graded value at the zero grading of a contraction of the vacuum-polarization family. -/
noncomputable def selValG (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) : ℂ :=
  if VPFam C then contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ else 0

/-- **The selected vertex of data without levels `≥ 1` as an order-`5` functional.** -/
theorem familyVertex_eq_orderFiveSum (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    familyVertex P Φ D selV 5 p' p μ i j = (1 / I) * orderFiveSum fun _ _ C =>
      selValG P Φ D (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
        (fun _ => μ) C := by
  rw [familyVertex, Matrix.of_apply]
  refine congrArg (fun x => (1 / I) * x) ?_
  unfold selectedPart orderFiveSum
  refine Finset.sum_congr rfl fun N _ => congrArg _ ?_
  rw [sum_filter_any]
  refine Finset.sum_congr rfl fun κ _ => ?_
  by_cases hκ : ∑ t, (κ t).order = 5
  · simp only [hκ, ↓reduceIte]
    have h0 : (0 : Grading κ) ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (5 + 1)).filter
        (fun g => gradedOrder κ g = 5) := by
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ => by simp, ?_⟩
      rw [gradedOrder_zero]
      exact hκ
    rw [Finset.sum_eq_single_of_mem 0 h0 fun g _ hg => Finset.sum_eq_zero fun C _ => by
      rw [contractionValue_eq_zero_of_level P Φ D hD hD₃ C g hg, mul_zero]]
    rw [sum_filter_any, sum_filter_any]
    refine Finset.sum_congr rfl fun C _ => ?_
    simp only [selValG, VPFam]
    by_cases h1 : IsOnePI C <;> by_cases h2 : (VPChain.IsVPChain 1 C ∨ ∀ t, κ t ≠ .gauge) <;>
      simp [h1, h2]
  · simp only [hκ, ↓reduceIte]
    refine Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C _ => ?_
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hκ (by simpa [gradedOrder_zero] using (Finset.mem_filter.1 hg).2)
    rw [contractionValue_eq_zero_of_level P Φ D hD hD₃ C g hg0, mul_zero]

section Split

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F} {X : ℝ}

/-- **The zero-grading value of a 1PI contraction of total order `5` through T1 parameter
sets.** -/
theorem contractionValue_zero_vSplit (hε : 0 < P.ε) (h₁ : ∑ g, Φ.coeff g = 0)
    (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hXm : X ^ 2 ≠ (GEx2.vParams P Φ D Φ.openLine).m ^ 2) (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5) (C : Contraction 1 1 κ)
    (hC : IsOnePI C) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ =
      QED.WickModel.contractionValue₂ (V5Zero.Split.zParams (GEx2.vParams P Φ D Φ.openLine) X)
          C pOut pIn kIn αOut βIn μ +
        ∑ g, (V5Zero.Split.weight (GEx2.vParams P Φ D Φ.openLine) Φ X g : ℂ) *
          QED.WickModel.contractionValue₂
            (V5Zero.Split.gParams (GEx2.vParams P Φ D Φ.openLine) Φ X g) C pOut pIn kIn αOut βIn
            μ := by
  have hCt : CtReaches C := ctReaches_of_isOnePI hC le_rfl (by omega)
  rw [contractionValue_eq_of_grading P (GEx2.vParams P Φ D Φ.openLine) Φ D C hCt 0 rfl rfl rfl
    rfl (fun t _ => by simp [GEx2.vParams]) (fun t _ => ⟨by simp [GEx2.vParams],
      by simp [GEx2.vParams], rfl⟩) (fun t _ => by simp [GEx2.vParams])]
  exact V5Zero.Split.contractionValue₂_split (Q := GEx2.vParams P Φ D Φ.openLine) hε rfl h₁ h₂
    hXm hX hκ C hC hmom αOut βIn μ

/-- **The selected order-`5` vertex through T1 parameter sets**, for data without levels
`≥ 1`. -/
theorem familyVertex_split (hε : 0 < P.ε) (h₁ : ∑ g, Φ.coeff g = 0)
    (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hXm : X ^ 2 ≠ (GEx2.vParams P Φ D Φ.openLine).m ^ 2) (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    familyVertex P Φ D selV 5 p' p μ =
      famT1 (V5Zero.Split.zParams (GEx2.vParams P Φ D Φ.openLine) X) p' p μ +
        ∑ g, (V5Zero.Split.weight (GEx2.vParams P Φ D Φ.openLine) Φ X g : ℂ) •
          famT1 (V5Zero.Split.gParams (GEx2.vParams P Φ D Φ.openLine) Φ X g) p' p μ := by
  set Q := GEx2.vParams P Φ D Φ.openLine
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
    (add_sub_cancel p p').symm
  ext i j
  rw [familyVertex_eq_orderFiveSum P Φ D hD hD₃]
  have hsel : ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order = 5 →
      ∀ C : Contraction 1 1 κ, IsOnePI C →
        selValG P Φ D (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
            (fun _ => μ) C =
          selVal (V5Zero.Split.zParams Q X) (fun _ => p') (fun _ => p) (fun _ => p' - p)
              (fun _ => i) (fun _ => j) (fun _ => μ) C +
            ∑ g, (V5Zero.Split.weight Q Φ X g : ℂ) *
              selVal (V5Zero.Split.gParams Q Φ X g) (fun _ => p') (fun _ => p)
                (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) C := by
    intro N κ hκ C hC
    by_cases h : VPFam C
    · simp only [selValG, selVal, h, ↓reduceIte]
      exact contractionValue_zero_vSplit hε h₁ h₂ hXm hX hκ C hC hmom _ _ _
    · simp [selValG, selVal, h]
  have e : ∀ S : Params, orderFiveSum (fun _ _ C => selVal S (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) C) =
      vpFamValue S (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j)
        (fun _ => μ) := fun S => sum_order_five_selVal S hmom _ _ _
  rw [orderFiveSum_congr hsel, orderFiveSum_add (fun _ _ C => selVal (V5Zero.Split.zParams Q X)
    (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) C),
    orderFiveSum_sum Finset.univ (fun g _ _ C => (V5Zero.Split.weight Q Φ X g : ℂ) *
      selVal (V5Zero.Split.gParams Q Φ X g) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) C), e]
  have e' : ∀ g, orderFiveSum (fun _ _ C => (V5Zero.Split.weight Q Φ X g : ℂ) *
      selVal (V5Zero.Split.gParams Q Φ X g) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) C) =
      (V5Zero.Split.weight Q Φ X g : ℂ) * vpFamValue (V5Zero.Split.gParams Q Φ X g)
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) :=
    fun g => by rw [orderFiveSum_const_mul, e]
  rw [Finset.sum_congr rfl fun g _ => e' g]
  rw [Matrix.add_apply, Matrix.sum_apply]
  simp only [famT1, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  ring

end Split

end QED.ChainProof.SetCLink

end
