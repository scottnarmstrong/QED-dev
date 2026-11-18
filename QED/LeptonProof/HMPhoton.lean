/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMVertex
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.WickModel.VacuumPolarizationExistsUnique
public import QED.Frozen.WickModel.VacuumPolarizationSpec
public import QED.Frozen.TwoLoop.OnePIFunctionEqOnePIFunction
public import QED.WickModel.VacuumPolarizationLimit
import QED.TwoLoop.LoopBound
import QED.TwoLoop.ChordLoopLine
import QED.TwoLoop.IntegrableOrderFiveTransfer
import QED.TwoLoop.JointIntegral
import QED.TwoLoop.OneLoopEmbedding
import QED.TwoLoop.EnumerationDecide
import QED.TwoLoop.CountertermScaling
import QED.WickModel.LszPhotonLeg

/-!
# The flavour-summed photon condition through T1's photon condition

Helper level, Phase 5 Stage 0 (decision D-50). The order-`e²` two-photon 1PI function of the
multi-lepton model splits by flavour blocks exactly as the vertex does
(`onePIFunction₂_photon_leptonFlavors_eq`): it is T1's at `P` plus `∑_ℓ ∑_j w_{ℓ j}` times T1's at
the auxiliary parameter sets. Each contraction is simple (`isSimple_of_photon`, a finite check);
the bubble's integrand is integrable for each T1 parameter set by the sealed (Z₂). At a lightlike
`k` each T1 function tends to `(-δ₃ + Π_loop(0)) (-k^μ k^ν)` (the sealed (Z₇′) with (T₁₄)), so

* `isPhotonOnShell_leptonFlavors_iff`: **(F₁₁) holds iff `δ₃ = Π_loop(0) + ∑_ℓ π_ℓ`**, with
  `π_ℓ = ∑_j w_{ℓ j} Π_loop^{(ℓ j)}(0)` the heavy lepton's contribution (`heavyPi0`);
* `isPhotonOnShell_leptonFlavors_iff_t1`: equivalently, T1's photon condition (Z₈) holds at the
  shifted counterterm `δ₃ - ∑_ℓ π_ℓ`.
-/

@[expose] public section

open Complex Finset Filter Topology
open QED.WickModel (Params Contraction IsOnePI fermionSign loopCount lineMomentum₂
  vacuumPolarizationLoop)

namespace QED.Lepton.Proof.HM

/-! ### Simplicity of the photon contractions -/

section PhotonSimple

open QED.TwoLoop.Enumeration

theorem simpleB_photon0 :
    ∀ κ : Fin 0 → Wick.VertexKind, ∀ C : Contraction 0 2 κ, IsOnePI C → SimpleB C := by
  decide +kernel

theorem simpleB_photon1 : ∀ κ : Fin 1 → Wick.VertexKind, ∑ t, (κ t).order ≤ 2 →
    ∀ C : Contraction 0 2 κ, IsOnePI C → SimpleB C := by
  decide +kernel

theorem simpleB_photon2 : ∀ κ : Fin 2 → Wick.VertexKind, ∑ t, (κ t).order ≤ 2 →
    ∀ C : Contraction 0 2 κ, IsOnePI C → SimpleB C := by
  decide +kernel

/-- **Every 1PI two-photon contraction of order at most `2` is simple.** -/
theorem isSimple_of_photon {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order ≤ 2)
    (C : Contraction 0 2 κ) (hC : IsOnePI C) : IsSimple C := by
  have hN : N ≤ 2 := (le_sum_order κ).trans hκ
  interval_cases N
  · exact isSimple_of_simpleB (simpleB_photon0 κ C hC)
  · exact isSimple_of_simpleB (simpleB_photon1 κ hκ C hC)
  · exact isSimple_of_simpleB (simpleB_photon2 κ hκ C hC)

end PhotonSimple

open scoped Classical

/-! ### The values -/

section Values

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- A value at `loopCount C = 0` is the evaluation of its integrand. -/
theorem contractionValue₂_of_loopCount_zero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (C : Contraction nf nA κ) (h : loopCount C = 0)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ =
      regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn (Fin.elim0 :
        Fin 0 → Fin 4 → ℝ)) αOut βIn μ := by
  have key : ∀ L, loopCount C = L → QED.TwoLoop.jointEnergyFirstIntegral L
      (fun ℓ : Fin L → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) =
      contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := by
    rintro L rfl
    rfl
  rw [← key 0 h, QED.TwoLoop.jointEnergyFirstIntegral_zero]
  simp

/-- The closed form of a value without a loop: it depends on the flavours only through the
open-line mass. -/
theorem contractionValue₂_of_not_hasLoop (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) {C : Contraction nf nA κ} (hS : IsSimple C) (hL : ¬ HasLoop C)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) fun ℓ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          loopAmp P hS (Φ.mass Φ.openLine) (Φ.mass Φ.openLine) pIn kIn
            (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  unfold contractionValue₂
  congr 1
  funext ℓ
  rw [regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]

variable {n : ℕ} {H : Fin n → HeavyLepton} {X : Fin n → ℝ}

/-- **The general value split**: for a simple contraction, the split holds when, in case of a
loop, either there is no loop momentum or all the T1 integrands are integrable. -/
theorem contractionValue₂_leptonFlavors_eq_gen (P : Params) (hok : AuxOK H X P.m)
    {C : Contraction nf nA κ} (hS : IsSimple C) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4)
    (hint : HasLoop C → loopCount C = 0 ∨
      ((QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P (t1F P) C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) ∧
      ∀ ℓ j, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun x =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C
            pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ)) :
    contractionValue₂ P (leptonFlavors P H) C pOut pIn kIn αOut βIn μ =
      contractionValue₂ P (t1F P) C pOut pIn kIn αOut βIn μ +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          contractionValue₂ (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C
            pOut pIn kIn αOut βIn μ := by
  have hw : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) = 0 := fun ℓ => by
    exact_mod_cast sum_auxWeight P (X ℓ) (hok.pv₁ ℓ) (hok.pv₂ ℓ)
  by_cases hL : HasLoop C
  · rcases hint hL with h0 | ⟨hP, hQ⟩
    · simp only [contractionValue₂_of_loopCount_zero _ _ C h0,
        regulatedAmplitude₂_leptonFlavors_eq P hok hS]
    · unfold contractionValue₂
      set c : ℂ := (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹
      have hQ' : ∀ ℓ j, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun x =>
          (auxWeight P (H ℓ) (X ℓ) j : ℂ) * (c * regulatedAmplitude₂ (auxParams P (H ℓ) (X ℓ) j)
            (t1F (auxParams P (H ℓ) (X ℓ) j)) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn
              μ) := fun ℓ j => jointIntegrable_const_mul _ (hQ ℓ j)
      have e : (fun x : Fin (loopCount C) → Fin 4 → ℝ => c * regulatedAmplitude₂ P
          (leptonFlavors P H) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) = fun x =>
          c * regulatedAmplitude₂ P (t1F P) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ +
            ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) * (c * regulatedAmplitude₂
              (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) C pIn kIn
                (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) := by
        funext x
        rw [regulatedAmplitude₂_leptonFlavors_eq P hok hS, mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e, jointIntegral_add hP (jointIntegrable_sum _ fun ℓ _ =>
        jointIntegrable_sum _ fun j _ => hQ' ℓ j), jointIntegral_sum _ fun ℓ _ =>
        jointIntegrable_sum _ fun j _ => hQ' ℓ j]
      congr 1
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [jointIntegral_sum _ fun j _ => hQ' ℓ j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [jointIntegral_const_mul]
  · simp only [contractionValue₂_of_not_hasLoop _ _ hS hL, leptonFlavors_mass_openLine,
      t1F_mass_openLine]
    have hGQ : ∀ ℓ j, (fun x : Fin (loopCount C) → Fin 4 → ℝ =>
        (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          loopAmp (auxParams P (H ℓ) (X ℓ) j) hS (auxParams P (H ℓ) (X ℓ) j).m
            (auxParams P (H ℓ) (X ℓ) j).m pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) =
        fun x => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          loopAmp P hS P.m P.m pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ :=
      fun _ _ => rfl
    simp only [hGQ, ← Finset.sum_mul, hw]
    simp

end Values

/-! ### The one-loop integrability -/

section OneLoop

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **(T₉′) from the one-loop stages** for a contraction with exactly one loop. -/
theorem jointIntegrable_of_oneLoop (P : Params) (C : Contraction nf nA κ) (h1 : loopCount C = 1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4)
    (h₁ : ∀ v : Fin 3 → ℝ, MeasureTheory.Integrable fun t : ℝ =>
      QED.WickModel.regulatedAmplitude P C pOut pIn kIn (Fin.cons t v) αOut βIn μ)
    (h₂ : MeasureTheory.Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      QED.WickModel.regulatedAmplitude P C pOut pIn kIn (Fin.cons t v) αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (t1F P) C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  have hiff := QED.TwoLoop.isChord_iff_isLoopLine h1.le
  have key : ∀ L, loopCount C = L → QED.TwoLoop.jointEnergyFirstIntegrable L
      (fun ℓ : Fin L → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (t1F P) C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) := by
    intro L hL
    obtain rfl : L = 1 := hL ▸ h1
    have h0 := jointIntegrable_const_mul ((((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹)
      (QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_one_sub
        (G := fun ℓ => QED.WickModel.regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ) h₁ h₂ 0)
    convert h0 using 2 with ℓ
    rw [sub_zero, QED.TwoLoop.regulatedAmplitude_eq_regulatedAmplitude₂,
      QED.TwoLoop.lineMomentum₂_eq_lineMomentum hiff ℓ (ℓ 0) fun g hg => ?_]
    · rfl
    have h := QED.TwoLoop.card_chordsBelow_lt hg
    rw [h1] at h
    unfold QED.WickModel.chordMomentum
    rw [dite_eq_left h]
    congr 1
    exact Subsingleton.elim _ _
  exact key _ rfl

end OneLoop

/-! ### The order-`e²` photon function -/

/-- The generic sum of (F₈) over the vertex sequences of order at most `K` and their 1PI
contractions, of a function `v` of the contractions. -/
noncomputable def ctSum (nf nA K : ℕ)
    (v : (N : ℕ) → (κ : Fin N → Wick.VertexKind) → Contraction nf nA κ → ℂ) : ℂ :=
  ∑ N ∈ range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (univ : Finset (Fin N → Wick.VertexKind)).filter (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * v N κ C

theorem onePIFunction₂_eq_ctSum (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIFunction₂ P Φ nf nA K pOut pIn kIn αOut βIn μ =
      ctSum nf nA K fun _ _ C => contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := rfl

section CtSum

variable {nf nA K : ℕ}

theorem ctSum_congr {v v' : (N : ℕ) → (κ : Fin N → Wick.VertexKind) → Contraction nf nA κ → ℂ}
    (h : ∀ N (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ K → ∀ C : Contraction nf nA κ,
      IsOnePI C → v N κ C = v' N κ C) :
    ctSum nf nA K v = ctSum nf nA K v' := by
  unfold ctSum
  refine sum_congr rfl fun N _ => congrArg _ (sum_congr rfl fun κ hκ => sum_congr rfl
    fun C hC => ?_)
  rw [h N κ (mem_filter.mp hκ).2 C (mem_filter.mp hC).2]

theorem ctSum_add (v v' : (N : ℕ) → (κ : Fin N → Wick.VertexKind) → Contraction nf nA κ → ℂ) :
    ctSum nf nA K (fun N κ C => v N κ C + v' N κ C) = ctSum nf nA K v + ctSum nf nA K v' := by
  unfold ctSum
  simp only [mul_add, sum_add_distrib]

theorem ctSum_const_mul (c : ℂ)
    (v : (N : ℕ) → (κ : Fin N → Wick.VertexKind) → Contraction nf nA κ → ℂ) :
    ctSum nf nA K (fun N κ C => c * v N κ C) = c * ctSum nf nA K v := by
  unfold ctSum
  simp only [mul_sum]
  refine sum_congr rfl fun N _ => sum_congr rfl fun κ _ => sum_congr rfl fun C _ => ?_
  ring

theorem ctSum_sum {ι : Type*} (s : Finset ι)
    (v : ι → (N : ℕ) → (κ : Fin N → Wick.VertexKind) → Contraction nf nA κ → ℂ) :
    ctSum nf nA K (fun N κ C => ∑ i ∈ s, v i N κ C) = ∑ i ∈ s, ctSum nf nA K (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [ctSum]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [ctSum_add (v a) (fun N κ C => ∑ i ∈ s, v i N κ C), ih]

end CtSum

theorem exists_isLoopLine_of_loopCount_eq_one {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} (h1 : loopCount C = 1) :
    ∃ g : QED.WickModel.Line C, QED.WickModel.IsLoopLine g := by
  obtain ⟨g, hg⟩ : ∃ g : QED.WickModel.Line C, QED.WickModel.IsChord g := by
    by_contra h
    push Not at h
    unfold loopCount at h1
    simp [h] at h1
  exact ⟨g, (QED.TwoLoop.isChord_iff_isLoopLine h1.le g).1 hg⟩

/-- The sealed (Z₂) integrability, in the joint form. -/
theorem jointIntegrable_photon (P : Params) (hε : 0 < P.ε) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order ≤ 2) (C : Contraction 0 2 κ)
    (hC : IsOnePI C) (h1 : loopCount C = 1) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (t1F P) C ![] ![k, -k] (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![]
          ![μ, ν] := by
  obtain ⟨h₁, h₂⟩ := (QED.WickModel.vacuumPolarization_existsUnique P hm hM₁ hM₂ hPV₁ hPV₂).1
    P.ε hε N κ hκ C hC (exists_isLoopLine_of_loopCount_eq_one h1) k μ ν
  exact jointIntegrable_of_oneLoop P C h1 ![] ![] ![k, -k] ![] ![] ![μ, ν] h₁ h₂

variable {n : ℕ} {H : Fin n → HeavyLepton} {X : Fin n → ℝ}

/-- The auxiliary parameter sets satisfy (Z₂)'s mass conditions. -/
structure AuxGt (H : Fin n → HeavyLepton) (X : Fin n → ℝ) (m : ℝ) : Prop where
  lt_mass : ∀ ℓ j, m < hMass (H ℓ) j
  lt_X : ∀ ℓ, m < X ℓ

/-- **The order-`e²` two-photon function splits by flavour blocks.** -/
theorem onePIFunction₂_photon_leptonFlavors_eq (P : Params) (hε : 0 < P.ε) (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    onePIFunction₂ P (leptonFlavors P H) 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] =
      onePIFunction₂ P (t1F P) 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
          onePIFunction₂ (auxParams P (H ℓ) (X ℓ) j) (t1F (auxParams P (H ℓ) (X ℓ) j)) 0 2 2 ![]
            ![] ![k, -k] ![] ![] ![μ, ν] := by
  simp only [onePIFunction₂_eq_ctSum]
  rw [ctSum_congr fun N κ hκ C hC => contractionValue₂_leptonFlavors_eq_gen P hok
    (isSimple_of_photon hκ C hC) ![] ![] ![k, -k] ![] ![] ![μ, ν] fun _ => ?_]
  · rw [ctSum_add, ctSum_sum]
    congr 1
    refine sum_congr rfl fun ℓ _ => ?_
    rw [ctSum_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [ctSum_const_mul]
  · have hle := QED.TwoLoop.LoopBound.loopCount_le_one_of_order hκ (by norm_num) C hC
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · exact Or.inl h0
    · refine Or.inr ⟨jointIntegrable_photon P hε hm hM₁ hM₂ hPV₁ hPV₂ hκ C hC h1 k μ ν,
        fun ℓ j => ?_⟩
      exact jointIntegrable_photon (auxParams P (H ℓ) (X ℓ) j) hε hm (hgt.lt_mass ℓ j)
        (hgt.lt_X ℓ) (auxParams_PV₁ P (H ℓ) (X ℓ) j) (auxParams_PV₂ P (H ℓ) j (hok.hX ℓ j)) hκ
        C hC h1 k μ ν

/-! ### The limit at a lightlike photon momentum -/

/-- **T1's two-photon function at a lightlike `k`** tends to `(-δ₃ + Π_loop(0)) (-k^μ k^ν)`:
the sealed (Z₇′) with (T₁₄) and the closed form of (Z₇). -/
theorem tendsto_photon_t1 (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {k : Fin 4 → ℝ} (hk : QED.Minkowski.dot k k = 0) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => (1 / I) * onePIFunction₂ { P with ε := ε } (t1F { P with ε := ε })
        0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν]) (𝓝[>] 0)
      (𝓝 (((-P.δ₃ + vacuumPolarizationLoop P 0 : ℝ) : ℂ) * ((-(k μ * k ν) : ℝ) : ℂ))) := by
  have hk' : -(4 * P.m ^ 2) < QED.Minkowski.dot k k := by
    rw [hk]
    have := pow_pos hm 2
    linarith
  have h := (QED.WickModel.vacuumPolarization_spec P hm hM₁ hM₂ hPV₁ hPV₂).1 k hk' μ ν
  rw [QED.WickModel.vacuumPolarization_eq_loop] at h
  have e : ∀ ε : ℝ, onePIFunction₂ { P with ε := ε } (t1F { P with ε := ε }) 0 2 2 ![] ![]
      ![k, -k] ![] ![] ![μ, ν] = QED.WickModel.onePIFunction { P with ε := ε } 0 2 2 ![] ![]
        ![k, -k] ![] ![] ![μ, ν] := fun ε =>
    QED.WickModel.onePIFunction₂_eq_onePIFunction _ 0 2 2 (by norm_num) _ _ _ _ _ _
  simp only [e]
  convert h using 2
  simp only [hk, zero_mul, zero_sub]
  push_cast
  ring

/-- **The heavy lepton's `Π(0)`**: the weighted sum of the auxiliary loop functions at `0`. -/
noncomputable def heavyPi0 (P : Params) (h : HeavyLepton) (X : ℝ) : ℝ :=
  ∑ j, auxWeight P h X j * vacuumPolarizationLoop (auxParams P h X j) 0

/-- **The multi-lepton two-photon function at a lightlike `k`** tends to
`(-δ₃ + Π_loop(0) + ∑_ℓ π_ℓ) (-k^μ k^ν)`. -/
theorem tendsto_photon_lepton (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) {k : Fin 4 → ℝ} (hk : QED.Minkowski.dot k k = 0) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => (1 / I) * onePIFunction₂ { P with ε := ε } (leptonFlavors P H)
        0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν]) (𝓝[>] 0)
      (𝓝 (((-P.δ₃ + vacuumPolarizationLoop P 0 + ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ) : ℝ) : ℂ) *
        ((-(k μ * k ν) : ℝ) : ℂ))) := by
  have hT := (tendsto_photon_t1 P hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν).add (tendsto_finsetSum univ
    fun ℓ _ => tendsto_finsetSum univ fun j _ =>
      (tendsto_photon_t1 (auxParams P (H ℓ) (X ℓ) j) hm (hgt.lt_mass ℓ j) (hgt.lt_X ℓ)
        (auxParams_PV₁ P (H ℓ) (X ℓ) j) (auxParams_PV₂ P (H ℓ) j (hok.hX ℓ j)) hk μ ν).const_mul
        (auxWeight P (H ℓ) (X ℓ) j : ℂ))
  have hw : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) = 0 := fun ℓ => by
    exact_mod_cast sum_auxWeight P (X ℓ) (hok.pv₁ ℓ) (hok.pv₂ ℓ)
  convert hT.congr' ?_ using 2
  · have e : ∀ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) *
        ((((-(auxParams P (H ℓ) (X ℓ) j).δ₃ +
          vacuumPolarizationLoop (auxParams P (H ℓ) (X ℓ) j) 0 : ℝ) : ℂ)) *
            ((-(k μ * k ν) : ℝ) : ℂ)) =
        ((heavyPi0 P (H ℓ) (X ℓ) : ℝ) : ℂ) * ((-(k μ * k ν) : ℝ) : ℂ) := fun ℓ => by
      have h1 : ∀ j, (auxParams P (H ℓ) (X ℓ) j).δ₃ = P.δ₃ := fun _ => rfl
      simp only [h1, heavyPi0]
      push_cast
      have h2 : ∀ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) * ((-(P.δ₃ : ℂ) +
          (vacuumPolarizationLoop (auxParams P (H ℓ) (X ℓ) j) 0 : ℂ)) * (-((k μ : ℂ) * k ν))) =
          (-(P.δ₃ : ℂ) * (-((k μ : ℂ) * k ν))) * auxWeight P (H ℓ) (X ℓ) j +
            (auxWeight P (H ℓ) (X ℓ) j *
              (vacuumPolarizationLoop (auxParams P (H ℓ) (X ℓ) j) 0 : ℂ)) * (-((k μ : ℂ) * k ν)) :=
        fun j => by ring
      rw [sum_congr rfl fun j _ => h2 j, sum_add_distrib, ← mul_sum, ← sum_mul, hw, mul_zero,
        zero_add]
    simp only [e]
    push_cast
    rw [← sum_mul]
    ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hs := onePIFunction₂_photon_leptonFlavors_eq { P with ε := ε } hε hm hM₁ hM₂ hPV₁ hPV₂
      hok hgt k μ ν
    have hl : leptonFlavors { P with ε := ε } H = leptonFlavors P H := rfl
    rw [hl] at hs
    rw [hs, mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun ℓ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have e1 : auxWeight { P with ε := ε } (H ℓ) (X ℓ) j = auxWeight P (H ℓ) (X ℓ) j := rfl
    have e2 : onePIFunction₂ (auxParams { P with ε := ε } (H ℓ) (X ℓ) j)
        (t1F (auxParams { P with ε := ε } (H ℓ) (X ℓ) j)) 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] =
        onePIFunction₂ { auxParams P (H ℓ) (X ℓ) j with ε := ε }
          (t1F { auxParams P (H ℓ) (X ℓ) j with ε := ε }) 0 2 2 ![] ![] ![k, -k] ![] ![]
          ![μ, ν] := rfl
    rw [e1, e2]
    ring

/-- The lightlike vector `(1, 1, 0, 0)`. -/
theorem dot_lightlike : QED.Minkowski.dot ![1, 1, 0, 0] ![1, 1, 0, 0] = 0 := by
  simp [QED.Minkowski.dot, QED.Minkowski.metric, Fin.sum_univ_four]

/-- **The flavour-summed photon condition (F₁₁) in closed form**: `δ₃ = Π_loop(0) + ∑_ℓ π_ℓ`. -/
theorem isPhotonOnShell_leptonFlavors_iff (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) :
    IsPhotonOnShell P (leptonFlavors P H) ↔
      P.δ₃ = vacuumPolarizationLoop P 0 + ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ) := by
  constructor
  · intro h
    have h1 := tendsto_nhds_unique (tendsto_photon_lepton P hm hM₁ hM₂ hPV₁ hPV₂ hok hgt
      dot_lightlike 0 0) (h ![1, 1, 0, 0] dot_lightlike 0 0)
    have h2 : (-P.δ₃ + vacuumPolarizationLoop P 0 + ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ)) * (-1) = 0 := by
      have : ((-(((![1, 1, 0, 0] : Fin 4 → ℝ) 0) * ((![1, 1, 0, 0] : Fin 4 → ℝ) 0)) : ℝ) : ℂ) =
          ((-1 : ℝ) : ℂ) := by simp
      rw [this, ← Complex.ofReal_mul] at h1
      exact_mod_cast h1
    linarith
  · intro h k hk μ ν
    have hT := tendsto_photon_lepton P hm hM₁ hM₂ hPV₁ hPV₂ hok hgt hk μ ν
    have h0 : -P.δ₃ + vacuumPolarizationLoop P 0 + ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ) = 0 := by
      linarith
    rw [h0] at hT
    simpa using hT

/-- **(F₁₁) is T1's (Z₈) at the shifted counterterm `δ₃ - ∑_ℓ π_ℓ`.** -/
theorem isPhotonOnShell_leptonFlavors_iff_t1 (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) :
    IsPhotonOnShell P (leptonFlavors P H) ↔
      QED.WickModel.IsPhotonOnShell { P with δ₃ := P.δ₃ - ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ) } hm hM₁
        hM₂ hPV₁ hPV₂ := by
  rw [isPhotonOnShell_leptonFlavors_iff P hm hM₁ hM₂ hPV₁ hPV₂ hok hgt,
    QED.TwoLoop.Scaling.isPhotonOnShell_iff]
  have : vacuumPolarizationLoop { P with δ₃ := P.δ₃ - ∑ ℓ, heavyPi0 P (H ℓ) (X ℓ) } 0 =
      vacuumPolarizationLoop P 0 := rfl
  rw [this]
  constructor <;> intro h <;> simp only at h ⊢ <;> linarith

end QED.Lepton.Proof.HM

end
