/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXApply
import QED.ChainProof.SetCMainBKKCurve

/-!
# Split and repeated parameters of grouped Pauli resolvents

The divided difference in `QED/ChainProof/SetCRegXApply.lean` applies to
any pair of grouped coefficient functions. A coincident mass instead leaves
the shared parameter width and the higher resolvent powers.
-/

@[expose] public section

open MeasureTheory Filter Set
open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.SetCUnit
open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.Integration.TwoLoop QED.Integration.SimplexMerge

namespace QED.ChainProof.SetCUnitM

variable {r : ℕ}

/-- Adjacent factorial resolvents with coefficients on the grouped simplex. -/
noncomputable def groupedParam (c : Class5) (P : Params) (s : Fin 8)
    (F G : (Fin 8 → ℝ) → ℝ) (a A b B : ℝ) (cs : Fin r → ℝ) (z : Fin (r + 8) → ℝ) : ℝ :=
  factorialResolventPair (r + 2) (F (groupExtra s z)) (G (groupExtra s z))
    (symanzikV (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (restMomentum P.m))
      (unitMMasses P.m a A b B cs) z)

private theorem unitMV0_update_slot (c : Class5) (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    (a A b B t : ℝ) (cs : Fin r → ℝ) (x : Fin (r + 7) → ℝ) :
    unitMV0 c P s (fun _ => 1)
        (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs) x =
      unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B cs) x +
        simplexPoint x (mEmb r s) * (t ^ 2 - unitMasses P.m a A b B s ^ 2) := by
  have hMass :
      unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs =
        Function.update (unitMMasses P.m a A b B cs) (mEmb r s) t := by
    funext i
    by_cases hi : i = mEmb r s
    · subst i
      rw [Function.update_self, unitMMasses_mEmb, unitMasses_slot hs, ite_eq_left rfl]
    · rw [Function.update_of_ne hi, unitMMasses_slot hs P.m a A b B t cs i hi]
  unfold unitMV0
  rw [hMass, QED.ChainProof.SetCMainB.symanzikV_update, unitMMasses_mEmb]

private theorem ae_unitMV0_pos {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    ∀ᵐ x ∂(volume.restrict (simplexSet (r + 7))),
      0 < unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B cs) x := by
  have hX : ExtraGe μ₀ (fun _ : Fin r => 1) cs := fun j => ⟨one_pos, le_rfl, hcs j⟩
  let C := unitMCurve hc P hm hs hμ₀ hM hX
  filter_upwards [C.ae_le_vfun] with x hx
  apply C.hc.trans_le
  simpa only [C, unitMCurve, CurveData.vfun, unitMV0, curveMomentum_zero]
    using hx 0 (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)

/-- Integrate out the last extra line when its mass differs from the element mass. -/
theorem integral_groupedParam_split {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) {s : Fin 8}
    (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    (F G : (Fin 8 → ℝ) → ℝ) {cs : Fin (r + 1) → ℝ} (hcs : ∀ j, μ₀ ≤ cs j)
    (hI : IntegrableOn (fun x => groupedParam c P s F G a A b B cs (simplexPoint x))
      (simplexSet (r + 8)))
    (hIa : IntegrableOn (fun x =>
      groupedParam c P s F G a A b B (Fin.init cs) (simplexPoint x)) (simplexSet (r + 7)))
    (hIb : IntegrableOn (fun x =>
      groupedParam c P s F G (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
        (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B)
        (Fin.init cs) (simplexPoint x)) (simplexSet (r + 7)))
    (hne : unitMasses P.m a A b B s ^ 2 ≠ cs (Fin.last r) ^ 2) :
    let t := cs (Fin.last r)
    (∫ x in simplexSet (r + 8), groupedParam c P s F G a A b B cs (simplexPoint x)) =
      ((∫ x in simplexSet (r + 7), groupedParam c P s F G a A b B (Fin.init cs) (simplexPoint x)) -
        (∫ x in simplexSet (r + 7),
          groupedParam c P s F G (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
            (Fin.init cs) (simplexPoint x))) / (t ^ 2 - unitMasses P.m a A b B s ^ 2) := by
  intro t
  have ht : μ₀ ≤ t := hcs (Fin.last r)
  have hi : ∀ j, μ₀ ≤ Fin.init cs j := fun j => hcs j.castSucc
  have hMt := massesGe_slot (s := s) hM ht
  obtain ⟨_, e⟩ := integral_simplex_splitAt (m := r + 7) (by omega) (mEmb r s) hI
  rw [e, ← integral_sub hIa hIb, ← integral_div]
  apply integral_congr_ae
  filter_upwards [ae_unitMV0_pos hc P hm hs hμ₀ hM hi, ae_unitMV0_pos hc P hm hs hμ₀ hMt hi]
    with x ha hb
  let W := simplexPoint x (mEmb r s)
  let α := unitMasses P.m a A b B s ^ 2
  let β := t ^ 2
  let K := unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x - α * W
  have eα : K + α * W =
      unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x := by
    simp [K]
  have eβ : K + β * W = unitMV0 c P s (fun _ => 1)
      (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
        (Fin.init cs)) x := by
    rw [unitMV0_update_slot c P hs]
    dsimp [K, α, β, W]
    ring
  let w := groupExtra s (simplexPoint x)
  have eInt := integral_factorialResolventPair_split (r + 2) (F w) (G w) hne
    (eα.symm ▸ ha) (eβ.symm ▸ hb)
  rw [eα, eβ] at eInt
  convert eInt using 1 <;> try rfl
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [groupedParam]
  rw [groupExtra_splitAt]
  congr 1
  have eV := symanzikV_unitM_splitAt c s (restMomentum P.m) (restMomentum P.m)
    (unitMasses P.m a A b B) cs (simplexPoint x) u
  unfold unitMMasses
  rw [eV]
  change unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x +
      (W - u) * (β - α) = K + α * u + β * (W - u)
  rw [← eα]
  ring

/-- An equal pair contributes the width of its shared parameter group. -/
theorem integral_groupedParam_repeat (c : Class5) (P : Params) (s : Fin 8)
    (F G : (Fin 8 → ℝ) → ℝ) {a A b B : ℝ} {cs : Fin (r + 1) → ℝ}
    (hI : IntegrableOn (fun x => groupedParam c P s F G a A b B cs (simplexPoint x))
      (simplexSet (r + 8)))
    (heq : cs (Fin.last r) ^ 2 = unitMasses P.m a A b B s ^ 2) :
    let g := fun x : Fin (r + 7) → ℝ => simplexPoint x (mEmb r s) *
      factorialResolventPair (r + 3) (F (groupExtra s (simplexPoint x)))
        (G (groupExtra s (simplexPoint x)))
        (unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x)
    IntegrableOn g (simplexSet (r + 7)) ∧
      (∫ x in simplexSet (r + 8), groupedParam c P s F G a A b B cs (simplexPoint x)) =
        ∫ x in simplexSet (r + 7), g x := by
  intro g
  obtain ⟨hi, e⟩ := integral_simplex_splitAt (m := r + 7) (by omega) (mEmb r s) hI
  have h (x : Fin (r + 7) → ℝ) :
      (∫ u in (0 : ℝ)..simplexPoint x (mEmb r s),
        groupedParam c P s F G a A b B cs (splitAt (mEmb r s) (simplexPoint x) u)) = g x := by
    have hValue (u : ℝ) :
        groupedParam c P s F G a A b B cs (splitAt (mEmb r s) (simplexPoint x) u) =
          factorialResolventPair (r + 3) (F (groupExtra s (simplexPoint x)))
            (G (groupExtra s (simplexPoint x)))
            (unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x) := by
      unfold groupedParam unitMMasses unitMV0
      rw [groupExtra_splitAt, symanzikV_unitM_splitAt, heq, sub_self, mul_zero, add_zero]
    simp only [g, hValue, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  simp only [h] at hi e
  exact ⟨hi, e⟩

end QED.ChainProof.SetCUnitM

end
