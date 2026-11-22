/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMDispPauli

/-!
# Set (c), Stage L1: remove the crossed bubble numerator

Expanding the unit numerator recursion twice expresses the eleven-line unit in terms of
zero-numerator units with nine, ten and eleven lines. The formula uses
`QED/ChainProof/SetCUnitMPauli.lean` and the extra-line permutation invariance in
`QED/ChainProof/SetCUnitMDispPauli.lean`.
-/

public section

open QED.WickModel QED.TwoLoop.Enumeration QED.ChainProof.SetCUnit
open QED.TwoLoop.ClassIntegrable

namespace QED.ChainProof.SetCUnitM

/-- Remove two powers of the element momentum squared by using the last two extra lines. -/
theorem unitMPauliZeroPow_three_two {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B x y z : ℝ}
    (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    (hx : μ₀ ≤ x) (hy : μ₀ ≤ y) (hz : μ₀ ≤ z) :
    unitMPauliZeroPow c P s (fun _ : Fin 3 => 1)
        (unitMMasses P.m a A b B ![x, y, z]) 2 =
      unitMPauliZero c P s (fun _ : Fin 1 => 1) (unitMMasses P.m a A b B ![x]) -
        ((y ^ 2 : ℝ) : ℂ) *
          unitMPauliZero c P s (fun _ : Fin 2 => 1) (unitMMasses P.m a A b B ![x, y]) -
        ((z ^ 2 : ℝ) : ℂ) *
          (unitMPauliZero c P s (fun _ : Fin 2 => 1) (unitMMasses P.m a A b B ![x, z]) -
            ((y ^ 2 : ℝ) : ℂ) *
              unitMPauliZero c P s (fun _ : Fin 3 => 1)
                (unitMMasses P.m a A b B ![x, z, y])) := by
  have hxy : ExtraGe μ₀ (fun _ : Fin 2 => 1) ![x, y] := by
    intro i
    fin_cases i
    · exact ⟨one_pos, le_rfl, hx⟩
    · exact ⟨one_pos, le_rfl, hy⟩
  have hxyz : ExtraGe μ₀ (fun _ : Fin 3 => 1) ![x, y, z] := by
    intro i
    fin_cases i
    · exact ⟨one_pos, le_rfl, hx⟩
    · exact ⟨one_pos, le_rfl, hy⟩
    · exact ⟨one_pos, le_rfl, hz⟩
  have hxzy : ExtraGe μ₀ (fun _ : Fin 3 => 1) ![x, z, y] := by
    intro i
    fin_cases i
    · exact ⟨one_pos, le_rfl, hx⟩
    · exact ⟨one_pos, le_rfl, hz⟩
    · exact ⟨one_pos, le_rfl, hy⟩
  have e1 : Fin.init (![x, y] : Fin 2 → ℝ) = ![x] := by
    funext i
    fin_cases i
    rfl
  have e2 : Fin.init (![x, y, z] : Fin 3 → ℝ) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  have e3 : Fin.init (![x, z, y] : Fin 3 → ℝ) = ![x, z] := by
    funext i
    fin_cases i <;> rfl
  have ep : (![x, y, z] : Fin 3 → ℝ) ∘ Equiv.swap 1 2 = ![x, z, y] := by
    funext i
    fin_cases i <;> rfl
  have hperm := unitMPauliZeroPow_perm c P s (Equiv.swap (1 : Fin 3) 2)
    (fun _ => 1) P.m a A b B ![x, y, z] 1
  simp only [ep, Function.comp_def] at hperm
  have h₁ := unitMPauliZeroPow_succ hc P hm hs hμ₀ hM
    (n := 1) (by decide) (fun _ _ => rfl) hxyz
  have h₂ := unitMPauliZeroPow_succ hc P hm hs hμ₀ hM
    (n := 0) (by decide) (fun _ _ => rfl) hxy
  have h₃ := unitMPauliZeroPow_succ hc P hm hs hμ₀ hM
    (n := 0) (by decide) (fun _ _ => rfl) hxzy
  rw [e2] at h₁
  rw [e1] at h₂
  rw [e3] at h₃
  rw [h₁, ← hperm]
  simp only [show Fin.init (fun _ : Fin 3 => (1 : ℝ)) = (fun _ : Fin 2 => 1) from rfl,
    show Fin.init (fun _ : Fin 2 => (1 : ℝ)) = (fun _ : Fin 1 => 1) from rfl,
    Nat.zero_add] at h₂ h₃ ⊢
  rw [h₂, h₃]
  have hx0 : ExtraGe μ₀ (fun _ : Fin 1 => 1) ![x] := by
    intro i
    fin_cases i
    exact ⟨one_pos, le_rfl, hx⟩
  have hxz : ExtraGe μ₀ (fun _ : Fin 2 => 1) ![x, z] := by
    intro i
    fin_cases i
    · exact ⟨one_pos, le_rfl, hx⟩
    · exact ⟨one_pos, le_rfl, hz⟩
  rw [unitMPauliZeroPow_zero hc P hm hs hμ₀ hM hx0,
      unitMPauliZeroPow_zero hc P hm hs hμ₀ hM hxy,
      unitMPauliZeroPow_zero hc P hm hs hμ₀ hM hxz,
      unitMPauliZeroPow_zero hc P hm hs hμ₀ hM hxzy]
  rfl

end QED.ChainProof.SetCUnitM

end
