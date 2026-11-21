/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajDRed
public import QED.GradedProof.RPi4MajLipRay

/-!
# (R-Π₄) step L10, two loops: increments of the class densities from their merged pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L10 (T2.UV) and
`MajLimLip4`. The increment bound `QED.GradedProof.RPi4.MajDRayInc`
(`‖u (G(u, k(s)) - G(u, k(s')))‖ ≤ C (s - s')`, `1 ≤ s' ≤ s ≤ 2s'`) is closed under finite
linear combinations, so for a class density it reduces, as `MajDRay` does
(`QED.GradedProof.RPi4.majD_vDens_of_pieces`), to the merged pieces of `triDens`.

* `MajDRayInc.zero`, `.add`, `.const_mul`, `.sum`, `.congr`: closure;
* `majDInc_triDens_of_pieces`, `MajDIncPieces`, `majDInc_blockDens_of_pieces`;
* **`majDInc_vDens_of_pieces`**, **`majDInc_classes_of_pieces`**: the three class densities.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

namespace MajDRayInc

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : MajDRayInc fun _ _ => 0 :=
  ⟨0, fun s s' _ _ _ u _ => by simp⟩

theorem add (hG : MajDRayInc G) (hH : MajDRayInc H) :
    MajDRayInc fun u k => G u k + H u k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  refine ⟨C + D, fun s s' h1 h2 h3 u hu => ?_⟩
  have e : (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) + H u (tiltVec (Real.sqrt s) s) -
      (G u (tiltVec (Real.sqrt s') s') + H u (tiltVec (Real.sqrt s') s'))) =
      (u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s')) +
        (u : ℂ) * (H u (tiltVec (Real.sqrt s) s) - H u (tiltVec (Real.sqrt s') s')) := by ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC s s' h1 h2 h3 u hu) (hD s s' h1 h2 h3 u hu))

theorem const_mul (hG : MajDRayInc G) (r : ℂ) : MajDRayInc fun u k => r * G u k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖r‖ * C, fun s s' h1 h2 h3 u hu => ?_⟩
  have e : (u : ℂ) * (r * G u (tiltVec (Real.sqrt s) s) - r * G u (tiltVec (Real.sqrt s') s')) =
      r * ((u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))) := by
    ring
  rw [e, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC s s' h1 h2 h3 u hu) (norm_nonneg _)

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, MajDRayInc (G i)) : MajDRayInc fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : MajDRayInc fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : MajDRayInc G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) : MajDRayInc H := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨C, fun s s' h1 h2 h3 u hu => ?_⟩
  rw [← e s (h1.trans h2) u hu, ← e s' h1 u hu]
  exact hC s s' h1 h2 h3 u hu

end MajDRayInc

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (M X Y : ℝ) (μ ν : Fin 4)

/-- **`triDens` increments from its merged pieces.** -/
theorem majDInc_triDens_of_pieces
    (hA : ∀ i j : Fin 4, i ≤ j → MajDRayInc (majDPieceA base c Num M X Y μ ν i j))
    (hB : ∀ i : Fin 4, MajDRayInc (majDPieceB base c Num M X Y μ ν i))
    (hP : MajDRayInc (majDPieceP base c E4 M X Y μ ν)) :
    MajDRayInc fun u k => triDens base c Num E4 M X Y u k μ ν := by
  have hA' : ∀ i j : Fin 4, MajDRayInc fun u k =>
      if i ≤ j then majDPieceA base c Num M X Y μ ν i j u k else 0 := fun i j => by
    by_cases hij : i ≤ j
    · simpa only [hij, ite_true] using hA i j hij
    · simpa only [hij, ite_false] using (MajDRayInc.zero : MajDRayInc fun _ _ => 0)
  exact ((MajDRayInc.sum Finset.univ fun i _ =>
    MajDRayInc.sum Finset.univ fun j _ => hA' i j).add
      (MajDRayInc.sum Finset.univ fun i _ => hB i)).add hP

/-- **Every merged piece of every three-flavour combination with masses `≥ m₀` is
`MajDRayInc`.** -/
def MajDIncPieces (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → MajDRayInc (majDPieceA base c Num M X Y μ ν i j)) ∧
      (∀ i : Fin 4, MajDRayInc (majDPieceB base c Num M X Y μ ν i)) ∧
        MajDRayInc (majDPieceP base c E4 M X Y μ ν)

/-- **`blockDens` increments from the merged pieces.** -/
theorem majDInc_blockDens_of_pieces {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : MajDIncPieces base c Num E4 μ ν m₀) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRayInc fun u k => blockDens base c Num E4 Φ m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  refine MajDRayInc.sum Finset.univ fun f _ => MajDRayInc.const_mul ?_ (Φ.coeff f : ℂ)
  obtain ⟨hA, hB, hP⟩ := h (Φ.mass f) (blockX Φ m₀) (blockX Φ m₀ + 1) (hmass f) hX
    (by linarith)
  exact majDInc_triDens_of_pieces base c Num E4 _ _ _ μ ν hA hB hP

end Pieces

/-- **A class density's increments from its merged pieces.** -/
theorem majDInc_vDens_of_pieces
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ) (μ ν : Fin 4) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : MajDIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRayInc fun u k => vDens A base c Φ e m₀ u k μ ν :=
  majDInc_blockDens_of_pieces base c _ _ μ ν hm₀ h Φ hmass

/-- **The three class densities' increments from their merged pieces.** -/
theorem majDInc_classes_of_pieces (e : ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA : MajDIncPieces baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) 2 3 m₀)
    (hB : MajDIncPieces baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) 2 3 m₀)
    (hC : MajDIncPieces baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) 2 3 m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    (MajDRayInc fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3) ∧
      (MajDRayInc fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3) ∧
        MajDRayInc fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3 :=
  ⟨majDInc_vDens_of_pieces _ _ _ e 2 3 hm₀ hA Φ hmass,
    majDInc_vDens_of_pieces _ _ _ e 2 3 hm₀ hB Φ hmass,
    majDInc_vDens_of_pieces _ _ _ e 2 3 hm₀ hC Φ hmass⟩

end QED.GradedProof.RPi4

end
