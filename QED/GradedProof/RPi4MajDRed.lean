/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajUV
public import QED.GradedProof.RPi4PairDensClass
public import QED.GradedProof.RPi4WireRed

/-!
# (R-Π₄) step L10, two loops: the class densities from their merged pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV). The
bound `QED.GradedProof.RPi4.MajDRay` (`‖u G(u, k)‖ ≤ C s` at the ray vector and at the null
vector of the tilt `c = √s`, `s, u ≥ 1`) is closed under finite linear combinations, so for a
class density `QED.GradedProof.RPi4.vDens` it reduces to the one-photon-line densities
`QED.GradedProof.RPi4.pairDens` of the fifteen merged pieces of each flavour.

* `MajDRay.zero`, `.add`, `.const_mul`, `.sum`, `.congr`: closure;
* `majDPieceA`, `majDPieceB`, `majDPieceP`: the merged pieces of `triDens` (seven lines, six
  lines, padded), `majD_triDens_eq`;
* `MajDPieces`: every merged piece of every three-flavour combination with masses `≥ m₀` is
  `MajDRay`;
* **`majD_vDens_of_pieces`**: `MajDPieces` of a class numerator gives `MajDRay` of the class
  density, for every flavour set with masses `≥ m₀`.
-/

@[expose] public section

open Complex MeasureTheory Matrix

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

namespace MajDRay

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : MajDRay fun _ _ => 0 :=
  ⟨0, fun s _ u _ => by simp⟩

theorem add (hG : MajDRay G) (hH : MajDRay H) : MajDRay fun u k => G u k + H u k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  refine ⟨C + D, fun s hs u hu => ⟨?_, ?_⟩⟩
  · rw [mul_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC s hs u hu).1 (hD s hs u hu).1)
  · rw [mul_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC s hs u hu).2 (hD s hs u hu).2)

theorem const_mul (hG : MajDRay G) (r : ℂ) : MajDRay fun u k => r * G u k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖r‖ * C, fun s hs u hu => ⟨?_, ?_⟩⟩
  · rw [mul_left_comm, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC s hs u hu).1 (norm_nonneg _)
  · rw [mul_left_comm, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC s hs u hu).2 (norm_nonneg _)

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, MajDRay (G i)) : MajDRay fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : MajDRay fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : MajDRay G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s) ∧
        G u (tiltVec (Real.sqrt s) 0) = H u (tiltVec (Real.sqrt s) 0)) : MajDRay H := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨C, fun s hs u hu => ?_⟩
  rw [← (e s hs u hu).1, ← (e s hs u hu).2]
  exact hC s hs u hu

end MajDRay

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (M X Y : ℝ) (μ ν : Fin 4)

/-- The merged piece with seven lines `(i, j)` of `triDens` (fermion lines `i`, `j` doubled). -/
noncomputable def majDPieceA (i j : Fin 4) (u : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      Num M k ℓ μ ν)
    (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
    (fun l => c (shA i j l.castSucc) • k)
    ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
    (Fin.last 6) u

/-- The merged piece with six lines `i` of `triDens` (fermion line `i` doubled). -/
noncomputable def majDPieceB (i : Fin 4) (u : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
    (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
    (fun l => c (shB i l.castSucc) • k)
    ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u

/-- The padded merged piece of `triDens`. -/
noncomputable def majDPieceP (u : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  pairDens (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν *
      propDenom Y 0 (fm base (ppc c k) 0 ℓ))
    (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
    (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) u

theorem majD_triDens_eq (u : ℝ) (k : Fin 4 → ℝ) :
    triDens base c Num E4 M X Y u k μ ν =
      (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then majDPieceA base c Num M X Y μ ν i j u k
        else 0) + ∑ i : Fin 4, majDPieceB base c Num M X Y μ ν i u k +
        majDPieceP base c E4 M X Y μ ν u k :=
  rfl

/-- **`triDens` from its merged pieces.** -/
theorem majD_triDens_of_pieces
    (hA : ∀ i j : Fin 4, i ≤ j → MajDRay (majDPieceA base c Num M X Y μ ν i j))
    (hB : ∀ i : Fin 4, MajDRay (majDPieceB base c Num M X Y μ ν i))
    (hP : MajDRay (majDPieceP base c E4 M X Y μ ν)) :
    MajDRay fun u k => triDens base c Num E4 M X Y u k μ ν := by
  have hA' : ∀ i j : Fin 4, MajDRay fun u k =>
      if i ≤ j then majDPieceA base c Num M X Y μ ν i j u k else 0 := fun i j => by
    by_cases hij : i ≤ j
    · simpa only [hij, ite_true] using hA i j hij
    · simpa only [hij, ite_false] using (MajDRay.zero : MajDRay fun _ _ => 0)
  exact ((MajDRay.sum Finset.univ fun i _ => MajDRay.sum Finset.univ fun j _ => hA' i j).add
    (MajDRay.sum Finset.univ fun i _ => hB i)).add hP

/-- **Every merged piece of every three-flavour combination with masses `≥ m₀` is
`MajDRay`.** -/
def MajDPieces (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → MajDRay (majDPieceA base c Num M X Y μ ν i j)) ∧
      (∀ i : Fin 4, MajDRay (majDPieceB base c Num M X Y μ ν i)) ∧
        MajDRay (majDPieceP base c E4 M X Y μ ν)

/-- **`blockDens` from the merged pieces.** -/
theorem majD_blockDens_of_pieces {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : MajDPieces base c Num E4 μ ν m₀) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRay fun u k => blockDens base c Num E4 Φ m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  refine MajDRay.sum Finset.univ fun f _ => MajDRay.const_mul ?_ (Φ.coeff f : ℂ)
  obtain ⟨hA, hB, hP⟩ := h (Φ.mass f) (blockX Φ m₀) (blockX Φ m₀ + 1) (hmass f) hX
    (by linarith)
  exact majD_triDens_of_pieces base c Num E4 _ _ _ μ ν hA hB hP

end Pieces

/-- **A class density from its merged pieces**: `MajDPieces` of the normalized class numerator
`vNum e 0 1` gives `MajDRay` of `vDens`. -/
theorem majD_vDens_of_pieces (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ) (μ ν : Fin 4) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : MajDPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRay fun u k => vDens A base c Φ e m₀ u k μ ν :=
  majD_blockDens_of_pieces base c _ _ μ ν hm₀ h Φ hmass

/-- **`WireDRay` from the merged pieces of the three classes.** -/
theorem majD_wireDRay_of_pieces (e : ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA : MajDPieces baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) 2 3 m₀)
    (hB : MajDPieces baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) 2 3 m₀)
    (hC : MajDPieces baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) 2 3 m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    WireDRay Φ e m₀ :=
  ⟨majD_vDens_of_pieces _ _ _ e 2 3 hm₀ hA Φ hmass,
    majD_vDens_of_pieces _ _ _ e 2 3 hm₀ hB Φ hmass,
    majD_vDens_of_pieces _ _ _ e 2 3 hm₀ hC Φ hmass⟩

end QED.GradedProof.RPi4

end
