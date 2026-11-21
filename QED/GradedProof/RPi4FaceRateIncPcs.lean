/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncInt
public import QED.GradedProof.RPi4MajDRed

/-!
# (R-Π₄) step L10, T2.UV: the face rate on one scale from the merged pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the input
`QED.GradedProof.RPi4.MajFaceRateInc` of `QED.GradedProof.RPi4.MajLipIns`). The increment inputs
(A) `QED.GradedProof.RPi4.FaceRateIncAPow` and (B) `QED.GradedProof.RPi4.FaceRateIncB` are closed
under finite linear combinations, so for a class density they reduce, as `MajDRayInc` does
(`QED.GradedProof.RPi4.majDInc_vDens_of_pieces`), to the merged pieces `majDPieceA/B/P` of
`triDens` (photon line last).

* `FaceRateIncLin Pr`: `Pr` holds for `0` and is closed under sums and scalar multiples;
  `FaceRateIncLin.sum`; `faceRateIncLin_aPow`, `faceRateIncLin_b`;
* `faceRateInc_triDens_of_pieces`, `FaceRateIncPieces`, `faceRateInc_blockDens_of_pieces`,
  `faceRateInc_vDens_of_pieces` (any such `Pr`);
* **`faceRateInc_cls_of_pieces`**: (A) and (B) of the merged pieces give `FaceRateIncRay` of a
  class density;
* **`faceRateInc_decDil_of_pieces`**: `MajFaceRateInc` at `decDil l (decCfg 1 4)`, `l ≥ 1`, from
  `FaceIdRateRay` of the three classes and (A), (B) of their merged pieces.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- `Pr` holds for the zero density and is closed under sums and scalar multiples. -/
structure FaceRateIncLin (Pr : (ℝ → (Fin 4 → ℝ) → ℂ) → Prop) : Prop where
  zero : Pr fun _ _ => 0
  add : ∀ {G H : ℝ → (Fin 4 → ℝ) → ℂ}, Pr G → Pr H → Pr fun u k => G u k + H u k
  const_mul : ∀ {G : ℝ → (Fin 4 → ℝ) → ℂ} (r : ℂ), Pr G → Pr fun u k => r * G u k

theorem FaceRateIncLin.sum {Pr : (ℝ → (Fin 4 → ℝ) → ℂ) → Prop} (hP : FaceRateIncLin Pr)
    {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ} (h : ∀ i ∈ t, Pr (G i)) :
    Pr fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hP.zero
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact hP.add (h a (Finset.mem_insert_self a t))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem faceRateIncLin_aPow : FaceRateIncLin FaceRateIncAPow :=
  ⟨FaceRateIncAPow.zero, fun hG hH => hG.add hH, fun r hG => hG.const_mul r⟩

theorem faceRateIncLin_b : FaceRateIncLin FaceRateIncB :=
  ⟨FaceRateIncB.zero, fun hG hH => hG.add hH, fun r hG => hG.const_mul r⟩

section Pieces

variable {Pr : (ℝ → (Fin 4 → ℝ) → ℂ) → Prop} (hP : FaceRateIncLin Pr)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4)

include hP

/-- **`triDens` from its merged pieces**, for a linear predicate. -/
theorem faceRateInc_triDens_of_pieces (M X Y : ℝ)
    (hA : ∀ i j : Fin 4, i ≤ j → Pr (majDPieceA base c Num M X Y μ ν i j))
    (hB : ∀ i : Fin 4, Pr (majDPieceB base c Num M X Y μ ν i))
    (hPP : Pr (majDPieceP base c E4 M X Y μ ν)) :
    Pr fun u k => triDens base c Num E4 M X Y u k μ ν := by
  have hA' : ∀ i j : Fin 4, Pr fun u k =>
      if i ≤ j then majDPieceA base c Num M X Y μ ν i j u k else 0 := fun i j => by
    by_cases hij : i ≤ j
    · simpa only [hij, ite_true] using hA i j hij
    · simpa only [hij, ite_false] using hP.zero
  exact hP.add (hP.add (hP.sum Finset.univ fun i _ => hP.sum Finset.univ fun j _ => hA' i j)
    (hP.sum Finset.univ fun i _ => hB i)) hPP

omit hP in
/-- **Every merged piece of every three-flavour combination with masses `≥ m₀` satisfies
`Pr`.** -/
def FaceRateIncPieces (Pr : (ℝ → (Fin 4 → ℝ) → ℂ) → Prop) (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → Pr (majDPieceA base c Num M X Y μ ν i j)) ∧
      (∀ i : Fin 4, Pr (majDPieceB base c Num M X Y μ ν i)) ∧
        Pr (majDPieceP base c E4 M X Y μ ν)

/-- **`blockDens` from the merged pieces**, for a linear predicate. -/
theorem faceRateInc_blockDens_of_pieces {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : FaceRateIncPieces base c Num E4 μ ν Pr m₀) {F : Type} [Fintype F]
    (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    Pr fun u k => blockDens base c Num E4 Φ m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  refine hP.sum Finset.univ fun f _ => hP.const_mul (Φ.coeff f : ℂ) ?_
  obtain ⟨hA, hB, hPP⟩ := h (Φ.mass f) (blockX Φ m₀) (blockX Φ m₀ + 1) (hmass f) hX
    (by linarith)
  exact faceRateInc_triDens_of_pieces hP base c Num E4 μ ν _ _ _ hA hB hPP

end Pieces

/-- **A class density from its merged pieces**, for a linear predicate. -/
theorem faceRateInc_vDens_of_pieces {Pr : (ℝ → (Fin 4 → ℝ) → ℂ) → Prop}
    (hP : FaceRateIncLin Pr)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ) (μ ν : Fin 4) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν Pr m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    Pr fun u k => vDens A base c Φ e m₀ u k μ ν :=
  faceRateInc_blockDens_of_pieces hP base c _ _ μ ν hm₀ h Φ hmass

/-- **The per-class increment rate of a class density from (A) with a power loss and (B) of its
merged pieces.** -/
theorem faceRateInc_cls_of_pieces
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ) (μ ν : Fin 4) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA : FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν FaceRateIncAPow m₀)
    (hB : FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) μ ν FaceRateIncB m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    FaceRateIncRay fun u k => vDens A base c Φ e m₀ u k μ ν :=
  faceRateInc_of_pow_rate (faceRateInc_vDens_of_pieces faceRateIncLin_aPow A base c e μ ν hm₀ hA Φ
    hmass) (faceRateInc_vDens_of_pieces faceRateIncLin_b A base c e μ ν hm₀ hB Φ hmass)

/-- **`MajFaceRateInc` at `decDil l (decCfg 1 4)`**, `l ≥ 1`, `m₀ = l`, from the value face rate
`FaceIdRateRay` of the three class densities and (A), (B) of their merged pieces with masses
`≥ l`. -/
theorem faceRateInc_decDil_of_pieces (P : Params) (he : P.e ≠ 0) {l : ℝ} (hl : 1 ≤ l)
    (hA : FaceIdRateRay fun u k => vDens aVA baseVA cVA (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hB : FaceIdRateRay fun u k => vDens aVB baseVB cVB (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hC : FaceIdRateRay fun u k => vDens aVC baseVC cVC (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hAa : FaceRateIncPieces baseVA cVA (vNum P.e 0 1 aVA baseVA cVA) (vNumE4 P.e 0 1 aVA) 2 3
      FaceRateIncAPow l)
    (hBa : FaceRateIncPieces baseVB cVB (vNum P.e 0 1 aVB baseVB cVB) (vNumE4 P.e 0 1 aVB) 2 3
      FaceRateIncAPow l)
    (hCa : FaceRateIncPieces baseVC cVC (vNum P.e 0 1 aVC baseVC cVC) (vNumE4 P.e 0 1 aVC) 2 3
      FaceRateIncAPow l)
    (hAb : FaceRateIncPieces baseVA cVA (vNum P.e 0 1 aVA baseVA cVA) (vNumE4 P.e 0 1 aVA) 2 3
      FaceRateIncB l)
    (hBb : FaceRateIncPieces baseVB cVB (vNum P.e 0 1 aVB baseVB cVB) (vNumE4 P.e 0 1 aVB) 2 3
      FaceRateIncB l)
    (hCb : FaceRateIncPieces baseVC cVC (vNum P.e 0 1 aVC baseVC cVC) (vNumE4 P.e 0 1 aVC) 2 3
      FaceRateIncB l) :
    MajFaceRateInc (decDil l (decCfg 1 4)) (fun _ => 0) P.e l := by
  have hl0 : 0 < l := one_pos.trans_le hl
  have hmass1 : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hm : ∀ g, l ≤ (decDil l (decCfg 1 4)).mass g := fun g => by
    simpa using majLip_decDil_mass_ge hl0.le hmass1 g
  exact faceRateInc_decDil P he hl hA hB hC
    (faceRateInc_cls_of_pieces _ _ _ P.e 2 3 hl0 hAa hAb _ hm)
    (faceRateInc_cls_of_pieces _ _ _ P.e 2 3 hl0 hBa hBb _ hm)
    (faceRateInc_cls_of_pieces _ _ _ P.e 2 3 hl0 hCa hCb _ hm)

end QED.GradedProof.RPi4

end
