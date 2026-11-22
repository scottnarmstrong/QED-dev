/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDKDel

/-!
# Set (c), the `δ₃` classes: the Ward vertex of each orbit

Helper level for the open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink`. For each of the
twelve classes `repB i` the element line (class line `pvLines (repBSlot i)`) ends on the chain
vertices `rev skP i`, `rev skQ i`; at a vertex `u` of the chain (between the electron momenta
`K'_u`, `K'_{u+1}`, with `K'_0 = p`, `K'_5 = p'`) the element momentum is `± (K'_{u+1} - K'_u)`.

* `kWardD i`: the end used for the Ward identity (an internal vertex when there is one; the
  outgoing end `4` for `i = 0, 6, 10`, whose other end is `0`), `kOthD i` the other end;
  `kPermD i` the photon labels `(rev skE, kWardD, kOthD, rev skR, rev skT)`;
* **`kChainD_repD_eq`**: the chain of `repD i s` in these labels (`kChainD` is symmetric in its
  two contracted vertices);
* `kVec`, `kMom`: the integer vectors and momenta `K'_u`; **`elemMom_eq_kMom`**: the element
  momentum is `sgn · (K'_{u+1} - K'_u)` at both ends (integer vectors checked by kernel
  evaluation).
-/

@[expose] public section
open Complex

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.ChainProof.SetCLink
open QED.WickModel (Params)
open QED.ChainProof.SetCLink (mvReal)
open QED.TwoLoop.Bridge (extMomenta)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix class5LoopMatrix pvLines)

/-- The end of the element line used for the Ward identity. -/
def kWardD : Fin 12 → Fin 5 := ![4, 1, 1, 3, 1, 2, 4, 2, 2, 3, 4, 2]

/-- The other end of the element line. -/
def kOthD : Fin 12 → Fin 5 := ![0, 3, 4, 0, 4, 0, 0, 1, 4, 0, 0, 3]

/-- The sign of the element momentum at `kWardD i`. -/
def kSgnW : Fin 12 → ℤ := ![1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, -1]

/-- The sign of the element momentum at `kOthD i`. -/
def kSgnO : Fin 12 → ℤ := ![-1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, 1]

theorem kVert_bijective : ∀ i : Fin 12, Function.Bijective
    (![Fin.rev (skE i), kWardD i, kOthD i, Fin.rev (skR i), Fin.rev (skT i)] : Fin 5 → Fin 5) := by
  decide

/-- The photon labels of the longitudinal chain of `repD i s`. -/
noncomputable def kPermD (i : Fin 12) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective _ (kVert_bijective i)

theorem kPermD_apply (i : Fin 12) :
    kPermD i 0 = Fin.rev (skE i) ∧ kPermD i 1 = kWardD i ∧ kPermD i 2 = kOthD i ∧
      kPermD i 3 = Fin.rev (skR i) ∧ kPermD i 4 = Fin.rev (skT i) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ctEnds_eq : ∀ (i : Fin 12) (s : Fin 2), (ctEndA i s = kWardD i ∧ ctEndB i s = kOthD i) ∨
    (ctEndA i s = kOthD i ∧ ctEndB i s = kWardD i) := by
  decide

theorem kChainD_swap (c : Class5) (P : Params) (σ : Fin 8) (e a b c' d : Fin 5)
    (p p' : Fin 4 → ℝ) (μ α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kChainD c P σ e a b c' d p p' μ α β ℓ = kChainD c P σ e b a c' d p p' μ α β ℓ := by
  unfold kChainD
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **The chain of `repD i s` in the photon labels `kPermD i`.** -/
theorem kChainD_repD_eq (i : Fin 12) (s : Fin 2) (P : Params) (p p' : Fin 4 → ℝ)
    (μ α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kChainD (repBClass i) P (repBSlot i) (Fin.rev (skE i)) (ctEndA i s) (ctEndB i s)
        (Fin.rev (skR i)) (Fin.rev (skT i)) p p' μ α β ℓ =
      kChainD (repBClass i) P (repBSlot i) (kPermD i 0) (kPermD i 1) (kPermD i 2) (kPermD i 3)
        (kPermD i 4) p p' μ α β ℓ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := kPermD_apply i
  rw [h0, h1, h2, h3, h4]
  rcases ctEnds_eq i s with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb]
  exact kChainD_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ### The electron momenta at the vertices -/

/-- The integer vector (loop, `p`, `q = p' - p` coefficients) of `K'_u`. -/
def kVec (c : Class5) (u : Fin 6) : Fin 4 → ℤ :=
  if u = 0 then ![0, 0, 1, 0] else if u = 5 then ![0, 0, 1, 1]
  else classVecD c 1 0 (u - 1)

/-- The momentum `K'_u`: `p`, the four electron lines, `p'`. -/
noncomputable def kMom (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (u : Fin 6) :
    Fin 4 → ℝ :=
  mvReal ℓ p (p' - p) (kVec c u)

theorem chgD_one_zero (p q : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : chgD 1 0 p q ℓ = ℓ := by
  funext s μ
  fin_cases s <;> simp [chgD, Matrix.one_apply]

theorem lineMomentum_class_eq (c : Class5) (p p' : Fin 4 → ℝ) (j : Fin 6)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p') j ℓ =
      mvReal ℓ p (p' - p) (classVecD c 1 0 j) := by
  have h := lineMomentum_chgD c 1 0 p p' j ℓ
  rwa [chgD_one_zero] at h

theorem kMom_electron (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 4) :
    kMom c p p' ℓ j.succ.castSucc =
      lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p')
        (Fin.castLE (by omega) j) ℓ := by
  rw [lineMomentum_class_eq]
  unfold kMom kVec
  fin_cases j <;> rfl

theorem kMom_zero (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kMom c p p' ℓ 0 = p := by
  funext μ; simp [kMom, kVec, mvReal]

theorem kMom_five (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kMom c p p' ℓ 5 = p' := by
  funext μ; simp [kMom, kVec, mvReal]

theorem elemMom_eq_class (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemMom c σ p p' ℓ = mvReal ℓ p (p' - p) (classVecD c 1 0 (pvLines σ)) := by
  rw [← lineMomentum_class_eq]
  rfl

theorem kVec_ward : ∀ i : Fin 12,
    classVecD (repBClass i) 1 0 (pvLines (repBSlot i)) =
        kSgnW i • (kVec (repBClass i) (kWardD i).succ - kVec (repBClass i) (kWardD i).castSucc) ∧
      classVecD (repBClass i) 1 0 (pvLines (repBSlot i)) =
        kSgnO i • (kVec (repBClass i) (kOthD i).succ - kVec (repBClass i) (kOthD i).castSucc) := by
  decide +kernel

/-- **The element momentum at the two ends of the element line.** -/
theorem elemMom_eq_kMom (i : Fin 12) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemMom (repBClass i) (repBSlot i) p p' ℓ = ((kSgnW i : ℤ) : ℝ) •
        (kMom (repBClass i) p p' ℓ (kWardD i).succ -
          kMom (repBClass i) p p' ℓ (kWardD i).castSucc) ∧
      elemMom (repBClass i) (repBSlot i) p p' ℓ = ((kSgnO i : ℤ) : ℝ) •
        (kMom (repBClass i) p p' ℓ (kOthD i).succ -
          kMom (repBClass i) p p' ℓ (kOthD i).castSucc) := by
  obtain ⟨h1, h2⟩ := kVec_ward i
  unfold kMom
  rw [elemMom_eq_class]
  constructor
  · rw [h1, map_zsmul, map_sub, ← Int.cast_smul_eq_zsmul ℝ]
  · rw [h2, map_zsmul, map_sub, ← Int.cast_smul_eq_zsmul ℝ]

end QED.ChainProof.SetCMain

end
