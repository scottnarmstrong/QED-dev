/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0SepCrit
public import QED.GradedProof.X0ClosedEnum

/-!
# (X₀): the decidable test for the non-separated contractions with a closed loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. Lines `i` of an integrand with two loop momenta carry integer rows
`a i ∈ ℤ²`, `n i` propagator denominators and `d i` affine numerator factors.
`LinesCrit a n d` is the numerator-aware no-subdivergence criterion of the two-loop theorems
with these multiplicities, together with their size conditions; `PadCrit` also allows one
extra denominator (with a numerator of degree two cancelling it) on one line.

For a contraction `C` with the closed fermion loop `zOf C`, an index term of the amplitude
has `p` same-block entries on the loop and an affine entry on each of the other loop lines
(`E'`); the mass expansion of the flavour sum (`jointEnergyFirstIntegrable_blockSumGen`) adds
extra lines parallel to the loop lines. `NsCrit C` asks `PadCrit` for every such pattern.
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel

/-! ### Multiplicity criterion -/

/-- The determinant of two integer rows. -/
def rdet (x y : Fin 2 → ℤ) : ℤ :=
  x 0 * y 1 - x 1 * y 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each numerator factor has its own denominator. -/
def DegOK (n d : ι → ℕ) : Prop :=
  ∀ i, d i ≤ n i

instance (n d : ι → ℕ) : Decidable (DegOK n d) := by
  unfold DegOK; infer_instance

/-- The numerator-aware criterion with multiplicities. -/
def CountOK (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) : Prop :=
  ∀ i, 0 < n i → 4 + ∑ e ∈ Finset.univ.filter (fun e => rdet (a i) (a e) ≠ 0), d e <
    2 * ∑ j ∈ Finset.univ.filter (fun j => rdet (a i) (a j) ≠ 0), n j

instance (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) : Decidable (CountOK a n d) := by
  unfold CountOK; infer_instance

/-- The size conditions of the refined and cubic two-loop theorems. -/
def SizeOK (n d : ι → ℕ) : Prop :=
  (8 ≤ ∑ i, n i ∧ ∑ i, d i ≤ 4) ∨ (7 ≤ ∑ i, n i ∧ ∑ i, d i ≤ 3)

instance (n d : ι → ℕ) : Decidable (SizeOK n d) := by
  unfold SizeOK; infer_instance

/-- **The two-loop line criterion.** -/
def LinesCrit (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) : Prop :=
  DegOK n d ∧ CountOK a n d ∧ SizeOK n d

instance (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) : Decidable (LinesCrit a n d) := by
  unfold LinesCrit; infer_instance

/-- `n` with `c` more on the line `e`. -/
def bump (n : ι → ℕ) (e : ι) (c : ℕ) : ι → ℕ :=
  fun i => n i + if i = e then c else 0

/-- The criterion after padding one line. -/
def PadAt (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) (e : ι) : Prop :=
  d e + 1 ≤ n e ∧ LinesCrit a (bump n e 1) (bump d e 2)

instance (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) (e : ι) : Decidable (PadAt a n d e) := by
  unfold PadAt; infer_instance

/-- **The criterion, possibly after padding one line.** -/
def PadCrit (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) : Prop :=
  LinesCrit a n d ∨ ∃ e, PadAt a n d e

instance (a : ι → Fin 2 → ℤ) (n d : ι → ℕ) : Decidable (PadCrit a n d) := by
  unfold PadCrit; infer_instance

/-! ### The data of a contraction -/

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The integer row of a line. -/
def rowOf (C : Contraction 1 nA κ) (l : Line C) : Fin 2 → ℤ :=
  ![loopCoeff C l 0, loopCoeff C l 1]

/-- The line is a fermion line of the closed loop `zOf C`. -/
def isZL (C : Contraction 1 nA κ) : Line C → Bool
  | .inl f => decide (zOf C f.1)
  | .inr _ => false

/-- The line carries no loop momentum. -/
def isTree (C : Contraction 1 nA κ) (l : Line C) : Bool :=
  decide (loopCoeff C l 0 = 0 ∧ loopCoeff C l 1 = 0)

/-- The lines of the closed loop. -/
def zSet (C : Contraction 1 nA κ) : Finset (Line C) :=
  Finset.univ.filter fun l => isZL C l = true

/-- The denominators of a line before the mass expansion: one on a loop line or another
fermion line, two (Pauli–Villars) on a photon line, none on a line carrying no loop
momentum. -/
def baseN (C : Contraction 1 nA κ) : Line C → ℕ
  | .inl f => if isZL C (.inl f) = true then 1 else if isTree C (.inl f) = true then 0 else 1
  | .inr g => if isTree C (.inr g) = true then 0 else 2

/-- The affine numerator factors of a line: one on the loop lines of `E'` and on the other
fermion lines carrying loop momentum, none on photon lines. -/
def baseD (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Line C → ℕ
  | .inl f => if isZL C (.inl f) = true then (if (Sum.inl f : Line C) ∈ E' then 1 else 0)
      else if isTree C (.inl f) = true then 0 else 1
  | .inr _ => 0

/-- Extra denominators on the loop lines of `S`. -/
def addSet {C : Contraction 1 nA κ} (n : Line C → ℕ) (S : Finset (Line C)) : Line C → ℕ :=
  fun i => n i + if i ∈ S then 1 else 0

/-- The terms with two extra lines parallel to one loop line. -/
def TwoOK (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Prop :=
  ∀ l ∈ zSet C, PadCrit (rowOf C) (bump (baseN C) l 2) (baseD C E')

instance (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Decidable (TwoOK C E') := by
  unfold TwoOK; infer_instance

/-- The terms with one extra line parallel to each loop line of `S`, `|S| ≥ 2`. -/
def SetOK (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Prop :=
  ∀ S ∈ (zSet C).powerset, 2 ≤ S.card → PadCrit (rowOf C) (addSet (baseN C) S) (baseD C E')

instance (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Decidable (SetOK C E') := by
  unfold SetOK; infer_instance

/-- The patterns with `p = 2` or `p = 0` same-block loop entries share the terms with two
or more extra lines. -/
def MultiOK (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Prop :=
  TwoOK C E' ∧ SetOK C E'

instance (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Decidable (MultiOK C E') := by
  unfold MultiOK; infer_instance

/-- The pattern with `p = 2` has also the terms with one extra massless line. -/
def OneOK (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Prop :=
  ∀ l ∈ zSet C, PadCrit (rowOf C) (bump (baseN C) l 1) (baseD C E')

instance (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Decidable (OneOK C E') := by
  unfold OneOK; infer_instance

/-- The criterion for one pattern: the loop entries off `E'` are the `p` same-block ones. -/
def PatOK (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Prop :=
  ((zSet C).card - E'.card = 4 → PadCrit (rowOf C) (baseN C) (baseD C E')) ∧
    ((zSet C).card - E'.card = 2 → OneOK C E' ∧ MultiOK C E') ∧
    ((zSet C).card - E'.card = 0 → MultiOK C E')

instance (C : Contraction 1 nA κ) (E' : Finset (Line C)) : Decidable (PatOK C E') := by
  unfold PatOK; infer_instance

/-- All patterns. -/
def AllPatOK (C : Contraction 1 nA κ) : Prop :=
  ∀ E' ∈ (zSet C).powerset, PatOK C E'

instance (C : Contraction 1 nA κ) : Decidable (AllPatOK C) := by
  unfold AllPatOK; infer_instance

/-- **The non-separated closed-loop test.** -/
def NsCrit (C : Contraction 1 nA κ) : Prop :=
  ShapeOK C (zOf C) ∧ Fintype.card (ZLine C (zOf C)) ≤ 4 ∧ AllPatOK C

instance (C : Contraction 1 nA κ) : Decidable (NsCrit C) := by
  unfold NsCrit; infer_instance

end QED.GradedProof.X0

end
