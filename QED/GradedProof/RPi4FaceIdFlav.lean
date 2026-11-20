/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdInst
public import QED.GradedProof.RPi4FaceIdVDens
public import QED.GradedProof.RPi4DecRep

/-!
# (R-Π₄) step L6d3: the flavour sum of the three-flavour combinations

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. On a
Pauli–Villars closed flavour set the Pauli–Villars coefficients `triA(M_f)`, `triB(M_f)` are
affine in `M_f²`, so their flavour sums vanish and the regulator flavours `X`, `Y` drop out:

* **`faceId_sum_triF`**: `∑_f c_f faceIdTriF(M_f) = ∑_f c_f H(M_f)`;
* `faceId_sum_efi`: the flavour sum of energy-first integrals with remainders;
* `faceId_mass_sq_ne`: the masses `M_f < X < X + 1` have distinct squares.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The regulator flavours drop out of the flavour sum.** -/
theorem faceId_sum_triF (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (b : Fin 4 → Bool) (c : Fin 5 → ℝ) (ε : ℝ) (k : Fin 4 → ℝ) (N : ℝ → (Fin 4 → ℝ) → ℂ)
    (X Y : ℝ) (x : Fin 4 → ℝ) :
    ∑ f, (Φ.coeff f : ℂ) * faceIdTriF b c ε k N (Φ.mass f) X Y x =
      ∑ f, (Φ.coeff f : ℂ) * (N (Φ.mass f) x *
        ∏ l, faceIdG (b l) (faceIdV c ε k x l) ((Φ.mass f : ℂ) ^ 2)) := by
  have hA : ∑ f, (Φ.coeff f : ℂ) * ((triA (Φ.mass f) X Y : ℝ) : ℂ) = 0 := by
    rw [← dec_sum_rep_affine Φ rep hrep hPV₁ hPV₂
      (fun _ => (Y : ℂ) ^ 2 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2))
      (fun _ => -1 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2))]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [triA]
    push_cast
    ring
  have hB : ∑ f, (Φ.coeff f : ℂ) * ((triB (Φ.mass f) X Y : ℝ) : ℂ) = 0 := by
    rw [← dec_sum_rep_affine Φ rep hrep hPV₁ hPV₂
      (fun _ => -(X : ℂ) ^ 2 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2))
      (fun _ => 1 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2))]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [triB]
    push_cast
    ring
  have e : ∀ f, (Φ.coeff f : ℂ) * faceIdTriF b c ε k N (Φ.mass f) X Y x =
      (Φ.coeff f : ℂ) * (N (Φ.mass f) x *
        ∏ l, faceIdG (b l) (faceIdV c ε k x l) ((Φ.mass f : ℂ) ^ 2)) +
      (Φ.coeff f : ℂ) * ((triA (Φ.mass f) X Y : ℝ) : ℂ) *
        (N X x * ∏ l, faceIdG (b l) (faceIdV c ε k x l) ((X : ℂ) ^ 2)) +
      (Φ.coeff f : ℂ) * ((triB (Φ.mass f) X Y : ℝ) : ℂ) *
        (N Y x * ∏ l, faceIdG (b l) (faceIdV c ε k x l) ((Y : ℂ) ^ 2)) := fun f => by
    simp only [faceIdTriF]
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hA, hB, zero_mul, add_zero]

omit [DecidableEq F] in
/-- **The flavour sum of energy-first integrals with remainders.** -/
theorem faceId_sum_efi (G H : ℝ → (Fin 4 → ℝ) → ℂ) (R : ℝ → ℂ) (T : ℝ → ℂ)
    (hT : ∀ f, T (Φ.mass f) = QED.OneLoop.energyFirstIntegral (G (Φ.mass f)) + R (Φ.mass f))
    (hG : ∀ f, EF (G (Φ.mass f)))
    (hGH : ∀ x, ∑ f, (Φ.coeff f : ℂ) * G (Φ.mass f) x = ∑ f, (Φ.coeff f : ℂ) * H (Φ.mass f) x) :
    ∑ f, (Φ.coeff f : ℂ) * T (Φ.mass f) =
      QED.OneLoop.energyFirstIntegral (fun x => ∑ f, (Φ.coeff f : ℂ) * H (Φ.mass f) x) +
        ∑ f, (Φ.coeff f : ℂ) * R (Φ.mass f) ∧
    EF fun x => ∑ f, (Φ.coeff f : ℂ) * H (Φ.mass f) x := by
  have hE : ∀ f ∈ Finset.univ, EF fun x => (Φ.coeff f : ℂ) * G (Φ.mass f) x :=
    fun f _ => (hG f).const_mul _
  refine ⟨?_, (EF.sum _ hE).congr hGH⟩
  simp only [hT, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [← funext hGH, faceId_efi_sum _ hE]
  exact Finset.sum_congr rfl fun f _ =>
    (QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul _ _).symm

omit [DecidableEq F] in
/-- The masses `M_f < X < X + 1` have distinct squares. -/
theorem faceId_mass_sq_ne {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (f : F) :
    (Φ.mass f : ℂ) ^ 2 - (blockX Φ m₀ : ℂ) ^ 2 ≠ 0 ∧
      (Φ.mass f : ℂ) ^ 2 - ((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 ≠ 0 ∧
      (blockX Φ m₀ : ℂ) ^ 2 - ((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 ≠ 0 := by
  have hf : Φ.mass f ≤ ∑ g, Φ.mass g :=
    Finset.single_le_sum (fun g _ => hm₀.le.trans (hmass g)) (Finset.mem_univ f)
  have h0 : 0 < Φ.mass f := hm₀.trans_le (hmass f)
  have hX : Φ.mass f < blockX Φ m₀ := by simp only [blockX]; linarith
  have n : ∀ a b : ℝ, 0 < a → a < b → (a : ℂ) ^ 2 - (b : ℂ) ^ 2 ≠ 0 := fun a b ha hab => by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_sub, ofReal_ne_zero]
    nlinarith
  exact ⟨n _ _ h0 hX, n _ _ h0 (by linarith), n _ _ (h0.trans hX) (by linarith)⟩

end QED.GradedProof.RPi4

end
