/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Reduce

/-!
# One closed loop: the flavour sum and the Pauli–Villars blocks

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2. Every class
representative of `QED/GradedProof/VP2Classes.lean` has no external fermion and one closed
fermion loop through all its fermion vertices. For such a contraction:

* `regulatedAmplitude_of_oneLoop`: the graded regulated amplitude (G₄) is
  `∑_f c_f A_f`, `A_f` the amplitude (G₃) at the constant flavouring `f`.
* `sum_block_affine_eq_zero`: under the block hypotheses of (G-Π₂) (idempotent `rep`, two
  Pauli–Villars conditions on each class), `∑_f c_f (α + β M_f²) H(rep f) = 0` for every `H`.
* `sum_block_eq_sum_triple`: hence, for two masses `X ≠ Y`, the block-weighted flavour sum
  `∑_f c_f G(rep f, M_f)` equals `∑_f c_f T_f`, where
  `T_f = G(rep f, M_f) + a_f G(rep f, X) + b_f G(rep f, Y)` is a three-flavour Pauli–Villars
  combination at the masses `(M_f, X, Y)` (`1 + a_f + b_f = 0`,
  `M_f² + a_f X² + b_f Y² = 0`). This is how each class obligation is reduced to three-flavour
  sets of fixed counterterm data.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.VP2

open QED.Graded
open QED.WickModel (Params Contraction ClosedLoop)

/-! ### One closed loop -/

section OneLoop

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} (Φ : Lepton.Flavors F)
  (C : Contraction 0 nA κ)

/-- All fermion fields of `C` lie on one cycle of the fermion pairing. -/
def OneLoop : Prop :=
  ∀ t s : Wick.FermionVertex κ, C.1.1.SameCycle (.inr t) (.inr s)

variable {C}

theorem preserves_const (f : F) : Preserves Φ C (fun _ => f) := by
  intro a
  rcases a with i | t
  · exact i.elim0
  · rcases h : C.1.1 (.inr t) with i | s
    · exact i.elim0
    · rfl

theorem preserves_iff_const (hC : OneLoop C) (t₀ : Wick.FermionVertex κ) (φ : Flavoring F κ) :
    Preserves Φ C φ ↔ φ = fun _ => φ t₀ := by
  refine ⟨fun hφ => funext fun t => ?_, fun h => h ▸ preserves_const Φ _⟩
  have := fermionFlavor_eq_of_sameCycle Φ hφ (hC t t₀)
  simpa [fermionFlavor] using this

/-- The loop through `t₀`. -/
def theLoop (t₀ : Wick.FermionVertex κ) : ClosedLoop C :=
  ⟨Quotient.mk _ (.inr t₀), fun i => i.elim0⟩

theorem eq_theLoop (hC : OneLoop C) (t₀ : Wick.FermionVertex κ) (q : ClosedLoop C) :
    q = theLoop t₀ := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases x with i | t
  · exact i.elim0
  · exact Quotient.sound (hC t t₀)

open scoped Classical in
/-- The regulator weight of the constant flavouring `f` is `c_f`. -/
theorem loopWeight_const (hC : OneLoop C) (t₀ : Wick.FermionVertex κ) (f : F) :
    loopWeight Φ C (fun _ => f) = Φ.coeff f := by
  rw [loopWeight, Fintype.prod_eq_single (theLoop t₀) fun q hq => absurd (eq_theLoop hC t₀ q) hq]
  rcases h : (theLoop (C := C) t₀).1.out with i | t
  · exact i.elim0
  · simp only [fermionFlavor]

/-- **The flavour sum of a one-loop contraction.** -/
theorem regulatedAmplitude_of_oneLoop (P : Params) [Fintype F] [DecidableEq F]
    (D : Counterterms F) (hC : OneLoop C) (t₀ : Wick.FermionVertex κ) (g : Grading κ)
    (pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 0 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) * contractionAmplitude P Φ D C (fun _ => f) g pIn kIn k αOut βIn μ := by
  classical
  unfold regulatedAmplitude
  refine Finset.sum_nbij' (fun φ => φ t₀) (fun f _ => f) (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_const Φ f⟩)
    (fun φ hφ => ((preserves_iff_const Φ hC t₀ φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => rfl) (fun φ hφ => ?_)
  have h := (preserves_iff_const Φ hC t₀ φ).mp (Finset.mem_filter.mp hφ).2
  conv_lhs => rw [h]
  rw [loopWeight_const Φ hC t₀]

end OneLoop

/-! ### Pauli–Villars blocks -/

section Block

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The block conditions annihilate affine functions of `M_f²` weighted by block data.** -/
theorem sum_block_affine_eq_zero (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (α β : ℂ) (H : F → ℂ) :
    ∑ f, (Φ.coeff f : ℂ) * ((α + β * (Φ.mass f : ℂ) ^ 2) * H (rep f)) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := rep) (t := Finset.univ.image rep)
    (fun f _ => Finset.mem_image_of_mem rep (Finset.mem_univ f))]
  refine Finset.sum_eq_zero fun b hb => ?_
  obtain ⟨f₀, -, rfl⟩ := Finset.mem_image.mp hb
  have hb' : rep (rep f₀) = rep f₀ := hrep f₀
  have e1 := hPV₁ _ hb'
  have e2 := hPV₂ _ hb'
  have e1' : ∑ f ∈ Finset.univ.filter (fun f => rep f = rep f₀), (Φ.coeff f : ℂ) = 0 := by
    exact_mod_cast e1
  have e2' : ∑ f ∈ Finset.univ.filter (fun f => rep f = rep f₀),
      (Φ.coeff f : ℂ) * (Φ.mass f : ℂ) ^ 2 = 0 := by exact_mod_cast e2
  calc ∑ f ∈ Finset.univ.filter (fun f => rep f = rep f₀),
        (Φ.coeff f : ℂ) * ((α + β * (Φ.mass f : ℂ) ^ 2) * H (rep f))
      = ∑ f ∈ Finset.univ.filter (fun f => rep f = rep f₀),
          (α * H (rep f₀) * (Φ.coeff f : ℂ) +
            β * H (rep f₀) * ((Φ.coeff f : ℂ) * (Φ.mass f : ℂ) ^ 2)) :=
        Finset.sum_congr rfl fun f hf => by
          rw [(Finset.mem_filter.mp hf).2]
          ring
    _ = α * H (rep f₀) * 0 + β * H (rep f₀) * 0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1', e2']
    _ = 0 := by ring

/-- The coefficient of the mass `X` in the three-flavour set `(M, X, Y)`. -/
noncomputable def triA (M X Y : ℝ) : ℝ := (Y ^ 2 - M ^ 2) / (X ^ 2 - Y ^ 2)

/-- The coefficient of the mass `Y` in the three-flavour set `(M, X, Y)`. -/
noncomputable def triB (M X Y : ℝ) : ℝ := (M ^ 2 - X ^ 2) / (X ^ 2 - Y ^ 2)

theorem triA_triB_pv₁ (M X Y : ℝ) (h : X ^ 2 - Y ^ 2 ≠ 0) : 1 + triA M X Y + triB M X Y = 0 := by
  unfold triA triB
  field_simp
  ring

theorem triA_triB_pv₂ (M X Y : ℝ) (h : X ^ 2 - Y ^ 2 ≠ 0) :
    M ^ 2 + triA M X Y * X ^ 2 + triB M X Y * Y ^ 2 = 0 := by
  unfold triA triB
  field_simp
  ring

/-- **The block-weighted flavour sum as a sum of three-flavour Pauli–Villars combinations.** -/
theorem sum_block_eq_sum_triple (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (X Y : ℝ) (G : F → ℝ → ℂ) :
    ∑ f, (Φ.coeff f : ℂ) * G (rep f) (Φ.mass f) =
      ∑ f, (Φ.coeff f : ℂ) * (G (rep f) (Φ.mass f) +
        (triA (Φ.mass f) X Y : ℂ) * G (rep f) X + (triB (Φ.mass f) X Y : ℂ) * G (rep f) Y) := by
  have hA := sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂
    ((Y : ℂ) ^ 2 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2)) (-1 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2))
    (fun b => G b X)
  have hB := sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂
    (-(X : ℂ) ^ 2 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2)) (1 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2))
    (fun b => G b Y)
  have hA' : ∀ f, (triA (Φ.mass f) X Y : ℂ) =
      (Y : ℂ) ^ 2 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) +
        -1 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) * (Φ.mass f : ℂ) ^ 2 := fun f => by
    unfold triA
    push_cast
    ring
  have hB' : ∀ f, (triB (Φ.mass f) X Y : ℂ) =
      -(X : ℂ) ^ 2 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) +
        1 / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) * (Φ.mass f : ℂ) ^ 2 := fun f => by
    unfold triB
    push_cast
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [hA', hB', ← mul_assoc] at hA hB ⊢
  simp only [mul_assoc] at hA hB ⊢
  rw [hA, hB, add_zero, add_zero]

end Block

end QED.GradedProof.VP2

end
