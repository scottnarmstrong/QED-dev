/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.SelfEnergyExistsUnique

/-!
# Families with a covariant self-energy limit

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, steps L0 and L4.

* `HasSEForm T G`: a family `G ε p α β` (`ε > 0`, `p` a four-vector) has, for every `p` with
  `p² > -T²`, the limit `(a(p²) p̸ + b(p²)) α β` as `ε → 0⁺`, for some functions `a, b` of `p²`.
  The property is closed under sums, constant multiples and eventual equality
  (`HasSEForm.add`, `HasSEForm.const_mul`, `HasSEForm.sum`, `HasSEForm.congr`), and holds for
  `ε`-independent covariant families (`HasSEForm.const`).
* `existsUnique_of_hasSEForm`: such a family has a unique pair `(A, B)` of functions of `s` on the
  region with limit `A p̸ + B M` (`M ≠ 0`), the form of the second clause of (G-Σ₂). Uniqueness
  is (Z₁)'s, at the test momenta `QED.WickModel.selfEnergyTestMomentum`.
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.SE2

/-- The covariant matrix `a p̸ + b`. -/
noncomputable def seMat (a b : ℂ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  a • Dirac.slash p + b • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- **A family with a covariant limit below `-T²`.** -/
def HasSEForm (T : ℝ) (G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∃ a b : ℝ → ℂ, ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
    Tendsto (fun ε => G ε p α β) (𝓝[>] 0)
      (𝓝 (seMat (a (Minkowski.dot p p)) (b (Minkowski.dot p p)) p α β))

namespace HasSEForm

variable {T : ℝ} {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem seMat_add (a b a' b' : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    seMat a b p α β + seMat a' b' p α β = seMat (a + a') (b + b') p α β := by
  simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem seMat_mul (c a b : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    c * seMat a b p α β = seMat (c * a) (c * b) p α β := by
  simp only [seMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem add (hG : HasSEForm T G) (hH : HasSEForm T H) :
    HasSEForm T fun ε p α β => G ε p α β + H ε p α β := by
  obtain ⟨a, b, h⟩ := hG
  obtain ⟨a', b', h'⟩ := hH
  refine ⟨a + a', b + b', fun p hp α β => ?_⟩
  have := (h p hp α β).add (h' p hp α β)
  rwa [seMat_add] at this

theorem const_mul (c : ℂ) (hG : HasSEForm T G) : HasSEForm T fun ε p α β => c * G ε p α β := by
  obtain ⟨a, b, h⟩ := hG
  refine ⟨fun s => c * a s, fun s => c * b s, fun p hp α β => ?_⟩
  have := (h p hp α β).const_mul c
  rwa [seMat_mul] at this

theorem zero : HasSEForm T fun _ _ _ _ => 0 :=
  ⟨0, 0, fun p _ α β => by simp [seMat]⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, HasSEForm T (G i)) : HasSEForm T fun ε p α β => ∑ i ∈ s, G i ε p α β := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HasSEForm T _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Eventual equality as `ε → 0⁺`, at every momentum of the region. -/
theorem congr (hG : HasSEForm T G)
    (h : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p α β = H ε p α β) : HasSEForm T H := by
  obtain ⟨a, b, hG⟩ := hG
  exact ⟨a, b, fun p hp α β => (hG p hp α β).congr' (h p hp α β)⟩

/-- An `ε`-independent covariant family. -/
theorem const (a b : ℂ) : HasSEForm T fun _ p α β => seMat a b p α β :=
  ⟨fun _ => a, fun _ => b, fun _ _ _ _ => tendsto_const_nhds⟩

end HasSEForm

/-- **The second clause of (G-Σ₂) from a covariant limit.** -/
theorem existsUnique_of_hasSEForm {M T : ℝ} (hM : M ≠ 0)
    {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : HasSEForm T G) :
    ∃! AB : {s : ℝ // -T ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ) (hp : -T ^ 2 < Minkowski.dot p p) (α β : Fin 4),
        Tendsto (fun ε : ℝ => G ε p α β) (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
  obtain ⟨a, b, hG⟩ := h
  set AB₀ : {s : ℝ // -T ^ 2 < s} → ℂ × ℂ := fun s => (a s.1, b s.1 / M)
  have hM' : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM
  have hex : ∀ (p : Fin 4 → ℝ) (hp : -T ^ 2 < Minkowski.dot p p) (α β : Fin 4),
      Tendsto (fun ε : ℝ => G ε p α β) (𝓝[>] 0)
        (𝓝 (((AB₀ ⟨_, hp⟩).1 • Dirac.slash p
          + ((AB₀ ⟨_, hp⟩).2 * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
    intro p hp α β
    have e : (AB₀ ⟨_, hp⟩).2 * M = b (Minkowski.dot p p) := by
      simp only [AB₀]
      field_simp
    rw [e]
    exact hG p hp α β
  refine ⟨AB₀, hex, fun AB hAB => ?_⟩
  funext ⟨s, hs⟩
  have hdot := QED.WickModel.dot_selfEnergyTestMomentum s
  have hp : -T ^ 2 < Minkowski.dot (QED.WickModel.selfEnergyTestMomentum s)
      (QED.WickModel.selfEnergyTestMomentum s) := by
    rw [hdot]
    exact hs
  have key := fun α β => tendsto_nhds_unique (hAB _ hp α β) (hex _ hp α β)
  have hsub : (⟨_, hp⟩ : {s : ℝ // -T ^ 2 < s}) = ⟨s, hs⟩ := Subtype.ext hdot
  rw [hsub] at key
  exact QED.WickModel.eq_of_smul_slash_add_apply hM s key

end QED.GradedProof.SE2

end
