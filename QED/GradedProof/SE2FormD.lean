/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamCont
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Families whose limit is differentiable along lines

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 3.

* `HasSEFormD T G`: along every line `t ↦ t w`, the family `G ε (t w) α β` has a limit `W(t) α β`
  as `ε → 0⁺` at every `t` with `(t w)² > -T²`, and `W(·) α β` is differentiable there. The
  property is closed under sums, constant multiples and eventual equality (`HasSEFormD.add`,
  `HasSEFormD.const_mul`, `HasSEFormD.sum`, `HasSEFormD.congr`), and holds for `ε`-independent
  covariant families (`HasSEFormD.const`) and for covariant limits `a(p²) p̸ + b(p²)` with `a`, `b`
  differentiable on the region (`HasSEFormD.of_seMat`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.SE2

/-- **A family whose limit below `-T²` is differentiable along every line.** -/
def HasSEFormD (T : ℝ) (G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ w : Fin 4 → ℝ, ∃ W : ℝ → Fin 4 → Fin 4 → ℂ, ∀ t : ℝ,
    -T ^ 2 < Minkowski.dot (t • w) (t • w) → ∀ α β : Fin 4,
      Tendsto (fun ε => G ε (t • w) α β) (𝓝[>] 0) (𝓝 (W t α β)) ∧
        DifferentiableAt ℝ (fun t => W t α β) t

theorem seMat_smul_apply (a b : ℂ) (t : ℝ) (w : Fin 4 → ℝ) (α β : Fin 4) :
    seMat a b (t • w) α β = a * ((t : ℂ) * Dirac.slash w α β) +
      b * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β := by
  simp only [seMat, Dirac.slash_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

namespace HasSEFormD

variable {T : ℝ} {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hG : HasSEFormD T G) (hH : HasSEFormD T H) :
    HasSEFormD T fun ε p α β => G ε p α β + H ε p α β := fun w => by
  obtain ⟨W, h⟩ := hG w
  obtain ⟨W', h'⟩ := hH w
  refine ⟨fun t α β => W t α β + W' t α β, fun t ht α β => ?_⟩
  exact ⟨((h t ht α β).1.add (h' t ht α β).1), (h t ht α β).2.add (h' t ht α β).2⟩

theorem const_mul (c : ℂ) (hG : HasSEFormD T G) :
    HasSEFormD T fun ε p α β => c * G ε p α β := fun w => by
  obtain ⟨W, h⟩ := hG w
  exact ⟨fun t α β => c * W t α β, fun t ht α β =>
    ⟨(h t ht α β).1.const_mul c, (h t ht α β).2.const_mul c⟩⟩

theorem zero : HasSEFormD T fun _ _ _ _ => 0 := fun _ =>
  ⟨fun _ _ _ => 0, fun _ _ _ _ => ⟨tendsto_const_nhds, differentiableAt_const _⟩⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, HasSEFormD T (G i)) : HasSEFormD T fun ε p α β => ∑ i ∈ s, G i ε p α β := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HasSEFormD T _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Eventual equality as `ε → 0⁺`, at every momentum of the region. -/
theorem congr (hG : HasSEFormD T G)
    (h : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p α β = H ε p α β) : HasSEFormD T H := fun w => by
  obtain ⟨W, hW⟩ := hG w
  exact ⟨W, fun t ht α β => ⟨(hW t ht α β).1.congr' (h _ ht α β), (hW t ht α β).2⟩⟩

/-- An `ε`-independent covariant family. -/
theorem const (a b : ℂ) : HasSEFormD T fun _ p α β => seMat a b p α β := fun w => by
  refine ⟨fun t α β => seMat a b (t • w) α β, fun t _ α β => ⟨tendsto_const_nhds, ?_⟩⟩
  simp only [seMat_smul_apply]
  fun_prop

/-- **A covariant limit with coefficients differentiable on the region.** -/
theorem of_seMat (a b : ℝ → ℂ) (ha : ∀ s, -T ^ 2 < s → DifferentiableAt ℝ a s)
    (hb : ∀ s, -T ^ 2 < s → DifferentiableAt ℝ b s)
    (h : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε => G ε p α β) (𝓝[>] 0)
        (𝓝 (seMat (a (Minkowski.dot p p)) (b (Minkowski.dot p p)) p α β))) :
    HasSEFormD T G := fun w => by
  refine ⟨fun t α β => seMat (a (t * t * Minkowski.dot w w)) (b (t * t * Minkowski.dot w w))
    (t • w) α β, fun t ht α β => ⟨?_, ?_⟩⟩
  · have := h _ ht α β
    rwa [dot_smul_smul] at this
  · rw [dot_smul_smul] at ht
    have hs : DifferentiableAt ℝ (fun t : ℝ => t * t * Minkowski.dot w w) t := by fun_prop
    have hA := (ha _ ht).comp t hs
    have hB := (hb _ ht).comp t hs
    simp only [seMat_smul_apply]
    exact (hA.mul ((Complex.ofRealCLM.differentiableAt.comp t differentiableAt_id).mul_const
      _)).add (hB.mul_const _)

end HasSEFormD

end QED.GradedProof.SE2

end
