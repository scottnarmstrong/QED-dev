/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# (X₁) piece D: limits `ε → 0⁺` near a point, continuous at the point

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. For a family `F ε y` (prescription `ε`, external data `y`),
`OffLim F y₀` says: there is `G` with `F ε y → G y` as `ε → 0⁺` for every `y` near `y₀`, and
`G` is continuous at `y₀`. This is closed under sums, constant multiples, finite sums, eventual
equality in `ε > 0`, factors converging as `ε → 0⁺`, and pull-back along maps continuous at
the point (`OffLim.comp`).
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.X1D

variable {Y : Type*} [TopologicalSpace Y]

/-- `F ε y` has an `ε → 0⁺` limit `G y` at every `y` near `y₀`, and `G` is continuous at `y₀`. -/
def OffLim (F : ℝ → Y → ℂ) (y₀ : Y) : Prop :=
  ∃ G : Y → ℂ, (∀ᶠ y in 𝓝 y₀, Tendsto (fun ε => F ε y) (𝓝[>] 0) (𝓝 (G y))) ∧ ContinuousAt G y₀

namespace OffLim

variable {F H : ℝ → Y → ℂ} {y₀ : Y}

theorem add (hF : OffLim F y₀) (hH : OffLim H y₀) : OffLim (fun ε y => F ε y + H ε y) y₀ := by
  obtain ⟨G, hG, hGc⟩ := hF
  obtain ⟨K, hK, hKc⟩ := hH
  exact ⟨fun y => G y + K y, by filter_upwards [hG, hK] with y h1 h2 using h1.add h2,
    hGc.add hKc⟩

theorem const_mul (a : ℂ) (hF : OffLim F y₀) : OffLim (fun ε y => a * F ε y) y₀ := by
  obtain ⟨G, hG, hGc⟩ := hF
  exact ⟨fun y => a * G y, by filter_upwards [hG] with y h using h.const_mul a,
    continuousAt_const.mul hGc⟩

theorem zero : OffLim (fun _ _ => 0) y₀ :=
  ⟨fun _ => 0, Eventually.of_forall fun _ => tendsto_const_nhds, continuousAt_const⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → Y → ℂ} (h : ∀ i ∈ s, OffLim (F i) y₀) :
    OffLim (fun ε y => ∑ i ∈ s, F i ε y) y₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : OffLim (fun _ _ => (0 : ℂ)) y₀)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Eventual equality for `ε > 0` near `0`, at every `y`. -/
theorem congr (hF : OffLim F y₀) (he : ∀ y, ∀ ε, 0 < ε → F ε y = H ε y) : OffLim H y₀ := by
  obtain ⟨G, hG, hGc⟩ := hF
  refine ⟨G, ?_, hGc⟩
  filter_upwards [hG] with y h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact he y ε hε

/-- Eventual equality for `ε → 0⁺`, at every `y`. -/
theorem congr' (hF : OffLim F y₀) (he : ∀ y, ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε y = H ε y) :
    OffLim H y₀ := by
  obtain ⟨G, hG, hGc⟩ := hF
  exact ⟨G, by filter_upwards [hG] with y h using h.congr' (he y), hGc⟩

/-- Multiplication by a factor `b ε → b₀` independent of `y`. -/
theorem mul_left {b : ℝ → ℂ} {b₀ : ℂ} (hb : Tendsto b (𝓝[>] 0) (𝓝 b₀)) (hF : OffLim F y₀) :
    OffLim (fun ε y => b ε * F ε y) y₀ := by
  obtain ⟨G, hG, hGc⟩ := hF
  exact ⟨fun y => b₀ * G y, by filter_upwards [hG] with y h using hb.mul h,
    continuousAt_const.mul hGc⟩

/-- Pull-back along a map continuous at the point. -/
theorem comp {Z : Type*} [TopologicalSpace Z] {f : Z → Y} {z₀ : Z} (hF : OffLim F (f z₀))
    (hf : ContinuousAt f z₀) : OffLim (fun ε z => F ε (f z)) z₀ := by
  obtain ⟨G, hG, hGc⟩ := hF
  exact ⟨G ∘ f, hf.eventually hG, hGc.comp hf⟩

end OffLim

end QED.GradedProof.X1D

end
