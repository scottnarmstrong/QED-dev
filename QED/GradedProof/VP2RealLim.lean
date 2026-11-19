/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealParam
public import QED.GradedProof.VP2Piece

/-!
# Limits with a conjugation phase, and the phase of vacuum-polarization pieces

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `VPReal`.

* `HasConjLim T d G`: at every `k` with `k² > -T²` and every pair of indices, the family
  `G ε k μ ν` converges as `ε → 0⁺` to some `w` with `w̄ = d w`. Stable under sums, real multiples,
  multiples by constants with a phase, and eventual equality.
* `VPPiece.conj_W`: if the numerator of a vacuum-polarization piece satisfies `N̄ = d N` at real
  loop momenta, so does its limit tensor (the parametric value at `ε = 0` commutes with conjugating
  the numerator, `QED.GradedProof.SE2Real.pv_conj_of_eval`).
* `VPPiece.hasConjLim`: a multiple `h(ε)` (with real limit) of the joint integrals of such a piece
  has a limit with phase `d`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2Real

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.GradedProof.SE2 QED.GradedProof.VP2 QED.GradedProof.SE2Real

/-- **A limit with conjugation phase `d`** on the region `k² > -T²`. -/
def HasConjLim (T : ℝ) (d : ℂ) (G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4, ∃ w : ℂ,
    Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 w) ∧ starRingEnd ℂ w = d * w

namespace HasConjLim

variable {T : ℝ} {d : ℂ} {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hG : HasConjLim T d G) (hH : HasConjLim T d H) :
    HasConjLim T d fun ε k μ ν => G ε k μ ν + H ε k μ ν := fun k hk μ ν => by
  obtain ⟨w, hw, hc⟩ := hG k hk μ ν
  obtain ⟨w', hw', hc'⟩ := hH k hk μ ν
  exact ⟨w + w', hw.add hw', by rw [map_add, hc, hc', mul_add]⟩

theorem zero : HasConjLim T d fun _ _ _ _ => 0 := fun _ _ _ _ =>
  ⟨0, tendsto_const_nhds, by rw [map_zero, mul_zero]⟩

/-- Multiplication by a constant with phase `e`. -/
theorem const_mul_conj (c e : ℂ) (hc : starRingEnd ℂ c = e * c) (hG : HasConjLim T d G) :
    HasConjLim T (e * d) fun ε k μ ν => c * G ε k μ ν := fun k hk μ ν => by
  obtain ⟨w, hw, hcw⟩ := hG k hk μ ν
  exact ⟨c * w, hw.const_mul c, by rw [map_mul, hc, hcw]; ring⟩

/-- Multiplication by a real constant. -/
theorem const_mul_real (r : ℝ) (hG : HasConjLim T d G) :
    HasConjLim T d fun ε k μ ν => (r : ℂ) * G ε k μ ν := by
  have h := const_mul_conj (r : ℂ) 1 (by rw [Complex.conj_ofReal, one_mul]) hG
  rwa [one_mul] at h

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, HasConjLim T d (G i)) :
    HasConjLim T d fun ε k μ ν => ∑ i ∈ s, G i ε k μ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HasConjLim T d fun _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : HasConjLim T d G)
    (h : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε k μ ν = H ε k μ ν) : HasConjLim T d H := fun k hk μ ν => by
  obtain ⟨w, hw, hc⟩ := hG k hk μ ν
  exact ⟨w, hw.congr' (h k hk μ ν), hc⟩

theorem mono {T' : ℝ} (hG : HasConjLim T d G) (hT : T' ^ 2 ≤ T ^ 2) : HasConjLim T' d G :=
  fun k hk μ ν => hG k (by linarith) μ ν

end HasConjLim

/-! ### The phase of a piece -/

namespace VPPiece

variable {T : ℝ} (P : VPPiece T)

/-- **The limit tensor inherits the conjugation phase of the numerator.** -/
theorem conj_W {d : ℂ} (hN : ∀ p ℓ i j, starRingEnd ℂ (P.N p ℓ i j) = d * P.N p ℓ i j)
    {p : Fin 4 → ℝ} (hp : -T ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    starRingEnd ℂ (P.W p i j) = d * P.W p i j := by
  set Q := P.quartic p i j
  set Qd := qsum Finset.univ (fun _ : Unit => d) fun _ => Q
  have hev : Qd.eval = fun ℓ => d * Q.eval ℓ := by
    funext ℓ
    rw [eval_qsum]
    simp
  have hgood : P.D.Good Qd := by
    refine ⟨?_, ?_⟩
    · rcases (P.good_quartic p i j).1 with h7 | hq
      · exact Or.inl h7
      · exact Or.inr (SEData.quart_qsum _ _ _ fun _ _ => hq)
    · rw [hev]
      exact (P.good_quartic p i j).2.const_mul d
  have he : Qd.eval = fun ℓ => starRingEnd ℂ (Q.eval ℓ) := by
    rw [hev]
    funext ℓ
    rw [P.eval_quartic, hN]
  have h1 := pv_conj_of_eval (P.good_quartic p i j) hgood he (P.hV p hp)
  have hI : ∀ u ∈ (Finset.univ : Finset Unit), MeasureTheory.IntegrableOn
      (paramIntegrand Q P.D.α (P.D.mom p) P.D.M 0)
      (QED.Integration.Feynman.simplexSet P.D.m) :=
    fun _ _ => SEData.integrableOn_pv (P.good_quartic p i j) (P.hV p hp)
  rw [SEData.pv_qsum _ _ _ hI] at h1
  simp only [Finset.univ_unique, Finset.sum_singleton] at h1
  simp only [VPPiece.W]
  exact h1.symm

/-- **A multiple of the joint integrals of a piece with phase-`d` numerator**, with a multiplier
of real limit, has a limit with phase `d`. -/
theorem hasConjLim {d : ℂ} (hN : ∀ p ℓ i j, starRingEnd ℂ (P.N p ℓ i j) = d * P.N p ℓ i j)
    {h : ℝ → ℂ} {h₀ : ℝ} (hh : Tendsto h (𝓝[>] 0) (𝓝 (h₀ : ℂ)))
    {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ i j : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p i j = h ε * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) :
    HasConjLim T d G := fun p hp i j => by
  refine ⟨(h₀ : ℂ) * P.W p i j, (hh.mul (P.tendsto hp i j)).congr' ?_, ?_⟩
  · filter_upwards [hG p hp i j] with ε hε
    exact hε.symm
  · rw [map_mul, Complex.conj_ofReal, conj_W P hN hp]
    ring

end VPPiece

end QED.GradedProof.VP2Real

end
