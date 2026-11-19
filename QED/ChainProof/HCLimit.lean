/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCValueEnum

/-!
# The per-class `ε → 0⁺` limits of set (b), reduced to the nine representatives

Helper level, Phase 5 Stage 1a, obligation `QED.ChainProof.ClassLimitLink` of
`QED/ChainProof/HCClasses.lean` for the class decomposition `X = QED.ChainProof.HCValue.enumClass`
(the nine signed class vertices of O3-4, `chainClassDecomposition_enum`).

* `RepLimit C`: at admissible parameters, every on-shell positive-energy pair with `q² > 0` and
  all indices, the value (F₇) of the contraction `C` at T1's flavours, with the external data of
  the chain vertex, has a limit as `ε → 0⁺`.
* `isClassLimit_classV`, `isClassLimit_neg_classV`: a limit of the value gives a class limit of
  `classV C` and of its negative.
* **`classLimitLink_enum_of_reps`**: `ClassLimitLink enumClass` from `RepLimit` of `repBB`, of
  `repBD s` and `repDB s` (`s : Fin 2`) and of `repDD s₀ s₁`.

The nine `RepLimit` statements are the analytic content (O3-5, O3-6 at the `ε → 0⁺` level). The
four `δ₃`–`δ₃` ones are proved in `QED/ChainProof/HCLimitDDLimit.lean` (`repLimit_repDD`); the
bubble–bubble class is reduced at fixed `ε` to an outer one-loop integral in
`QED/ChainProof/HCLimitNested.lean`; the bubble–bubble, bubble–`δ₃` and `δ₃`–bubble limits are
open.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction)

namespace QED.ChainProof.HCLimit

open QED.ChainProof.HCValue QED.ChainProof.Enum

/-- **The `ε → 0⁺` limit of a representative**: at admissible parameters, every on-shell
positive-energy pair with `q² > 0` and all indices, the value (F₇) of `C` at T1's flavours has a
limit as `ε → 0⁺`. -/
def RepLimit {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ p' p : Fin 4 → ℝ, IsPairQ P.m p' p → ∀ α β μ : Fin 4,
    ∃ L : ℂ, Tendsto (fun ε => QED.Lepton.contractionValue₂ { P with ε := ε } (chainFlavors P) C
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))
      (𝓝[>] 0) (𝓝 L)

theorem exists_classV_limit {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    (hC : RepLimit C) {P : Params} (hA : ChainAdmissible P) {p' p : Fin 4 → ℝ}
    (hpq : IsPairQ P.m p' p) : ∃ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∀ μ i j,
      Tendsto (fun ε => classV C { P with ε := ε } p' p μ i j) (𝓝[>] 0) (𝓝 (Y μ i j)) := by
  choose L hL using fun μ i j => hC P hA p' p hpq i j μ
  exact ⟨fun μ => Matrix.of fun i j => (1 / I) * L μ i j, fun μ i j =>
    (hL μ i j).const_mul (1 / I)⟩

/-- **`ClassLimitLink enumClass` from the nine representatives.** -/
theorem classLimitLink_enum_of_reps (hBB : RepLimit repBB) (hBD : ∀ s, RepLimit (repBD s))
    (hDB : ∀ s, RepLimit (repDB s)) (hDD : ∀ s₀ s₁, RepLimit (repDD s₀ s₁)) :
    ClassLimitLink enumClass := by
  have pos : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}, RepLimit C →
      ∀ P, ChainAdmissible P → ∀ p' p, IsPairQ P.m p' p →
        ∃ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∀ μ i j,
          Tendsto (fun ε => classV C { P with ε := ε } p' p μ i j) (𝓝[>] 0)
          (𝓝 (Y μ i j)) :=
    fun hC _ hA _ _ hpq => exists_classV_limit hC hA hpq
  have neg : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}, RepLimit C →
      ∀ P, ChainAdmissible P → ∀ p' p, IsPairQ P.m p' p →
        ∃ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∀ μ i j,
          Tendsto (fun ε => (-classV C { P with ε := ε } p' p μ) i j) (𝓝[>] 0) (𝓝 (Y μ i j)) := by
    intro N κ C hC P hA p' p hpq
    obtain ⟨Y, hY⟩ := exists_classV_limit hC hA hpq
    exact ⟨fun μ => -Y μ, fun μ i j => by simpa using (hY μ i j).neg⟩
  intro r P hA p' p hpq
  fin_cases r
  · exact pos hBB P hA p' p hpq
  · exact neg (hBD 0) P hA p' p hpq
  · exact neg (hBD 1) P hA p' p hpq
  · exact neg (hDB 0) P hA p' p hpq
  · exact neg (hDB 1) P hA p' p hpq
  · exact pos (hDD 0 0) P hA p' p hpq
  · exact pos (hDD 0 1) P hA p' p hpq
  · exact pos (hDD 1 0) P hA p' p hpq
  · exact pos (hDD 1 1) P hA p' p hpq

end QED.ChainProof.HCLimit

end
