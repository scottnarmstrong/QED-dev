/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.FermionVertex
public import QED.Frozen.Wick.PhotonSlot
public import QED.Frozen.Algebra.Gamma
public import QED.Frozen.Algebra.Slash
public import QED.Frozen.Algebra.Dot
public import QED.Frozen.Algebra.Metric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

open Complex

namespace QED.Wick

/-- (V₁₉) The factor of vertex `t` for spinor indices `α` (of `Ψ̄`) and `β` (of `Ψ`) and Lorentz
indices `lor` of the photon fields: `i` times the Lagrangian term in momentum space ((62.2)–(62.3);
rule 9, (62.12), (62.28)). The two photon fields of `photonCt` are distinguishable slots, so its
factor is half of the rule `-i (Z₃ - 1)(k² g^{μν} - k^μ k^ν)`, which counts both pairings;
`g^{μν} = g_{μν}` in the mostly-plus metric. -/
noncomputable def vertexFactor (e δ₁ δ₂ δm δ₃ m : ℝ) {N : ℕ} {κ : Fin N → VertexKind}
    (α β : FermionVertex κ → Fin 4) (lor : PhotonSlot κ → Fin 4)
    (kψ : FermionVertex κ → Fin 4 → ℝ) (kA : PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) : ℂ :=
  match h : κ t with
  | .gauge => I * e * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩)
      (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)
  | .gaugeCt => I * ((δ₁ * e : ℝ) : ℂ) *
      Dirac.gamma (lor ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)
  | .fermionCt => -I * (((δ₂ : ℂ) • Dirac.slash (kψ ⟨t, by simp [h]⟩)
      + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩))
  | .photonCt =>
      let k := kA ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩;
      let μ := lor ⟨t, ⟨0, by simp [h, VertexKind.photonSlots]⟩⟩;
      let ν := lor ⟨t, ⟨1, by simp [h, VertexKind.photonSlots]⟩⟩;
      -(I / 2) * ((δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ)

end QED.Wick

end
