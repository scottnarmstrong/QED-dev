/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Wick.ClassificationBasic

/-!
# Wick contractions with at most two vertices

The terms of `QED.Wick.wickVertex` (packet 5, decision D-20) with `N ≤ 2` vertices.

* `not_isOnePI_of_fin_zero`: there is no contraction without vertices (the external `A(z)` has
  nothing to pair with).
* `sum_isOnePI_tree`: a single vertex with one `Ψ̄ Ψ` pair and one photon field has exactly one
  1PI contraction; its fermionic sign is `+1`, it has no internal lines, and its value is the
  vertex factor with the external indices. This gives the trees `i e γ^μ` (`gauge`) and
  `i δ₁ e γ^μ` (`gaugeCt`).
* `not_isOnePI_of_fin_two`: no contraction of two vertices of total order at most `3` is 1PI.
  For `[gauge, gauge]` there is no contraction (three photon fields); in the other four cases
  at most one internal line joins the two vertices.
-/

@[expose] public section

namespace QED.Wick

variable {N : ℕ} {κ : Fin N → VertexKind}

/-- There is no contraction without vertices, so none is 1PI. -/
theorem not_isOnePI_of_fin_zero {κ : Fin 0 → VertexKind} (C : Contraction κ) : ¬ IsOnePI C := by
  refine fun _ => (C.2 none).2 ?_
  rcases C.1.2 none with _ | ⟨t, _⟩
  · rfl
  · exact t.elim0

/-- A sum over the 1PI contractions vanishes when no contraction is 1PI. -/
theorem sum_isOnePI_eq_zero {M : Type*} [AddCommMonoid M] [DecidablePred (IsOnePI (κ := κ))]
    (h : ∀ C : Contraction κ, ¬ IsOnePI C) (F : Contraction κ → M) :
    ∑ C ∈ (Finset.univ : Finset (Contraction κ)).filter IsOnePI, F C = 0 :=
  Finset.sum_eq_zero fun C hC => absurd (Finset.mem_filter.mp hC).2 (h C)

section TwoVertices

/-- With two vertices and the external `Ψ(x)` contracted with a vertex field, at most one
internal fermion line joins the two vertices. -/
theorem FermionLine.eq_of_crosses_of_two {κ : Fin 2 → VertexKind} {C : Contraction κ}
    (hC : C.1.1 none ≠ none) {f₁ f₂ : FermionLine C} {v : Fin 2}
    (h₁ : Line.Crosses (Sum.inl f₁ : Line C) v) (h₂ : Line.Crosses (Sum.inl f₂ : Line C) v) :
    f₁ = f₂ := by
  obtain ⟨t₁, ht₁⟩ := f₁
  obtain ⟨t₂, ht₂⟩ := f₂
  obtain ⟨s₁, hs₁⟩ := Option.ne_none_iff_exists'.mp ht₁
  obtain ⟨s₂, hs₂⟩ := Option.ne_none_iff_exists'.mp ht₂
  rw [Line.crosses_inl_iff _ hs₁] at h₁
  rw [Line.crosses_inl_iff _ hs₂] at h₂
  dsimp only at h₁ h₂
  by_contra hne
  have ht : t₁.1 ≠ t₂.1 := fun h => hne (by congr 1; exact Subtype.ext h)
  have e₁ : s₁ = t₂ := Subtype.ext (by omega)
  have e₂ : s₂ = t₁ := Subtype.ext (by omega)
  subst e₁ e₂
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hC
  rcases (show x = s₁ ∨ x = s₂ from by
    rcases x with ⟨x, hx'⟩; simp only [Subtype.ext_iff]; omega) with rfl | rfl
  · exact Option.some_ne_none _ (C.1.1.injective (hs₁.trans hx.symm))
  · exact Option.some_ne_none _ (C.1.1.injective (hs₂.trans hx.symm))

/-- If every vertex field of `κ` is the same fermion vertex, no internal fermion line crosses a
cut. -/
theorem FermionLine.not_crosses_of_forall_eq (hκ : ∀ x y : FermionVertex κ, x = y)
    {C : Contraction κ} (f : FermionLine C) (v : Fin N) :
    ¬ Line.Crosses (Sum.inl f : Line C) v := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp f.2
  rw [Line.crosses_inl_iff _ hs]
  exact fun h => h.1 (congrArg Subtype.val (hκ _ _))

/-- The pairs `(x, y)` of photon fields of `κ` at different vertices with `photonKey x <
photonKey y` all have the same `x`, or all have the same `y`. Then at most one internal photon
line joins different vertices. -/
def PhotonCrossingUnique (κ : Fin N → VertexKind) : Prop :=
  (∀ x y x' y' : PhotonSlot κ, (x.1 ≠ y.1 ∧ photonKey x < photonKey y) →
      (x'.1 ≠ y'.1 ∧ photonKey x' < photonKey y') → x = x') ∨
    ∀ x y x' y' : PhotonSlot κ, (x.1 ≠ y.1 ∧ photonKey x < photonKey y) →
      (x'.1 ≠ y'.1 ∧ photonKey x' < photonKey y') → y = y'

/-- Under `PhotonCrossingUnique κ`, two crossing internal photon lines are equal. -/
theorem PhotonLine.eq_of_crosses (hκ : PhotonCrossingUnique κ) {C : Contraction κ}
    {g₁ g₂ : PhotonLine C} {v w : Fin N} (h₁ : Line.Crosses (Sum.inr g₁ : Line C) v)
    (h₂ : Line.Crosses (Sum.inr g₂ : Line C) w) : g₁ = g₂ := by
  obtain ⟨x₁, y₁, hy₁, hk₁⟩ := g₁
  obtain ⟨x₂, y₂, hy₂, hk₂⟩ := g₂
  rw [Line.crosses_inr_iff _ hy₁] at h₁
  rw [Line.crosses_inr_iff _ hy₂] at h₂
  rcases hκ with hκ | hκ
  · have := hκ x₁ y₁ x₂ y₂ ⟨h₁.1, hk₁⟩ ⟨h₂.1, hk₂⟩
    subst this; rfl
  · have := hκ x₁ y₁ x₂ y₂ ⟨h₁.1, hk₁⟩ ⟨h₂.1, hk₂⟩
    subst this
    have : x₁ = x₂ := Option.some_injective _ (C.1.2.injective (hy₁.trans hy₂.symm))
    subst this; rfl

/-- A contraction with two vertices is not 1PI when its crossing photon lines are unique and it
has either a single fermion vertex or a single photon field. -/
theorem not_isOnePI_of_two {κ : Fin 2 → VertexKind} (hph : PhotonCrossingUnique κ)
    (hmix : (∀ x y : FermionVertex κ, x = y) ∨ ∀ x y : PhotonSlot κ, x = y)
    (C : Contraction κ) : ¬ IsOnePI C := by
  intro hC
  obtain ⟨f₁, f₂, hne, h₁, h₂⟩ := hC.exists_crosses_ne (v := 0) (w := 1) (by decide)
  have hinr : ∀ g : PhotonLine C, (∀ x y : PhotonSlot κ, x = y) → False := by
    rintro ⟨x, y, -, hk⟩ h
    rw [h x y] at hk
    exact lt_irrefl _ hk
  rcases f₁ with f₁ | g₁ <;> rcases f₂ with f₂ | g₂
  · exact hne (congrArg _ (FermionLine.eq_of_crosses_of_two hC.1 h₁ h₂))
  · rcases hmix with h | h
    · exact FermionLine.not_crosses_of_forall_eq h _ _ h₁
    · exact hinr g₂ h
  · rcases hmix with h | h
    · exact FermionLine.not_crosses_of_forall_eq h _ _ h₂
    · exact hinr g₁ h
  · exact hne (congrArg _ (PhotonLine.eq_of_crosses hph h₁ h₂))

/-- No contraction of two vertices of total order at most `3` is 1PI. -/
theorem not_isOnePI_of_fin_two (κ : Fin 2 → VertexKind) (hκ : ∑ t, (κ t).order ≤ 3)
    (C : Contraction κ) : ¬ IsOnePI C := by
  obtain ⟨k₀, k₁, rfl⟩ : ∃ k₀ k₁, κ = ![k₀, k₁] :=
    ⟨κ 0, κ 1, by funext i; fin_cases i <;> rfl⟩
  cases k₀ <;> cases k₁ <;> first
    | exact absurd hκ (by decide)
    | exact (isEmpty_contraction_of_not_two_dvd (by decide)).elim C
    | exact not_isOnePI_of_two (by unfold PhotonCrossingUnique; decide) (by decide) C

end TwoVertices

section OneVertex

variable (κ : Fin 1 → VertexKind) (h₁ : κ 0 ≠ .photonCt) (h₂ : (κ 0).photonSlots = 1)

/-- The fermion vertex of a single non-`photonCt` vertex. -/
def oneFv : FermionVertex κ := ⟨0, h₁⟩

/-- The photon field of a single vertex with one photon field. -/
def onePs : PhotonSlot κ := ⟨0, ⟨0, by omega⟩⟩

/-- A single vertex has one fermion vertex. -/
theorem eq_oneFv (x : FermionVertex κ) : x = oneFv κ h₁ := Subtype.ext (Subsingleton.elim _ _)

/-- A single vertex with one photon field has one photon field. -/
theorem eq_onePs (x : PhotonSlot κ) : x = onePs κ h₂ := by
  obtain ⟨t, k⟩ := x
  obtain rfl : t = 0 := Subsingleton.elim _ _
  have : k.val = 0 := by have := k.2; omega
  exact Sigma.ext rfl (heq_of_eq (Fin.ext this))

/-- The unique 1PI contraction of a single vertex with one photon field: the external fields
are contracted with the three fields of the vertex. -/
def treeContraction : Contraction κ :=
  ⟨(Equiv.swap none (some (oneFv κ h₁)), Equiv.swap none (some (onePs κ h₂))), fun a =>
    ⟨Equiv.swap_apply_self _ _ _, by
      rcases a with _ | x
      · simp
      · rw [eq_onePs κ h₂ x]; simp⟩⟩

/-- The only 1PI contraction of a single vertex with one photon field is `treeContraction`. -/
theorem isOnePI_iff_eq_treeContraction (C : Contraction κ) :
    IsOnePI C ↔ C = treeContraction κ h₁ h₂ := by
  constructor
  · intro hC
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hC.1
    rw [eq_oneFv κ h₁ x] at hx
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (C.2 none).2
    rw [eq_onePs κ h₂ y] at hy
    have hσ : C.1.1 (some (oneFv κ h₁)) = none := by
      rcases h : C.1.1 (some (oneFv κ h₁)) with _ | z
      · rfl
      · rw [eq_oneFv κ h₁ z] at h
        exact absurd (C.1.1.injective (h.trans hx.symm)) (Option.some_ne_none _)
    have hτ : C.1.2 (some (onePs κ h₂)) = none := by rw [← hy, (C.2 none).1]
    apply Subtype.ext
    apply Prod.ext <;> ext1 z
    · rcases z with _ | z
      · simp [treeContraction, hx]
      · rw [eq_oneFv κ h₁ z]; simp [treeContraction, hσ]
    · rcases z with _ | z
      · simp [treeContraction, hy]
      · rw [eq_onePs κ h₂ z]; simp [treeContraction, hτ]
  · rintro rfl
    refine ⟨by simp [treeContraction], fun g u w => ?_⟩
    rw [Subsingleton.elim u w]

/-- The tree contraction has no internal fermion line. -/
instance : IsEmpty (FermionLine (treeContraction κ h₁ h₂)) :=
  ⟨fun f => f.2 (by rw [eq_oneFv κ h₁ f.1]; simp [treeContraction])⟩

/-- The tree contraction has no internal photon line. -/
instance : IsEmpty (PhotonLine (treeContraction κ h₁ h₂)) :=
  ⟨fun g => by
    obtain ⟨x, y, hy, -⟩ := g
    rw [eq_onePs κ h₂ x] at hy
    simp [treeContraction] at hy⟩

/-- The tree contraction has fermionic sign `+1`: `(-1)¹` from the vertex times the sign `-1` of
a transposition. -/
theorem fermionSign_treeContraction : fermionSign (treeContraction κ h₁ h₂) = 1 := by
  have hcard : Fintype.card (FermionVertex κ) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨oneFv κ h₁, eq_oneFv κ h₁⟩
  simp [fermionSign, hcard, treeContraction]

/-- The amplitude of the tree contraction is the vertex factor with the external indices. -/
theorem contractionAmplitude_treeContraction (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p ℓ : Fin 4 → ℝ)
    (μ : Fin 4) (c : ℂ)
    (hvf : ∀ α β lor kψ kA, vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA 0 =
      c * Dirac.gamma (lor (onePs κ h₂)) (α (oneFv κ h₁)) (β (oneFv κ h₁))) :
    contractionAmplitude e δ₁ δ₂ δm δ₃ m mγ Λ ε (treeContraction κ h₁ h₂) p' p ℓ μ =
      c • Dirac.gamma μ := by
  ext αe βe
  simp only [contractionAmplitude, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, Fin.prod_univ_one, hvf]
  have hcond : ∀ (α β : FermionVertex κ → Fin 4) (lor : PhotonSlot κ → Fin 4),
      ((∀ j, (treeContraction κ h₁ h₂).1.1 none = some j → α j = αe) ∧
        (∀ t, (treeContraction κ h₁ h₂).1.1 (some t) = none → β t = βe) ∧
          ∀ a, (treeContraction κ h₁ h₂).1.2 none = some a → lor a = μ) ↔
        α (oneFv κ h₁) = αe ∧ β (oneFv κ h₁) = βe ∧ lor (onePs κ h₂) = μ := by
    intro α β lor
    simp [treeContraction, Equiv.swap_apply_eq_iff]
  have hfv : ∀ (α : FermionVertex κ → Fin 4) (i : Fin 4), α (oneFv κ h₁) = i →
      α = fun _ => i := fun α i h => funext fun j => by rw [eq_oneFv κ h₁ j, h]
  have hps : ∀ (lor : PhotonSlot κ → Fin 4), lor (onePs κ h₂) = μ → lor = fun _ => μ :=
    fun lor h => funext fun j => by rw [eq_onePs κ h₂ j, h]
  simp only [hcond]
  rw [Fintype.sum_eq_single (fun _ => αe) fun α hα => Finset.sum_eq_zero fun β _ =>
      Finset.sum_eq_zero fun lor _ => by rw [ite_eq_right fun h => hα (hfv α αe h.1), zero_mul],
    Fintype.sum_eq_single (fun _ => βe) fun β hβ => Finset.sum_eq_zero fun lor _ => by
      rw [ite_eq_right fun h => hβ (hfv β βe h.2.1), zero_mul],
    Fintype.sum_eq_single (fun _ => μ) fun lor hlor => by
      rw [ite_eq_right fun h => hlor (hps lor h.2.2), zero_mul]]
  simp

/-- The 1PI part of a single vertex with one `Ψ̄ Ψ` pair and one photon field whose vertex factor
is `c γ^ρ`: the tree `c γ^μ`. -/
theorem sum_isOnePI_tree [DecidablePred (IsOnePI (κ := κ))] (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) (c : ℂ)
    (hvf : ∀ α β lor kψ kA, vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA 0 =
      c * Dirac.gamma (lor (onePs κ h₂)) (α (oneFv κ h₁)) (β (oneFv κ h₁))) :
    ∑ C ∈ (Finset.univ : Finset (Contraction κ)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) • contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ =
      c • Dirac.gamma μ := by
  rw [Finset.sum_eq_single_of_mem (treeContraction κ h₁ h₂)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (isOnePI_iff_eq_treeContraction κ h₁ h₂ _).mpr rfl⟩)
      fun C hC hne => absurd ((isOnePI_iff_eq_treeContraction κ h₁ h₂ C).mp
        (Finset.mem_filter.mp hC).2) hne,
    fermionSign_treeContraction, contractionValue,
    ite_eq_left (inferInstance : IsEmpty (Line (treeContraction κ h₁ h₂))),
    contractionAmplitude_treeContraction κ h₁ h₂ e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p 0 μ c hvf]
  simp

end OneVertex

/-- The tree of a single `gauge` vertex: `i e γ^μ`. -/
theorem sum_isOnePI_gauge [DecidablePred (IsOnePI (κ := fun _ : Fin 1 => VertexKind.gauge))]
    (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction fun _ : Fin 1 => VertexKind.gauge)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) • contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ =
      (Complex.I * (e : ℂ)) • Dirac.gamma μ :=
  sum_isOnePI_tree _ (by decide) rfl e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ _ fun _ _ _ _ _ => rfl

/-- The tree of a single `gaugeCt` vertex: `i δ₁ e γ^μ`. -/
theorem sum_isOnePI_gaugeCt
    [DecidablePred (IsOnePI (κ := fun _ : Fin 1 => VertexKind.gaugeCt))]
    (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction fun _ : Fin 1 => VertexKind.gaugeCt)).filter
        IsOnePI,
      ((fermionSign C : ℤ) : ℂ) • contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ =
      (Complex.I * ((δ₁ * e : ℝ) : ℂ)) • Dirac.gamma μ :=
  sum_isOnePI_tree _ (by decide) rfl e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ _ fun _ _ _ _ _ => rfl

end QED.Wick

end
