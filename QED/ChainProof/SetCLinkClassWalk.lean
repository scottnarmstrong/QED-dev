/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkClassStd
public import QED.ChainProof.SetALinkClassLoop

/-!
# The set (c) classification: the open line and the renumbering

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step. The open line of a contraction is read off by following the
fermion pairing from the external `Ψ(x)` until it returns (`exists_openLine`, by the first return
time of `Ψ(x)`); numbering its vertices in order and the element last gives a bijection
(`bijective_ext`), along which the contraction is relabelled into standard form.

* `QED.ChainProof.SetCLink.OpenLine`: the open line `ov 0, …, ov (L - 1)` of a contraction.
* `QED.ChainProof.SetCLink.exists_openLine`: every contraction has one.
* `QED.ChainProof.SetCLink.std_of_agree`: if the fermion pairing agrees with `stdNext` along the
  renumbering, the renumbered contraction is in standard form.
* `QED.ChainProof.SetCLink.kfilter_of`, `sfilter_of`: the order conditions of the search, from
  graded order `7`.
* `QED.ChainProof.SetCLink.eq_relabelK_of_std`: a renumbered contraction equal to a relabelled
  representative is itself a relabelling of that representative.
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The first return time -/

/-- **The first return time** of a point under a permutation of a finite type: the iterates
before it are pairwise distinct and exhaust the cycle. -/
theorem exists_period {α : Type*} [Finite α] (σ : Equiv.Perm α) (x : α) :
    ∃ p, 0 < p ∧ (σ ^ p) x = x ∧ (∀ i j, i < p → j < p → (σ ^ i) x = (σ ^ j) x → i = j) ∧
      ∀ y, σ.SameCycle x y → ∃ i < p, (σ ^ i) x = y := by
  classical
  have hex : ∃ k, 0 < k ∧ (σ ^ k) x = x :=
    ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; rfl⟩
  have hp := Nat.find_spec hex
  refine ⟨Nat.find hex, hp.1, hp.2, ?_, ?_⟩
  · have key : ∀ i j, i < j → j < Nat.find hex → (σ ^ i) x = (σ ^ j) x → False := by
      intro i j hij hj e
      have h1 : (σ ^ (j - i)) x = x := by
        have hs : σ ^ j = σ ^ i * σ ^ (j - i) := by rw [← pow_add]; congr 1; omega
        rw [hs, Equiv.Perm.mul_apply] at e
        exact ((σ ^ i).injective e).symm
      exact Nat.find_min hex (show j - i < Nat.find hex by omega) ⟨by omega, h1⟩
    intro i j hi hj e
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj e).elim
    · exact h
    · exact (key j i h hi e.symm).elim
  · intro y hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    refine ⟨n % Nat.find hex, Nat.mod_lt _ hp.1, ?_⟩
    have hpow : ∀ q, (σ ^ (Nat.find hex * q)) x = x := by
      intro q
      induction q with
      | zero => simp
      | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hp.2, ih]
    rw [← hn]
    conv_rhs => rw [← Nat.mod_add_div n (Nat.find hex)]
    rw [pow_add, Equiv.Perm.mul_apply, hpow]

/-! ### The open line -/

/-- **The open line** `ov 0, …, ov (L - 1)` of `C`: the fermion pairing runs
`Ψ(x) → ov 0 → ⋯ → ov (L - 1) → Ψ̄(y)`, through pairwise distinct fermion vertices, and these are
the fermion vertices on the cycle of `Ψ(x)`. -/
structure OpenLine (C : Contraction 1 1 κ) (L : ℕ) (ov : ℕ → Fin N) : Prop where
  start0 : L = 0 → C.1.1 (.inl 0) = .inl 0
  start : 0 < L → ∀ v : Wick.FermionVertex κ, v.1 = ov 0 → C.1.1 (.inl 0) = .inr v
  isFV : ∀ i < L, κ (ov i) ≠ .photonCt
  step : ∀ i, i + 1 < L → ∀ v v' : Wick.FermionVertex κ, v.1 = ov i → v'.1 = ov (i + 1) →
    C.1.1 (.inr v) = .inr v'
  stop : ∀ i, i + 1 = L → ∀ v : Wick.FermionVertex κ, v.1 = ov i → C.1.1 (.inr v) = .inl 0
  inj : ∀ i j, i < L → j < L → ov i = ov j → i = j
  onCycle : ∀ i < L, ∀ v : Wick.FermionVertex κ, v.1 = ov i →
    (C.1.1).SameCycle (.inl 0) (.inr v)
  cover : ∀ v : Wick.FermionVertex κ, (C.1.1).SameCycle (.inl 0) (.inr v) → ∃ i < L, v.1 = ov i

/-- **Every contraction has an open line.** -/
theorem exists_openLine (hN : 0 < N) (C : Contraction 1 1 κ) : ∃ L ov, OpenLine C L ov := by
  obtain ⟨p, hp0, hpp, hinj, hcov⟩ := exists_period C.1.1 (.inl 0)
  set σ := C.1.1 with hσ
  let ov : ℕ → Fin N := fun i => Sum.elim (fun _ => ⟨0, hN⟩) (fun v => v.1) ((σ ^ (i + 1)) (.inl 0))
  have hA : ∀ i, i + 1 < p → ∃ w : Wick.FermionVertex κ, w.1 = ov i ∧
      (σ ^ (i + 1)) (.inl 0) = .inr w := by
    intro i hi
    rcases h : (σ ^ (i + 1)) (.inl 0) with j | w
    · rw [Subsingleton.elim j 0] at h
      exact absurd (hinj (i + 1) 0 hi hp0 (by rw [h]; rfl)) (by omega)
    · exact ⟨w, by simp only [ov, h, Sum.elim_inr], rfl⟩
  have hA' : ∀ i, i + 1 < p → ∀ v : Wick.FermionVertex κ, v.1 = ov i →
      (σ ^ (i + 1)) (.inl 0) = .inr v := by
    intro i hi v hv
    obtain ⟨w, hw, e⟩ := hA i hi
    rw [e, fv_ext (hw.trans hv.symm)]
  have hsucc : ∀ i, (σ ^ (i + 1 + 1)) (.inl 0) = σ ((σ ^ (i + 1)) (.inl 0)) := fun i => by
    rw [pow_succ', Equiv.Perm.mul_apply]
  refine ⟨p - 1, ov, ⟨fun h => ?_, fun h v hv => ?_, fun i hi => ?_, fun i hi v v' hv hv' => ?_,
    fun i hi v hv => ?_, fun i j hi hj e => ?_, fun i hi v hv => ?_, fun v hv => ?_⟩⟩
  · have : p = 1 := by omega
    simpa [this] using hpp
  · simpa using hA' 0 (by omega) v hv
  · obtain ⟨w, hw, -⟩ := hA i (by omega)
    rw [← hw]
    exact w.2
  · rw [← hA' i (by omega) v hv, ← hsucc, hA' (i + 1) (by omega) v' hv']
  · rw [← hA' i (by omega) v hv, ← hsucc, show i + 1 + 1 = p by omega, hpp]
  · obtain ⟨w, hw, ew⟩ := hA i (by omega)
    obtain ⟨w', hw', ew'⟩ := hA j (by omega)
    have := hinj (i + 1) (j + 1) (by omega) (by omega)
      (by rw [ew, ew', fv_ext (hw.trans (e.trans hw'.symm))])
    omega
  · exact ⟨((i + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact hA' i (by omega) v hv⟩
  · obtain ⟨k, hk, e⟩ := hcov _ hv
    rcases k with _ | i
    · exact absurd e (by simp)
    · refine ⟨i, by omega, ?_⟩
      simp only [ov, e, Sum.elim_inr]

/-! ### The renumbering -/

/-- **The renumbering is a bijection**: the open line `ov 0, …, ov (L - 1)`, then the element
vertices `E 0, …, E (k - 1)`. -/
theorem bijective_ext {L k : ℕ} (ov E : ℕ → Fin N)
    (h1 : ∀ i j, i < L → j < L → ov i = ov j → i = j)
    (h2 : ∀ i j, i < k → j < k → E i = E j → i = j) (h3 : ∀ i j, i < L → j < k → ov i ≠ E j)
    (h4 : ∀ t, (∃ i < L, t = ov i) ∨ ∃ j < k, t = E j) :
    Function.Bijective (fun i : Fin (L + k) => if i.val < L then ov i.val else E (i.val - L)) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · simp only at hab
    split_ifs at hab with ha hb hb
    · exact Fin.ext (h1 _ _ ha hb hab)
    · exact absurd hab (h3 _ _ ha (by omega))
    · exact absurd hab.symm (h3 _ _ hb (by omega))
    · have := h2 _ _ (by omega) (by omega) hab
      exact Fin.ext (by omega)
  · rcases h4 t with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨⟨i, by omega⟩, by simp [hi]⟩
    · exact ⟨⟨L + j, by omega⟩, by simp⟩

theorem card_le_sum_order : N ≤ ∑ t, (κ t).order := by
  have h := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => SetALink.order_pos (κ t)
  simpa using h

/-! ### Standard form along the renumbering -/

section Std

variable {κ₀ : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
  (h' : ∀ t, κ₀ (π.symm t) = κ t)

theorem toFN_eq (i : ℕ) (hi : i < N) (hk : κ₀ ⟨i, hi⟩ ≠ .photonCt) :
    toFN κ₀ i = .inr ⟨⟨i, hi⟩, hk⟩ := by
  simp [toFN, hi, hk]

theorem extFK_symm_inr_eq (v : Wick.FermionVertex κ₀) (w : Wick.FermionVertex κ) (hw : w.1 = π v.1) :
    (extFK (nf := 1) π.symm h').symm (.inr v) = .inr w :=
  congrArg Sum.inr (fv_ext hw.symm)

/-- **Standard form from agreement.** If the fermion pairing of `C` agrees with `stdNext` along
the renumbering, the renumbered contraction `relabelK π.symm h' C` is in standard form. -/
theorem std_of_agree (C : Contraction 1 1 κ) (L : ℕ) (b : Bool)
    (h : ∀ z, C.1.1 ((extFK π.symm h').symm z) = (extFK π.symm h').symm (stdNext κ₀ L b z)) :
    ∀ z, (relabelK π.symm h' C).1.1 z = stdNext κ₀ L b z := by
  intro z
  change (extFK π.symm h') (C.1.1 ((extFK π.symm h').symm z)) = _
  rw [h, Equiv.apply_symm_apply]

/-- **A renumbered relabelled representative**: if the renumbered contraction is the relabelling
`relabelK ρ h R` of a representative, `C` is the relabelling along `π * ρ`. -/
theorem eq_relabelK_of_std (C : Contraction 1 1 κ) (R : RepC N) (ρ : Equiv.Perm (Fin N))
    (h : ∀ t, κ₀ (ρ t) = R.kinds t) (hC : relabelK π.symm h' C = relabelK ρ h R.rep) :
    ∃ hκ : ∀ t, κ ((π * ρ) t) = R.kinds t, C = relabelK (π * ρ) hκ R.rep := by
  have hπ : ∀ t, κ (π t) = κ₀ t := fun t => by rw [← h' (π t), π.symm_apply_apply]
  have hκ : ∀ t, κ ((π * ρ) t) = R.kinds t := fun t => (hπ (ρ t)).trans (h t)
  refine ⟨hκ, ?_⟩
  have e1 : relabelK π hπ (relabelK π.symm h' C) = C := by
    rw [relabelK_trans π.symm h' π hπ (fun t => by simp) C]
    exact relabelK_self _ (fun t => by simp) _ C
  rw [← e1, hC, relabelK_trans ρ h π hπ hκ]

/-! ### The order conditions -/

include h' in
theorem sum_order_eq : ∑ t, (κ₀ t).order = ∑ t, (κ t).order := by
  rw [← Equiv.sum_comp π.symm (fun t => (κ₀ t).order)]
  simp only [h']

include h' in
/-- **The order conditions of the element branches.** -/
theorem kfilter_of (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    (hph : ∀ t : Graded.CtVertex κ, κ t.1 = .photonCt → g t = 0) : KFilter κ₀ := by
  have hs := sum_order_eq π h'
  rw [SetALink.gradedOrder_eq] at hg
  have h2 : ∑ t : Graded.CtVertex κ, 2 * g t = 2 * ∑ t : Graded.CtVertex κ, g t := by
    rw [Finset.mul_sum]
  refine ⟨by omega, by omega, fun hlt => ?_⟩
  have hne : ∑ t : Graded.CtVertex κ, g t ≠ 0 := by omega
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨π.symm t.1, ?_, ?_⟩ <;> rw [h']
  · exact t.2
  · exact fun e => ht (hph t e)

end Std

/-- **The order conditions of the VP-share branch.** -/
theorem sfilter_of (π : Equiv.Perm (Fin N)) (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (hfv : ∀ t, κ t ≠ .photonCt) (t₀ : Graded.CtVertex κ)
    (h1 : g t₀ = 1) (hu : ∀ t : Graded.CtVertex κ, t = t₀) : SFilter (fun i => κ (π i)) := by
  have hs : ∑ t, (κ (π t)).order = ∑ t, (κ t).order := Equiv.sum_comp π (fun t => (κ t).order)
  rw [SetALink.gradedOrder_eq, Fintype.sum_eq_single t₀ (fun t ht => absurd (hu t) ht), h1]
    at hg
  refine ⟨fun t => hfv _, show ∑ t, (κ (π t)).order = 5 by omega,
    ⟨π.symm t₀.1, by simpa using t₀.2⟩, fun t t' ht ht' => ?_⟩
  have e1 := congrArg Subtype.val (hu ⟨π t, ht⟩)
  have e2 := congrArg Subtype.val (hu ⟨π t', ht'⟩)
  exact π.injective (e1.trans e2.symm)

end QED.ChainProof.SetCLink

end
