/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.ChainProof.EnumWitness

/-!
# Set (a) and set (b) are disjoint

Helper for the Phase 5 Stage 3a goal (MA₂) `QED.ThreeLoop.not_isSetA_and_isVPChain_two`
(decision D-58). Both (A₁) `IsSetA` and (C₁) `IsVPChain 2` name the open line
`Ψ̄(y) → c → b → a → Ψ(x)`, which the contraction determines, so the photon field `sa` of `a`
is the first chain field `src 0` and the field `x` of the set (a) insertion is `dst 0`.

* If the set (a) insertion is a `photonCt` vertex, the first chain insertion is that vertex,
  so `src 1` is its other field `y`, whose photon partner is the field `sc` of `c`; the second
  chain insertion would then start at the open-line vertex `c`, which is neither a bubble vertex
  (it is followed by `Ψ̄(y)` on the fermion line) nor a `photonCt` vertex.
* If the set (a) insertion is a closed loop through the vertex `u` of `x`, the first chain
  insertion is a bubble `u ⇄ w₀`, so the cycle of `u` is `{u, w₀}`. The second chain insertion
  starts at a vertex that (A₁) puts on the open line (impossible: no open-line vertex is on a
  two-cycle) or on the cycle of `u`; at `u` the photon walk would return to `dst 0`, at `w₀` the
  photon field `src 1` would be paired with itself.

## Main statements

* `QED.ChainProof.SetALink.not_isSetA_and_isVPChain_two'`: the statement of (MA₂).
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.ChainProof.Enum

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- A two-cycle of a permutation is a whole cycle. -/
theorem eq_or_eq_of_sameCycle_of_swap {α : Type*} {σ : Equiv.Perm α} {p q r : α}
    (hpq : σ p = q) (hqp : σ q = p) (h : σ.SameCycle p r) : r = p ∨ r = q := by
  obtain ⟨i, rfl⟩ := h
  have hinv : σ⁻¹ p = q := by rw [Equiv.Perm.inv_eq_iff_eq, hqp]
  have hinv' : σ⁻¹ q = p := by rw [Equiv.Perm.inv_eq_iff_eq, hpq]
  induction i using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show (k : ℤ) + 1 = 1 + k by ring, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rcases ih with h | h <;> rw [h] <;> simp [hpq, hqp]
  | pred k ih =>
    rw [show -(k : ℤ) - 1 = -1 + -k by ring, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
    rcases ih with h | h <;> rw [h] <;> simp [hinv, hinv']

/-- (MA₂) **Set (a) and set (b) are disjoint**: no contraction is both in (A₁) and a
two-insertion chain (C₁). -/
theorem not_isSetA_and_isVPChain_two' (C : Contraction 1 1 κ) :
    ¬ (QED.ThreeLoop.IsSetA C ∧ VPChain.IsVPChain 2 C) := by
  rintro ⟨⟨a, b, c, sa, sb, sc, x, y, ka, kb, kc, s0a, sab, sbc, sc0, -, -, hsa, hsc, hx, hy,
    hins⟩, hch⟩
  obtain ⟨W, h⟩ := (isVPChain_iff 2 C).1 hch
  have ha : W.a = a := Sum.inr_injective (h.s0a.symm.trans s0a)
  have hb : W.b = b := by
    have e := h.sab
    rw [ha, sab] at e
    exact (Sum.inr_injective e).symm
  have hc : W.c = c := by
    have e := h.sbc
    rw [hb, sbc] at e
    exact (Sum.inr_injective e).symm
  have hs0 : W.src 0 = sa := ps_eq_of_gauge (by rw [h.src0, hsa, ha]) (by rw [h.src0]; exact h.ka)
  have hd0 : W.dst 0 = x := by
    have e := h.line 0
    rw [hs0, hx] at e
    exact (Sum.inr_injective e).symm
  have i0 : InsClause C (W.dst 0) (W.src 1) := h.ins 0
  have i1 : InsClause C (W.dst 1) (W.src 2) := h.ins 1
  rcases hins with ⟨kx, hyx, hne, -⟩ | ⟨u, w, hu, -, -, -, hexh⟩
  · -- the set (a) insertion is a `photonCt` vertex
    rcases i0 with ⟨kd, -⟩ | ⟨-, hs1, hne1⟩
    · rw [hd0, kx] at kd
      exact absurd kd (by decide)
    have hs1y : W.src 1 = y := by
      rw [hd0] at hs1 hne1
      rcases ps_eq_or_of_photonCt hs1.symm (hyx.trans hs1.symm) hne.symm (hs1 ▸ kx) with e | e
      · exact absurd e hne1
      · exact e
    have hd1 : W.dst 1 = sc := by
      have e := h.line 1
      rw [hs1y, tau_symm C hy] at e
      exact (Sum.inr_injective e).symm
    rcases i1 with ⟨-, -, -, u, w, hu, -, huw, -⟩ | ⟨kd, -⟩
    · have huc : u = c := fv_ext (by rw [hu, hd1, hsc])
      rw [huc, sc0] at huw
      exact Sum.inl_ne_inr huw
    · rw [hd1, hsc, kc] at kd
      exact absurd kd (by decide)
  · -- the set (a) insertion is a closed loop
    rcases i0 with ⟨-, -, -, u₀, w₀, hu₀, hw₀, huw₀, hwu₀⟩ | ⟨kd, -⟩
    · have huu : u₀ = u := fv_ext (by rw [hu₀, hd0, hu])
      subst huu
      rcases i1 with ⟨kd1, -, -, u₁, w₁, hu₁, -, huw₁, hwu₁⟩ | ⟨kd, -⟩
      · rcases hexh u₁.1 with e | e | e | ⟨v, hv, hcyc⟩
        · have e' : u₁ = a := fv_ext e
          rw [e', sab] at huw₁
          rw [← Sum.inr_injective huw₁, sbc, e'] at hwu₁
          rw [Sum.inr_injective hwu₁, sab] at sc0
          exact Sum.inr_ne_inl sc0
        · have e' : u₁ = b := fv_ext e
          rw [e', sbc] at huw₁
          rw [← Sum.inr_injective huw₁, sc0] at hwu₁
          exact Sum.inl_ne_inr hwu₁
        · have e' : u₁ = c := fv_ext e
          rw [e', sc0] at huw₁
          exact Sum.inl_ne_inr huw₁
        · rcases eq_or_eq_of_sameCycle_of_swap huw₀ hwu₀ hcyc with e | e
          · -- the second insertion starts at `u`: the photon walk returns to `dst 0`
            have hvu : v = u₀ := Sum.inr_injective e
            have hd : W.dst 1 = W.dst 0 :=
              ps_eq_of_gauge (by rw [← hu₁, ← hv, hvu, hu₀]) kd1
            have e1 := h.line 1
            rw [hd, ← h.line 0] at e1
            have hss : W.src 1 = W.src 0 := Sum.inr_injective (C.1.2.injective e1)
            have hwa : w₀ = a := fv_ext (by rw [hw₀, hss, h.src0, ha])
            rw [hwa, ← s0a] at huw₀
            exact Sum.inr_ne_inl (C.1.1.injective huw₀)
          · -- the second insertion starts at `w₀`: `src 1` is paired with itself
            have hvw : v = w₀ := Sum.inr_injective e
            have kw : κ (W.src 1).1 = .gauge := by rw [← hw₀, ← hvw, hv, hu₁]; exact kd1
            have hd : W.src 1 = W.dst 1 := ps_eq_of_gauge (by rw [← hw₀, ← hvw, hv, hu₁]) kw
            have e1 := h.line 1
            rw [← hd] at e1
            exact (C.2 _).2 e1
      · rcases hexh (W.dst 1).1 with e | e | e | ⟨v, hv, -⟩
        · rw [e, ka] at kd
          exact absurd kd (by decide)
        · rw [e, kb] at kd
          exact absurd kd (by decide)
        · rw [e, kc] at kd
          exact absurd kd (by decide)
        · exact v.2 (hv ▸ kd)
    · rw [hd0, ← hu] at kd
      exact u.2 kd

end QED.ChainProof.SetALink

end
