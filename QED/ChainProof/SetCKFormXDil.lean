/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXG1
public import QED.Polylog.Basic
import QED.Polylog.Deriv
import QED.Polylog.LiCalculus
import Mathlib.Tactic.FieldSimp

/-!
# Set (c), Stage K, closed forms: a dilogarithm identity for `ρ_X`

Helper level (no frozen statement). Step 5 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+). With `K = X² - 2X + 2` and `N = X² - X + 1`, the combination `formXDil` of the
dilogarithms at the endpoints of the antiderivatives `G₁`, `G₂`, minus the dilogarithms of
`formXW`, vanishes:

**`formXDil_eq_zero`**: for `X ∈ (0, 1)`,
`Li₂(1/K) + Li₂((1 - X)²) + Li₂(N) - Li₂(N/K) - Li₂((1 - X)²/N) + Li₂((1 - X)/N)
  + Li₂(1/(2 - X)) - Li₂((1 - X)/K) - Li₂((1 - X)/(2 - X)) + Li₂((1 - X)²/K) - 2 Li₂(1 - X)
  - 4 Li₂(X - 1) - 2 Li₂(1) + log K log N - log(1 - X) log K - log(1 - X) log(2 - X) = 0`.

Proof: the derivative vanishes on `(0, 1)` and the function is continuous on `[0, 1/2]` with
value `0` at `X = 0` (`Li₂(1) = π²/6`, `Li₂(-1) = -π²/12`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.ChainProof.SetCK

/-- `N = X² - X + 1`. -/
noncomputable def formXN (X : ℝ) : ℝ := X ^ 2 - X + 1

theorem formXN_pos (X : ℝ) : 0 < formXN X := by
  unfold formXN; nlinarith [sq_nonneg (X - 1 / 2)]

/-- The dilogarithm combination of `ρ_X`. -/
noncomputable def formXDil (X : ℝ) : ℝ :=
  Li₂ (1 / formXK X) + Li₂ ((1 - X) ^ 2) + Li₂ (formXN X) - Li₂ (formXN X / formXK X) -
    Li₂ ((1 - X) ^ 2 / formXN X) + Li₂ ((1 - X) / formXN X) + Li₂ (1 / (2 - X)) -
    Li₂ ((1 - X) / formXK X) - Li₂ ((1 - X) / (2 - X)) + Li₂ ((1 - X) ^ 2 / formXK X) -
    2 * Li₂ (1 - X) - 4 * Li₂ (X - 1) - 2 * Li₂ 1 + log (formXK X) * log (formXN X) -
    log (1 - X) * log (formXK X) - log (1 - X) * log (2 - X)

/-- The chain rule for `Li₂ ∘ f`, `f ∈ (-1, 1) \ {0}`, with `log(1 - f)` rewritten. -/
theorem formX_hasDerivAt_li2_log {f : ℝ → ℝ} {f' x A : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) (hA : log (1 - f x) = A) :
    HasDerivAt (fun z => Li₂ (f z)) (-A / f x * f') x := by
  rw [← hA]
  exact (hasDerivAt_Li₂ h1 h0).comp x hf

section

variable {X : ℝ}

theorem hasDerivAt_formXDil (hX : X ∈ Ioo (0 : ℝ) 1) : HasDerivAt formXDil 0 X := by
  obtain ⟨hX0, hX1⟩ := hX
  have hK := formXK_pos X
  have hN := formXN_pos X
  have h1X : 0 < 1 - X := by linarith
  have h2X : 0 < 2 - X := by linarith
  have hNK : formXN X < formXK X := by unfold formXN formXK; linarith
  have h1N : 1 - X < formXN X := by unfold formXN; nlinarith
  have h1K : 1 < formXK X := by unfold formXK; nlinarith
  have hab : ∀ y : ℝ, 0 < y → y < 1 → |y| < 1 := fun y h0 h1 => by
    rw [abs_lt]; constructor <;> linarith
  have dK : HasDerivAt formXK (2 * X - 2) X := by
    have h := ((hasDerivAt_pow 2 X).sub ((hasDerivAt_id X).const_mul 2)).add_const 2
    unfold formXK
    exact h.congr_deriv (by simp)
  have dN : HasDerivAt formXN (2 * X - 1) X := by
    have h := ((hasDerivAt_pow 2 X).sub (hasDerivAt_id X)).add_const 1
    unfold formXN
    exact h.congr_deriv (by simp)
  have d1 : HasDerivAt (fun x => 1 - x) (-1) X := by
    simpa using (hasDerivAt_id X).const_sub 1
  have d2 : HasDerivAt (fun x => 2 - x) (-1) X := by
    simpa using (hasDerivAt_id X).const_sub 2
  have d1s : HasDerivAt (fun x => (1 - x) ^ 2) (2 * (1 - X) * (-1)) X := by
    refine (d1.pow 2).congr_deriv ?_
    norm_num
  have dc := hasDerivAt_const X (1 : ℝ)
  -- the eleven `Li₂` terms with arguments in `(0, 1)`
  have t1 := formX_hasDerivAt_li2_log (f := fun x => 1 / formXK x) (dc.div dK hK.ne')
    (hab _ (by positivity) (by rw [div_lt_one hK]; exact h1K)) (by positivity)
    (A := 2 * log (1 - X) - log (formXK X)) (by
      rw [show 1 - 1 / formXK X = (1 - X) ^ 2 / formXK X by
        field_simp; unfold formXK; ring, log_div (by positivity) hK.ne', log_pow]
      push_cast; ring)
  have t2 := formX_hasDerivAt_li2_log (f := fun x => (1 - x) ^ 2) d1s
    (hab _ (by positivity) (by nlinarith)) (by positivity) (A := log X + log (2 - X)) (by
      rw [show 1 - (1 - X) ^ 2 = X * (2 - X) by ring, log_mul hX0.ne' h2X.ne'])
  have t3 := formX_hasDerivAt_li2_log (f := fun x => 1 - x) d1
    (hab _ h1X (by linarith)) h1X.ne' (A := log X) (by rw [sub_sub_cancel])
  have t4 := formX_hasDerivAt_li2_log (f := fun x => formXN x / formXK x) (dN.div dK hK.ne')
    (hab _ (by positivity) (by rw [div_lt_one hK]; exact hNK)) (by positivity)
    (A := log (1 - X) - log (formXK X)) (by
      rw [show 1 - formXN X / formXK X = (1 - X) / formXK X by
        field_simp; unfold formXN formXK; ring, log_div h1X.ne' hK.ne'])
  have t5 := formX_hasDerivAt_li2_log (f := formXN) dN
    (hab _ hN (by unfold formXN; nlinarith)) hN.ne' (A := log X + log (1 - X)) (by
      rw [show 1 - formXN X = X * (1 - X) by unfold formXN; ring, log_mul hX0.ne' h1X.ne'])
  have t6 := formX_hasDerivAt_li2_log (f := fun x => (1 - x) ^ 2 / formXN x)
    (d1s.div dN hN.ne') (hab _ (by positivity) (by rw [div_lt_one hN]; unfold formXN; nlinarith))
    (by positivity) (A := log X - log (formXN X)) (by
      rw [show 1 - (1 - X) ^ 2 / formXN X = X / formXN X by
        field_simp; unfold formXN; ring, log_div hX0.ne' hN.ne'])
  have t7 := formX_hasDerivAt_li2_log (f := fun x => (1 - x) / formXN x) (d1.div dN hN.ne')
    (hab _ (by positivity) (by rw [div_lt_one hN]; exact h1N)) (by positivity)
    (A := 2 * log X - log (formXN X)) (by
      rw [show 1 - (1 - X) / formXN X = X ^ 2 / formXN X by
        field_simp; unfold formXN; ring, log_div (by positivity) hN.ne', log_pow]
      push_cast; ring)
  have t8 := formX_hasDerivAt_li2_log (f := fun x => 1 / (2 - x)) (dc.div d2 h2X.ne')
    (hab _ (by positivity) (by rw [div_lt_one h2X]; linarith)) (by positivity)
    (A := log (1 - X) - log (2 - X)) (by
      rw [show 1 - 1 / (2 - X) = (1 - X) / (2 - X) by field_simp; ring,
        log_div h1X.ne' h2X.ne'])
  have t9 := formX_hasDerivAt_li2_log (f := fun x => (1 - x) / formXK x) (d1.div dK hK.ne')
    (hab _ (by positivity) (by rw [div_lt_one hK]; linarith)) (by positivity)
    (A := log (formXN X) - log (formXK X)) (by
      rw [show 1 - (1 - X) / formXK X = formXN X / formXK X by
        field_simp; unfold formXN formXK; ring, log_div hN.ne' hK.ne'])
  have t10 := formX_hasDerivAt_li2_log (f := fun x => (1 - x) / (2 - x)) (d1.div d2 h2X.ne')
    (hab _ (by positivity) (by rw [div_lt_one h2X]; linarith)) (by positivity)
    (A := -log (2 - X)) (by
      rw [show 1 - (1 - X) / (2 - X) = (2 - X)⁻¹ by field_simp; ring, log_inv])
  have t11 := formX_hasDerivAt_li2_log (f := fun x => (1 - x) ^ 2 / formXK x)
    (d1s.div dK hK.ne') (hab _ (by positivity) (by rw [div_lt_one hK]; unfold formXK; nlinarith))
    (by positivity) (A := -log (formXK X)) (by
      rw [show 1 - (1 - X) ^ 2 / formXK X = (formXK X)⁻¹ by
        field_simp; unfold formXK; ring, log_inv])
  have t12 := formX_hasDerivAt_li2_log (f := fun x => x - 1) ((hasDerivAt_id X).sub_const 1)
    (by rw [abs_lt]; constructor <;> linarith) (sub_ne_zero.2 hX1.ne)
    (A := log (2 - X)) (by congr 1; ring)
  have lK := dK.log hK.ne'
  have lN := dN.log hN.ne'
  have l1 := d1.log h1X.ne'
  have l2 := d2.log h2X.ne'
  have e : formXDil = fun x => Li₂ (1 / formXK x) + Li₂ ((1 - x) ^ 2) + Li₂ (formXN x) -
      Li₂ (formXN x / formXK x) - Li₂ ((1 - x) ^ 2 / formXN x) + Li₂ ((1 - x) / formXN x) +
      Li₂ (1 / (2 - x)) - Li₂ ((1 - x) / formXK x) - Li₂ ((1 - x) / (2 - x)) +
      Li₂ ((1 - x) ^ 2 / formXK x) - 2 * Li₂ (1 - x) - 4 * Li₂ (x - 1) - 2 * Li₂ 1 +
      log (formXK x) * log (formXN x) - log (1 - x) * log (formXK x) -
      log (1 - x) * log (2 - x) := rfl
  rw [e]
  have big := ((((((((((((((t1.add t2).add t5).sub t4).sub t6).add t7).add t8).sub t9).sub
    t10).add t11).sub (t3.const_mul 2)).sub (t12.const_mul 4)).sub (hasDerivAt_const X (2 * Li₂
    1))).add (lK.mul lN)).sub (l1.mul lK)).sub (l1.mul l2)
  refine big.congr_deriv ?_
  have n1 : 1 - X ≠ 0 := h1X.ne'
  have n2 : 2 - X ≠ 0 := h2X.ne'
  have n3 : X - 1 ≠ 0 := by linarith
  have n4 : X ≠ 0 := hX0.ne'
  have n5 := hK.ne'
  have n6 := hN.ne'
  field_simp
  unfold formXK formXN
  ring


theorem continuousOn_formXDil : ContinuousOn formXDil (Icc 0 (1 / 2)) := by
  have Kp := formXK_pos
  have Np := formXN_pos
  have cK : Continuous formXK := by unfold formXK; fun_prop
  have cN : Continuous formXN := by unfold formXN; fun_prop
  have cLi : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 0 (1 / 2)) →
      (∀ x ∈ Icc (0 : ℝ) (1 / 2), -1 ≤ f x ∧ f x ≤ 1) →
      ContinuousOn (fun x => Li₂ (f x)) (Icc 0 (1 / 2)) := fun hf hm =>
    continuousOn_Li₂.comp hf fun x hx => hm x hx
  have dv : ∀ {f g : ℝ → ℝ}, Continuous f → Continuous g →
      (∀ x ∈ Icc (0 : ℝ) (1 / 2), 0 ≤ f x ∧ f x ≤ g x) →
      (∀ x ∈ Icc (0 : ℝ) (1 / 2), 0 < g x) →
      ContinuousOn (fun x => Li₂ (f x / g x)) (Icc 0 (1 / 2)) := fun hf hg hm hg0 =>
    cLi (hf.continuousOn.div hg.continuousOn fun x hx => (hg0 x hx).ne') fun x hx =>
      ⟨by have := div_nonneg (hm x hx).1 (hg0 x hx).le; linarith,
        (div_le_one (hg0 x hx)).2 (hm x hx).2⟩
  have hK1 : ∀ x ∈ Icc (0 : ℝ) (1 / 2), 1 ≤ formXK x := fun x hx => by
    unfold formXK; nlinarith [hx.2]
  have hN1 : ∀ x ∈ Icc (0 : ℝ) (1 / 2), (1 - x) ≤ formXN x := fun x hx => by
    unfold formXN; nlinarith [hx.1]
  have c1 := dv (f := fun _ => 1) (g := formXK) continuous_const cK
    (fun x hx => ⟨zero_le_one, hK1 x hx⟩) fun x _ => Kp x
  have c2 := cLi (f := fun x => (1 - x) ^ 2) (by fun_prop) fun x hx =>
    ⟨by nlinarith, by nlinarith [hx.1, hx.2]⟩
  have c3 := cLi (f := formXN) cN.continuousOn fun x hx =>
    ⟨by linarith [Np x], by unfold formXN; nlinarith [hx.1, hx.2]⟩
  have c4 := dv (f := formXN) (g := formXK) cN cK
    (fun x hx => ⟨(Np x).le, by unfold formXN formXK; linarith [hx.2]⟩) fun x _ => Kp x
  have c5 := dv (f := fun x => (1 - x) ^ 2) (g := formXN) (by fun_prop) cN
    (fun x hx => ⟨by positivity, by unfold formXN; nlinarith [hx.1]⟩) fun x _ => Np x
  have c6 := dv (f := fun x => 1 - x) (g := formXN) (by fun_prop) cN
    (fun x hx => ⟨by linarith [hx.2], hN1 x hx⟩) fun x _ => Np x
  have c7 := dv (f := fun _ => 1) (g := fun x => 2 - x) continuous_const (by fun_prop)
    (fun x hx => ⟨zero_le_one, by linarith [hx.2]⟩) fun x hx => by linarith [hx.2]
  have c8 := dv (f := fun x => 1 - x) (g := formXK) (by fun_prop) cK
    (fun x hx => ⟨by linarith [hx.2], by linarith [hK1 x hx, hx.1]⟩) fun x _ => Kp x
  have c9 := dv (f := fun x => 1 - x) (g := fun x => 2 - x) (by fun_prop) (by fun_prop)
    (fun x hx => ⟨by linarith [hx.2], by linarith⟩) fun x hx => by linarith [hx.2]
  have c10 := dv (f := fun x => (1 - x) ^ 2) (g := formXK) (by fun_prop) cK
    (fun x hx => ⟨by positivity, by unfold formXK; nlinarith [hx.1]⟩) fun x _ => Kp x
  have c11 := cLi (f := fun x => 1 - x) (by fun_prop) fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have c12 := cLi (f := fun x => x - 1) (by fun_prop) fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have lK : ContinuousOn (fun x => log (formXK x)) (Icc 0 (1 / 2)) :=
    continuousOn_log.comp cK.continuousOn fun x _ => (Kp x).ne'
  have lN : ContinuousOn (fun x => log (formXN x)) (Icc 0 (1 / 2)) :=
    continuousOn_log.comp cN.continuousOn fun x _ => (Np x).ne'
  have l1 : ContinuousOn (fun x : ℝ => log (1 - x)) (Icc 0 (1 / 2)) :=
    continuousOn_log.comp (by fun_prop) fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.2]
  have l2 : ContinuousOn (fun x : ℝ => log (2 - x)) (Icc 0 (1 / 2)) :=
    continuousOn_log.comp (by fun_prop) fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.2]
  exact ((((((((((((((c1.add c2).add c3).sub c4).sub c5).add c6).add c7).sub c8).sub c9).add
    c10).sub (continuousOn_const.mul c11)).sub (continuousOn_const.mul c12)).sub
    continuousOn_const).add (lK.mul lN)).sub (l1.mul lK)).sub (l1.mul l2)

theorem formXDil_zero : formXDil 0 = 0 := by
  simp only [formXDil, formXK, formXN, Li₂_one]
  norm_num
  rw [Li₂_neg_one]
  ring

/-- **The dilogarithm identity**: `formXDil` vanishes on `(0, 1)`. -/
theorem formXDil_eq_zero (hX : X ∈ Ioo (0 : ℝ) 1) : formXDil X = 0 := by
  have hlim : Tendsto formXDil (𝓝[>] 0) (𝓝 0) := by
    have h := (continuousOn_formXDil 0 ⟨le_rfl, by norm_num⟩).tendsto
    rw [formXDil_zero] at h
    exact h.mono_left (nhdsWithin_le_of_mem
      (mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)) Ioo_subset_Icc_self))
  exact eq_of_hasDerivAt_zero_of_tendsto zero_lt_one (fun x hx => hasDerivAt_formXDil hx) hlim X hX

end

end QED.ChainProof.SetCK

end
