/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValFourWu
import QED.ThreeLoopD.SetDMastersI15KValFourWVBase
import QED.Polylog.HPLAlt4Rel
import QED.Polylog.HPLLiHalf
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues3
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValuesAlt4
import QED.Polylog.HPLValuesTrailing
import QED.Polylog.LiN

/-!
# Set (d), master `I₁₅`: ratio endpoint comparison

The parameter derivative and the collapsed alphabet at the right endpoint
determine the HPL expansion of each moving word.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL
open QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

private noncomputable def wvEval (L : List (ℝ × List Letter)) (r : ℝ) : ℝ :=
  (L.map fun t => t.1 * hpl t.2 r).sum

private noncomputable def wvRate (r : ℝ) : List (ℝ × List Letter) → ℝ
  | [] => 0
  | (_, []) :: L => wvRate r L
  | (c, b :: w) :: L => c * (b.kernel r * hpl w r) + wvRate r L

private theorem wv_deriv (L : List (ℝ × List Letter)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => (L.map fun t => t.1 * hpl t.2 x).sum) (wvRate r L) r := by
  induction L with
  | nil => exact hasDerivAt_const r 0
  | cons t L ih =>
    obtain ⟨c, w⟩ := t
    cases w with
    | nil =>
      simp only [List.map_cons, List.sum_cons, hpl_nil, mul_one, wvRate]
      exact ih.const_add c
    | cons b w =>
      exact ((hasDerivAt_hpl_cons b w hr).const_mul c).add ih

private theorem wv_eq {w : List Letter} (L : List (ℝ × List Letter)) (c : ℝ)
    (hc : hpl (w.map i15WuCollapse) 1 - (L.map fun t => t.1 * hplReg t.2).sum = c)
    (hd : ∀ r ∈ Ioo (0 : ℝ) 1, wvRate r L = i15WuTransport r w 1)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    i15FourWord (i15WuOffsets r) w 1 = c + wvEval L r := by
  have h := i15WV_eq_of_hasDerivAt_of_tendsto L
    (fun _ h => hasDerivAt_i15WuWord_transport h ⟨zero_lt_one, le_rfl⟩ w)
    (fun r h => (wv_deriv L h).congr_deriv (hd r h))
    (tendsto_i15WuWord_one w) hr
  rw [hc] at h
  exact h

@[local simp] private theorem wv_empty (r : ℝ) :
    i15FourWord (i15WuOffsets r) [] 1 = 1 := rfl

attribute [local simp] wvEval wvRate i15WuTransport i15WuUpper_at_one i15WuBoundary
  i15WuLower_kernel i15WuContact_kernel_at_one i15FourEval List.map_cons List.map_nil
  List.sum_cons List.sum_nil List.nil_append List.cons_append hpl_nil

attribute [local simp] List.map_cons List.map_nil List.sum_cons List.sum_nil
  i15WuCollapse hpl_nil

    local macro "wv_step" hr:ident : tactic =>
  `(tactic| refine wv_eq _ _
    (by simp [i15WuCollapse]; try ring)
    (by
      intro r hs
      simp (disch := assumption) [i15WuUpper_at_one hs.1, i15WuLower_kernel hs.1,
        i15WuContact_kernel_at_one hs]
      try ring) $hr)

local macro "wv_word " name:ident w:term " := " c:term " with " L:term : command =>
  `(command| @[local simp] private theorem $name {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    i15FourWord (i15WuOffsets r) $w 1 = $c + wvEval $L r := by wv_step hr)

@[local simp] private theorem reg_wm : hplReg [negOne] = log 2 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_at_one]
@[local simp] private theorem reg_wz : hplReg [zero] = 0 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_at_one]
@[local simp] private theorem reg_wp : hplReg [one] = 0 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil]
@[local simp] private theorem reg_wmm : hplReg [negOne, negOne] = log 2 ^ 2 / 2 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_at_one]
@[local simp] private theorem reg_wmz : hplReg [negOne, zero] = -π ^ 2 / 12 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_at_one]
@[local simp] private theorem reg_wmp : hplReg [negOne, one] = -log 2 ^ 2 / 2 + π ^ 2 / 12 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_one_at_one]
  ring
@[local simp] private theorem reg_wzm : hplReg [zero, negOne] = π ^ 2 / 12 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_at_one]
@[local simp] private theorem reg_wzz : hplReg [zero, zero] = 0 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_at_one]
@[local simp] private theorem reg_wzp : hplReg [zero, one] = π ^ 2 / 6 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_one_at_one]
@[local simp] private theorem reg_wpm : hplReg [one, negOne] = log 2 ^ 2 / 2 - π ^ 2 / 12 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_one_at_one]
@[local simp] private theorem reg_wpz : hplReg [one, zero] = -π ^ 2 / 6 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_one_at_one]; ring
@[local simp] private theorem reg_wpp : hplReg [one, one] = 0 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil]
@[local simp] private theorem reg_wmmm : hplReg [negOne, negOne, negOne] = log 2 ^ 3 / 6 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_negOne_at_one]
@[local simp] private theorem reg_wmmz :
  hplReg [negOne, negOne, zero] = -log 2 * π ^ 2 / 12 + zeta3 / 8 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wmzm :
  hplReg [negOne, zero, negOne] = log 2 * π ^ 2 / 12 - zeta3 / 4 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wmzz : hplReg [negOne, zero, zero] = 3 * zeta3 / 4 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_zero_at_one]
  ring
@[local simp] private theorem reg_wmpz :
  hplReg [negOne, one, zero] = log 2 * π ^ 2 / 12 - zeta3 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_one_zero_at_one]
  ring
@[local simp] private theorem reg_wzmm : hplReg [zero, negOne, negOne] = zeta3 / 8 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_negOne_at_one]
@[local simp] private theorem reg_wzmz : hplReg [zero, negOne, zero] = -3 * zeta3 / 2 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wzzm : hplReg [zero, zero, negOne] = 3 * zeta3 / 4 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wzzz : hplReg [zero, zero, zero] = 0 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_zero_at_one]
@[local simp] private theorem reg_wzpz : hplReg [zero, one, zero] = -2 * zeta3 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_one_zero_at_one]
@[local simp] private theorem reg_wpmz :
  hplReg [one, negOne, zero] = -log 2 * π ^ 2 / 4 + 13 * zeta3 / 8 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one]; ring
@[local simp] private theorem reg_wpzm : hplReg [one, zero, negOne] = -5 * zeta3 / 8 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_negOne_one_at_one, hpl_zero_one_negOne_at_one]; ring
@[local simp] private theorem reg_wpzz : hplReg [one, zero, zero] = zeta3 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one]; ring
@[local simp] private theorem reg_wppz : hplReg [one, one, zero] = zeta3 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_one_one_at_one]; ring
@[local simp] private theorem reg_wmmmm :
  hplReg [negOne, negOne, negOne, negOne] = log 2 ^ 4 / 24 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_negOne_negOne_at_one]
  ring
@[local simp] private theorem reg_wmmmz :
  hplReg [negOne, negOne, negOne, zero] = Li 4 (1 / 2) + log 2 ^ 4 / 24 - log 2 ^ 2 * π ^ 2 / 12 +
  log 2 * zeta3 - π ^ 4 / 90 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wmmzm :
  hplReg [negOne, negOne, zero, negOne] = -3 * Li 4 (1 / 2) - log 2 ^ 4 / 8 + log 2 ^ 2 * π ^ 2 / 6
  - 23 * log 2 * zeta3 / 8 + π ^ 4 / 30 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wmmzz :
  hplReg [negOne, negOne, zero, zero] = -2 * Li 4 (1 / 2) - log 2 ^ 4 / 12 + log 2 ^ 2 * π ^ 2 / 12
  - log 2 * zeta3 + π ^ 4 / 48 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_zero_zero_at_one]
  ring
@[local simp] private theorem reg_wmmpz :
  hplReg [negOne, negOne, one, zero] = 2 * Li 4 (1 / 2) + log 2 ^ 4 / 12 - log 2 ^ 2 * π ^ 2 / 24 +
  13 * log 2 * zeta3 / 8 - 7 * π ^ 4 / 288 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_negOne_one_zero_at_one]
  ring
@[local simp] private theorem reg_wmzmm :
  hplReg [negOne, zero, negOne, negOne] = 3 * Li 4 (1 / 2) + log 2 ^ 4 / 8 - log 2 ^ 2 * π ^ 2 / 8
  + 11 * log 2 * zeta3 / 4 - π ^ 4 / 30 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_negOne_negOne_at_one]
  ring
@[local simp] private theorem reg_wmzmz :
  hplReg [negOne, zero, negOne, zero] = 4 * Li 4 (1 / 2) + log 2 ^ 4 / 6 - log 2 ^ 2 * π ^ 2 / 6 +
  2 * log 2 * zeta3 - 11 * π ^ 4 / 288 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wmzzm :
  hplReg [negOne, zero, zero, negOne] = 3 * log 2 * zeta3 / 4 - π ^ 4 / 288 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wmzzz : hplReg [negOne, zero, zero, zero] = -7 * π ^ 4 / 720 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_zero_zero_at_one]
  ring
@[local simp] private theorem reg_wmzpz :
  hplReg [negOne, zero, one, zero] = 4 * Li 4 (1 / 2) + log 2 ^ 4 / 6 - log 2 ^ 2 * π ^ 2 / 6 + 3 *
  log 2 * zeta3 / 2 - 17 * π ^ 4 / 480 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_zero_one_zero_at_one]
  ring
@[local simp] private theorem reg_wmpmz :
  hplReg [negOne, one, negOne, zero] = log 2 ^ 2 * π ^ 2 / 24 - log 2 * zeta3 + π ^ 4 / 360 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_one_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wmpzm :
  hplReg [negOne, one, zero, negOne] = -4 * Li 4 (1 / 2) - log 2 ^ 4 / 6 + log 2 ^ 2 * π ^ 2 / 8 -
  13 * log 2 * zeta3 / 4 + 11 * π ^ 4 / 240 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_one_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wmpzz :
  hplReg [negOne, one, zero, zero] = -3 * log 2 * zeta3 / 4 + 19 * π ^ 4 / 1440 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_one_zero_zero_at_one]
  ring
@[local simp] private theorem reg_wmppz :
  hplReg [negOne, one, one, zero] = -Li 4 (1 / 2) - log 2 ^ 4 / 24 + log 2 * zeta3 / 8 - π ^ 4 /
  720 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_negOne_one_one_zero_at_one]
  ring
@[local simp] private theorem reg_wzmmm :
  hplReg [zero, negOne, negOne, negOne] = -Li 4 (1 / 2) - log 2 ^ 4 / 24 + log 2 ^ 2 * π ^ 2 / 24 -
  7 * log 2 * zeta3 / 8 + π ^ 4 / 90 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_negOne_negOne_at_one]
  ring
@[local simp] private theorem reg_wzmmz : hplReg [zero, negOne, negOne, zero] = -π ^ 4 / 288 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wzmzm :
  hplReg [zero, negOne, zero, negOne] = -4 * Li 4 (1 / 2) - log 2 ^ 4 / 6 + log 2 ^ 2 * π ^ 2 / 6 -
  7 * log 2 * zeta3 / 2 + 13 * π ^ 4 / 288 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wzmzz : hplReg [zero, negOne, zero, zero] = 7 * π ^ 4 / 240 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_zero_zero_at_one]
  ring
@[local simp] private theorem reg_wzmpz :
  hplReg [zero, negOne, one, zero] = -4 * Li 4 (1 / 2) - log 2 ^ 4 / 6 + log 2 ^ 2 * π ^ 2 / 6 + 13
  * π ^ 4 / 1440 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_negOne_one_zero_at_one]
  ring
@[local simp] private theorem reg_wzzmm :
  hplReg [zero, zero, negOne, negOne] = 2 * Li 4 (1 / 2) + log 2 ^ 4 / 12 - log 2 ^ 2 * π ^ 2 / 12
  + 7 * log 2 * zeta3 / 4 - π ^ 4 / 48 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_negOne_negOne_at_one]
  ring
@[local simp] private theorem reg_wzzmz : hplReg [zero, zero, negOne, zero] = -7 * π ^ 4 / 240 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wzzzm : hplReg [zero, zero, zero, negOne] = 7 * π ^ 4 / 720 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wzzzz : hplReg [zero, zero, zero, zero] = 0 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_zero_zero_at_one]
@[local simp] private theorem reg_wzzpz : hplReg [zero, zero, one, zero] = -π ^ 4 / 30 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_zero_one_zero_at_one]
@[local simp] private theorem reg_wzpmz :
  hplReg [zero, one, negOne, zero] = 4 * Li 4 (1 / 2) + log 2 ^ 4 / 6 - log 2 ^ 2 * π ^ 2 / 6 - 11
  * π ^ 4 / 480 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_one_negOne_zero_at_one]
  ring
@[local simp] private theorem reg_wzpzm :
  hplReg [zero, one, zero, negOne] = -4 * Li 4 (1 / 2) - log 2 ^ 4 / 6 + log 2 ^ 2 * π ^ 2 / 6 - 7
  * log 2 * zeta3 / 2 + 71 * π ^ 4 / 1440 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_one_zero_negOne_at_one]
  ring
@[local simp] private theorem reg_wzpzz : hplReg [zero, one, zero, zero] = π ^ 4 / 30 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_one_zero_zero_at_one]
@[local simp] private theorem reg_wzppz : hplReg [zero, one, one, zero] = -π ^ 4 / 72 := by
  rw [hplReg_eq_hpl_one (by decide), hpl_zero_one_one_zero_at_one]
@[local simp] private theorem reg_wpmmz :
  hplReg [one, negOne, negOne, zero] = -2 * Li 4 (1 / 2) - log 2 ^ 4 / 12 - log 2 ^ 2 * π ^ 2 / 12
  + 7 * π ^ 4 / 360 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_negOne_zero_one_at_one, hpl_negOne_negOne_one_zero_at_one,
  hpl_negOne_one_negOne_zero_at_one]; ring
@[local simp] private theorem reg_wpmzm :
  hplReg [one, negOne, zero, negOne] = 4 * Li 4 (1 / 2) + log 2 ^ 4 / 6 - log 2 ^ 2 * π ^ 2 / 8 +
  21 * log 2 * zeta3 / 8 - π ^ 4 / 24 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_zero_negOne_one_at_one, hpl_negOne_zero_one_negOne_at_one,
  hpl_negOne_one_zero_negOne_at_one]; ring
@[local simp] private theorem reg_wpmzz :
  hplReg [one, negOne, zero, zero] = -2 * Li 4 (1 / 2) - log 2 ^ 4 / 12 + log 2 ^ 2 * π ^ 2 / 12 +
  π ^ 4 / 180 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_one_zero_at_one,
  hpl_negOne_one_zero_zero_at_one]; ring
@[local simp] private theorem reg_wpmpz :
  hplReg [one, negOne, one, zero] = 3 * Li 4 (1 / 2) + log 2 ^ 4 / 8 + log 2 ^ 2 * π ^ 2 / 24 - π ^
  4 / 96 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_one_zero_one_at_one, hpl_negOne_one_one_zero_at_one]; ring
@[local simp] private theorem reg_wpzmm : hplReg [one, zero, negOne, negOne] = -π ^ 4 / 480 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_negOne_negOne_one_at_one, hpl_zero_negOne_one_negOne_at_one,
  hpl_zero_one_negOne_negOne_at_one]; ring
@[local simp] private theorem reg_wpzmz : hplReg [one, zero, negOne, zero] = 17 * π ^ 4 / 1440 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
  hpl_zero_one_negOne_zero_at_one]; ring
@[local simp] private theorem reg_wpzzm :
  hplReg [one, zero, zero, negOne] = 2 * Li 4 (1 / 2) + log 2 ^ 4 / 12 - log 2 ^ 2 * π ^ 2 / 12 + 7
  * log 2 * zeta3 / 4 - 11 * π ^ 4 / 360 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_negOne_at_one,
  hpl_zero_one_zero_negOne_at_one]; ring
@[local simp] private theorem reg_wpzzz : hplReg [one, zero, zero, zero] = -π ^ 4 / 90 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
  hpl_zero_one_zero_zero_at_one]; ring
@[local simp] private theorem reg_wpzpz : hplReg [one, zero, one, zero] = 7 * π ^ 4 / 360 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one]; ring
@[local simp] private theorem reg_wppmz :
  hplReg [one, one, negOne, zero] = -3 * Li 4 (1 / 2) - log 2 ^ 4 / 8 + 11 * π ^ 4 / 720 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_negOne_zero_one_one_at_one, hpl_negOne_one_zero_one_at_one,
  hpl_negOne_one_one_zero_at_one]; ring
@[local simp] private theorem reg_wppzm :
  hplReg [one, one, zero, negOne] = Li 4 (1 / 2) + log 2 ^ 4 / 24 - log 2 ^ 2 * π ^ 2 / 24 + 7 *
  log 2 * zeta3 / 8 - π ^ 4 / 288 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_negOne_one_one_at_one, hpl_zero_one_negOne_one_at_one,
  hpl_zero_one_one_negOne_at_one]; ring
@[local simp] private theorem reg_wppzz : hplReg [one, one, zero, zero] = -π ^ 4 / 360 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
  hpl_zero_one_one_zero_at_one]; ring
@[local simp] private theorem reg_wpppz : hplReg [one, one, one, zero] = -π ^ 4 / 90 := by
  norm_num [hplReg, regExpandWord, splitOnes, regExpand, insertOne, shuffle, shuffleAux, evalExp,
  hpl_nil, hpl_zero_one_one_one_at_one]; ring
  attribute [local simp] hpl_negOne_at_one hpl_negOne_negOne_at_one hpl_negOne_negOne_negOne_at_one
  hpl_negOne_negOne_negOne_negOne_at_one hpl_negOne_negOne_negOne_zero_at_one
  hpl_negOne_negOne_zero_at_one hpl_negOne_negOne_zero_negOne_at_one
  hpl_negOne_negOne_zero_zero_at_one hpl_negOne_zero_at_one hpl_negOne_zero_negOne_at_one
  hpl_negOne_zero_negOne_negOne_at_one hpl_negOne_zero_negOne_zero_at_one
  hpl_negOne_zero_zero_at_one hpl_negOne_zero_zero_negOne_at_one hpl_negOne_zero_zero_zero_at_one
  hpl_zero_at_one hpl_zero_negOne_at_one hpl_zero_negOne_negOne_at_one
  hpl_zero_negOne_negOne_negOne_at_one hpl_zero_negOne_negOne_zero_at_one
  hpl_zero_negOne_zero_at_one hpl_zero_negOne_zero_negOne_at_one hpl_zero_negOne_zero_zero_at_one
  hpl_zero_zero_at_one hpl_zero_zero_negOne_at_one hpl_zero_zero_negOne_negOne_at_one
  hpl_zero_zero_negOne_zero_at_one hpl_zero_zero_zero_at_one hpl_zero_zero_zero_negOne_at_one
  hpl_zero_zero_zero_zero_at_one

wv_word wz [zero] := (0) with []
wv_word wp [one] := (0) with [(1, [negOne]), (-1, [zero])]

wv_word wm [negOne] := (0) with [(1, [negOne])]
wv_word wzz [zero, zero] := (0) with []
wv_word wzp [zero, one] := (π ^ 2 / 6) with [(-1, [zero, negOne]), (1, [zero, zero])]
wv_word wzm [zero, negOne] := (0) with [(1, [zero, negOne])]
wv_word wpz [one, zero] := (-π ^ 2 / 6) with [(1, [zero, negOne]), (-1, [zero, zero])]
wv_word wpp [one, one] := (0) with [(1, [negOne, negOne]), (-1, [negOne, zero]), (-1, [zero,
  negOne]), (1, [zero, zero])]

wv_word wpm [one, negOne] := (0) with [(1, [negOne, negOne]), (-1, [negOne, zero]), (1, [zero,
  negOne]), (1, [one, zero])]
wv_word wmz [negOne, zero] := (0) with [(-1, [zero, negOne])]
wv_word wmp [negOne, one] := (0) with [(1, [negOne, negOne]), (-2, [zero, negOne]), (-1, [one,
  zero])]
wv_word wmm [negOne, negOne] := (0) with [(1, [negOne, negOne])]
wv_word wzzz [zero, zero, zero] := (0) with []
wv_word wzzp [zero, zero, one] := (0) with [(-π ^ 2 / 6, [zero]), (1, [zero, zero, negOne]), (-1,
  [zero, zero, zero])]
wv_word wzzm [zero, zero, negOne] := (0) with [(1, [zero, zero, negOne])]
wv_word wzpz [zero, one, zero] := (0) with [(π ^ 2 / 3, [zero]), (-2, [zero, zero, negOne]), (2,
  [zero, zero, zero])]
wv_word wzpp [zero, one, one] := (zeta3) with [(-1, [zero, negOne, negOne]), (1, [zero, negOne,
  zero]), (1, [zero, zero, negOne]), (-1, [zero, zero, zero])]
wv_word wzpm [zero, one, negOne] := (0) with [(π ^ 2 / 6, [negOne]), (-2, [negOne, zero, negOne]),
  (1, [negOne, zero, zero]), (-1, [zero, negOne, negOne]), (1, [zero, negOne, zero]), (1, [zero,
  zero, negOne]), (-1, [zero, one, zero]), (-π ^ 2 / 6, [one]), (2, [one, zero, negOne]), (-1, [one,
  zero, zero])]
wv_word wzmz [zero, negOne, zero] := (0) with [(-2, [zero, zero, negOne])]
wv_word wzmp [zero, negOne, one] := (0) with [(-π ^ 2 / 6, [negOne]), (2, [negOne, zero, negOne]),
  (-1, [negOne, zero, zero]), (1, [zero, negOne, negOne]), (-4, [zero, zero, negOne]), (-1, [zero,
  one, zero]), (π ^ 2 / 6, [one]), (-2, [one, zero, negOne]), (1, [one, zero, zero])]
wv_word wzmm [zero, negOne, negOne] := (0) with [(1, [zero, negOne, negOne])]
wv_word wpzz [one, zero, zero] := (0) with [(-π ^ 2 / 6, [zero]), (1, [zero, zero, negOne]), (-1,
  [zero, zero, zero])]
wv_word wpzp [one, zero, one] := (-2 * zeta3) with [(π ^ 2 / 6, [negOne]), (-1, [negOne, zero,
  negOne]), (1, [negOne, zero, zero]), (-π ^ 2 / 6, [zero]), (1, [zero, zero, negOne]), (-1, [zero,
  zero, zero])]
wv_word wpzm [one, zero, negOne] := (0) with [(1, [negOne, zero, negOne]), (2, [zero, negOne,
  negOne]), (-2, [zero, negOne, zero]), (1, [zero, zero, negOne]), (2, [zero, one, zero])]
wv_word wppz [one, one, zero] := (zeta3) with [(-π ^ 2 / 6, [negOne]), (1, [negOne, zero, negOne]),
  (-1, [negOne, zero, zero]), (π ^ 2 / 6, [zero]), (1, [zero, negOne, negOne]), (-1, [zero, negOne,
  zero]), (-2, [zero, zero, negOne]), (2, [zero, zero, zero])]
wv_word wppp [one, one, one] := (0) with [(1, [negOne, negOne, negOne]), (-1, [negOne, negOne,
  zero]), (-1, [negOne, zero, negOne]), (1, [negOne, zero, zero]), (-1, [zero, negOne, negOne]), (1,
  [zero, negOne, zero]), (1, [zero, zero, negOne]), (-1, [zero, zero, zero])]

wv_word wppm [one, one, negOne] := (0) with [(1, [negOne, negOne, negOne]), (-1, [negOne, negOne,
  zero]), (-1, [negOne, zero, negOne]), (1, [negOne, zero, zero]), (1, [zero, negOne, negOne]), (-1,
  [zero, negOne, zero]), (1, [zero, zero, negOne]), (1, [zero, one, zero]), (2, [one, zero,
  negOne]), (-1, [one, zero, zero]), (1, [one, one, zero])]
wv_word wpmz [one, negOne, zero] := (0) with [(-π ^ 2 / 6, [negOne]), (1, [negOne, zero, negOne]),
  (-1, [negOne, zero, zero]), (-1, [zero, negOne, negOne]), (1, [zero, negOne, zero]), (-2, [zero,
  zero, negOne]), (-1, [zero, one, zero]), (π ^ 2 / 6, [one]), (-2, [one, zero, negOne]), (1, [one,
  zero, zero])]
wv_word wpmp [one, negOne, one] := (0) with [(1, [negOne, negOne, negOne]), (-1, [negOne, negOne,
  zero]), (1, [negOne, zero, negOne]), (1, [negOne, one, zero]), (-1, [zero, negOne, negOne]), (2,
  [zero, negOne, zero]), (-4, [zero, zero, negOne]), (-3, [zero, one, zero]), (1, [one, negOne,
  zero]), (-3, [one, zero, negOne]), (-2, [one, one, zero])]
wv_word wpmm [one, negOne, negOne] := (0) with [(1, [negOne, negOne, negOne]), (-1, [negOne, negOne,
  zero]), (1, [negOne, zero, negOne]), (1, [negOne, one, zero]), (1, [zero, negOne, negOne]), (1,
  [one, negOne, zero]), (-1, [one, zero, negOne]), (-1, [one, one, zero])]
wv_word wmzz [negOne, zero, zero] := (0) with [(1, [zero, zero, negOne])]
wv_word wmzp [negOne, zero, one] := (0) with [(π ^ 2 / 6, [negOne]), (-1, [negOne, zero, negOne]),
  (1, [negOne, zero, zero]), (-2, [zero, negOne, negOne]), (4, [zero, zero, negOne]), (2, [zero,
  one, zero])]
wv_word wmzm [negOne, zero, negOne] := (0) with [(1, [negOne, zero, negOne])]
wv_word wmpz [negOne, one, zero] := (0) with [(-1, [negOne, zero, negOne]), (1, [zero, negOne,
  negOne]), (-1, [zero, one, zero]), (-π ^ 2 / 6, [one]), (2, [one, zero, negOne]), (-1, [one, zero,
  zero])]
wv_word wmpp [negOne, one, one] := (0) with [(1, [negOne, negOne, negOne]), (-2, [negOne, zero,
  negOne]), (-1, [negOne, one, zero]), (-2, [zero, negOne, negOne]), (4, [zero, zero, negOne]), (2,
  [zero, one, zero]), (-1, [one, negOne, zero]), (1, [one, zero, negOne]), (1, [one, zero, zero]),
  (1, [one, one, zero])]
wv_word wmpm [negOne, one, negOne] := (0) with [(1, [negOne, negOne, negOne]), (-2, [negOne, zero,
  negOne]), (-1, [negOne, one, zero]), (-1, [one, negOne, zero]), (3, [one, zero, negOne]), (2,
  [one, one, zero])]
wv_word wmmz [negOne, negOne, zero] := (0) with [(-1, [negOne, zero, negOne]), (-1, [zero, negOne,
  negOne])]
wv_word wmmp [negOne, negOne, one] := (0) with [(1, [negOne, negOne, negOne]), (-2, [zero, negOne,
  negOne]), (-2, [one, zero, negOne]), (-1, [one, one, zero])]
wv_word wmmm [negOne, negOne, negOne] := (0) with [(1, [negOne, negOne, negOne])]
wv_word wzzzz [zero, zero, zero, zero] := (0) with []
wv_word wzzzp [zero, zero, zero, one] := (7 * π ^ 4 / 360) with [(π ^ 2 / 6, [zero, zero]), (-1,
  [zero, zero, zero, negOne]), (1, [zero, zero, zero, zero])]
wv_word wzzzm [zero, zero, zero, negOne] := (0) with [(1, [zero, zero, zero, negOne])]
wv_word wzzpz [zero, zero, one, zero] := (-7 * π ^ 4 / 120) with [(-π ^ 2 / 2, [zero, zero]), (3,
  [zero, zero, zero, negOne]), (-3, [zero, zero, zero, zero])]
wv_word wzzpp [zero, zero, one, one] := (-7 * π ^ 4 / 360) with [(-zeta3, [zero]), (1, [zero, zero,
  negOne, negOne]), (-1, [zero, zero, negOne, zero]), (-1, [zero, zero, zero, negOne]), (1, [zero,
  zero, zero, zero])]
wv_word wzzpm [zero, zero, one, negOne] := (0) with [(-π ^ 2 / 6, [negOne, zero]), (-1, [negOne,
  zero, zero, zero]), (-π ^ 2 / 6, [zero, negOne]), (2, [zero, negOne, zero, negOne]), (-1, [zero,
  negOne, zero, zero]), (1, [zero, zero, negOne, negOne]), (-1, [zero, zero, negOne, zero]), (1,
  [zero, zero, zero, negOne]), (1, [zero, zero, one, zero]), (π ^ 2 / 6, [zero, one]), (-2, [zero,
  one, zero, negOne]), (1, [zero, one, zero, zero]), (π ^ 2 / 6, [one, zero]), (1, [one, zero, zero,
  zero])]
wv_word wzzmz [zero, zero, negOne, zero] := (0) with [(-3, [zero, zero, zero, negOne])]
wv_word wzzmp [zero, zero, negOne, one] := (0) with [(π ^ 2 / 6, [negOne, zero]), (1, [negOne, zero,
  zero, zero]), (-π ^ 2 / 6, [zero, negOne]), (2, [zero, negOne, zero, negOne]), (-1, [zero, negOne,
  zero, zero]), (1, [zero, zero, negOne, negOne]), (-6, [zero, zero, zero, negOne]), (-1, [zero,
  zero, one, zero]), (π ^ 2 / 6, [zero, one]), (-2, [zero, one, zero, negOne]), (1, [zero, one,
  zero, zero]), (-π ^ 2 / 6, [one, zero]), (-1, [one, zero, zero, zero])]
wv_word wzzmm [zero, zero, negOne, negOne] := (0) with [(1, [zero, zero, negOne, negOne])]
wv_word wzpzz [zero, one, zero, zero] := (7 * π ^ 4 / 120) with [(π ^ 2 / 2, [zero, zero]), (-3,
  [zero, zero, zero, negOne]), (3, [zero, zero, zero, zero])]
wv_word wzpzp [zero, one, zero, one] := (19 * π ^ 4 / 360) with [(2 * zeta3, [zero]), (-π ^ 2 / 6,
  [zero, negOne]), (1, [zero, negOne, zero, negOne]), (-1, [zero, negOne, zero, zero]), (π ^ 2 / 6,
  [zero, zero]), (-1, [zero, zero, zero, negOne]), (1, [zero, zero, zero, zero])]
wv_word wzpzm [zero, one, zero, negOne] := (0) with [(π ^ 2 / 3, [zero, negOne]), (-5, [zero,
  negOne, zero, negOne]), (2, [zero, negOne, zero, zero]), (-4, [zero, zero, negOne, negOne]), (4,
  [zero, zero, negOne, zero]), (1, [zero, zero, zero, negOne]), (-4, [zero, zero, one, zero]), (-π ^
  2 / 3, [zero, one]), (4, [zero, one, zero, negOne]), (-2, [zero, one, zero, zero])]
wv_word wzppz [zero, one, one, zero] := (-π ^ 4 / 72) with [(π ^ 2 / 6, [zero, negOne]), (-1, [zero,
  negOne, zero, negOne]), (1, [zero, negOne, zero, zero]), (-π ^ 2 / 6, [zero, zero]), (-2, [zero,
  zero, negOne, negOne]), (2, [zero, zero, negOne, zero]), (3, [zero, zero, zero, negOne]), (-3,
  [zero, zero, zero, zero])]
wv_word wzppp [zero, one, one, one] := (π ^ 4 / 90) with [(-1, [zero, negOne, negOne, negOne]), (1,
  [zero, negOne, negOne, zero]), (1, [zero, negOne, zero, negOne]), (-1, [zero, negOne, zero,
  zero]), (1, [zero, zero, negOne, negOne]), (-1, [zero, zero, negOne, zero]), (-1, [zero, zero,
  zero, negOne]), (1, [zero, zero, zero, zero])]
wv_word wzppm [zero, one, one, negOne] := (0) with [(zeta3, [negOne]), (-π ^ 2 / 6, [negOne,
  negOne]), (2, [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, zero, zero]), (-1, [negOne,
  zero, zero, zero]), (1, [negOne, zero, one, zero]), (π ^ 2 / 6, [negOne, one]), (-2, [negOne, one,
  zero, negOne]), (1, [negOne, one, zero, zero]), (π ^ 2 / 3, [zero, negOne]), (-1, [zero, negOne,
  negOne, negOne]), (1, [zero, negOne, negOne, zero]), (-3, [zero, negOne, zero, negOne]), (1,
  [zero, negOne, zero, zero]), (-3, [zero, zero, negOne, negOne]), (3, [zero, zero, negOne, zero]),
  (1, [zero, zero, zero, negOne]), (-3, [zero, zero, one, zero]), (-π ^ 2 / 3, [zero, one]), (2,
  [zero, one, zero, negOne]), (-1, [zero, one, zero, zero]), (-1, [zero, one, one, zero]), (-zeta3,
  [one]), (π ^ 2 / 6, [one, negOne]), (-2, [one, negOne, zero, negOne]), (1, [one, negOne, zero,
  zero]), (1, [one, zero, zero, zero]), (-1, [one, zero, one, zero]), (-π ^ 2 / 6, [one, one]), (2,
  [one, one, zero, negOne]), (-1, [one, one, zero, zero])]
wv_word wzpmz [zero, one, negOne, zero] := (0) with [(π ^ 2 / 3, [negOne, zero]), (2, [negOne, zero,
  zero, zero]), (1, [zero, negOne, zero, negOne]), (2, [zero, zero, negOne, negOne]), (-2, [zero,
  zero, negOne, zero]), (-3, [zero, zero, zero, negOne]), (2, [zero, zero, one, zero]), (-π ^ 2 / 3,
  [one, zero]), (-2, [one, zero, zero, zero])]
wv_word wzpmp [zero, one, negOne, one] := (0) with [(π ^ 2 / 3, [negOne, negOne]), (-4, [negOne,
  negOne, zero, negOne]), (2, [negOne, negOne, zero, zero]), (-2, [negOne, zero, negOne, negOne]),
  (1, [negOne, zero, negOne, zero]), (5, [negOne, zero, zero, negOne]), (-π ^ 2 / 3, [negOne, one]),
  (4, [negOne, one, zero, negOne]), (-2, [negOne, one, zero, zero]), (-2 * π ^ 2 / 3, [zero,
  negOne]), (-1, [zero, negOne, negOne, negOne]), (1, [zero, negOne, negOne, zero]), (7, [zero,
  negOne, zero, negOne]), (-4, [zero, negOne, zero, zero]), (-1, [zero, negOne, one, zero]), (5,
  [zero, zero, negOne, negOne]), (-4, [zero, zero, negOne, zero]), (-6, [zero, zero, zero, negOne]),
  (3, [zero, zero, one, zero]), (2 * π ^ 2 / 3, [zero, one]), (-1, [zero, one, negOne, zero]), (-5,
  [zero, one, zero, negOne]), (4, [zero, one, zero, zero]), (2, [zero, one, one, zero]), (-π ^ 2 /
  3, [one, negOne]), (4, [one, negOne, zero, negOne]), (-2, [one, negOne, zero, zero]), (2, [one,
  zero, negOne, negOne]), (-1, [one, zero, negOne, zero]), (-5, [one, zero, zero, negOne]), (π ^ 2 /
  3, [one, one]), (-4, [one, one, zero, negOne]), (2, [one, one, zero, zero])]
wv_word wzpmm [zero, one, negOne, negOne] := (0) with [(π ^ 2 / 6, [negOne, negOne]), (-2, [negOne,
  negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]), (-2, [negOne, zero, negOne, negOne]),
  (1, [negOne, zero, negOne, zero]), (1, [negOne, zero, zero, negOne]), (-1, [negOne, zero, one,
  zero]), (-π ^ 2 / 6, [negOne, one]), (2, [negOne, one, zero, negOne]), (-1, [negOne, one, zero,
  zero]), (-1, [zero, negOne, negOne, negOne]), (1, [zero, negOne, negOne, zero]), (-1, [zero,
  negOne, zero, negOne]), (-1, [zero, negOne, one, zero]), (1, [zero, zero, negOne, negOne]), (-1,
  [zero, one, negOne, zero]), (1, [zero, one, zero, negOne]), (1, [zero, one, one, zero]), (-π ^ 2 /
  6, [one, negOne]), (2, [one, negOne, zero, negOne]), (-1, [one, negOne, zero, zero]), (2, [one,
  zero, negOne, negOne]), (-1, [one, zero, negOne, zero]), (-1, [one, zero, zero, negOne]), (1,
  [one, zero, one, zero]), (π ^ 2 / 6, [one, one]), (-2, [one, one, zero, negOne]), (1, [one, one,
  zero, zero])]
wv_word wzmzz [zero, negOne, zero, zero] := (0) with [(3, [zero, zero, zero, negOne])]
wv_word wzmzp [zero, negOne, zero, one] := (0) with [(π ^ 2 / 2, [zero, negOne]), (-5, [zero,
  negOne, zero, negOne]), (3, [zero, negOne, zero, zero]), (-4, [zero, zero, negOne, negOne]), (12,
  [zero, zero, zero, negOne]), (4, [zero, zero, one, zero]), (-π ^ 2 / 3, [zero, one]), (4, [zero,
  one, zero, negOne]), (-2, [zero, one, zero, zero])]
wv_word wzmzm [zero, negOne, zero, negOne] := (0) with [(1, [zero, negOne, zero, negOne])]
wv_word wzmpz [zero, negOne, one, zero] := (0) with [(-π ^ 2 / 3, [negOne, zero]), (-2, [negOne,
  zero, zero, zero]), (-π ^ 2 / 6, [zero, negOne]), (1, [zero, negOne, zero, negOne]), (-1, [zero,
  negOne, zero, zero]), (2, [zero, zero, negOne, negOne]), (-2, [zero, zero, one, zero]), (π ^ 2 /
  3, [one, zero]), (2, [one, zero, zero, zero])]
wv_word wzmpp [zero, negOne, one, one] := (0) with [(-zeta3, [negOne]), (-π ^ 2 / 6, [negOne,
  negOne]), (2, [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, zero, zero]), (2, [negOne,
  zero, negOne, negOne]), (-1, [negOne, zero, negOne, zero]), (-5, [negOne, zero, zero, negOne]),
  (1, [negOne, zero, zero, zero]), (-1, [negOne, zero, one, zero]), (π ^ 2 / 6, [negOne, one]), (-2,
  [negOne, one, zero, negOne]), (1, [negOne, one, zero, zero]), (π ^ 2 / 3, [zero, negOne]), (1,
  [zero, negOne, negOne, negOne]), (-6, [zero, negOne, zero, negOne]), (2, [zero, negOne, zero,
  zero]), (-1, [zero, negOne, one, zero]), (-4, [zero, zero, negOne, negOne]), (12, [zero, zero,
  zero, negOne]), (4, [zero, zero, one, zero]), (-π ^ 2 / 3, [zero, one]), (-1, [zero, one, negOne,
  zero]), (5, [zero, one, zero, negOne]), (-1, [zero, one, zero, zero]), (1, [zero, one, one,
  zero]), (zeta3, [one]), (π ^ 2 / 6, [one, negOne]), (-2, [one, negOne, zero, negOne]), (1, [one,
  negOne, zero, zero]), (-2, [one, zero, negOne, negOne]), (1, [one, zero, negOne, zero]), (5, [one,
  zero, zero, negOne]), (-1, [one, zero, zero, zero]), (1, [one, zero, one, zero]), (-π ^ 2 / 6,
  [one, one]), (2, [one, one, zero, negOne]), (-1, [one, one, zero, zero])]
wv_word wzmpm [zero, negOne, one, negOne] := (0) with [(-π ^ 2 / 3, [negOne, negOne]), (4, [negOne,
  negOne, zero, negOne]), (-2, [negOne, negOne, zero, zero]), (2, [negOne, zero, negOne, negOne]),
  (-1, [negOne, zero, negOne, zero]), (-5, [negOne, zero, zero, negOne]), (π ^ 2 / 3, [negOne,
  one]), (-4, [negOne, one, zero, negOne]), (2, [negOne, one, zero, zero]), (1, [zero, negOne,
  negOne, negOne]), (-2, [zero, negOne, zero, negOne]), (-1, [zero, negOne, one, zero]), (-1, [zero,
  one, negOne, zero]), (3, [zero, one, zero, negOne]), (2, [zero, one, one, zero]), (π ^ 2 / 3,
  [one, negOne]), (-4, [one, negOne, zero, negOne]), (2, [one, negOne, zero, zero]), (-2, [one,
  zero, negOne, negOne]), (1, [one, zero, negOne, zero]), (5, [one, zero, zero, negOne]), (-π ^ 2 /
  3, [one, one]), (4, [one, one, zero, negOne]), (-2, [one, one, zero, zero])]
wv_word wzmmz [zero, negOne, negOne, zero] := (0) with [(-1, [zero, negOne, zero, negOne]), (-2,
  [zero, zero, negOne, negOne])]
wv_word wzmmp [zero, negOne, negOne, one] := (0) with [(π ^ 2 / 6, [negOne, negOne]), (-2, [negOne,
  negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]), (4, [negOne, zero, zero, negOne]), (1,
  [negOne, zero, one, zero]), (-π ^ 2 / 6, [negOne, one]), (2, [negOne, one, zero, negOne]), (-1,
  [negOne, one, zero, zero]), (1, [zero, negOne, negOne, negOne]), (-4, [zero, zero, negOne,
  negOne]), (-2, [zero, one, zero, negOne]), (-1, [zero, one, one, zero]), (-π ^ 2 / 6, [one,
  negOne]), (2, [one, negOne, zero, negOne]), (-1, [one, negOne, zero, zero]), (-4, [one, zero,
  zero, negOne]), (-1, [one, zero, one, zero]), (π ^ 2 / 6, [one, one]), (-2, [one, one, zero,
  negOne]), (1, [one, one, zero, zero])]
wv_word wzmmm [zero, negOne, negOne, negOne] := (0) with [(1, [zero, negOne, negOne, negOne])]
wv_word wpzzz [one, zero, zero, zero] := (-7 * π ^ 4 / 360) with [(-π ^ 2 / 6, [zero, zero]), (1,
  [zero, zero, zero, negOne]), (-1, [zero, zero, zero, zero])]
wv_word wpzzp [one, zero, zero, one] := (-π ^ 4 / 72) with [(-π ^ 2 / 6, [negOne, zero]), (1,
  [negOne, zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (π ^ 2 / 6, [zero, zero]), (-1,
  [zero, zero, zero, negOne]), (1, [zero, zero, zero, zero])]
wv_word wpzzm [one, zero, zero, negOne] := (0) with [(1, [negOne, zero, zero, negOne]), (2, [zero,
  negOne, zero, negOne]), (4, [zero, zero, negOne, negOne]), (-4, [zero, zero, negOne, zero]), (1,
  [zero, zero, zero, negOne]), (4, [zero, zero, one, zero])]
wv_word wpzpz [one, zero, one, zero] := (-π ^ 4 / 40) with [(π ^ 2 / 3, [negOne, zero]), (-2,
  [negOne, zero, zero, negOne]), (2, [negOne, zero, zero, zero]), (-2 * zeta3, [zero]), (π ^ 2 / 6,
  [zero, negOne]), (-1, [zero, negOne, zero, negOne]), (1, [zero, negOne, zero, zero]), (-π ^ 2 / 2,
  [zero, zero]), (3, [zero, zero, zero, negOne]), (-3, [zero, zero, zero, zero])]
wv_word wpzpp [one, zero, one, one] := (-π ^ 4 / 30) with [(zeta3, [negOne]), (-1, [negOne, zero,
  negOne, negOne]), (1, [negOne, zero, negOne, zero]), (1, [negOne, zero, zero, negOne]), (-1,
  [negOne, zero, zero, zero]), (-zeta3, [zero]), (1, [zero, zero, negOne, negOne]), (-1, [zero,
  zero, negOne, zero]), (-1, [zero, zero, zero, negOne]), (1, [zero, zero, zero, zero])]
wv_word wpzpm [one, zero, one, negOne] := (0) with [(-2 * zeta3, [negOne]), (π ^ 2 / 3, [negOne,
  negOne]), (-4, [negOne, negOne, zero, negOne]), (2, [negOne, negOne, zero, zero]), (-π ^ 2 / 6,
  [negOne, zero]), (-3, [negOne, zero, negOne, negOne]), (3, [negOne, zero, negOne, zero]), (1,
  [negOne, zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (-3, [negOne, zero, one, zero]),
  (-π ^ 2 / 6, [negOne, one]), (2, [negOne, one, zero, negOne]), (-1, [negOne, one, zero, zero]),
  (-π ^ 2 / 6, [zero, negOne]), (4, [zero, negOne, zero, negOne]), (-1, [zero, negOne, zero, zero]),
  (5, [zero, zero, negOne, negOne]), (-5, [zero, zero, negOne, zero]), (1, [zero, zero, zero,
  negOne]), (5, [zero, zero, one, zero]), (π ^ 2 / 6, [zero, one]), (-2, [zero, one, zero, negOne]),
  (1, [zero, one, zero, zero]), (2 * zeta3, [one]), (-π ^ 2 / 6, [one, negOne]), (2, [one, negOne,
  zero, negOne]), (-1, [one, negOne, zero, zero]), (π ^ 2 / 6, [one, zero]), (2, [one, zero, negOne,
  negOne]), (-2, [one, zero, negOne, zero]), (1, [one, zero, zero, zero]), (2, [one, zero, one,
  zero])]
wv_word wpzmz [one, zero, negOne, zero] := (0) with [(-2, [negOne, zero, zero, negOne]), (-π ^ 2 /
  3, [zero, negOne]), (1, [zero, negOne, zero, negOne]), (-2, [zero, negOne, zero, zero]), (-4,
  [zero, zero, negOne, negOne]), (4, [zero, zero, negOne, zero]), (-3, [zero, zero, zero, negOne]),
  (-4, [zero, zero, one, zero]), (π ^ 2 / 3, [zero, one]), (-4, [zero, one, zero, negOne]), (2,
  [zero, one, zero, zero])]
wv_word wpzmp [one, zero, negOne, one] := (0) with [(2 * zeta3, [negOne]), (-π ^ 2 / 3, [negOne,
  negOne]), (4, [negOne, negOne, zero, negOne]), (-2, [negOne, negOne, zero, zero]), (π ^ 2 / 6,
  [negOne, zero]), (3, [negOne, zero, negOne, negOne]), (-2, [negOne, zero, negOne, zero]), (-4,
  [negOne, zero, zero, negOne]), (1, [negOne, zero, zero, zero]), (1, [negOne, zero, one, zero]), (π
  ^ 2 / 6, [negOne, one]), (-2, [negOne, one, zero, negOne]), (1, [negOne, one, zero, zero]), (π ^ 2
  / 6, [zero, negOne]), (2, [zero, negOne, negOne, negOne]), (-2, [zero, negOne, negOne, zero]),
  (-2, [zero, negOne, zero, negOne]), (1, [zero, negOne, zero, zero]), (2, [zero, negOne, one,
  zero]), (-7, [zero, zero, negOne, negOne]), (8, [zero, zero, negOne, zero]), (-6, [zero, zero,
  zero, negOne]), (-9, [zero, zero, one, zero]), (-π ^ 2 / 6, [zero, one]), (2, [zero, one, negOne,
  zero]), (-4, [zero, one, zero, negOne]), (-1, [zero, one, zero, zero]), (-4, [zero, one, one,
  zero]), (-2 * zeta3, [one]), (π ^ 2 / 6, [one, negOne]), (-2, [one, negOne, zero, negOne]), (1,
  [one, negOne, zero, zero]), (-π ^ 2 / 6, [one, zero]), (-2, [one, zero, negOne, negOne]), (2,
  [one, zero, negOne, zero]), (-1, [one, zero, zero, zero]), (-2, [one, zero, one, zero])]
wv_word wpzmm [one, zero, negOne, negOne] := (0) with [(1, [negOne, zero, negOne, negOne]), (2,
  [zero, negOne, negOne, negOne]), (-2, [zero, negOne, negOne, zero]), (2, [zero, negOne, zero,
  negOne]), (2, [zero, negOne, one, zero]), (1, [zero, zero, negOne, negOne]), (2, [zero, one,
  negOne, zero]), (-2, [zero, one, zero, negOne]), (-2, [zero, one, one, zero])]
wv_word wppzz [one, one, zero, zero] := (7 * π ^ 4 / 360) with [(-π ^ 2 / 6, [negOne, zero]), (1,
  [negOne, zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (zeta3, [zero]), (-π ^ 2 / 6,
  [zero, negOne]), (1, [zero, negOne, zero, negOne]), (-1, [zero, negOne, zero, zero]), (π ^ 2 / 3,
  [zero, zero]), (1, [zero, zero, negOne, negOne]), (-1, [zero, zero, negOne, zero]), (-3, [zero,
  zero, zero, negOne]), (3, [zero, zero, zero, zero])]
wv_word wppzp [one, one, zero, one] := (π ^ 4 / 30) with [(-2 * zeta3, [negOne]), (π ^ 2 / 6,
  [negOne, negOne]), (-1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]), (-π ^
  2 / 6, [negOne, zero]), (1, [negOne, zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (2 *
  zeta3, [zero]), (-π ^ 2 / 6, [zero, negOne]), (1, [zero, negOne, zero, negOne]), (-1, [zero,
  negOne, zero, zero]), (π ^ 2 / 6, [zero, zero]), (-1, [zero, zero, zero, negOne]), (1, [zero,
  zero, zero, zero])]
wv_word wppzm [one, one, zero, negOne] := (0) with [(1, [negOne, negOne, zero, negOne]), (2,
  [negOne, zero, negOne, negOne]), (-2, [negOne, zero, negOne, zero]), (1, [negOne, zero, zero,
  negOne]), (2, [negOne, zero, one, zero]), (2, [zero, negOne, negOne, negOne]), (-2, [zero, negOne,
  negOne, zero]), (-3, [zero, negOne, zero, negOne]), (2, [zero, negOne, zero, zero]), (1, [zero,
  zero, zero, negOne]), (4, [zero, one, zero, negOne]), (-2, [zero, one, zero, zero]), (2, [zero,
  one, one, zero])]
wv_word wpppz [one, one, one, zero] := (-π ^ 4 / 90) with [(zeta3, [negOne]), (-π ^ 2 / 6, [negOne,
  negOne]), (1, [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, zero, zero]), (π ^ 2 / 6,
  [negOne, zero]), (1, [negOne, zero, negOne, negOne]), (-1, [negOne, zero, negOne, zero]), (-2,
  [negOne, zero, zero, negOne]), (2, [negOne, zero, zero, zero]), (-zeta3, [zero]), (π ^ 2 / 6,
  [zero, negOne]), (1, [zero, negOne, negOne, negOne]), (-1, [zero, negOne, negOne, zero]), (-2,
  [zero, negOne, zero, negOne]), (2, [zero, negOne, zero, zero]), (-π ^ 2 / 6, [zero, zero]), (-2,
  [zero, zero, negOne, negOne]), (2, [zero, zero, negOne, zero]), (3, [zero, zero, zero, negOne]),
  (-3, [zero, zero, zero, zero])]
wv_word wpppp [one, one, one, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1, [negOne,
  negOne, negOne, zero]), (-1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]),
  (-1, [negOne, zero, negOne, negOne]), (1, [negOne, zero, negOne, zero]), (1, [negOne, zero, zero,
  negOne]), (-1, [negOne, zero, zero, zero]), (-1, [zero, negOne, negOne, negOne]), (1, [zero,
  negOne, negOne, zero]), (1, [zero, negOne, zero, negOne]), (-1, [zero, negOne, zero, zero]), (1,
  [zero, zero, negOne, negOne]), (-1, [zero, zero, negOne, zero]), (-1, [zero, zero, zero, negOne]),
  (1, [zero, zero, zero, zero])]

wv_word wpppm [one, one, one, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (-1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, zero,
  zero]), (-1, [negOne, zero, negOne, negOne]), (1, [negOne, zero, negOne, zero]), (1, [negOne,
  zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (1, [zero, negOne, negOne, negOne]), (-1,
  [zero, negOne, negOne, zero]), (-1, [zero, negOne, zero, negOne]), (1, [zero, negOne, zero,
  zero]), (1, [zero, zero, negOne, negOne]), (-1, [zero, zero, negOne, zero]), (1, [zero, zero,
  zero, negOne]), (1, [zero, zero, one, zero]), (2, [zero, one, zero, negOne]), (-1, [zero, one,
  zero, zero]), (1, [zero, one, one, zero]), (2, [one, zero, negOne, negOne]), (-2, [one, zero,
  negOne, zero]), (1, [one, zero, zero, zero]), (1, [one, zero, one, zero]), (2, [one, one, zero,
  negOne]), (-1, [one, one, zero, zero]), (1, [one, one, one, zero])]
wv_word wppmz [one, one, negOne, zero] := (0) with [(zeta3, [negOne]), (-π ^ 2 / 6, [negOne,
  negOne]), (1, [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, zero, zero]), (π ^ 2 / 6,
  [negOne, zero]), (1, [negOne, zero, negOne, negOne]), (-1, [negOne, zero, negOne, zero]), (-2,
  [negOne, zero, zero, negOne]), (2, [negOne, zero, zero, zero]), (-π ^ 2 / 6, [zero, negOne]), (-1,
  [zero, negOne, negOne, negOne]), (1, [zero, negOne, negOne, zero]), (2, [zero, negOne, zero,
  negOne]), (-2, [zero, negOne, zero, zero]), (-2, [zero, zero, negOne, negOne]), (2, [zero, zero,
  negOne, zero]), (-3, [zero, zero, zero, negOne]), (-2, [zero, zero, one, zero]), (π ^ 2 / 6,
  [zero, one]), (-4, [zero, one, zero, negOne]), (2, [zero, one, zero, zero]), (-1, [zero, one, one,
  zero]), (-zeta3, [one]), (-π ^ 2 / 6, [one, zero]), (-2, [one, zero, negOne, negOne]), (2, [one,
  zero, negOne, zero]), (-2, [one, zero, zero, zero]), (-1, [one, zero, one, zero]), (π ^ 2 / 6,
  [one, one]), (-2, [one, one, zero, negOne]), (1, [one, one, zero, zero])]
wv_word wppmp [one, one, negOne, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (-1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, zero,
  zero]), (1, [negOne, zero, negOne, negOne]), (-1, [negOne, zero, negOne, zero]), (1, [negOne,
  zero, zero, negOne]), (1, [negOne, zero, one, zero]), (2, [negOne, one, zero, negOne]), (-1,
  [negOne, one, zero, zero]), (1, [negOne, one, one, zero]), (-1, [zero, negOne, negOne, negOne]),
  (1, [zero, negOne, negOne, zero]), (3, [zero, negOne, zero, negOne]), (-2, [zero, negOne, zero,
  zero]), (1, [zero, negOne, one, zero]), (-3, [zero, zero, negOne, negOne]), (4, [zero, zero,
  negOne, zero]), (-6, [zero, zero, zero, negOne]), (-5, [zero, zero, one, zero]), (1, [zero, one,
  negOne, zero]), (-7, [zero, one, zero, negOne]), (2, [zero, one, zero, zero]), (-4, [zero, one,
  one, zero]), (2, [one, negOne, zero, negOne]), (-1, [one, negOne, zero, zero]), (1, [one, negOne,
  one, zero]), (-2, [one, zero, negOne, negOne]), (3, [one, zero, negOne, zero]), (-5, [one, zero,
  zero, negOne]), (-4, [one, zero, one, zero]), (1, [one, one, negOne, zero]), (-5, [one, one, zero,
  negOne]), (1, [one, one, zero, zero]), (-3, [one, one, one, zero])]
wv_word wppmm [one, one, negOne, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (-1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, zero,
  zero]), (1, [negOne, zero, negOne, negOne]), (-1, [negOne, zero, negOne, zero]), (1, [negOne,
  zero, zero, negOne]), (1, [negOne, zero, one, zero]), (2, [negOne, one, zero, negOne]), (-1,
  [negOne, one, zero, zero]), (1, [negOne, one, one, zero]), (1, [zero, negOne, negOne, negOne]),
  (-1, [zero, negOne, negOne, zero]), (1, [zero, negOne, zero, negOne]), (1, [zero, negOne, one,
  zero]), (1, [zero, zero, negOne, negOne]), (1, [zero, one, negOne, zero]), (-1, [zero, one, zero,
  negOne]), (-1, [zero, one, one, zero]), (2, [one, negOne, zero, negOne]), (-1, [one, negOne, zero,
  zero]), (1, [one, negOne, one, zero]), (1, [one, zero, negOne, zero]), (-1, [one, zero, zero,
  negOne]), (-1, [one, zero, one, zero]), (1, [one, one, negOne, zero]), (-3, [one, one, zero,
  negOne]), (1, [one, one, zero, zero]), (-2, [one, one, one, zero])]
wv_word wpmzz [one, negOne, zero, zero] := (0) with [(-π ^ 2 / 6, [negOne, zero]), (1, [negOne,
  zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (π ^ 2 / 6, [zero, negOne]), (-1, [zero,
  negOne, zero, negOne]), (1, [zero, negOne, zero, zero]), (1, [zero, zero, negOne, negOne]), (-1,
  [zero, zero, negOne, zero]), (3, [zero, zero, zero, negOne]), (1, [zero, zero, one, zero]), (-π ^
  2 / 6, [zero, one]), (2, [zero, one, zero, negOne]), (-1, [zero, one, zero, zero]), (π ^ 2 / 6,
  [one, zero]), (1, [one, zero, zero, zero])]
wv_word wpmzp [one, negOne, zero, one] := (0) with [(-2 * zeta3, [negOne]), (π ^ 2 / 6, [negOne,
  negOne]), (-1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]), (-π ^ 2 / 6,
  [negOne, zero]), (1, [negOne, zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (π ^ 2 / 6,
  [zero, negOne]), (-2, [zero, negOne, negOne, negOne]), (2, [zero, negOne, negOne, zero]), (-3,
  [zero, negOne, zero, negOne]), (1, [zero, negOne, zero, zero]), (-2, [zero, negOne, one, zero]),
  (-4, [zero, zero, negOne, zero]), (12, [zero, zero, zero, negOne]), (8, [zero, zero, one, zero]),
  (-2, [zero, one, negOne, zero]), (6, [zero, one, zero, negOne]), (4, [zero, one, one, zero]), (2 *
  zeta3, [one]), (π ^ 2 / 6, [one, zero]), (-2, [one, zero, negOne, negOne]), (3, [one, zero, zero,
  negOne]), (1, [one, zero, zero, zero]), (2, [one, zero, one, zero])]
wv_word wpmzm [one, negOne, zero, negOne] := (0) with [(1, [negOne, negOne, zero, negOne]), (2,
  [negOne, zero, negOne, negOne]), (-2, [negOne, zero, negOne, zero]), (1, [negOne, zero, zero,
  negOne]), (2, [negOne, zero, one, zero]), (1, [zero, negOne, zero, negOne]), (-2, [one, zero,
  negOne, negOne]), (2, [one, zero, negOne, zero]), (-1, [one, zero, zero, negOne]), (-2, [one,
  zero, one, zero])]
wv_word wpmpz [one, negOne, one, zero] := (0) with [(-π ^ 2 / 6, [negOne, negOne]), (1, [negOne,
  negOne, zero, negOne]), (-1, [negOne, negOne, zero, zero]), (-1, [negOne, zero, negOne, negOne]),
  (1, [negOne, zero, negOne, zero]), (-2, [negOne, zero, zero, negOne]), (-1, [negOne, zero, one,
  zero]), (π ^ 2 / 6, [negOne, one]), (-2, [negOne, one, zero, negOne]), (1, [negOne, one, zero,
  zero]), (π ^ 2 / 3, [zero, negOne]), (1, [zero, negOne, negOne, negOne]), (-1, [zero, negOne,
  negOne, zero]), (-2, [zero, negOne, zero, negOne]), (2, [zero, negOne, zero, zero]), (1, [zero,
  negOne, one, zero]), (2, [zero, zero, negOne, negOne]), (-2, [zero, zero, one, zero]), (-π ^ 2 /
  2, [zero, one]), (1, [zero, one, negOne, zero]), (3, [zero, one, zero, negOne]), (-3, [zero, one,
  zero, zero]), (-2, [zero, one, one, zero]), (π ^ 2 / 6, [one, negOne]), (-2, [one, negOne, zero,
  negOne]), (1, [one, negOne, zero, zero]), (2, [one, zero, negOne, negOne]), (-1, [one, zero,
  negOne, zero]), (2, [one, zero, zero, negOne]), (-π ^ 2 / 3, [one, one]), (4, [one, one, zero,
  negOne]), (-2, [one, one, zero, zero])]
wv_word wpmpp [one, negOne, one, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, one,
  zero]), (-1, [negOne, zero, negOne, negOne]), (2, [negOne, zero, negOne, zero]), (-4, [negOne,
  zero, zero, negOne]), (-3, [negOne, zero, one, zero]), (1, [negOne, one, negOne, zero]), (-3,
  [negOne, one, zero, negOne]), (-2, [negOne, one, one, zero]), (-1, [zero, negOne, negOne,
  negOne]), (2, [zero, negOne, negOne, zero]), (-4, [zero, negOne, zero, negOne]), (-3, [zero,
  negOne, one, zero]), (-4, [zero, zero, negOne, zero]), (12, [zero, zero, zero, negOne]), (8,
  [zero, zero, one, zero]), (-3, [zero, one, negOne, zero]), (7, [zero, one, zero, negOne]), (1,
  [zero, one, zero, zero]), (5, [zero, one, one, zero]), (1, [one, negOne, negOne, zero]), (-3,
  [one, negOne, zero, negOne]), (-2, [one, negOne, one, zero]), (-1, [one, zero, negOne, negOne]),
  (-2, [one, zero, negOne, zero]), (8, [one, zero, zero, negOne]), (5, [one, zero, one, zero]), (-2,
  [one, one, negOne, zero]), (4, [one, one, zero, negOne]), (1, [one, one, zero, zero]), (3, [one,
  one, one, zero])]
wv_word wpmpm [one, negOne, one, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, one,
  zero]), (-1, [negOne, zero, negOne, negOne]), (2, [negOne, zero, negOne, zero]), (-4, [negOne,
  zero, zero, negOne]), (-3, [negOne, zero, one, zero]), (1, [negOne, one, negOne, zero]), (-3,
  [negOne, one, zero, negOne]), (-2, [negOne, one, one, zero]), (1, [zero, negOne, negOne, negOne]),
  (-2, [zero, negOne, zero, negOne]), (-1, [zero, negOne, one, zero]), (-1, [zero, one, negOne,
  zero]), (3, [zero, one, zero, negOne]), (2, [zero, one, one, zero]), (1, [one, negOne, negOne,
  zero]), (-3, [one, negOne, zero, negOne]), (-2, [one, negOne, one, zero]), (1, [one, zero, negOne,
  negOne]), (-2, [one, zero, negOne, zero]), (4, [one, zero, zero, negOne]), (3, [one, zero, one,
  zero]), (-2, [one, one, negOne, zero]), (6, [one, one, zero, negOne]), (4, [one, one, one, zero])]
wv_word wpmmz [one, negOne, negOne, zero] := (0) with [(-π ^ 2 / 6, [negOne, negOne]), (1, [negOne,
  negOne, zero, negOne]), (-1, [negOne, negOne, zero, zero]), (-1, [negOne, zero, negOne, negOne]),
  (1, [negOne, zero, negOne, zero]), (-2, [negOne, zero, zero, negOne]), (-1, [negOne, zero, one,
  zero]), (π ^ 2 / 6, [negOne, one]), (-2, [negOne, one, zero, negOne]), (1, [negOne, one, zero,
  zero]), (-1, [zero, negOne, negOne, negOne]), (1, [zero, negOne, negOne, zero]), (-2, [zero,
  negOne, zero, negOne]), (-1, [zero, negOne, one, zero]), (-2, [zero, zero, negOne, negOne]), (-1,
  [zero, one, negOne, zero]), (1, [zero, one, zero, negOne]), (1, [zero, one, one, zero]), (π ^ 2 /
  6, [one, negOne]), (-2, [one, negOne, zero, negOne]), (1, [one, negOne, zero, zero]), (-1, [one,
  zero, negOne, zero]), (2, [one, zero, zero, negOne]), (1, [one, zero, one, zero]), (-π ^ 2 / 6,
  [one, one]), (2, [one, one, zero, negOne]), (-1, [one, one, zero, zero])]
wv_word wpmmp [one, negOne, negOne, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, one,
  zero]), (1, [negOne, zero, negOne, negOne]), (1, [negOne, one, negOne, zero]), (-1, [negOne, one,
  zero, negOne]), (-1, [negOne, one, one, zero]), (-1, [zero, negOne, negOne, negOne]), (2, [zero,
  negOne, negOne, zero]), (-2, [zero, negOne, zero, negOne]), (-2, [zero, negOne, one, zero]), (-4,
  [zero, zero, negOne, negOne]), (-2, [zero, one, negOne, zero]), (1, [zero, one, one, zero]), (1,
  [one, negOne, negOne, zero]), (-1, [one, negOne, zero, negOne]), (-1, [one, negOne, one, zero]),
  (-3, [one, zero, negOne, negOne]), (-1, [one, one, negOne, zero]), (-1, [one, one, zero, negOne])]
wv_word wpmmm [one, negOne, negOne, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-1,
  [negOne, negOne, negOne, zero]), (1, [negOne, negOne, zero, negOne]), (1, [negOne, negOne, one,
  zero]), (1, [negOne, zero, negOne, negOne]), (1, [negOne, one, negOne, zero]), (-1, [negOne, one,
  zero, negOne]), (-1, [negOne, one, one, zero]), (1, [zero, negOne, negOne, negOne]), (1, [one,
  negOne, negOne, zero]), (-1, [one, negOne, zero, negOne]), (-1, [one, negOne, one, zero]), (-1,
  [one, zero, negOne, negOne]), (-1, [one, one, negOne, zero]), (1, [one, one, zero, negOne]), (1,
  [one, one, one, zero])]
wv_word wmzzz [negOne, zero, zero, zero] := (0) with [(-1, [zero, zero, zero, negOne])]
wv_word wmzzp [negOne, zero, zero, one] := (0) with [(-π ^ 2 / 6, [negOne, zero]), (1, [negOne,
  zero, zero, negOne]), (-1, [negOne, zero, zero, zero]), (-π ^ 2 / 3, [zero, negOne]), (2, [zero,
  negOne, zero, negOne]), (-2, [zero, negOne, zero, zero]), (4, [zero, zero, negOne, negOne]), (-8,
  [zero, zero, zero, negOne]), (-4, [zero, zero, one, zero])]
wv_word wmzzm [negOne, zero, zero, negOne] := (0) with [(1, [negOne, zero, zero, negOne])]
wv_word wmzpz [negOne, zero, one, zero] := (0) with [(π ^ 2 / 3, [negOne, zero]), (-2, [negOne,
  zero, zero, negOne]), (2, [negOne, zero, zero, zero]), (π ^ 2 / 6, [zero, negOne]), (1, [zero,
  negOne, zero, negOne]), (1, [zero, negOne, zero, zero]), (-4, [zero, zero, negOne, negOne]), (4,
  [zero, zero, zero, negOne]), (4, [zero, zero, one, zero]), (π ^ 2 / 3, [zero, one]), (-4, [zero,
  one, zero, negOne]), (2, [zero, one, zero, zero])]
wv_word wmzpp [negOne, zero, one, one] := (0) with [(zeta3, [negOne]), (-1, [negOne, zero, negOne,
  negOne]), (1, [negOne, zero, negOne, zero]), (1, [negOne, zero, zero, negOne]), (-1, [negOne,
  zero, zero, zero]), (-2, [zero, negOne, negOne, negOne]), (4, [zero, negOne, zero, negOne]), (2,
  [zero, negOne, one, zero]), (4, [zero, zero, negOne, negOne]), (-8, [zero, zero, zero, negOne]),
  (-4, [zero, zero, one, zero]), (2, [zero, one, negOne, zero]), (-2, [zero, one, zero, negOne]),
  (-2, [zero, one, zero, zero]), (-2, [zero, one, one, zero])]
wv_word wmzpm [negOne, zero, one, negOne] := (0) with [(π ^ 2 / 3, [negOne, negOne]), (-4, [negOne,
  negOne, zero, negOne]), (2, [negOne, negOne, zero, zero]), (-3, [negOne, zero, negOne, negOne]),
  (1, [negOne, zero, negOne, zero]), (5, [negOne, zero, zero, negOne]), (1, [negOne, zero, one,
  zero]), (-π ^ 2 / 6, [negOne, one]), (2, [negOne, one, zero, negOne]), (-1, [negOne, one, zero,
  zero]), (-2, [zero, negOne, negOne, negOne]), (6, [zero, negOne, zero, negOne]), (2, [zero,
  negOne, one, zero]), (2, [zero, one, negOne, zero]), (-6, [zero, one, zero, negOne]), (-4, [zero,
  one, one, zero]), (-π ^ 2 / 6, [one, negOne]), (2, [one, negOne, zero, negOne]), (-1, [one,
  negOne, zero, zero]), (2, [one, zero, negOne, negOne]), (-4, [one, zero, zero, negOne]), (-2,
  [one, zero, one, zero])]
wv_word wmzmz [negOne, zero, negOne, zero] := (0) with [(-2, [negOne, zero, zero, negOne]), (-1,
  [zero, negOne, zero, negOne])]
wv_word wmzmp [negOne, zero, negOne, one] := (0) with [(-π ^ 2 / 3, [negOne, negOne]), (4, [negOne,
  negOne, zero, negOne]), (-2, [negOne, negOne, zero, zero]), (3, [negOne, zero, negOne, negOne]),
  (-8, [negOne, zero, zero, negOne]), (-3, [negOne, zero, one, zero]), (π ^ 2 / 6, [negOne, one]),
  (-2, [negOne, one, zero, negOne]), (1, [negOne, one, zero, zero]), (-2, [zero, negOne, zero,
  negOne]), (π ^ 2 / 6, [one, negOne]), (-2, [one, negOne, zero, negOne]), (1, [one, negOne, zero,
  zero]), (-2, [one, zero, negOne, negOne]), (4, [one, zero, zero, negOne]), (2, [one, zero, one,
  zero])]
wv_word wmzmm [negOne, zero, negOne, negOne] := (0) with [(1, [negOne, zero, negOne, negOne])]
wv_word wmpzz [negOne, one, zero, zero] := (0) with [(1, [negOne, zero, zero, negOne]), (-1, [zero,
  negOne, zero, negOne]), (1, [zero, zero, negOne, negOne]), (-2, [zero, zero, zero, negOne]), (-1,
  [zero, zero, one, zero]), (-π ^ 2 / 6, [zero, one]), (2, [zero, one, zero, negOne]), (-1, [zero,
  one, zero, zero]), (-π ^ 2 / 6, [one, zero]), (-1, [one, zero, zero, zero])]
wv_word wmpzp [negOne, one, zero, one] := (0) with [(π ^ 2 / 6, [negOne, negOne]), (-1, [negOne,
  negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]), (-2, [negOne, zero, negOne, negOne]),
  (4, [negOne, zero, zero, negOne]), (2, [negOne, zero, one, zero]), (-π ^ 2 / 3, [zero, negOne]),
  (2, [zero, negOne, zero, negOne]), (-2, [zero, negOne, zero, zero]), (4, [zero, zero, negOne,
  negOne]), (-8, [zero, zero, zero, negOne]), (-4, [zero, zero, one, zero]), (-2 * zeta3, [one]),
  (-π ^ 2 / 6, [one, zero]), (2, [one, zero, negOne, negOne]), (-3, [one, zero, zero, negOne]), (-1,
  [one, zero, zero, zero]), (-2, [one, zero, one, zero])]
wv_word wmpzm [negOne, one, zero, negOne] := (0) with [(1, [negOne, negOne, zero, negOne]), (2,
  [zero, negOne, negOne, negOne]), (-6, [zero, negOne, zero, negOne]), (-2, [zero, negOne, one,
  zero]), (-2, [zero, one, negOne, zero]), (6, [zero, one, zero, negOne]), (4, [zero, one, one,
  zero]), (2, [one, zero, negOne, negOne]), (-2, [one, zero, negOne, zero]), (1, [one, zero, zero,
  negOne]), (2, [one, zero, one, zero])]
wv_word wmppz [negOne, one, one, zero] := (0) with [(-1, [negOne, negOne, zero, negOne]), (1,
  [negOne, zero, negOne, negOne]), (-1, [negOne, zero, one, zero]), (-π ^ 2 / 6, [negOne, one]), (2,
  [negOne, one, zero, negOne]), (-1, [negOne, one, zero, zero]), (1, [zero, negOne, negOne,
  negOne]), (-1, [zero, negOne, one, zero]), (-4, [zero, zero, negOne, negOne]), (4, [zero, zero,
  zero, negOne]), (4, [zero, zero, one, zero]), (π ^ 2 / 3, [zero, one]), (-1, [zero, one, negOne,
  zero]), (-3, [zero, one, zero, negOne]), (3, [zero, one, zero, zero]), (1, [zero, one, one,
  zero]), (zeta3, [one]), (-π ^ 2 / 6, [one, negOne]), (2, [one, negOne, zero, negOne]), (-1, [one,
  negOne, zero, zero]), (π ^ 2 / 6, [one, zero]), (-1, [one, zero, negOne, zero]), (-2, [one, zero,
  zero, negOne]), (2, [one, zero, zero, zero]), (1, [one, zero, one, zero]), (π ^ 2 / 6, [one,
  one]), (-2, [one, one, zero, negOne]), (1, [one, one, zero, zero])]
wv_word wmppp [negOne, one, one, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, one, zero]), (-2, [negOne, zero, negOne,
  negOne]), (4, [negOne, zero, zero, negOne]), (2, [negOne, zero, one, zero]), (-1, [negOne, one,
  negOne, zero]), (1, [negOne, one, zero, negOne]), (1, [negOne, one, zero, zero]), (1, [negOne,
  one, one, zero]), (-2, [zero, negOne, negOne, negOne]), (4, [zero, negOne, zero, negOne]), (2,
  [zero, negOne, one, zero]), (4, [zero, zero, negOne, negOne]), (-8, [zero, zero, zero, negOne]),
  (-4, [zero, zero, one, zero]), (2, [zero, one, negOne, zero]), (-2, [zero, one, zero, negOne]),
  (-2, [zero, one, zero, zero]), (-2, [zero, one, one, zero]), (-1, [one, negOne, negOne, zero]),
  (1, [one, negOne, zero, negOne]), (1, [one, negOne, zero, zero]), (1, [one, negOne, one, zero]),
  (1, [one, zero, negOne, negOne]), (1, [one, zero, negOne, zero]), (-3, [one, zero, zero, negOne]),
  (-1, [one, zero, zero, zero]), (-2, [one, zero, one, zero]), (1, [one, one, negOne, zero]), (-1,
  [one, one, zero, negOne]), (-1, [one, one, zero, zero]), (-1, [one, one, one, zero])]
wv_word wmppm [negOne, one, one, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, one, zero]), (-2, [negOne, zero, negOne,
  negOne]), (4, [negOne, zero, zero, negOne]), (2, [negOne, zero, one, zero]), (-1, [negOne, one,
  negOne, zero]), (1, [negOne, one, zero, negOne]), (1, [negOne, one, zero, zero]), (1, [negOne,
  one, one, zero]), (-1, [one, negOne, negOne, zero]), (1, [one, negOne, zero, negOne]), (1, [one,
  negOne, zero, zero]), (1, [one, negOne, one, zero]), (3, [one, zero, negOne, negOne]), (-1, [one,
  zero, negOne, zero]), (-3, [one, zero, zero, negOne]), (-1, [one, zero, one, zero]), (1, [one,
  one, negOne, zero]), (1, [one, one, zero, negOne]), (-2, [one, one, zero, zero])]
wv_word wmpmz [negOne, one, negOne, zero] := (0) with [(-1, [negOne, negOne, zero, negOne]), (1,
  [negOne, zero, negOne, negOne]), (-1, [negOne, zero, one, zero]), (-π ^ 2 / 6, [negOne, one]), (2,
  [negOne, one, zero, negOne]), (-1, [negOne, one, zero, zero]), (-1, [zero, negOne, negOne,
  negOne]), (2, [zero, negOne, zero, negOne]), (1, [zero, negOne, one, zero]), (1, [zero, one,
  negOne, zero]), (-3, [zero, one, zero, negOne]), (-2, [zero, one, one, zero]), (-π ^ 2 / 6, [one,
  negOne]), (2, [one, negOne, zero, negOne]), (-1, [one, negOne, zero, zero]), (-2, [one, zero,
  negOne, negOne]), (1, [one, zero, negOne, zero]), (-2, [one, zero, zero, negOne]), (π ^ 2 / 3,
  [one, one]), (-4, [one, one, zero, negOne]), (2, [one, one, zero, zero])]
wv_word wmpmp [negOne, one, negOne, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, one, zero]), (-1, [negOne, one, negOne,
  zero]), (3, [negOne, one, zero, negOne]), (2, [negOne, one, one, zero]), (-2, [zero, negOne,
  negOne, negOne]), (4, [zero, negOne, zero, negOne]), (2, [zero, negOne, one, zero]), (2, [zero,
  one, negOne, zero]), (-6, [zero, one, zero, negOne]), (-4, [zero, one, one, zero]), (-1, [one,
  negOne, negOne, zero]), (3, [one, negOne, zero, negOne]), (2, [one, negOne, one, zero]), (-1,
  [one, zero, negOne, negOne]), (2, [one, zero, negOne, zero]), (-4, [one, zero, zero, negOne]),
  (-3, [one, zero, one, zero]), (2, [one, one, negOne, zero]), (-6, [one, one, zero, negOne]), (-4,
  [one, one, one, zero])]
wv_word wmpmm [negOne, one, negOne, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [negOne, negOne, zero, negOne]), (-1, [negOne, negOne, one, zero]), (-1, [negOne, one, negOne,
  zero]), (3, [negOne, one, zero, negOne]), (2, [negOne, one, one, zero]), (-1, [one, negOne,
  negOne, zero]), (3, [one, negOne, zero, negOne]), (2, [one, negOne, one, zero]), (1, [one, zero,
  negOne, negOne]), (2, [one, one, negOne, zero]), (-4, [one, one, zero, negOne]), (-3, [one, one,
  one, zero])]
wv_word wmmzz [negOne, negOne, zero, zero] := (0) with [(1, [negOne, zero, zero, negOne]), (1,
  [zero, negOne, zero, negOne]), (1, [zero, zero, negOne, negOne])]
wv_word wmmzp [negOne, negOne, zero, one] := (0) with [(π ^ 2 / 6, [negOne, negOne]), (-1, [negOne,
  negOne, zero, negOne]), (1, [negOne, negOne, zero, zero]), (-2, [negOne, zero, negOne, negOne]),
  (4, [negOne, zero, zero, negOne]), (2, [negOne, zero, one, zero]), (-2, [zero, negOne, negOne,
  negOne]), (4, [zero, zero, negOne, negOne]), (4, [zero, one, zero, negOne]), (2, [zero, one, one,
  zero])]
wv_word wmmzm [negOne, negOne, zero, negOne] := (0) with [(1, [negOne, negOne, zero, negOne])]
wv_word wmmpz [negOne, negOne, one, zero] := (0) with [(-1, [negOne, negOne, zero, negOne]), (-1,
  [negOne, zero, negOne, negOne]), (1, [zero, negOne, negOne, negOne]), (2, [zero, negOne, zero,
  negOne]), (-2, [zero, one, zero, negOne]), (-1, [zero, one, one, zero]), (2, [one, zero, negOne,
  negOne]), (-1, [one, zero, one, zero]), (-π ^ 2 / 6, [one, one]), (2, [one, one, zero, negOne]),
  (-1, [one, one, zero, zero])]
wv_word wmmpp [negOne, negOne, one, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [negOne, zero, negOne, negOne]), (-2, [negOne, one, zero, negOne]), (-1, [negOne, one, one,
  zero]), (-2, [zero, negOne, negOne, negOne]), (4, [zero, zero, negOne, negOne]), (4, [zero, one,
  zero, negOne]), (2, [zero, one, one, zero]), (-2, [one, negOne, zero, negOne]), (-1, [one, negOne,
  one, zero]), (4, [one, zero, zero, negOne]), (2, [one, zero, one, zero]), (-1, [one, one, negOne,
  zero]), (3, [one, one, zero, negOne]), (1, [one, one, zero, zero]), (2, [one, one, one, zero])]
wv_word wmmpm [negOne, negOne, one, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [negOne, zero, negOne, negOne]), (-2, [negOne, one, zero, negOne]), (-1, [negOne, one, one,
  zero]), (-2, [one, negOne, zero, negOne]), (-1, [one, negOne, one, zero]), (2, [one, zero, negOne,
  negOne]), (-1, [one, one, negOne, zero]), (5, [one, one, zero, negOne]), (3, [one, one, one,
  zero])]
wv_word wmmmz [negOne, negOne, negOne, zero] := (0) with [(-1, [negOne, negOne, zero, negOne]), (-1,
  [negOne, zero, negOne, negOne]), (-1, [zero, negOne, negOne, negOne])]
wv_word wmmmp [negOne, negOne, negOne, one] := (0) with [(1, [negOne, negOne, negOne, negOne]), (-2,
  [zero, negOne, negOne, negOne]), (-2, [one, zero, negOne, negOne]), (-2, [one, one, zero,
  negOne]), (-1, [one, one, one, zero])]
wv_word wmmmm [negOne, negOne, negOne, negOne] := (0) with [(1, [negOne, negOne, negOne, negOne])]
private def letters : List (ℝ × Letter) := [(1, zero), (-2, one), (-2, negOne)]

private def wordSum {α : Type} (A : List (ℝ × α)) (f : α → ℝ) : ℝ :=
  (A.map fun t => t.1 * f t.2).sum

private def wordPower (A : List (ℝ × Letter)) :
    ℕ → (List Letter → ℝ) → ℝ
  | 0, f => f []
  | n + 1, f => wordSum A fun b => wordPower A n (f ∘ (b :: ·))

private def insertSum (A : List (ℝ × Letter)) (f : List Letter → ℝ) (w : List Letter) : ℝ :=
  wordSum A fun a => ((shuffle [a] w).map f).sum

private theorem wordSum_add {α : Type} (A : List (ℝ × α)) (f g : α → ℝ) :
    wordSum A (fun a => f a + g a) = wordSum A f + wordSum A g := by
  induction A with
  | nil => simp [wordSum]
  | cons t A ih =>
    simp only [wordSum, List.map_cons, List.sum_cons, mul_add] at *
    rw [ih]
    ring

private theorem wordSum_mul {α : Type} (A : List (ℝ × α)) (c : ℝ) (f : α → ℝ) :
    wordSum A (fun a => c * f a) = c * wordSum A f := by
  induction A with
  | nil => simp [wordSum]
  | cons t A ih =>
    simp only [wordSum, List.map_cons, List.sum_cons] at *
    rw [ih]
    ring

private theorem wordSum_comm {α β : Type} (A : List (ℝ × α)) (B : List (ℝ × β))
    (f : α → β → ℝ) :
    wordSum A (fun a => wordSum B (f a)) = wordSum B (fun b => wordSum A (f · b)) := by
  induction A with
  | nil =>
    simp [wordSum]
  | cons t A ih =>
    have h (b : β) :
        wordSum (t :: A) (f · b) = t.1 * f t.2 b + wordSum A (f · b) := rfl
    simp_rw [h]
    rw [wordSum_add B (fun b => t.1 * f t.2 b) (fun b => wordSum A (f · b)),
      wordSum_mul, ← ih]
    rfl

private theorem wordPower_add (A : List (ℝ × Letter)) (n : ℕ) (f g : List Letter → ℝ) :
    wordPower A n (fun w => f w + g w) = wordPower A n f + wordPower A n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [wordPower, Function.comp_def, ih, wordSum_add]

private theorem wordPower_insert (A : List (ℝ × Letter)) (n : ℕ) (f : List Letter → ℝ) :
    wordPower A n (insertSum A f) = (n + 1 : ℝ) * wordPower A (n + 1) f := by
  induction n generalizing f with
  | zero => simp [wordPower, wordSum, insertSum]
  | succ n ih =>
    have he (b : Letter) : insertSum A f ∘ (b :: ·) =
        fun w => wordSum A (fun a => f (a :: b :: w)) + insertSum A (f ∘ (b :: ·)) w := by
      funext w
      simp only [Function.comp_def, insertSum, shuffle_cons_cons, shuffle_nil_left,
        List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.sum_cons,
        List.map_map, wordSum_add]
    have hswap (B : List (ℝ × Letter)) (g : Letter → List Letter → ℝ) :
        wordPower A n (fun w => wordSum B (fun a => g a w)) =
          wordSum B (fun a => wordPower A n (g a)) := by
      clear he ih
      induction n generalizing g with
      | zero => rfl
      | succ n ih =>
        simp only [wordPower, Function.comp_def]
        exact (congrArg (wordSum A) (funext fun c => ih (fun a w => g a (c :: w)))).trans
          (wordSum_comm A B _)
    simp only [wordPower, he, wordPower_add, hswap, ih, wordSum_add, wordSum_mul]
    rw [wordSum_comm A A (fun b a => wordPower A n (fun w => f (a :: b :: w)))]
    simp only [Function.comp_def, Nat.cast_succ]
    ring

private theorem wordPower_mul (A : List (ℝ × Letter)) (n : ℕ) (c : ℝ)
    (f : List Letter → ℝ) :
    wordPower A n (fun w => c * f w) = c * wordPower A n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [wordPower, Function.comp_def, ih, wordSum_mul]

private noncomputable def powerEval (C : ℝ) (A : List (ℝ × Letter))
    (n : ℕ) (f : List Letter → ℝ) : ℝ :=
  wordSum (i15FourPower ((C, []) :: A.map fun t => (t.1, [t.2])) n) f

private theorem powerEval_succ (C : ℝ) (A : List (ℝ × Letter))
    (n : ℕ) (f : List Letter → ℝ) :
    powerEval C A n.succ f = C * powerEval C A n f + powerEval C A n (insertSum A f) := by
  let M := i15FourPower ((C, []) :: A.map fun t => (t.1, [t.2])) n
  have row (v : List Letter) (c : ℝ) :
      wordSum (M.flatMap fun (d, w) => (shuffle v w).map fun s => (c * d, s)) f =
        c * wordSum M (fun w => ((shuffle v w).map f).sum) := by
    induction M with
    | nil => simp [wordSum]
    | cons t M ih =>
      obtain ⟨d, w⟩ := t
      simp only [List.flatMap_cons, wordSum, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_map, mul_add] at *
      rw [ih]
      change (List.map (fun s => (c * d) * f s) (shuffle v w)).sum + _ = _
      rw [List.sum_map_mul_left]
      ring
  change wordSum (i15FourProduct ((C, []) :: A.map fun t => (t.1, [t.2])) M) f = _
  conv_lhs =>
    simp only [i15FourProduct, List.flatMap_cons, List.flatMap_map]
  rw [show ∀ (X Y : List (ℝ × List Letter)), wordSum (X ++ Y) f = wordSum X f + wordSum Y f from
    fun X Y => by simp [wordSum]]
  rw [row]
  simp only [shuffle_nil_left, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  have rest (B : List (ℝ × Letter)) :
      wordSum (B.flatMap fun t => M.flatMap fun (d, w) =>
        (shuffle [t.2] w).map fun s => (t.1 * d, s)) f =
        wordSum B (fun a => wordSum M (fun w => ((shuffle [a] w).map f).sum)) := by
    induction B with
    | nil => rfl
    | cons t B ih =>
      simp only [List.flatMap_cons]
      simp only [wordSum, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at *
      rw [ih]
      exact congrArg (· + _) (row [t.2] t.1)
  rw [rest, wordSum_comm]
  rfl

private theorem powerEval_zero (C : ℝ) (A : List (ℝ × Letter)) (f : List Letter → ℝ) :
    powerEval C A 0 f = f [] := by simp [powerEval, i15FourPower, wordSum]

private theorem powerEval_four (C : ℝ) (A : List (ℝ × Letter)) (f : List Letter → ℝ) :
    powerEval C A 4 f = C ^ 4 * f [] + 4 * C ^ 3 * wordPower A 1 f +
      12 * C ^ 2 * wordPower A 2 f + 24 * C * wordPower A 3 f + 24 * wordPower A 4 f := by
  change powerEval C A (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) f = _
  simp only [powerEval_succ, powerEval_zero]
  have h (g : List Letter → ℝ) : insertSum A g [] = wordPower A 1 g := by
    simp [insertSum, wordPower]
  simp only [h, wordPower_insert, Nat.cast_one]
  ring


private def zeroLetters : List (ℝ × Letter) := [(1, zero)]

private noncomputable def logBase (r : ℝ) := -log r + 2 * log (1 + r)

private theorem wvEval_mul (L M : List (ℝ × List Letter)) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    wvEval L r * wvEval M r =
      wordSum L (fun v => wordSum M fun w => ((shuffle v w).map (hpl · r)).sum) := by
  simp_rw [← hpl_mul_hpl _ _ hr, wordSum_mul]
  change wordSum L (hpl · r) * wordSum M (hpl · r) = _
  simp_rw [mul_comm (hpl _ r) (wordSum M (hpl · r)), wordSum_mul]
  ring

private noncomputable def wv1a : List (ℝ × List Letter) :=
  [(-2, [negOne])]
private noncomputable def wv1b : List (ℝ × List Letter) :=
  [(4, []), (-4, [negOne]), (2, [zero])]
private noncomputable def wv1c : List (ℝ × List Letter) :=
  [(-2, [negOne]), (2, [zero])]

private theorem primitive_weight1 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    wordPower letters 1 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
      wordPower zeroLetters 1 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) =
      r⁻¹ * wvEval wv1a r + wvEval wv1b r + r * wvEval wv1c r := by
  simp (disch := assumption) [wordPower, wordSum, letters, zeroLetters,
    i15FourWordPrim, i15WuOffsets, wv1a, wv1b, wv1c]
  ring

private noncomputable def wv2a : List (ℝ × List Letter) :=
  [(-6, [negOne]), (8, [negOne, negOne]), (-6, [zero, negOne]), (-4, [one, zero])]
private noncomputable def wv2b : List (ℝ × List Letter) :=
  [(8, []), (-12, [negOne]), (16, [negOne, negOne]), (-8, [negOne, zero]), (6, [zero]), (-8, [zero,
  negOne]), (4, [zero, zero])]
private noncomputable def wv2c : List (ℝ × List Letter) :=
  [(π ^ 2 / 3, []), (-6, [negOne]), (8, [negOne, negOne]), (-8, [negOne, zero]), (6, [zero]), (-2,
  [zero, negOne]), (6, [zero, zero]), (4, [one, zero])]

private theorem primitive_weight2 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    wordPower letters 2 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
      wordPower zeroLetters 2 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) =
      r⁻¹ * wvEval wv2a r + wvEval wv2b r + r * wvEval wv2c r := by
  simp (disch := assumption) [wordPower, wordSum, letters, zeroLetters,
    i15FourWordPrim, i15WuOffsets, wv2a, wv2b, wv2c]
  ring

private noncomputable def wv3a : List (ℝ × List Letter) :=
  [(2 * π ^ 2 / 3 - 18, [negOne]), (24, [negOne, negOne]), (-32, [negOne, negOne, negOne]), (24,
  [negOne, zero, negOne]), (4, [negOne, zero, zero]), (16, [negOne, one, zero]), (-18, [zero,
  negOne]), (24, [zero, negOne, negOne]), (-18, [zero, zero, negOne]), (-12, [zero, one, zero]), (-2
  * π ^ 2 / 3, [one]), (16, [one, negOne, zero]), (-12, [one, zero]), (-8, [one, zero, negOne]),
  (-12, [one, zero, zero]), (-16, [one, one, zero])]
private noncomputable def wv3b : List (ℝ × List Letter) :=
  [(28, []), (-36, [negOne]), (48, [negOne, negOne]), (-64, [negOne, negOne, negOne]), (32, [negOne,
  negOne, zero]), (-24, [negOne, zero]), (32, [negOne, zero, negOne]), (-16, [negOne, zero, zero]),
  (18, [zero]), (-24, [zero, negOne]), (32, [zero, negOne, negOne]), (-16, [zero, negOne, zero]),
  (12, [zero, zero]), (-16, [zero, zero, negOne]), (8, [zero, zero, zero])]
private noncomputable def wv3c : List (ℝ × List Letter) :=
  [(π ^ 2 - 4 * zeta3, []), (-2 * π ^ 2 / 3 - 18, [negOne]), (24, [negOne, negOne]), (-32, [negOne,
  negOne, negOne]), (32, [negOne, negOne, zero]), (-24, [negOne, zero]), (8, [negOne, zero,
  negOne]), (-20, [negOne, zero, zero]), (-16, [negOne, one, zero]), (π ^ 2 / 3 + 18, [zero]), (-6,
  [zero, negOne]), (8, [zero, negOne, negOne]), (-24, [zero, negOne, zero]), (18, [zero, zero]), (6,
  [zero, zero, negOne]), (14, [zero, zero, zero]), (20, [zero, one, zero]), (2 * π ^ 2 / 3, [one]),
  (-16, [one, negOne, zero]), (12, [one, zero]), (8, [one, zero, negOne]), (12, [one, zero, zero]),
  (16, [one, one, zero])]

private theorem primitive_weight3 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    wordPower letters 3 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
      wordPower zeroLetters 3 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) =
      r⁻¹ * wvEval wv3a r + wvEval wv3b r + r * wvEval wv3c r := by
  simp (disch := assumption) [wordPower, wordSum, letters, zeroLetters,
    i15FourWordPrim, i15WuOffsets, wv3a, wv3b, wv3c]
  ring

private noncomputable def wv4a : List (ℝ × List Letter) :=
  [(2 * π ^ 2 - 8 * zeta3 - 54, [negOne]), (72 - 8 * π ^ 2 / 3, [negOne, negOne]), (-96, [negOne,
  negOne, negOne]), (128, [negOne, negOne, negOne, negOne]), (-96, [negOne, negOne, zero, negOne]),
  (-16, [negOne, negOne, zero, zero]), (-64, [negOne, negOne, one, zero]), (2 * π ^ 2 / 3, [negOne,
  zero]), (72, [negOne, zero, negOne]), (-96, [negOne, zero, negOne, negOne]), (-16, [negOne, zero,
  negOne, zero]), (12, [negOne, zero, zero]), (80, [negOne, zero, zero, negOne]), (12, [negOne,
  zero, zero, zero]), (64, [negOne, zero, one, zero]), (8 * π ^ 2 / 3, [negOne, one]), (-64,
  [negOne, one, negOne, zero]), (48, [negOne, one, zero]), (32, [negOne, one, zero, negOne]), (48,
  [negOne, one, zero, zero]), (64, [negOne, one, one, zero]), (2 * π ^ 2 - 54, [zero, negOne]), (72,
  [zero, negOne, negOne]), (-96, [zero, negOne, negOne, negOne]), (72, [zero, negOne, zero,
  negOne]), (12, [zero, negOne, zero, zero]), (48, [zero, negOne, one, zero]), (-54, [zero, zero,
  negOne]), (72, [zero, zero, negOne, negOne]), (-54, [zero, zero, zero, negOne]), (-36, [zero,
  zero, one, zero]), (-2 * π ^ 2, [zero, one]), (48, [zero, one, negOne, zero]), (-36, [zero, one,
  zero]), (-24, [zero, one, zero, negOne]), (-36, [zero, one, zero, zero]), (-48, [zero, one, one,
  zero]), (-2 * π ^ 2 + 8 * zeta3, [one]), (8 * π ^ 2 / 3, [one, negOne]), (-64, [one, negOne,
  negOne, zero]), (48, [one, negOne, zero]), (32, [one, negOne, zero, negOne]), (48, [one, negOne,
  zero, zero]), (64, [one, negOne, one, zero]), (-2 * π ^ 2 / 3 - 36, [one, zero]), (-24, [one,
  zero, negOne]), (32, [one, zero, negOne, negOne]), (48, [one, zero, negOne, zero]), (-36, [one,
  zero, zero]), (-48, [one, zero, zero, negOne]), (-28, [one, zero, zero, zero]), (-64, [one, zero,
  one, zero]), (-8 * π ^ 2 / 3, [one, one]), (64, [one, one, negOne, zero]), (-48, [one, one,
  zero]), (-32, [one, one, zero, negOne]), (-48, [one, one, zero, zero]), (-64, [one, one, one,
  zero])]
private noncomputable def wv4b : List (ℝ × List Letter) :=
  [(80, []), (-108, [negOne]), (144, [negOne, negOne]), (-192, [negOne, negOne, negOne]), (256,
  [negOne, negOne, negOne, negOne]), (-128, [negOne, negOne, negOne, zero]), (96, [negOne, negOne,
  zero]), (-128, [negOne, negOne, zero, negOne]), (64, [negOne, negOne, zero, zero]), (-72, [negOne,
  zero]), (96, [negOne, zero, negOne]), (-128, [negOne, zero, negOne, negOne]), (64, [negOne, zero,
  negOne, zero]), (-48, [negOne, zero, zero]), (64, [negOne, zero, zero, negOne]), (-32, [negOne,
  zero, zero, zero]), (54, [zero]), (-72, [zero, negOne]), (96, [zero, negOne, negOne]), (-128,
  [zero, negOne, negOne, negOne]), (64, [zero, negOne, negOne, zero]), (-48, [zero, negOne, zero]),
  (64, [zero, negOne, zero, negOne]), (-32, [zero, negOne, zero, zero]), (36, [zero, zero]), (-48,
  [zero, zero, negOne]), (64, [zero, zero, negOne, negOne]), (-32, [zero, zero, negOne, zero]), (24,
  [zero, zero, zero]), (-32, [zero, zero, zero, negOne]), (16, [zero, zero, zero, zero])]
private noncomputable def wv4c : List (ℝ × List Letter) :=
  [(π ^ 4 / 20 + 3 * π ^ 2 - 12 * zeta3, []), (-2 * π ^ 2 + 8 * zeta3 - 54, [negOne]), (8 * π ^ 2 /
  3 + 72, [negOne, negOne]), (-96, [negOne, negOne, negOne]), (128, [negOne, negOne, negOne,
  negOne]), (-128, [negOne, negOne, negOne, zero]), (96, [negOne, negOne, zero]), (-32, [negOne,
  negOne, zero, negOne]), (80, [negOne, negOne, zero, zero]), (64, [negOne, negOne, one, zero]), (-2
  * π ^ 2 / 3 - 72, [negOne, zero]), (24, [negOne, zero, negOne]), (-32, [negOne, zero, negOne,
  negOne]), (80, [negOne, zero, negOne, zero]), (-60, [negOne, zero, zero]), (-16, [negOne, zero,
  zero, negOne]), (-44, [negOne, zero, zero, zero]), (-64, [negOne, zero, one, zero]), (-8 * π ^ 2 /
  3, [negOne, one]), (64, [negOne, one, negOne, zero]), (-48, [negOne, one, zero]), (-32, [negOne,
  one, zero, negOne]), (-48, [negOne, one, zero, zero]), (-64, [negOne, one, one, zero]), (π ^ 2 - 4
  * zeta3 + 54, [zero]), (-10 * π ^ 2 / 3 - 18, [zero, negOne]), (24, [zero, negOne, negOne]), (-32,
  [zero, negOne, negOne, negOne]), (96, [zero, negOne, negOne, zero]), (-72, [zero, negOne, zero]),
  (-24, [zero, negOne, zero, negOne]), (-68, [zero, negOne, zero, zero]), (-80, [zero, negOne, one,
  zero]), (π ^ 2 / 3 + 54, [zero, zero]), (18, [zero, zero, negOne]), (-24, [zero, zero, negOne,
  negOne]), (-56, [zero, zero, negOne, zero]), (42, [zero, zero, zero]), (46, [zero, zero, zero,
  negOne]), (30, [zero, zero, zero, zero]), (68, [zero, zero, one, zero]), (10 * π ^ 2 / 3, [zero,
  one]), (-80, [zero, one, negOne, zero]), (60, [zero, one, zero]), (40, [zero, one, zero, negOne]),
  (60, [zero, one, zero, zero]), (80, [zero, one, one, zero]), (2 * π ^ 2 - 8 * zeta3, [one]), (-8 *
  π ^ 2 / 3, [one, negOne]), (64, [one, negOne, negOne, zero]), (-48, [one, negOne, zero]), (-32,
  [one, negOne, zero, negOne]), (-48, [one, negOne, zero, zero]), (-64, [one, negOne, one, zero]),
  (2 * π ^ 2 / 3 + 36, [one, zero]), (24, [one, zero, negOne]), (-32, [one, zero, negOne, negOne]),
  (-48, [one, zero, negOne, zero]), (36, [one, zero, zero]), (48, [one, zero, zero, negOne]), (28,
  [one, zero, zero, zero]), (64, [one, zero, one, zero]), (8 * π ^ 2 / 3, [one, one]), (-64, [one,
  one, negOne, zero]), (48, [one, one, zero]), (32, [one, one, zero, negOne]), (48, [one, one, zero,
  zero]), (64, [one, one, one, zero])]

private theorem primitive_weight4 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    wordPower letters 4 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
      wordPower zeroLetters 4 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) =
      r⁻¹ * wvEval wv4a r + wvEval wv4b r + r * wvEval wv4c r := by
  simp (disch := assumption) [wordPower, wordSum, letters, zeroLetters,
    i15FourWordPrim, i15WuOffsets, wv4a, wv4b, wv4c]
  ring

private noncomputable def wvLogs1 : List (ℝ × List Letter) :=
  [(2, [negOne]), (-1, [zero])]
private theorem wv_logBase_pow1 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 1 = wvEval wvLogs1 r := by
  rw [logBase, pow_one, ← hpl_zero r, ← hpl_negOne hr]
  simp [wvLogs1]
  ring

private noncomputable def wvLogs2 : List (ℝ × List Letter) :=
  [(8, [negOne, negOne]), (-4, [negOne, zero]), (-4, [zero, negOne]), (2, [zero, zero])]
private theorem wv_logBase_pow2 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 2 = wvEval wvLogs2 r := by
  rw [show logBase r ^ 2 = logBase r ^ 1 * logBase r ^ 1 by ring,
    wv_logBase_pow1 hr, wvEval_mul _ _ hr]
  simp [wvLogs2, wvLogs1, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wvLogs3 : List (ℝ × List Letter) :=
  [(48, [negOne, negOne, negOne]), (-24, [negOne, negOne, zero]), (-24, [negOne, zero, negOne]),
  (12, [negOne, zero, zero]), (-24, [zero, negOne, negOne]), (12, [zero, negOne, zero]), (12, [zero,
  zero, negOne]), (-6, [zero, zero, zero])]
private theorem wv_logBase_pow3 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 3 = wvEval wvLogs3 r := by
  rw [show logBase r ^ 3 = logBase r ^ 2 * logBase r ^ 1 by ring,
    wv_logBase_pow2 hr, wv_logBase_pow1 hr, wvEval_mul _ _ hr]
  simp [wvLogs3, wvLogs2, wvLogs1, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv1aS : List (ℝ × List Letter) :=
  [(-384, [negOne, negOne, negOne, negOne]), (144, [negOne, negOne, negOne, zero]), (144, [negOne,
  negOne, zero, negOne]), (-48, [negOne, negOne, zero, zero]), (144, [negOne, zero, negOne,
  negOne]), (-48, [negOne, zero, negOne, zero]), (-48, [negOne, zero, zero, negOne]), (12, [negOne,
  zero, zero, zero]), (144, [zero, negOne, negOne, negOne]), (-48, [zero, negOne, negOne, zero]),
  (-48, [zero, negOne, zero, negOne]), (12, [zero, negOne, zero, zero]), (-48, [zero, zero, negOne,
  negOne]), (12, [zero, zero, negOne, zero]), (12, [zero, zero, zero, negOne])]
private theorem wv_shuffle_wv1a {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 3 * wvEval wv1a r = wvEval wv1aS r := by
  rw [wv_logBase_pow3 hr, wvEval_mul _ _ hr]
  simp [wvLogs3, wv1a, wv1aS, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv1bS : List (ℝ × List Letter) :=
  [(192, [negOne, negOne, negOne]), (-768, [negOne, negOne, negOne, negOne]), (384, [negOne, negOne,
  negOne, zero]), (-96, [negOne, negOne, zero]), (384, [negOne, negOne, zero, negOne]), (-192,
  [negOne, negOne, zero, zero]), (-96, [negOne, zero, negOne]), (384, [negOne, zero, negOne,
  negOne]), (-192, [negOne, zero, negOne, zero]), (48, [negOne, zero, zero]), (-192, [negOne, zero,
  zero, negOne]), (96, [negOne, zero, zero, zero]), (-96, [zero, negOne, negOne]), (384, [zero,
  negOne, negOne, negOne]), (-192, [zero, negOne, negOne, zero]), (48, [zero, negOne, zero]), (-192,
  [zero, negOne, zero, negOne]), (96, [zero, negOne, zero, zero]), (48, [zero, zero, negOne]),
  (-192, [zero, zero, negOne, negOne]), (96, [zero, zero, negOne, zero]), (-24, [zero, zero, zero]),
  (96, [zero, zero, zero, negOne]), (-48, [zero, zero, zero, zero])]
private theorem wv_shuffle_wv1b {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 3 * wvEval wv1b r = wvEval wv1bS r := by
  rw [wv_logBase_pow3 hr, wvEval_mul _ _ hr]
  simp [wvLogs3, wv1b, wv1bS, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv1cS : List (ℝ × List Letter) :=
  [(-384, [negOne, negOne, negOne, negOne]), (240, [negOne, negOne, negOne, zero]), (240, [negOne,
  negOne, zero, negOne]), (-144, [negOne, negOne, zero, zero]), (240, [negOne, zero, negOne,
  negOne]), (-144, [negOne, zero, negOne, zero]), (-144, [negOne, zero, zero, negOne]), (84,
  [negOne, zero, zero, zero]), (240, [zero, negOne, negOne, negOne]), (-144, [zero, negOne, negOne,
  zero]), (-144, [zero, negOne, zero, negOne]), (84, [zero, negOne, zero, zero]), (-144, [zero,
  zero, negOne, negOne]), (84, [zero, zero, negOne, zero]), (84, [zero, zero, zero, negOne]), (-48,
  [zero, zero, zero, zero])]
private theorem wv_shuffle_wv1c {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 3 * wvEval wv1c r = wvEval wv1cS r := by
  rw [wv_logBase_pow3 hr, wvEval_mul _ _ hr]
  simp [wvLogs3, wv1c, wv1cS, wordSum, shuffle, shuffleAux]
  ring

private theorem wv_weight1 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 3 *
      (wordPower letters 1 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
        wordPower zeroLetters 1 (fun w => i15FourWordPrim (i15WuOffsets r) w 1)) =
      r⁻¹ * wvEval wv1aS r + wvEval wv1bS r + r * wvEval wv1cS r := by
  rw [primitive_weight1 hr]
  calc
    _ = r⁻¹ * (logBase r ^ 3 * wvEval wv1a r) +
        logBase r ^ 3 * wvEval wv1b r + r * (logBase r ^ 3 * wvEval wv1c r) := by ring
    _ = _ := by rw [wv_shuffle_wv1a hr, wv_shuffle_wv1b hr, wv_shuffle_wv1c hr]

private noncomputable def wv2aS : List (ℝ × List Letter) :=
  [(-144, [negOne, negOne, negOne]), (384, [negOne, negOne, negOne, negOne]), (-96, [negOne, negOne,
  negOne, zero]), (48, [negOne, negOne, zero]), (-144, [negOne, negOne, zero, negOne]), (16,
  [negOne, negOne, zero, zero]), (-32, [negOne, negOne, one, zero]), (48, [negOne, zero, negOne]),
  (-192, [negOne, zero, negOne, negOne]), (40, [negOne, zero, negOne, zero]), (-12, [negOne, zero,
  zero]), (64, [negOne, zero, zero, negOne]), (16, [negOne, zero, one, zero]), (-32, [negOne, one,
  negOne, zero]), (-32, [negOne, one, zero, negOne]), (32, [negOne, one, zero, zero]), (48, [zero,
  negOne, negOne]), (-240, [zero, negOne, negOne, negOne]), (64, [zero, negOne, negOne, zero]),
  (-12, [zero, negOne, zero]), (88, [zero, negOne, zero, negOne]), (-12, [zero, negOne, zero,
  zero]), (16, [zero, negOne, one, zero]), (-12, [zero, zero, negOne]), (112, [zero, zero, negOne,
  negOne]), (-24, [zero, zero, negOne, zero]), (-36, [zero, zero, zero, negOne]), (-8, [zero, zero,
  one, zero]), (16, [zero, one, negOne, zero]), (16, [zero, one, zero, negOne]), (-16, [zero, one,
  zero, zero]), (-32, [one, negOne, negOne, zero]), (-32, [one, negOne, zero, negOne]), (32, [one,
  negOne, zero, zero]), (-32, [one, zero, negOne, negOne]), (32, [one, zero, negOne, zero]), (32,
  [one, zero, zero, negOne]), (-24, [one, zero, zero, zero])]
private theorem wv_shuffle_wv2a {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 2 * wvEval wv2a r = wvEval wv2aS r := by
  rw [wv_logBase_pow2 hr, wvEval_mul _ _ hr]
  simp [wvLogs2, wv2a, wv2aS, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv2bS : List (ℝ × List Letter) :=
  [(64, [negOne, negOne]), (-288, [negOne, negOne, negOne]), (768, [negOne, negOne, negOne,
  negOne]), (-384, [negOne, negOne, negOne, zero]), (144, [negOne, negOne, zero]), (-384, [negOne,
  negOne, zero, negOne]), (192, [negOne, negOne, zero, zero]), (-32, [negOne, zero]), (144, [negOne,
  zero, negOne]), (-384, [negOne, zero, negOne, negOne]), (192, [negOne, zero, negOne, zero]), (-72,
  [negOne, zero, zero]), (192, [negOne, zero, zero, negOne]), (-96, [negOne, zero, zero, zero]),
  (-32, [zero, negOne]), (144, [zero, negOne, negOne]), (-384, [zero, negOne, negOne, negOne]),
  (192, [zero, negOne, negOne, zero]), (-72, [zero, negOne, zero]), (192, [zero, negOne, zero,
  negOne]), (-96, [zero, negOne, zero, zero]), (16, [zero, zero]), (-72, [zero, zero, negOne]),
  (192, [zero, zero, negOne, negOne]), (-96, [zero, zero, negOne, zero]), (36, [zero, zero, zero]),
  (-96, [zero, zero, zero, negOne]), (48, [zero, zero, zero, zero])]
private theorem wv_shuffle_wv2b {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 2 * wvEval wv2b r = wvEval wv2bS r := by
  rw [wv_logBase_pow2 hr, wvEval_mul _ _ hr]
  simp [wvLogs2, wv2b, wv2bS, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv2cS : List (ℝ × List Letter) :=
  [(8 * π ^ 2 / 3, [negOne, negOne]), (-144, [negOne, negOne, negOne]), (384, [negOne, negOne,
  negOne, negOne]), (-288, [negOne, negOne, negOne, zero]), (96, [negOne, negOne, zero]), (-240,
  [negOne, negOne, zero, negOne]), (192, [negOne, negOne, zero, zero]), (32, [negOne, negOne, one,
  zero]), (-4 * π ^ 2 / 3, [negOne, zero]), (96, [negOne, zero, negOne]), (-192, [negOne, zero,
  negOne, negOne]), (168, [negOne, zero, negOne, zero]), (-60, [negOne, zero, zero]), (144, [negOne,
  zero, zero, negOne]), (-120, [negOne, zero, zero, zero]), (-16, [negOne, zero, one, zero]), (32,
  [negOne, one, negOne, zero]), (32, [negOne, one, zero, negOne]), (-32, [negOne, one, zero, zero]),
  (-4 * π ^ 2 / 3, [zero, negOne]), (96, [zero, negOne, negOne]), (-144, [zero, negOne, negOne,
  negOne]), (144, [zero, negOne, negOne, zero]), (-60, [zero, negOne, zero]), (120, [zero, negOne,
  zero, negOne]), (-108, [zero, negOne, zero, zero]), (-16, [zero, negOne, one, zero]), (2 * π ^ 2 /
  3, [zero, zero]), (-60, [zero, zero, negOne]), (96, [zero, zero, negOne, negOne]), (-96, [zero,
  zero, negOne, zero]), (36, [zero, zero, zero]), (-84, [zero, zero, zero, negOne]), (72, [zero,
  zero, zero, zero]), (8, [zero, zero, one, zero]), (-16, [zero, one, negOne, zero]), (-16, [zero,
  one, zero, negOne]), (16, [zero, one, zero, zero]), (32, [one, negOne, negOne, zero]), (32, [one,
  negOne, zero, negOne]), (-32, [one, negOne, zero, zero]), (32, [one, zero, negOne, negOne]), (-32,
  [one, zero, negOne, zero]), (-32, [one, zero, zero, negOne]), (24, [one, zero, zero, zero])]
private theorem wv_shuffle_wv2c {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 2 * wvEval wv2c r = wvEval wv2cS r := by
  rw [wv_logBase_pow2 hr, wvEval_mul _ _ hr]
  simp [wvLogs2, wv2c, wv2cS, wordSum, shuffle, shuffleAux]
  ring

private theorem wv_weight2 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 2 *
      (wordPower letters 2 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
        wordPower zeroLetters 2 (fun w => i15FourWordPrim (i15WuOffsets r) w 1)) =
      r⁻¹ * wvEval wv2aS r + wvEval wv2bS r + r * wvEval wv2cS r := by
  rw [primitive_weight2 hr]
  calc
    _ = r⁻¹ * (logBase r ^ 2 * wvEval wv2a r) +
        logBase r ^ 2 * wvEval wv2b r + r * (logBase r ^ 2 * wvEval wv2c r) := by ring
    _ = _ := by rw [wv_shuffle_wv2a hr, wv_shuffle_wv2b hr, wv_shuffle_wv2c hr]

private noncomputable def wv3aS : List (ℝ × List Letter) :=
  [(8 * π ^ 2 / 3 - 72, [negOne, negOne]), (144, [negOne, negOne, negOne]), (-256, [negOne, negOne,
  negOne, negOne]), (32, [negOne, negOne, negOne, zero]), (-24, [negOne, negOne, zero]), (128,
  [negOne, negOne, zero, negOne]), (16, [negOne, negOne, zero, zero]), (64, [negOne, negOne, one,
  zero]), (18 - 2 * π ^ 2 / 3, [negOne, zero]), (-60, [negOne, zero, negOne]), (176, [negOne, zero,
  negOne, negOne]), (-16, [negOne, zero, negOne, zero]), (-76, [negOne, zero, zero, negOne]), (-12,
  [negOne, zero, zero, zero]), (-40, [negOne, zero, one, zero]), (-4 * π ^ 2 / 3, [negOne, one]),
  (64, [negOne, one, negOne, zero]), (-24, [negOne, one, zero]), (16, [negOne, one, zero, negOne]),
  (-56, [negOne, one, zero, zero]), (-32, [negOne, one, one, zero]), (18 - 2 * π ^ 2 / 3, [zero,
  negOne]), (-96, [zero, negOne, negOne]), (176, [zero, negOne, negOne, negOne]), (-24, [zero,
  negOne, negOne, zero]), (18, [zero, negOne, zero]), (-84, [zero, negOne, zero, negOne]), (-4,
  [zero, negOne, zero, zero]), (-40, [zero, negOne, one, zero]), (36, [zero, zero, negOne]), (-120,
  [zero, zero, negOne, negOne]), (18, [zero, zero, negOne, zero]), (54, [zero, zero, zero, negOne]),
  (24, [zero, zero, one, zero]), (2 * π ^ 2 / 3, [zero, one]), (-40, [zero, one, negOne, zero]),
  (12, [zero, one, zero]), (-16, [zero, one, zero, negOne]), (36, [zero, one, zero, zero]), (16,
  [zero, one, one, zero]), (-4 * π ^ 2 / 3, [one, negOne]), (64, [one, negOne, negOne, zero]), (-24,
  [one, negOne, zero]), (16, [one, negOne, zero, negOne]), (-56, [one, negOne, zero, zero]), (-32,
  [one, negOne, one, zero]), (2 * π ^ 2 / 3, [one, zero]), (-24, [one, zero, negOne]), (-32, [one,
  zero, negOne, negOne]), (-32, [one, zero, negOne, zero]), (24, [one, zero, zero]), (-8, [one,
  zero, zero, negOne]), (36, [one, zero, zero, zero]), (16, [one, zero, one, zero]), (-32, [one,
  one, negOne, zero]), (-32, [one, one, zero, negOne]), (32, [one, one, zero, zero])]
private theorem wv_shuffle_wv3a {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 1 * wvEval wv3a r = wvEval wv3aS r := by
  rw [wv_logBase_pow1 hr, wvEval_mul _ _ hr]
  simp [wvLogs1, wv3a, wv3aS, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv3bS : List (ℝ × List Letter) :=
  [(56, [negOne]), (-144, [negOne, negOne]), (288, [negOne, negOne, negOne]), (-512, [negOne,
  negOne, negOne, negOne]), (256, [negOne, negOne, negOne, zero]), (-144, [negOne, negOne, zero]),
  (256, [negOne, negOne, zero, negOne]), (-128, [negOne, negOne, zero, zero]), (72, [negOne, zero]),
  (-144, [negOne, zero, negOne]), (256, [negOne, zero, negOne, negOne]), (-128, [negOne, zero,
  negOne, zero]), (72, [negOne, zero, zero]), (-128, [negOne, zero, zero, negOne]), (64, [negOne,
  zero, zero, zero]), (-28, [zero]), (72, [zero, negOne]), (-144, [zero, negOne, negOne]), (256,
  [zero, negOne, negOne, negOne]), (-128, [zero, negOne, negOne, zero]), (72, [zero, negOne, zero]),
  (-128, [zero, negOne, zero, negOne]), (64, [zero, negOne, zero, zero]), (-36, [zero, zero]), (72,
  [zero, zero, negOne]), (-128, [zero, zero, negOne, negOne]), (64, [zero, zero, negOne, zero]),
  (-36, [zero, zero, zero]), (64, [zero, zero, zero, negOne]), (-32, [zero, zero, zero, zero])]
private theorem wv_shuffle_wv3b {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 1 * wvEval wv3b r = wvEval wv3bS r := by
  rw [wv_logBase_pow1 hr, wvEval_mul _ _ hr]
  simp [wvLogs1, wv3b, wv3bS, wordSum, shuffle, shuffleAux]
  ring

private noncomputable def wv3cS : List (ℝ × List Letter) :=
  [(2 * π ^ 2 - 8 * zeta3, [negOne]), (-8 * π ^ 2 / 3 - 72, [negOne, negOne]), (144, [negOne,
  negOne, negOne]), (-256, [negOne, negOne, negOne, negOne]), (224, [negOne, negOne, negOne, zero]),
  (-120, [negOne, negOne, zero]), (128, [negOne, negOne, zero, negOne]), (-144, [negOne, negOne,
  zero, zero]), (-64, [negOne, negOne, one, zero]), (4 * π ^ 2 / 3 + 54, [negOne, zero]), (-84,
  [negOne, zero, negOne]), (80, [negOne, zero, negOne, negOne]), (-128, [negOne, zero, negOne,
  zero]), (84, [negOne, zero, zero]), (-44, [negOne, zero, zero, negOne]), (88, [negOne, zero, zero,
  zero]), (56, [negOne, zero, one, zero]), (4 * π ^ 2 / 3, [negOne, one]), (-64, [negOne, one,
  negOne, zero]), (24, [negOne, one, zero]), (-16, [negOne, one, zero, negOne]), (56, [negOne, one,
  zero, zero]), (32, [negOne, one, one, zero]), (-π ^ 2 + 4 * zeta3, [zero]), (4 * π ^ 2 / 3 + 54,
  [zero, negOne]), (-48, [zero, negOne, negOne]), (80, [zero, negOne, negOne, negOne]), (-136,
  [zero, negOne, negOne, zero]), (66, [zero, negOne, zero]), (-52, [zero, negOne, zero, negOne]),
  (96, [zero, negOne, zero, zero]), (56, [zero, negOne, one, zero]), (-2 * π ^ 2 / 3 - 36, [zero,
  zero]), (48, [zero, zero, negOne]), (8, [zero, zero, negOne, negOne]), (70, [zero, zero, negOne,
  zero]), (-54, [zero, zero, zero]), (10, [zero, zero, zero, negOne]), (-56, [zero, zero, zero,
  zero]), (-40, [zero, zero, one, zero]), (-2 * π ^ 2 / 3, [zero, one]), (56, [zero, one, negOne,
  zero]), (-12, [zero, one, zero]), (32, [zero, one, zero, negOne]), (-52, [zero, one, zero, zero]),
  (-16, [zero, one, one, zero]), (4 * π ^ 2 / 3, [one, negOne]), (-64, [one, negOne, negOne, zero]),
  (24, [one, negOne, zero]), (-16, [one, negOne, zero, negOne]), (56, [one, negOne, zero, zero]),
  (32, [one, negOne, one, zero]), (-2 * π ^ 2 / 3, [one, zero]), (24, [one, zero, negOne]), (32,
  [one, zero, negOne, negOne]), (32, [one, zero, negOne, zero]), (-24, [one, zero, zero]), (8, [one,
  zero, zero, negOne]), (-36, [one, zero, zero, zero]), (-16, [one, zero, one, zero]), (32, [one,
  one, negOne, zero]), (32, [one, one, zero, negOne]), (-32, [one, one, zero, zero])]
private theorem wv_shuffle_wv3c {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 1 * wvEval wv3c r = wvEval wv3cS r := by
  rw [wv_logBase_pow1 hr, wvEval_mul _ _ hr]
  simp [wvLogs1, wv3c, wv3cS, wordSum, shuffle, shuffleAux]
  ring

private theorem wv_weight3 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logBase r ^ 1 *
      (wordPower letters 3 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
        wordPower zeroLetters 3 (fun w => i15FourWordPrim (i15WuOffsets r) w 1)) =
      r⁻¹ * wvEval wv3aS r + wvEval wv3bS r + r * wvEval wv3cS r := by
  rw [primitive_weight3 hr]
  calc
    _ = r⁻¹ * (logBase r ^ 1 * wvEval wv3a r) +
        logBase r ^ 1 * wvEval wv3b r + r * (logBase r ^ 1 * wvEval wv3c r) := by ring
    _ = _ := by rw [wv_shuffle_wv3a hr, wv_shuffle_wv3b hr, wv_shuffle_wv3c hr]

private theorem ratioWeights (r : ℝ) :
    i15WuPhi4 r 1 =
      4 * (logBase r ^ 3 *
        (wordPower letters 1 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
          wordPower zeroLetters 1 (fun w => i15FourWordPrim (i15WuOffsets r) w 1))) +
      12 * (logBase r ^ 2 *
        (wordPower letters 2 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
          wordPower zeroLetters 2 (fun w => i15FourWordPrim (i15WuOffsets r) w 1))) +
      24 * (logBase r ^ 1 *
        (wordPower letters 3 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
          wordPower zeroLetters 3 (fun w => i15FourWordPrim (i15WuOffsets r) w 1))) +
      24 * (wordPower letters 4 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
        wordPower zeroLetters 4 (fun w => i15FourWordPrim (i15WuOffsets r) w 1)) := by
  change powerEval (logBase r) letters 4 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) -
    powerEval (logBase r) zeroLetters 4 (fun w => i15FourWordPrim (i15WuOffsets r) w 1) = _
  rw [powerEval_four, powerEval_four]
  ring

/-- The ratio endpoint equals the tracked weight-four HPL combination. -/
theorem i15WuPhi4_one {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : i15WuPhi4 r 1 = i15W4 r := by
  rw [ratioWeights, wv_weight1 hr, wv_weight2 hr, wv_weight3 hr, primitive_weight4 hr]
  simp [wv1aS, wv1bS, wv1cS, wv2aS, wv2bS, wv2cS, wv3aS, wv3bS, wv3cS,
    wv4a, wv4b, wv4c, i15W4, i15W4D, i15T3Sum, i15T3q, div_eq_mul_inv]
  ring

/-- The first weight-four inner slice of the Laurent coefficient. -/
theorem integrableOn_and_integral_i15A1k_four_inner {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u) = i15W4G x :=
  integrableOn_and_integral_i15A1k_four_of_endpoint (fun _ hr => i15WuPhi4_one hr) hx

end QED.ThreeLoopD
