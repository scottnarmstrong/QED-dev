/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemKuVal
public import QED.ThreeLoopD.SetDMastersI9MThree
public import QED.ThreeLoopD.SetDMastersI9Wire

/-!
# Set (d), master `I₉`: the expansion, unconditionally

`QED.ThreeLoopD.hasTruncLaurent_setDMasterI9_of_K_Rem` gives the set (d) input for `I₉` from
the expansions of `K` (`QED.ThreeLoopD.hasTruncLaurent_i9K`, with target
`QED.ThreeLoopD.i9KTarget`, the same polynomial as `QED.ThreeLoopD.i9KLaurent`) and of `Rem`
(`QED.ThreeLoopD.hasTruncLaurent_i9Rem`).

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI9`: `HasTruncLaurent setDMasterI9 setDLaurentI9 2`.
-/

@[expose] public section

namespace QED.ThreeLoopD

theorem i9KTarget_eq_i9KLaurent : i9KTarget = i9KLaurent := by
  funext ε
  simp only [i9KTarget, i9KLaurent]
  ring

/-- **The set (d) input for `I₉`**, unconditionally. -/
theorem hasTruncLaurent_setDMasterI9 : HasTruncLaurent setDMasterI9 setDLaurentI9 2 :=
  hasTruncLaurent_setDMasterI9_of_K_Rem (i9KTarget_eq_i9KLaurent ▸ hasTruncLaurent_i9K)
    hasTruncLaurent_i9Rem

end QED.ThreeLoopD
