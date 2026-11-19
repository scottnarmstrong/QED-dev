/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCCovClasses
public import QED.ChainProof.HCBB2Links
public import QED.ChainProof.HCSideBDRepLimit
public import QED.ChainProof.HCSideBDNestedForm
public import QED.ChainProof.HCSideBDCov

/-!
# The three class links of (HC₃), unconditionally

Helper level, Phase 5 Stage 1a (decision D-53). The fifteen per-representative inputs of
`QED.ChainProof.HCSide.classLinks_of_reps` are all proved:
* `repBB`: `QED.ChainProof.HCBB2.repLimit_repBB'`, `repNested_repBB`, `repCov_repBB`;
* `repBD s`, `repDB s`: `QED.ChainProof.HCSide.repLimit_repBD`, `repNested_repBD`,
  `repCov_repBD` and their `repDB` analogues.

Hence the class limit link, the class covariance link and the Pauli link hold, and
`isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks` gives (HC₃).
-/

@[expose] public section

namespace QED.ChainProof

open QED.ChainProof.HCSide QED.ChainProof.HCBB2

/-- **The three class links of (HC₃).** -/
theorem chainClassLinks :
    ClassLimitLink chainClassX ∧ ClassCovLink chainClassX ∧ ChainPauliAtLink :=
  classLinks_of_reps repLimit_repBB' repLimit_repBD repLimit_repDB repNested_repBB
    repNested_repBD repNested_repDB repCov_repBB repCov_repBD repCov_repDB

end QED.ChainProof

end
