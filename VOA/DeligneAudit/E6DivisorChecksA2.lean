/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6DivisorData

/-!
# E₆ pair-comparison certificates: kernel checks (A2, tree nodes 3283–6083)

The 6083 tree nodes (13 blocks), the column tables, the depth bound, the root, the relation ranges, the completeness of `psiT`, and the 651 complement tables (7 blocks).  Each theorem is a small `decide +kernel` check (kept small to bound kernel memory).
-/

namespace VOA.DeligneAudit.DeligneDivisor.E6

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_nodes_3284 : nodeChecks 3284 3753 = true := by decide +kernel

theorem e6_nodes_3753 : nodeChecks 3753 4222 = true := by decide +kernel

theorem e6_nodes_4222 : nodeChecks 4222 4691 = true := by decide +kernel

theorem e6_nodes_4691 : nodeChecks 4691 5160 = true := by decide +kernel

theorem e6_nodes_5160 : nodeChecks 5160 5629 = true := by decide +kernel

theorem e6_nodes_5629 : nodeChecks 5629 6084 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6
