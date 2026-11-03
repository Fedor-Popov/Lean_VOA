/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6DivisorData

/-!
# E₆ pair-comparison certificates: kernel checks (A, tree nodes 1–3283)

The 6083 tree nodes (13 blocks), the column tables, the depth bound, the root, the relation ranges, the completeness of `psiT`, and the 651 complement tables (7 blocks).  Each theorem is a small `decide +kernel` check (kept small to bound kernel memory).
-/

namespace VOA.DeligneAudit.DeligneDivisor.E6

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_nodes_1 : nodeChecks 1 470 = true := by decide +kernel

theorem e6_nodes_470 : nodeChecks 470 939 = true := by decide +kernel

theorem e6_nodes_939 : nodeChecks 939 1408 = true := by decide +kernel

theorem e6_nodes_1408 : nodeChecks 1408 1877 = true := by decide +kernel

theorem e6_nodes_1877 : nodeChecks 1877 2346 = true := by decide +kernel

theorem e6_nodes_2346 : nodeChecks 2346 2815 = true := by decide +kernel

theorem e6_nodes_2815 : nodeChecks 2815 3284 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6
