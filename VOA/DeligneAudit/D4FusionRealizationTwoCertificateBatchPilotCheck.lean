/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateData
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateBatchPilotData
import Mathlib.Data.List.GetD
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSortedData

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def batchPilotCheck (p : BatchPilotCase) : Bool :=
  sortedZero
    (scale p.denominator
      (applyColumns (pairColumn 28
        (fun i => (batchPilotColumns.getD p.color []).getD i []) p.color p.mode) p.source) ++
     scale (-1) p.target)

theorem batch_range_join {P : ℕ → Bool} (lo left mid right total : ℕ)
    (hm : lo + left = mid) (ht : left + right = total)
    (hL : (List.range' lo left).all P = true)
    (hR : (List.range' mid right).all P = true) :
    (List.range' lo total).all P = true := by
  rw [← ht, ← List.range'_append_1, List.all_append, hm, hL, hR]
  rfl

theorem batch_all_of_getD {α : Type*} (xs : List α) (fallback : α) (P : α → Bool)
    (h : (List.range' 0 xs.length).all (fun i => P (xs.getD i fallback)) = true) :
    xs.all P = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hh := List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)
  simpa only [List.getD_eq_getElem _ _ hi] using hh

end VOA.DeligneAudit.D4Two.Certificate
