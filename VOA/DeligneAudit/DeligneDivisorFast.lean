/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorSort

/-!
# Fast tree checks for large types

The sparse pair operators read a whole bracket row `rows x = [br x 0, …, br x (n-1)]` once (`opAQr`, `opBQr`,
equal to `opAQ`, `opBQ` when the row is correct), and the node equality is checked by the sort-based
`qzeroSort`.  **`levOK_treeF`** is `levOK_tree` for these checks.
-/

namespace VOA.DeligneAudit.DeligneDivisor

open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse

noncomputable section

variable {S : DeligneSectorData}

/-- Row-based `opA`. -/
def opAQr (row : List SV) (L : QV) : QV :=
  (L.flatMap fun t => row.zipIdx.map fun p => (p.2, t.2.1, -(sget p.1 t.1) * t.2.2)).filter
    fun t => t.2.2 != 0

/-- Row-based `opB`. -/
def opBQr (row : List SV) (L : QV) : QV :=
  (L.flatMap fun t => row.zipIdx.map fun p => (t.1, p.2, -(sget p.1 t.2.1) * t.2.2)).filter
    fun t => t.2.2 != 0

theorem zipIdx_map_range {α : Type*} (n : ℕ) (h : ℕ → α) :
    ((List.range n).map h).zipIdx = (List.range n).map fun c => (h c, c) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zipIdx]

theorem opAQr_eq {br : ℕ → ℕ → SV} {n x : ℕ} {row : List SV}
    (hrow : row = (List.range n).map (br x)) (L : QV) : opAQr row L = opAQ br n x L := by
  subst hrow
  simp only [opAQr, opAQ, zipIdx_map_range, List.map_map]
  rfl

theorem opBQr_eq {br : ℕ → ℕ → SV} {n x : ℕ} {row : List SV}
    (hrow : row = (List.range n).map (br x)) (L : QV) : opBQr row L = opBQ br n x L := by
  subst hrow
  simp only [opBQr, opBQ, zipIdx_map_range, List.map_map]
  rfl

section Tree

variable (n : ℕ) (rows : ℕ → List SV) (tab : ℕ → QV) (par : ℕ → ℕ × Bool × ℕ × ℕ × ℕ)

/-- The fast node check. -/
def nodeCheckF (i : ℕ) : Bool :=
  let p := par i
  decide (p.1 < i) && decide (p.2.2.1 < n) && qRange n (tab p.1) &&
    decide (p.2.2.2.1 = (par p.1).2.2.2.1 + 1) &&
    decide (p.2.2.2.2 = (par p.1).2.2.2.2 + (if p.2.1 then 1 else 0)) &&
    qzeroSort (tab i ++ smulQ (-1)
      (if p.2.1 then opAQr (rows p.2.2.1) (tab p.1) ++ smulQ (-1) (opBQr (rows p.2.2.1) (tab p.1))
       else opAQr (rows p.2.2.1) (tab p.1) ++ opBQr (rows p.2.2.1) (tab p.1)))

variable {n rows tab par}

theorem levOK_treeF {br : ℕ → ℕ → SV} (hn : S.n = n) (hn256 : n ≤ 256)
    (hf : ∀ x c e, S.f x c e = (fZ br x c e : ℂ))
    (hrows : ∀ x < n, rows x = (List.range n).map (br x))
    (hroot : castQZ (S := S) (tab 0) = baseZ) (h0 : (par 0).2.2.2.1 = 0 ∧ (par 0).2.2.2.2 = 0)
    (N : ℕ) (hnode : ∀ i, 0 < i → i < N → nodeCheckF n rows tab par i = true) :
    ∀ i, i < N → LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := S) (tab i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiN
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hroot, h0.1, h0.2]; exact levOK_base
    · have hc := hnode i hi hiN
      simp only [nodeCheckF, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨hp, hx⟩, hr⟩, hdep⟩, hlev⟩, hz⟩ := hc
      set p := (par i).1
      set xN := (par i).2.2.1
      have hpar := ih p hp (lt_trans hp hiN)
      have hx' : xN < S.n := by rw [hn]; exact hx
      have heq := castQZ_eq_of_sort (S := S) (by rw [hn]; exact hn256) hz
      rw [opAQr_eq (hrows xN hx), opBQr_eq (hrows xN hx)] at heq
      rw [heq, hdep, hlev]
      by_cases hA : (par i).2.1
      · simp only [hA, if_true, castQZ_append, castQZ_smulQ, neg_one_zsmul, ← sub_eq_add_neg]
        rw [castQZ_opAQ hn ⟨xN, hx'⟩ _ hr, castQZ_opBQ hn ⟨xN, hx'⟩ _ hr]
        exact levOK_A (fun x c e => fZ br x c e) hf ⟨xN, hx'⟩ hpar
      · simp only [hA, if_false, Bool.false_eq_true, castQZ_append, add_zero]
        rw [castQZ_opAQ hn ⟨xN, hx'⟩ _ hr, castQZ_opBQ hn ⟨xN, hx'⟩ _ hr]
        exact levOK_S (fun x c e => fZ br x c e) hf ⟨xN, hx'⟩ hpar

end Tree

end

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.levOK_treeF
end AxiomAudit
