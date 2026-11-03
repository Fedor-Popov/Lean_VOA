/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorNumeric
import VOA.DeligneAudit.DeligneDivisorEnc

/-!
# Column tables and the fastest tree checks

The pair operators need, for a current `x` and an index `e`, all `c` with `f(x,c,e) ≠ 0`: the column
`col x e`.  A column table is certified against the bracket rows by one encoded zero check per `x`
(`col_of_check`), and then `opAQc`, `opBQc` compute the pair operators in time linear in the table.
**`levOK_treeC`**: the generation tree with these operators and encoded equality checks.
-/

namespace VOA.DeligneAudit.DeligneDivisor

open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse

noncomputable section

variable {S : DeligneSectorData}







theorem qget_map_fst (V : SV) (d : ℕ) (g : ℤ → ℤ) (a b : ℕ) :
    qget (V.map fun p => (p.1, d, g p.2)) a b =
      if d = b then (V.map fun p => if p.1 = a then g p.2 else 0).sum else 0 := by
  induction V with
  | nil => simp [qget]
  | cons p V ih =>
    rw [List.map_cons, qget_cons, ih]
    by_cases h : d = b
    · simp [h]
    · simp [h]

theorem qget_map_snd (V : SV) (c : ℕ) (g : ℤ → ℤ) (a b : ℕ) :
    qget (V.map fun p => (c, p.1, g p.2)) a b =
      if c = a then (V.map fun p => if p.1 = b then g p.2 else 0).sum else 0 := by
  induction V with
  | nil => simp [qget]
  | cons p V ih =>
    rw [List.map_cons, qget_cons, ih]
    by_cases h : c = a
    · simp [h]
    · simp [h]

theorem qget_rowTrip (br : ℕ → ℕ → SV) (n x : ℕ) {a : ℕ} (ha : a < n) (b : ℕ) :
    qget (rowTrip br n x) a b = sget (br x a) b := by
  unfold rowTrip
  rw [qget_flatMap]
  have : ∀ c, qget ((br x c).map fun p => (c, p.1, p.2)) a b = if c = a then sget (br x a) b else 0 := by
    intro c
    have hm := qget_map_snd (br x c) c (fun k => k) a b
    simp only at hm
    rw [hm]
    by_cases h : c = a
    · subst h; simp [sget, id]
    · simp [h]
  simp only [this]
  have key : ∀ m, ((List.range m).map fun c => if c = a then sget (br x a) b else 0).sum =
      if a < m then sget (br x a) b else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases h1 : a < m
      · have : m ≠ a := by omega
        simp [h1, this, show a < m + 1 by omega]
      · by_cases h2 : m = a
        · subst h2; simp
        · simp [h1, h2, show ¬ a < m + 1 by omega]
  rw [key, if_pos ha]

theorem qget_colTrip (col : ℕ → ℕ → SV) (n x : ℕ) (a : ℕ) {b : ℕ} (hb : b < n) :
    qget (colTrip col n x) a b = sget (col x b) a := by
  unfold colTrip
  rw [qget_flatMap]
  have : ∀ e, qget ((col x e).map fun p => (p.1, e, p.2)) a b = if e = b then sget (col x b) a else 0 := by
    intro e
    have hm := qget_map_fst (col x e) e (fun k => k) a b
    simp only at hm
    rw [hm]
    by_cases h : e = b
    · subst h; simp [sget, id]
    · simp [h]
  simp only [this]
  have key : ∀ m, ((List.range m).map fun e => if e = b then sget (col x b) a else 0).sum =
      if b < m then sget (col x b) a else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases h1 : b < m
      · have : m ≠ b := by omega
        simp [h1, this, show b < m + 1 by omega]
      · by_cases h2 : m = b
        · subst h2; simp
        · simp [h1, h2, show ¬ b < m + 1 by omega]
  rw [key, if_pos hb]

theorem col_of_check {br : ℕ → ℕ → SV} {col : ℕ → ℕ → SV} {n x : ℕ}
    (h : colCheck br col n x = true) {c e : ℕ} (hc : c < n) (he : e < n) :
    sget (col x e) c = fZ br x c e := by
  have := qget_eq_zero_of_encCheck h hc he
  rw [qget_append, qget_smulQ, qget_rowTrip br n x hc, qget_colTrip col n x c he] at this
  simp only [fZ]; linarith





theorem sget_map_mul (V : SV) (a : ℕ) (k : ℤ) :
    (V.map fun p => if p.1 = a then -(p.2 * k) else 0).sum = -(sget V a * k) := by
  induction V with
  | nil => simp [sget]
  | cons p V ih =>
    rw [List.map_cons, List.sum_cons, ih, sget_cons]
    split_ifs <;> ring

theorem castQZ_opAQc {br : ℕ → ℕ → SV} {col : ℕ → ℕ → SV} (hn : S.n = n) {x : ℕ}
    (hcol : colCheck br col n x = true) (hx : x < S.n) (L : QV) (hL : qRange n L = true) :
    castQZ (S := S) (opAQc col x L) = opAZ (fun x c e => fZ br x c e) ⟨x, hx⟩ (castQZ L) := by
  funext a b
  simp only [castQZ, opAQc, opAZ]
  have hL' : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n := by simpa [qRange] using hL
  clear hL
  induction L with
  | nil => simp [qget]
  | cons t L ih =>
    rw [List.flatMap_cons, qget_append, ih (fun u hu => hL' u (List.mem_cons_of_mem _ hu))]
    have ht := hL' t List.mem_cons_self
    have hm := qget_map_fst (col x t.1) t.2.1 (fun k => -(k * t.2.2)) a b
    simp only at hm
    rw [hm, sget_map_mul, col_of_check hcol (by rw [← hn]; exact a.2) ht.1]
    simp only [qget_cons, mul_add, Finset.sum_add_distrib, neg_add]
    congr 1
    have := sum_fin_ite_mul (N := S.n) (fun e => fZ br x a e) t.1 (by rw [hn]; exact ht.1)
      (t.2.1 = b) t.2.2
    simp only [eq_comm (a := t.1)] at this ⊢
    rw [show (∑ i : Fin S.n, fZ br x a i * (if (i : ℕ) = t.1 ∧ t.2.1 = b then t.2.2 else 0)) =
        if t.2.1 = b then fZ br x a t.1 * t.2.2 else 0 from by rw [← this]]
    split_ifs <;> ring

theorem castQZ_opBQc {br : ℕ → ℕ → SV} {col : ℕ → ℕ → SV} (hn : S.n = n) {x : ℕ}
    (hcol : colCheck br col n x = true) (hx : x < S.n) (L : QV) (hL : qRange n L = true) :
    castQZ (S := S) (opBQc col x L) = opBZ (fun x c e => fZ br x c e) ⟨x, hx⟩ (castQZ L) := by
  funext a b
  simp only [castQZ, opBQc, opBZ]
  have hL' : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n := by simpa [qRange] using hL
  clear hL
  induction L with
  | nil => simp [qget]
  | cons t L ih =>
    rw [List.flatMap_cons, qget_append, ih (fun u hu => hL' u (List.mem_cons_of_mem _ hu))]
    have ht := hL' t List.mem_cons_self
    have hm := qget_map_snd (col x t.2.1) t.1 (fun k => -(k * t.2.2)) a b
    simp only at hm
    rw [hm]
    have e2 : (((col x t.2.1).map fun p => if p.1 = (b : ℕ) then -(p.2 * t.2.2) else 0).sum) =
        -(fZ br x b t.2.1 * t.2.2) := by
      rw [sget_map_mul, col_of_check hcol (by rw [← hn]; exact b.2) ht.2]
    rw [e2]
    simp only [qget_cons, mul_add, Finset.sum_add_distrib, neg_add]
    congr 1
    have := sum_fin_ite_mul (N := S.n) (fun e => fZ br x b e) t.2.1 (by rw [hn]; exact ht.2)
      (t.1 = a) t.2.2
    rw [show (∑ i : Fin S.n, fZ br x b i * (if t.1 = a ∧ t.2.1 = (i : ℕ) then t.2.2 else 0)) =
        if t.1 = a then fZ br x b t.2.1 * t.2.2 else 0 from by
      rw [← this]; refine Finset.sum_congr rfl fun i _ => ?_; congr 2; exact propext and_comm]
    split_ifs <;> ring

section Tree

variable (n : ℕ) (col : ℕ → ℕ → SV) (tab : ℕ → QV) (par : ℕ → ℕ × Bool × ℕ × ℕ × ℕ)



variable {n col tab par}

theorem levOK_treeC {br : ℕ → ℕ → SV} (hn : S.n = n)
    (hf : ∀ x c e, S.f x c e = (fZ br x c e : ℂ)) (hcols : ∀ x < n, colCheck br col n x = true)
    (hroot : castQZ (S := S) (tab 0) = baseZ) (h0 : (par 0).2.2.2.1 = 0 ∧ (par 0).2.2.2.2 = 0)
    (N : ℕ) (hnode : ∀ i, 0 < i → i < N → nodeCheckC n col tab par i = true) :
    ∀ i, i < N → LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := S) (tab i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiN
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hroot, h0.1, h0.2]; exact levOK_base
    · have hc := hnode i hi hiN
      simp only [nodeCheckC, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨hp, hx⟩, hr⟩, hdep⟩, hlev⟩, hz⟩ := hc
      set p := (par i).1
      set xN := (par i).2.2.1
      have hpar := ih p hp (lt_trans hp hiN)
      have hx' : xN < S.n := by rw [hn]; exact hx
      have heq := castQZ_eq_of_enc (S := S) (le_of_eq hn) hz
      rw [heq, hdep, hlev]
      by_cases hA : (par i).2.1
      · simp only [hA, if_true, castQZ_append, castQZ_smulQ, neg_one_zsmul, ← sub_eq_add_neg]
        rw [castQZ_opAQc hn (hcols xN hx) hx' _ hr, castQZ_opBQc hn (hcols xN hx) hx' _ hr]
        exact levOK_A (fun x c e => fZ br x c e) hf ⟨xN, hx'⟩ hpar
      · simp only [hA, if_false, Bool.false_eq_true, castQZ_append, add_zero]
        rw [castQZ_opAQc hn (hcols xN hx) hx' _ hr, castQZ_opBQc hn (hcols xN hx) hx' _ hr]
        exact levOK_S (fun x c e => fZ br x c e) hf ⟨xN, hx'⟩ hpar

end Tree

end

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.levOK_treeC
end AxiomAudit
