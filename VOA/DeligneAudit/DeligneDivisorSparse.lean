/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorNumeric
import VOA.DeligneAudit.DeligneDivisorAssembly
import VOA.DeligneAudit.DeligneSectorSparse

/-!
# Sparse two-slot certificates (type-generic)

Integer two-slot tables as sparse lists `QV` of `(c, d, k)` (`castQZ`), the ordered zero check
(`ozeroCheck`), and the sparse pair operators `opAQ`, `opBQ` for a sparse integer bracket table `br`,
with their soundness (`castQZ_opAQ`, `castQZ_opBQ`).

**`levOK_tree`**: a generation tree of sparse tables (root `δ_{c₀}⊗δ_{c₀}`, each node `S_x` or
`A_x` of its parent, checked by `treeCheck`) gives `LevOK (depth) (level)` for every node.
`levOK_flatMap`: integer combinations of such tables.
-/

namespace VOA.DeligneAudit.DeligneDivisor

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.A2 (Pm)

noncomputable section

variable {S : DeligneSectorData}

/-! ## Sparse tables -/

/-- The integer table of a sparse list (ordered coefficients). -/
def castQZ (L : QV) : ZTab S := fun c d => qget L c d

theorem qget_nil (a b : ℕ) : qget [] a b = 0 := rfl

theorem qget_cons (t : ℕ × ℕ × ℤ) (L : QV) (a b : ℕ) :
    qget (t :: L) a b = (if t.1 = a ∧ t.2.1 = b then t.2.2 else 0) + qget L a b := by
  simp [qget]

theorem qget_append (L M : QV) (a b : ℕ) : qget (L ++ M) a b = qget L a b + qget M a b := by
  simp [qget]

theorem qget_smulQ (k : ℤ) (L : QV) (a b : ℕ) : qget (smulQ k L) a b = k * qget L a b := by
  induction L with
  | nil => simp [smulQ, qget]
  | cons t L ih =>
    simp only [smulQ, List.map_cons] at ih ⊢
    rw [qget_cons, qget_cons, ih]; split_ifs <;> ring

theorem qget_flatMap {α : Type*} (L : List α) (F : α → QV) (a b : ℕ) :
    qget (L.flatMap F) a b = (L.map fun x => qget (F x) a b).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [List.flatMap_cons, qget_append, ih]

theorem qget_filter (L : QV) (a b : ℕ) :
    qget (L.filter fun t => t.2.2 != 0) a b = qget L a b := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    rw [List.filter_cons, qget_cons]
    split_ifs with h1 h2
    · rw [qget_cons, ih, if_pos h2]
    · rw [qget_cons, ih, if_neg h2]
    · simp only [bne_iff_ne, ne_eq, not_not] at h1
      rw [ih, h1]; simp
    · simp only [bne_iff_ne, ne_eq, not_not] at h1
      rw [ih]; simp

theorem castQZ_append (L M : QV) : castQZ (S := S) (L ++ M) = castQZ L + castQZ M := by
  funext c d; simp [castQZ, qget_append]

theorem castQZ_smulQ (k : ℤ) (L : QV) : castQZ (S := S) (smulQ k L) = k • castQZ L := by
  funext c d; simp [castQZ, qget_smulQ]

theorem castQZ_nil : castQZ (S := S) [] = 0 := by
  funext c d; rfl

/-- Every key carries total coefficient zero (ordered pairs). -/
def ozeroCheck (L : QV) : Bool := L.all fun t => qget L t.1 t.2.1 == 0

theorem qget_eq_zero_of_ocheck {L : QV} (h : ozeroCheck L = true) (a b : ℕ) : qget L a b = 0 := by
  by_cases hc : ∃ t ∈ L, t.1 = a ∧ t.2.1 = b
  · obtain ⟨t, ht, h1, h2⟩ := hc
    simp only [ozeroCheck, List.all_eq_true, beq_iff_eq] at h
    rw [← h1, ← h2]; exact h t ht
  · push Not at hc
    unfold qget
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    by_cases h1 : t.1 = a
    · simp [hc t ht h1]
    · simp [h1]

theorem castQZ_eq_of_check {L M : QV} (h : ozeroCheck (L ++ smulQ (-1) M) = true) :
    castQZ (S := S) L = castQZ M := by
  funext c d
  have := qget_eq_zero_of_ocheck h c d
  rw [qget_append, qget_smulQ] at this
  simp only [castQZ]; linarith

theorem qget_filter_fst (L : QV) (a b : ℕ) :
    qget (L.filter fun t => t.1 == a) a b = qget L a b := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    rw [List.filter_cons, qget_cons]
    split_ifs with h1 h2 h2
    · rw [qget_cons, ih, if_pos h2]
    · rw [qget_cons, ih, if_neg h2]
    · simp only [beq_iff_eq] at h1; exact absurd h2.1 h1
    · rw [ih]; simp

/-- The ordered zero check, bucketed by the first index (`a < n`). -/
def ozeroCheckB (n : ℕ) (L : QV) : Bool :=
  (List.range n).all fun a => ozeroCheck (L.filter fun t => t.1 == a)

theorem qget_eq_zero_of_ocheckB {n : ℕ} {L : QV} (h : ozeroCheckB n L = true) {a : ℕ}
    (ha : a < n) (b : ℕ) : qget L a b = 0 := by
  simp only [ozeroCheckB, List.all_eq_true, List.mem_range] at h
  rw [← qget_filter_fst]
  exact qget_eq_zero_of_ocheck (h a ha) a b

theorem castQZ_eq_of_checkB {n : ℕ} (hn : S.n = n) {L M : QV}
    (h : ozeroCheckB n (L ++ smulQ (-1) M) = true) : castQZ (S := S) L = castQZ M := by
  funext c d
  have := qget_eq_zero_of_ocheckB h (by rw [← hn]; exact c.2) d
  rw [qget_append, qget_smulQ] at this
  simp only [castQZ]; linarith

/-- Integer combinations of sparse tables. -/
def combQ (tab : ℕ → QV) (L : List (ℕ × ℤ)) : QV := L.flatMap fun p => smulQ p.2 (tab p.1)

theorem levOK_combQ {D ℓ : ℕ} (tab : ℕ → QV) (L : List (ℕ × ℤ))
    (h : ∀ p ∈ L, LevOK D ℓ (castQZ (S := S) (tab p.1))) :
    LevOK D ℓ (castQZ (S := S) (combQ tab L)) := by
  induction L with
  | nil => rw [combQ, List.flatMap_nil, castQZ_nil]; exact levOK_zero D ℓ
  | cons p L ih =>
    rw [combQ, List.flatMap_cons, castQZ_append, castQZ_smulQ]
    exact levOK_add (levOK_zsmul _ (h p List.mem_cons_self))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## Sparse pair operators -/

section Ops

variable (br : ℕ → ℕ → SV) (n : ℕ)

/-- Sparse `opA`. -/
def opAQ (x : ℕ) (L : QV) : QV :=
  (L.flatMap fun t => (List.range n).map fun c => (c, t.2.1, -(fZ br x c t.1) * t.2.2)).filter
    fun t => t.2.2 != 0

/-- Sparse `opB`. -/
def opBQ (x : ℕ) (L : QV) : QV :=
  (L.flatMap fun t => (List.range n).map fun d => (t.1, d, -(fZ br x d t.2.1) * t.2.2)).filter
    fun t => t.2.2 != 0



theorem qget_range_fst (d' : ℕ) (F : ℕ → ℤ) (a b : ℕ) (ha : a < n) :
    qget ((List.range n).map fun c => (c, d', F c)) a b = if d' = b then F a else 0 := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.map_append, qget_append]
    simp only [List.map_cons, List.map_nil, qget_cons, qget_nil, add_zero]
    by_cases hak : a < k
    · rw [ih hak]
      have : k ≠ a := by omega
      simp [this]
    · have hak' : a = k := by omega
      subst hak'
      have hz : qget ((List.range a).map fun c => (c, d', F c)) a b = 0 := by
        refine List.sum_eq_zero fun z hz => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        have : c ≠ a := by rw [List.mem_range] at hc; omega
        simp [this]
      rw [hz, zero_add]
      by_cases hd : d' = b <;> simp [hd]

theorem qget_range_snd (c' : ℕ) (F : ℕ → ℤ) (a b : ℕ) (hb : b < n) :
    qget ((List.range n).map fun d => (c', d, F d)) a b = if c' = a then F b else 0 := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.map_append, qget_append]
    simp only [List.map_cons, List.map_nil, qget_cons, qget_nil, add_zero]
    by_cases hbk : b < k
    · rw [ih hbk]
      have : k ≠ b := by omega
      simp [this]
    · have hbk' : b = k := by omega
      subst hbk'
      have hz : qget ((List.range b).map fun d => (c', d, F d)) a b = 0 := by
        refine List.sum_eq_zero fun z hz => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
        have : d ≠ b := by rw [List.mem_range] at hd; omega
        simp [this]
      rw [hz, zero_add]
      by_cases hc : c' = a <;> simp [hc]

variable {br n}

theorem sum_fin_ite_mul {N : ℕ} (G : ℕ → ℤ) (e : ℕ) (he : e < N) (P : Prop) [Decidable P]
    (k : ℤ) :
    ∑ i : Fin N, G i * (if e = (i : ℕ) ∧ P then k else 0) = if P then G e * k else 0 := by
  rw [Finset.sum_eq_single ⟨e, he⟩]
  · simp
  · intro i _ hi
    have : e ≠ (i : ℕ) := fun h => hi (Fin.ext h.symm)
    simp [this]
  · simp

theorem castQZ_opAQ (hn : S.n = n) (x : Fin S.n) (L : QV) (hL : qRange n L = true) :
    castQZ (S := S) (opAQ br n x L) = opAZ (fun x c e => fZ br x c e) x (castQZ L) := by
  funext a b
  simp only [castQZ, opAQ, opAZ, qget_filter]
  have hL' : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n := by
    simpa [qRange] using hL
  clear hL
  induction L with
  | nil => simp [qget]
  | cons t L ih =>
    rw [List.flatMap_cons, qget_append, ih (fun u hu => hL' u (List.mem_cons_of_mem _ hu))]
    have ht := hL' t List.mem_cons_self
    rw [qget_range_fst n t.2.1 _ (a : ℕ) (b : ℕ) (by rw [← hn]; exact a.2)]
    simp only [qget_cons, mul_add, Finset.sum_add_distrib, neg_add]
    congr 1
    have := sum_fin_ite_mul (N := S.n) (fun e => fZ br x a e) t.1 (by rw [hn]; exact ht.1) (t.2.1 = b) t.2.2
    simp only [eq_comm (a := t.1)] at this ⊢
    rw [show (∑ i : Fin S.n, fZ br x a i * (if (i : ℕ) = t.1 ∧ t.2.1 = b then t.2.2 else 0)) =
        if t.2.1 = b then fZ br x a t.1 * t.2.2 else 0 from by
      rw [← this]]
    split_ifs <;> ring

theorem castQZ_opBQ (hn : S.n = n) (x : Fin S.n) (L : QV) (hL : qRange n L = true) :
    castQZ (S := S) (opBQ br n x L) = opBZ (fun x c e => fZ br x c e) x (castQZ L) := by
  funext a b
  simp only [castQZ, opBQ, opBZ, qget_filter]
  have hL' : ∀ t ∈ L, t.1 < n ∧ t.2.1 < n := by
    simpa [qRange] using hL
  clear hL
  induction L with
  | nil => simp [qget]
  | cons t L ih =>
    rw [List.flatMap_cons, qget_append, ih (fun u hu => hL' u (List.mem_cons_of_mem _ hu))]
    have ht := hL' t List.mem_cons_self
    rw [qget_range_snd n t.1 _ (a : ℕ) (b : ℕ) (by rw [← hn]; exact b.2)]
    simp only [qget_cons, mul_add, Finset.sum_add_distrib, neg_add]
    congr 1
    have := sum_fin_ite_mul (N := S.n) (fun e => fZ br x b e) t.2.1 (by rw [hn]; exact ht.2) (t.1 = a) t.2.2
    rw [show (∑ i : Fin S.n, fZ br x b i * (if t.1 = a ∧ t.2.1 = (i : ℕ) then t.2.2 else 0)) =
        if t.1 = a then fZ br x b t.2.1 * t.2.2 else 0 from by
      rw [← this]; refine Finset.sum_congr rfl fun i _ => ?_; congr 2; exact propext and_comm]
    split_ifs <;> ring

end Ops

/-! ## The generation tree -/

section Tree

variable (br : ℕ → ℕ → SV) (n : ℕ) (tab : ℕ → QV) (par : ℕ → ℕ × Bool × ℕ × ℕ × ℕ)

/-- The node check: parent earlier, letter in range, depth and level bookkeeping, and the table
equal to `S_x` or `A_x` of the parent. -/
def nodeCheck (i : ℕ) : Bool :=
  let p := par i
  decide (p.1 < i) && decide (p.2.2.1 < n) && qRange n (tab p.1) &&
    decide (p.2.2.2.1 = (par p.1).2.2.2.1 + 1) &&
    decide (p.2.2.2.2 = (par p.1).2.2.2.2 + (if p.2.1 then 1 else 0)) &&
    ozeroCheckB n (tab i ++ smulQ (-1)
      (if p.2.1 then opAQ br n p.2.2.1 (tab p.1) ++ smulQ (-1) (opBQ br n p.2.2.1 (tab p.1))
       else opAQ br n p.2.2.1 (tab p.1) ++ opBQ br n p.2.2.1 (tab p.1)))

variable {br n tab par}

theorem levOK_tree (hn : S.n = n) (hf : ∀ x c e, S.f x c e = (fZ br x c e : ℂ))
    (hroot : castQZ (S := S) (tab 0) = baseZ) (h0 : (par 0).2.2.2.1 = 0 ∧ (par 0).2.2.2.2 = 0)
    (N : ℕ) (hnode : ∀ i, 0 < i → i < N → nodeCheck br n tab par i = true) :
    ∀ i, i < N → LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := S) (tab i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiN
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hroot, h0.1, h0.2]; exact levOK_base
    · have hc := hnode i hi hiN
      simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨hp, hx⟩, hr⟩, hdep⟩, hlev⟩, hz⟩ := hc
      set p := (par i).1
      set xN := (par i).2.2.1
      have hpar := ih p hp (lt_trans hp hiN)
      have hx' : xN < S.n := by rw [hn]; exact hx
      have heq := castQZ_eq_of_checkB (S := S) hn hz
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
#print axioms VOA.DeligneAudit.DeligneDivisor.castQZ_opAQ
#print axioms VOA.DeligneAudit.DeligneDivisor.castQZ_opBQ
#print axioms VOA.DeligneAudit.DeligneDivisor.levOK_tree
end AxiomAudit
