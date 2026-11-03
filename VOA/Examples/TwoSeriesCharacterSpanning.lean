/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterLeading

/-!
# Gordon spanning of the PBW-length filtration of `L(c_{2,2n+3}, 0)`

The generalisation of the Lee–Yang gap-two straightening (`LeeYangCharacterSpanning`) to every
member of the `(2, 2n+3)` series.  A sorted creation word `u = [u₀ ≥ u₁ ≥ ⋯]` (entry `j` standing
for `L_{-j-2}`) is **Gordon-good of order `n`** (`GordonGood n u`) if
`u_i ≥ u_{i+n} + 2` for every `i` — "difference two at distance `n`".  In terms of the
frequencies `f_m` of the parts `m = j + 2` this is the Andrews–Gordon condition
`f_m + f_{m+1} ≤ n`.  For `n = 1` it is the Rogers–Ramanujan gap-two condition.

* `comps m k`, `jetSum_eq_sum` — the jet sum `jetSum c m k` is the sum of the words of `m`
  letters summing to `k`;
* `sqSum_lt_of_not_perm` — the balanced multiset (all entries in `{b, b+1}`) is the unique
  minimiser of the sum of squares among multisets of the same size and sum;
* `sorted_mem_goodSpanG` — under `HasJetRelations c n`, every sorted word of length `ℓ` lies in
  the span of Gordon-good words of length `≤ ℓ` (same energy) modulo the maximal ideal;
* `goodFil_eq_gordonSpan` — the length-`≤ p`, weight-`N` step of the PBW flag of `L(c,0)` is
  the image of the span of Gordon-good words of length `≤ p` and energy `N`.

The straightening is the leading-term argument for the jet relations of `x(z)^{n+1} = 0`: a
sorted word with a violating window `u_i ≤ u_{i+n} + 1` is rewritten, modulo the ideal and the
strictly lower length step, through words of the same length whose entries are strictly more
spread out (larger sum of squares).  Everything here is proved from `HasJetRelations c n`, which
`TwoSeriesCharacterLeading.twoSeries_hasJetRelations` proves at `c = c_{2,2n+3}` for `n ≥ 1`.
-/

namespace VOA.TwoSeriesCharacter

open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYangCharacter
open scoped BigOperators

noncomputable section

/-! ## §1  Jet sums as sums of words -/

/-- Words of `m` letters with letter sum `k`. -/
def comps : ℕ → ℕ → Finset (List ℕ)
  | 0, k => if k = 0 then {[]} else ∅
  | m + 1, k => (Finset.antidiagonal k).biUnion
      (fun p => (comps m p.2).map ⟨List.cons p.1, List.cons_injective⟩)

theorem mem_comps : ∀ (m k : ℕ) (e : List ℕ), e ∈ comps m k ↔ e.length = m ∧ e.sum = k
  | 0, k, e => by
      by_cases hk : k = 0
      · subst hk
        simp only [comps, if_true, Finset.mem_singleton]
        constructor
        · rintro rfl; simp
        · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
      · simp only [comps, hk, if_false, Finset.notMem_empty, false_iff]
        rintro ⟨h, hs⟩
        rw [List.eq_nil_of_length_eq_zero h] at hs
        simp at hs; omega
  | m + 1, k, e => by
      rcases e with _ | ⟨a, e⟩
      · simp [comps]
      · simp only [comps, Finset.mem_biUnion, Finset.mem_map, Finset.mem_antidiagonal,
          Function.Embedding.coeFn_mk, List.cons.injEq, List.length_cons, List.sum_cons]
        constructor
        · rintro ⟨⟨p1, p2⟩, hp, e', he', h1, h2⟩
          dsimp only at hp h1
          subst h1 h2
          rw [mem_comps] at he'
          omega
        · rintro ⟨hl, hs⟩
          exact ⟨(a, e.sum), by dsimp only; omega, e, (mem_comps m _ e).mpr ⟨by omega, rfl⟩,
            rfl, rfl⟩

variable (c : ℂ)

theorem jetSum_eq_sum : ∀ (m k : ℕ), jetSum c m k = ∑ e ∈ comps m k, negWordVir c e
  | 0, k => by
      by_cases hk : k = 0
      · subst hk; simp [jetSum, comps]
      · simp [jetSum, comps, hk]
  | m + 1, k => by
      rw [jetSum_succ, comps, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [jetSum_eq_sum m p.2, map_sum, Finset.sum_map]
        rfl
      · intro p hp q hq hpq
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx'
        obtain ⟨e, -, rfl⟩ := hx
        obtain ⟨e', -, he⟩ := hx'
        have h1 : q.1 = p.1 := (List.cons.inj he).1
        have hp' := Finset.mem_antidiagonal.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_antidiagonal.mp (Finset.mem_coe.mp hq)
        exact hpq (Prod.ext h1.symm (by omega))

/-! ## §2  Gordon-good words and violating windows -/

/-- **Gordon-good of order `n`**: `u_i ≥ u_{i+n} + 2` whenever both entries exist. -/
def GordonGood (n : ℕ) (w : List ℕ) : Prop :=
  ∀ i < w.length - n, w.getD (i + n) 0 + 2 ≤ w.getD i 0

instance (n : ℕ) (w : List ℕ) : Decidable (GordonGood n w) := by
  unfold GordonGood; infer_instance

theorem sorted_getElem_le {u : List ℕ} (hs : SortedWord u) {a b : ℕ} (hab : a ≤ b)
    (hb : b < u.length) : u[b] ≤ u[a]'(by omega) := by
  rcases hab.lt_or_eq with h | rfl
  · exact List.pairwise_iff_getElem.mp hs a b (by omega) hb h
  · exact le_rfl

/-- A sorted word that is not Gordon-good has a window of `n+1` consecutive entries all lying in
some `{b, b+1}`. -/
theorem exists_window {n : ℕ} {u : List ℕ} (hs : SortedWord u) (hg : ¬ GordonGood n u) :
    ∃ l₁ W l₂ : List ℕ, ∃ b : ℕ, u = l₁ ++ W ++ l₂ ∧ W.length = n + 1 ∧
      ∀ x ∈ W, b ≤ x ∧ x ≤ b + 1 := by
  unfold GordonGood at hg
  push_neg at hg
  obtain ⟨i, hi, hlt⟩ := hg
  have hin : i + n < u.length := by omega
  rw [List.getD_eq_getElem _ _ hin, List.getD_eq_getElem _ _ (by omega)] at hlt
  refine ⟨u.take i, (u.drop i).take (n + 1), (u.drop i).drop (n + 1), u[i + n], ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · simp only [List.length_take, List.length_drop]; omega
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_take, List.length_drop] at hj
    simp only [List.getElem_take, List.getElem_drop]
    constructor
    · exact sorted_getElem_le hs (by omega) hin
    · have := sorted_getElem_le hs (a := i) (b := i + j) (by omega) (by omega)
      omega

/-! ## §3  The balanced multiset minimises the sum of squares -/

theorem sqSum_cons (a : ℕ) (l : List ℕ) : sqSum (a :: l) = a ^ 2 + sqSum l := by
  simp [sqSum]

theorem sqSum_append (l l' : List ℕ) : sqSum (l ++ l') = sqSum l + sqSum l' := by
  simp [sqSum, List.sum_append]

/-- The defect `Σ (x-b)(x-b-1) ≥ 0`. -/
def defect (b : ℕ) (l : List ℕ) : ℤ :=
  (l.map (fun x : ℕ => ((x : ℤ) - b) * ((x : ℤ) - b - 1))).sum

theorem defect_cons (b a : ℕ) (l : List ℕ) :
    defect b (a :: l) = ((a : ℤ) - b) * ((a : ℤ) - b - 1) + defect b l := by
  simp [defect]

theorem term_nonneg (a b : ℕ) : 0 ≤ ((a : ℤ) - b) * ((a : ℤ) - b - 1) := by
  rcases le_or_gt a b with h | h
  · have h' : (a : ℤ) ≤ b := by exact_mod_cast h
    nlinarith
  · have h' : (b : ℤ) + 1 ≤ a := by exact_mod_cast h
    nlinarith

theorem defect_nonneg (b : ℕ) : ∀ l : List ℕ, 0 ≤ defect b l
  | [] => by simp [defect]
  | a :: l => by rw [defect_cons]; exact add_nonneg (term_nonneg a b) (defect_nonneg b l)

theorem sqSum_eq_defect (b : ℕ) : ∀ l : List ℕ,
    (sqSum l : ℤ) = defect b l + (2 * b + 1) * (l.sum : ℤ) - l.length * (b * (b + 1))
  | [] => by simp [sqSum, defect]
  | a :: l => by
      rw [sqSum_cons, defect_cons, List.sum_cons, List.length_cons]
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_mul]
      rw [sqSum_eq_defect b l]
      ring

theorem window_of_defect_zero (b : ℕ) : ∀ l : List ℕ, defect b l = 0 →
    ∀ x ∈ l, b ≤ x ∧ x ≤ b + 1
  | [], _ => by simp
  | a :: l, h => by
      rw [defect_cons] at h
      have h1 := term_nonneg a b
      have h2 := defect_nonneg b l
      have ha : ((a : ℤ) - b) * ((a : ℤ) - b - 1) = 0 := by linarith
      have hl : defect b l = 0 := by linarith
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases mul_eq_zero.mp ha with h0 | h0
        · constructor <;> omega
        · constructor <;> omega
      · exact window_of_defect_zero b l hl x hx

theorem defect_window (b : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, b ≤ x ∧ x ≤ b + 1) → defect b l = 0
  | [], _ => by simp [defect]
  | a :: l, h => by
      rw [defect_cons, defect_window b l (fun x hx => h x (List.mem_cons_of_mem a hx))]
      obtain ⟨h1, h2⟩ := h a (List.mem_cons_self)
      rcases (by omega : a = b ∨ a = b + 1) with rfl | rfl
      · simp
      · push_cast; ring

/-- Window lists: the sum and the counts of `b`, `b+1`. -/
theorem window_counts (b : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, b ≤ x ∧ x ≤ b + 1) →
    l.sum = b * l.length + l.count (b + 1) ∧ l.count b + l.count (b + 1) = l.length
  | [], _ => by simp
  | a :: l, h => by
      obtain ⟨ih1, ih2⟩ := window_counts b l (fun x hx => h x (List.mem_cons_of_mem a hx))
      obtain ⟨h1, h2⟩ := h a (List.mem_cons_self)
      simp only [List.sum_cons, List.length_cons, List.count_cons, beq_iff_eq]
      rcases (by omega : a = b ∨ a = b + 1) with rfl | rfl
      · simp only [if_true, show ¬ (a = a + 1) by omega, if_false]
        constructor <;> nlinarith
      · simp only [if_true, show ¬ (b + 1 = b) by omega, if_false]
        constructor <;> nlinarith

theorem perm_of_window {b : ℕ} {e W : List ℕ} (he : ∀ x ∈ e, b ≤ x ∧ x ≤ b + 1)
    (hW : ∀ x ∈ W, b ≤ x ∧ x ≤ b + 1) (hl : e.length = W.length) (hs : e.sum = W.sum) :
    e.Perm W := by
  rw [List.perm_iff_count]
  intro a
  obtain ⟨e1, e2⟩ := window_counts b e he
  obtain ⟨w1, w2⟩ := window_counts b W hW
  have hc1 : e.count (b + 1) = W.count (b + 1) := by rw [hl] at e1; omega
  by_cases ha : a = b + 1
  · subst ha; exact hc1
  by_cases hb : a = b
  · subst hb; omega
  rw [List.count_eq_zero.mpr, List.count_eq_zero.mpr]
  · intro hx; have := hW a hx; omega
  · intro hx; have := he a hx; omega

/-- **Strict minimality of the balanced multiset.** -/
theorem sqSum_lt_of_not_perm {b : ℕ} {e W : List ℕ} (hW : ∀ x ∈ W, b ≤ x ∧ x ≤ b + 1)
    (hl : e.length = W.length) (hs : e.sum = W.sum) (hp : ¬ e.Perm W) :
    sqSum W < sqSum e := by
  have h1 := sqSum_eq_defect b e
  have h2 := sqSum_eq_defect b W
  rw [defect_window b W hW] at h2
  have hd := defect_nonneg b e
  have hd0 : defect b e ≠ 0 := fun h0 =>
    hp (perm_of_window (window_of_defect_zero b e h0) hW hl hs)
  have : (sqSum W : ℤ) < sqSum e := by
    rw [h1, h2, hl, hs]
    have : 0 < defect b e := lt_of_le_of_ne hd (Ne.symm hd0)
    linarith
  exact_mod_cast this

/-! ## §4  The straightening -/

variable (n : ℕ)

/-- Gordon-good sorted words of length `≤ ℓ` and energy `N`. -/
def gordonSpan (ℓ N : ℕ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ
    {x | ∃ u : List ℕ, SortedWord u ∧ GordonGood n u ∧ energyVir u = N ∧ u.length ≤ ℓ ∧
      negWordVir c u = x}

/-- Gordon-good words plus the maximal ideal. -/
def goodSpanG (ℓ N : ℕ) : Submodule ℂ (VirUniv c) :=
  gordonSpan c n ℓ N ⊔ maxIdealVir c

theorem gordonSpan_mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') (N : ℕ) :
    gordonSpan c n ℓ N ≤ gordonSpan c n ℓ' N :=
  Submodule.span_mono fun _ ⟨u, hs, hu, he, hl, hx⟩ => ⟨u, hs, hu, he, hl.trans h, hx⟩

theorem goodSpanG_mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') (N : ℕ) :
    goodSpanG c n ℓ N ≤ goodSpanG c n ℓ' N :=
  sup_le_sup_right (gordonSpan_mono c n h N) _

/-- **Straightening.**  Given the jet relations, every sorted word of length `ℓ` lies in the
span of Gordon-good words of length `≤ ℓ` and the same energy, modulo the maximal ideal. -/
theorem sorted_mem_goodSpanG (hJ : HasJetRelations c n) : ∀ ℓ : ℕ, ∀ u : List ℕ,
    SortedWord u → u.length = ℓ → negWordVir c u ∈ goodSpanG c n ℓ (energyVir u) := by
  classical
  obtain ⟨α, hα, hrel⟩ := hJ
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  have hlowFil : ∀ (N m : ℕ), m < ℓ → virFil c m (N : ℤ) ≤ goodSpanG c n ℓ N := by
    intro N m hm
    rw [virFil, Submodule.span_le]
    rintro _ ⟨u, hu, hen, hl, rfl⟩
    have hen' : energyVir u = N := by exact_mod_cast hen
    have := ihℓ u.length (by omega) u hu rfl
    rw [hen'] at this
    exact goodSpanG_mono c n (by omega) N this
  suffices H : ∀ t : ℕ, ∀ u : List ℕ, SortedWord u → u.length = ℓ →
      energyVir u ^ 2 - sqSum u = t → negWordVir c u ∈ goodSpanG c n ℓ (energyVir u) by
    intro u hu hl
    exact H _ u hu hl rfl
  intro t
  induction t using Nat.strong_induction_on with
  | _ t iht =>
  intro u hu hl ht
  by_cases hg : GordonGood n u
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, hg, rfl, hl.le, rfl⟩)
  obtain ⟨l₁, W, l₂, b, rfl, hWl, hWb⟩ := exists_window hu hg
  set u := l₁ ++ W ++ l₂ with hu_def
  set r := l₁ ++ l₂ with hr
  set N := energyVir u with hN
  set k := W.sum with hk
  have hperm : (r ++ W).Perm u := by
    rw [hr, hu_def, List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left l₁
  have hlenr : r.length + (n + 1) = ℓ := by
    have h1 := hperm.length_eq
    simp only [hu_def, hr, List.length_append] at h1 hl ⊢
    omega
  have hEe : ∀ e : List ℕ, e.length = n + 1 → e.sum = k → energyVir (r ++ e) = N := by
    intro e hel hes
    rw [hN, ← energyVir_perm hperm, energyVir_eq_sum, energyVir_eq_sum]
    simp only [List.sum_append, List.length_append]
    rw [hel, hes, hWl]
  have hEr : 2 * n + 2 + k + energyVir r = N := by
    rw [hN, ← energyVir_perm hperm, energyVir_eq_sum, energyVir_eq_sum]
    simp only [List.sum_append, List.length_append]
    rw [hWl]; ring
  obtain ⟨σ, hσ, hlead⟩ := hrel k
  have h1 : applyWord c r σ ∈ goodSpanG c n ℓ N :=
    Submodule.mem_sup_right (applyWord_mem_maxIdealVir c r hσ)
  have h2 : applyWord c r (σ - α • jetSum c (n + 1) k) ∈ goodSpanG c n ℓ N := by
    have := applyWord_mem_virFil c r hlead
    rw [hEr] at this
    exact hlowFil N _ (by omega) this
  have hJsum : applyWord c r (jetSum c (n + 1) k) =
      ∑ e ∈ comps (n + 1) k, negWordVir c (r ++ e) := by
    rw [jetSum_eq_sum, map_sum]
    simp only [negWordVir_append]
  have hterm : ∀ e ∈ comps (n + 1) k,
      negWordVir c (r ++ e) - (if e.Perm W then (1 : ℂ) else 0) • negWordVir c u ∈
        goodSpanG c n ℓ N := by
    intro e he
    obtain ⟨hel, hes⟩ := (mem_comps _ _ e).mp he
    set w := r ++ e with hw
    have hwE : energyVir w = N := hEe e hel hes
    have hwl : w.length = ℓ := by rw [hw, List.length_append, hel, hlenr]
    have hdiff := negWordVir_sub_sortDesc_mem c w
    rw [hwE, hwl] at hdiff
    have hdiff' : negWordVir c w - negWordVir c (sortDesc w) ∈ goodSpanG c n ℓ N :=
      hlowFil N _ (by omega) hdiff
    by_cases hpe : e.Perm W
    · rw [if_pos hpe, one_smul]
      have hwu : sortDesc w = u := by
        have hpw : w.Perm u := (List.Perm.append_left r hpe).trans hperm
        exact List.Perm.eq_of_pairwise (fun x y _ _ h1 h2 => le_antisymm h2 h1)
          (sortDesc_sorted w) hu ((sortDesc_perm w).trans hpw)
      rwa [hwu] at hdiff'
    · rw [if_neg hpe, zero_smul, sub_zero]
      have hsq : sqSum u < sqSum (sortDesc w) := by
        have e1 : sqSum (sortDesc w) = sqSum r + sqSum e :=
          (sqSum_perm (sortDesc_perm w)).trans (sqSum_append r e)
        have e2 : sqSum u = sqSum r + sqSum W := (sqSum_perm hperm).symm.trans (sqSum_append r W)
        have := sqSum_lt_of_not_perm hWb (by rw [hel, hWl]) hes hpe
        omega
      have hsE : energyVir (sortDesc w) = N := by rw [energyVir_sortDesc, hwE]
      have hbound := sqSum_le (sortDesc w)
      rw [hsE] at hbound
      have hmem := iht (energyVir (sortDesc w) ^ 2 - sqSum (sortDesc w))
        (by rw [← ht, hsE]; omega) (sortDesc w) (sortDesc_sorted w)
        (by rw [length_sortDesc, hwl]) rfl
      rw [hsE] at hmem
      have := Submodule.add_mem _ hdiff' hmem
      simpa using this
  have hsum := Submodule.sum_mem (goodSpanG c n ℓ N) hterm
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_boole] at hsum
  set m : ℂ := (((comps (n + 1) k).filter (fun e => e.Perm W)).card : ℂ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Nat.cast_ne_zero]
    apply Finset.card_ne_zero_of_mem (a := W)
    rw [Finset.mem_filter, mem_comps]
    exact ⟨⟨hWl, rfl⟩, List.Perm.refl W⟩
  have hcomb : (α * m) • negWordVir c u =
      applyWord c r σ - applyWord c r (σ - α • jetSum c (n + 1) k) -
        α • ((∑ e ∈ comps (n + 1) k, negWordVir c (r ++ e)) - m • negWordVir c u) := by
    rw [map_sub, map_smul, hJsum, mul_smul]; module
  have hαm : α * m ≠ 0 := mul_ne_zero hα hm0
  have h5 : (α * m) • negWordVir c u ∈ goodSpanG c n ℓ N := by
    rw [hcomb]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ hsum)
  have := Submodule.smul_mem _ (α * m)⁻¹ h5
  rwa [smul_smul, inv_mul_cancel₀ hαm, one_smul] at this

/-- The universal length step is contained in Gordon-good words plus the maximal ideal. -/
theorem virFil_le_goodSpanG (hJ : HasJetRelations c n) (ℓ N : ℕ) :
    virFil c ℓ (N : ℤ) ≤ goodSpanG c n ℓ N := by
  rw [virFil, Submodule.span_le]
  rintro _ ⟨u, hu, hen, hl, rfl⟩
  have hen' : energyVir u = N := by exact_mod_cast hen
  have := sorted_mem_goodSpanG c n hJ u.length u hu rfl
  rw [hen'] at this
  exact goodSpanG_mono c n hl N this

theorem gordonSpan_le_virFil (ℓ N : ℕ) : gordonSpan c n ℓ N ≤ virFil c ℓ (N : ℤ) := by
  rw [gordonSpan, Submodule.span_le]
  rintro _ ⟨u, hs, -, hen, hl, rfl⟩
  exact negWordVir_mem_virFil_of_sorted c hs hl hen

/-- **Gordon spanning of the PBW flag.**  Under the jet relations of order `n+1`, the
length-`≤ p`, weight-`N` step of the length filtration on `L(c,0)` is the image of the span of
Gordon-good words of length `≤ p` and energy `N`. -/
theorem goodFil_eq_gordonSpan (hJ : HasJetRelations c n) (p N : ℕ) :
    goodFil c p (N : ℤ) = (gordonSpan c n p N).map (maxIdealVir c).mkQ := by
  apply le_antisymm
  · rw [goodFil]
    refine (Submodule.map_mono (virFil_le_goodSpanG c n hJ p N)).trans ?_
    rw [goodSpanG, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  · exact Submodule.map_mono (gordonSpan_le_virFil c n p N)

end

end VOA.TwoSeriesCharacter
