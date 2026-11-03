import VOA.Classification.COne.OrbRat4Cert

/-! # Normal forms of the evaluator are faithful

`reduceR 8 Q` (sort, merge, reduce `c² = 8`, sort and merge again) always returns a list with
pairwise distinct words, nonzero coefficients, sorted words and at most one charge variable per
word (`RN_reduceR`).  On such lists the evaluation `evRc` at `c = cα 4` (with `c² = 8`, so `c` is
irrational) is injective enough to read the list back from its value (`RN_eval_zero`,
`RN_eval_single`).  Together with the separation of the charge sectors this turns the semantic
identity `evalSt s = w • h(-1)1` into the literal bucket identity (`bucket_eq_of_eval`).
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod
  OrbRat3

/-! ## 1. `compareWord` is a strict total order on `ℕ`-words -/

theorem cw_swap : ∀ a b : List ℕ, compareWord b a = (compareWord a b).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | i :: is, j :: js => by
    simp only [compareWord]
    by_cases h1 : i < j
    · rw [if_neg (by omega), if_pos h1, if_pos h1]; rfl
    · by_cases h2 : j < i
      · rw [if_pos h2, if_neg h1, if_pos h2]; rfl
      · rw [if_neg h2, if_neg h1, if_neg h2, if_neg h1, cw_swap is js]

theorem cw_self (a : List ℕ) : compareWord a a = .eq := (compareWord_eq_iff a a).mpr rfl

theorem cw_trans : ∀ a b c : List ℕ,
    compareWord a b = .lt → compareWord b c = .lt → compareWord a c = .lt
  | [], [], _, h, _ => by simp [compareWord] at h
  | [], _ :: _, [], _, h => by simp [compareWord] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [compareWord] at h
  | _ :: _, _ :: _, [], _, h => by simp [compareWord] at h
  | i :: is, j :: js, k :: ks, h1, h2 => by
    simp only [compareWord] at h1 h2 ⊢
    by_cases hij : i < j
    · by_cases hjk : j < k
      · rw [if_pos (by omega)]
      · rw [if_neg hjk] at h2
        by_cases hkj : k < j
        · rw [if_pos hkj] at h2; exact absurd h2 (by decide)
        · rw [if_pos (by omega)]
    · rw [if_neg hij] at h1
      by_cases hji : j < i
      · rw [if_pos hji] at h1; exact absurd h1 (by decide)
      · rw [if_neg hji] at h1
        have hij' : i = j := by omega
        subst hij'
        by_cases hik : i < k
        · rw [if_pos hik]
        · rw [if_neg hik] at h2 ⊢
          by_cases hki : k < i
          · rw [if_pos hki] at h2; exact absurd h2 (by decide)
          · rw [if_neg hki] at h2 ⊢
            exact cw_trans is js ks h1 h2

/-! ## 2. Invariants of the sorted insertion -/

/-- Strictly increasing words. -/
def StrictP (P : SparseRational.Poly ℕ) : Prop := P.Pairwise (fun x y => compareWord x.1 y.1 = .lt)

theorem mem_insertSorted (w : List ℕ) (q : ℚ) : ∀ (P : SparseRational.Poly ℕ) (x : List ℕ × ℚ),
    x ∈ insertSorted w q P → x ∈ P ∨ (x.1 = w ∧ x.2 ≠ 0)
  | [], x, hx => by
    simp only [insertSorted] at hx
    split_ifs at hx with hq
    · simp at hx
    · simp only [List.mem_singleton] at hx; subst hx; exact Or.inr ⟨rfl, hq⟩
  | (v, c) :: P, x, hx => by
    rw [insertSorted] at hx
    by_cases hq : q = 0
    · rw [if_pos hq] at hx; exact Or.inl hx
    · rw [if_neg hq] at hx
      generalize hcmp : compareWord w v = cmp at hx
      cases cmp with
      | lt =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr ⟨rfl, hq⟩
        · exact Or.inl (List.mem_cons.mpr hx)
      | gt =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inl List.mem_cons_self
        · rcases mem_insertSorted w q P x hx with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
      | eq =>
        have hwv : w = v := (compareWord_eq_iff w v).mp hcmp
        simp only at hx
        by_cases hqc : q + c = 0
        · rw [if_pos hqc] at hx; exact Or.inl (List.mem_cons_of_mem _ hx)
        · rw [if_neg hqc] at hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inr ⟨hwv.symm, hqc⟩
          · exact Or.inl (List.mem_cons_of_mem _ hx)

theorem strict_insertSorted (w : List ℕ) (q : ℚ) : ∀ P : SparseRational.Poly ℕ,
    StrictP P → StrictP (insertSorted w q P)
  | [], _ => by
    simp only [insertSorted]
    split_ifs <;> simp [StrictP]
  | (v, c) :: P, hP => by
    have hP' := List.pairwise_cons.mp hP
    rw [insertSorted]
    by_cases hq : q = 0
    · rw [if_pos hq]; exact hP
    · rw [if_neg hq]
      generalize hcmp : compareWord w v = cmp
      cases cmp with
      | lt =>
        refine List.pairwise_cons.mpr ⟨?_, hP⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hcmp
        · exact cw_trans _ _ _ hcmp (hP'.1 y hy)
      | gt =>
        refine List.pairwise_cons.mpr ⟨?_, strict_insertSorted w q P hP'.2⟩
        intro y hy
        rcases mem_insertSorted w q P y hy with h | ⟨h, -⟩
        · exact hP'.1 y h
        · rw [h, cw_swap, hcmp]; rfl
      | eq =>
        simp only
        by_cases hqc : q + c = 0
        · rw [if_pos hqc]; exact hP'.2
        · rw [if_neg hqc]; exact List.pairwise_cons.mpr ⟨fun y hy => hP'.1 y hy, hP'.2⟩

theorem strictP_nodup {P : SparseRational.Poly ℕ} (h : StrictP P) : (P.map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine h.imp ?_
  intro x y hxy hxy'
  rw [hxy', cw_self] at hxy
  exact absurd hxy (by decide)

theorem insertVar_eq (i : ℕ) : ∀ w : List ℕ, insertVar i w = w.orderedInsert (· ≤ ·) i
  | [] => rfl
  | j :: js => by
    simp only [insertVar, List.orderedInsert]
    split_ifs
    · rfl
    · rw [insertVar_eq i js]

theorem sortWord_eq : ∀ w : List ℕ, sortWord w = w.insertionSort (· ≤ ·)
  | [] => rfl
  | i :: is => by rw [sortWord, sortWord_eq is, insertVar_eq]; rfl

theorem sortWord_sorted (w : List ℕ) : (sortWord w).Pairwise (· ≤ ·) := by
  rw [sortWord_eq]; exact List.pairwise_insertionSort _ _

/-- The invariants of `normalizeQ`. -/
theorem normalizeQ_inv : ∀ P : RawPoly ℕ, StrictP (normalizeQ P) ∧
    ∀ x ∈ normalizeQ P, x.2 ≠ 0 ∧ x.1.Pairwise (· ≤ ·) ∧ ∃ t ∈ P, x.1 = sortWord t.2
  | [] => ⟨by simp [normalizeQ, StrictP], by simp [normalizeQ]⟩
  | (q, w) :: P => by
    obtain ⟨h1, h2⟩ := normalizeQ_inv P
    refine ⟨strict_insertSorted _ _ _ h1, ?_⟩
    intro x hx
    rcases mem_insertSorted _ _ _ x hx with h | ⟨h, hq⟩
    · obtain ⟨a, b, t, ht, e⟩ := h2 x h
      exact ⟨a, b, t, List.mem_cons_of_mem _ ht, e⟩
    · refine ⟨hq, ?_, (q, w), List.mem_cons_self, h⟩
      rw [h]; exact sortWord_sorted w

/-! ## 3. The charge reduction on sorted words -/

theorem reduceWordR_of_no_zero (K : ℚ) : ∀ w : List ℕ, 0 ∉ w → reduceWordR K w = [(1, w)]
  | [], _ => rfl
  | [_], _ => rfl
  | i :: j :: w, h => by
    have hi : i ≠ 0 := fun e => h (e ▸ List.mem_cons_self)
    rw [reduceWordR, if_neg (fun e => hi e.1),
      reduceWordR_of_no_zero K (j :: w) (fun e => h (List.mem_cons_of_mem _ e))]
    rfl

theorem reduceWordR_count (K : ℚ) : ∀ w : List ℕ, w.Pairwise (· ≤ ·) →
    ∀ t ∈ reduceWordR K w, t.2.count 0 ≤ 1
  | [], _, t, ht => by rw [reduceWordR, List.mem_singleton] at ht; subst ht; simp
  | [i], _, t, ht => by
    rw [reduceWordR, List.mem_singleton] at ht
    subst ht
    by_cases hi : i = 0 <;> simp [hi]
  | i :: j :: w, hw, t, ht => by
    rw [reduceWordR] at ht
    split_ifs at ht with hij
    · simp only [scaleR, List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact reduceWordR_count K w (List.pairwise_cons.mp (List.pairwise_cons.mp hw).2).2 u hu
    · simp only [prependC, List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hjw : (j :: w).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hw).2
      by_cases hi : i = 0
      · subst hi
        have hj : j ≠ 0 := fun e => hij ⟨rfl, e⟩
        have hnz : 0 ∉ j :: w := by
          intro h0
          rcases List.mem_cons.mp h0 with e | e
          · exact hj e.symm
          · have := (List.pairwise_cons.mp hjw).1 0 e; omega
        rw [reduceWordR_of_no_zero K _ hnz, List.mem_singleton] at hu
        subst hu
        simp only [List.count_cons_self]
        rw [List.count_eq_zero.mpr hnz]
      · simp only [List.count_cons, beq_iff_eq]
        rw [if_neg hi, add_zero]
        exact reduceWordR_count K (j :: w) hjw u hu

/-! ## 4. Reduced normal forms -/

/-- A reduced normal form: distinct words, nonzero coefficients, sorted words, and at most one
charge variable per word. -/
def RN (L : RawPoly ℕ) : Prop :=
  (L.map Prod.snd).Nodup ∧ ∀ t ∈ L, t.1 ≠ 0 ∧ t.2.Pairwise (· ≤ ·) ∧ t.2.count 0 ≤ 1

theorem normR_inv (P : RawPoly ℕ) : ((normR P).map Prod.snd).Nodup ∧
    ∀ x ∈ normR P, x.1 ≠ 0 ∧ x.2.Pairwise (· ≤ ·) ∧ ∃ t ∈ P, x.2 = sortWord t.2 := by
  obtain ⟨h1, h2⟩ := normalizeQ_inv P
  refine ⟨?_, ?_⟩
  · rw [normR, toRaw, List.map_map]
    exact strictP_nodup h1
  · intro x hx
    simp only [normR, toRaw, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h2 y hy

theorem RN_reduceR (K : ℚ) (Q : RawPoly ℕ) : RN (reduceR K Q) := by
  obtain ⟨h1, h2⟩ := normR_inv ((normR Q).flatMap fun t => scaleR t.1 (reduceWordR K t.2))
  refine ⟨h1, ?_⟩
  intro x hx
  obtain ⟨hx0, hxs, t, ht, hxt⟩ := h2 x hx
  refine ⟨hx0, hxs, ?_⟩
  simp only [List.mem_flatMap, scaleR, List.mem_map] at ht
  obtain ⟨u, hu, v, hv, rfl⟩ := ht
  obtain ⟨-, hus, -⟩ := (normR_inv Q).2 u hu
  rw [hxt, (List.perm_iff_count.mp (sortWord_perm v.2)) 0]
  exact reduceWordR_count K u.2 hus v hv

/-! ## 5. Reading a reduced normal form back from its value -/

section Coeff
variable {r : ℕ} (a : Fin r)

/-- The oscillator exponent of a charged word. -/
noncomputable def oscExp : List ℕ → (ℕ × Fin r) →₀ ℕ
  | [] => 0
  | 0 :: w => oscExp w
  | (i + 1) :: w => Finsupp.single (i, a) 1 + oscExp w

theorem evalWord_xvc (c : ℂ) : ∀ w : List ℕ,
    evalWord (xvc a c) w = MvPolynomial.C (c ^ w.count 0) * MvPolynomial.monomial (oscExp a w) 1
  | [] => by simp [evalWordC_nil, oscExp]
  | 0 :: w => by
    rw [evalWordC_cons, evalWord_xvc c w, List.count_cons_self, oscExp, pow_succ]
    simp only [xvc, map_mul]
    ring
  | (i + 1) :: w => by
    rw [evalWordC_cons, evalWord_xvc c w, oscExp]
    simp only [xvc, List.count_cons, beq_iff_eq, Nat.succ_ne_zero, if_false, add_zero]
    rw [MvPolynomial.X, mul_left_comm, MvPolynomial.monomial_mul, one_mul]

theorem coeff_evRc (c : ℂ) (m : (ℕ × Fin r) →₀ ℕ) : ∀ L : RawPoly ℕ,
    MvPolynomial.coeff m (evRc a c L) =
      (L.map fun t => if oscExp a t.2 = m then ((t.1 : ℚ) : ℂ) * c ^ t.2.count 0 else 0).sum
  | [] => by simp [evRc_nil]
  | (q, w) :: L => by
    rw [evRc_cons, MvPolynomial.coeff_add, MvPolynomial.coeff_smul, evalWord_xvc,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, coeff_evRc c m L, List.map_cons,
      List.sum_cons]
    congr 1
    split_ifs <;> simp

theorem oscExp_apply (i : ℕ) : ∀ w : List ℕ, oscExp a w (i, a) = w.count (i + 1)
  | [] => rfl
  | 0 :: w => by rw [oscExp, oscExp_apply i w, List.count_cons]; simp
  | (j + 1) :: w => by
    rw [oscExp, Finsupp.add_apply, oscExp_apply i w, List.count_cons, Finsupp.single_apply]
    by_cases h : j = i
    · subst h; simp; omega
    · rw [if_neg (by simp [h]), if_neg (by simp; omega)]; simp

theorem word_eq {w v : List ℕ} (hw : w.Pairwise (· ≤ ·)) (hv : v.Pairwise (· ≤ ·))
    (h0 : w.count 0 = v.count 0) (ho : oscExp a w = oscExp a v) : w = v := by
  have hc : ∀ j, w.count j = v.count j := by
    intro j
    cases j with
    | zero => exact h0
    | succ i => rw [← oscExp_apply a i, ← oscExp_apply a i, ho]
  exact List.Perm.eq_of_pairwise' hw hv (List.perm_iff_count.mpr hc)

end Coeff

theorem not_isSquare_eight : ¬ IsSquare (8 : ℚ) := by
  rw [Rat.isSquare_iff]
  decide +kernel

theorem rat_comb_zero (c : ℂ) (hc : c * c = 8) (A B : ℚ)
    (h : ((A : ℚ) : ℂ) + ((B : ℚ) : ℂ) * c = 0) : A = 0 ∧ B = 0 := by
  by_cases hB : B = 0
  · subst hB
    simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at h
    exact ⟨h, rfl⟩
  · exfalso
    have hB' : ((B : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hB
    have hcq : c = ((-A / B : ℚ) : ℂ) := by
      push_cast
      field_simp
      linear_combination h
    have hsq : ((-A / B) * (-A / B) : ℚ) = 8 := by
      have h8 : (((-A / B) * (-A / B) : ℚ) : ℂ) = ((8 : ℚ) : ℂ) := by
        rw [Rat.cast_mul, ← hcq, hc]; norm_num
      exact_mod_cast h8
    exact not_isSquare_eight ⟨-A / B, hsq.symm⟩

theorem list_sum_single {α β : Type*} [AddCommMonoid β] (L : List α)
    (hL : L.Nodup) (f : α → β) (t : α) (ht : t ∈ L) (h : ∀ s ∈ L, s ≠ t → f s = 0) :
    (L.map f).sum = f t := by
  classical
  rw [← List.sum_toFinset _ hL, Finset.sum_eq_single t
    (fun s hs hst => h s (List.mem_toFinset.mp hs) hst)
    (fun h' => absurd (List.mem_toFinset.mpr ht) h')]

section RN
variable {r : ℕ} (a : Fin r) (c : ℂ)

/-- The rational part of a coefficient. -/
noncomputable def cA (L : RawPoly ℕ) (m : (ℕ × Fin r) →₀ ℕ) : ℚ :=
  (L.map fun s => if oscExp a s.2 = m ∧ s.2.count 0 = 0 then s.1 else 0).sum

/-- The `c`-part of a coefficient. -/
noncomputable def cB (L : RawPoly ℕ) (m : (ℕ × Fin r) →₀ ℕ) : ℚ :=
  (L.map fun s => if oscExp a s.2 = m ∧ s.2.count 0 = 1 then s.1 else 0).sum

theorem coeff_split (L : RawPoly ℕ) (hL : ∀ t ∈ L, t.2.count 0 ≤ 1) (m : (ℕ × Fin r) →₀ ℕ) :
    MvPolynomial.coeff m (evRc a c L) = ((cA a L m : ℚ) : ℂ) + ((cB a L m : ℚ) : ℂ) * c := by
  rw [coeff_evRc]
  induction L with
  | nil => simp [cA, cB]
  | cons t L ih =>
    have ih' := ih (fun s hs => hL s (List.mem_cons_of_mem _ hs))
    simp only [cA, cB, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    push_cast
    have ht := hL t List.mem_cons_self
    by_cases ho : oscExp a t.2 = m
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h0 | h1
      · simp [ho, h0]; ring
      · simp [ho, h1]; ring
    · simp [ho]

theorem nodup_of_RN {L : RawPoly ℕ} (hL : RN L) : L.Nodup := List.Nodup.of_map _ hL.1

theorem eq_of_RN {L : RawPoly ℕ} (hL : RN L) {s t : ℚ × List ℕ} (hs : s ∈ L) (ht : t ∈ L)
    (h : s.2 = t.2) : s = t :=
  List.inj_on_of_nodup_map hL.1 hs ht h

theorem cA_of_mem {L : RawPoly ℕ} (hL : RN L) {t : ℚ × List ℕ} (ht : t ∈ L)
    (h0 : t.2.count 0 = 0) : cA a L (oscExp a t.2) = t.1 := by
  classical
  rw [cA, list_sum_single L (nodup_of_RN hL) _ t ht, if_pos ⟨rfl, h0⟩]
  intro s hs hst
  rw [if_neg]
  rintro ⟨ho, hz⟩
  exact hst (eq_of_RN hL hs ht (word_eq a (hL.2 s hs).2.1 (hL.2 t ht).2.1 (hz.trans h0.symm) ho))

theorem cB_of_mem {L : RawPoly ℕ} (hL : RN L) {t : ℚ × List ℕ} (ht : t ∈ L)
    (h1 : t.2.count 0 = 1) : cB a L (oscExp a t.2) = t.1 := by
  classical
  rw [cB, list_sum_single L (nodup_of_RN hL) _ t ht, if_pos ⟨rfl, h1⟩]
  intro s hs hst
  rw [if_neg]
  rintro ⟨ho, hz⟩
  exact hst (eq_of_RN hL hs ht (word_eq a (hL.2 s hs).2.1 (hL.2 t ht).2.1 (hz.trans h1.symm) ho))

/-- A nonzero coefficient sits at the oscillator exponent of every word of a reduced form. -/
theorem coeff_ne_zero {L : RawPoly ℕ} (hL : RN L) (hc : c * c = 8) {t : ℚ × List ℕ}
    (ht : t ∈ L) : MvPolynomial.coeff (oscExp a t.2) (evRc a c L) ≠ 0 := by
  rw [coeff_split a c L (fun s hs => (hL.2 s hs).2.2)]
  intro h
  obtain ⟨hA, hB⟩ := rat_comb_zero c hc _ _ h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hL.2 t ht).2.2 with h0 | h1
  · exact (hL.2 t ht).1 ((cA_of_mem a hL ht h0).symm.trans hA)
  · exact (hL.2 t ht).1 ((cB_of_mem a hL ht h1).symm.trans hB)

theorem RN_eval_zero {L : RawPoly ℕ} (hL : RN L) (hc : c * c = 8) (h : evRc a c L = 0) :
    L = [] := by
  rcases L with _ | ⟨t, L⟩
  · rfl
  · exact absurd (by rw [h]; simp) (coeff_ne_zero a c hL hc List.mem_cons_self)

theorem RN_eval_single {L : RawPoly ℕ} (hL : RN L) (hc : c * c = 8) (w : ℚ) (hw : w ≠ 0)
    (h : evRc a c L = evRc a c [(w, [1])]) : L = [(w, [1])] := by
  have hall : ∀ t ∈ L, t = (w, [1]) := by
    intro t ht
    have hco := coeff_ne_zero a c hL hc ht
    have hsp := coeff_split a c L (fun s hs => (hL.2 s hs).2.2) (oscExp a t.2)
    rw [h, coeff_evRc] at hco hsp
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hco hsp
    by_cases ho : oscExp a [1] = oscExp a t.2
    · rw [if_pos ho] at hsp
      have hz : ((w - cA a L (oscExp a t.2) : ℚ) : ℂ) + (((-cB a L (oscExp a t.2)) : ℚ) : ℂ) * c
          = 0 := by
        push_cast
        simp only [List.count_cons] at hsp
        simp at hsp
        linear_combination hsp
      obtain ⟨hA, hB⟩ := rat_comb_zero c hc _ _ hz
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hL.2 t ht).2.2 with h0 | h1
      · have hq := cA_of_mem a hL ht h0
        have hword : t.2 = [1] :=
          word_eq a (hL.2 t ht).2.1 (by simp) (by rw [h0]; rfl) ho.symm
        exact Prod.ext (by simp only; linarith) hword
      · have hq := cB_of_mem a hL ht h1
        exact absurd (by linarith) (hL.2 t ht).1
    · rw [if_neg ho] at hco
      exact absurd rfl hco
  rcases L with _ | ⟨t, L⟩
  · exfalso
    have := congrArg (MvPolynomial.coeff (oscExp a [1])) h
    rw [evRc_nil, coeff_evRc] at this
    simp at this
    exact hw (by exact_mod_cast this.symm)
  · rcases L with _ | ⟨s, L⟩
    · rw [hall t List.mem_cons_self]
    · exfalso
      have hts := hL.1
      rw [hall t List.mem_cons_self, hall s (List.mem_cons_of_mem _ List.mem_cons_self)] at hts
      simp at hts

end RN

/-! ## 6. Separating the charge sectors -/

/-- The charge-`d` component. -/
noncomputable def proj (d : ℤ) : LatModuleGen (latP 4) →ₗ[ℂ] FockN (rank (latP 4)) :=
  (TensorProduct.rid ℂ (FockN (rank (latP 4)))).toLinearMap ∘ₗ
    LinearMap.lTensor _ (Finsupp.lapply (d : (latP 4).carrier))

theorem proj_sector (d d' : ℤ) (p : FockN (rank (latP 4))) :
    proj d (sector d' p) = if d' = d then p else 0 := by
  simp only [proj, sector, LinearMap.coe_mk, AddHom.coe_mk, latStateGen, eGen,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul, Finsupp.lapply_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  by_cases hdd : d' = d
  · subst hdd; simp
  · rw [if_neg hdd]
    have h0 : (Finsupp.single (d' : (latP 4).carrier) (1 : ℂ)) (d : (latP 4).carrier) = 0 := by
      rw [Finsupp.single_apply, if_neg hdd]
    exact (congrArg (· • p) h0).trans (zero_smul ℂ p)

theorem cα_four_sq : cα 4 * cα 4 = 8 := by
  rw [cα_sq 4 four_ge_one]; norm_num

/-- The bucketed normal form is determined by the value: if a three-sector state evaluates to
`w • h(-1)1` with `w ≠ 0`, its bucket is literally `[(-2, []), (0, [(w, [1])]), (2, [])]`. -/
theorem bucket_eq_of_eval (s : St) (hs : ∀ p ∈ s, p.1 ∈ [-2, 0, 2]) (w : ℚ) (hw : w ≠ 0)
    (h : evalSt s = ((w : ℚ) : ℂ) • hV) :
    bucket [-2, 0, 2] s = [(-2, []), (0, [(w, [1])]), (2, [])] := by
  have hb := evalSt_bucket [-2, 0, 2] (by decide) s hs
  rw [h, ← sector_one] at hb
  simp only [bucket, List.map_cons, List.map_nil] at hb ⊢
  simp only [evalSt_cons, evalSt_nil, add_zero] at hb
  have e1 := congrArg (proj (-2)) hb
  have e2 := congrArg (proj 0) hb
  have e3 := congrArg (proj 2) hb
  simp only [map_add, proj_sector] at e1 e2 e3
  norm_num at e1 e2 e3
  rw [RN_eval_zero (a0 4) (cα 4) (RN_reduceR _ _) cα_four_sq e1,
    RN_eval_single (a0 4) (cα 4) (RN_reduceR _ _) cα_four_sq w hw e2,
    RN_eval_zero (a0 4) (cα 4) (RN_reduceR _ _) cα_four_sq e3]

end VOA.Classification.COne.OrbRat4
