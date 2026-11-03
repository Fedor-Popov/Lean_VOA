/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionTruncation

/-!
# PBW straightening for current-algebra modules

Generic in the structure constants `f`.  Fix a key `key : σ × ℕ → κ` into a linear order.  A loop
word is *sorted* if the keys are nondecreasing (`List.IsChain`).

* `wordOp_mem_sorted`: every loop word applied to any vector is a combination of sorted words of
  no greater length and the same `t`-degree (the spanning half of PBW, by induction on length and
  on the number of inversions; an adjacent swap costs one bracket, which is a shorter word).
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.DeligneAudit.SectorGraded

noncomputable section

variable {K σ : Type*} [Field K] {f : σ → σ → σ → K} [Fintype σ] {V : Type*} [AddCommGroup V]
  [Module K V]

theorem wordOp_append (ρ : CurrentModule f V) :
    ∀ (p q : List (σ × ℕ)) (v : V), wordOp ρ (p ++ q) v = wordOp ρ p (wordOp ρ q v)
  | [], q, v => rfl
  | (x :: p), q, v => by
      change ρ.op x.1 x.2 (wordOp ρ (p ++ q) v) = ρ.op x.1 x.2 (wordOp ρ p (wordOp ρ q v))
      rw [wordOp_append ρ p q v]

theorem wordOp_add (ρ : CurrentModule f V) :
    ∀ (p : List (σ × ℕ)) (u v : V), wordOp ρ p (u + v) = wordOp ρ p u + wordOp ρ p v
  | [], u, v => rfl
  | (x :: p), u, v => by
      change ρ.op x.1 x.2 (wordOp ρ p (u + v)) = ρ.op x.1 x.2 (wordOp ρ p u) + ρ.op x.1 x.2 (wordOp ρ p v)
      rw [wordOp_add ρ p u v, map_add]

theorem wordOp_smul (ρ : CurrentModule f V) :
    ∀ (p : List (σ × ℕ)) (c : K) (v : V), wordOp ρ p (c • v) = c • wordOp ρ p v
  | [], c, v => rfl
  | (x :: p), c, v => by
      change ρ.op x.1 x.2 (wordOp ρ p (c • v)) = c • ρ.op x.1 x.2 (wordOp ρ p v)
      rw [wordOp_smul ρ p c v, map_smul]

theorem wordOp_zero (ρ : CurrentModule f V) : ∀ (p : List (σ × ℕ)), wordOp ρ p (0 : V) = 0
  | [] => rfl
  | (x :: p) => by
      change ρ.op x.1 x.2 (wordOp ρ p 0) = 0
      rw [wordOp_zero ρ p, map_zero]

theorem wordOp_sum (ρ : CurrentModule f V) (p : List (σ × ℕ)) {ι : Type*} (s : Finset ι)
    (g : ι → V) : wordOp ρ p (∑ i ∈ s, g i) = ∑ i ∈ s, wordOp ρ p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wordOp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wordOp_add, ih]

/-- The adjacent swap: `x y ↦ y x` plus the bracket. -/
theorem wordOp_swap (ρ : CurrentModule f V) (p s : List (σ × ℕ)) (x y : σ × ℕ) (v : V) :
    wordOp ρ (p ++ x :: y :: s) v = wordOp ρ (p ++ y :: x :: s) v +
      ∑ e, f x.1 y.1 e • wordOp ρ (p ++ (e, x.2 + y.2) :: s) v := by
  simp only [wordOp_append]
  have hc := ρ.comm x.1 y.1 x.2 y.2 (wordOp ρ s v)
  have h1 : wordOp ρ (x :: y :: s) v = wordOp ρ (y :: x :: s) v +
      ∑ e, f x.1 y.1 e • ρ.op e (x.2 + y.2) (wordOp ρ s v) := by
    change ρ.op x.1 x.2 (ρ.op y.1 y.2 (wordOp ρ s v)) = ρ.op y.1 y.2 (ρ.op x.1 x.2 (wordOp ρ s v)) + _
    rw [← hc]; abel
  rw [h1, wordOp_add, wordOp_sum]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  rw [wordOp_smul]
  rfl

variable {κ : Type*} [LinearOrder κ] (key : σ × ℕ → κ)

/-- The number of inversions. -/
def invCount : List (σ × ℕ) → ℕ
  | [] => 0
  | (x :: l) => (l.filter fun z => key z < key x).length + invCount l

theorem filter_length_perm {l l' : List (σ × ℕ)} (h : l.Perm l') (P : σ × ℕ → Bool) :
    (l.filter P).length = (l'.filter P).length := (h.filter P).length_eq

theorem invCount_swap (p s : List (σ × ℕ)) (x y : σ × ℕ) (hxy : key y < key x) :
    invCount key (p ++ y :: x :: s) < invCount key (p ++ x :: y :: s) := by
  induction p with
  | nil =>
      simp only [List.nil_append, invCount, List.filter_cons, decide_eq_true_eq]
      have h1 : ¬ key x < key y := not_lt.mpr hxy.le
      simp only [h1, if_false, hxy, if_true, List.length_cons]
      omega
  | cons a p ih =>
      simp only [List.cons_append, invCount]
      have hp : (p ++ y :: x :: s).Perm (p ++ x :: y :: s) :=
        List.Perm.append_left p (List.Perm.swap x y s)
      rw [filter_length_perm hp]
      omega

theorem exists_descent :
    ∀ (l : List (σ × ℕ)), ¬ l.IsChain (fun a b => key a ≤ key b) →
      ∃ p s x y, l = p ++ x :: y :: s ∧ key y < key x
  | [] , h => absurd List.IsChain.nil h
  | [a], h => absurd (List.IsChain.singleton a) h
  | (a :: b :: l), h => by
      rw [List.isChain_cons_cons] at h
      by_cases hab : key a ≤ key b
      · obtain ⟨p, s, x, y, hl, hxy⟩ := exists_descent (b :: l) (fun h' => h ⟨hab, h'⟩)
        exact ⟨a :: p, s, x, y, by rw [hl]; rfl, hxy⟩
      · exact ⟨[], l, a, b, rfl, not_le.mp hab⟩

/-- Sorted words of length `≤ n` and degree `b`, applied to `v`. -/
def sortedSet (ρ : CurrentModule f V) (v : V) (n b : ℕ) : Set V :=
  {u | ∃ l : List (σ × ℕ), l.IsChain (fun a c => key a ≤ key c) ∧ l.length ≤ n ∧
    VOA.DeligneAudit.SectorGraded.wordDeg l = b ∧ u = wordOp ρ l v}

theorem wordDeg_append (p q : List (σ × ℕ)) :
    VOA.DeligneAudit.SectorGraded.wordDeg (p ++ q) =
      VOA.DeligneAudit.SectorGraded.wordDeg p + VOA.DeligneAudit.SectorGraded.wordDeg q := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

/-- **PBW spanning**: every word is a combination of sorted words of no greater length and the
same degree. -/
theorem wordOp_mem_sorted (ρ : CurrentModule f V) (v : V) :
    ∀ (n : ℕ) (l : List (σ × ℕ)), l.length = n →
      wordOp ρ l v ∈ Submodule.span K (sortedSet key ρ v n (VOA.DeligneAudit.SectorGraded.wordDeg l)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro l hl
    induction hk : invCount key l using Nat.strong_induction_on generalizing l with
    | _ k ihk =>
      by_cases hs : l.IsChain (fun a c => key a ≤ key c)
      · exact Submodule.subset_span ⟨l, hs, hl.le, rfl, rfl⟩
      obtain ⟨p, s, x, y, rfl, hxy⟩ := exists_descent key l hs
      rw [wordOp_swap]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ ?_)
      · have hlen : (p ++ y :: x :: s).length = n := by rw [← hl]; simp
        have hdeg : VOA.DeligneAudit.SectorGraded.wordDeg (p ++ y :: x :: s) =
            VOA.DeligneAudit.SectorGraded.wordDeg (p ++ x :: y :: s) := by
          simp only [VOA.DeligneAudit.SectorGraded.wordDeg, List.map_append, List.sum_append,
            List.map_cons, List.sum_cons]; omega
        have := ihk _ (by rw [← hk]; exact invCount_swap key p s x y hxy) _ hlen rfl
        rwa [hdeg] at this
      · have hlen : (p ++ (e, x.2 + y.2) :: s).length < n := by rw [← hl]; simp
        have hdeg : VOA.DeligneAudit.SectorGraded.wordDeg (p ++ (e, x.2 + y.2) :: s) =
            VOA.DeligneAudit.SectorGraded.wordDeg (p ++ x :: y :: s) := by
          simp only [VOA.DeligneAudit.SectorGraded.wordDeg, List.map_append, List.sum_append,
            List.map_cons, List.sum_cons]; omega
        have := ihn _ hlen _ rfl
        rw [hdeg] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨l', h1, h2, h3, rfl⟩
        exact ⟨l', h1, by omega, h3, rfl⟩

/-! ## Reduction to lowering words -/

section Lowering

variable (low : σ → Prop) [DecidablePred low]

/-- Non-lowering words act on a "highest-weight" generator by a scalar, and by zero in positive
degree. -/
theorem wordOp_nonlow (ρ : CurrentModule f V) {w : V}
    (hw : ∀ a r, ¬ low a → ρ.op a r w ∈ K ∙ w ∧ (1 ≤ r → ρ.op a r w = 0)) :
    ∀ (h : List (σ × ℕ)), (∀ x ∈ h, ¬ low x.1) →
      wordOp ρ h w ∈ K ∙ w ∧ (1 ≤ VOA.DeligneAudit.SectorGraded.wordDeg h → wordOp ρ h w = 0)
  | [], _ => ⟨Submodule.mem_span_singleton_self w, fun h => by simp [VOA.DeligneAudit.SectorGraded.wordDeg] at h⟩
  | (x :: h), hh => by
      obtain ⟨h1, h2⟩ := wordOp_nonlow ρ hw h fun y hy => hh y (List.mem_cons_of_mem _ hy)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
      have hx := hw x.1 x.2 (hh x (List.mem_cons_self))
      change ρ.op x.1 x.2 (wordOp ρ h w) ∈ K ∙ w ∧ (1 ≤ VOA.DeligneAudit.SectorGraded.wordDeg (x :: h) →
        ρ.op x.1 x.2 (wordOp ρ h w) = 0)
      rw [← hc, map_smul]
      refine ⟨Submodule.smul_mem _ _ hx.1, fun hd => ?_⟩
      simp only [VOA.DeligneAudit.SectorGraded.wordDeg, List.map_cons, List.sum_cons] at hd
      by_cases hr : 1 ≤ x.2
      · rw [hx.2 hr, smul_zero]
      · have hdh : 1 ≤ VOA.DeligneAudit.SectorGraded.wordDeg h := by
          simp only [VOA.DeligneAudit.SectorGraded.wordDeg]; omega
        rw [← map_smul, hc, h2 hdh, map_zero]

/-- A sorted word splits into a lowering prefix and a non-lowering suffix. -/
theorem sorted_split (hkey : ∀ x y : σ × ℕ, ¬ low x.1 → low y.1 → key y < key x) :
    ∀ (l : List (σ × ℕ)), l.IsChain (fun a c => key a ≤ key c) →
      ∃ lo hi, l = lo ++ hi ∧ lo.IsChain (fun a c => key a ≤ key c) ∧ (∀ x ∈ lo, low x.1) ∧
        (∀ x ∈ hi, ¬ low x.1)
  | [], _ => ⟨[], [], rfl, List.IsChain.nil, by simp, by simp⟩
  | (a :: l), hc => by
      have hpw := (List.isChain_iff_pairwise.mp hc)
      by_cases ha : low a.1
      · obtain ⟨lo, hi, hl, hlo, hlo', hhi⟩ := sorted_split hkey l hc.tail
        refine ⟨a :: lo, hi, by rw [hl]; rfl, ?_, ?_, hhi⟩
        · rw [List.isChain_iff_pairwise] at hlo ⊢
          refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hlo⟩
          rw [hl] at hpw
          exact List.rel_of_pairwise_cons hpw (List.mem_append_left _ hy)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ha
          · exact hlo' x hx'
      · refine ⟨[], a :: l, rfl, List.IsChain.nil, by simp, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha
        · intro hlx
          have h1 := List.rel_of_pairwise_cons hpw hx'
          exact absurd h1 (not_le.mpr (hkey a x ha hlx))

/-- **PBW reduction to sorted lowering words.** -/
theorem cycDeg_le_sortedLow (ρ : CurrentModule f V) {w : V}
    (hkey : ∀ x y : σ × ℕ, ¬ low x.1 → low y.1 → key y < key x)
    (hw : ∀ a r, ¬ low a → ρ.op a r w ∈ K ∙ w ∧ (1 ≤ r → ρ.op a r w = 0)) (b : ℕ) :
    cycDeg ρ w b ≤ Submodule.span K {u | ∃ l : List (σ × ℕ), l.IsChain (fun a c => key a ≤ key c) ∧
      (∀ x ∈ l, low x.1) ∧ VOA.DeligneAudit.SectorGraded.wordDeg l = b ∧ u = wordOp ρ l w} := by
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have h := wordOp_mem_sorted key ρ w l.length l rfl
  rw [hl] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨l', hs, -, hd, rfl⟩
  obtain ⟨lo, hi, rfl, hlo, hlo', hhi⟩ := sorted_split key low hkey l' hs
  obtain ⟨h1, h2⟩ := wordOp_nonlow low ρ hw hi hhi
  rw [wordOp_append]
  by_cases hdeg : 1 ≤ VOA.DeligneAudit.SectorGraded.wordDeg hi
  · rw [h2 hdeg, wordOp_zero]; exact Submodule.zero_mem _
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    rw [← hc, wordOp_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨lo, hlo, hlo', ?_, rfl⟩)
    rw [wordDeg_append] at hd
    omega

end Lowering

/-! ## `sl₃`: fusion modules are spanned by sorted lowering words of letter degree `< m` -/

open VOA.AffineSl3

/-- The lowering generators `f₁, f₂, f₁₂` (indices `3, 4, 5`). -/
def lowSl3 (a : Fin 8) : Prop := 3 ≤ a.val ∧ a.val < 6

instance : DecidablePred lowSl3 := fun a => by unfold lowSl3; infer_instance

/-- The PBW key: lowering letters first, then by index and degree. -/
def keySl3 (x : Fin 8 × ℕ) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (if lowSl3 x.1 then 0 else 1, toLex (x.1.val, x.2))

theorem keySl3_low (x y : Fin 8 × ℕ) (hx : ¬ lowSl3 x.1) (hy : lowSl3 y.1) :
    keySl3 y < keySl3 x := by
  simp only [keySl3, if_pos hy, if_neg hx]
  exact Prod.Lex.lt_iff.mpr (Or.inl Nat.zero_lt_one)

/-- **F2 for `sl₃`**: the degree-`b` piece of a fusion module is spanned by sorted words in the
lowering letters `f_α ⊗ t^r`, `r < m`. -/
theorem cycDeg_le_sortedLowSl3 {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : CurrentModule (bracketTable) V} {w : V} {m : ℕ} (hm : 1 ≤ m) (hW : LocalWeylRel ρ w m)
    (b : ℕ) :
    cycDeg ρ w b ≤ Submodule.span ℂ {u | ∃ l : List (Fin 8 × ℕ),
      l.IsChain (fun a c => keySl3 a ≤ keySl3 c) ∧ (∀ x ∈ l, lowSl3 x.1 ∧ x.2 < m) ∧
      VOA.DeligneAudit.SectorGraded.wordDeg l = b ∧ u = wordOp ρ l w} := by
  have hw : ∀ (a : Fin 8) r, ¬ lowSl3 a → ρ.op a r w ∈ ℂ ∙ w ∧ (1 ≤ r → ρ.op a r w = 0) := by
    intro a r ha
    unfold lowSl3 at ha
    by_cases h3 : a.val < 3
    · rw [hW.raising a h3 r]; exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · have h6 : 6 ≤ a.val := by omega
      refine ⟨?_, fun hr => hW.cartan_pos a h6 r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [hW.cartan_zero a h6]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [hW.cartan_pos a h6 r hr]; exact Submodule.zero_mem _
  refine (cycDeg_le_sortedLow keySl3 lowSl3 ρ keySl3_low hw b).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, hs, hlow, hd, rfl⟩
  by_cases hall : ∀ x ∈ l, x.2 < m
  · exact Submodule.subset_span ⟨l, hs, fun x hx => ⟨hlow x hx, hall x hx⟩, hd, rfl⟩
  · push_neg at hall
    rw [wordOp_eq_zero_of_mem ρ (truncIdeal m) (ideal_kills_w hm hW) l hall]
    exact Submodule.zero_mem _

end

end VOA.DeligneAudit.SectorWeyl

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorWeyl.wordOp_mem_sorted
#print axioms VOA.DeligneAudit.SectorWeyl.cycDeg_le_sortedLow
#print axioms VOA.DeligneAudit.SectorWeyl.cycDeg_le_sortedLowSl3
end AxiomAudit
