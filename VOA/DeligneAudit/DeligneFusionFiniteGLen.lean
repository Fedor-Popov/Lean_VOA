/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionFiniteGNil

/-!
# The finiteness clause for a Deligne sector

the `sl₃` argument (`DeligneFusionFinite`) made type-generic. The *low* letters are those that
are neither raising nor Cartan (`LowG S c`). Given the table facts `FiniteTableG S`

* `wt_ne`: low letters have nonzero weight (so they are `ad`-nilpotent of order `adK S`), and
* `nil`: in every module with `LocalWeylRelG S ρ w m`, each low letter at grade 0 is nilpotent
  on `w` (per type from a certificate, `known_of_certValid`),

every non-vanishing sorted low word of `t`-degree `b` has bounded length (`length_le_of_neG`), so

`cycDeg_finiteDimensionalG : FiniteTableG S → LocalWeylRelG S ρ w m →
FiniteDimensional ℂ (cycDeg ρ w b)`.
-/

namespace VOA.DeligneAudit.FiniteG

open Finset VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector

noncomputable section

open scoped Classical

local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg

variable (S : DeligneSectorData)

/-- The low letters: neither raising nor Cartan. -/
def LowG (c : Fin S.n) : Prop := ¬ (S.raising c ∨ S.cartan c ∨ S.cartanN c)

/-- **Table facts for the finiteness clause.** -/
structure FiniteTableG : Prop where
  wt_ne : ∀ c, LowG S c → S.wt c ≠ 0
  nil : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    LocalWeylRelG S ρ w m → ∀ c, LowG S c → Known ρ w c

/-- Low letters first; among them grade-0 letters first; then by index and grade. -/
def keyG (x : Fin S.n × ℕ) : ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex (if LowG S x.1 then 0 else 1, toLex (if x.2 = 0 then 0 else 1, toLex (x.1.val, x.2)))

variable {S}

theorem keyG_low (x y : Fin S.n × ℕ) (hx : ¬ LowG S x.1) (hy : LowG S y.1) : keyG S y < keyG S x := by
  simp only [keyG, if_pos hy, if_neg hx]
  exact Prod.Lex.lt_iff.mpr (Or.inl Nat.zero_lt_one)

theorem keyG_inj {x y : Fin S.n × ℕ} (h : keyG S x = keyG S y) : x = y := by
  simp only [keyG, toLex_inj, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.2.2.1) h.2.2.2

theorem keyG_zero_lt {x y : Fin S.n × ℕ} (hx : LowG S x.1) (hy : LowG S y.1) (hx0 : x.2 = 0)
    (hy0 : y.2 ≠ 0) : keyG S x < keyG S y := by
  simp only [keyG, if_pos hx, if_pos hy, if_pos hx0, if_neg hy0]
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, Prod.Lex.lt_iff.mpr (Or.inl Nat.zero_lt_one)⟩)

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule S.f V}

theorem cycDeg_le_sortedG {w : V} {m : ℕ} (hW : LocalWeylRelG S ρ w m) (b : ℕ) :
    cycDeg ρ w b ≤ Submodule.span ℂ {u | ∃ l : List (Fin S.n × ℕ),
      l.IsChain (fun a c => keyG S a ≤ keyG S c) ∧ (∀ x ∈ l, LowG S x.1) ∧ deg l = b ∧
        u = wordOp ρ l w} := by
  have hw : ∀ (a : Fin S.n) r, ¬ LowG S a → ρ.op a r w ∈ ℂ ∙ w ∧ (1 ≤ r → ρ.op a r w = 0) := by
    intro a r ha
    unfold LowG at ha
    rw [not_not] at ha
    rcases ha with h | h | h
    · rw [hW.raising a h r]; exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · refine ⟨?_, fun hr => hW.cartan_pos a h r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [hW.cartan_zero a h]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [hW.cartan_pos a h r hr]; exact Submodule.zero_mem _
    · refine ⟨?_, fun hr => hW.cartanN_pos a h r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [hW.cartanN_zero a h]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [hW.cartanN_pos a h r hr]; exact Submodule.zero_mem _
  exact cycDeg_le_sortedLow (keyG S) (LowG S) ρ keyG_low hw b

/-- Number of grade-0 letter types occurring. -/
def tcountG (l : List (Fin S.n × ℕ)) : ℕ := (Finset.univ.filter fun c : Fin S.n => (c, 0) ∈ l).card

theorem tcountG_le (l : List (Fin S.n × ℕ)) : tcountG l ≤ S.n := by
  unfold tcountG
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The length bound. -/
def GrG (K N0 d : ℕ) : ℕ → ℕ
  | 0 => d
  | t + 1 => (K + 1) * GrG K N0 d t + N0

theorem GrG_mono (K N0 d : ℕ) {s t : ℕ} (h : s ≤ t) : GrG K N0 d s ≤ GrG K N0 d t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by simp only [GrG]; nlinarith)

theorem len_le_degG : ∀ l : List (Fin S.n × ℕ), (∀ y ∈ l, y.2 ≠ 0) → l.length ≤ deg l
  | [] => fun _ => le_rfl
  | (x :: l) => fun h => by
      have := len_le_degG l fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx := h x List.mem_cons_self
      simp only [List.length_cons, VOA.DeligneAudit.SectorGraded.wordDeg, List.map_cons,
        List.sum_cons] at this ⊢
      omega

theorem deg_consG (x : Fin S.n × ℕ) (l : List (Fin S.n × ℕ)) : deg (x :: l) = x.2 + deg l := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

theorem deg_appendG (l l' : List (Fin S.n × ℕ)) : deg (l ++ l') = deg l + deg l' := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

theorem deg_replicate_zeroG (r : ℕ) (c : Fin S.n) : deg (List.replicate r (c, 0)) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [List.replicate_succ, deg_consG, ih]

/-- **Length bound for non-vanishing sorted low words.** -/
theorem length_le_of_neG {w : V} {N0 : ℕ} (hwt : ∀ c, LowG S c → S.wt c ≠ 0)
    (hN : ∀ c, LowG S c → (ρ.op c 0 ^ N0) w = 0) :
    ∀ n (l : List (Fin S.n × ℕ)), l.length = n → l.Pairwise (fun a c => keyG S a ≤ keyG S c) →
      (∀ x ∈ l, LowG S x.1) → wordOp ρ l w ≠ 0 →
        l.length ≤ GrG (adK S) N0 (deg l) (tcountG l) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hs hlow hne
  match l, hs, hlow, hne with
  | [], _, _, _ => exact Nat.zero_le _
  | (x :: rest), hs, hlow, hne =>
    by_cases hx0 : x.2 = 0
    · set p : Fin S.n × ℕ → Bool := fun y => decide (y = x) with hp
      set T := List.takeWhile p (x :: rest) with hT
      set D := List.dropWhile p (x :: rest) with hD
      have hTD : T ++ D = x :: rest := List.takeWhile_append_dropWhile
      have hTrep : T = List.replicate T.length x :=
        List.eq_replicate_iff.mpr ⟨rfl, fun y hy => by
          have := List.all_eq_true.mp (List.all_takeWhile (p := p) (l := x :: rest)) y hy
          simpa [hp] using this⟩
      have hTlen : 1 ≤ T.length := by
        rw [hT, List.takeWhile_cons_of_pos (by simp [hp])]; simp
      have hpw : (T ++ D).Pairwise (fun a c => keyG S a ≤ keyG S c) := hTD ▸ hs
      rw [List.pairwise_append] at hpw
      have hxT : x ∈ T := by
        rw [hTrep]; exact List.mem_replicate.mpr ⟨by omega, rfl⟩
      have hxD : x ∉ D := by
        intro hxD
        cases hDc : D with
        | nil => rw [hDc] at hxD; simp at hxD
        | cons y D' =>
          have hy : p y = false := by
            have := List.head_dropWhile_not p (l := x :: rest) (by rw [← hD, hDc]; simp)
            simpa [← hD, hDc] using this
          have hyx : y ≠ x := by simpa [hp] using hy
          rw [hDc] at hxD
          rcases List.mem_cons.mp hxD with h | h
          · exact hyx h.symm
          · have h1 := hpw.2.2 x hxT y (by rw [hDc]; exact List.mem_cons_self)
            have h2 := (List.pairwise_cons.mp (hDc ▸ hpw.2.1)).1 x h
            exact hyx (keyG_inj (le_antisymm h2 h1))
      have hDsub : ∀ z ∈ D, z ∈ x :: rest := fun z hz => hTD ▸ List.mem_append_right T hz
      have hlen : (x :: rest).length = T.length + D.length := by rw [← hTD, List.length_append]
      have hword : wordOp ρ (x :: rest) w = (ρ.op x.1 0 ^ T.length) (wordOp ρ D w) := by
        have hx : x = (x.1, 0) := Prod.ext rfl hx0
        rw [← hTD, wordOp_append]
        conv_lhs => rw [hTrep, hx]
        exact (pow_eq_wordOp ρ x.1 _ T.length).symm
      have hxl : LowG S x.1 := hlow x List.mem_cons_self
      have hDne : wordOp ρ D w ≠ 0 := by
        intro h0; apply hne; rw [hword, h0, map_zero]
      have hr : T.length < N0 + adK S * D.length := by
        by_contra hcon
        exact hne (hword ▸ pow_kill_mono _ (pow_kill_word ρ x.1 (hwt x.1 hxl) (hN x.1 hxl) D)
          (by omega))
      have hIH := ih D.length (by omega) D rfl hpw.2.1 (fun z hz => hlow z (hDsub z hz)) hDne
      have hdeg : deg D = deg (x :: rest) := by
        rw [← hTD, deg_appendG, hTrep, show x = (x.1, 0) from Prod.ext rfl hx0, deg_replicate_zeroG,
          zero_add]
      have ht : tcountG D + 1 ≤ tcountG (x :: rest) := by
        unfold tcountG
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset (fun c hc' => ?_) |>.mpr ⟨x.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢; exact hDsub _ hc'
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show (x.1, 0) = x from Prod.ext rfl hx0.symm]; exact List.mem_cons_self
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show (x.1, 0) = x from Prod.ext rfl hx0.symm]; exact hxD
      rw [hdeg] at hIH
      have hmono := GrG_mono (adK S) N0 (deg (x :: rest)) ht
      simp only [GrG] at hmono
      nlinarith
    · have hpos : ∀ y ∈ x :: rest, y.2 ≠ 0 := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx0
        · intro hy0
          have h1 := (List.pairwise_cons.mp hs).1 y hy
          exact absurd h1 (not_le.mpr (keyG_zero_lt (hlow y (List.mem_cons_of_mem _ hy))
            (hlow x List.mem_cons_self) hy0 hx0))
      exact (len_le_degG _ hpos).trans (GrG_mono _ _ _ (Nat.zero_le _))

theorem le_deg_of_memG : ∀ {l : List (Fin S.n × ℕ)} {x : Fin S.n × ℕ}, x ∈ l → x.2 ≤ deg l
  | [], _, h => absurd h List.not_mem_nil
  | (y :: l), x, h => by
      rw [deg_consG]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := le_deg_of_memG h; omega

theorem finite_bounded_listsG (L b : ℕ) :
    {l : List (Fin S.n × ℕ) | l.length ≤ L ∧ ∀ x ∈ l, x.2 ≤ b}.Finite := by
  haveI : Finite {x : Fin S.n × ℕ // x.2 ≤ b} :=
    Finite.of_injective (fun x => (x.1.1, (⟨x.1.2, by have := x.2; omega⟩ : Fin (b + 1))))
      (fun x y h => by
        simp only [Prod.mk.injEq, Fin.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.1 h.2))
  refine ((List.finite_length_le {x : Fin S.n × ℕ // x.2 ≤ b} L).image
    (List.map Subtype.val)).subset ?_
  rintro l ⟨hl, hb⟩
  refine ⟨l.pmap Subtype.mk hb, by simpa using hl, ?_⟩
  simp [List.map_pmap]

/-- **The finiteness clause**, type-generic. -/
theorem cycDeg_finiteDimensionalG (T : FiniteTableG S) {w : V} {m : ℕ}
    (hW : LocalWeylRelG S ρ w m) (b : ℕ) : FiniteDimensional ℂ (cycDeg ρ w b) := by
  have hex : ∀ c, ∃ N, LowG S c → (ρ.op c 0 ^ N) w = 0 := by
    intro c
    by_cases hc : LowG S c
    · obtain ⟨N, hN⟩ := T.nil m V ρ w hW c hc
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose Nf hNf using hex
  set N0 := ∑ c, Nf c
  have hN : ∀ c, LowG S c → (ρ.op c 0 ^ N0) w = 0 := fun c hc =>
    pow_kill_mono _ (hNf c hc) (Finset.single_le_sum (fun c _ => Nat.zero_le (Nf c))
      (Finset.mem_univ c))
  haveI : Trans (fun a c : Fin S.n × ℕ => keyG S a ≤ keyG S c)
      (fun a c : Fin S.n × ℕ => keyG S a ≤ keyG S c) (fun a c : Fin S.n × ℕ => keyG S a ≤ keyG S c) :=
    ⟨fun h1 h2 => le_trans h1 h2⟩
  set L := GrG (adK S) N0 b S.n
  have hle : cycDeg ρ w b ≤ Submodule.span ℂ ((fun l => wordOp ρ l w) ''
      {l : List (Fin S.n × ℕ) | l.length ≤ L ∧ ∀ x ∈ l, x.2 ≤ b}) := by
    refine (cycDeg_le_sortedG hW b).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hs, hlow, hd, rfl⟩
    by_cases h0 : wordOp ρ l w = 0
    · rw [h0]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨l, ⟨?_, fun x hx => hd ▸ le_deg_of_memG hx⟩, rfl⟩
      have := length_le_of_neG T.wt_ne hN l.length l rfl hs.pairwise hlow h0
      rw [hd] at this
      exact this.trans (GrG_mono _ _ b (tcountG_le l))
  haveI := FiniteDimensional.span_of_finite ℂ ((finite_bounded_listsG L b).image
    (fun l => wordOp ρ l w))
  exact Submodule.finiteDimensional_of_le hle

end

end VOA.DeligneAudit.FiniteG

section AxiomAudit
#print axioms VOA.DeligneAudit.FiniteG.length_le_of_neG
#print axioms VOA.DeligneAudit.FiniteG.cycDeg_finiteDimensionalG
end AxiomAudit
