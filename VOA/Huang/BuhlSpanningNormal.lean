/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BuhlSpanningIterate

/-!
# Buhl's spanning theorem for modules, layer 3: the normal form

Let `N` be an admissible (`ℕ`-gradable) module, `B₀ = N(0)` its bottom level, `D` generator data
of a `C₂`-cofinite `𝒱`, `N₀` with `𝒱_p ⊆ C₂(𝒱)` for `p ≥ N₀`, `Q = N₀ + 1`, and `Bm ≥ wt i` for
all generators.  A generator word is **normal** if its modes are weakly increasing from the outside
in (`modeLE`) and no letter occurs `Q` or more times.

* `wordL_eq_zero_of_big` — a sorted word with some mode `≥ Bm` kills `N(0)` (its innermost letter
  lowers below level `0`);
* `block_mem` — the `C₂` relation: `gen_{i,(n)}^Q w ∈ E(G−1) + span{unbalanced words}`,
  from `vPow_mode_sub_mem_Sp` and `O₂_act_mem_E` (`x^{(Q−1)} ∈ 𝒱_{Q wt x} ⊆ C₂(𝒱)`);
* `E_le_NS` — every `E G` lies in the span of the normal words on `N(0)`: induction on the
  grade `G`, and inside it on the potential `K − Σ modes²`, which the unbalancing strictly lowers
  while staying bounded on non-vanishing sorted words.

No `sorry`, no axioms beyond Lean's three.
-/

namespace VOA.Huang.BuhlSpanning

open VOA VOA.Huang.FusionC2 VOA.Huang.ModuleC2
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

section Combinatorics

variable (D : GenData W)

/-- Letters are compared by their mode only. -/
def modeLE (a b : Ltr D) : Prop := a.2 ≤ b.2

instance : DecidableRel (modeLE D) := fun a b => inferInstanceAs (Decidable (a.2 ≤ b.2))

instance : Std.Total (modeLE D) := ⟨fun a b => le_total a.2 b.2⟩

instance : IsTrans (Ltr D) (modeLE D) := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩

/-- The sum of the modes of a word. -/
def modeSum (l : List (Ltr D)) : ℤ := (l.map (fun a => a.2)).sum

/-- The potential `Σ modes²`. -/
def phi (l : List (Ltr D)) : ℤ := (l.map (fun a => a.2 ^ 2)).sum

variable {D}

theorem modeSum_perm {l₁ l₂ : List (Ltr D)} (h : l₁.Perm l₂) : modeSum D l₁ = modeSum D l₂ :=
  (h.map _).sum_eq

theorem phi_perm {l₁ l₂ : List (Ltr D)} (h : l₁.Perm l₂) : phi D l₁ = phi D l₂ :=
  (h.map _).sum_eq

theorem modeSum_append (l₁ l₂ : List (Ltr D)) :
    modeSum D (l₁ ++ l₂) = modeSum D l₁ + modeSum D l₂ := by simp [modeSum]

theorem phi_append (l₁ l₂ : List (Ltr D)) : phi D (l₁ ++ l₂) = phi D l₁ + phi D l₂ := by
  simp [phi]

theorem modeSum_map (i : Fin D.g) (c : List ℤ) :
    modeSum D (c.map (fun k => (i, k))) = c.sum := by
  simp [modeSum, List.map_map, Function.comp_def]

theorem phi_map (i : Fin D.g) (c : List ℤ) :
    phi D (c.map (fun k => (i, k))) = (c.map (fun k => k ^ 2)).sum := by
  simp [phi, List.map_map, Function.comp_def]

theorem grade_map (i : Fin D.g) (c : List ℤ) :
    grade D (c.map (fun k => (i, k))) = c.length * D.wt i := by
  simp [grade, List.map_map, Function.comp_def, List.sum_replicate]

theorem grade_replicate (Q : ℕ) (a : Ltr D) :
    grade D (List.replicate Q a) = Q * D.wt a.1 := by
  simp [grade, List.map_replicate, List.sum_replicate]

/-- `Σ (cₖ − n)² = Σ cₖ² − 2n Σ cₖ + |c| n²`. -/
theorem sum_sq_sub (n : ℤ) : ∀ c : List ℤ,
    (c.map (fun k => (k - n) ^ 2)).sum
      = (c.map (fun k => k ^ 2)).sum - 2 * n * c.sum + c.length * n ^ 2
  | [] => by simp
  | a :: c => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, sum_sq_sub n c]
      push_cast; ring

/-- An unbalanced composition has a strictly larger sum of squares. -/
theorem sum_sq_gt {Q : ℕ} {n : ℤ} {c : List ℤ} (hlen : c.length = Q) (hsum : c.sum = Q * n)
    (hne : c ≠ List.replicate Q n) : (Q : ℤ) * n ^ 2 < (c.map (fun k => k ^ 2)).sum := by
  have hex : ∃ a ∈ c, a ≠ n := by
    by_contra h
    push Not at h
    exact hne (List.eq_replicate_iff.mpr ⟨hlen, h⟩)
  obtain ⟨a, ha, han⟩ := hex
  have hpos : 0 < (c.map (fun k => (k - n) ^ 2)).sum := by
    have h1 : (a - n) ^ 2 ≤ (c.map (fun k => (k - n) ^ 2)).sum :=
      List.single_le_sum (fun x hx => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; positivity) _ (List.mem_map_of_mem ha)
    have h2 : 0 < (a - n) ^ 2 := by
      have : a - n ≠ 0 := sub_ne_zero.mpr han
      positivity
    linarith
  rw [sum_sq_sub n c, hsum, hlen] at hpos
  nlinarith

/-- In a word with all modes `< Bm`, every mode is `≥ modeSum − (length − 1)·Bm`. -/
theorem mode_ge_of_lt {Bm : ℤ} : ∀ (l : List (Ltr D)), (∀ e ∈ l, e.2 < Bm) →
    ∀ e ∈ l, modeSum D l - ((l.length : ℤ) - 1) * Bm ≤ e.2 := by
  intro l
  induction l with
  | nil => intro _ e he; simp at he
  | cons a l ih =>
      intro hlt e he
      have hsl : modeSum D l ≤ (l.length : ℤ) * Bm := by
        have := List.sum_le_card_nsmul (l.map (fun a => a.2)) Bm (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact le_of_lt (hlt y (List.mem_cons_of_mem _ hy)))
        simpa [modeSum] using this
      have ha := hlt a (List.mem_cons_self ..)
      have hcons : modeSum D (a :: l) = a.2 + modeSum D l := by simp [modeSum]
      rw [hcons, List.length_cons]
      push_cast
      rcases List.mem_cons.mp he with rfl | he'
      · nlinarith
      · have := ih (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) e he'
        nlinarith

/-- The potential is bounded on words with all modes `< Bm`, by a quantity depending only on the
length and the mode sum. -/
noncomputable def Kbd (Bm : ℤ) (r : ℕ) (S : ℤ) : ℤ :=
  (r : ℤ) * (Bm ^ 2 + (S - ((r : ℤ) - 1) * Bm) ^ 2)

theorem phi_le_Kbd {Bm : ℤ} (hBm : 0 ≤ Bm) (l : List (Ltr D)) (hlt : ∀ e ∈ l, e.2 < Bm) :
    phi D l ≤ Kbd Bm l.length (modeSum D l) := by
  have hge := mode_ge_of_lt l hlt
  set lo := modeSum D l - ((l.length : ℤ) - 1) * Bm
  have hb : ∀ e ∈ l, e.2 ^ 2 ≤ Bm ^ 2 + lo ^ 2 := by
    intro e he
    have h1 := hlt e he
    have h2 := hge e he
    rcases le_or_gt 0 e.2 with h | h
    · nlinarith
    · nlinarith
  have := List.sum_le_card_nsmul (l.map (fun a => a.2 ^ 2)) (Bm ^ 2 + lo ^ 2) (fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hb y hy)
  simpa [phi, Kbd] using this

end Combinatorics

section Module

variable (D : GenData W) (N : AdmissibleModule W M)

/-- A sorted word with a mode `≥ Bm` annihilates the bottom level. -/
theorem wordL_eq_zero_of_big {Bm : ℕ} (hBm : ∀ i, D.wt i ≤ Bm) :
    ∀ (l : List (Ltr D)), l.Pairwise (modeLE D) → (∃ e ∈ l, (Bm : ℤ) ≤ e.2) →
      ∀ b ∈ N.lev 0, wordL D N.toWeakModule l b = 0 := by
  intro l
  induction l with
  | nil => rintro _ ⟨e, he, _⟩; simp at he
  | cons a l ih =>
      intro hp ⟨e, he, hbig⟩ b hb
      rw [wordL_cons]
      by_cases h' : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
      · rw [ih hp.of_cons h' b hb, map_zero]
      · push Not at h'
        have hea : e = a := by
          rcases List.mem_cons.mp he with h | h
          · exact h
          · exact absurd hbig (not_le.mpr (h' e h))
        subst hea
        have hl : l = [] := by
          rcases l with _ | ⟨e', l'⟩
          · rfl
          · exfalso
            have := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
            have := h' e' (List.mem_cons_self ..)
            simp only [modeLE] at *
            omega
        subst hl
        have hmem := N.act_lev (D.gen_mem e.1) hb (p := e.2)
        have hneg : (0 : ℤ) + ((D.wt e.1 : ℤ) - e.2 - 1) < 0 := by
          have := hBm e.1; omega
        rw [N.lev_eq_bot_of_neg _ hneg, Submodule.mem_bot] at hmem
        exact hmem

/-- Products of modes of one generator, read as a generator word. -/
theorem wordX_eq_wordL (i₀ : Fin D.g) (l' : List (Ltr D)) (b : M) :
    ∀ c : List ℤ, wordX N.toWeakModule (D.gen i₀) c (wordL D N.toWeakModule l' b)
      = wordL D N.toWeakModule (c.map (fun k => (i₀, k)) ++ l') b
  | [] => rfl
  | a :: c => by
      rw [wordX_cons, wordX_eq_wordL i₀ l' b c]
      rfl

variable {D N}

/-- **The `C₂` relation on a repeated block**: `gen_{i₀,(n)}^{N₀+1} z` lies in the previous
grade plus the span of unbalanced products. -/
theorem block_mem {N₀ : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W) (i₀ : Fin D.g)
    (n : ℤ) (l' : List (Ltr D)) {b : M} (hb : b ∈ N.lev 0) :
    wordL D N.toWeakModule (List.replicate (N₀ + 1) (i₀, n) ++ l') b ∈
      E D N.toWeakModule (N.lev 0) (grade D (List.replicate (N₀ + 1) (i₀, n) ++ l') - 1) ⊔
        Submodule.span ℂ {y | ∃ c : List ℤ, c.length = N₀ + 1 ∧ c.sum = ((N₀ : ℤ) + 1) * n ∧
          c ≠ List.replicate (N₀ + 1) n ∧
          y = wordL D N.toWeakModule (c.map (fun k => (i₀, k)) ++ l') b} := by
  set A := N.toWeakModule
  set x := D.gen i₀
  set z := wordL D A l' b with hzdef
  set t : ℤ := ((N₀ : ℤ) + 1) * n + N₀ with ht
  have hz : z ∈ E D A (N.lev 0) (grade D l') := wordL_mem_E hb le_rfl
  set p : ℕ := (N₀ + 1) * D.wt i₀ with hp
  have hwt := D.wt_pos i₀
  have hp1 : N₀ + 1 ≤ p := by rw [hp]; nlinarith
  have hvg : vPow W x N₀ ∈ W.grading (p : ℤ) := by
    have := vPow_mem_grading (D.gen_mem i₀) N₀
    rw [hp]; push_cast; exact this
  have hO : vPow W x N₀ ∈ O₂ W ⊓ W.grading (p : ℤ) :=
    ⟨hN₀ (p : ℤ) (by exact_mod_cast (show N₀ ≤ p by omega)) hvg, hvg⟩
  have h1 := O₂_act_mem_E (A := A) (D := D) (B₀ := N.lev 0) p hO t hz
  have h2 := vPow_mode_sub_mem_Sp (A := A) (x := x) n N₀ t z
  rw [if_pos (by rw [ht])] at h2
  have hgr : grade D (List.replicate (N₀ + 1) (i₀, n) ++ l') - 1 = grade D l' + (p - 1) := by
    rw [grade_append, grade_replicate]; dsimp only; rw [← hp]; omega
  have hrep : wordL D A (List.replicate (N₀ + 1) (i₀, n) ++ l') b
      = wordX A x (List.replicate (N₀ + 1) n) z := by
    rw [hzdef, wordX_eq_wordL D N i₀ l' b, List.map_replicate]
  rw [hrep, hgr]
  have heq : wordX A x (List.replicate (N₀ + 1) n) z
      = mode (A.YM (vPow W x N₀)) t z
        - (mode (A.YM (vPow W x N₀)) t z - wordX A x (List.replicate (N₀ + 1) n) z) := by abel
  rw [heq]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right ?_)
  refine (Submodule.span_le.mpr ?_) h2
  rintro _ ⟨c, hlen, hsum, hne, rfl⟩
  refine Submodule.subset_span ⟨c, hlen, ?_, hne, ?_⟩
  · rw [hsum, ht]; ring
  · exact wordX_eq_wordL D N i₀ l' b c

/-- A word is **normal**: sorted by mode, no letter repeated `Q` or more times. -/
def Normal (D : GenData W) (Q : ℕ) (l : List (Ltr D)) : Prop :=
  l.Pairwise (modeLE D) ∧ ∀ a, l.count a < Q

/-- The span of the normal words on the bottom level. -/
noncomputable def NS (D : GenData W) (N : AdmissibleModule W M) (Q : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List (Ltr D)) (b : M), Normal D Q l ∧ b ∈ N.lev 0 ∧
    y = wordL D N.toWeakModule l b}

/-- **The normal-form theorem**: every `E G` lies in the span of the normal words. -/
theorem E_le_NS {N₀ : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W) {Bm : ℕ}
    (hBm : ∀ i, D.wt i ≤ Bm) :
    ∀ G : ℕ, E D N.toWeakModule (N.lev 0) G ≤ NS D N (N₀ + 1) := by
  set A := N.toWeakModule
  set Q := N₀ + 1 with hQ
  intro G
  induction G using Nat.strong_induction_on with
  | _ G IH =>
  have hlow : 1 ≤ G → E D A (N.lev 0) (G - 1) ≤ NS D N Q := fun h => IH (G - 1) (by omega)
  -- the sorted words of grade `G`
  have hsorted : ∀ (d : ℕ) (l : List (Ltr D)), l.Pairwise (modeLE D) → grade D l = G →
      ∀ b ∈ N.lev 0,
        (Kbd (Bm : ℤ) l.length (modeSum D l) - phi D l).toNat ≤ d → wordL D A l b ∈ NS D N Q := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IHd =>
    intro l hp hg b hb hd
    by_cases hbig : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
    · rw [wordL_eq_zero_of_big D N hBm l hp hbig b hb]; exact Submodule.zero_mem _
    push Not at hbig
    by_cases hnorm : ∀ a, l.count a < Q
    · exact Submodule.subset_span ⟨l, b, ⟨hp, hnorm⟩, hb, rfl⟩
    push Not at hnorm
    obtain ⟨a, ha⟩ := hnorm
    have hsub : List.Sublist (List.replicate Q a) l := List.replicate_sublist_iff.mpr ha
    obtain ⟨l', hperm⟩ := hsub.exists_perm_append
    have hgG : grade D (List.replicate Q a ++ l') = G := by rw [← grade_perm D hperm, hg]
    have hG1 : 1 ≤ G := by
      rw [← hgG, grade_append, grade_replicate]
      have := D.wt_pos a.1
      nlinarith
    have hdiff := perm_sub_mem_E (A := A) (B₀ := N.lev 0) hperm hb
    rw [hg] at hdiff
    have hblock := block_mem (N := N) hN₀ a.1 a.2 l' hb
    rw [Prod.mk.eta, hgG] at hblock
    have hspan : Submodule.span ℂ {y | ∃ c : List ℤ, c.length = N₀ + 1 ∧
        c.sum = ((N₀ : ℤ) + 1) * a.2 ∧ c ≠ List.replicate (N₀ + 1) a.2 ∧
        y = wordL D A (c.map (fun k => (a.1, k)) ++ l') b} ≤ NS D N Q := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hlen, hsum, hne, rfl⟩
      set l'' := c.map (fun k => (a.1, k)) ++ l' with hl''
      set s'' := List.insertionSort (modeLE D) l'' with hs''
      have hps : s''.Perm l'' := List.perm_insertionSort (modeLE D) l''
      have hgl'' : grade D l'' = G := by
        rw [← hgG, hl'', grade_append, grade_append, grade_map, grade_replicate, hlen]
      have hd2 := perm_sub_mem_E (A := A) (B₀ := N.lev 0) hps.symm hb
      rw [hgl''] at hd2
      have hs_mem : wordL D A s'' b ∈ NS D N Q := by
        have hsp : s''.Pairwise (modeLE D) := List.pairwise_insertionSort (modeLE D) l''
        by_cases hbig' : ∃ e ∈ s'', (Bm : ℤ) ≤ e.2
        · rw [wordL_eq_zero_of_big D N hBm s'' hsp hbig' b hb]; exact Submodule.zero_mem _
        push Not at hbig'
        -- invariants
        have hlen_eq : s''.length = l.length := by
          rw [hps.length_eq, hperm.length_eq, hl'']; simp [hlen, hQ]
        have hsum_eq : modeSum D s'' = modeSum D l := by
          rw [modeSum_perm hps, modeSum_perm hperm, hl'', modeSum_append, modeSum_append,
            modeSum_map, hsum]
          simp [modeSum, List.map_replicate, List.sum_replicate, hQ]
        have hphi_gt : phi D l < phi D s'' := by
          rw [phi_perm hps, phi_perm hperm, hl'', phi_append, phi_append, phi_map]
          have hrep : phi D (List.replicate Q a) = (Q : ℤ) * a.2 ^ 2 := by
            simp [phi, List.map_replicate, List.sum_replicate]
          rw [hrep]
          have := sum_sq_gt (Q := Q) (n := a.2) hlen (by rw [hsum]; push_cast [hQ]; ring) hne
          linarith
        have hbd := phi_le_Kbd (D := D) (by positivity) s'' hbig'
        rw [hlen_eq, hsum_eq] at hbd
        refine IHd _ ?_ s'' hsp (by rw [grade_perm D hps, hgl'']) b hb le_rfl
        rw [hlen_eq, hsum_eq]
        omega
      have := Submodule.add_mem _ hs_mem (hlow hG1 (by simpa using hd2))
      rwa [add_sub_cancel] at this
    have hrest : wordL D A (List.replicate Q a ++ l') b ∈ NS D N Q := by
      have := (sup_le (hlow hG1) hspan) hblock
      exact this
    have := Submodule.add_mem _ (hlow hG1 hdiff) hrest
    rwa [sub_add_cancel] at this
  -- all words of grade `≤ G`
  rw [E, Submodule.span_le]
  rintro _ ⟨l, b, hl, hb, rfl⟩
  rcases lt_or_eq_of_le hl with hlt | heq
  · exact (IH (grade D l) hlt) (wordL_mem_E hb le_rfl)
  · by_cases hl0 : l = []
    · subst hl0
      exact Submodule.subset_span ⟨[], b, ⟨List.Pairwise.nil, fun a => by simp [hQ]⟩, hb, rfl⟩
    have hG1 : 1 ≤ G := by
      rw [← heq]
      rcases l with _ | ⟨e, l⟩
      · exact absurd rfl hl0
      · rw [grade_cons]; have := D.wt_pos e.1; omega
    set s := List.insertionSort (modeLE D) l
    have hps : s.Perm l := List.perm_insertionSort (modeLE D) l
    have hd := perm_sub_mem_E (A := A) (B₀ := N.lev 0) hps.symm hb
    rw [heq] at hd
    have hs := hsorted _ s (List.pairwise_insertionSort (modeLE D) l)
      (by rw [grade_perm D hps, heq]) b hb le_rfl
    have := Submodule.add_mem _ hs (hlow hG1 hd)
    rwa [add_sub_cancel] at this

end Module

end VOA.Huang.BuhlSpanning
