import VOA.DeligneAudit.DeligneFusionCVRectMixedTheta

/-!
# Constructive spanning for two opposite rectangles

The span of lowering zero-mode words on the d-th theta descendant is stable
under lowering zero modes. Commuting a positive lowering current through such
a word keeps its positive mode in the lower-root commutator. Induction gives
the actual degree bridge, and PBW then supplies a finite spanning family.
-/

namespace VOA.DeligneAudit.A2.CVRectMixedSpanning

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CLNormal
open VOA.DeligneAudit.A2.CVRectMixedClassical VOA.DeligneAudit.A2.CVRectMixedTwo
open VOA.DeligneAudit.A2.CVRectMixedTheta VOA.DeligneAudit.A2.CVRectSingle

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V)

def zeroLow (g : List (Fin 8 × ℕ)) : Prop :=
  ∀ x ∈ g, lowSl3 x.1 ∧ x.2 = 0

def zeroLowSpan (v : V) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ g : List (Fin 8 × ℕ), zeroLow g ∧ x = wordOp R g v}

theorem zeroLowSpan_self (v : V) : v ∈ zeroLowSpan R v :=
  Submodule.subset_span ⟨[], by simp [zeroLow], rfl⟩

theorem zeroLowSpan_inv (v : V) (d : Fin 8) (hd : lowSl3 d) :
    zeroLowSpan R v ≤ (zeroLowSpan R v).comap (R.op d 0) := by
  rw [zeroLowSpan, Submodule.span_le]
  rintro _ ⟨g, hg, rfl⟩
  refine Submodule.subset_span ⟨(d, 0) :: g, ?_, rfl⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨hd, rfl⟩
  · exact hg x hx

theorem zeroLow_degree (g : List (Fin 8 × ℕ)) (hg : zeroLow g) :
    SectorGraded.wordDeg g = 0 := by
  induction g with
  | nil => rfl
  | cons x g ih =>
      have hx := (hg x List.mem_cons_self).2
      have hi := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))
      simp only [SectorGraded.wordDeg, List.map_cons, List.sum_cons] at hi ⊢
      rw [hx, hi, zero_add]

theorem zeroLowSpan_le_normal (v : V) : zeroLowSpan R v ≤ zeroNormalSpan R v := by
  rw [zeroLowSpan, Submodule.span_le]
  rintro _ ⟨g, hg, rfl⟩
  have hn := lowword_degree_normal (ρ := R) (w := v) g (fun x hx => (hg x hx).1)
  rw [zeroLow_degree g hg] at hn
  have hnormal : NW R v (fun a b c => a.sum + b.sum + c.sum = 0) ≤
      zeroNormalSpan R v := by
    rw [NW, Submodule.span_le]
    rintro _ ⟨a, b, c, hs, rfl⟩
    have ha : ∀ q ∈ a, q = 0 := List.sum_eq_zero_iff.mp (by omega : a.sum = 0)
    have hb : ∀ q ∈ b, q = 0 := List.sum_eq_zero_iff.mp (by omega : b.sum = 0)
    have hc : ∀ q ∈ c, q = 0 := List.sum_eq_zero_iff.mp (by omega : c.sum = 0)
    rw [nw, block_zero_modes R 3 a ha, block_zero_modes R 5 b hb,
      block_zero_modes R 4 c hc]
    exact Submodule.subset_span ⟨(a.length, b.length, c.length), rfl⟩
  exact hnormal hn

variable {R} {w : V} {k l : ℕ}

theorem positive_base (h : TwoRectRel R w k l) (q : ℕ) (d : Fin 8)
    (hd : lowSl3 d) (r : ℕ) (hr : 1 ≤ r) :
    R.op d r (thetaDesc R w q) ∈ zeroLowSpan R (thetaDesc R w (q + r)) := by
  have hd' : d = 3 ∨ d = 4 ∨ d = 5 := by unfold lowSl3 at hd; omega
  rcases hd' with rfl | rfl | rfl
  · rw [first_pos_desc h q r hr]
    exact Submodule.zero_mem _
  · rw [second_pos_desc h q r hr]
    exact Submodule.zero_mem _
  · by_cases hr1 : r = 1
    · subst r
      change R.op 5 1 ((R.op 5 1 ^ q) w) ∈ _
      rw [← Module.End.mul_apply, ← pow_succ']
      exact zeroLowSpan_self R _
    · rw [theta_high_desc h q r (by omega)]
      exact Submodule.zero_mem _

/-- The lower-root commutator keeps the same positive current mode, so no
new source-vector relation is assumed while commuting through a zero word. -/
theorem positive_map_zeroLowSpan (h : TwoRectRel R w k l) (q r : ℕ) (hr : 1 ≤ r)
    (d : Fin 8) (hd : lowSl3 d) : zeroLowSpan R (thetaDesc R w q) ≤
      (zeroLowSpan R (thetaDesc R w (q + r))).comap (R.op d r) := by
  have hword : ∀ g : List (Fin 8 × ℕ), zeroLow g → ∀ d : Fin 8, lowSl3 d →
      R.op d r (wordOp R g (thetaDesc R w q)) ∈
        zeroLowSpan R (thetaDesc R w (q + r)) := by
    intro g
    induction g with
    | nil => intro _ d hd; exact positive_base h q d hd r hr
    | cons x g ih =>
        intro hg d hd
        have hx := hg x List.mem_cons_self
        have hg' : zeroLow g := fun y hy => hg y (List.mem_cons_of_mem _ hy)
        rcases x with ⟨c, s⟩
        have hs : s = 0 := hx.2
        subst s
        change R.op d r (R.op c 0 (wordOp R g (thetaDesc R w q))) ∈ _
        rw [comm_apply]
        apply Submodule.add_mem
        · exact zeroLowSpan_inv R _ c hx.1 (ih hg' d hd)
        · have hθ := ih hg' 5 (by decide : lowSl3 5)
          have hd' : d = 3 ∨ d = 4 ∨ d = 5 := by unfold lowSl3 at hd; omega
          have hc' : c = 3 ∨ c = 4 ∨ c = 5 := by
            have hc := hx.1
            unfold lowSl3 at hc
            change 3 ≤ c.val ∧ c.val < 6 at hc
            omega
          rcases hd' with rfl | rfl | rfl <;>
            rcases hc' with rfl | rfl | rfl <;>
            simp [Fin.sum_univ_eight, bracketTable, Nat.add_zero] <;>
            first | exact hθ | exact Submodule.neg_mem _ hθ
  rw [zeroLowSpan, Submodule.span_le]
  rintro _ ⟨g, hg, rfl⟩
  exact hword g hg d hd

theorem lowering_map_zeroLowSpan (h : TwoRectRel R w k l) (q r : ℕ)
    (d : Fin 8) (hd : lowSl3 d) : zeroLowSpan R (thetaDesc R w q) ≤
      (zeroLowSpan R (thetaDesc R w (q + r))).comap (R.op d r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa only [Nat.add_zero] using zeroLowSpan_inv R (thetaDesc R w q) d hd
  · exact positive_map_zeroLowSpan h q r hr d hd

/-- Every lowering word is spanned by zero-mode lowering words on the exact
theta descendant of the same current degree. -/
theorem lowering_word_mem (h : TwoRectRel R w k l) :
    ∀ g : List (Fin 8 × ℕ), (∀ x ∈ g, lowSl3 x.1) →
      wordOp R g w ∈ zeroLowSpan R (thetaDesc R w (SectorGraded.wordDeg g)) := by
  intro g
  induction g with
  | nil => intro _; exact zeroLowSpan_self R w
  | cons x g ih =>
      intro hg
      have hi := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))
      have hv := lowering_map_zeroLowSpan h (SectorGraded.wordDeg g) x.2 x.1
        (hg x List.mem_cons_self) hi
      simpa only [SectorGraded.wordDeg, List.map_cons, List.sum_cons, Nat.add_comm] using hv

/-- PBW transfers the exact lowering-word degree bridge to the whole piece. -/
theorem cycDeg_le_zeroLowSpan (h : TwoRectRel R w k l) (d : ℕ) :
    cycDeg R w d ≤ zeroLowSpan R (thetaDesc R w d) := by
  have hw : ∀ (e : Fin 8) r, ¬ lowSl3 e →
      R.op e r w ∈ ℂ ∙ w ∧ (1 ≤ r → R.op e r w = 0) := by
    intro e r he
    by_cases he' : e.val < 3
    · rw [h.raising e he' r]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · have hh : 6 ≤ e.val := by unfold lowSl3 at he; omega
      refine ⟨?_, fun hr => h.cartan_pos e hh r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · have he' : e = 6 ∨ e = 7 := by omega
        rcases he' with rfl | rfl
        · rw [h.cartan_first]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
        · rw [h.cartan_second]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [h.cartan_pos e hh r hr]
        exact Submodule.zero_mem _
  refine (cycDeg_le_sortedLow keySl3 lowSl3 R keySl3_low hw d).trans
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨g, _, hg, hd, rfl⟩
  rw [← hd]
  exact lowering_word_mem h g hg

theorem zeroLowSpan_le_classical (h : TwoRectRel R w k l) (d : ℕ)
    (hd : d ≤ min k l) : zeroLowSpan R (thetaDesc R w d) ≤
      classicalSpan R (thetaDesc R w d) (k - d) (l - d) := by
  refine (zeroLowSpan_le_normal R _).trans ?_
  rw [zeroNormalSpan, Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  apply normal_mem_classicalSpan R (thetaDesc R w d)
    (raising_desc h d 0 (by decide) 0) _
    (first_sharp_nil_desc h d (hd.trans (min_le_left _ _)))
    (second_sharp_nil_desc h d (hd.trans (min_le_right _ _))) t.1 t.2.1 t.2.2
  rw [Nat.cast_sub (hd.trans (min_le_left _ _))]
  exact first_weight_desc h d

theorem zeroLowSpan_eq_bot_of_gt (h : TwoRectRel R w k l) (d : ℕ)
    (hd : min k l < d) : zeroLowSpan R (thetaDesc R w d) = ⊥ := by
  rw [thetaDesc_eq_zero h d hd, zeroLowSpan, Submodule.span_eq_bot]
  rintro _ ⟨g, _, rfl⟩
  exact wordOp_zero R g

/-- The explicit finite index of the full two-rectangle spanning family. -/
abbrev TwoIndex (k l : ℕ) :=
  Σ d : Fin (min k l + 1), ClassicalIndex (k - d.val) (l - d.val)

def twoWord (R : CurrentModule bracketTable V) (w : V) (k l : ℕ)
    (i : TwoIndex k l) : V :=
  classicalWord R (thetaDesc R w i.1.val) (k - i.1.val) (l - i.1.val) i.2

def twoSpan (R : CurrentModule bracketTable V) (w : V) (k l : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (twoWord R w k l))

/-- Every actual current word lies in the explicit finite two-factor family. -/
theorem cyclicSpan_le_twoSpan (h : TwoRectRel R w k l) :
    cyclicSpan R w ≤ twoSpan R w k l := by
  rw [cyclicSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  have hcyc : wordOp R g w ∈ cycDeg R w (SectorGraded.wordDeg g) :=
    Submodule.subset_span ⟨g, rfl, rfl⟩
  have hv := cycDeg_le_zeroLowSpan h _ hcyc
  by_cases hd : SectorGraded.wordDeg g ≤ min k l
  · have hc := zeroLowSpan_le_classical h _ hd hv
    have hle : classicalSpan R (thetaDesc R w (SectorGraded.wordDeg g))
        (k - SectorGraded.wordDeg g) (l - SectorGraded.wordDeg g) ≤ twoSpan R w k l := by
      rw [classicalSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨⟨⟨SectorGraded.wordDeg g, by omega⟩, i⟩, rfl⟩
    exact hle hc
  · rw [zeroLowSpan_eq_bot_of_gt h _ (by omega)] at hv
    change wordOp R g w ∈ twoSpan R w k l
    rw [(Submodule.mem_bot ℂ).mp hv]
    exact Submodule.zero_mem _

/-- The actual cyclic module is finite-dimensional, with a constructive bound
by the explicit classical branching family, for arbitrary rectangle sizes. -/
theorem two_rectangle_bound_index (h : TwoRectRel R w k l) :
    FiniteDimensional ℂ (cyclicSpan R w) ∧
      Module.finrank ℂ (cyclicSpan R w) ≤ Fintype.card (TwoIndex k l) := by
  classical
  have hle := cyclicSpan_le_twoSpan h
  haveI : FiniteDimensional ℂ (twoSpan R w k l) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (cyclicSpan R w) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  exact finrank_range_le_card (twoWord R w k l)

theorem TwoIndex_card_small (k l : ℕ) (hk : k ≤ 3) (hl : l ≤ 3) :
    Fintype.card (TwoIndex k l) = (k + 2).choose 2 * (l + 2).choose 2 := by
  rw [Fintype.card_sigma]
  exact (Fin.sum_univ_eq_sum_range (fun q : ℕ =>
    Fintype.card (ClassicalIndex (k - q) (l - q))) (min k l + 1)).trans
      (two_rectangle_count k l hk hl)

/-- The sharp product bound for two opposite rectangles of sizes at most three,
proved from the actual simple-root presentations and explicit spanning. -/
theorem two_rectangle_bound (h : TwoRectRel R w k l) (hk : k ≤ 3) (hl : l ≤ 3) :
    FiniteDimensional ℂ (cyclicSpan R w) ∧
      Module.finrank ℂ (cyclicSpan R w) ≤ (k + 2).choose 2 * (l + 2).choose 2 := by
  obtain ⟨hFD, hdim⟩ := two_rectangle_bound_index h
  exact ⟨hFD, hdim.trans_eq (TwoIndex_card_small k l hk hl)⟩

end

end VOA.DeligneAudit.A2.CVRectMixedSpanning

#print axioms VOA.DeligneAudit.A2.CVRectMixedSpanning.positive_map_zeroLowSpan
#print axioms VOA.DeligneAudit.A2.CVRectMixedSpanning.cycDeg_le_zeroLowSpan
#print axioms VOA.DeligneAudit.A2.CVRectMixedSpanning.two_rectangle_bound
