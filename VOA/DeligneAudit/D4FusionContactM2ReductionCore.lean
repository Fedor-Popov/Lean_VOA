import VOA.DeligneAudit.D4FusionContactM2WordRows
import VOA.DeligneAudit.D4FusionContactM2NormalWords
import VOA.DeligneAudit.D4FusionContactM2Weight
import VOA.DeligneAudit.D4FusionContactM2Weighted
import Mathlib.Algebra.MvPolynomial.Rename

/-! Sparse reducing packets give genuine normal-word quotient spanning.
Divisibility uses a complementary word, and additive weight makes every
multiplied tail strictly smaller. No count or finiteness premise is used. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

theorem subperm_complement {a b : Word} (h : a.Subperm b) :
    ∃ t : Word, b.Perm (a ++ t) := by
  obtain ⟨v, hv, hs⟩ := h
  obtain ⟨t, ht⟩ := hs.exists_perm_append
  exact ⟨t, ht.trans (hv.append_right t)⟩

variable {ι : Type} (f : Fin 18 → ι)

theorem mapped_polyWord_append (a b : Word) :
    polyWord ((a ++ b).map f) = polyWord (a.map f) * polyWord (b.map f) := by
  simp only [List.map_append, polyWord, List.map_append, List.prod_append]

theorem mapped_polyWord_perm {a b : Word} (h : a.Perm b) :
    polyWord (a.map f) = polyWord (b.map f) := by
  exact ((h.map f).map MvPolynomial.X).prod_eq

theorem rowEval_mul_factor (row : WordRow) (t : Word) :
    rowEval f row * polyWord (t.map f) =
      (row.map fun x => (x.2 : ℂ) • polyWord ((x.1 ++ t).map f)).sum := by
  induction row with
  | nil => simp
  | cons x row ih =>
      obtain ⟨v, z⟩ := x
      simp only [rowEval_cons, add_mul, smul_mul_assoc, ih, List.map_cons,
        List.sum_cons, mapped_polyWord_append, Int.cast_smul_eq_zsmul]

variable (I : Ideal (MvPolynomial ι ℂ))

abbrev quotientWord (l : Word) := (I.restrictScalars ℂ).mkQ (polyWord (l.map f))

theorem quotient_row_mul_zero (row : WordRow) (t : Word) (hrow : rowEval f row ∈ I) :
    (row.map fun x => (x.2 : ℂ) • quotientWord f I (x.1 ++ t)).sum = 0 := by
  have hm : rowEval f row * polyWord (t.map f) ∈ I := I.mul_mem_right _ hrow
  have hz : (I.restrictScalars ℂ).mkQ (rowEval f row * polyWord (t.map f)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  rw [rowEval_mul_factor] at hz
  simpa only [map_list_sum, List.map_map, Function.comp_def, map_smul] using hz

/-- The packet hypotheses concern actual relations in I and verified
strict weights. The normal list is the complete avoidance enumeration. -/
theorem quotient_normal_words_span (hf : Function.Surjective f)
    (packets : List WordRow) (leaders : List Word)
    (hheads : packets.map (fun row => (row.headD ([], 0)).1) = leaders)
    (hmem : ∀ row ∈ packets, rowEval f row ∈ I)
    (hred : ∀ row ∈ packets, ReducingRow row)
    (d : ℕ) (hhigh : ∀ l : Word, d + 1 ≤ l.length → polyWord (l.map f) ∈ I) :
    Submodule.span ℂ (Set.range fun i : Fin (normalWords leaders d).length =>
      quotientWord f I ((normalWords leaders d).get i)) = ⊤ := by
  let b : Word → MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ := quotientWord f I
  let normalVector : Fin (normalWords leaders d).length →
      MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ :=
    fun i => b ((normalWords leaders d).get i)
  have hrows : ∀ w : Word, (∃ i, b w = normalVector i) ∨
      ∃ (c : ℂ) (tail : List (ℂ × Word)), c ≠ 0 ∧
        (∀ x ∈ tail, wordWeight x.2 < wordWeight w) ∧
          c • b w + (tail.map fun x => x.1 • b x.2).sum ∈ (⊥ : Submodule ℂ _) := by
    intro w
    by_cases hw : d + 1 ≤ w.length
    · right
      refine ⟨1, [], one_ne_zero, by simp, ?_⟩
      have hz : b w = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (hhigh w hw)
      simp [hz]
    have hlen : w.length ≤ d := by omega
    by_cases ha : Avoids leaders w
    · left
      have hc : canonical w ∈ normalWords leaders d := by
        apply mem_normalWords_of_sorted
        · simpa only [canonical, List.length_insertionSort] using hlen
        · exact List.pairwise_insertionSort _ _
        · exact avoids_mono (List.perm_insertionSort (· ≤ ·) w).subperm ha
      have hex : ∃ v ∈ normalWords leaders d, b w = b v :=
        ⟨canonical w, hc, (congrArg (I.restrictScalars ℂ).mkQ
          (polyWord_canonical f w)).symm⟩
      exact List.exists_mem_iff_get.mp hex
    · right
      rw [avoids_iff] at ha
      push Not at ha
      obtain ⟨lead, hlead, hdiv⟩ := ha
      rw [← hheads] at hlead
      obtain ⟨row, hrow, hhead⟩ := List.mem_map.mp hlead
      cases row with
      | nil => exact (hred [] hrow).elim
      | cons x tail =>
          obtain ⟨l, c⟩ := x
          change l = lead at hhead
          subst lead
          have hr := hred ((l, c) :: tail) hrow
          obtain ⟨t, ht⟩ := subperm_complement hdiv
          refine ⟨(c : ℂ), tail.map (fun x => ((x.2 : ℂ), x.1 ++ t)),
            by exact_mod_cast hr.1, ?_, ?_⟩
          · intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            have hyw := (List.forall_iff_forall_mem.mp hr.2 y hy).2
            rw [wordWeight_append, wordWeight_perm ht, wordWeight_append]
            omega
          · have hz := quotient_row_mul_zero f I ((l, c) :: tail) t (hmem _ hrow)
            simp only [List.map_cons, List.sum_cons] at hz
            have hb : b w = b (l ++ t) :=
              congrArg (I.restrictScalars ℂ).mkQ (mapped_polyWord_perm f ht)
            rw [Submodule.mem_bot]
            simpa only [List.map_map, Function.comp_def, hb] using hz
  have hreduction := weighted_rows_span_le (⊥ : Submodule ℂ _)
    b wordWeight normalVector hrows
  rw [bot_sup_eq] at hreduction
  let L : MvPolynomial (Fin 18) ℂ →ₗ[ℂ] MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ :=
    (I.restrictScalars ℂ).mkQ ∘ₗ (MvPolynomial.rename f).toLinearMap
  have hL : ∀ l : Word, L (wordMonomial ℂ (Fin 18) l) = b l := by
    intro l
    change (I.restrictScalars ℂ).mkQ
      ((MvPolynomial.rename f) ((l.map MvPolynomial.X).prod)) =
        (I.restrictScalars ℂ).mkQ (((l.map f).map MvPolynomial.X).prod)
    congr 1
    simp only [map_list_prod, List.map_map, MvPolynomial.rename_X, Function.comp_def]
  have hsurj : Function.Surjective L :=
    (I.restrictScalars ℂ).mkQ_surjective.comp (MvPolynomial.rename_surjective f hf)
  have hspan := bounded_word_map_span L hsurj d (id : Word → Word)
    (fun l _ => ⟨l, List.Perm.refl l⟩) (fun l hl => by
      rw [hL]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hhigh l hl))
  have hspan' : Submodule.span ℂ (Set.range b) = ⊤ := by simpa only [hL] using hspan
  apply top_unique
  rw [← hspan']
  exact hreduction

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.quotient_normal_words_span
