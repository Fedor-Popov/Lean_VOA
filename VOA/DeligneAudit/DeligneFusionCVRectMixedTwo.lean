import VOA.DeligneAudit.DeligneFusionCVRectMixedClassical

/-!
# The classical current-degree bridge for mixed rectangles

PBW reduction at degree zero turns the actual classical normal-word bound
into a bound on the homogeneous cyclic piece. No equality of the two
simple-root highest weights is assumed, and no character-chain import is used.
-/

namespace VOA.DeligneAudit.A2.CVRectMixedTwo

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CLNormal
open VOA.DeligneAudit.A2.CVRectMixedClassical VOA.DeligneAudit.A2.CVRectSingle

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {ρ : CurrentModule bracketTable V} {w : V}

/-- Lowering-word normal ordering preserves its actual total current degree. -/
theorem lowword_degree_normal : ∀ l : List (Fin 8 × ℕ), (∀ x ∈ l, lowSl3 x.1) →
    wordOp ρ l w ∈ NW ρ w (fun a b c => a.sum + b.sum + c.sum = SectorGraded.wordDeg l)
  | [], _ => nw_mem (a := []) (b := []) (c := []) (by simp [SectorGraded.wordDeg])
  | (⟨d, k⟩ :: l), hl => by
      have ih := lowword_degree_normal l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have hdeg : SectorGraded.wordDeg ((d, k) :: l) = k + SectorGraded.wordDeg l := by
        simp [SectorGraded.wordDeg]
      change ρ.op d k (wordOp ρ l w) ∈ _
      rw [hdeg]
      have hd := hl _ List.mem_cons_self
      unfold lowSl3 at hd
      have : d = 3 ∨ d = 4 ∨ d = 5 := by
        rcases d with ⟨d, hd8⟩
        simp only at hd
        rcases (show d = 3 ∨ d = 4 ∨ d = 5 by omega) with h | h | h <;> subst h <;> simp [Fin.ext_iff]
      rcases this with rfl | rfl | rfl
      · exact map_NW _ (fun a b c hp => by
          rw [f1_nw]; exact nw_mem (by simp only [List.sum_cons]; omega)) ih
      · exact map_NW _ (fun a b c hp => NW_mono (fun a' b' c' h => by omega) (f2_nw k a b c)) ih
      · exact map_NW _ (fun a b c hp => by
          rw [fθ_nw]; exact nw_mem (by simp only [List.sum_cons]; omega)) ih

/-- The actual degree-zero cyclic piece is spanned by zero-mode normal words. -/
theorem cycDeg_zero_le_normal (hE : ∀ (e : Fin 8), e.val < 3 → ∀ r, ρ.op e r w = 0)
    (hHpos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ r, 1 ≤ r → ρ.op h r w = 0)
    {m n : ℕ} (hH1 : ρ.op 6 0 w = (m : ℂ) • w)
    (hH2 : ρ.op 7 0 w = (n : ℂ) • w) : cycDeg ρ w 0 ≤ zeroNormalSpan ρ w := by
  have hw : ∀ (d : Fin 8) r, ¬ lowSl3 d →
      ρ.op d r w ∈ ℂ ∙ w ∧ (1 ≤ r → ρ.op d r w = 0) := by
    intro d r hd
    by_cases he : d.val < 3
    · rw [hE d he r]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · have hh : 6 ≤ d.val := by unfold lowSl3 at hd; omega
      refine ⟨?_, fun hr => hHpos d hh r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · have hd' : d = 6 ∨ d = 7 := by omega
        rcases hd' with rfl | rfl
        · rw [hH1]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
        · rw [hH2]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [hHpos d hh r hr]
        exact Submodule.zero_mem _
  refine (cycDeg_le_sortedLow keySl3 lowSl3 ρ keySl3_low hw 0).trans
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, _, hl, hd, rfl⟩
  have hn := lowword_degree_normal (ρ := ρ) (w := w) l hl
  rw [hd] at hn
  have hnormal : NW ρ w (fun a b c => a.sum + b.sum + c.sum = 0) ≤
      zeroNormalSpan ρ w := by
    rw [NW, Submodule.span_le]
    rintro _ ⟨a, b, c, hs, rfl⟩
    have ha : ∀ q ∈ a, q = 0 := List.sum_eq_zero_iff.mp (by omega : a.sum = 0)
    have hb : ∀ q ∈ b, q = 0 := List.sum_eq_zero_iff.mp (by omega : b.sum = 0)
    have hc : ∀ q ∈ c, q = 0 := List.sum_eq_zero_iff.mp (by omega : c.sum = 0)
    rw [nw, block_zero_modes ρ 3 a ha, block_zero_modes ρ 5 b hb,
      block_zero_modes ρ 4 c hc]
    exact Submodule.subset_span ⟨(a.length, b.length, c.length), rfl⟩
  exact hnormal hn

/-- The constructive classical bound applies directly to an unequal-weight
degree-zero current piece, with all source hypotheses stated explicitly. -/
theorem cycDeg_zero_bound (hE : ∀ (e : Fin 8), e.val < 3 → ∀ r, ρ.op e r w = 0)
    (hHpos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ r, 1 ≤ r → ρ.op h r w = 0)
    {m n : ℕ} (hH1 : ρ.op 6 0 w = (m : ℂ) • w)
    (hH2 : ρ.op 7 0 w = (n : ℂ) • w)
    (hNil1 : (ρ.op 3 0 ^ (m + 1)) w = 0)
    (hNil2 : (ρ.op 4 0 ^ (n + 1)) w = 0) :
    FiniteDimensional ℂ (cycDeg ρ w 0) ∧
      Module.finrank ℂ (cycDeg ρ w 0) ≤ Fintype.card (ClassicalIndex m n) := by
  obtain ⟨hFD, hdim⟩ := zeroNormalSpan_bound ρ w
    (hE 0 (by decide) 0) hH1 hNil1 hNil2
  haveI := hFD
  have hle := cycDeg_zero_le_normal hE hHpos hH1 hH2
  exact ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans hdim⟩

/-- Tiny finite counts for the classical weights occurring in two rectangles
of sizes at most three. The largest index set tested has 112 candidates. -/
theorem classicalIndex_card_small (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :
    Fintype.card (ClassicalIndex m n) = (m + 1) * (n + 1) * (m + n + 2) / 2 := by
  interval_cases m <;> interval_cases n <;> decide

/-- The complete finite branching count for two opposite small rectangles. -/
theorem two_rectangle_count (k l : ℕ) (hk : k ≤ 3) (hl : l ≤ 3) :
    (∑ q ∈ Finset.range (min k l + 1), Fintype.card (ClassicalIndex (k - q) (l - q))) =
      (k + 2).choose 2 * (l + 2).choose 2 := by
  interval_cases k <;> interval_cases l <;> decide

end

end VOA.DeligneAudit.A2.CVRectMixedTwo

#print axioms VOA.DeligneAudit.A2.CVRectMixedTwo.cycDeg_zero_bound
#print axioms VOA.DeligneAudit.A2.CVRectMixedTwo.two_rectangle_count
