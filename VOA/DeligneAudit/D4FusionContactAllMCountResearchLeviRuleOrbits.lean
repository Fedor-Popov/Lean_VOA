import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleSeedWords

/-! Exact source-family description of the original actual differential ideal:
plain single-color shifts followed by negative words (U) or contact words (C).
The reverse spanning inclusion is proved, not postulated. No count is asserted. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
noncomputable section

def branchCategory (b : Bool) : ℕ := if b then 0 else 1

theorem branchCategory_lt_two (b : Bool) : branchCategory b < 2 := by cases b <;> decide

theorem split_two_categories (lo : ℕ) (hlo : lo < 2) :
    ∀ (l : List (Fin 18 × ℕ)), l.IsChain (fun x y => key x ≤ key y) →
      (∀ x ∈ l, category x.1 = lo ∨ category x.1 = 2) →
      ∃ p h, l = p++h ∧ (∀ x ∈ p, category x.1 = lo) ∧ (∀ x ∈ h, category x.1 = 2) := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨[],[],rfl,by simp,by simp⟩
  | cons x l ih =>
      intro hs hc
      have ht : ∀ y ∈ l, category y.1 = lo ∨ category y.1 = 2 :=
        fun y hy => hc y (List.mem_cons_of_mem _ hy)
      rcases hc x (List.mem_cons_self) with hx | hx
      · obtain ⟨p,h,he,hp,hh⟩ := ih hs.tail ht
        refine ⟨x::p,h,?_,?_,hh⟩
        · change x::l = x::(p++h)
          exact congrArg (List.cons x) he
        · intro y hy
          rcases List.mem_cons.mp hy with hy | hy
          · subst y; exact hx
          · exact hp y hy
      · refine ⟨[],x::l,rfl,by simp,?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · subst y; exact hx
        · have hxy := hs.rel_cons hy
          change category x.1 ≤ category y.1 at hxy
          rcases ht y hy with hylo | hytwo
          · omega
          · exact hytwo

theorem source_cartan_nonzero : ∀ b : Bool, coeff 1 (sourceColor b) ≠ 0 := by decide +kernel

theorem monoShift_mem (m : ℕ) (b : Bool) (k : ℕ) (p : MonoRing ℂ m)
    (hp : monoMap ℂ m (sourceColor b) p ∈ AllM.candidateIdeal m) :
    monoMap ℂ m (sourceColor b) (monoShift ℂ m k p) ∈ AllM.candidateIdeal m := by
  have hd := deriv_closed m 1 k hp
  rw [cartan_mono_any m 1 k b p (by decide)] at hd
  have hn : (coeff 1 (sourceColor b):ℂ) ≠ 0 := by exact_mod_cast source_cartan_nonzero b
  exact (Submodule.smul_mem_iff ((AllM.candidateIdeal m).restrictScalars ℂ) hn).mp hd

theorem shiftWord_seed_mem (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ) :
    monoMap ℂ m (sourceColor j.val.1) (shiftWord m modes (monoSeed m j)) ∈
      AllM.candidateIdeal m := by
  induction modes with
  | nil =>
      change monoMap ℂ m (sourceColor j.val.1) (monoSeed m j) ∈ AllM.candidateIdeal m
      rw [← seed_eq_monoMap]
      exact AllM.seed_mem_candidate m j
  | cons k modes ih => exact monoShift_mem m j.val.1 k _ ih

def orbitSeeds (m : ℕ) : Set (MvPolynomial (Vars m) ℂ) :=
  {p | ∃ (j : AllM.SeedIndex m) (modes : List ℕ) (outer : List (Fin 18 × ℕ)),
    (∀ x ∈ outer, category x.1 = branchCategory j.val.1) ∧
      p = wordOp (representation ℂ m) outer
        (monoMap ℂ m (sourceColor j.val.1) (shiftWord m modes (monoSeed m j)))}

def orbitIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) := Ideal.span (orbitSeeds m)

theorem separated_word_mem_orbit (m : ℕ) (j : AllM.SeedIndex m) (l : List (Fin 18 × ℕ))
    (hs : l.IsChain (fun x y => key x ≤ key y))
    (hc : ∀ x ∈ l, category x.1 = branchCategory j.val.1 ∨ category x.1 = 2) :
    wordOp (representation ℂ m) l (AllM.seedPoly m j) ∈ orbitIdeal m := by
  obtain ⟨p,h,he,hp,hh⟩ := split_two_categories (branchCategory j.val.1)
    (branchCategory_lt_two _) l hs hc
  rw [he,wordOp_append,seed_eq_monoMap,cartan_word m j.val.1 h hh,wordOp_smul]
  apply ((orbitIdeal m).restrictScalars ℂ).smul_mem
  exact Ideal.subset_span ⟨j,h.map Prod.snd,p,hp,rfl⟩

theorem noPositive_le_orbit (m : ℕ) : noPositiveIdeal m ≤ orbitIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨j,l,hs,hn,rfl⟩
  cases hb : j.val.1 with
  | false =>
      by_cases hp : ∃ x ∈ l, category x.1 = 0
      · rw [u_contact_word_zero m j hb l hp]
        exact Ideal.zero_mem _
      · apply separated_word_mem_orbit m j l hs
        intro x hx
        have hmax := hn x hx
        have hne : category x.1 ≠ 0 := fun he => hp ⟨x,hx,he⟩
        have hc : category x.1 = 1 ∨ category x.1 = 2 := by omega
        simpa only [branchCategory,hb,Bool.false_eq_true,if_false] using hc
  | true =>
      by_cases hp : ∃ x ∈ l, category x.1 = 1
      · rw [c_negative_word_zero m j hb l hs hn hp]
        exact Ideal.zero_mem _
      · apply separated_word_mem_orbit m j l hs
        intro x hx
        have hmax := hn x hx
        have hne : category x.1 ≠ 1 := fun he => hp ⟨x,hx,he⟩
        have hc : category x.1 = 0 ∨ category x.1 = 2 := by omega
        simpa only [branchCategory,hb,if_true] using hc

theorem orbit_le_candidate (m : ℕ) : orbitIdeal m ≤ AllM.candidateIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨j,modes,outer,_,rfl⟩
  exact word_mem_candidate m outer (shiftWord_seed_mem m j modes)

/-- Full source-family completeness for every m, with NO presentation premise. -/
theorem candidateIdeal_eq_orbitIdeal (m : ℕ) : AllM.candidateIdeal m = orbitIdeal m := by
  apply le_antisymm
  · exact ((candidate_le_triangular m).trans (triangular_le_noPositive m)).trans
      (noPositive_le_orbit m)
  · exact orbit_le_candidate m

end
#print axioms shiftWord_seed_mem
#print axioms noPositive_le_orbit
#print axioms candidateIdeal_eq_orbitIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
