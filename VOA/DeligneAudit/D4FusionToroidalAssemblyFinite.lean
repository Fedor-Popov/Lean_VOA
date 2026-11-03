import VOA.DeligneAudit.D4FusionToroidalAssembly

/-! A finite-dimensional universal module has a finite high-mode filtration. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)

/-- Only finitely many homogeneous current degrees occur in a finite universal module. -/
theorem finite_current_degrees [FiniteDimensional ℂ (UModG f R)] :
    {d : ℕ | cycDeg (univRepG f R) (wUG f R) d ≠ ⊥}.Finite := by
  let S : Set ℕ := {d | cycDeg (univRepG f R) (wUG f R) d ≠ ⊥}
  by_contra hfin
  have hinf : S.Infinite := hfin
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq
    (Module.finrank ℂ (UModG f R) + 1)
  have hpos : ∀ d ∈ s,
      1 ≤ Module.finrank ℂ (cycDeg (univRepG f R) (wUG f R) d) := by
    intro d hd
    have hne : cycDeg (univRepG f R) (wUG f R) d ≠ ⊥ :=
      hs (Finset.mem_coe.mpr hd)
    by_contra hn
    have hz : Module.finrank ℂ (cycDeg (univRepG f R) (wUG f R) d) = 0 := by
      omega
    exact hne (Submodule.finrank_eq_zero.mp hz)
  have hsum := D4FusionContact.Polynomial.sum_finrank_univ_cycDeg_le f R s
  have hlow : s.card ≤
      ∑ d ∈ s, Module.finrank ℂ (cycDeg (univRepG f R) (wUG f R) d) := by
    calc
      s.card = ∑ d ∈ s, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum hpos
  omega

/-- Each high-mode letter contributes at least `m` to current degree. -/
theorem tmWeight_mul_le_wordDeg (m : ℕ) : ∀ l : List (Ltr n),
    FusionToroidal.tmWeight m l * m ≤ SectorGraded.wordDeg l
  | [] => by simp [FusionToroidal.tmWeight, SectorGraded.wordDeg]
  | x :: l => by
      have ih := tmWeight_mul_le_wordDeg m l
      rw [FusionToroidal.tmWeight_cons]
      by_cases hx : m ≤ x.2
      · simp only [if_pos hx, Nat.add_mul]
        simp only [SectorGraded.wordDeg, List.map_cons, List.sum_cons] at ih ⊢
        omega
      · simp only [if_neg hx, add_zero, SectorGraded.wordDeg,
          List.map_cons, List.sum_cons]
        simp only [SectorGraded.wordDeg] at ih
        omega

/-- G1: for `m ≥ 1`, finite-dimensionality forces a vanishing filtration step. -/
theorem finite_TU [FiniteDimensional ℂ (UModG f R)]
    (m : ℕ) (hm : 1 ≤ m) : ∃ D, TU f R m D = ⊥ := by
  let S : Set ℕ := {d | cycDeg (univRepG f R) (wUG f R) d ≠ ⊥}
  have hS : S.Finite := finite_current_degrees f R
  obtain ⟨B, hB⟩ := hS.bddAbove
  refine ⟨B + 1, ?_⟩
  apply le_antisymm
  · rw [TU_eq_filt, FusionToroidal.TU, FusionToroidal.Tfree,
      Submodule.map_span, Submodule.span_le]
    rintro x ⟨v, ⟨l, hl, rfl⟩, rfl⟩
    have hdeg : B < SectorGraded.wordDeg l := by
      have hweight := tmWeight_mul_le_wordDeg (n := n) m l
      have hmul : B + 1 ≤ FusionToroidal.tmWeight m l * m := by
        have hmul1 : (B + 1) * 1 ≤ FusionToroidal.tmWeight m l * m :=
          Nat.mul_le_mul hl hm
        simpa using hmul1
      omega
    have hbot : cycDeg (univRepG f R) (wUG f R)
        (SectorGraded.wordDeg l) = ⊥ := by
      by_contra hn
      have hb := hB (show SectorGraded.wordDeg l ∈ S from hn)
      omega
    have hword : wordOp (univRepG f R) l (wUG f R) ∈
        cycDeg (univRepG f R) (wUG f R) (SectorGraded.wordDeg l) :=
      Submodule.subset_span ⟨l, rfl, rfl⟩
    rw [hbot] at hword
    change wordOp (univRepG f R) l (wUG f R) = 0 at hword
    change (Jrel f R).mkQ (sw l) = 0
    simpa only [wordOp_univG] using hword
  · exact bot_le

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.finite_current_degrees
#print axioms VOA.DeligneAudit.Toroidal.finite_TU
