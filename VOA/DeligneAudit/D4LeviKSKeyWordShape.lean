import VOA.DeligneAudit.D4LeviKSKeySourceOrbit

/-! Exact XYZ keys have fixed-shape homogeneous source representatives. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

theorem ksCountP_sum {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
      split <;> simp_all [Nat.add_comm]

theorem ksWord_colour_count (l : List (Fin 6 × ℕ)) (j : Fin 6) :
    (l.map Prod.fst).count j = l.countP (fun p => p.1 = j) := by
  simp only [List.count, List.countP_map, Function.comp_def]
  congr 1

theorem ksPairSource_colour_counts (a b c : ℕ) (j : Fin 6) :
    ((Finset.univ.toList : List (PairSource a b c)).map
      (pairSourceShape a b c)).count j =
        if j = 1 then a + b else if j = 4 then b else if j = 5 then c else 0 := by
  classical
  simp only [List.count, List.countP_map, ksCountP_sum, Finset.sum_map_toList]
  fin_cases j <;>
    simp [pairSourceShape, Fintype.sum_sum_type, Function.comp_def, Nat.add_comm]

theorem ksPair_key_hasWordShape (a b c d : ℕ) (l : List (Fin 6 × ℕ))
    (hk : wordKey l = pairFinalKey a b c d) :
    HasWordShape (pairSourceShape a b c) l := by
  classical
  apply hasWordShape_of_colourPerm
  apply List.perm_iff_count.mpr
  intro j
  rw [ksWord_colour_count, ksPairSource_colour_counts]
  have he := congrArg RadicalKey.e hk
  have hx := congrArg RadicalKey.x hk
  have hu := congrArg RadicalKey.u hk
  have hup := congrArg RadicalKey.up hk
  have hy := congrArg RadicalKey.y hk
  have hz := congrArg RadicalKey.z hk
  change l.countP (fun p => p.1 = 0) = 0 at he
  change l.countP (fun p => p.1 = 1) = a + b at hx
  change l.countP (fun p => p.1 = 2) = 0 at hu
  change l.countP (fun p => p.1 = 3) = 0 at hup
  change l.countP (fun p => p.1 = 4) = b at hy
  change l.countP (fun p => p.1 = 5) = c at hz
  fin_cases j
  · exact he
  · exact hx
  · exact hu
  · exact hup
  · exact hy
  · exact hz

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Every radical word of the final key has a symmetric source representative
    of exactly the key's mode degree. -/
theorem ksPair_key_word_symmetric_lift (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c d : ℕ) (l : List (Fin 6 × ℕ)) (hk : wordKey l = pairFinalKey a b c d) :
    ∃ P : pairSourceSymmetric a b c,
      (P : MvPolynomial (PairSource a b c) ℂ).IsHomogeneous d ∧
      xyzEvaluation ρ w (pairSourceShape a b c) P = radicalWord ρ w l := by
  classical
  obtain ⟨f, hf⟩ := ksPair_key_hasWordShape a b c d l hk
  have hd : (∑ i, f i) = d := by
    have hsum := (hf.map Prod.snd).sum_eq
    have hdegree := congrArg RadicalKey.degree hk
    change (l.map Prod.snd).sum = d at hdegree
    simpa only [shapedModes, List.map_map, Function.comp_def,
      Finset.sum_map_toList, hdegree] using hsum.symm
  obtain ⟨P, hP, he⟩ := ksPair_monomial_symmetric_lift ρ w a b c f
  refine ⟨P, by simpa only [hd] using hP, ?_⟩
  rw [he, xyzEvaluation_prod_X_pow]
  exact (radicalWord_perm ρ w hf).symm

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksCountP_sum
#print axioms VOA.DeligneAudit.D4Levi.ksWord_colour_count
#print axioms VOA.DeligneAudit.D4Levi.ksPairSource_colour_counts
#print axioms VOA.DeligneAudit.D4Levi.ksPair_key_hasWordShape
#print axioms VOA.DeligneAudit.D4Levi.ksPair_key_word_symmetric_lift
