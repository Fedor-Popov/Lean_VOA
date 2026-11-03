import VOA.DeligneAudit.D4CharA2KeyGraded

/-! The full node-two Levi orbit has the sharp GL2 bound in each exact degree. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2GradedKey_degree_action (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (a : Fin 8) (ha : a2Levi a) (d r : ℕ) :
    let z := (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v
    sl2LowerDegree (a2GradedKeyF ρ w q k) z d ≤
      (sl2LowerDegree (a2GradedKeyF ρ w q k) z (d + r)).comap
        (a2GradedKeyOp ρ w q k a ha r) := by
  have hs := a2GradedKey_sl2 ρ w q k
  have hr := a2GradedKey_rel ρ w p q h k hv
  have hx := a2GradedKey_extra_rel ρ w p q h k hv
  rcases ha with rfl | rfl | rfl | rfl
  · exact sl2LowerDegree_raise hs _ hr.1 hr.2.2.1 hr.2.1 d r
  · exact sl2LowerDegree_lower _ _ d r
  · exact sl2LowerDegree_cartan _ _ 1 (fun s t => by
      rw [one_smul]; exact a2GradedKey_extra_comm ρ w q k s t) _ hx.1 hx.2 d r
  · exact sl2LowerDegree_cartan _ _ (-2) hs.hHF _ hr.2.2.1 hr.2.1 d r

theorem a2GradedKey_word_mem (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (l : List (Fin 8 × ℕ)) (hl : l.Forall (fun x => a2Levi x.1)) :
    (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ (wordOp ρ l v) ∈
      sl2LowerDegree (a2GradedKeyF ρ w q k)
        ((a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v)
        (SectorGraded.wordDeg l) := by
  induction l with
  | nil => exact sl2LowerDegree_self _ _
  | cons x l ih =>
      obtain ⟨a, r⟩ := x
      simp only [List.forall_cons] at hl
      obtain ⟨ha, hl⟩ := hl
      have hh := a2GradedKey_degree_action ρ w p q h k hv a ha
        (SectorGraded.wordDeg l) r (ih hl)
      change (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ
        (ρ.op a r (wordOp ρ l v)) ∈
          sl2LowerDegree (a2GradedKeyF ρ w q k)
            ((a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v)
            (SectorGraded.wordDeg l + r) at hh
      simpa only [wordOp, SectorGraded.wordDeg, List.map_cons, List.sum_cons,
        Nat.add_comm] using hh

def gradedA2LeviOrbit (v : V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin 8 × ℕ),
    l.Forall (fun x => a2Levi x.1) ∧ SectorGraded.wordDeg l = d ∧ z = wordOp ρ l v}

theorem a2GradedKey_orbit_le_lower (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k) (d : ℕ) :
    (gradedA2LeviOrbit ρ v d).map
      (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ ≤
        sl2LowerDegree (a2GradedKeyF ρ w q k)
          ((a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v) d := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro z ⟨l, hl, hd, rfl⟩
  simpa only [← hd] using a2GradedKey_word_mem ρ w p q h k hv l hl

/-- Graded replacement for `a2_key_levi_orbit_rank`, retaining the full Levi action. -/
theorem a2GradedKey_orbit_bound (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (hk : 0 ≤ a2KeyHeight q k) (d : ℕ) :
    let O := (gradedA2LeviOrbit ρ v d).map
      (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ
    FiniteDimensional ℂ O ∧
      Module.finrank ℂ O ≤ A2.gl2Hilb (a2KeyHeight q k).toNat 0 d := by
  have hh := a2GradedKey_lower_bound ρ w p q h k hv hk d
  haveI := hh.1
  have hi := a2GradedKey_orbit_le_lower ρ w p q h k hv d
  exact ⟨Submodule.finiteDimensional_of_le hi, (Submodule.finrank_mono hi).trans hh.2⟩

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_degree_action
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_word_mem
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_orbit_le_lower
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_orbit_bound
