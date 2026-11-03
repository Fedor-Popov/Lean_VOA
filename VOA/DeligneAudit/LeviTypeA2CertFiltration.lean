import VOA.DeligneAudit.LeviTypeA2CertCompoundNil
import VOA.DeligneAudit.LeviTypeA2CertKeyClosure
import VOA.DeligneAudit.LeviTypeA2CertKeyInsert
import VOA.DeligneAudit.LeviTypeA2CertClosureMinimal

/-! The radical key layers generate the cyclic module after Levi closure. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The sum of all radical key layers. -/
def a2AllKeySpan : Submodule ℂ V :=
  ⨆ k : A2RadicalKey, a2KeyLayer ρ w k

private theorem radicalWord_mem_cyc (l : List (Fin 2 × ℕ)) :
    radicalWord (a2RadicalOp ρ) l • w ∈
      VOA.DeligneAudit.UnivG.cycSubG ρ w := by
  induction l with
  | nil =>
      simpa [radicalWord] using
        (VOA.DeligneAudit.UnivG.wordOp_mem_cycSubG ρ w [])
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      fin_cases i
      · simpa [radicalWord, a2RadicalOp] using
          VOA.DeligneAudit.UnivG.cycSubG_inv ρ w 3 s ih
      · simpa [radicalWord, a2RadicalOp] using
          VOA.DeligneAudit.UnivG.cycSubG_inv ρ w 5 s ih

private theorem keyLayer_le_cyc (k : A2RadicalKey) :
    a2KeyLayer ρ w k ≤ VOA.DeligneAudit.UnivG.cycSubG ρ w := by
  rw [a2KeyLayer, Submodule.span_le]
  rintro z ⟨l, _, _, _, _, rfl⟩
  exact radicalWord_mem_cyc ρ w l

private theorem radical_list_mem_key : ∀ (l : List (Fin 8 × ℕ)),
    l.Forall (fun x => a2Radical x.1) →
      ∃ k, wordOp ρ l w ∈ a2KeyLayer ρ w k := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨a2WordKey [], by
        simpa [wordOp, radicalWord] using
          (radicalWord_mem_own_key ρ w ([] : List (Fin 2 × ℕ)))⟩
  | cons x l ih =>
      intro hl
      rcases x with ⟨a, r⟩
      simp only [List.forall_cons] at hl
      obtain ⟨k, hk⟩ := ih hl.2
      rcases hl.1 with rfl | rfl
      · exact ⟨a2KeyInsert 0 r k, by
          simpa [wordOp, a2RadicalOp] using
            a2RadicalOp_maps_key ρ w 0 r k hk⟩
      · exact ⟨a2KeyInsert 1 r k, by
          simpa [wordOp, a2RadicalOp] using
            a2RadicalOp_maps_key ρ w 1 r k hk⟩

private theorem radical_list_mem_all (l : List (Fin 8 × ℕ))
    (hl : l.Forall (fun x => a2Radical x.1)) :
    wordOp ρ l w ∈ a2AllKeySpan ρ w := by
  obtain ⟨k, hk⟩ := radical_list_mem_key ρ w l hl
  exact (le_iSup (fun k => a2KeyLayer ρ w k) k) hk

/-- PBW generation expressed using the sum of all concrete key layers. -/
theorem a2_cycSubG_eq_leviClosure_allKeys (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) :
    VOA.DeligneAudit.UnivG.cycSubG ρ w =
      a2LeviClosure ρ (a2AllKeySpan ρ w) := by
  have hkeys : a2AllKeySpan ρ w ≤
      VOA.DeligneAudit.UnivG.cycSubG ρ w := by
    rw [a2AllKeySpan, iSup_le_iff]
    intro k
    exact keyLayer_le_cyc ρ w k
  have hclosure : a2LeviClosure ρ (a2AllKeySpan ρ w) ≤
      VOA.DeligneAudit.UnivG.cycSubG ρ w :=
    a2LeviClosure_le_of_inv ρ _ _ hkeys
      (fun a r _ => VOA.DeligneAudit.UnivG.cycSubG_inv ρ w a r)
  refine le_antisymm ?_ hclosure
  rw [a2_cycSubG_eq_leviSpan ρ w h, a2LeviSpan, Submodule.span_le]
  rintro z ⟨l, r, hl, hr, rfl⟩
  have hr' : wordOp ρ r w ∈ a2LeviClosure ρ (a2AllKeySpan ρ w) :=
    a2LeviClosure_contains ρ _ (radical_list_mem_all ρ w r hr)
  clear hr
  induction l with
  | nil => simpa [wordOp] using hr'
  | cons x l ih =>
      rcases x with ⟨a, s⟩
      simp only [List.forall_cons] at hl
      simpa [wordOp] using
        (a2LeviClosure_inv ρ _ a s hl.1 (ih hl.2))

/-- The explicit finite key box contains every key that contributes to the
Levi generation, conditional on sharp compound-root nilpotence. -/
theorem a2_cycSubG_eq_leviClosure_keyBox (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) :
    VOA.DeligneAudit.UnivG.cycSubG ρ w =
      a2LeviClosure ρ
        (⨆ k ∈ a2KeyBox p q, a2KeyLayer ρ w k) := by
  have hspan : a2AllKeySpan ρ w =
      ⨆ k ∈ a2KeyBox p q, a2KeyLayer ρ w k := by
    apply le_antisymm
    · rw [a2AllKeySpan, iSup_le_iff]
      intro k
      by_cases hk : a2KeyLayer ρ w k = ⊥
      · simp [hk]
      · exact le_iSup_of_le k
          (le_iSup_of_le
            (a2KeyBox_contains_nonzero_unconditional ρ w p q h k hk) le_rfl)
    · rw [iSup_le_iff]
      intro k
      rw [iSup_le_iff]
      intro _
      exact le_iSup (fun j => a2KeyLayer ρ w j) k
  rw [← hspan]
  exact a2_cycSubG_eq_leviClosure_allKeys ρ w p q h

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_cycSubG_eq_leviClosure_allKeys
#print axioms VOA.DeligneAudit.A3Sector.a2_cycSubG_eq_leviClosure_keyBox
