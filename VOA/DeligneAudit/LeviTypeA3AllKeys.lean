import VOA.DeligneAudit.LeviTypeA3ExtraCartanClosure

/-! The sum of all radical key layers generates the cyclic module under sl₃. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3AllKeySpan : Submodule ℂ V :=
  ⨆ k : A3RadicalKey, a3KeyLayer ρ w k

private theorem radicalWord_mem_cyc (l : List (Fin 3 × ℕ)) :
    radicalWord (radicalOp ρ) l • w ∈
      VOA.DeligneAudit.UnivG.cycSubG ρ w := by
  induction l with
  | nil =>
      simpa [radicalWord] using
        (VOA.DeligneAudit.UnivG.wordOp_mem_cycSubG ρ w [])
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      fin_cases i
      · simpa [radicalWord, radicalOp, F] using
          VOA.DeligneAudit.UnivG.cycSubG_inv ρ w 6 s ih
      · simpa [radicalWord, radicalOp, F] using
          VOA.DeligneAudit.UnivG.cycSubG_inv ρ w 7 s ih
      · simpa [radicalWord, radicalOp, F] using
          VOA.DeligneAudit.UnivG.cycSubG_inv ρ w 8 s ih

private theorem keyLayer_le_cyc (k : A3RadicalKey) :
    a3KeyLayer ρ w k ≤ VOA.DeligneAudit.UnivG.cycSubG ρ w := by
  rw [a3KeyLayer, Submodule.span_le]
  rintro z ⟨l, _, _, _, _, _, rfl⟩
  exact radicalWord_mem_cyc ρ w l

theorem a3AllKeySpan_extra_inv (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (r : ℕ) :
    a3AllKeySpan ρ w ≤ (a3AllKeySpan ρ w).comap (ρ.op 12 r) := by
  rw [a3AllKeySpan, iSup_le_iff]
  intro k v hv
  change ρ.op 12 r v ∈ a3AllKeySpan ρ w
  by_cases hr : r = 0
  · subst r
    rw [a3_extra_cartan_weight_key ρ w a b c h k hv]
    exact (a3AllKeySpan ρ w).smul_mem _
      ((le_iSup (fun j => a3KeyLayer ρ w j) k) hv)
  · exact (le_iSup (fun j => a3KeyLayer ρ w j) (a3KeyShift r k))
      (a3_extra_cartan_pos_maps_key ρ w a b c h r (by omega) k hv)

private theorem radical_list_mem_key : ∀ (l : List (Fin 15 × ℕ)),
    l.Forall (fun x => a3Radical x.1) →
      ∃ k, wordOp ρ l w ∈ a3KeyLayer ρ w k := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨a3WordKey [], by
        simpa [wordOp, radicalWord] using
          (a3_radicalWord_mem_own_key ρ w ([] : List (Fin 3 × ℕ)))⟩
  | cons x l ih =>
      intro hl
      rcases x with ⟨col, r⟩
      simp only [List.forall_cons] at hl
      obtain ⟨k, hk⟩ := ih hl.2
      rcases hl.1 with hcol | hcol | hcol
      · subst col
        exact ⟨a3KeyInsert 0 r k, by
          simpa [wordOp, radicalOp, F] using
            a3RadicalOp_maps_key ρ w 0 r k hk⟩
      · subst col
        exact ⟨a3KeyInsert 1 r k, by
          simpa [wordOp, radicalOp, F] using
            a3RadicalOp_maps_key ρ w 1 r k hk⟩
      · subst col
        exact ⟨a3KeyInsert 2 r k, by
          simpa [wordOp, radicalOp, F] using
            a3RadicalOp_maps_key ρ w 2 r k hk⟩

private theorem levi_colour_range (col : Fin 15)
    (hc : a3Levi col) (hne : col ≠ 12) :
    ∃ i : Fin 8, a3LeviColour i = col := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨4, rfl⟩
  · exact False.elim (hne rfl)
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

theorem a3_cycSubG_eq_leviClosure_allKeys (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    VOA.DeligneAudit.UnivG.cycSubG ρ w =
      a3LeviClosure ρ (a3AllKeySpan ρ w) := by
  let C := a3LeviClosure ρ (a3AllKeySpan ρ w)
  have hkeys : a3AllKeySpan ρ w ≤
      VOA.DeligneAudit.UnivG.cycSubG ρ w := by
    rw [a3AllKeySpan, iSup_le_iff]
    intro k
    exact keyLayer_le_cyc ρ w k
  have hC : C ≤ VOA.DeligneAudit.UnivG.cycSubG ρ w :=
    a3LeviClosure_le_of_inv ρ _ _ hkeys
      (fun i r x hx => VOA.DeligneAudit.UnivG.cycSubG_inv ρ w
        (a3LeviColour i) r hx)
  refine le_antisymm ?_ hC
  rw [a3_cycSubG_eq_leviSpan ρ w _ h, a3LeviSpan, Submodule.span_le]
  rintro z ⟨l, r, hl, hr, rfl⟩
  have hr' : wordOp ρ r w ∈ C := by
    obtain ⟨k, hk⟩ := radical_list_mem_key ρ w r hr
    exact a3LeviClosure_contains ρ _
      ((le_iSup (fun j => a3KeyLayer ρ w j) k) hk)
  clear hr
  induction l with
  | nil => simpa [wordOp] using hr'
  | cons x l ih =>
      rcases x with ⟨col, s⟩
      simp only [List.forall_cons] at hl
      by_cases hc : col = 12
      · subst col
        simpa [wordOp, C] using
          a3LeviClosure_extra_inv ρ _
            (fun t => a3AllKeySpan_extra_inv ρ w a b c h t) s (ih hl.2)
      · obtain ⟨i, rfl⟩ := levi_colour_range col hl.1 hc
        simpa [wordOp, C] using a3LeviClosure_inv ρ _ i s (ih hl.2)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3AllKeySpan_extra_inv
#print axioms VOA.DeligneAudit.A3Sector.a3_cycSubG_eq_leviClosure_allKeys
