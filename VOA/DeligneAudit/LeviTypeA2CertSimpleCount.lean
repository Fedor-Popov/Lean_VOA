import VOA.DeligneAudit.LeviTypeA2CertSimpleLength

/-! First-colour radical count cutoff in mixed monomials. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
    VOA.AffineSl3.bracketTable V) (w : V)

def firstModes (l : List (Fin 2 × ℕ)) : List ℕ :=
  (l.filter fun x => x.1 = 0).map Prod.snd

def secondModes (l : List (Fin 2 × ℕ)) : List ℕ :=
  (l.filter fun x => x.1 = 1).map Prod.snd

private theorem firstModes_length (l : List (Fin 2 × ℕ)) :
    (firstModes l).length = l.countP (fun x => x.1 = 0) := by
  simp [firstModes, List.countP_eq_length_filter]

private theorem commute_prod (i : Fin 2) (s : ℕ) (l : List ℕ) :
    a2RadicalOp ρ i s * (l.map fun t => a2RadicalOp ρ 0 t).prod =
      (l.map fun t => a2RadicalOp ρ 0 t).prod * a2RadicalOp ρ i s := by
  induction l with
  | nil => simp
  | cons t l ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        _ = (a2RadicalOp ρ i s * a2RadicalOp ρ 0 t) *
              (l.map fun u => a2RadicalOp ρ 0 u).prod := by rw [mul_assoc]
        _ = (a2RadicalOp ρ 0 t * a2RadicalOp ρ i s) *
              (l.map fun u => a2RadicalOp ρ 0 u).prod := by
                rw [a2RadicalOp_comm]
        _ = a2RadicalOp ρ 0 t *
              (a2RadicalOp ρ i s * (l.map fun u => a2RadicalOp ρ 0 u).prod) := by
                rw [mul_assoc]
        _ = _ := by rw [ih, mul_assoc]

theorem radicalWord_split (l : List (Fin 2 × ℕ)) :
    radicalWord (a2RadicalOp ρ) l =
      ((firstModes l).map fun s => a2RadicalOp ρ 0 s).prod *
        ((secondModes l).map fun s => a2RadicalOp ρ 1 s).prod := by
  induction l with
  | nil => simp [radicalWord, firstModes, secondModes]
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      fin_cases i
      · calc
          radicalWord (a2RadicalOp ρ) ((0, s) :: l) =
              a2RadicalOp ρ 0 s * radicalWord (a2RadicalOp ρ) l := rfl
          _ = a2RadicalOp ρ 0 s *
              (((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod *
                ((secondModes l).map fun t => a2RadicalOp ρ 1 t).prod) := by rw [ih]
          _ = _ := by simp [firstModes, secondModes, mul_assoc]
      · calc
          radicalWord (a2RadicalOp ρ) ((1, s) :: l) =
              a2RadicalOp ρ 1 s * radicalWord (a2RadicalOp ρ) l := rfl
          _ = a2RadicalOp ρ 1 s *
              (((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod *
                ((secondModes l).map fun t => a2RadicalOp ρ 1 t).prod) := by rw [ih]
          _ = _ := by
            change a2RadicalOp ρ 1 s *
              (((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod *
                ((secondModes l).map fun t => a2RadicalOp ρ 1 t).prod) =
              ((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod *
                (a2RadicalOp ρ 1 s *
                  ((secondModes l).map fun t => a2RadicalOp ρ 1 t).prod)
            rw [← mul_assoc, commute_prod, mul_assoc]

/-- A first-colour count above `p` kills a mixed radical word. -/
theorem a2_radicalWord_zero_of_first_count (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (l : List (Fin 2 × ℕ))
    (hl : p < l.countP (fun x => x.1 = 0)) :
    radicalWord (a2RadicalOp ρ) l • w = 0 := by
  have hfirst :
      ((firstModes l).map fun s => a2RadicalOp ρ 0 s).prod w = 0 := by
    have hlen : p < (firstModes l).length := by
      rw [firstModes_length]
      exact hl
    simpa [a2RadicalOp] using
      a2_simple_word_length_zero ρ w p q h (firstModes l) hlen
  rw [radicalWord_split ρ l]
  have hcomm :
      ((firstModes l).map fun s => a2RadicalOp ρ 0 s).prod *
          ((secondModes l).map fun s => a2RadicalOp ρ 1 s).prod =
        ((secondModes l).map fun s => a2RadicalOp ρ 1 s).prod *
          ((firstModes l).map fun s => a2RadicalOp ρ 0 s).prod := by
    induction secondModes l with
    | nil => simp
    | cons s rest ih =>
        simp only [List.map_cons, List.prod_cons]
        calc
          _ = ((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod *
                a2RadicalOp ρ 1 s *
                (rest.map fun t => a2RadicalOp ρ 1 t).prod := by rw [mul_assoc]
          _ = a2RadicalOp ρ 1 s *
                ((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod *
                (rest.map fun t => a2RadicalOp ρ 1 t).prod := by
                  rw [← commute_prod]
          _ = a2RadicalOp ρ 1 s *
                (rest.map fun t => a2RadicalOp ρ 1 t).prod *
                ((firstModes l).map fun t => a2RadicalOp ρ 0 t).prod := by
                  rw [mul_assoc, ih, ← mul_assoc]
  change ((firstModes l).map fun s => a2RadicalOp ρ 0 s).prod • w = 0 at hfirst
  rw [hcomm, mul_smul, hfirst, smul_zero]

/-- Every key with more than `p` first-colour letters has zero layer. -/
theorem a2KeyLayer_eq_bot_of_first_count (p q : ℕ) (k : A2RadicalKey)
    (h : A2LocalWeylRel ρ w p q) (hk : p < k.d₁) :
    a2KeyLayer ρ w k = ⊥ := by
  rw [a2KeyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, hd₁, _, _, _, rfl⟩ := hz
  rw [a2_radicalWord_zero_of_first_count ρ w p q h l (by simpa [hd₁] using hk)]
  exact Submodule.zero_mem _

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_radicalWord_zero_of_first_count
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLayer_eq_bot_of_first_count
#print axioms VOA.DeligneAudit.A3Sector.radicalWord_split
