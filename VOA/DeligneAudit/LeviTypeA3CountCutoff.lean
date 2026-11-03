import VOA.DeligneAudit.LeviTypeA3HighestLength

/-! Radical colour-count cutoffs in mixed mode words. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

def a3ColourModes (i : Fin 3) (l : List (Fin 3 × ℕ)) : List ℕ :=
  (l.filter fun x => x.1 = i).map Prod.snd

theorem a3ColourModes_length (i : Fin 3) (l : List (Fin 3 × ℕ)) :
    (a3ColourModes i l).length = l.countP (fun x => x.1 = i) := by
  simp [a3ColourModes, List.countP_eq_length_filter]

private theorem radicalWord_comm (i : Fin 3) (s : ℕ)
    (l : List (Fin 3 × ℕ)) :
    radicalOp ρ i s * radicalWord (radicalOp ρ) l =
      radicalWord (radicalOp ρ) l * radicalOp ρ i s := by
  induction l with
  | nil => simp [radicalWord]
  | cons x l ih =>
      rcases x with ⟨j, t⟩
      change radicalOp ρ i s *
        (radicalOp ρ j t * radicalWord (radicalOp ρ) l) =
        (radicalOp ρ j t * radicalWord (radicalOp ρ) l) * radicalOp ρ i s
      calc
        _ = (radicalOp ρ i s * radicalOp ρ j t) *
              radicalWord (radicalOp ρ) l := by rw [mul_assoc]
        _ = (radicalOp ρ j t * radicalOp ρ i s) *
              radicalWord (radicalOp ρ) l := by rw [radicalOp_comm]
        _ = radicalOp ρ j t *
              (radicalOp ρ i s * radicalWord (radicalOp ρ) l) := by rw [mul_assoc]
        _ = _ := by rw [ih, mul_assoc]

/-- Every occurrence of one colour can be moved to the right of the others. -/
theorem a3_radicalWord_split_colour (i : Fin 3)
    (l : List (Fin 3 × ℕ)) :
    radicalWord (radicalOp ρ) l =
      radicalWord (radicalOp ρ) (l.filter fun x => x.1 ≠ i) *
        ((a3ColourModes i l).map fun s => radicalOp ρ i s).prod := by
  induction l with
  | nil => simp [radicalWord, a3ColourModes]
  | cons x l ih =>
      rcases x with ⟨j, s⟩
      by_cases hj : j = i
      · subst j
        simp only [radicalWord, List.map_cons, List.prod_cons] at *
        simp only [List.filter_cons, a3ColourModes, beq_self_eq_true,
          ↓reduceIte] at *
        simp [ih]
        have hc := radicalWord_comm ρ i s
          (l.filter fun x => x.1 ≠ i)
        have hc' : radicalOp ρ i s *
            (List.map (fun p => radicalOp ρ p.1 p.2)
              (l.filter fun x => !decide (x.1 = i))).prod =
            (List.map (fun p => radicalOp ρ p.1 p.2)
              (l.filter fun x => !decide (x.1 = i))).prod *
              radicalOp ρ i s := by
          simpa only [radicalWord, ne_eq, decide_not] using hc
        rw [← mul_assoc, hc', mul_assoc]
      · simp only [radicalWord, List.map_cons, List.prod_cons] at *
        simp only [List.filter_cons, a3ColourModes] at *
        simp [hj, ih, mul_assoc]

/-- A mixed radical word vanishes when any one colour exceeds its root weight. -/
theorem a3_radicalWord_zero_of_count (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (l : List (Fin 3 × ℕ))
    (hi : (if i = 0 then a else if i = 1 then a + b else a + b + c) <
      l.countP (fun x => x.1 = i)) :
    radicalWord (radicalOp ρ) l • w = 0 := by
  have hlen : (if i = 0 then a else if i = 1 then a + b else a + b + c) <
      (a3ColourModes i l).length := by
    rw [a3ColourModes_length]
    exact hi
  have hzero :
      ((a3ColourModes i l).map fun s => radicalOp ρ i s).prod w = 0 := by
    fin_cases i
    · simpa [radicalOp, F, simpleF, weightABC] using
        a3_simple_word_length_zero ρ w a b c h 0 (a3ColourModes 0 l)
          (by simpa using hlen)
    · simpa [radicalOp, F] using
        a3_compound_word_length_zero ρ w a b c h (a3ColourModes 1 l)
          (by simpa using hlen)
    · simpa [radicalOp, F] using
        a3_highest_word_length_zero ρ w a b c h (a3ColourModes 2 l)
          (by simpa using hlen)
  rw [a3_radicalWord_split_colour ρ i l, mul_smul]
  change radicalWord (radicalOp ρ) (l.filter fun x => x.1 ≠ i) •
    ((a3ColourModes i l).map fun s => radicalOp ρ i s).prod w = 0
  rw [hzero, smul_zero]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_radicalWord_split_colour
#print axioms VOA.DeligneAudit.A3Sector.a3_radicalWord_zero_of_count
