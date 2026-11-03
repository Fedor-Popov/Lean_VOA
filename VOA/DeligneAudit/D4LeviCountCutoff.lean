import VOA.DeligneAudit.D4LeviRootBox

/-! A radical word has the sharp count cutoff for each of its six colours. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

def colourModes (j : Fin 6) (l : List (Fin 6 × ℕ)) : List ℕ :=
  (l.filter fun p => p.1 = j).map Prod.snd

theorem colourModes_length (j : Fin 6) (l : List (Fin 6 × ℕ)) :
    (colourModes j l).length = l.countP (fun p => p.1 = j) := by
  simp [colourModes, List.countP_eq_length_filter]

noncomputable def radicalEndWord (l : List (Fin 6 × ℕ)) : Module.End ℂ V :=
  (l.map fun p => ρ.op (radicalColour p.1) p.2).prod

theorem radicalEndWord_apply (l : List (Fin 6 × ℕ)) :
    radicalEndWord ρ l w = radicalWord ρ w l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      change ρ.op (radicalColour j) s (radicalEndWord ρ l w) =
        ρ.op (radicalColour j) s (radicalWord ρ w l)
      rw [ih]

private theorem radicalEnd_comm (i j : Fin 6) (r s : ℕ) :
    ρ.op (radicalColour i) r * ρ.op (radicalColour j) s =
      ρ.op (radicalColour j) s * ρ.op (radicalColour i) r := by
  ext v
  exact radical_ops_comm ρ i j r s v

private theorem radicalEndWord_comm (j : Fin 6) (s : ℕ)
    (l : List (Fin 6 × ℕ)) :
    ρ.op (radicalColour j) s * radicalEndWord ρ l =
      radicalEndWord ρ l * ρ.op (radicalColour j) s := by
  induction l with
  | nil => simp [radicalEndWord]
  | cons p l ih =>
      rcases p with ⟨i, r⟩
      change ρ.op (radicalColour j) s *
          (ρ.op (radicalColour i) r * radicalEndWord ρ l) =
        (ρ.op (radicalColour i) r * radicalEndWord ρ l) *
          ρ.op (radicalColour j) s
      rw [← mul_assoc, radicalEnd_comm ρ j i s r, mul_assoc, ih,
        ← mul_assoc]

theorem radicalEndWord_split_colour (j : Fin 6)
    (l : List (Fin 6 × ℕ)) :
    radicalEndWord ρ l =
      radicalEndWord ρ (l.filter fun p => p.1 ≠ j) *
        ((colourModes j l).map fun s => ρ.op (radicalColour j) s).prod := by
  induction l with
  | nil => simp [radicalEndWord, colourModes]
  | cons p l ih =>
      rcases p with ⟨i, s⟩
      by_cases hi : i = j
      · subst i
        simp only [radicalEndWord, List.map_cons, List.prod_cons] at *
        simp only [List.filter_cons, colourModes] at *
        simp [ih]
        have hc := radicalEndWord_comm ρ j s
          (l.filter fun p => p.1 ≠ j)
        have hc' : ρ.op (radicalColour j) s *
            (List.map (fun p => ρ.op (radicalColour p.1) p.2)
              (l.filter fun p => !decide (p.1 = j))).prod =
            (List.map (fun p => ρ.op (radicalColour p.1) p.2)
              (l.filter fun p => !decide (p.1 = j))).prod *
              ρ.op (radicalColour j) s := by
          simpa only [radicalEndWord, ne_eq, decide_not] using hc
        rw [← mul_assoc, hc', mul_assoc]
      · simp only [radicalEndWord, List.map_cons, List.prod_cons] at *
        simp only [List.filter_cons, colourModes] at *
        simp [hi, ih, mul_assoc]

theorem radicalWord_zero_of_count
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) (l : List (Fin 6 × ℕ))
    (hj : rootWeight m j < l.countP (fun p => p.1 = j)) :
    radicalWord ρ w l = 0 := by
  have hlen : rootWeight m j < (colourModes j l).length := by
    rw [colourModes_length]
    exact hj
  have hzero : ((colourModes j l).map fun s =>
      ρ.op (radicalColour j) s).prod w = 0 :=
    root_word_length_zero ρ w m h j (colourModes j l) hlen
  rw [← radicalEndWord_apply ρ w l,
    radicalEndWord_split_colour ρ j l, Module.End.mul_apply, hzero,
    map_zero]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.colourModes_length
#print axioms VOA.DeligneAudit.D4Levi.radicalEndWord_apply
#print axioms VOA.DeligneAudit.D4Levi.radicalEndWord_split_colour
#print axioms VOA.DeligneAudit.D4Levi.radicalWord_zero_of_count
