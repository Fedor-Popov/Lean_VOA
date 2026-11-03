import VOA.DeligneAudit.D4LeviKSPowerSums

/-! The first explicit higher source for the f₃ PAIR transfer. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

def pairOneTargetKey (xs zs : List ℕ) (r : ℕ) : RadicalKey :=
  ⟨0, xs.length, 0, 0, 1, zs.length, xs.sum + zs.sum + r⟩

def pairOneXWords (xs : List ℕ) : List (Fin 6 × ℕ) :=
  xs.map fun s => (1, s)

def pairOneUTail (zs : List ℕ) : List (Fin 6 × ℕ) :=
  (2, 0) :: zs.map fun s => (5, s)

private theorem countP_const_colour (j a : Fin 6) (ls : List ℕ) :
    (ls.map fun s => (j, s)).countP (fun p => p.1 = a) =
      if j = a then ls.length else 0 := by
  by_cases h : j = a
  · subst a
    simp [List.countP_map, Function.comp_def]
  · simp [List.countP_map, Function.comp_def, h]

/-- The X/U source has Levi height two above the X/Y target key. -/
theorem pairOne_source_key_higher (xs zs : List ℕ) (r : ℕ) :
    keyLess m (pairOneTargetKey xs zs r)
      (wordKey (pairOneXWords xs ++ pairOneUTail zs)) := by
  left
  simp only [pairOneTargetKey, pairOneXWords, pairOneUTail,
    keyHeight, wordKey, List.countP_append, List.countP_cons,
    countP_const_colour]
  norm_num

/-- One f₃ mode transfers across an X word modulo the higher-key orbit,
    without a separate source hypothesis. -/
theorem pairOne_transfer_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs zs : List ℕ) (r : ℕ) :
    fThreeDerivative ρ r (pairOneXWords xs)
        (radicalWord ρ w (pairOneUTail zs)) +
      wordOp ρ ((pairOneXWords xs).map fun p => (radicalColour p.1, p.2))
        (fThreeDerivative ρ r (pairOneUTail zs) w) ∈
          higherOrbit ρ w m (pairOneTargetKey xs zs r) := by
  exact fThree_antipode_one_higher ρ w m h _ r
    (pairOneXWords xs) (pairOneUTail zs)
    (pairOne_source_key_higher m xs zs r)

private theorem fThree_z_tail_zero (r : ℕ) (zs : List ℕ) :
    fThreeDerivative ρ r (zs.map fun s => (5, s)) w = 0 := by
  induction zs with
  | nil => rfl
  | cons s zs ih =>
      simp [fThreeDerivative, fThreeLetter, ih]

/-- The f₃ derivative of a single U followed by Z letters is minus a Y
    current followed by the same Z letters. -/
theorem pairOne_tail_derivative (r : ℕ) (zs : List ℕ) :
    fThreeDerivative ρ r (pairOneUTail zs) w =
      -yOp ρ r (radicalWord ρ w (zs.map fun s => (5, s))) := by
  simp [pairOneUTail, fThreeDerivative, fThreeLetter,
    fThree_z_tail_zero, yOp, radicalColour, radicalWord,
    List.map_map, Function.comp_def]
  rfl

/-- The concrete first PAIR relation: an X-word followed by Y and Z is
    congruent to the f₃ derivative of the X-word followed by U and Z. -/
theorem pairOne_xy_transfer_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs zs : List ℕ) (r : ℕ) :
    wordOp ρ ((pairOneXWords xs).map fun p => (radicalColour p.1, p.2))
        (yOp ρ r (radicalWord ρ w (zs.map fun s => (5, s)))) -
      fThreeDerivative ρ r (pairOneXWords xs)
        (radicalWord ρ w (pairOneUTail zs)) ∈
          higherOrbit ρ w m (pairOneTargetKey xs zs r) := by
  have hh := pairOne_transfer_higher ρ w m h xs zs r
  rw [pairOne_tail_derivative ρ w r zs] at hh
  have hneg (l : List (Fin 28 × ℕ)) (v : V) :
      wordOp ρ l (-v) = -wordOp ρ l v := by
    simpa using wordOp_smul ρ l (-1 : ℂ) v
  rw [hneg] at hh
  convert (higherOrbit ρ w m (pairOneTargetKey xs zs r)).neg_mem hh using 1
  abel

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairOne_source_key_higher
#print axioms VOA.DeligneAudit.D4Levi.pairOne_transfer_higher
#print axioms VOA.DeligneAudit.D4Levi.pairOne_tail_derivative
#print axioms VOA.DeligneAudit.D4Levi.pairOne_xy_transfer_higher
