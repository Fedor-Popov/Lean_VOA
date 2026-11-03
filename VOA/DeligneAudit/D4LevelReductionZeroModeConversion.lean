import VOA.DeligneAudit.D4LevelReductionBottomOrbit

/-! Middle raising generates every zero-mode radical count pattern from the bottom vector. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The three-colour radical word with every current mode zero. -/
def threeColourZeroWord (a j c : ℕ) : List (Fin 6 × ℕ) :=
  List.replicate a (1, 0) ++ List.replicate j (4, 0) ++ List.replicate c (5, 0)

/-- The vector of a zero-mode three-colour radical word. -/
def threeColourZeroVector (a j c : ℕ) : V :=
  radicalWord ρ w (threeColourZeroWord a j c)

/-- A middle raising current commutes past an adjoint radical letter on radical words. -/
theorem middleRaising_adjoint_word (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (r s : ℕ)
    (l : List (Fin 6 × ℕ)) :
    ρ.op (leviColour (A3Sector.simpleE 1)) r (radicalWord ρ w ((1, s) :: l)) =
      ρ.op (radicalColour 1) s
        (ρ.op (leviColour (A3Sector.simpleE 1)) r (radicalWord ρ w l)) := by
  have hc := simple_raise_comm ρ 1 1 r s (radicalWord ρ w l)
  have hz := radicalWord_zero_of_E ρ w m h ((0, r + s) :: l) (by simp)
  simp only [raiseAction, Int.cast_one, one_smul] at hc
  change ρ.op (radicalColour 0) (r + s) (radicalWord ρ w l) = 0 at hz
  rw [hz] at hc
  exact sub_eq_zero.mp hc

/-- A zero middle raising current converts one central letter, with its exact multiplicity. -/
theorem middleRaising_threeColourZero (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a j c : ℕ) :
    ρ.op (leviColour (A3Sector.simpleE 1)) 0 (threeColourZeroVector ρ w a j (c + 1)) =
      (c + 1 : ℂ) • threeColourZeroVector ρ w a (j + 1) c := by
  have hcentral (n : ℕ) :
      ρ.op (leviColour (A3Sector.simpleE 1)) 0
        (radicalWord ρ w (List.replicate n (5, 0))) =
      (n : ℂ) • radicalWord ρ w ((4, 0) :: List.replicate (n - 1) (5, 0)) := by
    induction n with
    | zero =>
        have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
          simpa [ravFam] using h
        simpa [radicalWord, wordOp] using
          (rs_raising hs (show D4sector.raising (leviColour (A3Sector.simpleE 1)) by
            change 4 ≤ (leviColour (A3Sector.simpleE 1)).val ∧
              (leviColour (A3Sector.simpleE 1)).val < 16
            decide) 0)
    | succ n ih =>
        have hc := simple_raise_comm ρ 1 5 0 0
          (radicalWord ρ w (List.replicate n (5, 0)))
        simp only [raiseAction, Int.cast_one, one_smul, zero_add] at hc
        change ρ.op (leviColour (A3Sector.simpleE 1)) 0
          (ρ.op (radicalColour 5) 0 (radicalWord ρ w (List.replicate n (5, 0)))) = _
        rw [sub_eq_iff_eq_add.mp hc, ih, map_smul]
        cases n with
        | zero => simp [radicalWord, wordOp]
        | succ n =>
            simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul,
              Nat.add_sub_cancel, List.replicate_succ, radicalWord, List.map_cons, wordOp]
            rw [radical_ops_comm ρ 5 4 0 0]
            abel
  have hy (j c : ℕ) :
      ρ.op (leviColour (A3Sector.simpleE 1)) 0 (threeColourZeroVector ρ w 0 j (c + 1)) =
        (c + 1 : ℂ) • threeColourZeroVector ρ w 0 (j + 1) c := by
    induction j with
    | zero => simpa [threeColourZeroVector, threeColourZeroWord] using hcentral (c + 1)
    | succ j ih =>
        have hc := simple_raise_comm ρ 1 4 0 0
          (threeColourZeroVector ρ w 0 j (c + 1))
        simp only [raiseAction] at hc
        change ρ.op (leviColour (A3Sector.simpleE 1)) 0
          (ρ.op (radicalColour 4) 0 (threeColourZeroVector ρ w 0 j (c + 1))) = _
        rw [sub_eq_zero.mp hc, ih, map_smul]
        rfl
  induction a with
  | zero => exact hy j c
  | succ a ih =>
      change ρ.op (leviColour (A3Sector.simpleE 1)) 0
        (radicalWord ρ w ((1, 0) :: threeColourZeroWord a j (c + 1))) = _
      rw [middleRaising_adjoint_word ρ w m h]
      change ρ.op (radicalColour 1) 0
        (ρ.op (leviColour (A3Sector.simpleE 1)) 0
          (threeColourZeroVector ρ w a j (c + 1))) = _
      rw [ih, map_smul]
      rfl

/-- Every zero-mode three-colour word is in the bottom reductive orbit. -/
theorem threeColourZero_mem_bottomOrbit (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a j c : ℕ) :
    threeColourZeroVector ρ w a j c ∈ keyVectorOrbit ρ (bottomVector ρ w a (j + c)) := by
  induction j generalizing c with
  | zero =>
      simpa [threeColourZeroVector, threeColourZeroWord, bottomVector, bottomRadicalWord] using
        keyVectorOrbit_mem ρ (bottomVector ρ w a c) [] (by simp)
  | succ j ih =>
      have hv := keyVectorOrbit_inv ρ (bottomVector ρ w a (j + (c + 1)))
        (leviColour (A3Sector.simpleE 1)) 0 (leviColour_isLevi _) (ih (c + 1))
      rw [middleRaising_threeColourZero ρ w m h a j c] at hv
      have hn : (c + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
      have hh := (Submodule.smul_mem_iff _ hn).mp hv
      simpa only [Nat.succ_add, Nat.add_succ] using hh

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaising_adjoint_word
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaising_threeColourZero
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourZero_mem_bottomOrbit
