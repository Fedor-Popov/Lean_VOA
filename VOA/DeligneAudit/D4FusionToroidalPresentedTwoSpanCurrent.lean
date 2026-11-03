import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedFinal

/-! The two positive spans are cyclic for the truncated current action. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl

noncomputable section

def twoGen (s : ℕ) : PTE 2 :=
  (ρPTE 2).op D4sector.c₀ 1 s (pTE 2)

def twoZeroLetters' (l : List (TLtr 28)) : List (Ltr 28) :=
  l.map fun x => (x.1, x.2.2)

def twoToroidalLetters (l : List (Ltr 28)) : List (TLtr 28) :=
  l.map fun x => (x.1, 0, x.2)

theorem two_current_word (s : ℕ) (l : List (TLtr 28))
    (hl : twoUDeg l = 0) :
    wordOpT (ρPTE 2) l (twoGen s) =
      wordOp twoCurrent (twoZeroLetters' l) (twoGen s) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hx : x.2.1 = 0 := by
        simp only [twoUDeg] at hl
        omega
      have ht : twoUDeg l = 0 := by
        simp only [twoUDeg] at hl
        omega
      simp only [wordOpT, wordOp, twoZeroLetters', List.map_cons]
      rw [ih ht, hx]
      by_cases hr : x.2.2 < 2
      · have hr' : x.2.2 ≤ 1 := by omega
        simp [twoCurrent, hr', twoZeroLetters']
      · have hr' : ¬ x.2.2 ≤ 1 := by omega
        rw [(ρPTE 2).high_zero x.1 0 x.2.2 (by omega)]
        simp [twoCurrent, hr', twoZeroLetters']

theorem two_toroidal_letters_deg (l : List (Ltr 28)) :
    twoUDeg (twoToroidalLetters l) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [twoToroidalLetters, twoUDeg] using ih

theorem two_current_word_reverse (s : ℕ) (l : List (Ltr 28)) :
    wordOp twoCurrent l (twoGen s) =
      wordOpT (ρPTE 2) (twoToroidalLetters l) (twoGen s) := by
  simpa [twoZeroLetters', twoToroidalLetters, List.map_map,
    Function.comp_def] using
    (two_current_word s (twoToroidalLetters l) (two_toroidal_letters_deg l)).symm

theorem twoM_eq_cycSubG (s : ℕ) :
    twoM s = cycSubG twoCurrent (twoGen s) := by
  apply le_antisymm
  · rw [twoM, Submodule.span_le]
    rintro v ⟨l, hl, rfl⟩
    change wordOpT (ρPTE 2) l (twoGen s) ∈ cycSubG twoCurrent (twoGen s)
    rw [two_current_word s l hl]
    exact wordOp_mem_cycSubG twoCurrent (twoGen s) _
  · rw [cycSubG, Submodule.span_le]
    rintro v ⟨l, rfl⟩
    change wordOp twoCurrent l (twoGen s) ∈ twoM s
    rw [two_current_word_reverse]
    exact twoM_word s _ (two_toroidal_letters_deg l)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_current_word
#print axioms VOA.DeligneAudit.Toroidal.two_current_word_reverse
#print axioms VOA.DeligneAudit.Toroidal.twoM_eq_cycSubG
