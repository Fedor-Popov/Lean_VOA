import VOA.DeligneAudit.D4LeviKSPairRestriction

/-! The one-contraction Rz presentation as a fixed-shape mode polynomial. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_single_topSum (ρ : CurrentModule D4sector.f V) (s : ℕ) :
    topSum (yOp ρ) (zOp ρ) 1 s [0] = zOp ρ s := by
  simp [topSum, choices, aWord, bWord, bTail]

/-- The basic Rz contraction is the evaluation of one Z variable. -/
theorem rz_single_presentation
    (ρ : CurrentModule D4sector.f V) (w : V) (s : ℕ) :
    xyzEvaluation ρ w (fun _ : Fin 1 => (5 : Fin 6))
        (X (0 : Fin 1) ^ s) =
      topSum (yOp ρ) (zOp ρ) 1 s [0] • w := by
  rw [rz_single_topSum]
  have hp : (X (0 : Fin 1) ^ s : MvPolynomial (Fin 1) ℂ) =
      modeMonomial (Fin 1) (Finsupp.single 0 s) := by
    simp [modeMonomial, X_pow_eq_monomial]
  rw [hp]
  change modeWordEvaluation (Fin 1)
      (fun a => radicalWord ρ w
        (shapedModes (fun _ : Fin 1 => (5 : Fin 6)) Finset.univ.toList a))
      (modeMonomial (Fin 1) (Finsupp.single 0 s)) =
        zOp ρ s w
  rw [modeWordEvaluation_monomial]
  simp [shapedModes, radicalWord, wordOp, radicalColour, zOp]

/-- The one-letter Rz relation and every polynomial in its Z power-sum
    shifts hold without a presentation hypothesis. -/
theorem rz_single_shift_family_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = rzKey [] [] [] 1 s)
    (hks : m + 1 ≤ 1 + s)
    (P : MvPolynomial (Fin 1) ℂ)
    (hP : P ∈ xyzPowerSumAlgebra (fun _ : Fin 1 => (5 : Fin 6))) :
    xyzEvaluation ρ w (fun _ : Fin 1 => (5 : Fin 6))
      (symmetricShiftAction (Fin 1) P (X (0 : Fin 1) ^ s)) ∈
        keyPrefix ρ w m i := by
  apply xyzPowerSumAlgebra_prefix ρ w m i h hi _
    (by intro t; exact Or.inr (Or.inr rfl)) P hP
  rw [rz_single_presentation]
  have hr := rz_top_prefix ρ w m h [] [] [] 1 s i
    (by omega) hks hi (by simpa using hkey)
  simpa using hr

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_single_topSum
#print axioms VOA.DeligneAudit.D4Levi.rz_single_presentation
#print axioms VOA.DeligneAudit.D4Levi.rz_single_shift_family_prefix
