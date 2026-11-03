import VOA.DeligneAudit.D4LeviKSLemma0Base

/-! The f₃ polarization with arbitrary Y and Z spectators. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- f₃ kills words formed only from Y and Z, before acting on the tail. -/
theorem fThreeDerivative_yz_zero (r : ℕ) (l : List (Fin 6 × ℕ)) (v : V)
    (hl : l.Forall (fun p => p.1 = 4 ∨ p.1 = 5)) :
    fThreeDerivative ρ r l v = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.forall_cons] at hl
      have hp : p.1 = 4 ∨ p.1 = 5 := hl.1
      have ht : l.Forall (fun p => p.1 = 4 ∨ p.1 = 5) :=
        hl.2
      rcases p with ⟨j, s⟩
      change j = 4 ∨ j = 5 at hp
      rcases hp with hp | hp
      · subst j
        simp [fThreeDerivative, fThreeLetter, ih ht]
      · subst j
        simp [fThreeDerivative, fThreeLetter, ih ht]

/-- One U'U pair is absorbed even with arbitrary Y and Z spectators. -/
theorem uup_pair_yz_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r u : ℕ) (l : List (Fin 6 × ℕ))
    (hl : l.Forall (fun p => p.1 = 4 ∨ p.1 = 5)) :
    radicalWord ρ w ((3, r) :: (2, u) :: l) ∈
      higherOrbit ρ w m (wordKey ((3, r) :: (2, u) :: l)) := by
  let k := wordKey ((3, r) :: (2, u) :: l)
  let N := higherOrbit ρ w m k
  have hsource : keyLess m k (wordKey ((1, 0) :: (2, u) :: l)) := by
    left
    simp [k, keyHeight, wordKey]
  have hderiv := fThree_derivative_higher ρ w m h k r
    ((1, 0) :: (2, u) :: l) hsource
  have htail := fThreeDerivative_yz_zero ρ r l w hl
  have hformula :
      fThreeDerivative ρ r ((1, 0) :: (2, u) :: l) w =
        -radicalWord ρ w ((3, r) :: (2, u) :: l) -
          radicalWord ρ w ((1, 0) :: (4, r + u) :: l) := by
    simp [fThreeDerivative, fThreeLetter, radicalWord, wordOp,
      radicalColour, htail]
    abel
  rw [hformula] at hderiv
  have hxy : keyLess m k (wordKey ((1, 0) :: (4, r + u) :: l)) := by
    simp [k, keyLess, keyHeight, wordKey]
    omega
  have hxy_mem : radicalWord ρ w ((1, 0) :: (4, r + u) :: l) ∈ N :=
    keyOrbit_le_higher ρ w m k _ hxy
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w ((1, 0) :: (4, r + u) :: l)))
  have hsum : -radicalWord ρ w ((3, r) :: (2, u) :: l) ∈ N := by
    simpa only [sub_add_cancel] using N.add_mem hderiv hxy_mem
  simpa [N] using N.neg_mem hsum

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fThreeDerivative_yz_zero
#print axioms VOA.DeligneAudit.D4Levi.uup_pair_yz_higher
