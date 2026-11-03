import VOA.DeligneAudit.D4LeviKSPairYRestriction

/-! X symmetry survives extraction of each Y coefficient. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

def pairSourceXPerm (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    Equiv.Perm (PairSource a b c) :=
  Equiv.Perm.sumCongr e (Equiv.refl (Fin b ⊕ Fin c))

def pairXZXPerm (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    Equiv.Perm (PairXZ a b c) :=
  Equiv.Perm.sumCongr e (Equiv.refl (Fin c))

theorem pairSourceXPerm_xz (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    pairSourceXPerm a b c e ∘ pairXZSource a b c =
      pairXZSource a b c ∘ pairXZXPerm a b c e := by
  funext t
  rcases t with x | z <;> rfl

theorem pairSourceXPerm_y (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) (y : Fin b) :
    pairSourceXPerm a b c e (pairYSlot a b c y) =
      pairYSlot a b c y := rfl

theorem pairSplitAlgebra_rename_x (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a))
    (P : MvPolynomial (PairSource a b c) ℂ) :
    pairSplitAlgebra a b c (rename (pairSourceXPerm a b c e) P) =
      MvPolynomial.map (rename (pairXZXPerm a b c e)).toRingHom
        (pairSplitAlgebra a b c P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [pairSplitAlgebra]
  | add P Q ihP ihQ => simp [ihP, ihQ]
  | mul_X P t ih =>
      simp only [map_mul, ih]
      congr 1
      rcases t with x | (y | z)
      · simp [pairSplitAlgebra, pairSourceXPerm, pairSplitVariables,
          pairXZXPerm, sumToIter_Xr]
      · simp [pairSplitAlgebra, pairSourceXPerm, pairSplitVariables,
          pairSourceXPerm_y, map_X]
      · simp [pairSplitAlgebra, pairSourceXPerm, pairSplitVariables,
          pairXZXPerm, sumToIter_Xr]

/-- Every Y coefficient of a separately symmetric source polynomial is
    invariant under permutations of all paired and unpaired X positions. -/
theorem pairYCoeff_rename_x (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a))
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) (d : Fin b →₀ ℕ) :
    rename (pairXZXPerm a b c e)
        (coeff d (pairSplitAlgebra a b c P)) =
      coeff d (pairSplitAlgebra a b c P) := by
  have h := congrArg (fun Q => coeff d (pairSplitAlgebra a b c Q))
    (pairSourceSymmetric_rename_x a b c e P hP)
  change coeff d (pairSplitAlgebra a b c
      (rename (pairSourceXPerm a b c e) P)) = _ at h
  rw [pairSplitAlgebra_rename_x a b c e P] at h
  rw [MvPolynomial.coeff_map] at h
  exact h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSourceXPerm_xz
#print axioms VOA.DeligneAudit.D4Levi.pairSourceXPerm_y
#print axioms VOA.DeligneAudit.D4Levi.pairSplitAlgebra_rename_x
#print axioms VOA.DeligneAudit.D4Levi.pairYCoeff_rename_x
