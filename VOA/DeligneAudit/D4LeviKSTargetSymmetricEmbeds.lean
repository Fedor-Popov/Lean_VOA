import VOA.DeligneAudit.D4LeviKSTargetKernel

/-! Symmetric polynomials in each PAIR target alphabet are target elements. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

theorem pairTarget_symmetric_X_mem (a b c : ℕ)
    (P : MvPolynomial (Fin a) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin a) ℂ) :
    rename Sum.inl P ∈ pairTargetSymmetric a b c := by
  apply symmetric_image_mem_of_power_sums (Fin a)
    (MvPolynomial (PairTarget a b c) ℂ)
    (rename Sum.inl) (pairTargetSymmetric a b c) ?_ P hP
  intro r
  have h := pairTargetPower_mem a b c 0 r
  simpa [pairTargetPower, pairTargetXPsum, psum] using h

theorem pairTarget_symmetric_Y_mem (a b c : ℕ)
    (P : MvPolynomial (Fin b) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin b) ℂ) :
    rename (fun y : Fin b => (Sum.inr (Sum.inl y) : PairTarget a b c)) P ∈
      pairTargetSymmetric a b c := by
  apply symmetric_image_mem_of_power_sums (Fin b)
    (MvPolynomial (PairTarget a b c) ℂ)
    (rename (fun y : Fin b =>
      (Sum.inr (Sum.inl y) : PairTarget a b c)))
    (pairTargetSymmetric a b c) ?_ P hP
  intro r
  have h := pairTargetPower_mem a b c 1 r
  simpa [pairTargetPower, targetYPsum, psum] using h

theorem pairTarget_symmetric_Z_mem (a b c : ℕ)
    (P : MvPolynomial (Fin c) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin c) ℂ) :
    rename (fun z : Fin c => (Sum.inr (Sum.inr z) : PairTarget a b c)) P ∈
      pairTargetSymmetric a b c := by
  apply symmetric_image_mem_of_power_sums (Fin c)
    (MvPolynomial (PairTarget a b c) ℂ)
    (rename (fun z : Fin c =>
      (Sum.inr (Sum.inr z) : PairTarget a b c)))
    (pairTargetSymmetric a b c) ?_ P hP
  intro r
  have h := pairTargetPower_mem a b c 2 r
  simpa [pairTargetPower, pairTargetZPsum, psum] using h

/-- A product of separately symmetric X, Y, and Z factors belongs to
    the target space used in the three-colour box induction. -/
theorem pairTarget_separate_symmetric_mem (a b c : ℕ)
    (Xpoly : MvPolynomial (Fin a) ℂ)
    (Ypoly : MvPolynomial (Fin b) ℂ)
    (Zpoly : MvPolynomial (Fin c) ℂ)
    (hX : Xpoly ∈ symmetricSubalgebra (Fin a) ℂ)
    (hY : Ypoly ∈ symmetricSubalgebra (Fin b) ℂ)
    (hZ : Zpoly ∈ symmetricSubalgebra (Fin c) ℂ) :
    rename Sum.inl Xpoly *
        rename (fun y : Fin b => (Sum.inr (Sum.inl y) : PairTarget a b c)) Ypoly *
        rename (fun z : Fin c => (Sum.inr (Sum.inr z) : PairTarget a b c)) Zpoly ∈
      pairTargetSymmetric a b c := by
  exact (pairTargetSymmetric a b c).mul_mem
    ((pairTargetSymmetric a b c).mul_mem
      (pairTarget_symmetric_X_mem a b c Xpoly hX)
      (pairTarget_symmetric_Y_mem a b c Ypoly hY))
    (pairTarget_symmetric_Z_mem a b c Zpoly hZ)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairTarget_symmetric_X_mem
#print axioms VOA.DeligneAudit.D4Levi.pairTarget_symmetric_Y_mem
#print axioms VOA.DeligneAudit.D4Levi.pairTarget_symmetric_Z_mem
#print axioms VOA.DeligneAudit.D4Levi.pairTarget_separate_symmetric_mem
