import VOA.DeligneAudit.D4LeviKSPairSymmetricSurj

/-! Every separately symmetric alphabet embeds in the power-sum PAIR domain. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

private theorem rename_symmetric_mem_of_psum
    (σ τ : Type*) [Fintype σ] (e : σ → τ)
    (S : Subalgebra ℂ (MvPolynomial τ ℂ))
    (hpower : ∀ r, rename e (psum σ ℂ r) ∈ S)
    (P : MvPolynomial σ ℂ) (hP : P ∈ symmetricSubalgebra σ ℂ) :
    rename e P ∈ S := by
  let φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ := rename e
  have hsub : powerSumAlgebra σ ≤ S.comap φ := by
    apply Algebra.adjoin_le
    rintro Q ⟨r, rfl⟩
    exact hpower r
  exact hsub (symmetric_mem_powerSumAlgebra σ P hP)

theorem pairSource_symmetric_X_mem (a b c : ℕ)
    (P : MvPolynomial (Fin b ⊕ Fin a) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin b ⊕ Fin a) ℂ) :
    rename Sum.inl P ∈ pairSourceSymmetric a b c := by
  apply rename_symmetric_mem_of_psum _ _ Sum.inl _ ?_ P hP
  intro r
  have h := pairSourcePower_mem a b c 0 r
  simpa [pairSourcePower, pairSourceXPsum, psum] using h

theorem pairSource_symmetric_Y_mem (a b c : ℕ)
    (P : MvPolynomial (Fin b) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin b) ℂ) :
    rename (fun y : Fin b => (Sum.inr (Sum.inl y) : PairSource a b c)) P ∈
      pairSourceSymmetric a b c := by
  apply rename_symmetric_mem_of_psum _ _
    (fun y : Fin b => (Sum.inr (Sum.inl y) : PairSource a b c)) _ ?_ P hP
  intro r
  have h := pairSourcePower_mem a b c 1 r
  simpa [pairSourcePower, sourceYPsum, psum] using h

theorem pairSource_symmetric_Z_mem (a b c : ℕ)
    (P : MvPolynomial (Fin c) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin c) ℂ) :
    rename (fun z : Fin c => (Sum.inr (Sum.inr z) : PairSource a b c)) P ∈
      pairSourceSymmetric a b c := by
  apply rename_symmetric_mem_of_psum _ _
    (fun z : Fin c => (Sum.inr (Sum.inr z) : PairSource a b c)) _ ?_ P hP
  intro r
  have h := pairSourcePower_mem a b c 2 r
  simpa [pairSourcePower, pairSourceZPsum, psum] using h

/-- Products of arbitrary symmetric polynomials in the three independent
    source alphabets lie in the domain of `pairSymmetricRestriction`. -/
theorem pairSource_separate_symmetric_mem (a b c : ℕ)
    (Xpoly : MvPolynomial (Fin b ⊕ Fin a) ℂ)
    (Ypoly : MvPolynomial (Fin b) ℂ)
    (Zpoly : MvPolynomial (Fin c) ℂ)
    (hX : Xpoly ∈ symmetricSubalgebra (Fin b ⊕ Fin a) ℂ)
    (hY : Ypoly ∈ symmetricSubalgebra (Fin b) ℂ)
    (hZ : Zpoly ∈ symmetricSubalgebra (Fin c) ℂ) :
    rename Sum.inl Xpoly *
        rename (fun y : Fin b => (Sum.inr (Sum.inl y) : PairSource a b c)) Ypoly *
        rename (fun z : Fin c => (Sum.inr (Sum.inr z) : PairSource a b c)) Zpoly ∈
      pairSourceSymmetric a b c := by
  exact (pairSourceSymmetric a b c).mul_mem
    ((pairSourceSymmetric a b c).mul_mem
      (pairSource_symmetric_X_mem a b c Xpoly hX)
      (pairSource_symmetric_Y_mem a b c Ypoly hY))
    (pairSource_symmetric_Z_mem a b c Zpoly hZ)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSource_symmetric_X_mem
#print axioms VOA.DeligneAudit.D4Levi.pairSource_symmetric_Y_mem
#print axioms VOA.DeligneAudit.D4Levi.pairSource_symmetric_Z_mem
#print axioms VOA.DeligneAudit.D4Levi.pairSource_separate_symmetric_mem
