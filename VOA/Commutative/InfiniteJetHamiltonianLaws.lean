import VOA.Commutative.InfiniteJetHamiltonian

/-!
# Locality, commutators, and translation of intrinsic arc Hamiltonians
-/
namespace VOA.InfiniteJet
open scoped BigOperators
noncomputable section
variable {R σ : Type*} [CommRing R]

/-- A polynomial is annihilated by all sufficiently high Hamiltonian modes. -/
theorem polynomialProlongation_locality
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (f : JetPoly R σ) :
    ∃ B : ℕ, ∀ n, B ≤ n → polynomialProlongation D n f = 0 := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨0, fun n hn => MvPolynomial.derivation_C _ c⟩
  | add f g hf hg =>
      obtain ⟨B,hB⟩ := hf
      obtain ⟨C,hC⟩ := hg
      exact ⟨max B C, fun n hn => by rw [map_add, hB n (le_trans (le_max_left _ _) hn),
        hC n (le_trans (le_max_right _ _) hn), add_zero]⟩
  | mul_X f v hf =>
      obtain ⟨B,hB⟩ := hf
      refine ⟨max B (v.2+1),fun n hn => ?_⟩
      rw [Derivation.leibniz, polynomialProlongation_X,
        if_neg (show ¬ n ≤ v.2 by omega), hB n (le_trans (le_max_left _ _) hn),
        smul_zero, smul_zero, add_zero]

/-- Locality passes to the actual arc quotient. -/
theorem prolongation_locality
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hI : ∀ f ∈ I, D f ∈ I) (y : PresentedJet I) :
    ∃ B : ℕ, ∀ n, B ≤ n → prolongation D I hI n y = 0 := by
  refine Submodule.Quotient.induction_on _ y (fun f => ?_)
  obtain ⟨B,hB⟩ := polynomialProlongation_locality D f
  refine ⟨B,fun n hn => ?_⟩
  change prolongation D I hI n (presentedJetMk I f) = 0
  rw [prolongation_mk, hB n hn, map_zero]

/-- Commutators of base ideal-preserving derivations preserve that ideal. -/
theorem commutator_stable
    (D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hD : ∀ f ∈ I, D f ∈ I) (hE : ∀ f ∈ I, E f ∈ I) :
    ∀ f ∈ I, ⁅D,E⁆ f ∈ I := by
  intro f hf
  rw [Derivation.commutator_apply]
  exact I.sub_mem (hD _ (hE _ hf)) (hE _ (hD _ hf))

/-- The intrinsic arc Hamiltonians form the current Lie algebra action after quotienting. -/
theorem prolongation_commutator
    (D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hD : ∀ f ∈ I, D f ∈ I) (hE : ∀ f ∈ I, E f ∈ I)
    (n m : ℕ) :
    ⁅prolongation D I hD n, prolongation E I hE m⁆ =
      prolongation ⁅D,E⁆ I (commutator_stable D E I hD hE) (n+m) := by
  apply Derivation.ext
  intro y
  refine Submodule.Quotient.induction_on _ y (fun f => ?_)
  change ⁅prolongation D I hD n, prolongation E I hE m⁆ (presentedJetMk I f) =
    prolongation ⁅D,E⁆ I (commutator_stable D E I hD hE) (n+m) (presentedJetMk I f)
  rw [Derivation.commutator_apply, prolongation_mk, prolongation_mk,
    prolongation_mk, prolongation_mk, prolongation_mk, ← map_sub]
  have h := DFunLike.congr_fun (polynomialProlongation_commutator D E n m) f
  rw [Derivation.commutator_apply] at h
  rw [h]

/-- Translation differentiates every universal Hasse--Schmidt coefficient. -/
theorem polynomialTranslation_relationCoefficient (f : MvPolynomial σ R) (s : ℕ) :
    polynomialTranslation (relationCoefficient f s) = (s+1) • relationCoefficient f (s+1) := by
  rw [relationCoefficient_eq_ofFinite, polynomialTranslation_relationCoeff s s le_rfl,
    ← relationCoefficient_eq_ofFinite]

/-- The zeroth Hamiltonian prolongation commutes with translation. -/
theorem polynomialTranslation_prolongation_zero
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) :
    ⁅polynomialTranslation (R := R) (σ := σ), polynomialProlongation D 0⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i,s⟩
  simp only [Derivation.commutator_apply, polynomialProlongation_X, Nat.zero_le, if_true,
    Nat.sub_zero, polynomialTranslation_relationCoefficient, polynomialTranslation_X,
    map_nsmul, sub_self, Derivation.zero_apply]

/-- Translation shifts Hamiltonian modes by the correct negative mode coefficient. -/
theorem polynomialTranslation_prolongation_succ
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n : ℕ) :
    ⁅polynomialTranslation (R := R) (σ := σ), polynomialProlongation D (n+1)⁆ =
      -((n+1) • polynomialProlongation D n) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i,s⟩
  rw [Derivation.commutator_apply, polynomialProlongation_X, polynomialTranslation_X,
    map_nsmul, polynomialProlongation_X]
  change polynomialTranslation (if n+1 ≤ s then _ else 0) -
      (s+1) • (if n+1 ≤ s+1 then _ else 0) =
    -((n+1) • polynomialProlongation D n (MvPolynomial.X (i,s)))
  rw [polynomialProlongation_X]
  by_cases hns : n ≤ s
  · rw [if_pos (show n+1 ≤ s+1 by omega), if_pos hns]
    by_cases hs : s=n
    · subst s
      simp only [if_neg (show ¬n+1 ≤ n by omega), map_zero, Nat.sub_self, zero_sub]
    · have hlt : n+1 ≤ s := by omega
      rw [if_pos hlt, polynomialTranslation_relationCoefficient]
      have h1 : s-(n+1)+1=s-n := by omega
      have h2 : s+1-(n+1)=s-n := by omega
      rw [h1,h2]
      have h3 : s+1=(s-n)+(n+1) := by omega
      rw [h3,add_nsmul]
      abel
  · rw [if_neg (show ¬n+1 ≤ s by omega), if_neg (show ¬n+1 ≤ s+1 by omega),
      if_neg hns, map_zero, nsmul_zero, nsmul_zero, sub_zero, neg_zero]

end
end VOA.InfiniteJet
