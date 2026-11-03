import VOA.Commutative.PoissonVertexHom
import VOA.Commutative.InfiniteJetHamiltonianLaws

/-! # Identification of PVA generator modes with intrinsic Hamiltonian prolongations -/
namespace VOA.InfiniteJet
open scoped BigOperators
noncomputable section
variable {σ : Type*}
variable (P : PoissonVertexAlgebra (JetPoly ℂ σ))
    (hT : P.translation = polynomialTranslation)
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hzero : ∀ i j, P.mode 0 (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) =
      relationCoefficient (D i (MvPolynomial.X j)) 0)
    (hpos : ∀ i j n, P.mode (n+1) (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) = 0)
include hT hzero hpos

/-- Genuine sesquilinearity determines the Hamiltonian action on every jet generator. -/
theorem base_mode_X (i j : σ) (s n : ℕ) :
    P.mode n (MvPolynomial.X (i,0)) (MvPolynomial.X (j,s)) =
      polynomialProlongation (D i) n (MvPolynomial.X (j,s)) := by
  induction s generalizing n with
  | zero =>
      cases n with
      | zero => simpa only [polynomialProlongation_X,Nat.zero_le,if_true,Nat.sub_zero] using hzero i j
      | succ n => simp [hpos,polynomialProlongation_X]
  | succ s ih =>
      have hp := P.translation_mode n (MvPolynomial.X (i,0)) (MvPolynomial.X (j,s))
      have hstep : (s+1) • P.mode n (MvPolynomial.X (i,0)) (MvPolynomial.X (j,s+1)) =
          (s+1) • polynomialProlongation (D i) n (MvPolynomial.X (j,s+1)) := by
        cases n with
        | zero =>
            have hd := congrArg (fun d : Derivation ℂ (JetPoly ℂ σ) (JetPoly ℂ σ) =>
              d (MvPolynomial.X (j,s))) (polynomialTranslation_prolongation_zero (D i))
            rw [P.translation_left_zero,zero_add,hT,polynomialTranslation_X,map_nsmul,ih] at hp
            simp only [Derivation.commutator_apply,Derivation.zero_apply,
              polynomialTranslation_X,map_nsmul] at hd
            exact hp.symm.trans (sub_eq_zero.mp hd)
        | succ n =>
            have hd := congrArg (fun d : Derivation ℂ (JetPoly ℂ σ) (JetPoly ℂ σ) =>
              d (MvPolynomial.X (j,s))) (polynomialTranslation_prolongation_succ (D i) n)
            rw [P.translation_left_succ,hT,polynomialTranslation_X,map_nsmul,ih,ih] at hp
            simp only [Derivation.commutator_apply,Derivation.neg_apply,Derivation.smul_apply,
              polynomialTranslation_X,map_nsmul] at hd
            rw [neg_smul, Nat.cast_smul_eq_nsmul] at hp
            apply add_left_cancel (a := -((n+1) • polynomialProlongation (D i) n (MvPolynomial.X (j,s))))
            exact hp.symm.trans (sub_eq_iff_eq_add.mp hd)
      exact (nsmul_right_injective (by omega : s+1 ≠ 0)) hstep

/-- The entire generator Hamiltonian is the independently defined shifted prolongation. -/
theorem base_mode_eq_prolongation (i : σ) (n : ℕ) (f : JetPoly ℂ σ) :
    P.mode n (MvPolynomial.X (i,0)) f = polynomialProlongation (D i) n f := by
  induction f using MvPolynomial.induction_on with
  | C c =>
      simpa using P.mode_algebraMap_right n (MvPolynomial.X (i,0)) c
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f v hf =>
      rw [P.leibniz,Derivation.leibniz,hf,base_mode_X P hT D hzero hpos]
      simp only [smul_eq_mul,mul_comm,add_comm]

omit hzero hpos D in
/-- Every successor jet generator is a divided translate of its predecessor. -/
theorem X_succ_eq_smul_translation (i : σ) (r : ℕ) :
    MvPolynomial.X (i,r+1) = ((r+1 : ℕ) : ℂ)⁻¹ • P.translation (MvPolynomial.X (i,r)) := by
  rw [hT,polynomialTranslation_X,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero r),one_smul]

omit hT hzero hpos D in
/-- A translation-stable ideal transfers mode stability to the reversed pair by skew symmetry. -/
theorem mode_mem_of_reverse (I : Ideal (JetPoly ℂ σ))
    (hIT : ∀ f ∈ I, P.translation f ∈ I) (x y : JetPoly ℂ σ)
    (h : ∀ n, P.mode n y x ∈ I) (n : ℕ) : P.mode n x y ∈ I := by
  have hp : ∀ j f, f ∈ I → (P.translation.toLinearMap^j) f ∈ I := by
    intro j f hf
    induction j with
    | zero => exact hf
    | succ j ih =>
        simp only [pow_succ',Module.End.mul_apply]
        exact hIT _ ih
  rw [P.skew]
  have hfin : (Function.support fun j : ℕ => (j.factorial : ℂ)⁻¹ •
      (-1 : ℂ)^(n+j+1) • ((P.translation.toLinearMap^j) (P.mode (n+j) y x))).Finite := by
    obtain ⟨b,hb⟩ := P.locality y x
    apply (Set.finite_Iio b).subset
    intro j hj
    change j < b
    by_contra hlt
    apply hj
    change (j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
      ((P.translation.toLinearMap^j) (P.mode (n+j) y x)) = 0
    rw [hb (n+j) (by omega),map_zero,smul_zero,smul_zero]
  rw [finsum_eq_sum _ hfin]
  apply I.sum_mem
  intro j hj
  exact (I.restrictScalars ℂ).smul_mem _ ((I.restrictScalars ℂ).smul_mem _ (hp j _ (h _)))

/-- Every differential generator preserves the true arc ideal in every mode. -/
theorem generator_mode_jetIdeal (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ i f, f ∈ I → D i f ∈ I) (i : σ) (r n : ℕ)
    {f : JetPoly ℂ σ} (hf : f ∈ jetIdeal I) :
    P.mode n (MvPolynomial.X (i,r)) f ∈ jetIdeal I := by
  induction r generalizing n with
  | zero =>
      rw [base_mode_eq_prolongation P hT D hzero hpos]
      exact polynomialProlongation_stable (D i) I (hI i) n hf
  | succ r ih =>
      rw [X_succ_eq_smul_translation P hT i r,map_smul,LinearMap.smul_apply]
      apply ((jetIdeal I).restrictScalars ℂ).smul_mem
      cases n with
      | zero => rw [P.translation_left_zero]; exact Ideal.zero_mem _
      | succ n =>
          rw [P.translation_left_succ]
          exact ((jetIdeal I).restrictScalars ℂ).smul_mem _ (ih n)

/-- All PVA modes preserve the actual arc ideal in their first argument. -/
theorem mode_jetIdeal_left (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ i f, f ∈ I → D i f ∈ I) (n : ℕ)
    {f : JetPoly ℂ σ} (hf : f ∈ jetIdeal I) (g : JetPoly ℂ σ) :
    P.mode n f g ∈ jetIdeal I := by
  have ht : ∀ a ∈ jetIdeal I, P.translation a ∈ jetIdeal I := by
    intro a ha
    rw [hT]
    exact polynomialTranslation_stable I a ha
  have hgen : ∀ v : σ × ℕ, P.mode n f (MvPolynomial.X v) ∈ jetIdeal I := by
    intro v
    exact mode_mem_of_reverse P (jetIdeal I) ht f (MvPolynomial.X v)
      (fun j => generator_mode_jetIdeal P hT D hzero hpos I hI v.1 v.2 j hf) n
  induction g using MvPolynomial.induction_on with
  | C c =>
      rw [show MvPolynomial.C c = algebraMap ℂ (JetPoly ℂ σ) c from rfl,
        P.mode_algebraMap_right]
      exact Ideal.zero_mem _
  | add g h hg hh => rw [map_add]; exact Ideal.add_mem _ hg hh
  | mul_X g v hg =>
      rw [P.leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (hgen v))

/-- All PVA modes preserve the actual arc ideal in their second argument. -/
theorem mode_jetIdeal_right (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ i f, f ∈ I → D i f ∈ I) (n : ℕ) (f : JetPoly ℂ σ)
    {g : JetPoly ℂ σ} (hg : g ∈ jetIdeal I) : P.mode n f g ∈ jetIdeal I :=
  mode_mem_of_reverse P (jetIdeal I)
    (fun a ha => by rw [hT]; exact polynomialTranslation_stable I a ha) f g
    (fun j => mode_jetIdeal_left P hT D hzero hpos I hI j hg f) n

end
end VOA.InfiniteJet
