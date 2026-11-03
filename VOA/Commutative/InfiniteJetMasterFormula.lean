import VOA.Commutative.InfiniteJetHamiltonianLaws
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic

/-!
# Explicit polynomial arc modes by the master formula

First extend a base Hamiltonian to every divided jet generator by left
sesquilinearity. Skew substitution gives its action with an arbitrary first
polynomial and a generator second. The unique polynomial derivation then extends
the second argument. These operations are explicit, independently of any VOA.
-/
namespace VOA.InfiniteJet
open scoped BigOperators
noncomputable section
variable {σ : Type*}

/-- The mode with a divided jet generator as its first argument. -/
def generatorHamiltonianMode
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (v : σ × ℕ) (n : ℕ) : Derivation ℂ (JetPoly ℂ σ) (JetPoly ℂ σ) :=
  if v.2 ≤ n then ((-1 : ℂ)^v.2 * (n.choose v.2 : ℂ)) • polynomialProlongation (D v.1) (n-v.2)
  else 0

/-- All generator Hamiltonians are locally finite on every polynomial. -/
theorem generatorHamiltonianMode_locality
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (v : σ × ℕ) (f : JetPoly ℂ σ) :
    ∃ B : ℕ, ∀ n, B ≤ n → generatorHamiltonianMode D v n f = 0 := by
  obtain ⟨B,hB⟩ := polynomialProlongation_locality (D v.1) f
  refine ⟨B+v.2,fun n hn => ?_⟩
  rw [generatorHamiltonianMode, if_pos (by omega)]
  change ((-1 : ℂ)^v.2 * (n.choose v.2 : ℂ)) •
    polynomialProlongation (D v.1) (n-v.2) f = 0
  rw [hB (n-v.2) (by omega), smul_zero]

/-- One summand of the genuine skew substitution used in the master formula. -/
def masterSkewTerm
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) (f : JetPoly ℂ σ) (v : σ × ℕ) (j : ℕ) : JetPoly ℂ σ :=
  (j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
    ((polynomialTranslation.toLinearMap^j) (generatorHamiltonianMode D v (n+j) f))

/-- The master-formula sum is finitely supported for each input polynomial. -/
theorem masterSkewTerm_finite
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) (f : JetPoly ℂ σ) (v : σ × ℕ) :
    (Function.support (masterSkewTerm D n f v)).Finite := by
  obtain ⟨B,hB⟩ := generatorHamiltonianMode_locality D v f
  apply (Set.finite_Iio B).subset
  intro j hj
  change j < B
  by_contra hlt
  apply hj
  simp only [masterSkewTerm, hB (n+j) (by omega), map_zero, smul_zero]

/-- The master formula on a generator in the second slot, linear in its first slot. -/
def masterGeneratorLinear
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) (v : σ × ℕ) : JetPoly ℂ σ →ₗ[ℂ] JetPoly ℂ σ where
  toFun f := ∑ᶠ j : ℕ, masterSkewTerm D n f v j
  map_add' f g := by
    have hf := masterSkewTerm_finite D n f v
    have hg := masterSkewTerm_finite D n g v
    simp only [masterSkewTerm, map_add, smul_add]
    exact finsum_add_distrib hf hg
  map_smul' c f := by
    change (∑ᶠ j : ℕ, masterSkewTerm D n (c • f) v j) =
      c • (∑ᶠ j : ℕ, masterSkewTerm D n f v j)
    have hs : ∀ j, masterSkewTerm D n (c • f) v j = c • masterSkewTerm D n f v j := by
      intro j
      simp only [masterSkewTerm, Derivation.map_smul, map_smul]
      simp only [smul_comm c]
    simp_rw [hs]
    exact (smul_finsum' c (masterSkewTerm_finite D n f v)).symm

/-- The full polynomial master operation: the unique derivation in the second slot
whose generator values are the explicit skew sums. -/
def masterDerivation
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) (f : JetPoly ℂ σ) : Derivation ℂ (JetPoly ℂ σ) (JetPoly ℂ σ) :=
  MvPolynomial.mkDerivation ℂ (fun v => masterGeneratorLinear D n v f)

@[simp] theorem masterDerivation_X
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) (f : JetPoly ℂ σ) (v : σ × ℕ) :
    masterDerivation D n f (MvPolynomial.X v) = masterGeneratorLinear D n v f := by
  simp [masterDerivation]

/-- The explicit master operation is bilinear. -/
def masterMode
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) : JetPoly ℂ σ →ₗ[ℂ] JetPoly ℂ σ →ₗ[ℂ] JetPoly ℂ σ where
  toFun f := (masterDerivation D n f).toLinearMap
  map_add' f g := by
    have h : masterDerivation D n (f+g) = masterDerivation D n f + masterDerivation D n g := by
      apply MvPolynomial.derivation_ext
      intro v
      simp only [masterDerivation_X, map_add, Derivation.add_apply]
    exact congrArg Derivation.toLinearMap h
  map_smul' c f := by
    have h : masterDerivation D n (c • f) = c • masterDerivation D n f := by
      apply MvPolynomial.derivation_ext
      intro v
      simp only [masterDerivation_X, map_smul, Derivation.smul_apply]
    exact congrArg Derivation.toLinearMap h

/-- The constructed modes satisfy the right Leibniz identity by construction as derivations. -/
theorem masterMode_leibniz
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (n : ℕ) (f g h : JetPoly ℂ σ) :
    masterMode D n f (g*h) = masterMode D n f g * h + g * masterMode D n f h := by
  change masterDerivation D n f (g*h) = masterDerivation D n f g * h + g * masterDerivation D n f h
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/-- The master operation is locally finite for each pair of polynomials. -/
theorem masterMode_locality
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f g : JetPoly ℂ σ) : ∃ B : ℕ, ∀ n, B ≤ n → masterMode D n f g = 0 := by
  induction g using MvPolynomial.induction_on with
  | C c => exact ⟨0,fun n hn => MvPolynomial.derivation_C (masterDerivation D n f) c⟩
  | add g h hg hh =>
      obtain ⟨B,hB⟩ := hg
      obtain ⟨C,hC⟩ := hh
      exact ⟨max B C,fun n hn => by rw [map_add,
        hB n (le_trans (le_max_left _ _) hn), hC n (le_trans (le_max_right _ _) hn), add_zero]⟩
  | mul_X g v hg =>
      obtain ⟨B,hB⟩ := hg
      obtain ⟨C,hC⟩ := generatorHamiltonianMode_locality D v f
      refine ⟨max B C,fun n hn => ?_⟩
      have hx : masterMode D n f (MvPolynomial.X v) = 0 := by
        change masterDerivation D n f (MvPolynomial.X v) = 0
        rw [masterDerivation_X]
        change (∑ᶠ j : ℕ, masterSkewTerm D n f v j) = 0
        apply finsum_eq_zero_of_forall_eq_zero
        intro j
        simp only [masterSkewTerm, hC (n+j) (by omega), map_zero, smul_zero]
      rw [masterMode_leibniz, hB n (le_trans (le_max_left _ _) hn), hx, zero_mul, mul_zero, add_zero]

/-- The first slot of the master operation preserves the intrinsic arc relations.
This is proved from base ideal stability, coefficient prolongation, and translation stability. -/
theorem masterMode_mem_of_left_mem_jetIdeal
    (D : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (I : Ideal (MvPolynomial σ ℂ)) (hI : ∀ i f, f ∈ I → D i f ∈ I)
    (n : ℕ) {f : JetPoly ℂ σ} (hf : f ∈ jetIdeal I) (g : JetPoly ℂ σ) :
    masterMode D n f g ∈ jetIdeal I := by
  have hT : ∀ (j : ℕ) (p : JetPoly ℂ σ), p ∈ jetIdeal I →
      (polynomialTranslation.toLinearMap^j) p ∈ jetIdeal I := by
    intro j p hp
    induction j with
    | zero => exact hp
    | succ j ih =>
        simp only [pow_succ', Module.End.mul_apply]
        exact polynomialTranslation_stable I _ ih
  have hgen : ∀ v : σ × ℕ, masterMode D n f (MvPolynomial.X v) ∈ jetIdeal I := by
    intro v
    change masterDerivation D n f (MvPolynomial.X v) ∈ jetIdeal I
    rw [masterDerivation_X]
    change (∑ᶠ j : ℕ, masterSkewTerm D n f v j) ∈ jetIdeal I
    rw [finsum_eq_sum _ (masterSkewTerm_finite D n f v)]
    apply Ideal.sum_mem
    intro j hj
    apply ((jetIdeal I).restrictScalars ℂ).smul_mem
    apply ((jetIdeal I).restrictScalars ℂ).smul_mem
    apply hT
    unfold generatorHamiltonianMode
    split_ifs
    · exact ((jetIdeal I).restrictScalars ℂ).smul_mem _
        (polynomialProlongation_stable (D v.1) I (hI v.1) _ hf)
    · exact (jetIdeal I).zero_mem
  induction g using MvPolynomial.induction_on with
  | C c =>
      change masterDerivation D n f (MvPolynomial.C c) ∈ jetIdeal I
      rw [MvPolynomial.derivation_C]
      exact Ideal.zero_mem _
  | add g h hg hh => rw [map_add]; exact Ideal.add_mem _ hg hh
  | mul_X g v hg =>
      rw [masterMode_leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (hgen v))

end
end VOA.InfiniteJet
