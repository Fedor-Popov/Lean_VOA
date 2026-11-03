import VOA.Commutative.InfiniteJetDifferential
import Mathlib.RingTheory.Derivation.Lie

/-!
# Intrinsic Hamiltonian modes on the arc algebra

Each derivation of the base polynomial algebra has a canonical family of shifted
Hasse--Schmidt prolongations. They are constructed directly on jet coordinates,
not transported from a vertex algebra. A base derivation preserving the original
ideal prolongs to derivations of the represented arc algebra.
-/
namespace VOA.InfiniteJet
open scoped BigOperators
noncomputable section
variable {R σ : Type*} [CommRing R]

/-- The `n`th shifted prolongation of a base derivation. For a Poisson Hamiltonian
`D = {a,-}`, these are the nonnegative modes with first argument the base element `a`. -/
def polynomialProlongation (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (n : ℕ) : Derivation R (JetPoly R σ) (JetPoly R σ) :=
  MvPolynomial.mkDerivation R (fun v : σ × ℕ =>
    if n ≤ v.2 then relationCoefficient (D (MvPolynomial.X v.1)) (v.2-n) else 0)

@[simp] theorem polynomialProlongation_X
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n : ℕ) (i : σ) (s : ℕ) :
    polynomialProlongation D n (MvPolynomial.X (i,s)) =
      if n ≤ s then relationCoefficient (D (MvPolynomial.X i)) (s-n) else 0 := by
  simp [polynomialProlongation]

/-- On universal generator series, prolongation is exactly a power-series shift. -/
theorem mapSeries_prolongation_generator
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n : ℕ) (i : σ) :
    mapSeries (polynomialProlongation D n) (generatorSeries i) =
      PowerSeries.X^n * MvPolynomial.aeval generatorSeries (D (MvPolynomial.X i)) := by
  apply PowerSeries.ext
  intro s
  simp only [coeff_mapSeries, coeff_generatorSeries, polynomialProlongation_X,
    PowerSeries.coeff_X_pow_mul', relationCoefficient]

/-- The chain rule proves prolongation on every universal base series. -/
theorem mapSeries_prolongation_aeval
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n : ℕ)
    (f : MvPolynomial σ R) :
    mapSeries (polynomialProlongation D n) (MvPolynomial.aeval generatorSeries f) =
      PowerSeries.X^n * MvPolynomial.aeval generatorSeries (D f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C, PowerSeries.algebraMap_apply, mapSeries_C,
        MvPolynomial.derivation_C, map_zero, mul_zero]
      simp
  | add f g hf hg =>
      simp only [map_add, mapSeries_add, hf, hg, mul_add]
  | mul_X f i hf =>
      simp only [map_mul, MvPolynomial.aeval_X, mapSeries_mul, hf,
        mapSeries_prolongation_generator, Derivation.leibniz, smul_eq_mul, map_add]
      ring

/-- Explicit action on every coefficient of every base polynomial. -/
theorem polynomialProlongation_relationCoefficient
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n s : ℕ)
    (f : MvPolynomial σ R) :
    polynomialProlongation D n (relationCoefficient f s) =
      if n ≤ s then relationCoefficient (D f) (s-n) else 0 := by
  have h := congrArg (PowerSeries.coeff s) (mapSeries_prolongation_aeval D n f)
  simpa only [coeff_mapSeries, relationCoefficient, PowerSeries.coeff_X_pow_mul'] using h

/-- Stability of the base ideal implies stability of the entire intrinsic arc ideal. -/
theorem polynomialProlongation_stable
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hI : ∀ f ∈ I, D f ∈ I)
    (n : ℕ) {f : JetPoly R σ} (hf : f ∈ jetIdeal I) :
    polynomialProlongation D n f ∈ jetIdeal I := by
  have heq : jetIdeal I = coefficientIdeal (I : Set (MvPolynomial σ R)) := by
    simpa only [Ideal.span_eq] using jetIdeal_span_eq_coefficientIdeal (I : Set (MvPolynomial σ R))
  rw [heq] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨g,hg,s,rfl⟩ := hp
      rw [polynomialProlongation_relationCoefficient]
      split_ifs with hns
      · exact relationCoefficient_mem_coefficientIdeal _ _ (hI g hg) _
      · exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Ideal.add_mem _ hf hg
  | smul a f hf hDf =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hDf) (Ideal.mul_mem_right _ _ hf)

/-- Intrinsically constructed Hamiltonian modes on the actual arc quotient. -/
def prolongation (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hI : ∀ f ∈ I, D f ∈ I) (n : ℕ) :
    Derivation R (PresentedJet I) (PresentedJet I) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective R (jetIdeal I))
    (d := polynomialProlongation D n)
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      (polynomialProlongation_stable D I hI n (Ideal.Quotient.eq_zero_iff_mem.mp hf)))

@[simp] theorem prolongation_mk
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) (hI : ∀ f ∈ I, D f ∈ I) (n : ℕ) (f : JetPoly R σ) :
    prolongation D I hI n (presentedJetMk I f) =
      presentedJetMk I (polynomialProlongation D n f) :=
  Derivation.liftOfSurjective_apply (Ideal.Quotient.mkₐ_surjective R (jetIdeal I))
    (fun g hg => Ideal.Quotient.eq_zero_iff_mem.mpr
      (polynomialProlongation_stable D I hI n (Ideal.Quotient.eq_zero_iff_mem.mp hg))) f

/-- Shifted prolongations respect the current Lie bracket of base derivations. -/
theorem polynomialProlongation_commutator
    (D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n m : ℕ) :
    ⁅polynomialProlongation D n, polynomialProlongation E m⁆ =
      polynomialProlongation ⁅D,E⁆ (n+m) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i,s⟩
  rw [Derivation.commutator_apply]
  simp only [polynomialProlongation_X, apply_ite, map_zero,
    polynomialProlongation_relationCoefficient, Derivation.commutator_apply]
  by_cases hnm : n+m ≤ s
  · have hm : m ≤ s := by omega
    have hn : n ≤ s := by omega
    have hns : n ≤ s-m := by omega
    have hms : m ≤ s-n := by omega
    rw [if_pos hm, if_pos hn, if_pos hns, if_pos hms, if_pos hnm]
    have hsn : s-m-n=s-(n+m) := by omega
    have hsm : s-n-m=s-(n+m) := by omega
    simp only [hsn,hsm,relationCoefficient,map_sub]
  · rw [if_neg hnm]
    by_cases hm : m ≤ s
    · have hns : ¬n ≤ s-m := by omega
      rw [if_pos hm, if_neg hns]
      by_cases hn : n ≤ s
      · rw [if_pos hn, if_neg (show ¬m ≤ s-n by omega), sub_zero]
      · rw [if_neg hn, sub_zero]
    · rw [if_neg hm]
      by_cases hn : n ≤ s
      · rw [if_pos hn, if_neg (show ¬m ≤ s-n by omega), sub_zero]
      · rw [if_neg hn, sub_zero]

end
end VOA.InfiniteJet
