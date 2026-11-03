/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.InfiniteJetGenerators
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Translation on the infinite jet algebra

The ordinary-coefficient convention has `T(x_(i,n)) = (n+1) x_(i,n+1)`.
We prove stability of the defining ideal before descending this derivation, and then
prove compatibility of the canonical differential evaluation with translation.
-/

namespace VOA.InfiniteJet

open scoped BigOperators

noncomputable section

variable {R σ A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Apply a derivation coefficientwise to a formal power series. -/
def mapSeries (D : Derivation R A A) (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coeff_mapSeries (D : Derivation R A A) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (mapSeries D f) = D (PowerSeries.coeff n f) := by
  simp [mapSeries]

@[simp] theorem mapSeries_add (D : Derivation R A A) (f g : PowerSeries A) :
    mapSeries D (f + g) = mapSeries D f + mapSeries D g := by
  apply PowerSeries.ext
  intro n
  simp

@[simp] theorem mapSeries_C (D : Derivation R A A) (a : A) :
    mapSeries D (PowerSeries.C a) = PowerSeries.C (D a) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n; simp
  · simp [PowerSeries.coeff_C, hn]

theorem mapSeries_mul (D : Derivation R A A) (f g : PowerSeries A) :
    mapSeries D (f * g) = mapSeries D f * g + f * mapSeries D g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_mapSeries, PowerSeries.coeff_mul, map_sum, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [D.leibniz, smul_eq_mul]
  ring

/-- Translation on the polynomial ring of unbounded jet coordinates. -/
def polynomialTranslation : Derivation R (JetPoly R σ) (JetPoly R σ) :=
  MvPolynomial.mkDerivation R (fun v : σ × ℕ =>
    (v.2 + 1) • MvPolynomial.X (v.1, v.2 + 1))

@[simp] theorem polynomialTranslation_X (i : σ) (n : ℕ) :
    polynomialTranslation (R := R) (MvPolynomial.X (i, n)) =
      (n + 1) • MvPolynomial.X (i, n + 1) := by
  simp [polynomialTranslation]

/-- Infinite substitution coefficients agree with every sufficiently long finite jet stage. -/
theorem coeff_generatorSeries_aeval (m n : ℕ) (hn : n ≤ m) (f : MvPolynomial σ R) :
    PowerSeries.coeff n (MvPolynomial.aeval (generatorSeries (R := R)) f) =
      ofFinite m (FiniteJet.relationCoeff m n f) := by
  rw [← seriesJetEval_ofFinite_relationCoeff _ m n hn, seriesJetEval_generatorSeries]
  rfl

theorem mapSeries_generatorSeries (i : σ) :
    mapSeries (polynomialTranslation (R := R)) (generatorSeries i) =
      PowerSeries.derivative (JetPoly R σ) (generatorSeries i) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_mapSeries, coeff_generatorSeries, polynomialTranslation_X,
    PowerSeries.coeff_derivative, nsmul_eq_mul]
  push_cast
  ring

/-- Translation of all coefficients agrees with differentiating the substituted relation. -/
theorem mapSeries_aeval_generatorSeries (f : MvPolynomial σ R) :
    mapSeries (polynomialTranslation (R := R))
        (MvPolynomial.aeval (generatorSeries (R := R)) f) =
      PowerSeries.derivative (JetPoly R σ)
        (MvPolynomial.aeval (generatorSeries (R := R)) f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [PowerSeries.algebraMap_apply]
  | add f g hf hg => simp only [map_add, mapSeries_add, hf, hg]
  | mul_X f i hf =>
      simp only [map_mul, MvPolynomial.aeval_X, mapSeries_mul, hf, mapSeries_generatorSeries,
        Derivation.leibniz, smul_eq_mul]
      ring

/-- Differentiating a relation coefficient gives the next relation coefficient with its
ordinary-coefficient normalization. -/
theorem polynomialTranslation_relationCoeff (m n : ℕ) (hn : n ≤ m)
    (f : MvPolynomial σ R) :
    polynomialTranslation (ofFinite m (FiniteJet.relationCoeff m n f)) =
      (n + 1) • ofFinite (n + 1) (FiniteJet.relationCoeff (n + 1) (n + 1) f) := by
  have h := congrArg (PowerSeries.coeff n) (mapSeries_aeval_generatorSeries f)
  rw [coeff_mapSeries, PowerSeries.coeff_derivative,
    coeff_generatorSeries_aeval m n hn,
    coeff_generatorSeries_aeval (n + 1) (n + 1) le_rfl] at h
  simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- Translation of a finite-stage relation ideal lies in the infinite relation ideal. -/
theorem polynomialTranslation_mem_ofFiniteJetIdeal
    (I : Ideal (MvPolynomial σ R)) (m : ℕ) (g : FiniteJet.JetPoly R σ m)
    (hg : g ∈ FiniteJet.jetIdeal m I) :
    polynomialTranslation (ofFinite m g) ∈ jetIdeal I := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨fj, rfl⟩ := hg
      change polynomialTranslation (ofFinite m (FiniteJet.jetCoeff m fj.2 fj.1.1)) ∈ _
      rw [FiniteJet.jetCoeff_apply, polynomialTranslation_relationCoeff m fj.2
        (Nat.le_of_lt_succ fj.2.isLt)]
      exact (jetIdeal I).nsmul_mem (ofFinite_mem_jetIdeal _ I _
        (FiniteJet.relationCoeff_mem_jetIdeal _ _ I fj.1.1 fj.1.2 le_rfl)) _
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add, map_add]
      exact (jetIdeal I).add_mem hx hy
  | smul r x hx hdx =>
      rw [smul_eq_mul, map_mul, Derivation.leibniz]
      exact (jetIdeal I).add_mem
        ((jetIdeal I).mul_mem_left _ hdx)
        ((jetIdeal I).mul_mem_right _ (ofFinite_mem_jetIdeal m I x hx))

/-- The infinite Hasse--Schmidt relation ideal is translation stable. -/
theorem polynomialTranslation_stable (I : Ideal (MvPolynomial σ R))
    (f : JetPoly R σ) (hf : f ∈ jetIdeal I) : polynomialTranslation f ∈ jetIdeal I := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨m, g, hg, rfl⟩ := hf
      exact polynomialTranslation_mem_ofFiniteJetIdeal I m g hg
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (jetIdeal I).add_mem hx hy
  | smul r x hx hdx =>
      rw [smul_eq_mul, Derivation.leibniz]
      exact (jetIdeal I).add_mem ((jetIdeal I).mul_mem_left _ hdx)
        ((jetIdeal I).mul_mem_right _ hx)

/-- Translation descended to the represented arc algebra. -/
def translation (I : Ideal (MvPolynomial σ R)) :
    Derivation R (PresentedJet I) (PresentedJet I) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective R (jetIdeal I))
    (d := polynomialTranslation)
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      (polynomialTranslation_stable I f (Ideal.Quotient.eq_zero_iff_mem.mp hf)))

@[simp] theorem translation_mk (I : Ideal (MvPolynomial σ R)) (f : JetPoly R σ) :
    translation I (presentedJetMk I f) = presentedJetMk I (polynomialTranslation f) :=
  Derivation.liftOfSurjective_apply (Ideal.Quotient.mkₐ_surjective R (jetIdeal I))
    (fun g hg => Ideal.Quotient.eq_zero_iff_mem.mpr
      (polynomialTranslation_stable I g (Ideal.Quotient.eq_zero_iff_mem.mp hg))) f

@[simp] theorem translation_X (I : Ideal (MvPolynomial σ R)) (i : σ) (n : ℕ) :
    translation I (presentedJetMk I (MvPolynomial.X (i, n))) =
      (n + 1) • presentedJetMk I (MvPolynomial.X (i, n + 1)) := by
  rw [translation_mk, polynomialTranslation_X, map_nsmul]

/-- The universal arc converts the intrinsic jet translation into formal differentiation. -/
theorem mapSeries_translation_universalArc (I : Ideal (MvPolynomial σ R))
    (a : MvPolynomial σ R ⧸ I) :
    mapSeries (translation I) (universalArc I a) =
      PowerSeries.derivative (PresentedJet I) (universalArc I a) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change mapSeries (translation I)
    (MvPolynomial.aeval (pointSeries I (AlgHom.id R (PresentedJet I))) f) =
      PowerSeries.derivative (PresentedJet I)
        (MvPolynomial.aeval (pointSeries I (AlgHom.id R (PresentedJet I))) f)
  induction f using MvPolynomial.induction_on with
  | C r => simp [PowerSeries.algebraMap_apply]
  | add f g hf hg => simp only [map_add, mapSeries_add, hf, hg]
  | mul_X f i hf =>
      have hi : mapSeries (translation I) (pointSeries I (AlgHom.id R (PresentedJet I)) i) =
          PowerSeries.derivative (PresentedJet I)
            (pointSeries I (AlgHom.id R (PresentedJet I)) i) := by
        apply PowerSeries.ext
        intro n
        simp only [coeff_mapSeries, coeff_pointSeries, AlgHom.id_apply, translation_X,
          PowerSeries.coeff_derivative, nsmul_eq_mul]
        push_cast
        ring
      simp only [map_mul, MvPolynomial.aeval_X, mapSeries_mul, hf, hi,
        Derivation.leibniz, smul_eq_mul]
      ring

/-- The universal Hasse--Schmidt coefficients obey the translation recurrence. -/
theorem translation_coeff_universalArc (I : Ideal (MvPolynomial σ R))
    (a : MvPolynomial σ R ⧸ I) (n : ℕ) :
    translation I (PowerSeries.coeff n (universalArc I a)) =
      (n + 1) • PowerSeries.coeff (n + 1) (universalArc I a) := by
  have h := congrArg (PowerSeries.coeff n) (mapSeries_translation_universalArc I a)
  simpa only [coeff_mapSeries, PowerSeries.coeff_derivative,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- Every induced map of arc algebras preserves the intrinsic translation. -/
theorem arcMap_translation {τ : Type*}
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J))
    (a : PresentedJet I) :
    arcMap I J f (translation I a) = translation J (arcMap I J f a) := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  change arcMap I J f (translation I (presentedJetMk I g)) =
    translation J (arcMap I J f (presentedJetMk I g))
  induction g using MvPolynomial.induction_on with
  | C r =>
      simp only [translation_mk, MvPolynomial.derivation_C, map_zero]
      change 0 = translation J (arcMap I J f (algebraMap R (PresentedJet I) r))
      rw [AlgHom.commutes, Derivation.map_algebraMap]
  | add g h hg hh => simp only [map_add, hg, hh]
  | mul_X g v hg =>
      rcases v with ⟨i, n⟩
      have hi : arcMap I J f (translation I (presentedJetMk I (MvPolynomial.X (i, n)))) =
          translation J (arcMap I J f (presentedJetMk I (MvPolynomial.X (i, n)))) := by
        rw [translation_X, map_nsmul]
        simp only [arcMap, ofArc_mk_X, AlgHom.comp_apply]
        exact (translation_coeff_universalArc J _ n).symm
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hg, hi]

end

section DifferentialEvaluation

variable {A σ : Type*} [CommRing A] [Algebra ℂ A]

/-- The factorial normalization is exactly the ordinary-coefficient translation rule. -/
theorem succ_nsmul_dividedIterate (D : A →ₗ[ℂ] A) (n : ℕ) (a : A) :
    (n + 1) • FiniteJet.dividedIterate D (n + 1) a =
      D (FiniteJet.dividedIterate D n a) := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, FiniteJet.dividedIterate,
    FiniteJet.dividedIterate, map_smul, smul_smul, pow_succ', Module.End.mul_apply]
  congr 1
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

/-- Evaluation by divided iterates intertwines polynomial translation with the target derivation. -/
theorem derivationJetEval_translation (D : A →ₗ[ℂ] A)
    (hleib : ∀ a b : A, D (a * b) = D a * b + a * D b) (hOne : D 1 = 0)
    (x : σ → A) (f : JetPoly ℂ σ) :
    derivationJetEval D x (polynomialTranslation f) = D (derivationJetEval D x f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.derivation_C, map_zero, derivationJetEval,
        MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one, map_smul, hOne, smul_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f v hf =>
      rcases v with ⟨i, n⟩
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, polynomialTranslation_X,
        map_nsmul, derivationJetEval, MvPolynomial.aeval_X] at *
      rw [succ_nsmul_dividedIterate, hf, hleib]
      ring

/-- The canonical map from the represented arc algebra is a differential algebra homomorphism. -/
theorem presentedJetToDifferentialAlgebra_translation (D : A →ₗ[ℂ] A)
    (hleib : ∀ a b : A, D (a * b) = D a * b + a * D b) (hOne : D 1 = 0)
    (x : σ → A) (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom) (a : PresentedJet I) :
    presentedJetToDifferentialAlgebra D hleib hOne x I hI (translation I a) =
      D (presentedJetToDifferentialAlgebra D hleib hOne x I hI a) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change presentedJetToDifferentialAlgebra D hleib hOne x I hI
    (translation I (presentedJetMk I f)) =
      D (presentedJetToDifferentialAlgebra D hleib hOne x I hI (presentedJetMk I f))
  rw [translation_mk, presentedJetToDifferentialAlgebra_mk,
    presentedJetToDifferentialAlgebra_mk]
  exact derivationJetEval_translation D hleib hOne x f

end DifferentialEvaluation
end VOA.InfiniteJet
