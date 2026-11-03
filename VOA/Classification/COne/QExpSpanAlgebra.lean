import VOA.Classification.COne.QExpSpanProducts

/-!
# Polynomial Eisenstein expressions and the eventual-weight alternative

Every polynomial expression in the integral Eisenstein series, with arbitrary
complex polynomial coefficients, has a finite integer coefficient lattice.
Eventual containment of all full-level forms in this algebra suffices for the
weight-two target, by the integral weight-one unit from QExpSpanUnit.

The residual eventual containment is true classically; see the opening of
Section 5 of Khuri-Makdisi, arXiv:0903.1439. It is not proved here. In
particular this file does not presume arithmetic Galois descent.
-/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

set_option maxSynthPendingDepth 3

noncomputable section
namespace VOA.Classification.COne.SSHecke

def HasIntegralCoeffLattice (f : PowerSeries ℂ) : Prop :=
  ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, f.coeff n ∈ L

theorem hasIntegralCoeffLattice_C (c : ℂ) : HasIntegralCoeffLattice (PowerSeries.C c) := by
  refine ⟨Submodule.span ℤ {c}, Submodule.fg_span_singleton c, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp only [PowerSeries.coeff_C]
    exact Submodule.subset_span (Set.mem_singleton c)
  · simp [PowerSeries.coeff_C, hn]

theorem HasIntegralCoeffLattice.add {f g : PowerSeries ℂ}
    (hf : HasIntegralCoeffLattice f) (hg : HasIntegralCoeffLattice g) :
    HasIntegralCoeffLattice (f + g) := by
  obtain ⟨L, hL, hc⟩ := hf
  obtain ⟨K, hK, hd⟩ := hg
  refine ⟨L ⊔ K, hL.sup hK, fun n => ?_⟩
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hc n))
    (Submodule.mem_sup_right (hd n))

theorem HasIntegralCoeffLattice.mul {f g : PowerSeries ℂ}
    (hf : HasIntegralCoeffLattice f) (hg : HasIntegralCoeffLattice g) :
    HasIntegralCoeffLattice (f * g) := by
  obtain ⟨L, hL, hc⟩ := hf
  obtain ⟨K, hK, hd⟩ := hg
  refine ⟨L * K, hL.mul hK, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  exact Submodule.sum_mem _ fun p _ => Submodule.mul_mem_mul (hc p.1) (hd p.2)

/-- Series having finite integer coefficient lattices form a complex algebra.
This does not say that the coefficients themselves are algebraic numbers. -/
def spanIntegralSeries : Subalgebra ℂ (PowerSeries ℂ) where
  carrier := {f | HasIntegralCoeffLattice f}
  zero_mem' := by simpa using hasIntegralCoeffLattice_C 0
  one_mem' := by simpa using hasIntegralCoeffLattice_C 1
  add_mem' := HasIntegralCoeffLattice.add
  mul_mem' := HasIntegralCoeffLattice.mul
  algebraMap_mem' c := hasIntegralCoeffLattice_C c

def spanEisensteinAlgebra {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) : Subalgebra ℂ (PowerSeries ℂ) :=
  Algebra.adjoin ℂ (Set.range (fun i : Fin N × Fin N =>
    qExpansion (N : ℝ) (weightOneModularForm hN hζ
      (fullLevelWeightOneSlash24 N hN h24 ζ hζ) i.1 i.2)))

theorem spanEisensteinAlgebra_le_integralSeries {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    spanEisensteinAlgebra hN h24 hζ ≤ spanIntegralSeries := by
  apply Algebra.adjoin_le
  rintro f ⟨i, rfl⟩
  have hzInt : IsIntegral ℤ ζ :=
    IsIntegral.of_pow hN (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  refine ⟨(Algebra.adjoin ℤ ({ζ} : Set ℂ)).toSubmodule,
    hzInt.fg_adjoin_singleton, fun n => ?_⟩
  rw [weightOneModularForm_coeff]
  exact weightOneIntegralCoeff_mem_int N ζ _ _ n

/-- The entire polynomial algebra, in every degree, has bounded coefficient
lattices. No analytic spanning assertion occurs in this theorem. -/
theorem exists_int_lattice_of_mem_eisensteinAlgebra {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (f : PowerSeries ℂ)
    (hf : f ∈ spanEisensteinAlgebra hN h24 hζ) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, f.coeff n ∈ L :=
  spanEisensteinAlgebra_le_integralSeries hN h24 hζ hf

/-- Exact alternative residual input: sufficiently high weights belong to
the polynomial algebra of the concrete weight-one Eisenstein expansions.
The threshold may depend on the level and the primitive root. -/
def FullLevelEventualProductSpan24 : Prop :=
  ∀ N : ℕ, ∀ hN : 0 < N, ∀ h24 : 24 ∣ N, ∀ ζ : ℂ, ∀ hζ : IsPrimitiveRoot ζ N,
    ∃ B : ℕ, ∀ k : ℕ, B ≤ k →
      ∀ F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ),
        qExpansion (N : ℝ) F ∈ spanEisensteinAlgebra hN h24 hζ

/-- Eventual spanning suffices even for the ordinary integral-lattice target.
The auxiliary weight is chosen above the unknown eventual threshold. -/
theorem qExpPrinciple24_two_of_eventualProductSpan
    (h : FullLevelEventualProductSpan24) : QExpPrinciple24 2 := by
  intro N hN h24 F
  letI : NeZero N := ⟨hN.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  obtain ⟨B, hB⟩ := h N hN h24 _ hζ
  let G := (restrictGamma1ToGamma hN F).mul ((spanWeightOneUnit hN h24).pow B)
  have hw : (2 : ℤ) + (B : ℤ) * 1 = ((B + 2 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨L, hL, hc⟩ := exists_int_lattice_of_mem_eisensteinAlgebra hN h24 hζ _
    (hB (B + 2) (by omega) (G.mcast hw))
  have hd := coeff_mem_of_weightRaise hN h24 (restrictGamma1ToGamma hN F) B L hc
  refine ⟨L, hL, fun n => ?_⟩
  rw [← qExpansion_coeff_nat_mul hN F n]
  exact hd (N * n)

theorem qExpPrinciple24Away_two_of_eventualProductSpan
    (h : FullLevelEventualProductSpan24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_qExpPrinciple24 (qExpPrinciple24_two_of_eventualProductSpan h)

end VOA.Classification.COne.SSHecke
