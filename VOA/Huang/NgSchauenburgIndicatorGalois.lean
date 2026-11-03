import VOA.Huang.NgSchauenburgGeneralized
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.DirectSum.Module
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # The Galois trace step for generalized indicators

The trace is still the ordinary trace of an operator. We derive a polynomial
expression from its eigenspaces, and use cyclotomic minimal polynomials to
implement the Galois argument without choosing an automorphism of the complex
numbers. Categorical rotation order and the smaller cyclotomic field bound
remain separate obligations when applying this to generalized indicators.
-/
noncomputable section
set_option linter.unusedSectionVars false
namespace VOA.Huang.NgSchauenburg
open Module Polynomial

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- All power traces of a finite-order operator are evaluations of one rational
polynomial at the corresponding powers of a primitive root. -/
theorem exists_trace_power_polynomial (E : Module.End ℂ W) {M : ℕ} (hM : 0 < M)
    (hE : E ^ M = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) :
    ∃ p : ℚ[X], ∀ l : ℕ, LinearMap.trace ℂ W (E ^ l) = aeval (ζ ^ l) p := by
  classical
  letI : NeZero M := ⟨hM.ne'⟩
  have hs : E.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := X ^ M - 1) ((Polynomial.X_pow_sub_one_separable_iff.mpr
      (by exact_mod_cast hM.ne')).squarefree) (by simp [hE])
  let decomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    E.eigenspaces_iSupIndep hs.iSup_eigenspace_eq_top
  let I := (μ : ℂ) × Fin (Module.finrank ℂ (E.eigenspace μ))
  let b : Module.Basis I ℂ W := decomp.collectedBasis fun μ =>
    Module.finBasis ℂ (E.eigenspace μ)
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hv (i : I) : E.HasEigenvector i.1 (b i) :=
    ⟨decomp.collectedBasis_mem _ i, b.ne_zero i⟩
  have hp (i : I) : ∃ k : ℕ, ζ ^ k = i.1 := by
    obtain ⟨k, _, hk⟩ := hζ.eq_pow_of_pow_eq_one
      (eigenvalue_pow_eq_one E hE (Module.End.hasEigenvalue_of_hasEigenvector (hv i)))
    exact ⟨k, hk⟩
  choose k hk using hp
  refine ⟨∑ i, X ^ k i, fun l => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, (hv _).pow_apply,
    map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, map_sum, map_pow, aeval_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hk i, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Conjugate primitive roots preserve every rational polynomial relation. -/
theorem aeval_eq_of_primitive_roots {M : ℕ} (hM : 0 < M) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ M) (hξ : IsPrimitiveRoot ξ M) (p q : ℚ[X])
    (h : aeval ζ p = aeval ζ q) : aeval ξ p = aeval ξ q := by
  have hm : minpoly ℚ ζ = minpoly ℚ ξ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hζ hM).symm.trans
      (Polynomial.cyclotomic_eq_minpoly_rat hξ hM)
  have hd : minpoly ℚ ζ ∣ p - q := minpoly.dvd ℚ ζ (by simp [h])
  rw [hm] at hd
  obtain ⟨r, hr⟩ := hd
  have hz : aeval ξ (p - q) = 0 := by rw [hr, map_mul, minpoly.aeval, zero_mul]
  simpa only [map_sub, sub_eq_zero] using hz

/-- The arithmetic heart of NS Lemma 6.4: if a finite-order trace lies in
`Q[ζ^m]`, every coprime power fixing `ζ^m` fixes that trace. -/
theorem trace_power_eq_of_cyclotomic_mem (E : Module.End ℂ W) {M : ℕ} (hM : 0 < M)
    (hE : E ^ M = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) (m k : ℕ)
    (hk : Nat.Coprime k M) (hfix : (ζ ^ m) ^ k = ζ ^ m)
    (hmem : LinearMap.trace ℂ W E ∈ Algebra.adjoin ℚ ({ζ ^ m} : Set ℂ)) :
    LinearMap.trace ℂ W (E ^ k) = LinearMap.trace ℂ W E := by
  obtain ⟨p, hp⟩ := exists_trace_power_polynomial E hM hE hζ
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hp1 : LinearMap.trace ℂ W E = aeval ζ p := by simpa using hp 1
  have hrel : aeval ζ p = aeval ζ (q.comp (X ^ m)) := by
    simpa [Polynomial.aeval_comp, hp1] using hq.symm
  have hconj := aeval_eq_of_primitive_roots hM hζ (hζ.pow_of_coprime k hk) p
    (q.comp (X ^ m)) hrel
  rw [hp k, hconj]
  have he : (ζ ^ k) ^ m = ζ ^ m := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hfix]
  simpa [Polynomial.aeval_comp, he] using hq

/-- The power `k = 1 mod N` acts trivially on a trace in `Q[ζ^m]`,
where `ζ` has order `m*N`. -/
theorem trace_power_eq_of_modEq (E : Module.End ℂ W) {m N k : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hE : E ^ (m * N) = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (m * N))
    (hk : Nat.Coprime k (m * N)) (hmod : Nat.ModEq N k 1)
    (hmem : LinearMap.trace ℂ W E ∈ Algebra.adjoin ℚ ({ζ ^ m} : Set ℂ)) :
    LinearMap.trace ℂ W (E ^ k) = LinearMap.trace ℂ W E := by
  apply trace_power_eq_of_cyclotomic_mem E (Nat.mul_pos hm hN) hE hζ m k hk _ hmem
  have hroot : (ζ ^ m) ^ N = 1 := by rw [← pow_mul]; exact hζ.pow_eq_one
  simpa using pow_eq_pow_of_modEq hmod hroot

/-- The same Galois argument applies to arbitrary nonnegative powers of the
rotation, so it concerns the second indicator index and not only the first trace. -/
theorem trace_mul_power_eq_of_modEq (E : Module.End ℂ W) {m N k : ℕ} (l : ℕ)
    (hm : 0 < m) (hN : 0 < N) (hE : E ^ (m * N) = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (m * N))
    (hk : Nat.Coprime k (m * N)) (hmod : Nat.ModEq N k 1)
    (hmem : LinearMap.trace ℂ W (E ^ l) ∈ Algebra.adjoin ℚ ({ζ ^ m} : Set ℂ)) :
    LinearMap.trace ℂ W (E ^ (k * l)) = LinearMap.trace ℂ W (E ^ l) := by
  have hel : (E ^ l) ^ (m * N) = 1 := by
    rw [← pow_mul, Nat.mul_comm l, pow_mul, hE, one_pow]
  simpa [← pow_mul, Nat.mul_comm l k] using
    trace_power_eq_of_modEq (E ^ l) hm hN hel hζ hk hmod hmem

open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- Apply the proved Galois step to the actual generalized rotation. The
categorical finite-order identity and the smaller-field bound are explicit;
neither is inferred from ordinary rotation order. -/
theorem generalizedIndicator_mul_eq_of_modEq (F : SphericalFusion C)
    (X : Center C) (V : C) (n l : ℕ) {N k : ℕ} (hN : 0 < N)
    (hrot : (generalizedRotation F.toPivotal X V n).toLinearMap ^ ((n + 1) * N) = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ ((n + 1) * N))
    (hk : Nat.Coprime k ((n + 1) * N)) (hmod : Nat.ModEq N k 1)
    (hmem : generalizedIndicator F.toPivotal X V n l ∈
      Algebra.adjoin ℚ ({ζ ^ (n + 1)} : Set ℂ)) :
    generalizedIndicator F.toPivotal X V n (k * l) =
      generalizedIndicator F.toPivotal X V n l := by
  letI := F.homFinite X.1 (tensorPower V (n + 1))
  exact trace_mul_power_eq_of_modEq _ l (Nat.succ_pos n) hN hrot hζ hk hmod hmem

end VOA.Huang.NgSchauenburg
