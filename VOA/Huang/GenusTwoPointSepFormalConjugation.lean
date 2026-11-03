import VOA.Huang.GenusTwoPointSepZeroConjugation

/-!
# Formal commutator flow on linear maps

This is the algebraic ODE used in change of coordinates, with no norm or
convergence assumptions. The two endomorphisms may act on different modules.
Coefficients are normalized by factorials, so the recurrence is the literal
coefficient equation for the first derivative in the flow parameter.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators

section LinearFlow
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Uniqueness of a formal linear initial-value problem in characteristic zero. -/
theorem formal_linearFlow_unique (D : Module.End ℂ M) (f g : ℕ → M)
    (h₀ : f 0 = g 0)
    (hf : ∀ n, ((n + 1 : ℕ) : ℂ) • f (n + 1) = D (f n))
    (hg : ∀ n, ((n + 1 : ℕ) : ℂ) • g (n + 1) = D (g n)) : f = g := by
  funext n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    apply (smul_right_injective M (by exact_mod_cast Nat.succ_ne_zero n :
      ((n + 1 : ℕ) : ℂ) ≠ 0))
    change ((n + 1 : ℕ) : ℂ) • f (n + 1) = ((n + 1 : ℕ) : ℂ) • g (n + 1)
    rw [hf, hg, ih]

/-- The factorial-normalized solution, before any evaluation of the parameter. -/
def linearFlowCoeff (D : Module.End ℂ M) (x : M) (n : ℕ) : M :=
  (n.factorial : ℂ)⁻¹ • (D ^ n) x

@[simp] theorem linearFlowCoeff_zero (D : Module.End ℂ M) (x : M) :
    linearFlowCoeff D x 0 = x := by simp [linearFlowCoeff]

theorem linearFlowCoeff_succ (D : Module.End ℂ M) (x : M) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) • linearFlowCoeff D x (n + 1) = D (linearFlowCoeff D x n) := by
  simp only [linearFlowCoeff, VOA.pow_succ'_apply, map_smul, smul_smul,
    Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  congr 1
  field_simp

theorem linearFlowCoeff_unique (D : Module.End ℂ M) (x : M) (f : ℕ → M)
    (h₀ : f 0 = x)
    (hf : ∀ n, ((n + 1 : ℕ) : ℂ) • f (n + 1) = D (f n)) :
    f = linearFlowCoeff D x :=
  formal_linearFlow_unique D f _ (by simpa using h₀) hf (linearFlowCoeff_succ D x)

theorem linearFlowCoeff_support_finite {D : Module.End ℂ M} (hD : IsLocNilp D) (x : M) :
    (Function.support (linearFlowCoeff D x)).Finite := by
  obtain ⟨N, hN⟩ := hD x
  refine (Set.finite_Iio N).subset fun n hn => ?_
  by_contra h
  exact hn (by rw [linearFlowCoeff, pow_apply_eq_zero_of_le hN (by simpa using h), smul_zero])

/-- For a locally nilpotent operator, evaluating the formal solution is a finite sum. -/
theorem expFun_eq_finsum_linearFlowCoeff {D : Module.End ℂ M} (hD : IsLocNilp D) (x : M) :
    expFun hD x = ∑ᶠ n, linearFlowCoeff D x n := by
  obtain ⟨N, hN⟩ := hD x
  rw [expFun_eq_expSum hD hN, expSum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hn (by rw [linearFlowCoeff, pow_apply_eq_zero_of_le hN (by omega), smul_zero])

end LinearFlow

section CommutatorFlow
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- The infinitesimal conjugation action on rectangular linear maps. -/
def conjugationGenerator (D : Module.End ℂ N) (E : Module.End ℂ M) :
    Module.End ℂ (M →ₗ[ℂ] N) where
  toFun f := D.comp f - f.comp E
  map_add' f g := by ext x; simp; module
  map_smul' c f := by ext x; simp; module

@[simp] theorem conjugationGenerator_apply (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) (x : M) :
    conjugationGenerator D E f x = D (f x) - f (E x) := rfl

/-- The unique formal conjugation coefficients. -/
def conjugationCoeff (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) : ℕ → M →ₗ[ℂ] N :=
  linearFlowCoeff (conjugationGenerator D E) f

@[simp] theorem conjugationCoeff_zero (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) : conjugationCoeff D E f 0 = f :=
  linearFlowCoeff_zero _ _

theorem conjugationCoeff_succ (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) (n : ℕ) (x : M) :
    ((n + 1 : ℕ) : ℂ) • conjugationCoeff D E f (n + 1) x =
      D (conjugationCoeff D E f n x) - conjugationCoeff D E f n (E x) :=
  congrArg (fun g : M →ₗ[ℂ] N => g x) (linearFlowCoeff_succ _ f n)

/-- Formal uniqueness applies to all modes, not merely to scalar matrix coefficients. -/
theorem conjugationCoeff_unique (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) (g : ℕ → M →ₗ[ℂ] N) (h₀ : g 0 = f)
    (hg : ∀ n x, ((n + 1 : ℕ) : ℂ) • g (n + 1) x = D (g n x) - g n (E x)) :
    g = conjugationCoeff D E f := by
  apply linearFlowCoeff_unique _ _ _ h₀
  intro n
  ext x
  exact hg n x

private def leftComposition (D : Module.End ℂ N) : Module.End ℂ (M →ₗ[ℂ] N) :=
  LinearMap.compRight ℂ D

private def rightComposition (E : Module.End ℂ M) : Module.End ℂ (M →ₗ[ℂ] N) where
  toFun f := f.comp E
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem leftComposition_pow (D : Module.End ℂ N) (n : ℕ) (f : M →ₗ[ℂ] N) :
    (leftComposition D ^ n) f = (D ^ n).comp f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VOA.pow_succ'_apply, ih]
    ext x
    exact (VOA.pow_succ'_apply D n (f x)).symm

private theorem rightComposition_pow (E : Module.End ℂ M) (n : ℕ) (f : M →ₗ[ℂ] N) :
    (rightComposition E ^ n) f = f.comp (E ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VOA.pow_succ'_apply, ih]
    ext x
    change f ((E ^ n) (E x)) = f ((E ^ (n + 1)) x)
    rw [pow_succ, Module.End.mul_apply]

/-- The binomial theorem for left and right composition gives the formal sandwich. -/
theorem conjugationCoeff_eq_sum (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) (n : ℕ) (x : M) :
    conjugationCoeff D E f n x =
      ∑ i ∈ Finset.range (n + 1),
        ((i.factorial : ℂ)⁻¹ * ((n - i).factorial : ℂ)⁻¹) •
          (D ^ i) (f (((-E) ^ (n - i)) x)) := by
  have he : conjugationGenerator D E = leftComposition D + rightComposition (-E) := by
    ext f x
    simp [conjugationGenerator, leftComposition, rightComposition, sub_eq_add_neg]
  have hc : Commute (leftComposition (M := M) D) (rightComposition (-E)) := by
    ext f x
    rfl
  unfold conjugationCoeff linearFlowCoeff
  rw [he, hc.add_pow']
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply,
    leftComposition_pow, rightComposition_pow, LinearMap.comp_apply,
    Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [VOA.fact_choose n i (by have := Finset.mem_range.mp hi; omega)]

/-- A finite double family can be summed by total degree. -/
theorem finsum_antidiagonal (f : ℕ × ℕ → N) (hf : (Function.support f).Finite) :
    (∑ᶠ n, ∑ ij ∈ Finset.antidiagonal n, f ij) = ∑ᶠ ij, f ij := by
  classical
  let K := hf.toFinset.sup (fun p => p.1 + p.2) + 1
  have hK : ∀ p ∈ Function.support f, p.1 + p.2 < K := by
    intro p hp
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun p : ℕ × ℕ => p.1 + p.2)
      (hf.mem_toFinset.mpr hp))
  have hs : Function.support (fun n => ∑ ij ∈ Finset.antidiagonal n, f ij) ⊆
      (Finset.range K : Finset ℕ) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hn
    apply Finset.sum_eq_zero
    intro p hp
    by_contra hp0
    have := hK p hp0
    have := Finset.mem_antidiagonal.mp hp
    omega
  rw [finsum_eq_sum_of_support_subset _ hs, VOA.tri_reindex]
  symm
  apply finsum_eq_sum_of_support_subset
  intro p hp
  have := hK p hp
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

private def sandwichTerm (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) (x : M) (p : ℕ × ℕ) : N :=
  linearFlowCoeff D (f (linearFlowCoeff (-E) x p.2)) p.1

private theorem sandwichTerm_finite {D : Module.End ℂ N} {E : Module.End ℂ M}
    (hD : IsLocNilp D) (hE : IsLocNilp E) (f : M →ₗ[ℂ] N) (x : M) :
    (Function.support (sandwichTerm D E f x)).Finite := by
  have hright := linearFlowCoeff_support_finite hE.neg x
  have hs := hright.biUnion fun j _ =>
    (linearFlowCoeff_support_finite hD (f (linearFlowCoeff (-E) x j))).image
      (fun i => (i, j))
  refine hs.subset fun p hp => ?_
  have hj : p.2 ∈ Function.support (linearFlowCoeff (-E) x) := by
    intro hj
    apply hp
    change linearFlowCoeff D (f (linearFlowCoeff (-E) x p.2)) p.1 = 0
    rw [hj, map_zero]
    simp only [linearFlowCoeff, map_zero, smul_zero]
  exact Set.mem_iUnion.mpr ⟨p.2, Set.mem_iUnion.mpr ⟨hj, ⟨p.1, hp, rfl⟩⟩⟩

private theorem conjugationCoeff_eq_antidiagonal (D : Module.End ℂ N) (E : Module.End ℂ M)
    (f : M →ₗ[ℂ] N) (n : ℕ) (x : M) :
    conjugationCoeff D E f n x =
      ∑ p ∈ Finset.antidiagonal n, sandwichTerm D E f x p := by
  rw [conjugationCoeff_eq_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sandwichTerm, linearFlowCoeff, map_smul, smul_smul]

/-- No common nilpotence bound on the whole Hom space is needed: the flow is
pointwise finite after applying any fixed linear map to any fixed vector. -/
theorem conjugationCoeff_support_finite {D : Module.End ℂ N} {E : Module.End ℂ M}
    (hD : IsLocNilp D) (hE : IsLocNilp E) (f : M →ₗ[ℂ] N) (x : M) :
    (Function.support (fun n => conjugationCoeff D E f n x)).Finite := by
  refine ((sandwichTerm_finite hD hE f x).image (fun p => p.1 + p.2)).subset ?_
  intro n hn
  have hne : (∑ p ∈ Finset.antidiagonal n, sandwichTerm D E f x p) ≠ 0 := by
    rwa [← conjugationCoeff_eq_antidiagonal]
  obtain ⟨p, hp, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨p, hp0, Finset.mem_antidiagonal.mp hp⟩

/-- Hadamard's conjugation formula for locally nilpotent operators on algebraic
modules, with all finiteness obligations discharged. -/
theorem expFun_conjugation_eq_finsum {D : Module.End ℂ N} {E : Module.End ℂ M}
    (hD : IsLocNilp D) (hE : IsLocNilp E) (f : M →ₗ[ℂ] N) (x : M) :
    expFun hD (f (expFun hE.neg x)) = ∑ᶠ n, conjugationCoeff D E f n x := by
  have hs := sandwichTerm_finite hD hE f x
  rw [finsum_congr (fun n => conjugationCoeff_eq_antidiagonal D E f n x),
    finsum_antidiagonal _ hs]
  rw [← finsum_comp_equiv (Equiv.prodComm ℕ ℕ)]
  have hswap : (Function.support (fun p : ℕ × ℕ => sandwichTerm D E f x p.swap)).Finite :=
    hs.preimage (Function.Injective.injOn Prod.swap_injective)
  simp only [Equiv.prodComm_apply]
  rw [finsum_curry _ hswap]
  change expLN hD (f (expFun hE.neg x)) = _
  rw [expFun_eq_finsum_linearFlowCoeff hE.neg,
    ← LinearMap.comp_apply (expLN hD) f,
    map_finsum ((expLN hD).comp f) (linearFlowCoeff_support_finite hE.neg x)]
  apply finsum_congr
  intro j
  exact expFun_eq_finsum_linearFlowCoeff hD (f (linearFlowCoeff (-E) x j))

end CommutatorFlow
end VOA.Huang.GenusTwoPoint.Separate
