import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Periodicity of rigid idempotents

Theorem `pow_apply_eq_self_of_rigid` proves periodicity of rigid idempotents in every
finite-dimensional complex vector space with a commutative bilinear product. No associativity, unit,
or VOA structure is assumed.

Generalized eigenspaces are multiplicative. Additive characters of the units yield
derivations, which vanish on rigid idempotents; separating characters then force
all eigenvalues in the support of the idempotent to be roots of unity. A common
power therefore has a locally unipotent orbit. That orbit is a polynomial curve;
differentiating its idempotent identity and applying rigidity at the integer orbit
points proves that the curve is constant. This avoids a logarithm construction.

The separating-character argument uses injectivity of divisible abelian groups.
The local unipotent lemma does not require finite dimension.
-/

namespace VOA.Moonshine.ConwayNorton.M8

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The product rule for a shifted multiplicative endomorphism. -/
theorem mul_spectral_shift (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (A : Module.End ℂ B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (l μ : ℂ) (x y : B) :
    (A - (l * μ) • 1) (mul x y) =
      mul ((A - l • 1) x) (A y) + l • mul x ((A - μ • 1) y) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    hA, map_sub, map_smul]
  module

/-- Multiplying generalized eigenvectors adds their nilpotence bounds. -/
theorem genEigenspace_mul_mem (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (A : Module.End ℂ B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (l μ : ℂ) (n m : ℕ) {x y : B}
    (hx : x ∈ A.genEigenspace l n) (hy : y ∈ A.genEigenspace μ m) :
    mul x y ∈ A.genEigenspace (l * μ) (n + m : ℕ) := by
  simp only [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx hy ⊢
  induction n generalizing m x y with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ n ihn =>
    induction m generalizing x y with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hy
      simp [hy]
    | succ m ihm =>
      have hx' : ((A - l • 1) ^ n) ((A - l • 1) x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      have hy' : ((A - μ • 1) ^ m) ((A - μ • 1) y) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hy
      have hAy : ((A - μ • 1) ^ (m + 1)) (A y) = 0 := by
        have hc : Commute A (A - μ • 1) :=
          (Commute.refl A).sub_right (Algebra.commute_algebraMap_right μ A)
        rw [← Module.End.mul_apply, ← (hc.pow_right (m + 1)).eq,
          Module.End.mul_apply, hy, map_zero]
      have hleft := ihn (m + 1) hx' hAy
      have hright := ihm hx hy'
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega,
        pow_succ, Module.End.mul_apply, mul_spectral_shift mul A hA,
        map_add, map_smul, hleft]
      have heq : n + 1 + m = n + (m + 1) := by omega
      rw [heq] at hright
      rw [hright, smul_zero, add_zero]

/-- Maximal generalized eigenspaces multiply according to their eigenvalues.
This does not require finite dimension or commutativity of the product. -/
theorem maxGenEigenspace_mul_le (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (A : Module.End ℂ B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (l μ : ℂ) {x y : B}
    (hx : x ∈ A.maxGenEigenspace l) (hy : y ∈ A.maxGenEigenspace μ) :
    mul x y ∈ A.maxGenEigenspace (l * μ) := by
  obtain ⟨n, hn⟩ := (A.mem_maxGenEigenspace l x).mp hx
  obtain ⟨m, hm⟩ := (A.mem_maxGenEigenspace μ y).mp hy
  apply A.genEigenspace_le_maximal (l * μ) (n + m)
  exact genEigenspace_mul_mem mul A hA l μ n m
    (Module.End.mem_genEigenspace_nat.mpr hn) (Module.End.mem_genEigenspace_nat.mpr hm)

/-- Every derivation annihilates a rigid idempotent in the normalization `e * e = 2e`. -/
theorem derivation_apply_eq_zero_of_rigid (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x) (D : Module.End ℂ B)
    (hD : ∀ x y, D (mul x y) = mul (D x) y + mul x (D y))
    (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0) : D e = 0 := by
  apply hrig
  have h := hD e e
  rw [he, map_smul, hcomm (D e) e, ← two_smul ℂ (mul e (D e))] at h
  exact (smul_right_injective B (by norm_num : (2 : ℂ) ≠ 0)) h.symm

/-- An infinite-order element in any commutative group
admits a complex-valued additive character taking the value one. -/
theorem exists_addChar_eq_one_of_not_isOfFinOrder {G : Type*} [CommGroup G]
    (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ φ : Additive G →+ ℂ, φ (Additive.ofMul g) = 1 := by
  let f : ℤ →+ Additive G :=
    { toFun := fun n => n • Additive.ofMul g
      map_zero' := zero_zsmul _
      map_add' := fun n m => add_zsmul _ _ _ }
  have hf : Function.Injective f := by
    intro n m h
    exact (injective_zpow_iff_not_isOfFinOrder.mpr hg) (congrArg Additive.toMul h)
  obtain ⟨φ, hφ⟩ := (Module.Baer.of_divisible ℂ).extension_property_addMonoidHom
    f hf (Int.castAddHom ℂ)
  refine ⟨φ, ?_⟩
  have h := DFunLike.congr_fun hφ 1
  simpa [f] using h

/-- The separating character in the form used in the periodicity blueprint. -/
theorem exists_addChar_ne_zero_of_not_isOfFinOrder (l : ℂˣ)
    (hl : ¬ IsOfFinOrder l) :
    ∃ φ : Additive ℂˣ →+ ℂ, φ (Additive.ofMul l) ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_addChar_eq_one_of_not_isOfFinOrder l hl
  exact ⟨φ, by rw [hφ]; exact one_ne_zero⟩

/-- An invertible operator has no generalized zero-eigenvectors. -/
theorem mem_maxGenEigenspace_zero_eq_zero (A : B ≃ₗ[ℂ] B) {x : B}
    (hx : x ∈ Module.End.maxGenEigenspace (A : Module.End ℂ B) 0) : x = 0 := by
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace (A : Module.End ℂ B) 0 x).mp hx
  simp only [zero_smul, sub_zero, Module.End.pow_apply] at hn
  exact (A.injective.iterate n) (hn.trans (by simp))

section SpectralDecomposition

variable [FiniteDimensional ℂ B]

/-- The canonical decomposition into maximal generalized eigenspaces. -/
noncomputable def spectralDecomposition (A : Module.End ℂ B) :
    B ≃ₗ[ℂ] DirectSum ℂ (fun l => A.maxGenEigenspace l) := by
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap A.maxGenEigenspace)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      A.independent_maxGenEigenspace A.iSup_maxGenEigenspace_eq_top)).symm

/-- Decomposing a vector already in one summand gives its single component. -/
theorem spectralDecomposition_apply_of_mem (A : Module.End ℂ B) (l : ℂ)
    {x : B} (hx : x ∈ A.maxGenEigenspace l) :
    spectralDecomposition A x = DirectSum.lof ℂ ℂ
      (fun t => A.maxGenEigenspace t) l ⟨x, hx⟩ := by
  classical
  apply (spectralDecomposition A).symm.injective
  simp [spectralDecomposition]

/-- The operator acting by an arbitrary scalar on each generalized eigenspace. -/
noncomputable def spectralWeight (A : Module.End ℂ B) (c : ℂ → ℂ) : Module.End ℂ B := by
  classical
  exact (DirectSum.toModule ℂ ℂ B (fun l => c l • (A.maxGenEigenspace l).subtype)).comp
    (spectralDecomposition A).toLinearMap

/-- The defining action of the spectral weight operator. -/
theorem spectralWeight_apply_of_mem (A : Module.End ℂ B) (c : ℂ → ℂ) (l : ℂ)
    {x : B} (hx : x ∈ A.maxGenEigenspace l) : spectralWeight A c x = c l • x := by
  classical
  simp [spectralWeight, spectralDecomposition_apply_of_mem A l hx]

/-- Weights additive on nonzero eigenvalues define a derivation. -/
theorem spectralWeight_mul_of_additive (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (c : ℂ → ℂ) (hc : ∀ l μ, l ≠ 0 → μ ≠ 0 → c (l * μ) = c l + c μ)
    (x y : B) :
    spectralWeight A c (mul x y) =
      mul (spectralWeight A c x) y + mul x (spectralWeight A c y) := by
  have hall (z : B) : z ∈ ⨆ l, Module.End.maxGenEigenspace (A : Module.End ℂ B) l := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  revert y
  refine Submodule.iSup_induction _ (motive := fun x => ∀ y,
    spectralWeight A c (mul x y) =
      mul (spectralWeight A c x) y + mul x (spectralWeight A c y)) (hall x) ?_ ?_ ?_
  · intro l x hx y
    refine Submodule.iSup_induction _ (motive := fun y =>
      spectralWeight A c (mul x y) =
        mul (spectralWeight A c x) y + mul x (spectralWeight A c y)) (hall y) ?_ ?_ ?_
    · intro μ y hy
      by_cases hl : l = 0
      · subst l
        rw [mem_maxGenEigenspace_zero_eq_zero A hx]
        simp
      by_cases hμ : μ = 0
      · subst μ
        rw [mem_maxGenEigenspace_zero_eq_zero A hy]
        simp
      rw [spectralWeight_apply_of_mem _ c (l * μ) (maxGenEigenspace_mul_le mul A hA l μ hx hy),
        spectralWeight_apply_of_mem _ c l hx, spectralWeight_apply_of_mem _ c μ hy,
        hc l μ hl hμ]
      simp [add_smul]
    · simp
    · intro y z ihy ihz
      simp only [map_add, ihy, ihz]
      module
  · intro y
    simp
  · intro x z ihx ihz y
    simp only [map_add, LinearMap.add_apply, ihx, ihz]
    module

/-- Extend a character of the units to a weight function, with value zero at zero. -/
noncomputable def unitCharacterValue (φ : Additive ℂˣ →+ ℂ) (l : ℂ) : ℂ :=
  if h : l = 0 then 0 else φ (Additive.ofMul (Units.mk0 l h))

/-- A unit character gives weights additive on products of nonzero scalars. -/
theorem unitCharacterValue_mul (φ : Additive ℂˣ →+ ℂ) (l μ : ℂ)
    (hl : l ≠ 0) (hμ : μ ≠ 0) :
    unitCharacterValue φ (l * μ) = unitCharacterValue φ l + unitCharacterValue φ μ := by
  simp only [unitCharacterValue, dif_neg hl, dif_neg hμ, dif_neg (mul_ne_zero hl hμ)]
  have hu : Units.mk0 (l * μ) (mul_ne_zero hl hμ) = Units.mk0 l hl * Units.mk0 μ hμ := by
    ext
    rfl
  rw [hu]
  exact φ.map_add _ _

/-- The character derivation on the generalized eigenspace decomposition. -/
noncomputable def characterDerivation (A : Module.End ℂ B) (φ : Additive ℂˣ →+ ℂ) :
    Module.End ℂ B := spectralWeight A (unitCharacterValue φ)

/-- The character operator satisfies the Leibniz rule. -/
theorem characterDerivation_mul (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (φ : Additive ℂˣ →+ ℂ) (x y : B) :
    characterDerivation A φ (mul x y) =
      mul (characterDerivation A φ x) y + mul x (characterDerivation A φ y) :=
  spectralWeight_mul_of_additive mul A hA _ (unitCharacterValue_mul φ) x y

/-- Every character derivation annihilates a rigid idempotent. -/
theorem characterDerivation_apply_eq_zero_of_rigid (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (φ : Additive ℂˣ →+ ℂ) (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0) : characterDerivation A φ e = 0 :=
  derivation_apply_eq_zero_of_rigid mul hcomm _ (characterDerivation_mul mul A hA φ) e he hrig

/-- Spectral weights act componentwise on the canonical decomposition. -/
theorem spectralDecomposition_spectralWeight (A : Module.End ℂ B) (c : ℂ → ℂ) (x : B) :
    spectralDecomposition A (spectralWeight A c x) =
      DirectSum.lmap (fun l => c l • (LinearMap.id : A.maxGenEigenspace l →ₗ[ℂ]
        A.maxGenEigenspace l)) (spectralDecomposition A x) := by
  classical
  have hx : x ∈ ⨆ l, A.maxGenEigenspace l := by
    rw [A.iSup_maxGenEigenspace_eq_top]
    trivial
  refine Submodule.iSup_induction _ (motive := fun x =>
    spectralDecomposition A (spectralWeight A c x) =
      DirectSum.lmap (fun l => c l • (LinearMap.id : A.maxGenEigenspace l →ₗ[ℂ]
        A.maxGenEigenspace l)) (spectralDecomposition A x)) hx ?_ ?_ ?_
  · intro l x hx
    rw [spectralWeight_apply_of_mem A c l hx, map_smul,
      spectralDecomposition_apply_of_mem A l hx, DirectSum.lmap_lof]
    exact (map_smul (DirectSum.lof ℂ ℂ (fun t => A.maxGenEigenspace t) l)
      (c l) ⟨x, hx⟩).symm
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- The character annihilation statement on each individual component of `e`. -/
theorem character_smul_component_eq_zero (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (φ : Additive ℂˣ →+ ℂ) (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0) (l : ℂ) :
    unitCharacterValue φ l • (spectralDecomposition A e l) = 0 := by
  have h := spectralDecomposition_spectralWeight (A : Module.End ℂ B) (unitCharacterValue φ) e
  change spectralDecomposition A (characterDerivation A φ e) = _ at h
  rw [characterDerivation_apply_eq_zero_of_rigid mul hcomm A hA φ e he hrig, map_zero] at h
  have hl := congrArg (fun z => z l) h
  simpa using hl.symm

/-- Every nonzero spectral component of a rigid idempotent has a root-of-unity eigenvalue. -/
theorem isOfFinOrder_of_rigid_component (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0)
    (l : ℂ) (hl : spectralDecomposition A e l ≠ 0) : IsOfFinOrder l := by
  have hl0 : l ≠ 0 := by
    intro h
    subst l
    apply hl
    apply Subtype.ext
    exact mem_maxGenEigenspace_zero_eq_zero A (spectralDecomposition A e 0).property
  by_contra hfin
  have hu : ¬ IsOfFinOrder (Units.mk0 l hl0) := by
    intro h
    obtain ⟨n, hn, hp⟩ := h.exists_pow_eq_one
    apply hfin
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg (fun z : ℂˣ => (z : ℂ)) hp⟩
  obtain ⟨φ, hφ⟩ := exists_addChar_eq_one_of_not_isOfFinOrder (Units.mk0 l hl0) hu
  have h := character_smul_component_eq_zero mul hcomm A hA φ e he hrig l
  simp only [unitCharacterValue, dif_neg hl0, hφ, one_smul] at h
  exact hl h

/-- The semisimple operator associated with the generalized eigenspace decomposition. -/
noncomputable def semisimplePart (A : Module.End ℂ B) : Module.End ℂ B :=
  spectralWeight A id

/-- The spectral semisimple part preserves the original bilinear product. -/
theorem semisimplePart_mul (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (A : Module.End ℂ B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (x y : B) : semisimplePart A (mul x y) = mul (semisimplePart A x) (semisimplePart A y) := by
  have hall (z : B) : z ∈ ⨆ l, A.maxGenEigenspace l := by
    rw [A.iSup_maxGenEigenspace_eq_top]
    trivial
  revert y
  refine Submodule.iSup_induction _ (motive := fun x => ∀ y,
    semisimplePart A (mul x y) = mul (semisimplePart A x) (semisimplePart A y))
    (hall x) ?_ ?_ ?_
  · intro l x hx y
    refine Submodule.iSup_induction _ (motive := fun y =>
      semisimplePart A (mul x y) = mul (semisimplePart A x) (semisimplePart A y))
      (hall y) ?_ ?_ ?_
    · intro μ y hy
      unfold semisimplePart
      rw [spectralWeight_apply_of_mem A id (l * μ) (maxGenEigenspace_mul_le mul A hA l μ hx hy),
        spectralWeight_apply_of_mem A id l hx, spectralWeight_apply_of_mem A id μ hy]
      simp [smul_smul, mul_comm]
    · simp
    · intro y z ihy ihz
      simp only [map_add, ihy, ihz]
  · intro y
    simp
  · intro x z ihx ihz y
    simp only [map_add, LinearMap.add_apply, ihx, ihz]

/-- Powers of spectral weights also act componentwise. -/
theorem spectralWeight_pow_component (A : Module.End ℂ B) (c : ℂ → ℂ)
    (n : ℕ) (x : B) (l : ℂ) :
    spectralDecomposition A ((spectralWeight A c ^ n) x) l =
      c l ^ n • spectralDecomposition A x l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, spectralDecomposition_spectralWeight]
    simp only [DirectSum.lmap_apply, LinearMap.smul_apply, LinearMap.id_apply, ih,
      smul_smul, pow_succ']

/-- The semisimple part has a positive power fixing every rigid idempotent. -/
theorem semisimplePart_pow_apply_eq_self_of_rigid (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0) :
    ∃ K : ℕ, 1 ≤ K ∧ (semisimplePart (A : Module.End ℂ B) ^ K) e = e := by
  classical
  let s := (spectralDecomposition A e).support
  let K := ∏ l ∈ s, orderOf l
  have hpos : 0 < K := by
    apply Finset.prod_pos
    intro l hl
    exact (isOfFinOrder_of_rigid_component mul hcomm A hA e he hrig l
      (DFinsupp.mem_support_iff.mp hl)).orderOf_pos
  refine ⟨K, hpos, ?_⟩
  apply (spectralDecomposition (A : Module.End ℂ B)).injective
  ext l
  rw [semisimplePart, spectralWeight_pow_component]
  by_cases hl : l ∈ s
  · have hp : l ^ K = 1 := orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem orderOf hl)
    simp only [id_eq, hp, one_smul]
  · have hz : spectralDecomposition A e l = 0 := DFinsupp.notMem_support_iff.mp hl
    simp [hz]

end SpectralDecomposition

section PolynomialCurves

variable {ι : Type*} [Fintype ι]

/-- Evaluation of a polynomial curve presented by finitely many vector coefficients. -/
noncomputable def polynomialCurve (p : ι → Polynomial ℂ) (v : ι → B) (t : ℂ) : B :=
  ∑ i, (p i).eval t • v i

private noncomputable def curveLinearPolynomial (p : ι → Polynomial ℂ) (v : ι → B)
    (f : Module.Dual ℂ B) : Polynomial ℂ := ∑ i, Polynomial.C (f (v i)) * p i

private noncomputable def curvePairPolynomial (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (p q : ι → Polynomial ℂ) (v : ι → B) (f : Module.Dual ℂ B) : Polynomial ℂ :=
  ∑ i, ∑ j, Polynomial.C (f (mul (v i) (v j))) * p i * q j

private theorem curveLinearPolynomial_eval (p : ι → Polynomial ℂ) (v : ι → B)
    (f : Module.Dual ℂ B) (t : ℂ) :
    (curveLinearPolynomial p v f).eval t = f (polynomialCurve p v t) := by
  simp [curveLinearPolynomial, polynomialCurve, Polynomial.eval_finsetSum, map_sum, mul_comm]

private theorem curvePairPolynomial_eval (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (p q : ι → Polynomial ℂ) (v : ι → B) (f : Module.Dual ℂ B) (t : ℂ) :
    (curvePairPolynomial mul p q v f).eval t =
      f (mul (polynomialCurve p v t) (polynomialCurve q v t)) := by
  simp only [curvePairPolynomial, mul_comm, mul_left_comm, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, polynomialCurve, map_sum, map_smul, LinearMap.coe_sum,
    LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem curveLinearPolynomial_derivative (p : ι → Polynomial ℂ) (v : ι → B)
    (f : Module.Dual ℂ B) :
    (curveLinearPolynomial p v f).derivative =
      curveLinearPolynomial (fun i => (p i).derivative) v f := by
  simp [curveLinearPolynomial]

private theorem curvePairPolynomial_derivative (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (p q : ι → Polynomial ℂ) (v : ι → B) (f : Module.Dual ℂ B) :
    (curvePairPolynomial mul p q v f).derivative =
      curvePairPolynomial mul (fun i => (p i).derivative) q v f +
      curvePairPolynomial mul p (fun i => (q i).derivative) v f := by
  simp [curvePairPolynomial, Polynomial.derivative_mul, Finset.sum_add_distrib]

private theorem rigidCurve_poly_eq_zero_of_nat_eval (p : Polynomial ℂ)
    (h : ∀ n : ℕ, p.eval (n : ℂ) = 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  exact (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono
    (by rintro _ ⟨n, rfl⟩; exact h n)

/-- A polynomial curve whose values at natural numbers are rigid idempotents is constant. -/
theorem polynomialCurve_eq_zero_value_of_rigid (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x) (p : ι → Polynomial ℂ) (v : ι → B)
    (he : ∀ n : ℕ, mul (polynomialCurve p v n) (polynomialCurve p v n) =
      (2 : ℂ) • polynomialCurve p v n)
    (hrig : ∀ (n : ℕ) y, mul (polynomialCurve p v n) y = y → y = 0)
    (t : ℂ) : polynomialCurve p v t = polynomialCurve p v 0 := by
  let dp := fun i => (p i).derivative
  have hder (n : ℕ) : polynomialCurve dp v n = 0 := by
    apply hrig n
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro f
    have hid : curvePairPolynomial mul p p v f = (2 : ℂ) • curveLinearPolynomial p v f := by
      apply sub_eq_zero.mp
      apply rigidCurve_poly_eq_zero_of_nat_eval
      intro k
      simp only [Polynomial.eval_sub, Polynomial.eval_smul, curvePairPolynomial_eval,
        curveLinearPolynomial_eval, he k, map_smul, sub_self]
    have hd := congrArg (fun q : Polynomial ℂ => q.derivative.eval (n : ℂ)) hid
    dsimp only at hd
    rw [curvePairPolynomial_derivative, Polynomial.eval_add,
      curvePairPolynomial_eval, curvePairPolynomial_eval, Polynomial.derivative_smul,
      Polynomial.eval_smul, curveLinearPolynomial_derivative, curveLinearPolynomial_eval] at hd
    change f (mul (polynomialCurve dp v n) (polynomialCurve p v n)) +
      f (mul (polynomialCurve p v n) (polynomialCurve dp v n)) =
        (2 : ℂ) • f (polynomialCurve dp v n) at hd
    rw [hcomm (polynomialCurve dp v n), ← two_smul ℂ] at hd
    rw [map_sub]
    exact sub_eq_zero.mpr ((smul_right_injective ℂ (by norm_num : (2 : ℂ) ≠ 0)) hd)
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  have hd : (curveLinearPolynomial p v f).derivative = 0 := by
    rw [curveLinearPolynomial_derivative]
    apply rigidCurve_poly_eq_zero_of_nat_eval
    intro n
    rw [curveLinearPolynomial_eval]
    change f (polynomialCurve dp v n) = 0
    rw [hder n, map_zero]
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  rw [map_sub, ← curveLinearPolynomial_eval, ← curveLinearPolynomial_eval, hc]
  simp

end PolynomialCurves

/-- Powers of a multiplicative linear automorphism preserve the product. -/
theorem equiv_pow_mul (mul : B →ₗ[ℂ] B →ₗ[ℂ] B) (A : B ≃ₗ[ℂ] B)
    (hA : ∀ x y, A (mul x y) = mul (A x) (A y)) (n : ℕ) (x y : B) :
    (A ^ n) (mul x y) = mul ((A ^ n) x) ((A ^ n) y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', LinearEquiv.mul_apply, ih, hA]

/-- Rigidity is invariant under a multiplicative linear automorphism. -/
theorem rigid_image (mul : B →ₗ[ℂ] B →ₗ[ℂ] B) (A : B ≃ₗ[ℂ] B)
    (hA : ∀ x y, A (mul x y) = mul (A x) (A y)) (e : B)
    (hrig : ∀ y, mul e y = y → y = 0) : ∀ y, mul (A e) y = y → y = 0 := by
  intro y hy
  have h : mul e (A.symm y) = A.symm y := by
    apply A.injective
    simpa only [hA, A.apply_symm_apply] using hy
  have hz := hrig (A.symm y) h
  have := congrArg A hz
  simpa using this

/-- A locally unipotent orbit is represented by its finite binomial polynomial. -/
theorem unipotentOrbit_eq_polynomialCurve (U : Module.End ℂ B) (e : B) (d : ℕ)
    (hd : ((U - 1) ^ d) e = 0) (k : ℕ) :
    polynomialCurve
      (fun j : Fin d => ((j.val.factorial : ℂ)⁻¹) • descPochhammer ℂ j.val)
      (fun j : Fin d => ((U - 1) ^ j.val) e) (k : ℂ) = (U ^ k) e := by
  have hzero (j : ℕ) (hj : d ≤ j) : ((U - 1) ^ j) e = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm, pow_add, Module.End.mul_apply, hd, map_zero]
  have hexp : (U ^ k) e =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • ((U - 1) ^ j) e := by
    have hbin := (Commute.one_right (U - 1)).add_pow k
    rw [sub_add_cancel] at hbin
    rw [hbin]
    simp [Finset.sum_apply, Module.End.mul_apply, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
  rw [hexp]
  unfold polynomialCurve
  simp only [Polynomial.eval_smul, smul_eq_mul]
  have hp (j : Fin d) :
      (j.val.factorial : ℂ)⁻¹ * (descPochhammer ℂ j.val).eval (k : ℂ) =
        (k.choose j.val : ℂ) := by
    rw [Nat.cast_choose_eq_descPochhammer_div, div_eq_mul_inv, mul_comm]
  simp_rw [hp]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (k.choose j : ℂ) • ((U - 1) ^ j) e)]
  by_cases hdk : d ≤ k + 1
  · apply Finset.sum_subset (Finset.range_mono hdk)
    intro j _ hj
    rw [hzero j (by simpa using hj), smul_zero]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ d))
    intro j _ hj
    have hkj : k < j := by simpa using hj
    rw [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, zero_smul]

/-- A unipotent orbit of a rigid idempotent is fixed. -/
theorem unipotent_fix_of_rigid (mul : B →ₗ[ℂ] B →ₗ[ℂ] B)
    (hcomm : ∀ x y, mul x y = mul y x)
    (U : B ≃ₗ[ℂ] B) (hU : ∀ x y, U (mul x y) = mul (U x) (U y))
    (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0)
    (huni : ∃ d : ℕ, (((U : Module.End ℂ B) - 1) ^ d) e = 0) : U e = e := by
  obtain ⟨d, hd⟩ := huni
  let p := fun j : Fin d => ((j.val.factorial : ℂ)⁻¹) • descPochhammer ℂ j.val
  let v := fun j : Fin d => (((U : Module.End ℂ B) - 1) ^ j.val) e
  have horbit (k : ℕ) : polynomialCurve p v (k : ℂ) = (U ^ k) e := by
    rw [unipotentOrbit_eq_polynomialCurve U e d hd k]
    simp only [Module.End.pow_apply, LinearEquiv.pow_apply]
    rfl
  have hcurve := polynomialCurve_eq_zero_value_of_rigid mul hcomm p v
    (fun k => by rw [horbit k, ← equiv_pow_mul mul U hU, he, map_smul])
    (fun k => by rw [horbit k]; exact rigid_image mul (U ^ k) (equiv_pow_mul mul U hU k) e hrig)
    1
  simpa only [← Nat.cast_one (R := ℂ), ← Nat.cast_zero (R := ℂ), horbit, pow_one, pow_zero] using
    hcurve

/-- Taking a power of an operator raises each generalized eigenvalue to that power. -/
theorem maxGenEigenspace_pow_mem (A : Module.End ℂ B) (l : ℂ) (k : ℕ) {x : B}
    (hx : x ∈ A.maxGenEigenspace l) : x ∈ (A ^ k).maxGenEigenspace (l ^ k) := by
  obtain ⟨n, hn⟩ := (A.mem_maxGenEigenspace l x).mp hx
  have hc : Commute A (l • (1 : Module.End ℂ B)) := Algebra.commute_algebraMap_right l A
  let Q := ∑ i ∈ Finset.range k, A ^ i * (l • (1 : Module.End ℂ B)) ^ (k - 1 - i)
  have hfactor : A ^ k - l ^ k • 1 = Q * (A - l • 1) := by
    simpa only [Q, smul_pow, one_pow] using (hc.geom_sum₂_mul k).symm
  have hcomm : Commute Q (A - l • 1) := by
    apply Commute.sum_left
    intro i _
    exact (((Commute.refl A).sub_right hc).pow_left i).mul_left
      ((hc.symm.sub_right (Commute.refl _)).pow_left (k - 1 - i))
  apply ((A ^ k).mem_maxGenEigenspace (l ^ k) x).mpr
  refine ⟨n, ?_⟩
  rw [hfactor, hcomm.mul_pow, Module.End.mul_apply, hn, map_zero]

/-- Every rigid idempotent in a finite-dimensional commutative complex
bilinear algebra is periodic under every multiplicative linear automorphism. -/
theorem pow_apply_eq_self_of_rigid [FiniteDimensional ℂ B]
    (mul : B →ₗ[ℂ] B →ₗ[ℂ] B) (hcomm : ∀ x y, mul x y = mul y x)
    (A : B ≃ₗ[ℂ] B) (hA : ∀ x y, A (mul x y) = mul (A x) (A y))
    (e : B) (he : mul e e = (2 : ℂ) • e)
    (hrig : ∀ y, mul e y = y → y = 0) :
    ∃ K : ℕ, 1 ≤ K ∧ (A ^ K) e = e := by
  classical
  let s := (spectralDecomposition A e).support
  let K := ∏ l ∈ s, orderOf l
  have hpos : 0 < K := by
    apply Finset.prod_pos
    intro l hl
    exact (isOfFinOrder_of_rigid_component mul hcomm A hA e he hrig l
      (DFinsupp.mem_support_iff.mp hl)).orderOf_pos
  have hroot (l : ℂ) (hl : l ∈ s) : l ^ K = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem orderOf hl)
  have hsum : (∑ l ∈ s, ((spectralDecomposition A e l :
      Module.End.maxGenEigenspace (A : Module.End ℂ B) l) : B)) = e := by
    change (spectralDecomposition A e).sum (fun _ z => (z : B)) = e
    rw [← DirectSum.coeLinearMap_eq_dfinsuppSum]
    exact (spectralDecomposition (A : Module.End ℂ B)).symm_apply_apply e
  have hmem : e ∈ Module.End.maxGenEigenspace ((A : Module.End ℂ B) ^ K) 1 := by
    rw [← hsum]
    apply Submodule.sum_mem
    intro l hl
    have h := maxGenEigenspace_pow_mem (A : Module.End ℂ B) l K
      (spectralDecomposition A e l).property
    rwa [hroot l hl] at h
  have hpow : ((A ^ K : B ≃ₗ[ℂ] B) : Module.End ℂ B) = (A : Module.End ℂ B) ^ K := by
    ext x
    change (A ^ K) x = ((A : Module.End ℂ B) ^ K) x
    simp only [Module.End.pow_apply, LinearEquiv.pow_apply]
    rfl
  refine ⟨K, hpos, unipotent_fix_of_rigid mul hcomm (A ^ K)
    (equiv_pow_mul mul A hA K) e he hrig ?_⟩
  rw [hpow]
  simpa only [one_smul] using
    (Module.End.mem_maxGenEigenspace ((A : Module.End ℂ B) ^ K) 1 e).mp hmem

end VOA.Moonshine.ConwayNorton.M8
