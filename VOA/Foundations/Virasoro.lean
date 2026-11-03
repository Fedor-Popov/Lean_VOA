/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Lie.Extension
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The Witt and Virasoro algebras  (Gannon §3.1.1–3.1.2, pp. 176–187)

The conformal symmetry algebra of a VOA. A VOA carries a representation of the Virasoro
algebra via the modes `Lₙ = ω₍ₙ₊₁₎` of the conformal vector (axiom VOA1).

* **Witt algebra** `Witt`: carrier `ℤ →₀ ℂ` (finite combinations of `ℓₙ`), bracket
  `[ℓₘ, ℓₙ] = (m - n) ℓ_{m+n}`. Rather than verify the Jacobi identity by hand we realize
  `Witt` *faithfully* as operators on `ℤ →₀ ℂ` via `ℓₙ · z^k = -k z^{k+n}` (i.e.
  `-z^{n+1}∂_z`); the bracket is then the operator commutator, so the Lie axioms transfer
  for free from the associative ring `End ℂ (ℤ →₀ ℂ)`.
* **Virasoro algebra** `Virasoro`: the central extension of `Witt` by the Gel'fand–Fuks
  cocycle `ψ(ℓₘ,ℓₙ) = (1/12)(m³-m)δ_{m+n,0}`, built with Mathlib's
  `LieAlgebra.ofTwoCocycle`. Bracket (Gannon eq. 3.1.5)
  `[Lₘ, Lₙ] = (m - n) L_{m+n} + (C/12)(m³ - m) δ_{m+n,0}`.

A `Virasoro`-module on which `C` acts as `c · id` has **central charge** `c` (`VirRep`).

## Dependencies
Mathlib (`LieAlgebra`, `ofTwoCocycle`, `Finsupp`, `Complex`).

## Status
Complete & `sorry`-free / axiom-free. The Witt algebra (faithful operator
realization, Jacobi for free), the Gel'fand–Fuks cocycle (alternating + cocycle condition
proved), the `Virasoro` central extension via `LieAlgebra.ofTwoCocycle` with its
`LieRing`/`LieAlgebra ℂ` instances, `virasoro_bracket` (eq. 3.1.5), and `VirRep`.

Stretch goal (not done): uniqueness of the central extension, `H²(𝔚;ℂ) ≅ ℂ`.

## References
* Gannon §3.1.1–3.1.2, eq. (3.1.5); Kac–Raina; Kac, *VA for Beginners* §1.3.
-/

namespace VOA

open Finsupp

/-! ## The Witt algebra as operators on `ℤ →₀ ℂ` -/

/-- The Witt algebra `𝔚`, carrier `ℤ →₀ ℂ`: finite `ℂ`-combinations of the generators
`ℓₙ` (Gannon §3.1.1). A reducible synonym for `ℤ →₀ ℂ` (so the `Finsupp` API applies
directly); its Lie structure is the Witt bracket defined below. -/
abbrev Witt : Type := ℤ →₀ ℂ

namespace Witt

/-- The generator `ℓₙ = -z^{n+1} d/dz` of the Witt algebra. -/
noncomputable def gen (n : ℤ) : Witt := single n 1

/-- The operator `ℓₙ = -z^{n+1}∂_z` acting on `ℂ[z^±] = ℤ →₀ ℂ`: `ℓₙ · z^k = -k z^{k+n}`. -/
noncomputable def op (n : ℤ) : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.lsum ℂ fun k => LinearMap.toSpanSingleton ℂ (ℤ →₀ ℂ) ((-(k : ℂ)) • single (k + n) 1)

/-- On a single Laurent monomial, the Witt operator differentiates its exponent and shifts it by n. This is the concrete action used to check every bracket identity. -/
@[simp] theorem op_single (n k : ℤ) (a : ℂ) :
    op n (single k a) = (-(k : ℂ) * a) • single (k + n) 1 := by
  simp only [op, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]
  rw [mul_comm]

/-- "Bracket with `ℓₘ` on the left": `single n b ↦ b·(m-n)·ℓ_{m+n}`. -/
noncomputable def bracketWith (m : ℤ) : Witt →ₗ[ℂ] Witt :=
  Finsupp.lsum ℂ fun n => LinearMap.toSpanSingleton ℂ Witt (single (m + n) ((m : ℂ) - n))

/-- Bracketing a generator with one scaled basis vector multiplies by the difference of their indices and adds the indices. Linearity then determines the action on every finite sum. -/
@[simp] theorem bracketWith_single (m n : ℤ) (b : ℂ) :
    bracketWith m (single n b) = single (m + n) (b * ((m : ℂ) - n)) := by
  simp only [bracketWith, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.smul_single, smul_eq_mul]

/-- The bilinear Witt bracket: `⁅ℓₘ, ℓₙ⁆ = (m-n) ℓ_{m+n}`, extended bilinearly. -/
noncomputable def bracketₗ : Witt →ₗ[ℂ] Witt →ₗ[ℂ] Witt :=
  Finsupp.lsum ℂ fun m => LinearMap.toSpanSingleton ℂ _ (bracketWith m)

/-- The bracket of two scaled generators has the product of their scalars as coefficient. This basis calculation is the link between the bilinear definition and the usual Witt relation. -/
@[simp] theorem bracketₗ_single (m n : ℤ) (a b : ℂ) :
    bracketₗ (single m a) (single n b) = single (m + n) (a * b * ((m : ℂ) - n)) := by
  have h1 : bracketₗ (single m a) = a • bracketWith m := by
    simp only [bracketₗ, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
  rw [h1, LinearMap.smul_apply, bracketWith_single, Finsupp.smul_single, smul_eq_mul]
  congr 1
  ring

/-- Registers the bilinear Witt operation as bracket notation. The Lie identities are proved below using its faithful operator realization. -/
noncomputable instance : Bracket Witt Witt := ⟨fun x y => bracketₗ x y⟩

/-- Unfolds bracket notation into the explicit bilinear map, so calculations can use finite-support linearity before the Lie structure has been established. -/
theorem bracket_def (x y : Witt) : ⁅x, y⁆ = bracketₗ x y := rfl

/-- The faithful representation `ℓₙ ↦ op n` of the Witt algebra on `ℤ →₀ ℂ`. -/
noncomputable def rep : Witt →ₗ[ℂ] Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => LinearMap.toSpanSingleton ℂ _ (op n)

/-- A scaled Witt generator acts by the same scalar times its Laurent-polynomial differential operator. This identifies the linear representation on a basis. -/
@[simp] theorem rep_single (n : ℤ) (a : ℂ) : rep (single n a) = a • op n := by
  simp only [rep, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The commutator of the Witt operators reproduces the Witt bracket:
`[op m, op n] = (m-n) • op (m+n)` (the Lie bracket in `End ℂ (ℤ →₀ ℂ)`). -/
theorem op_commutator (m n : ℤ) : ⁅op m, op n⁆ = ((m : ℂ) - n) • op (m + n) := by
  refine Finsupp.lhom_ext fun k a => ?_
  rw [LieRing.of_associative_ring_bracket]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, op_single, map_smul, smul_smul,
    LinearMap.smul_apply]
  rw [show k + n + m = k + m + n from by ring, ← sub_smul,
    show k + m + n = k + (m + n) from by ring]
  congr 1
  push_cast
  ring

/-- The representation `rep` carries the Witt bracket to the commutator in `End`. -/
theorem rep_bracket (x y : Witt) : rep ⁅x, y⁆ = ⁅rep x, rep y⁆ := by
  induction x using Finsupp.induction_linear with
  | zero => simp [bracket_def]
  | add x₁ x₂ h₁ h₂ =>
      simp only [bracket_def, map_add, LinearMap.add_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, add_lie]
  | single m a =>
      induction y using Finsupp.induction_linear with
      | zero => simp [bracket_def]
      | add y₁ y₂ h₁ h₂ =>
          simp only [bracket_def, map_add] at h₁ h₂ ⊢
          rw [h₁, h₂, lie_add]
      | single n b =>
          rw [bracket_def, bracketₗ_single, rep_single, rep_single, rep_single, smul_lie,
            lie_smul, op_commutator, smul_smul, smul_smul, mul_assoc]

/-- The value of `rep x` on `z = single 1 1`: `rep x · z = -(degree-shift of x)`. This makes
the representation manifestly faithful. -/
theorem rep_apply_single_one (x : Witt) : rep x (single 1 1) = - mapDomain (1 + ·) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂, Finsupp.mapDomain_add, neg_add]
  | single n a =>
      rw [rep_single, LinearMap.smul_apply, op_single, mapDomain_single, smul_smul,
        Finsupp.smul_single]
      simp

/-- No nonzero Witt element acts as the zero operator: evaluating on z recovers all its coefficients, shifted by one index and negated. This faithfulness lets operator identities prove identities in Witt itself. -/
theorem rep_injective : Function.Injective rep := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : mapDomain (1 + ·) x = 0 := by
    have hx1 := rep_apply_single_one x
    rw [hx] at hx1
    simpa using hx1.symm
  have hinj : Function.Injective (fun a : ℤ => 1 + a) := fun _ _ h => add_left_cancel h
  exact mapDomain_injective hinj (h.trans mapDomain_zero.symm)

/-! ### Lie algebra structure (transferred from the faithful representation) -/

/-- Transfers alternation and the Jacobi identity from operator commutators through the faithful representation. Additivity follows directly from the bilinear bracket. -/
noncomputable instance : LieRing Witt where
  add_lie x y z := by simp only [bracket_def, map_add, LinearMap.add_apply]
  lie_add x y z := by simp only [bracket_def, map_add]
  lie_self x := rep_injective (by rw [rep_bracket, lie_self, map_zero])
  leibniz_lie x y z := rep_injective (by simp only [rep_bracket, map_add]; exact leibniz_lie _ _ _)

/-- Makes the Witt Lie ring a complex Lie algebra by recording compatibility of its bracket with complex scalar multiplication. -/
noncomputable instance : LieAlgebra ℂ Witt where
  lie_smul a x y := by simp only [bracket_def, map_smul]

/-- The defining Witt relation `[ℓₘ, ℓₙ] = (m - n) ℓ_{m+n}` (Gannon §3.1.1). -/
theorem gen_bracket (m n : ℤ) : ⁅gen m, gen n⁆ = ((m : ℂ) - n) • gen (m + n) := by
  simp only [bracket_def, gen, bracketₗ_single, Finsupp.smul_single, smul_eq_mul, one_mul, mul_one]

/-! ## The Gel'fand–Fuks 2-cocycle -/

/-- The Gel'fand–Fuks cocycle value `ψ(ℓₘ,ℓₙ) = (1/12)(m³-m)δ_{m+n,0}` (Gannon eq. 3.1.5). -/
noncomputable def gfCoeff (m n : ℤ) : ℂ := if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 else 0

/-- `ψ(ℓₘ, ·)` as a `ℂ`-linear functional on `Witt`. -/
noncomputable def cocycleWith (m : ℤ) : Witt →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun n => LinearMap.toSpanSingleton ℂ ℂ (gfCoeff m n)

/-- The central cocycle evaluated on a scaled basis vector is the scalar times the explicit Gel'fand–Fuks coefficient. This reduces the central-extension calculation to integer indices. -/
@[simp] theorem cocycleWith_single (m n : ℤ) (b : ℂ) :
    cocycleWith m (single n b) = b * gfCoeff m n := by
  simp only [cocycleWith, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The Gel'fand–Fuks cocycle `ψ : Witt → Witt → ℂ`, bilinear. -/
noncomputable def cocycleₗ : Witt →ₗ[ℂ] Witt →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun m => LinearMap.toSpanSingleton ℂ _ (cocycleWith m)

/-- Evaluating the bilinear cocycle on two scaled generators gives their scalar product times the central coefficient. General cocycle identities can therefore be checked on generators. -/
@[simp] theorem cocycleₗ_single (m n : ℤ) (a b : ℂ) :
    cocycleₗ (single m a) (single n b) = a * b * gfCoeff m n := by
  have h1 : cocycleₗ (single m a) = a • cocycleWith m := by
    simp only [cocycleₗ, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
  rw [h1, LinearMap.smul_apply, cocycleWith_single, smul_eq_mul, mul_assoc]

/-- The cocycle coefficient is skew: `ψ(ℓₘ,ℓₙ) = -ψ(ℓₙ,ℓₘ)`. -/
theorem gfCoeff_skew (m n : ℤ) : gfCoeff m n = - gfCoeff n m := by
  unfold gfCoeff
  rw [add_comm n m]
  split_ifs with h
  · have hn : n = -m := by omega
    subst hn; push_cast; ring
  · simp

/-- Skew-symmetry of the cocycle (bilinear, from `gfCoeff_skew` on the basis). -/
theorem cocycleₗ_skew (x y : Witt) : cocycleₗ x y = - cocycleₗ y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, neg_add]
  | single m a =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, neg_add]
      | single n b =>
          rw [cocycleₗ_single, cocycleₗ_single, gfCoeff_skew m n]
          ring

/-- The cocycle is alternating: `ψ(x,x) = 0` (from skew-symmetry, `char ℂ ≠ 2`). -/
theorem cocycleₗ_self (x : Witt) : cocycleₗ x x = 0 := by
  have h := cocycleₗ_skew x x
  rw [eq_neg_iff_add_eq_zero, ← two_mul] at h
  rcases mul_eq_zero.mp h with h3 | h3
  · norm_num at h3
  · exact h3

/-- The scalar Gel'fand–Fuks cocycle identity (the heart of the central extension):
`(b-c)ψ(a,b+c) = (a-b)ψ(a+b,c) + (a-c)ψ(b,a+c)`. Nonzero only when `a+b+c=0`, where it is
a polynomial identity in `a,b`. -/
theorem gfCoeff_cocycle (a b c : ℤ) :
    ((b : ℂ) - c) * gfCoeff a (b + c)
      = ((a : ℂ) - b) * gfCoeff (a + b) c + ((a : ℂ) - c) * gfCoeff b (a + c) := by
  unfold gfCoeff
  by_cases h : a + b + c = 0
  · rw [if_pos (by omega : a + (b + c) = 0), if_pos (by omega : a + b + c = 0),
      if_pos (by omega : b + (a + c) = 0)]
    have hc : c = -a - b := by omega
    subst hc
    push_cast
    ring
  · rw [if_neg (by omega : ¬a + (b + c) = 0), if_neg (by omega : ¬a + b + c = 0),
      if_neg (by omega : ¬b + (a + c) = 0)]
    ring

/-- **Cocycle condition** for `ψ` with respect to the trivial module (Gannon §3.1.2): proven
by reducing the trilinear identity to the basis case `gfCoeff_cocycle`. -/
theorem cocycle_cond (x y z : Witt) :
    cocycleₗ x ⁅y, z⁆ = cocycleₗ ⁅x, y⁆ z + cocycleₗ y ⁅x, z⁆ := by
  induction x using Finsupp.induction_linear with
  | zero => simp [bracket_def]
  | add x₁ x₂ h₁ h₂ =>
      simp only [bracket_def, map_add, LinearMap.add_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]; ring
  | single a α =>
      induction y using Finsupp.induction_linear with
      | zero => simp [bracket_def]
      | add y₁ y₂ h₁ h₂ =>
          simp only [bracket_def, map_add, LinearMap.add_apply] at h₁ h₂ ⊢
          rw [h₁, h₂]; ring
      | single b β =>
          induction z using Finsupp.induction_linear with
          | zero => simp [bracket_def]
          | add z₁ z₂ h₁ h₂ =>
              simp only [bracket_def, map_add] at h₁ h₂ ⊢
              rw [h₁, h₂]; ring
          | single c γ =>
              simp only [bracket_def, bracketₗ_single, cocycleₗ_single]
              linear_combination (α * β * γ) * gfCoeff_cocycle a b c

end Witt

/-! ## The Virasoro algebra (central extension via the Gel'fand–Fuks cocycle) -/

open LieAlgebra LieModule.Cohomology

/-- `ℂ` as the trivial `Witt`-module — the centre of the Virasoro extension. -/
instance : LieRingModule Witt ℂ where
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  leibniz_lie _ _ _ := by simp

/-- The zero Witt action on the proposed centre respects complex scalars in both arguments, so it is a complex Lie-module structure. -/
instance : LieModule ℂ Witt ℂ where
  smul_lie _ _ _ := by simp [Bracket.bracket]
  lie_smul _ _ _ := by simp [Bracket.bracket]

/-- Records explicitly that the centre is a trivial Witt module: every Witt element acts by zero. This selects the central-extension form of the cocycle identity. -/
instance : LieModule.IsTrivial Witt ℂ where
  trivial _ _ := rfl

/-- The Gel'fand–Fuks 2-cochain `ψ` (alternating bilinear). -/
noncomputable def gfCochain : twoCochain ℂ Witt ℂ := ⟨Witt.cocycleₗ, Witt.cocycleₗ_self⟩

/-- The Gel'fand–Fuks 2-cocycle (Gannon §3.1.2). -/
noncomputable def gfCocycle : twoCocycle ℂ Witt ℂ :=
  ⟨gfCochain, (mem_twoCocycle_iff_of_trivial (a := gfCochain)).mpr
    fun x y z => Witt.cocycle_cond x y z⟩

/-- The **Virasoro algebra** `𝔙𝔦𝔯`: the central extension of the Witt algebra by `ℂ` along
the Gel'fand–Fuks cocycle (Gannon §3.1.2). Its `LieRing`/`LieAlgebra ℂ` structure comes for
free from Mathlib's `LieAlgebra.ofTwoCocycle`. -/
abbrev Virasoro : Type := LieAlgebra.ofTwoCocycle gfCocycle

/-- The Virasoro generator `Lₙ` (the lift of `ℓₙ`). -/
noncomputable def L (n : ℤ) : Virasoro := ofProd gfCocycle (Witt.gen n, 0)

/-- The central element `C` of the Virasoro algebra. -/
noncomputable def C : Virasoro := ofProd gfCocycle (0, 1)

/-- **The Virasoro relation** (Gannon eq. 3.1.5):
`[Lₘ, Lₙ] = (m - n) L_{m+n} + (C/12)(m³ - m) δ_{m+n,0}`. -/
theorem virasoro_bracket (m n : ℤ) :
    ⁅L m, L n⁆ = ((m : ℂ) - n) • L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12) • C else 0) := by
  rw [L, L, bracket_ofTwoCocycle]
  apply (ofProd gfCocycle).symm.injective
  rw [Equiv.symm_apply_apply, L, C]
  simp only [of_symm_add, of_symm_smul, Equiv.symm_apply_apply, trivial_lie_zero,
    Witt.bracket_def, Witt.bracketₗ_single, Witt.gen, one_mul, mul_one, add_zero, sub_zero,
    Prod.smul_mk, smul_zero, Prod.mk_add_mk, Finsupp.smul_single, smul_eq_mul, apply_ite,
    Prod.ext_iff]
  split_ifs with h <;>
    exact ⟨trivial, by
      change Witt.cocycleₗ (single m 1) (single n 1) = _
      rw [Witt.cocycleₗ_single, Witt.gfCoeff]; simp [h]⟩

/-- A representation of the Virasoro algebra of **central charge** `c`: `C` acts as `c · id`
(Gannon §3.1.2). -/
structure VirRep (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The Lie-algebra homomorphism `𝔙𝔦𝔯 → End ℂ V`. -/
  ρ : Virasoro →ₗ⁅ℂ⁆ Module.End ℂ V
  /-- The central charge. -/
  centralCharge : ℂ
  /-- The central element acts as the scalar `centralCharge`. -/
  acts_central : ρ C = centralCharge • LinearMap.id

/-! ## Smoke tests -/

/-- `[L₁, L₋₁] = 2 L₀` (the central term vanishes, since `1³ - 1 = 0`). -/
example : ⁅L 1, L (-1)⁆ = (2 : ℂ) • L 0 := by
  rw [virasoro_bracket]; norm_num

/-- `[L₂, L₋₂] = 4 L₀ + (C/2)` (central charge term `(2³-2)/12 = 1/2`). -/
example : ⁅L 2, L (-2)⁆ = (4 : ℂ) • L 0 + (2⁻¹ : ℂ) • C := by
  rw [virasoro_bracket]; norm_num

end VOA
