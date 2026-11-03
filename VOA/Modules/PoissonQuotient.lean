/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Modules.PoissonDescent
import VOA.Core.QuotientVOA

/-!
# `A₂` as a `ℂ`-algebra, and its functoriality under quotient VOAs

Two generic pieces of infrastructure that `Modules.PoissonDescent` stops just short of, and that
every presentation of a `C₂`-algebra by generators and relations needs.

## §1  `Algebra ℂ (A₂ W)`

`Modules.PoissonDescent` builds `A₂CommRing W : CommRing (A₂ W)` on top of the quotient
`Module ℂ (A₂ W)`, but registers no `Algebra ℂ (A₂ W)` — `Examples.AffineSl2Symbol` §0 records
that gap explicitly and works around it by hand.  The missing datum is exactly the
scalar/product interchange, and both halves are one application of `map_smul` of the bilinear
`A₂mul`:

* `A₂_smul_mul : (c • p) * q = c • (p * q)`,
* `A₂_mul_smul : p * (c • q) = c • (p * q)`.

`Algebra.ofModule` turns those two into `A₂Algebra W : Algebra ℂ (A₂ W)`.  There is **no
diamond**: `Algebra.ofModule` reuses the ambient `Module ℂ (A₂ W)` for its `SMul` field and sets
`algebraMap c = c • 1`, so `A₂_algebraMap_apply` is `rfl`.

The point of having the `Algebra` instance is that `MvPolynomial.aeval` becomes available, so a
symbol map `Sym(𝔤) → A₂(W)` can be built as an **`AlgHom`**.  That is what turns a check like
"the Poisson ideal `Cas·𝔪` dies" from an ideal induction into a check on the three generators
(`Ideal.span_le` into `RingHom.ker`).

## §2  The quotient map `A₂(W) ↠ A₂(W ⧸ I)`

`Core.QuotientVOA` builds `quotientVOA W I hI hgr` and proves the one identity that matters,
`quotientVOA_mkQ_smul : [u]₍ₙ₎[v] = [u₍ₙ₎v]`.  Consequently `O₂` is carried into `O₂`, and the
composite `𝒱 → 𝒱 ⧸ I → A₂(𝒱 ⧸ I)` factors through `A₂(W)`:

* `A₂quotₗ` — the `ℂ`-linear factorisation (`Submodule.liftQ`), with `A₂quotₗ_mk₂` by `rfl`;
* `A₂quotₗ_mul`, `A₂quotₗ_one`, `A₂quotₗ_bracket` — it is a morphism of Poisson algebras;
* `A₂quot` — the same map bundled as an `AlgHom`;
* `A₂quot_surjective`.

This is the transport step that lets a computation performed in `A₂` of a **universal** vertex
operator algebra be read off in `A₂` of any of its quotients — in particular in the `C₂`-algebra
of a simple quotient, which is where associated-variety statements live.

## Status
`sorry`-free and axiom-clean: every declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.  The theorem `VOA.pbw` is not used.

## Dependencies
* `Modules.PoissonDescent` — `O₂`, `A₂`, `mk₂`, `A₂mul`, `A₂bracket`, `A₂CommRing`, `A₂_mul_mk`;
* `Core.QuotientVOA` — `quotientVOA`, `quotientVOA_mkQ_smul`.
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The `ℂ`-algebra structure on `A₂ W` -/

/-- Scalars pass through the descended product on the left: `(c • p) · q = c • (p · q)`.

⚠ Stated in the root `VOA` namespace; `Examples.AffineSl2Symbol.A₂_smul_mul` is the
same statement, proved earlier in a file that this one does not depend on. -/
theorem A₂_smul_mul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (p q : A₂ W) :
    (c • p) * q = c • (p * q) := by
  have h : A₂mul W (c • p) = c • A₂mul W p := map_smul (A₂mul W) c p
  calc (c • p) * q = A₂mul W (c • p) q := rfl
    _ = (c • A₂mul W p) q := by rw [h]
    _ = c • A₂mul W p q := LinearMap.smul_apply _ _ _
    _ = c • (p * q) := rfl

/-- Scalars pass through the descended product on the right: `p · (c • q) = c • (p · q)`. -/
theorem A₂_mul_smul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (p q : A₂ W) :
    p * (c • q) = c • (p * q) :=
  map_smul (A₂mul W p) c q

/-- **`A₂(W)` is a `ℂ`-algebra.**  Built by `Algebra.ofModule` from the two interchange laws,
so its `SMul` field is the ambient quotient module structure and `algebraMap c = c • 1`: no
diamond with the existing `Module ℂ (A₂ W)`.

This is what makes `MvPolynomial.aeval` available for building symbol maps `Sym(𝔤) → A₂(W)` as
`AlgHom`s. -/
noncomputable instance A₂Algebra (W : VertexOperatorAlgebra 𝒱) : Algebra ℂ (A₂ W) :=
  Algebra.ofModule (A₂_smul_mul W) (A₂_mul_smul W)

/-- The structure map of `A₂Algebra` is `c ↦ c • 1`, definitionally. -/
theorem A₂_algebraMap_apply (W : VertexOperatorAlgebra 𝒱) (c : ℂ) :
    algebraMap ℂ (A₂ W) c = c • (1 : A₂ W) := rfl

/-- A numeral of `A₂ W` acts as the corresponding complex scalar: `(n : A₂ W) * x = (n : ℂ) • x`.
Used to reconcile ring-level numerals produced by `aeval` with the `ℂ`-scalar multiples in which
`Examples.AffineSl2Symbol` states the Casimir. -/
theorem A₂_natCast_mul (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : A₂ W) :
    ((n : ℕ) : A₂ W) * x = (n : ℂ) • x := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- `4 : A₂ W` acts as the complex scalar `4`.  Specialisation of `A₂_natCast_mul`, in the exact
shape needed to reconcile the numerals produced by `MvPolynomial.aeval` with the `ℂ`-scalar
multiples in which `Examples.AffineSl2Symbol` states the `𝔰𝔩₂` Casimir class. -/
theorem A₂_four_mul (W : VertexOperatorAlgebra 𝒱) (x : A₂ W) :
    (4 : A₂ W) * x = (4 : ℂ) • x := by
  simpa using A₂_natCast_mul W 4 x

/-- The unit is Poisson-central: `⁅[u], 1⁆ = 0`, because `u₍₀₎𝟙 = 0` (VA3). -/
@[simp] theorem A₂bracket_one (W : VertexOperatorAlgebra 𝒱) (p : A₂ W) :
    A₂bracket W p 1 = 0 := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  rw [A₂_one_eq, A₂bracket_mk, poissonBracket_def,
    W.toPreVertexAlgebra.smul_vacuum_zero u, map_zero]

/-! ## §2  Functoriality of `A₂` along a quotient VOA -/

namespace QuotVOA

variable {W : VertexOperatorAlgebra 𝒱} {I : Submodule ℂ 𝒱}

/-- `O₂(W)` is carried into `O₂` of the quotient: a generator `u₍₋₂₎v` maps to
`[u]₍₋₂₎[v]` by `quotientVOA_mkQ_smul`. -/
theorem O₂_le_ker_mk₂_comp_mkQ (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    O₂ W ≤ LinearMap.ker ((mk₂ (quotientVOA W I hI hgr)).comp I.mkQ) := by
  rw [O₂, Submodule.span_le]
  rintro x ⟨u, v, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
  refine (mk₂_eq_zero_iff _).mpr ?_
  rw [← quotientVOA_mkQ_smul hI hgr u (-2) v]
  exact Submodule.subset_span ⟨_, _, rfl⟩

/-- The **`C₂`-algebra of a quotient VOA**, as a `ℂ`-linear map out of `A₂(W)`. -/
noncomputable def A₂quotₗ (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    A₂ W →ₗ[ℂ] A₂ (quotientVOA W I hI hgr) :=
  (O₂ W).liftQ ((mk₂ (quotientVOA W I hI hgr)).comp I.mkQ) (O₂_le_ker_mk₂_comp_mkQ hI hgr)

@[simp] theorem A₂quotₗ_mk₂ (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (u : 𝒱) :
    A₂quotₗ hI hgr (mk₂ W u) = mk₂ (quotientVOA W I hI hgr) (I.mkQ u) := rfl

theorem A₂quotₗ_surjective (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    Function.Surjective (A₂quotₗ hI hgr) := by
  intro y
  obtain ⟨x, rfl⟩ := mk₂_surjective (quotientVOA W I hI hgr) y
  obtain ⟨u, rfl⟩ := I.mkQ_surjective x
  exact ⟨mk₂ W u, rfl⟩

/-- The transport preserves the commutative product `[u]·[v] = [u₍₋₁₎v]`. -/
theorem A₂quotₗ_mul (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (p q : A₂ W) :
    A₂quotₗ hI hgr (p * q) = A₂quotₗ hI hgr p * A₂quotₗ hI hgr q := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  rw [A₂_mul_mk, A₂quotₗ_mk₂, A₂quotₗ_mk₂, A₂quotₗ_mk₂, A₂_mul_mk, poissonMul_def,
    poissonMul_def, quotientVOA_mkQ_smul]

/-- The transport preserves the unit `1 = [𝟙]` (the vacuum of the quotient is the class of the
vacuum, definitionally). -/
theorem A₂quotₗ_one (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    A₂quotₗ hI hgr (1 : A₂ W) = 1 := rfl

/-- The transport preserves the Poisson bracket `⁅[u],[v]⁆ = [u₍₀₎v]`. -/
theorem A₂quotₗ_bracket (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (p q : A₂ W) :
    A₂quotₗ hI hgr (A₂bracket W p q)
      = A₂bracket (quotientVOA W I hI hgr) (A₂quotₗ hI hgr p) (A₂quotₗ hI hgr q) := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  rw [A₂bracket_mk, A₂quotₗ_mk₂, A₂quotₗ_mk₂, A₂quotₗ_mk₂, A₂bracket_mk, poissonBracket_def,
    poissonBracket_def, quotientVOA_mkQ_smul]

/-- **The `C₂`-algebra of a quotient VOA**, as a surjective `ℂ`-algebra map
`A₂(W) ↠ A₂(W ⧸ I)`. -/
noncomputable def A₂quot (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    A₂ W →ₐ[ℂ] A₂ (quotientVOA W I hI hgr) :=
  AlgHom.mk'
    { toFun := A₂quotₗ hI hgr
      map_one' := A₂quotₗ_one hI hgr
      map_mul' := A₂quotₗ_mul hI hgr
      map_zero' := (A₂quotₗ hI hgr).map_zero
      map_add' := (A₂quotₗ hI hgr).map_add }
    (fun c x => (A₂quotₗ hI hgr).map_smul c x)

@[simp] theorem A₂quot_apply (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (p : A₂ W) :
    A₂quot hI hgr p = A₂quotₗ hI hgr p := rfl

@[simp] theorem A₂quot_mk₂ (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (u : 𝒱) :
    A₂quot hI hgr (mk₂ W u) = mk₂ (quotientVOA W I hI hgr) (I.mkQ u) := rfl

theorem A₂quot_surjective (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    Function.Surjective (A₂quot hI hgr) := A₂quotₗ_surjective hI hgr

theorem A₂quot_bracket (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (p q : A₂ W) :
    A₂quot hI hgr (A₂bracket W p q)
      = A₂bracket (quotientVOA W I hI hgr) (A₂quot hI hgr p) (A₂quot hI hgr q) :=
  A₂quotₗ_bracket hI hgr p q

end QuotVOA

end VOA

section AxiomAudit
#print axioms VOA.A₂_smul_mul
#print axioms VOA.A₂_mul_smul
#print axioms VOA.A₂Algebra
#print axioms VOA.A₂_algebraMap_apply
#print axioms VOA.A₂_natCast_mul
#print axioms VOA.A₂_four_mul
#print axioms VOA.A₂bracket_one
#print axioms VOA.QuotVOA.A₂quot_apply
#print axioms VOA.QuotVOA.A₂quot_mk₂
#print axioms VOA.QuotVOA.O₂_le_ker_mk₂_comp_mkQ
#print axioms VOA.QuotVOA.A₂quotₗ
#print axioms VOA.QuotVOA.A₂quotₗ_mk₂
#print axioms VOA.QuotVOA.A₂quotₗ_surjective
#print axioms VOA.QuotVOA.A₂quotₗ_mul
#print axioms VOA.QuotVOA.A₂quotₗ_one
#print axioms VOA.QuotVOA.A₂quotₗ_bracket
#print axioms VOA.QuotVOA.A₂quot
#print axioms VOA.QuotVOA.A₂quot_surjective
#print axioms VOA.QuotVOA.A₂quot_bracket
end AxiomAudit
