/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.Data.Complex.Basic
import VOA.Foundations.AffineLie

/-!
# Root datum and Chevalley generators of a finite-dimensional simple Lie algebra (Gannon §3.2)

**First step towards affine integrability** (the deepest open `Foundations.AffineLie`
dependency — local nilpotency of the Chevalley generators on `L(λ)`, Kac–Garland). This file
assembles, from Mathlib's root theory, the *finite* root datum of `𝔤` that the affine construction
and the `𝔰𝔩₂`-string argument consume.

For a finite-dimensional Lie algebra `𝔤` over `ℂ` with non-degenerate Killing form (e.g. any
finite-dimensional **simple** `𝔤`, via `IsSimple → IsSemisimple → HasTrivialRadical → IsKilling`),
relative to a splitting Cartan subalgebra `H` (over `ℂ`, every Cartan subalgebra is splitting:
`IsTriangularizable` holds since `ℂ` is algebraically closed), Mathlib already provides:

* `LieAlgebra.IsKilling.rootSystem H` — the (reduced, crystallographic) root system of `𝔤`;
* `LieAlgebra.IsKilling.coroot α` — the coroot `αᵛ ∈ H` of a root `α`;
* `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero` — an `sl₂`-triple per root;
* `RootPairing.nonempty_base` — a base, i.e. a system of simple roots;
* `LieAlgebra.IsKilling.apply_coroot_eq_cast` — the Cartan-integer pairing `β(αᵛ) ∈ ℤ`.

Here we package the finite root datum (`nonempty_base`, `exists_chevalleyTriple`,
`cartanInteger`), the highest root relative to a base (`highestRoot`), chosen highest-root
Chevalley generators, the affine-node generators `affineEZero`/`affineFZero`, and the general
highest-weight quotients `AffineLie.verma`/`AffineLie.simpleHWOf`, conditional on highest-vector
nonvanishing. The final integrability target is also recorded as
`AffineLie.SimpleHWIntegrable`, with the quotient/representation wiring separated from the
remaining Kac–Garland local-nilpotency proof.

## What remains for `Integrable (L λ)` (not proved here)

The finite/root-system layer supplies the highest root and affine node. The genuinely missing
pieces are:

* **Affine-node normalization.** `affineEZero_bracket_affineFZero` is proved directly from
  `affine_bracket`. Rewriting it as the textbook `C - θᵛ` relation needs a normalization tying the
  chosen invariant form `κ` to the chosen Chevalley triple (`κ(f_θ,e_θ)=1` and
  `[f_θ,e_θ]=-θᵛ`).
* **The `sl₂`-string argument on `L(λ)`.** Mathlib's
  `IsSl2Triple.HasPrimitiveVectorWith.exists_nat` gives string-integrality only for
  *finite-dimensional* (Noetherian) modules; `L(λ)` is infinite-dimensional, so the Kac–Garland
  argument (the highest-weight vector generates a finite-dimensional `sl₂`-submodule under each
  node, forcing `fᵢ^{⟨λ,αᵢᵛ⟩+1}·vλ = 0`, then local nilpotency propagates) must be built directly.
* **`Integrable (L λ)`.** The general weight-`λ` Verma modules `M(λ)` are defined, and
  `L(λ)` is defined/proved simple once the highest vector is known nonzero. The integrability
  predicate and Chevalley-generator set are defined; what remains is the PBW nonvanishing theorem
  for arbitrary `λ`, followed by the Kac–Garland proof that those generators act locally
  nilpotently.

This module is imported by the `Foundations` aggregate so the affine root data is available
to the remaining highest-weight-module work.

## Status
Complete & `sorry`-free / axiom-free (root-data scaffolding).  Every declaration in this
file — the finite base/highest root, the chosen Chevalley triple, the affine-node generators
`affineEZero`/`affineFZero` and their `affine_bracket` relation, the general-`λ` Verma `verma`,
the conditional simple quotient `simpleHWOf`/`simpleHWOfModule` with its descended highest-weight
relations, and the theorem-shaped integrability target `SimpleHWIntegrable` /
`simpleHWOf_integrable_of_chevalley_locallyNilpotent` — is proved (`#print axioms = [propext,
Classical.choice, Quot.sound]`).  The remaining *unconditional* pieces (arbitrary-`λ` PBW
nonvanishing and the Kac–Garland local-nilpotency proof) are **open** (see the status section of
`Foundations.AffineLie`) — they are consumers of this scaffolding,
not holes in it.

## References
* Gannon §3.2; Kac, *Infinite Dimensional Lie Algebras* §1.3, §2.1, §3.6 (integrable modules).
-/

namespace VOA.RootDatum

open LieAlgebra LieAlgebra.IsKilling LieModule
open scoped BigOperators

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
  [LieAlgebra.IsKilling ℂ 𝔤]
  (H : LieSubalgebra ℂ 𝔤) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℂ H 𝔤]

/-- **Simple roots** of `𝔤`: the root system admits a base (Gannon §3.2; Kac §1.3). -/
theorem nonempty_base : Nonempty (rootSystem H).Base :=
  (rootSystem H).nonempty_base

variable {H}

/-- **Chevalley generators of a root** (Gannon §3.2; Kac §1.3): for a nonzero root `α` there are
nonzero `eₐ ∈ 𝔤_α`, `fₐ ∈ 𝔤_{-α}` whose bracket is the coroot `αᵛ`, so that `(αᵛ, eₐ, fₐ)` is an
`sl₂`-triple. These are the building blocks of the affine Chevalley generators (next step:
`e₀ = f_θ ⊗ t`, `f₀ = e_θ ⊗ t⁻¹` for the highest root `θ`). -/
theorem exists_chevalleyTriple (α : Weight ℂ H 𝔤) (hα : α.IsNonZero) :
    ∃ e f : 𝔤, IsSl2Triple (↑(coroot α) : 𝔤) e f ∧ e ∈ rootSpace H α ∧ f ∈ rootSpace H (-α) := by
  obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  exact ⟨e, f, ht.h_eq_coroot hα he hf ▸ ht, he, hf⟩

/-- **Cartan-matrix integrality** (Gannon §3.2; Kac §2.1): the pairing `β(αᵛ)` of a root `β` with a
coroot `αᵛ` is an integer. This integral structure is what forces the `sl₂`-string finiteness
(Step 3) that yields integrability. -/
theorem cartanInteger (α β : Weight ℂ H 𝔤) :
    ∃ z : ℤ, β (coroot α) = (z : ℂ) :=
  ⟨_, apply_coroot_eq_cast α β⟩

variable (H)

/-- Positive roots relative to a chosen base (Gannon §3.2; Kac §1.3). -/
noncomputable def positiveRoots (b : (rootSystem H).Base) : Finset H.root := by
  classical
  exact Finset.univ.filter fun α => b.IsPos α

/-- Membership in the positive-root finset is exactly positivity for the base (Gannon §3.2). -/
theorem mem_positiveRoots {b : (rootSystem H).Base} {α : H.root} :
    α ∈ positiveRoots H b ↔ b.IsPos α := by
  classical
  simp [positiveRoots]

/-- The positive roots are nonempty once the finite root system has a root (Gannon §3.2). -/
theorem positiveRoots_nonempty [Nonempty H.root] (b : (rootSystem H).Base) :
    (positiveRoots H b).Nonempty := by
  classical
  obtain ⟨α⟩ := (inferInstance : Nonempty H.root)
  letI := (rootSystem H).indexNeg
  rcases RootPairing.Base.IsPos.or_neg (b := b) α with h | h
  · exact ⟨α, (mem_positiveRoots (H := H) (b := b)).mpr h⟩
  · exact ⟨-α, (mem_positiveRoots (H := H) (b := b)).mpr h⟩

private theorem exists_highestRootIndex [Nonempty H.root] (b : (rootSystem H).Base) :
    ∃ θ ∈ positiveRoots H b, ∀ α ∈ positiveRoots H b, b.height α ≤ b.height θ :=
  Finset.exists_max_image (positiveRoots H b) (fun α => b.height α) (positiveRoots_nonempty H b)

/-- The highest root index: a positive finite root of maximal height for the chosen base
(Gannon §3.2; Kac §1.3). The `[Nonempty H.root]` hypothesis is the finite-simple case needed by
the affine node. -/
noncomputable def highestRootIndex [Nonempty H.root] (b : (rootSystem H).Base) : H.root :=
  (exists_highestRootIndex H b).choose

/-- The highest root is positive (Gannon §3.2). -/
theorem highestRootIndex_mem_positiveRoots [Nonempty H.root] (b : (rootSystem H).Base) :
    highestRootIndex H b ∈ positiveRoots H b :=
  (exists_highestRootIndex H b).choose_spec.1

/-- The highest root is positive for the chosen base (Gannon §3.2). -/
theorem highestRootIndex_isPos [Nonempty H.root] (b : (rootSystem H).Base) :
    b.IsPos (highestRootIndex H b) :=
  (mem_positiveRoots (H := H) (b := b)).mp (highestRootIndex_mem_positiveRoots H b)

/-- Maximality of the highest root height among positive roots (Gannon §3.2; Kac §1.3). -/
theorem height_le_highestRootIndex [Nonempty H.root] (b : (rootSystem H).Base)
    {α : H.root} (hα : b.IsPos α) : b.height α ≤ b.height (highestRootIndex H b) :=
  (exists_highestRootIndex H b).choose_spec.2 α ((mem_positiveRoots (H := H) (b := b)).mpr hα)

/-- The highest root `θ` as a finite root/weight (Gannon §3.2). -/
noncomputable def highestRoot [Nonempty H.root] (b : (rootSystem H).Base) : Weight ℂ H 𝔤 :=
  (highestRootIndex H b : Weight ℂ H 𝔤)

/-- The highest root is nonzero (Gannon §3.2). -/
theorem highestRoot_isNonZero [Nonempty H.root] (b : (rootSystem H).Base) :
    (highestRoot H b).IsNonZero := by
  have hlin : (Weight.toLinear ℂ H 𝔤 (highestRoot H b)) ≠ 0 := by
    simp [highestRoot]
  exact Weight.coe_toLinear_ne_zero_iff.mp hlin

/-- Chosen Chevalley generators for a finite root (Gannon §3.2; Kac §1.3). -/
structure ChevalleyTripleForRoot (α : H.root) where
  /-- The positive root vector `e_α`. -/
  e : 𝔤
  /-- The negative root vector `f_α`. -/
  f : 𝔤
  /-- `(αᵛ, e_α, f_α)` is an `sl₂`-triple. -/
  isSl2Triple : IsSl2Triple (↑(coroot (α : Weight ℂ H 𝔤)) : 𝔤) e f
  /-- `e_α` lies in the `α` root space. -/
  e_mem : e ∈ rootSpace H (α : Weight ℂ H 𝔤)
  /-- `f_α` lies in the `-α` root space. -/
  f_mem : f ∈ rootSpace H (-(α : Weight ℂ H 𝔤))

/-- Chevalley generators exist for every finite root (Gannon §3.2; Kac §1.3). -/
theorem nonempty_chevalleyTripleForRoot (α : H.root) :
    Nonempty (ChevalleyTripleForRoot H α) := by
  have hlin : (Weight.toLinear ℂ H 𝔤 (α : Weight ℂ H 𝔤)) ≠ 0 := by
    simp
  obtain ⟨e, f, ht, he, hf⟩ := exists_chevalleyTriple (H := H)
    (α := (α : Weight ℂ H 𝔤)) (Weight.coe_toLinear_ne_zero_iff.mp hlin)
  exact ⟨⟨e, f, ht, he, hf⟩⟩

/-- A noncomputable choice of Chevalley generators for a finite root (Gannon §3.2). -/
noncomputable def chevalleyTripleForRoot (α : H.root) : ChevalleyTripleForRoot H α :=
  Classical.choice (nonempty_chevalleyTripleForRoot H α)

/-- Chevalley generators for the highest root `θ` (Gannon §3.2). -/
noncomputable def highestChevalleyTriple [Nonempty H.root] (b : (rootSystem H).Base) :
    ChevalleyTripleForRoot H (highestRootIndex H b) :=
  chevalleyTripleForRoot H (highestRootIndex H b)

variable (κ : LinearMap.BilinForm ℂ 𝔤) (hκ : κ.IsInvariant)

/-- The affine-node generator `e₀ = f_θ ⊗ t` (Gannon §3.2; Kac §3.6). -/
noncomputable def affineEZero [Nonempty H.root] (b : (rootSystem H).Base) :
    VOA.AffineLie 𝔤 κ hκ :=
  VOA.AffineLie.ofLoop κ hκ (highestChevalleyTriple H b).f 1

/-- The affine-node generator `f₀ = e_θ ⊗ t⁻¹` (Gannon §3.2; Kac §3.6). -/
noncomputable def affineFZero [Nonempty H.root] (b : (rootSystem H).Base) :
    VOA.AffineLie 𝔤 κ hκ :=
  VOA.AffineLie.ofLoop κ hκ (highestChevalleyTriple H b).e (-1)

/-- The affine bracket relation for the affine node (Gannon §3.2.2): it is the defining
`affine_bracket` specialized to `e₀ = f_θ ⊗ t` and `f₀ = e_θ ⊗ t⁻¹`. Normalizing this further to
`C - θᵛ` requires the invariant form to be fixed compatibly with the chosen Chevalley triple. -/
theorem affineEZero_bracket_affineFZero [Nonempty H.root] (b : (rootSystem H).Base) :
    ⁅affineEZero H κ hκ b, affineFZero H κ hκ b⁆ =
      VOA.AffineLie.ofLoop κ hκ ⁅(highestChevalleyTriple H b).f,
        (highestChevalleyTriple H b).e⁆ 0 +
      (κ (highestChevalleyTriple H b).f (highestChevalleyTriple H b).e) •
        VOA.AffineLie.C κ hκ := by
  rw [affineEZero, affineFZero, VOA.AffineLie.affine_bracket]
  norm_num

end VOA.RootDatum

namespace VOA
namespace AffineLie

open UniversalEnvelopingAlgebra
open LieAlgebra LieAlgebra.IsKilling LieModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
  [LieAlgebra.IsKilling ℂ 𝔤]
  (H : LieSubalgebra ℂ 𝔤) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℂ H 𝔤]
  (κ : LinearMap.BilinForm ℂ 𝔤) (hκ : κ.IsInvariant)

/-- An affine Cartan weight `λ ∈ ĥ*` (Gannon §3.2; Kac §9.10), recorded by its finite-Cartan
part, central level, and `ℓ₀`/energy value. -/
structure AffineCartanWeight where
  /-- The restriction of `λ` to the finite Cartan subalgebra `H`. -/
  finite : H →ₗ[ℂ] ℂ
  /-- The level `λ(C)`. -/
  level : ℂ
  /-- The energy value `λ(ℓ₀)`. -/
  energy : ℂ

variable (b : (rootSystem H).Base) (lam : AffineCartanWeight H)

/-- The defining left-ideal generators of the affine Verma module `M(λ)` (Gannon §3.2):
positive loop modes, positive finite-root vectors at mode `0`, finite Cartan relations
`h - λ(h)`, and the affine Cartan relations `C - λ(C)`, `ℓ₀ - λ(ℓ₀)`. -/
def vermaGens : Set (UEnv 𝔤 κ hκ) :=
  {a | (∃ (x : 𝔤) (n : ℤ), 0 < n ∧ a = ι ℂ (ofLoop κ hκ x n))
      ∨ (∃ (α : H.root) (x : 𝔤), b.IsPos α ∧ x ∈ rootSpace H (α : Weight ℂ H 𝔤) ∧
          a = ι ℂ (ofLoop κ hκ x 0))
      ∨ (∃ h : H,
          a = ι ℂ (ofLoop κ hκ (h : 𝔤) 0) - algebraMap ℂ (UEnv 𝔤 κ hκ) (lam.finite h))
      ∨ a = ι ℂ (C κ hκ) - algebraMap ℂ (UEnv 𝔤 κ hκ) lam.level
      ∨ a = ι ℂ (ell0 κ hκ) - algebraMap ℂ (UEnv 𝔤 κ hκ) lam.energy}

/-- The Verma left ideal `I(λ) ⊆ U(ĝ)` (Gannon §3.2; Kac §9.10). -/
noncomputable def vermaIdeal : Submodule (UEnv 𝔤 κ hκ) (UEnv 𝔤 κ hκ) :=
  Submodule.span _ (vermaGens H κ hκ b lam)

/-- The defining generators lie in the Verma ideal `I(λ)` (Gannon §3.2). -/
theorem vermaGens_subset_ideal : vermaGens H κ hκ b lam ⊆ ↑(vermaIdeal H κ hκ b lam) :=
  Submodule.subset_span

/-- The affine Verma module `M(λ) = U(ĝ) / I(λ)` (Gannon §3.2; Kac §9.10). -/
abbrev verma : Type _ := UEnv 𝔤 κ hκ ⧸ vermaIdeal H κ hκ b lam

/-- The affine Lie action on `M(λ)`, by left multiplication through `U(ĝ)` (Gannon §3.2). -/
noncomputable def vermaRho : AffineLie 𝔤 κ hκ →ₗ⁅ℂ⁆ Module.End ℂ (verma H κ hκ b lam) :=
  (Algebra.lsmul ℂ ℂ (verma H κ hκ b lam)).toLieHom.comp (ι ℂ)

/-- The action formula on representatives in `M(λ)` (Gannon §3.2). -/
theorem vermaRho_mk (x : AffineLie 𝔤 κ hκ) (a : UEnv 𝔤 κ hκ) :
    vermaRho H κ hκ b lam x (Submodule.Quotient.mk a) = Submodule.Quotient.mk (ι ℂ x * a) := rfl

/-- The highest-weight vector `v_λ = [1] ∈ M(λ)` (Gannon §3.2). -/
noncomputable def highestVector : verma H κ hκ b lam := Submodule.Quotient.mk 1

/-- Positive loop modes annihilate the highest-weight vector of `M(λ)` (Gannon §3.2). -/
theorem verma_pos_loop_annihilate (x : 𝔤) (n : ℤ) (hn : 0 < n) :
    vermaRho H κ hκ b lam (ofLoop κ hκ x n) (highestVector H κ hκ b lam) = 0 := by
  rw [highestVector, vermaRho_mk, mul_one, Submodule.Quotient.mk_eq_zero]
  exact vermaGens_subset_ideal H κ hκ b lam (Or.inl ⟨x, n, hn, rfl⟩)

/-- Positive finite-root vectors at mode `0` annihilate the highest-weight vector of `M(λ)`
(Gannon §3.2). -/
theorem verma_pos_root_annihilate {α : H.root} (hα : b.IsPos α) {x : 𝔤}
    (hx : x ∈ rootSpace H (α : Weight ℂ H 𝔤)) :
    vermaRho H κ hκ b lam (ofLoop κ hκ x 0) (highestVector H κ hκ b lam) = 0 := by
  rw [highestVector, vermaRho_mk, mul_one, Submodule.Quotient.mk_eq_zero]
  exact vermaGens_subset_ideal H κ hκ b lam (Or.inr (Or.inl ⟨α, x, hα, hx, rfl⟩))

/-- Finite Cartan elements act on `v_λ` by the finite-Cartan part of `λ` (Gannon §3.2). -/
theorem verma_cartan_acts (h : H) :
    vermaRho H κ hκ b lam (ofLoop κ hκ (h : 𝔤) 0) (highestVector H κ hκ b lam) =
      lam.finite h • highestVector H κ hκ b lam := by
  rw [highestVector, vermaRho_mk, mul_one, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_one]
  rw [Submodule.Quotient.eq]
  exact vermaGens_subset_ideal H κ hκ b lam (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩)))

/-- The derivation `ℓ₀` acts on `v_λ` by `λ(ℓ₀)` (Gannon §3.2). -/
theorem verma_ell0_acts :
    vermaRho H κ hκ b lam (ell0 κ hκ) (highestVector H κ hκ b lam) =
      lam.energy • highestVector H κ hκ b lam := by
  rw [highestVector, vermaRho_mk, mul_one, ← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_one]
  rw [Submodule.Quotient.eq]
  exact vermaGens_subset_ideal H κ hκ b lam (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

set_option maxHeartbeats 800000 in
-- `vermaRho` unfolds the same heavy `Algebra.lsmul ∘ ι` quotient action as the vacuum module.
/-- The centre `C` acts on `M(λ)` by the level `λ(C)` (Gannon §3.2). -/
theorem verma_acts_central :
    vermaRho H κ hκ b lam (C κ hκ) = lam.level • LinearMap.id := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [vermaRho_mk, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have hcomm : Commute a (ι ℂ (C κ hκ) - algebraMap ℂ (UEnv 𝔤 κ hκ) lam.level) :=
    (commute_ι_C κ hκ a).symm.sub_right (Algebra.commute_algebraMap_right lam.level a)
  have heq : ι ℂ (C κ hκ) * a - lam.level • a
      = a * (ι ℂ (C κ hκ) - algebraMap ℂ (UEnv 𝔤 κ hκ) lam.level) := by
    rw [hcomm.eq, sub_mul, Algebra.smul_def]
  rw [heq, ← smul_eq_mul]
  exact (vermaIdeal H κ hκ b lam).smul_mem a
    (vermaGens_subset_ideal H κ hκ b lam (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-- The Verma module `M(λ)` packaged as an affine representation (Gannon §3.2). -/
noncomputable def vermaModule : AffineRep κ hκ (verma H κ hκ b lam) where
  ρ := vermaRho H κ hκ b lam
  level := lam.level
  acts_central := verma_acts_central H κ hκ b lam

/-- The highest-weight vector cyclically generates `M(λ)` (Gannon §3.2). -/
theorem verma_cyclic :
    Submodule.span (UEnv 𝔤 κ hκ) {highestVector H κ hκ b lam} = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hv : a • highestVector H κ hκ b lam = Submodule.Quotient.mk a := by
    rw [highestVector, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  rw [← hv]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

/-- Conditional nontriviality of `M(λ)` from survival of its highest-weight vector (Gannon §3.2).
The unconditional survival/nonvanishing theorem has not yet been derived for this quotient
presentation; the available route is relative PBW, `PBWTheorem.bottom_injective`
(`Foundations/PBWTheorem/Induced.lean`; the `inducedBottom` field of the theorem `VOA.pbw`). -/
theorem verma_nontrivial_of_highestVector_ne_zero
    (h : highestVector H κ hκ b lam ≠ 0) : Nontrivial (verma H κ hκ b lam) :=
  ⟨⟨highestVector H κ hκ b lam, 0, h⟩⟩

/-- A maximal proper submodule of a nonzero cyclic Verma module exists (Gannon §3.2; Kac §9.10):
cyclicity makes the top compact, hence the submodule lattice is coatomic. The hypothesis is exactly
the arbitrary-`λ` PBW nonvanishing result not yet derived here from `pbw.inducedBottom`. -/
theorem exists_simpleHWMaxSubmodule_of_highestVector_ne_zero
    (h : highestVector H κ hκ b lam ≠ 0) :
    ∃ P : Submodule (UEnv 𝔤 κ hκ) (verma H κ hκ b lam), IsCoatom P := by
  let R := UEnv 𝔤 κ hκ
  let V := verma H κ hκ b lam
  have htopfg : (⊤ : Submodule R V).FG := by
    rw [← verma_cyclic H κ hκ b lam]
    exact Submodule.fg_span_singleton (highestVector H κ hκ b lam)
  have hcompact : IsCompactElement (⊤ : Submodule R V) := by
    rwa [← Submodule.fg_iff_compact]
  haveI : IsCoatomic (Submodule R V) := CompleteLattice.coatomic_of_top_compact hcompact
  have hbot_ne_top : (⊥ : Submodule R V) ≠ ⊤ := by
    intro hb
    exact h (by
      have hv : highestVector H κ hκ b lam ∈ (⊥ : Submodule R V) := by
        rw [hb]
        trivial
      simpa using hv)
  obtain ⟨P, hP, _hle⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule R V)).resolve_left hbot_ne_top
  exact ⟨P, hP⟩

/-- The maximal submodule of `M(λ)` used to form the simple highest-weight quotient, conditional on
PBW nonvanishing of the highest-weight vector (Gannon §3.2; Kac §9.10). -/
noncomputable def simpleHWMaxSubmoduleOf (h : highestVector H κ hκ b lam ≠ 0) :
    Submodule (UEnv 𝔤 κ hκ) (verma H κ hκ b lam) :=
  (exists_simpleHWMaxSubmodule_of_highestVector_ne_zero H κ hκ b lam h).choose

/-- The chosen general highest-weight radical is a coatom (Gannon §3.2; Kac §9.10). -/
theorem simpleHWMaxSubmoduleOf_isCoatom (h : highestVector H κ hκ b lam ≠ 0) :
    IsCoatom (simpleHWMaxSubmoduleOf H κ hκ b lam h) :=
  (exists_simpleHWMaxSubmodule_of_highestVector_ne_zero H κ hκ b lam h).choose_spec

/-- The highest-weight vector survives the chosen simple quotient (Gannon §3.2; Kac §9.10). -/
theorem highestVector_not_mem_simpleHWMaxSubmoduleOf
    (h : highestVector H κ hκ b lam ≠ 0) :
    highestVector H κ hκ b lam ∉ simpleHWMaxSubmoduleOf H κ hκ b lam h := by
  intro hv
  have htop : (⊤ : Submodule (UEnv 𝔤 κ hκ) (verma H κ hκ b lam)) ≤
      simpleHWMaxSubmoduleOf H κ hκ b lam h := by
    rw [← verma_cyclic H κ hκ b lam, Submodule.span_singleton_le_iff_mem]
    exact hv
  exact (simpleHWMaxSubmoduleOf_isCoatom H κ hκ b lam h).ne_top (top_unique htop)

/-- The simple highest-weight quotient `L(λ)`, conditional on PBW nonvanishing of the highest-weight
vector (Gannon §3.2; Kac §9.10). -/
noncomputable abbrev simpleHWOf (h : highestVector H κ hκ b lam ≠ 0) : Type _ :=
  verma H κ hκ b lam ⧸ simpleHWMaxSubmoduleOf H κ hκ b lam h

/-- The conditional simple highest-weight quotient `L(λ)` is simple (Gannon §3.2; Kac §9.10). -/
theorem simpleHWOf_isSimpleModule (h : highestVector H κ hκ b lam ≠ 0) :
    IsSimpleModule (UEnv 𝔤 κ hκ) (simpleHWOf H κ hκ b lam h) := by
  rw [isSimpleModule_iff_isCoatom]
  exact simpleHWMaxSubmoduleOf_isCoatom H κ hκ b lam h

/-- The affine Lie action on the conditional simple highest-weight module `L(λ)` (Gannon §3.2). -/
noncomputable def simpleHWRhoOf (hnz : highestVector H κ hκ b lam ≠ 0) :
    AffineLie 𝔤 κ hκ →ₗ⁅ℂ⁆ Module.End ℂ (simpleHWOf H κ hκ b lam hnz) :=
  (Algebra.lsmul ℂ ℂ (simpleHWOf H κ hκ b lam hnz)).toLieHom.comp (ι ℂ)

/-- The action formula on representatives in `L(λ)` (Gannon §3.2). -/
theorem simpleHWRhoOf_mk (hnz : highestVector H κ hκ b lam ≠ 0)
    (x : AffineLie 𝔤 κ hκ) (m : verma H κ hκ b lam) :
    simpleHWRhoOf H κ hκ b lam hnz x (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk ((ι ℂ x) • m) := rfl

set_option maxHeartbeats 800000 in
-- This is the same quotient-by-representatives central-action calculation as for `vermaModule`.
/-- The centre acts on `L(λ)` by the level `λ(C)` (Gannon §3.2). -/
theorem simpleHWOf_acts_central (hnz : highestVector H κ hκ b lam ≠ 0) :
    simpleHWRhoOf H κ hκ b lam hnz (C κ hκ) = lam.level • LinearMap.id := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [simpleHWRhoOf_mk, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  change Submodule.Quotient.mk ((ι ℂ (C κ hκ)) • m) = Submodule.Quotient.mk (lam.level • m)
  have hm := congrArg (fun f : Module.End ℂ (verma H κ hκ b lam) => f m)
    (verma_acts_central H κ hκ b lam)
  simpa [vermaRho, Algebra.smul_def] using congrArg (Submodule.Quotient.mk) hm

/-- The conditional simple highest-weight module `L(λ)` packaged as an affine representation
(Gannon §3.2). -/
noncomputable def simpleHWOfModule (hnz : highestVector H κ hκ b lam ≠ 0) :
    AffineRep κ hκ (simpleHWOf H κ hκ b lam hnz) where
  ρ := simpleHWRhoOf H κ hκ b lam hnz
  level := lam.level
  acts_central := simpleHWOf_acts_central H κ hκ b lam hnz

/-- The highest-weight vector in the simple quotient `L(λ)` (Gannon §3.2). -/
noncomputable def simpleHighestVectorOf (hnz : highestVector H κ hκ b lam ≠ 0) :
    simpleHWOf H κ hκ b lam hnz :=
  Submodule.Quotient.mk (highestVector H κ hκ b lam)

/-- The simple highest-weight vector is nonzero (Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_ne_zero (hnz : highestVector H κ hκ b lam ≠ 0) :
    simpleHighestVectorOf H κ hκ b lam hnz ≠ 0 := by
  intro hzero
  rw [simpleHighestVectorOf] at hzero
  rw [Submodule.Quotient.mk_eq_zero] at hzero
  exact highestVector_not_mem_simpleHWMaxSubmoduleOf H κ hκ b lam hnz
    hzero

/-- Positive loop modes annihilate the highest-weight vector in the simple quotient `L(λ)`
(Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_pos_loop_annihilate
    (hnz : highestVector H κ hκ b lam ≠ 0) (x : 𝔤) (n : ℤ) (hn : 0 < n) :
    simpleHWRhoOf H κ hκ b lam hnz (ofLoop κ hκ x n)
      (simpleHighestVectorOf H κ hκ b lam hnz) = 0 := by
  rw [simpleHighestVectorOf, simpleHWRhoOf_mk]
  change Submodule.Quotient.mk
    (vermaRho H κ hκ b lam (ofLoop κ hκ x n) (highestVector H κ hκ b lam)) = 0
  rw [verma_pos_loop_annihilate H κ hκ b lam x n hn]
  rfl

/-- Positive finite-root vectors at mode `0` annihilate the highest-weight vector in `L(λ)`
(Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_pos_root_annihilate
    (hnz : highestVector H κ hκ b lam ≠ 0) {α : H.root} (hα : b.IsPos α) {x : 𝔤}
    (hx : x ∈ rootSpace H (α : Weight ℂ H 𝔤)) :
    simpleHWRhoOf H κ hκ b lam hnz (ofLoop κ hκ x 0)
      (simpleHighestVectorOf H κ hκ b lam hnz) = 0 := by
  rw [simpleHighestVectorOf, simpleHWRhoOf_mk]
  change Submodule.Quotient.mk
    (vermaRho H κ hκ b lam (ofLoop κ hκ x 0) (highestVector H κ hκ b lam)) = 0
  rw [verma_pos_root_annihilate H κ hκ b lam hα hx]
  rfl

/-- Finite Cartan elements act on the simple highest-weight vector by `λ`
(Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_cartan_acts
    (hnz : highestVector H κ hκ b lam ≠ 0) (h : H) :
    simpleHWRhoOf H κ hκ b lam hnz (ofLoop κ hκ (h : 𝔤) 0)
      (simpleHighestVectorOf H κ hκ b lam hnz) =
        lam.finite h • simpleHighestVectorOf H κ hκ b lam hnz := by
  rw [simpleHighestVectorOf, simpleHWRhoOf_mk, ← Submodule.Quotient.mk_smul]
  change Submodule.Quotient.mk
      (vermaRho H κ hκ b lam (ofLoop κ hκ (h : 𝔤) 0) (highestVector H κ hκ b lam)) =
    Submodule.Quotient.mk (lam.finite h • highestVector H κ hκ b lam)
  rw [verma_cartan_acts H κ hκ b lam h]

/-- The derivation `ℓ₀` acts on the simple highest-weight vector by `λ(ℓ₀)`
(Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_ell0_acts
    (hnz : highestVector H κ hκ b lam ≠ 0) :
    simpleHWRhoOf H κ hκ b lam hnz (ell0 κ hκ)
      (simpleHighestVectorOf H κ hκ b lam hnz) =
        lam.energy • simpleHighestVectorOf H κ hκ b lam hnz := by
  rw [simpleHighestVectorOf, simpleHWRhoOf_mk, ← Submodule.Quotient.mk_smul]
  change Submodule.Quotient.mk
      (vermaRho H κ hκ b lam (ell0 κ hκ) (highestVector H κ hκ b lam)) =
    Submodule.Quotient.mk (lam.energy • highestVector H κ hκ b lam)
  rw [verma_ell0_acts H κ hκ b lam]

/-- The centre acts on the simple highest-weight vector by the level `λ(C)`
(Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_central_acts
    (hnz : highestVector H κ hκ b lam ≠ 0) :
    simpleHWRhoOf H κ hκ b lam hnz (C κ hκ)
      (simpleHighestVectorOf H κ hκ b lam hnz) =
        lam.level • simpleHighestVectorOf H κ hκ b lam hnz := by
  have h := congrArg
    (fun f : Module.End ℂ (simpleHWOf H κ hκ b lam hnz) =>
      f (simpleHighestVectorOf H κ hκ b lam hnz))
    (simpleHWOf_acts_central H κ hκ b lam hnz)
  simpa [LinearMap.smul_apply, LinearMap.id_coe, id_eq] using h

/-- Positive Chevalley generators for finite positive roots annihilate the simple highest-weight
vector (Gannon §3.2; Kac §9.10). -/
theorem simpleHighestVectorOf_pos_chevalley_annihilate
    (hnz : highestVector H κ hκ b lam ≠ 0) {α : H.root} (hα : b.IsPos α) :
    simpleHWRhoOf H κ hκ b lam hnz
      (ofLoop κ hκ (VOA.RootDatum.chevalleyTripleForRoot H α).e 0)
      (simpleHighestVectorOf H κ hκ b lam hnz) = 0 :=
  simpleHighestVectorOf_pos_root_annihilate H κ hκ b lam hnz hα
    (VOA.RootDatum.chevalleyTripleForRoot H α).e_mem

/-- The affine positive node `e₀ = f_θ ⊗ t` annihilates the simple highest-weight vector
(Gannon §3.2; Kac §3.6). -/
theorem simpleHighestVectorOf_affineEZero_annihilate [Nonempty H.root]
    (hnz : highestVector H κ hκ b lam ≠ 0) :
    simpleHWRhoOf H κ hκ b lam hnz (VOA.RootDatum.affineEZero H κ hκ b)
      (simpleHighestVectorOf H κ hκ b lam hnz) = 0 := by
  rw [VOA.RootDatum.affineEZero]
  exact simpleHighestVectorOf_pos_loop_annihilate H κ hκ b lam hnz
    (VOA.RootDatum.highestChevalleyTriple H b).f 1 (by norm_num)

/-- Local nilpotence of a linear endomorphism (Gannon §3.2; Kac §3.6): every vector is killed by
some power of the operator. This is the target property for each affine Chevalley generator in the
Kac–Garland integrability argument. -/
def LocallyNilpotentEnd {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (T : Module.End ℂ V) : Prop :=
  ∀ v : V, ∃ n : ℕ, (T ^ n) v = 0

/-- Integrability for an affine representation, phrased as local nilpotence on a specified
Chevalley-generator set (Gannon §3.2; Kac §3.6). For highest-weight modules the set below supplies
the finite Chevalley root generators together with the affine node `e₀,f₀`. -/
def Integrable (V : Type*) [AddCommGroup V] [Module ℂ V]
    (ρ : AffineLie 𝔤 κ hκ →ₗ⁅ℂ⁆ Module.End ℂ V) (S : Set (AffineLie 𝔤 κ hκ)) : Prop :=
  ∀ X ∈ S, LocallyNilpotentEnd (ρ X)

/-- The affine Chevalley generators used for integrability: all finite-root Chevalley generators at
mode `0`, plus the affine node `e₀,f₀` attached to the highest root (Gannon §3.2; Kac §3.6). Using
all finite roots is a slightly stronger, basis-independent surface than only the simple finite
nodes, and contains the simple-node checks needed for Kac–Garland. -/
noncomputable def chevalleyGeneratorSet [Nonempty H.root] :
    Set (AffineLie 𝔤 κ hκ) :=
  {X | (∃ α : H.root, X =
          ofLoop κ hκ (VOA.RootDatum.chevalleyTripleForRoot H α).e 0)
      ∨ (∃ α : H.root, X =
          ofLoop κ hκ (VOA.RootDatum.chevalleyTripleForRoot H α).f 0)
      ∨ X = VOA.RootDatum.affineEZero H κ hκ b
      ∨ X = VOA.RootDatum.affineFZero H κ hκ b}

/-- Integrability of the conditional simple highest-weight module `L(λ)`: the Chevalley
generators act locally nilpotently (Gannon §3.2; Kac §3.6). This is the exact theorem-shaped
target left for the Kac–Garland `sl₂`-string argument. -/
def SimpleHWIntegrable [Nonempty H.root] (hnz : highestVector H κ hκ b lam ≠ 0) : Prop :=
  Integrable κ hκ (simpleHWOf H κ hκ b lam hnz) (simpleHWRhoOf H κ hκ b lam hnz)
    (chevalleyGeneratorSet H κ hκ b)

/-- ⚠ **A tautology.**  `SimpleHWIntegrable` *is* (unfolds to) local nilpotence of the Chevalley
generators, so the hypothesis `hKG` is the conclusion and the proof is `exact hKG`.  It records
the target of the Kac–Garland `sl₂`-string argument (Gannon §3.2; Kac §3.6) but proves nothing:
integrability of `L(λ)` is not established in the library. -/
theorem simpleHWOf_integrable_of_chevalley_locallyNilpotent [Nonempty H.root]
    (hnz : highestVector H κ hκ b lam ≠ 0)
    (hKG : ∀ X ∈ chevalleyGeneratorSet H κ hκ b,
      LocallyNilpotentEnd (simpleHWRhoOf H κ hκ b lam hnz X)) :
    SimpleHWIntegrable H κ hκ b lam hnz := by
  exact hKG

end AffineLie
end VOA
