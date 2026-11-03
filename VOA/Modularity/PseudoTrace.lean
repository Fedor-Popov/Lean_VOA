/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SymmetricFunctionals
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Pseudo-traces of endomorphisms of projective modules

`SemisimpleTrace.lean` and `SymmetricFunctionals.lean` establish that for a **completely general**
`K`-algebra `A` the symmetric linear functionals `φ(ab) = φ(ba)` are canonically the dual of the
commutator quotient, `symmetricFunctionals K A ≃ₗ[K] (A ⧸ [A,A])*`.  What Miyamoto's theorem
(*Modular invariance of vertex operator algebras satisfying `C₂`-cofiniteness*, Duke Math. J.
**122** (2004) 51–91) needs next is a way to *realize* such a `φ` as a trace-like function on a
module, when `A` is **not** semisimple and "trace of a simple module" is therefore the wrong
notion.  The replacement is the **pseudo-trace**.

## Which definition is formalized, and why

Miyamoto's own §3 definition fixes a basic symmetric indecomposable algebra `(P, φ)`, builds an
explicit basis `Ω` of `P` out of a socle/radical filtration, and defines `tr^φ_W` by summing
matrix entries in that basis.  Arike (*Some remarks on symmetric linear functions and pseudotrace
maps*, arXiv:1001.2696) proved that this equals a much simpler and far more general object
(his §2, and Theorem 3.10 for the comparison): for an **arbitrary** `K`-algebra `A`, an
**arbitrary** finitely generated projective `A`-module `W`, and an arbitrary symmetric `φ`,

  `tr^φ_W = φ̄ ∘ T_W`,   `T_W : End_A(W) → A ⧸ [A,A]`  the **Hattori–Stallings trace**.

That is what is formalized here, following Arike §2 and Steffen (arXiv:2606.19622, Def. 3.3).
Consequences of this choice, all deliberate:

* **No semisimplicity, no finite-dimensionality of `A`, no algebraic closure of `K`, and no
  Frobenius/symmetric-algebra structure appears anywhere in this file.**  Being a symmetric
  algebra is a *theorem about* `A ⧸ Rad(φ)` (Arike §5), not a hypothesis of the construction, so
  no such typeclass is carried.  The only hypotheses on `W` are `Module.Finite A W` and
  `Module.Projective A W`.
* `Mathlib` has no tensor product over a noncommutative ring, so Steffen's coordinate-free
  `W ⊗_A Hom_A(W,A) → End_A(W)` route is unavailable.  We use **coordinate systems** (Bourbaki
  *Algèbre* II §2.6 Prop. 12) and prove independence of the choice by hand.
* Mathlib's modules are **left** modules, so `W` here is a left `A`-module, where Miyamoto and
  Arike use right modules.  This is the harmless side convention Steffen §3.1 also notes.

## Main results

### Coordinate systems
* `FinCoords A W` — the data `(uᵢ, αᵢ)ᵢ<ⁿ` with `αᵢ : W →ₗ[A] A` and `∑ᵢ αᵢ(w) • uᵢ = w`;
* `FinCoords.nonempty_of_finite_projective` and, conversely, `FinCoords.finite`,
  `FinCoords.projective` — finite coordinate systems exist for **exactly** the finitely generated
  projective modules, so the pseudo-trace is defined on exactly the right class;
* `FinCoords.ofBasis` — the coordinate system of a finite basis.

### The Hattori–Stallings trace
* `FinCoords.rawTraceComp` and `FinCoords.rawTraceComp_sub_mem_commSpan` — **the one
  computation everything rests on**: `∑ᵢ αᵢ(f (g uᵢ)) ≡ ∑ⱼ βⱼ(g (f vⱼ))` mod `[A,A]`, for
  `g : W →ₗ[A] X`, `f : X →ₗ[A] W` and any coordinate systems of `W` and `X`.  Independence of
  the coordinate system (`FinCoords.rawTrace_sub_rawTrace_mem_commSpan`, take `X = W`, `g = id`)
  and cyclicity (`FinCoords.rawTrace_mul_sub_mem_commSpan`, take `X = W`, one coordinate system)
  are both instances;
* `hattoriTrace K A W : Module.End A W →ₗ[K] (A ⧸ commSpan K A)` — the trace itself, with
  `hattoriTrace_apply_of_coords` saying it is computed by *any* coordinate system;
* `hattoriTrace_comp_comm` (cross-module cyclicity, Arike–Nagatomo Prop. 4.2) and its
  special case `hattoriTrace_mul_comm`.

### The pseudo-trace
* `pseudoTrace W φ = symmetricLift φ ∘ₗ hattoriTrace K A W : Module.End A W →ₗ[K] K`;
* `pseudoTrace_mem_symmetricFunctionals` — **Arike, Proposition 2.1**: `tr^φ_W` is itself a
  symmetric linear functional on `End_A(W)`.  This is the statement that hands the construction
  back to `SymmetricFunctionals.lean`, so the process can be iterated;
* `pseudoTrace_comp_comm` — cyclicity across two modules;
* `pseudoTraceMap W : symmetricFunctionals K A →ₗ[K] symmetricFunctionals K (Module.End A W)`
  — the bundled, `K`-linear transport `S(A) → S(End_A W)`.

### Validation — that this *is* the trace
A pseudo-trace that did not reduce to the ordinary trace would be the wrong definition.  Three
independent checks:
* `pseudoTrace_idSymmetric_eq_trace` — for `A = K` a field and `φ = id`,
  `pseudoTrace W (idSymmetric K) f = LinearMap.trace K W f` for every endomorphism of a
  finite-dimensional `K`-vector space.  **This is the decisive check**;
* `hattoriTrace_pi` — on the free module `Fin n → A` over a possibly noncommutative `A`, the
  trace is the class of the sum of the diagonal matrix entries, `∑ᵢ (f (Pi.single i 1)) i`; and
  `hattoriTrace_pi_one` gives `[n · 1]` for the identity, matching `LinearMap.trace_id`;
* `pseudoTrace_rightMulEnd` — on the **left regular module** `A`, `tr^φ_A` of right
  multiplication by `a` is `φ(a)` on the nose.  Hence **every** symmetric functional on `A` is
  realized as a pseudo-trace of a finitely generated projective module
  (`pseudoTraceMap_regular_injective`), which is the construction direction Miyamoto's spanning
  argument consumes.

## Deliberately not here

* Miyamoto's Definition 3.6 verbatim (his basis `Ω` from Lemma 3.2), and Arike Theorem 3.10
  identifying it with this one.  Arike's definition is adopted from the start, which makes the
  identification unnecessary for our purposes.
* `Rad(φ) = {a | φ(Aa) = 0}` and the theorem that `A ⧸ Rad(φ)` is a symmetric algebra.  Not needed
  by the construction; a candidate for a separate file.
* Basic algebras `eAe`, Morita theory, `SLF(A) ≅ SLF(eAe)` (Arike Thm 5.6), Nesbitt–Scott, socle
  theory, block theory of `A ⧸ rad A`.  None of this is in Mathlib and none of it is needed: the
  dimension that Miyamoto's Theorem 5.5 produces is `dim_K (A ⧸ [A,A])`, which
  `SymmetricFunctionals.finrank_symmetricFunctionals_eq_finrank_quot_commSpan` already delivers
  intrinsically.  The DLM step that converted such a dimension into a count of simple modules is
  exactly the step Miyamoto's theorem removes.
* Additivity of `hattoriTrace` in `W` over a direct sum.  Not attempted; not needed yet.

## Status
Proved, axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only), `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open Module (finrank)

/-! ## Finite coordinate systems -/

/-- A **finite `A`-coordinate system** for a left `A`-module `W`. -/
structure FinCoords (A : Type*) [Ring A] (W : Type*) [AddCommGroup W] [Module A W] where
  /-- The number of generators. -/
  card : ℕ
  /-- The generators. -/
  gen : Fin card → W
  /-- The coordinate functionals. -/
  coord : Fin card → (W →ₗ[A] A)
  /-- The reproducing identity. -/
  total : ∀ w : W, ∑ i, coord i w • gen i = w

namespace FinCoords

variable {A : Type*} [Ring A] {W : Type*} [AddCommGroup W] [Module A W]

/-- A finitely generated projective module admits a finite coordinate system. -/
theorem nonempty_of_finite_projective (A : Type*) [Ring A] (W : Type*) [AddCommGroup W]
    [Module A W] [Module.Finite A W] [Module.Projective A W] : Nonempty (FinCoords A W) := by
  classical
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A W
  refine ⟨{ card := n
            gen := fun i => f (Pi.single i 1)
            coord := fun i => (LinearMap.proj i) ∘ₗ g
            total := ?_ }⟩
  intro w
  have hg : ∑ i, (g w i) • (Pi.single i (1 : A) : Fin n → A) = g w := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  have : ∑ i, ((LinearMap.proj i) ∘ₗ g) w • f (Pi.single i (1 : A))
      = f (∑ i, (g w i) • (Pi.single i (1 : A) : Fin n → A)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (f.map_smul _ _).symm
  rw [this, hg]
  exact congrArg (fun h => h w) hfg

/-- The `A`-linear map `W →ₗ[A] (Fin c.card → A)` assembled from the coordinate
functionals. -/
def toPi (c : FinCoords A W) : W →ₗ[A] (Fin c.card → A) :=
  LinearMap.pi c.coord

/-- The `A`-linear map `(Fin c.card → A) →ₗ[A] W` assembled from the generators. -/
def ofPi (c : FinCoords A W) : (Fin c.card → A) →ₗ[A] W where
  toFun v := ∑ j, v j • c.gen j
  map_add' v w := by simp only [Pi.add_apply, add_smul]; exact Finset.sum_add_distrib
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

theorem ofPi_comp_toPi (c : FinCoords A W) : c.ofPi ∘ₗ c.toPi = LinearMap.id :=
  LinearMap.ext c.total

/-- A module with a finite coordinate system is finitely generated. -/
theorem finite (c : FinCoords A W) : Module.Finite A W :=
  Module.Finite.of_surjective c.ofPi (fun w => ⟨c.toPi w, c.total w⟩)

/-- A module with a finite coordinate system is projective.  Together with
`nonempty_of_finite_projective` this says that finite coordinate systems exist for **exactly**
the finitely generated projective modules — the class on which the pseudo-trace is defined. -/
theorem projective (c : FinCoords A W) : Module.Projective A W :=
  Module.Projective.of_split c.toPi c.ofPi (c.ofPi_comp_toPi)

/-- The un-quotiented Hattori–Stallings sum. -/
def rawTrace (c : FinCoords A W) (f : Module.End A W) : A :=
  ∑ i, c.coord i (f (c.gen i))

theorem rawTrace_def (c : FinCoords A W) (f : Module.End A W) :
    c.rawTrace f = ∑ i, c.coord i (f (c.gen i)) := rfl

/-! ### The composable-pair sum

Everything below rests on a single computation: the Hattori–Stallings sum of a composable pair
`g : W →ₗ[A] X`, `f : X →ₗ[A] W` computed in a coordinate system for `W` agrees, modulo
commutators, with the one for the reversed pair computed in a coordinate system for `X`
(Arike–Nagatomo, Prop. 4.2; Steffen, §3.1).  Both *independence of the coordinate system*
(take `X = W`, `g = id`, `c ≠ d`) and *cyclicity* (take `X = W`, `c = d`) are instances of it. -/

section Comp

variable {X : Type*} [AddCommGroup X] [Module A X]

/-- The **un-quotiented Hattori–Stallings sum of a composable pair** `g : W →ₗ[A] X`,
`f : X →ₗ[A] W`, computed in a coordinate system `c` for `W`: `∑ᵢ αᵢ (f (g uᵢ))`. -/
def rawTraceComp (c : FinCoords A W) (f : X →ₗ[A] W) (g : W →ₗ[A] X) : A :=
  ∑ i, c.coord i (f (g (c.gen i)))

/-- `rawTrace` is the `g = id` case of `rawTraceComp`. -/
theorem rawTraceComp_id (c : FinCoords A W) (f : Module.End A W) :
    c.rawTraceComp f LinearMap.id = c.rawTrace f := rfl

/-- For two endomorphisms of the same module, `rawTraceComp` is `rawTrace` of the product. -/
theorem rawTraceComp_self (c : FinCoords A W) (f g : Module.End A W) :
    c.rawTraceComp f g = c.rawTrace (f * g) := rfl

/-- Expansion of `c.rawTraceComp f g` through a coordinate system `d` for `X`. -/
theorem rawTraceComp_eq_double (c : FinCoords A W) (d : FinCoords A X)
    (f : X →ₗ[A] W) (g : W →ₗ[A] X) :
    c.rawTraceComp f g = ∑ i, ∑ j, d.coord j (g (c.gen i)) * c.coord i (f (d.gen j)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : c.coord i (f (g (c.gen i)))
      = c.coord i (f (∑ j, d.coord j (g (c.gen i)) • d.gen j)) := by rw [d.total]
  rw [h]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Expansion of `d.rawTraceComp g f` through a coordinate system `c` for `W`. -/
theorem rawTraceComp_eq_double' (c : FinCoords A W) (d : FinCoords A X)
    (f : X →ₗ[A] W) (g : W →ₗ[A] X) :
    d.rawTraceComp g f = ∑ j, ∑ i, c.coord i (f (d.gen j)) * d.coord j (g (c.gen i)) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : d.coord j (g (f (d.gen j)))
      = d.coord j (g (∑ i, c.coord i (f (d.gen j)) • c.gen i)) := by rw [c.total]
  rw [h]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- **The master commutator identity.**  `∑ᵢ αᵢ (f (g uᵢ)) ≡ ∑ⱼ βⱼ (g (f vⱼ))` modulo
`[A,A]`, for any coordinate systems `c = (u,α)` of `W` and `d = (v,β)` of `X`.  Both the
independence of the Hattori–Stallings trace from the coordinate system and its cyclicity are
special cases. -/
theorem rawTraceComp_sub_mem_commSpan (K : Type*) [Field K] [Algebra K A]
    (c : FinCoords A W) (d : FinCoords A X) (f : X →ₗ[A] W) (g : W →ₗ[A] X) :
    c.rawTraceComp f g - d.rawTraceComp g f ∈ commSpan K A := by
  rw [rawTraceComp_eq_double c d f g, rawTraceComp_eq_double' c d f g, Finset.sum_comm
    (s := (Finset.univ : Finset (Fin d.card))) (t := (Finset.univ : Finset (Fin c.card))),
    ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun j _ => mul_sub_mul_mem_commSpan _ _

end Comp

section WithBase

variable (K : Type*) [Field K] [Algebra K A] [Module K W] [IsScalarTower K A W]

omit [Module K W] [IsScalarTower K A W] in
/-- **Independence of the coordinate system, modulo commutators.** -/
theorem rawTrace_sub_rawTrace_mem_commSpan (c d : FinCoords A W) (f : Module.End A W) :
    c.rawTrace f - d.rawTrace f ∈ commSpan K A :=
  rawTraceComp_sub_mem_commSpan K c d f LinearMap.id

omit [Module K W] [IsScalarTower K A W] in
/-- `rawTrace` is additive in the endomorphism. -/
theorem rawTrace_add (c : FinCoords A W) (f g : Module.End A W) :
    c.rawTrace (f + g) = c.rawTrace f + c.rawTrace g := by
  simp only [rawTrace, LinearMap.add_apply, map_add]
  exact Finset.sum_add_distrib

/-- `rawTrace` is `K`-homogeneous in the endomorphism. -/
theorem rawTrace_smul (c : FinCoords A W) (k : K) (f : Module.End A W) :
    c.rawTrace (k • f) = k • c.rawTrace f := by
  simp only [rawTrace, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (k • f) (c.gen i) = (algebraMap K A k) • f (c.gen i) := by
    rw [IsScalarTower.algebraMap_smul]; rfl
  rw [h1, map_smul, smul_eq_mul, Algebra.smul_def]

/-- The Hattori–Stallings trace computed from one coordinate system. -/
noncomputable def traceQuot (c : FinCoords A W) :
    Module.End A W →ₗ[K] (A ⧸ commSpan K A) where
  toFun f := (commSpan K A).mkQ (c.rawTrace f)
  map_add' f g := by rw [rawTrace_add, map_add]
  map_smul' k f := by rw [rawTrace_smul, map_smul]; rfl

@[simp] theorem traceQuot_apply (c : FinCoords A W) (f : Module.End A W) :
    traceQuot K c f = (commSpan K A).mkQ (c.rawTrace f) := rfl

/-- Any two coordinate systems give the same trace. -/
theorem traceQuot_eq (c d : FinCoords A W) : traceQuot K c = traceQuot K d := by
  refine LinearMap.ext fun f => ?_
  rw [traceQuot_apply, traceQuot_apply, ← sub_eq_zero, ← map_sub,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact rawTrace_sub_rawTrace_mem_commSpan K c d f

omit [Module K W] [IsScalarTower K A W] in
/-- **Cyclicity**, at the level of the un-quotiented sum. -/
theorem rawTrace_mul_sub_mem_commSpan (c : FinCoords A W) (f g : Module.End A W) :
    c.rawTrace (f * g) - c.rawTrace (g * f) ∈ commSpan K A :=
  rawTraceComp_sub_mem_commSpan K c c f g

end WithBase

end FinCoords

/-! ## The Hattori–Stallings trace -/

section HattoriTrace

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A]
variable (W : Type*) [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower K A W]
variable [Module.Finite A W] [Module.Projective A W]

/-- **The Hattori–Stallings trace.** -/
noncomputable def hattoriTrace : Module.End A W →ₗ[K] (A ⧸ commSpan K A) :=
  FinCoords.traceQuot K (FinCoords.nonempty_of_finite_projective A W).some

variable {K A W}

/-- The Hattori–Stallings trace is computed by *any* finite coordinate system. -/
theorem hattoriTrace_apply_of_coords (c : FinCoords A W) (f : Module.End A W) :
    hattoriTrace K A W f = (commSpan K A).mkQ (c.rawTrace f) := by
  rw [hattoriTrace, FinCoords.traceQuot_eq K _ c, FinCoords.traceQuot_apply]

/-- **Cyclicity of the Hattori–Stallings trace across two modules** (Arike–Nagatomo,
Prop. 4.2; Steffen, §3.1): for `g : W →ₗ[A] X` and `f : X →ₗ[A] W` with both `W` and `X`
finitely generated projective, `T_W (f ∘ g) = T_X (g ∘ f)`. -/
theorem hattoriTrace_comp_comm {X : Type*} [AddCommGroup X] [Module A X] [Module K X]
    [IsScalarTower K A X] [Module.Finite A X] [Module.Projective A X]
    (f : X →ₗ[A] W) (g : W →ₗ[A] X) :
    hattoriTrace K A W (f ∘ₗ g) = hattoriTrace K A X (g ∘ₗ f) := by
  set c := (FinCoords.nonempty_of_finite_projective A W).some with hc
  set d := (FinCoords.nonempty_of_finite_projective A X).some with hd
  rw [hattoriTrace_apply_of_coords c, hattoriTrace_apply_of_coords d, ← sub_eq_zero, ← map_sub,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact FinCoords.rawTraceComp_sub_mem_commSpan K c d f g

/-- **Cyclicity of the Hattori–Stallings trace.**  The `X = W` case of
`hattoriTrace_comp_comm`. -/
theorem hattoriTrace_mul_comm (f g : Module.End A W) :
    hattoriTrace K A W (f * g) = hattoriTrace K A W (g * f) :=
  hattoriTrace_comp_comm f g

/-- The Hattori–Stallings trace of the identity is the class of `∑ᵢ αᵢ (uᵢ)`, the
"rank" of `W` in `A ⧸ [A,A]`. -/
theorem hattoriTrace_one_of_coords (c : FinCoords A W) :
    hattoriTrace K A W (1 : Module.End A W) = (commSpan K A).mkQ (∑ i, c.coord i (c.gen i)) := by
  rw [hattoriTrace_apply_of_coords c]
  rfl

end HattoriTrace

/-! ## The pseudo-trace -/

section PseudoTrace

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (W : Type*) [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower K A W]
variable [Module.Finite A W] [Module.Projective A W]

/-- **The pseudo-trace** `tr^φ_W = φ̄ ∘ T_W`. -/
noncomputable def pseudoTrace (φ : symmetricFunctionals K A) : Module.End A W →ₗ[K] K :=
  (symmetricLift φ) ∘ₗ hattoriTrace K A W

variable {W}

@[simp] theorem pseudoTrace_apply (φ : symmetricFunctionals K A) (f : Module.End A W) :
    pseudoTrace W φ f = symmetricLift φ (hattoriTrace K A W f) := rfl

/-- The pseudo-trace is computed by *any* finite coordinate system. -/
theorem pseudoTrace_apply_of_coords (φ : symmetricFunctionals K A) (c : FinCoords A W)
    (f : Module.End A W) :
    pseudoTrace W φ f = (φ : A →ₗ[K] K) (c.rawTrace f) := by
  rw [pseudoTrace_apply, hattoriTrace_apply_of_coords c, symmetricLift_apply_mk]

/-- **Arike, Proposition 2.1.** -/
theorem pseudoTrace_mem_symmetricFunctionals (φ : symmetricFunctionals K A) :
    pseudoTrace W φ ∈ symmetricFunctionals K (Module.End A W) := by
  rw [mem_symmetricFunctionals]
  intro f g
  rw [pseudoTrace_apply, pseudoTrace_apply, hattoriTrace_mul_comm]

/-- **Cyclicity of the pseudo-trace across two modules** (Steffen, §3.1):
`tr^φ_W (f ∘ g) = tr^φ_X (g ∘ f)`. -/
theorem pseudoTrace_comp_comm {X : Type*} [AddCommGroup X] [Module A X] [Module K X]
    [IsScalarTower K A X] [Module.Finite A X] [Module.Projective A X]
    (φ : symmetricFunctionals K A) (f : X →ₗ[A] W) (g : W →ₗ[A] X) :
    pseudoTrace W φ (f ∘ₗ g) = pseudoTrace X φ (g ∘ₗ f) := by
  rw [pseudoTrace_apply, pseudoTrace_apply, hattoriTrace_comp_comm]

variable (W)

/-- The bundled transport `S(A) →ₗ[K] S(End_A W)`. -/
noncomputable def pseudoTraceMap :
    symmetricFunctionals K A →ₗ[K] symmetricFunctionals K (Module.End A W) where
  toFun φ := ⟨pseudoTrace W φ, pseudoTrace_mem_symmetricFunctionals φ⟩
  map_add' φ ψ := by
    refine Subtype.ext (LinearMap.ext fun f => ?_)
    change symmetricLift (φ + ψ) (hattoriTrace K A W f) = _
    rw [map_add]
    rfl
  map_smul' k φ := by
    refine Subtype.ext (LinearMap.ext fun f => ?_)
    change symmetricLift (k • φ) (hattoriTrace K A W f) = _
    rw [map_smul]
    rfl

variable {W}

@[simp] theorem pseudoTraceMap_apply (φ : symmetricFunctionals K A) :
    (pseudoTraceMap W φ : Module.End A W →ₗ[K] K) = pseudoTrace W φ := rfl

end PseudoTrace

/-! ## Coordinate systems from a basis -/

section OfBasis

variable {A : Type*} [Ring A] {W : Type*} [AddCommGroup W] [Module A W]

/-- The finite coordinate system attached to a finite basis. -/
noncomputable def FinCoords.ofBasis {n : ℕ} (b : Module.Basis (Fin n) A W) : FinCoords A W where
  card := n
  gen := b
  coord := fun i => b.coord i
  total := fun w => by simp

@[simp] theorem FinCoords.ofBasis_rawTrace {n : ℕ} (b : Module.Basis (Fin n) A W)
    (f : Module.End A W) :
    (FinCoords.ofBasis b).rawTrace f = ∑ i, b.coord i (f (b i)) := rfl

end OfBasis

/-! ## Validation 1: the left regular module -/

section Regular

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

/-- Right multiplication by `a`, as an `A`-endomorphism of the left regular module `A`. -/
def rightMulEnd (a : A) : Module.End A A where
  toFun x := x * a
  map_add' x y := add_mul x y a
  map_smul' b x := mul_assoc b x a

@[simp] theorem rightMulEnd_apply (a x : A) : rightMulEnd a x = x * a := rfl

/-- The one-element coordinate system `⟨1, id⟩` of the left regular module. -/
def FinCoords.regular (A : Type*) [Ring A] : FinCoords A A where
  card := 1
  gen := fun _ => 1
  coord := fun _ => LinearMap.id
  total := fun w => by simp

@[simp] theorem FinCoords.regular_rawTrace (f : Module.End A A) :
    (FinCoords.regular A).rawTrace f = f 1 := by
  simp [FinCoords.rawTrace, FinCoords.regular]

/-- On the left regular module the Hattori–Stallings trace of right multiplication by `a`
is the class of `a`. -/
theorem hattoriTrace_rightMulEnd (a : A) :
    hattoriTrace K A A (rightMulEnd a) = (commSpan K A).mkQ a := by
  rw [hattoriTrace_apply_of_coords (FinCoords.regular A), FinCoords.regular_rawTrace,
    rightMulEnd_apply, one_mul]

/-- **Every symmetric functional is realized as a pseudo-trace.** -/
theorem pseudoTrace_rightMulEnd (φ : symmetricFunctionals K A) (a : A) :
    pseudoTrace A φ (rightMulEnd a) = (φ : A →ₗ[K] K) a := by
  rw [pseudoTrace_apply, hattoriTrace_rightMulEnd, symmetricLift_apply_mk]

/-- The transport along the left regular module is injective. -/
theorem pseudoTraceMap_regular_injective :
    Function.Injective (pseudoTraceMap (K := K) (A := A) A) := by
  intro φ ψ h
  refine Subtype.ext (LinearMap.ext fun a => ?_)
  have h2 : (pseudoTraceMap (K := K) (A := A) A φ : Module.End A A →ₗ[K] K) (rightMulEnd a)
      = (pseudoTraceMap (K := K) (A := A) A ψ : Module.End A A →ₗ[K] K) (rightMulEnd a) := by
    rw [h]
  simpa only [pseudoTraceMap_apply, pseudoTrace_rightMulEnd] using h2

end Regular

/-! ## Validation 2: the ordinary trace -/

section OrdinaryTrace

variable (K : Type*) [Field K]

/-- The identity functional on `K`, viewed as a symmetric linear functional. -/
def idSymmetric : symmetricFunctionals K K :=
  ⟨LinearMap.id, fun a b => by simp [mul_comm]⟩

@[simp] theorem idSymmetric_apply (x : K) : (idSymmetric K : K →ₗ[K] K) x = x := rfl

variable {K}
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **The pseudo-trace reduces to the ordinary trace.** -/
theorem pseudoTrace_idSymmetric_eq_trace (f : Module.End K W) :
    pseudoTrace W (idSymmetric K) f = LinearMap.trace K W f := by
  classical
  have hb := Module.finBasis K W
  rw [pseudoTrace_apply_of_coords _ (FinCoords.ofBasis hb), FinCoords.ofBasis_rawTrace,
    idSymmetric_apply, LinearMap.trace_eq_matrix_trace K hb]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end OrdinaryTrace

/-! ## Validation 3: free modules and the matrix diagonal -/

section Free

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

/-- On the free module `Fin n → A` over a possibly noncommutative `A`, the
Hattori–Stallings trace of `f` is the class of the sum of the diagonal entries of the matrix
of `f`.  This is the classical "trace of a matrix, read modulo commutators". -/
theorem hattoriTrace_pi (n : ℕ) (f : Module.End A (Fin n → A)) :
    hattoriTrace K A (Fin n → A) f = (commSpan K A).mkQ (∑ i, f (Pi.single i 1) i) := by
  classical
  rw [hattoriTrace_apply_of_coords (FinCoords.ofBasis (Pi.basisFun A (Fin n))),
    FinCoords.ofBasis_rawTrace]
  simp [Module.Basis.coord_apply]

/-- Sanity check: on `Fin n → A` the Hattori–Stallings trace of the identity is the class of
`n · 1`, matching `LinearMap.trace_id`. -/
theorem hattoriTrace_pi_one (n : ℕ) :
    hattoriTrace K A (Fin n → A) (1 : Module.End A (Fin n → A))
      = (commSpan K A).mkQ (n : A) := by
  classical
  rw [hattoriTrace_pi]
  congr 1
  simp

/-- The pseudo-trace on a free module is `φ` of the matrix diagonal sum. -/
theorem pseudoTrace_pi (n : ℕ) (φ : symmetricFunctionals K A)
    (f : Module.End A (Fin n → A)) :
    pseudoTrace (Fin n → A) φ f = (φ : A →ₗ[K] K) (∑ i, f (Pi.single i 1) i) := by
  rw [pseudoTrace_apply, hattoriTrace_pi, symmetricLift_apply_mk]

end Free

end VOA
