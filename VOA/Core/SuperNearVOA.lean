/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperVertexOperatorAlgebra

/-!
# Super near-VOAs — the conformal layer without the CFT-type conditions

A **super near-VOA** is a `SuperVertexAlgebra` together with its whole Virasoro /
grading / translation layer (`ω`, `c`, VOA1–VOA3), but **without** the two CFT-type
conditions VOA4: `𝒱₀ = ℂ𝟙` (`vacuum_grade`) and "no weights of negative real part"
(`positivity`).  It is the super analogue of the bosonic `NearVOA`
(`Core.VertexOperatorAlgebra`, Gannon Def. 5.1.3(c)).

## Why the CFT-type conditions have to go

Both are *not inherited* by the structures we actually need to build:

* **`positivity` fails in the ambient algebra.**  The doublet's ambient lattice-type
  algebra has states of **negative** conformal weight; only the subalgebra we finally
  carve out of it is positive.  So positivity cannot be a hypothesis of the ambient
  object — it must be *proved for each subalgebra separately*, which is impossible if the
  ambient structure is required to have it already.
* **`vacuum_grade` fails for subalgebras of the wrong kind** and, more importantly, is not
  needed by any of the intermediate constructions; carrying it forces spurious proof
  obligations at every intermediate step.

What the module machinery downstream actually needs is not positivity but the weaker
**bounded below**: the weights that occur have real parts bounded below by *some* real
number, not necessarily `0`.  That is recorded here as a separate `Prop`
(`SuperNearVOA.BoundedBelow`) rather than as a structure field, exactly so that a
structure can be built first and the bound established afterwards.

## Main definitions

* `homogProj` — the homogeneous projection attached to *any* internal grading, together
  with the four facts about it (`_apply`, `_mem`, `_of_mem`, `_of_mem_ne`) and the two
  structural lemmas `homogProj_comm` (a grading-preserving operator commutes with the
  projections) and `isInternal_comap` (a subspace closed under the projections inherits
  the grading).  These are stated for a bare `DirectSum.Decomposition`, because they are
  needed *twice over* — once for the `ℂ`-valued weight grading and once for the `ZMod 2`
  parity grading.
* `SuperNearVOA` — the structure.
* `SuperNearVOA.wtProj` / `SuperNearVOA.parProj` — the weight and parity projections.
* `SuperNearVOA.BoundedBelow` — the weak substitute for `positivity`.
* `SuperNearVOA.toSVOA` — upgrade to a `SuperVertexOperatorAlgebra` once `vacuum_grade`
  and `positivity` *are* available.
* `SuperVertexOperatorAlgebra.toSuperNearVOA` — the forgetful map the other way.

## The two gradings are compatible — and this is a theorem, not an axiom

`SuperVertexAlgebra` deliberately keeps the weight grading and the parity grading
unlinked (no spin–statistics).  One might therefore fear that the weight projection of an
even vector need not be even, which would wreck the even-part construction.  It does not:

* `ω` is even (`conformal_parity`), so `L₀ = ω₍₁₎` preserves each parity space
  (`parity_L0_stable`) by `parity_mode`;
* the weight spaces are *exactly* the `L₀`-eigenspaces (`mem_grading_of_L0_eq`), because
  the weight grading is an internal direct sum;
* hence the parity projections preserve each weight space (`parProj_mem_grading`), the two
  projections commute (`wtProj_parProj_comm`), and finally the weight projections preserve
  each parity space (`wtProj_mem_parity`).

This is what makes `evenPart` a *graded* subalgebra downstream.  Note that none of it is
spin–statistics: it says the two gradings are simultaneously diagonalizable, not that one
determines the other.  (For symplectic fermions spin–statistics genuinely fails — the odd
fields have integer weight — while this compatibility of course holds.)

## References
* Gannon Def. 5.1.3(c) (near-VOAs); Kac, *Vertex Algebras for Beginners*, §4.1.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

/-! ## Homogeneous projections of an arbitrary internal grading

Everything in this section is grading-agnostic: it is applied below both to the `ℂ`-valued
conformal-weight grading and to the `ZMod 2` parity grading, and again in
`Core.SuperVOASubalgebra` to the induced gradings on a subalgebra. -/

section HomogProj

variable {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
  (A : ι → Submodule ℂ M) [DirectSum.Decomposition A]

/-- The **homogeneous projection** `π_i : M → A i` of an internal grading, viewed as an
endomorphism of `M`.  (The bosonic special case is `piHom`; this version is stated for a
bare `DirectSum.Decomposition` so that the parity grading can use it too.) -/
noncomputable def homogProj (i : ι) : M →ₗ[ℂ] M :=
  (A i).subtype.comp
    ((DirectSum.component ℂ ι (fun j => (A j : Submodule ℂ M)) i).comp
      (DirectSum.decomposeLinearEquiv A).toLinearMap)

theorem homogProj_apply (i : ι) (x : M) :
    homogProj A i x = ((DirectSum.decompose A x) i : M) := rfl

/-- The projection lands in the piece it projects onto. -/
theorem homogProj_mem (i : ι) (x : M) : homogProj A i x ∈ A i := by
  rw [homogProj_apply]
  exact ((DirectSum.decompose A x) i).2

/-- On its own piece the projection is the identity. -/
theorem homogProj_of_mem {i : ι} {x : M} (hx : x ∈ A i) : homogProj A i x = x := by
  rw [homogProj_apply]
  have hdec : DirectSum.decompose A x
      = DirectSum.of (fun j => (A j : Submodule ℂ M)) i ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun j => (A j : Submodule ℂ M)) (⟨x, hx⟩ : A i)
  rw [hdec]
  simp

/-- On a different piece the projection vanishes. -/
theorem homogProj_of_mem_ne {i j : ι} (hji : j ≠ i) {x : M} (hx : x ∈ A j) :
    homogProj A i x = 0 := by
  rw [homogProj_apply]
  have hdec : DirectSum.decompose A x
      = DirectSum.of (fun k => (A k : Submodule ℂ M)) j ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun k => (A k : Submodule ℂ M)) (⟨x, hx⟩ : A j)
  rw [hdec]
  simp only [DirectSum.of_eq_of_ne (β := fun k => (A k : Submodule ℂ M))
    j i (⟨x, hx⟩ : A j) hji.symm, ZeroMemClass.coe_zero]

/-- **Every vector is a finite sum of its homogeneous projections**, and the projections
outside that finite set vanish.

Stated existentially rather than as a sum over `(DirectSum.decompose A x).support`, so that
the *statement* needs no decidability instance: with a `ℂ`-valued index the only available
`DecidableEq ℂ` is the classical one, and pinning it into statements makes them fragile to
instance mismatch downstream. -/
theorem exists_sum_homogProj (x : M) :
    ∃ s : Finset ι, (∑ i ∈ s, homogProj A i x = x) ∧ ∀ i ∉ s, homogProj A i x = 0 := by
  classical
  refine ⟨(DirectSum.decompose A x).support, DirectSum.sum_support_decompose A x, ?_⟩
  intro i hi
  rw [DFinsupp.notMem_support_iff] at hi
  rw [homogProj_apply, hi]
  rfl

/-- **An operator preserving every homogeneous piece commutes with every projection.**

This is the workhorse behind the weight/parity compatibility below: `L₀` preserves the
parity spaces, hence commutes with the parity projections, and the parity projections
preserve the weight spaces, hence commute with the weight projections. -/
theorem homogProj_comm (f : M →ₗ[ℂ] M) (hf : ∀ i : ι, ∀ x ∈ A i, f x ∈ A i) (i : ι) (x : M) :
    homogProj A i (f x) = f (homogProj A i x) := by
  obtain ⟨s, hs, hs0⟩ := exists_sum_homogProj A x
  have hsum : f x = ∑ j ∈ s, f (homogProj A j x) := by
    conv_lhs => rw [← hs]
    exact map_sum f _ _
  rw [hsum, map_sum, Finset.sum_eq_single i]
  · rw [homogProj_of_mem A (hf i _ (homogProj_mem A i x))]
  · intro j _ hji
    exact homogProj_of_mem_ne A hji (hf j _ (homogProj_mem A j x))
  · intro hi
    rw [hs0 i hi, map_zero, map_zero]

/-- **A subspace closed under the homogeneous projections inherits the grading.**

The induced family is `A i ∩ C`, spelled as a comap along `C.subtype`.  This is exactly the
bosonic `VOASubalgebra.gradingS_isInternal` argument, made grading-agnostic. -/
theorem isInternal_comap (C : Submodule ℂ M)
    (hC : ∀ i : ι, ∀ x ∈ C, homogProj A i x ∈ C) :
    DirectSum.IsInternal (fun i => (A i).comap C.subtype) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- independence: pull back the independence of `A` along the injective `subtype`
    have hA := (DirectSum.Decomposition.isInternal A).submodule_iSupIndep
    refine iSupIndep_def.mpr (fun i => ?_)
    rw [Submodule.disjoint_def]
    intro x hxi hxrest
    have h1 : (x : M) ∈ A i := hxi
    have h2 : (x : M) ∈ ⨆ (j) (_ : j ≠ i), A j := by
      have hmap : Submodule.map C.subtype (⨆ (j) (_ : j ≠ i), (A j).comap C.subtype)
          ≤ ⨆ (j) (_ : j ≠ i), A j := by
        rw [Submodule.map_iSup]
        refine iSup_mono (fun j => ?_)
        rw [Submodule.map_iSup]
        refine iSup_mono (fun _ => ?_)
        exact Submodule.map_comap_le _ _
      exact hmap ⟨x, hxrest, rfl⟩
    have hdisj := iSupIndep_def.mp hA i
    rw [Submodule.disjoint_def] at hdisj
    exact Subtype.ext (hdisj _ h1 h2)
  · -- spanning: every `x ∈ C` is the finite sum of its projections, all of which lie in `C`
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs, -⟩ := exists_sum_homogProj A (x : M)
    have hx : x = ∑ i ∈ s, (⟨homogProj A i (x : M), hC i x x.2⟩ : C) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hs.symm
    rw [hx]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.mem_iSup_of_mem i (homogProj_mem A i (x : M))

end HomogProj

/-! ## The structure -/

/-- A **super near-VOA**: a `SuperVertexAlgebra` with a conformal vector `ω`, a central
charge `c`, and VOA1–VOA3 — but **without** the CFT-type conditions VOA4
(`vacuum_grade`, `positivity`).

This is the super analogue of the bosonic `NearVOA` (Gannon Def. 5.1.3(c)).  Unlike the
bosonic one it is spelled as an extension of `SuperVertexAlgebra`, keeping the
finite-dimensionality of the weight spaces: the examples this is built for (symplectic
fermions, the doublet) all have finite-dimensional weight spaces, and what they *lack* is
positivity, not finite-dimensionality.

`ω` is required to be even (`conformal_parity`), as in `SuperVertexOperatorAlgebra`.  This
is a genuine axiom, not a consequence, since spin–statistics is not assumed — and it is
the hypothesis that makes the weight and parity gradings compatible (see the module
docstring). -/
structure SuperNearVOA (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱]
    extends SuperVertexAlgebra 𝒱 where
  /-- The conformal vector `ω`. -/
  conformalVector : 𝒱
  /-- `ω` has conformal weight `2`. -/
  conformal_mem : conformalVector ∈ grading 2
  /-- `ω` is even.  Not a theorem: spin–statistics is not assumed. -/
  conformal_parity : conformalVector ∈ parity 0
  /-- The central charge `c ∈ ℂ`. -/
  centralCharge : ℂ
  /-- **VOA1 (conformal symmetry).**  The modes `Lₙ = ω₍ₙ₊₁₎` satisfy the Virasoro
  relations; the mode index is `ℤ` whatever the conformal weights. -/
  virasoro : ∀ m n : ℤ,
      ⁅mode (Y conformalVector) (m + 1), mode (Y conformalVector) (n + 1)⁆
        = ((m : ℂ) - n) • mode (Y conformalVector) (m + n + 1)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * centralCharge) • (1 : End ℂ 𝒱)
             else 0)
  /-- **VOA2 (conformal weight).**  `L₀` acts on `𝒱_h` as multiplication by `h`. -/
  L0_grading : ∀ {h : ℂ} (v : 𝒱), v ∈ grading h → mode (Y conformalVector) 1 v = h • v
  /-- **VOA3 (translation generator).** `Y(L₋₁ v, z) = ∂_z Y(v,z)`. -/
  translation : ∀ v : 𝒱, Y (mode (Y conformalVector) 0 v) = deriv (Y v)

namespace SuperNearVOA

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ### The two projections -/

/-- The weight grading of a super near-VOA is an internal decomposition, so it has a
(noncomputably chosen, but unique — `Decomposition` is a subsingleton) decomposition
instance. -/
noncomputable instance wtDecomp (W : SuperNearVOA 𝒱) : DirectSum.Decomposition W.grading :=
  W.isInternal.chooseDecomposition W.grading

/-- Likewise for the parity grading. -/
noncomputable instance parDecomp (W : SuperNearVOA 𝒱) : DirectSum.Decomposition W.parity :=
  W.parity_isInternal.chooseDecomposition W.parity

/-- The **weight projection** `π_h` onto the conformal-weight-`h` subspace. -/
noncomputable def wtProj (W : SuperNearVOA 𝒱) (h : ℂ) : 𝒱 →ₗ[ℂ] 𝒱 := homogProj W.grading h

/-- The **parity projection** `π_p` onto the parity-`p` subspace. -/
noncomputable def parProj (W : SuperNearVOA 𝒱) (p : ZMod 2) : 𝒱 →ₗ[ℂ] 𝒱 :=
  homogProj W.parity p

theorem wtProj_mem (W : SuperNearVOA 𝒱) (h : ℂ) (v : 𝒱) : W.wtProj h v ∈ W.grading h :=
  homogProj_mem W.grading h v

theorem wtProj_of_mem (W : SuperNearVOA 𝒱) {h : ℂ} {v : 𝒱} (hv : v ∈ W.grading h) :
    W.wtProj h v = v :=
  homogProj_of_mem W.grading hv

theorem wtProj_of_mem_ne (W : SuperNearVOA 𝒱) {h k : ℂ} (hkh : k ≠ h) {v : 𝒱}
    (hv : v ∈ W.grading k) : W.wtProj h v = 0 :=
  homogProj_of_mem_ne W.grading hkh hv

theorem parProj_mem (W : SuperNearVOA 𝒱) (p : ZMod 2) (v : 𝒱) : W.parProj p v ∈ W.parity p :=
  homogProj_mem W.parity p v

theorem parProj_of_mem (W : SuperNearVOA 𝒱) {p : ZMod 2} {v : 𝒱} (hv : v ∈ W.parity p) :
    W.parProj p v = v :=
  homogProj_of_mem W.parity hv

theorem parProj_of_mem_ne (W : SuperNearVOA 𝒱) {p q : ZMod 2} (hqp : q ≠ p) {v : 𝒱}
    (hv : v ∈ W.parity q) : W.parProj p v = 0 :=
  homogProj_of_mem_ne W.parity hqp hv

/-- Every state is a finite sum of its weight components. -/
theorem exists_sum_wtProj (W : SuperNearVOA 𝒱) (v : 𝒱) :
    ∃ s : Finset ℂ, (∑ h ∈ s, W.wtProj h v = v) ∧ ∀ h ∉ s, W.wtProj h v = 0 :=
  exists_sum_homogProj W.grading v

/-- Every state is the sum of its even and odd parts. -/
theorem exists_sum_parProj (W : SuperNearVOA 𝒱) (v : 𝒱) :
    ∃ s : Finset (ZMod 2), (∑ p ∈ s, W.parProj p v = v) ∧ ∀ p ∉ s, W.parProj p v = 0 :=
  exists_sum_homogProj W.parity v

/-! ### The Virasoro modes -/

/-- The Virasoro mode `Lₙ := ω₍ₙ₊₁₎`, as in the bosonic and the CFT-type super cases. -/
noncomputable def L (W : SuperNearVOA 𝒱) (n : ℤ) : End ℂ 𝒱 :=
  mode (W.Y W.conformalVector) (n + 1)

theorem L_def (W : SuperNearVOA 𝒱) (n : ℤ) :
    W.L n = mode (W.Y W.conformalVector) (n + 1) := rfl

/-- **VOA2 through `L`.**  With a `ℂ`-valued grading index the eigenvalue *is* the index. -/
theorem L0_eigenvalue (W : SuperNearVOA 𝒱) {h : ℂ} {v : 𝒱} (hv : v ∈ W.grading h) :
    W.L 0 v = h • v := by
  change mode (W.Y W.conformalVector) (0 + 1) v = h • v
  rw [zero_add]
  exact W.L0_grading v hv

/-- **VOA1 through `L`**: the Virasoro relation, verbatim the bosonic one. -/
theorem virasoro_L (W : SuperNearVOA 𝒱) (m n : ℤ) :
    ⁅W.L m, W.L n⁆ = ((m : ℂ) - n) • W.L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * W.centralCharge) • (1 : End ℂ 𝒱) else 0) :=
  W.virasoro m n

/-! ### The weight spaces are exactly the `L₀`-eigenspaces -/

/-- `π_k ∘ L₀ = k · π_k`: the weight projection turns `L₀` into a scalar. -/
theorem wtProj_L0 (W : SuperNearVOA 𝒱) (k : ℂ) (v : 𝒱) :
    W.wtProj k (W.L 0 v) = k • W.wtProj k v := by
  obtain ⟨s, hs, -⟩ := W.exists_sum_wtProj v
  conv_lhs => rw [← hs]
  rw [map_sum, map_sum]
  conv_rhs => rw [← hs, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj := W.wtProj_mem j v
  rw [W.L0_eigenvalue hj, LinearMap.map_smul]
  by_cases hjk : j = k
  · subst hjk; rfl
  · rw [W.wtProj_of_mem_ne hjk hj, smul_zero, smul_zero]

/-- **The weight spaces are exactly the `L₀`-eigenspaces.**  One inclusion is VOA2; this is
the converse, and it holds because the weight grading is an *internal direct sum*, so
eigenvectors cannot spread across several weights. -/
theorem mem_grading_of_L0_eq (W : SuperNearVOA 𝒱) {h : ℂ} {v : 𝒱} (hv : W.L 0 v = h • v) :
    v ∈ W.grading h := by
  have hzero : ∀ k : ℂ, k ≠ h → W.wtProj k v = 0 := by
    intro k hk
    have h1 := W.wtProj_L0 k v
    rw [hv, LinearMap.map_smul] at h1
    have h2 : (k - h) • W.wtProj k v = 0 := by rw [sub_smul, ← h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hk)
  obtain ⟨s, hs, -⟩ := W.exists_sum_wtProj v
  rw [← hs]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hjh : j = h
  · subst hjh; exact W.wtProj_mem j v
  · rw [hzero j hjh]
    exact Submodule.zero_mem _

/-! ### Compatibility of the weight and parity gradings

Not spin–statistics: this says the two gradings are simultaneously diagonalizable (each
weight space is parity-graded and vice versa), which follows from `ω` being even.  It says
nothing about which parity goes with which weight — and indeed for symplectic fermions the
odd fields carry integer weights. -/

/-- `L₀` preserves the parity spaces, because `ω` is even and modes add parities. -/
theorem parity_L0_stable (W : SuperNearVOA 𝒱) (p : ZMod 2) {v : 𝒱} (hv : v ∈ W.parity p) :
    W.L 0 v ∈ W.parity p := by
  have h := W.parity_mode W.conformalVector W.conformal_parity v hv 1
  rw [zero_add] at h
  change mode (W.Y W.conformalVector) (0 + 1) v ∈ W.parity p
  rwa [zero_add]

/-- Hence `L₀` commutes with the parity projections. -/
theorem parProj_comm_L0 (W : SuperNearVOA 𝒱) (p : ZMod 2) (v : 𝒱) :
    W.parProj p (W.L 0 v) = W.L 0 (W.parProj p v) :=
  homogProj_comm W.parity (W.L 0) (fun q _ hx => W.parity_L0_stable q hx) p v

/-- **The parity projections preserve the weight spaces.**  A weight-`h` vector is an
`L₀`-eigenvector; its parity components are again `L₀`-eigenvectors of the same
eigenvalue, hence again of weight `h` by `mem_grading_of_L0_eq`. -/
theorem parProj_mem_grading (W : SuperNearVOA 𝒱) (p : ZMod 2) {h : ℂ} {x : 𝒱}
    (hx : x ∈ W.grading h) : W.parProj p x ∈ W.grading h := by
  refine W.mem_grading_of_L0_eq ?_
  rw [← W.parProj_comm_L0, W.L0_eigenvalue hx, LinearMap.map_smul]

/-- **The two projections commute.** -/
theorem wtProj_parProj_comm (W : SuperNearVOA 𝒱) (h : ℂ) (p : ZMod 2) (x : 𝒱) :
    W.wtProj h (W.parProj p x) = W.parProj p (W.wtProj h x) :=
  homogProj_comm W.grading (W.parProj p) (fun _ _ hy => W.parProj_mem_grading p hy) h x

/-- **The weight projections preserve the parity spaces.**  This is the fact that makes
the even part of a super near-VOA a *weight-graded* subalgebra. -/
theorem wtProj_mem_parity (W : SuperNearVOA 𝒱) (h : ℂ) {p : ZMod 2} {v : 𝒱}
    (hv : v ∈ W.parity p) : W.wtProj h v ∈ W.parity p := by
  have hpv : W.parProj p v = v := W.parProj_of_mem hv
  rw [← hpv, W.wtProj_parProj_comm]
  exact W.parProj_mem p _

/-! ## Bounded below — the weak substitute for `positivity` -/

/-- **Bounded below**: the conformal weights that occur have real parts bounded below by
*some* real number `B`, not necessarily `0`.

This is deliberately *not* a structure field.  The doublet's ambient lattice-type algebra
has states of negative weight, so `positivity` (`B = 0`) is false there and can only be
established for the subalgebra one finally extracts.  `BoundedBelow` is what the module
machinery (characters, `q`-expansions, `L₀`-filtrations) actually needs, and it survives
the passage through the ambient object. -/
def BoundedBelow (W : SuperNearVOA 𝒱) : Prop :=
  ∃ B : ℝ, ∀ h : ℂ, h.re < B → W.grading h = ⊥

/-- A super near-VOA with `positivity` is bounded below, with bound `B = 0`.  (Sanity
check that `BoundedBelow` really is weaker than VOA4's second half.) -/
theorem boundedBelow_of_positivity (W : SuperNearVOA 𝒱)
    (hpos : ∀ h : ℂ, h.re < 0 → W.grading h = ⊥) : W.BoundedBelow :=
  ⟨0, hpos⟩

/-! ## Passing to and from `SuperVertexOperatorAlgebra` -/

/-- **Upgrade a super near-VOA to a super VOA** by supplying the two CFT-type conditions:
`𝒱₀ = ℂ𝟙` and the absence of weights of negative real part.  Both are proved *per
example*; neither is available in the ambient structures we pass through. -/
def toSVOA (W : SuperNearVOA 𝒱) (hvac : W.grading 0 = ℂ ∙ W.vacuum)
    (hpos : ∀ h : ℂ, h.re < 0 → W.grading h = ⊥) : SuperVertexOperatorAlgebra 𝒱 where
  __ := W.toSuperVertexAlgebra
  conformalVector := W.conformalVector
  conformal_mem := W.conformal_mem
  conformal_parity := W.conformal_parity
  centralCharge := W.centralCharge
  virasoro := W.virasoro
  L0_grading := W.L0_grading
  translation := W.translation
  vacuum_grade := hvac
  positivity := hpos

@[simp] theorem toSVOA_centralCharge (W : SuperNearVOA 𝒱) (hvac : W.grading 0 = ℂ ∙ W.vacuum)
    (hpos : ∀ h : ℂ, h.re < 0 → W.grading h = ⊥) :
    (W.toSVOA hvac hpos).centralCharge = W.centralCharge := rfl

end SuperNearVOA

namespace SuperVertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Every super VOA is a super near-VOA**: forget the two CFT-type conditions. -/
def toSuperNearVOA (W : SuperVertexOperatorAlgebra 𝒱) : SuperNearVOA 𝒱 where
  __ := W.toSuperVertexAlgebra
  conformalVector := W.conformalVector
  conformal_mem := W.conformal_mem
  conformal_parity := W.conformal_parity
  centralCharge := W.centralCharge
  virasoro := W.virasoro
  L0_grading := W.L0_grading
  translation := W.translation

@[simp] theorem toSuperNearVOA_centralCharge (W : SuperVertexOperatorAlgebra 𝒱) :
    W.toSuperNearVOA.centralCharge = W.centralCharge := rfl

/-- The near-VOA underlying a super VOA is bounded below. -/
theorem toSuperNearVOA_boundedBelow (W : SuperVertexOperatorAlgebra 𝒱) :
    W.toSuperNearVOA.BoundedBelow :=
  ⟨0, W.positivity⟩

end SuperVertexOperatorAlgebra

end VOA
