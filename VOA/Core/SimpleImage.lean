/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.QuotientVOA
import VOA.Core.ScreeningKernel

/-!
# Simple images: the kernel of a VOA map onto a simple VOA is the maximal ideal

This file supplies the **transfer lemma** that lets one identify a simple quotient
`V ⧸ maxGradedIdeal V` with a concretely realised vertex operator algebra **without ever
exhibiting, or computing with, a singular vector**.

The situation it is built for is *inverse quantum Hamiltonian reduction*: one writes down a
map `φ` from a universal VOA (say `V^k(𝔰𝔩₂)`) into a free-field/minimal-model target `T`, and
wants to conclude that the image is the *simple* quotient `L_k(𝔰𝔩₂)`.  The naive route is to
check that the maximal singular vector (at general admissible level, the Malikov–Feigin–Fuchs
vector, with complex powers) is annihilated by `φ`.  That does not scale.  The route taken
here instead is:

1. `ker φ` is an ideal of `V` (`IsVOAHom.isIdeal_ker`) — free;
2. `ker φ` is **proper**, because `φ 𝟙_V = 𝟙_T ≠ 0` (`IsVOAHom.vacuum_not_mem_ker`), hence
   `ker φ ≤ maxGradedIdeal V` (`IsVOAHom.ker_le_maxGradedIdeal`);
3. if `φ` is **onto a simple** `T`, then `φ (maxGradedIdeal V)` is a proper ideal of `T`,
   hence `⊥`, i.e. `maxGradedIdeal V ≤ ker φ` (`IsVOAHom.maxGradedIdeal_le_ker`).

Together: `ker φ = maxGradedIdeal V`, and `V ⧸ maxGradedIdeal V ≅ T`.  Vanishing of every
null vector is then a **corollary**, not an input: any element of any proper ideal whatsoever
is killed by `φ` (`IsVOAHom.apply_eq_zero_of_mem_properIdeal`).

## What a homomorphism means here

The repository had **no notion of vertex algebra homomorphism** before this file (see the
Status section).  `IsVOAHom V T φ` is defined here as a `ℂ`-linear map `φ` with

* `map_vacuum : φ 𝟙_V = 𝟙_T`, and
* `map_smul : φ (u₍ₙ₎ v) = (φ u)₍ₙ₎ (φ v)` for **all** `u, v` and **all** `n : ℤ`.

That is, the vacuum and *all* modes of `Y` are preserved.  Preservation of the **conformal
vector** is deliberately *not* required: for the intended applications (Sugawara vector of an
affine VOA landing inside a Virasoro⊗boson target) the two conformal vectors need not agree,
and no theorem below uses `ω`.  A hypothesis `φ ω_V = ω_T` is available as an *optional*
extra to `IsVOAHom.map_L`, which is the only statement that mentions `ω` at all.
Preservation of the **grading** is likewise neither required nor proved.

## The graded hypothesis: not needed

`maxGradedIdeal` is the supremum of the *graded* proper ideals, so one might fear a
`IsGradedIdeal W (ker φ)` side condition.  There is none: `QuotVOA.isGradedIdeal_of_isIdeal`
already proves in this repository that **every** ideal of a VOA is graded (it is stable under
`L₀`, whose eigenvalues separate the homogeneous pieces).  The packaged consequence
`QuotVOA.le_maxGradedIdeal'` therefore takes only `IsIdeal` and `𝟙 ∉ J`, and that is exactly
what step 2 above feeds it.  **No gradedness hypothesis appears anywhere in this file.**

## Properness: also not needed as a hypothesis

`QuotVOA.vacuum_not_mem_maxGradedIdeal` proves `𝟙 ∉ maxGradedIdeal W` for *every* VOA `W`
with `𝟙 ≠ 0`; it is a general theorem, not a per-example one.  And `𝟙_V ≠ 0` is itself free
here: a VOA whose vacuum vanishes is the zero VOA (see
`VertexOperatorAlgebra.eq_zero_of_vacuum_eq_zero`, from the creation axiom `u = u₍₋₁₎𝟙`), so
simplicity of `T` already gives `𝟙_T ≠ 0`
(`VertexOperatorAlgebra.IsSimple.vacuum_ne_zero`), and `φ 𝟙_V = 𝟙_T` gives `𝟙_V ≠ 0`.
Consequently the main theorem carries **no properness hypothesis** either — and no
"`φ ≠ 0`" hypothesis, which is subsumed.

## Main results

* `IsVOAHom` — the notion of a homomorphism of vertex operator
  algebras: linear, vacuum-preserving, and intertwining every mode.
* `IsVOAHom.isIdeal_ker` — the kernel of a VOA homomorphism is an ideal.
* `IsVOAHom.ker_le_maxGradedIdeal` — the "below" half.
* `IsVOAHom.maxGradedIdeal_le_ker` — the "above" half, from simplicity of the target.
* `IsVOAHom.ker_eq_maxGradedIdeal` — **the transfer lemma**: for a surjective
  homomorphism onto a simple VOA, `ker φ = maxGradedIdeal V`.
* `IsVOAHom.apply_eq_zero_of_mem_maxGradedIdeal`,
  `IsVOAHom.apply_eq_zero_of_mem_properIdeal` — **the nulls corollary**: every vector of
  the maximal ideal — indeed of any proper ideal, so in particular every singular vector that
  generates a proper ideal — dies under `φ`, with no computation.
* `IsVOAHom.maxQuotientEquiv`, `IsVOAHom.isVOAHom_maxQuotientHom` — the induced linear
  isomorphism `V ⧸ maxGradedIdeal V ≃ₗ T`, and the fact that it is a VOA homomorphism; so
  the target *is* the simple quotient.
* `isVOAHom_mkQ` — the quotient projection is a homomorphism (the source of examples).
* `isVOAHom_codRestrict` — corestriction of a homomorphism to a `VOASubalgebra` containing
  its image, so that "the image is a screening kernel" can be fed to the transfer lemma
  (the kernel is unchanged, by Mathlib's `LinearMap.ker_codRestrict`).
* `Screening.ker_eq_maxGradedIdeal_of_screeningKernel` — the specialisation to a map whose
  image is exactly the kernel of a screening operator `Q_a = a₍₀₎`.
* `maxGradedIdeal_eq_bot_of_isSimple`, `ker_mkQ_max_eq_maxGradedIdeal` — the transfer lemma
  evaluated at its two canonical instances (`φ = id` on a simple VOA, `φ = mkQ` onto the
  maximal quotient).  They are kept in the file as **non-vacuity witnesses**: each derives an
  independently-known fact through the new machinery, so a degenerate or misdirected
  statement of the transfer lemma would fail to typecheck here.

## Status

Complete, `sorry`-free, `admit`-free, `native_decide`-free, and it introduces **no new
axioms** (the theorem `VOA.pbw` is *not* used, directly or
transitively, by anything in this file).

Step-0 reconnaissance, recorded for the record:
* the repository contained **no** vertex algebra homomorphism before this file (the only
  `Hom`s were `WeakModule.Hom` for modules and `AmModHom` for Zhu-algebra modules), so
  `IsVOAHom` is defined here;
* `VertexOperatorAlgebra.IsIdeal W I : ∀ u v n, v ∈ I → W.smul u n v ∈ I` and
  `VertexOperatorAlgebra.IsSimple W : (⊤ : Submodule ℂ 𝒱) ≠ ⊥ ∧ ∀ I, W.IsIdeal I → I = ⊥ ∨ I = ⊤`
  live in `Core.BilinearForm`;
* properness of `maxGradedIdeal` is **general**, not per-example:
  `QuotVOA.vacuum_not_mem_maxGradedIdeal` needs only `W.vacuum ≠ 0`.

## Dependencies
* `VOA.Core.QuotientVOA` (ideals, `maxGradedIdeal`, `maxQuotientVOA`),
* `VOA.Core.ScreeningKernel` (only for the final screening specialisation).

## References
* Adamović, *Realizations of simple affine vertex algebras and their modules*;
  Adamović–Milas on inverse quantum Hamiltonian reduction.  The "kernel of a screening
  operator is simple" input is the uniform-in-`(p,q)` replacement for singular-vector
  computations; it enters here only as the hypothesis `IsSimple` on the target.
-/

namespace VOA

open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {𝒲 : Type v} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-! ## §0.  A VOA with vanishing vacuum is the zero VOA -/

namespace VertexOperatorAlgebra

/-- **A vertex operator algebra whose vacuum vanishes is the zero algebra.**  Immediate from
the creation axiom `u = u₍₋₁₎𝟙`: if `𝟙 = 0` then every `u` is the value of a linear map at
`0`. -/
theorem eq_zero_of_vacuum_eq_zero (T : VertexOperatorAlgebra 𝒲) (h : T.vacuum = 0) (u : 𝒲) :
    u = 0 := by
  have hc := (T.creation u).1
  rw [h, map_zero] at hc
  exact hc.symm

/-- A nonzero vertex operator algebra has a nonzero vacuum. -/
theorem vacuum_ne_zero_of_top_ne_bot (T : VertexOperatorAlgebra 𝒲)
    (h : (⊤ : Submodule ℂ 𝒲) ≠ ⊥) : T.vacuum ≠ 0 := by
  intro hv
  refine h (eq_bot_iff.mpr fun x _ => ?_)
  rw [Submodule.mem_bot]
  exact T.eq_zero_of_vacuum_eq_zero hv x

/-- **A simple vertex operator algebra has a nonzero vacuum.**  The first clause of
`IsSimple` is `⊤ ≠ ⊥`, and a VOA with `𝟙 = 0` is zero. -/
theorem IsSimple.vacuum_ne_zero {T : VertexOperatorAlgebra 𝒲} (hT : T.IsSimple) :
    T.vacuum ≠ 0 :=
  T.vacuum_ne_zero_of_top_ne_bot hT.1

end VertexOperatorAlgebra

/-! ## §1.  Homomorphisms of vertex operator algebras -/

/-- **A homomorphism of vertex operator algebras.**  A `ℂ`-linear map `φ : 𝒱 → 𝒲` is a
homomorphism from `V` to `T` when it takes the vacuum to the vacuum and intertwines **every**
mode of the state–field correspondence, `φ (u₍ₙ₎v) = (φ u)₍ₙ₎(φ v)` for all `n : ℤ`.

Preservation of the conformal vector is **not** part of the definition (see the module
docstring); no result in this file needs it. -/
structure IsVOAHom (V : VertexOperatorAlgebra 𝒱) (T : VertexOperatorAlgebra 𝒲)
    (φ : 𝒱 →ₗ[ℂ] 𝒲) : Prop where
  /-- The vacuum goes to the vacuum: `φ 𝟙_V = 𝟙_T`. -/
  map_vacuum : φ V.vacuum = T.vacuum
  /-- Every product is intertwined: `φ (u₍ₙ₎v) = (φ u)₍ₙ₎(φ v)`. -/
  map_smul : ∀ (u : 𝒱) (n : ℤ) (v : 𝒱), φ (V.smul u n v) = T.smul (φ u) n (φ v)

namespace IsVOAHom

variable {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲} {φ : 𝒱 →ₗ[ℂ] 𝒲}

/-- The identity is a homomorphism from a VOA to itself. -/
theorem id (V : VertexOperatorAlgebra 𝒱) : IsVOAHom V V (LinearMap.id) where
  map_vacuum := rfl
  map_smul _ _ _ := rfl

/-- Homomorphisms compose. -/
theorem comp {𝒰 : Type*} [AddCommGroup 𝒰] [Module ℂ 𝒰] {U : VertexOperatorAlgebra 𝒰}
    {ψ : 𝒲 →ₗ[ℂ] 𝒰} (hψ : IsVOAHom T U ψ) (hφ : IsVOAHom V T φ) :
    IsVOAHom V U (ψ.comp φ) where
  map_vacuum := by
    simp only [LinearMap.comp_apply]
    rw [hφ.map_vacuum, hψ.map_vacuum]
  map_smul u n v := by
    simp only [LinearMap.comp_apply]
    rw [hφ.map_smul, hψ.map_smul]

/-- **If the conformal vector is preserved, so are the Virasoro modes**:
`φ (Lₙ v) = Lₙ (φ v)`.  This is the *only* statement in the file that mentions `ω`, and the
hypothesis `hω` is an optional extra, not part of `IsVOAHom`. -/
theorem map_L (hφ : IsVOAHom V T φ) (hω : φ V.conformalVector = T.conformalVector)
    (n : ℤ) (v : 𝒱) : φ (V.L n v) = T.L n (φ v) := by
  have hV : V.L n v = V.smul V.conformalVector (n + 1) v := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  have hT : T.L n (φ v) = T.smul T.conformalVector (n + 1) (φ v) := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  rw [hV, hT, hφ.map_smul, hω]

/-! ### The kernel -/

/-- **The kernel of a VOA homomorphism is an ideal.**  If `φ v = 0` then
`φ (u₍ₙ₎v) = (φ u)₍ₙ₎0 = 0`. -/
theorem isIdeal_ker (hφ : IsVOAHom V T φ) : V.IsIdeal (LinearMap.ker φ) := by
  intro u v n hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [hφ.map_smul u n v, hv, PreVertexAlgebra.smul_zero_right]

/-- **The kernel is proper** as soon as the target has a nonzero vacuum: `φ 𝟙_V = 𝟙_T ≠ 0`. -/
theorem vacuum_not_mem_ker (hφ : IsVOAHom V T φ) (hT : T.vacuum ≠ 0) :
    V.vacuum ∉ LinearMap.ker φ := by
  intro h
  rw [LinearMap.mem_ker, hφ.map_vacuum] at h
  exact hT h

/-- **The source has a nonzero vacuum** whenever the target does. -/
theorem vacuum_ne_zero (hφ : IsVOAHom V T φ) (hT : T.vacuum ≠ 0) : V.vacuum ≠ 0 := by
  intro h
  exact hT (by rw [← hφ.map_vacuum, h, map_zero])

/-- **The "below" half of the transfer lemma**: `ker φ ≤ maxGradedIdeal V`.

It is a proper ideal, and every proper ideal lies below the maximal one — gradedness is
automatic by `QuotVOA.isGradedIdeal_of_isIdeal`, so no graded hypothesis is needed. -/
theorem ker_le_maxGradedIdeal (hφ : IsVOAHom V T φ) (hT : T.vacuum ≠ 0) :
    LinearMap.ker φ ≤ QuotVOA.maxGradedIdeal V :=
  QuotVOA.le_maxGradedIdeal' hφ.isIdeal_ker (hφ.vacuum_not_mem_ker hT)

/-- **The image of the maximal ideal is an ideal of the target**, for a surjective
homomorphism. -/
theorem isIdeal_map_maxGradedIdeal (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ) :
    T.IsIdeal ((QuotVOA.maxGradedIdeal V).map φ) := by
  rintro u' v' n ⟨v, hvM, rfl⟩
  obtain ⟨u, rfl⟩ := hsurj u'
  exact ⟨V.smul u n v, QuotVOA.maxGradedIdeal_isIdeal V u v n hvM, hφ.map_smul u n v⟩

/-- **The image of the maximal ideal is a proper ideal of the target.**  If `𝟙_T = φ m` with
`m ∈ maxGradedIdeal V`, then `𝟙_V - m ∈ ker φ ≤ maxGradedIdeal V`, so `𝟙_V` would lie in the
maximal ideal — which it does not. -/
theorem vacuum_not_mem_map_maxGradedIdeal (hφ : IsVOAHom V T φ) (hT : T.vacuum ≠ 0) :
    T.vacuum ∉ (QuotVOA.maxGradedIdeal V).map φ := by
  rintro ⟨m, hmM, hm⟩
  have hker : V.vacuum - m ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, hφ.map_vacuum, hm, sub_self]
  have hsub : V.vacuum - m ∈ QuotVOA.maxGradedIdeal V := hφ.ker_le_maxGradedIdeal hT hker
  have hvac : V.vacuum ∈ QuotVOA.maxGradedIdeal V := by
    have := (QuotVOA.maxGradedIdeal V).add_mem hsub hmM
    rwa [sub_add_cancel] at this
  exact QuotVOA.vacuum_not_mem_maxGradedIdeal V (hφ.vacuum_ne_zero hT) hvac

/-- **The "above" half of the transfer lemma**: if `φ` is onto a *simple* `T`, then
`maxGradedIdeal V ≤ ker φ`.

The image of the maximal ideal is a proper ideal of `T`, hence `⊥` by simplicity. -/
theorem maxGradedIdeal_le_ker (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) : QuotVOA.maxGradedIdeal V ≤ LinearMap.ker φ := by
  have hT : T.vacuum ≠ 0 := hsimple.vacuum_ne_zero
  rcases hsimple.2 _ (hφ.isIdeal_map_maxGradedIdeal hsurj) with h | h
  · rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot] at h
    exact h
  · exact absurd (by rw [h]; exact Submodule.mem_top)
      (hφ.vacuum_not_mem_map_maxGradedIdeal hT)

/-! ### The transfer lemma -/

/-- **THE TRANSFER LEMMA.**  If `φ : V → T` is a homomorphism of vertex operator algebras
which is **surjective** onto a **simple** `T`, then

  `ker φ = maxGradedIdeal V`,

so `T` is (isomorphic to) the simple quotient `V ⧸ maxGradedIdeal V`.

No singular vector is mentioned, no gradedness hypothesis is needed (every ideal of a VOA is
graded), and no properness hypothesis is needed (simplicity of `T` forces `𝟙_T ≠ 0`, hence
`𝟙_V ≠ 0` and `𝟙_V ∉ ker φ`).  The "`φ ≠ 0`" condition of the informal argument is subsumed:
`φ 𝟙_V = 𝟙_T ≠ 0`. -/
theorem ker_eq_maxGradedIdeal (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) : LinearMap.ker φ = QuotVOA.maxGradedIdeal V :=
  le_antisymm (hφ.ker_le_maxGradedIdeal hsimple.vacuum_ne_zero)
    (hφ.maxGradedIdeal_le_ker hsurj hsimple)

/-! ### The corollary for null vectors -/

/-- **THE NULLS COROLLARY.**  Under the transfer hypotheses, **every** vector of the
maximal graded ideal is annihilated by `φ`.

This is the point of the whole construction: for a concrete realisation `φ` one never has to
substitute into a singular vector.  Whatever the maximal ideal contains — the
Malikov–Feigin–Fuchs vector at a general admissible level included — is killed automatically.

Only the "above" half is used, so simplicity of the image is the sole real input. -/
theorem apply_eq_zero_of_mem_maxGradedIdeal (hφ : IsVOAHom V T φ)
    (hsurj : Function.Surjective φ) (hsimple : T.IsSimple)
    {x : 𝒱} (hx : x ∈ QuotVOA.maxGradedIdeal V) : φ x = 0 :=
  LinearMap.mem_ker.mp (hφ.maxGradedIdeal_le_ker hsurj hsimple hx)

/-- **The nulls corollary, in its most usable form.**  Under the transfer hypotheses, every
vector of **every proper ideal** of `V` is annihilated by `φ`.

In particular, if `s` is a singular vector whose generated ideal `J` is proper (`𝟙 ∉ J`), then
`φ s = 0`, *without computing anything*: feed `J := SingularVector.idealGen V s`,
`hJ := idealGen_isIdeal`, `hx := mem_idealGen_self`. -/
theorem apply_eq_zero_of_mem_properIdeal (hφ : IsVOAHom V T φ)
    (hsurj : Function.Surjective φ) (hsimple : T.IsSimple)
    {J : Submodule ℂ 𝒱} (hJ : V.IsIdeal J) (hJv : V.vacuum ∉ J)
    {x : 𝒱} (hx : x ∈ J) : φ x = 0 :=
  hφ.apply_eq_zero_of_mem_maxGradedIdeal hsurj hsimple (QuotVOA.le_maxGradedIdeal' hJ hJv hx)

/-! ### The induced isomorphism with the maximal quotient -/

/-- The map `V ⧸ maxGradedIdeal V → T` induced by `φ`.  Only the "above" half
(`maxGradedIdeal V ≤ ker φ`) is needed for it to exist. -/
noncomputable def maxQuotientHom (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) : (𝒱 ⧸ QuotVOA.maxGradedIdeal V) →ₗ[ℂ] 𝒲 :=
  (QuotVOA.maxGradedIdeal V).liftQ φ (hφ.maxGradedIdeal_le_ker hsurj hsimple)

@[simp] theorem maxQuotientHom_mkQ (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) (x : 𝒱) :
    hφ.maxQuotientHom hsurj hsimple ((QuotVOA.maxGradedIdeal V).mkQ x) = φ x := rfl

/-- **The induced map is a homomorphism of vertex operator algebras** from the maximal
quotient `maxQuotientVOA V` to `T`. -/
theorem isVOAHom_maxQuotientHom (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) :
    IsVOAHom (QuotVOA.maxQuotientVOA V) T (hφ.maxQuotientHom hsurj hsimple) where
  map_vacuum := hφ.map_vacuum
  map_smul := by
    intro u n v
    obtain ⟨u, rfl⟩ := (QuotVOA.maxGradedIdeal V).mkQ_surjective u
    obtain ⟨v, rfl⟩ := (QuotVOA.maxGradedIdeal V).mkQ_surjective v
    rw [QuotVOA.maxQuotientVOA, QuotVOA.quotientVOA_mkQ_smul, maxQuotientHom_mkQ,
      maxQuotientHom_mkQ, maxQuotientHom_mkQ, hφ.map_smul]

/-- **The simple quotient is the target.**  Under the transfer hypotheses the induced map is
a linear isomorphism `V ⧸ maxGradedIdeal V ≃ₗ[ℂ] 𝒲`; combined with
`isVOAHom_maxQuotientHom` it is an isomorphism of vertex operator algebras. -/
noncomputable def maxQuotientEquiv (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) : (𝒱 ⧸ QuotVOA.maxGradedIdeal V) ≃ₗ[ℂ] 𝒲 :=
  LinearEquiv.ofBijective (hφ.maxQuotientHom hsurj hsimple)
    ⟨by
      rw [← LinearMap.ker_eq_bot, maxQuotientHom]
      exact Submodule.ker_liftQ_eq_bot _ _ _
        (le_of_eq (hφ.ker_eq_maxGradedIdeal hsurj hsimple)),
     by
      intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨(QuotVOA.maxGradedIdeal V).mkQ x, rfl⟩⟩

@[simp] theorem maxQuotientEquiv_mkQ (hφ : IsVOAHom V T φ) (hsurj : Function.Surjective φ)
    (hsimple : T.IsSimple) (x : 𝒱) :
    hφ.maxQuotientEquiv hsurj hsimple ((QuotVOA.maxGradedIdeal V).mkQ x) = φ x := rfl

end IsVOAHom

/-! ## §2.  Two sources of homomorphisms -/

/-- **The quotient projection is a homomorphism** `V → V ⧸ I` for any ideal `I`. -/
theorem isVOAHom_mkQ (V : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) (hI : V.IsIdeal I) :
    IsVOAHom V (QuotVOA.quotientVOA' V I hI) I.mkQ where
  map_vacuum := rfl
  map_smul u n v :=
    (QuotVOA.quotientVOA_mkQ_smul hI (QuotVOA.isGradedIdeal_of_isIdeal hI) u n v).symm

/-- **The projection onto the maximal quotient is a homomorphism.** -/
theorem isVOAHom_mkQ_max (V : VertexOperatorAlgebra 𝒱) :
    IsVOAHom V (QuotVOA.maxQuotientVOA V) (QuotVOA.maxGradedIdeal V).mkQ where
  map_vacuum := rfl
  map_smul u n v :=
    (QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal V)
      (QuotVOA.maxGradedIdeal_isGradedIdeal V) u n v).symm

/-- **Corestriction to a vertex operator subalgebra.**  If every value of `φ` lies in a
`VOASubalgebra S` of the target, then `φ` corestricts to a homomorphism into the VOA `S.toVOA`
carried by `S`.

This is what turns "the image of `φ` is the kernel of a screening operator" into a hypothesis
the transfer lemma can consume. -/
theorem isVOAHom_codRestrict {V : VertexOperatorAlgebra 𝒱} {W : VertexOperatorAlgebra 𝒲}
    (S : VOASubalgebra W) {φ : 𝒱 →ₗ[ℂ] 𝒲} (hmem : ∀ x, φ x ∈ S.carrier)
    (hφ : IsVOAHom V W φ) :
    IsVOAHom V S.toVOA (LinearMap.codRestrict S.carrier φ hmem) where
  map_vacuum := Subtype.ext hφ.map_vacuum
  map_smul u n v := Subtype.ext (hφ.map_smul u n v)

/-! ## §3.  Specialisation: the image is a screening kernel -/

namespace Screening

/-- **The transfer lemma for a screening-kernel image.**  Let `φ : V → W` be a homomorphism
of vertex operator algebras whose image is *exactly* the kernel of the screening operator
`Q_a = a₍₀₎` for a weight-one `a ∈ 𝒲₁`:

* `hin`  — every value of `φ` is killed by `Q_a`;
* `honto` — every vector killed by `Q_a` is a value of `φ`.

If that kernel VOA is **simple**, then `ker φ = maxGradedIdeal V`, so the image is the simple
quotient of `V`.

This is the shape the Adamović-style free-field realisations take: the image of `V^k(𝔰𝔩₂)` is
the joint kernel of screening charges, and simplicity of such kernels is an argument uniform
in the level, replacing per-level singular-vector computations. -/
theorem ker_eq_maxGradedIdeal_of_screeningKernel {V : VertexOperatorAlgebra 𝒱}
    {W : VertexOperatorAlgebra 𝒲} {a : 𝒲} (ha : a ∈ W.grading 1) {φ : 𝒱 →ₗ[ℂ] 𝒲}
    (hφ : IsVOAHom V W φ) (hin : ∀ x, screening W a (φ x) = 0)
    (honto : ∀ y, screening W a y = 0 → ∃ x, φ x = y)
    (hsimple : (screeningKernelVOA W a ha).IsSimple) :
    LinearMap.ker φ = QuotVOA.maxGradedIdeal V := by
  have hmem : ∀ x, φ x ∈ (screeningKernel W a ha).carrier := fun x =>
    mem_screeningKernel.mpr (hin x)
  have hcor : IsVOAHom V (screeningKernelVOA W a ha)
      (LinearMap.codRestrict (screeningKernel W a ha).carrier φ hmem) :=
    isVOAHom_codRestrict _ hmem hφ
  have hsurj : Function.Surjective
      (LinearMap.codRestrict (screeningKernel W a ha).carrier φ hmem) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := honto y (mem_screeningKernel.mp hy)
    exact ⟨x, rfl⟩
  have h := hcor.ker_eq_maxGradedIdeal hsurj hsimple
  rwa [LinearMap.ker_codRestrict] at h

/-- **The nulls corollary for a screening-kernel image.**  Under the hypotheses of
`ker_eq_maxGradedIdeal_of_screeningKernel`, every vector of every proper ideal of `V` — in
particular every singular vector generating a proper ideal — is annihilated by `φ`. -/
theorem apply_eq_zero_of_screeningKernel {V : VertexOperatorAlgebra 𝒱}
    {W : VertexOperatorAlgebra 𝒲} {a : 𝒲} (ha : a ∈ W.grading 1) {φ : 𝒱 →ₗ[ℂ] 𝒲}
    (hφ : IsVOAHom V W φ) (hin : ∀ x, screening W a (φ x) = 0)
    (honto : ∀ y, screening W a y = 0 → ∃ x, φ x = y)
    (hsimple : (screeningKernelVOA W a ha).IsSimple)
    {J : Submodule ℂ 𝒱} (hJ : V.IsIdeal J) (hJv : V.vacuum ∉ J) {x : 𝒱} (hx : x ∈ J) :
    φ x = 0 := by
  have hker := ker_eq_maxGradedIdeal_of_screeningKernel ha hφ hin honto hsimple
  have : x ∈ LinearMap.ker φ := by
    rw [hker]; exact QuotVOA.le_maxGradedIdeal' hJ hJv hx
  exact LinearMap.mem_ker.mp this

end Screening

/-! ## §4.  Non-vacuity: the transfer lemma at its two canonical instances

Neither theorem below is needed downstream.  They exist because a transfer lemma of this
shape is easy to state vacuously or with an inverted inclusion, and these two instantiations
would both break if it were.  Each recovers, purely from `ker_eq_maxGradedIdeal`, a fact that
is known independently in the repository. -/

/-- **A simple VOA has trivial maximal ideal**, obtained by feeding the identity map to the
transfer lemma.  (Independently known as `VirSimple.isSimple_iff_maxGradedIdeal_eq_bot` in
`Examples.VirasoroSimple`; reproved here through the new machinery as a consistency check.) -/
theorem maxGradedIdeal_eq_bot_of_isSimple (W : VertexOperatorAlgebra 𝒱) (hW : W.IsSimple) :
    QuotVOA.maxGradedIdeal W = ⊥ := by
  have h := (IsVOAHom.id W).ker_eq_maxGradedIdeal (fun x => ⟨x, rfl⟩) hW
  rw [LinearMap.ker_id] at h
  exact h.symm

/-- **The transfer lemma applied to the canonical projection** `V ↠ V ⧸ maxGradedIdeal V`
returns `maxGradedIdeal V`, as it must: the projection is a surjective homomorphism onto the
simple quotient (`QuotVOA.isSimple_maxQuotientVOA'`), and its kernel is `maxGradedIdeal V` by
`Submodule.ker_mkQ`.  A direction error in `ker_eq_maxGradedIdeal` would be visible here. -/
theorem ker_mkQ_max_eq_maxGradedIdeal (V : VertexOperatorAlgebra 𝒱) (hvac : V.vacuum ≠ 0) :
    LinearMap.ker (QuotVOA.maxGradedIdeal V).mkQ = QuotVOA.maxGradedIdeal V :=
  (isVOAHom_mkQ_max V).ker_eq_maxGradedIdeal
    (QuotVOA.maxGradedIdeal V).mkQ_surjective (QuotVOA.isSimple_maxQuotientVOA' V hvac)

end VOA
