/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VOASubalgebraGenerated
import VOA.Core.LieAlgebraV1
import VOA.Core.SuperVOASubalgebra

/-!
# Screening operators and their kernels

A **screening operator** on a vertex operator algebra `W` is the zero mode
`Q_a := a₍₀₎ = mode (Y a) 0` of a state `a` of conformal weight one.  This file proves the
one structural fact that makes the whole *free-field* side of the subject work:

> **`Q_a` is a derivation of every product, and its kernel is a vertex operator
> subalgebra.**

Every free-field realisation — the Virasoro minimal models inside a Feigin–Fuchs boson, the
`(1,p)` triplet `W`-algebras inside a lattice VOA, the doublet algebras, and the
screening-side construction of `W^k(𝔤,f)` in Drinfeld–Sokolov reduction — is an instance of
this statement: one *defines* the algebra as `⋂ᵢ ker Q_{aᵢ}` and then needs to know that the
intersection is a VOA at all.  That is exactly `screeningKernelInter` below.

## The two ingredients, and where they come from

* **Derivation.** `Q_a(u₍ₙ₎v) = (Q_a u)₍ₙ₎v + u₍ₙ₎(Q_a v)`.  This is the `ℓ = 0` slice of the
  Borcherds/Jacobi commutator formula (Gannon 5.1.7c), where `C(0,j) = δ_{j0}` collapses the
  sum to a single term.  The repository *already* has it, in the sharpest available form:
  `Core.LieAlgebraV1.zeroMode_isDerivation`, proved from the field `n`-th-product theorem
  `nth_product` rather than from the existential-`N` commutator form.  We do **not** reprove
  it; `screening_leibniz` is a two-line consequence.  Note in particular that **no weight
  hypothesis is needed for the Leibniz rule itself** — `a₍₀₎` is a derivation for *every*
  state `a`.

* **Weight one.**  The hypothesis `a ∈ 𝒱₁` is what makes the *kernel* a subalgebra rather
  than just a subspace closed under products, and it enters in exactly two places:
  - `screening_mem_grading`: by VA1, `a₍₀₎ : 𝒱ₙ → 𝒱_{1+n-0-1} = 𝒱ₙ`, so `Q_a` has degree `0`
    and therefore commutes with the homogeneous projections `piHom W n`
    (`screening_piHom`).  Gradedness is an *axiom* of `VOASubalgebra`, so this clause is not
    optional.
  - `screening_conformalVector`: `Q_a ω = 0`.

## `Q_a ω = 0` needs no primarity hypothesis

One expects to have to assume that `a` is *primary* of weight one.  In a VOA of CFT type
(VOA4) one does not, and the file proves the unconditional statement.  Skew-symmetry
(Gannon 5.1.8, `Core.SkewSymmetry.skew_mode`) at `n = 0` gives

  `a₍₀₎ω = ∑_{j ≥ 0} (1/j!)·(-1)^{j+1}·Tʲ(L_{j-1}a)`,

and for `a ∈ 𝒱₁`:

| `j` | `L_{j-1}a` lives in | contribution |
|-----|---------------------|--------------|
| `0` | `L₋₁a = Ta`         | `−Ta`        |
| `1` | `L₀a = a`           | `+Ta`        |
| `2` | `L₁a ∈ 𝒱₀ = ℂ𝟙` (VOA4) | `T²(c𝟙) = 0` since `T𝟙 = 0` |
| `≥3`| `𝒱_{2-j} = 0` (VOA4, positivity) | `0` |

so the tower telescopes to `−Ta + Ta = 0`.  This is the same mechanism as
`Core.LieAlgebraV1.skew_v1_tower_vanish` (which handles `a, b ∈ 𝒱₁`), one weight higher;
`skew_omega_tower_vanish` below is its `b = ω ∈ 𝒱₂` analogue.

## Main definitions

* `Screening.IsVOADerivation W D` — the four clauses a linear operator must satisfy for its
  kernel to be a `VOASubalgebra`: Leibniz on all products, killing `𝟙` and `ω`, and
  commuting with the homogeneous projections.
* `Screening.kerSubalgebra` — **the kernel of such a derivation is a vertex operator
  subalgebra**, hence (via `VOASubalgebra.toVOA`) a VOA with the same central charge.
* `Screening.screening W a := mode (W.Y a) 0` — the screening operator `Q_a = a₍₀₎`.
* `Screening.screeningKernel W a ha` — `ker Q_a` as a `VOASubalgebra W`, for
  `ha : a ∈ W.grading 1`; `screeningKernelVOA` is the induced VOA.
* `Screening.screeningKernelInter` / `screeningKernelPair` — arbitrary (in particular
  finite) intersections of screening kernels, again subalgebras.
* `Screening.superScreening`, `Screening.IsSuperScreening`,
  `Screening.superScreeningKernel` — the super analogue (see the honest caveat below).

## Main results

* `screening_leibniz` — the derivation property, unconditional in `a`.
* `screening_vacuum` — `Q_a 𝟙 = 0`, unconditional (VA3, creation).
* `screening_mem_grading`, `screening_piHom` — `Q_a` has degree `0` and commutes with `π_n`,
  for `a ∈ 𝒱₁`.
* `screening_conformalVector` — `Q_a ω = 0` for `a ∈ 𝒱₁`, **no primarity assumed**.
* `screening_isDerivation` — the four clauses, assembled.
* `mem_screeningKernel`, `mem_screeningKernelInter`, `mem_screeningKernelPair` — membership.

## The super case: what is proved and what is assumed

For a `SuperNearVOA` the *grading* half goes through verbatim: `superScreening_mem_grading`
and `superScreening_mem_parity` (for `a` even) are proved from VA1/VA1′, and hence
`wtProj_comm_of_gradePreserving` / `parProj_comm_of_parityPreserving` give the two
projection clauses of `SuperVOASubalgebra`; `superScreening_vacuum` is VA3.  What is **not**
used *in this file* is the super Borcherds machinery.  The library has `superBorcherds`/`superJacobi` (`Core/SuperBorcherds.lean`), `mode_iterateε`
(`Core/SuperBorcherdsIdentity.lean`) and unconditional super skew-symmetry `superSmul_eq_skew_Lpow`
(`Modularity/SuperZhuCommutator.lean`), which make the conditional `Core.SuperSkew.skew_modeε`
unnecessary.  The two fields below have not been re-derived from them.  The two facts that need that
machinery — the Leibniz rule and `Q_a ω = 0` — are carried as *hypotheses*, packaged as
`IsSuperScreening`.  `superScreeningKernel` is then a genuine theorem: given them, the
kernel is a `SuperVOASubalgebra`.  Discharging the two fields is the precise remaining work.

## Relation to the concrete `Qscr` of `Examples.TripletScreening`

`Examples.TripletScreening` defines `Qscr L α := mode (Yeαvec L α) 0` on the lattice module
`LatModuleGen L`, and `Qscr_eq_mode_YfullGen` identifies it with `mode (YfullGen … eᵅ) 0`.
So `Qscr` is *literally* of the shape `mode (Y a) 0` with `a = e^α`, and
`screening_eq_mode_of_Y_eq` is the one-rewrite bridge.  The honest caveat is about the
weight hypothesis, and it is a real one:

* `TripletScreening`'s `wt(e^α) = 1` is `½⟨α,α⟩ − ⟨λ,α⟩ = 1`, the weight measured by the
  **background-charge** Virasoro `L^λ` (`LBG L lam`), and the statement proved there is
  `LBG_zero_comm_Qscr : [L^λ₀, Q] = 0`, i.e. preservation of the *deformed* weight grading.
* `screeningKernel` needs `a ∈ W.grading 1` for the grading `W.grading` of an actual
  `VertexOperatorAlgebra` structure `W` on the module.  The lattice VOA instance
  (`Examples.LatticeGenVOAInstance`) carries the **undeformed** conformal vector, for which
  `wt(e^α) = ½⟨α,α⟩ = p`.
* Hence the two coincide exactly when `λ = 0` and `⟨α,α⟩ = 2`, i.e. `p = 1`.  For `p ≥ 2`
  the general theorem does **not** literally apply to `Qscr`: what is missing is a
  `VertexOperatorAlgebra` (or `NearVOA`) structure whose conformal vector is the deformed
  `ω^λ` and whose grading is the `L^λ₀`-grading — the Feigin–Fuchs/background-charge VOA.
  That structure is not in the repository, and this file deliberately does not import
  `Examples.*` (a `Core` file must not depend on the lattice tower).  Once it exists, the
  instantiation is `screeningKernel W (e^α) hwt` with `hwt` supplied by `triplet_wt_one`.

## Dependencies
* `Core.VOASubalgebraGenerated` (hence `Modularity.Twisted`: `VOASubalgebra`, `toVOA`,
  `InfSet`; and `Modules.FiniteGenerationProof`: `piHom`), `Core.LieAlgebraV1`
  (`zeroMode_isDerivation`, `sgn_neg_one`, and transitively `Core.SkewSymmetry.skew_mode`),
  `Core.SuperVOASubalgebra`.

## Status
`sorry`-free, `admit`-free, `native_decide`-free, no new axioms.  The bosonic half is
unconditional; the super half is a conditional theorem with the two missing super-Borcherds
inputs exposed as the fields of `IsSuperScreening`.

## References
* Gannon §5.1.3 (Borcherds identity 5.1.7c), §5.2.1 (`𝒱₁` and zero modes), §5.1.8
  (skew-symmetry); Feigin–Fuchs; Adamović–Milas (triplet); Frenkel–Ben-Zvi Ch. 15
  (screening operators and `W`-algebras).
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace Screening

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  Derivations of a VOA and their kernels

The abstract engine.  Nothing here is about screening operators specifically: it is the
observation that a `VOASubalgebra` is cut out by exactly four closure conditions, all four
of which are *linear* in the defining operator, so the kernel of an operator satisfying the
matching four conditions is one. -/

/-- The four clauses that make the kernel of a linear operator `D` a vertex operator
subalgebra of `W`:

* `leibniz` — `D` is a derivation of **every** product `u₍ₙ₎v`, `n ∈ ℤ`;
* `vacuum` / `conformal` — `D` annihilates `𝟙` and `ω`;
* `piHom_comm` — `D` commutes with the homogeneous projections `π_n`, equivalently `D` has
  degree `0`.  This clause is forced by the definition of `VOASubalgebra`, in which
  gradedness is an axiom (see `Core.VOASubalgebraGenerated`'s module docstring). -/
structure IsVOADerivation (W : VertexOperatorAlgebra 𝒱) (D : End ℂ 𝒱) : Prop where
  /-- `D(u₍ₙ₎v) = (Du)₍ₙ₎v + u₍ₙ₎(Dv)` for all `u v` and all `n ∈ ℤ`. -/
  leibniz : ∀ (u : 𝒱) (n : ℤ) (v : 𝒱),
      D (W.smul u n v) = W.smul (D u) n v + W.smul u n (D v)
  /-- `D 𝟙 = 0`. -/
  vacuum : D W.vacuum = 0
  /-- `D ω = 0`. -/
  conformal : D W.conformalVector = 0
  /-- `D ∘ π_n = π_n ∘ D`: `D` preserves the conformal grading. -/
  piHom_comm : ∀ (n : ℤ) (v : 𝒱), D (piHom W n v) = piHom W n (D v)

/-- **The kernel of a derivation is a vertex operator subalgebra.**  Composing with
`VOASubalgebra.toVOA` (`Modularity.Twisted`) it is therefore a VOA in its own right, with
the same vacuum, the same conformal vector and the same central charge. -/
def kerSubalgebra (W : VertexOperatorAlgebra 𝒱) (D : End ℂ 𝒱)
    (hD : IsVOADerivation W D) : VOASubalgebra W where
  carrier := LinearMap.ker D
  vacuum_mem := LinearMap.mem_ker.mpr hD.vacuum
  conformal_mem := LinearMap.mem_ker.mpr hD.conformal
  smul_mem := by
    intro u hu n v hv
    rw [LinearMap.mem_ker] at hu hv ⊢
    rw [hD.leibniz u n v, hu, hv, PreVertexAlgebra.smul_zero_left,
      PreVertexAlgebra.smul_zero_right, add_zero]
  graded := by
    intro n v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hD.piHom_comm n v, hv, map_zero]

@[simp] theorem mem_kerSubalgebra {W : VertexOperatorAlgebra 𝒱} {D : End ℂ 𝒱}
    {hD : IsVOADerivation W D} {x : 𝒱} :
    x ∈ (kerSubalgebra W D hD).carrier ↔ D x = 0 := LinearMap.mem_ker

/-- The VOA structure carried by the kernel of a derivation. -/
noncomputable def kerSubalgebraVOA (W : VertexOperatorAlgebra 𝒱) (D : End ℂ 𝒱)
    (hD : IsVOADerivation W D) : VertexOperatorAlgebra (kerSubalgebra W D hD).carrier :=
  (kerSubalgebra W D hD).toVOA

@[simp] theorem kerSubalgebraVOA_centralCharge (W : VertexOperatorAlgebra 𝒱) (D : End ℂ 𝒱)
    (hD : IsVOADerivation W D) :
    (kerSubalgebraVOA W D hD).centralCharge = W.centralCharge := rfl

/-! ### The degree-`0` criterion for `piHom_comm`

The projection clause is never checked by hand: it follows from grade preservation, exactly
as `Aut.map_piHom` follows from `Aut.map_grading` in `Modularity.Twisted`. -/

/-- A linear operator that preserves every homogeneous grade commutes with every homogeneous
projection.  (Decompose `v`, apply `D` termwise, and note that only the degree-`n` term
survives `π_n`.) -/
theorem piHom_comm_of_gradePreserving (W : VertexOperatorAlgebra 𝒱) (D : End ℂ 𝒱)
    (hD : ∀ (k : ℤ) (v : 𝒱), v ∈ W.grading k → D v ∈ W.grading k) (n : ℤ) (v : 𝒱) :
    D (piHom W n v) = piHom W n (D v) := by
  classical
  have hsum : D v = ∑ j ∈ (DirectSum.decompose W.grading v).support, D (piHom W j v) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose W.grading v]
    exact map_sum D _ _
  rw [hsum, map_sum, Finset.sum_eq_single n]
  · rw [piHom_of_mem W (hD n _ (piHom_mem W n v))]
  · intro j _ hjn
    rw [piHom_of_mem_ne W hjn (hD j _ (piHom_mem W j v))]
  · intro hn
    rw [DFinsupp.notMem_support_iff] at hn
    rw [show piHom W n v = 0 from by rw [piHom_apply, hn]; rfl, map_zero, map_zero]

/-! ## §2  The screening operator `Q_a = a₍₀₎` -/

/-- The **screening operator** attached to a state `a`: the zero mode `Q_a := a₍₀₎`.  It is
called a screening operator when `a` has conformal weight one, which is exactly the
condition under which `Q_a` has degree `0` and `Q_a ω = 0`. -/
def screening (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) : End ℂ 𝒱 := mode (W.Y a) 0

theorem screening_apply (W : VertexOperatorAlgebra 𝒱) (a v : 𝒱) :
    screening W a v = W.smul a 0 v := rfl

/-- `Q_a` is Gannon's zero mode `o(a)` of a weight-one state (`Core.LieAlgebraV1`). -/
theorem screening_eq_zeroMode (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) :
    screening W a = W.zeroMode a 1 := by
  simp only [screening, VertexOperatorAlgebra.zeroMode]
  norm_num

/-- On `𝒱₁` the screening operator is the left action of the `𝒱₁` Lie bracket. -/
theorem screening_eq_bracketV1 (W : VertexOperatorAlgebra 𝒱) (a b : W.grading 1) :
    screening W (a : 𝒱) (b : 𝒱) = (W.bracketV1 a b : 𝒱) := rfl

/-! ### (a)  The derivation property -/

/-- **The screening operator is a derivation of every product**:
`Q_a(u₍ₙ₎v) = (Q_a u)₍ₙ₎v + u₍ₙ₎(Q_a v)` for all `u v` and all `n ∈ ℤ`.

This is the `ℓ = 0` case of the Borcherds/Jacobi commutator formula (Gannon 5.1.7c), in
which `C(0,j) = δ_{j0}` collapses the sum to its single `j = 0` term.  It is *not* reproved
here: the repository's `Core.LieAlgebraV1.zeroMode_isDerivation` already has it in the
strongest form (derived from the field `n`-th-product theorem `nth_product`, avoiding the
existential-`N` commutator form altogether).

**No hypothesis on `a` is needed.**  Weight one enters only for the *kernel* to be graded
and to contain `ω`; the Leibniz rule holds for the zero mode of an arbitrary state. -/
theorem screening_leibniz (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    screening W a (W.smul u n v)
      = W.smul (screening W a u) n v + W.smul u n (screening W a v) := by
  have h := W.zeroMode_isDerivation a u v n
  simp only [screening_apply]
  rw [← h]
  abel

/-- The commutator form: `[Q_a, u₍ₙ₎] = (Q_a u)₍ₙ₎` as operators. -/
theorem screening_comm_mode (W : VertexOperatorAlgebra 𝒱) (a u : 𝒱) (n : ℤ) (v : 𝒱) :
    screening W a (W.smul u n v) - W.smul u n (screening W a v)
      = W.smul (screening W a u) n v := by
  rw [screening_leibniz W a u n v]
  abel

/-- **Total-derivative contact terms make screening zero modes commute.**  Suppose the
simple-pole product of two screening states is a scalar multiple of a translate,
`a₍₀₎b = λ·Tc`.  Then their zero modes commute on every state.

This is the all-level algebraic endpoint of the standard free-boson mixed-screening
calculation.  The commutator formula identifies `[a₍₀₎,b₍₀₎]` with the zero mode of
`a₍₀₎b`; translation covariance identifies the field of `Tc` with a formal derivative;
and the zero mode (formal residue) of a derivative vanishes. -/
theorem screening_commute_of_zeroProduct_eq_translation
    (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (scalar : ℂ)
    (hcontact : W.smul a 0 b = scalar • W.toPreVertexAlgebra.T c) :
    Commute (screening W a) (screening W b) := by
  change screening W a * screening W b = screening W b * screening W a
  ext v
  have hcomm := screening_comm_mode W a b 0 v
  simp only [screening_apply] at hcomm
  have hzero : W.toPreVertexAlgebra.smul (W.toPreVertexAlgebra.T c) 0 v = 0 := by
    rw [PreVertexAlgebra.smul_def, VertexOperatorAlgebra.mode_Y_T]
    simp
  rw [hcontact, PreVertexAlgebra.smul_smul_left, hzero, smul_zero] at hcomm
  simpa only [Module.End.mul_apply, screening_apply] using sub_eq_zero.mp hcomm

/-! ### (b)  `Q_a 𝟙 = 0`, unconditionally -/

/-- `Q_a 𝟙 = 0`: immediate from the creation axiom VA3 (`u₍ₙ₎𝟙 = 0` for `n ≥ 0`). -/
theorem screening_vacuum (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) :
    screening W a W.vacuum = 0 := (W.creation a).2 0 le_rfl

/-! ### (c)  Weight one ⇒ degree `0` ⇒ commutes with the projections -/

/-- **VA1.**  For `a ∈ 𝒱₁`, the screening operator preserves every homogeneous grade:
`Q_a : 𝒱ₙ → 𝒱_{1+n-0-1} = 𝒱ₙ`. -/
theorem screening_mem_grading (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} (ha : a ∈ W.grading 1)
    {n : ℤ} {v : 𝒱} (hv : v ∈ W.grading n) : screening W a v ∈ W.grading n := by
  have h := W.smul_mem_grading ha hv 0
  rw [show (1 : ℤ) + n - 0 - 1 = n from by ring] at h
  exact h

/-- For `a ∈ 𝒱₁` the screening operator commutes with the homogeneous projections. -/
theorem screening_piHom (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} (ha : a ∈ W.grading 1)
    (n : ℤ) (v : 𝒱) : screening W a (piHom W n v) = piHom W n (screening W a v) :=
  piHom_comm_of_gradePreserving W (screening W a)
    (fun _ _ hx => screening_mem_grading W ha hx) n v

/-! ### (d)  `Q_a ω = 0` for `a ∈ 𝒱₁` — no primarity hypothesis

The skew-symmetry tower, computed exactly as in `Core.LieAlgebraV1.skew_v1_tower_vanish`
but with the second slot at weight `2` instead of weight `1`. -/

/-- `sgn (-2) = 1`. -/
theorem sgn_neg_two : sgn (-2 : ℤ) = 1 := by
  rw [sgn, if_pos (by decide : Even (-2 : ℤ))]

/-- The skew tower term at `j` for `a ∈ 𝒱₁` against `ω ∈ 𝒱₂`, `n = 0`, vanishes for `j ≥ 2`.

For `j = 2`: `ω₍₂₎a = L₁a ∈ 𝒱_{2+1-2-1} = 𝒱₀ = ℂ𝟙` (VA1 and VOA4) and `Tʲ` annihilates `ℂ𝟙`
for `j ≥ 1` (`T𝟙 = 0`).  For `j ≥ 3`: `ω₍ⱼ₎a ∈ 𝒱_{2-j}` with `2-j < 0`, so it is `0` by
VOA4 (`positivity`). -/
theorem skew_omega_tower_vanish (W : VertexOperatorAlgebra 𝒱) {a : 𝒱}
    (ha : a ∈ W.grading 1) (j : ℕ) (hj : 2 ≤ j) :
    ((j.factorial : ℂ)⁻¹) • (sgn (-(0 : ℤ) - 1 - j)) •
      ((W.toPreVertexAlgebra.T ^ j)
        ((W.Y W.conformalVector) (-(0 : ℤ) - 1 - j) a)) = 0 := by
  have hmode : (W.Y W.conformalVector) (-(0 : ℤ) - 1 - j) a
      = W.smul W.conformalVector (j : ℤ) a := by
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show (-(j : ℤ) - 1) = -(0 : ℤ) - 1 - (j : ℤ) from by ring]
  rw [hmode]
  have hmem : W.smul W.conformalVector (j : ℤ) a ∈ W.grading (2 - (j : ℤ)) := by
    have h := W.smul_mem_grading W.conformal_mem ha (j : ℤ)
    rwa [show (2 : ℤ) + 1 - (j : ℤ) - 1 = 2 - (j : ℤ) from by ring] at h
  rcases eq_or_lt_of_le hj with hj2 | hj3
  · have hj2' : (j : ℤ) = 2 := by exact_mod_cast hj2.symm
    rw [hj2', show (2 : ℤ) - 2 = 0 from by ring, W.vacuum_grade,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hTvac : (W.toPreVertexAlgebra.T ^ j) W.vacuum = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hk, pow_succ, Module.End.mul_apply, PreVertexAlgebra.T_vacuum, map_zero]
    have hT0 : (W.toPreVertexAlgebra.T ^ j) (W.smul W.conformalVector (j : ℤ) a) = 0 := by
      rw [hj2', ← hc, map_smul, hTvac, smul_zero]
    rw [hT0, smul_zero, smul_zero]
  · rw [W.positivity (2 - (j : ℤ)) (by omega), Submodule.mem_bot] at hmem
    rw [hmem, map_zero, smul_zero, smul_zero]

/-- A two-term evaluation of a `ℕ`-indexed `finsum` whose terms vanish from `j = 2` on. -/
theorem finsum_eq_two_terms {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (hf : ∀ j : ℕ, 2 ≤ j → f j = 0) : (∑ᶠ j : ℕ, f j) = f 0 + f 1 := by
  have hsub : Function.support f ⊆ (↑(Finset.range 2) : Set ℕ) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hj (hf j (by omega))
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_range_succ, Finset.sum_range_one]

/-- **`Q_a ω = 0` for every `a ∈ 𝒱₁`** — with **no primarity hypothesis**.

Skew-symmetry (Gannon 5.1.8, `Core.SkewSymmetry.skew_mode`) at `n = 0` writes `a₍₀₎ω` as the
tower `∑_j (1/j!)·sgn(-1-j)·Tʲ(ω₍ⱼ₎a)`.  All terms with `j ≥ 2` vanish by CFT type
(`skew_omega_tower_vanish`); the surviving `j = 0` and `j = 1` terms are `−L₋₁a = −Ta` and
`+T(L₀a) = +Ta`, which cancel. -/
theorem screening_conformalVector (W : VertexOperatorAlgebra 𝒱) {a : 𝒱}
    (ha : a ∈ W.grading 1) : screening W a W.conformalVector = 0 := by
  have hsk := W.skew_mode a W.conformalVector 0
  rw [finsum_eq_two_terms _ (fun j hj => skew_omega_tower_vanish W ha j hj)] at hsk
  have hidx0 : (-(0 : ℤ) - 1 - ((0 : ℕ) : ℤ)) = (-1 : ℤ) := by norm_num
  have hidx1 : (-(0 : ℤ) - 1 - ((1 : ℕ) : ℤ)) = (-2 : ℤ) := by norm_num
  rw [hidx0, hidx1, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, one_smul, pow_zero, pow_one, Module.End.one_apply,
    VertexOperatorAlgebra.sgn_neg_one, sgn_neg_two, neg_one_smul, one_smul] at hsk
  have hT : W.toPreVertexAlgebra.T a = (W.Y W.conformalVector) (-1 : ℤ) a := by
    have h : W.toPreVertexAlgebra.T a = W.L (-1) a := by
      rw [VertexOperatorAlgebra.T_eq_Lneg1]
    rw [h, VertexOperatorAlgebra.L_def, mode_apply,
      show (-((-1 : ℤ) + 1) - 1) = (-1 : ℤ) from by ring]
  have hL0 : (W.Y W.conformalVector) (-2 : ℤ) a = a := by
    have h := W.L0_grading a ha
    rw [mode_apply, show (-(1 : ℤ) - 1) = (-2 : ℤ) from by ring, Int.cast_one, one_smul] at h
    exact h
  rw [hL0, ← hT, neg_add_cancel] at hsk
  exact hsk

/-! ### The four clauses, assembled -/

/-- **A weight-one state gives a derivation of `W`.** -/
theorem screening_isDerivation (W : VertexOperatorAlgebra 𝒱) {a : 𝒱}
    (ha : a ∈ W.grading 1) : IsVOADerivation W (screening W a) where
  leibniz := screening_leibniz W a
  vacuum := screening_vacuum W a
  conformal := screening_conformalVector W ha
  piHom_comm := screening_piHom W ha

/-! ## §3  The screening kernel -/

/-- **The kernel of a screening operator is a vertex operator subalgebra.**  For
`a ∈ 𝒱₁`, `ker Q_a` contains `𝟙` and `ω`, is closed under every product `u₍ₙ₎v`, and is
graded. -/
def screeningKernel (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (ha : a ∈ W.grading 1) :
    VOASubalgebra W :=
  kerSubalgebra W (screening W a) (screening_isDerivation W ha)

@[simp] theorem mem_screeningKernel {W : VertexOperatorAlgebra 𝒱} {a : 𝒱}
    {ha : a ∈ W.grading 1} {x : 𝒱} :
    x ∈ (screeningKernel W a ha).carrier ↔ screening W a x = 0 := LinearMap.mem_ker

@[simp] theorem screeningKernel_carrier (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (ha : a ∈ W.grading 1) :
    (screeningKernel W a ha).carrier = LinearMap.ker (screening W a) := rfl

theorem vacuum_mem_screeningKernel (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (ha : a ∈ W.grading 1) : W.vacuum ∈ (screeningKernel W a ha).carrier :=
  (screeningKernel W a ha).vacuum_mem

theorem conformalVector_mem_screeningKernel (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (ha : a ∈ W.grading 1) : W.conformalVector ∈ (screeningKernel W a ha).carrier :=
  (screeningKernel W a ha).conformal_mem

/-- **The screening kernel is a VOA**, with the same central charge as `W`. -/
noncomputable def screeningKernelVOA (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (ha : a ∈ W.grading 1) : VertexOperatorAlgebra (screeningKernel W a ha).carrier :=
  (screeningKernel W a ha).toVOA

@[simp] theorem screeningKernelVOA_centralCharge (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (ha : a ∈ W.grading 1) :
    (screeningKernelVOA W a ha).centralCharge = W.centralCharge := rfl

@[simp] theorem screeningKernelVOA_Y_coe (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (ha : a ∈ W.grading 1) (u : (screeningKernel W a ha).carrier) (k : ℤ)
    (x : (screeningKernel W a ha).carrier) :
    (((screeningKernelVOA W a ha).Y u k x : (screeningKernel W a ha).carrier) : 𝒱)
      = W.Y u k x := rfl

/-! ## §4  Intersections of screening kernels

The free-field realisations of interest are cut out by *several* screenings at once (two for
the Virasoro minimal models, `rank 𝔤` for a general `W`-algebra), so what is actually used
downstream is that a family of screening kernels intersects to a subalgebra.  This is free:
`VOASubalgebra` carries an `InfSet` (`Core.VOASubalgebraGenerated`). -/

/-- **An arbitrary intersection of screening kernels is a vertex operator subalgebra.**
(In particular a finite one; take `ι = Fin n`.) -/
def screeningKernelInter {ι : Type*} (W : VertexOperatorAlgebra 𝒱) (a : ι → 𝒱)
    (ha : ∀ i, a i ∈ W.grading 1) : VOASubalgebra W :=
  sInf (Set.range fun i => screeningKernel W (a i) (ha i))

theorem mem_screeningKernelInter {ι : Type*} {W : VertexOperatorAlgebra 𝒱} {a : ι → 𝒱}
    {ha : ∀ i, a i ∈ W.grading 1} {x : 𝒱} :
    x ∈ (screeningKernelInter W a ha).carrier ↔ ∀ i, screening W (a i) x = 0 := by
  rw [screeningKernelInter, VOASubalgebra.mem_sInf]
  constructor
  · intro h i
    exact mem_screeningKernel.mp (h _ ⟨i, rfl⟩)
  · rintro h A ⟨i, rfl⟩
    exact mem_screeningKernel.mpr (h i)

/-- The intersection of the kernels of two screenings — the case relevant to the Virasoro
minimal models (`Q₊` and `Q₋`). -/
def screeningKernelPair (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱)
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) : VOASubalgebra W :=
  sInf ({screeningKernel W a ha, screeningKernel W b hb} : Set (VOASubalgebra W))

theorem mem_screeningKernelPair {W : VertexOperatorAlgebra 𝒱} {a b : 𝒱}
    {ha : a ∈ W.grading 1} {hb : b ∈ W.grading 1} {x : 𝒱} :
    x ∈ (screeningKernelPair W a b ha hb).carrier
      ↔ screening W a x = 0 ∧ screening W b x = 0 := by
  rw [screeningKernelPair, VOASubalgebra.mem_sInf]
  constructor
  · intro h
    exact ⟨mem_screeningKernel.mp (h _ (Set.mem_insert _ _)),
      mem_screeningKernel.mp (h _ (Set.mem_insert_of_mem _ rfl))⟩
  · rintro ⟨h1, h2⟩ A hA
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact mem_screeningKernel.mpr h1
    · exact mem_screeningKernel.mpr h2

/-- Monotonicity: a bigger family of screenings cuts out a smaller subalgebra. -/
theorem screeningKernelInter_le {ι : Type*} (W : VertexOperatorAlgebra 𝒱) (a : ι → 𝒱)
    (ha : ∀ i, a i ∈ W.grading 1) (i : ι) :
    (screeningKernelInter W a ha).carrier ≤ (screeningKernel W (a i) (ha i)).carrier := by
  intro x hx
  exact mem_screeningKernel.mpr (mem_screeningKernelInter.mp hx i)

/-- The intersection of a family of screening kernels is a VOA. -/
noncomputable def screeningKernelInterVOA {ι : Type*} (W : VertexOperatorAlgebra 𝒱)
    (a : ι → 𝒱) (ha : ∀ i, a i ∈ W.grading 1) :
    VertexOperatorAlgebra (screeningKernelInter W a ha).carrier :=
  (screeningKernelInter W a ha).toVOA

@[simp] theorem screeningKernelInterVOA_centralCharge {ι : Type*}
    (W : VertexOperatorAlgebra 𝒱) (a : ι → 𝒱) (ha : ∀ i, a i ∈ W.grading 1) :
    (screeningKernelInterVOA W a ha).centralCharge = W.centralCharge := rfl

/-! ## §5  The bridge to a concretely-built zero mode

`Examples.TripletScreening`'s `Qscr L α := mode (Yeαvec L α) 0` is of the shape `mode F 0`
for a hand-built field `F`; `Qscr_eq_mode_YfullGen` identifies `F` with the reconstructed
`Y` of the lattice VOA.  Whenever such an identification is available, the concrete operator
*is* the general screening operator.  See the module docstring for the (real) caveat about
which conformal vector measures `wt(e^α) = 1`. -/

/-- If a concretely-built field `F` is the vertex operator of the state `a`, then the
concretely-built zero mode `mode F 0` is the screening operator `Q_a`. -/
theorem screening_eq_mode_of_Y_eq (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (F : FormalDist (End ℂ 𝒱)) (hF : W.Y a = F) : screening W a = mode F 0 := by
  rw [screening, hF]

/-- The same identification at the level of a single vector. -/
theorem screening_apply_eq_mode_of_Y_eq (W : VertexOperatorAlgebra 𝒱) (a : 𝒱)
    (F : FormalDist (End ℂ 𝒱)) (hF : W.Y a = F) (v : 𝒱) :
    screening W a v = mode F 0 v := by
  rw [screening_eq_mode_of_Y_eq W a F hF]

/-! ## §6  The super analogue

For a `SuperNearVOA` the *grading* half of the argument goes through verbatim — VA1 makes a
weight-one `a` give a degree-`0` zero mode, VA1′ makes an **even** `a` give a parity-preserving
one, and VA3 kills the vacuum — so the two projection clauses and `vacuum_mem` of
`SuperVOASubalgebra` are proved here outright.

The two facts that need the super Borcherds machinery are carried as the two remaining fields
of `IsSuperScreening`.  The machinery itself exists (`superJacobi`, `mode_iterateε`,
unconditional super skew `superSmul_eq_skew_Lpow`, which makes the conditional
`Core.SuperSkew.skew_modeε` unnecessary), and `leibniz` is noted dischargeable in
`Modules/SuperAdjointModule.lean`; neither field is discharged from it here. -/

/-- The **super screening operator** `Q_a := a₍₀₎` of a super near-VOA. -/
def superScreening (W : SuperNearVOA 𝒱) (a : 𝒱) : End ℂ 𝒱 := mode (W.Y a) 0

theorem superScreening_apply (W : SuperNearVOA 𝒱) (a v : 𝒱) :
    superScreening W a v = mode (W.Y a) 0 v := rfl

/-- `Q_a 𝟙 = 0`, from the super creation axiom VA3.  Unconditional. -/
theorem superScreening_vacuum (W : SuperNearVOA 𝒱) (a : 𝒱) :
    superScreening W a W.vacuum = 0 := (W.creation a).2 0 le_rfl

/-- **VA1.**  A weight-one `a` gives a degree-`0` zero mode: `Q_a : 𝒱_h → 𝒱_{1+h-0-1} = 𝒱_h`. -/
theorem superScreening_mem_grading (W : SuperNearVOA 𝒱) {a : 𝒱} (ha : a ∈ W.grading 1)
    {h : ℂ} {v : 𝒱} (hv : v ∈ W.grading h) : superScreening W a v ∈ W.grading h := by
  have hg := W.grading_mode a ha v hv 0
  rw [show (1 : ℂ) + h - ((0 : ℤ) : ℂ) - 1 = h from by norm_num] at hg
  exact hg

/-- **VA1′.**  An *even* `a` gives a parity-preserving zero mode: `Q_a : 𝒱_q → 𝒱_{0+q} = 𝒱_q`.
Evenness is genuinely needed — an odd screening would shift the parity. -/
theorem superScreening_mem_parity (W : SuperNearVOA 𝒱) {a : 𝒱} (hp : a ∈ W.parity 0)
    {q : ZMod 2} {v : 𝒱} (hv : v ∈ W.parity q) : superScreening W a v ∈ W.parity q := by
  have hg := W.parity_mode a hp v hv 0
  rw [zero_add] at hg
  exact hg

/-- A weight-preserving operator commutes with the weight projections `π_h`. -/
theorem wtProj_comm_of_gradePreserving (W : SuperNearVOA 𝒱) (D : End ℂ 𝒱)
    (hD : ∀ (h : ℂ) (v : 𝒱), v ∈ W.grading h → D v ∈ W.grading h) (k : ℂ) (v : 𝒱) :
    D (W.wtProj k v) = W.wtProj k (D v) := by
  classical
  obtain ⟨s, hs, hns⟩ := W.exists_sum_wtProj v
  have hsum : D v = ∑ h ∈ s, D (W.wtProj h v) := by
    conv_lhs => rw [← hs]
    exact map_sum D _ _
  rw [hsum, map_sum, Finset.sum_eq_single k]
  · rw [W.wtProj_of_mem (hD k _ (W.wtProj_mem k v))]
  · intro j _ hjk
    rw [W.wtProj_of_mem_ne hjk (hD j _ (W.wtProj_mem j v))]
  · intro hk
    rw [hns k hk, map_zero, map_zero]

/-- A parity-preserving operator commutes with the parity projections `π_p`. -/
theorem parProj_comm_of_parityPreserving (W : SuperNearVOA 𝒱) (D : End ℂ 𝒱)
    (hD : ∀ (q : ZMod 2) (v : 𝒱), v ∈ W.parity q → D v ∈ W.parity q) (p : ZMod 2) (v : 𝒱) :
    D (W.parProj p v) = W.parProj p (D v) := by
  classical
  obtain ⟨s, hs, hns⟩ := W.exists_sum_parProj v
  have hsum : D v = ∑ q ∈ s, D (W.parProj q v) := by
    conv_lhs => rw [← hs]
    exact map_sum D _ _
  rw [hsum, map_sum, Finset.sum_eq_single p]
  · rw [W.parProj_of_mem (hD p _ (W.parProj_mem p v))]
  · intro j _ hjp
    rw [W.parProj_of_mem_ne hjp (hD j _ (W.parProj_mem j v))]
  · intro hp
    rw [hns p hp, map_zero, map_zero]

/-- **What it takes for `a₍₀₎` to be a screening operator on a super near-VOA.**

The first two fields are proved facts about `a` in the examples (weight one, even).  The last
two are the *inputs the repository does not yet have*, stated exactly:

* `leibniz` — the super `ℓ = 0` Borcherds/Jacobi commutator formula.  For an **even** `a` there
  are no Koszul signs, so the identity has literally the bosonic shape; what is missing is a
  super analogue of `Core.Reconstruction.nth_product` (equivalently of `mode_iterate` at
  `ℓ = 0`).
* `conformal` — `a₍₀₎ω = 0`, which in the bosonic case (`screening_conformalVector`) came from
  skew-symmetry plus CFT type.  Super skew-symmetry `Core.SuperSkew.skew_modeε` is currently
  gated on `WeakAssocLocε`, and a `SuperNearVOA` is not assumed CFT type at all, so both halves
  of that argument are unavailable here.

Given the four, `superScreeningKernel` is a genuine theorem. -/
structure IsSuperScreening (W : SuperNearVOA 𝒱) (a : 𝒱) : Prop where
  /-- `a` has conformal weight one. -/
  weight_one : a ∈ W.grading 1
  /-- `a` is even (no Koszul signs, and the zero mode preserves parity). -/
  even : a ∈ W.parity 0
  /-- `a₍₀₎` is a derivation of every product. -/
  leibniz : ∀ (u : 𝒱) (n : ℤ) (v : 𝒱),
      superScreening W a (mode (W.Y u) n v)
        = mode (W.Y (superScreening W a u)) n v + mode (W.Y u) n (superScreening W a v)
  /-- `a₍₀₎ω = 0`. -/
  conformal : superScreening W a W.conformalVector = 0

/-- **The kernel of a super screening operator is a super vertex operator subalgebra**, hence
(via `SuperVOASubalgebra.toSuperNearVOA`) a super near-VOA with the same central charge.

Only `vacuum_mem`, `wt_graded` and `par_graded` are proved from scratch here; `smul_mem` and
`conformal_mem` are the two hypotheses of `IsSuperScreening`. -/
def superScreeningKernel (W : SuperNearVOA 𝒱) (a : 𝒱) (h : IsSuperScreening W a) :
    SuperVOASubalgebra W where
  carrier := LinearMap.ker (superScreening W a)
  vacuum_mem := LinearMap.mem_ker.mpr (superScreening_vacuum W a)
  conformal_mem := LinearMap.mem_ker.mpr h.conformal
  smul_mem := by
    intro u hu n v hv
    rw [LinearMap.mem_ker] at hu hv ⊢
    have hl := h.leibniz u n v
    rw [hu, hv] at hl
    simp only [map_zero, mode_zero, LinearMap.zero_apply, add_zero] at hl
    exact hl
  wt_graded := by
    intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [wtProj_comm_of_gradePreserving W (superScreening W a)
      (fun _ _ hx => superScreening_mem_grading W h.weight_one hx) k v, hv, map_zero]
  par_graded := by
    intro p v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [parProj_comm_of_parityPreserving W (superScreening W a)
      (fun _ _ hx => superScreening_mem_parity W h.even hx) p v, hv, map_zero]

@[simp] theorem mem_superScreeningKernel {W : SuperNearVOA 𝒱} {a : 𝒱}
    {h : IsSuperScreening W a} {x : 𝒱} :
    x ∈ (superScreeningKernel W a h).carrier ↔ superScreening W a x = 0 := LinearMap.mem_ker

/-- The super screening kernel is a super near-VOA. -/
noncomputable def superScreeningKernelVOA (W : SuperNearVOA 𝒱) (a : 𝒱)
    (h : IsSuperScreening W a) : SuperNearVOA (superScreeningKernel W a h).carrier :=
  (superScreeningKernel W a h).toSuperNearVOA

@[simp] theorem superScreeningKernelVOA_centralCharge (W : SuperNearVOA 𝒱) (a : 𝒱)
    (h : IsSuperScreening W a) :
    (superScreeningKernelVOA W a h).centralCharge = W.centralCharge := rfl

end Screening

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Inner automorphism construction (Gannon 5.2.4).**  For `u ∈ 𝒱₁`, *if* the zero-mode
`D := u₍₀₎` is locally nilpotent (`VOA.IsLocNilp`), then `exp(D)` is an automorphism
`α : Aut W` with `IsExpInner u α`.  The condition `D ω = 0` holds for every weight-one state
(`Screening.screening_conformalVector`, no primarity needed), so it is not a hypothesis; an
earlier version carried it as the redundant hypothesis `homega` (register entry 11).  The vacuum
is fixed (`zeroMode_one_vacuum`); the product is intertwined by `expFun_smul`; invertibility is
`expEquiv`. -/
theorem inner_of_locallyNilpotent (u : W.grading 1)
    (hnilp : VOA.IsLocNilp (W.zeroMode (u : 𝒱) 1)) :
    ∃ α : Aut W, IsExpInner u α := by
  have homega : W.zeroMode (u : 𝒱) 1 W.conformalVector = 0 := by
    rw [← Screening.screening_eq_zeroMode]; exact Screening.screening_conformalVector W u.2
  exact ⟨inner u hnilp homega, inner_isExpInner u hnilp homega⟩

end VertexOperatorAlgebra

end VOA
