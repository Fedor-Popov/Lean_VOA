/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.GoodFiltration
import VOA.Core.RealStructure
import VOA.Core.InvariantFormRadical
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Graded unitarity: the statement, and the layer reduction

⚠ **NOTHING IN THIS FILE IS A PROOF OF GRADED UNITARITY.**  The file contains

* (a) the **formalized statement** — clauses (iii), (v), (vi) of the datum of Arabi
  Ardehali–Beem–Lemos–Rastelli, *Graded Unitarity in the SCFT/VOA Correspondence*,
  arXiv:2507.23781v2 = JHEP 06 (2026) 075, Definition 2.2, assembled on top of the flag of
  `Core.GoodFiltration` and the anti-linear `ρ` of `Core.RealStructure`; and
* (b) a **reduction**: given nondegeneracy of the form on every step of the flag (clause (iv)),
  the Gram–Schmidt orthogonal decomposition of clause (v) is *not an extra hypothesis* — it is a
  theorem, and the layers have the expected dimensions.

The statement whose truth is open — that the boundary Virasoro minimal models `L(c_{2,2n+1},0)`
satisfy this — is **not** touched here.  It has been open since Kaufmann, hep-th/9405041, §4.2
(1994); the only evidence this repository carries for it is numerical.

## §0 ⚠⚠ Why clause (vi) is stated for a sesquilinear form.  Read this first.

**Remark.**  A tempting encoding of the positivity clause (vi) is

```
def IsPosOn (β : BilinForm ℂ E) (S : Submodule ℂ E) : Prop :=
  ∀ x ∈ S, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ β x x = (r : ℂ)
```

— positivity of a ℂ-**bilinear** form on a ℂ-**submodule**.  That is self-defeating.  If `x ∈ S`
then `i·x ∈ S`, and bilinearity gives `β (i x) (i x) = i² β x x = -β x x`; so `β x x` and
`β (ix) (ix)` cannot both be positive reals.  The predicate therefore forced `S = ⊥`, and
`GradedUnitary`/`VirGradedUnitary` would be **provably false** for every VOA with a nonzero
weight space, although the conjecture is *open*.  A refutable predicate advertised as
open is worse than an open one.

That argument is not folklore here: it is a **theorem of this file**,
`eq_bot_of_bilinear_pos`.

**The correct encoding.**  ABLR clause (vi) is not about the bilinear form.  Clause (iii) introduces the
*sesquilinear* form (2.30) `(a,b) ↦ B(ρ a, b)` built from the anti-linear `ρ`; clause (vi) asserts
positive definiteness of the **Hermitian** form (2.33), the `σ`-twisted version of that
sesquilinear form.  On a sesquilinear form the obstruction evaporates:

  `⟨i x, i x⟩ = \bar i · i · ⟨x,x⟩ = |i|² ⟨x,x⟩ = ⟨x,x⟩`   (`SesqForm.I_smul_self`).

So positivity is stated for a bundled `SesqForm` — conjugate-linear in the first slot,
ℂ-linear in the second — and `IsPosOn` does not accept a `BilinForm` at all.  Two
non-vacuity checks, both proved below:

* **not refutable.** The killing step is dead (`SesqForm.I_smul_self`, `isPosOn_I_smul`); the
  predicate *does* hold on a nonzero subspace (`isPosOn_stdHerm_top` with
  `top_ne_bot_of_complex`); and — sharper — it holds on a nonzero layer of a *genuine* VOA,
  `isPosOn_layer_zero_vacuum`, where under the bilinear encoding it is false.  (This is consistency of
  the *clause*, not a model of the full datum: building a graded-unitary VOA is the open problem
  and is not attempted.)
* **not trivially true.** `not_isPosOn_signedForm_stdHerm_one` exhibits a Hermitian form and a
  nonzero subspace where `IsPosOn` **fails**, while `isPosOn_signedForm_stdHerm_zero` shows that
  the same pair passes at the preceding layer.  At the VOA level, `pos_gradedSesq_vacuum`
  verifies directly that the untwisted form is positive on the vacuum line, as the `p = 0`
  convention requires.

**What stays bilinear.**  Clauses (iv) and (v) — nondegeneracy on the steps and the
Gram–Schmidt decomposition — are pure ℂ-bilinear linear algebra
(`layerDecomposition`, `finrank_pieceLT_add_layer`, `iSup_layer_eq_top`).  That is legitimate and
not a fudge: `orthogonal_gradedSesq_eq` proves that on a `ρ`-stable step **the sesquilinear
orthogonal complement and the bilinear one are the same submodule**, so the layer `L_p` carved out
by the bilinear form is ABLR's layer.

## §1 Clause (iii): the sesquilinear form, and where the bilinear form still belongs

ABLR's form (2.30) is `(a,b) ↦ B(ρ a, b)`: conjugate-linear in the first slot, ℂ-linear in the
second.  It is recorded as `sesqForm` (unbundled, with its homogeneity lemmas) and as
`gradedSesq` (bundled as a `SesqForm` on a single weight space) — never as a `BilinForm`, which it
is not.

The ℂ-**bi**linear `LiRadical.gradedForm` continues to carry clauses (iv)–(v), for two reasons
that are theorems rather than assertions:

* `orthogonal_gradedSesq_eq` — on a `ρ`-stable subspace the two orthogonal complements coincide,
  so the flag geometry is the same whichever form defines it;
* `sesqForm_eq_form_of_fixes` / `sesq_diag_eq_gradedForm` — **on a set where `ρ` is the identity
  the two forms agree**, which is why the repository's bilinear Gram matrices compute ABLR's
  Hermitian values on the Virasoro creation monomials (whose structure constants are real).

## §2 The sign, and why it is `(-1)^p`

This repository uses the textbook normalisation `(𝟙|𝟙) = +1` (`InvariantForm.Normalized`), so
its canonical Gram matrix has the textbook global sign.  ABLR eq. (3.16) / Kaufmann eq. (4.4)
read `sign⟨O|O⟩ = (-1)^{R_O}`; accordingly `signedForm` below carries `(-1)^p`.  This is ABLR's
`σ`-twist (2.33), applied to the sesquilinear form of clause (iii) to produce the Hermitian form
of clause (vi).

The exponent is **machine-calibrated, not asserted**: `signedForm_gradedSesq_vacuum` and
`pos_gradedSesq_vacuum` compute the signed and untwisted values on the vacuum layer to be
`(𝟙|𝟙) = +1`.  The VOA-free witnesses `isPosOn_signedForm_stdHerm_zero` and
`not_isPosOn_signedForm_stdHerm_one` check that the same positive Hermitian form passes at layer
`0` and fails after the sign flip at layer `1`.

Further calibration, reproduced by hand against this repository's own mode
identities: at `c = -22/5`, level `6`, in the words `L₋₆|0⟩` and `L₋₄L₋₂|0⟩`, the *textbook* Gram
matrix is `[[-77, -22], [-22, 66/5]]`, with pivots `-77` (length 1, negative) and `682/35`
(length 2, positive).

## §3 What the reduction says, stated so it cannot be misread

`layerDecomposition` and `finrank_pieceLT_add_layer` say: **if** the form is nondegenerate on every
step `G_p 𝒱ₙ` of the flag, **then** `G_p 𝒱ₙ = G_{p-1} 𝒱ₙ ⊕ L_p` with `L_p` the orthogonal
complement of `G_{p-1}` inside `G_p`, and `dim L_p = dim G_p - dim G_{p-1}`.  That is clause (v)
of Definition 2.2 *derived from* clause (iv).  It is **not** a proof that the form is
nondegenerate on the steps, and it is **not** a proof of the positivity clause (vi).

## Status
* Definitions and the layer reduction, `sorry`-free, no new axioms.
* Clause (vi) is stated for the **Hermitian/sesquilinear** form, and the refutation of the
  bilinear encoding is recorded as a theorem (`eq_bot_of_bilinear_pos`).
* The pivot/leading-principal-minor form of the criterion is proved in
  `Core.MinorPivots` (not in this file): the converse Sylvester criterion
  `posDef_of_det_leadingPrincipal_pos` and the layer lemmas `schurOfLeading_posDef_of_sign_ratios`
  / `schurOfLeading_negDef_of_sign_ratios`.
* The universal affine VOA `V^k(sl₂)` is proved graded unitary for every real `k < -2`, for the
  ordinary current-length flag and the constructed compact real structure:
  `AffineSl2BelowCritical.universal_gradedUnitary_belowCritical_unconditional`
  (`Examples/AffineSl2BelowCriticalAnchor.lean`).  Partial positivity (through length two) for
  the Virasoro boundary family is in `Examples/VirasoroLengthTwoLayerPositive.lean`
  (`boundary_gradedUnitaryThroughTwo`).
⚠ `GradedUnitary B R F` quantifies over an arbitrary `GradedFlag` `F`, not tied to the vertex
  operators or to ABLR's filtration, so "graded unitary for some flag" is nearly vacuous.
  Kaufmann 1994 is open; Beem–Garner arXiv:2509.10364, by an ABLR co-author, records that ABLR did
  not establish the full graded-unitary structure.

## References
* Arabi Ardehali, Beem, Lemos, Rastelli, arXiv:2507.23781v2, Definition 2.2 and eqs. (2.30),
  (2.33), (3.11), (3.16).
* R. M. Kaufmann, hep-th/9405041, §4.2, eq. (4.4).
-/

namespace VOA

open VOA.VertexOperatorAlgebra
open LinearMap (BilinForm)
open Module (finrank)

universe u

/-! ## §1  Clause (iii): the sesquilinear form `(a,b) ↦ B(ρa, b)` -/

section Sesq

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **ABLR eq. (2.30)**: the sesquilinear form attached to an invariant bilinear form `B` and an
anti-linear automorphism `ρ`.  Conjugate-linear in the first slot, ℂ-linear in the second, so it
is deliberately *not* packaged as a `BilinForm`. -/
def sesqForm (B : InvariantForm W) (R : RealStructure W) (a b : 𝒱) : ℂ := B.form (R.rho a) b

variable (B : InvariantForm W) (R : RealStructure W)

@[simp] theorem sesqForm_apply (a b : 𝒱) : sesqForm B R a b = B.form (R.rho a) b := rfl

theorem sesqForm_add_left (a a' b : 𝒱) :
    sesqForm B R (a + a') b = sesqForm B R a b + sesqForm B R a' b := by
  simp [sesqForm, R.map_add]

theorem sesqForm_add_right (a b b' : 𝒱) :
    sesqForm B R a (b + b') = sesqForm B R a b + sesqForm B R a b' := by
  simp [sesqForm]

/-- Conjugate-homogeneity in the first slot. -/
theorem sesqForm_smul_left (z : ℂ) (a b : 𝒱) :
    sesqForm B R (z • a) b = (starRingEnd ℂ) z * sesqForm B R a b := by
  simp [sesqForm, R.antilinear, smul_eq_mul]

/-- ℂ-homogeneity in the second slot. -/
theorem sesqForm_smul_right (z : ℂ) (a b : 𝒱) :
    sesqForm B R a (z • b) = z * sesqForm B R a b := by
  simp [sesqForm, smul_eq_mul]

/-- **The collapse onto the bilinear form.**  Where `ρ` is the identity, ABLR's sesquilinear
form (2.30) *is* the repository's ℂ-bilinear invariant form.  This is why the bilinear Gram
matrices this repository computes are also the Hermitian values of clause (iii) on the Virasoro
creation monomials — whose structure constants are real, so `ρ` fixes them.

⚠ It is **not** a licence to state clause (vi) for the bilinear form: see §0 and
`eq_bot_of_bilinear_pos`.  The collapse holds pointwise on a `ρ`-fixed *set*, which is a real
form, never a ℂ-submodule. -/
theorem sesqForm_eq_form_of_fixes {S : Set 𝒱} (hfix : R.Fixes S) {a : 𝒱} (ha : a ∈ S) (b : 𝒱) :
    sesqForm B R a b = B.form a b := by rw [sesqForm, hfix.apply ha]

end Sesq

/-! ## §2  Sesquilinear forms, positivity on a subspace, and the sign convention

⚠ The whole point of this section is §0: positivity is a statement about a **sesquilinear** form.
`IsPosOn` does not accept a `BilinForm`, and `eq_bot_of_bilinear_pos` says why. -/

section PosDef

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- ⚠⚠ **Remark: the bilinear encoding of clause (vi) is refuted.**

Asking a ℂ-**bilinear** form to take positive real values on every nonzero vector of a
ℂ-**submodule** forces that submodule to be `⊥`: if `β x x = r > 0` then `i·x` is also in `S` and
`β (i x) (i x) = i² · r = -r < 0`.

Had ABLR clause (vi) been encoded in that shape, `GradedUnitary` would be refutable for every VOA
with a nonzero weight space, although the conjecture is open.  Clause (vi) is stated for `SesqForm` below, where the
same step is harmless (`SesqForm.I_smul_self`). -/
theorem eq_bot_of_bilinear_pos (β : BilinForm ℂ E) (S : Submodule ℂ E)
    (hpos : ∀ x ∈ S, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ β x x = (r : ℂ)) : S = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  by_contra hne
  obtain ⟨r, hr, hrx⟩ := hpos x hx hne
  obtain ⟨s, hs, hsx⟩ :=
    hpos (Complex.I • x) (S.smul_mem _ hx) (smul_ne_zero Complex.I_ne_zero hne)
  have hval : β (Complex.I • x) (Complex.I • x) = -(r : ℂ) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hrx]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  rw [hsx] at hval
  have : ((s : ℝ) : ℂ) = ((-r : ℝ) : ℂ) := by rw [hval, Complex.ofReal_neg]
  have hsr : s = -r := Complex.ofReal_inj.1 this
  linarith

/-- A **sesquilinear form** on a ℂ-module: conjugate-linear in the first slot, ℂ-linear in the
second.  This is the shape of ABLR's (2.30), and it is the shape clause (vi) has to be stated for
— see §0 and `eq_bot_of_bilinear_pos`.

Hermitian symmetry is deliberately *not* a field: the positivity predicate `IsPosOn` asserts
reality of the diagonal where it needs it (`β x x = (r : ℂ)`), which is the honest content, and
nothing below needs symmetry. -/
structure SesqForm (E : Type*) [AddCommGroup E] [Module ℂ E] where
  /-- The underlying function. -/
  toFun : E → E → ℂ
  /-- Additivity in the first slot. -/
  add_left : ∀ a a' b : E, toFun (a + a') b = toFun a b + toFun a' b
  /-- **Conjugate**-homogeneity in the first slot: `⟨z a, b⟩ = z̄ ⟨a,b⟩`. -/
  smul_left : ∀ (z : ℂ) (a b : E), toFun (z • a) b = (starRingEnd ℂ) z * toFun a b
  /-- Additivity in the second slot. -/
  add_right : ∀ a b b' : E, toFun a (b + b') = toFun a b + toFun a b'
  /-- ℂ-homogeneity in the second slot: `⟨a, z b⟩ = z ⟨a,b⟩`. -/
  smul_right : ∀ (z : ℂ) (a b : E), toFun a (z • b) = z * toFun a b

namespace SesqForm

instance : CoeFun (SesqForm E) fun _ => E → E → ℂ := ⟨SesqForm.toFun⟩

@[simp] theorem coe_mk (f : E → E → ℂ) (h₁ h₂ h₃ h₄) (a b : E) :
    (SesqForm.mk f h₁ h₂ h₃ h₄ : E → E → ℂ) a b = f a b := rfl

theorem zero_right (h : SesqForm E) (x : E) : h x 0 = 0 := by
  have := h.smul_right 0 x 0
  rwa [zero_smul, zero_mul] at this

theorem zero_left (h : SesqForm E) (x : E) : h 0 x = 0 := by
  have := h.smul_left 0 0 x
  rwa [zero_smul, map_zero, zero_mul] at this

/-- **The obstruction of §0 is gone.**  On a sesquilinear form the diagonal scales by
`z̄ z = |z|²`, a *nonnegative real*, not by `z²`. -/
theorem smul_self (h : SesqForm E) (z : ℂ) (x : E) :
    h (z • x) (z • x) = ((starRingEnd ℂ) z * z) * h x x := by
  rw [h.smul_left, h.smul_right, ← mul_assoc]

/-- **The exact step that refuted the bilinear encoding, and its fate here.**  For the
bilinear form `β (i x) (i x) = -β x x` (whence `eq_bot_of_bilinear_pos`); for a sesquilinear form
the value is *unchanged*. -/
theorem I_smul_self (h : SesqForm E) (x : E) :
    h (Complex.I • x) (Complex.I • x) = h x x := by
  rw [h.smul_self, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-- The orthogonal complement with respect to a sesquilinear form: the `y` killed by every `x` of
`S` in the *first* slot, matching ABLR's convention for (2.30). -/
def orthogonal (h : SesqForm E) (S : Submodule ℂ E) : Submodule ℂ E where
  carrier := {y | ∀ x ∈ S, h x y = 0}
  add_mem' := fun hy hz x hx => by rw [h.add_right, hy x hx, hz x hx, add_zero]
  zero_mem' := fun x _ => h.zero_right x
  smul_mem' := fun c _ hy x hx => by rw [h.smul_right, hy x hx, mul_zero]

@[simp] theorem mem_orthogonal {h : SesqForm E} {S : Submodule ℂ E} {y : E} :
    y ∈ h.orthogonal S ↔ ∀ x ∈ S, h x y = 0 := Iff.rfl

end SesqForm

/-- A **sesquilinear** form is **positive on `S`** if its diagonal values on the nonzero vectors of
`S` are positive reals.  (Stated as "equals a positive real", which is the honest content: the form
takes values in `ℂ`, and both reality and positivity are being asserted.)

⚠ This is ABLR clause (vi) — positive definiteness of the Hermitian form (2.33).  It takes a
`SesqForm`, **never** a `BilinForm`: see §0 and `eq_bot_of_bilinear_pos`. -/
def IsPosOn (h : SesqForm E) (S : Submodule ℂ E) : Prop :=
  ∀ x ∈ S, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ h x x = (r : ℂ)

/-- Positivity on the zero subspace is vacuous.  (So the *content* of `LayerPositive` lives on the
layers that are nonzero — see `exists_layer_ne_bot`.) -/
theorem isPosOn_bot (h : SesqForm E) : IsPosOn h (⊥ : Submodule ℂ E) := by
  intro x hx hne
  exact absurd (Submodule.mem_bot ℂ |>.1 hx) hne

/-- **Consistency of the sesquilinear clause, at the point where the bilinear one breaks.**  If
`IsPosOn h S` holds and `x ∈ S` is nonzero, the vector `i·x` — which is also in `S`, and which
refuted the bilinear encoding — carries *the same* positive value. -/
theorem isPosOn_I_smul {h : SesqForm E} {S : Submodule ℂ E} (hS : IsPosOn h S) {x : E}
    (hx : x ∈ S) (hne : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ h (Complex.I • x) (Complex.I • x) = (r : ℂ) := by
  obtain ⟨r, hr, hrx⟩ := hS x hx hne
  exact ⟨r, hr, by rw [h.I_smul_self, hrx]⟩

/-- The sign-corrected (`σ`-twisted, ABLR (2.33)) form of layer `p`: `(-1)^p h`.

The exponent agrees with the textbook convention because this repository normalises
`(𝟙|𝟙) = +1`.  See §2 of the file docstring and the vacuum and standard-Hermitian calibrations
below. -/
def signedForm (h : SesqForm E) (p : ℕ) : SesqForm E where
  toFun a b := (-1 : ℂ) ^ p * h a b
  add_left a a' b := by rw [h.add_left]; ring
  smul_left z a b := by rw [h.smul_left]; ring
  add_right a b b' := by rw [h.add_right]; ring
  smul_right z a b := by rw [h.smul_right]; ring

@[simp] theorem signedForm_apply (h : SesqForm E) (p : ℕ) (x y : E) :
    signedForm h p x y = (-1 : ℂ) ^ p * h x y := rfl

end PosDef

/-! ### §2.5  ⚠ Non-vacuity witnesses: the clause is satisfiable, and it is not vacuous

Both failure modes are checked here, on the smallest possible
example: an over-strong encoding (the bilinear one, refuted for every nonzero subspace) and an
over-weak one (a predicate everything satisfies). -/

section Witnesses

/-- The standard Hermitian form on `ℂ`, `⟨a,b⟩ = ā b`. -/
def stdHerm : SesqForm ℂ where
  toFun a b := (starRingEnd ℂ) a * b
  add_left a a' b := by rw [map_add]; ring
  smul_left z a b := by rw [smul_eq_mul, map_mul]; ring
  add_right a b b' := by ring
  smul_right z a b := by rw [smul_eq_mul]; ring

@[simp] theorem stdHerm_apply (a b : ℂ) : stdHerm a b = (starRingEnd ℂ) a * b := rfl

/-- `ℂ` has a subspace other than `⊥` — needed to make the witnesses below say something. -/
theorem top_ne_bot_of_complex : (⊤ : Submodule ℂ ℂ) ≠ ⊥ := by
  intro h
  have h1 : (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) := h ▸ Submodule.mem_top
  exact one_ne_zero (Submodule.mem_bot ℂ |>.1 h1)

/-- **Not refutable (the clause is satisfiable on a nonzero subspace).**  The sesquilinear `IsPosOn`
holds for the standard Hermitian form on all of `ℂ`, and `⊤ ≠ ⊥` (`top_ne_bot_of_complex`).

Contrast `eq_bot_of_bilinear_pos`: with the bilinear encoding **no** nonzero subspace could
satisfy the clause, for any form whatsoever. -/
theorem isPosOn_stdHerm_top : IsPosOn stdHerm (⊤ : Submodule ℂ ℂ) := by
  intro x _ hx
  refine ⟨Complex.normSq x, Complex.normSq_pos.2 hx, ?_⟩
  rw [stdHerm_apply, ← Complex.normSq_eq_conj_mul_self]

/-- **The textbook base sign is positive.**  At layer `0` the twist is `(-1)^0 = +1`, so the
standard Hermitian form remains positive on all of `ℂ`. -/
theorem isPosOn_signedForm_stdHerm_zero :
    IsPosOn (signedForm stdHerm 0) (⊤ : Submodule ℂ ℂ) := by
  intro x _ hx
  refine ⟨Complex.normSq x, Complex.normSq_pos.2 hx, ?_⟩
  rw [signedForm_apply, stdHerm_apply, ← Complex.normSq_eq_conj_mul_self]
  norm_num

/-- **NOT TRIVIALLY TRUE (the clause has teeth).**  At layer `1` the twist is
`(-1)^1 = -1`, so the same form and the same nonzero subspace fail the clause.  Layers `0` and
`1` impose opposite sign conditions, as required by ABLR eq. (3.16) / Kaufmann eq. (4.4). -/
theorem not_isPosOn_signedForm_stdHerm_one :
    ¬ IsPosOn (signedForm stdHerm 1) (⊤ : Submodule ℂ ℂ) := by
  intro hpos
  obtain ⟨r, hr, hval⟩ := hpos 1 Submodule.mem_top one_ne_zero
  have hv : signedForm stdHerm 1 1 1 = (-1 : ℂ) := by
    rw [signedForm_apply, stdHerm_apply, map_one]
    norm_num
  rw [hv] at hval
  have h1 : ((-1 : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
    rw [Complex.ofReal_neg, Complex.ofReal_one, hval]
  have : (-1 : ℝ) = r := Complex.ofReal_inj.1 h1
  linarith

end Witnesses

/-! ## §3  The layer reduction, as pure linear algebra

Everything in this section is about a ℂ-**bi**linear form on a finite-dimensional space and a pair
of nested subspaces; there is no VOA content, and no positivity.  It is the engine of clause (v),
and it stays bilinear (see §0) — legitimately so, because `orthogonal_gradedSesq_eq` below
identifies the bilinear orthogonal complement with ABLR's sesquilinear one on `ρ`-stable
subspaces. -/

section LayerLinearAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
variable {β : BilinForm ℂ E}

/-- The zero subspace is nondegenerate for any form (vacuously). -/
theorem nondegenerate_restrict_bot (β : BilinForm ℂ E) :
    (β.restrict (⊥ : Submodule ℂ E)).Nondegenerate :=
  ⟨fun x _ => Subsingleton.elim x 0, fun x _ => Subsingleton.elim x 0⟩

/-- **Gram–Schmidt, one step.**  If `β` is reflexive and nondegenerate on `S`, then any `T ⊇ S`
splits as `S` plus the part of `T` orthogonal to `S`. -/
theorem sup_inf_orthogonal_eq (href : β.IsRefl) {S T : Submodule ℂ E} (hST : S ≤ T)
    (hnd : (β.restrict S).Nondegenerate) : S ⊔ (T ⊓ β.orthogonal S) = T := by
  have hc : IsCompl S (β.orthogonal S) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate href hnd
  have h1 : (S ⊔ β.orthogonal S) ⊓ T = S ⊔ (β.orthogonal S ⊓ T) := sup_inf_assoc_of_le _ hST
  rw [hc.sup_eq_top, top_inf_eq, inf_comm] at h1
  exact h1.symm

/-- The complementary part is disjoint from `S`. -/
theorem disjoint_inf_orthogonal (href : β.IsRefl) {S : Submodule ℂ E} (T : Submodule ℂ E)
    (hnd : (β.restrict S).Nondegenerate) : Disjoint S (T ⊓ β.orthogonal S) :=
  Disjoint.mono_right inf_le_right
    (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate href hnd).disjoint

/-- The dimension count for one Gram–Schmidt step: `dim S + dim L = dim T`. -/
theorem finrank_add_inf_orthogonal (href : β.IsRefl) {S T : Submodule ℂ E} (hST : S ≤ T)
    (hnd : (β.restrict S).Nondegenerate) :
    finrank ℂ S + finrank ℂ (T ⊓ β.orthogonal S : Submodule ℂ E) = finrank ℂ T := by
  have hsup := sup_inf_orthogonal_eq href hST hnd
  have hdis := disjoint_inf_orthogonal href T hnd
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (T ⊓ β.orthogonal S)
  rw [hsup, hdis.eq_bot, finrank_bot, add_zero] at h
  exact h.symm

end LayerLinearAlgebra

/-! ## §4  The graded-unitarity predicate (clauses (iii)–(vi) assembled) -/

section Graded

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **ABLR (2.30) on a single weight space**, bundled as a `SesqForm`.  This is the object clause
(vi) is about; `signedForm … p` applies ABLR's `σ`-twist to it, giving the Hermitian form (2.33) of
layer `p`. -/
def gradedSesq (B : InvariantForm W) (R : RealStructure W) (n : ℤ) : SesqForm (W.grading n) where
  toFun a b := sesqForm B R (a : 𝒱) (b : 𝒱)
  add_left a a' b := by
    change sesqForm B R ((a : 𝒱) + (a' : 𝒱)) (b : 𝒱) = _
    exact sesqForm_add_left B R _ _ _
  smul_left z a b := by
    change sesqForm B R (z • (a : 𝒱)) (b : 𝒱) = _
    exact sesqForm_smul_left B R _ _ _
  add_right a b b' := by
    change sesqForm B R (a : 𝒱) ((b : 𝒱) + (b' : 𝒱)) = _
    exact sesqForm_add_right B R _ _ _
  smul_right z a b := by
    change sesqForm B R (a : 𝒱) (z • (b : 𝒱)) = _
    exact sesqForm_smul_right B R _ _ _

@[simp] theorem gradedSesq_apply (B : InvariantForm W) (R : RealStructure W) (n : ℤ)
    (a b : W.grading n) : gradedSesq B R n a b = B.form (R.rho (a : 𝒱)) (b : 𝒱) := rfl

/-- `ρ` maps the subspace `S ≤ 𝒱ₙ` into itself.  (Together with `ρ² = s` and `s ≠ 0` this makes `ρ`
a bijection of `S`; see `orthogonal_gradedSesq_eq`.) -/
def RhoStableOn (R : RealStructure W) {n : ℤ} (S : Submodule ℂ (W.grading n)) : Prop :=
  ∀ x ∈ S, ∃ y ∈ S, (y : 𝒱) = R.rho (x : 𝒱)

/-- **THE FLAG GEOMETRY IS THE SAME FOR BOTH FORMS.**

On a `ρ`-stable subspace of a weight space with invertible parity, the orthogonal complement taken
with ABLR's *sesquilinear* form (2.30) is **literally the same submodule** as the one taken with
the ℂ-bilinear invariant form.

This is what makes the §0 encoding coherent rather than a fudge: the layer `L_p = G_p ∩ G_{p-1}^⊥` is
carved out below by the bilinear form (because that is what Mathlib's orthogonality API supports),
but it *is* ABLR's layer; only the positivity clause (vi) needed to move to the Hermitian form. -/
theorem orthogonal_gradedSesq_eq (B : InvariantForm W) (R : RealStructure W) {n : ℤ}
    {S : Submodule ℂ (W.grading n)} (hS : RhoStableOn R S) (hp : R.parity n ≠ 0) :
    (gradedSesq B R n).orthogonal S = (LiRadical.gradedForm B n).orthogonal S := by
  ext y
  simp only [SesqForm.mem_orthogonal, LinearMap.BilinForm.mem_orthogonal_iff,
    LinearMap.BilinForm.isOrtho_def, gradedSesq_apply, LiRadical.gradedForm_apply]
  constructor
  · intro hy x hx
    obtain ⟨z, hz, hzeq⟩ := hS x hx
    have h0 := hy z hz
    rw [hzeq, R.sq (x : 𝒱) x.2, map_smul, LinearMap.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hp
  · intro hy x hx
    obtain ⟨z, hz, hzeq⟩ := hS x hx
    rw [← hzeq]
    exact hy z hz

namespace GradedFlag

/-- **The layer `L_p`** of the flag at weight `n`: the part of `G_p 𝒱ₙ` orthogonal to
`G_{p-1} 𝒱ₙ`.  This is the summand appearing in clause (v) of ABLR Definition 2.2.

⚠ The orthogonal complement is the ℂ-bilinear one — which, on `ρ`-stable steps, *is* ABLR's
sesquilinear one (`orthogonal_gradedSesq_eq`). -/
def layer (F : GradedFlag W) (n : ℤ) (β : BilinForm ℂ (W.grading n)) (p : ℕ) :
    Submodule ℂ (W.grading n) :=
  F.pieceIn p n ⊓ β.orthogonal (F.pieceLT p n)

theorem layer_le_pieceIn (F : GradedFlag W) (n : ℤ) (β : BilinForm ℂ (W.grading n)) (p : ℕ) :
    F.layer n β p ≤ F.pieceIn p n := inf_le_left

/-- The bottom layer is the bottom step of the flag: nothing is quotiented out below `p = 0`. -/
theorem layer_zero (F : GradedFlag W) (n : ℤ) (β : BilinForm ℂ (W.grading n)) :
    F.layer n β 0 = F.pieceIn 0 n := by
  rw [layer, pieceLT_zero, LinearMap.BilinForm.orthogonal_bot, inf_top_eq]

end GradedFlag

/-- **Clause (iv) at weight `n`**: the form is nondegenerate on every step of the flag. -/
def LayerNondegenerate (F : GradedFlag W) (n : ℤ) (β : BilinForm ℂ (W.grading n)) : Prop :=
  ∀ p : ℕ, (β.restrict (F.pieceIn p n)).Nondegenerate

/-- **Clause (vi) at weight `n`**: on layer `p` the sign-corrected **Hermitian** form is positive
definite.

⚠⚠ Note the two forms, and that this is deliberate.  The layer `L_p` is cut out by the ℂ-bilinear
`β` (Mathlib's orthogonality API), while positivity is asserted for the sesquilinear `h` of clause
(iii) twisted by ABLR's `σ` (`signedForm`).  `orthogonal_gradedSesq_eq` proves the two notions of
"orthogonal complement" agree on `ρ`-stable steps, so this is one condition, not two.  Stating
positivity for `β` itself is the refuted encoding of §0. -/
def LayerPositive (F : GradedFlag W) (n : ℤ) (β : BilinForm ℂ (W.grading n))
    (h : SesqForm (W.grading n)) : Prop :=
  ∀ p : ℕ, IsPosOn (signedForm h p) (F.layer n β p)

/-- **Graded unitarity at weight `n`**, for a ℂ-bilinear form and a sesquilinear form on `𝒱ₙ`:
clauses (iv) and (vi) of ABLR Definition 2.2.  Clause (v) is *not* an assumption — see
`layerDecomposition`.

⚠ This is a *predicate*.  Nothing in this file asserts it of anything; downstream it holds at every
weight for `V^k(sl₂)`, `k < -2` real
(`AffineSl2BelowCritical.universal_gradedUnitary_belowCritical_unconditional`). -/
def GradedUnitaryAt (F : GradedFlag W) (n : ℤ) (β : BilinForm ℂ (W.grading n))
    (h : SesqForm (W.grading n)) : Prop :=
  LayerNondegenerate F n β ∧ LayerPositive F n β h

/-- **Graded unitarity** of a VOA with respect to an invariant form, an anti-linear `ρ` and a
graded flag: the weight-by-weight condition above, with clause (iv) for the level-`n` Gram form of
`B` and clause (vi) for ABLR's Hermitian form built from `B` and `ρ`.

⚠ `R` is part of the datum, exactly as in ABLR Definition 2.2 (clauses (i)–(iii)); it is a
parameter here so that a missing `ρ` is visible in every signature rather than silently absent.

⚠ A predicate.  Nothing in this file asserts it of anything.  The one VOA family for which the
library proves it is `V^k(sl₂)`, `k < -2` real, with the ordinary current-length flag:
`AffineSl2BelowCritical.universal_gradedUnitary_belowCritical_unconditional`
(`Examples/AffineSl2BelowCriticalAnchor.lean`). -/
def GradedUnitary (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W) : Prop :=
  ∀ n : ℤ, GradedUnitaryAt F n (LiRadical.gradedForm B n) (gradedSesq B R n)

/-- The diagonal of ABLR's sesquilinear form (2.30), on a `ρ`-fixed set, is the diagonal of the
ℂ-bilinear form.  This is what lets the repository's *bilinear* Gram computations be read as
values of the Hermitian form of clause (vi) — on real vectors, which is where the Virasoro creation
monomials live. -/
theorem sesq_diag_eq_gradedForm (B : InvariantForm W) (R : RealStructure W) {S : Set 𝒱}
    (hfix : R.Fixes S) {n : ℤ} (x : W.grading n) (hx : (x : 𝒱) ∈ S) :
    sesqForm B R x x = LiRadical.gradedForm B n x x :=
  sesqForm_eq_form_of_fixes B R hfix hx _

end Graded

/-! ## §5  The reduction: clause (v) is a consequence of clause (iv) -/

section Reduction

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable (F : GradedFlag W) {n : ℤ} {β : BilinForm ℂ (W.grading n)}

/-- Nondegeneracy on the *previous* step, extracted from `LayerNondegenerate` (with the `p = 0`
case discharged by `nondegenerate_restrict_bot`). -/
theorem nondegenerate_pieceLT [FiniteDimensional ℂ (W.grading n)]
    (hnd : LayerNondegenerate F n β) (p : ℕ) : (β.restrict (F.pieceLT p n)).Nondegenerate := by
  cases p with
  | zero => rw [GradedFlag.pieceLT_zero]; exact nondegenerate_restrict_bot β
  | succ q => rw [GradedFlag.pieceLT_succ]; exact hnd q

/-- **THE GRAM–SCHMIDT CLAUSE IS A THEOREM, NOT A HYPOTHESIS.**

`G_p 𝒱ₙ = G_{p-1} 𝒱ₙ ⊕ L_p`, where `L_p = G_p ∩ (G_{p-1})^⊥`, whenever the form is reflexive and
nondegenerate on each step of the flag.  This is clause (v) of ABLR Definition 2.2 *derived from*
clause (iv).

⚠ It is **not** a proof that the form is nondegenerate on the steps, and it says nothing whatever
about positivity. -/
theorem layerDecomposition [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) (p : ℕ) :
    F.pieceLT p n ⊔ F.layer n β p = F.pieceIn p n ∧
      Disjoint (F.pieceLT p n) (F.layer n β p) :=
  ⟨sup_inf_orthogonal_eq href (F.pieceLT_le_pieceIn p n) (nondegenerate_pieceLT F hnd p),
    disjoint_inf_orthogonal href _ (nondegenerate_pieceLT F hnd p)⟩

/-- **The layer dimensions.**  `dim G_{p-1} 𝒱ₙ + dim L_p = dim G_p 𝒱ₙ`.

Combined with a *cited* refined character (`Examples.AdmissiblePartitions.AdmissibleBasisHyp`,
Salazar arXiv:2405.07126) this is what turns the layer statement into the alternating-sum
signature statement.  On its own it is unconditional and character-free. -/
theorem finrank_pieceLT_add_layer [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) (p : ℕ) :
    finrank ℂ (F.pieceLT p n) + finrank ℂ (F.layer n β p) = finrank ℂ (F.pieceIn p n) :=
  finrank_add_inf_orthogonal href (F.pieceLT_le_pieceIn p n) (nondegenerate_pieceLT F hnd p)

/-- Each step of the flag is contained in the span of the layers up to it. -/
theorem pieceIn_le_iSup_layer [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) (p : ℕ) :
    F.pieceIn p n ≤ ⨆ r : ℕ, F.layer n β r := by
  induction p with
  | zero =>
      have h := (layerDecomposition F href hnd 0).1
      rw [GradedFlag.pieceLT_zero, bot_sup_eq] at h
      exact h ▸ le_iSup (fun r : ℕ => F.layer n β r) 0
  | succ q ih =>
      have h := (layerDecomposition F href hnd (q + 1)).1
      rw [GradedFlag.pieceLT_succ] at h
      rw [← h]
      exact sup_le ih (le_iSup (fun r : ℕ => F.layer n β r) (q + 1))

/-- **The orthogonal decomposition of the whole weight space** (clause (v), globally): the
layers span `𝒱ₙ`. -/
theorem iSup_layer_eq_top [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) : (⨆ p : ℕ, F.layer n β p) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← F.iSup_pieceIn n]
  exact iSup_le fun p => pieceIn_le_iSup_layer F href hnd p

/-- **The positivity clause is not vacuous.**  Under clause (iv), on a nonzero weight space at
least one layer is nonzero — so `LayerPositive` really does constrain the form, rather than being
satisfied by default via `isPosOn_bot`. -/
theorem exists_layer_ne_bot [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) (hne : (⊤ : Submodule ℂ (W.grading n)) ≠ ⊥) :
    ∃ p : ℕ, F.layer n β p ≠ ⊥ := by
  by_contra hall
  have hbot : ∀ p : ℕ, F.layer n β p = ⊥ := fun p => by
    by_contra hp
    exact hall ⟨p, hp⟩
  refine hne ?_
  rw [← iSup_layer_eq_top F href hnd]
  simp [hbot]

end Reduction

/-! ## §6  The sign calibrated at the vacuum

At weight `0` the bottom layer is the vacuum line, whatever the flag and whatever the form.  The
value of clause (vi) there is therefore forced, and it is a number this repository has already
fixed by its textbook normalisation `(𝟙|𝟙) = +1`.  This makes the exponent `p` checkable rather
than asserted: both the signed and untwisted forms have value `+1` at `p = 0`. -/

section Vacuum

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The vacuum, as a vector of the weight-zero space. -/
def vacuumIn (W : VertexOperatorAlgebra 𝒱) : W.grading 0 := ⟨W.vacuum, W.vacuum_mem⟩

@[simp] theorem coe_vacuumIn : ((vacuumIn W : W.grading 0) : 𝒱) = W.vacuum := rfl

/-- The vacuum lies in the bottom layer at weight `0` — for **every** graded flag and **every**
bilinear form, since `G_{-1} = 0` and `G_0 𝒱₀ = ℂ𝟙` are flag axioms. -/
theorem vacuumIn_mem_layer_zero (F : GradedFlag W) (β : BilinForm ℂ (W.grading 0)) :
    vacuumIn W ∈ F.layer 0 β 0 := by
  rw [GradedFlag.layer_zero]
  change (W.vacuum : 𝒱) ∈ F.piece 0 0
  rw [F.vacuum_zero]
  exact Submodule.mem_span_singleton_self _

/-- **THE CALIBRATION.**  With the textbook normalisation `(𝟙|𝟙) = +1`, the
clause-(vi) value on the vacuum layer is

  `(-1)^0 · (ρ𝟙 | 𝟙) = (𝟙|𝟙) = +1`,

a positive real — exactly what clause (vi) demands. -/
theorem signedForm_gradedSesq_vacuum (B : InvariantForm W) (R : RealStructure W)
    (hn : B.Normalized) :
    signedForm (gradedSesq B R 0) 0 (vacuumIn W) (vacuumIn W) = 1 := by
  rw [signedForm_apply, gradedSesq_apply, coe_vacuumIn, R.map_vacuum, hn.vacuum_self]
  norm_num

/-- The vacuum is a nonzero vector of `𝒱₀` whenever it is a nonzero vector of `𝒱`. -/
theorem vacuumIn_ne_zero (hvac : W.vacuum ≠ 0) : vacuumIn W ≠ 0 :=
  fun h => hvac (by simpa using congrArg Subtype.val h)

/-- The bottom layer at weight `0` is **nonzero** (for every flag and every form), because it
contains the vacuum.  This is the submodule the refuted encoding forced to be `⊥`. -/
theorem layer_zero_ne_bot (F : GradedFlag W) (β : BilinForm ℂ (W.grading 0))
    (hvac : W.vacuum ≠ 0) : F.layer 0 β 0 ≠ ⊥ := by
  intro h
  exact vacuumIn_ne_zero hvac
    ((Submodule.mem_bot ℂ).1 (h ▸ vacuumIn_mem_layer_zero F β))

/-- **CLAUSE (vi) HOLDS ON THE VACUUM LAYER — a nonzero layer of a genuine VOA.**

This is the sharpest available check that the fixed clause is not refutable.  At weight `0` the
bottom layer is `𝒱₀ = ℂ𝟙` (a flag axiom, for every flag and every form), which is nonzero whenever
`𝟙 ≠ 0`; and on it the sign-corrected Hermitian form takes the value `|z|² > 0` at `z𝟙`, using
only `ρ𝟙 = 𝟙` and `(𝟙|𝟙) = +1`.

Compare `eq_bot_of_bilinear_pos`: under the refuted bilinear encoding this statement was **false**
— not merely unproved — for every VOA with `𝟙 ≠ 0`.

⚠⚠ **THIS IS NOT PROGRESS TOWARDS GRADED UNITARITY.**  It is one layer at one weight, forced by
the normalisation; it says nothing about any other weight, about clause (iv), or about any
particular VOA.  Kaufmann's conjecture is untouched. -/
theorem isPosOn_layer_zero_vacuum (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (β : BilinForm ℂ (W.grading 0)) (hn : B.Normalized) :
    IsPosOn (signedForm (gradedSesq B R 0) 0) (F.layer 0 β 0) := by
  intro x hx hne
  rw [GradedFlag.layer_zero] at hx
  have hx' : (x : 𝒱) ∈ F.piece 0 0 := hx
  rw [F.vacuum_zero, Submodule.mem_span_singleton] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hzne : z ≠ 0 := by
    intro h0
    exact hne (Subtype.ext (by rw [← hz, h0, zero_smul]; simp))
  refine ⟨Complex.normSq z, Complex.normSq_pos.2 hzne, ?_⟩
  rw [signedForm_apply, gradedSesq_apply, ← hz, R.antilinear, R.map_vacuum]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hn.vacuum_self]
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- **The untwisted vacuum value is positive.**  At filtration degree `0` the textbook twist
is the identity, so the raw sesquilinear form must already be positive on the vacuum.  This is the
direct untwisted calibration complementary to `signedForm_gradedSesq_vacuum`. -/
theorem pos_gradedSesq_vacuum (B : InvariantForm W) (R : RealStructure W)
    (hn : B.Normalized) :
    ∃ r : ℝ, 0 < r ∧ gradedSesq B R 0 (vacuumIn W) (vacuumIn W) = (r : ℂ) := by
  refine ⟨1, by norm_num, ?_⟩
  rw [gradedSesq_apply, coe_vacuumIn, R.map_vacuum, hn.vacuum_self]
  norm_num

/-- **The sesquilinear clause at the point where the bilinear one fails.**

`eq_bot_of_bilinear_pos` says that under the ℂ-bilinear encoding of clause (vi), any subspace
satisfying the clause is `⊥`.  Here is a subspace — the bottom layer at weight `0`, present in
*every* graded flag on *every* VOA with `𝟙 ≠ 0` — which is **not** `⊥` and **does** satisfy the
sesquilinear clause.

So the refutation is not merely blocked syntactically: its conclusion is false for the
sesquilinear clause, on this very submodule.

⚠ This is a statement about the *clause*, at one weight.  It is not graded unitarity, and it is
not evidence for or against Kaufmann's conjecture. -/
theorem layer_zero_ne_bot_and_isPosOn (B : InvariantForm W) (R : RealStructure W)
    (F : GradedFlag W) (β : BilinForm ℂ (W.grading 0)) (hn : B.Normalized)
    (hvac : W.vacuum ≠ 0) :
    F.layer 0 β 0 ≠ ⊥ ∧ IsPosOn (signedForm (gradedSesq B R 0) 0) (F.layer 0 β 0) :=
  ⟨layer_zero_ne_bot F β hvac, isPosOn_layer_zero_vacuum B R F β hn⟩

end Vacuum

end VOA
