/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AdmissiblePartitions
import VOA.Core.GradedUnitarity
import VOA.Core.FlagMinors

/-!
# Graded unitarity of `L(c,0)`: **the statement, and the reduction**

⚠⚠ **Nothing in this file is a proof of graded unitarity, and nothing in this repository is.**
(The repository does prove the truncation *through filtration degree two* for the boundary models:
`boundary_gradedUnitaryThroughTwo`, `VirasoroLengthTwoLayerPositive.lean`.)
The target — that the boundary Virasoro minimal models `L(c_{2,2n+1},0)` are graded unitary — is a
research problem that has been **open since 1994** (R. M. Kaufmann, hep-th/9405041, §4.2, Main
conjecture; Kaufmann himself checked only `n = 2, 3`).  There is no proof of sufficiency in the
literature to transcribe.  Beem–Garner arXiv:2509.10364 (September 2025), by an ABLR co-author,
records that ABLR studied the constraints "albeit without confirming the existence of the full
graded-unitary structure".

What this file contains is exactly two things, and each declaration says which it is:

* **(a) the formalized STATEMENT** — `VirGradedUnitary`, the graded-unitarity datum of
  Arabi Ardehali–Beem–Lemos–Rastelli arXiv:2507.23781v2 Definition 2.2 instantiated at `L(c,0)`
  with the length filtration of ABLR eq. (3.11) = Kaufmann `Ṽ_{n,k}`;
* **(b) the formalized REDUCTION** — theorems turning that statement into conditions on the
  **leading principal minors** of a Gram matrix the repository already builds.

There is a third category recorded only in prose, never in a Lean statement:

* **(c) numerical evidence**, *not* re-derived in this file.  A from-scratch,
  exact-rational check of the alternating-sum consequence
  `sig(M_N) = Σ_r (-1)^r a_{N,r}` far beyond Kaufmann's `n = 2, 3` — roughly 700 `(n, N)` pairs by
  three independent routes, with **zero mismatches**.  That is *consistency*, not proof: one
  mismatch would have refuted the programme, and none appeared.  Nothing in Lean below depends on
  it, and no Lean statement asserts it.

## What the reduction delivers, phrased so it cannot be misread

> **Graded unitarity of `L(c,0)` with respect to the length flag HOLDS IF AND ONLY IF the leading
> principal minors of `canGram` satisfy the alternating pivot law.**

Not: that they do.  Every docstring below says "reduction", never "criterion satisfied".

## The two halves, and their status

* **Clause (iv), nondegeneracy on every step** — fully reduced to minors, unconditionally in the
  abstract (`Core.FlagMinors.nondegenerate_flag_iff_minors`) and here at `L(c,0)` given a flag
  basis.  `layerNondegenerate_iff_minors`.
* **Clause (v), the Gram–Schmidt decomposition** — **not an assumption at all**: it is a
  *theorem*, derived from clause (iv).  `virLayerDecomposition`, `virFinrank_layer`.  This is the
  part of ABLR Definition 2.2 that the formalization removes.
* **Clause (vi), positivity of the layers** — stated for the **Hermitian** form of ABLR clause
  (iii), `Core.GradedUnitarity.gradedSesq`, twisted by `signedForm`.  This file does not reduce
  it to minors.  The linear-algebra input for that reduction (converse Sylvester criterion
  `posDef_of_det_leadingPrincipal_pos`, Jacobi quotient identity, and the layer lemma
  `schurOfLeading_posDef_of_sign_ratios`) is in `Core.MinorPivots`.

## ⚠⚠ Remark: the positivity clause must be sesquilinear

Asserting positivity of the ℂ-**bilinear** canonical form
on the ℂ-**submodule** `L_p` is refutable — `i·x` flips the sign of a bilinear diagonal —
so a `VirGradedUnitary c` stated that way is **provably false** for every `c`, although the
conjecture is open.  The refutation is a theorem,
`Core.GradedUnitarity.eq_bot_of_bilinear_pos`, kept so the encoding cannot recur; positivity is
stated for the sesquilinear form of clause (iii); and the real structure `ρ` is a **parameter** of
`VirGradedUnitary`, so its absence is visible in every signature.  See `Core.GradedUnitarity` §0.

## ⚠ The sign

This repository uses the textbook normalisation `(𝟙|𝟙) = +1`, so `canGram` has the textbook
global sign.  ABLR eq. (3.16) / Kaufmann eq. (4.4) read
`sign⟨O|O⟩ = (-1)^{R_O}`, which is the exponent carried by
`Core.GradedUnitarity.signedForm`.  Calibration, reproduced by hand against this repository's own
mode identities: at `c = -22/5`, level `6`, in the words `L₋₆|0⟩` and `L₋₄L₋₂|0⟩` the Gram is
`[[-77,-22],[-22,66/5]]`, with pivots `-77` and `682/35`.

## Status
* Definitions and reductions, `sorry`-free, no new axioms.
* **The sesquilinear clause (iii) is in force.**  Clause (vi) is stated for ABLR's Hermitian form
  `gradedSesq (Bsimp c) R`, not for the bilinear form.
* Not proved: **`VirGradedUnitary c R` is never inhabited** in the repository, for any `c` and any `R`.
* Partial positivity is proved: the vacuum layer here (`isPosOn_layer_zero_vacuum_simple`) and,
  for the boundary models, graded unitarity through filtration degree two
  (`boundary_gradedUnitaryThroughTwo`, `VirasoroLengthTwoLayerPositive.lean`).
* Real structures on `L(c,0)` are constructed: `VirasoroRealStructure.lean` (given a real
  Feigin–Fuchs parameter) and `boundaryVirasoroRealStructure` (`VirasoroBoundaryRealStructure.lean`).
  `R` remains a parameter of `VirGradedUnitary`, as in ABLR clauses (i)–(iii).
* Not proved: **`AdmissiblePartitions.FlagBasisHyp` is a hypothesis, never discharged.**  It is the open
  Andrews–Gordon/Salazar half and it appears in the signature of every minor-form statement.

## References
* Arabi Ardehali, Beem, Lemos, Rastelli, arXiv:2507.23781v2 = JHEP 06 (2026) 075, Def. 2.2, eqs.
  (2.30), (3.11), (3.16).
* R. M. Kaufmann, hep-th/9405041, §4.2, eq. (4.4).
* J. Salazar, arXiv:2405.07126, Remark 5.3.
-/

namespace VOA

namespace VirGradedUnitarity

open VOA.VirModule VOA.VirSimple VOA.VirQuotForm
open VOA.VirGoodFil VOA.AdmissiblePartitions VOA.VirGram4
open VOA.VertexOperatorAlgebra
open Module (finrank)

variable (c : ℂ)

/-! ## §1  (a) The STATEMENT -/

/-- **(a) THE STATEMENT.**  Graded unitarity of `L(c,0)` with respect to its canonical invariant
form and the length filtration of ABLR eq. (3.11) = Kaufmann `Ṽ_{n,k}`.

⚠ This is a `Prop`.  **No theorem in this repository asserts it of any `c`**, and the sufficiency
direction is open (Kaufmann 1994).  Its two clauses are nondegeneracy of the form on every step of
the flag, and positivity of the sign-corrected form on every layer.

⚠⚠ **The positivity clause is the sesquilinear one.**  Positivity of the ℂ-**bilinear**
canonical form on the ℂ-**submodule** `L_p` is
refutable (`Core.GradedUnitarity.eq_bot_of_bilinear_pos`), so a definition using it would be
provably false for every `c`.  Clause (vi) is stated for ABLR's Hermitian form
`gradedSesq (Bsimp c) R` — eq. (2.30) twisted by `σ` as in eq. (2.33) — exactly as ABLR write it.
Clauses (iv) and (v) remain ℂ-bilinear, which is *not* a fudge:
`Core.GradedUnitarity.orthogonal_gradedSesq_eq` proves the two orthogonal complements agree on
`ρ`-stable steps, so `L_p` is ABLR's layer either way.

⚠ **`R` REMAINS PART OF THE DATUM.**  This general definition accepts an arbitrary real
structure, as required by ABLR clauses (i)–(iii).  The partition-basis construction in
`VirasoroRealStructure` supplies one when a real Feigin--Fuchs parameter is chosen, and
`VirasoroBoundaryRealStructure` specializes it canonically to every boundary model.  On the
`ρ`-fixed real span of the creation monomials the Hermitian form agrees with the bilinear one
(`Core.GradedUnitarity.sesq_diag_eq_gradedForm`), which is why the repository's bilinear Gram
matrices compute the numbers clause (vi) is about.

The reduction below is **insensitive** to the choice of `ρ`: it is a chain of equivalences about
clause (iv), which does not mention it. -/
def VirGradedUnitary (R : RealStructure (virasoroSimple c)) : Prop :=
  GradedUnitary (Bsimp c) R (virGradedFlag c)

/-- Unfolding of the statement, weight by weight. -/
theorem virGradedUnitary_iff (R : RealStructure (virasoroSimple c)) :
    VirGradedUnitary c R ↔ ∀ n : ℤ,
      LayerNondegenerate (virGradedFlag c) n (LiRadical.gradedForm (Bsimp c) n) ∧
        LayerPositive (virGradedFlag c) n (LiRadical.gradedForm (Bsimp c) n)
          (gradedSesq (Bsimp c) R n) :=
  Iff.rfl

/-- **THE CLAUSE IS NOT VACUOUS AT `L(c,0)`, AND THE SIGN IS RIGHT.**  Whatever `ρ` turns out to
be, at weight `0` the bottom layer is the vacuum line and the clause-(vi) value is forced by the
textbook normalisation to be `(-1)^0·(𝟙|𝟙) = +1`: positive, as clause (vi) demands.  Thus the
exponent carried by `signedForm` is calibrated, not chosen. -/
theorem signedForm_gradedSesq_vacuum_simple (R : RealStructure (virasoroSimple c)) :
    signedForm (gradedSesq (Bsimp c) R 0) 0 (vacuumIn (virasoroSimple c))
        (vacuumIn (virasoroSimple c)) = 1 :=
  VOA.signedForm_gradedSesq_vacuum (Bsimp c) R (Bsimp_normalized c)

/-- **The weight-`0` slice of clause (vi) at `L(c,0)` is a THEOREM.**  The bottom layer at weight
`0` is the vacuum line `ℂ𝟙`, and the sign-corrected Hermitian form is positive definite on it for
every `c` and every `ρ`.

⚠⚠ **This is not progress towards the Kaufmann conjecture.**  One layer at one weight, forced by
`(𝟙|𝟙) = +1` and `ρ𝟙 = 𝟙`; it says nothing about clause (iv), nothing about weight `N > 0`, and
nothing about `c = c_{2,2n+1}`.  Its only job is to certify that the fixed clause (vi) is
satisfiable on a *nonzero* layer of an actual VOA — which, under the refuted ℂ-bilinear encoding,
it provably is not. -/
theorem isPosOn_layer_zero_vacuum_simple (R : RealStructure (virasoroSimple c)) :
    IsPosOn (signedForm (gradedSesq (Bsimp c) R 0) 0)
      ((virGradedFlag c).layer 0 (LiRadical.gradedForm (Bsimp c) 0) 0) :=
  VOA.isPosOn_layer_zero_vacuum (Bsimp c) R (virGradedFlag c) _ (Bsimp_normalized c)

/-! ## §2  (b) The REDUCTION, part 1: clause (v) is a **theorem**

⚠ Everything in this section is conditional on clause (iv) — nondegeneracy on the steps — which is
*not* proved anywhere.  What is proved is that clause (iv) already forces clause (v). -/

section Reduction

variable {c} {n : ℤ}

/-- **CLAUSE (v) IS NOT AN ASSUMPTION.**  At `L(c,0)`, nondegeneracy of the canonical form on
each step of the length flag *forces* the Gram–Schmidt decomposition
`G_p 𝒱ₙ = G_{p-1} 𝒱ₙ ⊕ L_p` of ABLR Definition 2.2(v).

The reflexivity hypothesis that Mathlib's orthogonality API needs is supplied by
`VirQuotForm.gradedForm_Bsimp_isRefl`, i.e. ultimately by `VirFormSym.canB_isSymmetric` — a
theorem this repository proves outright.

⚠ This is **not** a proof that the form is nondegenerate on the steps, and it says nothing
whatever about positivity. -/
theorem virLayerDecomposition
    (hnd : LayerNondegenerate (virGradedFlag c) n (LiRadical.gradedForm (Bsimp c) n)) (p : ℕ) :
    (virGradedFlag c).pieceLT p n
        ⊔ (virGradedFlag c).layer n (LiRadical.gradedForm (Bsimp c) n) p
        = (virGradedFlag c).pieceIn p n ∧
      Disjoint ((virGradedFlag c).pieceLT p n)
        ((virGradedFlag c).layer n (LiRadical.gradedForm (Bsimp c) n) p) := by
  haveI := (virasoroSimple c).finrank n
  exact layerDecomposition _ (gradedForm_Bsimp_isRefl c n) hnd p

/-- The layer dimensions add up: `dim G_{p-1} + dim L_p = dim G_p`.

Combined with the **cited** refined character (`AdmissiblePartitions.AdmissibleBasisHyp`, Salazar
arXiv:2405.07126) this is what turns the layer statement into the alternating-sum signature
statement.  On its own it is unconditional in the character and needs only clause (iv). -/
theorem virFinrank_layer
    (hnd : LayerNondegenerate (virGradedFlag c) n (LiRadical.gradedForm (Bsimp c) n)) (p : ℕ) :
    finrank ℂ ((virGradedFlag c).pieceLT p n)
        + finrank ℂ ((virGradedFlag c).layer n (LiRadical.gradedForm (Bsimp c) n) p)
      = finrank ℂ ((virGradedFlag c).pieceIn p n) := by
  haveI := (virasoroSimple c).finrank n
  exact finrank_pieceLT_add_layer _ (gradedForm_Bsimp_isRefl c n) hnd p

/-- The layers span the whole weight space — clause (v) globally. -/
theorem virISup_layer_eq_top
    (hnd : LayerNondegenerate (virGradedFlag c) n (LiRadical.gradedForm (Bsimp c) n)) :
    (⨆ p : ℕ, (virGradedFlag c).layer n (LiRadical.gradedForm (Bsimp c) n) p) = ⊤ := by
  haveI := (virasoroSimple c).finrank n
  exact iSup_layer_eq_top _ (gradedForm_Bsimp_isRefl c n) hnd

end Reduction

/-! ## §3  (b) The REDUCTION, part 2: clause (iv) as **leading principal minors** -/

section Minors

open VOA.FlagMinors

variable {c} {N m : ℕ}
    (e : Module.Basis (Fin m) ℂ ((virasoroSimple c).grading (N : ℤ)))

/-- **THE MINOR FORM OF CLAUSE (iv).**

Given an ordered basis of `L(c,0)_N` whose initial segments are the steps of the length flag — i.e.
given `AdmissiblePartitions.FlagBasisHyp`, packaged as `FlagMinors.RefinesBasis` — nondegeneracy of
the canonical form on **every step** is *exactly* the statement that **every leading principal
minor** of the level-`N` Gram matrix is nonzero.

⚠ Three things this does **not** say.  (1) It does not say the minors are nonzero.  (2) It says
nothing about their **signs**, which is the positivity clause (vi) and is *not* reducible to minors
with what Mathlib currently has — see `Core.FlagMinors`.  (3) The refining basis is a **hypothesis**
(the open Andrews–Gordon/Salazar half), not something proved here: `VirGoodFil.goodFil` is defined
as an image precisely so that no basis of the simple quotient is ever assumed by accident. -/
theorem layerNondegenerate_iff_minors
    (hrb : RefinesBasis (fun p => (virGradedFlag c).pieceIn p (N : ℤ)) e) :
    LayerNondegenerate (virGradedFlag c) (N : ℤ) (LiRadical.gradedForm (Bsimp c) (N : ℤ))
      ↔ ∀ p : ℕ, (leadingPrincipal
          (LinearMap.BilinForm.toMatrix e (LiRadical.gradedForm (Bsimp c) (N : ℤ)))
          (hrb.dim_le p)).det ≠ 0 :=
  nondegenerate_flag_iff_minors hrb _

/-- **One matrix for two algebras.**  If the chosen basis of `L(c,0)_N` consists of images of
creation monomials — which is what a flag basis coming from admissible partitions *is* — then the
Gram matrix appearing in `layerNondegenerate_iff_minors` has entries
`(canB c) (L₋λ|0⟩, L₋μ|0⟩)`: it is a submatrix of `GramMat.canGram` of the **universal** module
`V(c,0)`, which `Examples.VirasoroGram4` and `Examples.VirasoroGram56` already compute.

No form on the quotient ever has to be evaluated directly.  This is `VirQuotForm.canB_quot_mkQ`. -/
theorem toMatrix_eq_canB_of_monomials (w : Fin m → List ℕ)
    (hw : ∀ i, (e i : VirUniv c ⧸ maxIdealVir c)
      = (maxIdealVir c).mkQ (negWordVir c (w i))) (i j : Fin m) :
    LinearMap.BilinForm.toMatrix e (LiRadical.gradedForm (Bsimp c) (N : ℤ)) i j
      = (canB c).form (negWordVir c (w i)) (negWordVir c (w j)) := by
  rw [LinearMap.BilinForm.toMatrix_apply]
  show (Bsimp c).form (e i : VirUniv c ⧸ maxIdealVir c) (e j : VirUniv c ⧸ maxIdealVir c) = _
  rw [hw i, hw j, canB_quot_mkQ]

end Minors

/-! ## §4  The assembled reduction

The landing statement, with every hypothesis visible. -/

/-- **THE REDUCTION, ASSEMBLED, AT ONE WEIGHT.**

Given a flag basis of `L(c,0)_N` (the cited Andrews–Gordon/Salazar half), the graded-unitarity
datum at weight `N` splits into

* a purely **determinantal** condition — all leading principal minors of the level-`N` Gram matrix
  are nonzero — which is clause (iv); and
* the **positivity** condition on the layers for the **Hermitian** form `h` of clause (iii),
  which is clause (vi),

and clause (v) is then automatic (`virLayerDecomposition`).

⚠⚠ **This is an equivalence, not an assertion.**  This repository does not prove that either side
holds for any `c`.  Establishing the right-hand side for `c = c_{2,2n+1}` and all `N` *is* the
Kaufmann conjecture, open since 1994; the only evidence carried anywhere here is the numerical
consistency check recorded in the file docstring, and consistency is
not proof. -/
theorem gradedUnitaryAt_iff_minors_and_positive {c : ℂ} {N m : ℕ}
    (e : Module.Basis (Fin m) ℂ ((virasoroSimple c).grading (N : ℤ)))
    (hrb : FlagMinors.RefinesBasis (fun p => (virGradedFlag c).pieceIn p (N : ℤ)) e)
    (h : SesqForm ((virasoroSimple c).grading (N : ℤ))) :
    GradedUnitaryAt (virGradedFlag c) (N : ℤ) (LiRadical.gradedForm (Bsimp c) (N : ℤ)) h
      ↔ (∀ p : ℕ, (FlagMinors.leadingPrincipal
            (LinearMap.BilinForm.toMatrix e (LiRadical.gradedForm (Bsimp c) (N : ℤ)))
            (hrb.dim_le p)).det ≠ 0) ∧
        LayerPositive (virGradedFlag c) (N : ℤ) (LiRadical.gradedForm (Bsimp c) (N : ℤ)) h :=
  and_congr_left' (layerNondegenerate_iff_minors e hrb)

end VirGradedUnitarity

end VOA
