/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.ReconstructionExistence
import VOA.Core.LocalSystem
import VOA.Foundations.Parity
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Defining a vertex algebra by strong generators and singular OPEs

Every concrete vertex algebra in this library was built by a bespoke realization — an
eleven-file symplectic-fermion chain, a lattice-plus-screenings construction, a Heisenberg
Fock model.  The theory that removes the need for such realizations is De Sole–Kac,
*Freely generated vertex algebras and non-linear Lie conformal algebras*,
Comm. Math. Phys. **254** (2005) 659–694 (arXiv:math-ph/0312042): one specifies a set of
**strong generators** with conformal weights, parities, and their **singular OPE**, and the
vertex algebra is the universal enveloping object `U(R) = T(R)/M(R)`.

This file builds that input datum and the algebra `U(R)` on which the vertex algebra is to
live, together with everything on the path from `U(R)` to `Core.ReconstructionExistence.reconstruct`
that does **not** depend on the hard analytic step.

## The formalism

* **Definition 3.1** — a *non-linear conformal superalgebra* is a `ℂ[T]`-module `R = ⨁_Δ R[Δ]`
  with a λ-bracket `R ⊗ R → ℂ[λ] ⊗ T(R)`, where `T(R)` is the **tensor algebra**, not `R`.  That
  codomain is the whole point: the singular OPE of two generators contains normally ordered
  *products* of generators.  The axioms are sesquilinearity and the grading condition
  `Δ([a_λ b]) < Δa + Δb`.
* **Lemma 3.2** — the normally ordered product `N` and the bracket `L_λ` extend uniquely from `R`
  to all of `T(R)`, by simultaneous recursion on `Δ(A) + Δ(B)`.
* **Definition 3.4** — `M(R) = span_ℂ { A ⊗ ((b⊗c - p(b,c)·c⊗b) ⊗ D - N(∫₋ᵀ⁰[b_λ c]dλ, D)) }`
  over `b,c ∈ R` and `A,D ∈ T(R)`.  Since `A` is arbitrary, this is a **left** ideal of the
  associative algebra `T(R)`; it is not a right ideal, so `T(R)/M(R)` is a quotient of vector
  spaces and **not** an algebra.
* **Theorem 3.9** — `U(R) := T(R)/M(R)` carries a vertex algebra structure, and the ordered
  monomials are a basis (PBW).  PBW is *deliberately out of scope here.*

## Main results

* `OPEData` — **Definition 3.1 as a Lean structure**, in the form a physicist writes it: a set
  of strong generators, a weight and a parity for each, and a table of singular-OPE coefficients
  `ope i j n = aⁱ₍ₙ₎aʲ ∈ T(R)`.  Nothing else is asked.  Sesquilinearity is *derived* (`brk`,
  `brk_left`, `brk_right`), not imposed, and the OPE terminates by itself (`brk_vanish`).
* `virasoroOPE` — the Virasoro algebra at central charge `c` as a **machine-checked** term of
  `OPEData Unit`: the worked example of the interface, with the grading condition *proved*.
* `Ttr` — the translation operator on `T(R)`: the unique derivation extending `T` on `R`
  (`Ttr_mul`, `Ttr_gv`), built by the dual-numbers trick.
* `brk` — the λ-bracket extended from the bottom generators to all divided powers, with
  `brk_left`, `brk_right` its two sesquilinearity identities and `brk_mem_filt` the full grading
  condition `Δ(p₍ₙ₎q) ≤ Δp + Δq - n - 1`, so `brk` really is a Definition 3.1 λ-bracket.
* `Ttr_mem_filt`, `filt_exhaustive` — the conformal-weight filtration of `T(R)` is load-bearing:
  `T` shifts it by one, and it exhausts `T(R)` (the two hypotheses `isField_of_filt` consumes).
* `rel`, `Ttr_rel` — the quantum-commutator relation, and `T(rel(a,b)) = rel(Ta,b) + rel(a,Tb)`.
* `MIdeal`, `MRbot`, `MRbot_le` — admissible relation ideals; the smallest one, explicitly the
  `D = 1` slice of Definition 3.4; and its minimality.
* `UR`, `vacU`, `TrU`, `leftMulU`, `wstU_span` — the quotient `T(R)/M` with its vacuum, its
  translation operator, the descended left multiplications, and the spanning of the word states
  (`reconstruct`'s `hspan`, for free — no PBW, no independence).
* `dpow`, `creHalf`, `creHalf_cov_nonneg` — the **creation half of every generating field,
  constructed**: for `j ≥ 0` the mode `a₍₋ⱼ₋₁₎` is left multiplication by `Tʲa/j!`, and it is
  `T`-covariant throughout that range.
* `vacU_ne_zero_bot`, `UR_nontrivial_bot` — **`T(R)/MRbot ≠ 0`**, via an augmentation.  No PBW.
* `isField_of_filt`, `local_of_ope` — the two bridges turning weight bookkeeping and a
  mode-commutator formula into `IsField` and `Local`, for an arbitrary complex vector space.
* `reconstruct_of_generators` — `reconstruct` reduced to five properties of the *generating*
  fields, with pairwise locality of all word fields supplied by
  `Core.LocalSystem.generated_local`.  (That machinery had been proved and left unused in this
  library; this is its first application.)
* `GenFields`, `UR_YA` — the contract the remaining hard step must deliver, and the vertex
  operator map on `T(R)/M` that follows from it — VA3 creation, VA4 locality, VA5 regularity and
  translation covariance — with **no PBW and no basis**.

## Status

Delivered: the data structure with a checked Virasoro instance; `T(R)`, the translation
derivation, the sesquilinear λ-bracket, the relations and their `T`-stability; the quotient
`T(R)/M` with vacuum, translation, spanning and non-vacuity; the whole creation half of the
generating fields; and the reduction of `reconstruct` to properties of the generating fields.

**Not delivered, precisely.**

1. **De Sole–Kac Lemma 3.2 is not formalized** — the simultaneous recursion defining `N` and
   `L_λ` on all of `T(R)`.  Consequently:
2. **`M(R)` itself is not constructed *here*.**  Only its `D = 1` slice `MRbot` is
   (`N(X,1) = X` makes those generators explicit).  `MRbot ⊆ M(R)`, and the inclusion is
   **strict**: the `D ≠ 1` generators permit commuting two adjacent letters *in the middle* of a
   monomial, which the `D = 1` ones do not imply.
   **Linear data (`Core.NonlinearVirasoro`).**  For a *linear* OPE datum — every value of `ope` in
   `ℂ·1 ⊕ span (gv)`, which covers `virasoroOPE` — only `N(X,D)` with `X ∈ R ⊕ ℂ1` ever occurs,
   where `N(X,D) = X·D`; so `M(R)` *is* the two-sided `T`-stable ideal generated by the relations,
   constructed there as `MRtwo`, with `MRbot_lt_MRtwo_virasoro` witnessing the strictness
   explicitly (`rel(L,TL)·L`).  Lemma 3.2 is still needed for data with genuine normally ordered
   products in the OPE.
3. **The annihilation half of the generating fields is not constructed here**, and neither is
   their locality.  That is the content of `GenFields.loc` and the annihilation range of
   `GenFields.fld`; `emptyGenFields` below is a consistency witness only.
   **Over `MRbot` the obligation is not merely open but false:**
   `Core.NonlinearVirasoro.not_nonempty_genFields_MRbot_virasoro` refutes
   `GenFields (MRbot (virasoroOPE c))` at every central charge, because `GenFields.cre` pins the
   whole creation quadrant to left multiplication while `MRbot` is only a *left* ideal.  Over the
   corrected ideal `ker Φ ⊇ MRtwo`, `Examples.NonlinearVirasoroTransport.genFieldsVir` **does**
   populate `GenFields` for the Virasoro generator set — by transporting an independently
   constructed realization, not by formalising Lemma 3.2 or De Sole–Kac §4.  `UR_YA` therefore
   has a nonempty-generator instance.  The identification
   `MRtwo (virasoroOPE c) = ker Φ` is proved
   (`Examples.NonlinearVirasoroGenuine.MRtwo_eq_ker_PhiVir`, via the straightening lemma
   `sortedWstUw_span`), and `Examples.NonlinearVirasoroGenuine.genFieldsVirTwo` populates
   `GenFields (MRtwo (virasoroOPE c))` — over De Sole–Kac's own `M(R)` for this linear datum.
4. Nothing *here* asserts that a general `OPEData` yields a vertex algebra.
   **Virasoro.**  For Virasoro,
   `Examples.NonlinearVirasoroTransport.virasoro_presentation_equivalence` identifies
   `T(R)/ker Φ` with the Borcherds-axiomatised `virasoroVOA c` (vacuum, translation and every
   generating field matched), `virasoroURVA` puts an actual bundled `PreVertexAlgebra` on it, and
   `sortedWordSt_linearIndependent` shows the strong generators — indeed all sorted monomials in
   them — stay independent in the quotient, `pbw`-free.  The equivalence is not circular:
   `Examples.NonlinearVirasoroGenuine.MRtwo_eq_ker_PhiVir` proves
   `MRtwo (virasoroOPE c) = ker Φ` (the straightening lemma `sortedWstUw_span` — sorted words
   span `T(R)/MRtwo` — plus the `pbw`-free independence `negWordVir_coef_zero'`), and
   `virasoro_presentation_equivalence_genuine` states the equivalence over
   `MRtwo (virasoroOPE c)` itself, an ideal defined by the OPE presentation alone.
   ⚠ **Scope.**  This is weaker than the slogan "generators + OPE = Borcherds": the relations in
   `MRtwo (virasoroOPE c)` do not depend on `c` (certificate `L11Checks.virasoro_MRtwo_indep`,
   `Notes/Textbook/certificates/L11_Checks.lean`), and the vertex-algebra structure on the quotient is
   *transported* from `virasoroVOA c` (only the creation half is pinned by the presentation); the
   fields are not derived from the OPE.  What is proved: the space and creation operators presented
   by one weight-two generator with the Virasoro OPE are those of `V(c,0)`, for every `c`.

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.  Every
declaration depends only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.NonlinearConformal

open Module (End)

set_option maxRecDepth 4000

universe u v

/-! ## §1  The tensor algebra `T(R)` and its word basis

`R` is the free `ℂ[T]`-module on the strong generators `ι`.  Its `ℂ`-basis is `ι × ℕ`, the pair
`(i,k)` standing for the divided power `Tᵏaⁱ/k!`; then `T(R)` is the free associative algebra on
that index set, which *is* the tensor algebra of `R` (`TensorAlgebra.equivFreeAlgebra`) and comes
with an honest word basis.

Taking `R` free is a deliberate restriction of Definition 3.1 (no `ℂ[T]`-torsion).  Central
elements such as the central charge are handled the physicist's way, as scalars multiplying the
**unit word** of `T(R)` — see `virasoroOPE`. -/

/-- The `ℂ`-basis index of `R`: `(i,k)` denotes the divided power `Tᵏaⁱ/k!`. -/
abbrev GenIdx (ι : Type u) : Type u := ι × ℕ

/-- `T(R)`, the tensor algebra of `R`, presented as the free associative algebra on `GenIdx ι`. -/
abbrev TR (ι : Type u) : Type u := FreeAlgebra ℂ (GenIdx ι)

/-- The word basis of `T(R)`, indexed by `FreeMonoid (GenIdx ι)`. -/
noncomputable abbrev wbasis (ι : Type u) : Module.Basis (FreeMonoid (GenIdx ι)) ℂ (TR ι) :=
  FreeAlgebra.basisFreeMonoid ℂ (GenIdx ι)

variable {ι : Type u}

/-- The word basis **is** the monoid homomorphism `w ↦ x₁ ⋯ xₙ`.  This is what makes every
later induction over words a two-line argument. -/
theorem wbasis_eq_lift (w : FreeMonoid (GenIdx ι)) :
    wbasis ι w = FreeMonoid.lift (FreeAlgebra.ι ℂ) w := by
  simp only [FreeAlgebra.basisFreeMonoid, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
      (MonoidAlgebra.single w (1 : ℂ) : MonoidAlgebra ℂ (FreeMonoid (GenIdx ι)))) = _
  rw [FreeAlgebra.equivMonoidAlgebraFreeMonoid, AlgEquiv.ofAlgHom_symm_apply,
    MonoidAlgebra.lift_single, one_smul]

/-- The word basis is multiplicative. -/
theorem wbasis_mul (v w : FreeMonoid (GenIdx ι)) :
    wbasis ι (v * w) = wbasis ι v * wbasis ι w := by
  rw [wbasis_eq_lift, wbasis_eq_lift, wbasis_eq_lift, map_mul]

/-- The empty word is the unit. -/
theorem wbasis_one : wbasis ι 1 = 1 := by rw [wbasis_eq_lift, map_one]

/-- A one-letter word is the corresponding generator of the free algebra. -/
theorem wbasis_of (p : GenIdx ι) : wbasis ι (FreeMonoid.of p) = FreeAlgebra.ι ℂ p := by
  rw [wbasis_eq_lift, FreeMonoid.lift_eval_of]

/-- The basis vector of `R` viewed inside `T(R)`: `gv (i,k) = Tᵏaⁱ/k!`. -/
noncomputable def gv (p : GenIdx ι) : TR ι := wbasis ι (FreeMonoid.of p)

/-- `gv` is the canonical inclusion of generators into the free algebra. -/
theorem gv_eq (p : GenIdx ι) : gv p = FreeAlgebra.ι ℂ p := wbasis_of p

/-! ## §2  Conformal weight and the weight filtration -/

section Weight
variable (wt : ι → ℕ)

/-- The conformal weight of a basis vector of `R`: `Δ(Tᵏaⁱ/k!) = Δ(aⁱ) + k`. -/
def wtIdx : GenIdx ι → ℕ := fun p => wt p.1 + p.2

/-- The conformal weight of a word of `T(R)` — the sum of the weights of its letters. -/
def wtWord : FreeMonoid (GenIdx ι) → ℕ := fun w => (w.toList.map (wtIdx wt)).sum

/-- The conformal-weight **filtration** of `T(R)`, indexed by `ℤ` so that a negative bound gives
`⊥`.  That is what makes the singular OPE terminate without a separate finiteness axiom. -/
noncomputable def filt (d : ℤ) : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (wbasis ι '' {w | ((wtWord wt w : ℤ)) ≤ d})

/-- Below weight `0` the filtration is trivial. -/
theorem filt_neg {d : ℤ} (hd : d < 0) : filt wt d = (⊥ : Submodule ℂ (TR ι)) := by
  rw [filt, Submodule.span_eq_bot]
  rintro x ⟨w, hw, rfl⟩
  simp only [Set.mem_setOf_eq] at hw
  exact absurd (hw.trans_lt hd) (by omega)

/-- The filtration is monotone. -/
theorem filt_mono {d e : ℤ} (h : d ≤ e) : filt wt d ≤ filt wt e := by
  rw [filt, filt]
  refine Submodule.span_mono ?_
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, le_trans hw h, rfl⟩

/-- A word of weight at most `d` lies in `filt d`. -/
theorem wbasis_mem_filt {w : FreeMonoid (GenIdx ι)} {d : ℤ} (h : (wtWord wt w : ℤ) ≤ d) :
    wbasis ι w ∈ filt wt d :=
  Submodule.subset_span ⟨w, h, rfl⟩

/-- The weight of a one-letter word. -/
theorem wtWord_of (p : GenIdx ι) : wtWord wt (FreeMonoid.of p) = wtIdx wt p := by
  change ((FreeMonoid.of p).toList.map (wtIdx wt)).sum = wtIdx wt p
  rw [show (FreeMonoid.of p).toList = [p] from rfl, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- The weight of the empty word. -/
theorem wtWord_one : wtWord wt (1 : FreeMonoid (GenIdx ι)) = 0 := rfl

/-- A generator of weight at most `d` lies in `filt d`. -/
theorem gv_mem_filt {p : GenIdx ι} {d : ℤ} (h : (wtIdx wt p : ℤ) ≤ d) : gv p ∈ filt wt d := by
  refine wbasis_mem_filt wt ?_
  rw [wtWord_of]
  exact h

/-- The unit word has weight `0`, so `1 ∈ filt d` for every `d ≥ 0`. -/
theorem one_mem_filt {d : ℤ} (h : 0 ≤ d) : (1 : TR ι) ∈ filt wt d := by
  rw [← wbasis_one]
  refine wbasis_mem_filt wt ?_
  rw [wtWord_one]
  exact_mod_cast h

/-- Weights add along the product of words. -/
theorem wtWord_mul (v w : FreeMonoid (GenIdx ι)) :
    wtWord wt (v * w) = wtWord wt v + wtWord wt w := by
  change (((v * w).toList).map (wtIdx wt)).sum = _
  rw [show (v * w).toList = v.toList ++ w.toList from rfl, List.map_append, List.sum_append]
  rfl

/-- Multiplying by a generator shifts the filtration by that generator's weight. -/
theorem gv_mul_mem_filt (p : GenIdx ι) {e : ℤ} {y : TR ι} (hy : y ∈ filt wt e) :
    gv p * y ∈ filt wt ((wtIdx wt p : ℤ) + e) := by
  rw [filt] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      refine Submodule.subset_span ⟨FreeMonoid.of p * w, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, wtWord_mul, wtWord_of]
        push_cast
        omega
      · rw [wbasis_mul, ← gv]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- The filtration is exhaustive — the `hcov` hypothesis of `isField_of_filt`. -/
theorem filt_exhaustive (x : TR ι) : ∃ d : ℤ, x ∈ filt wt d := by
  have hx : x ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨w, rfl⟩ := hz; exact ⟨(wtWord wt w : ℤ), wbasis_mem_filt wt le_rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
      obtain ⟨d, hd⟩ := ha
      obtain ⟨e, he⟩ := hb
      exact ⟨max d e, Submodule.add_mem _ (filt_mono wt (le_max_left d e) hd)
        (filt_mono wt (le_max_right d e) he)⟩
  | smul c a _ ha => obtain ⟨d, hd⟩ := ha; exact ⟨d, Submodule.smul_mem _ c hd⟩

end Weight

/-! ## §3  The translation operator on `T(R)`

`T` acts on `R` by `T(Tᵏaⁱ/k!) = (k+1)·(Tᵏ⁺¹aⁱ/(k+1)!)` and extends uniquely to a derivation of
`T(R)`.  The derivation is produced by the dual-numbers trick: an algebra homomorphism into
`T(R) ⊕ εT(R)` whose first component is the identity has second component a derivation. -/

/-- `T` on the basis of `R`: `T (Tᵏaⁱ/k!) = (k+1)·(Tᵏ⁺¹aⁱ/(k+1)!)`. -/
noncomputable def TGen (p : GenIdx ι) : TR ι := ((p.2 + 1 : ℕ) : ℂ) • gv (p.1, p.2 + 1)

/-- The algebra homomorphism `T(R) → T(R) ⊕ εT(R)` implementing the derivation. -/
noncomputable def phiT : TR ι →ₐ[ℂ] TrivSqZeroExt (TR ι) (TR ι) :=
  FreeAlgebra.lift ℂ (fun p => TrivSqZeroExt.inl (FreeAlgebra.ι ℂ p) + TrivSqZeroExt.inr (TGen p))

set_option maxRecDepth 4000 in
/-- The first component of `phiT` is the identity. -/
theorem phiT_fst (x : TR ι) : (phiT x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ (TR ι) (TR ι)).comp (phiT (ι := ι)) = AlgHom.id ℂ (TR ι) := by
    apply FreeAlgebra.hom_ext
    funext p
    change ((TrivSqZeroExt.fstHom ℂ (TR ι) (TR ι)) (phiT (FreeAlgebra.ι ℂ p)) : TR ι)
        = FreeAlgebra.ι ℂ p
    rw [phiT, FreeAlgebra.lift_ι_apply]
    change ((TrivSqZeroExt.inl (FreeAlgebra.ι ℂ p) +
      TrivSqZeroExt.inr (TGen p) : TrivSqZeroExt (TR ι) (TR ι))).fst = FreeAlgebra.ι ℂ p
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  exact DFunLike.congr_fun h x

/-- The **translation operator** `T : T(R) →ₗ T(R)`, the unique derivation extending `T` on
`R`. -/
noncomputable def Ttr : TR ι →ₗ[ℂ] TR ι where
  toFun := fun x => (phiT x).snd
  map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add]
  map_smul' := fun c x => by rw [RingHom.id_apply, map_smul, TrivSqZeroExt.snd_smul]

/-- Unfolding `Ttr`. -/
theorem Ttr_apply (x : TR ι) : Ttr x = (phiT x).snd := rfl

/-- `Ttr` is a derivation of `T(R)`. -/
theorem Ttr_mul (x y : TR ι) : Ttr (x * y) = x * Ttr y + Ttr x * y := by
  rw [Ttr_apply, map_mul, TrivSqZeroExt.snd_mul, phiT_fst, phiT_fst]
  rfl

/-- `Ttr` on a generator of `R` is the prescribed divided-power shift. -/
theorem Ttr_gv (p : GenIdx ι) : Ttr (gv p) = ((p.2 + 1 : ℕ) : ℂ) • gv (p.1, p.2 + 1) := by
  rw [gv_eq, Ttr_apply, phiT, FreeAlgebra.lift_ι_apply]
  simp [TGen]

/-- `T|0⟩ = 0`. -/
theorem Ttr_one : Ttr (1 : TR ι) = (0 : TR ι) := by
  rw [Ttr_apply, map_one, TrivSqZeroExt.snd_one]

/-- `T` raises the conformal weight of a monomial by exactly one. -/
theorem Ttr_wbasis_mem_filt (wt : ι → ℕ) (l : List (GenIdx ι)) :
    Ttr (wbasis ι (FreeMonoid.ofList l))
      ∈ filt wt ((wtWord wt (FreeMonoid.ofList l) : ℤ) + 1) := by
  induction l with
  | nil =>
      rw [show (FreeMonoid.ofList ([] : List (GenIdx ι))) = 1 from rfl, wbasis_one, Ttr_one]
      exact Submodule.zero_mem _
  | cons p l ih =>
      have hsplit : (FreeMonoid.ofList (p :: l))
          = FreeMonoid.of p * FreeMonoid.ofList l := rfl
      have hw : wbasis ι (FreeMonoid.ofList (p :: l))
          = gv p * wbasis ι (FreeMonoid.ofList l) := by rw [hsplit, wbasis_mul, gv]
      have hwt : wtWord wt (FreeMonoid.ofList (p :: l))
          = wtIdx wt p + wtWord wt (FreeMonoid.ofList l) := by
        rw [hsplit, wtWord_mul, wtWord_of]
      rw [hw, Ttr_mul, hwt]
      refine Submodule.add_mem _ ?_ ?_
      · exact filt_mono wt (by push_cast; omega) (gv_mul_mem_filt wt p ih)
      · rw [Ttr_gv, smul_mul_assoc]
        refine Submodule.smul_mem _ _ ?_
        refine filt_mono wt (by simp only [wtIdx]; push_cast; omega)
          (gv_mul_mem_filt wt (p.1, p.2 + 1) (wbasis_mem_filt wt (le_refl _)))

/-- `T` shifts the weight filtration by one — the bookkeeping every conformal-weight argument
downstream rests on. -/
theorem Ttr_mem_filt (wt : ι → ℕ) {d : ℤ} {x : TR ι} (hx : x ∈ filt wt d) :
    Ttr x ∈ filt wt (d + 1) := by
  rw [filt] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      have hT := Ttr_wbasis_mem_filt wt (FreeMonoid.toList w)
      rw [show FreeMonoid.ofList (FreeMonoid.toList w) = w from rfl] at hT
      exact filt_mono wt (by omega) hT
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-! ## §4  De Sole–Kac Definition 3.1 — the user-facing datum

This is the interface.  To define a vertex algebra one writes down

* `wt`  — the conformal weight of each strong generator (a positive natural number; half-integer
  fermion weights are accommodated by rescaling all weights by `2`, which is harmless since the
  grading set only has to be a discrete additive monoid);
* `par` — its parity;
* `ope` — the **singular OPE**, i.e. the table `aⁱ(z)aʲ(w) ~ Σₙ (ope i j n)(w)/(z-w)ⁿ⁺¹`, whose
  entries are arbitrary elements of `T(R)`: normally ordered polynomials in the generators, plus
  scalars times the unit word for central terms.

and nothing else.  Sesquilinearity is **not** an axiom the user checks — it is the definition of
the bracket on the divided powers `Tᵏaⁱ/k!`, derived once and for all in `brk` below.  The single
axiom is the grading condition. -/

/-- **Definition 3.1** (non-linear conformal superalgebra), in the free-generator form: `R` is the
free `ℂ[T]`-module on `ι`, and the λ-bracket `R ⊗ R → ℂ[λ] ⊗ T(R)` is determined by its values on
the bottom generators, which are exactly the singular-OPE coefficients.

The grading condition `Δ(aⁱ₍ₙ₎aʲ) ≤ Δᵢ + Δⱼ - n - 1` is stated through the `ℤ`-indexed filtration
`filt`, so that it *also* encodes the termination of the OPE: for `n + 1 > Δᵢ + Δⱼ` the bound is
negative, `filt` is `⊥`, and the coefficient is forced to vanish (`OPEData.ope_eq_zero`).  No
separate finiteness axiom is needed. -/
structure OPEData (ι : Type u) where
  /-- the conformal weight of each strong generator -/
  wt : ι → ℕ
  /-- weights are positive: the grading set is `ℕ_{>0}` -/
  wt_pos : ∀ i, 0 < wt i
  /-- the parity of each strong generator -/
  par : ι → ZMod 2
  /-- the singular OPE: `ope i j n = aⁱ₍ₙ₎aʲ ∈ T(R)` -/
  ope : ι → ι → ℕ → TR ι
  /-- the grading condition of Definition 3.1 -/
  ope_wt : ∀ i j (n : ℕ), ope i j n ∈ filt wt ((wt i : ℤ) + (wt j : ℤ) - (n : ℤ) - 1)

namespace OPEData

variable (D : OPEData ι)

/-- The singular OPE **terminates by itself**: the grading condition forces the coefficient of
`(z-w)^{-n-1}` to vanish once `n ≥ Δᵢ + Δⱼ`. -/
theorem ope_eq_zero (i j : ι) {n : ℕ} (h : D.wt i + D.wt j ≤ n) : D.ope i j n = 0 := by
  have hmem := D.ope_wt i j n
  rw [filt_neg D.wt (by omega : (D.wt i : ℤ) + (D.wt j : ℤ) - (n : ℤ) - 1 < 0)] at hmem
  exact hmem

end OPEData

/-! ### The Virasoro algebra in this form

The worked example.  With the single generator `L` of weight `2`, `[L_λ L] = (T + 2λ)L +
(c/12)λ³`, and since `[a_λ b] = Σₙ λⁿ/n! · a₍ₙ₎b` this reads

  `L₍₀₎L = TL`,  `L₍₁₎L = 2L`,  `L₍₂₎L = 0`,  `L₍₃₎L = (c/2)·1`,  `L₍ₙ₎L = 0 (n ≥ 4)`.

`TL` is the divided power `((),1)` and the central term is a scalar times the **unit word** of
`T(R)`.  That is the entire input; nothing else about Virasoro is supplied. -/

/-- **The Virasoro algebra of central charge `c` as a term of `OPEData Unit`** — the worked
example of the interface, machine-checked (the grading condition is *proved*, not assumed). -/
noncomputable def virasoroOPE (c : ℂ) : OPEData Unit where
  wt := fun _ => 2
  wt_pos := fun _ => by norm_num
  par := fun _ => 0
  ope := fun _ _ n =>
    if n = 0 then gv ((), 1)
    else if n = 1 then (2 : ℂ) • gv ((), 0)
    else if n = 3 then (c / 2) • (1 : TR Unit)
    else 0
  ope_wt := by
    intro i j n
    split_ifs with h0 h1 h3
    · subst h0
      exact gv_mem_filt _ (by norm_num [wtIdx])
    · subst h1
      exact Submodule.smul_mem _ _ (gv_mem_filt _ (by norm_num [wtIdx]))
    · subst h3
      exact Submodule.smul_mem _ _ (one_mem_filt _ (by norm_num))
    · exact Submodule.zero_mem _

/-! ## §5  The λ-bracket on all of `R`, by sesquilinearity

Definition 3.1 gives the bracket on the bottom generators; sesquilinearity
`[Ta_λ b] = -λ[a_λ b]`, `[a_λ Tb] = (λ + T)[a_λ b]` determines it on the divided powers.  In
`n`-th product form these two rules are

  `(Ta)₍ₙ₎b = -n·a₍ₙ₋₁₎b`   and   `a₍ₙ₎(Tb) = T(a₍ₙ₎b) + n·a₍ₙ₋₁₎b`,

each of which is a single operation on the *function* `n ↦ a₍ₙ₎b`.  Iterating them and dividing
by `k!·l!` gives the bracket of `Tᵏaⁱ/k!` with `Tˡaʲ/l!`.  Presenting the extension this way —
as iterates of two commuting one-step operators rather than a closed binomial formula — is what
makes the two sesquilinearity identities `brk_left`, `brk_right` one-line consequences of the
definition, which in turn is what makes `M(R)` provably `T`-stable. -/

/-- One step of `T` on the **left** slot: `(Ta)₍ₙ₎b = -n·a₍ₙ₋₁₎b`. -/
noncomputable def Lstep (f : ℕ → TR ι) : ℕ → TR ι := fun n => -(n : ℂ) • f (n - 1)

/-- One step of `T` on the **right** slot: `a₍ₙ₎(Tb) = T(a₍ₙ₎b) + n·a₍ₙ₋₁₎b`. -/
noncomputable def Rstep (f : ℕ → TR ι) : ℕ → TR ι := fun n => Ttr (f n) + (n : ℂ) • f (n - 1)

/-- The two sesquilinearity steps act on different slots, so they commute. -/
theorem Lstep_Rstep (f : ℕ → TR ι) : Lstep (Rstep f) = Rstep (Lstep f) := by
  funext n
  change -(n : ℂ) • (Ttr (f (n - 1)) + ((n - 1 : ℕ) : ℂ) • f (n - 1 - 1))
      = Ttr (-(n : ℂ) • f (n - 1)) + (n : ℂ) • (-((n - 1 : ℕ) : ℂ) • f (n - 1 - 1))
  rw [smul_add, map_smul, smul_smul, smul_smul]
  ring_nf

/-- Iterating the left step past one right step. -/
theorem Lstep_iterate_Rstep (k : ℕ) (f : ℕ → TR ι) :
    Lstep^[k] (Rstep f) = Rstep (Lstep^[k] f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Lstep_Rstep, ih, Function.iterate_succ_apply]

/-- **The λ-bracket of Definition 3.1**, extended from the bottom generators to all of `R`:
`brk D (i,k) (j,l) n = (Tᵏaⁱ/k!)₍ₙ₎(Tˡaʲ/l!)`. -/
noncomputable def brk (D : OPEData ι) (p q : GenIdx ι) (n : ℕ) : TR ι :=
  (((p.2).factorial : ℂ) * ((q.2).factorial : ℂ))⁻¹ •
    Lstep^[p.2] (Rstep^[q.2] (D.ope p.1 q.1)) n

/-- On the bottom generators `brk` is the user's OPE table. -/
theorem brk_bot (D : OPEData ι) (i j : ι) (n : ℕ) : brk D (i, 0) (j, 0) n = D.ope i j n := by
  rw [brk]
  simp

/-- **Sesquilinearity in the left slot**: `(Ta)₍ₙ₎b = -n·a₍ₙ₋₁₎b`, in divided-power form. -/
theorem brk_left (D : OPEData ι) (i : ι) (k : ℕ) (q : GenIdx ι) (n : ℕ) :
    (((k : ℂ) + 1) • brk D (i, k + 1) q n) = -(n : ℂ) • brk D (i, k) q (n - 1) := by
  have hfac : (((k + 1).factorial : ℂ)) = ((k : ℂ) + 1) * ((k.factorial : ℂ)) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hne : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hfk : ((k.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfq : ((q.2.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q.2)
  rw [brk, brk, Function.iterate_succ_apply']
  change ((k : ℂ) + 1) • (((((k + 1).factorial : ℂ)) * ((q.2.factorial : ℂ)))⁻¹ •
      (-(n : ℂ) • Lstep^[k] (Rstep^[q.2] (D.ope i q.1)) (n - 1)))
    = -(n : ℂ) • ((((k.factorial : ℂ)) * ((q.2.factorial : ℂ)))⁻¹ •
      Lstep^[k] (Rstep^[q.2] (D.ope i q.1)) (n - 1))
  rw [hfac]
  simp only [smul_smul]
  congr 1
  field_simp

/-- **Sesquilinearity in the right slot**: `a₍ₙ₎(Tb) = T(a₍ₙ₎b) + n·a₍ₙ₋₁₎b`, in divided-power
form. -/
theorem brk_right (D : OPEData ι) (p : GenIdx ι) (j : ι) (l : ℕ) (n : ℕ) :
    (((l : ℂ) + 1) • brk D p (j, l + 1) n)
      = Ttr (brk D p (j, l) n) + (n : ℂ) • brk D p (j, l) (n - 1) := by
  have hfac : (((l + 1).factorial : ℂ)) = ((l : ℂ) + 1) * ((l.factorial : ℂ)) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hne : ((l : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero l
  have hfl : ((l.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  have hfk : ((p.2.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p.2)
  set G : ℕ → TR ι := Lstep^[p.2] (Rstep^[l] (D.ope p.1 j)) with hG
  have hstep : Lstep^[p.2] (Rstep^[l + 1] (D.ope p.1 j)) = Rstep G := by
    rw [Function.iterate_succ_apply', Lstep_iterate_Rstep, ← hG]
  rw [brk, brk, brk, hstep, hfac]
  change ((l : ℂ) + 1) • (((p.2.factorial : ℂ) * (((l : ℂ) + 1) * (l.factorial : ℂ)))⁻¹ •
      (Ttr (G n) + (n : ℂ) • G (n - 1)))
    = Ttr (((p.2.factorial : ℂ) * (l.factorial : ℂ))⁻¹ • G n)
      + (n : ℂ) • (((p.2.factorial : ℂ) * (l.factorial : ℂ))⁻¹ • G (n - 1))
  simp only [map_smul, smul_add, smul_smul]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

/-! ### Termination of the extended bracket -/

/-- Vanishing propagates through the right step. -/
theorem Rstep_iterate_eq_zero {f : ℕ → TR ι} {N : ℕ} (hf : ∀ n, N ≤ n → f n = 0) :
    ∀ (l n : ℕ), N + l ≤ n → Rstep^[l] f n = 0 := by
  intro l
  induction l with
  | zero => intro n hn; exact hf n (by omega)
  | succ l ih =>
      intro n hn
      rw [Function.iterate_succ_apply']
      change Ttr (Rstep^[l] f n) + (n : ℂ) • Rstep^[l] f (n - 1) = 0
      rw [ih n (by omega), ih (n - 1) (by omega), map_zero, smul_zero, add_zero]

/-- Vanishing propagates through the left step. -/
theorem Lstep_iterate_eq_zero {f : ℕ → TR ι} {N : ℕ} (hf : ∀ n, N ≤ n → f n = 0) :
    ∀ (k n : ℕ), N + k ≤ n → Lstep^[k] f n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; exact hf n (by omega)
  | succ k ih =>
      intro n hn
      rw [Function.iterate_succ_apply']
      change -(n : ℂ) • Lstep^[k] f (n - 1) = 0
      rw [ih (n - 1) (by omega), smul_zero]

/-- **The extended bracket terminates**: `p₍ₙ₎q = 0` once `n ≥ Δp + Δq`.  This is inherited
from the grading condition alone — no finiteness has been assumed anywhere. -/
theorem brk_vanish (D : OPEData ι) (p q : GenIdx ι) {n : ℕ}
    (h : wtIdx D.wt p + wtIdx D.wt q ≤ n) : brk D p q n = 0 := by
  have hbase : ∀ m, D.wt p.1 + D.wt q.1 ≤ m → D.ope p.1 q.1 m = 0 := fun m hm =>
    D.ope_eq_zero p.1 q.1 hm
  have hR := Rstep_iterate_eq_zero hbase q.2
  have hL := Lstep_iterate_eq_zero (f := Rstep^[q.2] (D.ope p.1 q.1))
    (N := D.wt p.1 + D.wt q.1 + q.2) hR p.2
  rw [brk, hL n (by simp only [wtIdx] at h; omega), smul_zero]

/-- The grading condition propagates through the right sesquilinearity step. -/
theorem Rstep_mem_filt {wt : ι → ℕ} {f : ℕ → TR ι} {c : ℤ}
    (hf : ∀ n : ℕ, f n ∈ filt wt (c - n)) (n : ℕ) : Rstep f n ∈ filt wt (c + 1 - n) := by
  change Ttr (f n) + ((n : ℂ)) • f (n - 1) ∈ filt wt (c + 1 - n)
  exact Submodule.add_mem _ (filt_mono wt (by omega) (Ttr_mem_filt wt (hf n)))
    (Submodule.smul_mem _ _ (filt_mono wt (by omega) (hf (n - 1))))

/-- The grading condition propagates through the left sesquilinearity step. -/
theorem Lstep_mem_filt {wt : ι → ℕ} {f : ℕ → TR ι} {c : ℤ}
    (hf : ∀ n : ℕ, f n ∈ filt wt (c - n)) (n : ℕ) : Lstep f n ∈ filt wt (c + 1 - n) := by
  change -((n : ℂ)) • f (n - 1) ∈ filt wt (c + 1 - n)
  exact Submodule.smul_mem _ _ (filt_mono wt (by omega) (hf (n - 1)))

/-- Iterating the right step. -/
theorem Rstep_iterate_mem_filt {wt : ι → ℕ} :
    ∀ (l : ℕ) {f : ℕ → TR ι} {c : ℤ}, (∀ n : ℕ, f n ∈ filt wt (c - n)) →
      ∀ n : ℕ, Rstep^[l] f n ∈ filt wt (c + l - n) := by
  intro l
  induction l with
  | zero =>
      intro f c hf n
      rw [Function.iterate_zero_apply]
      exact filt_mono wt (by push_cast; omega) (hf n)
  | succ l ih =>
      intro f c hf n
      rw [Function.iterate_succ_apply]
      exact filt_mono wt (by push_cast; omega)
        (ih (f := Rstep f) (c := c + 1) (fun m => Rstep_mem_filt hf m) n)

/-- Iterating the left step. -/
theorem Lstep_iterate_mem_filt {wt : ι → ℕ} :
    ∀ (k : ℕ) {f : ℕ → TR ι} {c : ℤ}, (∀ n : ℕ, f n ∈ filt wt (c - n)) →
      ∀ n : ℕ, Lstep^[k] f n ∈ filt wt (c + k - n) := by
  intro k
  induction k with
  | zero =>
      intro f c hf n
      rw [Function.iterate_zero_apply]
      exact filt_mono wt (by push_cast; omega) (hf n)
  | succ k ih =>
      intro f c hf n
      rw [Function.iterate_succ_apply]
      exact filt_mono wt (by push_cast; omega)
        (ih (f := Lstep f) (c := c + 1) (fun m => Lstep_mem_filt hf m) n)

/-- **The extended bracket satisfies the grading condition of Definition 3.1**:
`Δ(p₍ₙ₎q) ≤ Δp + Δq - n - 1`.  So `brk` really is a λ-bracket in the sense of Definition 3.1,
not merely a formula; `brk_vanish` is the special case where the bound goes negative. -/
theorem brk_mem_filt (D : OPEData ι) (p q : GenIdx ι) (n : ℕ) :
    brk D p q n ∈ filt D.wt ((wtIdx D.wt p : ℤ) + (wtIdx D.wt q : ℤ) - n - 1) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  have hbase : ∀ m : ℕ, D.ope i j m
      ∈ filt D.wt (((D.wt i : ℤ) + (D.wt j : ℤ) - 1) - m) :=
    fun m => filt_mono D.wt (by omega) (D.ope_wt i j m)
  have hL := Lstep_iterate_mem_filt k (Rstep_iterate_mem_filt l hbase) n
  rw [brk]
  exact Submodule.smul_mem _ _
    (filt_mono D.wt (by simp only [wtIdx]; push_cast; omega) hL)

/-! ## §7  The relation, and the quotient `T(R)/M`

De Sole–Kac **Definition 3.4** sets

  `M(R) = span_ℂ { A ⊗ ((b⊗c - p(b,c)·c⊗b) ⊗ D - N(∫₋ᵀ⁰[b_λ c]dλ, D)) | b,c ∈ R, A,D ∈ T(R) }`,

where `N` is the normally ordered product extended from `R` to all of `T(R)` — their Lemma 3.2.
Because `A` ranges over all of `T(R)`, `M(R)` is a **left** ideal of the associative algebra
`T(R)`; it is not a right ideal, and `T(R)/M(R)` is a quotient of `ℂ`-vector spaces, **not** an
associative algebra.  Nothing below treats it as one.  (Concretely, an ideal is carried here as a
`Submodule ℂ (TR ι)` *plus* the left-multiplication property as a field.  Packaging it as a
`Submodule (TR ι) (TR ι)` would make the quotient a `T(R)`-module quotient, and `Submodule.mapQ`
would then demand `T(R)`-linear operators — which the nonnegative modes are not.)

⚠ **Exactly what is formalized.**  `N` is *not* formalized in this file — that is Lemma 3.2, the
step this development stops short of.  What is formalized is the `D = 1` slice of Definition 3.4:
since `N(X,1) = X` (their (3.1)), those generators are precisely `A ⊗ rel(b,c)` with

  `rel(b,c) = b⊗c - p(b,c)·c⊗b - ∫₋ᵀ⁰[b_λ c]dλ`,

giving the left ideal `MRbot`, which therefore satisfies `MRbot ⊆ M(R)`.  The inclusion is
generally strict: the `D ≠ 1` generators say that two adjacent letters may be commuted *in the
middle* of a monomial, and those are not consequences of the `D = 1` ones.  (In the free algebra
on `x, y`, the element `(xy-yx)x` is not in the left ideal generated by `xy-yx`.)

Accordingly everything downstream is stated for an **arbitrary** admissible relation ideal
`M : MIdeal D` — a `T`-stable left ideal containing the relations — of which `MRbot` is the
smallest (`MRbot_le`), and of which the full `M(R)` will be one as soon as `N` exists.  Nothing
below has to be redone when that happens. -/

/-- Powers of `Ttr` as an endomorphism, peeled on the right. -/
theorem Ttr_pow_succ_right (m : ℕ) (x : TR ι) :
    (((Ttr : End ℂ (TR ι)) ^ (m + 1)) x) = ((Ttr : End ℂ (TR ι)) ^ m) (Ttr x) := by
  rw [pow_succ]; rfl

/-- Powers of `Ttr` as an endomorphism, peeled on the left. -/
theorem Ttr_pow_succ_left (m : ℕ) (x : TR ι) :
    (((Ttr : End ℂ (TR ι)) ^ (m + 1)) x) = Ttr (((Ttr : End ℂ (TR ι)) ^ m) x) := by
  rw [pow_succ']; rfl

/-- `Ttr` commutes with its own powers. -/
theorem Ttr_pow_comm (m : ℕ) (x : TR ι) :
    ((Ttr : End ℂ (TR ι)) ^ m) (Ttr x) = Ttr (((Ttr : End ℂ (TR ι)) ^ m) x) := by
  rw [← Ttr_pow_succ_right, Ttr_pow_succ_left]

/-- The `∫₋ᵀ⁰` of the singular OPE, `∫₋ᵀ⁰ [a_λ b] dλ = Σₙ ((-1)ⁿ/(n+1)!)·Tⁿ⁺¹(a₍ₙ₎b)`.  The
summation range is exactly the one the grading condition provides; by `brk_vanish` every omitted
term is zero. -/
noncomputable def opeInt (D : OPEData ι) (p q : GenIdx ι) : TR ι :=
  ∑ n ∈ Finset.range (wtIdx D.wt p + wtIdx D.wt q),
    ((-1 : ℂ) ^ n / ((n + 1).factorial : ℂ)) •
      (((Ttr : End ℂ (TR ι)) ^ (n + 1)) (brk D p q n))

/-- **The defining relation of `M(R)`**: the quantum commutator of two basis vectors of `R`
minus the `∫₋ᵀ⁰` of their singular OPE. -/
noncomputable def rel (D : OPEData ι) (p q : GenIdx ι) : TR ι :=
  gv p * gv q - koszul (D.par p.1) (D.par q.1) • (gv q * gv p) - opeInt D p q

/-- `T` acts on the relations by the Leibniz rule: this is the identity that makes `M(R)`
`T`-stable.  It is a *pointwise* cancellation — the two sesquilinearity rules contribute
`-n·a₍ₙ₋₁₎b` and `+n·a₍ₙ₋₁₎b` at each `n` — plus the vanishing of the one extra term at the top of
the enlarged summation range. -/
theorem Ttr_opeInt (D : OPEData ι) (p q : GenIdx ι) :
    ((p.2 : ℂ) + 1) • opeInt D (p.1, p.2 + 1) q
        + ((q.2 : ℂ) + 1) • opeInt D p (q.1, q.2 + 1)
      = Ttr (opeInt D p q) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  have hN1 : wtIdx D.wt (i, k + 1) + wtIdx D.wt (j, l)
      = (wtIdx D.wt (i, k) + wtIdx D.wt (j, l)) + 1 := by simp only [wtIdx]; omega
  have hN2 : wtIdx D.wt (i, k) + wtIdx D.wt (j, l + 1)
      = (wtIdx D.wt (i, k) + wtIdx D.wt (j, l)) + 1 := by simp only [wtIdx]; omega
  have hin : ∀ n : ℕ, ((k : ℂ) + 1) • brk D (i, k + 1) (j, l) n
      + ((l : ℂ) + 1) • brk D (i, k) (j, l + 1) n = Ttr (brk D (i, k) (j, l) n) := by
    intro n
    rw [brk_left, brk_right, neg_smul]
    abel
  have key : ∀ n : ℕ,
      ((k : ℂ) + 1) • (((-1 : ℂ) ^ n / ((n + 1).factorial : ℂ)) •
          (((Ttr : End ℂ (TR ι)) ^ (n + 1)) (brk D (i, k + 1) (j, l) n)))
        + ((l : ℂ) + 1) • (((-1 : ℂ) ^ n / ((n + 1).factorial : ℂ)) •
          (((Ttr : End ℂ (TR ι)) ^ (n + 1)) (brk D (i, k) (j, l + 1) n)))
      = ((-1 : ℂ) ^ n / ((n + 1).factorial : ℂ)) •
          Ttr (((Ttr : End ℂ (TR ι)) ^ (n + 1)) (brk D (i, k) (j, l) n)) := by
    intro n
    rw [smul_comm ((k : ℂ) + 1), smul_comm ((l : ℂ) + 1), ← smul_add]
    congr 1
    rw [← map_smul, ← map_smul, ← map_add, hin, Ttr_pow_comm]
  rw [opeInt, opeInt, opeInt, hN1, hN2, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun n _ => key n), Finset.sum_range_succ,
    brk_vanish D (i, k) (j, l) (le_refl _), map_zero, map_zero, smul_zero, add_zero, map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_smul]

/-- **`T` maps a relation into the span of the relations** — precisely,
`T(rel(a,b)) = rel(Ta,b) + rel(a,Tb)`.  This is the whole content of the `T`-stability of
`M(R)`, and it is why the relations must be imposed for *all* divided powers `Tᵏaⁱ/k!`, not only
for the bottom generators. -/
theorem Ttr_rel (D : OPEData ι) (p q : GenIdx ι) :
    Ttr (rel D p q)
      = ((p.2 : ℂ) + 1) • rel D (p.1, p.2 + 1) q
        + ((q.2 : ℂ) + 1) • rel D p (q.1, q.2 + 1) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  have hA : Ttr (gv (i, k) * gv (j, l))
      = ((k : ℂ) + 1) • (gv (i, k + 1) * gv (j, l))
        + ((l : ℂ) + 1) • (gv (i, k) * gv (j, l + 1)) := by
    rw [Ttr_mul, Ttr_gv, Ttr_gv, smul_mul_assoc, mul_smul_comm]
    push_cast
    exact add_comm _ _
  have hB : Ttr (gv (j, l) * gv (i, k))
      = ((l : ℂ) + 1) • (gv (j, l + 1) * gv (i, k))
        + ((k : ℂ) + 1) • (gv (j, l) * gv (i, k + 1)) := by
    rw [Ttr_mul, Ttr_gv, Ttr_gv, smul_mul_assoc, mul_smul_comm]
    push_cast
    exact add_comm _ _
  rw [rel, rel, rel, map_sub, map_sub, map_smul, hA, hB, ← Ttr_opeInt]
  simp only [smul_sub, smul_add, smul_smul, mul_comm (koszul (D.par i) (D.par j))]
  abel

/-! ### Admissible relation ideals -/

/-- An **admissible relation ideal**: a `ℂ`-subspace of `T(R)` that is closed under
multiplication on the **left** (and only on the left), is stable under the translation operator,
and contains all the relations of Definition 3.4 with `D = 1`.

De Sole–Kac's `M(R)` is one of these (once `N` is available); `MRbot` below is the smallest one.
Every construction in §§7–11 works for an arbitrary `MIdeal`, so none of it depends on which. -/
structure MIdeal (D : OPEData ι) where
  /-- the underlying `ℂ`-subspace -/
  car : Submodule ℂ (TR ι)
  /-- closed under multiplication on the left — and only on the left -/
  left : ∀ (A x : TR ι), x ∈ car → A * x ∈ car
  /-- stable under the translation operator -/
  Tstable : ∀ x ∈ car, Ttr x ∈ car
  /-- contains the quantum-commutator relations -/
  rel_mem : ∀ p q : GenIdx ι, rel D p q ∈ car

/-- The underlying subspace of `MRbot`: the `ℂ`-span of the left multiples of the relations. -/
noncomputable def MRbotCar (D : OPEData ι) : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (Set.range (fun z : TR ι × GenIdx ι × GenIdx ι => z.1 * rel D z.2.1 z.2.2))

/-- `MRbotCar` is closed under left multiplication. -/
theorem MRbotCar_left (D : OPEData ι) (A x : TR ι) (hx : x ∈ MRbotCar D) :
    A * x ∈ MRbotCar D := by
  rw [MRbotCar] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨B, pq⟩, rfl⟩ := hz
      refine Submodule.subset_span ⟨(A * B, pq), ?_⟩
      change A * B * rel D pq.1 pq.2 = A * (B * rel D pq.1 pq.2)
      exact mul_assoc _ _ _
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

/-- The relations belong to `MRbotCar`. -/
theorem rel_mem_MRbotCar (D : OPEData ι) (p q : GenIdx ι) : rel D p q ∈ MRbotCar D := by
  refine Submodule.subset_span ⟨(1, p, q), ?_⟩
  change (1 : TR ι) * rel D p q = rel D p q
  exact one_mul _

/-- **`MRbotCar` is `T`-stable.**  This is where `Ttr_rel` is consumed, and it is the reason the
relations have to be imposed for *all* divided powers `Tᵏaⁱ/k!` rather than only for the bottom
generators. -/
theorem Ttr_mem_MRbotCar (D : OPEData ι) : ∀ x ∈ MRbotCar D, Ttr x ∈ MRbotCar D := by
  intro x hx
  rw [MRbotCar] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨B, p, q⟩, rfl⟩ := hz
      change Ttr (B * rel D p q) ∈ MRbotCar D
      rw [Ttr_mul, Ttr_rel]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_add, mul_smul_comm, mul_smul_comm]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(B, (p.1, p.2 + 1), q), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(B, p, (q.1, q.2 + 1)), rfl⟩))
      · exact Submodule.subset_span ⟨(Ttr B, p, q), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

/-- **The smallest admissible relation ideal** — the `D = 1` slice of Definition 3.4. -/
noncomputable def MRbot (D : OPEData ι) : MIdeal D where
  car := MRbotCar D
  left := MRbotCar_left D
  Tstable := Ttr_mem_MRbotCar D
  rel_mem := rel_mem_MRbotCar D

/-- `MRbot` is contained in every admissible relation ideal — in particular in De Sole–Kac's
`M(R)`.  So the quotient built below from `MRbot` surjects onto the true `U(R)`. -/
theorem MRbot_le {D : OPEData ι} (M : MIdeal D) : (MRbot D).car ≤ M.car := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨⟨A, p, q⟩, rfl⟩
  exact M.left A _ (M.rel_mem p q)

/-! ### The quotient -/

variable {D : OPEData ι}

/-- **The quotient** `T(R)/M`, as a `ℂ`-vector space.  For `M = M(R)` this is the universal
enveloping vertex algebra `U(R)` of Theorem 3.9.
⚠ It is *not* an associative algebra: `M` is only a left ideal. -/
abbrev UR (M : MIdeal D) : Type u := TR ι ⧸ M.car

/-- The vacuum `|0⟩ = [1]`. -/
noncomputable def vacU (M : MIdeal D) : UR M := Submodule.Quotient.mk 1

/-- **Descent of a `ℂ`-linear operator** that preserves `M`. -/
noncomputable def descendU (M : MIdeal D) (f : TR ι →ₗ[ℂ] TR ι)
    (hf : ∀ x ∈ M.car, f x ∈ M.car) : End ℂ (UR M) :=
  M.car.mapQ M.car f (fun x hx => hf x hx)

@[simp] theorem descendU_mk (M : MIdeal D) (f : TR ι →ₗ[ℂ] TR ι)
    (hf : ∀ x ∈ M.car, f x ∈ M.car) (X : TR ι) :
    descendU M f hf (Submodule.Quotient.mk X) = Submodule.Quotient.mk (f X) := rfl

/-- The **translation operator** on `T(R)/M`, descended from the derivation of `T(R)`. -/
noncomputable def TrU (M : MIdeal D) : End ℂ (UR M) := descendU M Ttr M.Tstable

/-- `T|0⟩ = 0`. -/
theorem TrU_vac (M : MIdeal D) : TrU M (vacU M) = 0 := by
  rw [TrU, vacU, descendU_mk, Ttr_one, Submodule.Quotient.mk_zero]

/-- **The creation half of every generating field is free.**  Left multiplication by a fixed
`A ∈ T(R)` preserves `M` *because `M` is a left ideal*, so it descends with no theorem at all.
Every mode `a₍₋ₖ₋₁₎ = (Tᵏa/k!)₍₋₁₎` of a generating field is of this form. -/
noncomputable def leftMulU (M : MIdeal D) (A : TR ι) : End ℂ (UR M) :=
  descendU M
    { toFun := fun X => A * X,
      map_add' := fun X Y => by rw [mul_add],
      map_smul' := fun c X => by rw [RingHom.id_apply, mul_smul_comm] }
    (fun x hx => M.left A x hx)

@[simp] theorem leftMulU_mk (M : MIdeal D) (A X : TR ι) :
    leftMulU M A (Submodule.Quotient.mk X) = Submodule.Quotient.mk (A * X) := rfl

/-- The word states: the images of the monomials of `T(R)`. -/
noncomputable def wstU (M : MIdeal D) (w : FreeMonoid (GenIdx ι)) : UR M :=
  Submodule.Quotient.mk (wbasis ι w)

/-- **The word states span** — the `hspan` hypothesis of `reconstruct`, for free.  The monomials
are a Mathlib basis of `T(R)` and the quotient map is a surjective `ℂ`-linear map; no PBW, no
linear independence, and no ordering of monomials is involved. -/
theorem wstU_span (M : MIdeal D) : Submodule.span ℂ (Set.range (wstU M)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hX : X ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hX using Submodule.span_induction with
  | mem z hz => obtain ⟨w, rfl⟩ := hz; exact Submodule.subset_span ⟨w, rfl⟩
  | zero => rw [Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ c ha

/-! ### The creation half of the generating fields, constructed

For a basis vector `a = Tᵐaⁱ/m!` of `R`, De Sole–Kac's normally ordered product satisfies
`N(a, A) = a ⊗ A`, so the modes of `Y(a,z)` in the **creation** range are left multiplications by
the divided powers of `a`: `a₍₋ⱼ₋₁₎ = leftMul(Tʲa/j!)` for `j ≥ 0`.  Those are constructed here
outright, together with their translation covariance.  What is missing is only the annihilation
range — the modes `a₍ₙ₎` with `n ≥ 0` — and that is the whole of Lemma 3.2. -/

/-- The divided power `Tᵏ(Tᵐaⁱ/m!)/k! = C(m+k,k)·(Tᵐ⁺ᵏaⁱ/(m+k)!)` inside `T(R)`. -/
noncomputable def dpow (p : GenIdx ι) (k : ℕ) : TR ι :=
  (((p.2 + k).choose k : ℕ) : ℂ) • gv (p.1, p.2 + k)

@[simp] theorem dpow_zero (p : GenIdx ι) : dpow p 0 = gv p := by
  obtain ⟨i, m⟩ := p
  rw [dpow]
  simp

/-- `T` acts on the divided powers as `T(Tᵏa/k!) = (k+1)·(Tᵏ⁺¹a/(k+1)!)`. -/
theorem Ttr_dpow (p : GenIdx ι) (k : ℕ) :
    Ttr (dpow p k) = ((k : ℂ) + 1) • dpow p (k + 1) := by
  obtain ⟨i, m⟩ := p
  have hnat : (m + k + 1) * (m + k).choose k = (m + k + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (m + k) k
  have hcast : (((m + k).choose k : ℕ) : ℂ) * (((m + k + 1 : ℕ)) : ℂ)
      = ((k : ℂ) + 1) * (((m + k + 1).choose (k + 1) : ℕ) : ℂ) := by
    have h := congrArg (fun t : ℕ => (t : ℂ)) hnat
    push_cast at h ⊢
    linear_combination h
  rw [dpow, dpow, map_smul, Ttr_gv, smul_smul, smul_smul,
    show m + (k + 1) = m + k + 1 from by omega, hcast]

/-- Left multiplication is linear in the multiplier. -/
theorem leftMulU_smul (M : MIdeal D) (c : ℂ) (A : TR ι) :
    leftMulU M (c • A) = c • leftMulU M A := by
  refine LinearMap.ext (fun x => ?_)
  obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [leftMulU_mk, LinearMap.smul_apply, leftMulU_mk, smul_mul_assoc,
    Submodule.Quotient.mk_smul]

/-- The descended translation operator commutes with a left multiplication up to the left
multiplication by the derivative: `[T, leftMul A] = leftMul (T A)`.  This is the derivation
property of `Ttr`, descended, and it is what makes the creation half `T`-covariant. -/
theorem TrU_leftMulU (M : MIdeal D) (A : TR ι) :
    TrU M * leftMulU M A - leftMulU M A * TrU M = leftMulU M (Ttr A) := by
  refine LinearMap.ext (fun x => ?_)
  obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, TrU, descendU_mk, leftMulU_mk]
  rw [Ttr_mul, ← Submodule.Quotient.mk_sub, add_sub_cancel_left]

/-- **The creation half of the generating field** `Y(Tᵐaⁱ/m!, z)`: for `j ≥ 0` the
`zʲ`-coefficient is left multiplication by the divided power `Tʲa/j!`; the annihilation range is
set to zero, since it is not constructed in this file. -/
noncomputable def creHalf (M : MIdeal D) (p : GenIdx ι) : FormalDist (End ℂ (UR M)) :=
  fun j => if 0 ≤ j then leftMulU M (dpow p j.toNat) else 0

theorem creHalf_of_nonneg (M : MIdeal D) (p : GenIdx ι) {j : ℤ} (hj : 0 ≤ j) :
    creHalf M p j = leftMulU M (dpow p j.toNat) := if_pos hj

theorem creHalf_of_neg (M : MIdeal D) (p : GenIdx ι) {j : ℤ} (hj : j < 0) :
    creHalf M p j = 0 := if_neg (by omega)

/-- The creation half is lower truncated (trivially: it vanishes below `0`). -/
theorem creHalf_isField (M : MIdeal D) (p : GenIdx ι) : IsField (creHalf M p) :=
  fun x => ⟨0, fun j hj => by rw [creHalf_of_neg M p hj]; rfl⟩

/-- The `z⁰`-mode of the creation half is left multiplication by the generator itself. -/
theorem creHalf_zero_mk (M : MIdeal D) (p : GenIdx ι) (X : TR ι) :
    creHalf M p 0 (Submodule.Quotient.mk X) = Submodule.Quotient.mk (gv p * X) := by
  rw [creHalf_of_nonneg M p (le_refl 0), show (0 : ℤ).toNat = 0 from rfl, dpow_zero, leftMulU_mk]

/-- The creation half annihilates the vacuum in negative degree (trivially). -/
theorem creHalf_vac_neg (M : MIdeal D) (p : GenIdx ι) {j : ℤ} (hj : j < 0) :
    creHalf M p j (vacU M) = 0 := by rw [creHalf_of_neg M p hj]; rfl

/-- **The creation half is `T`-covariant throughout the creation range.**  (The covariance
identity at `m = -1` involves the annihilation mode `a₍₀₎` and is therefore *not* available
here — that is exactly the missing half.) -/
theorem creHalf_cov_nonneg (M : MIdeal D) (p : GenIdx ι) {m : ℤ} (hm : 0 ≤ m) :
    TrU M * creHalf M p m - creHalf M p m * TrU M = ((m + 1 : ℤ)) • creHalf M p (m + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
  rw [creHalf_of_nonneg M p hm, creHalf_of_nonneg M p (by omega : (0 : ℤ) ≤ (n : ℤ) + 1),
    TrU_leftMulU, Int.toNat_natCast, show ((n : ℤ) + 1).toNat = n + 1 from by omega,
    Ttr_dpow, leftMulU_smul, ← Int.cast_smul_eq_zsmul ℂ ((n : ℤ) + 1)]
  push_cast
  rfl

/-! ## §8  Non-vacuity

Everything above would be formally true and completely empty if `M` were all of `T(R)`.  What
rules that out is *not* PBW: the augmentation `T(R) → ℂ` that kills every generator also kills
every relation — the quantum-commutator terms are quadratic in the generators, and every OPE term
carries at least one `T`, whose image lies in the augmentation ideal.  So `1 ∉ MRbot`. -/

/-- The augmentation `T(R) → ℂ`, killing every generator. -/
noncomputable def aug : TR ι →ₐ[ℂ] ℂ := FreeAlgebra.lift ℂ (fun _ => (0 : ℂ))

@[simp] theorem aug_gv (p : GenIdx ι) : aug (gv p) = 0 := by
  rw [gv_eq, aug, FreeAlgebra.lift_ι_apply]

/-- The augmentation kills the image of `T`: `T` maps `T(R)` into the augmentation ideal. -/
theorem aug_Ttr (x : TR ι) : aug (Ttr x) = 0 := by
  induction x using FreeAlgebra.induction with
  | grade0 r => rw [Algebra.algebraMap_eq_smul_one, map_smul, Ttr_one, smul_zero, map_zero]
  | grade1 p => rw [← gv_eq, Ttr_gv, map_smul, aug_gv, smul_zero]
  | mul a b ha hb => rw [Ttr_mul, map_add, map_mul, map_mul, ha, hb, mul_zero, zero_mul, add_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

/-- Positive powers of `T` also land in the augmentation ideal. -/
theorem aug_Ttr_pow (m : ℕ) (x : TR ι) : aug (((Ttr : End ℂ (TR ι)) ^ (m + 1)) x) = 0 := by
  rw [Ttr_pow_succ_left]; exact aug_Ttr _

/-- The augmentation kills every relation. -/
theorem aug_rel (D : OPEData ι) (p q : GenIdx ι) : aug (rel D p q) = 0 := by
  have h1 : aug (gv p * gv q) = 0 := by rw [map_mul, aug_gv, zero_mul]
  have h2 : aug (koszul (D.par p.1) (D.par q.1) • (gv q * gv p)) = 0 := by
    rw [map_smul, map_mul, aug_gv, zero_mul, smul_zero]
  have h3 : aug (opeInt D p q) = 0 := by
    rw [opeInt, map_sum]
    exact Finset.sum_eq_zero (fun n _ => by rw [map_smul, aug_Ttr_pow, smul_zero])
  rw [rel, map_sub, map_sub, h1, h2, h3, sub_zero, sub_zero]

/-- **The vacuum survives any quotient the augmentation sees through.** -/
theorem vacU_ne_zero_of_aug (M : MIdeal D) (h : ∀ x ∈ M.car, aug x = 0) : vacU M ≠ 0 := by
  rw [vacU, Ne, Submodule.Quotient.mk_eq_zero]
  intro hmem
  have := h 1 hmem
  rw [map_one] at this
  exact one_ne_zero this

/-- The augmentation kills `MRbot`. -/
theorem aug_MRbot (D : OPEData ι) : ∀ x ∈ (MRbot D).car, aug x = 0 := by
  intro x hx
  change x ∈ MRbotCar D at hx
  rw [MRbotCar] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨B, p, q⟩, rfl⟩ := hz
      change aug (B * rel D p q) = 0
      rw [map_mul, aug_rel, mul_zero]
  | zero => rw [map_zero]
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

/-- **`|0⟩ ≠ 0`** in `T(R)/MRbot`, for every `OPEData`.  No PBW is used. -/
theorem vacU_ne_zero_bot (D : OPEData ι) : vacU (MRbot D) ≠ 0 :=
  vacU_ne_zero_of_aug (MRbot D) (aug_MRbot D)

/-- **`T(R)/MRbot ≠ 0`.**  This is the minimal non-vacuity statement.  It does *not* say that
the strong generators stay independent — that is PBW, deliberately out of scope — nor does it
transfer to the larger ideal `M(R)`, whose non-vacuity needs the same augmentation argument run
against the `D ≠ 1` generators, hence needs `N`. -/
theorem UR_nontrivial_bot (D : OPEData ι) : Nontrivial (UR (MRbot D)) :=
  ⟨⟨vacU (MRbot D), 0, vacU_ne_zero_bot D⟩⟩

/-! ## §9  Two bridges from OPE data to `reconstruct`'s hypotheses

These are stated for an arbitrary complex vector space, because they are useful to every example
in the library, not only to `U(R)`. -/

section Bridges

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- **`IsField` from a bounded-below weight filtration.**  If every vector lies in some `F d`,
if `F d = ⊥` for `d < 0`, and if the `zʲ`-coefficient of `a` shifts the filtration by `Δ + j` —
the conformal-weight bookkeeping `a₍ₙ₎ : F d → F (d + Δ - n - 1)` with `n = -j-1` — then `a` is a
field.  This is how the weight grading of `T(R)` will discharge `reconstruct`'s `hfield`. -/
theorem isField_of_filt (a : FormalDist (End ℂ V)) (F : ℤ → Submodule ℂ V) (Δ : ℤ)
    (hbot : ∀ d : ℤ, d < 0 → F d = ⊥)
    (hcov : ∀ x : V, ∃ d : ℤ, x ∈ F d)
    (hmap : ∀ (j d : ℤ) (x : V), x ∈ F d → a j x ∈ F (d + Δ + j)) :
    IsField a := by
  intro x
  obtain ⟨d, hd⟩ := hcov x
  refine ⟨-(d + Δ), fun j hj => ?_⟩
  have hmem : a j x ∈ F (d + Δ + j) := hmap j d x hd
  rw [hbot (d + Δ + j) (by omega)] at hmem
  exact hmem

/-- **`Local` from the singular OPE.**  If the mode commutator of `a` and `b` is the
falling-factorial sum over finitely many OPE-coefficient fields — i.e.
`[a₍ₚ₎, b₍q₎] = Σⱼ C(p,j)·(a₍ⱼ₎b)₍ₚ₊q₋ⱼ₎`, written here in the library's `z`-power indexing —
then `a` and `b` are mutually local.  This is `local_iff_deltaSum` read right to left, and it is
the exact bridge from an OPE table to `reconstruct`'s `hlocal`. -/
theorem local_of_ope (a b : FormalDist (End ℂ V)) (N : ℕ) (c : Fin N → FormalDist (End ℂ V))
    (h : ∀ m n : ℤ, a m * b n - b n * a m
        = ∑ j : Fin N, (∏ i ∈ Finset.range (j : ℕ), (-m - 1 - (i : ℤ))) • c j (m + n + 1 + j)) :
    Local a b := by
  refine ⟨N, ?_⟩
  refine (local_iff_deltaSum (bracketDist a b) N).mpr ⟨c, ?_⟩
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply, h m n, formalDist₂_sum_apply]
  exact Finset.sum_congr rfl (fun j _ => by rw [deltaDeriv_apply])

end Bridges

/-! ## §10  From generating fields to `reconstruct`

`reconstruct` asks for a family of pairwise-local fields whose creation states span.  A vertex
algebra given by strong generators supplies fields only for the *generators*; the fields of the
composite states are the iterated normal-ordered products.  This section closes that gap once and
for all, for an arbitrary cyclic module.

The locality of all word fields is *not* proved here by a hand-rolled Dong cascade — it is
`Core.LocalSystem.generated_local` applied to the set of generating fields.  (That machinery had
been proved and left unused in this library; this is its first application.) -/

section Generators

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

open VOA.Reconstruction

/-- The iterated normal-ordered product along a word in the generators, packaged with its
`IsField` witness. -/
noncomputable def wordFldF {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) : List κ → Fld V
  | [] => Fld.one
  | (i :: l) => Fld.nprod ⟨gen i, hgen i⟩ (wordFldF gen hgen l)

/-- The field attached to a word in the generators. -/
noncomputable def wordFld {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (l : List κ) : FormalDist (End ℂ V) :=
  (wordFldF gen hgen l).1

/-- Word fields are fields. -/
theorem wordFld_isField {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (l : List κ) : IsField (wordFld gen hgen l) :=
  (wordFldF gen hgen l).2

/-- Every word field is generated, in the sense of `Core.LocalSystem`, from the generating set. -/
theorem wordFldF_gen {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (l : List κ) :
    wordFldF gen hgen l ∈ Generated (Set.range (fun i => (⟨gen i, hgen i⟩ : Fld V))) := by
  induction l with
  | nil => exact one_mem_generated
  | cons i l ih => exact nprod_mem_generated (subset_generated ⟨i, rfl⟩) ih

/-- **Pairwise locality of all word fields**, straight out of `generated_local`: locality of
the *generators* is all that must be checked. -/
theorem wordFld_local {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (hloc : ∀ i j, Local (gen i) (gen j)) (l₁ l₂ : List κ) :
    Local (wordFld gen hgen l₁) (wordFld gen hgen l₂) := by
  refine generated_local (S := Set.range (fun i => (⟨gen i, hgen i⟩ : Fld V))) ?_
    (wordFldF_gen gen hgen l₁) (wordFldF_gen gen hgen l₂)
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
  exact hloc i j

/-- The state attached to a word: the iterated `(-1)`-modes applied to the vacuum. -/
noncomputable def wordSt {κ : Type*} (gen : κ → FormalDist (End ℂ V)) (vac : V) : List κ → V
  | [] => vac
  | (i :: l) => gen i 0 (wordSt gen vac l)

/-- Word fields annihilate the vacuum in negative degree. -/
theorem wordFld_vac_neg {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (vac : V)
    (hvn : ∀ i, ∀ q : ℤ, q < 0 → gen i q vac = 0) (l : List κ) :
    ∀ q : ℤ, q < 0 → wordFld gen hgen l q vac = 0 := by
  induction l with
  | nil =>
      intro q hq
      change (idField : FormalDist (End ℂ V)) q vac = 0
      rw [idField, if_neg (by omega : ¬ q = 0)]; rfl
  | cons i l ih =>
      intro q hq
      exact nprod_vacuum_neg_gen (hgen i) (wordFld_isField gen hgen l) vac (hvn i) ih hq

/-- Word fields create the word states. -/
theorem wordFld_vac_base {κ : Type*} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (vac : V)
    (hvn : ∀ i, ∀ q : ℤ, q < 0 → gen i q vac = 0) (l : List κ) :
    wordFld gen hgen l 0 vac = wordSt gen vac l := by
  induction l with
  | nil =>
      change (idField : FormalDist (End ℂ V)) 0 vac = vac
      rw [idField, if_pos rfl]; rfl
  | cons i l ih =>
      change nprod (hgen i) (wordFld_isField gen hgen l) 0 vac = _
      rw [nprod_vacuum_base_gen (hgen i) (wordFld_isField gen hgen l) vac (hvn i)
        (wordFld_vac_neg gen hgen vac hvn l), ih]
      rfl

/-- Word fields are `T`-covariant. -/
theorem wordFld_cov {κ : Type*} {T : End ℂ V} (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i)) (hcov : ∀ i, DCovariant T (gen i)) (l : List κ) :
    DCovariant T (wordFld gen hgen l) := by
  induction l with
  | nil =>
      have e : ∀ j : ℤ, (idField : FormalDist (End ℂ V)) j
          = if j = 0 then (1 : End ℂ V) else 0 := fun _ => rfl
      intro m
      change T * (idField : FormalDist (End ℂ V)) m - (idField : FormalDist (End ℂ V)) m * T
          = ((m + 1 : ℤ)) • (idField : FormalDist (End ℂ V)) (m + 1)
      rw [e m, e (m + 1)]
      split_ifs with h0 h1 h1
      · omega
      · simp
      · rw [show (m + 1 : ℤ) = 0 from h1]; simp
      · simp
  | cons i l ih => exact DCovariant.nprod (hgen i) (wordFld_isField gen hgen l) (hcov i) ih

/-- **`reconstruct` from generating fields alone.**  Five properties of the generators plus
the spanning of the word states give the full all-states vertex operator map: VA3 creation, VA4
locality, VA5 regularity and translation covariance.  No property of the composite fields has to
be checked by hand. -/
theorem reconstruct_of_generators {κ : Type*} (vac : V) (T : End ℂ V)
    (gen : κ → FormalDist (End ℂ V))
    (hgen : ∀ i, IsField (gen i))
    (hloc : ∀ i j, Local (gen i) (gen j))
    (hvn : ∀ i, ∀ q : ℤ, q < 0 → gen i q vac = 0)
    (hTvac : T vac = 0)
    (hcov : ∀ i, DCovariant T (gen i))
    (hspan : Submodule.span ℂ (Set.range (wordSt gen vac)) = ⊤) :
    ∃ YA : V →ₗ[ℂ] FormalDist (End ℂ V),
      (∀ l : List κ, YA (wordSt gen vac l) = wordFld gen hgen l) ∧
      (∀ u : V, IsField (YA u)) ∧
      (∀ u v : V, Local (YA u) (YA v)) ∧
      (∀ u : V, (YA u) 0 vac = u) ∧
      (∀ u : V, ∀ q : ℤ, q < 0 → (YA u) q vac = 0) ∧
      (∀ u : V, DCovariant T (YA u)) :=
  reconstruct vac (wordSt gen vac) (wordFld gen hgen) T hspan
    (wordFld_isField gen hgen) (wordFld_local gen hgen hloc)
    (wordFld_vac_base gen hgen vac hvn)
    (fun l q hq => wordFld_vac_neg gen hgen vac hvn l q hq)
    hTvac (wordFld_cov gen hgen hcov)

end Generators

/-! ## §11  The contract, and the vertex operator map on `T(R)/M`

`GenFields M` is *exactly* what remains to be constructed: De Sole–Kac Lemma 3.2 and §4.  It
asks for the generating fields on `T(R)/M` and five properties of them.  Two of the five are
already paid for by the left-ideal structure (`cre_mul`, `cre_neg`); `isFld` is weight
bookkeeping through `isField_of_filt`; `cov` is the derivation property for the creation half;
and `loc` is the mode commutator formula — the hard theorem.

`UR_YA` then produces the vertex operator map — with **no PBW and no basis** — which is the point
of the whole staging. -/

open VOA.Reconstruction

/-- **The contract.**  Everything the remaining construction (the recursive definition of the
nonnegative modes on `T(R)`, their `M`-invariance, and the mode commutator formula) has to
deliver, stated as data on `T(R)/M`.

⚠ This structure is **not** populated for a general `OPEData` anywhere in this file; see the
Status section of the module docstring.  Its purpose is to pin the remaining obligation down
exactly, and to show that nothing beyond it is needed. -/
structure GenFields {D : OPEData ι} (M : MIdeal D) where
  /-- the generating field `Y(Tᵏaⁱ/k!, z)`, for each basis vector of `R` -/
  fld : GenIdx ι → FormalDist (End ℂ (UR M))
  /-- lower truncation (from the weight filtration, via `isField_of_filt`) -/
  isFld : ∀ p, IsField (fld p)
  /-- mutual locality of the *generating* fields — the hard output, De Sole–Kac §4 -/
  loc : ∀ p q, Local (fld p) (fld q)
  /-- the creation half is the one **already constructed** in §7: for `j ≥ 0` the mode is left
  multiplication by a divided power.  So the only freedom left in `fld` is the annihilation
  range `j < 0`, i.e. the modes `a₍ₙ₎` with `n ≥ 0` — which is exactly Lemma 3.2. -/
  cre : ∀ (p : GenIdx ι) (j : ℤ), 0 ≤ j → fld p j = creHalf M p j
  /-- the generators annihilate `|0⟩` in negative degree -/
  cre_neg : ∀ p, ∀ j : ℤ, j < 0 → (fld p) j (vacU M) = 0
  /-- covariance under the translation operator already constructed above -/
  cov : ∀ p, DCovariant (TrU M) (fld p)

variable {M : MIdeal D} (G : GenFields M)

/-- The `z⁰`-mode of a generating field is left multiplication by the generator — a consequence
of `GenFields.cre` and the construction of `creHalf`. -/
theorem GenFields.cre_mul (p : GenIdx ι) (X : TR ι) :
    (G.fld p) 0 (Submodule.Quotient.mk X) = Submodule.Quotient.mk (gv p * X) := by
  rw [G.cre p 0 (le_refl 0), creHalf_zero_mk]

/-- The word states built by the generic machinery are the images of the monomials of `T(R)` —
because the `z⁰`-modes are left multiplication. -/
theorem wordSt_eq_wstU (l : List (GenIdx ι)) :
    wordSt G.fld (vacU M) l = wstU M (FreeMonoid.ofList l) := by
  induction l with
  | nil =>
      change vacU M = _
      rw [vacU, wstU, show (FreeMonoid.ofList ([] : List (GenIdx ι))) = 1 from rfl, wbasis_one]
  | cons p l ih =>
      change G.fld p 0 (wordSt G.fld (vacU M) l) = _
      rw [ih, wstU, G.cre_mul, wstU, gv, ← wbasis_mul]
      rfl

/-- **`hspan`**: the word states of the generating fields span `T(R)/M`.  No PBW. -/
theorem wordSt_span_UR : Submodule.span ℂ (Set.range (wordSt G.fld (vacU M))) = ⊤ := by
  refine top_unique ?_
  rw [← wstU_span M]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, rfl⟩
  exact Submodule.subset_span ⟨FreeMonoid.toList w, wordSt_eq_wstU G (FreeMonoid.toList w)⟩

/-- **The payoff.**  From the contract alone — no PBW, no basis, no linear independence
anywhere — the all-states vertex operator map `YA` on `T(R)/M`, satisfying VA3 creation, VA4
locality, VA5 regularity, and covariance under the translation operator `TrU` constructed above.

This is the theorem the staging was designed to reach: the vertex algebra structure on an algebra
presented by strong generators and singular OPEs does *not* pass through the PBW theorem.
⚠ It is conditional on `GenFields M`, which this file does not construct. -/
theorem UR_YA :
    ∃ YA : UR M →ₗ[ℂ] FormalDist (End ℂ (UR M)),
      (∀ l : List (GenIdx ι), YA (wordSt G.fld (vacU M) l) = wordFld G.fld G.isFld l) ∧
      (∀ u : UR M, IsField (YA u)) ∧
      (∀ u v : UR M, Local (YA u) (YA v)) ∧
      (∀ u : UR M, (YA u) 0 (vacU M) = u) ∧
      (∀ u : UR M, ∀ j : ℤ, j < 0 → (YA u) j (vacU M) = 0) ∧
      (∀ u : UR M, DCovariant (TrU M) (YA u)) :=
  reconstruct_of_generators (vacU M) (TrU M) G.fld G.isFld G.loc G.cre_neg (TrU_vac M) G.cov
    (wordSt_span_UR G)

/-! ### A consistency witness for the contract

⚠ The following says only that `GenFields` is *inhabitable*, so that `UR_YA` is not vacuously
true as a schema.  It is the empty set of strong generators, where every obligation holds because
there is nothing to check.  It is **not** evidence that `GenFields` can be populated for an
`OPEData` that has generators.

**What is open.**  The open step is not
populating `GenFields` per se — `Examples.NonlinearVirasoroTransport.genFieldsVir` does that for
`virasoroOPE`.  It is that **`MRbot` is the wrong ideal**: over it the contract is refutable
(`Core.NonlinearVirasoro.not_nonempty_genFields_MRbot_virasoro`), because `cre` pins the entire
creation quadrant to left multiplication and a *left* ideal cannot make the resulting mode
commutator a delta-sum.  The right ideal is the two-sided `MRtwo` (= De Sole–Kac's `M(R)` for a
linear datum).  What genuinely remains open is De Sole–Kac Lemma 3.2 for nonlinear data, De
Sole–Kac §4 (locality from the OPE, via `local_of_ope`), and `MRtwo = ker Φ` beyond the Virasoro case
(`Examples.NonlinearVirasoroGenuine.MRtwo_eq_ker_PhiVir`). -/

/-- The `OPEData` with no strong generators. -/
def emptyOPE : OPEData Empty where
  wt := fun i => i.elim
  wt_pos := fun i => i.elim
  par := fun i => i.elim
  ope := fun i => i.elim
  ope_wt := fun i => i.elim

/-- ⚠ Consistency witness only: the contract is inhabitable (vacuously, with no generators). -/
def emptyGenFields : GenFields (MRbot emptyOPE) where
  fld := fun p => p.1.elim
  isFld := fun p => p.1.elim
  loc := fun p => p.1.elim
  cre := fun p => p.1.elim
  cre_neg := fun p => p.1.elim
  cov := fun p => p.1.elim

/-- The quotient carrying that trivial instance is nonzero, so `UR_YA` applied to it produces a
vertex operator map on a space that is not `0`.  (It is one-dimensional: the trivial vertex
algebra.) -/
theorem emptyUR_nontrivial : Nontrivial (UR (MRbot emptyOPE)) := UR_nontrivial_bot emptyOPE

/-! ### The Virasoro instance, exercised

Three checks that the interface is not merely well typed: the extended bracket reproduces the
user's table on the bottom generators, sesquilinearity in the divided powers is *computed* rather
than assumed, and the quotient built from the data is nonzero.

⚠ None of this says that `T(R)/MRbot (virasoroOPE c)` is the Virasoro vertex algebra.  It is a
strictly larger quotient (§7), and no vertex algebra structure is constructed on it here — indeed
`Core.NonlinearVirasoro.not_nonempty_genFields_MRbot_virasoro` shows none can be, by this route.
(Hand computation, *not* machine-checked: at conformal weight `7`, `T(R)` has the `8` ordered
words of weight `7` and `MRbot` the `3` independent elements `rel(0,3)`, `rel(1,2)`,
`gv₀·rel(0,1)`, so `dim (T(R)/MRbot)₇ = 5`, whereas `dim V(c,0)₇ = 4`, the number of partitions of
`7` into parts `≥ 2`.  The two sides first differ at weight `7`, which is why these low-weight
smoke tests show nothing wrong.) -/

/-- The central term of the Virasoro OPE, read back through the extended bracket. -/
theorem virasoro_brk_three (c : ℂ) :
    brk (virasoroOPE c) ((), 0) ((), 0) 3 = (c / 2) • (1 : TR Unit) := by
  rw [brk_bot]
  rfl

/-- Sesquilinearity is **derived**: `(TL)₍₁₎L = -L₍₀₎L = -TL`, obtained from `brk_left` and the
user's table, with nothing about divided powers supplied by the user. -/
theorem virasoro_brk_T (c : ℂ) :
    brk (virasoroOPE c) ((), 1) ((), 0) 1 = -(gv ((), 1) : TR Unit) := by
  have h := brk_left (virasoroOPE c) () 0 ((), 0) 1
  rw [brk_bot] at h
  rw [show ((0 : ℕ) : ℂ) + 1 = 1 from by norm_num, one_smul] at h
  rw [h, show ((1 : ℕ) : ℂ) = 1 from by norm_num, neg_one_smul]
  rfl

/-- The quotient carrying the Virasoro data is nonzero. -/
theorem virasoro_UR_nontrivial (c : ℂ) : Nontrivial (UR (MRbot (virasoroOPE c))) :=
  UR_nontrivial_bot (virasoroOPE c)

end VOA.NonlinearConformal
