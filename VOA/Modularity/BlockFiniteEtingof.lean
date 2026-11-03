/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.QuasiLisseFinite

/-!
# The Etingof–Schedler substitution, closed at every rung of the block-growth chain

`Modules.QuasiLisseFinite` carries the Arakawa–Kawasetsu (arXiv:1610.05865) improvement of Zhu's
finite-generation argument: `C2Cofinite W` may be replaced by the weaker `EtingofFinite W`
throughout the chain that ends in `Modularity.BlockGrowth.onePointSubexp_of_c2`.  It proves the
Etingof-hypothesis form of every rung, and it checks the *top* rung against the old one
(`onePointSubexp_of_c2_via_etingofFinite`).

This file completes that audit downwards.  For each intermediate rung it records

* the `EtingofFinite` form, where `QuasiLisseFinite` stated only a hypothesis-free port taking the
  finiteness as an argument (`fg_blockSpanS_of_fg`, `exists_system_matrix_of_fg`), and
* the **subsumption check**: the *verbatim statement* of the existing `C2Cofinite` theorem,
  re-proved through the Etingof route.  Each such check is one line, and each is the assertion that
  the substitution generalises rather than sidesteps — a theorem `P → Q` proved from `P → R` and
  `R → Q` cannot be a sideways restatement of `P → Q`.

Nothing here is new mathematics; every proof is a composition of results already in the repository.
The content is the *verification*, in the kernel, that the chain

  `C2Cofinite ⟹ EtingofFinite ⟹ (spanning mod O₂P) ⟹ fg block span ⟹ system ⟹ subexponential`

reproduces the old chain rung by rung, with no gap and no strengthening smuggled in.

## Main results

* `exists_homog_gen_of_c2_via_etingofFinite` — the spanning datum, rung 1;
* `fg_blockSpan_of_c2_via_etingofFinite` — **the crux rung**: `Modularity.FormalBlockFinite.
  fg_blockSpan` verbatim, recovered from `fg_blockSpan_of_etingofFinite`.  `fg_blockSpan` is the
  only place `C2Cofinite` enters **the `onePointSubexp_of_c2` chain**, so this single line is the
  whole substitution *for that chain*.  It is **not** the only entry point of `C2Cofinite` into
  `Modularity/` as a whole: `finiteDimensional_A_of_C2Cofinite` and
  `moduleFinite_quot_blockRelSpanE` are two further live entry points, neither routed through
  `fg_blockSpan`, and neither generalised here;
* `fg_blockSpanS_of_etingofFinite`, `fg_blockSpanS_of_c2_via_etingofFinite`;
* `exists_system_matrix_of_etingofFinite`, `exists_system_matrix_of_c2_via_etingofFinite`;
* `subexponential_block_of_c2_via_etingofFinite`;
* `trivial_fg_blockSpanS_adjoint`, `trivial_exists_system_matrix_adjoint` — the new statements
  instantiated with **all hypotheses discharged**, so none of them is vacuous.

## ⚠ What is *not* claimed

`EtingofFinite` is an axiomatized hypothesis, not a theorem: see the warning block of
`Modules.PoissonTrace`.  Etingof–Schedler is not formalized here, quasi-lisseness is not defined
here, and the only VOA at which `EtingofFinite` is discharged unconditionally in this repository is
the trivial one — which is already `C₂`-cofinite.  So the gain is the implication, not a new
example.

Nor is any modular linear differential equation proved.  Arakawa–Kawasetsu's conclusion is weaker
than Zhu's: characters are among the solutions of *some* MLDE, not a modular representation.  What
is delivered here is the growth datum `OnePointSubexp`, exactly the interface
`Modularity.BlockGrowth` already served, and nothing beyond it.

⚠ The literal quotient form `Module.Finite (↥GSeries) ((𝒱G 𝒱) ⧸ blockRelSpanG W)` of
`Modularity.BlockRelSpanG.moduleFinite_quot_blockRelSpanG` is **not** restated here.  It cannot be:
outside `Modularity.BlockRelSpanG`, `Submodule (↥GSeries) (𝒱G 𝒱)` elaborates with
`TensorProduct.addCommMonoid` while `Submodule.hasQuotient` demands
`AddCommGroup.toAddCommMonoid`, and instance synthesis for `HasQuotient` fails.  This was verified
directly, and it is the obstruction already recorded in
`exists_finite_gen_sup_blockRelSpanG_of_etingofFinite`, whose finite-generating-family form is the
same assertion and is what every consumer here uses.

## Status
Proved, `sorry`-free, axiom-clean (`propext` / `Classical.choice` / `Quot.sound` only); the
theorem `VOA.pbw` is not used.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Chain

variable (W : VertexOperatorAlgebra 𝒱)

/-! ## Rung 1 — the spanning datum

`Modularity.C2Extraction.exists_homog_gen_of_C2Cofinite` produces a finite homogeneous
positive-weight family spanning `𝒱` modulo `O₂ W`.  Its Etingof form
(`exists_homog_gen_of_etingofFinite`) produces one spanning modulo the *larger* `O₂P W = O₂ W +
{𝒱,𝒱}`, so the conclusions differ and the two are not directly comparable; what is comparable is
that the weaker hypothesis still yields the datum the downstream machinery consumes.
-/

/-- **Rung 1, subsumption.**  From `C2Cofinite` one still obtains the Arakawa–Kawasetsu spanning
datum — a finite homogeneous family of strictly positive conformal weight spanning `𝒱` modulo
`O₂P W = O₂ W + {𝒱,𝒱}`.  Routed through `EtingofFinite`, so this is the rung-1 statement that the
Etingof hypothesis is genuinely weaker: `C2Cofinite` gives it, and (mathematically, though no
witness is available in this repository) not conversely. -/
theorem exists_homog_gen_of_c2_via_etingofFinite (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂P W :=
  exists_homog_gen_of_etingofFinite W (EtingofFinite_of_C2Cofinite W hC2)

/-! ## Rung 2 — the crux: the `GSeries`-span of a formal block

`C2Cofinite` enters **the `onePointSubexp_of_c2` chain** at exactly one place,
`Modularity.FormalBlockFinite.fg_blockSpan`, and inside that proof at exactly one line, the call to
`exists_homog_gen_of_C2Cofinite`.  Everything below rung 2 in `Modularity.BlockSystem` and
`Modularity.BlockGrowth` is `C₂`-free.  So the theorem immediately below *is* the substitution
for that chain.  The scoping matters: across `Modularity/` as a whole `C2Cofinite` has further
live entry points (`finiteDimensional_A_of_C2Cofinite`, `moduleFinite_quot_blockRelSpanE`), so
this is not a claim that the modularity development is `C₂`-free after this file.
-/

/-- **Rung 2, subsumption — the whole substitution in one line.**  The verbatim statement of
`Modularity.FormalBlockFinite.fg_blockSpan`, re-proved from `fg_blockSpan_of_etingofFinite`.

Because `fg_blockSpan` is the unique point of entry of `C2Cofinite` into the
`onePointSubexp_of_c2` chain specifically, the existence of this proof is exactly the claim that
`Modules.QuasiLisseFinite` generalises *that* chain rather than proving something adjacent to it.
It says nothing about the other `C2Cofinite` consumers elsewhere in `Modularity/`. -/
theorem fg_blockSpan_of_c2_via_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    (Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))).FG :=
  fg_blockSpan_of_etingofFinite W hsupp hS hzero (EtingofFinite_of_C2Cofinite W hC2)

/-! ## Rung 3 — the `SubexpPS`-span

`Modules.QuasiLisseFinite.fg_blockSpanS_of_fg` takes the `GSeries`-finiteness as an argument rather
than deriving it, so the `EtingofFinite` form of `Modularity.BlockSystem.fg_blockSpanS` is not
stated there.  It is here.
-/

/-- **Rung 3, Etingof form.**  `Modularity.BlockSystem.fg_blockSpanS` with `C2Cofinite` weakened to
`EtingofFinite`: the block span is a finitely generated `SubexpPS`-module. -/
theorem fg_blockSpanS_of_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    (blockSpanS hsupp).FG :=
  fg_blockSpanS_of_fg hsupp (fg_blockSpan_of_etingofFinite W hsupp hS hzero hE)

/-- **Rung 3, subsumption.**  The verbatim statement of `Modularity.BlockSystem.fg_blockSpanS`,
recovered through the Etingof route. -/
theorem fg_blockSpanS_of_c2_via_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    (blockSpanS hsupp).FG :=
  fg_blockSpanS_of_etingofFinite W hsupp hS hzero (EtingofFinite_of_C2Cofinite W hC2)

/-! ## Rung 4 — the first-order system

⚠ This is the rung where `Modularity.UniCollapse` refutes the naive per-vector unitriangular
reading of Zhu Lemma 4.4.4 (= Arakawa–Kawasetsu Lemmas 5.4–5.6): that reading forces
`Z(L[-n]x) = 0` for all `n ≥ 3`.  The repository's replacement is the first-order **system** below,
and the Etingof substitution changes nothing about it — `qD_mem_blockSpanS` and
`subexponential_of_system` never mentioned `C₂` at all.
-/

/-- **Rung 4, Etingof form.**  `Modularity.BlockSystem.exists_system_matrix` with `C2Cofinite`
weakened to `EtingofFinite`: a finite `SubexpPS`-generating family of the block span on which
`qDeriv` acts by a matrix, together with the expansion of every block value in it. -/
theorem exists_system_matrix_of_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    ∃ (g : ℕ) (y : Fin g → ↥(QSeriesAt hbase)) (A : Fin g → Fin g → ↥SubexpPS),
      (∀ k, qD hbase (y k) = ∑ l, A k l • y l) ∧
      (∀ v : 𝒱, ∃ c : Fin g → ↥SubexpPS,
        blockRestrict hsupp v = ∑ l, c l • y l) :=
  exists_system_matrix_of_fg W hsupp hS (fg_blockSpanS_of_etingofFinite W hsupp hS hzero hE)

/-- **Rung 4, subsumption.**  The verbatim statement of
`Modularity.BlockSystem.exists_system_matrix`, recovered through the Etingof route. -/
theorem exists_system_matrix_of_c2_via_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (y : Fin g → ↥(QSeriesAt hbase)) (A : Fin g → Fin g → ↥SubexpPS),
      (∀ k, qD hbase (y k) = ∑ l, A k l • y l) ∧
      (∀ v : 𝒱, ∃ c : Fin g → ↥SubexpPS,
        blockRestrict hsupp v = ∑ l, c l • y l) :=
  exists_system_matrix_of_etingofFinite W hsupp hS hzero (EtingofFinite_of_C2Cofinite W hC2)

/-! ## Rung 5 — subexponential growth of block values -/

/-- **Rung 5, subsumption.**  The verbatim statement of
`Modularity.BlockGrowth.subexponential_block_of_c2`, recovered through the Etingof route. -/
theorem subexponential_block_of_c2_via_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (v : 𝒱) :
    Subexponential (fun n : ℕ => ‖S v (hbase + (n : ℂ))‖) :=
  subexponential_block_of_etingofFinite W hsupp hS hzero (EtingofFinite_of_C2Cofinite W hC2) v

end Chain

/-! ## Non-vacuity

Rung 6, `onePointSubexp_of_c2_via_etingofFinite`, is already in `Modules.QuasiLisseFinite`, as is
its instantiation `trivial_onePointSubexp_adjoint`.  The two witnesses below discharge *every*
hypothesis of the new rung-3 and rung-4 statements above at the trivial VOA `ℂ𝟙`, so neither is
vacuously true.

The trivial VOA is `C₂`-cofinite, so these witnesses are sanity checks.  A non-`C₂`-cofinite VOA
with `EtingofFinite` is available unconditionally, `L_{-4/3}(𝔰𝔩₂)` (see `Modules.QuasiLisseFinite`
§7; `Modularity.AKSl2Instance.finiteDimensional_analyticBlocks_simpleSl2QL`).
-/

/-- The support datum of the trivial VOA's adjoint one-point function, stated for the **linear
map** `torusOnePointHom` rather than the bare function `torusOnePoint`, which is the shape
`blockSpanS` and `blockRestrict` consume.  The two agree by `rfl`
(`Modularity.ZhuBlockConditions.torusOnePointHom_apply`). -/
theorem trivial_adjoint_onePoint_supp (v : LatGen.LatModuleGen (stdLattice 0)) :
    torusOnePointHom (adjointModule trivialVOA) v
      ∈ QSeriesAt (0 - trivialVOA.centralCharge / 24) :=
  torusOnePoint_mem_QSeriesAt trivialVOA (adjointModule trivialVOA)
    (adjoint_hasConformalWeight trivialVOA trivialVacuum_ne_zero) v

/-- **Rung 3, instantiated.**  The block span of the trivial VOA's adjoint one-point function is
a finitely generated `SubexpPS`-module, obtained through the Arakawa–Kawasetsu route.  All
hypotheses are discharged. -/
theorem trivial_fg_blockSpanS_adjoint :
    (blockSpanS trivial_adjoint_onePoint_supp).FG :=
  fg_blockSpanS_of_etingofFinite trivialVOA trivial_adjoint_onePoint_supp
    (torusOnePointHom_isFormalBlock (adjointModule trivialVOA))
    trivial_vacuumGradeZero trivial_etingofFinite

/-- **Rung 4, instantiated.**  The trivial VOA's adjoint one-point function satisfies a
first-order system over `SubexpPS`, obtained through the Arakawa–Kawasetsu route.  All hypotheses
are discharged. -/
theorem trivial_exists_system_matrix_adjoint :
    ∃ (g : ℕ)
      (y : Fin g → ↥(QSeriesAt (0 - trivialVOA.centralCharge / 24)))
      (A : Fin g → Fin g → ↥SubexpPS),
      (∀ k, qD (0 - trivialVOA.centralCharge / 24) (y k) = ∑ l, A k l • y l) ∧
      (∀ v : LatGen.LatModuleGen (stdLattice 0), ∃ c : Fin g → ↥SubexpPS,
        blockRestrict trivial_adjoint_onePoint_supp v = ∑ l, c l • y l) :=
  exists_system_matrix_of_etingofFinite trivialVOA trivial_adjoint_onePoint_supp
    (torusOnePointHom_isFormalBlock (adjointModule trivialVOA))
    trivial_vacuumGradeZero trivial_etingofFinite

end VOA
