# LeanVOA: Vertex Operator Algebras in Lean

**Fedor K. Popov** and **Leonardo Rastelli** (Simons Center for Geometry and Physics and C. N. Yang Institute for
Theoretical Physics, Stony Brook University)

LeanVOA is a Lean 4 library for the theory of vertex operator algebras (VOAs), together with a companion book that
sets each formalized result next to its textbook statement. The library constructs the Moonshine module V♮, proves
the Conway–Norton moonshine conjecture for every automorphism of V♮ (Borcherds' theorem), and identifies Aut V♮ with
the Monster, given one named theorem of AxiomMath's CFSG library. It also formalizes Zhu's modular invariance, Huang's tensor categories with the Verlinde formula, the Gannon–Rayhaun
classification of c = 1 VOAs, and classical freeness of the boundary admissible L<sub>k</sub>(sl₂) (Arakawa–Dai) and
of the minimal models M(2,2m+3) (van Ekeren–Heluani). It also contains new results: graded first-order rigidity of
all Virasoro minimal models and of L<sub>k</sub>(sl₂) at every admissible level; classical freeness of
L<sub>−3/2</sub>(sl₃), and of the other members of the Deligne series under stated assumptions; and a proof that
graded unitarity of the boundary admissible L<sub>k</sub>(sl₂) implies that of the minimal models M(2,2n+1). The
library declares no axiom of its own.

- **Release:** v1.05 (tag `v1.05`; previous release v1.0)
- **Book:** [`Notes/book.pdf`](Notes/book.pdf), *Vertex Operator Algebras in Lean* (sources in
  [`Notes/Textbook/`](Notes/Textbook/))
- **Brief:** [`Notes/brief.pdf`](Notes/brief.pdf), the book's headline statements with their Lean names and verbatim
  Lean, without proofs
- **Release note:** [`Notes/arxiv.tex`](Notes/arxiv.tex)
- **License:** Apache-2.0

The library formalizes, on top of Mathlib, the algebraic theory of VOAs: formal calculus and locality from first
principles, the VOA axioms and the Borcherds identity, the standard constructions (Heisenberg, Virasoro, affine,
lattice), the module theory, Zhu's algebra and modular invariance, Huang's tensor categories, and several recent
theorems from the literature. The book is the reviewed account of the library: for each definition and theorem it
gives the mathematical statement, the Lean declaration copied verbatim from the source, and a dictionary that decodes
every convention and hypothesis.

VOAs are defined in the general sense of Frenkel–Lepowsky–Meurman and Lepowsky–Li (`GradedVertexOperatorAlgebra`),
and the theory is developed for VOAs of CFT type, V₀ = ℂ𝟙 and V<sub>n</sub> = 0 for n < 0 (`VertexOperatorAlgebra`).

## Scope

The headline results, with what each assumes. Every listed declaration depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); the book gives the precise statements and conventions. The only result
stated with a hypothesis that is a theorem proved elsewhere is the Monster identification: `GmatEqAutO` is
AxiomMath's theorem `CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess` (commit `69cb972f`, Lean v4.35).
Its proof, about 15,500 files through the Baby Monster recognition, does not run on this library's toolchain. It
will be imported when the library moves to Lean v4.35. Our hypothesis is their statement after renaming (the ported
definitions were compared declaration by declaration with that commit). The literature milestones on that proof's path
that we inspected (the Stroth–Leon–Sims recognition of the Baby Monster, Goldschmidt's theorem) are theorems in their
library, not axioms. We have not re-run `#print axioms` on their theorem, which needs a v4.35 build.

### Foundations and classical theorems

| Result | Lean name(s) |
|---|---|
| **Foundations.** VOAs of CFT type, with the Borcherds identity derived from locality. Constructed examples: the Heisenberg VOA, the universal Virasoro VOA at every central charge, the universal affine VOA V<sup>k</sup>(sl₂), and the lattice VOA of every positive-definite even lattice. | `VOA.VertexOperatorAlgebra.borcherds`, `VOA.heisenbergVOA`, `VOA.VirModule.virasoroVOA`, `VOA.AffineVOA.affineSl2VOA_closed`, `VOA.LatGen.latticeVOAGen` |
| **Moonshine module.** The Frenkel–Lepowsky–Meurman module V♮, with no hypotheses: a simple VOA with c = 24, V♮₁ = 0 and dim V♮₂ = 196884, whose graded dimensions are the coefficients of j(τ) − 744. | `VOA.Moonshine.moonshine`, `VOA.Moonshine.hasSum_JShift` |
| **Monstrous moonshine (Conway–Norton, Borcherds).** For every automorphism g of V♮, the McKay–Thompson series T<sub>g</sub>(τ) = q<sup>−1</sup> + Σ tr(g \| V♮<sub>n+1</sub>) q<sup>n</sup> is the normalised Hauptmodul of a genus-zero group that contains some Γ₀(N) and is commensurable with SL₂(ℤ). No hypotheses. The proof follows Borcherds: the vertex algebra of the hyperbolic plane II<sub>1,1</sub>, the no-ghost theorem, the Monster Lie algebra as a Borcherds–Kac–Moody algebra, the twisted denominator identities, complete replicability, and a case-free proof that completely replicable series are Hauptmoduln. Aut V♮ is finite and every automorphism has rational traces. | `VOA.Moonshine.ConwayNorton.conwayNorton`, `VOA.Moonshine.ConwayNorton.M8.finite_autVnat`, `VOA.Moonshine.ConwayNorton.rationalTraces` |
| **The Monster acts on V♮.** AxiomMath's Monster is `AutO`, the automorphism group of their rational Griess algebra. Its definition is ported from their CFSG library. The Griess algebra of V♮ is that algebra tensored with ℂ. Every element of AxiomMath's generated group G<sub>mat</sub> = ⟨2<sup>1+24</sup>.Co₁, τ<sub>B</sub>⟩ acts on V♮, and moonshine holds for it, with no hypotheses. Aut V♮ is isomorphic to the subgroup of `AutO` acting on V♮, with no hypotheses and without Tits' theorem. Given AxiomMath's generation theorem G<sub>mat</sub> = `AutO`, carried as the named hypothesis `GmatEqAutO`, Aut V♮ ≅ `AutO` and moonshine holds for every element of the Monster. | `VOA.Moonshine.ConwayNorton.conwayNorton_gmat`, `VOA.Moonshine.ConwayNorton.nonempty_autVnat_mulEquiv_liftable`, `VOA.Moonshine.ConwayNorton.monstrousMoonshine` |
| **Zhu's modular invariance.** For a C₂-cofinite rational VOA, the torus one-point functions of the irreducible modules transform according to a representation of SL₂(ℤ). Instances with every hypothesis checked: all rank-one lattice VOAs and their ℤ₂-orbifolds. | `VOA.zhuModularity_canonical_of_C2Cofinite_admissiblyRational`, `VOA.Classification.COne.DLMRat.admissiblyRational_of_dlmRational`, `VOA.Classification.COne.zhuModularity_V2m` |
| **Affine VOAs for every simple Lie algebra.** The universal affine VOA V<sup>k</sup>(𝔤) and its simple quotient L<sub>k</sub>(𝔤) at every non-critical level, with concrete models of sl<sub>n</sub> and of the exceptional Lie algebras. | `VOA.AffineGeneral.universalAffineVOA`, `VOA.AffineGeneral.simpleAffineQuotientVOA_isSimple` |

### Recent theorems

| Result | Lean name(s) |
|---|---|
| **Classical freeness of L<sub>k</sub>(sl₂) (Arakawa–Dai).** At the boundary admissible levels k = −2 + 2/(2m+1), m ≥ 1, L<sub>k</sub>(sl₂) is classically free, with C₂ algebra ℂ[e,h,f]/(eQ<sup>m</sup>, hQ<sup>m</sup>, fQ<sup>m</sup>), Q the Casimir; also its vacuum character, in product and fermionic form. | `VOA.AffineSl2BoundaryClassicalFreeness.arakawaDai_theorem_1_1`, `VOA.AffineSl2BoundaryCharacter.character_eq_fermionic_chain` |
| **Classical freeness of the minimal models M(2,2m+3)**, for every m ≥ 0, with C₂ algebra ℂ[T]/(T<sup>m+1</sup>). | `VOA.VirasoroClassicalFreeness.classicallyFree` |
| **Huang's tensor categories.** For strongly rational VOAs, the braided tensor category of modules; for C₂-cofinite VOAs, that of logarithmic modules. For pseudo-unitary ones: rigidity, the Verlinde formula and the congruence property of the modular representation. | `VOA.Huang.TensorCat.HexagonClose.braidedCategory_stronglyRational_pbw`, `VOA.Huang.HuangRigid.rigid_ordinary`, `VOA.Classification.COne.huangVerlindeFusionInput_holds`, `VOA.Huang.CongruenceNamed.dlnCongruenceInput_holds` |
| **Classification at c = 1 (Gannon–Rayhaun).** The strongly rational, pseudo-unitary VOAs of central charge one are exactly the lattice VOAs V<sub>2m</sub>, their orbifolds V<sub>2m</sub><sup>+</sup>, and the three exceptional orbifolds V₂<sup>A₄</sup>, V₂<sup>S₄</sup>, V₂<sup>A₅</sup>, each occurring once. | `VOA.Classification.COne.gannonRayhaun_classification` |
| **Modular differential equations beyond C₂-cofiniteness.** L<sub>−4/3</sub>(sl₂) is not C₂-cofinite, yet its characters converge, its torus conformal blocks form a finite-dimensional space, and its vacuum one-point functions satisfy a modular linear differential equation. The Arakawa–Kawasetsu theorem is proved for every VOA with finite-dimensional zeroth Poisson homology. | `VOA.Sl2NonLisse.not_C2Cofinite_simpleSl2QL`, `VOA.IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite_uncond` |

### New results: rigidity

| Result | Lean name(s) |
|---|---|
| **Virasoro minimal models.** Every graded first-order deformation of every minimal model L(c<sub>p,q</sub>, 0), p, q ≥ 2 coprime, is trivial. For the series M(2,2n+1), rigidity was also proved by Butson and Nair by other methods. The universal Virasoro VOA is not rigid. | `VOA.VirModule.minimal_graded_rigidity`, `VOA.VirPoly.not_isRigidGraded_virasoroVOA` |
| **Affine sl₂ at admissible levels.** Every graded first-order deformation of L<sub>k</sub>(sl₂) is trivial, at every admissible level. This contains Linshaw and Qi's results for sl₂, at the positive integral levels and at k = −4/3. | `VOA.AffineSl2GeneralRigidity.admissible_graded_rigidity` |

### New results: classical freeness for the Deligne series

| Result | Lean name(s) |
|---|---|
| **A₂.** L<sub>−3/2</sub>(sl₃) is classically free: its C₂ algebra is the quotient by eight explicit quadrics, and the arc algebra of that quotient is isomorphic to the associated graded of the VOA. | `VOA.DeligneAudit.DeligneSeries.A2_classicallyFree_final` |
| **D₄.** The same for L<sub>−2</sub>(so₈), with 105 quadrics, given a published dimension bound for fusion products of current-algebra modules (Kus–Littelmann). | `VOA.DeligneAudit.DeligneSeries.D4_classicallyFree_of_inputT` |
| **G₂, F₄, E₆, E₇, E₈.** The same at the other levels of the series, given the same bound, a published result on Demazure modules, and a character identity. | `VOA.DeligneAudit.DeligneSeries.G2_classicallyFree_final` and its F₄, E₆, E₇, E₈ analogues |

### New results: graded unitarity

| Result | Lean name(s) |
|---|---|
| **Universal affine sl₂.** For every real k < −2, V<sup>k</sup>(sl₂) is graded unitary in the sense of Arabi Ardehali–Beem–Lemos–Rastelli. | `VOA.AffineSl2BelowCritical.universal_gradedUnitary_belowCritical_unconditional` |
| **Transfer through the BRST coset.** If L<sub>k</sub>(sl₂) at the boundary admissible level is graded unitary, then so is the minimal model M(2,2n+1), for every n ≥ 2. The proof formalizes the argument of Beem and Garner on the BRST complex. | `VOA.TwoSeries.JetPoincareTwo.twoSeries_gradedUnitary_of_affine_final` |

**Also in the library.** Vertex operator superalgebras, with symplectic fermions and the βγ system as examples, and
the triplet algebra W(2), proved simple, C₂-cofinite and not rational.

## Trust model

**Base.** The library is built with Lean 4.30.0 and Mathlib v4.30.0 and declares no axiom of its own. Production code
contains no `sorry`, `admit`, `native_decide`, `stop` or `implemented_by`. The repository checker
`scripts/check_repository.py` rejects any of these, as well as any `axiom` declaration, and requires every library
file to be reachable from the umbrella module `VOA.lean`. Large finite verifications are done by kernel reduction
(`decide`, `decide +kernel`), never by the compiler, and `#print axioms` is run on every headline declaration
(`scripts/audit/run_axiom_audits.py`).

**Definitions and theorems.** The book connects each declaration to the corresponding statement in the literature.
For every theorem it prints the Lean declaration verbatim, decodes every convention and hypothesis in a dictionary
box, and explains why the statement is about the intended object. Each chapter has two referees, one for clarity and
one for fidelity, and each headline area received an independent release audit that compared the Lean statement
with the source paper, traced every definition it depends on, listed every explicit hypothesis and re-printed the
axioms.

## Building and checking

With [`elan`](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build VOA
python3 scripts/check_repository.py
python3 scripts/audit/run_axiom_audits.py
```

To print the axioms of a single declaration, use `lake build` or `lake env lean -DmaxSynthPendingDepth=3`, which
keeps the synthesis depth the library is built with.

The book and the Brief are built with LuaLaTeX from `Notes/Textbook/`: `lualatex book.tex` (three passes) and
`lualatex brief.tex` (two passes).

## Size and structure

The library has 12,051 Lean files and 3,843,978 lines under `VOA/`.

| Directory | Files | Lines | Content |
|---|---:|---:|---|
| `Foundations` | 29 | 9,642 | formal calculus, PBW, Lie-theoretic input |
| `Core` | 128 | 46,320 | VOA axioms, Borcherds identity, quotients |
| `Modules` | 466 | 132,816 | weak/admissible/ordinary modules, Zhu algebra |
| `Modularity` | 234 | 66,958 | modular forms, Zhu's theorem, q-traces |
| `Examples` | 1,181 | 307,367 | constructions; rigidity; Arakawa–Dai; graded unitarity |
| `AffineGeneral` | 354 | 21,641 | affine VOAs for every simple 𝔤 |
| `LatticesAndCodes` | 25 | 8,472 | lattices, Golay code, Leech lattice |
| `Moonshine` | 561 | 146,923 | V♮; monstrous moonshine; the Monster's action |
| `Huang` | 931 | 183,719 | tensor categories, rigidity, Verlinde, congruence |
| `Classification` | 1,756 | 1,627,513 | Gannon–Rayhaun c = 1 classification |
| `DeligneAudit` | 6,173 | 1,241,760 | Deligne series |
| `Commutative`, `Filtered`, `Geometric` | 201 | 45,436 | commutative algebra, Li filtration |
| umbrella files | 12 | 5,411 | |

A large part of the line count is certificate data: the 167 files larger than 200 KB contain 1,518,787 lines, mostly
exact rational data for the c = 1 orbifold computations, checked by kernel reduction. The book has 2,786 pages and
the Brief 257; the 1,575 Lean excerpts quoted in the Brief are checked verbatim against the source.

## Method

The formalization was human-directed and carried out with the assistance of AI coding agents (Anthropic's Claude
Opus and Claude Fable, and OpenAI's Codex), while Python scripts generated the certificate data that the Lean kernel
re-checks and Python and Mathematica supplied independent numerical cross-checks. The authors chose the targets, the
definitions and conventions, and the release scope; agents wrote the Lean code and the first drafts of the book
chapters. Every chapter and every headline result was reviewed independently by several AI models, and a result
counts only when the aggregate build is green.

## In preparation

- **Lean v4.35** (release v1.1): the library moves to AxiomMath's toolchain, and `GmatEqAutO` becomes an imported
  theorem.
- **Deligne series beyond A₂:** removing the assumptions of the conditional theorems.
- **Graded unitarity in the other direction**, from the minimal models to the affine algebra, through Adamović's
  free-field realization (inverse Drinfeld–Sokolov reduction).
- **Affine sl₃**, towards its rigidity.
- **Rigidity, the Verlinde formula and the congruence property for every strongly rational VOA**, without
  pseudo-unitarity.

## Acknowledgements

We thank Brandon Rayhaun, Avia Raviv-Moshe and Chris Beem for useful discussions, and the Lean and Mathlib
communities. The work of LR is supported in part by NSF grant PHY-2513893 and by the Simons Foundation grant 681267
(Simons Investigator Award).

## License

Apache 2.0. See [`LICENSE`](LICENSE).

---

> "That is a Landau-Lifshitz of VOAs."
>
> — Justin Kulp, PhD
