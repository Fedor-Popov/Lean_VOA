# CFSG port fidelity: is our `Generated.Gmat = AutO` literally CFSG's `gmat_eq_griess`?

A read-only comparison of source texts; no build was involved. Source: AxiomMath/CFSG at the pinned commit
`69cb972f587a3ecc035e092253167ff2e303c962`, fetched with `gh api …/contents/<path>?ref=<sha>`.
The fetched files were kept outside the repository as data and were never built, run or imported.

## 1. The CFSG statement

File `CFSG/Sporadic/Bridge/MonsterModelsGriess.lean`, `namespace CFSG.Blueprint.NativeSporadic.MonsterModel`:

```lean
theorem gmat_eq_griess :
    CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO :=
  CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
```

* **Full name.** `CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess`.
* **Both sides are written with fully qualified names.**
  - `CFSG.Monster.Generated.Gmat` is the `def Gmat` in `CFSG/Monster/Generated/Data.lean`.
  - `CFSG.Monster.Griess.AutO` is the `def AutO` in `CFSG/Monster/Griess/AutFinite.lean`.
* **These are the declarations the port copied.** Ours are `VOA.Moonshine.MonsterGriess.Generated.Gmat`
  (`TrialityFourGroup.lean`) and `VOA.Moonshine.MonsterGriess.AutO` (`AutO.lean`).
* **No other `Gmat` is involved.** The Blueprint `MonsterModel.gmat` model and the `YGroups` names appear
  only in the proof and in sibling theorems, not in the statement.
* **The type is the same.** Both sides have type `Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)`.
* **Name resolution inside the `Gmat` body is unique.** `Data.lean` opens
  `CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible`, and the body
  `Subgroup.closure ((Gvis : Set _) ∪ {tauB})` resolves to `Visible.Gvis` and `Griess.tauB`. A second
  candidate of the same type would be an ambiguity error, so the resolution is unique.

Not checked here: the axiom footprint of `gmat_eq_griess`. Its proof runs through
`cl_lit_stroth_leon_sims_baby_monster_recognition_models` (see `RECON_CFSG.md` §2.1). Whether that
is a proved theorem or a literature axiom needs `#print axioms` in the CFSG toolchain.

## 2. Method

1. **Parsing our side.** A parser strips comments and splits every port file
   (`VOA/Moonshine/MonsterGriess/*.lean`, excluding `*Audit.lean` and `LeechMatch.lean`) into
   top-level declarations, tracking namespaces.
2. **Definitional closure, an over-approximation.** Start from `Generated.Gmat` and `AutO`. Follow every
   identifier, matched by any qualified suffix, that occurs in:
   * a def, abbrev, structure, instance or inductive body;
   * the **statement** of any theorem referenced from such a body. Theorems can fix data through
     implicit arguments: `tauB := Matrix.toLinOfInv tbasis tbasis tauMat_transpose_mul …` gets `tauMat`
     from the statement, and `tbasis := basisOfLinearIndependentOfCardEqFinrank linearIndependent_tvec …`
     gets `tvec`. `Classical.choose` values (`thetaD`, `uvec`, `octRep`) depend on the chosen predicate.

   The traversal stops at Mathlib. The result is **199 definition-like declarations** and **104
   referenced theorem statements**. A few entries are spurious hits on short names: `Jordan.symMat`,
   `Parity.IsParityAut`, `xB`, `parityMap`, and the private `zmod2_cases` / `two_eq_zero'` copies.
   Comparing them does no harm.
3. **Fetching the source.** The 49 CFSG source files named in the port headers of the closure files
   were fetched, plus `Generated/Data.lean` and the bridge file.
4. **Normalization.** Both sides were reduced the same way:
   * comments and attributes (`@[expose]`, `@[simp]`) dropped;
   * the keywords `public`, `noncomputable`, `private` and `protected` dropped;
   * the namespace prefixes `CFSG.Monster.Griess.`, `CFSG.Monster.` and `VOA.Moonshine.MonsterGriess.`
     removed;
   * whitespace collapsed.

   Each declaration was then matched by its namespace-relative name and its body compared. Any
   mismatch was read by hand.
5. **Extra checks.**
   * All 46 instances of the port were compared against the source instances.
   * The `variable` contexts on both sides were compared, since they fix binder explicitness and
     instance arguments of defs.
   * Every closure def body was scanned for tactic-built data and for `choose`.

## 3. Per-declaration verdicts

**Totals.**
* **Definition bodies, 198 matched to source.** 194 are textually identical after normalization. Four
  needed a manual read (§3.2).
* **Spurious hit without a source counterpart.** `Jordan.symMat` (`ParityRealExtension.lean`) is
  port-only and outside the real closure: no closure file imports it, and the `Jordan` namespace is
  not opened.
* **Theorem statements feeding definitions, 88 matched to source.** All 88 are identical after
  normalization. The other 16 have no source counterpart: the port-added
  `gmulFun_add_right`/`gmulFun_smul_right` (Prop arguments of `gmul`), `Jordan.mem_symMat`, and the
  private `zmod2_cases`/`two_eq_zero'` copies. They are Props and fix no data.
* **Instances, 46.**
  - 44 are identical to source instances, among them every instance in the closure files: `F4`
    (DecidableEq, Fintype, Zero … Field, Algebra), `DecidablePred (· ∈ C)`, `(· ∈ H₆)`, `(· ∈ C₀)`,
    `DecidableEq Cocode`, `Fintype`/`DecidableEq ShortIdx`, `EvenQuot` (AddCommGroup, Module,
    Finite, Fintype, DecidableEq), `SpinCoord` (Mul, One, Inv, Group), `Parker` (Finite, Mul, One),
    the `DecidableEq` instances on `XIdx`, `BlockIdx`, `TIdx`, `OctIdx`, `ShortLabel` and the two
    `instDecidableEq…OctIdx`, the two `zpowers … Normal` instances, and `instFiniteQ`.
  - The other 2 are outside the closure: `DecidableEq Gam` (`GriessGrading`) and
    `Decidable (IsPairTriangle …)` (`InvarianceTwoCoord`).
* **`variable` contexts.** Every port-only `variable` line sits in a file outside the closure
  (`ParityRealExtension`, `OctadThreeOctad`, `SpinMatrixLaws`, `SpinMatrixMap`, `ParityShortLines`),
  or in a theorem-only section (`SpinGroupQ` `SignedPermExtra`). The `R`-explicit and `{R}` regions
  around `sgnR`, `spm`, `qmatR`, `XmatR` and `DmatR`, and the `E`/`I` contexts of `fourierMatrix`,
  `signMatrix` and the `Octad.*` defs, match the source line for line.
* **Tactic-built data.** Every `by` in a closure def body proves a Prop: subtype membership, `map_add'`,
  `Fin` bounds, the `mapQ` hypothesis in `modTwoEnd`. The `choose` sites are `Spin.thetaD`
  (predicate from `exists_pair_eq`, statement identical), `octRep` (`Octad.exists_cls_eq`, identical)
  and `uvec` (predicate `IsShortCoord`, see §3.2).

### 3.1 Identical up to cosmetics (194)

Format: our file ← source file : declarations, with namespace-relative names. Prefixes:
ours `VOA.Moonshine.MonsterGriess.`, theirs `CFSG.Monster.Griess.` or `CFSG.Monster.`.

- `Algebra.lean` ← `Griess/Space.lean` : `SpaceB`, `SpaceW`, `SpaceX`, `symMat`
- `Algebra.lean` ← `Griess/Trilinear.lean` : `Am`, `Nm`, `xs`, `Rmat`, `Umat`, `gmulA`, `gmulFun`, `gmulW`, `gmulWHalf`, `gmulX`, `qf`, `tau`, `uQ`
- `AutO.lean` ← `Griess/AutFinite.lean` : `AutO`
- `AutO.lean` ← `Griess/ProductInvariance.lean` : `IsAlgAut`
- `Golay.lean` ← `Code/Basis.lean` : `Code.ev`, `Code.ψ`
- `Golay.lean` ← `Code/Defs.lean` : `Code.B`, `Code.C`, `Code.H₆`, `Code.col`, `Code.coord`, `Code.g`, `Code.hexProj`, `Code.l`, `Code.lCol`, `Code.row`, `Code.topParity`, `Code.v₁`, `Code.v₂`, `Code.v₃`, `Code.Ω`, `Code.ω`, `Code.ωInf`
- `Golay.lean` ← `Code/F4.lean` : `Code.F4`, `Code.F4.α`, `Code.F4.ᾱ`
- `Golay.lean` ← `Code/Loop.lean` : `Code.A`, `Code.K`, `Code.P`, `Code.supp`, `Code.β`, `Code.θ`, `Code.θc`
- `GriessTrilinear.lean` ← `Griess/Parity.lean` : `parityMap`, `xB`
- `GriessTrilinear.lean` ← `Griess/Short.lean` : `centralCoord`, `coordOf`, `rep`
- `GriessTrilinear.lean` ← `Griess/Space.lean` : `PairIdx`, `Xlift`, `basisA`, `symCoord`, `symEntry`, `tensor`
- `Lattice.lean` ← `CodeLattice.lean` : `allOnes`, `bitLift`, `codeForm`, `codeLattice`, `codeLatticeSubgroup`
- `Lattice.lean` ← `CodeLatticeUnimodular.lean` : `codeLatticeModTwo`
- `Lattice.lean` ← `SpinLattice/Lambda.lean` : `SpinLattice.L2`, `SpinLattice.Pint`, `SpinLattice.cls`, `SpinLattice.lamCode`, `SpinLattice.lamCodeCls`, `SpinLattice.lamSum`, `SpinLattice.lamVec`, `SpinLattice.lamVecLin`
- `Lattice.lean` ← `Code/LatticeCount.lean` : `Code.classOf`
- `Lattice.lean` ← `Code/LatticeShort.lean` : `Code.minVecs`
- `LatticeFamilies.lean` ← `Code/LatticeCount.lean` : `Code.sgn`
- `OctadEvenSubset.lean` ← `Octad/EvenSubset.lean` : `Octad.EvenQuot`, `Octad.cls`, `Octad.complSpan`, `Octad.dotForm`, `Octad.evenQuad`, `Octad.evenSubsets`, `Octad.ind`, `Octad.liftQuad`, `Octad.mk`, `Octad.quadForm`, `Octad.wt`
- `OctadEvenSubset.lean` ← `FourierTriality.lean` : `fourierMatrix`
- `ParityTraceSplitting.lean` ← `Parity/TraceSplitting.lean` : `Parity.IsParityAut`
- `ScalarKernel.lean` ← `ScalarKernel.lean` : `ScalarKernel.latHom`, `latVec`, `latticeO`, `latticeQ`, `mat`, `modTwoEnd`, `ratVec`
- `Short.lean` ← `SpinLattice/Cocode.lean` : `SpinLattice.lamCocode`, `SpinLattice.lamT`, `SpinLattice.lamX`
- `Short.lean` ← `Griess/Short.lean` : `IsShortCoord`, `ShortIdx`, `LexLE`, `uvec` (text identical, but see §3.2 on `phi0`)
- `Spin.lean` ← `Spin/Coords.lean` : `Spin.qPerm`, `Spin.qSign`, `Spin.qmatR`
- `Spin.lean` ← `Spin/Defs.lean` : `Spin.SpinIdx`, `Spin.shift`
- `Spin.lean` ← `Lagrangian.lean` : `sgn`
- `Spin.lean` ← `Spin/Pairing.lean` : `Spin.Cocode`, `Spin.C₀`, `Spin.dotL`, `Spin.pair`, `Spin.thetaD`, `Spin.ΩC`, `Spin.θL`, `Spin.μ₀`, `Spin.π₀`
- `Spin.lean` ← `Spin/SignedPerm.lean` : `Spin.sgnR`, `Spin.spm`
- `SpinExtraspecial.lean` ← `Dyadic.lean` : `dyadic`
- `SpinExtraspecial.lean` ← `Spin/Extraspecial.lean` : `Spin.SpinCoord.proj`, `Spin.spinEquiv`, `Spin.toGL`
- `SpinExtraspecial.lean` ← `SpinLattice/Isometry.lean` : `SpinLattice.phi`
- `SpinExtraspecial.lean` ← `Spin/SpinCoord.lean` : `Spin.SpinCoord`, `Spin.SpinCoord.z`
- `SpinGroupQ.lean` ← `Spin/Defs.lean` : `Spin.DU`, `Spin.Dmat`, `Spin.DmatR`, `Spin.E`, `Spin.Q`, `Spin.XU`, `Spin.Xmat`, `Spin.XmatR`, `Spin.dPerm`, `Spin.dSign`, `Spin.xPerm`, `Spin.xSign`
- `SpinGroupQ.lean` ← `Code/Loop.lean` : `Code.Parker`
- `TrialityBasis.lean` ← `Griess/TrialityBasis.lean` : `AIdx`, `BlockIdx`, `TIdx`, `WIdx`, `XIdx`, `aPair`, `blockVec`, `tbasis`, `toBlock`, `tvec`, `wEta`, `wSign`, `wVec`, `xVec`
- `TrialityClasses.lean` ← `Griess/TrialityBasis/Classes.lean` : `LtPair`, `OctIdx`, `OctadWord`, `octSupp`, `octRep`, `rOctQ`
- `TrialityFourGroup.lean` ← `Generated/Data.lean` : `Generated.Gmat`
- `TrialityLabels.lean` ← `SpinLattice/Isometry.lean` : `SpinLattice.DQ`, `SpinLattice.XQ`
- `TrialityLabels.lean` ← `Griess/TrialityBasis/Labels.lean` : `aOct`, `aOdd`, `deltaPair`, `mOdd`, `nOct`, `rMinus`, `rOct`, `rOdd`, `rPlus`
- `TrialityMatrix.lean` ← `Griess/TrialityMatrix/Blocks.lean` : `cyc3`, `diag2`, `kron1`, `octD`, `octH`, `octHD`
- `TrialityMatrix.lean` ← `Griess/TrialityMatrix.lean` : `octBlock`, `oddBlock`, `pairBlock`, `tauB`, `tauMat`
- `VisiblePair.lean` ← `Visible/Pair.lean` : `Visible.Gvis`, `Visible.IsCompatible`, `Visible.IsDyadicSpinNormalizer`, `Visible.Pvis`, `Visible.conjQ`, `Visible.conjQOf`, `Visible.theta`, `Visible.thetaA`, `Visible.thetaEquiv`, `Visible.thetaW`, `Visible.thetaX`

### 3.2 Bodies that differ textually (4)

| declaration (ours ← theirs) | difference | value changed? |
|---|---|---|
| `bform` (`Algebra.lean` ← `Griess/Space.lean`) | In the four `LinearMap.mk₂` proof arguments, ours drops `Matrix.add_mul` / `Matrix.mul_add` from two `simp only` lists. The function argument `fun u v => trace (u.1 * v.1) + ∑ c, … + ∑ j, ∑ i, …` is identical. | **No.** The difference is in Prop proof terms only. |
| `gmul` (`Algebra.lean` ← `Griess/Trilinear.lean`) | The last two `mk₂` arguments are port lemmas `gmulFun_add_right`, `gmulFun_smul_right` instead of inline `fun … => by rw [gmulFun_comm, …]`. The data argument `gmulFun` is identical. | **No.** The difference is in Prop proof terms only. |
| `signMatrix` (`OctadEvenSubset.lean` ← `FourierTriality.lean`) | None. The diff is a parser artefact: a trailing `omit … in` line was attached to the body. | **No.** |
| **`SpinLattice.phi0`** (`Short.lean` ← `SpinLattice/Cocode.lean`) | **Ours:** `noncomputable def phi0 (p : C × Cocode) : L2 := lamT p.1 + lamCocode p.2`, a plain function. **Theirs:** `noncomputable def phi0 : C × Cocode →ₗ[ZMod 2] L2 := (AddMonoidHom.toZModLinearMap 2 lamTHom).coprod lamCocode`, a bundled linear map, where `lamTHom : C →+ L2` has `toFun := lamT`. Documented in the `Short.lean` port notes. | **Different constant, different type.** The underlying function is definitionally equal (see §4). |

## 4. Consequence of the `phi0` adaptation

`phi0` enters the closure only through:

```text
IsShortCoord p := ∃ u ∈ minVecs, classOf u = phi0 p
```

`IsShortCoord` determines `ShortIdx`. `ShortIdx` determines `SpaceX = ShortIdx → ℚ` and hence
`SpaceB`, `gmul`, `bform`, `AutO` and `Gmat`. `phi0` also enters `uvec` through the `choose`
predicate `c.2`.

* **Ours** elaborates to `classOf u = phi0 p`, a plain application.
* **Theirs** elaborates to `classOf u = ⇑phi0 p`: `DFunLike.coe` of a `LinearMap.coprod`.

The two are **definitionally equal**:

* `LinearMap.coprod f g` is `f ∘ₗ fst + g ∘ₗ snd`, and addition and composition of linear maps are
  pointwise. So `⇑phi0 p` reduces to `toZModLinearMap 2 lamTHom p.1 + lamCocode p.2`.
* That in turn reduces to `lamT p.1 + lamCocode p.2`, since `lamTHom.toFun := lamT`.
* Both sides state `phi0_apply : phi0 (a, δ) = lamT a + lamCocode δ := rfl`, and structure eta for
  `Prod` covers a general `p`.

So the two `IsShortCoord` predicates are kernel-convertible, the `ShortIdx` subtypes are definitionally
equal, and `Classical.choose` in `uvec` is taken over definitionally equal predicates. The *values*
of every downstream definition therefore agree, but the elaborated terms of
`IsShortCoord`/`ShortIdx` are not syntactically the same expression.

## 5. Cosmetic changes confirmed harmless

* **Namespaces.** `CFSG.Monster.Griess` and `CFSG.Monster` are merged into
  `VOA.Moonshine.MonsterGriess`. The Code, Spin, SpinLattice, Visible, Octad, ScalarKernel, Parity
  and Generated namespaces are kept under the new prefix. This creates one short-name collision,
  `MonsterGriess.sgn : ZMod 2 → ℚ` against `Code.sgn : Bool → ℤ`. The same pair exists in the source
  (`CFSG.Monster.sgn` and `CFSG.Monster.Code.sgn`). The types differ, so every use resolves the same
  way.
* **Module-system syntax.** `module`, `public import`, `public section`, `public noncomputable
  section` and `@[expose]` were dropped, with `noncomputable` added per declaration. These control
  visibility and compilation only, not values.
* **Dropped `attribute [-instance]`.** The line removed
  `instCommGroupOfIsSimpleGroupOfIsNilpotent` and `instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent`.
  In Mathlib v4.30 only the multiplicative instance exists (`Mathlib/GroupTheory/Nilpotent.lean:1066`,
  no `to_additive`). It fires only on a type carrying an `IsSimpleGroup` instance, and no closure type
  has one: `grep` finds `IsSimpleGroup`/`IsNilpotent` in the port only in comments. It cannot have
  altered any elaborated term.
* **Duplicate instance.** `DecidableEq Cocode := Classical.decEq _` appears in both `Spin.lean` and
  `SpinGroupQ.lean`. The bodies are identical, and the class is a subsingleton.

## 6. Not covered by this audit

* **Mathlib drift.** The closure bottoms out in Mathlib constants: `Subgroup.closure`,
  `Matrix.toLinOfInv`, `basisOfLinearIndependentOfCardEqFinrank`, `LinearMap.mk₂`, `Matrix.trace`,
  `Submodule.Quotient`/`liftQ`/`mapQ`, `LinearMap.coprod`, `Basis.ofEquivFun`, `Classical.choose`,
  `Fintype.ofFinite`, `toLex`, `GL`. They are assumed to mean the same in Mathlib v4.30 and in CFSG's
  pinned Mathlib. Ours compiles with them, but this audit did not compare their definitions across
  versions.
* **Build status.** No build was run. Fidelity is a source-text comparison; the port's own compilation
  status is whatever the last aggregate `lake build` recorded.
* **Axiom footprint.** The axioms behind `gmat_eq_griess` were not checked (§1).

## 7. Overall verdict

**Not literally identical, but definitionally equal.** After renaming
`CFSG.Monster.{Griess.,}` ↦ `VOA.Moonshine.MonsterGriess.`, our hypothesis
`Generated.Gmat = AutO` is CFSG's
`CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess :
CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO` **up to definitional equality**, not
syntactically.

* **The one discrepancy** is `SpinLattice.phi0`. Ours is the unbundled function
  `p ↦ lamT p.1 + lamCocode p.2`; theirs is the bundled `ZMod 2`-linear map
  `(toZModLinearMap 2 lamTHom).coprod lamCocode`. This changes the elaborated term of `IsShortCoord`
  (and hence of the type `ShortIdx`), but the two are kernel-convertible.
* **Everything else is identical up to cosmetics.** This covers the other 197 definition bodies
  compared, the 88 theorem statements that fix data, and the instances and `variable` contexts. The
  only other textual differences are Prop proof terms in `bform` and `gmul`.
* **What a cross-toolchain transfer needs.** A literal name-for-name transport would need a bridge
  step that closes by `rfl` (or `Iff.rfl` on `IsShortCoord`). Alternatively, `phi0` could be
  re-ported as the bundled linear map. That would require porting `lamT_add`, `lamTHom` and their
  theta-cocycle dependencies, after which the closure would be literally identical.
