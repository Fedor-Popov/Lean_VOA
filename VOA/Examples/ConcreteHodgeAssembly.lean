/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteHodgeGU
import VOA.Examples.ConcreteHodgeSymmetry
import VOA.Examples.LeeYangTransferAssembly

/-!
# The concrete Beem–Garner instantiation, in the interface of `LeeYangTransferAssembly`

Assembly layer. It produces the fields `kahler`, `weakGU` and `gu` of
`LeeYangTransferAssembly.OpenInputs` for the actual relative complex
`relativeWeight n` with the actual differential `relativeDifferential n`, using the assembly's
`affineForm`, `affineRealStructure`, `affineFlag` and auxiliary triple.

## Proved outright (given the named factor hypotheses)

* `matterGhostForm` — the product of the modified forms on `((A ⊗ B) ⊗ U) ⊗ ghosts`: the
  `σ`-twisted form of `A` (`carrierForm`, built from **`hA`**), the ABLR form of `B`
  (`unitaryCarrierForm`), the `σ`-twisted form of `U` (built from the *proved*
  `auxiliaryGradedUnitary`), and a ghost form `PG`.
* `weakGU_matterGhostForm` (**weak GU of the tensor product**): positive definite on the whole
  matter-ghost space. Its hypotheses are `hA`, `Unitary BB RB` and `IsPosOn PG ⊤` only.
* `assemblyForm n` — the form on `relativeWeight n` that the interface needs *before* `hA` is
  available (`WeakGUTensorPositivity` is an implication from `hA`): by classical case split, the
  restricted product form when `hA` holds, and `0` otherwise. `assemblyForm_pos`: positive
  under `hA`. In every use `hA` is assumed, so only the first branch matters.
* `concreteKahler` / `concreteKahler_weakGU` / `concreteGUData`: the three interface
  fields, from the geometry input `ConcreteGoodGeometry` and the conjugation input `ConjData`.
  The four pieces `Q^±, S^±`, the four adjoint relations, the ghost bookkeeping of `differential`,
  and `ρ_maps`, `ρ_onto` are *derived* (`ConcreteHodgeSplit`, `ConcreteHodgeGU`).
* `leeYang_gradedUnitary_of_affine_concrete` — `leeYang_gradedUnitary_of_affine` with these
  three fields discharged.

## Named hypotheses (none asserts positivity of the complex or a conclusion)

* `hA : GradedUnitary affineForm affineRealStructure affineFlag` — **the hypothesis.**
* (Gram reflexivity of the affine and auxiliary forms is *proved*: `affineGramRefl`,
  `auxiliaryGramRefl`, from `ConcreteHodgeSymmetry`.)
* `Unitary BB RB` — unitarity of `L_1(sl2)`. OPEN in the repository. (`GradedFlag` cannot express
  the trivial filtration, whose degree-`0` piece is everything, so `B` enters through its form.)
* `IsPosOn PG ⊤` — positivity of the ghost form. OPEN (the ghost Fock space is a Clifford
  algebra here; no form is constructed on it yet).
* `ConcreteGoodGeometry` — **OPEN: Beem–Garner Lemma 3.16 for this complex.** A bigrading by
  `(2R, gh)` orthogonal for `assemblyForm`, compatible with the actual ghost number, the second
  bold differential `𝐐⁺`, goodness (no `ℜ`-preserving components of `𝐐^±`), the single relation
  `(𝐐⁻)† = c (S⁺ - Q⁺)`, and `𝐐⁻𝐐⁺ + 𝐐⁺𝐐⁻ = 0`.
* `GoodComplex.ConjData` — **OPEN**: the invariant form and `ρ` at weight `n`, `P = i^{2R}(ρ·,·)`,
  `ρ` reversing ghost number, `ρ𝐐⁻ = κ𝐐⁺ρ`, `ρ𝐐⁺ = κ'𝐐⁻ρ`, `ρ² = s ≠ 0`.

Not addressed: `LeadingInvariantSymbolDimension` (the concrete `LeadModel`).
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open VirSimple VirGradedUnitarity
open scoped TensorProduct
open Module (finrank)

noncomputable section

/-! ### Unitary factors (trivial filtration) -/

section Unitary

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Unitarity** of a VOA for a form and a real structure: ABLR's Hermitian form is positive
definite on every weight space (graded unitarity for the trivial filtration). -/
def Unitary (B : InvariantForm W) (R : RealStructure W) : Prop :=
  ∀ n : ℤ, IsPosOn (gradedSesq B R n) ⊤

/-- The ABLR form of a unitary factor on its whole carrier (weight-orthogonal sum). -/
def unitaryCarrierForm (B : InvariantForm W) (R : RealStructure W) : SesqForm 𝒱 :=
  internalForm W.isInternal (fun n => gradedSesq B R n)

theorem isPosOn_unitaryCarrierForm (B : InvariantForm W) (R : RealStructure W)
    (hU : Unitary B R) : IsPosOn (unitaryCarrierForm B R) ⊤ :=
  isPosOn_internalForm _ _ hU

end Unitary

/-! ### The product form and weak graded unitarity -/

/-- The product of four forms on `((A ⊗ B) ⊗ U) ⊗ ghosts`. -/
def brstForm (PA : SesqForm ASpace) (PB : SesqForm BSpace) (PU : SesqForm USpace)
    (PG : SesqForm Sl2GhostSpace) : SesqForm (MatterSpace ⊗[ℂ] Sl2GhostSpace) :=
  ((PA.tensor PB).tensor PU).tensor PG

theorem isPosOn_brstForm (PA : SesqForm ASpace) (PB : SesqForm BSpace) (PU : SesqForm USpace)
    (PG : SesqForm Sl2GhostSpace) (hA : IsPosOn PA ⊤) (hB : IsPosOn PB ⊤) (hU : IsPosOn PU ⊤)
    (hG : IsPosOn PG ⊤) : IsPosOn (brstForm PA PB PU PG) ⊤ :=
  SesqForm.isPosOn_tensor _ _ (SesqForm.isPosOn_tensor _ _
    (SesqForm.isPosOn_tensor _ _ hA hB) hU) hG

/-- Gram reflexivity of the boundary affine form (proved: `simpleForm_isSymmetric`). -/
theorem affineGramRefl : GramRefl affineForm := gramRefl_simpleForm ALevel aNoncritical

/-- Gram reflexivity of the auxiliary form (proved: `universalForm_isSymmetric`). -/
theorem auxiliaryGramRefl : GramRefl auxiliaryForm :=
  gramRefl_universalForm (-11 / 3) uNoncritical

/-- **The modified product form** of the matter-ghost system. -/
def matterGhostForm (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) (PG : SesqForm Sl2GhostSpace) :
    SesqForm (MatterSpace ⊗[ℂ] Sl2GhostSpace) :=
  brstForm (carrierForm affineForm affineRealStructure affineFlag hA affineGramRefl)
    (unitaryCarrierForm BB RB)
    (carrierForm auxiliaryForm auxiliaryRealStructure auxiliaryFlag auxiliaryGradedUnitary
      auxiliaryGramRefl)
    PG

/-- **Weak graded unitarity of `A ⊗ B ⊗ U ⊗ ghosts`**: from graded unitarity of `A` (`hA`),
unitarity of `B`, positivity of the ghost form and the proved graded unitarity of `U`, the
modified product form is positive definite on the whole matter-ghost space. -/
theorem weakGU_matterGhostForm (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA}
    {RB : RealStructure BVOA} (hB : Unitary BB RB) {PG : SesqForm Sl2GhostSpace}
    (hG : IsPosOn PG ⊤) : IsPosOn (matterGhostForm hA BB RB PG) ⊤ :=
  isPosOn_brstForm _ _ _ _ (isPosOn_carrierForm _ _ _ hA affineGramRefl)
    (isPosOn_unitaryCarrierForm BB RB hB)
    (isPosOn_carrierForm _ _ _ auxiliaryGradedUnitary auxiliaryGramRefl) hG

/-! ### The form on the relative weight spaces -/

/-- The zero sesquilinear form. -/
def _root_.VOA.SesqForm.zero (E : Type*) [AddCommGroup E] [Module ℂ E] : SesqForm E where
  toFun _ _ := 0
  add_left _ _ _ := by ring
  smul_left _ _ _ := by ring
  add_right _ _ _ := by ring
  smul_right _ _ _ := by ring

open Classical in
/-- The form on `relativeWeight n` used by the interface: the restricted product form under
`hA`, and `0` otherwise (the interface fixes the form before `hA` is assumed). -/
def assemblyForm (BB : InvariantForm BVOA) (RB : RealStructure BVOA)
    (PG : SesqForm Sl2GhostSpace) (n : ℤ) : SesqForm (relativeWeight n) :=
  if hA : GradedUnitary affineForm affineRealStructure affineFlag then
    (matterGhostForm hA BB RB PG).restrict (relativeWeight n)
  else SesqForm.zero _

theorem assemblyForm_eq (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) (PG : SesqForm Sl2GhostSpace) (n : ℤ) :
    assemblyForm BB RB PG n =
      (matterGhostForm hA BB RB PG).restrict (relativeWeight n) := by
  classical
  unfold assemblyForm
  rw [dif_pos hA]

theorem assemblyForm_pos (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA}
    {RB : RealStructure BVOA} (hB : Unitary BB RB) {PG : SesqForm Sl2GhostSpace}
    (hG : IsPosOn PG ⊤) (n : ℤ) : IsPosOn (assemblyForm BB RB PG n) ⊤ := by
  rw [assemblyForm_eq hA]
  exact SesqForm.isPosOn_restrict _ (weakGU_matterGhostForm hA hB hG) _

/-! ### The open Lemma 3.16 input and the interface fields -/

set_option maxHeartbeats 4000000 in
-- The auto-generated structure lemmas unfold the heavy tensor carrier.
/-- **OPEN (Beem–Garner Lemma 3.16 for the actual complex at weight `n`)**: a good geometry on
`relativeWeight n` whose form is the given `P`, whose bold differential is the actual
`relativeDifferential n`, and whose ghost coordinate is the actual ghost number. -/
structure ConcreteGoodGeometry (n : ℤ) (P : SesqForm (relativeWeight n)) where
  geom : GoodGeometry (relativeWeight n)
  P_eq : geom.P = P
  D_eq : geom.D = relativeDifferential n
  ghost : ∀ a, geom.deg a ≤ (leeYangBRSTComplex.ghost a.2).comap (relativeWeight n).subtype

universe u in
/-- A good geometry as a `KahlerGeometry` of the assembly interface. -/
def _root_.VOA.ConcreteHodge.GoodGeometry.toKahlerGeometry {K : Type u} [AddCommGroup K]
    [Module ℂ K] (G : GoodGeometry K) : KahlerGeometry K where
  P := G.P
  deg := G.deg
  span := G.span
  orth := G.orth
  Qm := G.Qm
  Sm := G.Sm
  Qp := G.Qp
  Sp := G.Sp
  Qm_deg := G.Qm_deg
  Sm_deg := G.Sm_deg
  Qp_deg := G.Qp_deg
  Sp_deg := G.Sp_deg
  c := G.c
  c_sq := G.c_sq
  adj_Qm := G.adj_Qm
  adj_Sm := G.adj_Sm
  sq_zero := by rw [G.Qm_add_Sm]; exact G.sq_zero
  anticomm := by rw [G.Qm_add_Sm, G.Qp_add_Sp]; exact G.anticomm

section Interface

variable {BB : InvariantForm BVOA} {RB : RealStructure BVOA} {PG : SesqForm Sl2GhostSpace}

/-- **The `kahler` field of `OpenInputs`**, from the Lemma 3.16 input at every weight. -/
def concreteKahler (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n)) :
    ConcreteKahlerGeometry where
  geometry n := (I n).geom.toKahlerGeometry
  differential n := (I n).geom.Qm_add_Sm.trans (I n).D_eq
  ghost n := (I n).ghost

/-- **The `weakGU` field of `OpenInputs`**: proved from `hA`, `L_1` unitarity, ghost
positivity and Gram reflexivity, via tensor positivity. -/
theorem concreteKahler_weakGU (hB : Unitary BB RB) (hG : IsPosOn PG ⊤)
    (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n)) :
    WeakGUTensorPositivity (concreteKahler I) := by
  intro hA _ n
  change IsPosOn (I n).geom.P ⊤
  rw [(I n).P_eq]
  exact assemblyForm_pos hA hB hG n

/-- The good complex at weight `n` once positivity is known. -/
def concreteGood (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n)) (n : ℤ)
    (hp : IsPosOn ((concreteKahler I).geometry n).P ⊤) : GoodComplex (relativeWeight n) :=
  { (I n).geom with pos := hp }

/-- The interface's Kähler model is the Kähler package of the good complex. -/
theorem concreteKahler_model (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n))
    (n : ℤ) (hp : IsPosOn ((concreteKahler I).geometry n).P ⊤) :
    (concreteKahler I).model n hp = (concreteGood I n hp).toKahler := rfl

/-- **The `gu` field of `OpenInputs`**, from the conjugation input at every weight. -/
def concreteGUData (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n))
    (R : ∀ n hp, GoodComplex.ConjData (concreteGood I n hp)) :
    ConcreteGUData (concreteKahler I) where
  data n hp := (concreteGood I n hp).guData (R n hp)

end Interface

/-- **Graded unitarity of Lee–Yang from the boundary affine algebra**, with the
`kahler`, `weakGU`, `gu` fields of `OpenInputs` discharged by the concrete Beem–Garner
instantiation. Remaining inputs: the factor facts `hB`, `hG`, the Lemma 3.16
geometry `I`, the conjugation data `R`, and the remaining `OpenInputs` fields
(`identification`, `metric`, `filtered`, `symbols`, `character`). -/
theorem leeYang_gradedUnitary_of_affine_concrete
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤)
    (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n))
    (R : ∀ n hp, GoodComplex.ConjData (concreteGood I n hp))
    (ident : CosetIdentification)
    (metric : HarmonicMetricAgreement ident (concreteKahler I) (concreteGUData I R))
    (filtered : CosetFiltrationCompatibility ident (concreteKahler I))
    (symbols : LeadingInvariantSymbolDimension (concreteKahler I))
    (character : LeeYangPBWCharacter) :
    VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine hA
    { identification := ident
      kahler := concreteKahler I
      weakGU := concreteKahler_weakGU hB hG I
      gu := concreteGUData I R
      metric := metric
      filtered := filtered
      symbols := symbols
      character := character }

end

end VOA.ConcreteHodge
