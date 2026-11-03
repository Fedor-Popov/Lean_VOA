/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodGrading
import VOA.Examples.ConcreteHodgeAssembly

/-!
# The interpreted `(2R, gh)` grading of the actual relative complex

Before this file the bigrading `deg` of `ConcreteGoodGeometry` was uninterpreted: any orthogonal
spanning family would do. Here it is **constructed from the factor data** and restricted to the
actual relative weight spaces `relativeWeight n`:

* on `A = L_{-4/3}(sl₂)`: the orthogonal layers of the corrected flag `affineFlag`, which exist by
  clause (iv) of **`hA`**; `2R = 2p` on layer `p` (`aDeg`);
* on `B = L_1(sl₂)`: everything in `R = 0` (`bDeg`);
* on `U = V^{-11/3}(sl₂)`: the orthogonal layers of the ordinary PBW flag `auxiliaryFlag`, which
  exist by the *proved* `auxiliaryGradedUnitary` (`uDeg`);
* on the ghosts: a `GhostRGrading` (the input: creation modes of nonzero index count `R = 1/2`,
  i.e. `2R = 1`, and the actual ghost number), orthogonal for the ghost form `PG`;
* on the BRST space: the tensor grading (`brstDeg`), indexed by `((2R, gh), weight)`.

## Proved outright (from `hA`, `Unitary BB RB`, `IsPosOn PG ⊤` and the ghost grading)

* `brstDeg_orth` — orthogonality for the product form `matterGhostForm` (the form of
  `assemblyForm`); `brstDeg_span`; `brstDeg_isInternal`;
* `brstDeg_le_weight` — every piece lies in one conformal weight of `brstSVA`;
* `brstDeg_le_ghost` — every piece lies in one actual BRST ghost number;
* `relativeWeight_stable` — `relativeWeight n` is closed under all `R`-projections, **given**
  `ZeroModesPreserve` (the six relative constraints are `R`-homogeneous of degree `0`);
* `interpretedHalf n` — the minimal Lemma 3.16 input `GoodHalf` on `relativeWeight n`, with form
  `assemblyForm`, the interpreted grading, and the actual `relativeDifferential n`, **given**
  `RelativeDifferentialGood` (goodness of the actual `Q` for the interpreted grading);
* `interpretedGoodGeometry` — `ConcreteGoodGeometry n (assemblyForm BB RB PG n)` for every
  `n`, from the above and `InterpretedKahlerAnticomm` (the Kähler relation for the derived `𝐐⁺`
  of `ConcreteGoodDerived`). The second differential and the adjoint relation are *not* inputs.

## Named hypotheses (OPEN; each is a statement about the actual operators and the interpreted
grading, so none is vacuous)

* `GhostRGrading PG` — the ghost `R`-grading and its orthogonality for `PG`.
* `ZeroModesPreserve` — the total current zero modes and antighost zero modes map every
  interpreted piece into itself. Mathematically: Li-goodness of current zero modes on the corrected
  and PBW flags plus invariance of the forms (`J₀` preserves `F_p` and is skew, so it preserves
  layers), and `b₀` counts no nonzero-index mode.
* `RelativeDifferentialGood` — on relative states, `Q` maps `(2R, gh)` into
  `(2R ± 1, gh + 1)`: Beem–Garner's shortening `J_n = J_n^{[1]} + J_n^{[0]} + J_n^{[-1]}` with
  `J_n^{[1]} = 0` for `n ≥ 0` and `J_n^{[-1]} = 0` for `n ≤ 0`, for the actual flags.
  (Since proved for `ghostRGrading w`: `relativeDifferentialGood_of_affine`.)
* `InterpretedKahlerAnticomm` — `𝐐⁻ 𝐐⁺ + 𝐐⁺ 𝐐⁻ = 0` for the derived `𝐐⁺` (equivalent to the
  existence of Beem–Garner's second differential with the adjoint relation:
  `GoodHalf.exists_goodGeometry_iff`).
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open scoped TensorProduct

noncomputable section

/-! ### Generic: ghost number zero, unitary weight orthogonality -/

section Generic

universe u

/-- Ghost number zero: everything in ghost number `0`. -/
def zeroGhost (V : Type u) [AddCommGroup V] [Module ℂ V] (g : ℤ) : Submodule ℂ V :=
  if g = 0 then ⊤ else ⊥

theorem eq_zero_of_mem_zeroGhost {V : Type u} [AddCommGroup V] [Module ℂ V] {g : ℤ} {x : V}
    (hg : g ≠ 0) (hx : x ∈ zeroGhost V g) : x = 0 := by
  simpa [zeroGhost, hg] using hx

/-- The ghost-number projection of an index `((2R, gh), weight)`. -/
def ghIndex : (ℤ × ℤ) × ℂ →+ ℤ :=
  (AddMonoidHom.snd ℤ ℤ).comp (AddMonoidHom.fst (ℤ × ℤ) ℂ)

/-- The weight projection of an index. -/
def wtIndex : (ℤ × ℤ) × ℂ →+ ℂ := AddMonoidHom.snd (ℤ × ℤ) ℂ

@[simp] theorem ghIndex_apply (i : (ℤ × ℤ) × ℂ) : ghIndex i = i.1.2 := rfl
@[simp] theorem wtIndex_apply (i : (ℤ × ℤ) × ℂ) : wtIndex i = i.2 := rfl

theorem tmul_mem_zeroGhost {V W : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (k k' : ℤ) (x : V) (y : W) (hx : x ∈ zeroGhost V k)
    (hy : y ∈ zeroGhost W k') : x ⊗ₜ[ℂ] y ∈ zeroGhost (V ⊗[ℂ] W) (k + k') := by
  by_cases hk : k = 0
  · by_cases hk' : k' = 0
    · subst hk; subst hk'; simp [zeroGhost]
    · rw [eq_zero_of_mem_zeroGhost hk' hy, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_zeroGhost hk hx, TensorProduct.zero_tmul]; exact Submodule.zero_mem _

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem layerDeg_le_zeroGhost (B : InvariantForm W) (F : GradedFlag W) (i : (ℤ × ℤ) × ℂ) :
    layerDeg B F i ≤ zeroGhost 𝒱 (ghIndex i) := by
  by_cases h : i.1.2 = 0
  · simp [zeroGhost, h]
  · rw [layerDeg_ghost B F i h]; exact bot_le

theorem trivialDeg_le_zeroGhost (i : (ℤ × ℤ) × ℂ) :
    trivialDeg W i ≤ zeroGhost 𝒱 (ghIndex i) := by
  by_cases h : i.1.2 = 0
  · simp [zeroGhost, h]
  · rw [trivialDeg_ghost i h]; exact bot_le

/-- The ABLR form of a unitary factor is weight-orthogonal (in the `ℂ`-graded reading). -/
theorem unitaryCarrierForm_weight_orth (B : InvariantForm W) (R : RealStructure W) :
    ∀ h h' : ℂ, h ≠ h' → ∀ x ∈ W.toPreVertexAlgebra.gradingC h,
      ∀ y ∈ W.toPreVertexAlgebra.gradingC h', unitaryCarrierForm B R x y = 0 := by
  classical
  intro h h' hh x hx y hy
  by_cases hn : ∃ n : ℤ, (n : ℂ) = h
  · obtain ⟨n, rfl⟩ := hn
    by_cases hn' : ∃ n' : ℤ, (n' : ℂ) = h'
    · obtain ⟨n', rfl⟩ := hn'
      rw [PreVertexAlgebra.gradingC_intCast] at hx hy
      have hne : n ≠ n' := fun e => hh (by rw [e])
      exact internalForm_of_mem_ne W.isInternal _ hne hx hy
    · rw [PreVertexAlgebra.gradingC_of_not_int _ hn', Submodule.mem_bot] at hy
      rw [hy, SesqForm.zero_right]
  · rw [PreVertexAlgebra.gradingC_of_not_int _ hn, Submodule.mem_bot] at hx
    rw [hx, SesqForm.zero_left]

end Generic

/-! ### The ghost input -/

/-- **OPEN input: the ghost `R`-grading.** Index `((2R, gh), weight)`; intended: `2R` = number of
ghost creation modes of nonzero index (each has `R = 1/2`), `gh` = ghost number. It must be
orthogonal for the ghost form `PG`, span, and be compatible with the actual weight and ghost
gradings of `sl2GhostSVA`. -/
structure GhostRGrading (PG : SesqForm Sl2GhostSpace) where
  deg : (ℤ × ℤ) × ℂ → Submodule ℂ Sl2GhostSpace
  span : iSup deg = ⊤
  orth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, PG x y = 0
  le_weight : ∀ i, deg i ≤ sl2GhostSVA.grading (wtIndex i)
  le_ghost : ∀ i, deg i ≤ sl2GhostGrading (ghIndex i)

/-! ### The factor gradings -/

/-- `A`: the orthogonal layers of the corrected flag (`R = p` on layer `p`). -/
def aDeg : (ℤ × ℤ) × ℂ → Submodule ℂ ASpace := layerDeg affineForm affineFlag

/-- `B`: everything in `R = 0`. -/
def bDeg : (ℤ × ℤ) × ℂ → Submodule ℂ BSpace := trivialDeg BVOA

/-- `U`: the orthogonal layers of the ordinary PBW flag. -/
def uDeg : (ℤ × ℤ) × ℂ → Submodule ℂ USpace := layerDeg auxiliaryForm auxiliaryFlag

/-- The matter grading on `(A ⊗ B) ⊗ U`. -/
def matterDeg : (ℤ × ℤ) × ℂ → Submodule ℂ MatterSpace := tensorDeg (tensorDeg aDeg bDeg) uDeg

/-- **The interpreted `((2R, gh), weight)` grading of the BRST space.** -/
def brstDeg {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) :
    (ℤ × ℤ) × ℂ → Submodule ℂ BRSTSpace :=
  tensorDeg matterDeg Gh.deg

section Grading

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)

/-! #### Spanning and orthogonality (from `hA`) -/

theorem matterDeg_span (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    iSup matterDeg = ⊤ :=
  tensorDeg_span _ _ (tensorDeg_span _ _
    (layerDeg_span affineForm affineRealStructure affineFlag hA affineGramRefl)
    trivialDeg_span) (layerDeg_span _ _ _ auxiliaryGradedUnitary auxiliaryGramRefl)

theorem brstDeg_span (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    iSup (brstDeg Gh) = ⊤ :=
  tensorDeg_span _ _ (matterDeg_span hA) Gh.span

theorem brstDeg_orth (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) :
    ∀ a b, a ≠ b → ∀ x ∈ brstDeg Gh a, ∀ y ∈ brstDeg Gh b,
      matterGhostForm hA BB RB PG x y = 0 :=
  tensorDeg_orth _ _ _ _
    (tensorDeg_orth _ _ _ _
      (tensorDeg_orth _ _ _ _
        (layerDeg_orth affineForm affineRealStructure affineFlag hA affineGramRefl)
        (trivialDeg_orth _ (unitaryCarrierForm_weight_orth BB RB)))
      (layerDeg_orth _ _ _ auxiliaryGradedUnitary auxiliaryGramRefl))
    Gh.orth

/-! #### Weight and ghost-number compatibility (unconditional) -/

theorem matterDeg_le_weight (i : (ℤ × ℤ) × ℂ) : matterDeg i ≤ matterSVA.grading (wtIndex i) := by
  refine tensorDeg_le wtIndex _ _ abSVA.grading USVA.grading matterSVA.grading ?_ ?_ ?_ i
  · intro k k' x y hx hy
    exact TensorVA.tmul_mem_tenGrading abSVA USVA hx (by rwa [add_sub_cancel_left])
  · intro j
    refine tensorDeg_le wtIndex _ _ ASVA.grading BSVA.grading abSVA.grading ?_ ?_ ?_ j
    · intro k k' x y hx hy
      exact TensorVA.tmul_mem_tenGrading ASVA BSVA hx (by rwa [add_sub_cancel_left])
    · intro l; exact layerDeg_le_gradingC _ _ l
    · intro l; exact trivialDeg_le_gradingC l
  · intro j; exact layerDeg_le_gradingC _ _ j

theorem brstDeg_le_weight (i : (ℤ × ℤ) × ℂ) : brstDeg Gh i ≤ brstSVA.grading (wtIndex i) := by
  refine tensorDeg_le wtIndex _ _ matterSVA.grading sl2GhostSVA.grading brstSVA.grading ?_
    matterDeg_le_weight Gh.le_weight i
  intro k k' x y hx hy
  exact TensorVA.tmul_mem_tenGrading matterSVA sl2GhostSVA hx (by rwa [add_sub_cancel_left])

theorem matterDeg_le_zeroGhost (i : (ℤ × ℤ) × ℂ) :
    matterDeg i ≤ zeroGhost MatterSpace (ghIndex i) :=
  tensorDeg_le ghIndex _ _ _ _ _ (tmul_mem_zeroGhost)
    (tensorDeg_le ghIndex _ _ _ _ _ (tmul_mem_zeroGhost)
      (layerDeg_le_zeroGhost _ _) trivialDeg_le_zeroGhost)
    (layerDeg_le_zeroGhost _ _) i

theorem brstDeg_le_ghost (i : (ℤ × ℤ) × ℂ) :
    brstDeg Gh i ≤ leeYangBRSTComplex.ghost (ghIndex i) := by
  refine tensorDeg_le ghIndex _ _ (zeroGhost MatterSpace) sl2GhostGrading
    (matterGhostGrading MatterSpace) ?_ matterDeg_le_zeroGhost Gh.le_ghost i
  intro k k' x y hx hy
  by_cases hk : k = 0
  · subst hk
    rw [zero_add]
    exact tmul_mem_matterGhostGrading MatterSpace x hy
  · rw [eq_zero_of_mem_zeroGhost hk hx, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

/-! #### Internality (from positivity) -/

theorem brstDeg_isInternal (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (hG : IsPosOn PG ⊤) : DirectSum.IsInternal (brstDeg Gh) := by
  classical
  have hpos := weakGU_matterGhostForm hA hB hG
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ (brstDeg_span Gh hA)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), brstDeg Gh b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact brstDeg_orth Gh hA BB RB a b (Ne.symm hba) x hx y hy

end Grading

/-! ### The open operator inputs, stated for the interpreted grading -/

/-- The shift `gh ↦ gh - 1` of an index (the antighost zero mode). -/
def ghDown (i : (ℤ × ℤ) × ℂ) : (ℤ × ℤ) × ℂ := ((i.1.1, i.1.2 - 1), i.2)

theorem ghDown_injective : Function.Injective ghDown := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
  simp only [ghDown, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  subst h1; subst h3
  have : b = b' := by omega
  subst this; rfl

/-- **OPEN: the relative constraints are `R`-homogeneous of degree `0`.** The three total current
zero modes map every interpreted piece into itself, and the three antighost zero modes (which
remove `c_0`, of `R = 0` and weight `0`) map `((2R, gh), h)` into `((2R, gh - 1), h)`. -/
def ZeroModesPreserve {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) : Prop :=
  ∀ (a : Fin 3) (i : (ℤ × ℤ) × ℂ), ∀ x ∈ brstDeg Gh i,
    totalCurrentZero leeYangMatterAction.toAffineSl2Action a x ∈ brstDeg Gh i ∧
      antighostZero matterSVA a x ∈ brstDeg Gh (ghDown i)

/-- **Goodness of the actual differential for the interpreted grading** (Beem–Garner
Lemma 3.16): on relative states of weight `n`, `Q` maps `(2R, gh)` into `(2R ± 1, gh + 1)`; there
is no `ℜ`-preserving component.  Proved for the concrete ghost gradings `ghostRGrading w`
(`w > 0`), given `hA` and `hB`: `relativeDifferentialGood_of_affine`
(`BRSTGoodnessDifferential.lean`). -/
def RelativeDifferentialGood {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) : Prop :=
  ∀ (n j g : ℤ) (x : BRSTSpace), x ∈ relativeWeight n → x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    leeYangBRSTComplex.Q x ∈
      brstDeg Gh ((j + 1, g + 1), (n : ℂ)) ⊔ brstDeg Gh ((j - 1, g + 1), (n : ℂ))

section Relative

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem relativeWeight_stable (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (n : ℤ) :
    ProjStable (brstDeg_isInternal Gh hA hB hG) (relativeWeight n) := by
  classical
  have hI := brstDeg_isInternal Gh hA hB hG
  refine projStable_inf hI (projStable_inf hI ?_ ?_) ?_
  · exact projStable_iInf hI fun a => projStable_ker hI _ fun i x hx => (hZ a i x hx).1
  · exact projStable_iInf hI fun a =>
      projStable_ker_shift hI _ ghDown ghDown_injective fun i x hx => (hZ a i x hx).2
  · exact projStable_weight hI brstSVA.isInternal wtIndex (brstDeg_le_weight Gh) (n : ℂ)

/-- The interpreted grading at weight `n`, as subspaces of `relativeWeight n`. -/
def relDeg (n : ℤ) (a : ℤ × ℤ) : Submodule ℂ (relativeWeight n) :=
  (brstDeg Gh (a, (n : ℂ))).comap (relativeWeight n).subtype

theorem relDeg_span (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (n : ℤ) :
    iSup (relDeg Gh n) = ⊤ := by
  classical
  have hI := brstDeg_isInternal Gh hA hB hG
  have htop := iSup_comap_eq_top_of_stable hI (relativeWeight_stable Gh hA hB hG hZ n)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun i => ?_
  by_cases hi : i.2 = (n : ℂ)
  · obtain ⟨a, h⟩ := i
    simp only at hi
    subst hi
    exact le_iSup (relDeg Gh n) a
  · intro x hx
    have h1 : (x : BRSTSpace) ∈ brstSVA.grading i.2 := brstDeg_le_weight Gh i hx
    have h2 : (x : BRSTSpace) ∈ brstSVA.grading (n : ℂ) := x.2.2
    have hd := brstSVA.isInternal.submodule_iSupIndep.pairwiseDisjoint hi
    have : (x : BRSTSpace) = 0 := (Submodule.disjoint_def.mp hd) _ h1 h2
    have hx0 : x = 0 := Subtype.ext this
    rw [hx0]; exact Submodule.zero_mem _

theorem relDeg_orth (hA : GradedUnitary affineForm affineRealStructure affineFlag) (n : ℤ) :
    ∀ a b, a ≠ b → ∀ x ∈ relDeg Gh n a, ∀ y ∈ relDeg Gh n b,
      assemblyForm BB RB PG n x y = 0 := by
  intro a b hab x hx y hy
  rw [assemblyForm_eq hA]
  exact brstDeg_orth Gh hA BB RB (a, (n : ℂ)) (b, (n : ℂ)) (fun h => hab (congrArg Prod.fst h))
    x hx y hy

theorem relDeg_good (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh)
    (hD : RelativeDifferentialGood Gh) (n : ℤ) :
    ∀ a, ∀ x ∈ relDeg Gh n a,
      relativeDifferential n x ∈ relDeg Gh n (a + shQm) ⊔ relDeg Gh n (a + shSm) := by
  rintro ⟨j, g⟩ x hx
  have hI := brstDeg_isInternal Gh hA hB hG
  have hy := hD n j g x x.2 hx
  have hne : (((j, g) + shQm, (n : ℂ)) : (ℤ × ℤ) × ℂ) ≠ ((j, g) + shSm, (n : ℂ)) := by
    intro h
    have := congrArg (fun z => z.1.1) h
    simp only [shQm, shSm, Prod.mk_add_mk] at this
    omega
  have hQ : ((j, g) + shQm : ℤ × ℤ) = (j + 1, g + 1) := rfl
  have hS : ((j, g) + shSm : ℤ × ℤ) = (j - 1, g + 1) :=
    Prod.ext (show j + -1 = j - 1 by omega) rfl
  rw [← hQ, ← hS] at hy
  exact mem_sup_comap_of_stable hI (relativeWeight_stable Gh hA hB hG hZ n) hne
    (relativeDifferential n x) hy

/-- **The minimal Lemma 3.16 input for the actual relative complex at weight `n`**, with the
interpreted grading. -/
def interpretedHalf (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh)
    (hD : RelativeDifferentialGood Gh) (n : ℤ) :
    GoodHalf (relativeWeight n) where
  P := assemblyForm BB RB PG n
  deg := relDeg Gh n
  span := relDeg_span Gh hA hB hG hZ n
  orth := relDeg_orth Gh hA n
  D := relativeDifferential n
  D_good := relDeg_good Gh hA hB hG hZ hD n
  sq_zero := relativeDifferential_sq n

theorem interpretedHalf_pos (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh)
    (hD : RelativeDifferentialGood Gh)
    (n : ℤ) : IsPosOn (interpretedHalf Gh hA hB hG hZ hD n).P ⊤ :=
  assemblyForm_pos hA hB hG n

end Relative

/-- **OPEN: the Kähler relation for the derived second differential** at every weight. By
`GoodHalf.exists_goodGeometry_iff` this is exactly the existence of a Beem–Garner `𝐐⁺` satisfying
the adjoint relation and `𝐐⁻𝐐⁺ + 𝐐⁺𝐐⁻ = 0` on the interpreted geometry. -/
def InterpretedKahlerAnticomm {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh) : Prop :=
  ∀ n, (interpretedHalf Gh hA hB hG hZ hD n).KahlerAnticomm
    (interpretedHalf_pos Gh hA hB hG hZ hD n)

/-- **The Lemma 3.16 geometry of the old interface, from the interpreted inputs.** -/
def interpretedGoodGeometry {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)
    (hK : InterpretedKahlerAnticomm Gh hA hB hG hZ hD) (n : ℤ) :
    ConcreteGoodGeometry n (assemblyForm BB RB PG n) where
  geom := (interpretedHalf Gh hA hB hG hZ hD n).toGoodGeometry
    (interpretedHalf_pos Gh hA hB hG hZ hD n) (hK n)
  P_eq := rfl
  D_eq := rfl
  ghost := fun a _ hx => brstDeg_le_ghost Gh (a, (n : ℂ)) hx

/-- The geometry's bigrading is literally the interpreted one. -/
theorem interpretedGoodGeometry_deg {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)
    (hK : InterpretedKahlerAnticomm Gh hA hB hG hZ hD) (n : ℤ) (a : ℤ × ℤ) :
    (interpretedGoodGeometry Gh hA hB hG hZ hD hK n).geom.deg a =
      (brstDeg Gh (a, (n : ℂ))).comap (relativeWeight n).subtype := rfl

end

end VOA.ConcreteHodge
