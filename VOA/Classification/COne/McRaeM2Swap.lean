import VOA.Classification.COne.McRaeM2Main

/-!
# McRae's route: the contragredient sends projectives to injectives

For a `C₂`-cofinite VOA, on finite-length weak modules:

* `isFiniteLength_contra` — the contragredient of a finite-length module has finite length
  (annihilators reverse the submodule lattice);
* `IsInjFL` — injectivity relative to finite-length weak modules (dual to `OrbMcRae.IsProjFL`);
* `isInjFL_contra_of_isProjFL` — if `P` is projective (relative to finite-length modules),
  its contragredient `P'` is injective.

So the contragredient of a Huang cover `P_{S'}` is an injective module with essential simple socle
`S` (`transpose_le_of_superfluous`): an injective hull of `S`.  `CoverDualLitFact` says exactly
that the projective cover of `S` is this injective hull.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.OrbMcRae VOA.Classification.COne.McRaeM1
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}

/-- The contragredient of a finite-length generalized-eigenspace-graded module has finite
length. -/
theorem isFiniteLength_contra (N : GWModule W M) (hN : IsGenGraded N)
    (hfl : IsFiniteLength (modeAlg N.toWeakModule) M) :
    IsFiniteLength (modeAlg (contra N).toWeakModule) (RestrictedDual N) := by
  obtain ⟨hNo, hAr⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI : WellFoundedGT (Submodule (modeAlg N.toWeakModule) M) := isNoetherian_iff'.mp hNo
  haveI : WellFoundedLT (Submodule (modeAlg N.toWeakModule) M) := hAr
  let e := (perpIsoGen N hN).symm
  have h1 : WellFoundedLT (Submodule (modeAlg (Dm N).toWeakModule) (RestrictedDual N))ᵒᵈ :=
    e.strictMono.wellFoundedLT
  have h2 : WellFoundedGT (Submodule (modeAlg (Dm N).toWeakModule) (RestrictedDual N))ᵒᵈ :=
    e.strictMono.wellFoundedGT
  haveI : WellFoundedGT (Submodule (modeAlg (Dm N).toWeakModule) (RestrictedDual N)) := h1
  haveI : WellFoundedLT (Submodule (modeAlg (Dm N).toWeakModule) (RestrictedDual N)) := h2
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff'.mpr inferInstance, inferInstance⟩

/-- `⟨φ, ι x⟩ = ⟨x, φ⟩` for every `φ` (not necessarily homogeneous). -/
theorem pairing_iota_all (N : GWModule W M) (φ : RestrictedDual N) (x : M) :
    dualPairing (contra N) φ (iota N x) = dualPairing N x φ := by
  obtain ⟨s, -, hsum⟩ := exists_sum_cmp (Dm N) φ
  rw [← hsum, pr_sum_left, map_sum]
  exact Finset.sum_congr rfl fun α _ => pairing_iota N (cmp_mem (Dm N) α φ) x

/-- **Injectivity relative to finite-length weak modules** (dual to `OrbMcRae.IsProjFL`). -/
def IsInjFL {I : Type u} [AddCommGroup I] [Module ℂ I] (BI : WeakModule W I) : Prop :=
  ∀ {Y Z : Type u} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (BY : WeakModule W Y) (BZ : WeakModule W Z),
    IsFiniteLength (modeAlg BZ) Z →
    ∀ g : BY.Hom BZ, Function.Injective g.toLinearMap →
    ∀ f : BY.Hom BI, ∃ k : BZ.Hom BI, ∀ y, k.toLinearMap (g.toLinearMap y) = f.toLinearMap y

/-- **The contragredient of a projective is injective** (finite-length weak modules of a
`C₂`-cofinite VOA). -/
theorem isInjFL_contra_of_isProjFL (hC2 : C2Cofinite W) {P : Type u} [AddCommGroup P]
    [Module ℂ P] (BP : WeakModule W P) (hfl : IsFiniteLength (modeAlg BP) P)
    (hproj : IsProjFL BP) : IsInjFL (contra (gwOfFiniteLength hC2 BP hfl)).toWeakModule := by
  intro Y Z _ _ _ _ BY BZ hZ g hg f
  have hY : IsFiniteLength (modeAlg BY) Y := finiteLength_of_injective_hom g hg hZ
  let Pg := gwOfFiniteLength hC2 BP hfl
  let Yg := gwOfFiniteLength hC2 BY hY
  let Zg := gwOfFiniteLength hC2 BZ hZ
  have hPg : IsGenGraded Pg := isGenGraded_gwOfFiniteLength hC2 BP hfl
  have hYg : IsGenGraded Yg := isGenGraded_gwOfFiniteLength hC2 BY hY
  have hZg : IsGenGraded Zg := isGenGraded_gwOfFiniteLength hC2 BZ hZ
  have hgr := gradedHom_of_isGenGraded Yg Zg g hYg hZg
  let gt := transpose Yg Zg g hgr
  have hgt : Function.Surjective gt.toLinearMap :=
    transpose_surjective_of_injective Yg Zg g hgr hg
  have hfgr := gradedHom_of_isGenGraded Yg (contra Pg) f hYg (isGenGraded_contra Pg hPg)
  let ft := transpose Yg (contra Pg) f hfgr
  obtain ⟨k, hk⟩ := hproj (contra Zg).toWeakModule (contra Yg).toWeakModule
    (isFiniteLength_contra Zg hZg hZ) gt hgt (homComp ft (iotaHom Pg))
  have hkgr := gradedHom_of_isGenGraded Pg (contra Zg) k hPg (isGenGraded_contra Zg hZg)
  refine ⟨homComp (transpose Pg (contra Zg) k hkgr) (iotaHom Zg), fun y => ?_⟩
  apply restrictedDual_ext_of_pairing Pg
  intro α x hx
  change dualPairing Pg x (transposeL Pg (contra Zg) k hkgr (iota Zg (g.toLinearMap y))) =
    dualPairing Pg x (f.toLinearMap y)
  rw [pairing_transposeL Pg (contra Zg) k hkgr hx, pairing_iota Zg (hkgr α x hx),
    ← pairing_transposeL_all Yg Zg g hgr y]
  have hkx := hk x
  change transposeL Yg Zg g hgr (k.toLinearMap x) =
    transposeL Yg (contra Pg) f hfgr (iota Pg x) at hkx
  rw [hkx, pairing_transposeL_all Yg (contra Pg) f hfgr y, pairing_iota_all Pg]

/-- **Injective hulls from projective covers.**  For a simple `S` and a Huang cover `D` of
`S' = contra S`, the module `I = (P_{S'})'` is injective (relative to finite-length modules), of
finite length, and contains `S` as an essential simple socle. -/
theorem injHull_of_cover (hC2 : C2Cofinite W) {X : Type u} [AddCommGroup X] [Module ℂ X]
    (B : WeakModule W X) (hB : IsSimpleModule (modeAlg B) X)
    (D : HuangCover (contra (gwOfFiniteLength hC2 B (finiteLength_of_simple hB))).toWeakModule) :
    IsInjFL (contra (gwOfFiniteLength hC2 D.BP D.finiteLength)).toWeakModule ∧
      IsFiniteLength (modeAlg (contra (gwOfFiniteLength hC2 D.BP D.finiteLength)).toWeakModule)
        (RestrictedDual (gwOfFiniteLength hC2 D.BP D.finiteLength)) ∧
      ∃ i : B.Hom (contra (gwOfFiniteLength hC2 D.BP D.finiteLength)).toWeakModule,
        Function.Injective i.toLinearMap ∧
        ∀ N : Submodule (modeAlg (contra (gwOfFiniteLength hC2 D.BP D.finiteLength)).toWeakModule)
          (RestrictedDual (gwOfFiniteLength hC2 D.BP D.finiteLength)), N ≠ ⊥ → modeMap i ⊤ ≤ N := by
  let Sg := gwOfFiniteLength hC2 B (finiteLength_of_simple hB)
  have hSg : IsGenGraded Sg := isGenGraded_gwOfFiniteLength hC2 B _
  let G := gwOfFiniteLength hC2 D.BP D.finiteLength
  have hG : IsGenGraded G := isGenGraded_gwOfFiniteLength hC2 D.BP D.finiteLength
  have hq := gradedHom_of_isGenGraded G (contra Sg) D.p hG (isGenGraded_contra Sg hSg)
  let qt := transpose G (contra Sg) D.p hq
  have hqt : Function.Injective qt.toLinearMap :=
    transpose_injective_of_surjective G (contra Sg) D.p hq D.surj
  refine ⟨isInjFL_contra_of_isProjFL hC2 D.BP D.finiteLength D.proj,
    isFiniteLength_contra G hG D.finiteLength, homComp qt (iotaHom Sg), ?_, ?_⟩
  · intro a b hab
    exact iota_injective Sg (hqt hab)
  · intro N hN
    rw [modeMap_homComp]
    exact le_trans (modeMap_mono qt le_top)
      (transpose_le_of_superfluous G (contra Sg) D.p hq hG (isGenGraded_contra Sg hSg)
        D.superfluous (isSimple_contra Sg hSg hB) N hN)

end VOA.C2Rigid
