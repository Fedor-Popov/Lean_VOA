import VOA.Huang.GenusOneG1fSkew
import VOA.Huang.GenusOneG1fSepSpan
import VOA.Huang.RepPackagingSemisimple

/-!
# The `(b,a)` channels in terms of the universal `(a,b)` bracket modes

* `postcompose_skewModes`: module maps commute with FHL's skew operator `Ω`;
* `braid`: the morphism `R' : M_a ⊠ M_b → M_b ⊠ M_a` with `R' ∘ 𝒴_{ab} = Ω⁻¹(𝒴_{ba})`, so that
  `q ∘ 𝒴_{ba} = Ω(q ∘ R' ∘ 𝒴_{ab})` for every module map `q` (`postcompose_ba_eq_skew`);
* `traceFunction_bracketModes_skew`: for ANY lowest-weight target and any outer intertwiner,
  the one-point function of `Ω(Y)[w_q]_n w_p` is `e^{iπ(−n−1)}` times that of `Y[w_p]_n w_q`
  (the `L[−1]`-descendants are killed by `trace_cylT`);
* `vacuum_hom_unique`: `Hom(V, M_b ⊠ M_a)` is spanned by any nonzero element (finite
  semisimplicity `semisimple_lw_pbw` + `vacuum_pairing_le_one` + Schur).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open VOA VOA.Huang Complex CategoryTheory CategoryTheory.Limits
open VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.TensorCat
  VOA.Huang.VerlindeTransport VOA.Huang.FusionUnit
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes transportedModes_apply
  inverse_square_translation)
open VOA.Huang.GenusTwoPoint (vacuumLW)
open VOA.Huang.GenusTwoPoint.Separate (normalizedCoordinateChange)
open VOA.Huang.FusionProduct (postcompose)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1 Skew-symmetry commutes with module maps -/

section Skew

variable {M₁ M₂ M₃ M₄ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂]
  [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}

theorem hom_Lm1_pow (g : homSpace A₃ A₄) (j : ℕ) (y : M₃) :
    g.val (((VOA.SkewIntertwiner.Lm1 A₃.toWeakModule) ^ j) y) =
      ((VOA.SkewIntertwiner.Lm1 A₄.toWeakModule) ^ j) (g.val y) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    exact g.property W.conformalVector 0 _

theorem postcompose_skewModes (Y : IntertwiningOperator A₁ A₂ A₃) (g : homSpace A₃ A₄)
    (c : ℂ → ℂ) (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) :
    (postcompose (BraidingSkew.skewMap A₁ A₂ A₃ hc hc0 Y) A₄ g).val =
      BraidingSkew.skewModes (VOA.SkewIntertwiner.Lm1 A₄.toWeakModule) c
        (postcompose Y A₄ g).val := by
  funext n
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  have hT : BraidingSkew.Trunc Y.val := BraidingSkew.trunc_of_isIntertwining Y.property
  have hT' : BraidingSkew.Trunc (postcompose Y A₄ g).val :=
    BraidingSkew.trunc_of_isIntertwining (postcompose Y A₄ g).property
  change g.val (BraidingSkew.skewModes _ c Y.val n w₂ w₁) = _
  rw [BraidingSkew.skewModes_apply hT, BraidingSkew.skewModes_apply hT']
  obtain ⟨K, hK⟩ := hT.bound w₁ w₂ n
  rw [BraidingSkew.sSum_eq_sum K hK, BraidingSkew.sSum_eq_sum K (fun j hj => by
      change g.val (Y.val (n + j) w₁ w₂) = 0
      rw [hK j hj, map_zero]),
    map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [BraidingSkew.sTerm, BraidingSkew.sTerm, map_smul, hom_Lm1_pow]
  rfl

end Skew

/-! ## §2 Bracket skew-symmetry at trace level, any lowest-weight target -/

section TraceSkew

theorem coordinateChange_Lm1_pow' (N : LWModule W) (j : ℕ) (y : N.carrier) :
    normalizedCoordinateChange N
        (((VOA.SkewIntertwiner.Lm1 N.isMod.toWeakModule) ^ j) y) =
      ((sqL N.isMod (-1)) ^ j) (normalizedCoordinateChange N y) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    have h := inverse_square_translation N (normalizedCoordinateChange N
        (((VOA.SkewIntertwiner.Lm1 N.isMod.toWeakModule) ^ j) y))
    rw [LinearEquiv.symm_apply_apply] at h
    have h2 := congrArg (normalizedCoordinateChange N) h
    rw [LinearEquiv.apply_symm_apply] at h2
    exact h2.symm

variable {M₁ M : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {A : OrdVModule W M₁} {Nt : OrdVModule W M}

theorem traceFunction_sqL_negOne (Yo : IntertwiningOperator A Nt Nt) (h : ℂ) (u : M₁)
    (τ : UpperHalfPlane) : traceFunction Yo h (sqL A (-1) u) τ = 0 := by
  have h0 : VOA.Huang.GenusOne.trace Yo (sqL A (-1) u) = VOA.Huang.GenusOne.trace Yo 0 := by
    rw [VOA.Huang.GenusOne.sqL_negOne, VOA.Huang.GenusOne.trace_cylT, map_zero]
  have hz := VOA.Huang.GenusOneG1e.traceFunction_zero Yo h τ
  unfold traceFunction at hz ⊢
  rw [h0]
  exact hz

theorem traceFunction_sqL_negOne_pow (Yo : IntertwiningOperator A Nt Nt) (h : ℂ) (u : M₁)
    (τ : UpperHalfPlane) (j : ℕ) :
    traceFunction Yo h (((sqL A (-1)) ^ (j + 1)) u) τ = 0 := by
  rw [pow_succ', Module.End.mul_apply]
  exact traceFunction_sqL_negOne Yo h _ τ

/-- **Trace-level bracket skew-symmetry, any lowest-weight target.** -/
theorem traceFunction_bracketModes_skew (hC2 : C2Cofinite W) {P Q N R : LWModule W}
    (hN : N.isMod.IsIrreducible) (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (Y' : IntertwiningOperator Q.isMod P.isMod N.isMod)
    (hY' : Y'.val = BraidingSkew.skewModes
      (VOA.SkewIntertwiner.Lm1 N.isMod.toWeakModule) BraidingSkew.omegaPhase Y.val)
    (Yo : IntertwiningOperator N.isMod R.isMod R.isMod) {h : ℂ}
    (hcw : HasConformalWeight R.isMod h) (n : ℂ) (wq : Q.carrier) (wp : P.carrier)
    (τ : UpperHalfPlane) :
    traceFunction Yo h (bracketModes Y' n wq wp) τ =
      exp ((Real.pi : ℂ) * I * (-n - 1)) * traceFunction Yo h (bracketModes Y n wp wq) τ := by
  let ℓ := VOA.Huang.GenusOneG1e.tfLin hC2 hN Yo hcw τ
  have hℓ : ∀ v, ℓ v = traceFunction Yo h v τ := fun v => rfl
  rw [← hℓ, ← hℓ, normalizedIntertwinerSubstitution_holds Y' n wq wp,
    normalizedIntertwinerSubstitution_holds Y n wp wq, transportedModes_apply,
    transportedModes_apply, hY']
  set wp' := (normalizedCoordinateChange P).symm wp
  set wq' := (normalizedCoordinateChange Q).symm wq
  have hT : BraidingSkew.Trunc Y.val :=
    BraidingSkew.trunc_of_isIntertwining Y.property
  obtain ⟨K, hK⟩ := hT.bound wp' wq' n
  rw [BraidingSkew.skewModes_apply hT,
    BraidingSkew.sSum_eq_sum (K + 1) (fun j hj => hK j (by omega)), Finset.sum_range_succ',
    map_smul, map_smul, map_add, map_add, map_sum, map_sum]
  have hz : ∀ j ∈ Finset.range K, ℓ (normalizedCoordinateChange N
      (BraidingSkew.sTerm (VOA.SkewIntertwiner.Lm1 N.isMod.toWeakModule) Y.val n wp' wq'
        (j + 1))) = 0 := by
    intro j _
    rw [BraidingSkew.sTerm, map_smul, coordinateChange_Lm1_pow', map_smul, hℓ,
      traceFunction_sqL_negOne_pow, smul_zero]
  rw [Finset.sum_eq_zero hz, zero_add, BraidingSkew.sTerm, pow_zero, Module.End.one_apply,
    map_smul, map_smul, Nat.cast_zero, add_zero]
  simp only [BraidingSkew.sc, BraidingSkew.omegaPhase, Nat.factorial_zero, Nat.cast_one,
    inv_one, pow_zero, mul_one, smul_eq_mul, one_mul]
  rw [show -(↑Real.pi * I) * (n + 1) = (Real.pi : ℂ) * I * (-n - 1) by ring]

end TraceSkew

/-! ## §3 The braiding morphism -/

section Braid

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (F : FusionChoice W)
  (D : VOA.ModularData W ι) (a b : ι)

/-- `Ω⁻¹(𝒴_{ba})`, an intertwiner of type `(M_b ⊠ M_a / M_a M_b)`. -/
def braidZ : IntertwiningOperator (famObj D a).isMod (famObj D b).isMod
    (tensorObj F (famObj D b) (famObj D a)).isMod :=
  (BraidingSkew.skewEquiv (famObj D a).isMod (famObj D b).isMod
    (tensorObj F (famObj D b) (famObj D a)).isMod BraidingSkew.omegaPhase_succ
    BraidingSkew.omegaPhase_ne_zero).symm (F (famObj D b) (famObj D a)).intertwiner

/-- The braiding-type morphism `R' : M_a ⊠ M_b → M_b ⊠ M_a`, `R' ∘ 𝒴_{ab} = Ω⁻¹(𝒴_{ba})`. -/
def braidR : tensorObj F (famObj D a) (famObj D b) ⟶ tensorObj F (famObj D b) (famObj D a) :=
  (F (famObj D a) (famObj D b)).lift (tensorObj F (famObj D b) (famObj D a)).isMod
    (braidZ F D a b)

/-- **`q ∘ 𝒴_{ba} = Ω(q ∘ R' ∘ 𝒴_{ab})`.** -/
theorem postcompose_ba_eq_skew {T : Ordinary W}
    (q : tensorObj F (famObj D b) (famObj D a) ⟶ T) :
    (postcompose (F (famObj D b) (famObj D a)).intertwiner T.isMod q).val =
      BraidingSkew.skewModes (VOA.SkewIntertwiner.Lm1 T.isMod.toWeakModule)
        BraidingSkew.omegaPhase
        (postcompose (F (famObj D a) (famObj D b)).intertwiner T.isMod
          (braidR F D a b ≫ q)).val := by
  have hE : BraidingSkew.skewMap (famObj D a).isMod (famObj D b).isMod
      (tensorObj F (famObj D b) (famObj D a)).isMod BraidingSkew.omegaPhase_succ
      BraidingSkew.omegaPhase_ne_zero (braidZ F D a b) =
        (F (famObj D b) (famObj D a)).intertwiner :=
    LinearEquiv.apply_symm_apply (BraidingSkew.skewEquiv (famObj D a).isMod (famObj D b).isMod
      (tensorObj F (famObj D b) (famObj D a)).isMod BraidingSkew.omegaPhase_succ
      BraidingSkew.omegaPhase_ne_zero) (F (famObj D b) (famObj D a)).intertwiner
  rw [← hE]
  refine (postcompose_skewModes (braidZ F D a b) q _ _ _).trans ?_
  congr 1
  have hZ : postcompose (F (famObj D a) (famObj D b)).intertwiner
      (tensorObj F (famObj D b) (famObj D a)).isMod (braidR F D a b) = braidZ F D a b :=
    (F (famObj D a) (famObj D b)).lift_spec _ _
  rw [← hZ]
  rfl

end Braid

/-! ## §4 `Hom(V, M_b ⊠ M_a)` is one-dimensional -/

section HomUnique

theorem exists_smul_of_finrank_le_one {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (h : Module.finrank ℂ E ≤ 1) {v : E} (hv : v ≠ 0) (x : E) :
    ∃ c : ℂ, x = c • v := by
  have hpos : 0 < Module.finrank ℂ E := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp (le_antisymm h hpos) x
  exact ⟨c, hc.symm⟩

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Maps `M_b ⊠ M_a → V` form a space in which any nonzero element spans. -/
theorem out_hom_smul (hV : Nice W) (F : FusionChoice W) (D : VOA.ModularData W ι) (a b : ι)
    {ψ₀ : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (h0 : ψ₀ ≠ 0)
    (ψ : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) : ∃ μ : ℂ, ψ = μ • ψ₀ := by
  obtain ⟨hfin, hle⟩ := vacuum_pairing_le_one D hV a b
  let P := postcompose (F (famObj D b) (famObj D a)).intertwiner (adjointModule W)
  have hP0 : (P ψ₀ : intertwiningSpace (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W))
      ≠ 0 := fun h => h0 (postcompose_eq_zero ψ₀ h)
  obtain ⟨μ, hμ⟩ := exists_smul_of_finrank_le_one hle hP0 (P ψ)
  refine ⟨μ, ?_⟩
  have hinj : P ψ = P (μ • ψ₀) := hμ.trans (map_smul P μ ψ₀).symm
  have e1 := TensorCat.lift_postcompose F ψ
  have e2 := TensorCat.lift_postcompose F (μ • ψ₀)
  change (F (famObj D b) (famObj D a)).lift (adjointModule W) (P ψ) = ψ at e1
  change (F (famObj D b) (famObj D a)).lift (adjointModule W) (P (μ • ψ₀)) = μ • ψ₀ at e2
  rw [← e1, ← e2, hinj]

/-- **`Hom(V, M_b ⊠ M_a)` is spanned by any nonzero element** (nice `V`). -/
theorem vacuum_hom_unique (hV : Nice W) (F : FusionChoice W) (D : VOA.ModularData W ι)
    (a b : ι) (hv : W.vacuum ≠ 0) {η0 : (vacuumObject : Ordinary W) ⟶
      tensorObj F (famObj D b) (famObj D a)} (hη0 : η0 ≠ 0)
    (f : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) :
    ∃ μ : ℂ, f = μ • η0 := by
  classical
  obtain ⟨n, R, hR, ⟨e⟩⟩ := TensorCat.RepPackaging.semisimple_lw_pbw hV.1
    (tensorObj F (famObj D b) (famObj D a))
  have iV : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.1.simple
  let X := tensorObj F (famObj D b) (famObj D a)
  let pj : ∀ j, X ⟶ Ordinary.of (R j).isMod := fun j =>
    e.hom ≫ biproduct.π (fun j => Ordinary.of (R j).isMod) j
  let ij : ∀ j, Ordinary.of (R j).isMod ⟶ X := fun j =>
    biproduct.ι (fun j => Ordinary.of (R j).isMod) j ≫ e.inv
  have htot : ∑ j, pj j ≫ ij j = 𝟙 X := by
    have h1 : ∑ j, pj j ≫ ij j = e.hom ≫ (∑ j, biproduct.π (fun j => Ordinary.of (R j).isMod) j ≫
        biproduct.ι (fun j => Ordinary.of (R j).isMod) j) ≫ e.inv := by
      simp only [pj, ij, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    rw [h1, biproduct.total, Category.id_comp, e.hom_inv_id]
  have hii : ∀ j, ij j ≫ pj j = 𝟙 _ := by
    intro j
    simp only [pj, ij, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self]
  have hik : ∀ j k, j ≠ k → ij j ≫ pj k = 0 := by
    intro j k hjk
    simp only [pj, ij, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_ne _ hjk]
  have hdecomp : ∀ h : (vacuumObject : Ordinary W) ⟶ X, h = ∑ j, (h ≫ pj j) ≫ ij j := by
    intro h
    conv_lhs => rw [← Category.comp_id h, ← htot]
    rw [Preadditive.comp_sum]
    simp only [Category.assoc]
  have hbij : ∀ j (g : (vacuumObject : Ordinary W) ⟶ Ordinary.of (R j).isMod), g ≠ 0 →
      Function.Bijective g.val := fun j g hg =>
    bijective_of_hom (A₂ := adjointModule W) (A₃ := (R j).isMod) iV (hR j) g.property
      (fun h => hg (Subtype.ext h))
  have hVid : (𝟙 (vacuumObject : Ordinary W)) ≠ 0 := vacuumObject_id_ne_zero hv
  -- a summand carrying `η0`
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, η0 ≫ pj j₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hη0
    rw [hdecomp η0]
    exact Finset.sum_eq_zero fun j _ => by rw [hall j, zero_comp]
  -- no other summand receives a map from `V`
  have hother : ∀ j, j ≠ j₀ → ∀ g : (vacuumObject : Ordinary W) ⟶ Ordinary.of (R j).isMod,
      g = 0 := by
    intro j hj g
    by_contra hg
    let gi := (TensorCat.RepPackaging.isoOfBijective g (hbij j g hg)).inv
    let g0i := (TensorCat.RepPackaging.isoOfBijective (η0 ≫ pj j₀)
      (hbij j₀ _ hj₀)).inv
    have hgi : g ≫ gi = 𝟙 _ := (TensorCat.RepPackaging.isoOfBijective g (hbij j g hg)).hom_inv_id
    have hg0i : (η0 ≫ pj j₀) ≫ g0i = 𝟙 _ :=
      (TensorCat.RepPackaging.isoOfBijective (η0 ≫ pj j₀) (hbij j₀ _ hj₀)).hom_inv_id
    have hgi0 : gi ≠ 0 := fun h => hVid (by rw [← hgi, h, comp_zero])
    have hg0i0 : g0i ≠ 0 := fun h => hVid (by rw [← hg0i, h, comp_zero])
    have hψ0 : pj j₀ ≫ g0i ≠ 0 := by
      intro h
      apply hg0i0
      rw [← Category.id_comp g0i, ← hii j₀, Category.assoc, h, comp_zero]
    obtain ⟨μ, hμ⟩ := out_hom_smul hV F D a b hψ0 (pj j ≫ gi)
    have h1 := congrArg (fun k => ij j ≫ k) hμ
    simp only at h1
    rw [← Category.assoc, hii, Category.id_comp, Linear.comp_smul, ← Category.assoc,
      hik j j₀ hj, zero_comp, smul_zero] at h1
    exact hgi0 h1
  have hconc : ∀ h : (vacuumObject : Ordinary W) ⟶ X, h = (h ≫ pj j₀) ≫ ij j₀ := by
    intro h
    conv_lhs => rw [hdecomp h]
    rw [Finset.sum_eq_single j₀]
    · intro j _ hj
      rw [hother j hj (h ≫ pj j), zero_comp]
    · intro h'; exact absurd (Finset.mem_univ j₀) h'
  have hfl := finite_and_finrank_homSpace_le_one (P₂ := vacuumLW W hv) (P₃ := R j₀) iV (hR j₀)
  haveI : FiniteDimensional ℂ ((vacuumObject : Ordinary W) ⟶ Ordinary.of (R j₀).isMod) := hfl.1
  have hle : Module.finrank ℂ ((vacuumObject : Ordinary W) ⟶ Ordinary.of (R j₀).isMod) ≤ 1 :=
    hfl.2
  obtain ⟨μ, hμ⟩ := exists_smul_of_finrank_le_one hle hj₀ (f ≫ pj j₀)
  refine ⟨μ, ?_⟩
  rw [hconc f, hμ, Linear.smul_comp, ← hconc η0]

end HomUnique

end VOA.Huang.GenusOneG1f
