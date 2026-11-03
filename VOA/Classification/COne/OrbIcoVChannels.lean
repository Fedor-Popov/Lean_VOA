import VOA.Classification.COne.OrbIcoVChannelRigidity

/-! Actual projections onto the vacuum and spin-six Virasoro channels.
Their domain contains every icosahedral state of conformal weight below 100. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbIcoS OrbC2c
  VOA.LatGen VOA.LatGen.Triplet

abbrev TwoSeed := OrbIcoS.twoSeedSpan

def twoSeedEmbedding : TwoSeed →ₗ[ℂ] Sp :=
  (orbifold ico).carrier.subtype.comp TwoSeed.subtype

theorem twoSeedEmbedding_injective : Function.Injective twoSeedEmbedding := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact he

theorem spinCasimir_virWord (ks : List ℕ) (x : (orbifold ico).carrier) :
    spinCasimir ((virWord Wi ks x : (orbifold ico).carrier) : Sp) = virWord V2v ks (spinCasimir (x : Sp)) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    change spinCasimir (V2v.L (-(k : ℤ) - 1) ((virWord Wi ks x : (orbifold ico).carrier) : Sp)) = _
    rw [spinCasimir_L, ih]
    rfl

theorem virWord_coe (ks : List ℕ) (x : (orbifold ico).carrier) :
    ((virWord Wi ks x : (orbifold ico).carrier) : Sp) = virWord V2v ks (x : Sp) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => change V2v.L _ ((virWord Wi ks x : (orbifold ico).carrier) : Sp) = _; rw [ih]; rfl

theorem spinCasimir_word_vacuum (ks : List ℕ) :
    spinCasimir ((virWord Wi ks Wi.vacuum : (orbifold ico).carrier) : Sp) = 0 := by
  rw [spinCasimir_virWord]
  change virWord V2v ks (spinCasimir V2v.vacuum) = 0
  rw [spinCasimir_vacuum]
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [virWord, ih, map_zero]

theorem spinCasimir_word_Xico (ks : List ℕ) :
    spinCasimir ((virWord Wi ks Xico : (orbifold ico).carrier) : Sp) = (168 : ℂ) • ((virWord Wi ks Xico : (orbifold ico).carrier) : Sp) := by
  rw [spinCasimir_virWord, spinCasimir_Xico, virWord_coe]
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [virWord, ih, map_smul]

theorem spinCasimir_mem_range (v : (orbifold ico).carrier) (hv : v ∈ TwoSeed) :
    spinCasimir (v : Sp) ∈ twoSeedEmbedding.range := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨ks, rfl | rfl⟩ := hv
    · rw [spinCasimir_word_vacuum]
      exact Submodule.zero_mem _
    · rw [spinCasimir_word_Xico]
      apply Submodule.smul_mem
      exact LinearMap.mem_range.mpr ⟨⟨virWord Wi ks Xico,
        Submodule.subset_span ⟨ks, Or.inr rfl⟩⟩, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    change spinCasimir ((x : Sp) + (y : Sp)) ∈ _
    rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    change spinCasimir (c • (x : Sp)) ∈ _
    rw [map_smul]; exact Submodule.smul_mem _ c hx

def twoSeedCasimir : Module.End ℂ TwoSeed :=
  (LinearEquiv.ofInjective twoSeedEmbedding twoSeedEmbedding_injective).symm.toLinearMap.comp
    ((spinCasimir.comp twoSeedEmbedding).codRestrict twoSeedEmbedding.range
      (fun x => spinCasimir_mem_range x.val x.property))

theorem twoSeedCasimir_coe (x : TwoSeed) :
    twoSeedEmbedding (twoSeedCasimir x) = spinCasimir (twoSeedEmbedding x) := by
  exact LinearEquiv.ofInjective_symm_apply
    (h := twoSeedEmbedding_injective)
    (x := ((spinCasimir.comp twoSeedEmbedding).codRestrict twoSeedEmbedding.range
      (fun x => spinCasimir_mem_range x.val x.property)) x)

theorem spinCasimir_square (v : (orbifold ico).carrier) (hv : v ∈ TwoSeed) :
    spinCasimir (spinCasimir (v : Sp)) = (168 : ℂ) • spinCasimir (v : Sp) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨ks, rfl | rfl⟩ := hv
    · rw [spinCasimir_word_vacuum, map_zero, smul_zero]
    · rw [spinCasimir_word_Xico, map_smul, spinCasimir_word_Xico]
  | zero => simp
  | add x y _ _ hx hy =>
    change spinCasimir (spinCasimir ((x : Sp) + (y : Sp))) =
      (168 : ℂ) • spinCasimir ((x : Sp) + (y : Sp))
    simp only [map_add, hx, hy, smul_add]
  | smul c x _ hx =>
    change spinCasimir (spinCasimir (c • (x : Sp))) =
      (168 : ℂ) • spinCasimir (c • (x : Sp))
    simp only [map_smul, hx]
    exact smul_comm c 168 _

theorem twoSeedCasimir_square : twoSeedCasimir * twoSeedCasimir = (168 : ℂ) • twoSeedCasimir := by
  apply LinearMap.ext
  intro x
  apply twoSeedEmbedding_injective
  simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, twoSeedCasimir_coe]
  exact spinCasimir_square x.val x.property

def sixthProjection : Module.End ℂ TwoSeed := (1 / 168 : ℂ) • twoSeedCasimir

def vacuumProjection : Module.End ℂ TwoSeed := LinearMap.id - sixthProjection

theorem sixthProjection_idempotent : sixthProjection * sixthProjection = sixthProjection := by
  rw [sixthProjection, smul_mul_smul_comm, twoSeedCasimir_square, smul_smul]
  norm_num

theorem vacuumProjection_idempotent : vacuumProjection * vacuumProjection = vacuumProjection := by
  apply LinearMap.ext
  intro x
  have hp := LinearMap.congr_fun sixthProjection_idempotent x
  change sixthProjection (sixthProjection x) = sixthProjection x at hp
  simp only [Module.End.mul_apply, vacuumProjection, LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_sub, hp]
  abel

theorem projection_sum : vacuumProjection + sixthProjection = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change x - sixthProjection x + sixthProjection x = x
  abel

theorem projections_disjoint : vacuumProjection * sixthProjection = 0 := by
  apply LinearMap.ext
  intro x
  have hp := LinearMap.congr_fun sixthProjection_idempotent x
  change sixthProjection (sixthProjection x) = sixthProjection x at hp
  change sixthProjection x - sixthProjection (sixthProjection x) = 0
  rw [hp, sub_self]

theorem sixthProjection_coe (x : TwoSeed) :
    twoSeedEmbedding (sixthProjection x) = (1 / 168 : ℂ) • spinCasimir (twoSeedEmbedding x) := by
  rw [sixthProjection, LinearMap.smul_apply, map_smul, twoSeedCasimir_coe]

theorem vacuumProjection_coe (x : TwoSeed) :
    twoSeedEmbedding (vacuumProjection x) = twoSeedEmbedding x -
      (1 / 168 : ℂ) • spinCasimir (twoSeedEmbedding x) := by
  rw [vacuumProjection, LinearMap.sub_apply, LinearMap.id_apply, map_sub, sixthProjection_coe]

end VOA.Classification.COne.OrbIcoV
