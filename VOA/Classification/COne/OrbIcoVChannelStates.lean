import VOA.Classification.COne.OrbIcoVChannels

/-! Actual graded vacuum and spin-six projections of the icosahedral
self-product, with the genuine positive-mode Ward equations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbIcoS OrbC2c

theorem twoSeedCasimir_grading (N : ℤ) (x : TwoSeed) (hx : x.val ∈ Wi.grading N) :
    (twoSeedCasimir x).val ∈ Wi.grading N := by
  rw [VOA.Deform.grading_eq_L_zero_eigenspace, Module.End.mem_eigenspace_iff]
  apply (orbifold ico).carrier.subtype_injective
  change V2v.L 0 (twoSeedEmbedding (twoSeedCasimir x)) =
    (N : ℂ) • twoSeedEmbedding (twoSeedCasimir x)
  rw [twoSeedCasimir_coe, ← spinCasimir_L]
  have he := congrArg (fun y : (orbifold ico).carrier => (y : Sp))
    (Wi.L_zero_grading x.val hx)
  change V2v.L 0 (twoSeedEmbedding x) = (N : ℂ) • twoSeedEmbedding x at he
  rw [he, map_smul]

theorem sixthProjection_grading (N : ℤ) (x : TwoSeed) (hx : x.val ∈ Wi.grading N) :
    (sixthProjection x).val ∈ Wi.grading N :=
  (Wi.grading N).smul_mem _ (twoSeedCasimir_grading N x hx)

theorem vacuumProjection_grading (N : ℤ) (x : TwoSeed) (hx : x.val ∈ Wi.grading N) :
    (vacuumProjection x).val ∈ Wi.grading N :=
  (Wi.grading N).sub_mem hx (sixthProjection_grading N x hx)

theorem sixthProjection_spin (x : TwoSeed) :
    spinCasimir (twoSeedEmbedding (sixthProjection x)) =
      (168 : ℂ) • twoSeedEmbedding (sixthProjection x) := by
  have hs : spinCasimir (spinCasimir (twoSeedEmbedding x)) =
      (168 : ℂ) • spinCasimir (twoSeedEmbedding x) :=
    spinCasimir_square x.val x.property
  simp only [sixthProjection_coe, map_smul, hs, smul_smul]
  norm_num

theorem vacuumProjection_spin (x : TwoSeed) :
    spinCasimir (twoSeedEmbedding (vacuumProjection x)) = 0 := by
  have hs : spinCasimir (spinCasimir (twoSeedEmbedding x)) =
      (168 : ℂ) • spinCasimir (twoSeedEmbedding x) :=
    spinCasimir_square x.val x.property
  rw [vacuumProjection_coe, map_sub, map_smul, hs, smul_smul]
  norm_num

def productState (N : ℕ) (hN : N < 100) : TwoSeed :=
  ⟨Wi.smul Xico (71-(N : ℤ)) Xico, OrbIcoS.grading_lt_100 (N : ℤ) (by exact_mod_cast hN) (by
    have h := Wi.smul_mem_grading Xico_grading Xico_grading (71-(N : ℤ))
    convert h using 1 <;> ring_nf)⟩

def vacuumState (N : ℕ) (hN : N < 100) : TwoSeed := vacuumProjection (productState N hN)

def sixthState (N : ℕ) (hN : N < 100) : TwoSeed := sixthProjection (productState N hN)

theorem productState_grading (N : ℕ) (hN : N < 100) :
    (productState N hN).val ∈ Wi.grading (N : ℤ) := by
  have h := Wi.smul_mem_grading Xico_grading Xico_grading (71-(N : ℤ))
  convert h using 1 <;> ring_nf

theorem vacuumState_grading (N : ℕ) (hN : N < 100) :
    (vacuumState N hN).val ∈ Wi.grading (N : ℤ) :=
  vacuumProjection_grading _ _ (productState_grading N hN)

theorem sixthState_grading (N : ℕ) (hN : N < 100) :
    (sixthState N hN).val ∈ Wi.grading (N : ℤ) :=
  sixthProjection_grading _ _ (productState_grading N hN)

theorem Xico_positive_modes (k : ℕ) (hk : 1 ≤ k) : Wi.L (k : ℤ) Xico = 0 := by
  have he := ((mem_prim _).mp OrbIcoZ.X_primary).2 (k-1)
  rwa [show ((k-1 : ℕ) : ℤ)+1 = k by omega] at he

theorem productState_positive (N k : ℕ) (hN : N < 100) (hk : 0 < k) (hkN : k ≤ N) :
    Wi.L (k : ℤ) (productState N hN).val =
      (((N : ℂ)+35*(k : ℂ)-36)) • (productState (N-k) (by omega)).val := by
  change Wi.L (k : ℤ) (Wi.smul Xico (71-(N : ℤ)) Xico) = _
  rw [OrbOdd.L_smul_primary Xico_grading
    (fun m hm => Xico_positive_modes m hm)]
  have hz : Wi.L (k : ℤ) Xico = 0 := Xico_positive_modes k (by omega)
  rw [hz, PreVertexAlgebra.smul_zero_right, zero_add]
  have hm : (k : ℤ)+(71-(N : ℤ)) = 71-((N-k : ℕ) : ℤ) := by omega
  rw [hm]
  change (((36-1)*((k : ℤ)+1)-(71-(N : ℤ)) : ℤ) : ℂ) •
    (productState (N-k) (by omega)).val =
    ((N : ℂ)+35*(k : ℂ)-36) • (productState (N-k) (by omega)).val
  congr 1
  push_cast
  ring

theorem sixthState_positive (N k : ℕ) (hN : N < 100) (hk : 0 < k) (hkN : k ≤ N) :
    Wi.L (k : ℤ) (sixthState N hN).val =
      ((N : ℂ)+35*(k : ℂ)-36) • (sixthState (N-k) (by omega)).val := by
  apply (orbifold ico).carrier.subtype_injective
  change V2v.L (k : ℤ) (twoSeedEmbedding (sixthState N hN)) =
    ((N : ℂ)+35*(k : ℂ)-36) • twoSeedEmbedding (sixthState (N-k) (by omega))
  rw [sixthState, sixthProjection_coe, map_smul, ← spinCasimir_L]
  have hw := congrArg (fun y : (orbifold ico).carrier => (y : Sp))
    (productState_positive N k hN hk hkN)
  change V2v.L (k : ℤ) (twoSeedEmbedding (productState N hN)) =
    ((N : ℂ)+35*(k : ℂ)-36) • twoSeedEmbedding (productState (N-k) (by omega)) at hw
  rw [hw, map_smul]
  simp only [sixthState, sixthProjection_coe]
  exact smul_comm _ _ _

theorem vacuumState_positive (N k : ℕ) (hN : N < 100) (hk : 0 < k) (hkN : k ≤ N) :
    Wi.L (k : ℤ) (vacuumState N hN).val =
      ((N : ℂ)+35*(k : ℂ)-36) • (vacuumState (N-k) (by omega)).val := by
  change Wi.L (k : ℤ) ((productState N hN).val - (sixthState N hN).val) =
    _ • ((productState (N-k) (by omega)).val - (sixthState (N-k) (by omega)).val)
  rw [map_sub, productState_positive N k hN hk hkN, sixthState_positive N k hN hk hkN,
    smul_sub]

end VOA.Classification.COne.OrbIcoV
