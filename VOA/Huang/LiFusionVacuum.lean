import VOA.Huang.LiFusionTop
import VOA.Huang.FusionUnit

/-! # An unconditional instance of the converse: vacuum insertion

For an irreducible lowest-weight module `P`, every Frenkel–Zhu datum of type
`(P / V P)` is the top map of a scalar multiple of `Y_P`. This is a genuine
instance of top-map surjectivity, not a rationality-dependent extension theorem
for arbitrary insertions. Its proof uses simplicity of the Zhu bottom, rather
than any construction of a generalized Verma intertwiner.
-/
namespace VOA.Huang.LiFusion
open VOA VOA.FZ FusionTop FusionUnit
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

theorem state_induction (W : VertexOperatorAlgebra V) {P : V → Prop}
    (hh : ∀ k a, a ∈ W.grading k → P a) (h0 : P 0)
    (ha : ∀ a b, P a → P b → P (a + b)) (a : V) : P a := by
  have htop : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]
    trivial
  exact Submodule.iSup_induction _ (motive := P) htop hh h0 ha

theorem fzLeft_adjoint_vacuum (p : ℕ) (a : V) :
    fzLeft (adjointModule W).toWeakModule p a W.vacuum = a := by
  unfold fzLeft
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, zero_sub, cbz_apply_nonneg _ le_rfl,
      Int.toNat_zero, gBinom_zero, one_smul, adjoint_mode]
    exact W.toPreVertexAlgebra.smul_vacuum_neg_one a
  · intro i _ hi
    rw [adjoint_mode, W.toPreVertexAlgebra.smul_vacuum_nonneg a (by omega), smul_zero]
  · simp

theorem fzRight_adjoint_vacuum (p : ℕ) (a : V) :
    fzRight (adjointModule W).toWeakModule p a W.vacuum = a := by
  unfold fzRight
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, zero_sub, cbz_apply_nonneg _ le_rfl,
      Int.toNat_zero, gBinom_zero, one_smul, adjoint_mode]
    exact W.toPreVertexAlgebra.smul_vacuum_neg_one a
  · intro i _ hi
    rw [adjoint_mode, W.toPreVertexAlgebra.smul_vacuum_nonneg a (by omega), smul_zero]
  · simp

/-- Vacuum evaluation determines an adjoint-insertion top datum. -/
theorem fzSpace_adjoint_eq_rho {P₂ P₃ : LWModule W}
    (T : fzSpace (adjointModule W) P₂ P₃) (a : V) (y : bot P₂) :
    T.val a y = rhoLW P₃.isMod P₃.h a (T.val W.vacuum y) := by
  refine state_induction W (P := fun a =>
    T.val a y = rhoLW P₃.isMod P₃.h a (T.val W.vacuum y)) ?_ ?_ ?_ a
  · intro k a ha
    by_cases hk : k < 0
    · rw [W.positivity k hk, Submodule.mem_bot] at ha
      simp [ha]
    · have ha' : a ∈ W.grading (k.toNat : ℤ) := by
        rwa [Int.toNat_of_nonneg (by omega)]
      apply Subtype.ext
      have h := T.property.2.1 k.toNat a ha' W.vacuum y
      rw [fzLeft_adjoint_vacuum] at h
      rw [rhoLW_apply_coe, oMod_homogeneous P₃.isMod ha']
      exact h
  · simp
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Vacuum evaluation intertwines the zero-mode representations on the tops. -/
theorem fzSpace_adjoint_vacuum_intertwines {P₂ P₃ : LWModule W}
    (T : fzSpace (adjointModule W) P₂ P₃) (a : V) (y : bot P₂) :
    T.val W.vacuum (rhoLW P₂.isMod P₂.h a y) =
      rhoLW P₃.isMod P₃.h a (T.val W.vacuum y) := by
  refine state_induction W (P := fun a =>
    T.val W.vacuum (rhoLW P₂.isMod P₂.h a y) =
      rhoLW P₃.isMod P₃.h a (T.val W.vacuum y)) ?_ ?_ ?_ a
  · intro k a ha
    rcases lt_trichotomy k 0 with hk | hk | hk
    · rw [W.positivity k hk, Submodule.mem_bot] at ha
      simp [ha]
    · subst k
      rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp [rhoLW_vacuum]
    · have ha' : a ∈ W.grading (k.toNat : ℤ) := by
        rwa [Int.toNat_of_nonneg (by omega)]
      have h := T.property.2.2 k.toNat (by omega) a ha' W.vacuum y
        (rhoLW P₂.isMod P₂.h a y) (by rw [rhoLW_apply_coe, oMod_homogeneous _ ha'])
      rw [fzRight_adjoint_vacuum] at h
      exact h.symm.trans (fzSpace_adjoint_eq_rho T a y)
  · simp
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Schur's lemma on the bottom, using its proved intrinsic Zhu simplicity. -/
theorem bottom_endomorphism_scalar (P : LWModule W) (hP : P.IsIrreducibleLW)
    (f : Module.End ℂ (bot P))
    (hf : ∀ a y, f (rhoLW P.isMod P.h a y) = rhoLW P.isMod P.h a (f y)) :
    ∃ c : ℂ, f = c • LinearMap.id := by
  have hs := LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible P hP
  let f' : Module.End ℂ P.toAMod.carrier := f
  letI : Nontrivial P.toAMod.carrier := hs.1
  letI : FiniteDimensional ℂ P.toAMod.carrier := P.isMod.finrank P.h
  have hr (a : VOA.A W) (y : P.toAMod.carrier) :
      f' (P.toAMod.ρ a y) = P.toAMod.ρ a (f' y) := by
    obtain ⟨a, rfl⟩ := (O W).mkQ_surjective a
    change f (actA P.isMod P.isLow (VOA.mk W a) y) =
      actA P.isMod P.isLow (VOA.mk W a) (f y)
    simpa only [actA_mk] using hf a y
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let K : AModSubmodule P.toAMod :=
    { carrier := LinearMap.ker (f' - c • LinearMap.id)
      ρ_mem := by
        intro a y hy
        change f' y - c • y = 0 at hy
        change f' (P.toAMod.ρ a y) - c • P.toAMod.ρ a y = 0
        rw [hr, sub_eq_zero.mp hy, map_smul, sub_self] }
  rcases hs.2 K with hk | hk
  · have hvk : v ∈ K.carrier := by
      change f' v - c • v = 0
      rw [hv.apply_eq_smul, sub_self]
    rw [hk, Submodule.mem_bot] at hvk
    exact (hv.2 hvk).elim
  · have he : f' = c • LinearMap.id := by
      apply LinearMap.ext
      intro y
      have hy : y ∈ K.carrier := by rw [hk]; trivial
      exact sub_eq_zero.mp hy
    exact ⟨c, he⟩

/-- The actual vertex operator has the identity as its top value at the vacuum. -/
theorem topMapFZ_moduleIntertwiner_vacuum (P : LWModule W) :
    (topMapFZ (adjointModule W) P P (moduleIntertwiner P.isMod)).val W.vacuum =
      LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  change topComp (adjointModule W) P P (moduleModes P.isMod) W.vacuum y = (y : P.carrier)
  have hv : W.vacuum ∈ (adjointModule W).weight 0 := by
    change W.vacuum ∈ adjWeight W 0
    have hz := adjWeight_cast W (0 : ℤ)
    norm_num only at hz
    rw [hz]
    exact W.vacuum_mem_grading_zero
  rw [topComp_of_mem _ hv]
  simp only [zero_add, sub_self, zero_sub]
  rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by norm_num, moduleModes_apply_intCast,
    ← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]

/-- Li's converse is unconditional for a vacuum insertion and equal
irreducible source and target. The lift is a scalar multiple of `Y_P`. -/
theorem topMapFZ_surjective_adjoint_self (P : LWModule W) (hP : P.IsIrreducibleLW) :
    Function.Surjective (topMapFZ (adjointModule W) P P) := by
  intro T
  obtain ⟨c, hc⟩ := bottom_endomorphism_scalar P hP (T.val W.vacuum)
    (fzSpace_adjoint_vacuum_intertwines T)
  refine ⟨c • moduleIntertwiner P.isMod, ?_⟩
  rw [map_smul]
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro y
  have hT := fzSpace_adjoint_eq_rho T a y
  have hY := fzSpace_adjoint_eq_rho
    (topMapFZ (adjointModule W) P P (moduleIntertwiner P.isMod)) a y
  rw [hc] at hT
  rw [topMapFZ_moduleIntertwiner_vacuum] at hY
  simpa only [Submodule.coe_smul, LinearMap.smul_apply, LinearMap.id_apply,
    hY, map_smul] using hT.symm

end VOA.Huang.LiFusion
