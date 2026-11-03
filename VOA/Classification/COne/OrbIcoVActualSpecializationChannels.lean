import VOA.Classification.COne.OrbIcoVActualSpecialization

/-! The genuine projected self-product channels and their normalized ground states. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbC2c
  VOA.LatGen VOA.LatGen.Triplet
open scoped Classical

/-- The spin-six Casimir projection kills every genuine grade below 36. -/
theorem sixthProjection_below (N : ℤ) (hN : N<36) (x : TwoSeed)
    (hx : x.val∈Wi.grading N) : sixthProjection x=0 := by
  have hkill : ∀ y∈TwoSeed, piHom V2v N (spinCasimir (y : Sp))=0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,rfl | rfl⟩ := hy
      · rw [spinCasimir_word_vacuum,map_zero]
      · rw [spinCasimir_word_Xico,map_smul]
        have hg : ((virWord Wi w Xico : (orbifold ico).carrier) : Sp)∈V2v.grading (36+(OrbOctaR.wordWeight w : ℤ)) :=
          OrbOctaR.virWord_grading Wi OrbIco.Xico_grading w
        rw [piHom_of_mem_ne V2v (by omega) hg,smul_zero]
    | zero => simp
    | add y z _ _ hy hz =>
      change piHom V2v N (spinCasimir ((y : Sp)+(z : Sp)))=0
      rw [map_add,map_add,hy,hz,add_zero]
    | smul c y _ hy =>
      change piHom V2v N (spinCasimir (c • (y : Sp)))=0
      rw [map_smul,map_smul,hy,smul_zero]
  have hg : spinCasimir (x.val : Sp)∈V2v.grading N := by
    change spinCasimir (twoSeedEmbedding x)∈_
    rw [← twoSeedCasimir_coe x]
    exact twoSeedCasimir_grading N x hx
  have hz := hkill x.val x.property
  rw [piHom_of_mem V2v hg] at hz
  apply twoSeedEmbedding_injective
  rw [sixthProjection_coe]
  simp only [twoSeedEmbedding,LinearMap.comp_apply,Submodule.subtype_apply,hz,smul_zero,map_zero]

/-- At grade 36, the genuine spin-six projection lies on the actual primary line. -/
theorem sixthProjection_ground_line (x : TwoSeed) (hx : x.val∈Wi.grading 36) :
    ∃ c : ℂ, (sixthProjection x).val=c • Xico := by
  have hline : ∀ y∈TwoSeed, piHom V2v 36 (spinCasimir (y : Sp))∈
      Submodule.span ℂ {(Xico : Sp)} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,rfl | rfl⟩ := hy
      · rw [spinCasimir_word_vacuum,map_zero]
        exact Submodule.zero_mem _
      · rw [spinCasimir_word_Xico,map_smul]
        apply Submodule.smul_mem
        by_cases hw : w=[]
        · subst w
          have hg : (Xico : Sp)∈V2v.grading 36 := OrbIco.Xico_grading
          simpa only [virWord,piHom_of_mem V2v hg] using
            (Submodule.subset_span (by simp : (Xico : Sp)∈{(Xico : Sp)}))
        · have hwpos : 0<OrbOctaR.wordWeight w := by
            cases w with
            | nil => contradiction
            | cons k w => simp [OrbOctaR.wordWeight]
          have hg : ((virWord Wi w Xico : (orbifold ico).carrier) : Sp)∈V2v.grading (36+(OrbOctaR.wordWeight w : ℤ)) :=
            OrbOctaR.virWord_grading Wi OrbIco.Xico_grading w
          rw [piHom_of_mem_ne V2v (by omega) hg]
          exact Submodule.zero_mem _
    | zero => simp
    | add y z _ _ hy hz =>
      change piHom V2v 36 (spinCasimir ((y : Sp)+(z : Sp)))∈_
      rw [map_add,map_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      change piHom V2v 36 (spinCasimir (c • (y : Sp)))∈_
      rw [map_smul,map_smul]
      exact Submodule.smul_mem _ c hy
  have hg : spinCasimir (x.val : Sp)∈V2v.grading 36 := by
    change spinCasimir (twoSeedEmbedding x)∈_
    rw [← twoSeedCasimir_coe x]
    exact twoSeedCasimir_grading 36 x hx
  have hs := hline x.val x.property
  rw [piHom_of_mem V2v hg] at hs
  have hp : twoSeedEmbedding (sixthProjection x)∈Submodule.span ℂ {(Xico : Sp)} := by
    rw [sixthProjection_coe]
    exact Submodule.smul_mem _ _ hs
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hp
  refine ⟨c,?_⟩
  apply (orbifold ico).carrier.subtype_injective
  exact hc.symm

/-- Projection preserves the actual spin-six oscillator measurement. -/
theorem sixthProbe_sixthProjection (x : TwoSeed) : sixthProbe (sixthProjection x).val=sixthProbe x.val := by
  rw [sixthProbe_apply,sixthProbe_apply]
  change (1/168 : ℂ)*OrbOctaR.neutralProbe (spinCasimir (twoSeedEmbedding (sixthProjection x)))=_
  rw [sixthProjection_coe,map_smul]
  change (1/168 : ℂ)*OrbOctaR.neutralProbe ((1/168 : ℂ) • spinCasimir (spinCasimir (x.val : Sp)))=_
  rw [spinCasimir_square x.val x.property,map_smul,map_smul]
  ring

theorem sixthProbe_vacuumProjection (x : TwoSeed) : sixthProbe (vacuumProjection x).val=0 := by
  change sixthProbe (x.val-(sixthProjection x).val)=0
  rw [map_sub,sixthProbe_sixthProjection,sub_self]

theorem vacuumProbe_vacuumProjection (x : TwoSeed) : vacuumProbe (vacuumProjection x).val=vacuumProbe x.val := by
  rw [vacuumProbe_apply,vacuumProbe_apply,sixthProbe_vacuumProjection]
  change OrbIcoS.neutralProbe (x.val-(sixthProjection x).val)-0=
    OrbIcoS.neutralProbe x.val-sixthProbe x.val
  rw [map_sub]
  have hp : OrbIcoS.neutralProbe (sixthProjection x).val=sixthProbe x.val := by
    change OrbOctaR.neutralProbe (twoSeedEmbedding (sixthProjection x))=_
    rw [sixthProjection_coe,map_smul]
    rfl
  rw [hp,sub_zero]

theorem sixthState_below (N : ℕ) (hN : N<36) : (sixthState N (by omega)).val=0 := by
  have h := sixthProjection_below N (by exact_mod_cast hN) (productState N (by omega))
    (productState_grading N (by omega))
  exact congrArg Subtype.val h

theorem sixthState_ground : (sixthState 36 (by omega)).val=OrbIcoT.icoSixthCoupling • Xico := by
  obtain ⟨c,hc⟩ := sixthProjection_ground_line (productState 36 (by omega)) (productState_grading 36 (by omega))
  change (sixthState 36 (by omega)).val=c • Xico at hc
  have hp := congrArg sixthProbe hc
  rw [sixthState,sixthProbe_sixthProjection,map_smul,sixthProbe_Xico] at hp
  have hd : sixthCoefficient 18 = sixthProbe (productState 36 (by omega)).val/OrbIcoS.neutralProbe Xico := by
    simp [sixthCoefficient,productState]
  have hcouple := sixthCoefficient_eighteen
  rw [hd] at hcouple
  have hme : sixthProbe (productState 36 (by omega)).val=
      OrbIcoT.icoSixthCoupling*OrbIcoS.neutralProbe Xico :=
    (div_eq_iff neutralProbe_Xico_ne_zero).mp hcouple
  have he : c=OrbIcoT.icoSixthCoupling :=
    mul_right_cancel₀ neutralProbe_Xico_ne_zero (hp.symm.trans hme)
  rwa [he] at hc

/-- The actual projected vacuum channel starts with its nonzero top coupling. -/
theorem vacuumState_ground : (vacuumState 0 (by omega)).val=vacuumCoefficient 0 • Wi.vacuum := by
  obtain ⟨c,hc,he⟩ := OrbIcoZ.self_top_nonzero
  have hprod : (productState 0 (by omega)).val=c • Wi.vacuum := by
    simpa only [productState,Nat.cast_zero,sub_zero] using he
  have hp : (vacuumState 0 (by omega)).val=(productState 0 (by omega)).val := by
    change (productState 0 (by omega)).val-(sixthState 0 (by omega)).val=_
    rw [sixthState_below 0 (by omega),sub_zero]
  have hv : vacuumCoefficient 0=c := by
    simp only [vacuumCoefficient,Nat.cast_zero,mul_zero,sub_zero,pow_zero,one_mul]
    rw [he,map_smul,vacuumProbe_vacuum]
    simp
  rw [hp,hprod,hv]

/-- The actual projected spin-six probe equals the normalized PBW survival functional. -/
theorem actualProbe_fiber (self : Bool) (N : ℕ)
    (v : VOA.InverseDS.VirasoroVerma.Verma (familyCharge 1) (symbolFamilyWeight self 1))
    (hv : v∈VOA.InverseDS.VirasoroVerma.sortedSpan _ _ N) :
    (if self then sixthProbe else vacuumProbe) (actualFiberMap self v)=
      uniformProbe _ _ v*(if self then OrbIcoS.neutralProbe Xico else 1) := by
  obtain ⟨a,rfl⟩ := VOA.InverseDS.VirasoroVerma.exists_vermaLevelState _ _ N v hv
  rw [actualFiberMap_levelState,actualProbe_levelState,uniformProbe_levelState]

end VOA.Classification.COne.OrbIcoV
