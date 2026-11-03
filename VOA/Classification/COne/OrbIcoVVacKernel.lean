import VOA.Classification.COne.OrbIcoVVacFlat

/-! Actual c=1 vacuum kernel comparison via the translation singular
submodule and the proved Feigin--Fuchs radical dimension. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  InverseDS.VirasoroVerma VOA.VirasoroScreening
open scoped Classical
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem c_one_translation_positive :
    vermaMode 1 0 1 (vermaBSASource 1 0 1 1 1)=0 ∧
    vermaMode 1 0 2 (vermaBSASource 1 0 1 1 1)=0 := by
  have he := vermaBSASource_one_two_all (1:ℂ) 1 one_ne_zero (by norm_num)
  have transfer (c h : ℂ) (hc : c=1) (hh : h=0)
      (he : vermaMode c h 1 (vermaBSASource c h 1 1 1)=0 ∧
        vermaMode c h 2 (vermaBSASource c h 1 1 1)=0) :
      vermaMode 1 0 1 (vermaBSASource 1 0 1 1 1)=0 ∧
        vermaMode 1 0 2 (vermaBSASource 1 0 1 1 1)=0 := by
    subst c
    subst h
    exact he
  exact transfer _ _ (by norm_num [vermaBSACharge]) (by norm_num [vermaBSAWeight]) he

theorem kernel_eq_radical_of_singular (c h : ℂ) (n m : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hne : v ≠ 0)
    (h₁ : vermaMode c h 1 v=0) (h₂ : vermaMode c h 2 v=0)
    (f : Verma c h →ₗ[ℂ] V) (Lm : ℤ → Module.End ℂ V)
    (hmode : ∀ k u, f (vermaMode c h k u)=Lm k (f u))
    (hker : LinearMap.ker f ≤ vermaRadical c h) (hz : f v=0)
    (hR : Module.finrank ℂ (vermaRadicalLevel c h (n+m)) ≤
      Fintype.card (VermaPartitions m)) :
    sortedSpan c h (n+m) ⊓ LinearMap.ker f = vermaRadicalLevel c h (n+m) := by
  let S := vermaSingularMap c h n v hv h₁ h₂
  let D := (sortedSpan c (h+(n:ℂ)) m).map S
  let K := sortedSpan c h (n+m) ⊓ LinearMap.ker f
  have hD : Module.finrank ℂ D = Fintype.card (VermaPartitions m) :=
    vermaSingularMap_level_finrank c h n m v hv hne h₁ h₂
  have hDK : D ≤ K := by
    rintro x ⟨u,hu,rfl⟩
    refine ⟨(vermaSingularMap_mem_level_iff c h n m v hv hne h₁ h₂ u).mpr hu,?_⟩
    exact LinearMap.congr_fun (map_killed_singularMap_zero c h n v hv h₁ h₂
      f Lm hmode hz) u
  have hKR : K ≤ vermaRadicalLevel c h (n+m) := by
    rintro x ⟨hx,hf⟩
    exact ⟨hx,hker hf⟩
  have hdim := Submodule.finrank_mono hDK
  rw [hD] at hdim
  exact Submodule.eq_of_le_of_finrank_le hKR (hR.trans hdim)

set_option maxHeartbeats 500000 in
theorem killed_translation_kernel_eq_radicalLevel (c h : ℂ) (hc : c=1) (hh : h=0)
    (f : Verma c h →ₗ[ℂ] V) (Lm : ℤ → Module.End ℂ V)
    (hmode : ∀ k u, f (vermaMode c h k u)=Lm k (f u))
    (hker : LinearMap.ker f ≤ vermaRadical c h)
    (hz : f (vermaBSASource c h 1 1 1)=0) (m : ℕ) :
    sortedSpan c h (1+m) ⊓ LinearMap.ker f = vermaRadicalLevel c h (1+m) := by
  have hpos : vermaMode c h 1 (vermaBSASource c h 1 1 1)=0 ∧
      vermaMode c h 2 (vermaBSASource c h 1 1 1)=0 := by
    subst c
    subst h
    exact c_one_translation_positive
  apply kernel_eq_radical_of_singular c h 1 m (vermaBSASource c h 1 1 1)
    (vermaBSASource_mem_level _ _ _ _ _)
    (vermaBSASource_ne_zero _ _ _ _ one_ne_zero (by norm_num)) hpos.1 hpos.2
    f Lm hmode hker hz
  subst c
  subst h
  exact radical_bound_zero m

theorem vacuum_seedMap_source_one_zero :
    seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)
      (vermaBSASource Wi.centralCharge ((0 : ℤ) : ℂ) 1 1 1)=0 := by
  simp only [vermaBSASource, Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, Nat.cast_one,
    zero_sub, vermaBSAState_zero]
  rw [seedMap_mode, seedMap, universalMap_highestVector, L_neg_one_vacuum]

theorem vacuum_seed_ne_zero : Wi.vacuum ≠ 0 := by
  intro hz
  have hh := vacuumProbe_vacuum
  rw [hz,map_zero] at hh
  exact zero_ne_one hh

theorem vacuum_seedMap_kernel_level (m : ℕ) :
    sortedSpan Wi.centralCharge ((0:ℤ):ℂ) (1+m) ⊓
      LinearMap.ker (seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)) =
      vermaRadicalLevel Wi.centralCharge ((0:ℤ):ℂ) (1+m) := by
  exact killed_translation_kernel_eq_radicalLevel _ _ Wi_charge_one (by norm_num)
    (seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)) Wi.L
    (seedMap_mode Wi 0 Wi.vacuum (vacuum_mem_prim Wi))
    (seedMap_kernel_le_radical Wi 0 Wi.vacuum (vacuum_mem_prim Wi) vacuum_seed_ne_zero)
    vacuum_seedMap_source_one_zero m

theorem vacFamilyMap_one_kernel_level (m : ℕ) :
    sortedSpan (familyCharge 1) (vacFamilyWeight 1) (1+m) ⊓ LinearMap.ker (vacFamilyMap 1) =
      vermaRadicalLevel (familyCharge 1) (vacFamilyWeight 1) (1+m) := by
  apply killed_translation_kernel_eq_radicalLevel _ _
    (by norm_num [familyCharge, familyBackground])
    (by norm_num [vacFamilyWeight, vacFamilyMomentum])
    (vacFamilyMap 1) (InverseDS.LeeYangFockVirasoro.sectorVirasoro (familyBackground 1) 0)
  · intro k u
    exact chargedFockMap_mode _ _ k u
  · intro v hv
    exact chargedFockMap_kernel_radical _ _ v hv
  · simpa only [vermaBSASource, Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, Nat.cast_one,
      zero_sub, vermaBSAState_zero] using vacuum_fock_translation_zero (familyBackground 1)

end VOA.Classification.COne.OrbIcoV
