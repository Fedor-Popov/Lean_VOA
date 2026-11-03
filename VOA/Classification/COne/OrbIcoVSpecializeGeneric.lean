import VOA.Classification.COne.OrbIcoVSpecializeWard

/-! Actual normalized generic Ward sequences give nonzero kernels in fixed local Fock bases. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma InverseDS.LeeYangFockVirasoro Filter Topology
open scoped Classical

theorem exists_symbolFamily_finite_ward (self : Bool) (N : ℕ) (s : ℂ)
    (hs : s≠0) (him : (s^2).im≠0) :
    ∃ f : wardSequenceSpace (familyCharge s) (symbolFamilyWeight self s),
      f.val 0=highestVector _ _ ∧
      (∀ r<2*N, vermaMode _ _ 1 (f.val (r+1)) =
        (symbolFamilyWeight self s+(r:ℂ)) • f.val r) ∧
      (∀ r<2*N-1, vermaMode _ _ 2 (f.val (r+2)) =
        (symbolFamilyWeight self s+incomingWeight (s^2)+(r:ℂ)) • f.val r) ∧
      ∀ n, (2:ℂ)^n*uniformProbe _ _ (f.val (2*n))=
        genericSymbolCoefficient self N (s^2) n := by
  have hc := family_charge s hs
  have hh := symbolFamily_weight self s hs
  have haux (c h : ℂ) (hc : c=vermaBSACharge (s^2))
      (hh : h=symbolTargetWeight self (s^2)) :
      ∃ f : wardSequenceSpace c h,
        f.val 0=highestVector _ _ ∧
        (∀ r<2*N, vermaMode c h 1 (f.val (r+1))=(h+(r:ℂ)) • f.val r) ∧
        (∀ r<2*N-1, vermaMode c h 2 (f.val (r+2))=
          (h+incomingWeight (s^2)+(r:ℂ)) • f.val r) ∧
        ∀ n, (2:ℂ)^n*uniformProbe c h (f.val (2*n))=
          genericSymbolCoefficient self N (s^2) n := by
    subst c
    subst h
    let f := genericSymbolWard self N (s^2) him
    have hf := genericSymbolWard_spec self N (s^2) him
    have h1 (r : ℕ) (hr : r<2*N+2) : vermaMode _ _ 1 (f.val (r+1)) =
        (symbolTargetWeight self (s^2)+(r:ℂ)) • f.val r := by
      have he := hf.2.2.1 r hr
      change vermaMode _ _ 1 (f.val (r+1)) -
        (symbolTargetWeight self (s^2)-incomingWeight (s^2)+incomingWeight (s^2)+(r:ℂ)) •
          f.val r=0 at he
      simpa only [sub_add_cancel] using sub_eq_zero.mp he
    refine ⟨f,hf.1,fun r hr => h1 r (by omega),?_,?_⟩
    · intro r hr
      have he := hf.2.2.2 r (by omega)
      change vermaMode _ _ 2 (f.val (r+2)) -
        (symbolTargetWeight self (s^2)-incomingWeight (s^2)+2*incomingWeight (s^2)+(r:ℂ)) •
          f.val r - (3:ℂ) •
          (vermaMode _ _ 1 (f.val (r+1)) -
            (symbolTargetWeight self (s^2)-incomingWeight (s^2)+incomingWeight (s^2)+(r:ℂ)) •
              f.val r)=0 at he
      rw [sub_add_cancel,h1 r (by omega),sub_self,smul_zero,sub_zero] at he
      have heq : symbolTargetWeight self (s^2)-incomingWeight (s^2)+
          2*incomingWeight (s^2)+(r:ℂ) =
          symbolTargetWeight self (s^2)+incomingWeight (s^2)+(r:ℂ) := by ring
      rw [heq] at he
      exact sub_eq_zero.mp he
    · intro n
      rw [genericSymbolCoefficient,dif_pos him]
  exact haux _ _ hc hh

theorem symbolFamily_coordinate_mem (self : Bool) (N : ℕ) (s : ℂ)
    (v : Verma (familyCharge s) (symbolFamilyWeight self s))
    (hv : v ∈ sortedSpan _ _ N) :
    fockCoordinates N ⟨symbolFamilyMap self s v,
      chargedFockMap_mem_level _ _ N v hv⟩ ∈ symbolCoordinateImage self N s := by
  cases self
  · change _ ∈ (LinearMap.range (chargedFockLevelMap (familyBackground s) 0 N)).map
      (fockCoordinates N)
    refine ⟨⟨vacFamilyMap s v,chargedFockMap_mem_level _ _ N v hv⟩,
      ⟨⟨v,hv⟩,rfl⟩,rfl⟩
  · change _ ∈ (LinearMap.range
      (chargedFockLevelMap (familyBackground s) (familyMomentum s) N)).map (fockCoordinates N)
    refine ⟨⟨familyMap s v,chargedFockMap_mem_level _ _ N v hv⟩,
      ⟨⟨v,hv⟩,rfl⟩,rfl⟩

theorem finiteBlockFock_level (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R+1)) (v : FiniteFockColumns self R → ℂ) :
    finiteBlockFock self R a s n v ∈ gradingWN 1 n.val :=
  chargedFockMap_mem_level _ _ n.val _ (finiteBlockVerma_level self R a s n v)

theorem exists_finiteBlock_coordinates (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (hs : s≠0)
    (hspan : ∀ n : Fin (R+1), Submodule.span ℂ (Set.range (symbolColumns self n.val (a n) s)) =
      symbolCoordinateImage self n.val s)
    (f : wardSequenceSpace (familyCharge s) (symbolFamilyWeight self s)) :
    ∃ v : FiniteFockColumns self R → ℂ, ∀ n : Fin (R+1),
      finiteBlockFock self R a s n v=symbolFamilyMap self s (f.val n.val) := by
  have hm (n : Fin (R+1)) :
      fockCoordinates n.val ⟨symbolFamilyMap self s (f.val n.val),
        chargedFockMap_mem_level _ _ n.val _ (f.property n.val)⟩ ∈
        Submodule.span ℂ (Set.range (symbolColumns self n.val (a n) s)) := by
    rw [hspan n]
    exact symbolFamily_coordinate_mem self n.val s _ (f.property n.val)
  choose c hc using fun n : Fin (R+1) =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hm n)
  let v : FiniteFockColumns self R → ℂ := fun j => c j.1 j.2
  refine ⟨v,fun n => ?_⟩
  have he : fockCoordinates n.val
      ⟨finiteBlockFock self R a s n v,finiteBlockFock_level self R a s n v⟩ =
      fockCoordinates n.val
      ⟨symbolFamilyMap self s (f.val n.val),
        chargedFockMap_mem_level _ _ n.val _ (f.property n.val)⟩ := by
    rw [← hc n]
    funext d
    change coeff d.val (finiteBlockFock self R a s n v) =
      (∑ j : Fin (symbolBasisSize self n.val), c n j • symbolColumns self n.val (a n) s j) d
    have hm := congrArg (coeff d.val)
      (map_finiteBlockVerma self R a s n v (symbolFamilyMap self s))
    have hcol : coeff d.val (finiteBlockFock self R a s n v) =
        ∑ j : Fin (symbolBasisSize self n.val), c n j *
          coeff d.val (symbolFamilyMap self s
            (vermaLevelState (familyCharge s) (symbolFamilyWeight self s) n.val (a n j))) := by
      simpa only [finiteBlockFock,LinearMap.comp_apply,coeff_sum,coeff_smul,smul_eq_mul,v] using hm
    rw [hcol]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [symbolColumns_sound self n.val (a n) s hs j d]
  exact congrArg Subtype.val (fockCoordinates_injective n.val he)

def finiteEvenPositions (N : ℕ) (indices : Fin 2 → ℕ) (hn : ∀ r, indices r≤N) :
    Fin 2 → Fin (2*N+1) := fun r => ⟨2*indices r,by have := hn r; omega⟩

/-- Changing from an actual Verma Ward sequence to a genuine local Fock basis
retains its leading scalar and every descended probe coordinate. -/
theorem finite_generic_kernel_of_basis (self : Bool) (N : ℕ)
    (a : FiniteFockPBW self (2*N)) (indices : Fin 2 → ℕ) (hn : ∀ r, indices r≤N)
    (s : ℂ) (hs : s≠0) (him : (s^2).im≠0)
    (hspan : ∀ n : Fin (2*N+1),
      Submodule.span ℂ (Set.range (symbolColumns self n.val (a n) s)) =
        symbolCoordinateImage self n.val s)
    (hprobe : ∀ n : Fin (2*N+1),
      ∀ u : Verma (familyCharge s) (symbolFamilyWeight self s),
        u ∈ sortedSpan _ _ n.val → symbolFamilyMap self s u=0 → uniformProbe _ _ u=0) :
    ∃ v : FiniteFockColumns self (2*N) → ℂ,
      finiteBlockProbe self (2*N) a ⟨0,by omega⟩ v=1 ∧
      finiteWardRowMap self (2*N) a s v=0 ∧
      ∀ r, finiteBlockProbe self (2*N) a (finiteEvenPositions N indices hn r) v =
        genericSymbolCoefficient self N (s^2) (indices r)/(2:ℂ)^(indices r) := by
  obtain ⟨f,hf0,hf1,hf2,hfc⟩ := exists_symbolFamily_finite_ward self N s hs him
  obtain ⟨v,hv⟩ := exists_finiteBlock_coordinates self (2*N) a s hs hspan f
  have hpr (n : Fin (2*N+1)) : finiteBlockProbe self (2*N) a n v =
      uniformProbe _ _ (f.val n.val) := by
    have hm : symbolFamilyMap self s (finiteBlockVerma self (2*N) a s n v-f.val n.val)=0 := by
      exact (map_sub (symbolFamilyMap self s) _ _).trans
        (sub_eq_zero.mpr (hv n))
    have hd := hprobe n (finiteBlockVerma self (2*N) a s n v-f.val n.val)
      ((sortedSpan _ _ n.val).sub_mem
        (finiteBlockVerma_level self (2*N) a s n v) (f.property n.val)) hm
    have he := (map_sub (uniformProbe (familyCharge s) (symbolFamilyWeight self s)) _ _).symm.trans hd
    exact (finiteBlockProbe_sound self (2*N) a s n v).symm.trans (sub_eq_zero.mp he)
  refine ⟨v,?_,?_,?_⟩
  · rw [hpr,hf0,uniformProbe_highest]
  · apply (finiteWardRowMap_eq_zero_iff self (2*N) a s v).mpr
    constructor
    · intro n
      simp only [finiteFirstDefect,LinearMap.sub_apply,LinearMap.comp_apply,
        LinearMap.smul_apply]
      rw [hv ⟨n.val+1,by omega⟩,hv ⟨n.val,by omega⟩]
      apply sub_eq_zero.mpr
      exact (chargedFockMap_mode _ _ 1 (f.val (n.val+1))).symm.trans
        ((congrArg (symbolFamilyMap self s) (hf1 n.val n.isLt)).trans
          (map_smul (symbolFamilyMap self s) _ _))
    · intro n
      simp only [finiteSecondDefect,LinearMap.sub_apply,LinearMap.comp_apply,
        LinearMap.smul_apply]
      rw [hv ⟨n.val+2,by omega⟩,hv ⟨n.val,by omega⟩]
      apply sub_eq_zero.mpr
      exact (chargedFockMap_mode _ _ 2 (f.val (n.val+2))).symm.trans
        ((congrArg (symbolFamilyMap self s) (hf2 n.val n.isLt)).trans
          (map_smul (symbolFamilyMap self s) _ _))
  · intro r
    rw [hpr]
    change uniformProbe _ _ (f.val (2*indices r)) = _
    apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2:ℂ)≠0))).mpr
    rw [mul_comm]
    exact hfc (indices r)

theorem nonzeroParameter_map_nhds_one :
    Filter.map (fun s : NonzeroParameter => s.val) (𝓝 parameterOne) = 𝓝 (1 : ℂ) := by
  exact map_nhds_subtype_coe_eq_nhds (p := fun s : ℂ => s≠0) (x := 1) one_ne_zero
    (continuousAt_id.eventually_ne one_ne_zero)

/-- The finite actual Fock Ward matrix has normalized nonzero kernels on
an approaching nonreal locus, and its scalar rows are the actual generic coefficients. -/
theorem exists_generic_finite_kernel (self : Bool) (N : ℕ)
    (indices : Fin 2 → ℕ) (hn : ∀ r, indices r≤N) :
    ∃ a : FiniteFockPBW self (2*N),
      (∀ n : Fin (2*N+1), LinearIndependent ℂ (symbolColumns self n.val (a n) 1)) ∧
      ∀ᶠ s in OrbIcoW.nonrealNhdsOne,
        ∃ v : FiniteFockColumns self (2*N) → ℂ,
          v≠0 ∧ finiteWardRowMap self (2*N) a s v=0 ∧
          ∀ r, finiteBlockProbe self (2*N) a (finiteEvenPositions N indices hn r) v =
            (genericSymbolCoefficient self N (s^2) (indices r)/(2:ℂ)^(indices r)) *
              finiteBlockProbe self (2*N) a ⟨0,by omega⟩ v := by
  choose a ha using fun n : Fin (2*N+1) => exists_local_symbol_basis self n.val
  have hLI (n : Fin (2*N+1)) : LinearIndependent ℂ (symbolColumns self n.val (a n) 1) :=
    ((ha n).self_of_nhds).1
  have hnear : ∀ᶠ s in OrbIcoW.nonrealNhdsOne,
      ∀ n : Fin (2*N+1),
        Submodule.span ℂ (Set.range (symbolColumns self n.val (a n) s)) =
          symbolCoordinateImage self n.val s := by
    apply Filter.eventually_all.mpr
    intro n
    have he : ∀ᶠ s in 𝓝 (1 : ℂ),
        Submodule.span ℂ (Set.range (symbolColumns self n.val (a n) s)) =
          symbolCoordinateImage self n.val s := by
      rw [← nonzeroParameter_map_nhds_one]
      exact (ha n).mono (fun s hs => hs.2)
    exact he.filter_mono nhdsWithin_le_nhds
  have hprobe : ∀ᶠ s in OrbIcoW.nonrealNhdsOne,
      ∀ n : Fin (2*N+1),
        ∀ u : Verma (familyCharge s) (symbolFamilyWeight self s),
          u ∈ sortedSpan _ _ n.val → symbolFamilyMap self s u=0 → uniformProbe _ _ u=0 := by
    apply Filter.eventually_all.mpr
    intro n
    have he : ∀ᶠ s in 𝓝 (1 : ℂ),
        ∀ u : Verma (familyCharge s) (symbolFamilyWeight self s),
          u ∈ sortedSpan _ _ n.val → symbolFamilyMap self s u=0 → uniformProbe _ _ u=0 := by
      rw [← nonzeroParameter_map_nhds_one]
      exact symbol_uniformProbe_kills_kernel_near self n.val
    exact he.filter_mono nhdsWithin_le_nhds
  have him : ∀ᶠ s in OrbIcoW.nonrealNhdsOne, (s^2).im≠0 :=
    OrbIcoW.square_tendsto_nonreal.eventually self_mem_nhdsWithin
  refine ⟨a,hLI,?_⟩
  filter_upwards [hnear,hprobe,him,self_mem_nhdsWithin] with s hsp hpr him hsnonreal
  have hs : s≠0 := by intro he; subst s; norm_num at hsnonreal
  obtain ⟨v,hv0,hvw,hvs⟩ := finite_generic_kernel_of_basis self N a indices hn s hs him hsp hpr
  refine ⟨v,?_,hvw,?_⟩
  · intro he
    rw [he,map_zero] at hv0
    exact zero_ne_one hv0
  · intro r
    rw [hv0,mul_one]
    exact hvs r

end VOA.Classification.COne.OrbIcoV
