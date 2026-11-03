import VOA.Examples.AffineSl2HorizontalString
import VOA.Examples.AffineSl2ParabolicModule

/-! # Actual parabolic highest modules and singular-vector evaluation

The parabolic module is the genuine affine Verma quotient with the finite
horizontal highest-weight relation imposed. Its map to an actual homogeneous
primitive is constructed from enveloping-algebra evaluation.
-/
namespace VOA.AffineSl2GeneralRigidity
noncomputable section
open AffineVOA AffineVOA.HighestModule AffineVOA.Strong
open AffineLie UniversalEnvelopingAlgebra
open Module (End)

/-- Retain the actual currents and shift the degree origin to energy N.
The auxiliary vacuum is zero; this data is used only to assemble its Lie action. -/
def energyShiftCurrentData (k : ℂ) (N : ℤ) : AffineCurrentData k (WakModule k) where
  loopMode n := (vacuumRho kappaForm kappaForm_isInvariant k).toLinearMap.comp
    (ofLoopₗ kappaForm kappaForm_isInvariant n)
  degree := ell0OpA k + (N:ℂ) • 1
  vacuum := 0
  loop_comm x y m n := by
    change ⁅vacuumRho kappaForm kappaForm_isInvariant k (ofLoop _ _ x m),
      vacuumRho kappaForm kappaForm_isInvariant k (ofLoop _ _ y n)⁆ = _
    rw [← (vacuumRho kappaForm kappaForm_isInvariant k).map_lie, affine_bracket, map_add]
    congr 1
    split_ifs <;> simp only [map_smul,vacuum_acts_central,map_zero] <;> rfl
  degree_comm x n := by
    change ⁅ell0OpA k + (N:ℂ) • 1,
      vacuumRho kappaForm kappaForm_isInvariant k (ofLoop _ _ x n)⁆ = _
    have hz : ⁅(N:ℂ) • (1:End ℂ (WakModule k)),
        vacuumRho kappaForm kappaForm_isInvariant k (ofLoop _ _ x n)⁆ = 0 := by
      simp [Ring.lie_def]
    rw [add_lie,hz,add_zero]
    change ⁅vacuumRho kappaForm kappaForm_isInvariant k (ell0 _ _),
      vacuumRho kappaForm kappaForm_isInvariant k (ofLoop _ _ x n)⁆ = _
    rw [← (vacuumRho kappaForm kappaForm_isInvariant k).map_lie,
      ell0_lie_ofLoop,map_smul]
    rfl
  pos_annihilate x n hn := map_zero _
  degree_vacuum := map_zero _

/-- The shifted representation has exactly the original current modes. -/
theorem energyShiftCurrentData_mode (k : ℂ) (N : ℤ) (a : Fin 3) (n : ℤ) :
    (energyShiftCurrentData k N).rho (modeElement a n) = J k a n := by
  rw [modeElement,AffineCurrentData.rho_ofLoop]
  rfl

/-- An actual homogeneous affine primitive satisfies the universal highest
relations after shifting the degree origin to its conformal energy. -/
theorem energyShift_isHighest (k h : ℂ) (N : ℤ) (v : WakModule k)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v) :
    IsHighest (energyShiftCurrentData k N).rho v k h where
  central := (energyShiftCurrentData k N).rho_C
  degree := by
    rw [AffineCurrentData.rho_ell0]
    change ell0OpA k v + (N:ℂ) • v = 0
    rw [gradingZA_def,Module.End.mem_eigenspace_iff] at hn
    rw [hn]
    module
  modes a n hnot := by
    rw [energyShiftCurrentData_mode]
    have hn0 : 0 ≤ n := by
      simp only [HighestNormalOrdering.IsLower,not_or] at hnot
      omega
    by_cases hpos : 0 < n
    · rw [hp a n hpos,if_neg (by omega)]
    · have hnz : n=0 := by omega
      subst n
      fin_cases a
      · simpa using he
      · exact False.elim (hnot (by simp [HighestNormalOrdering.IsLower]))
      · simpa using hh

/-- The literal Verma evaluation at an actual primitive state. -/
def primitiveVermaMap (k h : ℂ) (N : ℤ) (v : WakModule k)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v) :
    Verma k h →ₗ[ℂ] WakModule k :=
  universalMap (energyShiftCurrentData k N).rho v (energyShift_isHighest k h N v hn hp he hh)

@[simp] theorem primitiveVermaMap_highest (k h : ℂ) (N : ℤ) (v : WakModule k)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v) :
    primitiveVermaMap k h N v hn hp he hh (highestVector k h)=v :=
  universalMap_highest _ _ _

/-- This is an actual affine-current homomorphism at every integer mode. -/
theorem primitiveVermaMap_mode (k h : ℂ) (N : ℤ) (v : WakModule k)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v)
    (a : Fin 3) (n : ℤ) (u : Verma k h) :
    primitiveVermaMap k h N v hn hp he hh (HighestModule.mode k h a n u)=
      J k a n (primitiveVermaMap k h N v hn hp he hh u) := by
  exact (universalMap_intertwines _ _ _ _ u).trans
    (congrArg (fun T : End ℂ (WakModule k) => T (primitiveVermaMap k h N v hn hp he hh u))
      (energyShiftCurrentData_mode k N a n))

end
end VOA.AffineSl2GeneralRigidity

namespace VOA.AffineVOA.HighestModule
noncomputable section
open UniversalEnvelopingAlgebra
open Module (End)
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Both the actual highest ideal and the finite horizontal relation
vanish under evaluation at a highest vector with a finite lowering string. -/
theorem parabolicIdeal_le_ker (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (v : E)
    {k : ℂ} {d : ℕ} (hv : IsHighest R v k (d:ℂ))
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) :
    (parabolicIdeal k d).restrictScalars ℂ ≤ LinearMap.ker (evaluate R v) := by
  intro u hu
  change u ∈ highestIdeal k (d:ℂ) ⊔ Submodule.span U {parabolicRelation d} at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
  have hzero : ∀ b ∈ Submodule.span U {parabolicRelation d}, evaluate R v b=0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
        have hz' : z=parabolicRelation d := Set.mem_singleton_iff.mp hz
        subst z
        change (lift ℂ R (parabolicRelation d)) v=0
        rw [parabolicRelation,map_pow,lift_ι_apply]
        exact hf
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add,ha,hb,add_zero]
    | smul a b _ hb =>
        change (lift ℂ R (a*b)) v=0
        rw [map_mul,Module.End.mul_apply]
        change (lift ℂ R a) (evaluate R v b)=0
        rw [hb,map_zero]
  change evaluate R v (a+b)=0
  rw [map_add, show evaluate R v a=0 from highestIdeal_le_ker R v hv ha,
    hzero b hb,add_zero]

/-- Canonical evaluation from the actual parabolic quotient. -/
def parabolicUniversalMap (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (v : E)
    {k : ℂ} {d : ℕ} (hv : IsHighest R v k (d:ℂ))
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) : Parabolic k d →ₗ[ℂ] E :=
  (((parabolicIdeal k d).restrictScalars ℂ).liftQ (evaluate R v)
    (parabolicIdeal_le_ker R v hv hf)).comp
    (Submodule.Quotient.restrictScalarsEquiv ℂ (parabolicIdeal k d)).symm.toLinearMap

@[simp] theorem parabolicUniversalMap_mk (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (v : E)
    {k : ℂ} {d : ℕ} (hv : IsHighest R v k (d:ℂ))
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) (u : U) :
    parabolicUniversalMap R v hv hf (Submodule.Quotient.mk u)=evaluate R v u := rfl

@[simp] theorem parabolicUniversalMap_highest (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (v : E)
    {k : ℂ} {d : ℕ} (hv : IsHighest R v k (d:ℂ))
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) :
    parabolicUniversalMap R v hv hf (parabolicHighest k d)=v := by
  rw [parabolicHighest,parabolicUniversalMap_mk,evaluate_one]

/-- The quotient evaluation intertwines the actual full affine action. -/
theorem parabolicUniversalMap_intertwines (R : AffSl2 →ₗ⁅ℂ⁆ End ℂ E) (v : E)
    {k : ℂ} {d : ℕ} (hv : IsHighest R v k (d:ℂ))
    (hf : (R (modeElement 1 0) ^ (d+1)) v=0) (x : AffSl2) (u : Parabolic k d) :
    parabolicUniversalMap R v hv hf (parabolicRho k d x u)=
      R x (parabolicUniversalMap R v hv hf u) := by
  obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective (parabolicIdeal k d) u
  rw [parabolicRho_mk,parabolicUniversalMap_mk,parabolicUniversalMap_mk]
  change (lift ℂ R (ι ℂ x*a)) v=R x ((lift ℂ R a) v)
  rw [map_mul,lift_ι_apply,Module.End.mul_apply]

end
end VOA.AffineVOA.HighestModule

namespace VOA.AffineSl2GeneralRigidity
noncomputable section
open AffineVOA AffineVOA.HighestModule AffineVOA.Strong
open AffineLie UniversalEnvelopingAlgebra
open Module (End)

/-- The actual parabolic map determined by a homogeneous affine primitive. -/
def primitiveParabolicMap (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v) :
    Parabolic k d →ₗ[ℂ] WakModule k :=
  parabolicUniversalMap (energyShiftCurrentData k N).rho v
    (energyShift_isHighest k d N v hn hp he hh)
    (by rw [energyShiftCurrentData_mode]; exact lowering_pow_succ_eq_zero k hk d hd v hv he hh)

@[simp] theorem primitiveParabolicMap_highest (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v) :
    primitiveParabolicMap k hk d hd N v hv hn hp he hh (parabolicHighest k d)=v :=
  parabolicUniversalMap_highest _ _ _ _

/-- The genuine parabolic evaluation preserves every current mode. -/
theorem primitiveParabolicMap_mode (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v)
    (a : Fin 3) (n : ℤ) (u : Parabolic k d) :
    primitiveParabolicMap k hk d hd N v hv hn hp he hh (parabolicMode k d a n u)=
      J k a n (primitiveParabolicMap k hk d hd N v hv hn hp he hh u) := by
  exact (parabolicUniversalMap_intertwines _ _ _ _ _ u).trans
    (congrArg (fun T : End ℂ (WakModule k) => T
      (primitiveParabolicMap k hk d hd N v hv hn hp he hh u))
      (energyShiftCurrentData_mode k N a n))

/-- All actual current descendants belong to the range of parabolic evaluation. -/
theorem currentDescendantSpan_le_primitiveParabolicMap_range
    (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v) :
    AffineSl2BoundaryMaximalIdeal.currentDescendantSpan k v ≤
      LinearMap.range (primitiveParabolicMap k hk d hd N v hv hn hp he hh) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil =>
      exact ⟨parabolicHighest k d, primitiveParabolicMap_highest k hk d hd N v hv hn hp he hh⟩
  | cons an l ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨parabolicMode k d an.1 an.2 u, ?_⟩
      rw [primitiveParabolicMap_mode,hu]
      rfl

/-- Every parabolic image lies in the actual VOA ideal generated by its primitive. -/
theorem primitiveParabolicMap_range_le_idealGen
    (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v) :
    LinearMap.range (primitiveParabolicMap k hk d hd N v hv hn hp he hh) ≤
      SingVec.idealGen (affineSl2VOA_closed k hk) v := by
  let I := SingVec.idealGen (affineSl2VOA_closed k hk) v
  let f := primitiveVermaMap k d N v hn hp he hh
  have hall : ∀ u, f u ∈ I := by
    have htop : (⊤ : Submodule ℂ (Verma k d)) ≤ I.comap f := by
      rw [← (occupationBasis k (d:ℂ)).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      change f (occupationBasis k (d:ℂ) t) ∈ I
      rw [occupationBasis_apply]
      change universalMap (energyShiftCurrentData k N).rho v _ _ ∈ I
      rw [universalMap_word]
      simp only [energyShiftCurrentData_mode]
      have hw (l : List (Fin 3 × ℤ)) :
          NormalOrdering.currentWord (J k) l v = AffineSl2BoundaryC2.currentWord k l v := by
        induction l with
        | nil => rfl
        | cons a l ih =>
            simpa only [NormalOrdering.currentWord,Module.End.mul_apply,
              AffineSl2BoundaryC2.currentWord_cons] using congrArg (J k a.1 a.2) ih
      rw [hw]
      exact AffineSl2BoundaryMaximalIdeal.currentWord_mem_idealGen k hk v _
    intro u
    exact htop Submodule.mem_top
  rintro _ ⟨u, rfl⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (parabolicIdeal k d) u
  exact hall (Submodule.Quotient.mk a)

/-- The image is exactly the genuine VOA ideal generated by the primitive.
This proves the first resolution map's image without a maximal-generation premise. -/
theorem primitiveParabolicMap_range
    (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v) :
    LinearMap.range (primitiveParabolicMap k hk d hd N v hv hn hp he hh) =
      SingVec.idealGen (affineSl2VOA_closed k hk) v := by
  apply le_antisymm (primitiveParabolicMap_range_le_idealGen k hk d hd N v hv hn hp he hh)
  rw [AffineSl2BoundaryMaximalIdeal.idealGen_eq_currentDescendantSpan]
  exact currentDescendantSpan_le_primitiveParabolicMap_range k hk d hd N v hv hn hp he hh

/-- The actual parabolic map shifts conformal energy by its primitive's degree. -/
theorem primitiveParabolicMap_energy
    (k : ℂ) (hk : k+2 ≠ 0) (d : ℕ) (hd : 0 < d)
    (N : ℤ) (v : WakModule k) (hv : v ≠ 0)
    (hn : v ∈ gradingZA k N) (hp : SingP k v)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = (d:ℂ) • v)
    (n : ℤ) (u : Parabolic k d)
    (hu : parabolicRho k d (ell0 kappaForm kappaForm_isInvariant) u = -(n:ℂ) • u) :
    primitiveParabolicMap k hk d hd N v hv hn hp he hh u ∈ gradingZA k (N+n) := by
  have ht := parabolicUniversalMap_intertwines (energyShiftCurrentData k N).rho v
    (energyShift_isHighest k d N v hn hp he hh)
    (show ((energyShiftCurrentData k N).rho (modeElement 1 0) ^ (d+1)) v=0 by
      rw [energyShiftCurrentData_mode]; exact lowering_pow_succ_eq_zero k hk d hd v hv he hh)
    (ell0 kappaForm kappaForm_isInvariant) u
  rw [hu,map_smul,AffineCurrentData.rho_ell0] at ht
  let w := primitiveParabolicMap k hk d hd N v hv hn hp he hh u
  change -(n:ℂ) • w = ell0OpA k w + (N:ℂ) • w at ht
  rw [gradingZA_def,Module.End.mem_eigenspace_iff]
  change ell0OpA k w = -((N+n:ℤ):ℂ) • w
  push_cast
  rw [eq_sub_of_add_eq ht.symm]
  module

/-- Every admissible parameter supplies a nonzero, genuine affine-current
map from the first parabolic term into the universal vacuum module, whose
image is the ideal generated by its actual first-null highest vector. -/
theorem admissible_first_parabolic_map_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q) :
    ∃ f : Parabolic ((p:ℂ)/q-2) (2*(p-1)) →ₗ[ℂ] WakModule ((p:ℂ)/q-2),
      f (parabolicHighest _ (2*(p-1))) ≠ 0 ∧
      (∀ a n u, f (parabolicMode _ (2*(p-1)) a n u)=J _ a n (f u)) ∧
      LinearMap.range f = SingVec.idealGen
        (affineSl2VOA_closed _ (admissible_level_noncritical p q hp hq))
        (f (parabolicHighest _ (2*(p-1)))) ∧
      LinearMap.range f ≤ QuotVOA.maxGradedIdeal
        (universal _ (admissible_level_noncritical p q hp hq)) := by
  let k : ℂ := (p:ℂ)/q-2
  let hk := admissible_level_noncritical p q hp hq
  obtain ⟨v, hv, hj, hi⟩ := admissible_first_null p q hp hq hcop
  have he := admissible_first_null_raising p q hp hq hcop v hj hi
  have hs := admissible_first_null_positive p q hp hq hcop v hj hi
  have hh : J k 2 0 v = ((2*(p-1):ℕ):ℂ) • v := by
    have h := ((mem_jointSpace_iff k hk _ _ v).mp hj).2
    change J k 2 0 v = ((2*((p:ℤ)-1):ℤ):ℂ) • v at h
    have hc : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_sub,Int.cast_natCast,
      Int.cast_one,Nat.cast_mul,Nat.cast_ofNat,hc] using h
  have hd : 0 < 2*(p-1) := by omega
  have hn := jointSpace_le_grading k hk _ _ hj
  let f := primitiveParabolicMap k hk (2*(p-1)) hd (q*(p-1):ℕ) v hv hn hs he hh
  have hf : f (parabolicHighest k (2*(p-1)))=v := primitiveParabolicMap_highest ..
  refine ⟨f, hf ▸ hv, fun a n u => primitiveParabolicMap_mode _ _ _ _ _ _ _ _ _ _ _ a n u, ?_, ?_⟩
  · rw [hf]
    exact primitiveParabolicMap_range ..
  · rw [primitiveParabolicMap_range]
    exact SingVec.idealGen_le (QuotVOA.maxGradedIdeal_isIdeal (universal k hk)) hi

end
end VOA.AffineSl2GeneralRigidity
