/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom
import VOA.Modules.ZhuVermaAnArchLUUniversal
import VOA.Modules.ZhuVermaAnArchLU
import VOA.Modules.ZhuVermaAnArchLUFiniteWeights
import VOA.Modularity.AModBridge
import VOA.Modularity.HL0Scoped

/-!
# Simple submodules of Zhu bottoms

This file supplies small closure constructions needed to apply the Dong--Jiang universal module
to a Zhu submodule.  The main bottom-simplicity theorem is assembled below from the same universal
map and the canonical PBW bottom projection used elsewhere in the project.
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open Module (End)
open VertexOperatorAlgebra
open VHat VHat.DLM3
open GradedLWWeakModule

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}

/-- An intrinsic Zhu submodule, bundled as a Zhu module in its own right. -/
noncomputable def AModSubmodule.toAMod {U : AMod W} (S : AModSubmodule U) : AMod W where
  carrier := S.carrier
  ρ :=
    { toFun := fun a =>
        { toFun := fun x => ⟨U.ρ a x, S.ρ_mem a x.2⟩
          map_add' := fun x y => by
            ext
            exact map_add (U.ρ a) (x : U.carrier) (y : U.carrier)
          map_smul' := fun c x => by
            ext
            exact map_smul (U.ρ a) c (x : U.carrier) }
      map_add' := fun a b => by
        ext x
        exact congrArg (fun f : End ℂ U.carrier => f (x : U.carrier)) (map_add U.ρ a b)
      map_smul' := fun c a => by
        ext x
        exact congrArg (fun f : End ℂ U.carrier => f (x : U.carrier)) (map_smul U.ρ c a) }
  ρ_one := by
    ext x
    exact congrArg (fun f : End ℂ U.carrier => f (x : U.carrier)) U.ρ_one
  ρ_mul := fun a b => by
    ext x
    exact congrArg (fun f : End ℂ U.carrier => f (x : U.carrier)) (U.ρ_mul a b)

/-- The inclusion of a Zhu submodule into its ambient Zhu module. -/
noncomputable def AModSubmodule.inclusion {U : AMod W} (S : AModSubmodule U) :
    S.toAMod.carrier →ₗ[ℂ] U.carrier :=
  S.carrier.subtype

@[simp] theorem AModSubmodule.inclusion_apply {U : AMod W} (S : AModSubmodule U)
    (x : S.toAMod.carrier) : S.inclusion x = S.carrier.subtype x := rfl

/-- The submodule inclusion intertwines the Zhu actions. -/
theorem AModSubmodule.inclusion_ρ {U : AMod W} (S : AModSubmodule U)
    (a : A W) (x : S.toAMod.carrier) :
    S.inclusion (S.toAMod.ρ a x) = U.ρ a (S.inclusion x) := rfl

/-- A nonzero Zhu submodule has a nontrivial bundled carrier. -/
theorem AModSubmodule.nontrivial_of_ne_bot {U : AMod W} (S : AModSubmodule U)
    (hS : S.carrier ≠ ⊥) : Nontrivial S.toAMod.carrier := by
  rw [Submodule.ne_bot_iff] at hS
  obtain ⟨x, hx, hx0⟩ := hS
  exact ⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩

/-- Over a semisimple Zhu algebra, every nonzero intrinsic Zhu submodule contains a simple
intrinsic Zhu submodule. -/
theorem AModSubmodule.exists_simple_submodule
    (hss : letI := instRingA W; IsSemisimpleRing (A W)) {U : AMod W}
    (S : AModSubmodule U) (hS : S.carrier ≠ ⊥) :
    ∃ T : AModSubmodule S.toAMod, IsSimpleAMod T.toAMod := by
  letI := instRingA W
  letI := S.toAMod.moduleA
  letI : IsSemisimpleRing (A W) := hss
  letI : Nontrivial S.toAMod.carrier := S.nontrivial_of_ne_bot hS
  obtain ⟨T, hT⟩ :=
    IsSemisimpleModule.exists_simple_submodule (A W) S.toAMod.carrier
  let T' : AModSubmodule S.toAMod := S.toAMod.toAModSubmodule T
  refine ⟨T', ?_⟩
  letI := T'.toAMod.moduleA
  exact (isSimpleAMod_iff_isSimpleModule T'.toAMod).mpr hT

/-! ## Embedding a Zhu module into an irreducible bottom -/

/-- An injective Zhu-module map into the bottom of a lowest-weight module. -/
structure AModBottomEmbedding (U : AMod W) (P : LWModule W) where
  toLinearMap : U.carrier →ₗ[ℂ] P.toAMod.carrier
  injective : Function.Injective toLinearMap
  map_ρ : ∀ (a : A W) (x : U.carrier),
    toLinearMap (U.ρ a x) = P.toAMod.ρ a (toLinearMap x)

namespace AModBottomEmbedding

variable {U : AMod W} {P : LWModule W}

-- Typeclass search does not unfold the `AMod.toAmModZero` bridge deeply enough to recover
-- the canonical direct-sum instances.  Register those same instances at the bridged type.
noncomputable local instance inducedCarrierAddCommGroup (T : AMod W) :
    AddCommGroup (DJCarrier W T.toAmModZero) :=
  DirectSum.instAddCommGroup (fun n => DJPiece W T.toAmModZero n)

noncomputable local instance inducedCarrierModule (T : AMod W) :
    Module ℂ (DJCarrier W T.toAmModZero) :=
  DirectSum.instModule

/-- A Zhu module embedded in `P_h` has the same conformal-vector scalar `h`. -/
theorem omegaScalar (e : AModBottomEmbedding U P) : U.OmegaScalar P.h := by
  ext x
  apply e.injective
  rw [LinearMap.smul_apply, map_smul, e.map_ρ]
  exact AMod.omegaScalar_apply (lowestAMod_omegaScalar P.isLow) (e.toLinearMap x)

/-- The embedding, viewed as a linear map into the full carrier of `P`. -/
noncomputable def carrierMap (e : AModBottomEmbedding U P) : U.carrier →ₗ[ℂ] P.carrier :=
  (P.isMod.weight P.h).subtype.comp e.toLinearMap

theorem carrierMap_injective (e : AModBottomEmbedding U P) :
    Function.Injective e.carrierMap :=
  (P.isMod.weight P.h).injective_subtype.comp e.injective

theorem carrierMap_mem_bottom (e : AModBottomEmbedding U P) (x : U.carrier) :
    e.carrierMap x ∈ P.isMod.weight P.h :=
  (e.toLinearMap x).2

theorem carrierMap_mem_level_zero (e : AModBottomEmbedding U P) (x : U.carrier) :
    e.carrierMap x ∈ (pAdmLev P).lev 0 := by
  have hlev : (pAdmLev P).lev 0 = P.isMod.weight P.h := by
    show (if (0 : ℤ) ≤ 0 then P.isMod.weight (P.h + ((0 : ℤ) : ℂ)) else ⊥) =
      P.isMod.weight P.h
    rw [if_pos le_rfl, Int.cast_zero, add_zero]
  rw [hlev]
  exact e.carrierMap_mem_bottom x

/-- The embedded bottom map is equivariant in the exact `AmMod W 0` form consumed by the
Dong--Jiang universal map. -/
theorem carrierMap_act (e : AModBottomEmbedding U P) (a : 𝒱) (x : U.carrier) :
    e.carrierMap (U.toAmModZero.ρ (mkAnFull W 0 a) x) =
      oLevW P.isMod.toWeakModule (0 : ℤ) a (e.carrierMap x) := by
  rw [AMod.toAmModZero_ρ]
  change (P.isMod.weight P.h).subtype
      (e.toLinearMap (U.ρ (VOA.mk W a) x)) = _
  rw [e.map_ρ, oLevW_zero_eq_oMod]
  exact actA_mk_apply_coe P.isMod P.isLow a (e.toLinearMap x)

/-- The Dong--Jiang universal map induced by a Zhu embedding into a lowest-weight bottom. -/
noncomputable def universalMap (e : AModBottomEmbedding U P) :
    DJCarrier W U.toAmModZero →ₗ[ℂ] P.carrier :=
  oLevUnivMap P.isMod.toWeakModule (pAdmLev P) U.toAmModZero e.carrierMap
    e.carrierMap_mem_level_zero e.carrierMap_act

/-- On the vacuum tensor, the universal map is the original bottom embedding. -/
theorem universalMap_bottom (e : AModBottomEmbedding U P) (x : U.carrier) :
    e.universalMap (djVacTensor W U.toAmModZero x) = e.carrierMap x := by
  simp only [universalMap, djVacTensor_def, oLevUnivMap_incl,
    oLevPieceMap_mk, Nat.cast_zero, sub_zero, oLevW_zero_eq_oMod,
    oMod_vacuum, LinearMap.id_coe, id_eq]
  rfl

/-- The universal map intertwines every mode. -/
theorem universalMap_intertwine (e : AModBottomEmbedding U P) (p : ℤ) (a : 𝒱)
    (x : DJCarrier W U.toAmModZero) :
    e.universalMap (djModeZero W U.toAmModZero p a x) =
      P.isMod.toWeakModule.act a p (e.universalMap x) :=
  oLevUnivMap_intertwine (pAdmLev P) U.toAmModZero e.carrierMap
    e.carrierMap_mem_level_zero e.carrierMap_act p a x

/-- The image of the universal map as a weak submodule of the target. -/
noncomputable def universalRange (e : AModBottomEmbedding U P) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := LinearMap.range e.universalMap
  act_mem a n x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact LinearMap.mem_range.mpr ⟨djModeZero W U.toAmModZero n a y,
      e.universalMap_intertwine n a y⟩

/-- Into an irreducible target, a nonzero bottom embedding induces a surjective universal map. -/
theorem universalMap_surjective (e : AModBottomEmbedding U P) (hP : P.IsIrreducibleLW)
    (hU : Nontrivial U.carrier) : Function.Surjective e.universalMap := by
  have hne : e.universalRange.carrier ≠ ⊥ := by
    obtain ⟨x, y, hxy⟩ := hU
    let u : U.carrier := x - y
    have hu : u ≠ 0 := sub_ne_zero.mpr hxy
    have hmem : e.carrierMap u ∈ e.universalRange.carrier :=
      LinearMap.mem_range.mpr ⟨djVacTensor W U.toAmModZero u, e.universalMap_bottom u⟩
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    exact hu (e.carrierMap_injective (by rw [hmem, map_zero]))
  rcases hP.2 e.universalRange with hbot | htop
  · exact absurd hbot hne
  · exact LinearMap.range_eq_top.mp htop

/-- The kernel of the induced universal map as a weak submodule of the Dong--Jiang carrier. -/
noncomputable def universalKer (e : AModBottomEmbedding U P) :
    WeakModule.Submodule' (djCarrierWeak W U.toAmModZero) where
  carrier := LinearMap.ker e.universalMap
  act_mem a n x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [djCarrierWeak_act, e.universalMap_intertwine, hx, WeakModule.act_def, map_zero]

/-- The image of a weak submodule under the universal map. -/
noncomputable def universalImage (e : AModBottomEmbedding U P)
    (Q : WeakModule.Submodule' (djCarrierWeak W U.toAmModZero)) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := Submodule.map e.universalMap Q.carrier
  act_mem a n x hx := by
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨(djCarrierWeak W U.toAmModZero).act a n q,
      Q.act_mem a n hq, ?_⟩
    rw [djCarrierWeak_act, e.universalMap_intertwine]

/-- The universal kernel is maximal when the target is irreducible. -/
theorem universalKer_maximal (e : AModBottomEmbedding U P) (hP : P.IsIrreducibleLW)
    (Q : WeakModule.Submodule' (djCarrierWeak W U.toAmModZero))
    (hQ : e.universalKer.carrier ≤ Q.carrier) :
    Q.carrier = e.universalKer.carrier ∨ Q.carrier = ⊤ := by
  rcases hP.2 (e.universalImage Q) with hbot | htop
  · left
    have hQker : Q.carrier ≤ e.universalKer.carrier := by
      intro z hz
      rw [show e.universalKer.carrier = LinearMap.ker e.universalMap from rfl,
        LinearMap.mem_ker]
      have hzm : e.universalMap z ∈ Submodule.map e.universalMap Q.carrier :=
        Submodule.mem_map_of_mem hz
      rw [show Submodule.map e.universalMap Q.carrier = ⊥ from hbot] at hzm
      exact (Submodule.mem_bot ℂ).mp hzm
    exact le_antisymm hQker hQ
  · right
    rw [eq_top_iff]
    intro x _
    obtain ⟨q, hq, hqx⟩ : ∃ q ∈ Q.carrier, e.universalMap q = e.universalMap x := by
      have hx : e.universalMap x ∈ Submodule.map e.universalMap Q.carrier := by
        rw [show Submodule.map e.universalMap Q.carrier = ⊤ from htop]
        exact Submodule.mem_top
      exact Submodule.mem_map.mp hx
    have hxq : x - q ∈ e.universalKer.carrier := by
      rw [show e.universalKer.carrier = LinearMap.ker e.universalMap from rfl,
        LinearMap.mem_ker, map_sub, hqx, sub_self]
    have hx : x = (x - q) + q := by abel
    rw [hx]
    exact Q.carrier.add_mem (hQ hxq) hq

/-- The universal kernel meets the PBW bottom trivially. -/
theorem universalKer_bottom_trivial (e : AModBottomEmbedding U P)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    e.universalKer.carrier ⊓ DJCarrier.deg W U.toAmModZero 0 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzker, hzdeg⟩ := Submodule.mem_inf.mp hz
  rw [Submodule.mem_bot]
  have hpz : e.universalMap z = 0 := hzker
  let w : U.carrier := djCarrierWeak_bottom_equiv Pr U.toAmModZero ⟨z, hzdeg⟩
  have hsymm : (djCarrierWeak_bottom_equiv Pr U.toAmModZero).symm w = ⟨z, hzdeg⟩ :=
    LinearEquiv.symm_apply_apply _ _
  have hvac : (((djCarrierWeak_bottom_equiv Pr U.toAmModZero).symm w :
      DJCarrier.deg W U.toAmModZero 0) : DJCarrier W U.toAmModZero) =
      djVacTensor W U.toAmModZero w :=
    degMEquiv_symm_eq_vacTensor
      (djAnnEqAn_zero_of_gate (gate_le_of_pbwDatum Pr)) U.toAmModZero w
  rw [hsymm] at hvac
  have hzv : z = djVacTensor W U.toAmModZero w := hvac
  rw [hzv, e.universalMap_bottom] at hpz
  have hw0 : w = 0 := e.carrierMap_injective (by rw [hpz, map_zero])
  have hζ0 : (⟨z, hzdeg⟩ : DJCarrier.deg W U.toAmModZero 0) = 0 := by
    rw [← hsymm, hw0]
    exact map_zero _
  exact congrArg Subtype.val hζ0

/-- The kernel of the universal map is Dong--Jiang's canonical maximal bottom-trivial submodule. -/
theorem universalKer_eq_djJ (e : AModBottomEmbedding U P)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hP : P.IsIrreducibleLW) (hU : Nontrivial U.carrier) :
    e.universalKer.carrier =
      (djJ Pr U.toAmModZero hU P.h (genHL0 U P.h e.omegaScalar)).carrier :=
  djJ_unique Pr U.toAmModZero hU P.h (genHL0 U P.h e.omegaScalar) e.universalKer
    (e.universalKer_bottom_trivial Pr) (e.universalKer_maximal hP)

/-- The induced quotient by Dong--Jiang's canonical kernel is linearly equivalent to the
irreducible target. -/
noncomputable def universalLinEquiv (e : AModBottomEmbedding U P)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hP : P.IsIrreducibleLW) (hU : Nontrivial U.carrier) :
    (DJCarrier W U.toAmModZero ⧸
      (djJ Pr U.toAmModZero hU P.h (genHL0 U P.h e.omegaScalar)).carrier) ≃ₗ[ℂ]
      P.carrier :=
  (Submodule.quotEquivOfEq _ _ (e.universalKer_eq_djJ Pr hP hU).symm).trans
    (e.universalMap.quotKerEquivOfSurjective (e.universalMap_surjective hP hU))

@[simp] theorem universalLinEquiv_mk (e : AModBottomEmbedding U P)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hP : P.IsIrreducibleLW) (hU : Nontrivial U.carrier)
    (x : DJCarrier W U.toAmModZero) :
    e.universalLinEquiv Pr hP hU (Submodule.Quotient.mk x) = e.universalMap x := by
  unfold universalLinEquiv
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

/-- The quotient equivalence intertwines all vertex-operator modes. -/
theorem universalLinEquiv_act (e : AModBottomEmbedding U P)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hP : P.IsIrreducibleLW) (hU : Nontrivial U.carrier) (a : 𝒱) (n : ℤ)
    (x : DJCarrier W U.toAmModZero ⧸
      (djJ Pr U.toAmModZero hU P.h (genHL0 U P.h e.omegaScalar)).carrier) :
    e.universalLinEquiv Pr hP hU
        ((djLU Pr U.toAmModZero hU P.h (genHL0 U P.h e.omegaScalar)).toWeakModule.act a n x) =
      P.isMod.toWeakModule.act a n (e.universalLinEquiv Pr hP hU x) := by
  refine Submodule.Quotient.induction_on _ x (fun z => ?_)
  rw [djLU_act_mk, e.universalLinEquiv_mk, e.universalLinEquiv_mk,
    e.universalMap_intertwine]

/-- Every Zhu embedding into the bottom of an irreducible lowest-weight module is surjective.
The proof identifies the target with `L(U)` and uses that `L(U)`'s lowest-weight space is `U`. -/
theorem toLinearMap_surjective (e : AModBottomEmbedding U P)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hP : P.IsIrreducibleLW) (hU : Nontrivial U.carrier) :
    Function.Surjective e.toLinearMap := by
  intro y
  let hL0 := genHL0 U P.h e.omegaScalar
  let F := e.universalLinEquiv Pr hP hU
  let N := djLU Pr U.toAmModZero hU P.h hL0
  let yP : P.carrier := (P.isMod.weight P.h).subtype y
  let x : DJCarrier W U.toAmModZero ⧸
      (djJ Pr U.toAmModZero hU P.h hL0).carrier := F.symm yP
  have hFx : F x = yP := F.apply_symm_apply _
  have hxL0 : N.L0op x = P.h • x := by
    apply F.injective
    change F (N.toWeakModule.act W.conformalVector 1 x) = F (P.h • x)
    rw [show F (N.toWeakModule.act W.conformalVector 1 x) =
        P.isMod.toWeakModule.act W.conformalVector 1 (F x) from
      e.universalLinEquiv_act Pr hP hU W.conformalVector 1 x,
      map_smul, hFx]
    exact P.isMod.L0_weight P.h yP y.2
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  have hxmem : x ∈ N.weight P.h := mem_weight_of_L0op_eq N hxL0
  let xb : N.weight P.h := ⟨x, hxmem⟩
  let z := (djLU_bottom_equiv Pr U.toAmModZero hU P.h hL0).symm xb
  have hxdec : x = Submodule.Quotient.mk (z : DJCarrier W U.toAmModZero) :=
    LU_bottom_equiv_symm_coe (djGradedLW_of_pbwDatum Pr U.toAmModZero hU P.h hL0) xb
  have hzdeg : (z : DJCarrier W U.toAmModZero) ∈ DJCarrier.deg W U.toAmModZero 0 := by
    have hw : (djGradedLW_of_pbwDatum Pr U.toAmModZero hU P.h hL0).weight P.h =
        DJCarrier.deg W U.toAmModZero 0 := djCWeight_zero U.toAmModZero P.h
    rw [← hw]
    exact z.2
  let u : U.carrier := djCarrierWeak_bottom_equiv Pr U.toAmModZero ⟨z, hzdeg⟩
  have hsymm : (djCarrierWeak_bottom_equiv Pr U.toAmModZero).symm u = ⟨z, hzdeg⟩ :=
    LinearEquiv.symm_apply_apply _ _
  have hvac : (((djCarrierWeak_bottom_equiv Pr U.toAmModZero).symm u :
      DJCarrier.deg W U.toAmModZero 0) : DJCarrier W U.toAmModZero) =
      djVacTensor W U.toAmModZero u :=
    degMEquiv_symm_eq_vacTensor
      (djAnnEqAn_zero_of_gate (gate_le_of_pbwDatum Pr)) U.toAmModZero u
  rw [hsymm] at hvac
  refine ⟨u, Subtype.ext ?_⟩
  change e.carrierMap u = yP
  calc
    e.carrierMap u = e.universalMap (djVacTensor W U.toAmModZero u) :=
      (e.universalMap_bottom u).symm
    _ = F (Submodule.Quotient.mk (djVacTensor W U.toAmModZero u)) :=
      (e.universalLinEquiv_mk Pr hP hU _).symm
    _ = F x := by rw [← hvac, ← hxdec]
    _ = yP := hFx

end AModBottomEmbedding

/-! ## Simplicity of an irreducible lowest-weight bottom -/

/-- If the Zhu algebra is semisimple, the bottom of every irreducible lowest-weight module is a
simple Zhu module.  A nonzero bottom submodule contains a simple constituent; its universal
Dong--Jiang module maps onto the irreducible target, and the lowest-weight-space comparison above
forces that constituent to equal the entire bottom. -/
theorem isSimpleAMod_of_irreducible_of_semisimple
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (P : LWModule W) (hP : P.IsIrreducibleLW) : IsSimpleAMod P.toAMod := by
  refine ⟨nontrivial_toAMod P, fun S => ?_⟩
  by_cases hS : S.carrier = ⊥
  · exact Or.inl hS
  · right
    obtain ⟨T, hT⟩ := S.exists_simple_submodule hss hS
    let e : AModBottomEmbedding T.toAMod P :=
      { toLinearMap := S.inclusion.comp T.inclusion
        injective := S.carrier.injective_subtype.comp T.carrier.injective_subtype
        map_ρ a x := by
          change S.inclusion (T.inclusion (T.toAMod.ρ a x)) =
            P.toAMod.ρ a (S.inclusion (T.inclusion x))
          rw [T.inclusion_ρ, S.inclusion_ρ] }
    have hsurj : Function.Surjective e.toLinearMap :=
      e.toLinearMap_surjective Pr hP hT.1
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht⟩ := hsurj x
    rw [← ht]
    exact (T.inclusion t).2

end VOA
