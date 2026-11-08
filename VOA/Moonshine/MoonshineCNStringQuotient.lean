import VOA.Moonshine.MoonshineCNStringTransverse
import Mathlib.LinearAlgebra.Projection

/-! # The two abstract no-ghost quotient isometries

The forms descend through their actual radicals before any splitting is used.
The transverse identifications require the separately proved light-cone
splitting; the physical identification additionally requires charge 26.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

/-- The radical as a submodule of the restricted weight space itself. -/
def weightRadical (U : Submodule ℂ H) (N : ℤ) :
    Submodule ℂ (M.weightSlice U N) :=
  (M.formRadicalIn U N).comap (M.weightSlice U N).subtype

/-- The actual quotient of a weight slice by the radical of its form. -/
abbrev weightRadicalQuotient (U : Submodule ℂ H) (N : ℤ) :=
  M.weightSlice U N ⧸ M.weightRadical U N

theorem mem_weightRadical_iff (U : Submodule ℂ H) (N : ℤ)
    (x : M.weightSlice U N) :
    x ∈ M.weightRadical U N ↔ ∀ y : M.weightSlice U N, M.B x.val y.val = 0 := by
  change x.val ∈ M.formRadicalIn U N ↔ _
  rw [M.mem_formRadicalIn_iff]
  exact ⟨fun h y => h.2 y.val y.property,
    fun h => ⟨x.property, fun y hy => h ⟨y, hy⟩⟩⟩

def weightPairingDescend (U : Submodule ℂ H) (N : ℤ) (x : M.weightSlice U N) :
    M.weightRadicalQuotient U N →ₗ[ℂ] ℂ :=
  (M.weightRadical U N).liftQ ((M.stringWeightForm N).restrict (M.weightSlice U N) x)
    (by
      intro y hy
      change M.B x.val y.val = 0
      rw [M.B_symm.eq]
      exact (M.mem_weightRadical_iff U N y).mp hy x)

@[simp] theorem weightPairingDescend_mk (U : Submodule ℂ H) (N : ℤ)
    (x y : M.weightSlice U N) :
    M.weightPairingDescend U N x (Submodule.Quotient.mk y) = M.B x.val y.val := rfl

def weightPairingDescendLinear (U : Submodule ℂ H) (N : ℤ) :
    M.weightSlice U N →ₗ[ℂ] (M.weightRadicalQuotient U N →ₗ[ℂ] ℂ) where
  toFun := M.weightPairingDescend U N
  map_add' x y := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with | _ z =>
    exact M.B.map_add₂ x.val y.val z.val
  map_smul' a x := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with | _ z =>
    exact M.B.map_smul₂ a x.val z.val

/-- The bilinear form descended through the radical in both arguments. -/
def radicalQuotientForm (U : Submodule ℂ H) (N : ℤ) :
    LinearMap.BilinForm ℂ (M.weightRadicalQuotient U N) :=
  (M.weightRadical U N).liftQ (M.weightPairingDescendLinear U N) (by
    intro x hx
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with | _ y =>
    exact (M.mem_weightRadical_iff U N x).mp hx y)

@[simp] theorem radicalQuotientForm_mk (U : Submodule ℂ H) (N : ℤ)
    (x y : M.weightSlice U N) :
    M.radicalQuotientForm U N (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      M.B x.val y.val := rfl

theorem radicalQuotientForm_symm (U : Submodule ℂ H) (N : ℤ) :
    (M.radicalQuotientForm U N).IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  exact M.B_symm.eq x.val y.val

theorem radicalQuotientForm_nondegenerate (U : Submodule ℂ H) (N : ℤ) :
    (M.radicalQuotientForm U N).Nondegenerate := by
  have hleft : ∀ x, (∀ y, M.radicalQuotientForm U N x y = 0) → x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    intro hx
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (M.mem_weightRadical_iff U N x).mpr fun y => hx (Submodule.Quotient.mk y)
  exact ⟨hleft, fun x hx => hleft x fun y => by
    rw [(M.radicalQuotientForm_symm U N).eq]; exact hx y⟩

def transverseQuotientMap (U : Submodule ℂ H) (N : ℤ)
    (hTU : M.weightSlice M.transverse N ≤ M.weightSlice U N) :
    M.weightSlice M.transverse N →ₗ[ℂ] M.weightRadicalQuotient U N :=
  (M.weightRadical U N).mkQ.comp (Submodule.inclusion hTU)

theorem transverseQuotientMap_bijective (U : Submodule ℂ H) (N : ℤ)
    (hTU : M.weightSlice M.transverse N ≤ M.weightSlice U N)
    (hsum : M.weightSlice U N = M.weightSlice M.transverse N ⊔ M.formRadicalIn U N)
    (hdisj : Disjoint (M.weightSlice M.transverse N) (M.formRadicalIn U N)) :
    Function.Bijective (M.transverseQuotientMap U N hTU) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    have hr' : Submodule.inclusion hTU x ∈ M.weightRadical U N :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    have hr : x.val ∈ M.formRadicalIn U N := hr'
    exact Subtype.ext (Submodule.disjoint_def.mp hdisj x.val x.property hr)
  · intro q
    induction q using Submodule.Quotient.induction_on with | _ x =>
    have hx := hsum.le x.property
    obtain ⟨t, ht, r, hr, he⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    change t - x.val ∈ M.formRadicalIn U N
    rw [← he, sub_add_cancel_left]
    exact (M.formRadicalIn U N).neg_mem hr

def transverseQuotientEquivOfSplit (U : Submodule ℂ H) (N : ℤ)
    (hTU : M.weightSlice M.transverse N ≤ M.weightSlice U N)
    (hsum : M.weightSlice U N = M.weightSlice M.transverse N ⊔ M.formRadicalIn U N)
    (hdisj : Disjoint (M.weightSlice M.transverse N) (M.formRadicalIn U N)) :
    M.weightSlice M.transverse N ≃ₗ[ℂ] M.weightRadicalQuotient U N :=
  LinearEquiv.ofBijective (M.transverseQuotientMap U N hTU)
    (M.transverseQuotientMap_bijective U N hTU hsum hdisj)

@[simp] theorem transverseQuotientEquivOfSplit_apply (U : Submodule ℂ H) (N : ℤ)
    (hTU : M.weightSlice M.transverse N ≤ M.weightSlice U N)
    (hsum : M.weightSlice U N = M.weightSlice M.transverse N ⊔ M.formRadicalIn U N)
    (hdisj : Disjoint (M.weightSlice M.transverse N) (M.formRadicalIn U N))
    (x : M.weightSlice M.transverse N) :
    M.transverseQuotientEquivOfSplit U N hTU hsum hdisj x =
      Submodule.Quotient.mk (Submodule.inclusion hTU x) := rfl

/-- The natural isomorphism `T^N ≃ K^N / radical`, under the light-cone splitting. -/
def transverseKQuotientEquiv (hF : M.LightConeSplit) (N : ℤ) :
    M.weightSlice M.transverse N ≃ₗ[ℂ] M.weightRadicalQuotient M.kVacuum N :=
  M.transverseQuotientEquivOfSplit M.kVacuum N (fun _ h => h.2)
    (M.kVacuum_eq_transverse_sup_radical hF N) (M.transverse_radical_disjoint hF N)

/-- The natural critical-charge isomorphism `T¹ ≃ P¹ / radical`. -/
def transversePhysicalQuotientEquiv (hc : M.c = 26) (hF : M.LightConeSplit) :
    M.weightSlice M.transverse 1 ≃ₗ[ℂ] M.weightRadicalQuotient M.physical 1 :=
  M.transverseQuotientEquivOfSplit M.physical 1 (fun _ h => h.1)
    (by rw [M.physicalOne_radical_eq]; exact M.physicalOne_eq_transverse_sup_null hc hF)
    (by rw [M.physicalOne_radical_eq]; exact M.physicalOne_transverse_null_disjoint hF)

theorem transverseKQuotientEquiv_isometry (hF : M.LightConeSplit) (N : ℤ)
    (x y : M.weightSlice M.transverse N) :
    M.radicalQuotientForm M.kVacuum N (M.transverseKQuotientEquiv hF N x)
      (M.transverseKQuotientEquiv hF N y) = M.B x.val y.val := rfl

theorem transversePhysicalQuotientEquiv_isometry (hc : M.c = 26) (hF : M.LightConeSplit)
    (x y : M.weightSlice M.transverse 1) :
    M.radicalQuotientForm M.physical 1 (M.transversePhysicalQuotientEquiv hc hF x)
      (M.transversePhysicalQuotientEquiv hc hF y) = M.B x.val y.val := rfl

theorem physicalQuotientRepresentative_sub_mem (hc : M.c = 26) (hF : M.LightConeSplit)
    (p : M.weightSlice M.physical 1) :
    p.val - ((M.transversePhysicalQuotientEquiv hc hF).symm
      (Submodule.Quotient.mk p)).val ∈ M.weightSlice (M.physical ⊓ M.spurious) 1 := by
  let t := (M.transversePhysicalQuotientEquiv hc hF).symm (Submodule.Quotient.mk p)
  have he := (M.transversePhysicalQuotientEquiv hc hF).apply_symm_apply
    (Submodule.Quotient.mk p)
  have hr := (Submodule.Quotient.eq (M.weightRadical M.physical 1)).mp he.symm
  change p.val - t.val ∈ M.formRadicalIn M.physical 1 at hr
  rwa [M.physicalOne_radical_eq] at hr

/-- The inverse quotient isomorphism takes precisely the K-component in the light-cone
splitting `H = S ⊕ K`. -/
theorem physicalQuotientRepresentative_kComponent (hc : M.c = 26) (hF : M.LightConeSplit)
    (p : M.weightSlice M.physical 1) :
    (((M.transversePhysicalQuotientEquiv hc hF).symm
      (Submodule.Quotient.mk p)).val : H) =
      M.kVacuum.projection M.spurious hF.symm p.val := by
  let t := (M.transversePhysicalQuotientEquiv hc hF).symm (Submodule.Quotient.mk p)
  have hr := (M.physicalQuotientRepresentative_sub_mem hc hF p).2
  have hz := (Submodule.projection_apply_eq_zero_iff hF.symm).mpr hr
  have ht : M.kVacuum.projection M.spurious hF.symm (t.val : H) = t.val :=
    Submodule.projection_apply_left hF.symm ⟨t.val, t.property.2⟩
  change M.kVacuum.projection M.spurious hF.symm ((p.val : H) - t.val) = 0 at hz
  rw [map_sub, ht, sub_eq_zero] at hz
  exact hz.symm

end VOA.Moonshine.ConwayNorton.StringModule
