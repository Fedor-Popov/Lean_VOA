import VOA.Moonshine.MoonshineCNPhysicalLie

/-! Functoriality of the physical quotient under Virasoro-intertwining linear maps. -/

namespace VOA.NearVOA

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

theorem primarySpurious_map (f : H →ₗ[ℂ] H)
    (hf : ∀ (n : ℤ) (v : H), f (V.L n v) = V.L n (f v))
    (v : H) (hv : v ∈ V.spurious) : f v ∈ V.spurious := by
  refine Submodule.iSup_induction (fun n : ℕ => LinearMap.range (V.L (-(n + 1 : ℤ))))
    (motive := fun v => f v ∈ V.spurious) hv ?_ ?_ ?_
  · intro n y hy
    obtain ⟨z, rfl⟩ := hy
    rw [hf]
    exact V.negativeVirasoro_mem_spurious n (f z)
  · change f 0 ∈ V.spurious
    rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

noncomputable def primaryLinearMap (f : H →ₗ[ℂ] H)
    (hf : ∀ (n : ℤ) (v : H), f (V.L n v) = V.L n (f v)) :
    V.primaryWeightOne →ₗ[ℂ] V.primaryWeightOne :=
  (f.comp V.primaryWeightOne.subtype).codRestrict V.primaryWeightOne fun v =>
    ⟨by change V.L 0 (f v) = f v; rw [← hf, v.property.1],
      fun n hn => by change V.L n (f v) = 0; rw [← hf, v.property.2 n hn, map_zero]⟩

/-- Every Virasoro-intertwining endomorphism induces a linear map on physical classes. -/
noncomputable def primaryQuotientMap (f : H →ₗ[ℂ] H)
    (hf : ∀ (n : ℤ) (v : H), f (V.L n v) = V.L n (f v)) :
    V.primaryLieQuotient →ₗ[ℂ] V.primaryLieQuotient :=
  V.primarySpurious.mapQ V.primarySpurious (V.primaryLinearMap f hf)
    (fun v hv => V.primarySpurious_map f hf v hv)

theorem primaryQuotientMap_mk (f : H →ₗ[ℂ] H)
    (hf : ∀ (n : ℤ) (v : H), f (V.L n v) = V.L n (f v))
    (v : V.primaryWeightOne) :
    V.primaryQuotientMap f hf (V.primarySpurious.mkQ v) =
      V.primarySpurious.mkQ (V.primaryLinearMap f hf v) := rfl

/-- An invertible Virasoro intertwiner preserving zero-products acts by Lie automorphisms. -/
noncomputable def primaryQuotientLieEquiv (e : H ≃ₗ[ℂ] H)
    (he : ∀ (n : ℤ) (v : H), e (V.L n v) = V.L n (e v))
    (hzero : ∀ u v : H, e (V.smul u 0 v) = V.smul (e u) 0 (e v)) :
    V.primaryLieQuotient ≃ₗ⁅ℂ⁆ V.primaryLieQuotient := by
  have hi : ∀ (n : ℤ) (v : H), e.symm (V.L n v) = V.L n (e.symm v) := by
    intro n v
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  refine
    { V.primaryQuotientMap e.toLinearMap he with
      invFun := V.primaryQuotientMap e.symm.toLinearMap hi
      left_inv := ?left_inv
      right_inv := ?right_inv
      map_lie' := ?map_lie' }
  case left_inv =>
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      change V.primarySpurious.mkQ _ = V.primarySpurious.mkQ v
      congr 1
      exact Subtype.ext (e.symm_apply_apply (v : H))
  case right_inv =>
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      change V.primarySpurious.mkQ _ = V.primarySpurious.mkQ v
      congr 1
      exact Subtype.ext (e.apply_symm_apply (v : H))
  case map_lie' =>
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ u =>
      induction y using Submodule.Quotient.induction_on with
      | _ v =>
        change V.primarySpurious.mkQ _ = V.primarySpurious.mkQ _
        congr 1
        exact Subtype.ext (hzero u v)

end VOA.NearVOA
