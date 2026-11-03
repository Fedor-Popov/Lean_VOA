import VOA.Classification.COne.OrbC2Reduction

/-! # Restriction and iterated fixed points

The automorphism and the VOA isomorphism are constructed on the actual
subtype carriers. No orbifold cofiniteness theorem is assumed here.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbC2b
open VOA VertexOperatorAlgebra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V}

/-- Restrict an automorphism which preserves a subVOA in both directions. -/
def restrictAut (S : VOASubalgebra W) (g : Aut W)
    (h : ∀ x, g x ∈ S.carrier ↔ x ∈ S.carrier) : Aut S.toVOA where
  toLinearEquiv :=
    { toFun := fun x => ⟨g x, (h x).mpr x.2⟩
      invFun := fun x => ⟨g.toLinearEquiv.symm x,
        (h _).mp (by simpa only [Aut.coe_toLinearEquiv, LinearEquiv.apply_symm_apply] using x.2)⟩
      left_inv := fun x => Subtype.ext (g.toLinearEquiv.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (g.toLinearEquiv.apply_symm_apply x)
      map_add' := fun x y => Subtype.ext (map_add g.toLinearEquiv x.val y.val)
      map_smul' := fun c x => Subtype.ext (map_smul g.toLinearEquiv c x.val) }
  map_smul' := fun x n y => Subtype.ext (g.map_smul' x n y)
  map_vacuum := Subtype.ext g.map_vacuum
  map_omega := Subtype.ext g.map_omega

@[simp] theorem restrictAut_val (S : VOASubalgebra W) (g : Aut W)
    (h : ∀ x, g x ∈ S.carrier ↔ x ∈ S.carrier) (x : S.carrier) :
    (restrictAut S g h x : V) = g x := rfl

theorem restrictAut_pow_val (S : VOASubalgebra W) (g : Aut W)
    (h : ∀ x, g x ∈ S.carrier ↔ x ∈ S.carrier) (n : ℕ) (x : S.carrier) :
    ((restrictAut S g h ^ n) x : V) = (g ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Aut.mul_apply, restrictAut_val, ih]

theorem restrictAut_pow_eq_one (S : VOASubalgebra W) (g : Aut W)
    (h : ∀ x, g x ∈ S.carrier ↔ x ∈ S.carrier) {n : ℕ} (hn : g ^ n = 1) :
    restrictAut S g h ^ n = 1 := by
  apply Aut.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simpa [hn] using restrictAut_pow_val S g h n x

/-- Fixed by a generated extension iff fixed at both steps. -/
theorem mem_join_fixed_iff (K : Subgroup (Aut W)) (g : Aut W) (x : V) :
    x ∈ (orbifold (K ⊔ Subgroup.zpowers g)).carrier ↔
      x ∈ (orbifold K).carrier ∧ g x = x := by
  change (K ⊔ Subgroup.zpowers g ≤ fixSub x) ↔ _
  rw [sup_le_iff, Subgroup.zpowers_le]
  rfl

/-- `(W^K)^g` and `W^(K ∨ ⟨g⟩)` are isomorphic as VOAs, including conformal vectors. -/
theorem iterated_orbifold_iso (K : Subgroup (Aut W)) (g : Aut W)
    (h : ∀ x, g x ∈ (orbifold K).carrier ↔ x ∈ (orbifold K).carrier) :
    VOAIsomorphic
      (orbifoldVOA (Subgroup.zpowers (restrictAut (orbifold K) g h)))
      (orbifoldVOA (K ⊔ Subgroup.zpowers g)) := by
  let e : (orbifold (Subgroup.zpowers (restrictAut (orbifold K) g h))).carrier ≃ₗ[ℂ]
      (orbifold (K ⊔ Subgroup.zpowers g)).carrier :=
    { toFun := fun x => ⟨x.1.1, (mem_join_fixed_iff K g x.1.1).mpr
        ⟨x.1.2, congrArg Subtype.val ((mem_orbifold_zpowers_iff _ _).mp x.2)⟩⟩
      invFun := fun x => ⟨⟨x.1, ((mem_join_fixed_iff K g x.1).mp x.2).1⟩,
        (mem_orbifold_zpowers_iff _ _).mpr
          (Subtype.ext ((mem_join_fixed_iff K g x.1).mp x.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ⟨e, ⟨rfl, fun _ _ _ => rfl⟩, rfl⟩

/-- The second-step moving-pair bound suffices; no descent from ambient C₂ is used. -/
theorem join_c2Cofinite_of_movingPairs (K : Subgroup (Aut W)) (g : Aut W)
    (h : ∀ x, g x ∈ (orbifold K).carrier ↔ x ∈ (orbifold K).carrier)
    [Fintype (Subgroup.zpowers (restrictAut (orbifold K) g h))]
    (hK : C2Cofinite (orbifoldVOA K))
    (hp : OrbC2.MovingPairSpanFinite
      (Subgroup.zpowers (restrictAut (orbifold K) g h))) :
    C2Cofinite (orbifoldVOA (K ⊔ Subgroup.zpowers g)) := by
  obtain ⟨e, he, _⟩ := iterated_orbifold_iso K g h
  exact ConverseUniverse.c2Cofinite_of_iso e.symm (isVOAHom_symm' e he)
    ((OrbC2.movingPairSpanFinite_iff_c2Cofinite
      (Subgroup.zpowers (restrictAut (orbifold K) g h)) hK).mp hp)

end VOA.Classification.COne.OrbC2b
