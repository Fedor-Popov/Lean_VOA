import VOA.Classification.COne.OrbIcoSpan

/-! # OrbIco: conjugation invariance of the primary reduction

`primaryC2Reduction_conj`: if `W₀^H` has the primary reduction with seeds `T`, then
`W₀^{hHh⁻¹}` has it with seeds `h T`, for every automorphism `h` of `W₀`. The map is
`x ↦ h x` (`conjMap`, the isomorphism of `orbifold_conj_iso`), which preserves modes, `L(n)`,
gradings, hence `O₂`, lower descendants and primaries.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VertexOperatorAlgebra OrbSpan OrbC2b OrbPrim

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W₀ : VertexOperatorAlgebra V}

/-- The conjugation isomorphism `W₀^H ≃ W₀^{hHh⁻¹}`, `x ↦ h x`. -/
def conjMap (h : Aut W₀) (H : Subgroup (Aut W₀)) :
    (orbifold H).carrier ≃ₗ[ℂ] (orbifold (H.map (MulAut.conj h).toMonoidHom)).carrier :=
  (Submodule.equivMapOfInjective h.toLinearEquiv.toLinearMap h.toLinearEquiv.injective
    (orbifold H).carrier).trans (LinearEquiv.ofEq _ _ (orbifold_map_conj h H))

theorem conjMap_val (h : Aut W₀) (H : Subgroup (Aut W₀)) (x : (orbifold H).carrier) :
    ((conjMap h H x : (orbifold (H.map (MulAut.conj h).toMonoidHom)).carrier) : V) =
      h (x : V) := rfl

theorem conjMap_smul (h : Aut W₀) (H : Subgroup (Aut W₀)) (a : (orbifold H).carrier) (n : ℤ)
    (b : (orbifold H).carrier) :
    conjMap h H ((orbifoldVOA H).smul a n b) =
      (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)).smul (conjMap h H a) n
        (conjMap h H b) := by
  apply Subtype.ext
  rw [conjMap_val, orb_smul_coe, orb_smul_coe, conjMap_val, conjMap_val]
  exact h.map_smul' _ _ _

theorem conjMap_L (h : Aut W₀) (H : Subgroup (Aut W₀)) (n : ℤ) (x : (orbifold H).carrier) :
    conjMap h H ((orbifoldVOA H).L n x) =
      (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)).L n (conjMap h H x) := by
  apply Subtype.ext
  rw [conjMap_val, orb_L_coe, orb_L_coe, conjMap_val]
  exact aut_comm_L h n _

theorem conjMap_grading (h : Aut W₀) (H : Subgroup (Aut W₀)) {N : ℤ} {x : (orbifold H).carrier}
    (hx : x ∈ (orbifoldVOA H).grading N) :
    conjMap h H x ∈ (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)).grading N := by
  rw [orb_mem_grading] at hx ⊢
  rw [conjMap_val]
  exact Aut.map_grading h hx

theorem conjMap_grading_iff (h : Aut W₀) (H : Subgroup (Aut W₀)) {N : ℤ}
    {x : (orbifold H).carrier} :
    conjMap h H x ∈ (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)).grading N ↔
      x ∈ (orbifoldVOA H).grading N := by
  refine ⟨fun hx => ?_, conjMap_grading h H⟩
  rw [orb_mem_grading] at hx ⊢
  rw [conjMap_val] at hx
  have := Aut.map_grading h⁻¹ hx
  rwa [Aut.inv_apply, Aut.coe_toLinearEquiv, LinearEquiv.symm_apply_apply] at this

theorem conjMap_O₂ (h : Aut W₀) (H : Subgroup (Aut W₀)) {x : (orbifold H).carrier}
    (hx : x ∈ O₂ (orbifoldVOA H)) :
    conjMap h H x ∈ O₂ (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    rw [conjMap_smul]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem conjMap_lowerDesc (h : Aut W₀) (H : Subgroup (Aut W₀)) {N : ℤ}
    {x : (orbifold H).carrier} (hx : x ∈ lowerDesc (orbifoldVOA H) N) :
    conjMap h H x ∈ lowerDesc (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)) N := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, y, hy, rfl⟩ := hx
    rw [conjMap_L]
    exact Submodule.subset_span ⟨m, _, conjMap_grading h H hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem conjMap_prim_iff (h : Aut W₀) (H : Subgroup (Aut W₀)) {N : ℤ}
    {x : (orbifold H).carrier} :
    conjMap h H x ∈ prim (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)) N ↔
      x ∈ prim (orbifoldVOA H) N := by
  rw [mem_prim, mem_prim, conjMap_grading_iff]
  refine and_congr_right fun _ => forall_congr' fun m => ?_
  rw [← conjMap_L, LinearEquiv.map_eq_zero_iff]

/-- **Conjugation invariance of the primary reduction.** -/
theorem primaryC2Reduction_conj (h : Aut W₀) (H : Subgroup (Aut W₀)) (T : Set (orbifold H).carrier)
    (hT : PrimaryC2Reduction (orbifoldVOA H) T) :
    PrimaryC2Reduction (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)) (conjMap h H '' T) := by
  intro N p hp
  obtain ⟨q, rfl⟩ := (conjMap h H).surjective p
  have hq := hT N ((conjMap_prim_iff h H).mp hp)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨o, ho, s, hs, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (conjMap_O₂ h H ho))
  · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    have := Submodule.mem_map_of_mem (f := (conjMap h H).toLinearMap) hs
    rwa [Submodule.map_span] at this
  · exact Submodule.mem_sup_right (conjMap_lowerDesc h H hz)

end VOA.Classification.COne.OrbIco
