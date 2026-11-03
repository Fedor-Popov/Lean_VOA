import VOA.Classification.COne.OrbOddPrim

/-!
# OrbSgl (1): the Virasoro primaries of `W = V₂^{A₄}` in weights `9` and `16`

* `prim_nine`: every primary of weight `9` is a multiple of `u = T I₃`.
* `prim_sixteen`: every primary of weight `16` is a multiple of `v = T I₄`.

Proof: `PrimModel.span` puts a primary in `span T(invariants of degree √N)` plus lower
descendants; the descendant part is a primary in `lowerDesc`, hence `0` (unitarity of `V₂`);
`A₄`-invariants of degree `3` are spanned by `I₃`, of degree `4` by `r⁴, I₄`, and
`T(r⁴) = 0` (`ψ(r²) = 0`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 OrbZhu OrbOdd
  VOA.LatGen VOA.LatGen.Triplet MvPolynomial

/-- `tetra ≅ A₄` is finite (the same instance as in `OrbZhuGraded`). -/
noncomputable local instance tetraFintypeS : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

theorem tT_r2_sq : tT (r2 ^ 2) = 0 := by
  have h : T2 (r2 ^ 2) = 0 := by
    rw [T2_apply, map_pow, psi_r2, zero_pow two_ne_zero, map_zero]
  simp only [tT, avgT, LinearMap.comp_apply, h, map_zero]

/-- The target in weights `9` and `16`. -/
def sglTarget (N : ℤ) : Submodule ℂ (orbifold tetra).carrier :=
  if N = 9 then ℂ ∙ tetraU else if N = 16 then ℂ ∙ tetraV else ⊤

theorem tT_genMon_mem {t : ℕ × ℕ × ℕ × ℕ} (ht : gdeg t = 3 ∨ gdeg t = 4) :
    tT (genMon t) ∈ sglTarget ((gdeg t : ℤ) ^ 2) := by
  have h5 : gdeg t ≤ 5 := by omega
  rcases gdeg_le_five h5 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [gdeg] at ht <;> norm_num at ht
  · -- `I₃`
    have h3 : genMon (0, 1, 0, 0) = I3 := by simp [genMon]
    rw [h3, sglTarget, if_pos (by simp [gdeg])]
    exact Submodule.mem_span_singleton_self _
  · -- `r⁴`
    have h4 : genMon (2, 0, 0, 0) = r2 ^ 2 := by simp [genMon]
    rw [h4, tT_r2_sq]
    exact Submodule.zero_mem _
  · -- `I₄`
    have h4 : genMon (0, 0, 1, 0) = I4 := by simp [genMon]
    rw [h4, sglTarget, if_neg (by simp [gdeg]), if_pos (by simp [gdeg])]
    exact Submodule.mem_span_singleton_self _

theorem prim_sgl {N : ℤ} (hN : N = 9 ∨ N = 16) {y : (orbifold tetra).carrier}
    (hy : y ∈ prim Wt N) : y ∈ sglTarget N := by
  have hsp := tetraPrimModel.span N hy
  obtain ⟨t, ht, l, hl, rfl⟩ := Submodule.mem_sup.mp hsp
  have htp : t ∈ prim Wt N := by
    refine (Submodule.span_le.mpr ?_) ht
    rintro _ ⟨F, ⟨hF, n, hh, hnN⟩, rfl⟩
    rw [← hnN]; exact tT_prim hF hh
  have hl0 : l = 0 := by
    apply prim_lowerDesc_eq_zero (N := N) _ hl
    have : l = (t + l) - t := by abel
    rw [this]; exact Submodule.sub_mem _ hy htp
  subst hl0
  rw [add_zero]
  refine (Submodule.span_le.mpr ?_) ht
  rintro _ ⟨F, ⟨hF, n, hh, hnN⟩, rfl⟩
  have hn : n = 3 ∨ n = 4 := by
    have hle : n ≤ 4 := by
      by_contra h
      have : (5 : ℤ) ^ 2 ≤ (n : ℤ) ^ 2 := by
        have : (5 : ℤ) ≤ n := by omega
        nlinarith
      omega
    interval_cases n <;> norm_num at hnN <;> omega
  have hs := mem_span_genMon_of_isHomogeneous hF hh
  have hmap := Submodule.mem_map_of_mem (f := tT) hs
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨t, htd, rfl⟩, rfl⟩
  simp only [Set.mem_setOf_eq] at htd
  have := tT_genMon_mem (t := t) (by rw [htd]; exact hn)
  rwa [htd, hnN] at this

/-- The weight-nine primaries are the multiples of `u`. -/
theorem prim_nine {y : (orbifold tetra).carrier} (hy : y ∈ prim Wt 9) :
    ∃ a : ℂ, y = a • tetraU := by
  have h := prim_sgl (Or.inl rfl) hy
  rw [sglTarget, if_pos rfl] at h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  exact ⟨a, ha.symm⟩

/-- The weight-sixteen primaries are the multiples of `v`. -/
theorem prim_sixteen {y : (orbifold tetra).carrier} (hy : y ∈ prim Wt 16) :
    ∃ b : ℂ, y = b • tetraV := by
  have h := prim_sgl (Or.inr rfl) hy
  rw [sglTarget, if_neg (by norm_num), if_pos rfl] at h
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h
  exact ⟨b, hb.symm⟩

end VOA.Classification.COne.OrbSgl
