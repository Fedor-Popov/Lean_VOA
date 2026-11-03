import VOA.Classification.COne.OrbZhuParity
import VOA.Classification.COne.OrbPrimTop

/-!
# OrbOdd (5): `τ`-odd Virasoro primaries of `W = V₂^{A₄}` in weights `≤ 25`

`τ = tetraInvolution` (the octahedral involution, `τu = -u`, `τv = v`).

* `tT_prim`: the averaged polynomial model `T F` of an `A₄`-invariant homogeneous `F` of
  degree `n` is a Virasoro primary of weight `n²`.
* `prim_lowerDesc_eq_zero`: a primary lying in the lower descendants vanishes (unitarity of
  `V₂`, restricted to `W`).
* `tT_r2_mul_I3`: `T(r² I₃) = 0` (`ψ(r²) = 0`).
* `odd_prim`: a `τ`-odd primary of weight `N ≤ 25` is a multiple of `u = T I₃` when `N = 9`
  and vanishes otherwise.

Proof of the last: `PrimModel.span` puts a primary in `span T(invariants of degree √N)` plus
lower descendants; the descendant part is a primary in `lowerDesc`, hence `0`; invariants of
degree `≤ 5` are spanned by `1, r², I₃, r⁴, I₄, r² I₃`, on which `τ` acts by `I₃ ↦ -I₃` only.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 OrbZhu
  VOA.LatGen VOA.LatGen.Triplet MvPolynomial

/-- `tetra ≅ A₄` is finite (the same instance as in `OrbZhuGraded`). -/
noncomputable local instance tetraFintypeO : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

theorem tT_prim {F : P3} {n : ℕ} (hF : IsA4Inv F) (hh : F.IsHomogeneous n) :
    tT F ∈ prim Wt ((n : ℤ) ^ 2) := by
  rw [mem_prim]
  refine ⟨avgT_grading tetraV2Model hF hh, fun m => ?_⟩
  apply Subtype.ext
  change (V2m 1 le_rfl).L ((m : ℤ) + 1) ((avgT tetra T2 F : (orbifold tetra).carrier) :
    LatModuleGen (latP 1)) = 0
  rw [avgT_coe tetraV2Model hF]
  exact ((mem_prim _).mp (T2_prim hh)).2 m

theorem prim_lowerDesc_eq_zero {N : ℤ} {y : (orbifold tetra).carrier} (hp : y ∈ prim Wt N)
    (hl : y ∈ lowerDesc Wt N) : y = 0 := by
  have h := prim_inf_lowerDesc (W := Wt) ((v2VirUnitary_holds.some).restrict (orbifold tetra)) N
  have : y ∈ prim Wt N ⊓ lowerDesc Wt N := ⟨hp, hl⟩
  rw [h] at this
  exact (Submodule.mem_bot ℂ).mp this

theorem tT_r2_mul_I3 : tT (r2 * I3) = 0 := by
  have h : T2 (r2 * I3) = 0 := by
    rw [T2_apply, map_mul, psi_r2, zero_mul, map_zero]
  simp only [tT, avgT, LinearMap.comp_apply, h, map_zero]

/-- Generator monomials of degree `≤ 5`. -/
theorem gdeg_le_five {t : ℕ × ℕ × ℕ × ℕ} (ht : gdeg t ≤ 5) :
    t = (0, 0, 0, 0) ∨ t = (1, 0, 0, 0) ∨ t = (0, 1, 0, 0) ∨ t = (2, 0, 0, 0) ∨
      t = (0, 0, 1, 0) ∨ t = (1, 1, 0, 0) := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [gdeg] at ht
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 1 := by omega
  have hc : c ≤ 1 := by omega
  have hd : d = 0 := by omega
  subst hd
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

/-- The odd part `z - τ z`. -/
def oddD : P3 →ₗ[ℂ] (orbifold tetra).carrier :=
  tT - tetraInvolution.toLinearEquiv.toLinearMap ∘ₗ tT

theorem oddD_apply (F : P3) : oddD F = tT F - tetraInvolution (tT F) := rfl

theorem oddD_fixed {F : P3} (hF : IsA4Inv F) (hφ : phiE (octHom transposition) F = F) :
    oddD F = 0 := by
  rw [oddD_apply, tetraInvolution_tT hF (by rw [hφ]; exact hF), hφ, sub_self]

/-- The target of the odd part in weight `N`. -/
def oddTarget (N : ℤ) : Submodule ℂ (orbifold tetra).carrier :=
  if N = 9 then ℂ ∙ tetraU else ⊥

theorem oddD_genMon {t : ℕ × ℕ × ℕ × ℕ} (ht : gdeg t ≤ 5) :
    oddD (genMon t) ∈ oddTarget ((gdeg t : ℤ) ^ 2) := by
  rcases gdeg_le_five ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [oddD_fixed (isA4Inv_genMon _) (by simp [genMon])]; exact Submodule.zero_mem _
  · rw [oddD_fixed (isA4Inv_genMon _) (by simp [genMon, phiE_rot2_r2])]
    exact Submodule.zero_mem _
  · have h3 : genMon (0, 1, 0, 0) = I3 := by simp [genMon]
    rw [h3, oddD_apply]
    have hτ := tetraInvolution_U
    change tetraU - tetraInvolution tetraU ∈ _
    rw [hτ, sub_neg_eq_add, oddTarget, if_pos (by simp [gdeg])]
    rw [← two_smul ℂ tetraU]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [oddD_fixed (isA4Inv_genMon _) (by simp [genMon, map_pow, phiE_rot2_r2])]
    exact Submodule.zero_mem _
  · rw [oddD_fixed (isA4Inv_genMon _) (by simp [genMon, phiE_rot2_I4])]
    exact Submodule.zero_mem _
  · have h5 : genMon (1, 1, 0, 0) = r2 * I3 := by simp [genMon]
    rw [h5, oddD_apply, tT_r2_mul_I3, map_zero, sub_zero]
    exact Submodule.zero_mem _

theorem oddD_mem_of_inv {F : P3} {n : ℕ} (hF : IsA4Inv F) (hh : F.IsHomogeneous n)
    (hn : n ≤ 5) : oddD F ∈ oddTarget ((n : ℤ) ^ 2) := by
  have hs := mem_span_genMon_of_isHomogeneous hF hh
  have hmap := Submodule.mem_map_of_mem (f := oddD) hs
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  have := oddD_genMon (t := t) (by rw [ht]; exact hn)
  rwa [ht] at this

/-- `τ`-odd primaries of weight `N ≤ 25`. -/
theorem odd_prim {N : ℤ} (hN : N ≤ 25) {y : (orbifold tetra).carrier} (hy : y ∈ prim Wt N)
    (hodd : tetraInvolution y = -y) : y ∈ oddTarget N := by
  have hsp := tetraPrimModel.span N hy
  obtain ⟨t, ht, l, hl, rfl⟩ := Submodule.mem_sup.mp hsp
  -- the span part is primary
  have htp : t ∈ prim Wt N := by
    refine (Submodule.span_le.mpr ?_) ht
    rintro _ ⟨F, ⟨hF, n, hh, hnN⟩, rfl⟩
    rw [← hnN]; exact tT_prim hF hh
  have hl0 : l = 0 := by
    apply prim_lowerDesc_eq_zero (N := N) _ hl
    have : l = (t + l) - t := by abel
    rw [this]; exact Submodule.sub_mem _ hy htp
  subst hl0
  rw [add_zero] at hodd ⊢
  -- `2 t = t - τ t` lies in the target
  have hD : t - tetraInvolution t ∈ oddTarget N := by
    have hmap : t ∈ Submodule.span ℂ (tT '' invDeg N) := ht
    have key : ∀ z ∈ Submodule.span ℂ (tT '' invDeg N), z - tetraInvolution z ∈ oddTarget N := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨F, ⟨hF, n, hh, hnN⟩, rfl⟩ := hz
        have hn : n ≤ 5 := by
          by_contra h
          have : (6 : ℤ) ^ 2 ≤ (n : ℤ) ^ 2 := by
            have : (6 : ℤ) ≤ n := by omega
            nlinarith
          omega
        have := oddD_mem_of_inv hF hh hn
        rw [hnN] at this
        exact this
      | zero => simp
      | add x y _ _ hx hy =>
        have e : x + y - tetraInvolution (x + y) =
            (x - tetraInvolution x) + (y - tetraInvolution y) := by
          rw [show tetraInvolution (x + y) = tetraInvolution x + tetraInvolution y from
            map_add tetraInvolution.toLinearEquiv x y]
          abel
        rw [e]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have e : c • x - tetraInvolution (c • x) = c • (x - tetraInvolution x) := by
          rw [show tetraInvolution (c • x) = c • tetraInvolution x from
            map_smul tetraInvolution.toLinearEquiv c x, smul_sub]
        rw [e]; exact Submodule.smul_mem _ _ hx
    exact key t hmap
  rw [hodd, sub_neg_eq_add, ← two_smul ℂ t] at hD
  have := Submodule.smul_mem _ ((2 : ℂ)⁻¹) hD
  rwa [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at this

end VOA.Classification.COne.OrbOdd
