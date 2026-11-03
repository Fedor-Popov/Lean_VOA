import VOA.DeligneAudit.SL4TMarkedFlagDeletion

/-!
# A lower bound for a subspace from the power filtration of a nilpotent element

Let `C` be a finite-dimensional commutative algebra, `z ∈ C` with `z^N = 0`, and `I` a subspace.
If subspaces `W i` satisfy `z^i · W i ⊆ I + z^(i+1) C`, then the images of the `W i` in the
layers `C ⧸ (z^(i+1) : z^i)` have total dimension at most `dim I` (`layer_finrank_sum_le`). The
proof filters `I` by `I ∩ z^i C`: the image of `W i` in `z^i C / z^(i+1) C` lies in the image of
`I ∩ z^i C`, and the successive quotients of this filtration add up to `dim I`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Dimension of a subspace through its image in a quotient and its intersection with the
kernel. -/
theorem submodule_finrank_eq_map_mkQ_add_inf {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (S N : Submodule ℂ V) :
    Module.finrank ℂ S = Module.finrank ℂ (S.map N.mkQ) + Module.finrank ℂ ↥(S ⊓ N) := by
  let f := N.mkQ.comp S.subtype
  have hr : LinearMap.range f = S.map N.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : Module.finrank ℂ (LinearMap.ker f) = Module.finrank ℂ ↥(S ⊓ N) := by
    rw [← Submodule.finrank_map_subtype_eq S (LinearMap.ker f)]
    rw [show LinearMap.ker f = N.comap S.subtype by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ], Submodule.map_comap_subtype]
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hk] at hd
  exact hd.symm

/-- Two linear maps with the same kernel have images of the same dimension on every
subspace. -/
theorem finrank_map_eq_of_ker_eq {V V₁ V₂ : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V₁) (g : V →ₗ[ℂ] V₂) (h : LinearMap.ker f = LinearMap.ker g)
    (W : Submodule ℂ V) :
    Module.finrank ℂ (W.map f) = Module.finrank ℂ (W.map g) := by
  have hf := (f.comp W.subtype).finrank_range_add_finrank_ker
  have hg := (g.comp W.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.ker_comp, h, ← LinearMap.ker_comp] at hf
  rw [LinearMap.range_comp, Submodule.range_subtype] at hf hg
  omega

variable {C : Type*} [CommRing C] [Algebra ℂ C]

/-- Multiplication by `z^i` followed by the quotient by `z^(i+1) C`. -/
def layerMultiplication (z : C) (i : ℕ) :
    C →ₗ[ℂ] C ⧸ (Ideal.span {z ^ (i + 1)}).restrictScalars ℂ :=
  ((Ideal.span {z ^ (i + 1)}).restrictScalars ℂ).mkQ ∘ₗ LinearMap.mulLeft ℂ (z ^ i)

theorem layerMultiplication_ker (z : C) (i : ℕ) :
    LinearMap.ker (layerMultiplication z i) =
      LinearMap.ker (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal z i)).toLinearMap := by
  ext c
  simp only [LinearMap.mem_ker, layerMultiplication, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    rootPowerLayerIdeal_mem, Submodule.restrictScalars_mem]
  rw [mul_comm]

/-- **Layer lower bound.** If `z^i · W i ⊆ I + z^(i+1) C` for every `i < N` and `z^N = 0`, then
the images of the `W i` in the layer rings have total dimension at most `dim I`. -/
theorem layer_finrank_sum_le [FiniteDimensional ℂ C] (z : C) (N : ℕ) (hz : z ^ N = 0)
    (I : Submodule ℂ C) (W : ℕ → Submodule ℂ C)
    (hW : ∀ i < N, ∀ c ∈ W i,
      z ^ i * c ∈ I ⊔ (Ideal.span {z ^ (i + 1)}).restrictScalars ℂ) :
    ∑ i ∈ Finset.range N,
        Module.finrank ℂ ((W i).map (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal z i)).toLinearMap)
      ≤ Module.finrank ℂ I := by
  let F : ℕ → Submodule ℂ C := fun i => (Ideal.span {z ^ i}).restrictScalars ℂ
  let G : ℕ → Submodule ℂ C := fun i => I ⊓ F i
  have hFmono : ∀ i, F (i + 1) ≤ F i := by
    intro i c hc
    simp only [F, Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hc ⊢
    obtain ⟨a, rfl⟩ := hc
    exact ⟨a * z, by rw [pow_succ]; ring⟩
  have hstep : ∀ i, Module.finrank ℂ (G i) =
      Module.finrank ℂ ((G i).map (F (i + 1)).mkQ) + Module.finrank ℂ (G (i + 1)) := by
    intro i
    have he : G i ⊓ F (i + 1) = G (i + 1) := by
      simp only [G]
      rw [inf_assoc, inf_eq_right.mpr (hFmono i)]
    rw [submodule_finrank_eq_map_mkQ_add_inf (G i) (F (i + 1)), he]
  have hlayer : ∀ i < N, Module.finrank ℂ
      ((W i).map (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal z i)).toLinearMap) ≤
        Module.finrank ℂ ((G i).map (F (i + 1)).mkQ) := by
    intro i hi
    rw [← finrank_map_eq_of_ker_eq _ _ (layerMultiplication_ker z i)]
    apply Submodule.finrank_mono
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hW i hi c hc)
    refine ⟨a, ⟨ha, ?_⟩, ?_⟩
    · have hzc : z ^ i * c ∈ F i := by
        simp only [F, Submodule.restrictScalars_mem]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      have ha' : a = z ^ i * c - b := by rw [← hab]; ring
      rw [ha']
      exact Submodule.sub_mem _ hzc (hFmono i hb)
    · change (F (i + 1)).mkQ a = ((F (i + 1)).mkQ) (z ^ i * c)
      have hb0 : (F (i + 1)).mkQ b = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hb
      rw [← hab, map_add, hb0, add_zero]
  have htel : ∀ m, (∑ i ∈ Finset.range m, Module.finrank ℂ ((G i).map (F (i + 1)).mkQ)) +
      Module.finrank ℂ (G m) = Module.finrank ℂ (G 0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_assoc, ← hstep m, ih]
  have hG0 : G 0 = I := by
    simp only [G, F, pow_zero, Ideal.span_singleton_one, Submodule.restrictScalars_top,
      inf_top_eq]
  have hGN : Module.finrank ℂ (G N) = 0 := by
    have hF : F N = ⊥ := by
      simp only [F, hz, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.restrictScalars_bot]
    change Module.finrank ℂ ↥(I ⊓ F N) = 0
    rw [hF, inf_bot_eq, finrank_bot]
  have h := htel N
  rw [hGN, add_zero, hG0] at h
  rw [← h]
  exact Finset.sum_le_sum fun i hi => hlayer i (Finset.mem_range.mp hi)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.submodule_finrank_eq_map_mkQ_add_inf
#print axioms VOA.DeligneAudit.SL4T.finrank_map_eq_of_ker_eq
#print axioms VOA.DeligneAudit.SL4T.layerMultiplication
#print axioms VOA.DeligneAudit.SL4T.layerMultiplication_ker
#print axioms VOA.DeligneAudit.SL4T.layer_finrank_sum_le
