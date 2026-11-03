import VOA.Classification.COne.PlusSplitCosets

/-!
# Nonintegral extensions over an arbitrary VOA

An ordinary kernel has invertible `L(0)-k` on every weight outside `k+ℤ`.
Correcting a lift of an upper eigenvector therefore makes it an eigenvector.
Its cyclic mode module stays in `k+ℤ` and is disjoint from the kernel.
No C₂-cofiniteness or local finiteness of the extension is assumed.
Reference: Abe, https://arxiv.org/html/math/0311210, Proposition 2.4.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting
open PlusRational VOA.Huang.LogRemovalAdmissible
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Correct an eigenvector lift across a kernel with disjoint ordinary spectrum. -/
theorem exists_isCompl_of_nonintegral_lift (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤) (k : ℂ)
    (hdiag : P.restrictScalars ℂ ≤ ⨆ μ : ℂ, ⨆ _ : ¬SameCoset k μ,
      P.restrictScalars ℂ ⊓ (L0 A).eigenspace μ)
    (x : M) (hx : x ∉ P) (hshift : (L0 A - k • 1) x ∈ P) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  let f := L0 A - k • 1
  have hrange : P.restrictScalars ℂ ≤ LinearMap.range (f.domRestrict (P.restrictScalars ℂ)) := by
    apply hdiag.trans
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ y hy
    have hne : μ - k ≠ 0 := by
      intro he
      exact hμ (by rw [sub_eq_zero.mp he]; exact sameCoset_refl k)
    refine ⟨⟨(μ - k)⁻¹ • y, (P.restrictScalars ℂ).smul_mem _ hy.1⟩, ?_⟩
    have he := Module.End.mem_eigenspace_iff.mp hy.2
    change (L0 A - k • 1) ((μ - k)⁻¹ • y) = y
    simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, he]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  obtain ⟨y, hy⟩ := hrange hshift
  have heig : x - (y : M) ∈ (L0 A).maxGenEigenspace k := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    have he : (L0 A - k • 1) (x - (y : M)) = 0 := by
      change f (x - (y : M)) = 0
      rw [map_sub, show f (y : M) = f x from hy, sub_self]
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] using he
  have hnot : x - (y : M) ∉ P := by
    intro hh
    exact hx (by simpa using P.add_mem hh y.property)
  have hother : P ≤ otherCosets A k := by
    apply hdiag.trans
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ z hz
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Module.End.eigenspace_le_maxGenEigenspace hz.2))
  let Q := cyclic A (x - (y : M))
  have hd : Disjoint P Q :=
    (cosetBlock_disjoint_otherCosets A k).symm.mono hother (cyclic_le_cosetBlock A k _ heig)
  have hu : P ⊔ Q = ⊤ := by
    rcases hP.wcovBy.eq_or_eq le_sup_left le_top with hh | hh
    · have hz : x - (y : M) ∈ P ⊔ Q :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      rw [hh] at hz
      exact (hnot hz).elim
    · exact hh
  exact ⟨Q, ⟨hd, codisjoint_iff.mpr hu⟩⟩

/-- An irreducible ordinary kernel supplies precisely the disjoint spectrum
needed to correct an upper eigenvector lift. -/
theorem exists_isCompl_of_ordinary_kernel (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤)
    (O : OrdVModule W P)
    (hO : O.toWeakModule = (show WeakModule W P from WeakModule.submodule A (ofR A P)))
    (hirr : O.IsIrreducible) (h k : ℂ) (hh : O.weight h ≠ ⊥)
    (hne : ¬SameCoset h k) (x : M) (hx : x ∉ P)
    (hshift : (L0 A - k • 1) x ∈ P) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  apply exists_isCompl_of_nonintegral_lift A P hP k _ x hx hshift
  intro y hy
  let z : P := ⟨y, hy⟩
  have hz : z ∈ ⨆ μ, O.weight μ := by
    rw [O.isInternal.submodule_iSup_eq_top]; trivial
  have hle : (⨆ μ, O.weight μ) ≤
      (⨆ μ : ℂ, ⨆ _ : ¬SameCoset k μ,
        P.restrictScalars ℂ ⊓ (L0 A).eigenspace μ).comap
          (P.subtype.restrictScalars ℂ) := by
    apply iSup_le
    intro μ v hv
    by_cases hμ : O.weight μ = ⊥
    · have hv0 : v = 0 := by simpa [hμ] using hv
      rw [hv0]
      exact Submodule.zero_mem _
    · have hcos := O.weight_eq_coset_of_irreducible hirr hh hμ
      have hnot : ¬SameCoset k μ := fun he => hne (sameCoset_trans hcos (sameCoset_symm he))
      refine Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hnot ⟨v.property, ?_⟩)
      change (v : M) ∈ (L0 A).eigenspace μ
      rw [Module.End.mem_eigenspace_iff]
      have he := O.L0_weight μ v hv
      change L0 O.toWeakModule v = μ • v at he
      rw [hO] at he
      exact congrArg Subtype.val he
  exact hle hz

/-- An extension with an irreducible ordinary kernel and a simple ordinary
quotient splits if their realized lowest weights differ modulo integers.
In fact any realized weights suffice, and no C₂ hypothesis is needed. -/
theorem exists_isCompl_of_ordinary_factors_nonintegral (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤)
    (O : OrdVModule W P)
    (hO : O.toWeakModule = (show WeakModule W P from WeakModule.submodule A (ofR A P)))
    (hirr : O.IsIrreducible)
    (T : OrdVModule W (M ⧸ P))
    (hT : T.toWeakModule =
      (show WeakModule W (M ⧸ P) from WeakModule.quotient A (ofR A P)))
    (h k : ℂ) (hh : O.weight h ≠ ⊥) (hk : T.weight k ≠ ⊥)
    (hne : ¬SameCoset h k) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  obtain ⟨x, hxv⟩ := P.mkQ_surjective v
  have hx : x ∉ P := by
    intro hx
    exact hv0 (hxv.symm.trans ((Submodule.Quotient.mk_eq_zero P).mpr hx))
  apply exists_isCompl_of_ordinary_kernel A P hP O hO hirr h k hh hne x hx
  apply (Submodule.Quotient.mk_eq_zero P).mp
  have he := T.L0_weight k v hv
  change L0 T.toWeakModule v = k • v at he
  rw [hT, ← hxv] at he
  have hcomm : P.mkQ (L0 A x) =
      L0 (show WeakModule W (M ⧸ P) from WeakModule.quotient A (ofR A P)) (P.mkQ x) := rfl
  change P.mkQ ((L0 A - k • 1) x) = 0
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub]
  rw [hcomm, he]
  change k • (P.mkQ.restrictScalars ℂ) x - (P.mkQ.restrictScalars ℂ) (k • x) = 0
  rw [map_smul, sub_self]

end VOA.Classification.COne.PlusSplitting
