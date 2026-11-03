/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.SchurWeylDLMProofOccurs

/-!
# Dong–Li–Mason Schur–Weyl duality for finite groups — proved (`dlmSchurWeyl_holds`)

For a simple VOA `W` and a finite group `G ≤ Aut W`, and irreducible finite-dimensional
representations `σ`, `σ'` of `G`:

* (occurs) `multSpace_ne_bot` (`SchurWeylDLMProofOccurs.lean`): `Hom_G(E, 𝒱) ≠ 0`;
* (irreducible) `multSpace_irreducible`: every `W^G`-mode-stable subspace of `Hom_G(E, 𝒱)` is
  `0` or everything.  Proof: a nonzero `φ` is injective (`E` irreducible); Jacobson density gives
  `ψ = f ∘ φ` with `f` in the mode algebra; Li's lemma and averaging over `G` put
  `ψ` in the span of `u₍ₙ₎ ∘ φ`, `u ∈ W^G` (`mem_invSpan_of_comp`);
* (inequivalent) `multSpace_inequivalent`: a `W^G`-mode-commuting map
  `T : Hom_G(E, 𝒱) → Hom_G(E', 𝒱)` with `σ ≇ σ'` vanishes.  Proof: for `ψ = Tφ ≠ 0`, the images
  of `φ` and `ψ` meet trivially (`range_inf_range_eq_bot`, Schur for `G`), so `χ = (φ, ψ)` on
  `E × E'` is injective; density gives `f` with `f ∘ χ = (0, ψ)`, which is `G`-equivariant, hence
  in the `W^G`-span of `χ`, which lies in the graph of `T`; so `ψ = T 0 = 0`.

`dlmSchurWeyl_holds : DLMSchurWeyl` — the Prop of `SchurWeylDLM.lean`, with no hypotheses.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.SchurWeyl

open VOA Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A nonzero `G`-map out of an irreducible representation is injective. -/
theorem injective_of_mem_multSpace {G : Subgroup (Aut W)} {E : Type*} [AddCommGroup E]
    [Module ℂ E] {σ : Representation ℂ G E} (hσ : σ.IsIrreducible) {φ : E →ₗ[ℂ] 𝒱}
    (hφ : φ ∈ multSpace G σ) (h0 : φ ≠ 0) : Function.Injective φ := by
  rw [← LinearMap.ker_eq_bot]
  rcases stable_eq_bot_or_top hσ (LinearMap.ker φ) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← hφ g x, hx]
      exact map_zero (g : Aut W).toLinearEquiv) with h | h
  · exact h
  · exact absurd (LinearMap.ker_eq_top.mp h) h0

/-- **Irreducibility clause.** -/
theorem multSpace_irreducible (hW : W.IsSimple) (G : Subgroup (Aut W)) [Finite G] {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] {σ : Representation ℂ G E}
    (hσ : σ.IsIrreducible) (P : Submodule ℂ (E →ₗ[ℂ] 𝒱)) (hPle : P ≤ multSpace G σ)
    (hP : ModeStable G P) : P = ⊥ ∨ P = multSpace G σ := by
  haveI := Fintype.ofFinite G
  by_cases hbot : P = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨φ, hφP, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hφ := hPle hφP
  have hinj := injective_of_mem_multSpace hσ hφ hφ0
  refine le_antisymm hPle (fun ψ hψ => ?_)
  obtain ⟨f, hf, hfψ⟩ := exists_modeAlgebra_comp_eq hW hinj ψ
  have hmem := mem_invSpan_of_comp G σ hφ hf (by rw [hfψ]; exact hψ)
  rw [hfψ] at hmem
  exact invSpan_le G (Set.singleton_subset_iff.mpr hφP) hP hmem

/-- Images of `G`-embeddings of inequivalent irreducibles meet trivially. -/
theorem range_inf_range_eq_bot {G : Subgroup (Aut W)} {E E' : Type*} [AddCommGroup E]
    [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] {σ : Representation ℂ G E}
    {σ' : Representation ℂ G E'} (hσ : σ.IsIrreducible) (hσ' : σ'.IsIrreducible)
    (hne : IsEmpty (σ.Equiv σ')) {φ : E →ₗ[ℂ] 𝒱} (hφ : φ ∈ multSpace G σ)
    (hφi : Function.Injective φ) {ψ : E' →ₗ[ℂ] 𝒱} (hψ : ψ ∈ multSpace G σ')
    (hψi : Function.Injective ψ) : LinearMap.range φ ⊓ LinearMap.range ψ = ⊥ := by
  haveI := hσ
  haveI := hσ'
  haveI := hne
  haveI := nontrivial_of_isIrreducible hσ
  have hstab : ∀ (g : G) (x : E), x ∈ (LinearMap.range ψ).comap φ →
      σ g x ∈ (LinearMap.range ψ).comap φ := by
    intro g x hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨σ' g y, by rw [← hψ g y, hy, hφ g x]⟩
  rcases stable_eq_bot_or_top hσ _ hstab with h | h
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨x, rfl⟩, hz2⟩ := hz
    have hx : x ∈ (LinearMap.range ψ).comap φ := hz2
    rw [h] at hx
    rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
    exact Submodule.zero_mem _
  · exfalso
    obtain ⟨r, hr⟩ := ψ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hψi)
    have hfac : ∀ x, ψ (r (φ x)) = φ x := by
      intro x
      have hx : x ∈ (LinearMap.range ψ).comap φ := h ▸ Submodule.mem_top
      obtain ⟨y, hy⟩ := hx
      rw [← hy, ← LinearMap.comp_apply r ψ, hr, LinearMap.id_apply]
    let F : Representation.IntertwiningMap σ σ' :=
      ⟨r ∘ₗ φ, fun g => LinearMap.ext fun x => hψi (by
        simp only [LinearMap.comp_apply]
        rw [hfac, ← hψ g, hfac, hφ g x])⟩
    have hF0 : F = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    apply hx
    apply hφi
    rw [map_zero, ← hfac x]
    have hrx : r (φ x) = 0 := by
      have := congrArg (fun F : Representation.IntertwiningMap σ σ' => F x) hF0
      simpa [F] using this
    rw [hrx, map_zero]

/-- **Inequivalence clause.** -/
theorem multSpace_inequivalent (hW : W.IsSimple) (G : Subgroup (Aut W)) [Finite G] {E E' : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [AddCommGroup E'] [Module ℂ E']
    [FiniteDimensional ℂ E'] {σ : Representation ℂ G E} {σ' : Representation ℂ G E'}
    (hσ : σ.IsIrreducible) (hσ' : σ'.IsIrreducible) (hne : IsEmpty (σ.Equiv σ'))
    (T : multSpace G σ →ₗ[ℂ] multSpace G σ')
    (hT : ∀ u (hu : u ∈ (orbifold G).carrier) (n : ℤ) (φ : multSpace G σ),
      (T ⟨(modeOp W u n).comp φ, modeOp_comp_mem G σ hu n φ.2⟩ : E' →ₗ[ℂ] 𝒱) =
        (modeOp W u n).comp (T φ : E' →ₗ[ℂ] 𝒱)) : T = 0 := by
  haveI := Fintype.ofFinite G
  apply LinearMap.ext
  intro φ
  by_contra hTφ
  set ψ : E' →ₗ[ℂ] 𝒱 := (T φ : E' →ₗ[ℂ] 𝒱) with hψdef
  have hψ0 : ψ ≠ 0 := fun h => hTφ (Subtype.ext h)
  have hφ0 : (φ : E →ₗ[ℂ] 𝒱) ≠ 0 := by
    intro h
    apply hTφ
    have : φ = 0 := Subtype.ext h
    rw [this, map_zero, LinearMap.zero_apply]
  have hφi := injective_of_mem_multSpace hσ φ.2 hφ0
  have hψi := injective_of_mem_multSpace hσ' (T φ).2 hψ0
  have hinter := range_inf_range_eq_bot hσ hσ' hne φ.2 hφi (T φ).2 hψi
  let χ : E × E' →ₗ[ℂ] 𝒱 := LinearMap.coprod (φ : E →ₗ[ℂ] 𝒱) ψ
  have hχ : χ ∈ multSpace G (σ.prod σ') := by
    rintro g ⟨e, e'⟩
    simp only [χ, LinearMap.coprod_apply]
    rw [← Aut.coe_toLinearEquiv, map_add, Aut.coe_toLinearEquiv, Aut.coe_toLinearEquiv,
      φ.2 g e, (T φ).2 g e']
    rfl
  have hχi : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨e, e'⟩ h
    simp only [χ, LinearMap.coprod_apply] at h
    have hmem : (φ : E →ₗ[ℂ] 𝒱) e ∈ LinearMap.range (φ : E →ₗ[ℂ] 𝒱) ⊓ LinearMap.range ψ :=
      ⟨⟨e, rfl⟩, ⟨-e', by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left h).symm⟩⟩
    rw [hinter] at hmem
    have he : (φ : E →ₗ[ℂ] 𝒱) e = 0 := (Submodule.mem_bot ℂ).mp hmem
    have he' : ψ e' = 0 := by rw [he, zero_add] at h; exact h
    rw [Prod.mk_eq_zero]
    exact ⟨hφi (by rw [he, map_zero]), hψi (by rw [he', map_zero])⟩
  have htarget : ψ ∘ₗ LinearMap.snd ℂ E E' ∈ multSpace G (σ.prod σ') := by
    rintro g ⟨e, e'⟩
    exact (T φ).2 g e'
  obtain ⟨f, hf, hfχ⟩ := exists_modeAlgebra_comp_eq hW hχi (ψ ∘ₗ LinearMap.snd ℂ E E')
  have hmem := mem_invSpan_of_comp G (σ.prod σ') hχ hf (by rw [hfχ]; exact htarget)
  rw [hfχ] at hmem
  -- the graph of `T` inside `Hom(E × E', 𝒱)`
  let Φ : multSpace G σ →ₗ[ℂ] (E × E' →ₗ[ℂ] 𝒱) :=
    { toFun := fun ξ => LinearMap.coprod (ξ : E →ₗ[ℂ] 𝒱) (T ξ : E' →ₗ[ℂ] 𝒱)
      map_add' := fun a b => by
        apply LinearMap.ext
        rintro ⟨e, e'⟩
        simp only [LinearMap.coprod_apply, Submodule.coe_add, map_add, LinearMap.add_apply]
        abel
      map_smul' := fun c a => by
        apply LinearMap.ext
        rintro ⟨e, e'⟩
        simp only [LinearMap.coprod_apply, Submodule.coe_smul, map_smul, LinearMap.smul_apply,
          RingHom.id_apply, smul_add] }
  have hQ : ModeStable G (LinearMap.range Φ) := by
    rintro u hu n _ ⟨ξ, rfl⟩
    refine ⟨⟨(modeOp W u n).comp ξ, modeOp_comp_mem G σ hu n ξ.2⟩, ?_⟩
    apply LinearMap.ext
    rintro ⟨e, e'⟩
    change (modeOp W u n) ((ξ : E →ₗ[ℂ] 𝒱) e) +
        (T ⟨(modeOp W u n).comp ξ, modeOp_comp_mem G σ hu n ξ.2⟩ : E' →ₗ[ℂ] 𝒱) e' =
      (modeOp W u n) ((ξ : E →ₗ[ℂ] 𝒱) e + (T ξ : E' →ₗ[ℂ] 𝒱) e')
    rw [hT u hu n ξ, map_add]
    rfl
  have hχQ : χ ∈ LinearMap.range Φ := ⟨φ, rfl⟩
  obtain ⟨ξ, hξ⟩ := invSpan_le G (Set.singleton_subset_iff.mpr hχQ) hQ hmem
  have hξ0 : ξ = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro e
    have := congrArg (fun F : E × E' →ₗ[ℂ] 𝒱 => F (e, 0)) hξ
    simpa [Φ] using this
  rw [hξ0, map_zero] at hξ
  apply hψ0
  apply LinearMap.ext
  intro e'
  have := congrArg (fun F : E × E' →ₗ[ℂ] 𝒱 => F (0, e')) hξ
  simpa using this.symm

/-- **Dong–Li–Mason Schur–Weyl duality for finite groups holds**: for every simple VOA `W`,
finite `G ≤ Aut W` and irreducible `σ`, the multiplicity space `Hom_G(E, 𝒱)` is nonzero and an
irreducible `W^G`-module, and inequivalent `σ`'s give `W^G`-inequivalent multiplicity spaces. -/
theorem dlmSchurWeyl_holds : DLMSchurWeyl.{u} := by
  intro 𝒱 _ _ W G hW hG E _ _ _ σ hσ
  haveI := nontrivial_of_isIrreducible hσ
  refine ⟨multSpace_ne_bot hW G σ, fun P hPle hP => multSpace_irreducible hW G hσ P hPle hP, ?_⟩
  intro E' _ _ _ σ' hσ' hne T hT
  exact multSpace_inequivalent hW G hσ hσ' hne T hT

end VOA.Huang.SchurWeyl
