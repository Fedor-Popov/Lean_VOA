/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.SchurWeylDLMProofFinGen

/-! # O4b: twisted products span all `G`-tuples (Dedekind plus density)

Let `W` be a simple VOA and `G ≤ Aut W` finite. A linear map `ψ : ℂ^G → W` is the same as a
`G`-tuple `(ψ(δ_g))_g` of vectors. The orbit map `orbitMap b` corresponds to the tuple
`(g b)_g`.

`linearMap_mem_modeSpan_orbit`: every `ψ` lies in the single-mode span of the orbit maps,
`span{ a₍ₙ₎ ∘ orbitMap b }`. In tuple language,
`span{ (a₍ₙ₎ g(b))_g : a, b ∈ W, n ∈ ℤ } = W^G`.

This is the vertex-algebra content of the surjectivity half of McRae's Kirillov functor
(McRae arXiv:1810.00747, Prop. 3.6/4.3). The proof is the argument of `orbifold_generates`
with an arbitrary `ψ` in place of an orbit map:
- Dedekind's lemma plus Artinian `ℂ^G` give finitely many jointly injective orbit maps;
- `ψ` factors linearly through them;
- Jacobson density replaces the linear factors by mode-algebra elements;
- Li's lemma `comp_mem_modeSpan` closes the argument.

`McRaeO4bRigid.exists_delta` applies this to the tuple `(δ_{g,1} 𝟙)_g`.
-/

noncomputable section
namespace VOA.Huang.SchurWeyl
open VOA Module

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable (G : Subgroup (Aut W)) [Fintype G]

/-- **Every `G`-tuple is a combination of twisted products.** -/
theorem linearMap_mem_modeSpan_orbit (hW : W.IsSimple) (ψ : (G → ℂ) →ₗ[ℂ] 𝒱) :
    ψ ∈ VOA.Moonshine.SigmaExist.modeSpan (homModule W (G → ℂ)) (Set.range (orbitMap G)) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_iInf_ker_eq_bot G hW
  let Θ : (G → ℂ) →ₗ[ℂ] (S → 𝒱) := LinearMap.pi fun j : S => orbitMap G (j : 𝒱)
  have hΘ : LinearMap.ker Θ = ⊥ := by
    rw [eq_bot_iff, ← hS]
    intro c hc
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro w hw
    have := congrFun ((LinearMap.mem_ker).mp hc) ⟨w, hw⟩
    simpa [Θ] using this
  obtain ⟨R, hR⟩ := Θ.exists_leftInverse_of_injective hΘ
  let F : (S → 𝒱) →ₗ[ℂ] 𝒱 := ψ ∘ₗ R
  let s : S → Finset 𝒱 := fun j =>
    Finset.univ.image fun g : G => orbitMap G (j : 𝒱) (Pi.single g 1)
  choose f hf hfF using fun j : S =>
    exists_modeAlgebra_eq hW (F ∘ₗ LinearMap.single ℂ (fun _ : S => 𝒱) j) (s j)
  have hcomp : ∀ j : S, (f j).comp (orbitMap G (j : 𝒱)) =
      (F ∘ₗ LinearMap.single ℂ (fun _ : S => 𝒱) j).comp (orbitMap G (j : 𝒱)) := by
    intro j
    refine (Pi.basisFun ℂ G).ext fun g => ?_
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    exact hfF j _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))
  have hξ : ψ = ∑ j : S, (f j).comp (orbitMap G (j : 𝒱)) := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.coe_sum, Finset.sum_apply, hcomp, LinearMap.comp_apply]
    rw [← map_sum]
    have hsum : ∑ j : S, LinearMap.single ℂ (fun _ : S => 𝒱) j (orbitMap G (j : 𝒱) c) = Θ c := by
      funext i
      simp [Θ, Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    simp only [F, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply R Θ, hR, LinearMap.id_apply]
  rw [hξ]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact comp_mem_modeSpan _ (hf j) _
    (VOA.Moonshine.SigmaExist.subset_modeSpan (homModule W (G → ℂ)) _ ⟨j, rfl⟩)

end VOA.Huang.SchurWeyl
