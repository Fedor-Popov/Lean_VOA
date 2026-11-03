/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.SchurWeylDLMProof
import VOA.Modules.ModuleRestrict
import VOA.Modules.LogTensorTargets
import VOA.Classification.COne.LatticeSimple

/-!
# A simple VOA is a finitely generated module over a finite orbifold

For a simple VOA `W` and a finite `G ≤ Aut W`, `𝒱` is generated, as a `W^G`-module, by finitely
many vectors (`orbifold_generates`), hence `(orbifold G).adjointRestrict` is a finitely generated
weak `orbifoldVOA G`-module (`orbifold_finGen`); in particular for every finite
`G ≤ Aut (V2m 1 le_rfl)` (`V2m_orbifold_finGen`), the finite-generation field needed to place
`V₂` in `LogModuleCat (orbifoldVOA G)`.

Proof (no enumeration of `Irr G` is needed).  For `v ∈ 𝒱` let `orbitMap v : ℂ^G → 𝒱`,
`c ↦ Σ_g c_g g v`, a `G`-map out of the regular representation `regRep G`.
1. (`exists_finset_iInf_ker_eq_bot`) Dedekind's lemma (`aut_sum_eq_zero_imp`) says
   `⋂_v ker (orbitMap v) = 0`; `ℂ^G` is Artinian, so finitely many `v_j` already give `0`.
2. (`orbifold_generates`) For any `v`, `c ↦ (orbitMap v_j c)_j` is injective, so
   `orbitMap v = Σ_j F_j ∘ orbitMap v_j` for linear `F_j`; density replaces each `F_j` by an element
   `f_j` of the mode algebra; Li's lemma plus averaging (`mem_invSpan_of_modeSpan`) put
   `orbitMap v` in the span of `u₍ₙ₎ ∘ orbitMap v_j`, `u ∈ W^G`; evaluate at `δ₁`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.SchurWeyl

open VOA Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

variable (G : Subgroup (Aut W))

/-- The left regular representation of `G` on `ℂ^G`: `(h · c)(g) = c(h⁻¹ g)`. -/
def regRep : Representation ℂ G (G → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ (fun g => h⁻¹ * g)
  map_one' := LinearMap.ext fun c => funext fun g => by simp [LinearMap.funLeft_apply]
  map_mul' a b := LinearMap.ext fun c => funext fun g => by
    simp [LinearMap.funLeft_apply, mul_inv_rev, mul_assoc]

theorem regRep_apply (h : G) (c : G → ℂ) (g : G) : regRep G h c g = c (h⁻¹ * g) := rfl

variable [Fintype G]

/-- The orbit map `c ↦ Σ_g c_g · g v`. -/
def orbitMap (v : 𝒱) : (G → ℂ) →ₗ[ℂ] 𝒱 :=
  ∑ g : G, (LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ).smulRight ((g : Aut W) v)

theorem orbitMap_apply (v : 𝒱) (c : G → ℂ) : orbitMap G v c = ∑ g : G, c g • (g : Aut W) v := by
  simp [orbitMap, LinearMap.coe_sum, Finset.sum_apply]

theorem orbitMap_single [DecidableEq G] (v : 𝒱) : orbitMap G v (Pi.single 1 1) = v := by
  classical
  rw [orbitMap_apply, Finset.sum_eq_single (1 : G)]
  · simp
  · intro g _ hg
    rw [Pi.single_eq_of_ne hg, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem orbitMap_mem_multSpace (v : 𝒱) : orbitMap G v ∈ multSpace G (regRep G) := by
  intro h c
  rw [orbitMap_apply, orbitMap_apply, ← Aut.coe_toLinearEquiv, map_sum]
  simp only [map_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  simp [regRep_apply, Subgroup.coe_mul, Aut.mul_apply]

/-- Finitely many orbit maps are jointly injective (Dedekind's lemma + Artinian `ℂ^G`). -/
theorem exists_finset_iInf_ker_eq_bot (hW : W.IsSimple) :
    ∃ S : Finset 𝒱, (⨅ v ∈ S, LinearMap.ker (orbitMap G v)) = ⊥ := by
  classical
  have hwf : WellFounded ((· < ·) : Submodule ℂ (G → ℂ) → Submodule ℂ (G → ℂ) → Prop) :=
    wellFounded_lt
  obtain ⟨K, ⟨S, rfl⟩, hmin⟩ := hwf.has_min
    (Set.range fun S : Finset 𝒱 => ⨅ v ∈ S, LinearMap.ker (orbitMap G v)) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨S, ?_⟩
  rw [eq_bot_iff]
  intro c hc
  have hall : ∀ v, orbitMap G v c = 0 := by
    intro v
    have hle : (⨅ w ∈ insert v S, LinearMap.ker (orbitMap G w)) ≤
        ⨅ w ∈ S, LinearMap.ker (orbitMap G w) :=
      biInf_mono (fun w hw => Finset.mem_insert_of_mem hw)
    have heq : (⨅ w ∈ insert v S, LinearMap.ker (orbitMap G w)) =
        ⨅ w ∈ S, LinearMap.ker (orbitMap G w) := by
      by_contra hne
      exact hmin _ ⟨insert v S, rfl⟩ (lt_of_le_of_ne hle hne)
    have hc' : c ∈ ⨅ w ∈ insert v S, LinearMap.ker (orbitMap G w) := heq ▸ hc
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hc'
    exact hc' v (Finset.mem_insert_self v S)
  rw [Submodule.mem_bot]
  funext g
  exact aut_sum_eq_zero_imp hW G Finset.univ c
    (fun v => by rw [← orbitMap_apply]; exact hall v) g (Finset.mem_univ g)

omit [Fintype G] in
/-- **`𝒱` is a finitely generated `W^G`-module**: there is a finite set `S` such that every
`W^G`-mode-stable subspace containing `S` is everything. -/
theorem orbifold_generates [Finite G] (hW : W.IsSimple) :
    ∃ S : Finset 𝒱, ∀ P : Submodule ℂ 𝒱, (↑S : Set 𝒱) ⊆ P →
      (∀ u ∈ (orbifold G).carrier, ∀ (n : ℤ), ∀ x ∈ P, W.smul u n x ∈ P) → P = ⊤ := by
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_finset_iInf_ker_eq_bot G hW
  refine ⟨S, fun P hSP hP => ?_⟩
  rw [eq_top_iff]
  intro v _
  -- the joint orbit map is injective
  let Θ : (G → ℂ) →ₗ[ℂ] (S → 𝒱) := LinearMap.pi fun j : S => orbitMap G (j : 𝒱)
  have hΘ : LinearMap.ker Θ = ⊥ := by
    rw [eq_bot_iff, ← hS]
    intro c hc
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro w hw
    have := congrFun ((LinearMap.mem_ker).mp hc) ⟨w, hw⟩
    simpa [Θ] using this
  obtain ⟨R, hR⟩ := Θ.exists_leftInverse_of_injective hΘ
  let F : (S → 𝒱) →ₗ[ℂ] 𝒱 := orbitMap G v ∘ₗ R
  let s : S → Finset 𝒱 := fun j => Finset.univ.image fun g : G => orbitMap G (j : 𝒱) (Pi.single g 1)
  choose f hf hfF using fun j : S =>
    exists_modeAlgebra_eq hW (F ∘ₗ LinearMap.single ℂ (fun _ : S => 𝒱) j) (s j)
  have hcomp : ∀ j : S, (f j).comp (orbitMap G (j : 𝒱)) =
      (F ∘ₗ LinearMap.single ℂ (fun _ : S => 𝒱) j).comp (orbitMap G (j : 𝒱)) := by
    intro j
    refine (Pi.basisFun ℂ G).ext fun g => ?_
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    exact hfF j _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))
  let U : Set ((G → ℂ) →ₗ[ℂ] 𝒱) := (fun w => orbitMap G w) '' (↑S : Set 𝒱)
  have hU : U ⊆ multSpace G (regRep G) := by
    rintro _ ⟨w, _, rfl⟩
    exact orbitMap_mem_multSpace G w
  have hξ : orbitMap G v = ∑ j : S, (f j).comp (orbitMap G (j : 𝒱)) := by
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
  have hmode : orbitMap G v ∈ VOA.Moonshine.SigmaExist.modeSpan (homModule W (G → ℂ)) U := by
    rw [hξ]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact comp_mem_modeSpan U (hf j) _
      (VOA.Moonshine.SigmaExist.subset_modeSpan (homModule W (G → ℂ)) U ⟨j, j.2, rfl⟩)
  have hinv := mem_invSpan_of_modeSpan G (regRep G) hU hmode (orbitMap_mem_multSpace G v)
  have hle : invSpan G U ≤ P.comap (LinearMap.applyₗ (R := ℂ) (Pi.single (1 : G) (1 : ℂ))) := by
    rw [invSpan, Submodule.span_le]
    rintro _ ⟨u, hu, n, _, ⟨w, hw, rfl⟩, rfl⟩
    change W.smul u n (orbitMap G w (Pi.single 1 1)) ∈ P
    rw [orbitMap_single]
    exact hP u hu n w (hSP hw)
  have := hle hinv
  simpa [orbitMap_single] using this

omit [Fintype G] in
/-- **`𝒱` is a finitely generated weak `W^G`-module** (restriction of the adjoint module). -/
theorem orbifold_finGen (hW : W.IsSimple) [Finite G] :
    VOA.LogTensor.FinGen (orbifold G).adjointRestrict := by
  obtain ⟨S, hS⟩ := orbifold_generates G hW
  exact ⟨↑S, S.finite_toSet, fun P hSP hP => hS P hSP (fun u hu n x hx => hP ⟨u, hu⟩ n x hx)⟩

/-- **The c = 1 instance**: for every finite `G ≤ Aut V₂`, `V₂` is a finitely generated weak
`V₂^G`-module. -/
theorem V2m_orbifold_finGen
    (G : Subgroup (Aut (VOA.Classification.COne.V2m 1 le_rfl))) [Finite G] :
    VOA.LogTensor.FinGen (orbifold G).adjointRestrict :=
  orbifold_finGen G (VOA.Classification.COne.V2m_isSimple 1 le_rfl)

end VOA.Huang.SchurWeyl
