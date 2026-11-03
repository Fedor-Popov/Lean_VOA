import VOA.Huang.DLNSmallThreeBase

/-!
# The layer reduction for the homology-free Schur condition

Let `ρ : G ↠ Ḡ` be surjective with `Ḡ` Schur-trivial, and let `π : E ↠ G` be a central
extension. Put `M = π⁻¹(ker ρ)`. Then `[E,E] ∩ ker π ⊆ ⁅E, M⁆`. Hence `G` is Schur-trivial as
soon as the *layer condition* `⁅E, M⁆ ∩ ker π = 1` holds in every central extension.
Conversely the layer condition follows from Schur triviality of `G`, so it is a true
narrowing of the original statement, not a weakening.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

/-- The layer condition for `ρ : G → Ḡ`: in every central extension `π : E ↠ G`, the
subgroup `⁅E, π⁻¹(ker ρ)⁆` meets `ker π` trivially. -/
def LayerTrivial {G Gb : Type} [Group G] [Group Gb] (ρ : G →* Gb) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ x ∈ ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆, π x = 1 → x = 1

/-- If the quotient `Ḡ` is Schur-trivial, every derived kernel element lies in the layer
commutator `⁅E, π⁻¹(ker ρ)⁆`. -/
theorem mem_layer_commutator_of_schurTrivial_quotient {G Gb E : Type} [Group G] [Group Gb]
    [Group E] (ρ : G →* Gb) (hρ : Function.Surjective ρ) (hGb : SchurTrivial Gb)
    (π : E →* G) (hs : Function.Surjective π)
    (x : E) (hx : x ∈ commutator E) (hρx : ρ (π x) = 1) :
    x ∈ ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆ := by
  set M : Subgroup E := ρ.ker.comap π with hM
  set K : Subgroup E := ⁅(⊤ : Subgroup E), M⁆ with hK
  haveI : M.Normal := by rw [hM]; infer_instance
  haveI : K.Normal := by rw [hK]; exact Subgroup.commutator_normal ⊤ M
  have hKle : K ≤ (ρ.comp π).ker := by
    rw [hK, Subgroup.commutator_le]
    intro e _ m hm
    have hm' : ρ (π m) = 1 := hm
    simp [MonoidHom.mem_ker, map_commutatorElement, hm']
  let ψ : E ⧸ K →* Gb := QuotientGroup.lift K (ρ.comp π) hKle
  have hψs : Function.Surjective ψ := by
    intro g
    obtain ⟨h, rfl⟩ := hρ g
    obtain ⟨e, rfl⟩ := hs h
    exact ⟨QuotientGroup.mk e, rfl⟩
  have hψc : ψ.ker ≤ Subgroup.center (E ⧸ K) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective K y
    have he : e ∈ M := hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective K w
    have hcomm : ⁅d, e⁆ ∈ K := Subgroup.commutator_mem_commutator (Subgroup.mem_top d) he
    have h1 : (QuotientGroup.mk' K) ⁅d, e⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hcrit := (schurTrivial_iff_centralDerivedInjective Gb).mp hGb
  have hmk : (QuotientGroup.mk' K) x ∈ commutator (E ⧸ K) := by
    have hmap : (commutator E).map (QuotientGroup.mk' K) ≤ commutator (E ⧸ K) := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap ⟨x, hx, rfl⟩
  have h1 := hcrit (E ⧸ K) ψ hψs hψc _ hmk hρx
  exact (QuotientGroup.eq_one_iff x).mp h1

/-- **Layer reduction.** A Schur-trivial quotient plus the layer condition give Schur
triviality. -/
theorem schurTrivial_of_layerTrivial {G Gb : Type} [Group G] [Group Gb] (ρ : G →* Gb)
    (hρ : Function.Surjective ρ) (hGb : SchurTrivial Gb) (hL : LayerTrivial ρ) :
    SchurTrivial G := by
  apply (schurTrivial_iff_centralDerivedInjective G).mpr
  intro E _ π hs hc x hx hπx
  exact hL E π hs hc x
    (mem_layer_commutator_of_schurTrivial_quotient ρ hρ hGb π hs x hx (by simp [hπx])) hπx

/-- The layer condition is implied by Schur triviality of the source. -/
theorem layerTrivial_of_schurTrivial {G Gb : Type} [Group G] [Group Gb] (ρ : G →* Gb)
    (hG : SchurTrivial G) : LayerTrivial ρ := by
  intro E _ π hs hc x hx hπx
  have hcrit := (schurTrivial_iff_centralDerivedInjective G).mp hG
  apply hcrit E π hs hc x _ hπx
  have : ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆ ≤ commutator E := by
    rw [commutator_def]; exact Subgroup.commutator_mono le_rfl le_top
  exact this hx

end VOA.Huang.DLNSchur
