import VOA.DeligneAudit.SL4TCellQuotient
import Mathlib.RingTheory.Finiteness.Finsupp

/-! Right exactness of current-mode truncation, uniformly in the truncation degree. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module ℂ U] [Module ℂ V] [Module ℂ W]
variable {EU HU FU : ℕ → Module.End ℂ U}
variable {EV HV FV : ℕ → Module.End ℂ V}
variable {EW HW FW : ℕ → Module.End ℂ W}

/-- A linear map intertwines all three families of current modes. -/
def CurrentIntertwines (E H F : ℕ → Module.End ℂ V)
    (E' H' F' : ℕ → Module.End ℂ W) (f : V →ₗ[ℂ] W) : Prop :=
  (∀ s x, f (E s x) = E' s (f x)) ∧
    (∀ s x, f (H s x) = H' s (f x)) ∧ (∀ s x, f (F s x) = F' s (f x))

/-- Invariant subspaces pull back along current intertwiners. -/
theorem currentStable_comap (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (P : Submodule ℂ W)
    (hP : CurrentStable EW HW FW P) : CurrentStable EV HV FV (P.comap f) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro s x hx
  · change f (EV s x) ∈ P
    rw [hf.1]
    exact hP.1 s hx
  · change f (HV s x) ∈ P
    rw [hf.2.1]
    exact hP.2.1 s hx
  · change f (FV s x) ∈ P
    rw [hf.2.2]
    exact hP.2.2 s hx

/-- Images of invariant subspaces remain invariant under intertwined currents. -/
theorem currentStable_map (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (P : Submodule ℂ V)
    (hP : CurrentStable EV HV FV P) : CurrentStable EW HW FW (P.map f) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro s x hx <;> obtain ⟨y, hy, rfl⟩ := hx
  · exact ⟨EV s y, hP.1 s hy, hf.1 s y⟩
  · exact ⟨HV s y, hP.2.1 s hy, hf.2.1 s y⟩
  · exact ⟨FV s y, hP.2.2 s hy, hf.2.2 s y⟩

/-- Taking the current-generated span commutes with equivariant linear images. -/
theorem currentSpan_map (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (S : Set V) :
    (currentSpan EV HV FV S).map f = currentSpan EW HW FW (f '' S) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply currentSpan_le
    · intro x hx
      exact subset_currentSpan _ ⟨x, hx, rfl⟩
    · exact currentStable_comap f hf _ (currentSpan_stable _)
  · apply currentSpan_le
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨y, subset_currentSpan S hy, rfl⟩
    · exact currentStable_map f hf _ (currentSpan_stable S)

/-- Images of all modes at or above the truncation degree. -/
def currentTailImages (E H F : ℕ → Module.End ℂ V) (M : ℕ) : Set V :=
  {x | ∃ s, M ≤ s ∧ ∃ y, E s y = x ∨ H s y = x ∨ F s y = x}

/-- The invariant relation submodule imposing the current-mode cutoff. -/
def currentTruncationSubmodule (E H F : ℕ → Module.End ℂ V) (M : ℕ) : Submodule ℂ V :=
  currentSpan E H F (currentTailImages E H F M)

/-- Every intertwiner respects the truncation relation submodules. -/
theorem currentTruncationSubmodule_map_le (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (M : ℕ) :
    (currentTruncationSubmodule EV HV FV M).map f ≤
      currentTruncationSubmodule EW HW FW M := by
  rw [currentTruncationSubmodule, currentSpan_map f hf]
  apply currentSpan_mono
  rintro x ⟨z, ⟨s, hs, y, hy⟩, rfl⟩
  refine ⟨s, hs, f y, ?_⟩
  rcases hy with hy | hy | hy
  · exact Or.inl (by rw [← hf.1, hy])
  · exact Or.inr (Or.inl (by rw [← hf.2.1, hy]))
  · exact Or.inr (Or.inr (by rw [← hf.2.2, hy]))

/-- A surjective intertwiner maps truncation relations onto truncation relations. -/
theorem currentTruncationSubmodule_map (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (hsur : Function.Surjective f) (M : ℕ) :
    (currentTruncationSubmodule EV HV FV M).map f =
      currentTruncationSubmodule EW HW FW M := by
  apply le_antisymm (currentTruncationSubmodule_map_le f hf M)
  apply currentSpan_le
  · rintro x ⟨s, hs, y, hy⟩
    obtain ⟨z, rfl⟩ := hsur y
    rcases hy with hy | hy | hy
    · exact ⟨EV s z, subset_currentSpan _ ⟨s, hs, z, Or.inl rfl⟩,
        (hf.1 s z).trans hy⟩
    · exact ⟨HV s z, subset_currentSpan _ ⟨s, hs, z, Or.inr (Or.inl rfl)⟩,
        (hf.2.1 s z).trans hy⟩
    · exact ⟨FV s z, subset_currentSpan _ ⟨s, hs, z, Or.inr (Or.inr rfl)⟩,
        (hf.2.2 s z).trans hy⟩
  · exact currentStable_map f hf _ (currentSpan_stable _)

/-- The induced map on modules with a fixed current-mode cutoff. -/
def currentTruncationMap (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (M : ℕ) :
    (V ⧸ currentTruncationSubmodule EV HV FV M) →ₗ[ℂ]
      W ⧸ currentTruncationSubmodule EW HW FW M :=
  (currentTruncationSubmodule EV HV FV M).mapQ
    (currentTruncationSubmodule EW HW FW M) f
    (Submodule.map_le_iff_le_comap.mp (currentTruncationSubmodule_map_le f hf M))

/-- Truncating a surjective current map preserves surjectivity. -/
theorem currentTruncationMap_surjective (f : V →ₗ[ℂ] W)
    (hf : CurrentIntertwines EV HV FV EW HW FW f) (hsur : Function.Surjective f) (M : ℕ) :
    Function.Surjective (currentTruncationMap f hf M) := by
  intro x
  obtain ⟨y, rfl⟩ := (currentTruncationSubmodule EW HW FW M).mkQ_surjective x
  obtain ⟨z, rfl⟩ := hsur y
  exact ⟨(currentTruncationSubmodule EV HV FV M).mkQ z, rfl⟩

/-- Current-mode truncation preserves exactness at the middle of a right exact sequence. -/
theorem currentTruncationMap_range_eq_ker (g : U →ₗ[ℂ] V) (f : V →ₗ[ℂ] W)
    (hg : CurrentIntertwines EU HU FU EV HV FV g)
    (hf : CurrentIntertwines EV HV FV EW HW FW f)
    (hex : LinearMap.range g = LinearMap.ker f) (hsur : Function.Surjective f) (M : ℕ) :
    LinearMap.range (currentTruncationMap g hg M) =
      LinearMap.ker (currentTruncationMap f hf M) := by
  rw [currentTruncationMap, currentTruncationMap, Submodule.range_mapQ,
    Submodule.ker_mapQ, ← currentTruncationSubmodule_map f hf hsur M,
    Submodule.comap_map_eq, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, hex]

/-- A right exact sequence bounds the truncated middle dimension by its two outer dimensions. -/
theorem currentTruncation_finrank_le (g : U →ₗ[ℂ] V) (f : V →ₗ[ℂ] W)
    (hg : CurrentIntertwines EU HU FU EV HV FV g)
    (hf : CurrentIntertwines EV HV FV EW HW FW f)
    (hex : LinearMap.range g = LinearMap.ker f) (hsur : Function.Surjective f) (M : ℕ)
    [FiniteDimensional ℂ (U ⧸ currentTruncationSubmodule EU HU FU M)]
    [FiniteDimensional ℂ (W ⧸ currentTruncationSubmodule EW HW FW M)] :
    FiniteDimensional ℂ (V ⧸ currentTruncationSubmodule EV HV FV M) ∧
      Module.finrank ℂ (V ⧸ currentTruncationSubmodule EV HV FV M) ≤
        Module.finrank ℂ (U ⧸ currentTruncationSubmodule EU HU FU M) +
          Module.finrank ℂ (W ⧸ currentTruncationSubmodule EW HW FW M) := by
  let g' := currentTruncationMap g hg M
  let f' := currentTruncationMap f hf M
  have he : LinearMap.ker f' = LinearMap.range g' :=
    (currentTruncationMap_range_eq_ker g f hg hf hex hsur M).symm
  have hs : Function.Surjective f' := currentTruncationMap_surjective f hf hsur M
  haveI : FiniteDimensional ℂ (V ⧸ currentTruncationSubmodule EV HV FV M) :=
    Module.Finite.of_exact (LinearMap.exact_iff.mpr he) hs
  refine ⟨inferInstance, ?_⟩
  have hd := f'.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, he] at hd
  have hb := g'.finrank_range_le
  omega

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.currentStable_comap
#print axioms VOA.DeligneAudit.SL4T.currentStable_map
#print axioms VOA.DeligneAudit.SL4T.currentSpan_map
#print axioms VOA.DeligneAudit.SL4T.currentTruncationSubmodule_map_le
#print axioms VOA.DeligneAudit.SL4T.currentTruncationSubmodule_map
#print axioms VOA.DeligneAudit.SL4T.currentTruncationMap_surjective
#print axioms VOA.DeligneAudit.SL4T.currentTruncationMap_range_eq_ker
#print axioms VOA.DeligneAudit.SL4T.currentTruncation_finrank_le
