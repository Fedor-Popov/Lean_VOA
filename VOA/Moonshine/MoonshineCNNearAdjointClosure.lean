import VOA.Moonshine.MoonshineCNNearOppositeModes
import VOA.Moonshine.MoonshineCNNearIterate

/-! Generator closure for a NearVOA, conditional on the opposite iterate identity.
The opposite modes and all finite-support requirements are constructed here or
in the imported module. The opposite iterate identity remains an explicit input. -/

noncomputable section
namespace VOA.NearVOA

open Module (End)
open scoped BigOperators

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

theorem modeIterate_terms_finite (u v x : H) (ℓ n : ℤ) :
    (Function.support fun i : ℕ => ((-1 : ℂ) ^ i * gBinom ℓ i) •
      (V.smul u (ℓ - i) (V.smul v (n + i) x) -
        (-1 : ℂ) ^ ℓ • V.smul v (ℓ + n - i) (V.smul u i x))).Finite := by
  obtain ⟨K, hK⟩ := V.regularity u x
  obtain ⟨J, hJ⟩ := V.regularity v x
  apply (Finset.range ((max K (J - n)).toNat + 1)).finite_toSet.subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  apply hi
  change ((-1 : ℂ) ^ i * gBinom ℓ i) •
    (mode (V.Y u) (ℓ - i) (mode (V.Y v) (n + i) x) -
      (-1 : ℂ) ^ ℓ • mode (V.Y v) (ℓ + n - i) (mode (V.Y u) i x)) = 0
  rw [hK _ (by omega), hJ _ (by omega), map_zero, map_zero,
    smul_zero, sub_zero, smul_zero]

theorem oppositeIterate_terms_finite
    (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0) (u v y : H) (ℓ n : ℤ) :
    (Function.support fun i : ℕ => ((-1 : ℂ) ^ i * gBinom ℓ i) •
      (V.oppositeModes hNil (n + i) v (V.oppositeModes hNil (ℓ - i) u y) -
        (-1 : ℂ) ^ ℓ • V.oppositeModes hNil i u
          (V.oppositeModes hNil (ℓ + n - i) v y))).Finite := by
  obtain ⟨K, hK⟩ := V.oppositeModes_eventually_zero hNil u y
  obtain ⟨J, hJ⟩ := V.oppositeModes_eventually_zero hNil v y
  apply (Finset.range ((max (ℓ - K) (ℓ + n - J)).toNat + 1)).finite_toSet.subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  apply hi
  dsimp only
  rw [hK _ (by omega), hJ _ (by omega), map_zero, map_zero,
    smul_zero, sub_zero, smul_zero]

/-- States whose actual modes are adjoint to the constructed opposite modes. -/
def oppositeIntertwinedStates (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (B : LinearMap.BilinForm ℂ H) : Submodule ℂ H where
  carrier := {u | ∀ (n : ℤ) (x y : H),
    B (mode (V.Y u) n x) y = B x (V.oppositeModes hNil n u y)}
  zero_mem' := by
    intro n x y
    simp only [map_zero, mode_zero, LinearMap.zero_apply]
  add_mem' := by
    intro u v hu hv n x y
    simp only [map_add, mode_add, LinearMap.add_apply, hu n x y, hv n x y]
  smul_mem' := by
    intro c u hu n x y
    simp only [map_smul, mode_smul, LinearMap.smul_apply, hu n x y]

/-- The precise remaining opposite-field identity needed for adjoint closure. -/
def OppositeIterateIdentity (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0) : Prop :=
  ∀ (u v y : H) (ℓ n : ℤ),
    V.oppositeModes hNil n (V.smul u ℓ v) y =
      ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
        (V.oppositeModes hNil (n + i) v (V.oppositeModes hNil (ℓ - i) u y) -
          (-1 : ℂ) ^ ℓ • V.oppositeModes hNil i u
            (V.oppositeModes hNil (ℓ + n - i) v y))

/-- Intertwined states are closed under every product once opposite iteration is proved. -/
theorem mode_mem_oppositeIntertwinedStates
    (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (hIter : V.OppositeIterateIdentity hNil) (B : LinearMap.BilinForm ℂ H)
    {u v : H} (hu : u ∈ V.oppositeIntertwinedStates hNil B)
    (hv : v ∈ V.oppositeIntertwinedStates hNil B) (ℓ : ℤ) :
    V.smul u ℓ v ∈ V.oppositeIntertwinedStates hNil B := by
  intro n x y
  change B.flip y (V.smul (V.smul u ℓ v) n x) = _
  rw [V.mode_iterate, hIter u v y ℓ n]
  simp only [one_mul]
  rw [map_finsum _ (V.modeIterate_terms_finite u v x ℓ n),
    map_finsum _ (V.oppositeIterate_terms_finite hNil u v y ℓ n)]
  apply finsum_congr
  intro i
  simp only [map_smul, map_sub, LinearMap.flip_apply]
  simp only [smul_def]
  rw [hu, hv, hv, hu]

/-- A reusable generator theorem. The opposite iterate law is not hidden in the conclusion. -/
theorem adjoint_of_oppositeIterate_generators
    (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (hIter : V.OppositeIterateIdentity hNil) (B : LinearMap.BilinForm ℂ H) (G : Set H)
    (hGen : ∀ S : Submodule ℂ H, G ⊆ S →
      (∀ u ∈ S, ∀ v ∈ S, ∀ ℓ : ℤ, V.smul u ℓ v ∈ S) → S = ⊤)
    (hAdj : ∀ u ∈ G, ∀ (n : ℤ) (x y : H),
      B (mode (V.Y u) n x) y = B x (V.oppositeModes hNil n u y))
    (u : H) (n : ℤ) (x y : H) :
    B (mode (V.Y u) n x) y = B x (V.oppositeModes hNil n u y) := by
  have htop : V.oppositeIntertwinedStates hNil B = ⊤ :=
    hGen _ hAdj (fun _ hu _ hv ℓ =>
      V.mode_mem_oppositeIntertwinedStates hNil hIter B hu hv ℓ)
  have hu : u ∈ V.oppositeIntertwinedStates hNil B := by rw [htop]; trivial
  exact hu n x y

end VOA.NearVOA
