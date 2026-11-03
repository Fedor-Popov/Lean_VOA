import VOA.Examples.LeeYangShortcutRelative
import VOA.Examples.LeeYangShortcutFiltration

/-!
# Generator tests for the actual relative Virasoro class filtration

The Kähler geometry need not yet carry a vertex-algebra-compatible filtration.
The sufficient class-level tests are therefore stated explicitly: the vacuum
class has degree zero, and each Virasoro creation operation raises filtered
degree by at most one. These tests imply every PBW-prefix inclusion by an
induction on creation words. No filtered isomorphism is an input.
-/

namespace VOA.LeeYangShortcut

open VirModule VirGoodFil LeeYang LeeYangTransferAssembly
open GradedUnitaryCohomology

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

/-- The actual universal vacuum as a weight-zero vector. -/
def universalVacuum : UniversalWeight 0 :=
  ⟨vacVec leeYangC, vacVec_mem_gradingVir_zero leeYangC⟩

/-- A creation mode regarded as a map between its actual universal weights. -/
def universalCreation (n : ℤ) (i : ℕ) :
    UniversalWeight n →ₗ[ℂ] UniversalWeight (n + i + 2) :=
  ((Lop leeYangC (-(i : ℤ) - 2)).comp (UniversalWeight n).subtype).codRestrict _
    (fun x => by
      simpa only [add_assoc] using Lop_neg_maps_grading leeYangC i x.2)

/-- The vacuum and creation tests imply all prefixes for a family of
subspaces of the actual universal weight spaces. -/
theorem universalPrefix_le_of_generators
    (F : ∀ n : ℤ, ℕ → Submodule ℂ (UniversalWeight n))
    (hmono : ∀ n, Monotone (F n))
    (hvac : universalVacuum ∈ F 0 0)
    (hcreation : ∀ (n : ℤ) (p i : ℕ) (x : UniversalWeight n),
      x ∈ F n p → universalCreation n i x ∈ F (n + i + 2) (p + 1))
    (p : ℕ) (n : ℤ) : universalPrefix p n ≤ F n p := by
  let F' := fun p n => (F n p).map (UniversalWeight n).subtype
  have hm : ∀ n, Monotone fun p => F' p n :=
    fun n _ _ h => Submodule.map_mono (hmono n h)
  have hv : (LinearMap.id : VirUniv leeYangC →ₗ[ℂ] VirUniv leeYangC)
      (vacVec leeYangC) ∈ F' 0 0 :=
    Submodule.mem_map.mpr ⟨universalVacuum, hvac, rfl⟩
  have hs : ∀ (p : ℕ) (n : ℤ) (i : ℕ) (x : VirUniv leeYangC),
      x ∈ F' p n → Lop leeYangC (-(i : ℤ) - 2) x ∈ F' (p + 1) (n + i + 2) := by
    intro p n i x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨universalCreation n i y, hcreation n p i y hy, rfl⟩
  have h := virFil_map_le_of_creation LinearMap.id F' hm hv hs p n
  intro x hx
  have hx' : (x : VirUniv leeYangC) ∈ F' p n :=
    h (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx'
  have he : y = x := Subtype.ext hxy
  exact he ▸ hy

/-- The concrete target cohomology prefix, with positivity chosen at every
weight so that creation operations can be compared across weights. -/
def generatorCohomPrefix (S : ConcreteKahlerGeometry)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (n : ℤ) (p : ℕ) :=
  (S.model n (hp n)).cohomFilt
    (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)

theorem generatorCohomPrefix_mono (S : ConcreteKahlerGeometry)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (n : ℤ) :
    Monotone (generatorCohomPrefix S hp n) := by
  intro p q hpq
  apply Submodule.map_mono
  apply Submodule.comap_mono
  apply KahlerComplex.degOn_mono
  intro a ha
  refine ⟨?_, ha.2⟩
  have h := Finset.mem_Icc.mp ha.1
  apply Finset.mem_Icc.mpr
  exact ⟨h.1, le_trans h.2 (by exact_mod_cast Nat.mul_le_mul_left 2 hpq)⟩

/-- Pull the actual cohomology filtration back to universal weight spaces. -/
def generatorPullback (S : ConcreteKahlerGeometry)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (n : ℤ) (p : ℕ) :
    Submodule ℂ (UniversalWeight n) :=
  (generatorCohomPrefix S hp n p).comap (modelUniversalClass S n (hp n))

/-- OPEN: a minimal class-level generator interface. The creation field is
the concrete missing compatibility with Kähler filtration; it follows from
a compatible VOA filtration and conformal degree one when those structures
are connected to the relative complex. -/
structure ClassGeneratorFiltration (S : ConcreteKahlerGeometry)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) : Prop where
  vacuum : universalVacuum ∈ generatorPullback S hp 0 0
  creation : ∀ (n : ℤ) (p i : ℕ) (x : UniversalWeight n),
    x ∈ generatorPullback S hp n p →
      universalCreation n i x ∈ generatorPullback S hp (n + i + 2) (p + 1)

/-- The two generator tests imply the full concrete filtered class-map
inclusion needed by the Virasoro-image dimension squeeze. -/
theorem modelUniversalClass_filtered_of_generators (S : ConcreteKahlerGeometry)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤)
    (hgen : ClassGeneratorFiltration S hp) (p : ℕ) (n : ℤ) :
    (universalPrefix p n).map (modelUniversalClass S n (hp n)) ≤
      generatorCohomPrefix S hp n p := by
  rw [Submodule.map_le_iff_le_comap]
  apply universalPrefix_le_of_generators (generatorPullback S hp)
  · intro n p q hpq
    exact Submodule.comap_mono (generatorCohomPrefix_mono S hp n hpq)
  · exact hgen.vacuum
  · exact hgen.creation

end
end VOA.LeeYangShortcut
