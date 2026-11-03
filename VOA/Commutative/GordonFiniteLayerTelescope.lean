/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonKernelFlag

/-!
# Finite-dimensional telescopes from exact filtration layers

The rooted-Gordon argument constructs maps on successive kernel layers, not a single map from
the whole source into every corrected profile carrier.  This file records the precise linear
algebra needed to pass from those layer maps to the global Hilbert inequality.

For an increasing finite filtration

```text
0 = F 0 <= F 1 <= ... <= F length = V,
```

an injection from every exact layer `F (i+1) / F i` into a carrier `C i` implies

```text
finrank V <= sum_{i < length} finrank (C i).
```

No choice of complements and no artificial global evaluation map is involved.
-/

namespace VOA.GordonFiniteLayerTelescope

noncomputable section

universe u v w

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- A finite increasing filtration, indexed by all natural numbers but required to start at
zero and exhaust the ambient space at the specified finite length.  Only the terms through
`length` enter the theorem. -/
structure Filtration (K : Type u) (V : Type v) [DivisionRing K]
    [AddCommGroup V] [Module K V] where
  length : ℕ
  piece : ℕ → Submodule K V
  monotone_succ : ∀ i, piece i ≤ piece (i + 1)
  piece_zero : piece 0 = ⊥
  piece_length : piece length = ⊤

namespace Filtration

variable (F : Filtration K V)

/-- The exact layer added at step `i`. -/
abbrev layer (i : ℕ) : Type v :=
  Submodule.Layer (F.piece (i + 1)) (F.piece i) (F.monotone_succ i)

variable [FiniteDimensional K V]

/-- The ranks of the exact layers telescope to the rank of every filtration piece up to the
exhaustion length. -/
theorem finrank_piece_eq_sum_layers {r : ℕ} (hr : r ≤ F.length) :
    Module.finrank K (F.piece r) =
      ∑ i ∈ Finset.range r, Module.finrank K (F.layer i) := by
  induction r with
  | zero =>
      simp [F.piece_zero]
  | succ r ihr =>
      have hr' : r ≤ F.length := by omega
      have hstep := VOA.Submodule.Layer.finrank_layer_add_finrank
        (F.piece (r + 1)) (F.piece r) (F.monotone_succ r)
      rw [Finset.sum_range_succ, ← ihr hr']
      simpa [Nat.succ_eq_add_one, add_comm] using hstep.symm

/-- Exact finite-filtration rank identity. -/
theorem finrank_eq_sum_layers :
    Module.finrank K V =
      ∑ i ∈ Finset.range F.length, Module.finrank K (F.layer i) := by
  have h := F.finrank_piece_eq_sum_layers (r := F.length) le_rfl
  rw [F.piece_length, finrank_top] at h
  exact h

variable {C : ℕ → Type w}
variable [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
variable [∀ i, FiniteDimensional K (C i)]

/-- Layerwise injections imply the global finite-dimensional bound.  This is the form consumed
by the boundary affine kernel-flag proof. -/
theorem finrank_le_sum_carriers
    (layerMap : ∀ i, i < F.length → F.layer i →ₗ[K] C i)
    (layerMap_injective : ∀ i (hi : i < F.length), Function.Injective (layerMap i hi)) :
    Module.finrank K V ≤
      ∑ i ∈ Finset.range F.length, Module.finrank K (C i) := by
  rw [F.finrank_eq_sum_layers]
  exact Finset.sum_le_sum fun i hi => by
    let hi' := Finset.mem_range.mp hi
    exact (layerMap i hi').finrank_le_finrank_of_injective
      (layerMap_injective i hi')

end Filtration

/-! ## The finite tail-kernel filtration -/

variable {W : ℕ → Type w}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- Vectors killed by every evaluation with index in the half-open interval
`[first, length)`. -/
def tailKernel (length : ℕ) (phi : ∀ i, V →ₗ[K] W i) (first : ℕ) : Submodule K V :=
  ⨅ j : {j : ℕ // j < length ∧ first ≤ j}, LinearMap.ker (phi j.1)

/-- A tail kernel lies in the kernel of every evaluation belonging to that tail. -/
theorem tailKernel_le_ker (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    {first j : ℕ} (hjLength : j < length) (hjFirst : first ≤ j) :
    tailKernel length phi first ≤ LinearMap.ker (phi j) := by
  exact iInf_le_of_le (⟨j, hjLength, hjFirst⟩ : {j : ℕ // j < length ∧ first ≤ j}) le_rfl

/-- Forgetting the first possible kernel condition enlarges a tail kernel. -/
theorem tailKernel_mono_succ (length : ℕ) (phi : ∀ i, V →ₗ[K] W i) (first : ℕ) :
    tailKernel length phi first ≤ tailKernel length phi (first + 1) := by
  rw [tailKernel]
  refine le_iInf fun j => ?_
  exact tailKernel_le_ker length phi j.2.1 (by omega)

/-- Once the first index reaches the finite length there are no remaining kernel conditions. -/
theorem tailKernel_length (length : ℕ) (phi : ∀ i, V →ₗ[K] W i) :
    tailKernel length phi length = ⊤ := by
  apply top_unique
  rw [tailKernel]
  refine le_iInf fun j => ?_
  exfalso
  omega

/-- At an index inside the finite range, the present tail is obtained from the next tail by
imposing exactly the current kernel. -/
theorem tailKernel_eq_succ_inf_ker (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    {first : ℕ} (hfirst : first < length) :
    tailKernel length phi first =
      tailKernel length phi (first + 1) ⊓ LinearMap.ker (phi first) := by
  apply le_antisymm
  · exact le_inf (tailKernel_mono_succ length phi first)
      (tailKernel_le_ker length phi hfirst le_rfl)
  · intro x hx
    rw [tailKernel]
    refine (Submodule.mem_iInf _).mpr fun j => ?_
    by_cases hj : first = j.1
    · rw [← hj]
      exact hx.2
    · exact tailKernel_le_ker length phi j.2.1 (by omega) hx.1

/-- Evaluation at the first index, restricted to the vectors killed by every later index. -/
def tailRestrictedEvaluation (length : ℕ) (phi : ∀ i, V →ₗ[K] W i) (first : ℕ) :
    tailKernel length phi (first + 1) →ₗ[K] W first :=
  (phi first).domRestrict (tailKernel length phi (first + 1))

/-- Inside the next tail, the kernel of the current evaluation is exactly the present tail. -/
theorem ker_tailRestrictedEvaluation (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    {first : ℕ} (hfirst : first < length) :
    LinearMap.ker (tailRestrictedEvaluation length phi first) =
      (tailKernel length phi first).comap
        (tailKernel length phi (first + 1)).subtype := by
  ext x
  change phi first x.1 = 0 ↔ x.1 ∈ tailKernel length phi first
  rw [tailKernel_eq_succ_inf_ker length phi hfirst]
  simp only [Submodule.mem_inf, x.property, true_and, LinearMap.mem_ker]

/-- The exact tail-kernel layer is canonically the range of the current restricted
evaluation. -/
def tailLayerEquivRange (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (first : ℕ) (hfirst : first < length) :
    Submodule.Layer
        (tailKernel length phi (first + 1))
        (tailKernel length phi first)
        (tailKernel_mono_succ length phi first) ≃ₗ[K]
      LinearMap.range (tailRestrictedEvaluation length phi first) :=
  (Submodule.quotEquivOfEq
      ((tailKernel length phi first).comap
        (tailKernel length phi (first + 1)).subtype)
      (LinearMap.ker (tailRestrictedEvaluation length phi first))
      (ker_tailRestrictedEvaluation length phi hfirst).symm).trans
    (tailRestrictedEvaluation length phi first).quotKerEquivRange

variable (carrier : ∀ i, Submodule K (W i))

/-- If the current restricted evaluation lands in a prescribed carrier, its range maps
canonically and injectively into that carrier. -/
def tailRangeToCarrier (length : ℕ) (phi : ∀ i, V →ₗ[K] W i) (first : ℕ)
    (hcarrier : ∀ x, x ∈ tailKernel length phi (first + 1) → phi first x ∈ carrier first) :
    LinearMap.range (tailRestrictedEvaluation length phi first) →ₗ[K] carrier first where
  toFun y := ⟨y.1, by
    rcases y.2 with ⟨x, hx⟩
    rw [← hx]
    exact hcarrier x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    rfl

theorem tailRangeToCarrier_injective
    (length : ℕ) (phi : ∀ i, V →ₗ[K] W i) (first : ℕ)
    (hcarrier : ∀ x, x ∈ tailKernel length phi (first + 1) → phi first x ∈ carrier first) :
    Function.Injective (tailRangeToCarrier carrier length phi first hcarrier) := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg (fun z : carrier first => (z : W first)) hxy
  exact hval

/-- The current evaluation therefore gives an injective map from the exact tail-kernel layer
to the prescribed carrier. -/
def tailLayerToCarrier (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (first : ℕ) (hfirst : first < length)
    (hcarrier : ∀ x, x ∈ tailKernel length phi (first + 1) → phi first x ∈ carrier first) :
    Submodule.Layer
        (tailKernel length phi (first + 1))
        (tailKernel length phi first)
        (tailKernel_mono_succ length phi first) →ₗ[K]
      carrier first :=
  (tailRangeToCarrier carrier length phi first hcarrier).comp
    (tailLayerEquivRange length phi first hfirst).toLinearMap

theorem tailLayerToCarrier_injective
    (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (first : ℕ) (hfirst : first < length)
    (hcarrier : ∀ x, x ∈ tailKernel length phi (first + 1) → phi first x ∈ carrier first) :
    Function.Injective (tailLayerToCarrier carrier length phi first hfirst hcarrier) :=
  (tailRangeToCarrier_injective carrier length phi first hcarrier).comp
    (tailLayerEquivRange length phi first hfirst).injective

/-- The increasing filtration associated with a finite ordered list of evaluations.  The sole
exhaustivity hypothesis is that their joint kernel is zero. -/
def kernelFiltration (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : tailKernel length phi 0 = ⊥) : Filtration K V where
  length := length
  piece := tailKernel length phi
  monotone_succ := tailKernel_mono_succ length phi
  piece_zero := jointKernel_eq_bot
  piece_length := tailKernel_length length phi

@[simp]
theorem kernelFiltration_piece (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : tailKernel length phi 0 = ⊥) (first : ℕ) :
    (kernelFiltration length phi jointKernel_eq_bot).piece first =
      tailKernel length phi first :=
  rfl

variable [FiniteDimensional K V]
variable {C : ℕ → Type*}
variable [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
variable [∀ i, FiniteDimensional K (C i)]

/-- Tail-kernel form of the layer telescope.  This is the direct adapter for a linearly ordered
finite profile list: it only asks for maps on the successive exact kernel layers. -/
theorem finrank_le_sum_carriers_of_tailKernel_layers
    (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : tailKernel length phi 0 = ⊥)
    (layerMap : ∀ i, i < length →
      (kernelFiltration length phi jointKernel_eq_bot).layer i →ₗ[K] C i)
    (layerMap_injective : ∀ i (hi : i < length), Function.Injective (layerMap i hi)) :
    Module.finrank K V ≤
      ∑ i ∈ Finset.range length, Module.finrank K (C i) :=
  (kernelFiltration length phi jointKernel_eq_bot).finrank_le_sum_carriers
    layerMap layerMap_injective

/-- Final carrier-membership form.  If the joint kernel is zero and each evaluation sends its
later-kernel layer into the corresponding finite-dimensional carrier, then the source dimension
is bounded by the sum of the carrier dimensions.  This is exactly the abstract linear-algebra
conclusion needed after the rooted endpoint and height-one gluing arguments. -/
theorem finrank_le_sum_carriers_of_tailKernel_membership
    (length : ℕ) (phi : ∀ i, V →ₗ[K] W i)
    (carrier : ∀ i, Submodule K (W i))
    [∀ i, FiniteDimensional K (carrier i)]
    (jointKernel_eq_bot : tailKernel length phi 0 = ⊥)
    (hcarrier : ∀ i, i < length → ∀ x,
      x ∈ tailKernel length phi (i + 1) → phi i x ∈ carrier i) :
    Module.finrank K V ≤
      ∑ i ∈ Finset.range length, Module.finrank K (carrier i) := by
  exact finrank_le_sum_carriers_of_tailKernel_layers
    (C := fun i => carrier i) length phi jointKernel_eq_bot
    (fun i hi => tailLayerToCarrier carrier length phi i hi (hcarrier i hi))
    (fun i hi => tailLayerToCarrier_injective carrier length phi i hi (hcarrier i hi))

end

end VOA.GordonFiniteLayerTelescope

section AxiomAudit
namespace VOA.GordonFiniteLayerTelescope
end VOA.GordonFiniteLayerTelescope
end AxiomAudit
