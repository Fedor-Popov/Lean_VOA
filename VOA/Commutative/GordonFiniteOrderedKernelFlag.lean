/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Finset.Sort
import VOA.Commutative.GordonFiniteLayerTelescope

/-!
# Finite ordered kernel flags with dependent targets

This file puts the abstract finite-layer telescope in the form used by the rooted-Gordon proof.
The profile set is a finite linear order and the raw profile evaluations may have dependent
codomains.  For a profile `i`, only vectors killed by every later profile are required to land in
the corrected carrier at `i`.

The conclusion is the global finrank inequality.  In particular, no map from the whole source to
the product of corrected carriers is assumed or constructed.
-/

namespace VOA.GordonFiniteOrderedKernelFlag

open VOA.GordonFiniteLayerTelescope

noncomputable section

universe u v w

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {I : Type*} [Fintype I] [LinearOrder I]
variable {W : I → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- Increasing enumeration of a finite linear order. -/
def profileOrderIso : Fin (Fintype.card I) ≃o I :=
  Fintype.orderIsoFinOfCardEq I rfl

/-- Intersection of all profile kernels whose increasing enumeration index is at least `first`.
The definition also makes sense at `first = card I`, where it is the whole source. -/
def orderedTailKernel (phi : ∀ i, V →ₗ[K] W i) (first : ℕ) : Submodule K V :=
  ⨅ j : {j : Fin (Fintype.card I) // first ≤ j.1},
    LinearMap.ker (phi (profileOrderIso j.1))

/-- The ordered tail lies in every kernel indexed by that tail. -/
theorem orderedTailKernel_le_ker (phi : ∀ i, V →ₗ[K] W i)
    {first : ℕ} (j : Fin (Fintype.card I)) (hj : first ≤ j.1) :
    orderedTailKernel phi first ≤ LinearMap.ker (phi (profileOrderIso j)) := by
  exact iInf_le_of_le (⟨j, hj⟩ : {j : Fin (Fintype.card I) // first ≤ j.1}) le_rfl

/-- Forgetting the first possible profile kernel enlarges the ordered tail. -/
theorem orderedTailKernel_mono_succ (phi : ∀ i, V →ₗ[K] W i) (first : ℕ) :
    orderedTailKernel phi first ≤ orderedTailKernel phi (first + 1) := by
  rw [orderedTailKernel]
  refine le_iInf fun j => ?_
  exact orderedTailKernel_le_ker phi j.1 (by omega)

/-- The tail after the final profile is the whole source. -/
theorem orderedTailKernel_card (phi : ∀ i, V →ₗ[K] W i) :
    orderedTailKernel phi (Fintype.card I) = ⊤ := by
  apply top_unique
  rw [orderedTailKernel]
  refine le_iInf fun j => ?_
  exfalso
  exact (Nat.not_lt_of_ge j.2) j.1.2

/-- At index zero, the ordered tail is the simultaneous kernel of every profile evaluation. -/
theorem orderedTailKernel_zero (phi : ∀ i, V →ₗ[K] W i) :
    orderedTailKernel phi 0 = ⨅ i, LinearMap.ker (phi i) := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    let j : Fin (Fintype.card I) := (profileOrderIso (I := I)).symm i
    have h := orderedTailKernel_le_ker phi j (Nat.zero_le _)
    have hji : profileOrderIso j = i := by
      exact (profileOrderIso (I := I)).apply_symm_apply i
    rw [hji] at h
    exact h
  · rw [orderedTailKernel]
    refine le_iInf fun j => ?_
    exact iInf_le _ (profileOrderIso j.1)

/-- Removing the profile at enumeration index `j` leaves exactly the intrinsic later kernel of
that profile. -/
theorem orderedTailKernel_succ_eq_laterKernel
    (phi : ∀ i, V →ₗ[K] W i) (j : Fin (Fintype.card I)) :
    orderedTailKernel phi (j.1 + 1) =
      VOA.GordonKernelFlag.laterKernel phi (profileOrderIso j) := by
  apply le_antisymm
  · rw [VOA.GordonKernelFlag.laterKernel]
    refine le_iInf fun k => ?_
    let l : Fin (Fintype.card I) := (profileOrderIso (I := I)).symm k.1
    have hjl : j.1 + 1 ≤ l.1 := by
      have hlt : j < l := by
        apply (profileOrderIso (I := I)).lt_iff_lt.mp
        simpa only [l, (profileOrderIso (I := I)).apply_symm_apply k.1] using k.2
      omega
    have h := orderedTailKernel_le_ker phi l hjl
    have hlk : profileOrderIso l = k.1 := by
      exact (profileOrderIso (I := I)).apply_symm_apply k.1
    rw [hlk] at h
    exact h
  · rw [orderedTailKernel]
    refine le_iInf fun l => ?_
    have hjl : j < l.1 := by omega
    exact VOA.GordonKernelFlag.laterKernel_le_ker phi
      ((profileOrderIso (I := I)).lt_iff_lt.mpr hjl)

/-- The tail beginning at `j` is the intrinsic current kernel at that profile. -/
theorem orderedTailKernel_eq_currentKernel
    (phi : ∀ i, V →ₗ[K] W i) (j : Fin (Fintype.card I)) :
    orderedTailKernel phi j.1 =
      VOA.GordonKernelFlag.currentKernel phi (profileOrderIso j) := by
  rw [VOA.GordonKernelFlag.currentKernel,
    ← orderedTailKernel_succ_eq_laterKernel phi j]
  apply le_antisymm
  · exact le_inf (orderedTailKernel_mono_succ phi j.1)
      (orderedTailKernel_le_ker phi j le_rfl)
  · intro x hx
    rw [orderedTailKernel]
    refine (Submodule.mem_iInf _).mpr fun l => ?_
    by_cases hjl : j = l.1
    · rw [← hjl]
      exact hx.2
    · exact orderedTailKernel_le_ker phi l.1 (by omega) hx.1

/-- The increasing finite filtration attached to a jointly separating ordered profile family. -/
def filtration (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : (⨅ i, LinearMap.ker (phi i)) = ⊥) :
    GordonFiniteLayerTelescope.Filtration K V where
  length := Fintype.card I
  piece := orderedTailKernel phi
  monotone_succ := orderedTailKernel_mono_succ phi
  piece_zero := (orderedTailKernel_zero phi).trans jointKernel_eq_bot
  piece_length := orderedTailKernel_card phi

/-- The enumerated filtration layer and the intrinsic kernel-flag layer of the corresponding
profile have equal rank.  Stating the bridge numerically avoids transporting quotient types
across proof-dependent submodule equalities. -/
theorem filtrationLayer_finrank_eq_kernelLayer
    (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : (⨅ i, LinearMap.ker (phi i)) = ⊥)
    [FiniteDimensional K V]
    (j : Fin (Fintype.card I)) :
    Module.finrank K ((filtration phi jointKernel_eq_bot).layer j.1) =
      Module.finrank K (Submodule.Layer
        (VOA.GordonKernelFlag.laterKernel phi (profileOrderIso j))
        (VOA.GordonKernelFlag.currentKernel phi (profileOrderIso j))
        (VOA.GordonKernelFlag.currentKernel_le_laterKernel
          phi (profileOrderIso j))) := by
  have hFiltration := VOA.Submodule.Layer.finrank_layer_add_finrank
    ((filtration phi jointKernel_eq_bot).piece (j.1 + 1))
    ((filtration phi jointKernel_eq_bot).piece j.1)
    ((filtration phi jointKernel_eq_bot).monotone_succ j.1)
  have hKernel := VOA.Submodule.Layer.finrank_layer_add_finrank
    (VOA.GordonKernelFlag.laterKernel phi (profileOrderIso j))
    (VOA.GordonKernelFlag.currentKernel phi (profileOrderIso j))
    (VOA.GordonKernelFlag.currentKernel_le_laterKernel phi (profileOrderIso j))
  have hLater := congrArg (fun S : Submodule K V => Module.finrank K S)
    (orderedTailKernel_succ_eq_laterKernel phi j)
  have hCurrent := congrArg (fun S : Submodule K V => Module.finrank K S)
    (orderedTailKernel_eq_currentKernel phi j)
  change Module.finrank K (orderedTailKernel phi (j.1 + 1)) =
      Module.finrank K (VOA.GordonKernelFlag.laterKernel phi (profileOrderIso j)) at hLater
  change Module.finrank K (orderedTailKernel phi j.1) =
      Module.finrank K (VOA.GordonKernelFlag.currentKernel phi (profileOrderIso j)) at hCurrent
  change Module.finrank K ((filtration phi jointKernel_eq_bot).layer j.1) +
      Module.finrank K (orderedTailKernel phi j.1) =
        Module.finrank K (orderedTailKernel phi (j.1 + 1)) at hFiltration
  omega

/-- Exact telescoping into the images of the actual restricted evaluations. -/
theorem finrank_eq_sum_restrictedRanges
    (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : (⨅ i, LinearMap.ker (phi i)) = ⊥)
    [FiniteDimensional K V] :
    Module.finrank K V = ∑ i, Module.finrank K
      (VOA.GordonKernelFlag.restrictedEvaluation phi i).range := by
  let F := filtration phi jointKernel_eq_bot
  rw [F.finrank_eq_sum_layers]
  change (∑ r ∈ Finset.range (Fintype.card I), Module.finrank K (F.layer r)) = _
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦ Module.finrank K (F.layer r))]
  rw [← (profileOrderIso (I := I)).sum_comp
    (fun i ↦ Module.finrank K (VOA.GordonKernelFlag.restrictedEvaluation phi i).range)]
  apply Finset.sum_congr rfl
  intro j _
  exact (filtrationLayer_finrank_eq_kernelLayer phi jointKernel_eq_bot j).trans
    (VOA.GordonKernelFlag.layerEquivRange phi (profileOrderIso j)).finrank_eq

variable (carrier : ∀ i, Submodule K (W i))

/-- The range of a restricted profile evaluation embeds into its corrected carrier once
later-kernel carrier membership has been proved. -/
def restrictedRangeToCarrier (phi : ∀ i, V →ₗ[K] W i) (i : I)
    (hcarrier : ∀ x, x ∈ VOA.GordonKernelFlag.laterKernel phi i →
      phi i x ∈ carrier i) :
    LinearMap.range (VOA.GordonKernelFlag.restrictedEvaluation phi i) →ₗ[K] carrier i where
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

omit [Fintype I] in
theorem restrictedRangeToCarrier_injective
    (phi : ∀ i, V →ₗ[K] W i) (i : I)
    (hcarrier : ∀ x, x ∈ VOA.GordonKernelFlag.laterKernel phi i →
      phi i x ∈ carrier i) :
    Function.Injective (restrictedRangeToCarrier carrier phi i hcarrier) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : carrier i => (z : W i)) hxy

/-- Each intrinsic exact kernel layer injects into the corrected carrier at that profile. -/
def kernelLayerToCarrier
    (phi : ∀ i, V →ₗ[K] W i) (i : I)
    (hcarrier : ∀ x, x ∈ VOA.GordonKernelFlag.laterKernel phi i →
      phi i x ∈ carrier i) :
    Submodule.Layer
        (VOA.GordonKernelFlag.laterKernel phi i)
        (VOA.GordonKernelFlag.currentKernel phi i)
        (VOA.GordonKernelFlag.currentKernel_le_laterKernel phi i) →ₗ[K]
      carrier i :=
  (restrictedRangeToCarrier carrier phi i hcarrier).comp
    (VOA.GordonKernelFlag.layerEquivRange phi i).toLinearMap

omit [Fintype I] in
theorem kernelLayerToCarrier_injective
    (phi : ∀ i, V →ₗ[K] W i) (i : I)
    (hcarrier : ∀ x, x ∈ VOA.GordonKernelFlag.laterKernel phi i →
      phi i x ∈ carrier i) :
    Function.Injective
      (kernelLayerToCarrier carrier phi i hcarrier) :=
  (restrictedRangeToCarrier_injective carrier phi i hcarrier).comp
    (VOA.GordonKernelFlag.layerEquivRange phi i).injective

variable [FiniteDimensional K V]
variable [∀ i, FiniteDimensional K (carrier i)]

/-- **Ordered kernel-flag telescope.**  Joint separation of the raw evaluations and corrected
carrier membership only on each later-kernel layer imply the global dimension bound. -/
theorem finrank_le_sum_carriers
    (phi : ∀ i, V →ₗ[K] W i)
    (jointKernel_eq_bot : (⨅ i, LinearMap.ker (phi i)) = ⊥)
    (hcarrier : ∀ i x, x ∈ VOA.GordonKernelFlag.laterKernel phi i →
      phi i x ∈ carrier i) :
    Module.finrank K V ≤ ∑ i, Module.finrank K (carrier i) := by
  let F := filtration phi jointKernel_eq_bot
  rw [F.finrank_eq_sum_layers]
  change (∑ r ∈ Finset.range (Fintype.card I), Module.finrank K (F.layer r)) ≤ _
  rw [← Fin.sum_univ_eq_sum_range (fun r => Module.finrank K (F.layer r))]
  rw [← (profileOrderIso (I := I)).sum_comp
    (fun i => Module.finrank K (carrier i))]
  refine Finset.sum_le_sum fun j _ => ?_
  calc
    Module.finrank K (F.layer j.1) =
        Module.finrank K (Submodule.Layer
          (VOA.GordonKernelFlag.laterKernel phi (profileOrderIso j))
          (VOA.GordonKernelFlag.currentKernel phi (profileOrderIso j))
          (VOA.GordonKernelFlag.currentKernel_le_laterKernel
            phi (profileOrderIso j))) :=
      filtrationLayer_finrank_eq_kernelLayer phi jointKernel_eq_bot j
    _ ≤ Module.finrank K (carrier (profileOrderIso j)) :=
      (kernelLayerToCarrier carrier phi (profileOrderIso j)
        (hcarrier (profileOrderIso j))).finrank_le_finrank_of_injective
          (kernelLayerToCarrier_injective carrier phi (profileOrderIso j)
            (hcarrier (profileOrderIso j)))

end

end VOA.GordonFiniteOrderedKernelFlag

section AxiomAudit
namespace VOA.GordonFiniteOrderedKernelFlag
end VOA.GordonFiniteOrderedKernelFlag
end AxiomAudit
