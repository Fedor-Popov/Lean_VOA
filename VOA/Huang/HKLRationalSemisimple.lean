/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorSemisimple

/-!
# Complete reducibility from completely reducible generating pieces

Pure module theory for weak modules (no VOA-specific input beyond the definition), used to pass
from ordinary to admissible modules in the HKL rationality argument.

`completelyReducible_of_generating` — if every vector of a weak `W`-module `A` lies in the
range of a mode-intertwining linear map `φ : M' → M` out of a **completely reducible** weak
`W`-module `A'`, then `A` is completely reducible (every weak submodule has a weak complement).

Proof: in the mode algebra `R = modeAlg A`, the ranges `S_x = φ_x(M')` are `R`-submodules with
`⨆ S_x = ⊤`; each interval `Iic S_x` is complemented (pull a submodule `T ≤ S_x` back along
`φ_x`, complement it in `M'`, push the complement forward); Mathlib's
`complementedLattice_of_complementedLattice_Iic` makes the whole submodule lattice complemented.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

namespace VOA.Huang.HKLRational

open VOA VOA.Huang.PzTensorSemisimple

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Every weak submodule has a weak complement. -/
def WeakCompletelyReducible {M : Type v} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) :
    Prop :=
  ∀ P : WeakModule.Submodule' A, ∃ Q : WeakModule.Submodule' A, IsCompl P.carrier Q.carrier

/-- A linear map intertwining all modes. -/
def IsModeHom {M : Type v} [AddCommGroup M] [Module ℂ M] {M' : Type w} [AddCommGroup M']
    [Module ℂ M'] (A : WeakModule W M) (A' : WeakModule W M') (φ : M' →ₗ[ℂ] M) : Prop :=
  ∀ (a : 𝒱) (k : ℤ) (y : M'), φ (mode (A'.YM a) k y) = mode (A.YM a) k (φ y)

variable {M : Type v} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)

/-- The range of a mode homomorphism is mode-stable. -/
theorem stable_range {M' : Type w} [AddCommGroup M'] [Module ℂ M'] {A' : WeakModule W M'}
    {φ : M' →ₗ[ℂ] M} (hφ : IsModeHom A A' φ) : Stable A (LinearMap.range φ) := by
  rintro u n _ ⟨y, rfl⟩
  exact ⟨mode (A'.YM u) n y, hφ u n y⟩

/-- The interval below the range of a mode homomorphism out of a completely reducible module is
complemented. -/
theorem complementedLattice_Iic_range {M' : Type w} [AddCommGroup M'] [Module ℂ M']
    {A' : WeakModule W M'} {φ : M' →ₗ[ℂ] M} (hφ : IsModeHom A A' φ)
    (hA' : WeakCompletelyReducible A') :
    ComplementedLattice (Set.Iic (liftSub A (LinearMap.range φ) (stable_range A hφ))) := by
  set S := liftSub A (LinearMap.range φ) (stable_range A hφ) with hS
  refine ⟨fun T => ?_⟩
  obtain ⟨T, hT⟩ := T
  -- pull back
  let P' : WeakModule.Submodule' A' :=
    { carrier := Submodule.comap φ (T.restrictScalars ℂ)
      act_mem := by
        intro u n y hy
        change φ (A'.act u n y) ∈ T
        rw [WeakModule.act_def, hφ]
        exact T.smul_mem (modeElt A u n) hy }
  obtain ⟨Q', hQ'⟩ := hA' P'
  have hstQ : Stable A (Submodule.map φ Q'.carrier) := by
    rintro u n _ ⟨y, hy, rfl⟩
    refine ⟨mode (A'.YM u) n y, ?_, hφ u n y⟩
    have := Q'.act_mem u n hy
    rwa [WeakModule.act_def] at this
  let U := liftSub A (Submodule.map φ Q'.carrier) hstQ
  have hUS : U ≤ S := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  refine ⟨⟨U, hUS⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subtype.ext
    change T ⊓ U = ⊥
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxU⟩
    obtain ⟨y, hy, rfl⟩ := hxU
    have hyP : y ∈ P'.carrier := hxT
    have : y ∈ P'.carrier ⊓ Q'.carrier := ⟨hyP, hy⟩
    rw [hQ'.inf_eq_bot, Submodule.mem_bot] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  · rw [codisjoint_iff]
    apply Subtype.ext
    change T ⊔ U = S
    apply le_antisymm (sup_le hT hUS)
    rintro x ⟨y, rfl⟩
    have hy : y ∈ P'.carrier ⊔ Q'.carrier := by rw [hQ'.sup_eq_top]; trivial
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    exact Submodule.add_mem_sup hy₁ ⟨y₂, hy₂, rfl⟩

/-- **Complete reducibility from completely reducible generating pieces.** -/
theorem completelyReducible_of_generating
    (hgen : ∀ x : M, ∃ (M' : Type w) (_ : AddCommGroup M') (_ : Module ℂ M')
      (A' : WeakModule W M') (φ : M' →ₗ[ℂ] M),
      IsModeHom A A' φ ∧ WeakCompletelyReducible A' ∧ x ∈ LinearMap.range φ) :
    WeakCompletelyReducible A := by
  choose M' _ _ A' φ hφ hcr hx using hgen
  let p : M → Submodule (modeAlg A) M := fun x =>
    liftSub A (LinearMap.range (φ x)) (stable_range A (hφ x))
  have htop : ⨆ x, p x = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Submodule.mem_iSup_of_mem x (hx x)
  have hcl : ComplementedLattice (Submodule (modeAlg A) M) :=
    complementedLattice_of_complementedLattice_Iic (s := Set.univ)
      (fun x _ => complementedLattice_Iic_range A (hφ x) (hcr x)) (by simpa using htop)
  intro P
  obtain ⟨Q, hQ⟩ := hcl.exists_isCompl (toSub A P)
  refine ⟨ofSub A Q, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have : x ∈ toSub A P ⊓ Q := hx
    rw [hQ.inf_eq_bot] at this
    exact this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have : x ∈ toSub A P ⊔ Q := by rw [hQ.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp this
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, rfl⟩

/-- **Complete reducibility from a spanning family of completely reducible images.** -/
theorem completelyReducible_of_iSup {ι : Type*} (M' : ι → Type w) [∀ i, AddCommGroup (M' i)]
    [∀ i, Module ℂ (M' i)] (A' : ∀ i, WeakModule W (M' i)) (φ : ∀ i, M' i →ₗ[ℂ] M)
    (hφ : ∀ i, IsModeHom A (A' i) (φ i)) (hcr : ∀ i, WeakCompletelyReducible (A' i))
    (hsup : ⨆ i, LinearMap.range (φ i) = ⊤) :
    WeakCompletelyReducible A := by
  let p : ι → Submodule (modeAlg A) M := fun i =>
    liftSub A (LinearMap.range (φ i)) (stable_range A (hφ i))
  have htop : ⨆ i, p i = ⊤ := by
    rw [eq_top_iff]
    intro x hxt
    clear hxt
    have hx : x ∈ ⨆ i, LinearMap.range (φ i) := by rw [hsup]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem i y hy => exact Submodule.mem_iSup_of_mem i hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  have hcl : ComplementedLattice (Submodule (modeAlg A) M) :=
    complementedLattice_of_complementedLattice_Iic (s := Set.univ)
      (fun i _ => complementedLattice_Iic_range A (hφ i) (hcr i)) (by simpa using htop)
  intro P
  obtain ⟨Q, hQ⟩ := hcl.exists_isCompl (toSub A P)
  refine ⟨ofSub A Q, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have : x ∈ toSub A P ⊓ Q := hx
    rw [hQ.inf_eq_bot] at this
    exact this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have : x ∈ toSub A P ⊔ Q := by rw [hQ.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp this
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, rfl⟩

end VOA.Huang.HKLRational
