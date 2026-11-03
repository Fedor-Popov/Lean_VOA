/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLeaf3
import VOA.Modules.ZhuRingInstance

/-!
# `IsSimpleAMod` is Mathlib's `IsSimpleModule` over `A(𝒱)`

`Modules.ZhuBijection` defines the codomain predicate of Zhu's Theorem 5.3.4 intrinsically —
`AMod W` bundles a
`ℂ`-space with a `ℂ`-linear `ρ : A(𝒱) →ₗ End`, unital and multiplicative *on representable Zhu
products*, and `IsSimpleAMod` quantifies over `AModSubmodule`s.  Since `mk` is surjective and
`instRingA` makes `mk W u * mk W v = mk W (u * v)`, that data **is** a genuine module, and the two
simplicity notions agree.

This is link **L1**'s missing bridge: it lets the Artin–Wedderburn machinery of
`Modularity.SemisimpleTrace` / `Modularity.WedderburnSimples` speak about `Irr A(𝒱)` as `AMod`
defines it.

## Main results

* `AMod.ρRingHom` — the action as a ring homomorphism `A(𝒱) →+* End ℂ U.carrier`;
* `AMod.moduleA` — the induced `A(𝒱)`-module structure, and `AMod.smul_def`;
* `isSimpleAMod_iff_isSimpleModule`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **The action of a bundled `AMod` is a ring homomorphism.**  Multiplicativity is only assumed
on representable Zhu products, but `mk` is surjective, so that is everything. -/
noncomputable def AMod.ρRingHom (U : AMod W) :
    letI := instRingA W
    A W →+* End ℂ U.carrier :=
  letI := instRingA W
  { toFun := fun a => U.ρ a
    map_one' := U.ρ_one
    map_mul' := fun p q => by
      obtain ⟨u, rfl⟩ := _root_.VOA.mk_surjective W p
      obtain ⟨v, rfl⟩ := _root_.VOA.mk_surjective W q
      show U.ρ (Amul (zhuRingData_holds W)
        (_root_.VOA.mk W u) (_root_.VOA.mk W v)) = _
      rw [Amul_mk]
      exact U.ρ_mul u v
    map_zero' := map_zero U.ρ
    map_add' := fun p q => map_add U.ρ p q }

/-- The `A(𝒱)`-module structure carried by a bundled `AMod`. -/
@[reducible] noncomputable def AMod.moduleA (U : AMod W) :
    letI := instRingA W
    Module (A W) U.carrier :=
  letI := instRingA W
  Module.compHom U.carrier (AMod.ρRingHom U)

theorem AMod.smul_def (U : AMod W) (a : A W) (x : U.carrier) :
    letI := instRingA W
    letI := U.moduleA
    a • x = U.ρ a x := rfl

/-- The `ℂ`-action and the `A(𝒱)`-action are compatible. -/
theorem AMod.smul_comm_C (U : AMod W) (c : ℂ) (a : A W) (x : U.carrier) :
    letI := instRingA W
    letI := U.moduleA
    (c • a) • x = c • (a • x) := by
  letI := instRingA W
  letI := U.moduleA
  change U.ρ (c • a) x = c • U.ρ a x
  rw [map_smul]
  rfl

/-! ## The two simplicity notions agree -/

/-- An `A(𝒱)`-submodule in Mathlib's sense, read as an `AModSubmodule`. -/
noncomputable def AMod.toAModSubmodule (U : AMod W)
    (N : letI := instRingA W; letI := U.moduleA; Submodule (A W) U.carrier) :
    AModSubmodule U :=
  letI := instRingA W
  letI := U.moduleA
  { carrier :=
      { carrier := (N : Set U.carrier)
        add_mem' := fun hx hy => N.add_mem hx hy
        zero_mem' := N.zero_mem
        smul_mem' := fun c x hx => by
          have h := N.smul_mem (c • (1 : A W)) hx
          rwa [AMod.smul_comm_C U c (1 : A W) x, one_smul] at h }
    ρ_mem := fun a {x} hx => N.smul_mem a hx }

/-- An `AModSubmodule`, read as an `A(𝒱)`-submodule in Mathlib's sense. -/
noncomputable def AMod.ofAModSubmodule (U : AMod W) (S : AModSubmodule U) :
    letI := instRingA W; letI := U.moduleA; Submodule (A W) U.carrier :=
  letI := instRingA W
  letI := U.moduleA
  { carrier := (S.carrier : Set U.carrier)
    add_mem' := fun hx hy => S.carrier.add_mem hx hy
    zero_mem' := S.carrier.zero_mem
    smul_mem' := fun a x hx => S.ρ_mem a hx }

/-- **`IsSimpleAMod` is `IsSimpleModule` over `A(𝒱)`.** -/
theorem isSimpleAMod_iff_isSimpleModule (U : AMod W) :
    letI := instRingA W
    letI := U.moduleA
    (IsSimpleAMod U ↔ IsSimpleModule (A W) U.carrier) := by
  letI := instRingA W
  letI := U.moduleA
  constructor
  · rintro ⟨hnt, hsub⟩
    haveI := hnt
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases hsub (U.toAModSubmodule N) with h | h
    · left
      refine SetLike.ext (fun x => ?_)
      constructor
      · intro hx
        have : x ∈ (U.toAModSubmodule N).carrier := hx
        rw [h] at this
        simpa using this
      · intro hx
        rw [Submodule.mem_bot] at hx
        rw [hx]
        exact N.zero_mem
    · right
      refine SetLike.ext (fun x => ?_)
      constructor
      · intro _; trivial
      · intro _
        have : x ∈ (U.toAModSubmodule N).carrier := by rw [h]; trivial
        exact this
  · intro hsimple
    refine ⟨hsimple.nontrivial, fun S => ?_⟩
    rcases hsimple.eq_bot_or_eq_top (U.ofAModSubmodule S) with h | h
    · left
      refine SetLike.ext (fun x => ?_)
      constructor
      · intro hx
        have : x ∈ U.ofAModSubmodule S := hx
        rw [h, Submodule.mem_bot] at this
        rw [this]
        exact Submodule.zero_mem _
      · intro hx
        rw [Submodule.mem_bot] at hx
        rw [hx]
        exact S.carrier.zero_mem
    · right
      refine SetLike.ext (fun x => ?_)
      constructor
      · intro _; trivial
      · intro _
        have : x ∈ U.ofAModSubmodule S := by rw [h]; trivial
        exact this

end VOA
