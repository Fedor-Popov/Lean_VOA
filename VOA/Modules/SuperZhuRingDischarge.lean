/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.SuperZhuAssociator
import VOA.Modules.SuperAdjointModule

/-!
# `SuperZhuRingData` discharged — `A(V)` is an honest ring (Dong–Zhao Thm 3.1)

`Modules/SuperZhuRing` built the super Zhu product `∗`, the ideal `O(V)`, the quotient
`A(V) = V/O(V)`, and the `Ring`/`ℂ`-Algebra structures **conditional** on the packaged hypothesis
class `SuperZhuRingData`.  The bosonic proof (`ZhuRightIdeal`, `ZhuAssociator`,
`ZhuRingResidue`) runs off the Borcherds/Jacobi identity
`Core.Borcherds.VertexOperatorAlgebra.jacobi`; on the super side the corresponding identity is
`Core/SuperBorcherds.superJacobi`, and this file uses it to discharge `SuperZhuRingData`.

## Main results

* **`SuperNearVOA.superZhuRingData_holds`** — for any `SuperNearVOA` with `IntegralWeights` and
  vanishing negative weight spaces, `SuperZhuRingData V hV` holds.  The two analytic cores are
  `SuperZhuHR.right_ideal_coreε` and `SuperZhuAssoc.associator_coreε`; the left-ideal direction is
  free from associativity (`left_ideal_gen_of_assocε`).
* **`SuperVertexOperatorAlgebra.superZhuRingData`** — for a genuine super **VOA** the positivity
  hypothesis is discharged by the `positivity` axiom (VOA4), so the conclusion is *unconditional*
  apart from `IntegralWeights`.
* **`SuperVertexOperatorAlgebra.instRingSuperA` / `.instAlgebraSuperA`** — the `Ring` and
  `ℂ`-algebra structures, unconditional.
* **`SympFerm.instRingASF`, `SympFerm.instAlgebraASF`** — `A(SF)` is an **honest ring**, with
  no hypothesis at all; and `SympFerm.chiClass_sq_eq_zero`, `SympFerm.chiClass_anticomm` restate the
  exterior-algebra relations `[χᵃ]² = 0`, `[χᵃ][χᵇ] + [χᵇ][χᵃ] = 0` in it, unconditionally.

## The exact hypothesis ledger (nothing hidden)

`superZhuRingData_holds` takes, and only takes:

* `hV : V.IntegralWeights` — inherited from `superZhuMul`'s own gate; `(1+z)^h` is a finite sum
  only for `h ∈ ℤ`, and the whole Dong–Zhao theory is stated for `ℤ`-graded VOSAs.
* `hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥` — `SuperNearVOA` has no `positivity` field (that is
  what "near" means), and the reduction of a general element to the `ℕ`-indexed cores needs it.
  For a `SuperVertexOperatorAlgebra` it is VOA4 and therefore free.

Nothing else.  In particular **no spin–statistics**, no `SkewVacLocal₀`, no `vacuum_grade`, no
`BoundedBelow`, and no unproved package: `right_ideal_coreε` and `associator_coreε` are theorems.

## Status
`sorry`-free, with no project axioms.

## References
* Dong–Zhao, arXiv:math/0601571, Thm 3.1; Zhu [574] Thm 2.1.1–2.1.2; Frenkel–Zhu.
-/

namespace VOA

open scoped BigOperators
open Classical

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  Positivity in the `ℤ`-graded form -/

namespace SuperVertexOperatorAlgebra

/-- **VOA4 in `ℤ`-graded form.**  A super VOA has no negative integer weight spaces. -/
theorem gradingZ_neg_eq_bot (W : SuperVertexOperatorAlgebra 𝒱) (k : ℤ) (hk : k < 0) :
    W.toSuperNearVOA.gradingZ k = ⊥ := by
  rw [SuperNearVOA.gradingZ_apply]
  refine W.positivity ((k : ℤ) : ℂ) ?_
  rw [Complex.intCast_re]
  exact_mod_cast hk

end SuperVertexOperatorAlgebra

/-! ## §2  The discharge -/

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- **The two-sided-ideal and associativity content of Dong–Zhao Thm 3.1, from the two cores.**
The `ℤ`-graded, parity-refined reductions bridge to the `ℕ`-indexed bi-homogeneous cores;
negative grades vanish by `hpos`. -/
theorem superZhuRingData_of_cores (hV : V.IntegralWeights)
    (hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥)
    (hRcore : ∀ (K M : ℕ) (p q : ZMod 2) (u a : 𝒱), u ∈ V.gradingZ (K : ℤ) → u ∈ V.parity p →
        a ∈ V.gradingZ (M : ℤ) → a ∈ V.parity q → ∀ b : 𝒱,
        V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV)
    (hAcore : ∀ (K L : ℕ) (p q : ZMod 2) (u v : 𝒱), u ∈ V.gradingZ (K : ℤ) → u ∈ V.parity p →
        v ∈ V.gradingZ (L : ℤ) → v ∈ V.parity q → ∀ w : 𝒱,
        V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
          ∈ V.superO hV) :
    SuperZhuRingData V hV := by
  -- (a) associativity mod `O`
  have hA : ∀ u v w : 𝒱,
      V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
        ∈ V.superO hV := by
    refine V.assoc_of_bihomogeneous hV (fun K p u hu L q v hv w => ?_)
    rw [Submodule.mem_inf] at hu hv
    rcases lt_or_ge K 0 with hK | hK
    · rw [hpos K hK, Submodule.mem_bot] at hu
      rw [hu.1]
      simp only [superZhuMul_zero_left, superZhuMul_zero_right, sub_self]
      exact (V.superO hV).zero_mem
    rcases lt_or_ge L 0 with hL | hL
    · rw [hpos L hL, Submodule.mem_bot] at hv
      rw [hv.1]
      simp only [superZhuMul_zero_left, superZhuMul_zero_right, sub_self]
      exact (V.superO hV).zero_mem
    · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
      obtain ⟨L', rfl⟩ : ∃ L' : ℕ, L = (L' : ℤ) := ⟨L.toNat, by omega⟩
      exact hAcore K' L' p q u v hu.1 hu.2 hv.1 hv.2 w
  -- (b) the right-ideal generator statement
  have hR : ∀ u a b : 𝒱,
      V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV := by
    refine V.right_ideal_gen_of_bihomogeneous hV (fun K p u hu M q a ha b => ?_)
    rw [Submodule.mem_inf] at hu ha
    rcases lt_or_ge K 0 with hK | hK
    · rw [hpos K hK, Submodule.mem_bot] at hu
      rw [hu.1, superZhuMul_zero_left]
      exact (V.superO hV).zero_mem
    rcases lt_or_ge M 0 with hM | hM
    · rw [hpos M hM, Submodule.mem_bot] at ha
      rw [ha.1]
      simp only [map_zero, add_zero, superZhuMul_zero_left, superZhuMul_zero_right]
      exact (V.superO hV).zero_mem
    · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
      exact hRcore K' M' p q u a hu.1 hu.2 ha.1 ha.2 b
  exact
    { left_ideal := fun {u} hu v =>
        V.left_ideal_of_gen hV v (fun g hg => V.left_ideal_gen_of_assocε hV hA g hg v) u hu
      right_ideal := fun u {v} hv =>
        V.right_ideal_of_gen hV u
          (fun g hg => by obtain ⟨a, b, rfl⟩ := hg; exact hR u a b) v hv
      assoc := hA }

/-- **Dong–Zhao Thm 3.1, discharged.**  For a super near-VOA with integral weights and no
negative weight spaces, `O(V)` is a two-sided ideal for the super Zhu product and `∗` is
associative modulo `O(V)`.  The two hypotheses are the *only* ones. -/
theorem superZhuRingData_holds (hV : V.IntegralWeights)
    (hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥) : SuperZhuRingData V hV :=
  V.superZhuRingData_of_cores hV hpos
    (fun _ _ _ _ _ _ hu hup ha haq b => SuperZhuHR.right_ideal_coreε V hV hpos hu hup ha haq b)
    (fun _ _ _ _ _ _ hu hup hv hvq w => SuperZhuAssoc.associator_coreε V hV hu hup hv hvq w)

end SuperNearVOA

/-! ## §3  The unconditional ring on a genuine super VOA -/

namespace SuperVertexOperatorAlgebra

/-- **Dong–Zhao Thm 3.1 for a super VOA**: positivity is VOA4, so `IntegralWeights` is the only
remaining hypothesis. -/
theorem superZhuRingData (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) :
    SuperZhuRingData W.toSuperNearVOA hV :=
  W.toSuperNearVOA.superZhuRingData_holds hV (fun k hk => W.gradingZ_neg_eq_bot k hk)

/-- **`A(W)` is an associative `Ring`** for every integrally graded super VOA. -/
@[reducible] noncomputable def instRingSuperA (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) : Ring (W.toSuperNearVOA.superA hV) :=
  (W.superZhuRingData hV).AsRing

/-- **`A(W)` is a `ℂ`-algebra** for every integrally graded super VOA. -/
@[reducible] noncomputable def instAlgebraSuperA (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) :
    @Algebra ℂ (W.toSuperNearVOA.superA hV) _ (instRingSuperA W hV).toSemiring :=
  (W.superZhuRingData hV).AsAlgebra

end SuperVertexOperatorAlgebra

/-! ## §4  The symplectic-fermion application: `A(SF)` is an honest ring -/

namespace SympFerm

open VOA.SympFerm

/-- **Dong–Zhao Thm 3.1 for symplectic fermions**, with no hypothesis: `SF` has integral weights
(`sympFerm_integralWeights`) and no negative weight spaces (VOA4). -/
theorem sympFermSuperZhuRingData :
    SuperZhuRingData sympFermSVOA.toSuperNearVOA sympFerm_integralWeights :=
  sympFermSVOA.superZhuRingData sympFerm_integralWeights

/-- **`A(SF)` is an associative ring**, unconditionally. -/
@[reducible] noncomputable def instRingASF :
    Ring (sympFermSVOA.toSuperNearVOA.superA sympFerm_integralWeights) :=
  sympFermSuperZhuRingData.AsRing

/-- **`A(SF)` is a `ℂ`-algebra**, unconditionally. -/
@[reducible] noncomputable def instAlgebraASF :
    @Algebra ℂ (sympFermSVOA.toSuperNearVOA.superA sympFerm_integralWeights) _
      instRingASF.toSemiring :=
  sympFermSuperZhuRingData.AsAlgebra

/-- **`[χᵃ]² = 0` in the ring `A(SF)`** — unconditional (`chiStateSF_sq_eq_zero` is stated
with `SuperZhuRingData` as a hypothesis; that hypothesis is a theorem). -/
theorem chiClass_sq_eq_zero (a : Fin 2) :
    letI := instRingASF
    (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
      * (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
      = 0 :=
  chiStateSF_sq_eq_zero sympFermSuperZhuRingData a

/-- **`[χᵃ][χᵇ] + [χᵇ][χᵃ] = 0` in the ring `A(SF)`** — unconditional.  Together with
`chiClass_sq_eq_zero` these are the defining relations of the exterior algebra `Λ(χ⁺, χ⁻)`, holding in
a genuine associative ring.

⚠ Still **not** claimed (and still open): that `[χᵃ] ≠ 0`, which needs `O(SF)` computed.  Without
it these relations remain compatible with `A(SF)` being trivial in those degrees. -/
theorem chiClass_anticomm (a b : Fin 2) :
    letI := instRingASF
    (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
        * (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF b))
      + (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF b))
        * (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
      = 0 :=
  chiStateSF_anticomm sympFermSuperZhuRingData a b

end SympFerm

end VOA
