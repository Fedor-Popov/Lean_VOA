/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSquareBracket
import VOA.Modularity.EisensteinAnalytic
import VOA.Modules.SuperZhuRingDischarge

/-!
# Genus-one relation spaces for an integral-weight super VOA

This file defines the two algebraic relation families satisfied by an untwisted supertrace
one-point function.  Their formulas are the same as in the bosonic theory.  The super sign is not
an extra scalar in the relation: it appears when the zero-mode relation is identified, modulo the
super Zhu ideal, with a **supercommutator**.

The cusp degeneration itself is proved here without any commutator theorem:

`superBlockRelSpanAtCusp = superO + span {a[0]v}`.

Thus this file isolates the exact remaining signed gate.  To identify the quotient with a
supercommutator quotient of `superA`, one needs the super Zhu commutator congruence

`a * b - koszul p q • b * a - a[0]b ∈ superO`

for parity-homogeneous positive-weight `a,b`.  That congruence is not assumed as a structure field
or hidden in the definition below.
-/

namespace VOA

open scoped BigOperators

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)

/-- The deformed genus-one relation space at a point `z`: square-bracket zero modes and the
`G₂`-free `[−2]` family.  This is the untwisted supertrace sector. -/
noncomputable def superBlockRelSpan (z : ℂ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ
    ({x : 𝒱 | ∃ (k : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        x = V.superVSqZ a k 0 v} ∪
     {x : 𝒱 | ∃ (k K : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        (∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = V.superVSqZ a k (-2) v + ∑ m ∈ Finset.range K,
          (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z)
            • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v})

/-- The `q → 0` specialization of the super genus-one relation space. -/
def superBlockRelSpanAtCusp : Submodule ℂ 𝒱 :=
  Submodule.span ℂ
    ({x : 𝒱 | ∃ (k : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        x = V.superVSqZ a k 0 v} ∪
     {x : 𝒱 | ∃ (k K : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        (∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = V.superVSqZ a k (-2) v + ∑ m ∈ Finset.range K,
          (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
            • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v})

/-- The intrinsic algebraic cusp relation: the super Zhu ideal plus the square-bracket zero modes.
No claim about supercommutators is built into this definition. -/
def superCuspRelSpan : Submodule ℂ 𝒱 :=
  V.superO hV ⊔ Submodule.span ℂ
    {x : 𝒱 | ∃ (k : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
      x = V.superVSqZ a k 0 v}

variable {V hV}

theorem superVSqZ_zero_mem_superBlockRelSpanAtCusp {k : ℕ} (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.gradingZ (k : ℤ)) (v : 𝒱) :
    V.superVSqZ a k 0 v ∈ V.superBlockRelSpanAtCusp :=
  Submodule.subset_span (Or.inl ⟨k, a, v, hk, ha, rfl⟩)

theorem superVSqZ_zero_mem_superCuspRelSpan {k : ℕ} (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.gradingZ (k : ℤ)) (v : 𝒱) :
    V.superVSqZ a k 0 v ∈ V.superCuspRelSpan hV :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨k, a, v, hk, ha, rfl⟩)

theorem superO_le_superCuspRelSpan : V.superO hV ≤ V.superCuspRelSpan hV := le_sup_left

/-- The truncated cusp tail is its locally finite `finsum`. -/
theorem superNegTwo_cusp_finsum_eq_sum {k K : ℕ} {a v : 𝒱}
    (hK : ∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) :
    (∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • V.superVSqZ a k (2 * ((m : ℤ) + 2) - 2) v)
      = ∑ m ∈ Finset.range K, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  have hz := hK (m + 1) (by omega)
  rw [show (2 * ((((m : ℕ) + 1 : ℕ) : ℤ) + 1) - 2)
      = 2 * ((m : ℤ) + 2) - 2 from by push_cast; ring] at hz
  exact hm (by rw [hz, smul_zero])

/-- Every specialized analytic relation lies in `superO + span {a[0]v}`. -/
theorem superBlockRelSpanAtCusp_le_superCuspRelSpan :
    V.superBlockRelSpanAtCusp ≤ V.superCuspRelSpan hV := by
  rw [superBlockRelSpanAtCusp, Submodule.span_le]
  rintro x (⟨k, a, v, hk, ha, rfl⟩ | ⟨k, K, a, v, hk, ha, hK, rfl⟩)
  · exact superVSqZ_zero_mem_superCuspRelSpan hk ha v
  · rw [← superNegTwo_cusp_finsum_eq_sum hK, V.superNegTwoFamily_cusp hk a v]
    exact (V.superCuspRelSpan hV).add_mem
      (superO_le_superCuspRelSpan (V.superPres_mem_superO hV ha v 0))
      (Submodule.smul_mem _ _ (superVSqZ_zero_mem_superCuspRelSpan hk ha v))

/-- A depth-zero super Zhu residue belongs to the specialized block relation space. -/
theorem superPres_zero_mem_superBlockRelSpanAtCusp {k : ℕ} (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.gradingZ (k : ℤ)) (v : 𝒱) :
    V.superPres k a v 0 ∈ V.superBlockRelSpanAtCusp := by
  obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a k v
  have hmem : V.superVSqZ a k (-2) v + ∑ m ∈ Finset.range K,
      (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v
      ∈ V.superBlockRelSpanAtCusp :=
    Submodule.subset_span (Or.inr ⟨k, K, a, v, hk, ha, hK, rfl⟩)
  rw [← superNegTwo_cusp_finsum_eq_sum hK, V.superNegTwoFamily_cusp hk a v] at hmem
  have hsub := V.superBlockRelSpanAtCusp.sub_mem hmem
    (Submodule.smul_mem _ (1 / 12 : ℂ)
      (superVSqZ_zero_mem_superBlockRelSpanAtCusp hk ha v))
  simpa using hsub

/-- For a nonnegative homogeneous state, the defining generator of `superO` is the depth-zero
super Zhu residue. -/
theorem superZhuLgen_eq_superPres {k : ℕ} {a : 𝒱} (ha : a ∈ V.gradingZ (k : ℤ)) (v : 𝒱) :
    V.superZhuMul hV (V.L (-1) a + V.L 0 a) v = V.superPres k a v 0 := by
  rw [V.superZhuMul_L_base hV ha v]
  unfold superPres
  rw [Nat.add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
    show ((i : ℤ) - 2 - ((0 : ℕ) : ℤ)) = (i : ℤ) - 2 from by push_cast; ring]

/-- For a super VOA, every algebraic cusp relation is generated by the specialized analytic
relations.  Positivity and the vacuum axiom handle the nonpositive weight slices. -/
theorem superCuspRelSpan_le_superBlockRelSpanAtCusp
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights) :
    W.toSuperNearVOA.superCuspRelSpan hW
      ≤ W.toSuperNearVOA.superBlockRelSpanAtCusp := by
  let V := W.toSuperNearVOA
  refine sup_le ?_ ?_
  · rw [V.superO_eq_span hW, Submodule.span_le]
    rintro _ ⟨u, v, rfl⟩
    refine V.reduce_bihomogeneous hW
      (P := fun u => V.superZhuMul hW (V.L (-1) u + V.L 0 u) v
        ∈ V.superBlockRelSpanAtCusp) ?_ ?_ ?_ u
    · intro k p a ha
      rcases lt_trichotomy k 0 with hk | hk | hk
      · have ha0 : a = 0 := by
          have hbot := W.gradingZ_neg_eq_bot k hk
          rw [hbot] at ha
          simpa using ha.1
        subst ha0
        simp only [map_zero, add_zero, V.superZhuMul_zero_left]
        exact V.superBlockRelSpanAtCusp.zero_mem
      · subst hk
        have ha0 : a ∈ W.grading 0 := by
          simpa [V, SuperNearVOA.gradingZ_apply] using ha.1
        rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha0
        obtain ⟨c, rfl⟩ := ha0
        have hvac : V.smul W.vacuum (-2) v = 0 := by
          change V.smul V.vacuum (-2) v = 0
          rw [SuperVertexAlgebra.smul_vacuum_left, if_neg (by norm_num)]
        rw [V.superZhuLgen_eq_superPres (hV := hW) (k := 0) (by
            change c • V.vacuum ∈ V.grading (((0 : ℤ) : ℂ))
            exact ha.1) v]
        unfold superPres
        rw [Nat.zero_add, Finset.sum_range_one]
        norm_num
        rw [hvac, smul_zero]
        exact V.superBlockRelSpanAtCusp.zero_mem
      · have hk1 : 1 ≤ k.toNat := by omega
        have ha' : a ∈ V.gradingZ ((k.toNat : ℕ) : ℤ) := by
          rw [show ((k.toNat : ℕ) : ℤ) = k from by omega]
          exact ha.1
        rw [V.superZhuLgen_eq_superPres (hV := hW) ha' v]
        exact superPres_zero_mem_superBlockRelSpanAtCusp hk1 ha' v
    · simp only [map_zero, add_zero, V.superZhuMul_zero_left]
      exact V.superBlockRelSpanAtCusp.zero_mem
    · intro x y hx hy
      rw [show V.L (-1) (x + y) + V.L 0 (x + y)
          = (V.L (-1) x + V.L 0 x) + (V.L (-1) y + V.L 0 y) from by
            simp only [map_add]; abel,
        V.superZhuMul_add_left hW]
      exact V.superBlockRelSpanAtCusp.add_mem hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨k, a, v, hk, ha, rfl⟩
    exact superVSqZ_zero_mem_superBlockRelSpanAtCusp hk ha v

/-- The exact cusp degeneration for an integral-weight super VOA. -/
theorem superBlockRelSpanAtCusp_eq_superCuspRelSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights) :
    W.toSuperNearVOA.superBlockRelSpanAtCusp
      = W.toSuperNearVOA.superCuspRelSpan hW :=
  le_antisymm superBlockRelSpanAtCusp_le_superCuspRelSpan
    (superCuspRelSpan_le_superBlockRelSpanAtCusp W hW)

end SuperNearVOA

end VOA
