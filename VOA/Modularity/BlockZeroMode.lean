/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SemisimpleTrace
import VOA.Modularity.BlockFiniteDim
import VOA.Modules.ZhuRingInstance
import VOA.Modules.ZhuVermaAnArchDLM3Zero
import VOA.Modularity.ZhuRecursionProof

/-!
# Block condition (i) is the Zhu commutator — the round-bracket form of `a[0]v`

Zhu's genus-one block condition (i) reads `F(a[0]v) = 0`, where `a[0]` is a **square-bracket**
zero mode.  Dong–Li–Mason (*Modular invariance of trace functions in orbifold theory*, eq. (10.6),
after Zhu Lemma 2.1.3) observe that this square-bracket mode is a **round-bracket** residue:

  `a[0]v = Res_z Y(a,z)v (1+z)^{wt a − 1} = Σ_{i ≥ 0} C(wt a − 1, i)·a₍ᵢ₎v ≡ a * v − v * a  (mod O(𝒱))`.

Everything here is **proved**: the explicit expansion comes from the repo's own square-bracket
coefficients, and the congruence itself is *not* a carried datum — it is proved upstream as
`Modules.ZhuVermaAnArchDLM3Zero.zhu_comm_mod_O`, and
`Modularity.ZhuRecursionProof.cbz_eq_sqBracketCoeffZ_zero` matches its binomials to the
square-bracket coefficients.  The upshot is that a block's pointwise functional descends to a
**symmetric** functional on `A(𝒱)` — the object
`Modularity.SemisimpleTrace.finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix` counts.

## Main results

* `vSqZ_zero_eq_sum` / `vSqZ_zero_eq_sum_range` — unconditional:
  `a[0]v = Σ_{i<wt a} C(wt a − 1, i)·a₍ᵢ₎v` for `a ∈ 𝒱_{wt a}`, `wt a ≥ 1`.
* `vSqZ_zero_eq_resFull` — the same mode **is** the Frenkel–Zhu residue `Res_z(1+z)^{k−1}Y(a,z)v`.
* `zhuCommutatorLaw_holds : ZhuCommutatorLaw W` — **DLM (10.6) is a THEOREM here**, for every
  `v` (not just homogeneous), off `zhu_comm_mod_O` + `reduce_homogeneous` + `positivity`.
* `VacuumGradeZero W` — `𝒱₀ ⊆ ℂ𝟙`; the only genuinely carried hypothesis (negative grades already
  vanish by the VOA axiom `positivity`).  A hypothesis of Zhu's theorem, not a gap.
* `symmetricFunctional_of_zeroModeVanishing` — a linear functional that kills `O(𝒱)` and every
  `a[0]v` induces a **symmetric** functional on `A(𝒱)`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Sole carried hypothesis: `VacuumGradeZero`.
-/

namespace VOA

open scoped BigOperators
open Module (finrank)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The explicit round-bracket expansion of `a[0]` -/

section Expansion

variable (W : VertexOperatorAlgebra 𝒱)

theorem sqBracketCoeffZ_zero_eq (ka : ℕ) (hka : 1 ≤ ka) (i : ℤ) :
    sqBracketCoeffZ ka 0 i
      = if 0 ≤ i then (((ka - 1).choose i.toNat : ℕ) : ℂ) else 0 := by
  have h1 : sqBracketCoeffZ ka 0 i = sqCoeffZ ka 0 i := by
    simpa using sqBracketCoeffZ_natCast ka 0 i
  rw [h1, sqCoeffZ]
  by_cases h : 0 ≤ i
  · rw [if_pos h, if_pos h, sqBracketCoeff_zero _ _ hka]
  · rw [if_neg h, if_neg h]

/-- **The square-bracket zero mode as a finite round-bracket sum** (DLM (10.6), left side):
`a[0]v = Σ_{0 ≤ i < wt a} C(wt a − 1, i)·a₍ᵢ₎v`. -/
theorem vSqZ_zero_eq_sum {ka : ℕ} (hka : 1 ≤ ka) (a v : 𝒱) :
    vSqZ W a ka 0 v
      = ∑ i ∈ Finset.Ico (0 : ℤ) (ka : ℤ),
          (((ka - 1).choose i.toNat : ℕ) : ℂ) • W.smul a i v := by
  classical
  rw [vSqZ_apply]
  have hsupp : (Function.support fun i : ℤ => sqBracketCoeffZ ka 0 i • mode (W.Y a) i v)
      ⊆ ↑(Finset.Ico (0 : ℤ) (ka : ℤ)) := by
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    rw [sqBracketCoeffZ_zero_eq ka hka i] at hi
    by_cases h0 : 0 ≤ i
    · refine ⟨h0, ?_⟩
      by_contra hle
      push_neg at hle
      rw [if_pos h0] at hi
      have hz : ((ka - 1).choose i.toNat : ℕ) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      exact hi (by rw [hz]; simp)
    · rw [if_neg h0] at hi
      exact absurd (by simp : (0:ℂ) • mode (W.Y a) i v = 0) hi
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Ico] at hi
  rw [sqBracketCoeffZ_zero_eq ka hka i, if_pos hi.1]
  rfl

/-- The same expansion indexed by `Finset.range`. -/
theorem vSqZ_zero_eq_sum_range {ka : ℕ} (hka : 1 ≤ ka) (a v : 𝒱) :
    vSqZ W a ka 0 v
      = ∑ i ∈ Finset.range ka, (((ka - 1).choose i : ℕ) : ℂ) • W.smul a (i : ℤ) v := by
  classical
  rw [vSqZ_zero_eq_sum W hka a v]
  have hset : Finset.Ico (0 : ℤ) (ka : ℤ)
      = (Finset.range ka).map ⟨fun i : ℕ => (i : ℤ), fun x y h => by
          simpa using h⟩ := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h0, hn⟩
      exact ⟨i.toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by positivity, by exact_mod_cast hj⟩
  rw [hset, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Function.Embedding.coeFn_mk, Int.toNat_natCast]

end Expansion

/-! ## The descent to a symmetric functional on `A(𝒱)` -/

section Descent

variable (W : VertexOperatorAlgebra 𝒱)

/-- **DLM (10.6) / Zhu Lemma 2.1.3** — the square-bracket zero mode is the round-bracket Zhu
commutator modulo `O(𝒱)`.  Carried as named data: a classical lemma of Zhu's theory, and **not**
an open target. -/
def ZhuCommutatorLaw : Prop :=
  ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱,
    zhuMul W a v - zhuMul W v a - vSqZ W a ka 0 v ∈ O W

/-- `𝒱₀` is spanned by the vacuum.  ⚠ This is **automatic**: the `VertexOperatorAlgebra` axiom
`vacuum_grade : W.grading 0 = span {vacuum}` gives it for every `W`
(`QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade`, `Modularity/AKSl2Payoff.lean`).  So a hypothesis
`hzero : VacuumGradeZero W` is always redundant. -/
def VacuumGradeZero : Prop := W.grading 0 ≤ Submodule.span ℂ ({W.vacuum} : Set 𝒱)

/-- **`VacuumGradeZero` holds for every VOA**: it is the field `vacuum_grade` weakened from `=` to
`≤`. So a hypothesis `hzero : VacuumGradeZero W` is always discharged by this. -/
theorem vacuumGradeZero_holds : VacuumGradeZero W := le_of_eq W.vacuum_grade

variable {W}

/-! ### `ZhuCommutatorLaw` is a THEOREM

`Modules.ZhuVermaAnArchDLM3Zero.zhu_comm_mod_O` already proves Zhu's Lemma 2.1(iii) in the form
`u * v − v * u − Res_z(1+z)^{K−1}Y(u,z)v ∈ O(𝒱)`, and `Modularity.ZhuRecursionProof.cbz_eq_
sqBracketCoeffZ_zero` identifies that residue's binomials with the square-bracket coefficients.  So
the two sides literally coincide. -/

/-- **The square-bracket zero mode IS the Frenkel–Zhu residue** `Res_z (1+z)^{k−1}Y(a,z)v`. -/
theorem vSqZ_zero_eq_resFull (W : VertexOperatorAlgebra 𝒱) {k : ℕ} (hk : 1 ≤ k) (a v : 𝒱) :
    vSqZ W a k 0 v = resFull W ((k : ℤ) - 1) 0 a v := by
  rw [vSqZ_apply, resFull]
  refine finsum_congr (fun ℓ => ?_)
  rw [add_zero, cbz_eq_sqBracketCoeffZ_zero k hk ℓ]
  rfl

/-- **DLM (10.6) / Zhu Lemma 2.1(iii)**, unconditionally. -/
theorem zhuCommutatorLaw_holds (W : VertexOperatorAlgebra 𝒱) : ZhuCommutatorLaw W := by
  intro k hk a ha v
  refine reduce_homogeneous W
    (P := fun v => zhuMul W a v - zhuMul W v a - vSqZ W a k 0 v ∈ O W) ?_ ?_ ?_ v
  · intro M w hw
    rcases lt_or_ge M 0 with hM | hM
    · have hw0 : w = 0 := by
        rw [W.positivity M hM] at hw
        simpa using hw
      subst hw0
      simpa using (O W).zero_mem
    · have hMn : w ∈ W.grading ((M.toNat : ℕ) : ℤ) := by
        rwa [show ((M.toNat : ℕ) : ℤ) = M from by omega]
      rw [vSqZ_zero_eq_resFull W hk]
      exact zhu_comm_mod_O W ha hMn
  · simpa using (O W).zero_mem
  · intro x y hx hy
    have hrw : zhuMul W a (x + y) - zhuMul W (x + y) a - vSqZ W a k 0 (x + y)
        = (zhuMul W a x - zhuMul W x a - vSqZ W a k 0 x)
          + (zhuMul W a y - zhuMul W y a - vSqZ W a k 0 y) := by
      rw [zhuMul_add_right, zhuMul_add_left, map_add]
      abel
    rw [hrw]
    exact (O W).add_mem hx hy

/-- Multiples of the vacuum are central for the Zhu product. -/
theorem zhuMul_comm_of_mem_span_vacuum {a : 𝒱}
    (h : a ∈ Submodule.span ℂ ({W.vacuum} : Set 𝒱)) (v : 𝒱) :
    zhuMul W a v = zhuMul W v a := by
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨c, rfl⟩ := h
  rw [zhuMul_smul_left, zhuMul_vacuum_left, zhuMul_smul_right, zhuMul_vacuum_right]

/-- **A functional killing `O(𝒱)` and every `a[0]v` is symmetric for the Zhu product.** -/
theorem phi_zhuMul_comm (hzero : VacuumGradeZero W)
    {φ : 𝒱 →ₗ[ℂ] ℂ} (hO : O W ≤ LinearMap.ker φ)
    (hvan : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱, φ (vSqZ W a ka 0 v) = 0)
    (u v : 𝒱) : φ (zhuMul W u v) = φ (zhuMul W v u) := by
  classical
  refine reduce_homogeneous W (P := fun u => φ (zhuMul W u v) = φ (zhuMul W v u)) ?_ ?_ ?_ u
  · intro k a ha
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have : a = 0 := by
        have := W.positivity k hk
        rw [this] at ha
        simpa using ha
      subst this
      rw [zhuMul_zero_left, zhuMul_zero_right]
    · subst hk
      rw [zhuMul_comm_of_mem_span_vacuum (hzero ha) v]
    · have hka : 1 ≤ k.toNat := by omega
      have hak : a ∈ W.grading ((k.toNat : ℕ) : ℤ) := by
        rwa [show ((k.toNat : ℕ) : ℤ) = k from by omega]
      have hmem := zhuCommutatorLaw_holds W k.toNat hka a hak v
      have hker : φ (zhuMul W a v - zhuMul W v a - vSqZ W a k.toNat 0 v) = 0 := hO hmem
      rw [map_sub, map_sub, hvan k.toNat hka a hak v, sub_zero, sub_eq_zero] at hker
      exact hker
  · show φ (zhuMul W 0 v) = φ (zhuMul W v 0)
    rw [zhuMul_zero_left, zhuMul_zero_right]
  · intro x y hx hy
    rw [zhuMul_add_left, zhuMul_add_right, map_add, map_add, hx, hy]

/-- **The induced functional on `A(𝒱)` is SYMMETRIC** — the object counted by
`finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix`. -/
theorem symmetricFunctional_of_zeroModeVanishing (hzero : VacuumGradeZero W)
    {φ : 𝒱 →ₗ[ℂ] ℂ} (hO : O W ≤ LinearMap.ker φ)
    (hvan : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱, φ (vSqZ W a ka 0 v) = 0) :
    letI := instRingA W
    letI := instAlgebraA W
    Submodule.liftQ (O W) φ hO ∈ symmetricFunctionals ℂ (A W) := by
  letI := instRingA W
  letI := instAlgebraA W
  intro p q
  obtain ⟨x, rfl⟩ := mk_surjective W p
  obtain ⟨y, rfl⟩ := mk_surjective W q
  have hmul : ∀ s t : 𝒱, Submodule.liftQ (O W) φ hO (mk W s * mk W t) = φ (zhuMul W s t) := by
    intro s t
    rw [AsRing_mul_eq, Amul_mk]
    rfl
  rw [hmul, hmul]
  exact phi_zhuMul_comm hzero hO hvan x y

end Descent

end VOA
