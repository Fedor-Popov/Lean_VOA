/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPolyStructure
import VOA.Examples.VirasoroGradedField

/-!
# All vertex operators of `V(c,0)` have structure constants polynomial in `c`

This is step 2 of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`). Step 1
(`VirasoroPolyStructure`) treated the Virasoro modes `L_m`. This file treats the modes `u₍ₙ₎` of every
state `u`.

A family of operators `T c : End (VirUniv c)` is `PolyOp` when, for every creation word `w`, one
`c`-independent `P : List ℕ →₀ ℂ[X]` gives `T c (L₋w|0⟩) = polyComb c P` at every `c`.

* `PolyOp` is closed under composition, sums and scalars, and contains every `L_m`.
* `polyOp_nprod`: the normal-ordered product of two graded fields with `PolyOp` coefficients has
  `PolyOp` coefficients. On a word of energy `E`, the defining sum is supported in a finite range
  of indices that depends only on `E`, the field weights and `s`. It never depends on `c`, because
  negative energy spaces vanish (`gradingVir_neg`).
* `polyOp_YwordVir`: every coefficient of every word field `YwordVir c ws` is `PolyOp`.
* `exists_sorted_polyComb_mode`: for creation words `u`, `w` and any `n`, the product
  `u₍ₙ₎ w = mode (virYA c u) n w` has a `c`-uniform expansion in the sorted basis with polynomial
  coefficients. By `polyComb_injective`, that expansion is unique.

So, transported to the `c`-free sorted basis, all structure constants of `V(c,0)` are polynomials in
`c`. The next step of the route is to differentiate at `c` and prove the order-`t` Jacobi identity.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

/-- A `c`-family of operators whose matrix on creation words is polynomial in `c`. -/
def PolyOp (T : ∀ c : ℂ, Module.End ℂ (VirUniv c)) : Prop :=
  ∀ w : List ℕ, ∃ P : List ℕ →₀ ℂ[X], ∀ c : ℂ, T c (negWordVir c w) = polyComb c P

theorem PolyOp.apply {T : ∀ c : ℂ, Module.End ℂ (VirUniv c)} (hT : PolyOp T)
    (P : List ℕ →₀ ℂ[X]) : ∃ Q : List ℕ →₀ ℂ[X], ∀ c : ℂ, T c (polyComb c P) = polyComb c Q := by
  induction P using Finsupp.induction_linear with
  | zero => exact ⟨0, fun c => by simp⟩
  | add P Q hP hQ =>
      obtain ⟨P', hP'⟩ := hP
      obtain ⟨Q', hQ'⟩ := hQ
      exact ⟨P' + Q', fun c => by rw [map_add, map_add, hP', hQ', map_add]⟩
  | single u p =>
      obtain ⟨Q, hQ⟩ := hT u
      exact ⟨p • Q, fun c => by rw [polyComb_single, map_smul, hQ, polyComb_smul]⟩

theorem PolyOp.comp {S T : ∀ c : ℂ, Module.End ℂ (VirUniv c)} (hS : PolyOp S) (hT : PolyOp T) :
    PolyOp fun c => S c * T c := fun w => by
  obtain ⟨P, hP⟩ := hT w
  obtain ⟨Q, hQ⟩ := hS.apply P
  exact ⟨Q, fun c => by rw [Module.End.mul_apply, hP, hQ]⟩

theorem PolyOp.smul {T : ∀ c : ℂ, Module.End ℂ (VirUniv c)} (a : ℂ) (hT : PolyOp T) :
    PolyOp fun c => a • T c := fun w => by
  obtain ⟨P, hP⟩ := hT w
  exact ⟨Polynomial.C a • P, fun c => by rw [LinearMap.smul_apply, hP, polyComb_smul, eval_C]⟩

theorem polyOp_zero : PolyOp fun c => (0 : Module.End ℂ (VirUniv c)) :=
  fun _ => ⟨0, fun c => by simp⟩

theorem polyOp_id : PolyOp fun c => (LinearMap.id : Module.End ℂ (VirUniv c)) :=
  fun w => ⟨Finsupp.single w 1, fun c => by simp⟩

theorem polyOp_Lop (m : ℤ) : PolyOp fun c => Lop c m := fun w => exists_polyComb_Lop w m

/-- The coefficients of `∂^i Y(ω,z)`. -/
theorem polyOp_deriv_iterate (i : ℕ) :
    ∀ t : ℤ, PolyOp fun c => (VOA.deriv^[i] (YomegaVir c)) t := by
  induction i with
  | zero => intro t; exact polyOp_Lop (-t - 2)
  | succ i ih =>
      intro t
      have h := (ih (t + 1)).smul ((t + 1 : ℤ) : ℂ)
      refine fun w => (h w).imp fun P hP c => ?_
      rw [← hP c]
      show (VOA.deriv^[i + 1] (YomegaVir c)) t (negWordVir c w)
        = (((t + 1 : ℤ) : ℂ) • (VOA.deriv^[i] (YomegaVir c)) (t + 1)) (negWordVir c w)
      rw [Function.iterate_succ_apply', deriv_apply, Int.cast_smul_eq_zsmul]

theorem polyOp_genFieldVir (i : ℕ) (t : ℤ) : PolyOp fun c => genFieldVir c i t :=
  ((polyOp_deriv_iterate i t).smul ((i.factorial : ℂ)⁻¹))

theorem polyOp_idFieldVir (t : ℤ) : PolyOp fun c => idFieldVir c t := by
  by_cases ht : t = 0
  · simpa [idFieldVir, ht] using polyOp_id
  · simpa [idFieldVir, ht] using polyOp_zero

/-! ## §1  Normal-ordered products -/

theorem eq_zero_of_mem_neg {c : ℂ} {q : ℤ} (hq : q < 0) {x : VirUniv c}
    (hx : x ∈ gradingVir c q) : x = 0 := by
  rw [gradingVir_neg c q hq] at hx
  exact (Submodule.mem_bot ℂ).mp hx

/-- The normal-ordered product of graded fields with polynomial coefficients has polynomial
coefficients. -/
theorem polyOp_nprod {a b : ∀ c : ℂ, FormalDist (Module.End ℂ (VirUniv c))}
    (ha : ∀ c, IsField (a c)) (hb : ∀ c, IsField (b c)) {ka kb : ℤ} (hka : 0 ≤ ka)
    (hga : ∀ c, GradedFieldVir c (a c) ka) (hgb : ∀ c, GradedFieldVir c (b c) kb)
    (hpa : ∀ t, PolyOp fun c => a c t) (hpb : ∀ t, PolyOp fun c => b c t) (s : ℤ) :
    PolyOp fun c => nprod (ha c) (hb c) s := by
  classical
  intro w
  set E : ℤ := (energyVir w : ℤ)
  have hE : 0 ≤ E := by positivity
  let S : Finset ℤ := Finset.Icc (-(E + ka)) (E + kb + s) ∪ Finset.Icc (-(E + ka)) 0
  -- each normal-ordered term is `PolyOp`
  have hterm : ∀ m : ℤ, PolyOp fun c => normalOrdered (a c) (b c) m (s - m) := by
    intro m
    by_cases hm : 0 ≤ m
    · simpa [normalOrdered, hm] using (hpa m).comp (hpb (s - m))
    · simpa [normalOrdered, hm] using (hpb (s - m)).comp (hpa m)
  choose P hP using fun m => hterm m w
  refine ⟨∑ m ∈ S, P m, fun c => ?_⟩
  have hx := negWord_mem_gradingVir c w
  have hsupp : (Function.support fun m : ℤ =>
      normalOrdered (a c) (b c) m (s - m) (negWordVir c w)) ⊆ S := by
    intro m hm
    rw [Function.mem_support] at hm
    by_contra hmS
    simp only [S, Finset.coe_union, Finset.coe_Icc, Set.mem_union, Set.mem_Icc, not_or,
      not_and_or, not_le] at hmS
    apply hm
    by_cases h0 : 0 ≤ m
    · simp only [normalOrdered, h0, if_true, Module.End.mul_apply]
      have hb0 : b c (s - m) (negWordVir c w) = 0 :=
        eq_zero_of_mem_neg (by omega) (hgb c (s - m) _ _ hx)
      rw [hb0, map_zero]
    · simp only [normalOrdered, h0, if_false, Module.End.mul_apply]
      have ha0 : a c m (negWordVir c w) = 0 :=
        eq_zero_of_mem_neg (by omega) (hga c m _ _ hx)
      rw [ha0, map_zero]
  rw [nprod_apply, finsum_eq_sum_of_support_subset _ hsupp, map_sum]
  exact Finset.sum_congr rfl fun m _ => hP m c

/-! ## §2  All word fields, and all modes -/

/-- Every coefficient of every word field is `PolyOp`. -/
theorem polyOp_YwordVir (ws : List ℕ) : ∀ t : ℤ, PolyOp fun c => YwordVir c ws t := by
  induction ws with
  | nil => intro t; simpa using polyOp_idFieldVir t
  | cons i rest ih =>
      intro t
      exact polyOp_nprod (fun c => genFieldVir_isField c i) (fun c => YwordVir_isField c rest)
        (by positivity) (fun c => genFieldVir_gradedField c i)
        (fun c => YwordVir_gradedField c rest) (polyOp_genFieldVir i) ih t

/-- Any polynomial combination can be re-expressed in the sorted basis, uniformly in `c`. -/
theorem exists_sorted_of_polyComb (P : List ℕ →₀ ℂ[X]) :
    ∃ Q, Sorted Q ∧ ∀ c : ℂ, polyComb c P = polyComb c Q := by
  classical
  have hch : ∀ u : P.support, ∃ Q, SortedSupp (energyVir u.1) Q ∧
      ∀ c : ℂ, negWordVir c u.1 = polyComb c Q := fun u => exists_sorted_polyComb u.1
  choose Q hQ hQe using hch
  refine ⟨∑ u ∈ P.support.attach, P u.1 • Q u, fun v hv => ?_, fun c => ?_⟩
  · obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hv)
    exact (hQ u v (Finsupp.support_smul hu)).1
  · rw [polyComb_eq_sum, map_sum, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [polyComb_smul, ← hQe u c]

/-- **The structure constants of `V(c,0)` are polynomial in `c`.** For creation words `u`, `w`
and a mode `n`, there is one `c`-independent sorted family `P` of polynomials with
`u₍ₙ₎ w = Σ_v P_v(c) L₋ᵥ|0⟩` at every central charge. -/
theorem exists_sorted_polyComb_mode (u w : List ℕ) (n : ℤ) :
    ∃ P, Sorted P ∧ ∀ c : ℂ,
      mode (virYA c (negWordVir c u)) n (negWordVir c w) = polyComb c P := by
  obtain ⟨P, hP⟩ := polyOp_YwordVir u (-n - 1) w
  obtain ⟨Q, hQ, hQe⟩ := exists_sorted_of_polyComb P
  refine ⟨Q, hQ, fun c => ?_⟩
  rw [virYA_word, mode_apply, hP c, hQe c]

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.polyOp_nprod
#print axioms VOA.VirPoly.polyOp_YwordVir
#print axioms VOA.VirPoly.exists_sorted_polyComb_mode
end AxiomAudit
