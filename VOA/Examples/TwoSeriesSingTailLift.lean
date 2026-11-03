/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesTailWitt

/-!
# The test without the jet ideal is sharp in every `T`-degree

For a `T`-polynomial `F` write `F(J + x̃)` for its image under `T_m ↦ J_m + x_{m+1}` in
`ℂ[u_j, v_j]`.  The test space of `TwoSeriesMembershipTest` asks that `F(J + x̃) · v₀^{2N}` lie in
the span of products of `r` jets of `u², uv, v²` **modulo the jets of `(J + x̃)ⁿ`**.  This file
separates the two ingredients.

* `vars_lt_of_mem_Lpoly_pow` — **without the ideal the test is sharp in every `T`-degree**:
  if `F` is homogeneous of `T`-degree `k` and `F(J + x̃) · v₀^{2N}` is a combination of products of
  `N + k` letters, then every jet `T_m` occurring in `F` has `m < N`.  The proof is the
  dual-number specialisation `chi` of `TwoSeriesInclLow`, applied with no ideal to absorb, so the
  restriction `k < n` of `InclLow.boxInclusion_low` disappears.
* `mem_boxW_of_mem_Lpoly_pow` — hence `F` lies in the box of `ℂ[T_j]`.

So the only obstruction in the tail of `BoxInclusion` is the jet ideal: the remaining question
is whether a test-passing element of `R_n` has a lift for which the ideal is not needed.

* `SingularLift n r` — **the ideal-elimination input**, for Witt-singular test-passing
  elements only: such a `τ` (in a slot with `T`-degree `r - N ≥ n`) has a lift `F ∈ ℂ[T_j]`,
  homogeneous of the same degree and weight, with `F(J + x̃) · v₀^{2N}` a combination of products
  of `r` letters (no ideal);
* `boxSingularTail_of_singularLift` — `SingularLift n r → BoxSingularTail n r`;
* `twoSeries_gradedUnitary_of_strictModel_singularLift` — the endpoint with that input.

Numerically (exact linear algebra mod `p = 1000003`, scripts not in the repository, not a proof): the products of
the `T_m` with `m < N`, times `v₀^{2N}`, already lie in the span of products of `N + k` letters
with no ideal (every box monomial tested, `N ≤ 4`, `k ≤ 4`, lowest weights), so on the tested
range `SingularLift` is equivalent to `BoxSingularTail`: it is a reformulation that isolates the
ideal, not a weakening.  The `r = n` case is proved in `TwoSeriesSingTailDiag`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section


namespace SingTailLift

open InclLow TailWitt

/-- The letters-only test implies the test of every level `n`. -/
theorem mem_testLetters_of_Lpoly (n r N : ℕ) {F : TPoly}
    (hL : aeval tco F * X (1, 0) ^ (2 * N) ∈ Lpoly ^ r) :
    ψn n (Ideal.Quotient.mk (jetIdealT n) F) * tmk n (X (1, 0)) ^ (2 * N) ∈
      testLetters n ^ r := by
  rw [ψn_mk, ← map_pow, ← map_mul, testLetters_eq, ← Submodule.map_pow]
  exact Submodule.mem_map_of_mem hL

/-- **The letters-only test is sharp in every `T`-degree**: if `F` is homogeneous of `T`-degree
`k` and `F(J + x̃) · v₀^{2N}` is a combination of products of `N + k` letters, then `F` only
involves the jets `T_m` with `m < N`. -/
theorem vars_lt_of_mem_Lpoly_pow {N k : ℕ} {e : ℤ} {F : TPoly} (hF : F ∈ tMonW TPoly X k e)
    (hL : aeval tco F * X (1, 0) ^ (2 * N) ∈ Lpoly ^ (N + k)) : ∀ m ∈ F.vars, m < N := by
  have hT := mem_testLetters_of_Lpoly (k + 1) (N + k) N hL
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0, hm0N⟩ := hcon
  have hne : F.vars.Nonempty := ⟨m0, hm0⟩
  have hMmem : F.vars.max' hne ∈ F.vars := Finset.max'_mem _ _
  have hMle : ∀ m ∈ F.vars, m ≤ F.vars.max' hne := fun m hm => Finset.le_max' _ _ hm
  have hNM : N ≤ F.vars.max' hne := le_trans hm0N (hMle m0 hm0)
  have hFV : F ∈ InclLead.V (F.vars.max' hne) k := by
    have := cut_tMonW_le_V (F.vars.max' hne) k e (Submodule.mem_map.mpr ⟨F, hF, rfl⟩)
    rwa [AlgHom.toLinearMap_apply, cut_eq_self (fun m hm => hMle m hm)] at this
  obtain ⟨-, hlead⟩ :=
    InclLead.lead_span Aco Bco natDegree_Aco natDegree_Bco coeff_Bco hFV
  have h0 := piA_coeff_eq_zero (Nat.lt_succ_self k) hF hT (D := k + F.vars.max' hne)
    (by omega)
  rw [hlead, map_mul, map_pow, map_neg, map_one] at h0
  have hsq : piA (aeval (InclLead.sb Aco) (pderiv (F.vars.max' hne) F)) =
      InclLead.sqMap (pderiv (F.vars.max' hne) F) := by
    rw [MvPolynomial.comp_aeval_apply, InclLead.sqMap]
    exact congrArg (fun g : ℕ → MvPolynomial ℕ ℂ => aeval g (pderiv (F.vars.max' hne) F))
      (funext piA_sb)
  rw [hsq] at h0
  have hpd : InclLead.sqMap (pderiv (F.vars.max' hne) F) = 0 :=
    (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact InclLead.not_mem_vars_of_pderiv_eq_zero
    (InclLead.aeval_sq_injective (hpd.trans (map_zero _).symm)) hMmem

/-- **The letters-only test puts `F` in the box of `ℂ[T_j]`.** -/
theorem mem_boxW_of_mem_Lpoly_pow {N k : ℕ} {e : ℤ} {F : TPoly} (hF : F ∈ tMonW TPoly X k e)
    (hL : aeval tco F * X (1, 0) ^ (2 * N) ∈ Lpoly ^ (N + k)) : F ∈ boxW X N k e := by
  have := cut_tMonW_le_boxW N k e (Submodule.mem_map.mpr ⟨F, hF, rfl⟩)
  rwa [AlgHom.toLinearMap_apply, cut_eq_self (vars_lt_of_mem_Lpoly_pow hF hL)] at this

end SingTailLift

open SingTailLift TailWitt

/-- **The ideal-elimination input** (Witt-singular part): in every slot of `T`-degree
`r - N ≥ n`, a test-passing `τ ∈ R_n` whose images under all positive Witt operators lie in the
box has a lift `F ∈ ℂ[T_j]`, homogeneous of `T`-degree `r - N` and weight `d - r`, for which the
jet ideal is not needed: `F(J + x̃) · v₀^{2N}` is a combination of products of `r` letters. -/
def SingularLift (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → n ≤ r - N → ∀ τ : Rn n,
    τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N →
    (∀ j : ℕ, 1 ≤ j → dR n j τ ∈ boxW (tn n) N (r - N) (d - r - j)) →
    ∃ F ∈ tMonW TPoly X (r - N) (d - r), Ideal.Quotient.mk (jetIdealT n) F = τ ∧
      aeval tco F * X (1, 0) ^ (2 * N) ∈ InclLow.Lpoly ^ r

/-- **`BoxSingularTail` from ideal elimination.** -/
theorem boxSingularTail_of_singularLift {n r : ℕ} (h : SingularLift n r) :
    BoxSingularTail n r := by
  intro d N hN hk τ hτ hsing
  obtain ⟨F, hF, rfl, hL⟩ := h d N hN hk τ hτ hsing
  have hL' : aeval tco F * X (1, 0) ^ (2 * N) ∈ InclLow.Lpoly ^ (N + (r - N)) := by
    rwa [show N + (r - N) = r by omega]
  exact InclLow.boxW_map n N (r - N) (d - r)
    (Submodule.mem_map.mpr ⟨F, mem_boxW_of_mem_Lpoly_pow hF hL', rfl⟩)

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the ideal-elimination input `SingularLift`. -/
theorem twoSeries_gradedUnitary_of_strictModel_singularLift (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (lift : ∀ r, SingularLift n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_singular n hn hA det fun r =>
    boxSingularTail_of_singularLift (lift r)

end

end VOA.TwoSeries.StrictModel
