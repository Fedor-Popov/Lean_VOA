/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxTwo

/-!
# `BoxCount n` from a statement about symmetric polynomials alone

The reversed monomial map `Psi n N m : ℂ[y_1, …, y_m] → R_n` (`y^β ↦ Π_i T_{N-1-β_i}`) carries
the symmetric polynomials of degree `D` onto a space containing the box image of weight
`m N - D`, and it kills

* `h_q · g` for `q > (n-1) N - m` (`Psi_hh_mul_eq_zero`, the truncated-product relations of
  `R_n`), and
* every monomial with an exponent `≥ N` (by definition).

So the counting half `BoxCount n r` follows from a bound on a quotient of symmetric polynomials
that does not mention `R_n`:

* `boxRel n N m` — the span of those two kinds of polynomials;
* `symDeg m D` — the symmetric polynomials homogeneous of degree `D`;
* `SymBoxBound n` — *for `m ≥ 1`, the degree-`D` symmetric polynomials in `m` variables modulo
  `boxRel n N m` span a space of dimension at most the number of socle words with `N` letters,
  size `N + m` and degree `N + m + m N - D`* (**proved for every `n ≥ 1`** in
  `TwoSeriesBoxFusion`, `symBoxBound`);
* `Psi_boxRel` — `Psi` kills `boxRel`;
* `boxCount_of_symBoxBound` — `SymBoxBound n → ∀ r, BoxCount n r`;
* `twoSeries_gradedUnitary_of_strictModel_symBox` — the endpoint with the counting half
  replaced by `SymBoxBound n`.

`SymBoxBound n` is the graded weight-space count of the fusion product of `N` copies of the
`n`-dimensional `sl₂`-module (the quotient is that weight space, in the symmetric-function
presentation).  Numerically (exact linear algebra mod `p = 1000003`, not a proof) the quotient has
**exactly** the socle-word dimension in every slot tested: `n = 2` (`N ≤ 5`, `m ≤ 4`), `n = 3`
(`N ≤ 4`, `m ≤ 5`), `n = 4` (`N ≤ 3`, `m ≤ 5`).  The bound is proved for every `n ≥ 1` in
`TwoSeriesBoxFusion` (the fusion recursion); for `n = 2` there is also the direct Grassmannian
proof `boxCount_two` in `TwoSeriesBoxTwo`.

Everything here is proved outright from the stated hypotheses.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SocleEval
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-- The relations of the box quotient: `h_q · g` with `(n-1) N < q + m`, and the monomials with
an exponent `≥ N`. -/
def boxRel (n N m : ℕ) : Submodule ℂ (MvPolynomial (Fin m) ℂ) :=
  Submodule.span ℂ ({x | ∃ q g, (n - 1) * N < q + m ∧ x = hh m q * g} ∪
    {x | ∃ (β : Fin m →₀ ℕ) (c : ℂ), (∃ i, N ≤ β i) ∧ x = monomial β c})

/-- **`Psi` kills the box relations.** -/
theorem Psi_boxRel {n N m : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ boxRel n N m) :
    Psi n N m x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨q, g, hq, rfl⟩ | ⟨β, c, ⟨i, hi⟩, rfl⟩
    · exact Psi_hh_mul_eq_zero q hq g
    · rw [Psi_monomial, psiMono, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (by omega)),
        smul_zero]
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

/-- The symmetric polynomials homogeneous of degree `D`. -/
def symDeg (m D : ℕ) : Submodule ℂ (MvPolynomial (Fin m) ℂ) :=
  Subalgebra.toSubmodule (symmetricSubalgebra (Fin m) ℂ) ⊓ homogeneousSubmodule (Fin m) ℂ D

/-- **The remaining input for general `n`, in plain words**: for `m ≥ 1`, the degree-`D`
symmetric polynomials in `m` variables, modulo the products `h_q · g` (`q > (n-1) N - m`) and the
monomials with an exponent `≥ N`, span a space of dimension at most the number of socle words
with `N` letters, size `N + m` and degree `N + m + m N - D`. -/
def SymBoxBound (n : ℕ) : Prop :=
  ∀ N m D : ℕ, 1 ≤ m →
    Module.rank ℂ (↥(symDeg m D) ⧸ (boxRel n N m).comap (symDeg m D).subtype) ≤
      socleCount n (N + m) (((N + m + m * N : ℕ) : ℤ) - D) N

theorem OS_mem_symDeg (k : ℕ) (β : Fin k →₀ ℕ) : OS k β ∈ symDeg k (Finsupp.degree β) :=
  ⟨(mem_symmetricSubalgebra _).mpr (OS_isSymmetric k β),
    (mem_homogeneousSubmodule _ _).mpr (OS_isHomogeneous k β)⟩

theorem psiMono_mem_range {n N k : ℕ} (β : Fin k →₀ ℕ) :
    psiMono n N β ∈ LinearMap.range
      ((Psi n N k).comp (symDeg k (Finsupp.degree β)).subtype) := by
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  refine ⟨((k.factorial : ℕ) : ℂ)⁻¹ • ⟨OS k β, OS_mem_symDeg k β⟩, ?_⟩
  rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, Psi_OS, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

/-- **The counting half from the symmetric-polynomial bound.** -/
theorem boxCount_of_symBoxBound {n : ℕ} (h : SymBoxBound n) (r : ℕ) : BoxCount n r := by
  intro d N hN
  set k := r - N with hk
  have hk1 : 1 ≤ k := by omega
  have hr : r = N + k := by omega
  by_cases hD : 0 ≤ (k : ℤ) * N - (d - (r : ℕ))
  · obtain ⟨D, hDeq⟩ : ∃ D : ℕ, (D : ℤ) = (k : ℤ) * N - (d - (r : ℕ)) :=
      ⟨_, Int.toNat_of_nonneg hD⟩
    set f := (Psi n N k).comp (symDeg k D).subtype with hf
    have hle : boxW (tn n) N k (d - (r : ℕ)) ≤ LinearMap.range f := by
      refine (boxW_le_span_psiMono n N k _).trans ?_
      rw [Submodule.span_le]
      rintro _ ⟨β, ⟨-, hβ⟩, rfl⟩
      have hdeg : Finsupp.degree β = D := by
        have : ((Finsupp.degree β : ℕ) : ℤ) = D := by rw [hDeq]; linarith
        exact_mod_cast this
      have := psiMono_mem_range (n := n) (N := N) β
      rwa [hdeg] at this
    have hker : (boxRel n N k).comap (symDeg k D).subtype ≤ LinearMap.ker f := by
      intro x hx
      rw [Submodule.mem_comap] at hx
      rw [LinearMap.mem_ker, hf, LinearMap.comp_apply]
      exact Psi_boxRel hx
    have hrange : LinearMap.range f =
        LinearMap.range (((boxRel n N k).comap (symDeg k D).subtype).liftQ f hker) := by
      rw [Submodule.range_liftQ]
    refine (Submodule.rank_mono hle).trans ?_
    rw [hrange]
    refine (rank_range_le _).trans ((h N k D hk1).trans (le_of_eq ?_))
    have h2 : (((N + k + k * N : ℕ) : ℤ) - D) = d := by
      rw [hDeq, hr]
      push_cast
      ring
    rw [h2, show N + k = r by omega]
  · have hbot : boxW (tn n) N k (d - (r : ℕ)) = ⊥ := by
      rw [eq_bot_iff]
      refine (boxW_le_span_psiMono n N k _).trans ?_
      rw [Submodule.span_le]
      rintro _ ⟨β, ⟨-, hβ⟩, rfl⟩
      exfalso
      apply hD
      have : (0 : ℤ) ≤ ((Finsupp.degree β : ℕ) : ℤ) := by positivity
      linarith
    rw [hbot, rank_bot]
    exact zero_le

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional on `hA`,
detection `det`, the structural half `BoxInclusion`, and the symmetric-polynomial bound
`SymBoxBound n` (proved for `n = 2` in the form `boxCount_two`). -/
theorem twoSeries_gradedUnitary_of_strictModel_symBox (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (incl : ∀ r, BoxInclusion n r) (hS : SymBoxBound n) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_box n hn hA det incl (boxCount_of_symBoxBound hS)

end

end VOA.TwoSeries.StrictModel
