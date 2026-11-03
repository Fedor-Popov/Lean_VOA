/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficientwise locally finite sums of formal power series

An infinite sum of formal power series is algebraic data only when every coefficient receives
finitely many nonzero contributions.  This file packages that condition and the corresponding
coefficientwise `finsum`.  No topology or analytic convergence is involved.

The intended application is a fermionic character: its summands are indexed by occupation
profiles or descending tail-count chains.  Reindexing those profiles by an equivalence is then a
literal equality of formal series.
-/

namespace VOA.LocallyFinitePowerSeriesSum

open scoped BigOperators

noncomputable section

universe u v w

variable {R : Type u} [Semiring R]
variable {ι : Type v} {κ : Type w}

/-- Every coefficient of the family has finite support in the summand index. -/
def IsCoefficientwiseFinite (F : ι → PowerSeries R) : Prop :=
  ∀ n, (Function.support fun i => PowerSeries.coeff n (F i)).Finite

/-- A finite coefficientwise bounding set is enough to prove local finiteness.  In fermionic
applications the bounding set consists of the profiles whose conductor is at most `n`. -/
theorem isCoefficientwiseFinite_of_mem_finset (F : ι → PowerSeries R)
    (bound : ℕ → Finset ι)
    (hbound : ∀ n i, PowerSeries.coeff n (F i) ≠ 0 → i ∈ bound n) :
    IsCoefficientwiseFinite F := by
  intro n
  exact (bound n).finite_toSet.subset fun i hi => hbound n i hi

/-- Sum a family of formal power series coefficientwise.  Mathematical uses should separately
provide `IsCoefficientwiseFinite F`; keeping the sum itself total makes reindexing transparent. -/
def sum (F : ι → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ᶠ i, PowerSeries.coeff n (F i)

@[simp]
theorem coeff_sum (F : ι → PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (sum F) = ∑ᶠ i, PowerSeries.coeff n (F i) := by
  rw [sum, PowerSeries.coeff_mk]

/-- Coefficientwise finite support is preserved by an equivalence of index types. -/
theorem isCoefficientwiseFinite_comp_equiv (e : κ ≃ ι) (F : ι → PowerSeries R)
    (hF : IsCoefficientwiseFinite F) :
    IsCoefficientwiseFinite (fun k => F (e k)) := by
  intro n
  have hsupport :
      Function.support (fun k => PowerSeries.coeff n (F (e k))) =
        e ⁻¹' Function.support (fun i => PowerSeries.coeff n (F i)) := by
    ext k
    rfl
  rw [hsupport]
  exact (hF n).preimage e.injective.injOn

/-- Coefficientwise sums are invariant under an arbitrary equivalence of summand indices. -/
theorem sum_comp_equiv (e : κ ≃ ι) (F : ι → PowerSeries R) :
    sum (fun k => F (e k)) = sum F := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_sum]
  exact finsum_comp_equiv (M := R) e
    (f := fun i => PowerSeries.coeff n (F i))

/-- For a finite index type, the coefficientwise sum is the ordinary finite sum. -/
theorem sum_eq_finset_sum [Fintype ι] (F : ι → PowerSeries R) :
    sum F = ∑ i, F i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_sum, finsum_eq_sum_of_fintype]
  exact (map_sum (PowerSeries.coeff (R := R) n) F Finset.univ).symm

/-- Pointwise equality of summands gives equality of coefficientwise sums. -/
theorem sum_congr {F G : ι → PowerSeries R} (h : ∀ i, F i = G i) :
    sum F = sum G := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_sum]
  exact finsum_congr fun i => by rw [h i]

end

end VOA.LocallyFinitePowerSeriesSum
