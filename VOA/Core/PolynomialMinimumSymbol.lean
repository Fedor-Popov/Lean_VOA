/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.PolynomialMinimumWeight

/-!
# Independence from minimum-weight polynomial symbols

A finite dependence has a least occupied signed weight. Projection to
that homogeneous component isolates a dependence of its proposed symbols.
Thus independent lowest symbols imply independence without a uniform
bound on the weights or on the number of variables.
-/
namespace VOA.PolynomialMinimum
noncomputable section
open MvPolynomial
variable {σ : Type*} {w : σ → ℤ}

/-- The polynomial Q is homogeneous of weight d and agrees with P
modulo terms of strictly larger weight. -/
structure Symbol (w : σ → ℤ) (d : ℤ) (P Q : MvPolynomial σ ℂ) : Prop where
  homogeneous : Q.IsWeightedHomogeneous w d
  remainder : P-Q ∈ AtLeast w (d+1)

/-- A minimum symbol bounds the weight of the whole polynomial below. -/
theorem Symbol.bound {d : ℤ} {P Q : MvPolynomial σ ℂ} (h : Symbol w d P Q) :
    P ∈ AtLeast w d := by
  have he := mono (show d≤d+1 by omega) h.remainder
  simpa using (AtLeast w d).add_mem he (homogeneous_mem h.homogeneous)

/-- The indicated homogeneous component is exactly the symbol. -/
theorem Symbol.component {d : ℤ} {P Q : MvPolynomial σ ℂ} (h : Symbol w d P Q) :
    weightedHomogeneousComponent w d P=Q := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with he
  · have hr : coeff e (P-Q)=0 := by
      by_contra hc
      have hb := (mem_iff _).mp h.remainder e hc
      rw [he] at hb
      omega
    simpa only [coeff_sub,sub_eq_zero] using hr
  · exact (h.homogeneous.coeff_eq_zero e he).symm

/-- Independent minimum symbols imply independent polynomials, even
when the signed weights vary and the indexing family is infinite. -/
theorem linearIndependent_of_symbols {ι : Type*} (d : ι → ℤ)
    (P Q : ι → MvPolynomial σ ℂ) (h : ∀ i, Symbol w (d i) (P i) (Q i))
    (hq : LinearIndependent ℂ Q) : LinearIndependent ℂ P := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter fun j => g j ≠ 0
  have ht : t.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨hi,hgi⟩⟩
  let n := (t.image d).min' (ht.image d)
  obtain ⟨j₀,hj₀,hdegree⟩ := Finset.mem_image.mp (Finset.min'_mem (t.image d) (ht.image d))
  have hp := congrArg (weightedHomogeneousComponent w n) hsum
  simp only [map_sum,map_smul,map_zero] at hp
  have hh : ∑ j ∈ s, (if d j=n then g j else 0) • Q j=0 := by
    rw [← hp]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hg : g j=0
    · simp [hg]
    · have hjt : j∈t := Finset.mem_filter.mpr ⟨hj,hg⟩
      have hd : n≤d j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j,hjt,rfl⟩)
      rcases hd.eq_or_lt with he | he
      · rw [if_pos he.symm,he,(h j).component]
      · rw [if_neg (ne_of_gt he),component_below (h j).bound he]
        simp
  have hz := linearIndependent_iff'.mp hq s
    (fun j => if d j=n then g j else 0) hh j₀ (Finset.mem_filter.mp hj₀).1
  exact (Finset.mem_filter.mp hj₀).2 (by simpa only [hdegree,n,if_true] using hz)

end
end VOA.PolynomialMinimum
