import VOA.Huang.LogAssocOutsideJacobiCoefficients
import VOA.Huang.PzTensorOutside

/-! Pure finite-support binomial reorganization of the genuine transposed
P(1) coproduct. This identity uses actual bilinear functionals only. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocOutsideJacobi
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.PzTensorRho VOA.Huang.PzTensorOutside VOA.Huang.PzTensorHatBridge
open VOA.Huang.AssocAssociator VOA.Huang.PzTensorCompatProof VOA.Huang.AssocCoeffRules
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

/-- The coproduct sum is exactly the binomial Cauchy convolution. Genuine
truncation and a uniform lower exponent bound justify every rearrangement. -/
theorem rho_convolution (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (u : V) (x : M₁) (y : M₂) (F : ℤ → BilinearDual (M₁ := M₁) (M₂ := M₂))
    (m : ℤ) {N : ℕ}
    (hX : ∀ i : ℤ,(N : ℤ) ≤ i → mode (A₁.YM u) i x=0)
    (hY : ∀ i : ℤ,(N : ℤ) ≤ i → mode (A₂.YM u) i y=0)
    (hF : ∃ I : ℤ,∀ i : ℤ,I ≤ i → F i=0) :
    (∑ᶠ i : ℤ,cbz m i*rhoL A₁ A₂ u i (F i) x y)=
      (∑ i∈Finset.Ico 0 (N : ℤ),cbz m i*∑ᶠ j : ℕ,
        PowerSeries.coeff j (binPS (m-i))*F (i+j) (mode (A₁.YM u) i x) y)+
      ∑ i∈Finset.Ico 0 (N : ℤ),cbz m i*F i x (mode (A₂.YM u) i y) := by
  classical
  obtain ⟨I,hI⟩ := hF
  have fR : Function.HasFiniteSupport fun i : ℤ =>
      cbz m i*F i x (mode (A₂.YM u) i y) :=
    hfs_of _ 0 N fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hY i (by omega),map_zero]; ring
  have fL : Function.HasFiniteSupport fun i : ℤ =>
      cbz m i*∑ᶠ r : ℤ,cbz i r*F i (mode (A₁.YM u) r x) y :=
    hfs_of _ 0 (max I 0) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hI i (by omega)]; simp
  simp only [rhoL_apply,mul_add]
  rw [finsum_add_distrib fR fL]
  have hRpart : (∑ᶠ i : ℤ,cbz m i*F i x (mode (A₂.YM u) i y))=
      ∑ i∈Finset.Ico 0 (N : ℤ),cbz m i*F i x (mode (A₂.YM u) i y) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_Ico,Set.mem_Ico]
    by_contra hc
    apply hi
    rcases lt_or_ge i 0 with h0 | h0
    · rw [cbz_neg h0]; ring
    · rw [hY i (by omega),map_zero]; ring
  let g : ℤ → ℂ := fun r => cbz m r*∑ᶠ j : ℕ,
    cbz (m-r) j*F (r+j) (mode (A₁.YM u) r x) y
  have hA : (∑ i∈Finset.Ico 0 (N : ℤ),cbz m i*∑ᶠ j : ℕ,
      PowerSeries.coeff j (binPS (m-i))*F (i+j) (mode (A₁.YM u) i x) y)=∑ᶠ r : ℤ,g r := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ico 0 (N : ℤ)) (fun r hr => by
      rw [Function.mem_support] at hr
      simp only [Finset.coe_Ico,Set.mem_Ico]
      by_contra hc
      apply hr
      dsimp only [g]
      rcases lt_or_ge r 0 with h0 | h0
      · rw [cbz_neg h0]; ring
      · rw [finsum_eq_zero_of_forall_eq_zero fun j => by
          rw [hX r (by omega),map_zero,LinearMap.zero_apply]; ring]; ring)]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only [g]
    congr 1
    exact finsum_congr fun j => by rw [coeff_binPS]
  have hLpart : (∑ᶠ i : ℤ,cbz m i*∑ᶠ r : ℤ,
      cbz i r*F i (mode (A₁.YM u) r x) y)=∑ᶠ r : ℤ,g r := by
    simp only [mul_finsum]
    rw [finsum_comm_box _ 0 (max I 0) 0 N (fun i r hir => by
      rcases hir with h | h | h | h
      · rw [cbz_neg h]; ring
      · rw [hI i (by omega)]; simp
      · rw [cbz_neg h]; ring
      · rw [hX r (by omega),map_zero,LinearMap.zero_apply]; ring)]
    refine finsum_congr fun r => ?_
    dsimp only [g]
    rcases lt_or_ge r 0 with h0 | h0
    · rw [cbz_neg h0,zero_mul]
      exact finsum_eq_zero_of_forall_eq_zero fun i => by rw [cbz_neg h0]; ring
    rw [← finsum_shift _ r,finsum_int_eq_nat _ (fun j hj => by
      rcases lt_or_ge (j+r) 0 with h1 | h1
      · rw [cbz_neg h1]; ring
      · rw [cbz_nat_lt h1 (by omega)]; ring),mul_finsum]
    refine finsum_congr fun j => ?_
    have ht := trinom m (show 0 ≤ (j : ℤ)+r by omega) r
    rw [show (j : ℤ)+r-r=j by ring] at ht
    rw [show (j : ℤ)+r=r+j by ring] at ht ⊢
    linear_combination (F (r+j) (mode (A₁.YM u) r x) y)*ht.symm
  rw [hRpart,hLpart,← hA]
  ring

end VOA.Huang.LogAssocOutsideJacobi
