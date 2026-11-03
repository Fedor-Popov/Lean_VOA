import VOA.Classification.COne.OrbIcoVScalarWidth
import VOA.Classification.COne.OrbIcoVGenericWard

/-! Finite convolution of the actual normalized even Ward source with
its canonical width-six monomial coefficients. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open Polynomial VOA InverseDS.VirasoroVerma
open scoped Classical

theorem polyWidthSource_add (H K t : ℂ) (P Q : ℂ[X]) :
    polyWidthSource H K t (P+Q)=polyWidthSource H K t P+polyWidthSource H K t Q := by
  simp only [polyWidthSource,polyWidthStage_add,polyWidthStep_add,Finset.sum_add_distrib]

theorem polyWidthSource_smul (H K t a : ℂ) (P : ℂ[X]) :
    polyWidthSource H K t (a • P)=a • polyWidthSource H K t P := by
  simp only [polyWidthSource,polyWidthStage_smul,polyWidthStep_smul,Finset.smul_sum]

def polyWidthLinear (H K t : ℂ) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun := polyWidthSource H K t
  map_add' := polyWidthSource_add H K t
  map_smul' := polyWidthSource_smul H K t

theorem polyWidthSource_monomial_below (H K t : ℂ) (n k : ℕ) (hk : k<n) :
    (polyWidthSource H K t (monomial n 1)).coeff k=0 := by
  simp only [polyWidthSource,finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [polyWidthStep_coeff,polyWidthStage_monomial_below H K t j n k hk,
    mul_zero,zero_add]
  split_ifs with hh
  · exact polyWidthStage_monomial_below H K t j n (k-1) (by omega)
  · rfl

theorem polyWidthSource_monomial_above (H K t : ℂ) (n k : ℕ) (hk : n+6<k) :
    (polyWidthSource H K t (monomial n 1)).coeff k=0 := by
  simp only [polyWidthSource,finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [polyWidthStep_coeff,polyWidthStage_monomial_above H K t j n k (by omega),
    mul_zero,zero_add]
  split_ifs with hh
  · exact polyWidthStage_monomial_above H K t j n (k-1) (by omega)
  · rfl

theorem polyWidthSource_monomial_smul (H K t a : ℂ) (n k : ℕ) :
    (polyWidthSource H K t (monomial n a)).coeff k=
      a*(polyWidthSource H K t (monomial n 1)).coeff k := by
  have he : monomial n a=a • monomial n (1:ℂ) := by simp [smul_monomial]
  rw [he,polyWidthSource_smul,coeff_smul,smul_eq_mul]

def evenScalarPolynomial (N : ℕ) (u : ℕ → ℂ) : ℂ[X] :=
  ∑ m ∈ Finset.range (N+1), monomial m (u m)

theorem evenScalarPolynomial_coeff (N : ℕ) (u : ℕ → ℂ) (n : ℕ) (hn : n≤N) :
    (evenScalarPolynomial N u).coeff n=u n := by
  simp [evenScalarPolynomial,finsetSum_coeff,coeff_monomial,
    Finset.mem_range,show n<N+1 by omega]

theorem polyWidthSource_convolution (H K t : ℂ) (N n : ℕ) (u : ℕ → ℂ) (hn : n≤N) :
    (polyWidthSource H K t (evenScalarPolynomial N u)).coeff n=
      ∑ q : Fin 7, (if (q:ℕ)≤n then
        OrbIcoW.scalarWidth H K t (n-q) q*u (n-q) else 0) := by
  change ((polyWidthLinear H K t) (∑ m ∈ Finset.range (N+1), monomial m (u m))).coeff n=_
  rw [map_sum,finsetSum_coeff]
  change (∑ m ∈ Finset.range (N+1),
    (polyWidthSource H K t (monomial m (u m))).coeff n)=_
  have hm : (∑ m ∈ Finset.range (N+1),
      (polyWidthSource H K t (monomial m (u m))).coeff n)=
      ∑ m ∈ Finset.range (N+1),
        u m*(polyWidthSource H K t (monomial m 1)).coeff n := by
    apply Finset.sum_congr rfl
    intro m hm
    exact polyWidthSource_monomial_smul H K t (u m) m n
  rw [hm]
  have hs : (∑ m ∈ Finset.range (n+1),
      u m*(polyWidthSource H K t (monomial m 1)).coeff n) =
      ∑ m ∈ Finset.range (N+1),
        u m*(polyWidthSource H K t (monomial m 1)).coeff n := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hm hmn
    rw [polyWidthSource_monomial_below H K t m n (by
      simp only [Finset.mem_range] at hm hmn; omega),mul_zero]
  rw [← hs,← Finset.sum_range_reflect
    (fun m => u m*(polyWidthSource H K t (monomial m 1)).coeff n) (n+1)]
  simp only [Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun q : ℕ =>
    if q≤n then OrbIcoW.scalarWidth H K t (n-q) q*u (n-q) else 0) 7]
  apply Finset.sum_bij_ne_zero (fun q _ _ => q)
  · intro q hq hne
    have hqn : q≤n := by simp only [Finset.mem_range] at hq; omega
    by_contra hq7
    have hbig : n-q+6<n := by simp only [Finset.mem_range] at hq7; omega
    apply hne
    rw [polyWidthSource_monomial_above H K t (n-q) n hbig,mul_zero]
  · intro a ha hna b hb hnb he
    exact he
  · intro q hq hne
    have hqn : q≤n := by
      by_contra hh
      apply hne
      rw [if_neg hh]
    have hqr : q<n+1 := by omega
    refine ⟨q,Finset.mem_range.mpr hqr,?_,rfl⟩
    have he : (polyWidthSource H K t (monomial (n-q) 1)).coeff n=
        OrbIcoW.scalarWidth H K t (n-q) q := by
      simpa only [Nat.sub_add_cancel hqn] using
        polyWidthSource_monomial_width H K t (n-q) q (Finset.mem_range.mp hq)
    rw [he]
    simpa only [if_pos hqn,mul_comm] using hne
  · intro q hq hne
    have hqn : q≤n := by simp only [Finset.mem_range] at hq; omega
    have hq7 : q<7 := by
      by_contra hh
      apply hne
      rw [polyWidthSource_monomial_above H K t (n-q) n (by omega),mul_zero]
    have he : (polyWidthSource H K t (monomial (n-q) 1)).coeff n=
        OrbIcoW.scalarWidth H K t (n-q) q := by
      simpa only [Nat.sub_add_cancel hqn] using
        polyWidthSource_monomial_width H K t (n-q) q hq7
    rw [if_pos hqn,he]
    ring

theorem actual_even_width_recurrence (c H K t : ℂ) (N n : ℕ)
    (f : wardSequenceSpace c K) (hn : n≤N)
    (hsource : (wardSourceAt c K H t H 13 f).val (2*n)=0) :
    (∑ q : Fin 7, (if (q:ℕ)≤n then
      OrbIcoW.scalarWidth H K t (n-q) q*
        ((2:ℂ)^(n-q)*uniformProbe c K (f.val (2*(n-q)))) else 0))=0 := by
  let u : ℕ → ℂ := fun j => (2:ℂ)^j*uniformProbe c K (f.val (2*j))
  rw [← polyWidthSource_convolution H K t N n u hn,
    polyWidthSource_actual_sound c H K t N f (evenScalarPolynomial N u)
      (fun j hj => evenScalarPolynomial_coeff N u j hj) n hn,hsource,map_zero,mul_zero]

end VOA.Classification.COne.OrbIcoV
