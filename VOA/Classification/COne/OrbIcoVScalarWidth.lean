import VOA.Classification.COne.OrbIcoVScalarSound
import VOA.Classification.COne.OrbIcoWScalar

/-! The canonical width-six dynamic program is exactly the actual polynomial
source on monomials. The support bound follows from the genuine L-minus-two
shift at each finite BSA stage. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open Polynomial
open scoped Classical

private theorem list_range_sum (r : ℕ) (f : ℕ → ℂ) :
    ((List.range r).map f).sum = ∑ j : Fin r, f j := by
  rw [Fin.sum_univ_eq_sum_range]
  induction r with
  | zero => simp
  | succ r ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem scalarSource_entry (H K : ℂ) (n r q : ℕ) (A : List (List ℂ)) (hq : q<7) :
    (((OrbIcoW.scalarSource H K n r A)[q]?).getD 0) =
      ∑ j : Fin r, ((-1:ℂ)^(r-(j:ℕ))*OrbIcoW.scalarBracket H K n q r j*
          ((((A[(j:ℕ)]?).getD [])[q]?).getD 0) +
        if r-(j:ℕ)=2 ∧ 0<q then ((((A[(j:ℕ)]?).getD [])[q-1]?).getD 0) else 0) := by
  simp only [OrbIcoW.scalarSource,List.getElem?_map,List.getElem?_range hq,
    Option.map_some,Option.getD_some]
  exact list_range_sum r _

theorem polyWidthStage_monomial_below (H K t : ℂ) (r n k : ℕ) (hk : k<n) :
    (polyWidthStage H K t r (monomial n 1)).coeff k=0 := by
  induction r using Nat.strong_induction_on generalizing k with
  | h r ih =>
    cases r with
    | zero => simp [polyWidthStage,coeff_monomial,show n≠k by omega]
    | succ r =>
      simp only [polyWidthStage,coeff_smul,finsetSum_coeff,smul_eq_mul]
      rw [Finset.sum_eq_zero]
      · simp
      · intro j hj
        rw [polyWidthStep_coeff,ih j j.isLt k hk,mul_zero,zero_add]
        split_ifs with hh
        · exact ih j j.isLt (k-1) (by omega)
        · rfl

theorem polyWidthStage_monomial_above (H K t : ℂ) (r n k : ℕ)
    (hk : 2*n+r<2*k) :
    (polyWidthStage H K t r (monomial n 1)).coeff k=0 := by
  induction r using Nat.strong_induction_on generalizing k with
  | h r ih =>
    cases r with
    | zero => simp [polyWidthStage,coeff_monomial,show n≠k by omega]
    | succ r =>
      simp only [polyWidthStage,coeff_smul,finsetSum_coeff,smul_eq_mul]
      rw [Finset.sum_eq_zero]
      · simp
      · intro j hj
        rw [polyWidthStep_coeff,ih j j.isLt k (by omega),mul_zero,zero_add]
        split_ifs with hh
        · exact ih j j.isLt (k-1) (by omega)
        · rfl

theorem polyWidthStage_monomial_rows (H K t : ℂ) (r n q : ℕ) (hq : q<7) :
    (polyWidthStage H K t r (monomial n 1)).coeff (n+q)=
      (((((OrbIcoW.scalarRows H K t n r)[r]?).getD [])[q]?).getD 0) := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    cases r with
    | zero =>
      rw [OrbIcoW.scalarRows_zero H K t n q hq]
      simp [polyWidthStage,coeff_monomial,show n=n+q ↔ q=0 by omega]
    | succ r =>
      rw [OrbIcoW.scalarRows_last]
      simp only [OrbIcoW.scalarStep,List.getElem?_map]
      rw [show ((OrbIcoW.scalarSource H K n (r+1)
        (OrbIcoW.scalarRows H K t n r))[q]?) = some
          (((OrbIcoW.scalarSource H K n (r+1)
            (OrbIcoW.scalarRows H K t n r))[q]?).getD 0) by
              rw [List.getElem?_eq_getElem (by simpa using hq)]
              rfl]
      simp only [Option.map_some,Option.getD_some]
      rw [scalarSource_entry H K n (r+1) q _ hq]
      simp only [polyWidthStage,coeff_smul,finsetSum_coeff,smul_eq_mul]
      simp only [Nat.cast_add,Nat.cast_one]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [polyWidthStep_coeff,ih j j.isLt q hq,
        OrbIcoW.scalarRows_earlier H K t n r j (by omega)]
      unfold OrbIcoW.scalarBracket
      congr 1
      by_cases hq0 : q=0
      · subst q
        rw [if_neg (by omega : ¬ (r+1-j=2 ∧ 0<0))]
        split_ifs with hh
        · exact polyWidthStage_monomial_below H K t j n (n+0-1) (by omega)
        · rfl
      · split_ifs with hh
        · rw [show n+q-1=n+(q-1) by omega,ih j j.isLt (q-1) (by omega)]
        · omega
        · omega
        · rfl

theorem polyWidthSource_monomial_width (H K t : ℂ) (n q : ℕ) (hq : q<7) :
    (polyWidthSource H K t (monomial n 1)).coeff (n+q)=
      OrbIcoW.scalarWidth H K t n q := by
  rw [OrbIcoW.scalarWidth,scalarSource_entry H K n 13 q _ hq]
  simp only [polyWidthSource,finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [polyWidthStep_coeff,polyWidthStage_monomial_rows H K t j n q hq,
    OrbIcoW.scalarRows_earlier H K t n 12 j (by omega)]
  unfold OrbIcoW.scalarBracket
  congr 1
  by_cases hq0 : q=0
  · subst q
    rw [if_neg (by omega : ¬ (13-(j:ℕ)=2 ∧ 0<0))]
    split_ifs with hh
    · exact polyWidthStage_monomial_below H K t j n (n+0-1) (by omega)
    · rfl
  · split_ifs with hh
    · rw [show n+q-1=n+(q-1) by omega,polyWidthStage_monomial_rows H K t j n (q-1)
        (by omega)]
    · omega
    · omega
    · rfl

end VOA.Classification.COne.OrbIcoV
