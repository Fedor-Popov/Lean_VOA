/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaBSANonvanishing
import VOA.Examples.VirasoroVermaUniformStraightening
import VOA.Examples.VirasoroDescendantTriangular

/-!
# Extracting the all-L-minus-one coordinate

The highest-length coordinate at level n is the coefficient of L-1^n.
A free-momentum coefficient detects it, including on unsorted words. This
provides a scalar test for nonvanishing without a normalization product.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- The all-L-minus-one word is ordered at every length. -/
theorem sortedWord_replicate_zero (n : ℕ) : SortedWord (List.replicate n 0) := by
  induction n with
  | zero => exact sortedWord_nil
  | succ n ih =>
    rw [List.replicate_succ]
    apply SortedWord.cons ih
    intro b hb
    have hb0 : b=0 := (List.mem_replicate.mp hb).2
    simp [hb0]

/-- At fixed energy the maximal possible length occurs only for L-1^n. -/
theorem verma_length_eq_energy_iff (w : List ℕ) :
    w.length=energyHW w ↔ w=List.replicate (energyHW w) 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.length_cons,energyHW_cons]
    constructor
    · intro he
      have hw := verma_length_le_energy w
      have hi : i=0 := by omega
      have hl : w.length=energyHW w := by omega
      subst i
      simp only [zero_add,show 1+energyHW w=energyHW w+1 by omega,List.replicate_succ]
      exact congrArg (List.cons 0) (ih.mp hl)
    · intro he
      have hh := congrArg List.length he
      simpa using hh

/-- The PBW coordinate corresponding to n copies of L-1, as a linear map
on actual Verma states. It does not require the state to be singular. -/
noncomputable def vermaTopCoordinate (c h : ℂ) (n : ℕ) : Verma c h →ₗ[ℂ] ℂ :=
  (Finsupp.lapply ⟨List.replicate n 0,sortedWord_replicate_zero n⟩).comp
    (vermaSortedBasis c h).repr.toLinearMap

/-- On an ordered word this projection is its PBW Kronecker coefficient. -/
theorem vermaTopCoordinate_sorted (c h : ℂ) (n : ℕ) (w : List ℕ) (hw : SortedWord w) :
    vermaTopCoordinate c h n (negWord c h w)=if w=List.replicate n 0 then 1 else 0 := by
  classical
  change (vermaSortedBasis c h).repr (negWord c h w) ⟨List.replicate n 0,_⟩=_
  rw [← vermaSortedBasis_apply c h ⟨w,hw⟩,Module.Basis.repr_self]
  simp only [Finsupp.single_apply,Subtype.mk.injEq]

/-- On level n the free-momentum symbol extracts precisely this coordinate.
No other PBW word at that energy can have n creation factors. -/
theorem vermaTopCoordinate_eq_symbol (ell p : ℂ) (n : ℕ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p))
    (hv : v∈sortedSpan (3-24*ell^2) (p^2-2*ell*p) n) :
    vermaTopCoordinate _ _ n v=
      MvPolynomial.coeff (vermaWordExponent (List.replicate n 0))
        (vermaSymbolProjection (vermaPolynomialLift ell p v n)) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w,hw,he,rfl⟩ := hv
    rw [vermaTopCoordinate_sorted _ _ n w hw,
      vermaPolynomialLift_sorted ell p ⟨w,hw⟩]
    exact (vermaWordPolynomial_top_selector ell p n w (List.replicate n 0)
      hw (sortedWord_replicate_zero n) (by simpa [he] using verma_length_le_energy w) (by simp)).symm
  | zero =>
    rw [map_zero,map_zero]
    change 0=MvPolynomial.coeff _ (vermaSymbolProjection 0)
    simp
  | add v w _ _ hv hw => simp only [map_add,PolynomialModule.add_apply,MvPolynomial.coeff_add,hv,hw]
  | smul z v _ hv =>
    rw [map_smul,map_smul]
    change z • vermaTopCoordinate _ _ n v=MvPolynomial.coeff _
      (vermaSymbolProjection (z • (vermaPolynomialLift ell p v n)))
    rw [map_smul,MvPolynomial.coeff_smul,hv]

/-- Any negative word has all-L-minus-one coordinate one exactly when the
word consists entirely of those modes. Reordering cannot create that term. -/
theorem vermaTopCoordinate_word (c h : ℂ) (w : List ℕ) :
    vermaTopCoordinate c h (energyHW w) (negWord c h w)=
      if w=List.replicate (energyHW w) 0 then 1 else 0 := by
  classical
  let c0 : ℂ := 3-24*(0:ℂ)^2
  let h0 : ℂ := (0:ℂ)^2-2*0*0
  have hc := congrArg (fun f => f ⟨List.replicate (energyHW w) 0,sortedWord_replicate_zero _⟩)
    (verma_negWord_coordinates_independent c h c0 h0 w)
  change vermaTopCoordinate c h (energyHW w) (negWord c h w)=
    vermaTopCoordinate c0 h0 (energyHW w) (negWord c0 h0 w) at hc
  rw [hc]
  by_cases he : w=List.replicate (energyHW w) 0
  · rw [vermaTopCoordinate_sorted _ _ _ w (by rw [he]; exact sortedWord_replicate_zero _),if_pos he]
  · rw [if_neg he]
    have hl : w.length<energyHW w := by
      have hw := verma_length_le_energy w
      have hn : w.length≠energyHW w := fun hh => he ((verma_length_eq_energy_iff w).mp hh)
      omega
    have hh := vermaTopCoordinate_eq_symbol 0 0 (energyHW w) (negWord c0 h0 w)
      (negWord_mem_sortedSpan c0 h0 w)
    rw [hh,vermaPolynomialLift_word,vermaWordPolynomial_coeff_above 0 0 w _ hl,map_zero]
    simp
/-- Only L-1 can contribute to the all-L-minus-one coordinate after one
creation mode. Every higher negative mode contributes zero there. -/
theorem vermaTopCoordinate_creation (c h : ℂ) (n i : ℕ) (v : Verma c h)
    (hv : v∈sortedSpan c h n) :
    vermaTopCoordinate c h (n+i+1) (vermaMode c h (-(i:ℤ)-1) v)=
      if i=0 then vermaTopCoordinate c h n v else 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w,hw,he,rfl⟩ := hv
    change vermaTopCoordinate c h (n+i+1) (negWord c h (i::w))=_
    have hen : energyHW (i::w)=n+i+1 := by rw [energyHW_cons,he]; omega
    rw [← hen,vermaTopCoordinate_word,← he,vermaTopCoordinate_word]
    by_cases hi : i=0
    · subst i
      simp only [if_true,energyHW_cons,zero_add,
        show 1+energyHW w=energyHW w+1 by omega,List.replicate_succ,List.cons.injEq,true_and]
    · have hn : i::w≠List.replicate (energyHW (i::w)) 0 := by
        intro hh
        rw [energyHW_cons,show i+1+energyHW w=(i+energyHW w)+1 by omega,List.replicate_succ] at hh
        exact hi (List.cons.inj hh).1
      rw [if_neg hn,if_neg hi]
  | zero => simp
  | add v w _ _ hv hw =>
    simp only [map_add,hv,hw]
    split_ifs <;> simp
  | smul z v _ hv =>
    simp only [map_smul,hv]
    split_ifs <;> simp

/-- In the finite negative-mode source, the highest-length coordinate
comes only from applying L-1 to the immediately preceding coefficient. -/
theorem vermaTopCoordinate_wardSource (c h : ℂ) (f : ℕ → Verma c h)
    (hf : WardLevel c h f) (r : ℕ) :
    vermaTopCoordinate c h (r+1) (wardSource c h f (r+1))=
      vermaTopCoordinate c h r (f r) := by
  classical
  simp only [wardSource,map_sum]
  have hj (j : Fin (r+1)) :
      vermaTopCoordinate c h (r+1) (vermaMode c h ((j:ℤ)-((r+1:ℕ):ℤ)) (f j))=
        if j.val=r then vermaTopCoordinate c h j (f j) else 0 := by
    have hi : (j:ℤ)-((r+1:ℕ):ℤ)=-((r-j:ℕ):ℤ)-1 := by omega
    have hn : j.val+(r-j.val)+1=r+1 := by omega
    rw [hi]
    have hh := vermaTopCoordinate_creation c h j (r-j) (f j) (hf j)
    rw [hn] at hh
    have he : r-j.val=0 ↔ j.val=r := by omega
    simpa only [he] using hh
  simp only [hj]
  rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+1))]
  · simp
  · intro j hj hne
    have he : j.val≠r := fun hh => hne (Fin.ext hh)
    simp [he]
  · simp
/-- The first descendant rescales the top coordinate by its ordinary
field exponent, just as it rescales the whole state. -/
theorem vermaTopCoordinate_wardA (c h b : ℂ) (f : ℂ → wardSequenceSpace c h)
    (a : ℂ) (r : ℕ) :
    vermaTopCoordinate c h r ((wardA c h b f a).val r)=
      (h-b-a+1+(r:ℂ))*vermaTopCoordinate c h r ((f (a-1)).val r) := by
  rw [wardA_apply,map_smul,smul_eq_mul]
  ring

/-- The second descendant's top coordinate depends only on the current
and previous input coefficients; higher negative modes disappear. -/
theorem vermaTopCoordinate_wardB (c h b : ℂ) (f : ℂ → wardSequenceSpace c h)
    (a : ℂ) (r : ℕ) :
    vermaTopCoordinate c h (r+1) ((wardB c h b f a).val (r+1))=
      vermaTopCoordinate c h r ((f (a-2)).val r)+
      (2*b+a-2-h-((r+1:ℕ):ℂ))*vermaTopCoordinate c h (r+1) ((f (a-2)).val (r+1)) := by
  change vermaTopCoordinate c h (r+1)
    (wardSource c h (f (a-2)).val (r+1)+(2*b+(a-2)-h-((r+1:ℕ):ℂ)) • (f (a-2)).val (r+1))=_
  rw [map_add,map_smul,vermaTopCoordinate_wardSource c h _ (f (a-2)).property,smul_eq_mul]
  ring

/-- Every higher negative descendant has the same two-coefficient top
projection, with its proved alternating sign and shifted field weight. -/
theorem vermaTopCoordinate_wardNegative (c h b : ℂ) (n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (a : ℂ) (r : ℕ) :
    vermaTopCoordinate c h (r+1) ((wardNegative c h b n f a).val (r+1))=
      (-1:ℂ)^n * (vermaTopCoordinate c h r ((f (a-((n:ℂ)+2))).val r)+
        (((n:ℂ)+2)*b+a-((n:ℂ)+2)-h-((r+1:ℕ):ℂ))*
          vermaTopCoordinate c h (r+1) ((f (a-((n:ℂ)+2))).val (r+1))) := by
  induction n generalizing f a with
  | zero =>
    rw [wardNegative_zero,vermaTopCoordinate_wardB]
    simp only [Nat.cast_zero,zero_add,pow_zero,one_mul]
  | succ n ih =>
    change vermaTopCoordinate c h (r+1) (((n:ℂ)+1)⁻¹ •
      (((wardA c h b) ((wardNegative c h b n) f) a).val (r+1)-
       ((wardNegative c h b n) ((wardA c h b) f) a).val (r+1)))=_
    rw [map_smul,map_sub,smul_eq_mul,vermaTopCoordinate_wardA,
      ih f (a-1),ih ((wardA c h b) f) a,vermaTopCoordinate_wardA,vermaTopCoordinate_wardA]
    have hi : a-1-((n:ℂ)+2)=a-((n:ℂ)+2)-1 := by ring
    have hj : a-((n:ℂ)+2)-1=a-(((n:ℂ)+1)+2) := by ring
    simp only [hi,hj,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp [show (n:ℂ)+1≠0 by exact_mod_cast (Nat.succ_ne_zero n)]
    <;> ring
end VOA.InverseDS.VirasoroVerma
