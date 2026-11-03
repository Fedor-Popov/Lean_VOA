/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaDescendantSymbols

/-!
# Full descendant independence on arbitrary nonzero Verma states

Every sorted negative word, including translation, acts independently on
any nonzero state in any Verma module. Highest momentum symbols multiply
in the oscillator polynomial domain. This proves the absence of relations
inside a singular Verma submodule, without an abstract PBW axiom.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangFockExponential

/-- Apply a negative word to an arbitrary Verma state. Unlike vacuum-only
creation words, index zero here includes the translation mode L-minus-one. -/
noncomputable def vermaDescendant (c h : ℂ) : List ℕ → Module.End ℂ (Verma c h)
  | [] => LinearMap.id
  | i::w => (vermaMode c h (-(i:ℤ)-1)).comp (vermaDescendant c h w)

/-- Acting on the highest vector gives the original PBW word. -/
theorem vermaDescendant_highest (c h : ℂ) (w : List ℕ) :
    vermaDescendant c h w (highestVector c h)=negWord c h w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [vermaDescendant,LinearMap.comp_apply,ih,negWord_cons]

/-- Each letter increases the momentum-degree bound by at most one,
regardless of whether the starting state is singular or homogeneous. -/
theorem vermaDescendant_polynomial_above (ell p : ℂ) (w : List ℕ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) (d : ℕ)
    (hv : ∀ k, d<k → vermaPolynomialLift ell p v k=0) :
    ∀ k, d+w.length<k →
      vermaPolynomialLift ell p (vermaDescendant _ _ w v) k=0 := by
  induction w with
  | nil => exact hv
  | cons i w ih =>
    intro k hk
    change vermaPolynomialLift ell p (vermaMode _ _ _ _) k=0
    rw [vermaPolynomialLift_negative]
    exact vermaPolynomialCreation_above ell p i (d+w.length) _ ih k (by
      simp only [List.length_cons] at hk; omega)

/-- At maximal momentum degree, an entire descendant word multiplies the
starting symbol by its oscillator monomial with coefficient one. -/
theorem vermaDescendant_polynomial_top (ell p : ℂ) (w : List ℕ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) (d : ℕ)
    (hv : ∀ k, d<k → vermaPolynomialLift ell p v k=0) :
    vermaSymbolProjection
      (vermaPolynomialLift ell p (vermaDescendant _ _ w v) (d+w.length))=
      MvPolynomial.monomial (vermaWordExponent w) 1 *
        vermaSymbolProjection (vermaPolynomialLift ell p v d) := by
  induction w with
  | nil => simp [vermaDescendant,vermaWordExponent]
  | cons i w ih =>
    change vermaSymbolProjection (vermaPolynomialLift ell p (vermaMode _ _ _ _)
      (d+(w.length+1)))=_
    rw [vermaPolynomialLift_negative,← Nat.add_assoc]
    change vermaSymbolProjection (vermaPolynomialCreation ell p i
      (vermaPolynomialLift ell p (vermaDescendant _ _ w v)) (d+w.length+1))=_
    rw [vermaPolynomialCreation_top ell p i (d+w.length) _
        (vermaDescendant_polynomial_above ell p w v d hv),ih]
    simp [vermaWordExponent,MvPolynomial.monomial_single_add,mul_assoc]

/-- In a vanishing descendant relation, every coefficient at maximal word
length is zero. The nonzero starting symbol cancels in the oscillator domain,
and distinct sorted words have distinct exponent vectors. -/
theorem vermaDescendant_max_coeff (ell p : ℂ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) (hv : v≠0)
    (K : ℕ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hs : ∀ w ∈ s, SortedWord w) (hl : ∀ w ∈ s, w.length≤K)
    (he : ∑ w ∈ s, coef w • vermaDescendant _ _ w v=0)
    (w : List ℕ) (hw : w∈s) (hwK : w.length=K) : coef w=0 := by
  classical
  obtain ⟨d,hd,hn⟩ := vermaPolynomialLift_top_exists ell p v hv
  let P := vermaSymbolProjection (vermaPolynomialLift ell p v d)
  let E : Verma (3-24*ell^2) (p^2-2*ell*p) →ₗ[ℂ] LeeYangFock :=
    vermaSymbolProjection.comp
      ((vermaPolynomialCoefficient (d+K)).comp (vermaPolynomialLift ell p))
  have hp : ∀ u ∈ s, E (vermaDescendant _ _ u v)=
      (if u.length=K then MvPolynomial.monomial (vermaWordExponent u) (1:ℂ) else 0)*P := by
    intro u hu
    by_cases huK : u.length=K
    · rw [if_pos huK]
      simpa only [E,P,LinearMap.comp_apply,vermaPolynomialCoefficient,
        LinearMap.coe_mk,AddHom.coe_mk,huK] using
        vermaDescendant_polynomial_top ell p u v d hd
    · rw [if_neg huK,zero_mul]
      change vermaSymbolProjection (vermaPolynomialLift ell p
        (vermaDescendant _ _ u v) (d+K))=0
      rw [vermaDescendant_polynomial_above ell p u v d hd _ (by have := hl u hu; omega),map_zero]
  have hh := congrArg E he
  simp only [map_sum,map_smul,map_zero] at hh
  have hz : (∑ u ∈ s, coef u •
      (if u.length=K then MvPolynomial.monomial (vermaWordExponent u) (1:ℂ) else 0))=0 := by
    have hm : (∑ u ∈ s, coef u •
        (if u.length=K then MvPolynomial.monomial (vermaWordExponent u) (1:ℂ) else 0))*P=0 := by
      rw [Finset.sum_mul]
      calc
        _ = ∑ u ∈ s, coef u • ((if u.length=K then
            MvPolynomial.monomial (vermaWordExponent u) (1:ℂ) else 0)*P) := by
          simp only [smul_mul_assoc]
        _ = ∑ u ∈ s, coef u • E (vermaDescendant _ _ u v) :=
          Finset.sum_congr rfl (fun u hu => congrArg (fun x => coef u • x) (hp u hu).symm)
        _ = 0 := hh
    exact (mul_eq_zero.mp hm).resolve_right hn
  have hc := congrArg (MvPolynomial.coeff (vermaWordExponent w)) hz
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,MvPolynomial.coeff_zero,
    smul_eq_mul] at hc
  have hselect : ∀ u ∈ s, MvPolynomial.coeff (vermaWordExponent w)
      (if u.length=K then MvPolynomial.monomial (vermaWordExponent u) (1:ℂ) else 0)=
      if u=w then 1 else 0 := by
    intro u hu
    by_cases heq : u=w
    · subst u; simp [hwK]
    · by_cases huK : u.length=K
      · rw [if_pos huK,if_neg heq,MvPolynomial.coeff_monomial]
        exact if_neg (fun h => heq (vermaWordExponent_injective_sorted (hs u hu) (hs w hw) h))
      · simp [huK,heq]
  have hvalue : (∑ u ∈ s, coef u * MvPolynomial.coeff (vermaWordExponent w)
      (if u.length=K then MvPolynomial.monomial (vermaWordExponent u) (1:ℂ) else 0))=coef w := by
    calc
      _ = ∑ u ∈ s, coef u * (if u=w then 1 else 0) :=
        Finset.sum_congr rfl (fun u hu => congrArg (fun x => coef u*x) (hselect u hu))
      _ = coef w := by simp [hw]
  exact hvalue.symm.trans hc

/-- Successively remove maximal-length terms to eliminate every coefficient
of a finite sorted descendant relation on a nonzero Verma state. -/
theorem vermaDescendant_coef_zero (ell p : ℂ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) (hv : v≠0) (K : ℕ)
    (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hs : ∀ w ∈ s, SortedWord w) (hl : ∀ w ∈ s, w.length≤K)
    (he : ∑ w ∈ s, coef w • vermaDescendant _ _ w v=0) :
    ∀ w ∈ s, coef w=0 := by
  classical
  induction K generalizing s with
  | zero =>
    intro w hw
    exact vermaDescendant_max_coeff ell p v hv 0 s coef hs hl he w hw
      (by have := hl w hw; omega)
  | succ K ih =>
    have ht := vermaDescendant_max_coeff ell p v hv (K+1) s coef hs hl he
    let t := s.filter (fun w => w.length≤K)
    have het : ∑ w ∈ t, coef w • vermaDescendant _ _ w v=0 := by
      rw [Finset.sum_filter]
      have heq : (∑ w ∈ s, if w.length≤K then coef w • vermaDescendant _ _ w v else 0) =
          ∑ w ∈ s, coef w • vermaDescendant _ _ w v := by
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hh : w.length≤K
        · simp [hh]
        · simp [hh,ht w hw (by have := hl w hw; omega)]
      exact heq.trans he
    have hi := ih t (fun w hw => hs w (Finset.mem_filter.mp hw).1)
      (fun w hw => (Finset.mem_filter.mp hw).2) het
    intro w hw
    by_cases hh : w.length≤K
    · exact hi w (Finset.mem_filter.mpr ⟨hw,hh⟩)
    · exact ht w hw (by have := hl w hw; omega)

/-- Every nonzero state in every general Verma module has independent sorted
negative-mode descendants, INCLUDING L-minus-one. No singularity assumption
and no project PBW axiom is used. -/
theorem vermaDescendant_linearIndependent (c h : ℂ) (v : Verma c h) (hv : v≠0) :
    LinearIndependent ℂ
      (fun w : {w : List ℕ // SortedWord w} => vermaDescendant c h w.val v) := by
  obtain ⟨ell,p,hc,hh⟩ := exists_vermaFockFamily_parameters c h
  subst c
  subst h
  classical
  rw [linearIndependent_iff']
  intro s g he i hi
  have hinj : Function.Injective (fun w : {w : List ℕ // SortedWord w} => w.val) :=
    Subtype.val_injective
  let coef := Function.extend (fun w : {w : List ℕ // SortedWord w} => w.val) g 0
  have hcv : ∀ j : {w : List ℕ // SortedWord w}, coef j.val=g j :=
    fun j => hinj.extend_apply g 0 j
  let t := s.image (fun w : {w : List ℕ // SortedWord w} => w.val)
  have ht : ∑ w ∈ t, coef w • vermaDescendant _ _ w v=0 := by
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    simpa only [hcv] using he
  have hs : ∀ w ∈ t, SortedWord w := by
    intro w hw
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact j.property
  obtain ⟨w₀,_,hK⟩ := t.exists_max_image List.length ⟨i.val,Finset.mem_image_of_mem _ hi⟩
  have hh := vermaDescendant_coef_zero ell p v hv w₀.length t coef hs hK ht i.val
    (Finset.mem_image_of_mem _ hi)
  rwa [hcv i] at hh

end VOA.InverseDS.VirasoroVerma
