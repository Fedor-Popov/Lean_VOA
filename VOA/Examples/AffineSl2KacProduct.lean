/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2KacDegreeCount

/-!
# Full real-root Kac product at nonreal affine parameters

The screening construction supplies both root families with actual full
radical descendants. Their weights are distinct at nonreal shifted level.
The exact occupation count exhausts the proved highest-weight degree, so
these genuine factors determine the normalized actual Verma determinant.
-/
namespace VOA.Wak.Charged
open Polynomial
open AffineVOA.HighestModule
noncomputable section
local instance kacProductFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- Signed shifted-level coefficient of a real-root highest weight. Beta
creation has positive slope; gamma creation, including gamma zero, nonpositive slope. -/
def realRootSlope (v : Fin 3×ℕ) : ℤ := if v.1=0 then (v.2 : ℤ)+1 else -(v.2 : ℤ)

/-- Integer offset for the r+1 occurrence threshold of a root oscillator. -/
def realRootOffset (v : Fin 3×ℕ) (r : ℕ) : ℤ :=
  if v.1=0 then -(r : ℤ)-2 else (r : ℤ)

/-- Actual highest weight at which the threshold root family is degenerate. -/
def realRootWeight (t : ℂ) (i : (Fin 3×ℕ)×ℕ) : ℂ :=
  (realRootSlope i.1 : ℂ)*t+(realRootOffset i.1 i.2 : ℂ)

/-- At a nonreal parameter, integer affine-linear functions have equal
values only when both their slope and intercept agree. -/
theorem integer_linear_parameters (t : ℂ) (ht : t.im≠0) (a b a' b' : ℤ)
    (he : (a : ℂ)*t+b=(a' : ℂ)*t+b') : a=a' ∧ b=b' := by
  have hi := congrArg Complex.im he
  simp only [Complex.add_im,Complex.mul_im,Complex.intCast_re,Complex.intCast_im,
    zero_mul,add_zero] at hi
  have ha : (a : ℝ)=(a' : ℝ) := mul_right_cancel₀ ht hi
  have haa : a=a' := by exact_mod_cast ha
  subst a'
  exact ⟨rfl,by exact_mod_cast (add_left_cancel he : (b : ℂ)=(b' : ℂ))⟩

/-- Distinct genuine root-colour/occurrence labels have distinct highest
weights at nonreal shifted level, including the horizontal gamma-zero family. -/
theorem realRootWeight_injective (t : ℂ) (ht : t.im≠0)
    (i j : (Fin 3×ℕ)×ℕ) (hi : i.1.1≠2) (hj : j.1.1≠2)
    (he : realRootWeight t i=realRootWeight t j) : i=j := by
  obtain ⟨hs,ho⟩ := integer_linear_parameters t ht _ _ _ _ he
  rcases i with ⟨⟨a,u⟩,r⟩
  rcases j with ⟨⟨b,v⟩,s⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [realRootSlope,realRootOffset,Fin.ext_iff] <;> omega

/-- Finite real-root labels whose creation energy fits the selected block.
The principal bound also controls horizontal lowering multiplicities. -/
def affineKacLabels (n : ℕ) (c : ℤ) : Finset ((Fin 3×ℕ)×ℕ) :=
  ((realRootModes n c).product (Finset.range (2*(n : ℤ)-c).toNat)).filter
    (fun i => (i.2+1)*oscillatorEnergy i.1≤n)

/-- Full joint descendant multiplicity of one actual real-root relation. -/
def affineKacMultiplicity (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ) : ℕ :=
  Fintype.card (JointIndex (n-(i.2+1)*oscillatorEnergy i.1)
    (c-((i.2+1 : ℕ) : ℤ)*oscillatorCharge i.1))

/-- Finite monic real-root product with actual joint occupation multiplicities. -/
def affineKacProduct (t : ℂ) (n : ℕ) (c : ℤ) : Polynomial ℂ :=
  ∏ i∈affineKacLabels n c,(X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i

/-- The finite root product is monic, including the empty product. -/
theorem affineKacProduct_monic (t : ℂ) (n : ℕ) (c : ℤ) : (affineKacProduct t n c).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C _).pow _

/-- The expected real-root product has exactly the proved highest-weight
degree budget; this is the finite occupation-threshold count. -/
theorem affineKacProduct_natDegree (t : ℂ) (n : ℕ) (c : ℤ) :
    (affineKacProduct t n c).natDegree=rowDegree n c+creationDegree n c := by
  unfold affineKacProduct
  rw [Polynomial.natDegree_prod_of_monic (s:=affineKacLabels n c)
    (f:=fun i => (X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i)
    (fun i _ => (Polynomial.monic_X_sub_C _).pow _)]
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one]
  rw [affineKacLabels,Finset.sum_filter]
  change (∑ a∈realRootModes n c ×ˢ Finset.range (2*(n : ℤ)-c).toNat,
    if (a.2+1)*oscillatorEnergy a.1≤n then affineKacMultiplicity n c a else 0)=_
  rw [Finset.sum_product,joint_root_degree_count]
  rfl

/-- Each finite real-root label contributes its full proved descendant
factor to the actual Verma determinant. There is no singular-state premise. -/
theorem affineKac_factor (t : ℂ) (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels n c) :
    (X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i ∣ weightDeterminant (t-2) n c := by
  have hc : i.1.1≠2 := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1).2
  have hn := (Finset.mem_filter.mp hi).2
  rcases i with ⟨⟨a,q⟩,r⟩
  fin_cases a
  · have hh := weightDeterminant_positive_factor (r+1) (q+1) (n-(r+1)*(q+1))
      (by omega) (by omega) (c-((r+1 : ℕ) : ℤ)) t
    have he : (r+1)*(q+1)+(n-(r+1)*(q+1))=n := by
      norm_num [oscillatorEnergy] at hn
      omega
    rw [he,add_sub_cancel] at hh
    have hw : realRootWeight t ((0,q),r)=((q+1 : ℕ) : ℂ)*t-((r+1 : ℕ) : ℂ)-1 := by
      simp [realRootWeight,realRootSlope,realRootOffset]
      ring
    change (X-Polynomial.C (realRootWeight t ((0,q),r)))^affineKacMultiplicity n c ((0,q),r) ∣ _
    rw [hw]
    simpa [affineKacMultiplicity,oscillatorEnergy,oscillatorCharge] using hh
  · have hh := weightDeterminant_negative_factor (r+1) q (n-(r+1)*q)
      (by omega) (c+((r+1 : ℕ) : ℤ)) t
    have he : (r+1)*q+(n-(r+1)*q)=n := by
      norm_num [oscillatorEnergy] at hn
      omega
    rw [he] at hh
    have hcc : -((r+1 : ℕ) : ℤ)+(c+((r+1 : ℕ) : ℤ))=c := by ring
    rw [hcc] at hh
    simpa [realRootWeight,realRootSlope,realRootOffset,affineKacMultiplicity,
      oscillatorEnergy,oscillatorCharge,sub_eq_add_neg,add_assoc,add_comm,add_left_comm,Polynomial.C_ofNat] using hh
  · exact False.elim (hc rfl)

/-- Pairwise distinct actual root families divide simultaneously at nonreal
parameter, using their already proved full descendant multiplicities. -/
theorem affineKacProduct_dvd (t : ℂ) (ht : t.im≠0) (n : ℕ) (c : ℤ) :
    affineKacProduct t n c ∣ weightDeterminant (t-2) n c := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hci : i.1.1≠2 := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1).2
    have hcj : j.1.1≠2 := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hj).1).1).2
    have hne : realRootWeight t i≠realRootWeight t j := fun he => hij (realRootWeight_injective t ht i j hci hcj he)
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))).pow
  · intro i hi; exact affineKac_factor t n c i hi

/-- Full normalized actual Verma determinant formula at every nonreal
shifted level, with all representation and multiplicity inputs proved. -/
theorem weightDeterminant_eq_affineKacProduct (t : ℂ) (ht : t.im≠0) (n : ℕ) (c : ℤ) :
    weightDeterminant (t-2) n c=
      Polynomial.C (∏ i : JointIndex n c,derivativeMultiplier (t-2) i.val.toMultiset.toList.reverse 0)*
        affineKacProduct t n c := by
  have hk : t-2+2≠0 := by
    have ht0 : t≠0 := by intro hz; simp [hz] at ht
    simpa using ht0
  have hh := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (affineKacProduct_monic t n c) (affineKacProduct_dvd t ht n c)
    (by rw [weightDeterminant_natDegree (t-2) hk,affineKacProduct_natDegree])
  simpa only [weightDeterminant_leadingCoeff (t-2) hk] using hh

end
end VOA.Wak.Charged
