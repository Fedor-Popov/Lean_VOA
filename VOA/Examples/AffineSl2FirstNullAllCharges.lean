import VOA.Examples.AffineSl2FirstNullDimension

/-! # The complete first admissible null multiplet in the actual Gram matrix -/
namespace VOA.Wak.Charged
noncomputable section
open scoped Classical
open Polynomial AffineVOA.HighestModule AffineSl2AdmissibleArithmetic
local instance allChargesFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- A zero-energy occupation uses only the horizontal lowering oscillator. -/
theorem occupationEnergy_zero_single (d : Occupation) (hd : occupationEnergy d = 0) :
    d = Finsupp.single (1,0) (d (1,0)) := by
  ext v
  by_cases hv : v=(1,0)
  · subst v; simp
  rw [Finsupp.single_eq_of_ne hv]
  have hh := occupationEnergy_remove d v (d v) le_rfl
  rw [hd] at hh
  have hz : d v * oscillatorEnergy v=0 := by omega
  have he : oscillatorEnergy v ≠ 0 := by
    rcases v with ⟨a,n⟩
    simp only [oscillatorEnergy]
    split_ifs with ha
    · intro hn; apply hv; simp [ha,hn]
    · omega
  exact (mul_eq_zero.mp hz).resolve_right he

/-- Every nonpositive zero-energy charge has exactly one occupation. -/
theorem jointIndex_zero_nonpositive_card (c : ℤ) (hc : c ≤ 0) :
    Fintype.card (JointIndex 0 c)=1 := by
  let z : JointIndex 0 c := ⟨Finsupp.single (1,0) (-c).toNat, by
    simp [occupationEnergy,occupationCharge,Finsupp.weight_single,
      oscillatorEnergy,oscillatorCharge,Int.toNat_of_nonneg (by omega : 0 ≤ -c)]⟩
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨z, ?_⟩
  intro d
  apply Subtype.ext
  rw [occupationEnergy_zero_single d.val d.property.1]
  congr 1
  have hh := d.property.2
  rw [occupationEnergy_zero_single d.val d.property.1] at hh
  simp only [occupationCharge,Finsupp.weight_single,oscillatorCharge] at hh
  norm_num at hh
  omega

/-- The first affine root is present throughout its horizontal multiplet. -/
theorem admissible_first_label_mem_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (c : ℤ) (hc : c ≤ (p:ℤ)-1) :
    ((0,q-1),p-2)∈affineKacLabels (q*(p-1)) c := by
  have hm := admissible_first_label_mem p q hp hq
  have hr : p-2+1=p-1 := by omega
  have hq' : q-1+1=q := by omega
  simp [affineKacLabels,realRootModes,jointModeBox,oscillatorEnergy,hr,hq',Nat.mul_comm] at hm ⊢
  omega

/-- The affine root has one zero-energy descendant in every allowed charge. -/
theorem admissible_first_multiplicity_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (c : ℤ) (hc : c ≤ (p:ℤ)-1) :
    affineKacMultiplicity (q*(p-1)) c ((0,q-1),p-2)=1 := by
  have hr : p-2+1=p-1 := by omega
  have hm : q-1+1=q := by omega
  simp only [affineKacMultiplicity,oscillatorEnergy,oscillatorCharge,
    Fin.isValue,Fin.reduceEq,if_false,if_true,hr,hm]
  rw [Nat.mul_comm (p-1) q,Nat.sub_self]
  exact jointIndex_zero_nonpositive_card _ (by omega)

/-- The remainder after the unique resonant root at an arbitrary first-level charge. -/
def admissibleVacuumRemainderCharge (p q : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i∈((affineKacLabels (q*(p-1)) c).erase ((1,0),0)).erase ((0,q-1),p-2),
    (affineRootPolynomial i)^affineKacMultiplicity (q*(p-1)) c i

theorem affineVacuumProduct_admissible_factor_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (c : ℤ) (hc : c ≤ (p:ℤ)-1) :
    affineVacuumProduct (q*(p-1)) c =
      (Polynomial.C (-(q : ℂ))*(X-Polynomial.C ((p : ℂ)/q-2)))*
        admissibleVacuumRemainderCharge p q c := by
  have hm : ((0,q-1),p-2)∈(affineKacLabels (q*(p-1)) c).erase ((1,0),0) :=
    Finset.mem_erase.mpr ⟨by simp,admissible_first_label_mem_charge p q hp hq c hc⟩
  have he := Finset.mul_prod_erase ((affineKacLabels (q*(p-1)) c).erase ((1,0),0))
    (fun i => (affineRootPolynomial i)^affineKacMultiplicity (q*(p-1)) c i) hm
  dsimp only at he
  rw [admissible_first_multiplicity_charge p q hp hq c hc,pow_one,
    admissible_first_root_polynomial p q hp hq] at he
  exact he.symm

theorem admissibleVacuumRemainderCharge_ne_zero (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (c : ℤ) :
    (admissibleVacuumRemainderCharge p q c).eval ((p : ℂ)/q-2)≠0 := by
  simp only [admissibleVacuumRemainderCharge,eval_prod,eval_pow,affineRootPolynomial_eval,
    sub_add_cancel]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  obtain ⟨hne,hii⟩ := Finset.mem_erase.mp hi
  obtain ⟨hnh,hii⟩ := Finset.mem_erase.mp hii
  apply pow_ne_zero
  apply neg_ne_zero.mpr
  intro hz
  rcases admissible_zero_labels_le p q hp hq hcop _ c le_rfl i hii hz with hh|hh
  · exact hnh hh
  · exact hne hh

/-- The reduced Kac numerator has an exact simple zero at every multiplet charge. -/
theorem affineVacuumProduct_admissible_simple_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (c : ℤ) (hc : c ≤ (p:ℤ)-1) :
    (affineVacuumProduct (q*(p-1)) c).eval ((p : ℂ)/q-2)=0 ∧
    (affineVacuumProduct (q*(p-1)) c).derivative.eval ((p : ℂ)/q-2)≠0 := by
  rw [affineVacuumProduct_admissible_factor_charge p q hp hq c hc]
  constructor
  · simp
  · have hqC : -(q : ℂ)≠0 := neg_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hq))
    simpa only [derivative_mul,derivative_C,derivative_sub,derivative_X,
      sub_zero,zero_mul,mul_one,zero_add,eval_add,eval_mul,eval_sub,eval_X,eval_C,
      sub_self,mul_zero,zero_add,add_zero] using
      mul_ne_zero hqC (admissibleVacuumRemainderCharge_ne_zero p q hp hq hcop c)
theorem admissible_minus_two_labels_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels (q*(p-1)) c)
    (hz : realRootWeight ((p : ℂ)/q) i = -2) :
    i=((1,q),p-2) := by
  obtain ⟨hc,he⟩ := affineKacLabels_bounds _ _ i hi
  rcases i with ⟨⟨a,m⟩,r⟩
  fin_cases a
  · have hz' : ((r+1 : ℕ) : ℂ)-1-((m+1 : ℕ) : ℂ)*((p : ℂ)/q)=0 := by
      norm_num [realRootWeight,realRootSlope,realRootOffset,Fin.ext_iff] at hz
      push_cast
      linear_combination -hz
    have eqn := negative_weight_zero_equation p q (m+1) (r+1) hq hz'
    have hs := plus_resonance_energy_gt hp hq (by omega) hcop eqn
    have hb : (m+1)*(r+1)≤q*(p-1) := by simpa [oscillatorEnergy,Nat.mul_comm] using he
    omega
  · have hz' : (m : ℂ)*((p : ℂ)/q)-((r+1 : ℕ) : ℂ)-1=0 := by
      norm_num [realRootWeight,realRootSlope,realRootOffset,Fin.ext_iff] at hz
      push_cast
      linear_combination -hz
    have eqn := positive_weight_zero_equation p q m (r+1) hq hz'
    have hm : 0<m := by
      by_contra hn
      have hm0 : m=0 := by omega
      simp only [hm0,zero_mul] at eqn
      have : 0<q*(r+1+1) := Nat.mul_pos hq (by omega)
      omega
    have hb : m*(r+1)≤q*(p-1) := by simpa [oscillatorEnergy,Nat.mul_comm] using he
    obtain ⟨hm',hr⟩ := first_minus_resonance_unique hp hq hm hcop eqn hb
    have hr' : r=p-2 := by omega
    simp [hm',hr']
  · exact False.elim (hc rfl)


/-- The shifted denominator has no resonant descendants in this charge range. -/
theorem admissible_minus_two_multiplicity_zero_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (c : ℤ) (hc : 1-(p:ℤ) ≤ c)
    (i : (Fin 3×ℕ)×ℕ) (hi : i∈affineKacLabels (q*(p-1)) (c+1))
    (hz : realRootWeight ((p : ℂ)/q) i = -2) :
    affineKacMultiplicity (q*(p-1)) (c+1) i=0 := by
  rw [admissible_minus_two_labels_charge p q hp hq hcop (c+1) i hi hz]
  have hr : p-2+1=p-1 := by omega
  simp only [affineKacMultiplicity,oscillatorEnergy,oscillatorCharge,
    Fin.isValue,Fin.reduceEq,if_pos,if_false,hr]
  rw [Nat.mul_comm (p-1) q,Nat.sub_self]
  letI := jointIndex_zero_positive_empty (c+1-((p-1:ℕ):ℤ)*(-1)) (by omega)
  exact Fintype.card_eq_zero

theorem affineKacProduct_admissible_minus_two_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (c : ℤ) (hc : 1-(p:ℤ) ≤ c) :
    (affineKacProduct ((p : ℂ)/q) (q*(p-1)) (c+1)).eval (-2)≠0 := by
  simp only [affineKacProduct,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_cases hz : realRootWeight ((p : ℂ)/q) i = -2
  · rw [admissible_minus_two_multiplicity_zero_charge p q hp hq hcop c hc i hi hz,pow_zero]
    exact one_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz))

theorem affineMinusTwoPolynomial_admissible_ne_zero_charge (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (c : ℤ) (hc : 1-(p:ℤ) ≤ c) :
    (affineMinusTwoPolynomial (q*(p-1)) (c+1)).eval ((p : ℂ)/q-2)≠0 := by
  have ht : (p : ℂ)/q≠0 := div_ne_zero
    (by exact_mod_cast (show p≠0 by omega)) (by exact_mod_cast (Nat.ne_of_gt hq))
  have hk : (p : ℂ)/q-2+2≠0 := by simpa only [sub_add_cancel] using ht
  rw [affineMinusTwoPolynomial_eval,weightDeterminant_eq_affineKacProduct_all,
    eval_mul,eval_C]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => derivativeMultiplier_ne_zero _ hk _ _))
    (affineKacProduct_admissible_minus_two_charge p q hp hq hcop c hc)

/-- Every actual Gram determinant in the entire first null multiplet has
an exact simple root, including the zero and negative charge blocks. -/
theorem vacuumChevalleyDeterminant_admissible_simple_charge (p q : ℕ)
    (hp : 2≤p) (hq : 0<q) (hcop : p.Coprime q) (c : ℤ)
    (hc₀ : 1-(p:ℤ) ≤ c) (hc₁ : c ≤ (p:ℤ)-1) :
    (vacuumChevalleyPolynomial (q*(p-1)) c).det.eval ((p:ℂ)/q-2)=0 ∧
    (vacuumChevalleyPolynomial (q*(p-1)) c).det.derivative.eval ((p:ℂ)/q-2)≠0 := by
  let k : ℂ := (p:ℂ)/q-2
  let n := q*(p-1)
  have hpr : 0 < 2*(n:ℤ)-c := by
    have := admissible_principal_positive p q hp hq
    dsimp [n]
    omega
  have hid := affine_vacuum_polynomial_identity n c hpr
  obtain ⟨hz,hd⟩ := affineVacuumProduct_admissible_simple_charge p q hp hq hcop c hc₁
  have hden := affineMinusTwoPolynomial_admissible_ne_zero_charge p q hp hq hcop c hc₀
  have hscale := vacuumDeterminantScale_ne_zero n c
  have hk : k+2≠0 := by
    dsimp [k]
    rw [sub_add_cancel]
    exact div_ne_zero (by exact_mod_cast (show p≠0 by omega)) (by exact_mod_cast (Nat.ne_of_gt hq))
  have hlead := affineLeadingPolynomial_eval_ne_zero k hk n c
  have he := congrArg (Polynomial.eval k) hid
  simp only [eval_mul,eval_C] at he
  have hv : (vacuumChevalleyPolynomial n c).det.eval k=0 := by
    rw [show (affineVacuumProduct n c).eval k=0 from hz,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hden
  refine ⟨hv,?_⟩
  intro hvd
  have hdid := congrArg (fun P : ℂ[X] => P.derivative.eval k) hid
  simp only [derivative_mul,derivative_C,eval_add,eval_mul,eval_zero,eval_C] at hdid
  rw [show (vacuumChevalleyPolynomial n c).det.derivative.eval k=0 from hvd,hv,
    show (affineVacuumProduct n c).eval k=0 from hz] at hdid
  have hnon : vacuumDeterminantScale n c*(affineLeadingPolynomial n c).eval k*
      (affineVacuumProduct n c).derivative.eval k≠0 := mul_ne_zero (mul_ne_zero hscale hlead) hd
  apply hnon
  linear_combination -hdid

end
end VOA.Wak.Charged


namespace VOA.AffineSl2GeneralRigidity
noncomputable section

/-- Exact actual simple-module joint ranks at every charge in the first
admissible horizontal null multiplet: precisely one dimension disappears. -/
theorem admissible_simpleJointPiece_first_finrank_add_one_charge (p q : ℕ)
    (hp : 2≤p) (hq : 0<q) (hcop : p.Coprime q) (c : ℤ)
    (hc₀ : 1-(p:ℤ) ≤ c) (hc₁ : c ≤ (p:ℤ)-1) :
    Module.finrank ℂ (simpleJointPiece ((p:ℂ)/q-2)
      (admissible_level_noncritical p q hp hq) (q*(p-1):ℕ) (2*c)) + 1 =
        Fintype.card (JointIndex (q*(p-1):ℕ) (2*c)) := by
  classical
  rw [simpleJointPiece_finrank_eq_gramRank]
  obtain ⟨hz, hd⟩ := Wak.Charged.vacuumChevalleyDeterminant_admissible_simple_charge p q hp hq hcop c hc₀ hc₁
  exact PolynomialMatrix.rank_add_one_of_simple_root _ _ hz hd

end
end VOA.AffineSl2GeneralRigidity
