import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleMono
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Exact pruning of zero and out-of-cutoff single-color current shifts.
Zero shifts are Euler scalars on every whole length-homogeneous polynomial. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
noncomputable section
variable (K : Type*) [CommRing K]

theorem monoShift_X (m k : ℕ) (i : Fin m) :
    monoShift K m k (MvPolynomial.X i) = monoMode K m (k + i.val) :=
  MvPolynomial.mkDerivation_X K _ _

theorem monoShift_high (m k : ℕ) (hk : m ≤ k) : monoShift K m k = 0 := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [monoShift_X]
  have hi : ¬k + i.val<m := by omega
  simp only [monoMode,dif_neg hi,Derivation.zero_apply]

theorem monoShift_zero_X (m : ℕ) (i : Fin m) :
    monoShift K m 0 (MvPolynomial.X i)=MvPolynomial.X i := by
  rw [monoShift_X]
  simp only [monoMode,zero_add,dif_pos i.isLt]

theorem monoShift_apply_sum (m k : ℕ) (p : MonoRing K m) :
    monoShift K m k p = ∑ i : Fin m, monoMode K m (k + i.val)*MvPolynomial.pderiv i p := by
  classical
  have he : monoShift K m k =
      ∑ i : Fin m, monoMode K m (k + i.val) • MvPolynomial.pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [monoShift_X]
    change _ = (Derivation.coeFnAddMonoidHom
      (∑ i : Fin m, monoMode K m (k + i.val) • MvPolynomial.pderiv i)) (MvPolynomial.X j)
    rw [map_sum,Finset.sum_apply]
    simp [Derivation.smul_apply,smul_eq_mul,MvPolynomial.pderiv_X,Pi.single_apply]
  conv_lhs => rw [he]
  change (Derivation.coeFnAddMonoidHom
    (∑ i : Fin m, monoMode K m (k + i.val) • MvPolynomial.pderiv i)) p = _
  rw [map_sum,Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply,Derivation.smul_apply,smul_eq_mul]

/-- The actual zero-mode shift is precisely the polynomial Euler operator. -/
theorem monoShift_zero (m r : ℕ) {p : MonoRing K m} (hp : p.IsHomogeneous r) :
    monoShift K m 0 p = r • p := by
  rw [monoShift_apply_sum]
  have hx : ∀ i : Fin m, monoMode K m (0 + i.val)=MvPolynomial.X i := by
    intro i
    simpa only [monoShift_X] using monoShift_zero_X K m i
  simp_rw [hx]
  exact hp.sum_X_mul_pderiv

theorem monoMode_homogeneous (m k : ℕ) : (monoMode K m k).IsHomogeneous 1 := by
  by_cases hk : k < m
  · rw [monoMode,dif_pos hk]
    exact MvPolynomial.isHomogeneous_X K _
  · rw [monoMode,dif_neg hk]
    exact MvPolynomial.isHomogeneous_zero (Fin m) K _

/-- Every single-color current shift preserves the whole polynomial's length. -/
theorem monoShift_homogeneous (m k r : ℕ) {p : MonoRing K m} (hp : p.IsHomogeneous r) :
    (monoShift K m k p).IsHomogeneous r := by
  cases r with
  | zero =>
      rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
        MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
      rw [hp,MvPolynomial.derivation_C]
      exact MvPolynomial.isHomogeneous_zero (Fin m) K _
  | succ r =>
      rw [monoShift_apply_sum]
      apply MvPolynomial.IsHomogeneous.sum
      intro i _
      have hh := (monoMode_homogeneous K m (k + i.val)).mul (hp.pderiv (i:=i))
      convert hh using 1; omega

def monoSeriesHomogeneous (m n : ℕ) (f : PowerSeries (MonoRing K m)) : Prop :=
  ∀ s, (PowerSeries.coeff s f).IsHomogeneous n

theorem monoSeriesHomogeneous_one (m : ℕ) :
    monoSeriesHomogeneous K m 0 1 := by
  intro s
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact MvPolynomial.isHomogeneous_one (Fin m) K
  · exact MvPolynomial.isHomogeneous_zero (Fin m) K _

theorem monoSeriesHomogeneous_mul (m : ℕ) {n d : ℕ}
    {f g : PowerSeries (MonoRing K m)}
    (hf : monoSeriesHomogeneous K m n f) (hg : monoSeriesHomogeneous K m d g) :
    monoSeriesHomogeneous K m (n+d) (f*g) := by
  intro s
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.IsHomogeneous.sum
  intro x _
  exact (hf x.1).mul (hg x.2)

/-- Every original whole highest-color coefficient has its source power's length. -/
theorem monoCoefficient_homogeneous (m r s : ℕ) :
    (PowerSeries.coeff s (monoCurrent K m^r)).IsHomogeneous r := by
  have hh : monoSeriesHomogeneous K m 1 (monoCurrent K m) := by
    intro k
    rw [monoCurrent,PowerSeries.coeff_mk]
    exact monoMode_homogeneous K m k
  have hp : monoSeriesHomogeneous K m r (monoCurrent K m^r) := by
    induction r with
    | zero => simpa only [pow_zero] using monoSeriesHomogeneous_one K m
    | succ r ih =>
        simpa only [pow_succ,Nat.succ_eq_add_one] using monoSeriesHomogeneous_mul K m ih hh
  exact hp s

/-- Generic scalar-linear shift words, matching the one-color words of the certificate generator. -/
def monoShiftWord (m : ℕ) : List ℕ → MonoRing K m → MonoRing K m
  | [],p => p
  | k::l,p => monoShift K m k (monoShiftWord m l p)

theorem monoShiftWord_smul (m : ℕ) (l : List ℕ) (z : K) (p : MonoRing K m) :
    monoShiftWord K m l (z • p)=z • monoShiftWord K m l p := by
  induction l with
  | nil => rfl
  | cons k l ih =>
      simp only [monoShiftWord,ih,Derivation.map_smul]

theorem monoShiftWord_homogeneous (m r : ℕ) (l : List ℕ)
    {p : MonoRing K m} (hp : p.IsHomogeneous r) :
    (monoShiftWord K m l p).IsHomogeneous r := by
  induction l with
  | nil => exact hp
  | cons k l ih => exact monoShift_homogeneous K m k r ih

theorem monoShiftWord_high_zero (m : ℕ) (l : List ℕ) (p : MonoRing K m)
    (hl : ∃ k ∈ l, m ≤ k) : monoShiftWord K m l p=0 := by
  induction l with
  | nil =>
      obtain ⟨j,hj,_⟩ := hl
      simp only [List.not_mem_nil] at hj
  | cons k l ih =>
      obtain ⟨j,hj,hhigh⟩ := hl
      rcases List.mem_cons.mp hj with hj | hj
      · subst j
        rw [monoShiftWord,monoShift_high K m k hhigh,Derivation.zero_apply]
      · rw [monoShiftWord,ih ⟨j,hj,hhigh⟩,map_zero]

/-- Remove every zero shift, recording only the scalar needed by ideal spanning. -/
theorem monoShiftWord_prune_zero (m r : ℕ) (l : List ℕ)
    {p : MonoRing K m} (hp : p.IsHomogeneous r) :
    ∃ z : K, monoShiftWord K m l p = z • monoShiftWord K m (l.filter (· ≠ 0)) p := by
  classical
  induction l with
  | nil => exact ⟨1,by simp only [monoShiftWord,List.filter_nil,one_smul]⟩
  | cons k l ih =>
      obtain ⟨z,hz⟩ := ih
      by_cases hk : k = 0
      · subst k
        refine ⟨(r:K)*z,?_⟩
        rw [monoShiftWord,monoShift_zero K m r (monoShiftWord_homogeneous K m r l hp),hz]
        rw [← Nat.cast_smul_eq_nsmul K]
        simp only [List.filter_cons,ne_eq,not_true_eq_false,decide_false,
          Bool.false_eq_true,if_false,smul_smul]
      · refine ⟨z,?_⟩
        simp only [List.filter_cons,ne_eq,hk,not_false_eq_true,decide_true,if_true,monoShiftWord]
        rw [hz,Derivation.map_smul]

/-- Once zero shifts are removed, the current-mode sum bounds their number. -/
theorem positive_modes_length_le_sum (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp only [List.length_nil,List.sum_nil,le_refl]
  | cons k l ih =>
      have hk := hl k (List.mem_cons_self)
      have ht := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      simp only [List.length_cons,List.sum_cons]
      omega

theorem pruned_modes_length_le_sum (l : List ℕ) : (l.filter (· ≠ 0)).length ≤ l.sum := by
  classical
  have he : (l.filter (· ≠ 0)).sum=l.sum := by
    induction l with
    | nil => rfl
    | cons k l ih =>
        by_cases hk : k = 0
        · subst k
          simpa only [List.filter_cons,ne_eq,not_true_eq_false,decide_false,
            Bool.false_eq_true,if_false,List.sum_cons,zero_add] using ih
        · simpa only [List.filter_cons,ne_eq,hk,not_false_eq_true,decide_true,if_true,
            List.sum_cons] using congrArg (fun n => k+n) ih
  have hpos : ∀ k ∈ l.filter (· ≠ 0), 0 < k := by
    intro k hk
    have hne : k ≠ 0 := by simpa using (List.mem_filter.mp hk).2
    exact Nat.pos_of_ne_zero hne
  rw [← he]
  exact positive_modes_length_le_sum _ hpos

end
#print axioms monoCoefficient_homogeneous
#print axioms monoShift_zero
#print axioms monoShift_high
#print axioms monoShiftWord_prune_zero
#print axioms pruned_modes_length_le_sum
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
