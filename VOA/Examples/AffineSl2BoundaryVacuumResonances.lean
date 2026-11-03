import VOA.Examples.AffineSl2BoundaryParabolicRoots
import VOA.Examples.AffineSl2VacuumDeterminantOrder

/-! # All boundary resonances in the actual vacuum determinant quotient -/
namespace VOA.AffineSl2BoundaryVacuumResonances
open AffineSl2BoundaryParabolicRoots

abbrev vacuumPositive (P s : ℕ) : (Fin 3×ℕ)×ℕ := ((0,P*s-1),2*s-2)
abbrev vacuumNegative (P s : ℕ) : (Fin 3×ℕ)×ℕ := ((1,P*s),2*s)
abbrev reflectedPositive (P s : ℕ) : (Fin 3×ℕ)×ℕ := ((0,P*s-1),2*s)
abbrev reflectedNegative (P s : ℕ) : (Fin 3×ℕ)×ℕ := ((1,P*s),2*s-2)

/-- All actual vacuum-weight resonances, with the horizontal relation separated. -/
theorem vacuum_labels (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈Wak.Charged.affineKacLabels n c)
    (hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i=0) :
    i=((1,0),0) ∨ ∃ s : ℕ, 0<s ∧ s≤n ∧
      (i=vacuumPositive P s ∨ i=vacuumNegative P s) := by
  obtain ⟨ha,he⟩ := Wak.Charged.affineKacLabels_bounds n c i hi
  have hPc : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  rcases i with ⟨⟨a,m⟩,j⟩
  fin_cases a
  · have heq : 2*(m+1)=P*((j+1)+(2*1-1)) := by
      have hh : (2:ℂ)*(m+1)=(P:ℂ)*(j+2) := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        field_simp [hPc] at hz
        linear_combination hz
      norm_num at ⊢
      exact_mod_cast hh
    obtain ⟨s,hs,hm,hj⟩ := positive_resonance_scale P 1 (m+1) (j+1)
      hP (by omega) (by omega) hcop heq
    have hmle : m+1≤n := le_trans (Nat.le_mul_of_pos_left _ (by omega : 0<j+1))
      (by simpa [Wak.Charged.oscillatorEnergy] using he)
    right
    refine ⟨s,by omega,?_,Or.inl ?_⟩
    · nlinarith
    · have hm' : m=P*s-1 := by omega
      have hj' : j=2*s-2 := by omega
      simp [vacuumPositive,hm',hj']
  · by_cases hm : m=0
    · subst m
      norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
        Wak.Charged.realRootOffset] at hz
      left
      simp [hz]
    · have heq : 2*m+P*(2*1-1)=P*(j+1) := by
        have hh : (2:ℂ)*m+P=(P:ℂ)*(j+1) := by
          norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
            Wak.Charged.realRootOffset] at hz
          field_simp [hPc] at hz
          linear_combination -hz
        norm_num at ⊢
        exact_mod_cast hh
      obtain ⟨s,hs,hm',hj⟩ := negative_resonance_scale P 1 m (j+1)
        hP (by omega) (by omega) hcop heq
      have hmle : m≤n := le_trans (Nat.le_mul_of_pos_left _ (by omega : 0<j+1))
        (by simpa [Wak.Charged.oscillatorEnergy] using he)
      right
      refine ⟨s,hs,?_,Or.inr ?_⟩
      · nlinarith
      · have hj' : j=2*s := by omega
        simp [vacuumNegative,hm',hj']
  · exact False.elim (ha rfl)

/-- All reflected-weight resonances. There is no horizontal factor at weight −2. -/
theorem reflected_labels (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈Wak.Charged.affineKacLabels n c)
    (hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i= -2) :
    ∃ s : ℕ, 0<s ∧ s≤n ∧
      (i=reflectedPositive P s ∨ i=reflectedNegative P s) := by
  obtain ⟨ha,he⟩ := Wak.Charged.affineKacLabels_bounds n c i hi
  have hPc : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  rcases i with ⟨⟨a,m⟩,j⟩
  fin_cases a
  · have heq : 2*(m+1)+P*(2*1-1)=P*(j+1) := by
      have hh : (2:ℂ)*(m+1)+P=(P:ℂ)*(j+1) := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        field_simp [hPc] at hz
        linear_combination hz
      norm_num at ⊢
      exact_mod_cast hh
    obtain ⟨s,hs,hm,hj⟩ := negative_resonance_scale P 1 (m+1) (j+1)
      hP (by omega) (by omega) hcop heq
    have hmle : m+1≤n := le_trans (Nat.le_mul_of_pos_left _ (by omega : 0<j+1))
      (by simpa [Wak.Charged.oscillatorEnergy] using he)
    refine ⟨s,hs,?_,Or.inl ?_⟩
    · nlinarith
    · have hm' : m=P*s-1 := by omega
      have hj' : j=2*s := by omega
      simp [reflectedPositive,hm',hj']
  · have heq : 2*m=P*((j+1)+(2*1-1)) := by
      have hh : (2:ℂ)*m=(P:ℂ)*(j+2) := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        field_simp [hPc] at hz
        linear_combination -hz
      norm_num at ⊢
      exact_mod_cast hh
    obtain ⟨s,hs,hm,hj⟩ := positive_resonance_scale P 1 m (j+1)
      hP (by omega) (by omega) hcop heq
    have hmle : m≤n := le_trans (Nat.le_mul_of_pos_left _ (by omega : 0<j+1))
      (by simpa [Wak.Charged.oscillatorEnergy] using he)
    refine ⟨s,by omega,?_,Or.inr ?_⟩
    · nlinarith
    · have hj' : j=2*s-2 := by omega
      simp [reflectedNegative,hm,hj']
  · exact False.elim (ha rfl)

/-- Nonzero guarded multiplicity forces every actual Kac-label cutoff.
This prevents fictitious terms from natural subtraction beyond the energy bound. -/
theorem multiplicity_ne_zero_mem (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (ha : i.1.1≠2) (he : (i.2+1)*Wak.Charged.oscillatorEnergy i.1≤n)
    (hm : Wak.Charged.affineKacMultiplicity n c i≠0) :
    i∈Wak.Charged.affineKacLabels n c := by
  classical
  letI : Fintype (Wak.Charged.JointIndex (n-(i.2+1)*Wak.Charged.oscillatorEnergy i.1)
    (c-((i.2+1:ℕ):ℤ)*Wak.Charged.oscillatorCharge i.1)) := Wak.Charged.jointIndexFintype _ _
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hm)
  let y := (Wak.Charged.removeOccupationEquiv n c i.1 (i.2+1) he).symm x
  have hy : i.1∈Wak.Charged.jointModeBox n c := by
    apply Wak.Charged.jointIndex_support_box n c y.1
    exact Finsupp.mem_support_iff.mpr (by have := y.2; omega)
  have hi : i.2 < (2*(n:ℤ)-c).toNat := by
    have hb := Wak.Charged.jointIndex_multiplicity_le n c y.1 i.1
    have := y.2
    omega
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hy,ha⟩,
    Finset.mem_range.mpr hi⟩,he⟩

/-- Missing labels contribute zero whenever the real-root energy fits. -/
theorem multiplicity_zero_of_not_mem (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (ha : i.1.1≠2) (he : (i.2+1)*Wak.Charged.oscillatorEnergy i.1≤n)
    (hi : i∉Wak.Charged.affineKacLabels n c) :
    Wak.Charged.affineKacMultiplicity n c i=0 := by
  by_contra hm
  exact hi (multiplicity_ne_zero_mem n c i ha he hm)


/-- The common exact threshold count, explicitly zero above the source energy. -/
noncomputable def guardedMultiplicity (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ) : ℕ :=
  if (i.2+1)*Wak.Charged.oscillatorEnergy i.1≤n then
    Wak.Charged.affineKacMultiplicity n c i else 0

def vacuumLabel (P : ℕ) (x : ℕ×Bool) :=
  if x.2 then vacuumNegative P x.1 else vacuumPositive P x.1

def reflectedLabel (P : ℕ) (x : ℕ×Bool) :=
  if x.2 then reflectedNegative P x.1 else reflectedPositive P x.1

theorem vacuumLabel_resonant (P s : ℕ) (hP : 0<P) (hs : 0<s) (b : Bool) :
    Wak.Charged.realRootWeight (2/(P:ℂ)) (vacuumLabel P (s,b))=0 := by
  have hp : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  have hps : 1≤P*s := Nat.mul_pos hP hs
  have hs2 : 2≤2*s := by omega
  cases b <;>
    simp [vacuumLabel,vacuumPositive,vacuumNegative,Wak.Charged.realRootWeight,
      Wak.Charged.realRootSlope,Wak.Charged.realRootOffset,
      Nat.cast_sub hps,Nat.cast_sub hs2] <;> field_simp <;> ring

theorem reflectedLabel_resonant (P s : ℕ) (hP : 0<P) (hs : 0<s) (b : Bool) :
    Wak.Charged.realRootWeight (2/(P:ℂ)) (reflectedLabel P (s,b))= -2 := by
  have hp : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  have hps : 1≤P*s := Nat.mul_pos hP hs
  have hs2 : 2≤2*s := by omega
  cases b <;>
    simp [reflectedLabel,reflectedPositive,reflectedNegative,Wak.Charged.realRootWeight,
      Wak.Charged.realRootSlope,Wak.Charged.realRootOffset,
      Nat.cast_sub hps,Nat.cast_sub hs2] <;> field_simp <;> ring

theorem vacuumLabel_injective (P s t : ℕ) (hs : 0<s) (ht : 0<t) (b e : Bool)
    (h : vacuumLabel P (s,b)=vacuumLabel P (t,e)) : (s,b)=(t,e) := by
  cases b <;> cases e <;> simp [vacuumLabel,vacuumPositive,vacuumNegative] at h ⊢ <;> omega

theorem reflectedLabel_injective (P s t : ℕ) (hs : 0<s) (ht : 0<t) (b e : Bool)
    (h : reflectedLabel P (s,b)=reflectedLabel P (t,e)) : (s,b)=(t,e) := by
  cases b <;> cases e <;> simp [reflectedLabel,reflectedPositive,reflectedNegative] at h ⊢ <;> omega


theorem guardedMultiplicity_eq (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (ha : i.1.1≠2) :
    guardedMultiplicity n c i =
      if i∈Wak.Charged.affineKacLabels n c then Wak.Charged.affineKacMultiplicity n c i else 0 := by
  classical
  by_cases hi : i∈Wak.Charged.affineKacLabels n c
  · simp [guardedMultiplicity,hi,(Wak.Charged.affineKacLabels_bounds n c i hi).2]
  · simp only [if_neg hi,guardedMultiplicity]
    split_ifs with he
    · exact multiplicity_zero_of_not_mem n c i ha he hi
    · rfl

/-- Exact finite reindexing of the vacuum numerator root order. -/
theorem vacuum_resonance_sum (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) :
    (∑ i∈(Wak.Charged.affineKacLabels n c).erase ((1,0),0),
      if Wak.Charged.realRootWeight (2/(P:ℂ)) i=0 then
        Wak.Charged.affineKacMultiplicity n c i else 0) =
    ∑ s∈Finset.Icc 1 n, (guardedMultiplicity n c (vacuumPositive P s) +
      guardedMultiplicity n c (vacuumNegative P s)) := by
  classical
  have hsum :
      (∑ x∈(Finset.Icc 1 n).product (Finset.univ : Finset Bool),
        guardedMultiplicity n c (vacuumLabel P x)) =
      ∑ i∈(Wak.Charged.affineKacLabels n c).erase ((1,0),0),
        if Wak.Charged.realRootWeight (2/(P:ℂ)) i=0 then
          Wak.Charged.affineKacMultiplicity n c i else 0 := by
    apply Finset.sum_bij_ne_zero (fun x _ _ => vacuumLabel P x)
    · rintro ⟨s,b⟩ hx hh
      have hs : 0<s := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
      have ha : (vacuumLabel P (s,b)).1.1≠2 := by cases b <;> simp [vacuumLabel]
      rw [guardedMultiplicity_eq n c _ ha] at hh
      have hm : vacuumLabel P (s,b)∈Wak.Charged.affineKacLabels n c := by
        by_contra h; simp [h] at hh
      refine Finset.mem_erase.mpr ⟨?_,hm⟩
      cases b
      · simp [vacuumLabel,vacuumPositive]
      · simp [vacuumLabel,vacuumNegative]
        omega
    · rintro ⟨s,b⟩ hs hh ⟨t,e⟩ ht hh' he
      exact vacuumLabel_injective P s t
        (Finset.mem_Icc.mp (Finset.mem_product.mp hs).1).1
        (Finset.mem_Icc.mp (Finset.mem_product.mp ht).1).1 b e he
    · intro i hi hm
      obtain ⟨hi0,hi⟩ := Finset.mem_erase.mp hi
      have hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i=0 := by
        by_contra h; simp [h] at hm
      have hm' : Wak.Charged.affineKacMultiplicity n c i≠0 := by simpa [hz] using hm
      rcases vacuum_labels P hP hcop n c i hi hz with h|⟨s,hs,hsn,h|h⟩
      · exact False.elim (hi0 h)
      all_goals
        subst i
      · refine ⟨(s,false),by simp [Nat.succ_le_iff,hs,hsn],?_,rfl⟩
        rw [guardedMultiplicity_eq n c _ (by simp [vacuumLabel,vacuumPositive])]
        simpa [vacuumLabel,hi] using hm'
      · refine ⟨(s,true),by simp [Nat.succ_le_iff,hs,hsn],?_,rfl⟩
        rw [guardedMultiplicity_eq n c _ (by simp [vacuumLabel,vacuumNegative])]
        simpa [vacuumLabel,hi] using hm'
    · rintro ⟨s,b⟩ hx hh
      have hs : 0<s := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
      have ha : (vacuumLabel P (s,b)).1.1≠2 := by cases b <;> simp [vacuumLabel]
      rw [guardedMultiplicity_eq n c _ ha] at hh ⊢
      have hi : vacuumLabel P (s,b)∈Wak.Charged.affineKacLabels n c := by
        by_contra h; simp [h] at hh
      simp [hi,vacuumLabel_resonant P s hP hs b]
  rw [← hsum]
  change (∑ x∈(Finset.Icc 1 n) ×ˢ (Finset.univ : Finset Bool),
    guardedMultiplicity n c (vacuumLabel P x)) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp [vacuumLabel,add_comm]

/-- Exact finite reindexing of the reflected denominator root order. -/
theorem reflected_resonance_sum (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) :
    (∑ i∈Wak.Charged.affineKacLabels n c,
      if Wak.Charged.realRootWeight (2/(P:ℂ)) i= -2 then
        Wak.Charged.affineKacMultiplicity n c i else 0) =
    ∑ s∈Finset.Icc 1 n, (guardedMultiplicity n c (reflectedPositive P s) +
      guardedMultiplicity n c (reflectedNegative P s)) := by
  classical
  have hsum :
      (∑ x∈(Finset.Icc 1 n).product (Finset.univ : Finset Bool),
        guardedMultiplicity n c (reflectedLabel P x)) =
      ∑ i∈Wak.Charged.affineKacLabels n c,
        if Wak.Charged.realRootWeight (2/(P:ℂ)) i= -2 then
          Wak.Charged.affineKacMultiplicity n c i else 0 := by
    apply Finset.sum_bij_ne_zero (fun x _ _ => reflectedLabel P x)
    · rintro ⟨s,b⟩ hx hh
      have hs : 0<s := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
      have ha : (reflectedLabel P (s,b)).1.1≠2 := by cases b <;> simp [reflectedLabel]
      rw [guardedMultiplicity_eq n c _ ha] at hh
      have hm : reflectedLabel P (s,b)∈Wak.Charged.affineKacLabels n c := by
        by_contra h; simp [h] at hh
      exact hm
    · rintro ⟨s,b⟩ hs hh ⟨t,e⟩ ht hh' he
      exact reflectedLabel_injective P s t
        (Finset.mem_Icc.mp (Finset.mem_product.mp hs).1).1
        (Finset.mem_Icc.mp (Finset.mem_product.mp ht).1).1 b e he
    · intro i hi hm
      have hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i= -2 := by
        by_contra h; simp [h] at hm
      have hm' : Wak.Charged.affineKacMultiplicity n c i≠0 := by simpa [hz] using hm
      obtain ⟨s,hs,hsn,h|h⟩ := reflected_labels P hP hcop n c i hi hz
      all_goals subst i
      · refine ⟨(s,false),by simp [Nat.succ_le_iff,hs,hsn],?_,rfl⟩
        rw [guardedMultiplicity_eq n c _ (by simp [reflectedLabel,reflectedPositive])]
        simpa [reflectedLabel,hi] using hm'
      · refine ⟨(s,true),by simp [Nat.succ_le_iff,hs,hsn],?_,rfl⟩
        rw [guardedMultiplicity_eq n c _ (by simp [reflectedLabel,reflectedNegative])]
        simpa [reflectedLabel,hi] using hm'
    · rintro ⟨s,b⟩ hx hh
      have hs : 0<s := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
      have ha : (reflectedLabel P (s,b)).1.1≠2 := by cases b <;> simp [reflectedLabel]
      rw [guardedMultiplicity_eq n c _ ha] at hh ⊢
      have hi : reflectedLabel P (s,b)∈Wak.Charged.affineKacLabels n c := by
        by_contra h; simp [h] at hh
      simp [hi,reflectedLabel_resonant P s hP hs b]
  rw [← hsum]
  change (∑ x∈(Finset.Icc 1 n) ×ˢ (Finset.univ : Finset Bool),
    guardedMultiplicity n c (reflectedLabel P x)) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp [reflectedLabel,add_comm]


noncomputable section
local instance resonanceFintype (n : ℕ) (c : ℤ) : Fintype (Wak.Charged.JointIndex n c) :=
  Wak.Charged.jointIndexFintype n c

/-- A full joint Verma count shifted by an energy and charge, with its
indispensable energy guard. -/
def shiftedJointCount (n : ℕ) (c : ℤ) (energy : ℕ) (charge : ℤ) : ℕ :=
  if energy≤n then Fintype.card (Wak.Charged.JointIndex (n-energy) (c-charge)) else 0

def lowerEnergy (P s : ℕ) : ℕ := P*s*(2*s-1)
def upperEnergy (P s : ℕ) : ℕ := P*s*(2*s+1)

theorem vacuumPositive_count (P s : ℕ) (hP : 0<P) (hs : 0<s) (n : ℕ) (c : ℤ) :
    guardedMultiplicity n c (vacuumPositive P s) =
      shiftedJointCount n c (lowerEnergy P s) (2*(s:ℤ)-1) := by
  have hm : P*s-1+1=P*s := by have := Nat.mul_pos hP hs; omega
  have hj : 2*s-2+1=2*s-1 := by omega
  have hc : ((2*s-1:ℕ):ℤ)=2*(s:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*s)]; push_cast; rfl
  simp only [guardedMultiplicity,Wak.Charged.oscillatorEnergy,
    Wak.Charged.oscillatorCharge,Wak.Charged.affineKacMultiplicity,
    hj,hm,hc,shiftedJointCount,lowerEnergy]
  simp [mul_comm]

theorem vacuumNegative_count (P s : ℕ) (n : ℕ) (c : ℤ) :
    guardedMultiplicity n c (vacuumNegative P s) =
      shiftedJointCount n c (upperEnergy P s) (-(2*(s:ℤ)+1)) := by
  simp [guardedMultiplicity,Wak.Charged.oscillatorEnergy,
    Wak.Charged.oscillatorCharge,Wak.Charged.affineKacMultiplicity,
    shiftedJointCount,upperEnergy,mul_comm]

theorem reflectedPositive_count (P s : ℕ) (hP : 0<P) (hs : 0<s) (n : ℕ) (c : ℤ) :
    guardedMultiplicity n c (reflectedPositive P s) =
      shiftedJointCount n c (upperEnergy P s) (2*(s:ℤ)+1) := by
  have hm : P*s-1+1=P*s := by have := Nat.mul_pos hP hs; omega
  simp [guardedMultiplicity,Wak.Charged.oscillatorEnergy,
    Wak.Charged.oscillatorCharge,Wak.Charged.affineKacMultiplicity,
    hm,shiftedJointCount,upperEnergy,mul_comm]

theorem reflectedNegative_count (P s : ℕ) (hs : 0<s) (n : ℕ) (c : ℤ) :
    guardedMultiplicity n c (reflectedNegative P s) =
      shiftedJointCount n c (lowerEnergy P s) (-(2*(s:ℤ)-1)) := by
  have hj : 2*s-2+1=2*s-1 := by omega
  have hc : ((2*s-1:ℕ):ℤ)=2*(s:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*s)]; push_cast; rfl
  simp only [guardedMultiplicity,Wak.Charged.oscillatorEnergy,
    Wak.Charged.oscillatorCharge,Wak.Charged.affineKacMultiplicity,
    hj,hc,shiftedJointCount,lowerEnergy]
  simp [mul_comm]

/-- The actual numerator valuation equals the explicit two-family count. -/
theorem vacuumOrder_boundary (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) :
    Wak.Charged.vacuumOrder (2/(P:ℂ)-2) n c =
      ∑ s∈Finset.Icc 1 n, (shiftedJointCount n c (lowerEnergy P s) (2*(s:ℤ)-1) +
        shiftedJointCount n c (upperEnergy P s) (-(2*(s:ℤ)+1))) := by
  unfold Wak.Charged.vacuumOrder
  simp only [sub_add_cancel]
  rw [vacuum_resonance_sum P hP hcop]
  apply Finset.sum_congr rfl
  intro s hs
  rw [vacuumPositive_count P s hP (Finset.mem_Icc.mp hs).1,
    vacuumNegative_count]

/-- The actual reflected valuation equals the explicit reversed-family count. -/
theorem reflectedOrder_boundary (P : ℕ) (hP : 0<P) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) :
    Wak.Charged.reflectedOrder (2/(P:ℂ)-2) n c =
      ∑ s∈Finset.Icc 1 n, (shiftedJointCount n c (upperEnergy P s) (2*(s:ℤ)+1) +
        shiftedJointCount n c (lowerEnergy P s) (-(2*(s:ℤ)-1))) := by
  unfold Wak.Charged.reflectedOrder
  simp only [sub_add_cancel]
  rw [reflected_resonance_sum P hP hcop]
  apply Finset.sum_congr rfl
  intro s hs
  rw [reflectedPositive_count P s hP (Finset.mem_Icc.mp hs).1,
    reflectedNegative_count P s (Finset.mem_Icc.mp hs).1]

end
end VOA.AffineSl2BoundaryVacuumResonances
