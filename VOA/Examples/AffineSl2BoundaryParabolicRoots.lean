import VOA.Examples.AffineSl2FirstNullAllCharges

/-! # The first nonhorizontal root in every boundary parabolic term

For highest charge 2r-2 and shifted level 2/P, coprimality with the odd
denominator forces the next affine root to have relative energy P*r.
-/
namespace VOA.AffineSl2BoundaryParabolicRoots

/-- Positive-family resonances have mode P*s and multiplicity 2s-2r+1. -/
theorem positive_resonance_scale (P r m ell : ℕ) (hP : 0<P) (hr : 0<r)
    (hell : 0<ell) (hcop : P.Coprime 2)
    (he : 2*m=P*(ell+(2*r-1))) :
    ∃ s : ℕ, r≤s ∧ m=P*s ∧ ell+(2*r-1)=2*s := by
  have hdiv : P ∣ m := hcop.dvd_of_dvd_mul_left (he ▸ dvd_mul_right P _)
  obtain ⟨s,hs⟩ := hdiv
  refine ⟨s, ?_, hs, ?_⟩
  · have hh : 2*s=ell+(2*r-1) := Nat.mul_left_cancel hP (by rw [← he,hs]; ring)
    omega
  · exact (Nat.mul_left_cancel hP (by rw [← he,hs]; ring)).symm

/-- The unique positive-family resonance at or below the first candidate
energy has multiplicity one and mode P*r. -/
theorem positive_resonance_first (P r m ell : ℕ) (hP : 0<P) (hr : 0<r)
    (hell : 0<ell) (hcop : P.Coprime 2)
    (he : 2*m=P*(ell+(2*r-1))) (hbound : m*ell≤P*r) :
    m=P*r ∧ ell=1 := by
  obtain ⟨s,hs,hm,hell'⟩ := positive_resonance_scale P r m ell hP hr hell hcop he
  have hmle : m ≤ P*r := le_trans (Nat.le_mul_of_pos_right m hell) hbound
  have hsle : s≤r := by nlinarith [hmle]
  have hsr : s=r := by omega
  constructor
  · simpa [hsr] using hm
  · omega

/-- Negative-family resonances have mode P*s and multiplicity 2s+2r-1. -/
theorem negative_resonance_scale (P r m ell : ℕ) (hP : 0<P) (_hr : 0<r)
    (hm : 0<m) (hcop : P.Coprime 2)
    (he : 2*m+P*(2*r-1)=P*ell) :
    ∃ s : ℕ, 0<s ∧ m=P*s ∧ ell=2*s+(2*r-1) := by
  have hdiv : P ∣ 2*m := (Nat.dvd_add_iff_left (dvd_mul_right P (2*r-1))).mpr
    (he ▸ dvd_mul_right P ell)
  obtain ⟨s,hs⟩ := hcop.dvd_of_dvd_mul_left hdiv
  refine ⟨s, by nlinarith, hs, ?_⟩
  apply Nat.mul_left_cancel hP
  rw [← he,hs]
  ring

/-- Every nonhorizontal negative root lies strictly above the first
positive root energy; its smallest possible energy is P*(2r+1). -/
theorem negative_resonance_energy (P r m ell : ℕ) (hP : 0<P) (hr : 0<r)
    (hm : 0<m) (hcop : P.Coprime 2)
    (he : 2*m+P*(2*r-1)=P*ell) : P*(2*r+1) ≤ m*ell := by
  obtain ⟨s,hs,hm',hell⟩ := negative_resonance_scale P r m ell hP hr hm hcop he
  have hmP : P ≤ m := by nlinarith
  have hellr : 2*r+1 ≤ ell := by omega
  exact le_trans (Nat.mul_le_mul_left P hellr) (Nat.mul_le_mul_right ell hmP)

/-- Exact isolation of actual Kac labels at or below the first boundary
parabolic singular degree, uniformly in the target charge cutoff. -/
theorem first_kac_labels (P r : ℕ) (hP : 0<P) (hr : 0<r) (hcop : P.Coprime 2)
    (n : ℕ) (c : ℤ) (hn : n≤P*r) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈Wak.Charged.affineKacLabels n c)
    (hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i=2*(r:ℂ)-2) :
    i=((1,0),2*r-2) ∨ i=((0,P*r-1),0) := by
  obtain ⟨ha,he⟩ := Wak.Charged.affineKacLabels_bounds n c i hi
  have hPc : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  have hrc : ((2*r-1:ℕ):ℂ)=2*(r:ℂ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*r)]
    push_cast
    rfl
  rcases i with ⟨⟨a,m⟩,j⟩
  fin_cases a
  · have heq : 2*(m+1)=P*((j+1)+(2*r-1)) := by
      have hh : (2:ℂ)*(m+1)=(P:ℂ)*((j+1)+(2*r-1:ℕ)) := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        field_simp [hPc] at hz
        rw [hrc]
        linear_combination hz
      exact_mod_cast hh
    have hb : (m+1)*(j+1)≤P*r := by
      exact le_trans (by simpa [Wak.Charged.oscillatorEnergy,Nat.mul_comm] using he) hn
    obtain ⟨hm,hj⟩ := positive_resonance_first P r (m+1) (j+1) hP hr (by omega) hcop heq hb
    right
    have hm' : m=P*r-1 := by omega
    have hj' : j=0 := by omega
    simp [hm',hj']
  · by_cases hm : m=0
    · subst m
      have hj : j=2*r-2 := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        have hh : (j:ℂ)=((2*r-2:ℕ):ℂ) := by
          rw [Nat.cast_sub (by omega : 2 ≤ 2*r)]
          push_cast
          exact hz
        exact_mod_cast hh
      left; simp [hj]
    · have heq : 2*m+P*(2*r-1)=P*(j+1) := by
        have hh : (2:ℂ)*m+(P:ℂ)*(2*r-1:ℕ)=(P:ℂ)*(j+1) := by
          norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
            Wak.Charged.realRootOffset] at hz
          field_simp [hPc] at hz
          rw [hrc]
          linear_combination -hz
        exact_mod_cast hh
      have henergy := negative_resonance_energy P r m (j+1) hP hr (by omega) hcop heq
      have hb : m*(j+1)≤P*r := by
        exact le_trans (by simpa [Wak.Charged.oscillatorEnergy,Nat.mul_comm] using he) hn
      have : P*r<P*(2*r+1) := Nat.mul_lt_mul_of_pos_left (by omega) hP
      omega
  · exact False.elim (ha rfl)

/-- Below the first relative singular degree, every actual resonant label
is precisely the horizontal finite-dimensional relation. -/
theorem kac_labels_below_first (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n<P*r)
    (i : (Fin 3×ℕ)×ℕ) (hi : i∈Wak.Charged.affineKacLabels n c)
    (hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i=2*(r:ℂ)-2) :
    i=((1,0),2*r-2) := by
  rcases first_kac_labels P r hP hr hcop n c (by omega) i hi hz with h|h
  · exact h
  · subst i
    have hb := (Wak.Charged.affineKacLabels_bounds n c _ hi).2
    have hpr : P*r-1+1=P*r := by have := Nat.mul_pos hP hr; omega
    simp [Wak.Charged.oscillatorEnergy,hpr] at hb
    omega

/-- The next positive root really occurs in the finite actual Kac product. -/
theorem next_label_mem (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (c : ℤ) (hc : c≤1) :
    ((0,P*r-1),0) ∈ Wak.Charged.affineKacLabels (P*r) c := by
  have hpr : 0<P*r := Nat.mul_pos hP hr
  have hm := Wak.Charged.admissible_first_label_mem_charge 2 (P*r)
    (by omega) hpr c (by simpa using hc)
  simpa using hm

/-- Its exact actual occupation multiplicity is one through all lower charges. -/
theorem next_label_multiplicity (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (c : ℤ) (hc : c≤1) :
    Wak.Charged.affineKacMultiplicity (P*r) c ((0,P*r-1),0)=1 := by
  simpa using Wak.Charged.admissible_first_multiplicity_charge 2 (P*r)
    (by omega) (Nat.mul_pos hP hr) c (by simpa using hc)

/-- The root isolated above has precisely the required boundary highest weight. -/
theorem next_label_resonant (P r : ℕ) (hP : 0<P) (hr : 0<r) :
    Wak.Charged.realRootWeight (2/(P:ℂ)) ((0,P*r-1),0)=2*(r:ℂ)-2 := by
  have hpr : P*r-1+1=P*r := by have := Nat.mul_pos hP hr; omega
  have hPc : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  simp only [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
    Wak.Charged.realRootOffset,Fin.isValue,if_true]
  push_cast
  have hh : ((P*r-1:ℕ):ℂ)+1=(P:ℂ)*(r:ℂ) := by exact_mod_cast hpr
  rw [hh]
  field_simp
  ring

/-- The reflected highest weight has only the opposite first affine root
in this entire degree range. -/
theorem reflected_first_kac_labels (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n≤P*r)
    (i : (Fin 3×ℕ)×ℕ) (hi : i∈Wak.Charged.affineKacLabels n c)
    (hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i= -2*(r:ℂ)) :
    i=((1,P*r),0) := by
  obtain ⟨ha,he⟩ := Wak.Charged.affineKacLabels_bounds n c i hi
  have hPc : (P:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hP
  have hrc : ((2*r-1:ℕ):ℂ)=2*(r:ℂ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*r)]
    push_cast
    rfl
  rcases i with ⟨⟨a,m⟩,j⟩
  fin_cases a
  · have heq : 2*(m+1)+P*(2*r-1)=P*(j+1) := by
      have hh : (2:ℂ)*(m+1)+(P:ℂ)*(2*r-1:ℕ)=(P:ℂ)*(j+1) := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        field_simp [hPc] at hz
        rw [hrc]
        linear_combination hz
      exact_mod_cast hh
    have henergy := negative_resonance_energy P r (m+1) (j+1)
      hP hr (by omega) hcop heq
    have hb : (m+1)*(j+1)≤P*r := by
      exact le_trans (by simpa [Wak.Charged.oscillatorEnergy,Nat.mul_comm] using he) hn
    have : P*r<P*(2*r+1) := Nat.mul_lt_mul_of_pos_left (by omega) hP
    omega
  · have heq : 2*m=P*((j+1)+(2*r-1)) := by
      have hh : (2:ℂ)*m=(P:ℂ)*((j+1)+(2*r-1:ℕ)) := by
        norm_num [Wak.Charged.realRootWeight,Wak.Charged.realRootSlope,
          Wak.Charged.realRootOffset] at hz
        field_simp [hPc] at hz
        rw [hrc]
        linear_combination -hz
      exact_mod_cast hh
    have hb : m*(j+1)≤P*r := by
      exact le_trans (by simpa [Wak.Charged.oscillatorEnergy,Nat.mul_comm] using he) hn
    obtain ⟨hm,hj⟩ := positive_resonance_first P r m (j+1) hP hr (by omega) hcop heq hb
    have hj' : j=0 := by omega
    simp [hm,hj']
  · exact False.elim (ha rfl)

/-- Every reflected resonant factor has exponent zero at nonnegative
relative charge, so it cannot obstruct the parabolic determinant cancellation. -/
theorem reflected_resonant_multiplicity_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n≤P*r) (hc : 0≤c)
    (i : (Fin 3×ℕ)×ℕ) (hi : i∈Wak.Charged.affineKacLabels n c)
    (hz : Wak.Charged.realRootWeight (2/(P:ℂ)) i= -2*(r:ℂ)) :
    Wak.Charged.affineKacMultiplicity n c i=0 := by
  rw [reflected_first_kac_labels P r hP hr hcop n c hn i hi hz]
  simp only [Wak.Charged.affineKacMultiplicity,Wak.Charged.oscillatorEnergy,
    Wak.Charged.oscillatorCharge,Fin.isValue,Fin.reduceEq,if_true,if_false,
    zero_add,one_mul,Nat.sub_eq_zero_of_le hn]
  letI := Wak.Charged.jointIndex_zero_positive_empty (c-1*(-1)) (by omega)
  exact Fintype.card_eq_zero

end VOA.AffineSl2BoundaryParabolicRoots
