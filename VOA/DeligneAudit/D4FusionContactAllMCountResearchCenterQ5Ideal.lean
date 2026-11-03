import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticSourceReduction

/-! The literal polar ideal of source powers 2..R (R = 4 gives J234). It is
preserved by every actual negative-current mode, its top analogue by every
plain top shift, and every power-(n+1) source word reduces modulo the
powers-2..n ideal to (n+1)^(number of shifts) times one static polar. Power-two
lower tails vanish by the linear truncation. No closure premise is used. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Admissible whole polar coefficients of every source power from 2 to R. -/
def polarRangeSeeds (m R : ℕ) : Set (MvPolynomial (Vars m) ℂ) :=
  {p | ∃ r a b c s, 2 ≤ r ∧ r ≤ R ∧ m < r + s ∧
    p = PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))}

def polarRangeIdeal (m R : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) :=
  Ideal.span (polarRangeSeeds m R)

theorem polarRange_coeff_mem (m R r a b c s : ℕ) (h2 : 2 ≤ r) (hR : r ≤ R)
    (hs : m < r + s) :
    PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) ∈ polarRangeIdeal m R :=
  Ideal.subset_span ⟨r,a,b,c,s,h2,hR,hs,rfl⟩

theorem polarRange_highest_mem (m R r s : ℕ) (h2 : 2 ≤ r) (hR : r ≤ R) (hs : m < r + s) :
    PowerSeries.coeff s (AllM.current m 0 ^ r) ∈ polarRangeIdeal m R := by
  simpa only [currentMap_orbit,Function.iterate_zero_apply] using
    polarRange_coeff_mem m R r 0 0 0 s h2 hR hs

theorem polarRangeIdeal_mono (m : ℕ) {R R' : ℕ} (h : R ≤ R') :
    polarRangeIdeal m R ≤ polarRangeIdeal m R' := by
  apply Ideal.span_le.mpr
  rintro p ⟨r,a,b,c,s,h2,hR,hs,rfl⟩
  exact polarRange_coeff_mem m R' r a b c s h2 (by omega) hs

theorem quadraticCubicPolarIdeal_le_polarRange (m R : ℕ) (hR : 3 ≤ R) :
    quadraticCubicPolarIdeal m ≤ polarRangeIdeal m R := by
  apply Ideal.span_le.mpr
  rintro p ⟨r,a,b,c,s,hr,hs,rfl⟩
  exact polarRange_coeff_mem m R r a b c s (by omega) (by omega) hs

theorem polarRangeIdeal_le_candidate (m R : ℕ) :
    polarRangeIdeal m R ≤ AllM.candidateIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨r,a,b,c,s,h2,hR,hs,rfl⟩
  exact current_orbit_coeff_mem m r a b c s (by omega) hs

theorem polarRange_seed_zero_mem (m R : ℕ) (d : Fin 3)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ polarRangeSeeds m R) :
    g0Deriv m (cubeDirection d) 0 p ∈ polarRangeIdeal m R := by
  obtain ⟨r,a,b,c,s,h2,hR,hs,rfl⟩ := hp
  rw [actual_zero_polar_coefficient]
  fin_cases d
  · change PowerSeries.coeff s (currentMap m (orbit ℂ r (a + 1) b c)) ∈ _
    exact polarRange_coeff_mem m R r (a + 1) b c s h2 hR hs
  · change PowerSeries.coeff s (currentMap m (orbit ℂ r a (b + 1) c)) ∈ _
    exact polarRange_coeff_mem m R r a (b + 1) c s h2 hR hs
  · change PowerSeries.coeff s (currentMap m (orbit ℂ r a b (c + 1))) ∈ _
    exact polarRange_coeff_mem m R r a b (c + 1) s h2 hR hs

theorem polarRangeIdeal_zero_closed (m R : ℕ) (d : Fin 3)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ polarRangeIdeal m R) :
    g0Deriv m (cubeDirection d) 0 p ∈ polarRangeIdeal m R :=
  polar_ideal_span_derivation_closed (g0Deriv m (cubeDirection d) 0)
    (polarRangeSeeds m R) (fun _ hp => polarRange_seed_zero_mem m R d hp) hp

theorem polarRange_iterate_zero_mem (m R : ℕ) (d : Fin 3) (n : ℕ)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ polarRangeIdeal m R) :
    (((g0Deriv m (cubeDirection d) 0 : _ → _)^[n]) p) ∈ polarRangeIdeal m R := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact polarRangeIdeal_zero_closed m R d ih

/-- Every mode on an admissible highest coefficient of power 2..R stays in the
ideal; the power-two lower tail is killed by the linear truncation. -/
theorem polarRange_lower_highest_mem (m R r s ell : ℕ) (d : Fin 3) (h2 : 2 ≤ r)
    (hR : r ≤ R) (hs : m < r + s) :
    g0Deriv m (cubeDirection d) ell (PowerSeries.coeff s (AllM.current m 0 ^ r)) ∈
      polarRangeIdeal m R := by
  obtain ⟨n,rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1,by omega⟩
  rw [actual_lower_highest_coeff_recurrence m n s ell d]
  apply (polarRangeIdeal m R).sub_mem
  · exact polarRangeIdeal_zero_closed m R d
      (polarRange_highest_mem m R (n + 1) (s + ell) h2 hR (by omega))
  · apply (polarRangeIdeal m R).nsmul_mem
    apply Submodule.sum_mem
    intro a ha
    have ha' : a < ell := Finset.mem_range.mp ha
    by_cases hn : n = 1
    · subst hn
      rw [highest_linear_coeff_eq_zero m (s + ell - a) (by omega),mul_zero]
      exact (polarRangeIdeal m R).zero_mem
    · exact (polarRangeIdeal m R).mul_mem_left _
        (polarRange_highest_mem m R n (s + ell - a) (by omega) (by omega) (by omega))

theorem polarRange_lower_coeff_mem (m R r a b c s ell : ℕ) (d : Fin 3) (h2 : 2 ≤ r)
    (hR : r ≤ R) (hs : m < r + s) :
    g0Deriv m (cubeDirection d) ell
      (PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))) ∈ polarRangeIdeal m R := by
  rw [actual_lower_orbit_coeff_eq]
  apply polarRange_iterate_zero_mem m R 2 c
  apply polarRange_iterate_zero_mem m R 1 b
  apply polarRange_iterate_zero_mem m R 0 a
  exact polarRange_lower_highest_mem m R r s ell d h2 hR hs

/-- Stability of the WHOLE powers-2..R ideal under every actual negative mode. -/
theorem polarRangeIdeal_lower_mode (m R : ℕ) (d : Fin 3) (ell : ℕ)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ polarRangeIdeal m R) :
    g0Deriv m (cubeDirection d) ell p ∈ polarRangeIdeal m R := by
  apply polar_ideal_span_derivation_closed (g0Deriv m (cubeDirection d) ell)
    (polarRangeSeeds m R) ?_ hp
  rintro p ⟨r,a,b,c,s,h2,hR,hs,rfl⟩
  exact polarRange_lower_coeff_mem m R r a b c s ell d h2 hR hs

theorem negativeModeWord_mem_polarRange (m R : ℕ) (l : List (Fin 3 × ℕ))
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ polarRangeIdeal m R) :
    negativeModeWord m l p ∈ polarRangeIdeal m R := by
  induction l with
  | nil => exact hp
  | cons x l ih => exact polarRangeIdeal_lower_mode m R x.1 x.2 ih

theorem negativeModeWord_congr_polarRange (m R : ℕ) (l : List (Fin 3 × ℕ))
    {p q : MvPolynomial (Vars m) ℂ} (h : p - q ∈ polarRangeIdeal m R) :
    negativeModeWord m l p - negativeModeWord m l q ∈ polarRangeIdeal m R := by
  rw [← negativeModeWord_sub]
  exact negativeModeWord_mem_polarRange m R l h

theorem polarRange_difference_trans (m R : ℕ) {p q r : MvPolynomial (Vars m) ℂ}
    (hp : p - q ∈ polarRangeIdeal m R) (hq : q - r ∈ polarRangeIdeal m R) :
    p - r ∈ polarRangeIdeal m R := by
  have he : p - r = (p - q) + (q - r) := by ring
  rw [he]
  exact (polarRangeIdeal m R).add_mem hp hq

/-! ### The top (highest-color) analogue and plain shifts -/

/-- Admissible whole top coefficients of every source power from 2 to R. -/
def topPolarRangeSeeds (m R : ℕ) : Set (TopPoly m) :=
  {p | ∃ r s, 2 ≤ r ∧ r ≤ R ∧ m < r + s ∧ p = PowerSeries.coeff s (topCurrent m ^ r)}

def topPolarRangeIdeal (m R : ℕ) : Ideal (TopPoly m) :=
  Ideal.span (topPolarRangeSeeds m R)

theorem topPolarRange_coeff_mem (m R r s : ℕ) (h2 : 2 ≤ r) (hR : r ≤ R) (hs : m < r + s) :
    PowerSeries.coeff s (topCurrent m ^ r) ∈ topPolarRangeIdeal m R :=
  Ideal.subset_span ⟨r,s,h2,hR,hs,rfl⟩

theorem topShift_seed_mem_topPolarRange (m R r s ell : ℕ) (h2 : 2 ≤ r) (hR : r ≤ R)
    (hs : m < r + s) :
    topShift m ell (PowerSeries.coeff s (topCurrent m ^ r)) ∈ topPolarRangeIdeal m R := by
  obtain ⟨n,rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1,by omega⟩
  rw [topShift_highest_coeff_recurrence m n s ell]
  apply (topPolarRangeIdeal m R).sub_mem
  · exact (topPolarRangeIdeal m R).nsmul_mem
      (topPolarRange_coeff_mem m R (n + 1) (s + ell) h2 hR (by omega)) _
  · apply (topPolarRangeIdeal m R).nsmul_mem
    apply Submodule.sum_mem
    intro a ha
    have ha' : a < ell := Finset.mem_range.mp ha
    by_cases hn : n = 1
    · subst hn
      rw [topLinear_coeff_high m (s + ell - a) (by omega),mul_zero]
      exact (topPolarRangeIdeal m R).zero_mem
    · exact (topPolarRangeIdeal m R).mul_mem_left _
        (topPolarRange_coeff_mem m R n (s + ell - a) (by omega) (by omega) (by omega))

/-- The literal top powers-2..R ideal is preserved by every plain shift mode. -/
theorem topPolarRangeIdeal_shift_closed (m R ell : ℕ) {p : TopPoly m}
    (hp : p ∈ topPolarRangeIdeal m R) :
    topShift m ell p ∈ topPolarRangeIdeal m R := by
  apply polar_ideal_span_derivation_closed (topShift m ell) (topPolarRangeSeeds m R) ?_ hp
  rintro p ⟨r,s,h2,hR,hs,rfl⟩
  exact topShift_seed_mem_topPolarRange m R r s ell h2 hR hs

theorem topShiftWord_mem_topPolarRange (m R : ℕ) (ks : List ℕ) {p : TopPoly m}
    (hp : p ∈ topPolarRangeIdeal m R) :
    topShiftWord m ks p ∈ topPolarRangeIdeal m R := by
  induction ks with
  | nil => exact hp
  | cons k ks ih => exact topPolarRangeIdeal_shift_closed m R k ih

/-- The image of the whole top ideal consists of actual powers-2..R members. -/
theorem topMap_topPolarRange_mem (m R : ℕ) {p : TopPoly m}
    (hp : p ∈ topPolarRangeIdeal m R) :
    topMap m p ∈ polarRangeIdeal m R := by
  have hle : (topPolarRangeIdeal m R).map (topMap m).toRingHom ≤ polarRangeIdeal m R := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro p ⟨r,s,h2,hR,hs,rfl⟩
    change topMap m (PowerSeries.coeff s (topCurrent m ^ r)) ∈ polarRangeIdeal m R
    rw [topMap_seed]
    exact polarRange_highest_mem m R r s h2 hR hs
  exact hle (Ideal.mem_map_of_mem (topMap m).toRingHom hp)

/-! ### Static reduction of power-(n+1) sources modulo powers 2..n -/

/-- A power-(n+1) plain-shift step is the shifted static coefficient times n+1. -/
theorem topShift_step_mem_topPolarRange (m n s ell : ℕ) (hn : 2 ≤ n)
    (hs : m < n + 1 + s) :
    topShift m ell (PowerSeries.coeff s (topCurrent m ^ (n + 1))) -
      (n + 1) • PowerSeries.coeff (s + ell) (topCurrent m ^ (n + 1)) ∈
      topPolarRangeIdeal m n := by
  rw [topShift_highest_coeff_recurrence m n s ell,sub_right_comm,sub_self,zero_sub]
  apply (topPolarRangeIdeal m n).neg_mem
  apply (topPolarRangeIdeal m n).nsmul_mem
  apply Submodule.sum_mem
  intro a ha
  have ha' : a < ell := Finset.mem_range.mp ha
  exact (topPolarRangeIdeal m n).mul_mem_left _
    (topPolarRange_coeff_mem m n n (s + ell - a) hn le_rfl (by omega))

theorem topShiftWord_static_mem_topPolarRange (m n s : ℕ) (ks : List ℕ) (hn : 2 ≤ n)
    (hs : m < n + 1 + s) :
    topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ (n + 1))) -
      ((n + 1) ^ ks.length) • PowerSeries.coeff (s + ks.sum) (topCurrent m ^ (n + 1)) ∈
      topPolarRangeIdeal m n := by
  induction ks with
  | nil =>
      simp only [topShiftWord,List.length_nil,List.sum_nil,pow_zero,one_nsmul,
        Nat.add_zero,sub_self]
      exact (topPolarRangeIdeal m n).zero_mem
  | cons k ks ih =>
      let t := s + ks.sum
      let N := (n + 1) ^ ks.length
      have hpres :
          topShift m k (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ (n + 1)))) -
            N • topShift m k (PowerSeries.coeff t (topCurrent m ^ (n + 1))) ∈
          topPolarRangeIdeal m n := by
        simpa only [map_sub,map_nsmul] using topPolarRangeIdeal_shift_closed m n k ih
      have hstep := (topPolarRangeIdeal m n).nsmul_mem
        (topShift_step_mem_topPolarRange m n t k hn (by dsimp [t]; omega)) N
      rw [nsmul_sub,smul_smul] at hstep
      have hsum := (topPolarRangeIdeal m n).add_mem hpres hstep
      have htel :
          (topShift m k (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ (n + 1)))) -
              N • topShift m k (PowerSeries.coeff t (topCurrent m ^ (n + 1)))) +
            (N • topShift m k (PowerSeries.coeff t (topCurrent m ^ (n + 1))) -
              (N * (n + 1)) • PowerSeries.coeff (t + k) (topCurrent m ^ (n + 1))) =
          topShift m k (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ (n + 1)))) -
            (N * (n + 1)) • PowerSeries.coeff (t + k) (topCurrent m ^ (n + 1)) := by abel
      rw [htel] at hsum
      have hidx : t + k = s + (k :: ks).sum := by
        simp only [t,List.sum_cons]
        omega
      rw [hidx] at hsum
      simpa only [topShiftWord,List.length_cons,pow_succ,N] using hsum

/-- An arbitrary-mode lowering of a power-(n+1) highest coefficient differs from
the shifted zero-mode lowering by a powers-2..n member. -/
theorem highest_mode_step_mem_polarRange (m n s ell : ℕ) (d : Fin 3) (hn : 2 ≤ n)
    (hs : m < n + 1 + s) :
    g0Deriv m (cubeDirection d) ell (PowerSeries.coeff s (AllM.current m 0 ^ (n + 1))) -
      g0Deriv m (cubeDirection d) 0
        (PowerSeries.coeff (s + ell) (AllM.current m 0 ^ (n + 1))) ∈
      polarRangeIdeal m n := by
  rw [actual_lower_highest_coeff_recurrence m n s ell d,sub_right_comm,sub_self,zero_sub]
  apply (polarRangeIdeal m n).neg_mem
  apply (polarRangeIdeal m n).nsmul_mem
  apply Submodule.sum_mem
  intro a ha
  have ha' : a < ell := Finset.mem_range.mp ha
  exact (polarRangeIdeal m n).mul_mem_left _
    (polarRange_highest_mem m n n (s + ell - a) hn le_rfl (by omega))

theorem polar_mode_step_mem_polarRange (m n a b c s ell : ℕ) (d : Fin 3) (hn : 2 ≤ n)
    (hs : m < n + 1 + s) :
    g0Deriv m (cubeDirection d) ell
        (PowerSeries.coeff s (currentMap m (orbit ℂ (n + 1) a b c))) -
      g0Deriv m (cubeDirection d) 0
        (PowerSeries.coeff (s + ell) (currentMap m (orbit ℂ (n + 1) a b c))) ∈
      polarRangeIdeal m n := by
  rw [actual_lower_orbit_coeff_eq m (n + 1) a b c s ell d,
    actual_lower_orbit_coeff_eq m (n + 1) a b c (s + ell) 0 d]
  have h := polarRange_iterate_zero_mem m n 2 c
    (polarRange_iterate_zero_mem m n 1 b (polarRange_iterate_zero_mem m n 0 a
      (highest_mode_step_mem_polarRange m n s ell d hn hs)))
  simpa only [VariablePower.iterate_deriv_sub] using h

/-- Every negative word on an admissible power-(n+1) polar reduces modulo the
powers-2..n ideal to one static polar, with exact index and lowering counts. -/
theorem negativeModeWord_static_mem_polarRange (m n s a b c : ℕ) (l : List (Fin 3 × ℕ))
    (hn : 2 ≤ n) (hs : m < n + 1 + s) :
    negativeModeWord m l (PowerSeries.coeff s (currentMap m (orbit ℂ (n + 1) a b c))) -
      PowerSeries.coeff (s + (l.map Prod.snd).sum)
        (currentMap m (orbit ℂ (n + 1) (a + negativeModeAxisCount 0 l)
          (b + negativeModeAxisCount 1 l) (c + negativeModeAxisCount 2 l))) ∈
      polarRangeIdeal m n := by
  induction l with
  | nil =>
      simp only [negativeModeWord,negativeModeAxisCount,List.map_nil,List.sum_nil,
        Nat.add_zero,sub_self]
      exact (polarRangeIdeal m n).zero_mem
  | cons x l ih =>
      rcases x with ⟨d,ell⟩
      let t := s + (l.map Prod.snd).sum
      let a' := a + negativeModeAxisCount 0 l
      let b' := b + negativeModeAxisCount 1 l
      let c' := c + negativeModeAxisCount 2 l
      have hpres :
          g0Deriv m (cubeDirection d) ell
              (negativeModeWord m l
                (PowerSeries.coeff s (currentMap m (orbit ℂ (n + 1) a b c)))) -
            g0Deriv m (cubeDirection d) ell
              (PowerSeries.coeff t (currentMap m (orbit ℂ (n + 1) a' b' c'))) ∈
          polarRangeIdeal m n := by
        simpa only [negativeModeWord] using
          negativeModeWord_congr_polarRange m n [(d,ell)] ih
      have hstep := polar_mode_step_mem_polarRange m n a' b' c' t ell d hn
        (by dsimp [t]; omega)
      have hsum := polarRange_difference_trans m n hpres hstep
      rw [actual_zero_polar_coefficient] at hsum
      fin_cases d <;>
        simpa [negativeModeWord,negativeModeAxisCount,polarZeroStep,t,a',b',c',
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsum

/-- MAIN: mixed top-shift and negative words on a power-(n+1) source reduce
modulo the powers-2..n ideal to (n+1)^(number of shifts) times one static polar. -/
theorem shift_negativeModeWord_static_mem_polarRange (m n s : ℕ) (ks : List ℕ)
    (l : List (Fin 3 × ℕ)) (hn : 2 ≤ n) (hs : m < n + 1 + s) :
    negativeModeWord m l
        (topMap m (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ (n + 1))))) -
      ((n + 1) ^ ks.length) • PowerSeries.coeff (s + ks.sum + (l.map Prod.snd).sum)
        (currentMap m (orbit ℂ (n + 1) (negativeModeAxisCount 0 l)
          (negativeModeAxisCount 1 l) (negativeModeAxisCount 2 l))) ∈
      polarRangeIdeal m n := by
  have hshift := topMap_topPolarRange_mem m n
    (topShiftWord_static_mem_topPolarRange m n s ks hn hs)
  rw [map_sub,map_nsmul,topMap_seed] at hshift
  have hnegative := negativeModeWord_congr_polarRange m n l hshift
  rw [negativeModeWord_nsmul] at hnegative
  have hstatic := negativeModeWord_static_mem_polarRange m n (s + ks.sum) 0 0 0 l hn
    (by omega)
  have hzero : currentMap m (orbit ℂ (n + 1) 0 0 0) = AllM.current m 0 ^ (n + 1) := by
    rw [currentMap_orbit]
    rfl
  simp only [hzero,Nat.zero_add] at hstatic
  have hscaled := (polarRangeIdeal m n).nsmul_mem hstatic ((n + 1) ^ ks.length)
  rw [nsmul_sub] at hscaled
  exact polarRange_difference_trans m n hnegative hscaled

end
#print axioms quadraticCubicPolarIdeal_le_polarRange
#print axioms polarRangeIdeal_le_candidate
#print axioms polarRangeIdeal_lower_mode
#print axioms topPolarRangeIdeal_shift_closed
#print axioms topMap_topPolarRange_mem
#print axioms shift_negativeModeWord_static_mem_polarRange
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
