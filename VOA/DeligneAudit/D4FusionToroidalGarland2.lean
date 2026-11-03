import VOA.DeligneAudit.D4FusionToroidalGarlandSymbol

/-!
# Further Garland symbol reductions

The general filtration lemma applies to words of any length.  The low multiplicities
of the full `JprimeLeAnnGr` proposition follow from the established `j = 1` case.
The cubic identity records the first correction term in the uniform lift formula.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
  VOA.DeligneAudit.SectorWeyl

noncomputable section

/-- A word on the universal generator lies in every step up to its symbol degree. -/
theorem d4_word_mem (m : ℕ) (hm : 1 ≤ m) (l : List (Ltr 28)) (j : ℕ)
    (hj : j ≤ symbolDegree m l) :
    wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l (d4Gen m) ∈
      TU D4sector.f (ravFam D4sector m 0) m j := by
  have h := word_mem_shift D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm l 0 (d4Gen m)
    (by rw [TU_zero]; trivial)
  exact TU_mono _ _ _ (by simpa using hj) (by simpa using h)

/-- A word with one more unit of symbol degree has zero class in grade `j`. -/
theorem d4_word_symbol_zero (m : ℕ) (hm : 1 ≤ m) (l : List (Ltr 28)) (j : ℕ)
    (hj : j + 1 ≤ symbolDegree m l) :
    symbL m j ⟨wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l
      (d4Gen m), d4_word_mem m hm l j (by omega)⟩ = 0 := by
  exact symbL_zero m j _ (d4_word_mem m hm l (j + 1) hj)

/-- One shifted theta mode raises the filtration by at least one step. -/
theorem d4_high_step_mem (m : ℕ) (hm : 1 ≤ m) (s j : ℕ)
    (x : UModG D4sector.f (ravFam D4sector m 0))
    (hx : x ∈ TU D4sector.f (ravFam D4sector m 0) m j) :
    d4Ftheta m (m + s) x ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
  have h := word_mem_shift D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm
    [(D4sector.c₀, m + s)] j x hx
  have hd := d4_div_ge_one m hm s
  have h' : d4Ftheta m (m + s) x ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + (m + s) / m) := by
    simpa [wordOp, symbolDegree, d4Ftheta] using h
  exact TU_mono _ _ _ (by omega) h'

/-- An out-of-range residual high mode gives zero in its nominal graded step. -/
theorem d4_high_step_deep (m : ℕ) (hm : 1 ≤ m) (s j : ℕ) (hs : m ≤ s)
    (x : UModG D4sector.f (ravFam D4sector m 0))
    (hx : x ∈ TU D4sector.f (ravFam D4sector m 0) m j) :
    d4Ftheta m (m + s) x ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 2) := by
  have h := word_mem_shift D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm
    [(D4sector.c₀, m + s)] j x hx
  have hd := d4_div_ge_two m hm s hs
  have h' : d4Ftheta m (m + s) x ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + (m + s) / m) := by
    simpa [wordOp, symbolDegree, d4Ftheta] using h
  exact TU_mono _ _ _ (by omega) h'

/-- The high theta symbol agrees with its shifted lift on every homogeneous class. -/
theorem d4_grOp_high_single (m : ℕ) (hm : 1 ≤ m) (s j : ℕ)
    (x : UModG D4sector.f (ravFam D4sector m 0))
    (hx : x ∈ TU D4sector.f (ravFam D4sector m 0) m j) :
    (grToroidal_D4 m hm).op D4sector.c₀ 1 s (symbL m j ⟨x, hx⟩) =
      symbL m (j + 1) ⟨d4Ftheta m (m + s) x,
        d4_high_step_mem m hm s j x hx⟩ := by
  by_cases hs : s < m
  · rw [grToroidal_D4_op, symbL_apply,
      grOp_single D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 1 s j x hs hx,
      symbL_apply]
    congr 1
    apply Subtype.ext
    simp [gradedSingle, d4Ftheta]
  · rw [grToroidal_D4_op,
      grOp_high_zero D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 1 s
        (Nat.le_of_not_lt hs), LinearMap.zero_apply]
    exact (symbL_zero m (j + 1) _
      (d4_high_step_deep m hm s j (Nat.le_of_not_lt hs) x hx)).symm

/-- The ordered sum of `j` high theta modes, before taking its graded symbol. -/
def d4_highPow (m : ℕ) : ℕ → ℕ →
    UModG D4sector.f (ravFam D4sector m 0) →
      UModG D4sector.f (ravFam D4sector m 0)
  | 0, s, x => if s = 0 then x else 0
  | j + 1, s, x => ∑ p ∈ Finset.antidiagonal s,
      d4Ftheta m (m + p.1) (d4_highPow m j p.2 x)

/-- The high-mode sum raises the filtration by at least `j`. -/
theorem d4_highPow_mem (m : ℕ) (hm : 1 ≤ m) :
    ∀ (j s k : ℕ) (x : UModG D4sector.f (ravFam D4sector m 0)),
      x ∈ TU D4sector.f (ravFam D4sector m 0) m k →
      d4_highPow m j s x ∈ TU D4sector.f (ravFam D4sector m 0) m (k + j)
  | 0, s, k, x, hx => by
      simp only [d4_highPow, Nat.add_zero]
      split_ifs
      · exact hx
      · exact Submodule.zero_mem _
  | j + 1, s, k, x, hx => by
      change (∑ p ∈ Finset.antidiagonal s,
        d4Ftheta m (m + p.1) (d4_highPow m j p.2 x)) ∈
          TU D4sector.f (ravFam D4sector m 0) m (k + (j + 1))
      apply Submodule.sum_mem
      intro p hp
      have h := d4_high_step_mem m hm p.1 (k + j) (d4_highPow m j p.2 x)
        (d4_highPow_mem m hm j p.2 k x hx)
      simpa only [Nat.add_assoc] using h

theorem d4_highPow_gen_mem (m : ℕ) (hm : 1 ≤ m) (j s : ℕ) :
    d4_highPow m j s (d4Gen m) ∈
      TU D4sector.f (ravFam D4sector m 0) m j := by
  simpa using d4_highPow_mem m hm j s 0 (d4Gen m) (by rw [TU_zero]; trivial)

/-- The toroidal high-mode power is the graded class of its universal lift. -/
theorem d4_gpow_symbol (m : ℕ) (hm : 1 ≤ m) : ∀ j s,
    gpow (grToroidal_D4 m hm) D4sector.c₀ j s
      (grGenerator D4sector.f (ravFam D4sector m 0) m) =
    symbL m j ⟨d4_highPow m j s (d4Gen m), d4_highPow_gen_mem m hm j s⟩
  | 0, s => by
      by_cases hs : s = 0
      · subst s
        change grGenerator D4sector.f (ravFam D4sector m 0) m =
          symbL m 0 ⟨d4Gen m, d4_highPow_gen_mem m hm 0 0⟩
        rfl
      · simp only [gpow, d4_highPow, if_neg hs]
        change (0 : Gr D4sector.f (ravFam D4sector m 0) m) =
          symbL m 0 (0 : TU D4sector.f (ravFam D4sector m 0) m 0)
        simp
  | j + 1, s => by
      change (∑ p ∈ Finset.antidiagonal s,
        (grToroidal_D4 m hm).op D4sector.c₀ 1 p.1
          (gpow (grToroidal_D4 m hm) D4sector.c₀ j p.2
            (grGenerator D4sector.f (ravFam D4sector m 0) m))) =
        symbL m (j + 1) ⟨∑ p ∈ Finset.antidiagonal s,
          d4Ftheta m (m + p.1) (d4_highPow m j p.2 (d4Gen m)),
          d4_highPow_gen_mem m hm (j + 1) s⟩
      simp_rw [d4_gpow_symbol m hm j]
      rw [Finset.sum_congr rfl (fun p _ =>
        d4_grOp_high_single m hm p.1 j (d4_highPow m j p.2 (d4Gen m))
          (d4_highPow_gen_mem m hm j p.2)), ← map_sum]
      congr 1
      apply Subtype.ext
      simp

/-- A theta mode preserves the filtration, regardless of its index. -/
theorem d4_low_step_mem (m : ℕ) (hm : 1 ≤ m) (r j : ℕ)
    (x : UModG D4sector.f (ravFam D4sector m 0))
    (hx : x ∈ TU D4sector.f (ravFam D4sector m 0) m j) :
    d4Ftheta m r x ∈ TU D4sector.f (ravFam D4sector m 0) m j := by
  have h := word_mem_shift D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm
    [(D4sector.c₀, r)] j x hx
  have h' : d4Ftheta m r x ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + r / m) := by
    simpa [wordOp, symbolDegree, d4Ftheta] using h
  exact TU_mono _ _ _ (Nat.le_add_right j (r / m)) h'

/-- A theta mode at least `m` lies one step deeper than its nominal low symbol. -/
theorem d4_low_step_deep (m : ℕ) (hm : 1 ≤ m) (r j : ℕ) (hr : m ≤ r)
    (x : UModG D4sector.f (ravFam D4sector m 0))
    (hx : x ∈ TU D4sector.f (ravFam D4sector m 0) m j) :
    d4Ftheta m r x ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
  have h := word_mem_shift D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm
    [(D4sector.c₀, r)] j x hx
  have hd := d4_div_ge_one' m hm r hr
  have h' : d4Ftheta m r x ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + r / m) := by
    simpa [wordOp, symbolDegree, d4Ftheta] using h
  exact TU_mono _ _ _ (by omega) h'

/-- The low theta symbol agrees with its lift on every homogeneous class. -/
theorem d4_grOp_low_single (m : ℕ) (hm : 1 ≤ m) (r j : ℕ)
    (x : UModG D4sector.f (ravFam D4sector m 0))
    (hx : x ∈ TU D4sector.f (ravFam D4sector m 0) m j) :
    (grToroidal_D4 m hm).op D4sector.c₀ 0 r (symbL m j ⟨x, hx⟩) =
      symbL m j ⟨d4Ftheta m r x, d4_low_step_mem m hm r j x hx⟩ := by
  by_cases hr : r < m
  · rw [grToroidal_D4_op, symbL_apply,
      grOp_single D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 0 r j x hr hx,
      symbL_apply]
    congr 1
    apply Subtype.ext
    simp [gradedSingle, d4Ftheta]
  · rw [grToroidal_D4_op,
      grOp_high_zero D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 0 r
        (Nat.le_of_not_lt hr), LinearMap.zero_apply]
    exact (symbL_zero m j _
      (d4_low_step_deep m hm r j (Nat.le_of_not_lt hr) x hx)).symm

/-- The universal lift of the full symbol `P^(j)_N`. -/
def d4_PsymLift (m j N : ℕ) : UModG D4sector.f (ravFam D4sector m 0) :=
  ∑ p ∈ Finset.antidiagonal N,
    d4Ftheta m p.1 (d4_highPow m j p.2 (d4Gen m))

theorem d4_PsymLift_mem (m : ℕ) (hm : 1 ≤ m) (j N : ℕ) :
    d4_PsymLift m j N ∈ TU D4sector.f (ravFam D4sector m 0) m j := by
  unfold d4_PsymLift
  apply Submodule.sum_mem
  intro p hp
  exact d4_low_step_mem m hm p.1 j _ (d4_highPow_gen_mem m hm j p.2)

/-- The abstract Garland symbol is precisely the class of its explicit lift. -/
theorem d4_Psym_symbol (m : ℕ) (hm : 1 ≤ m) (j N : ℕ) :
    Psym (grToroidal_D4 m hm) D4sector.c₀ j N
      (grGenerator D4sector.f (ravFam D4sector m 0) m) =
      symbL m j ⟨d4_PsymLift m j N, d4_PsymLift_mem m hm j N⟩ := by
  change (∑ p ∈ Finset.antidiagonal N,
    (grToroidal_D4 m hm).op D4sector.c₀ 0 p.1
      (gpow (grToroidal_D4 m hm) D4sector.c₀ j p.2
        (grGenerator D4sector.f (ravFam D4sector m 0) m))) = _
  simp_rw [d4_gpow_symbol m hm j]
  rw [Finset.sum_congr rfl (fun p _ =>
    d4_grOp_low_single m hm p.1 j (d4_highPow m j p.2 (d4Gen m))
      (d4_highPow_gen_mem m hm j p.2)), ← map_sum]
  congr 1
  apply Subtype.ext
  simp [d4_PsymLift]

/-- The part of the lift whose outer theta mode is below `m`. -/
def d4_lowLift (m j N : ℕ) : UModG D4sector.f (ravFam D4sector m 0) :=
  ∑ p ∈ Finset.antidiagonal N,
    if p.1 < m then d4Ftheta m p.1 (d4_highPow m j p.2 (d4Gen m)) else 0

/-- The outer-high terms, which are invisible in grade `j`. -/
def d4_outerHigh (m j N : ℕ) : UModG D4sector.f (ravFam D4sector m 0) :=
  ∑ p ∈ Finset.antidiagonal N,
    if m ≤ p.1 then d4Ftheta m p.1 (d4_highPow m j p.2 (d4Gen m)) else 0

theorem d4_PsymLift_split (m j N : ℕ) :
    d4_PsymLift m j N = d4_lowLift m j N + d4_outerHigh m j N := by
  unfold d4_PsymLift d4_lowLift d4_outerHigh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.1 < m
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem d4_outerHigh_mem (m : ℕ) (hm : 1 ≤ m) (j N : ℕ) :
    d4_outerHigh m j N ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
  unfold d4_outerHigh
  apply Submodule.sum_mem
  intro p hp
  by_cases h : m ≤ p.1
  · rw [if_pos h]
    exact d4_low_step_deep m hm p.1 j h _ (d4_highPow_gen_mem m hm j p.2)
  · rw [if_neg h]
    exact Submodule.zero_mem _

/-- The all-high term in the corrected Garland lift; it is zero when `N < m`. -/
def d4_correction (m j N : ℕ) : UModG D4sector.f (ravFam D4sector m 0) :=
  if m ≤ N then d4_highPow m (j + 1) (N - m) (d4Gen m) else 0

theorem d4_correction_mem (m : ℕ) (hm : 1 ≤ m) (j N : ℕ) :
    d4_correction m j N ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
  unfold d4_correction
  split_ifs
  · exact d4_highPow_gen_mem m hm (j + 1) (N - m)
  · exact Submodule.zero_mem _

/-- The candidate annihilating lift from the uniform Garland identity. -/
def d4_correctedLift (m j N : ℕ) : UModG D4sector.f (ravFam D4sector m 0) :=
  d4_lowLift m j N + ((j : ℂ) / (j + 1)) • d4_correction m j N

theorem d4_PsymLift_deep_of_corrected_zero (m : ℕ) (hm : 1 ≤ m) (j N : ℕ)
    (h : d4_correctedLift m j N = 0) :
    d4_PsymLift m j N ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
  have hs : d4_lowLift m j N + ((j : ℂ) / (j + 1)) •
      d4_correction m j N ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
    change d4_correctedLift m j N ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 1)
    rw [h]
    exact Submodule.zero_mem _
  have hc := Submodule.smul_mem
    (TU D4sector.f (ravFam D4sector m 0) m (j + 1))
    ((j : ℂ) / (j + 1)) (d4_correction_mem m hm j N)
  have hh := Submodule.add_mem
    (TU D4sector.f (ravFam D4sector m 0) m (j + 1)) hs
    (Submodule.neg_mem _ hc)
  have hlow : d4_lowLift m j N ∈
      TU D4sector.f (ravFam D4sector m 0) m (j + 1) := by
    convert hh using 1
    abel
  rw [d4_PsymLift_split]
  exact Submodule.add_mem _ hlow (d4_outerHigh_mem m hm j N)

/-- Every theta mode from `2*m` onward kills the universal generator. -/
theorem d4Ftheta_high_zero (m r : ℕ) (hr : 2 * m ≤ r) :
    d4Ftheta m r (d4Gen m) = 0 := by
  have h := d4_garland_univ m 1 r (by omega) (by omega)
  simpa only [garlandVec_one] using h

/-- An `a`-fold low-mode multiplication of a Garland coefficient. -/
def d4_lowGarland (m k : ℕ) : ℕ → ℕ →
    UModG D4sector.f (ravFam D4sector m 0)
  | 0, M => garlandVec (d4Ftheta m) k M (d4Gen m)
  | a + 1, M => ∑ r ∈ Finset.range m,
      if r ≤ M then d4Ftheta m r (d4_lowGarland m k a (M - r)) else 0

/-- Each low-mode multiple vanishes in the corresponding sharp Garland range. -/
theorem d4_lowGarland_zero (m k a M : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hM : 2 * m + 1 + a * (m - 1) ≤ k + M) :
    d4_lowGarland m k a M = 0 := by
  induction a generalizing M with
  | zero =>
      change garlandVec (d4Ftheta m) k M (d4Gen m) = 0
      exact d4_garland_univ m k M hk (by simpa using hM)
  | succ a ih =>
      change (∑ r ∈ Finset.range m,
        if r ≤ M then d4Ftheta m r (d4_lowGarland m k a (M - r)) else 0) = 0
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hrM : r ≤ M
      · rw [if_pos hrM]
        have hrm : r < m := Finset.mem_range.mp hr
        have hbound : 2 * m + 1 + a * (m - 1) ≤ k + (M - r) := by
          have hsmall : r ≤ m - 1 := by omega
          have heq : (a + 1) * (m - 1) = a * (m - 1) + (m - 1) := by ring
          rw [heq] at hM
          omega
        rw [ih (M - r) hbound, map_zero]
      · rw [if_neg hrM]

/-- Every Garland coefficient used in the corrected lift vanishes in the target range. -/
theorem d4_lowGarland_target_zero (m j N a : ℕ) (hm : 1 ≤ m)
    (ha : a < j) (hN : m ≤ N + j) :
    d4_lowGarland m (j + 1 - a) a (N + j * m) = 0 := by
  have hja : a + 1 ≤ j := by omega
  have hrel : a * (m - 1) + a = a * m := by
    calc
      a * (m - 1) + a = a * ((m - 1) + 1) := by ring
      _ = a * m := by rw [Nat.sub_add_cancel hm]
  have hjm : a * m + m ≤ j * m := by
    simpa only [add_mul, one_mul] using Nat.mul_le_mul_right m hja
  have hk : 1 ≤ j + 1 - a := by omega
  apply d4_lowGarland_zero m (j + 1 - a) a (N + j * m) hm hk
  omega

/-- The cubic correction identity, for commuting scalar variables. -/
theorem garland_cubic_identity (x y : ℂ) :
    (2 / 3 : ℂ) * (x + y) ^ 3 - x * (x + y) ^ 2 =
      x * y ^ 2 + (2 / 3 : ℂ) * y ^ 3 - (1 / 3 : ℂ) * x ^ 3 := by
  ring

/-- Coefficients in the uniform formal-power-series identity. -/
def d4_identityCoeff (j a : ℕ) : ℂ :=
  (-1 : ℂ) ^ a * ((j : ℂ) * (Nat.choose j a : ℂ) -
    (if a = 0 then 0 else (Nat.choose j (a - 1) : ℂ))) / (j + 1)

/-- The precise remaining algebraic identity for the corrected universal lift. -/
def D4CorrectedLiftExpansion (m : ℕ) : Prop :=
  ∀ j N, 1 ≤ j → j + 1 ≤ m → m ≤ N + j →
    d4_correctedLift m j N =
      ∑ a ∈ Finset.range j,
        d4_identityCoeff j a • d4_lowGarland m (j + 1 - a) a (N + j * m)

theorem d4_correctedLift_zero_of_expansion (m : ℕ) (hm : 1 ≤ m)
    (h : D4CorrectedLiftExpansion m) (j N : ℕ)
    (hj : 1 ≤ j) (hjm : j + 1 ≤ m) (hN : m ≤ N + j) :
    d4_correctedLift m j N = 0 := by
  rw [h j N hj hjm hN]
  apply Finset.sum_eq_zero
  intro a ha
  rw [d4_lowGarland_target_zero m j N a hm (Finset.mem_range.mp ha) hN]
  simp

/-- The full package reduces to its higher Garland symbols. -/
theorem Jprime_le_annGr_of_Psym (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ j N, 1 ≤ j → j + 1 ≤ m → m ≤ N + j →
      Psym (grToroidal_D4 m hm) D4sector.c₀ j N
        (grGenerator D4sector.f (ravFam D4sector m 0) m) = 0) :
    JprimeLeAnnGr m hm := by
  intro ρ hρ
  rcases hρ with ht | ⟨j, N, hj, hjm, hN, rfl⟩
  · exact Jsymbols_le_annGr m hm ht
  · exact h j N hj hjm hN

/-- The exact missing lift equation implies the full annihilator package. -/
theorem Jprime_le_annGr_of_corrected_zero (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ j N, 1 ≤ j → j + 1 ≤ m → m ≤ N + j →
      d4_correctedLift m j N = 0) : JprimeLeAnnGr m hm := by
  apply Jprime_le_annGr_of_Psym
  intro j N hj hjm hN
  rw [d4_Psym_symbol m hm j N]
  exact symbL_zero m j _ (d4_PsymLift_deep_of_corrected_zero m hm j N
    (h j N hj hjm hN))

/-- The formal expansion, once proved, closes the full `Jprime` package. -/
theorem Jprime_le_annGr_of_expansion (m : ℕ) (hm : 1 ≤ m)
    (h : D4CorrectedLiftExpansion m) : JprimeLeAnnGr m hm := by
  apply Jprime_le_annGr_of_corrected_zero m hm
  intro j N hj hjm hN
  exact d4_correctedLift_zero_of_expansion m hm h j N hj hjm hN

/-- At multiplicity one, `Jprime` has no additional symbols. -/
theorem Jprime_le_annGr_one : JprimeLeAnnGr 1 (by omega) := by
  apply Jprime_le_annGr_of_Psym
  intro j N hj hjm hN
  omega

/-- At multiplicity two, the existing quadratic Garland proof covers `Jprime`. -/
theorem Jprime_le_annGr_two : JprimeLeAnnGr 2 (by omega) := by
  apply Jprime_le_annGr_of_Psym
  intro j N hj hjm hN
  have hj1 : j = 1 := by omega
  subst j
  exact garland_symbol_zero 2 (by omega) N (by omega)

end

end VOA.DeligneAudit.Toroidal

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.d4_word_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_word_symbol_zero
#print axioms VOA.DeligneAudit.Toroidal.d4_high_step_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_high_step_deep
#print axioms VOA.DeligneAudit.Toroidal.d4_grOp_high_single
#print axioms VOA.DeligneAudit.Toroidal.d4_highPow_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_gpow_symbol
#print axioms VOA.DeligneAudit.Toroidal.d4_low_step_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_low_step_deep
#print axioms VOA.DeligneAudit.Toroidal.d4_grOp_low_single
#print axioms VOA.DeligneAudit.Toroidal.d4_PsymLift_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_Psym_symbol
#print axioms VOA.DeligneAudit.Toroidal.d4_PsymLift_split
#print axioms VOA.DeligneAudit.Toroidal.d4_outerHigh_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_correction_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_PsymLift_deep_of_corrected_zero
#print axioms VOA.DeligneAudit.Toroidal.d4Ftheta_high_zero
#print axioms VOA.DeligneAudit.Toroidal.d4_lowGarland_zero
#print axioms VOA.DeligneAudit.Toroidal.d4_lowGarland_target_zero
#print axioms VOA.DeligneAudit.Toroidal.garland_cubic_identity
#print axioms VOA.DeligneAudit.Toroidal.d4_correctedLift_zero_of_expansion
#print axioms VOA.DeligneAudit.Toroidal.Jprime_le_annGr_of_Psym
#print axioms VOA.DeligneAudit.Toroidal.Jprime_le_annGr_of_corrected_zero
#print axioms VOA.DeligneAudit.Toroidal.Jprime_le_annGr_of_expansion
#print axioms VOA.DeligneAudit.Toroidal.Jprime_le_annGr_one
#print axioms VOA.DeligneAudit.Toroidal.Jprime_le_annGr_two
end AxiomAudit
