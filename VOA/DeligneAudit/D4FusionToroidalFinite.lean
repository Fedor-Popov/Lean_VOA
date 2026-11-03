import VOA.DeligneAudit.D4FusionContactCurrentBound
import VOA.DeligneAudit.D4FusionKernelTheta
import VOA.DeligneAudit.D4FusionTruncatedWeyl
import VOA.DeligneAudit.D4FusionContactPolynomialGrDimensionUniversal
import VOA.DeligneAudit.DeligneFusionFiniteGD4

/-! Finite spanning for the universal D4 Demazure module, without a rank bound. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

private theorem highest_of_rav (h : Sat D4sector.f R w (ravFam D4sector m 0)) :
    HighestRel R w m := by
  rw [ravFam_zero_right] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he r
    exact rs_raising h he r
  · intro c hc r hr
    exact rs_cartan_pos h hc r hr
  · intro c hc
    have hh := rs_cartan_zero h hc
    by_cases h1 : c.val = 1
    · simpa only [D4sector, thetaD4, h1, if_true, Nat.mul_one] using hh
    · simpa only [D4sector, thetaD4, h1, if_false, Nat.mul_zero,
        Nat.cast_zero] using hh
  · intro i
    have hi : D4sector.lowering (leviIndex i) := by
      change 16 ≤ (leviIndex i).val ∧ (leviIndex i).val < 20
      fin_cases i <;> decide
    have he : D4sector.lowExp (leviIndex i) = 0 := by fin_cases i <;> rfl
    have hh := rs_lowering h hi
    simpa only [he, Nat.mul_zero, Nat.zero_add, Function.iterate_one] using hh

private theorem center_pow_of_rav
    (h : Sat D4sector.f R w (ravFam D4sector m 0)) :
    (currentCenter R 0 ^ (2 * m + 1)) w = 0 := by
  rw [ravFam_zero_right] at h
  have hh := d4_thetaNil m V R w
    (fun e he => rs_raising h he 0)
    (fun c hc => rs_cartan_zero h hc)
    (fun c hc => (show False from hc).elim)
    (fun i hi => rs_lowering h hi)
  exact hh

private theorem negative_high_from (h : HighestRel R w m) (i : Fin 12)
    (q r : ℕ) (hq : R.op (negativeIndex i) q w = 0) (hr : q ≤ r) :
    R.op (negativeIndex i) r w = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = q + k := ⟨r - q, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hq
  have hc := R.comm (negativeCartan i) (negativeIndex i) k q w
  rw [hq, map_zero, h.cartan_pos _ (negativeCartan_lt_four i) k hk,
    map_zero, sub_zero] at hc
  have hs : (∑ c : Fin 28, contactF (negativeCartan i) (negativeIndex i) c •
      R.op c (k + q) w) =
      (negativeWeight i : ℂ) • R.op (negativeIndex i) (q + k) w := by
    simp only [negative_cartan_table, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, add_comm k q]
  change 0 = (∑ c : Fin 28, contactF (negativeCartan i) (negativeIndex i) c •
    R.op c (k + q) w) at hc
  rw [hs] at hc
  exact (smul_eq_zero.mp hc.symm).resolve_left (negativeWeight_ne_zero i)

theorem rav_high_kills_generator (hm : 1 ≤ m)
    (h : Sat D4sector.f R w (ravFam D4sector m 0)) :
    ∀ (c : Fin 28) r, 2 * m ≤ r → R.op c r w = 0 := by
  have hs : Sat D4sector.f R w (ravSpec D4sector m (2 * m)) := by
    simpa only [ravFam_zero_right] using h
  have hw := highest_of_rav h
  intro c r hr
  by_cases hc4 : c.val < 4
  · exact hw.cartan_pos c hc4 r (by omega)
  by_cases hc16 : c.val < 16
  · exact hw.raising c (by omega) r
  obtain ⟨i, rfl⟩ := negativeIndex_covers c (by omega)
  by_cases hi : negativeIndex i = D4sector.c₀
  · have hf := rs_fusion hs
      (show D4sector.fusion (negativeIndex i) by
        change 16 ≤ (negativeIndex i).val
        exact negativeIndex_range i)
    have hf' : R.op (negativeIndex i) (2 * m) w = 0 := by
      simpa only [hi, if_pos] using hf
    exact negative_high_from hw i (2 * m) r hf' hr
  · have hf := rs_fusion hs
      (show D4sector.fusion (negativeIndex i) by
        change 16 ≤ (negativeIndex i).val
        exact negativeIndex_range i)
    have hf' : R.op (negativeIndex i) m w = 0 := by
      split_ifs at hf with he
      · exact (hi he).elim
      · exact hf
    exact negative_high_from hw i m r hf' (by omega)

private theorem rav_currentWord_cutoff
    (h : Sat D4sector.f R w (ravFam D4sector m 0))
    (l : List CurrentLetter) (hl : l.length = 2 * m + 1) :
    currentRadicalWord R l w ∈ currentPiece R w (2 * m) := by
  obtain ⟨a, n, c, hp, hperm⟩ := exists_current_normal_form l
  have hlen := current_normal_form_length hperm
  have hsize : a.length + n + c.length = 2 * m + 1 := by omega
  have hcenter := current_center_word_zero_of_pow (highest_of_rav h)
    (center_pow_of_rav h)
  have hN := currentNormal_cutoff_of_center (highest_of_rav h)
    (2 * m + 1) hcenter a n c hp hsize
  have hN' : currentNormal R a n c w ∈ currentPiece R w (2 * m) := by
    simpa only [Nat.add_sub_cancel] using hN
  rw [currentNormal_eq_word] at hN'
  have hperm' : l.Perm (currentNormalList a n c) := by
    simpa only [currentNormalList, List.append_assoc] using hperm
  have hdiff := currentRadicalWord_perm_sub R w hperm'
  have hdiff' : currentRadicalWord R l w -
      currentRadicalWord R (currentNormalList a n c) w ∈
      currentPiece R w (2 * m) :=
    currentPiece_mono R w (by omega) hdiff
  have hh := (currentPiece R w (2 * m)).add_mem hdiff' hN'
  convert hh using 1; abel

private theorem rav_currentPiece_step
    (h : Sat D4sector.f R w (ravFam D4sector m 0)) :
    currentPiece R w (2 * m + 1) ≤ currentPiece R w (2 * m) := by
  rw [currentPiece, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  by_cases hs : l.length ≤ 2 * m
  · exact currentRadicalWord_mem R w l hs
  · exact rav_currentWord_cutoff h l (by omega)

private theorem rav_currentWord_bound
    (h : Sat D4sector.f R w (ravFam D4sector m 0))
    (l : List CurrentLetter) :
    currentRadicalWord R l w ∈ currentPiece R w (2 * m) := by
  induction l with
  | nil => exact current_generator_mem R w (2 * m)
  | cons x l ih =>
      exact rav_currentPiece_step h (current_radical_mem R w x.1 x.2 ih)

private theorem current_word_indices : ∀ (l : List (Fin 28 × ℕ)),
    (∀ x ∈ l, active x.1) → ∃ t : List CurrentLetter,
      l = t.map (fun x => (radIndex x.1, x.2))
  | [], _ => ⟨[], rfl⟩
  | (c, r) :: l, ha => by
      obtain ⟨i, hi⟩ := (active_iff_index c).mp (ha (c, r) (by simp))
      obtain ⟨t, ht⟩ := current_word_indices l (fun x hx => ha x (by simp [hx]))
      exact ⟨(i, r) :: t, by simp only [List.map_cons, ← hi, ← ht]⟩

private theorem rav_cycDeg_currentPiece
    (h : Sat D4sector.f R w (ravFam D4sector m 0)) (d : ℕ) :
    cycDeg R w d ≤ currentPiece R w (2 * m) := by
  apply (cycDeg_le_contact (highest_of_rav h) d).trans
  rw [Submodule.span_le]
  rintro _ ⟨l, _, ha, _, rfl⟩
  obtain ⟨t, rfl⟩ := current_word_indices l ha
  exact rav_currentWord_bound h t

theorem rav_currentPiece_finite
    (hm : 1 ≤ m) (h : Sat D4sector.f R w (ravFam D4sector m 0)) :
    FiniteDimensional ℂ (currentPiece R w (2 * m)) := by
  let A : Set (List (Fin 28 × ℕ)) :=
    {l | l.length ≤ 2 * m ∧ ∀ x ∈ l, x.2 ≤ 2 * m}
  have hA : A.Finite := FiniteG.finite_bounded_listsG (S := D4sector) (2 * m) (2 * m)
  have hspan : currentPiece R w (2 * m) ≤
      Submodule.span ℂ ((fun l => wordOp R l w) '' A) := by
    rw [currentPiece, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    by_cases hbad : ∃ x ∈ l, 2 * m ≤ x.2
    · obtain ⟨x, hx, hr⟩ := hbad
      have hz : wordOp R (l.map fun x => (radIndex x.1, x.2)) w = 0 :=
        wordOp_eq_zero_of_mem R (contact_truncIdeal (2 * m))
          (rav_high_kills_generator hm h) (l.map fun x => (radIndex x.1, x.2))
          ⟨(radIndex x.1, x.2), List.mem_map_of_mem hx, hr⟩
      change wordOp R (l.map fun x => (radIndex x.1, x.2)) w ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨l.map (fun x => (radIndex x.1, x.2)), ?_, rfl⟩
      constructor
      · have hlen : (l.map fun x => (radIndex x.1, x.2)).length = l.length := by
          simp only [List.length_map]
        exact hlen.le.trans hl
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have : y.2 < 2 * m := by
          by_contra hn
          exact hbad ⟨y, hy, by omega⟩
        omega
  haveI := FiniteDimensional.span_of_finite ℂ (hA.image fun l => wordOp R l w)
  exact Submodule.finiteDimensional_of_le hspan

theorem rav_finiteDimensional (m : ℕ) (hm : 1 ≤ m) :
    FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0)) := by
  let R := univRepG D4sector.f (ravFam D4sector m 0)
  let w := wUG D4sector.f (ravFam D4sector m 0)
  have h : Sat D4sector.f R w (ravFam D4sector m 0) :=
    univG_sat D4sector.f (ravFam D4sector m 0)
  have htop : (⊤ : Submodule ℂ (UModG D4sector.f (ravFam D4sector m 0))) ≤
      currentPiece R w (2 * m) := by
    rw [← D4FusionContact.Polynomial.universal_word_span D4sector.f
      (ravFam D4sector m 0), Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hc : wordOp R l w ∈ cycDeg R w
        (VOA.DeligneAudit.SectorGraded.wordDeg l) :=
      Submodule.subset_span ⟨l, rfl, rfl⟩
    exact rav_cycDeg_currentPiece h _ hc
  haveI := rav_currentPiece_finite hm h
  haveI : FiniteDimensional ℂ
      (⊤ : Submodule ℂ (UModG D4sector.f (ravFam D4sector m 0))) :=
    Submodule.finiteDimensional_of_le htop
  exact Module.Finite.equiv (Submodule.topEquiv)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.rav_high_kills_generator
#print axioms VOA.DeligneAudit.Toroidal.rav_currentPiece_finite
#print axioms VOA.DeligneAudit.Toroidal.rav_finiteDimensional
