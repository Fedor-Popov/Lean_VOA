import VOA.DeligneAudit.D4FusionToroidalPresentedTwoCurrent
import VOA.DeligneAudit.D4FusionTruncatedWeyl

/-! Ravinder relations on the zero-u-degree quotient. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector

noncomputable section

theorem two_syntax_tail (t : List (Ltr 28))
    (ht : t ∈ (ravFam D4sector 2 0).tails) :
    wordOpT (ρPTE 2) (symbolLetters 2 t) (pTE 2) = 0 := by
  change wordOpT (rhoPT D4sector.f 2 (JprimeSyntaxE 2))
    (symbolLetters 2 t) (pPT D4sector.f 2 (JprimeSyntaxE 2)) = 0
  rw [wordOpT_rhoPT]
  exact mk_syntax D4sector.f 2 (JprimeSyntaxE 2)
    (swT (symbolLetters 2 t)) (Or.inl (Or.inl ⟨t, ht, rfl⟩))

theorem two_current_word_small (t : List (Ltr 28))
    (ht : ∀ x ∈ t, x.2 < 2) :
    wordOp twoCurrent t (pTE 2) =
      wordOpT (ρPTE 2) (symbolLetters 2 t) (pTE 2) := by
  induction t with
  | nil => rfl
  | cons x t ih =>
      have hx : x.2 < 2 := ht x (by simp)
      have hrest : ∀ y ∈ t, y.2 < 2 := by
        intro y hy
        exact ht y (by simp [hy])
      change twoCurrent.op x.1 x.2 (wordOp twoCurrent t (pTE 2)) = _
      rw [ih hrest]
      have hx' : x.2 ≤ 1 := by omega
      simp [twoCurrent, symbolLetters, hx', wordOpT,
        Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hx]

theorem two_zero_tail_small (t : List (Ltr 28))
    (ht : t ∈ (ravFam D4sector 2 0).tails)
    (hsmall : ∀ x ∈ t, x.2 < 2) :
    wordOp twoZeroCurrent t twoZeroGen = 0 := by
  change wordOp (quotRepG twoCurrent (twoN 1) twoCurrent_inv) t
    ((twoN 1).mkQ (pTE 2)) = 0
  rw [quot_wordOpG twoCurrent (twoN 1) twoCurrent_inv (pTE 2) t]
  rw [two_current_word_small t hsmall, two_syntax_tail t ht]
  exact map_zero _

theorem two_zero_eig (q : Fin D4sector.n × ℂ)
    (hq : q ∈ (ravFam D4sector 2 0).eig) :
    twoZeroCurrent.op q.1 0 twoZeroGen = q.2 • twoZeroGen := by
  have h := mk_syntax D4sector.f 2 (JprimeSyntaxE 2)
    (swT [(q.1, 0, 0)] - q.2 • swT [])
    (Or.inr ⟨q, hq, rfl⟩)
  rw [← Submodule.mkQ_apply, map_sub, map_smul] at h
  have h1 := wordOpT_rhoPT D4sector.f 2 (JprimeSyntaxE 2) [(q.1, 0, 0)]
  have h0 := wordOpT_rhoPT D4sector.f 2 (JprimeSyntaxE 2) []
  change (ρPTE 2).op q.1 0 0 (pTE 2) =
    (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ (swT [(q.1, 0, 0)]) at h1
  change pTE 2 = (JT D4sector.f 2 (JprimeSyntaxE 2)).mkQ (swT []) at h0
  rw [← h1, ← h0] at h
  have he : (ρPTE 2).op q.1 0 0 (pTE 2) = q.2 • pTE 2 :=
    sub_eq_zero.mp h
  change (twoN 1).mkQ (twoCurrent.op q.1 0 (pTE 2)) = _
  simpa [twoCurrent, twoZeroGen] using congrArg (twoN 1).mkQ he

theorem two_zero_single_high (c : Fin 28) (r : ℕ) (hr : 2 ≤ r) :
    twoZeroCurrent.op c r twoZeroGen = 0 := by
  change (twoN 1).mkQ (twoCurrent.op c r (pTE 2)) = 0
  have h : ¬ r ≤ 1 := by omega
  simp [twoCurrent, h]

theorem two_zero_sat :
    Sat D4sector.f twoZeroCurrent twoZeroGen (ravFam D4sector 2 0) where
  tail t ht := by
    have ht' := ht
    change t ∈ (ravSpec D4sector 2 4).tails at ht'
    rcases ht' with ⟨e, r, he, rfl⟩ | ⟨h, r, hh, hr, rfl⟩ |
      ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨h, r, hh, hr, rfl⟩
    · by_cases hr : r < 2
      · apply two_zero_tail_small _ ht
        intro y hy
        have hy' : y = (e, r) := List.eq_of_mem_singleton hy
        simpa [hy'] using hr
      · exact two_zero_single_high e r (by omega)
    · by_cases hs : r < 2
      · apply two_zero_tail_small _ ht
        intro y hy
        have hy' : y = (h, r) := List.eq_of_mem_singleton hy
        simpa [hy'] using hs
      · exact two_zero_single_high h r (by omega)
    · apply two_zero_tail_small _ ht
      intro y hy
      have hy' : y = (i, 0) := List.eq_of_mem_replicate hy
      simp [hy']
    · apply two_zero_single_high
      split_ifs <;> omega
    · by_cases hs : r < 2
      · apply two_zero_tail_small _ ht
        intro y hy
        have hy' : y = (h, r) := List.eq_of_mem_singleton hy
        simpa [hy'] using hs
      · exact two_zero_single_high h r (by omega)
  eig q hq := two_zero_eig q hq

theorem two_zero_localWeyl :
    LocalWeylRelG D4sector twoZeroCurrent twoZeroGen 2 := by
  apply (localWeylRelG_iff_demazure_trunc (by omega)).mpr
  exact ⟨two_zero_sat, two_zero_single_high D4sector.c₀ 2 le_rfl⟩

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_syntax_tail
#print axioms VOA.DeligneAudit.Toroidal.two_current_word_small
#print axioms VOA.DeligneAudit.Toroidal.two_zero_tail_small
#print axioms VOA.DeligneAudit.Toroidal.two_zero_eig
#print axioms VOA.DeligneAudit.Toroidal.two_zero_single_high
#print axioms VOA.DeligneAudit.Toroidal.two_zero_sat
#print axioms VOA.DeligneAudit.Toroidal.two_zero_localWeyl
