import VOA.DeligneAudit.D4FusionContactAllMNormalCore
import VOA.DeligneAudit.D4FusionContactAllMNormalTable
import VOA.DeligneAudit.D4FusionContactAllMCandidate

/-! The all-m word cutoff follows inside the actual differential ideal.
Thus the extra high-word summand in Model is redundant, with no count premise. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

abbrev Poly (m : ℕ) := MvPolynomial (Vars m) ℂ

def aVar (m : ℕ) (a : Fin 8 × ℕ) : Poly m := modeX m a.1.castSucc a.2
def cVar (m r : ℕ) : Poly m := modeX m 8 r

theorem cartan_modeX (m k r : ℕ) (i : Fin 9) :
    g0Deriv m 1 k (modeX m i r) = (cartanCoeff i : ℂ) • modeX m i (k + r) := by
  by_cases hr : r < m
  · rw [modeX, dif_pos hr]
    simp only [g0Deriv, MvPolynomial.mkDerivation_X, g0Image,
      show zeroIndex 1 = 1 by rfl, cartan_row, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hkr : ¬ k + r < m := by omega
    simp only [modeX, dif_neg hr, dif_neg hkr, map_zero, smul_zero]

theorem e_modeX (m k r : ℕ) (i : Fin 8) (j : Fin 9) :
    eDeriv m i k (modeX m j r) = if j = 8 then modeX m i.castSucc (k + r) else 0 := by
  by_cases hr : r < m
  · rw [modeX, dif_pos hr]
    simp only [eDeriv, MvPolynomial.mkDerivation_X, eImage]
  · have hkr : ¬ k + r < m := by omega
    simp only [modeX, dif_neg hr, dif_neg hkr, map_zero, ite_self]

theorem g0_closed (m k : ℕ) (g : Fin 10) {p : Poly m} (hp : p ∈ AllM.candidateIdeal m) :
    g0Deriv m g k p ∈ AllM.candidateIdeal m := by
  by_cases hk : k < m
  · exact AllM.candidateIdeal_deriv m (.inl (g, ⟨k, hk⟩)) hp
  · have he : g0Deriv m g k = 0 := by
      apply MvPolynomial.derivation_ext
      intro x
      have hhigh : ∀ j : Fin 9, modeX m j (k + x.2.val) = 0 := by
        intro j
        exact dif_neg (by omega)
      simp only [g0Deriv, MvPolynomial.mkDerivation_X, g0Image, hhigh,
        smul_zero, Finset.sum_const_zero, Derivation.zero_apply]
    rw [he]
    exact (AllM.candidateIdeal m).zero_mem

theorem e_closed (m k : ℕ) (i : Fin 8) {p : Poly m} (hp : p ∈ AllM.candidateIdeal m) :
    eDeriv m i k p ∈ AllM.candidateIdeal m := by
  by_cases hk : k < m
  · exact AllM.candidateIdeal_deriv m (.inr (i, ⟨k, hk⟩)) hp
  · have he : eDeriv m i k = 0 := by
      apply MvPolynomial.derivation_ext
      intro x
      have hhigh : modeX m i.castSucc (k + x.2.val) = 0 := dif_neg (by omega)
      simp only [eDeriv, MvPolynomial.mkDerivation_X, eImage, hhigh,
        ite_self, Derivation.zero_apply]
    rw [he]
    exact (AllM.candidateIdeal m).zero_mem

theorem center_power_mem (m : ℕ) : cVar m 0 ^ (2 * m + 1) ∈ AllM.candidateIdeal m := by
  let j : AllM.SeedIndex m := ⟨(true, 2 * m + 1, 0), by
    constructor
    · change 1 ≤ 2 * m + 1
      omega
    · change 2 * m < 2 * m + 1 + 0
      omega⟩
  have h := AllM.seed_mem_candidate m j
  change PowerSeries.coeff 0 (AllM.current m 8 ^ (2 * m + 1)) ∈ AllM.candidateIdeal m at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] at h
  simpa only [AllM.current, PowerSeries.constantCoeff_mk, cVar] using h

theorem a_center_word_mem (m : ℕ) (a : List (Fin 8 × ℕ)) (c : List ℕ) (n : ℕ)
    (hlen : a.length + c.length + n = 2 * m + 1) :
    word (aVar m) a * word (cVar m) c * cVar m 0 ^ n ∈ AllM.candidateIdeal m := by
  let E : (Fin 8 × ℕ) → Derivation ℂ (Poly m) (Poly m) := fun a => eDeriv m a.1 a.2
  let H : ℕ → Derivation ℂ (Poly m) (Poly m) := fun k => -g0Deriv m 1 k
  refine mixed_word_mem (AllM.candidateIdeal m) (aVar m) (cVar m) (cVar m 0) H
    ?_ ?_ ?_ ?_ (2 * m + 1) ?_ a c n hlen
  · intro b p hp
    exact (AllM.candidateIdeal m).neg_mem (g0_closed m b 1 hp)
  · intro b
    simp only [H, cVar, Derivation.neg_apply, cartan_modeX, cartanCoeff]
    simp
  · intro b d
    refine ⟨algebraMap ℂ (Poly m) (-(cartanCoeff d.1.castSucc : ℂ)), (d.1, b + d.2), ?_⟩
    simp only [H, aVar, Derivation.neg_apply, cartan_modeX,
      Algebra.smul_def, map_neg, neg_mul]
  · intro b d
    refine ⟨1, b + d, ?_⟩
    simp only [H, cVar, Derivation.neg_apply, cartan_modeX, cartanCoeff]
    simp
  · intro a' n' hn'
    refine a_word_center_pow_mem (AllM.candidateIdeal m) (aVar m) (cVar m 0) E
      ?_ ?_ ?_ (2 * m + 1) (center_power_mem m) a' n' hn'
    · intro d p hp
      exact e_closed m d.2 d.1 hp
    · intro d
      simp only [E, cVar, aVar, e_modeX, if_true, Nat.add_zero]
    · intro d b
      have hb : b.1.castSucc ≠ (8 : Fin 9) := Fin.castSucc_ne_last b.1
      simp only [E, aVar, e_modeX, if_neg hb]

theorem split_polyWord (m : ℕ) (l : List (Vars m)) :
    ∃ a : List (Fin 8 × ℕ), ∃ c : List ℕ,
      a.length + c.length = l.length ∧ polyWord l = word (aVar m) a * word (cVar m) c := by
  induction l with
  | nil =>
      exact ⟨[], [], rfl, by
        simp only [polyWord, word_nil, List.map_nil, List.prod_nil, mul_one]⟩
  | cons x l ih =>
      obtain ⟨a, c, hlen, hp⟩ := ih
      obtain ⟨i, r⟩ := x
      refine Fin.lastCases ?_ (fun j => ?_) i
      · refine ⟨a, r.val :: c, by simp only [List.length_cons]; omega, ?_⟩
        change MvPolynomial.X ((8, r) : Vars m) * polyWord l = _
        have hx : cVar m r.val = MvPolynomial.X ((8, r) : Vars m) := by
          simp only [cVar, modeX, dif_pos r.isLt]
        rw [← hx, hp, word_cons]
        ring
      · refine ⟨(j, r.val) :: a, c, by simp only [List.length_cons]; omega, ?_⟩
        change MvPolynomial.X ((j.castSucc, r) : Vars m) * polyWord l = _
        have hx : aVar m (j, r.val) = MvPolynomial.X ((j.castSucc, r) : Vars m) := by
          simp only [aVar, modeX, dif_pos r.isLt]
        rw [← hx, hp, word_cons]
        ring

theorem polyWord_exact_mem (m : ℕ) (l : List (Vars m)) (hl : l.length = 2 * m + 1) :
    polyWord l ∈ AllM.candidateIdeal m := by
  obtain ⟨a, c, hlen, hp⟩ := split_polyWord m l
  rw [hp]
  simpa only [pow_zero, mul_one] using a_center_word_mem m a c 0 (by omega)

theorem polyWord_high_mem (m : ℕ) (l : List (Vars m)) (hl : 2 * m + 1 ≤ l.length) :
    polyWord l ∈ AllM.candidateIdeal m := by
  have ht : (l.take (2 * m + 1)).length = 2 * m + 1 := by
    rw [List.length_take, min_eq_left hl]
  have hh := polyWord_exact_mem m (l.take (2 * m + 1)) ht
  have he : polyWord l = polyWord (l.take (2 * m + 1)) * polyWord (l.drop (2 * m + 1)) := by
    simp only [polyWord, ← List.prod_append, ← List.map_append, List.take_append_drop]
  rw [he]
  exact (AllM.candidateIdeal m).mul_mem_right _ hh

/-- The independent source cutoff is already a relation of the fixed
coefficient/derivation ideal, including the empty-variable m=0 boundary. -/
theorem highWordIdeal_le_candidate (m : ℕ) : highWordIdeal m ≤ AllM.candidateIdeal m := by
  apply Ideal.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  exact polyWord_high_mem m l hl

theorem modelIdeal_eq_candidate (m : ℕ) : AllM.modelIdeal m = AllM.candidateIdeal m :=
  sup_eq_left.mpr (highWordIdeal_le_candidate m)

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.a_center_word_mem
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.highWordIdeal_le_candidate
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.modelIdeal_eq_candidate
