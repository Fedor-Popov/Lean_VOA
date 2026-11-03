import VOA.DeligneAudit.D4LeviKSBlockGradedMaximal

/-! Relative one-alphabet box reduction, preserving total degree. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Box polynomials with outer coefficients of the complementary degree. -/
noncomputable def ksRelativeBoxSpan (q n D : ℕ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (O : ℕ → Submodule ℂ A) :
    Submodule ℂ A :=
  Submodule.span ℂ {T | ∃ j : ℕ, j ≤ D ∧
    ∃ B ∈ ksBlockBoxPolys q n j, ∃ U ∈ O (D - j), T = U * φ B}

/-- A relative box theorem for complete-homogeneous relations whose lower
    terms move positive degree from the new alphabet to the outer alphabet. -/
theorem ksRelative_box_span (q n D : ℕ) (hn : n ≤ q)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (O : ℕ → Submodule ℂ A)
    (H M : ℕ → A) (K : Submodule ℂ A)
    (hmul : ∀ e f U W, U ∈ O e → W ∈ O f → U * W ∈ O (e + f))
    (hH : ∀ r, H r ∈ O r)
    (hconv : ∀ s, M s = φ (hsymm (Fin n) ℂ s) +
      ∑ t ∈ Finset.range s, H (s - t) * φ (hsymm (Fin n) ℂ t))
    (hrel : ∀ s e v, q + 1 ≤ n + s → e + v + s = D →
      ∀ U ∈ O e, ∀ W : MvPolynomial (Fin n) ℂ,
        W ∈ symmetricSubalgebra (Fin n) ℂ → W.IsHomogeneous v →
          U * φ W * M s ∈ K)
    (d e : ℕ) (hde : e + d = D) (U : A) (hU : U ∈ O e)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) (hd : P.IsHomogeneous d) :
    U * φ P ∈ ksRelativeBoxSpan q n D φ O ⊔ K := by
  classical
  induction d using Nat.strong_induction_on generalizing e U P with
  | h d ih =>
      let S := ksRelativeBoxSpan q n D φ O ⊔ K
      let L : MvPolynomial (Fin n) ℂ →ₗ[ℂ] A :=
        (LinearMap.mulLeft ℂ U).comp φ.toLinearMap
      have hbox : ∀ B ∈ Submodule.span ℂ (ksBlockBoxPolys q n d : Set _), L B ∈ S := by
        intro B hB
        induction hB using Submodule.span_induction with
        | mem B hB =>
            apply Submodule.mem_sup_left
            apply Submodule.subset_span
            exact ⟨d, by omega, B, hB, U, by simpa [show D - d = e by omega] using hU,
              rfl⟩
        | zero => simp [L, S]
        | add B C hB hC ihB ihC =>
            simpa only [map_add] using S.add_mem ihB ihC
        | smul t B hB ihB =>
            simpa only [map_smul] using S.smul_mem t ihB
      have hmax : ∀ G ∈ ksBlockGradedMaximalSpan q n d, L G ∈ S := by
        intro G hG
        induction hG using Submodule.span_induction with
        | mem G hG =>
            obtain ⟨s, hs, hsd, W, hW, hdW, rfl⟩ := hG
            have hmain : U * φ W * M s ∈ S :=
              Submodule.mem_sup_right (hrel s e (d - s) hs (by omega) U hU W hW hdW)
            have hlower :
                (∑ t ∈ Finset.range s, U * H (s - t) *
                  φ (W * hsymm (Fin n) ℂ t)) ∈ S := by
              apply S.sum_mem
              intro t ht
              have ht' : t < s := Finset.mem_range.mp ht
              exact ih (d - s + t) (by omega) (e + (s - t)) (by omega)
                (U * H (s - t)) (hmul _ _ _ _ hU (hH _))
                (W * hsymm (Fin n) ℂ t)
                ((symmetricSubalgebra (Fin n) ℂ).mul_mem hW (hsymm_isSymmetric _ _ _))
                (hdW.mul (ksHsymm_homogeneous n t))
            have heq : L (W * hsymm (Fin n) ℂ s) =
                U * φ W * M s -
                  ∑ t ∈ Finset.range s, U * H (s - t) *
                    φ (W * hsymm (Fin n) ℂ t) := by
              change U * φ (W * hsymm (Fin n) ℂ s) = _
              rw [hconv, mul_add, Finset.mul_sum]
              simp only [map_mul]
              have he : (∑ t ∈ Finset.range s,
                  U * φ W * (H (s - t) * φ (hsymm (Fin n) ℂ t))) =
                  ∑ t ∈ Finset.range s,
                    U * H (s - t) * (φ W * φ (hsymm (Fin n) ℂ t)) := by
                apply Finset.sum_congr rfl
                intro t ht
                ring
              rw [he, add_sub_cancel_right, mul_assoc]
            rw [heq]
            exact S.sub_mem hmain hlower
        | zero => simp [L, S]
        | add B C hB hC ihB ihC =>
            simpa only [map_add] using S.add_mem ihB ihC
        | smul t B hB ihB =>
            simpa only [map_smul] using S.smul_mem t ihB
      obtain ⟨B, hB, C, hC, heq⟩ := Submodule.mem_sup.mp
        (ksBlockSymmetric_span_graded_maximal q n d hn P hP hd)
      change L P ∈ S
      rw [← heq, map_add]
      exact S.add_mem (hbox B hB) (hmax C hC)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksRelative_box_span
