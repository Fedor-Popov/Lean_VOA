import VOA.DeligneAudit.D4LeviKSFlagYStep

/-! Two-block homogeneous coefficients for the X-over-YZ reduction. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

variable {A : Type*} [CommRing A] [Algebra ℂ A]

noncomputable def ksProductCoefficient (O P : ℕ → Submodule ℂ A) (d : ℕ) :
    Submodule ℂ A :=
  Submodule.span ℂ {T | ∃ e f : ℕ, e + f = d ∧
    ∃ U ∈ O e, ∃ W ∈ P f, T = U * W}

theorem ksProductCoefficient_mul (O P : ℕ → Submodule ℂ A)
    (hO : ∀ e f U W, U ∈ O e → W ∈ O f → U * W ∈ O (e + f))
    (hP : ∀ e f U W, U ∈ P e → W ∈ P f → U * W ∈ P (e + f))
    (e f : ℕ) (U W : A)
    (hU : U ∈ ksProductCoefficient O P e) (hW : W ∈ ksProductCoefficient O P f) :
    U * W ∈ ksProductCoefficient O P (e + f) := by
  induction hU using Submodule.span_induction with
  | mem U hU =>
      obtain ⟨i, j, hij, B, hB, C, hC, rfl⟩ := hU
      induction hW using Submodule.span_induction with
      | mem W hW =>
          obtain ⟨k, l, hkl, E, hE, F, hF, rfl⟩ := hW
          exact Submodule.subset_span
            ⟨i + k, j + l, by omega, B * E, hO _ _ _ _ hB hE,
              C * F, hP _ _ _ _ hC hF, by ring⟩
      | zero => simp
      | add V W hV hW ihV ihW =>
          simpa only [mul_add] using Submodule.add_mem _ ihV ihW
      | smul t W hW ihW =>
          simpa only [mul_smul_comm] using Submodule.smul_mem _ t ihW
  | zero => simp
  | add U V hU hV ihU ihV =>
      simpa only [add_mul] using Submodule.add_mem _ ihU ihV
  | smul t U hU ihU =>
      simpa only [smul_mul_assoc] using Submodule.smul_mem _ t ihU

noncomputable def ksFlagYZCoefficient (a b c d : ℕ) :
    Submodule ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  ksProductCoefficient
    (fun e => ksBlockCoefficient b e (ksTargetYMap a b c))
    (ksFlagZCoefficient a b c) d

theorem ksFlagYZCoefficient_mul (a b c e f : ℕ)
    (U W : MvPolynomial (PairTarget a b c) ℂ)
    (hU : U ∈ ksFlagYZCoefficient a b c e) (hW : W ∈ ksFlagYZCoefficient a b c f) :
    U * W ∈ ksFlagYZCoefficient a b c (e + f) :=
  ksProductCoefficient_mul _ _ (fun e f => ksBlockCoefficient_mul b e f _)
    (fun e f => ksBlockCoefficient_mul c e f _) e f U W hU hW

theorem ksFlagYZCoefficient_symmetric (a b c d : ℕ)
    (P : MvPolynomial (PairTarget a b c) ℂ) (hP : P ∈ ksFlagYZCoefficient a b c d) :
    P ∈ pairTargetSymmetric a b c := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨e, f, _, U, hU, W, hW, rfl⟩ := hP
      obtain ⟨Q, ⟨hQ, _⟩, rfl⟩ := hU
      exact (pairTargetSymmetric a b c).mul_mem
        (ksTargetYMap_symmetric a b c Q hQ) (ksFlagZCoefficient_symmetric a b c f W hW)
  | zero => exact (pairTargetSymmetric a b c).zero_mem
  | add P Q hP hQ ihP ihQ => exact (pairTargetSymmetric a b c).add_mem ihP ihQ
  | smul t P hP ihP => exact (pairTargetSymmetric a b c).toSubmodule.smul_mem t ihP

theorem ksFlagYZCoefficient_hsymm (a b c d : ℕ) :
    (ryMixedTarget a b c d : MvPolynomial (PairTarget a b c) ℂ) ∈
      ksFlagYZCoefficient a b c d := by
  classical
  rw [← ksTargetYZAlphabet_coeff, ksHSeries_append, PowerSeries.coeff_mul]
  apply Submodule.sum_mem
  intro p hp
  rw [ksTargetYAlphabet_coeff, ksTargetZAlphabet_coeff]
  exact Submodule.subset_span
    ⟨p.1, p.2, Finset.mem_antidiagonal.mp hp, _, ksBlockCoefficient_hsymm b p.1 _,
      _, ksBlockCoefficient_hsymm c p.2 _, rfl⟩

theorem ksFlagYZCoefficient_one (a b c : ℕ) :
    (1 : MvPolynomial (PairTarget a b c) ℂ) ∈ ksFlagYZCoefficient a b c 0 := by
  simpa only [ryMixedTarget_zero, Subalgebra.coe_one] using
    ksFlagYZCoefficient_hsymm a b c 0

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksProductCoefficient_mul
#print axioms VOA.DeligneAudit.D4Levi.ksFlagYZCoefficient_mul
#print axioms VOA.DeligneAudit.D4Levi.ksFlagYZCoefficient_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksFlagYZCoefficient_hsymm
#print axioms VOA.DeligneAudit.D4Levi.ksFlagYZCoefficient_one
