import VOA.DeligneAudit.D4LeviKSFlagGradedProducts

/-! Three-block boxes span the homogeneous partial-flag quotient. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def ksFlagBoxSpan (m a b c d : ℕ) :
    Submodule ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  Submodule.span ℂ {T | ∃ dx dy dz : ℕ, dx + dy + dz = d ∧
    ∃ P ∈ ksBlockBoxPolys (m - c - b) a dx,
    ∃ Q ∈ ksBlockBoxPolys (m - c) b dy,
    ∃ R ∈ ksBlockBoxPolys m c dz,
      T = ksTargetXMap a b c P * ksTargetYMap a b c Q * ksTargetZMap a b c R}

theorem ksBlockBoxPolys_symmetric (q n d : ℕ) (hn : n ≤ q)
    (P : MvPolynomial (Fin n) ℂ) (hP : P ∈ ksBlockBoxPolys q n d) :
    P ∈ symmetricSubalgebra (Fin n) ℂ := by
  obtain ⟨v, _, _, rfl⟩ := ksBlockBoxPolys_spec q n d hn P hP
  exact rzOrbitSum_symmetric _ _

theorem ksFlag_boxXY_z_reduce (m a b c dx dy dz : ℕ) (hsize : a + b + c ≤ m)
    (P : MvPolynomial (Fin a) ℂ) (hP : P ∈ ksBlockBoxPolys (m - c - b) a dx)
    (Q : MvPolynomial (Fin b) ℂ) (hQ : Q ∈ ksBlockBoxPolys (m - c) b dy)
    (R : MvPolynomial (Fin c) ℂ)
    (hR : R ∈ symmetricSubalgebra (Fin c) ℂ) (hdR : R.IsHomogeneous dz) :
    ksTargetXMap a b c P * ksTargetYMap a b c Q * ksTargetZMap a b c R ∈
      ksFlagBoxSpan m a b c (dx + dy + dz) ⊔
        ksFlagRelationImage m a b c (dx + dy + dz) := by
  let U : pairTargetSymmetric a b c :=
    ⟨ksTargetXMap a b c P * ksTargetYMap a b c Q,
      (pairTargetSymmetric a b c).mul_mem
        (ksTargetXMap_symmetric a b c P
          (ksBlockBoxPolys_symmetric _ _ _ (by omega) P hP))
        (ksTargetYMap_symmetric a b c Q
          (ksBlockBoxPolys_symmetric _ _ _ (by omega) Q hQ))⟩
  have hh := ksFlag_z_box_step m a b c dz (dx + dy + dz)
    (by omega) (by omega) U R hR hdR
  have hle : Submodule.span ℂ
      (ksFlagZMultiplication a b c U '' (ksBlockBoxPolys m c dz : Set _)) ≤
        ksFlagBoxSpan m a b c (dx + dy + dz) := by
    apply Submodule.span_le.mpr
    rintro T ⟨B, hB, rfl⟩
    exact Submodule.subset_span ⟨dx, dy, dz, rfl, P, hP, Q, hQ, B, hB, rfl⟩
  exact (sup_le_sup_right hle _) hh

/-- A homogeneous YZ coefficient is reduced after fixing an X box polynomial. -/
theorem ksFlag_boxX_YZ_reduce (m a b c dx e : ℕ) (hsize : a + b + c ≤ m)
    (P : MvPolynomial (Fin a) ℂ) (hP : P ∈ ksBlockBoxPolys (m - c - b) a dx)
    (U : MvPolynomial (PairTarget a b c) ℂ) (hU : U ∈ ksFlagYZCoefficient a b c e) :
    ksTargetXMap a b c P * U ∈
      ksFlagBoxSpan m a b c (dx + e) ⊔ ksFlagRelationImage m a b c (dx + e) := by
  let S := ksFlagBoxSpan m a b c (dx + e) ⊔ ksFlagRelationImage m a b c (dx + e)
  have hPX := ksTargetXMap_symmetric a b c P
    (ksBlockBoxPolys_symmetric _ _ _ (by omega) P hP)
  induction hU using Submodule.span_induction with
  | mem U hU =>
      obtain ⟨dy, dz, hdeg, Y, hY, Z, hZ, rfl⟩ := hU
      obtain ⟨Q, ⟨hQ, hdQ⟩, rfl⟩ := hY
      have hstep := ksFlag_y_box_step m a b c dy dz (by omega) Z hZ Q hQ hdQ
      have hbox : ∀ T ∈ ksRelativeBoxSpan (m - c) b (dz + dy)
          (ksTargetYMap a b c) (ksFlagZCoefficient a b c),
          ksTargetXMap a b c P * T ∈ S := by
        intro T hT
        induction hT using Submodule.span_induction with
        | mem T hT =>
            obtain ⟨j, hj, B, hB, W, hW, rfl⟩ := hT
            obtain ⟨R, ⟨hR, hdR⟩, rfl⟩ := hW
            have hh := ksFlag_boxXY_z_reduce m a b c dx j (dz + dy - j)
              hsize P hP B hB R hR hdR
            have hd : dx + j + (dz + dy - j) = dx + e := by omega
            rw [hd] at hh
            simpa only [S, mul_assoc, mul_comm, mul_left_comm] using hh
        | zero => simp [S]
        | add T W hT hW ihT ihW =>
            simpa only [mul_add] using S.add_mem ihT ihW
        | smul t T hT ihT =>
            simpa only [mul_smul_comm] using S.smul_mem t ihT
      obtain ⟨B, hB, C, hC, heq⟩ := Submodule.mem_sup.mp hstep
      have hC' : ksTargetXMap a b c P * C ∈ S := by
        apply Submodule.mem_sup_right
        apply ksFlagRelationImage_mul m a b c (dx + e) _ _ hPX
        exact ksFlagRelationImage_mono m a b c (dz + dy) (dx + e) (by omega) hC
      have hh := S.add_mem (hbox B hB) hC'
      rw [← mul_add, heq] at hh
      simpa only [S, mul_comm, mul_left_comm, mul_assoc] using hh
  | zero => simp [S]
  | add T W hT hW ihT ihW =>
      simpa only [mul_add] using S.add_mem ihT ihW
  | smul t T hT ihT =>
      simpa only [mul_smul_comm] using S.smul_mem t ihT

/-- The complete graded partial-flag spanning inclusion. -/
theorem ksFlag_three_block_span (m a b c d : ℕ) (hsize : a + b + c ≤ m)
    (P : MvPolynomial (PairTarget a b c) ℂ)
    (hP : P ∈ pairTargetSymmetric a b c) (hd : P.IsHomogeneous d) :
    P ∈ ksFlagBoxSpan m a b c d ⊔ ksFlagRelationImage m a b c d := by
  let S := ksFlagBoxSpan m a b c d ⊔ ksFlagRelationImage m a b c d
  have hp := ksFlag_homogeneous_mem_products a b c d P hP hd
  clear hP hd
  induction hp using Submodule.span_induction with
  | mem T hT =>
      obtain ⟨dx, e, hdeg, Xp, hXp, U, hU, rfl⟩ := hT
      obtain ⟨Q, ⟨hQ, hdQ⟩, rfl⟩ := hXp
      have hstep := ksFlag_x_box_step m a b c dx e hsize U hU Q hQ hdQ
      have htotal : e + dx = d := by omega
      rw [htotal] at hstep
      have hle : ksRelativeBoxSpan (m - c - b) a d (ksTargetXMap a b c)
          (ksFlagYZCoefficient a b c) ≤ S := by
        apply Submodule.span_le.mpr
        rintro T ⟨j, hj, B, hB, W, hW, rfl⟩
        have hh := ksFlag_boxX_YZ_reduce m a b c j (d - j) hsize B hB W hW
        rw [Nat.add_sub_of_le hj] at hh
        simpa only [S, mul_comm] using hh
      have hh := (sup_le hle le_sup_right) hstep
      simpa only [S, mul_comm] using hh
  | zero => exact S.zero_mem
  | add P Q hP hQ ihP ihQ => exact S.add_mem ihP ihQ
  | smul t P hP ihP => exact S.smul_mem t ihP

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBlockBoxPolys_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_boxXY_z_reduce
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_boxX_YZ_reduce
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_three_block_span
