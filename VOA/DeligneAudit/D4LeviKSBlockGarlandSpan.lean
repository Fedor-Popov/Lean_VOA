import VOA.DeligneAudit.D4LeviKSBlockThetaGarland

/-! The graded image of the occupation Garland ideal is a subset-sum relation span. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.CLAssembly

/-- Full symmetrization of the active complete homogeneous factor and its spectators. -/
noncomputable def ksBlockGarlandSeed (k l s : ℕ) (β : Fin l → ℕ) :
    MvPolynomial (Fin (k + l)) ℂ :=
  rzOrbitSum (Fin (k + l))
    (rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) *
      ∏ j : Fin l, X (Fin.natAdd k j) ^ β j)

/-- All subset Garland relations of a fixed block size and mode degree. -/
noncomputable def ksBlockGarlandSpan (q n d : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ) :=
  Submodule.span ℂ {T | ∃ k l s : ℕ, ∃ h : k + l = n, ∃ β : Fin l → ℕ,
    1 ≤ k ∧ q + 1 ≤ k + s ∧ s + ∑ j, β j = d ∧
      T = rename (finCongr h) (ksBlockGarlandSeed k l s β)}

theorem ksBlockTheta_monomial_xx_mem (q n d k s : ℕ)
    (hk : 1 ≤ k) (hks : q + 1 ≤ k + s)
    (f : ℕ →₀ ℕ) (t : ℂ)
    (hweight : Finsupp.weight om f + (k, s) = (n, d)) :
    ksBlockTheta n (monomial f t * xx k s) ∈ ksBlockGarlandSpan q n d := by
  classical
  have ht : (monomial f t : R) = t • mono (lst f) := by
    rw [← monomial_eq_mono]
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [ht, smul_mul_assoc, map_smul]
  apply Submodule.smul_mem
  generalize hl : lst f = ls
  induction ls using List.ofFnRec with
  | _ l β =>
      have hlen : (Finsupp.weight om f).1 = l := by
        rw [← VOA.DeligneAudit.A3Sector.a2_lst_length, hl, List.length_ofFn]
      have hsum : (Finsupp.weight om f).2 = ∑ j, β j := by
        rw [← VOA.DeligneAudit.A3Sector.a2_lst_sum, hl, rz_sum_ofFn]
      have hn : n = k + l := by
        have hh := congrArg Prod.fst hweight
        simp only [Prod.fst_add, hlen] at hh
        omega
      have hd : s + ∑ j, β j = d := by
        have hh := congrArg Prod.snd hweight
        simpa only [Prod.snd_add, hsum, Nat.add_comm] using hh
      subst n
      rw [mul_comm, ksBlockTheta_xx_mul_mono]
      apply Submodule.subset_span
      refine ⟨k, l, s, rfl, β, hk, hks, hd, ?_⟩
      simp [ksBlockGarlandSeed]

/-- Taking the prescribed bidegree of any ideal element yields an explicit
    linear combination of subset Garland relations. -/
theorem ksBlockTheta_component_J_mem (q n d : ℕ) (P : R) (hP : P ∈ J q) :
    ksBlockTheta n (weightedHomogeneousComponent om (n, d) P) ∈
      ksBlockGarlandSpan q n d := by
  have hmain : ∀ P ∈ J q, ∀ A : R,
      ksBlockTheta n (weightedHomogeneousComponent om (n, d) (A * P)) ∈
        ksBlockGarlandSpan q n d := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem G hG =>
        obtain ⟨k, s, hk, hks, rfl⟩ := hG
        intro A
        induction A using MvPolynomial.induction_on' with
        | monomial f t =>
            have hh := (isWeightedHomogeneous_monomial om f t rfl).mul (xx_hom k s)
            by_cases hw : (n, d) = Finsupp.weight om f + (k, s)
            · rw [hw, hh.weightedHomogeneousComponent_same]
              exact ksBlockTheta_monomial_xx_mem q n d k s hk hks f t hw.symm
            · rw [hh.weightedHomogeneousComponent_ne (n, d) hw, map_zero]
              exact Submodule.zero_mem _
        | add A B hA hB =>
            rw [add_mul, map_add, map_add]
            exact Submodule.add_mem _ hA hB
    | zero => intro A; simp
    | add P Q hP hQ ihP ihQ =>
        intro A
        rw [mul_add, map_add, map_add]
        exact Submodule.add_mem _ (ihP A) (ihQ A)
    | smul A P hP ih =>
        intro B
        rw [smul_eq_mul, ← mul_assoc]
        exact ih (B * A)
  simpa only [one_mul] using hmain P hP 1

theorem ksBlockTheta_J_mem (q n d : ℕ) (P : R)
    (hP : P ∈ J q) (hd : IsWeightedHomogeneous om P (n, d)) :
    ksBlockTheta n P ∈ ksBlockGarlandSpan q n d := by
  simpa only [hd.weightedHomogeneousComponent_same] using
    ksBlockTheta_component_J_mem q n d P hP

theorem ksBlockGarlandSpan_le_image (q n d : ℕ) :
    ksBlockGarlandSpan q n d ≤
      ((J q).restrictScalars ℂ ⊓ weightedHomogeneousSubmodule ℂ om (n, d)).map
        (ksBlockTheta n) := by
  apply Submodule.span_le.mpr
  rintro T ⟨k, l, s, hn, β, hk, hks, hd, rfl⟩
  subst n
  simp only [finCongr_refl, Equiv.coe_refl, rename_id]
  refine ⟨xx k s * mono (List.ofFn β), ⟨?_, ?_⟩, ?_⟩
  · exact Ideal.mul_mem_right _ _ (xx_mem_J hk hks)
  · have hb : IsWeightedHomogeneous om (mono (List.ofFn β)) (l, ∑ j, β j) := by
      rw [mono_eq]
      exact isWeightedHomogeneous_monomial om _ 1 (ksModeOccupation_weight l β)
    have hh := (xx_hom k s).mul hb
    simpa only [Prod.mk_add_mk, hd] using hh
  · exact ksBlockTheta_xx_mul_mono k l s β

/-- Exact identification, degree by degree, of the occupation ideal with the
    symmetrized complete-homogeneous subset relations. -/
theorem ksBlockGarlandSpan_eq_image (q n d : ℕ) :
    ksBlockGarlandSpan q n d =
      ((J q).restrictScalars ℂ ⊓ weightedHomogeneousSubmodule ℂ om (n, d)).map
        (ksBlockTheta n) := by
  apply le_antisymm (ksBlockGarlandSpan_le_image q n d)
  rintro T ⟨P, ⟨hP, hd⟩, rfl⟩
  exact ksBlockTheta_J_mem q n d P hP hd

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_monomial_xx_mem
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_component_J_mem
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_J_mem
#print axioms VOA.DeligneAudit.D4Levi.ksBlockGarlandSpan_le_image
#print axioms VOA.DeligneAudit.D4Levi.ksBlockGarlandSpan_eq_image
