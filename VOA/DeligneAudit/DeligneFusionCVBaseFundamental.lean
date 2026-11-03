import VOA.DeligneAudit.DeligneFusionCVQuotient
import VOA.DeligneAudit.DeligneFusionCVKernelFundamental
import VOA.DeligneAudit.DeligneFusionCVUnivDimension

/-!
# The fundamental one-adjoint base quotient

For the presentation with epsilon `ω₁` and `j=1`, killing the first
kernel generator merges the two final parts one of the first-root
partition. The result has epsilon `ω₂`, one extra first-root part two,
and `j=0`. The other two root partitions and the highest weight agree.
The equivalence below is an equality of actual defining relations and
has no dimension or fusion-product premise.
-/

namespace VOA.DeligneAudit.A2.CVBaseFundamental

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVFamily

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight}

/-- Killing the first kernel generator at `j=1` gives the complete
fundamental base quotient presentation. -/
theorem quotient_rel (h : CV3Rel R w (1, 0) ν ϱ 1)
    (htop : R.op 3 (ν.1 + ϱ.1 + 1) w = 0) :
    CV3Rel R w (0, 1) (ν + (1, 0)) ϱ 0 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 w = ((0 + 2 * (ν.1 + 1) + 3 * ϱ.1 + 0 : ℕ) : ℂ) • w
    rw [show 0 + 2 * (ν.1 + 1) + 3 * ϱ.1 + 0 =
      1 + 2 * ν.1 + 3 * ϱ.1 + 1 by omega]
    exact h.cartan_first
  · change R.op 7 0 w = ((1 + 2 * (ν.2 + 0) + 3 * ϱ.2 + 0 : ℕ) : ℂ) • w
    rw [show 1 + 2 * (ν.2 + 0) + 3 * ϱ.2 + 0 =
      0 + 2 * ν.2 + 3 * ϱ.2 + 1 by omega]
    exact h.cartan_second
  · change (R.op 3 0)^[0 + 2 * (ν.1 + 1) + 3 * ϱ.1 + 0 + 1] w = 0
    rw [show 0 + 2 * (ν.1 + 1) + 3 * ϱ.1 + 0 + 1 =
      1 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1 by omega]
    exact h.lowering_first
  · change (R.op 4 0)^[1 + 2 * (ν.2 + 0) + 3 * ϱ.2 + 0 + 1] w = 0
    rw [show 1 + 2 * (ν.2 + 0) + 3 * ϱ.2 + 0 + 1 =
      0 + 2 * ν.2 + 3 * ϱ.2 + 1 + 1 by omega]
    exact h.lowering_second
  · change CVRel (R.op 3) (parts ϱ.1 (ν.1 + 1) 0) w
    apply cvrel_merge_last_two_ones ϱ.1 ν.1 0 (CVRoots.sl2_first R)
      (fun s => h.raising 0 (by decide) s)
      (fun p hp => h.cartan_pos 6 (by decide) p hp)
    · simpa only [Nat.zero_add] using h.first
    · simpa only [Nat.add_zero, Nat.add_comm ϱ.1 ν.1] using htop
  · simpa only [Nat.add_zero, Nat.zero_add] using h.second
  · change CVRel (R.op 5)
      (parts (ϱ.1 + ϱ.2) ((ν.1 + 1) + (ν.2 + 0) + 0) (0 + 1)) w
    rw [show (ν.1 + 1) + (ν.2 + 0) + 0 = ν.1 + ν.2 + 1 by omega]
    exact h.highest

/-- The fundamental base quotient has exactly the original relations
together with its first kernel generator relation. -/
theorem quotient_rel_iff :
    CV3Rel R w (0, 1) (ν + (1, 0)) ϱ 0 ↔
      CV3Rel R w (1, 0) ν ϱ 1 ∧ R.op 3 (ν.1 + ϱ.1 + 1) w = 0 := by
  constructor
  · intro h
    have h1 := cvrel_split_last_two_ones ϱ.1 ν.1 0 (CVRoots.sl2_first R)
      (fun s => h.raising 0 (by decide) s)
      (fun p hp => h.cartan_pos 6 (by decide) p hp) h.first
    have htop : R.op 3 (ν.1 + ϱ.1 + 1) w = 0 := by
      simpa only [Nat.add_zero, Nat.add_comm ϱ.1 ν.1] using h1.2
    refine ⟨⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, htop⟩
    · change R.op 6 0 w = ((1 + 2 * ν.1 + 3 * ϱ.1 + 1 : ℕ) : ℂ) • w
      rw [show 1 + 2 * ν.1 + 3 * ϱ.1 + 1 =
        0 + 2 * (ν.1 + 1) + 3 * ϱ.1 + 0 by omega]
      exact h.cartan_first
    · change R.op 7 0 w = ((0 + 2 * ν.2 + 3 * ϱ.2 + 1 : ℕ) : ℂ) • w
      rw [show 0 + 2 * ν.2 + 3 * ϱ.2 + 1 =
        1 + 2 * (ν.2 + 0) + 3 * ϱ.2 + 0 by omega]
      exact h.cartan_second
    · change (R.op 3 0)^[1 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1] w = 0
      rw [show 1 + 2 * ν.1 + 3 * ϱ.1 + 1 + 1 =
        0 + 2 * (ν.1 + 1) + 3 * ϱ.1 + 0 + 1 by omega]
      exact h.lowering_first
    · change (R.op 4 0)^[0 + 2 * ν.2 + 3 * ϱ.2 + 1 + 1] w = 0
      rw [show 0 + 2 * ν.2 + 3 * ϱ.2 + 1 + 1 =
        1 + 2 * (ν.2 + 0) + 3 * ϱ.2 + 0 + 1 by omega]
      exact h.lowering_second
    · simpa only [Nat.zero_add] using h1.1
    · simpa only [Nat.add_zero, Nat.zero_add] using h.second
    · change CVRel (R.op 5) (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + 1) (1 + 0)) w
      rw [show ν.1 + ν.2 + 1 = (ν.1 + 1) + (ν.2 + 0) + 0 by omega]
      exact h.highest
  · rintro ⟨h, htop⟩
    exact quotient_rel h htop

/-- The first kernel at `j=1` has its genuine zero-adjoint base
presentation, also without a dimension assumption. -/
theorem kernel_rel (h : CV3Rel R w (1, 0) ν ϱ 1) :
    CV3Rel R (R.op 3 (ν.1 + ϱ.1 + 1) w) (0, 0) (ν + (0, 1)) ϱ 0 := by
  simpa only [Nat.sub_self] using
    CVKernelFundamental.first_kernel_rel_fundamental h (by decide)

open VOA.DeligneAudit.A2.CVUniv

noncomputable section

/-- The actual universal map to the fundamental base quotient. -/
def quotientMap (ν ϱ : Weight) :
    CVMod (1, 0) ν ϱ 1 →ₗ[ℂ] CVMod (0, 1) (ν + (1, 0)) ϱ 0 :=
  cvMap (quotient_rel_iff.mp (cvUniv_rel (0, 1) (ν + (1, 0)) ϱ 0)).1

theorem quotientMap_wordOp (ν ϱ : Weight) (l : List (UnivG.Ltr 8)) :
    quotientMap ν ϱ (wordOp (cvUnivRep (1, 0) ν ϱ 1) l (cv_wU (1, 0) ν ϱ 1)) =
      wordOp (cvUnivRep (0, 1) (ν + (1, 0)) ϱ 0) l
        (cv_wU (0, 1) (ν + (1, 0)) ϱ 0) :=
  cvMap_wordOp _ l

/-- Every exact current-degree piece maps onto its counterpart. -/
theorem quotientMap_cycDeg (ν ϱ : Weight) (d : ℕ) :
    (cycDeg (cvUnivRep (1, 0) ν ϱ 1) (cv_wU (1, 0) ν ϱ 1) d).map (quotientMap ν ϱ) =
      cycDeg (cvUnivRep (0, 1) (ν + (1, 0)) ϱ 0)
        (cv_wU (0, 1) (ν + (1, 0)) ϱ 0) d :=
  map_cycDeg (quotient_rel_iff.mp (cvUniv_rel (0, 1) (ν + (1, 0)) ϱ 0)).1 d

/-- The actual base quotient map is surjective, by universal word spanning. -/
theorem quotientMap_surjective (ν ϱ : Weight) : Function.Surjective (quotientMap ν ϱ) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← cv_span_top (0, 1) (ν + (1, 0)) ϱ 0]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact ⟨wordOp (cvUnivRep (1, 0) ν ϱ 1) l (cv_wU (1, 0) ν ϱ 1),
    quotientMap_wordOp ν ϱ l⟩

/-- The one first-root kernel generator in the actual universal source. -/
def kernelGenerator (ν ϱ : Weight) : CVMod (1, 0) ν ϱ 1 :=
  (cvUnivRep (1, 0) ν ϱ 1).op 3 (ν.1 + ϱ.1 + 1) (cv_wU (1, 0) ν ϱ 1)

/-- The explicit kernel candidate is its actual cyclic submodule. -/
def kernelSpan (ν ϱ : Weight) : Submodule ℂ (CVMod (1, 0) ν ϱ 1) :=
  cycSub (cvUnivRep (1, 0) ν ϱ 1) (kernelGenerator ν ϱ)

theorem kernelSpan_inv (ν ϱ : Weight) (c : Fin 8) (r : ℕ) :
    kernelSpan ν ϱ ≤ (kernelSpan ν ϱ).comap ((cvUnivRep (1, 0) ν ϱ 1).op c r) :=
  cycSub_inv _ _ c r

theorem kernelGenerator_mem (ν ϱ : Weight) : kernelGenerator ν ϱ ∈ kernelSpan ν ϱ :=
  wordOp_mem_cycSub _ _ []

theorem kernelSpan_le_ker (ν ϱ : Weight) : kernelSpan ν ϱ ≤ LinearMap.ker (quotientMap ν ϱ) := by
  have ht := (quotient_rel_iff.mp (cvUniv_rel (0, 1) (ν + (1, 0)) ϱ 0)).2
  rw [kernelSpan, cycSub, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  change quotientMap ν ϱ
    (wordOp (cvUnivRep (1, 0) ν ϱ 1) l (kernelGenerator ν ϱ)) = 0
  have hw : wordOp (cvUnivRep (1, 0) ν ϱ 1) l (kernelGenerator ν ϱ) =
      wordOp (cvUnivRep (1, 0) ν ϱ 1) (l ++ [(3, ν.1 + ϱ.1 + 1)])
        (cv_wU (1, 0) ν ϱ 1) := by
    rw [wordOp_append]
    rfl
  rw [hw, quotientMap_wordOp, wordOp_append]
  change wordOp (cvUnivRep (0, 1) (ν + (1, 0)) ϱ 0) l
    ((cvUnivRep (0, 1) (ν + (1, 0)) ϱ 0).op 3 (ν.1 + ϱ.1 + 1)
      (cv_wU (0, 1) (ν + (1, 0)) ϱ 0)) = 0
  rw [ht, wordOp_zero]

/-- The current action on the quotient by the explicit one-generator submodule. -/
def kernelQuotientRep (ν ϱ : Weight) :
    CurrentModule bracketTable (CVMod (1, 0) ν ϱ 1 ⧸ kernelSpan ν ϱ) :=
  quotRep (cvUnivRep (1, 0) ν ϱ 1) (kernelSpan ν ϱ) (kernelSpan_inv ν ϱ)

/-- The explicit quotient satisfies the complete actual base presentation. -/
theorem kernelQuotient_rel (ν ϱ : Weight) :
    CV3Rel (kernelQuotientRep ν ϱ) ((kernelSpan ν ϱ).mkQ (cv_wU (1, 0) ν ϱ 1))
      (0, 1) (ν + (1, 0)) ϱ 0 := by
  have hs := sat_cvSpec_iff.mpr (cvUniv_rel (1, 0) ν ϱ 1)
  have hq : UnivG.Sat bracketTable (kernelQuotientRep ν ϱ)
      ((kernelSpan ν ϱ).mkQ (cv_wU (1, 0) ν ϱ 1)) (cvSpec (1, 0) ν ϱ 1) := by
    refine ⟨?_, ?_⟩
    · intro t ht
      dsimp only [kernelQuotientRep]
      rw [quot_wordOp, hs.tail t ht, map_zero]
    · intro p hp
      dsimp only [kernelQuotientRep]
      rw [quotRep_op, hs.eig p hp, map_smul]
  apply quotient_rel (sat_cvSpec_iff.mp hq)
  dsimp only [kernelQuotientRep]
  rw [quotRep_op]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (kernelGenerator_mem ν ϱ)

/-- The actual universal inverse into the explicit quotient. -/
def quotientInverse (ν ϱ : Weight) :
    CVMod (0, 1) (ν + (1, 0)) ϱ 0 →ₗ[ℂ] (CVMod (1, 0) ν ϱ 1 ⧸ kernelSpan ν ϱ) :=
  cvMap (kernelQuotient_rel ν ϱ)

theorem quotientInverse_comp (ν ϱ : Weight) :
    (quotientInverse ν ϱ).comp (quotientMap ν ϱ) = (kernelSpan ν ϱ).mkQ := by
  apply LinearMap.ext_on_range (cv_span_top (1, 0) ν ϱ 1)
  intro l
  rw [LinearMap.comp_apply, quotientMap_wordOp]
  change cvMap (kernelQuotient_rel ν ϱ)
    (wordOp (cvUnivRep (0, 1) (ν + (1, 0)) ϱ 0) l
      (cv_wU (0, 1) (ν + (1, 0)) ϱ 0)) = _
  rw [cvMap_wordOp]
  dsimp only [kernelQuotientRep]
  rw [quot_wordOp]

/-- The kernel of the actual base quotient is exactly the first cyclic
kernel submodule, with no exactness or dimension premise. -/
theorem quotientMap_ker (ν ϱ : Weight) : LinearMap.ker (quotientMap ν ϱ) = kernelSpan ν ϱ := by
  apply le_antisymm _ (kernelSpan_le_ker ν ϱ)
  intro x hx
  have he := congrArg (fun f => f x) (quotientInverse_comp ν ϱ)
  change quotientInverse ν ϱ (quotientMap ν ϱ x) = (kernelSpan ν ϱ).mkQ x at he
  rw [LinearMap.mem_ker.mp hx, map_zero] at he
  exact (Submodule.Quotient.mk_eq_zero _).mp he.symm

/-- The actual universal map onto the one cyclic kernel submodule. -/
def kernelMap (ν ϱ : Weight) :
    CVMod (0, 0) (ν + (0, 1)) ϱ 0 →ₗ[ℂ] CVMod (1, 0) ν ϱ 1 :=
  cvMap (kernel_rel (cvUniv_rel (1, 0) ν ϱ 1))

theorem kernelMap_range (ν ϱ : Weight) : LinearMap.range (kernelMap ν ϱ) = kernelSpan ν ϱ :=
  cvMap_range _

/-- The genuine fundamental `j=1` two-term dimension step. Only
finite-dimensionality of the two zero-adjoint base modules is assumed. -/
theorem dimension_step (ν ϱ : Weight)
    [FiniteDimensional ℂ (CVMod (0, 1) (ν + (1, 0)) ϱ 0)]
    [FiniteDimensional ℂ (CVMod (0, 0) (ν + (0, 1)) ϱ 0)] :
    FiniteDimensional ℂ (CVMod (1, 0) ν ϱ 1) ∧
      Module.finrank ℂ (CVMod (1, 0) ν ϱ 1) ≤
        Module.finrank ℂ (CVMod (0, 1) (ν + (1, 0)) ϱ 0) +
        Module.finrank ℂ (CVMod (0, 0) (ν + (0, 1)) ϱ 0) := by
  haveI : FiniteDimensional ℂ (kernelSpan ν ϱ) := by
    rw [← kernelMap_range ν ϱ]
    infer_instance
  haveI : FiniteDimensional ℂ (CVMod (1, 0) ν ϱ 1) :=
    Module.Finite.of_exact (f := (kernelSpan ν ϱ).subtype) (g := quotientMap ν ϱ)
      (LinearMap.exact_iff.mpr (by rw [Submodule.range_subtype, quotientMap_ker]))
      (quotientMap_surjective ν ϱ)
  refine ⟨inferInstance, ?_⟩
  have hk := LinearMap.finrank_range_le (kernelMap ν ϱ)
  rw [kernelMap_range] at hk
  have he := (quotientMap ν ϱ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientMap_surjective ν ϱ), finrank_top,
    quotientMap_ker] at he
  omega

end

end VOA.DeligneAudit.A2.CVBaseFundamental

#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.quotient_rel
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.quotient_rel_iff
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.kernel_rel
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.quotientMap_surjective
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.quotientMap_cycDeg
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.kernelQuotient_rel
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.quotientMap_ker
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.kernelMap_range
#print axioms VOA.DeligneAudit.A2.CVBaseFundamental.dimension_step
