import VOA.Classification.COne.QExpSpanUnit

/-!
# The actual weight-two product submodule

All elements of this submodule have a finite integer coefficient lattice.
Containment of all Gamma1 restrictions is the remaining classical spanning
statement (Khuri-Makdisi, Theorems 3.5 and 5.1, arXiv:0903.1439).
It is not proved here.
-/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

set_option maxSynthPendingDepth 3

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Finite coefficient algebras control every complex combination, even with
arbitrary transcendental complex coordinates. -/
theorem exists_int_lattice_of_mem_span_coeff {N : ℕ} (hN : 0 < N) {k : ℤ}
    {ι : Type*} [Finite ι] (A : Subalgebra ℤ ℂ) (hA : A.toSubmodule.FG)
    (E : ι → ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k)
    (hE : ∀ i n, (qExpansion (N : ℝ) (E i)).coeff n ∈ A)
    (F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : F ∈ Submodule.span ℂ (Set.range E)) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, (qExpansion (N : ℝ) F).coeff n ∈ L := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hF
  letI : Module.Finite ℤ A := Module.Finite.of_fg hA
  let L := Submodule.span A (Set.range c)
  have hL : L.FG := Submodule.fg_span (Set.finite_range c)
  refine ⟨L.restrictScalars ℤ, hL.restrictScalars (R := ℤ), fun n => ?_⟩
  rw [← hc]
  let Q := ModularForm.qExpansionAddHom (by exact_mod_cast hN : (0 : ℝ) < N)
    (nat_mem_strictPeriods_Gamma N) k
  change (Q (∑ i, c i • E i)).coeff n ∈ L
  rw [map_sum, map_sum]
  apply L.sum_mem
  intro i _
  change (qExpansion (N : ℝ) (c i • E i)).coeff n ∈ L
  rw [ModularForm.qExpansion_smul (by exact_mod_cast hN)
    (nat_mem_strictPeriods_Gamma N), PowerSeries.coeff_smul]
  have hm := L.smul_mem (⟨_, hE i n⟩ : A) (Submodule.subset_span ⟨i, rfl⟩)
  simpa only [Algebra.smul_def, smul_eq_mul, mul_comm] using hm

abbrev SpanProductIndex (N : ℕ) := (Fin N × Fin N) × (Fin N × Fin N)

def spanWeightTwoProduct {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (i : SpanProductIndex N) :
    ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2 :=
  (weightOneModularForm hN hζ (fullLevelWeightOneSlash24 N hN h24 ζ hζ) i.1.1 i.1.2).mul
    (weightOneModularForm hN hζ (fullLevelWeightOneSlash24 N hN h24 ζ hζ) i.2.1 i.2.2)

def spanWeightTwoProducts {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) :
    Submodule ℂ (ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2) :=
  Submodule.span ℂ (Set.range (spanWeightTwoProduct hN h24 hζ))

theorem spanWeightTwoProduct_coeff {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (i : SpanProductIndex N) (n : ℕ) :
    (qExpansion (N : ℝ) (spanWeightTwoProduct hN h24 hζ i)).coeff n =
      weightTwoProductCoeff N ζ i.1.1 i.1.2 i.2.1 i.2.2 n :=
  weightOneModularForm_mul_coeff hN hζ _ _ _ _ _ n

/-- The product subspace contains a nonzero form at every permitted level. -/
theorem spanWeightTwoProducts_ne_bot {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    spanWeightTwoProducts hN h24 hζ ≠ ⊥ := by
  have h4 : 4 ∣ N := dvd_trans (by norm_num : 4 ∣ 24) h24
  have hdiv : N / 4 * 4 = N := Nat.div_mul_cancel h4
  have ha : N / 4 ≠ 0 := by omega
  have haC : (N / 4 : ℕ) ≠ (0 : ℂ) := Nat.cast_ne_zero.mpr ha
  have hdivC : (N : ℂ) = (N / 4 : ℕ) * 4 := by exact_mod_cast hdiv.symm
  let i : SpanProductIndex N :=
    ((spanQuarterIndex hN, ⟨0, hN⟩), (spanQuarterIndex hN, ⟨0, hN⟩))
  have hc : (qExpansion (N : ℝ) (spanWeightTwoProduct hN h24 hζ i)).coeff 0 =
      ((N : ℂ) - 2 * (N / 4 : ℕ)) ^ 2 := by
    rw [spanWeightTwoProduct_coeff]
    simp [weightTwoProductCoeff, weightOneIntegralCoeff, i, spanQuarterIndex, ha, pow_two]
  have hn : (N : ℂ) - 2 * (N / 4 : ℕ) ≠ 0 := by
    rw [hdivC]
    have he : (N / 4 : ℕ) * (4 : ℂ) - 2 * (N / 4 : ℕ) = 2 * (N / 4 : ℕ) := by ring
    rw [he]
    exact mul_ne_zero (by norm_num) haC
  intro hbot
  have hm : spanWeightTwoProduct hN h24 hζ i ∈ spanWeightTwoProducts hN h24 hζ :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [hbot, Submodule.mem_bot] at hm
  rw [hm] at hc
  change (qExpansion (N : ℝ) (0 : ℍ → ℂ)).coeff 0 = _ at hc
  rw [qExpansion_zero, map_zero] at hc
  exact (pow_ne_zero 2 hn) hc.symm

/-- Unconditional arithmetic on the entire product subspace. -/
theorem exists_int_lattice_of_mem_products {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hF : F ∈ spanWeightTwoProducts hN h24 hζ) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, (qExpansion (N : ℝ) F).coeff n ∈ L := by
  have hzInt : IsIntegral ℤ ζ := isIntegral_of_pow_eq_one hN hζ.pow_eq_one
  apply exists_int_lattice_of_mem_span_coeff hN (Algebra.adjoin ℤ ({ζ} : Set ℂ))
    hzInt.fg_adjoin_singleton
    (spanWeightTwoProduct hN h24 hζ) _ F hF
  intro i n
  rw [spanWeightTwoProduct_coeff]
  exact (Algebra.adjoin ℤ ({ζ} : Set ℂ)).sum_mem fun p _ =>
    (Algebra.adjoin ℤ ({ζ} : Set ℂ)).mul_mem
      (weightOneIntegralCoeff_mem_int N ζ _ _ p.1)
      (weightOneIntegralCoeff_mem_int N ζ _ _ p.2)

/-- The restricted target holds integrally for any Gamma1 form in the product
subspace. There is no prime restriction in this stronger conclusion. -/
theorem exists_int_lattice_of_restriction_mem_products {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hF : restrictGamma1ToGamma hN F ∈ spanWeightTwoProducts hN h24 hζ) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, (qExpansion 1 F).coeff n ∈ L := by
  letI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨L, hL, hc⟩ := exists_int_lattice_of_mem_products hN h24 hζ _ hF
  refine ⟨L, hL, fun n => ?_⟩
  rw [← qExpansion_coeff_nat_mul hN F n]
  exact hc (N * n)

/-- The exact remaining containment. This is a consequence of the classical
full-level spanning theorem, not a Lean theorem or an axiom. -/
def FullLevelProductContainment24 : Prop :=
  ∀ N : ℕ, ∀ hN : 0 < N, ∀ h24 : 24 ∣ N, ∀ ζ : ℂ, ∀ hζ : IsPrimitiveRoot ζ N,
    ∀ F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2,
      restrictGamma1ToGamma hN F ∈ spanWeightTwoProducts hN h24 hζ

/-- This submodule formulation is exactly the earlier pointwise span input. -/
theorem fullLevelProductContainment24_iff_qSeriesSpan :
    FullLevelProductContainment24 ↔ FullLevelWeightOneQSeriesSpan24 := by
  classical
  constructor
  · intro h N hN h24 ζ hζ F
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (h N hN h24 ζ hζ F)
    let e := (Fintype.equivFin (SpanProductIndex N)).symm
    refine ⟨Fintype.card (SpanProductIndex N), (fun i => (e i).1.1),
      (fun i => (e i).1.2), (fun i => (e i).2.1), (fun i => (e i).2.2),
      (fun i => c (e i)), ?_⟩
    have he : (∑ i, c (e i) • spanWeightTwoProduct hN h24 hζ (e i)) =
        restrictGamma1ToGamma hN F :=
      (e.sum_comp (fun i => c i • spanWeightTwoProduct hN h24 hζ i)).trans hc
    intro τ
    have hev := congrArg (fun G : ModularForm
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2 => G τ) he
    change (ModularForm.coeHom (∑ i, c (e i) •
      spanWeightTwoProduct hN h24 hζ (e i))) τ = F τ at hev
    simpa [map_sum, ModularForm.coeHom, ModularForm.coe_smul, ModularForm.coe_mul,
      Finset.sum_apply, smul_eq_mul, spanWeightTwoProduct, weightOneModularForm] using hev.symm
  · intro h N hN h24 ζ hζ F
    obtain ⟨d, a, b, a', b', c, hc⟩ := h N hN h24 ζ hζ F
    have he : restrictGamma1ToGamma hN F =
        ∑ i, c i • spanWeightTwoProduct hN h24 hζ ((a i, b i), (a' i, b' i)) := by
      apply ModularForm.ext
      intro τ
      change F τ = (ModularForm.coeHom (∑ i, c i •
        spanWeightTwoProduct hN h24 hζ ((a i, b i), (a' i, b' i)))) τ
      simpa [map_sum, ModularForm.coeHom, ModularForm.coe_smul, ModularForm.coe_mul,
        Finset.sum_apply, smul_eq_mul, spanWeightTwoProduct, weightOneModularForm] using hc τ
    rw [he]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The new remaining statement has precisely the original Sturm-matching
content; no rank hypothesis was removed. -/
theorem fullLevelProductContainment24_iff_sturmMatching :
    FullLevelProductContainment24 ↔ FullLevelWeightTwoSturmMatching24 :=
  fullLevelProductContainment24_iff_qSeriesSpan.trans
    (fullLevelWeightTwoSturmMatching24_iff_span fullLevelWeightOneSlash24).symm

theorem qExpPrinciple24_two_of_productContainment
    (h : FullLevelProductContainment24) : QExpPrinciple24 2 := by
  intro N hN h24 F
  exact exists_int_lattice_of_restriction_mem_products hN h24
    (Complex.isPrimitiveRoot_exp N hN.ne') F
    (h N hN h24 _ (Complex.isPrimitiveRoot_exp N hN.ne') F)

theorem qExpPrinciple24Away_two_of_productContainment
    (h : FullLevelProductContainment24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_qExpPrinciple24 (qExpPrinciple24_two_of_productContainment h)

end VOA.Classification.COne.SSHecke
