import VOA.DeligneAudit.D4LeviKSPairUFactorial

/-! Linear extension of the one-mode and iterated Θ5 word conversion. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

abbrev PairWord := List (Fin 6 × ℕ)
abbrev PairWordCombination := PairWord →₀ ℂ

/-- The free linear combination of the words obtained by one f₃ conversion. -/
noncomputable def pairWordConvertBasis (r : ℕ) (l : PairWord) :
    PairWordCombination :=
  ((threeWords r l).map fun q => Finsupp.single q (1 : ℂ)).sum

/-- The one-mode conversion on finite linear combinations of radical words. -/
noncomputable def pairWordConvert (r : ℕ) :
    PairWordCombination →ₗ[ℂ] PairWordCombination :=
  Finsupp.lsum ℂ fun l =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ PairWordCombination).symm
      (pairWordConvertBasis r l)

theorem pairWordConvert_single (r : ℕ) (l : PairWord) :
    pairWordConvert r (Finsupp.single l 1) = pairWordConvertBasis r l := by
  simp [pairWordConvert, Finsupp.lsum_single]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Linear evaluation of a finite radical-word combination as operators. -/
noncomputable def pairWordOpEvaluation (ρ : CurrentModule D4sector.f V) :
    PairWordCombination →ₗ[ℂ] Module.End ℂ V :=
  Finsupp.lsum ℂ fun l =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ (Module.End ℂ V)).symm
      (pairRadicalOp ρ l)

theorem pairWordOpEvaluation_single (ρ : CurrentModule D4sector.f V)
    (l : PairWord) :
    pairWordOpEvaluation ρ (Finsupp.single l 1) = pairRadicalOp ρ l := by
  simp [pairWordOpEvaluation, Finsupp.lsum_single]

theorem pairWordOpEvaluation_convertBasis
    (ρ : CurrentModule D4sector.f V) (r : ℕ) (l : PairWord) :
    pairWordOpEvaluation ρ (pairWordConvertBasis r l) =
      ((threeWords r l).map (pairRadicalOp ρ)).sum := by
  simp only [pairWordConvertBasis, map_list_sum, List.map_map,
    Function.comp_def, pairWordOpEvaluation_single]

/-- Exact linear Θ5 bridge, valid for arbitrary finite word combinations. -/
theorem pairWordOpEvaluation_convert
    (ρ : CurrentModule D4sector.f V) (r : ℕ)
    (P : PairWordCombination) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r] (pairWordOpEvaluation ρ P) =
      -pairWordOpEvaluation ρ (pairWordConvert r P) := by
  induction P using Finsupp.induction with
  | zero => simp [pairWordConvert, pairWordOpEvaluation, pairAdjoint]
  | single_add l z P hl hz ih =>
      simp only [map_add, pairAdjoint_add]
      have hone :
          pairAdjoint (ρ.op (17 : Fin 28)) [r]
              (pairWordOpEvaluation ρ (Finsupp.single l z)) =
            -pairWordOpEvaluation ρ
              (pairWordConvert r (Finsupp.single l z)) := by
        rw [← Finsupp.smul_single_one, map_smul, pairAdjoint_smul,
          map_smul, map_smul, pairWordConvert_single,
          pairWordOpEvaluation_single]
        simp only [pairAdjoint, fThree_adjoint_radicalOp,
          pairWordOpEvaluation_convertBasis]
        module
      rw [hone, ih]
      abel

/-- Convert successively at the modes of a current word. -/
noncomputable def pairWordConvertIter : List ℕ →
    PairWordCombination →ₗ[ℂ] PairWordCombination
  | [] => LinearMap.id
  | r :: rs => (pairWordConvertIter rs).comp (pairWordConvert r)

/-- The linear iterate has exactly the paths of the recursive Θ5 tree. -/
theorem pairWordConvertIter_single (rs : List ℕ) (l : PairWord) :
    pairWordConvertIter rs (Finsupp.single l 1) =
      ((threeWordsIter rs l).map fun q => Finsupp.single q (1 : ℂ)).sum := by
  induction rs generalizing l with
  | nil => simp [pairWordConvertIter, threeWordsIter]
  | cons r rs ih =>
      simp only [pairWordConvertIter, LinearMap.comp_apply,
        pairWordConvert_single, pairWordConvertBasis, threeWordsIter]
      rw [map_list_sum]
      simp only [List.map_map, Function.comp_def, ih]
      simp [List.flatMap_def, List.map_flatten, List.sum_flatten]
      rfl

/-- The iterated adjoint is the evaluation of the iterated linear conversion. -/
theorem pairWordOpEvaluation_convertIter
    (ρ : CurrentModule D4sector.f V) (rs : List ℕ)
    (P : PairWordCombination) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs (pairWordOpEvaluation ρ P) =
      (-1 : ℂ) ^ rs.length •
        pairWordOpEvaluation ρ (pairWordConvertIter rs P) := by
  induction rs generalizing P with
  | nil => simp [pairAdjoint, pairWordConvertIter]
  | cons r rs ih =>
      simp only [pairAdjoint, pairWordConvertIter, LinearMap.comp_apply,
        List.length_cons, pow_succ]
      have hone :
          ρ.op (17 : Fin 28) r * pairWordOpEvaluation ρ P -
              pairWordOpEvaluation ρ P * ρ.op (17 : Fin 28) r =
            -pairWordOpEvaluation ρ (pairWordConvert r P) := by
        simpa only [pairAdjoint] using pairWordOpEvaluation_convert ρ r P
      rw [hone, pairAdjoint_neg, ih]
      simp

/-- A zero converted word combination has zero iterated adjoint operator. -/
theorem pairWordConvertIter_zero_adjoint
    (ρ : CurrentModule D4sector.f V) (rs : List ℕ)
    (P : PairWordCombination)
    (h : pairWordConvertIter rs P = 0) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs (pairWordOpEvaluation ρ P) = 0 := by
  rw [pairWordOpEvaluation_convertIter, h]
  simp

/-- Embed a labelled mode polynomial linearly into radical-word combinations. -/
noncomputable def pairPolynomialWords {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) :
    MvPolynomial σ ℂ →ₗ[ℂ] PairWordCombination :=
  modeWordEvaluation σ fun a =>
    Finsupp.single (shapedModes shape Finset.univ.toList a) 1

theorem pairPolynomialWords_monomial {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (a : σ →₀ ℕ) :
    pairPolynomialWords shape (modeMonomial σ a) =
      Finsupp.single (shapedModes shape Finset.univ.toList a) 1 := by
  exact modeWordEvaluation_monomial σ _ a

/-- Evaluating the embedded polynomial on a vector is the existing XYZ
    word evaluator, for any fixed choice of radical colours. -/
theorem pairPolynomialWords_eval {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (P : MvPolynomial σ ℂ) :
    pairWordOpEvaluation ρ (pairPolynomialWords shape P) w =
      xyzEvaluation ρ w shape P := by
  induction P using MvPolynomial.induction_on' with
  | monomial a t =>
      have hm : (monomial a t : MvPolynomial σ ℂ) =
          t • modeMonomial σ a := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul, LinearMap.smul_apply,
        pairPolynomialWords_monomial, pairWordOpEvaluation_single,
        pairRadicalOp_apply, xyzEvaluation, modeWordEvaluation_monomial]
  | add P Q ihP ihQ =>
      simp only [map_add, LinearMap.add_apply, ihP, ihQ]

/-- The polynomial one-mode conversion, with converted colours retained
    as labels in the free word module. -/
noncomputable def pairPolynomialConvert {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (r : ℕ) :
    MvPolynomial σ ℂ →ₗ[ℂ] PairWordCombination :=
  (pairWordConvert r).comp (pairPolynomialWords shape)

/-- The iterated polynomial conversion on labelled mode assignments. -/
noncomputable def pairPolynomialConvertIter {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (rs : List ℕ) :
    MvPolynomial σ ℂ →ₗ[ℂ] PairWordCombination :=
  (pairWordConvertIter rs).comp (pairPolynomialWords shape)

theorem pairPolynomialConvert_monomial {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (r : ℕ) (a : σ →₀ ℕ) :
    pairPolynomialConvert shape r (modeMonomial σ a) =
      ((threeWords r (shapedModes shape Finset.univ.toList a)).map
        fun q => Finsupp.single q (1 : ℂ)).sum := by
  simp [pairPolynomialConvert, pairPolynomialWords_monomial,
    pairWordConvert_single, pairWordConvertBasis]

theorem pairPolynomialConvertIter_monomial {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (rs : List ℕ) (a : σ →₀ ℕ) :
    pairPolynomialConvertIter shape rs (modeMonomial σ a) =
      ((threeWordsIter rs (shapedModes shape Finset.univ.toList a)).map
        fun q => Finsupp.single q (1 : ℂ)).sum := by
  simpa only [pairPolynomialConvertIter, LinearMap.comp_apply,
    pairPolynomialWords_monomial] using
      pairWordConvertIter_single rs (shapedModes shape Finset.univ.toList a)

/-- A polynomial identity in the converted word module evaluates to an
    exact operator identity, independently of saturation or key hypotheses. -/
theorem pairPolynomialConvertIter_zero_adjoint
    {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (shape : σ → Fin 6)
    (rs : List ℕ) (P : MvPolynomial σ ℂ)
    (h : pairPolynomialConvertIter shape rs P = 0) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
      (pairWordOpEvaluation ρ (pairPolynomialWords shape P)) = 0 := by
  apply pairWordConvertIter_zero_adjoint ρ rs
  exact h

/-- The exact Θ5 conversion of a mode polynomial, evaluated at a vector. -/
theorem pairPolynomialConvertIter_adjoint_apply
    {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (rs : List ℕ) (P : MvPolynomial σ ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairWordOpEvaluation ρ (pairPolynomialWords shape P)) w =
      (-1 : ℂ) ^ rs.length •
        pairWordOpEvaluation ρ (pairPolynomialConvertIter shape rs P) w := by
  exact congrArg (fun A : Module.End ℂ V => A w)
    (pairWordOpEvaluation_convertIter ρ rs (pairPolynomialWords shape P))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairWordConvert_single
#print axioms VOA.DeligneAudit.D4Levi.pairWordOpEvaluation_single
#print axioms VOA.DeligneAudit.D4Levi.pairWordOpEvaluation_convertBasis
#print axioms VOA.DeligneAudit.D4Levi.pairWordOpEvaluation_convert
#print axioms VOA.DeligneAudit.D4Levi.pairWordOpEvaluation_convertIter
#print axioms VOA.DeligneAudit.D4Levi.pairWordConvertIter_single
#print axioms VOA.DeligneAudit.D4Levi.pairWordConvertIter_zero_adjoint
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialWords_monomial
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialWords_eval
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialConvert_monomial
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialConvertIter_monomial
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialConvertIter_zero_adjoint
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialConvertIter_adjoint_apply
