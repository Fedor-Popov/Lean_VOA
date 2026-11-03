import VOA.DeligneAudit.D4LeviKSPairThetaLinear

/-! Recolour the paired X positions while retaining the source variable type. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

/-- The first `k` paired X positions have become U', while the remaining
    paired and unpaired X positions retain colour X. -/
def pairRecolourShape (a b c k : ℕ) : PairSource a b c → Fin 6
  | Sum.inl (Sum.inl y) => if y.val < k then 3 else 1
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr (Sum.inl _) => 4
  | Sum.inr (Sum.inr _) => 5

/-- At the start, the recoloured shape is the source XYZ shape. -/
theorem pairRecolourShape_zero (a b c : ℕ) :
    pairRecolourShape a b c 0 = pairSourceShape a b c := by
  funext t
  rcases t with (y | x) | (y | z)
  · simp [pairRecolourShape, pairSourceShape]
  · rfl
  · rfl
  · rfl

/-- In the final shape, every paired X position has colour U'. -/
theorem pairRecolourShape_paired_final (a b c : ℕ) (y : Fin b) :
    pairRecolourShape a b c b (Sum.inl (Sum.inl y)) = 3 := by
  simp [pairRecolourShape, y.isLt]

/-- The target variables have colours X, U', and Z. -/
def pairRecolourTargetShape (a b c : ℕ) : PairTarget a b c → Fin 6
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 3
  | Sum.inr (Sum.inr _) => 5

/-- After removing the Y variables, final source colours agree with the
    target colours along restriction. -/
theorem pairRecolourShape_final_of_not_y (a b c : ℕ)
    (t : PairSource a b c)
    (ht : ∀ y : Fin b, t ≠ Sum.inr (Sum.inl y)) :
    pairRecolourShape a b c b t =
      pairRecolourTargetShape a b c (pairVariable a b c t) := by
  rcases t with (y | x) | (y | z)
  · exact pairRecolourShape_paired_final a b c y
  · rfl
  · exact False.elim (ht y rfl)
  · rfl

/-- The colour at an as-yet-unpaired X position. -/
theorem pairRecolourShape_unpaired_at (a b c k : ℕ)
    (y : Fin b) (hy : k ≤ y.val) :
    pairRecolourShape a b c k (Sum.inl (Sum.inl y)) = 1 := by
  simp [pairRecolourShape, not_lt.mpr hy]

/-- Recolouring one position advances only that paired X position. -/
theorem pairRecolourShape_step (a b c k : ℕ) (hk : k < b)
    (t : PairSource a b c) :
    pairRecolourShape a b c (k + 1) t =
      if t = Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b)) then 3
      else pairRecolourShape a b c k t := by
  rcases t with (y | x) | (y | z)
  · by_cases h : y.val = k
    · have heq : y = (⟨k, hk⟩ : Fin b) := Fin.ext h
      subst y
      simp [pairRecolourShape]
    · have heq : y ≠ (⟨k, hk⟩ : Fin b) := by
        intro heq
        exact h (congrArg Fin.val heq)
      simp only [Sum.inl.injEq, heq, if_false, pairRecolourShape]
      have hlt : y.val < k + 1 ↔ y.val < k := by omega
      simp [hlt]
  · simp [pairRecolourShape]
  · simp [pairRecolourShape]
  · simp [pairRecolourShape]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A variable permutation changes only the order of the abelian radical
    word, so fixed-shape evaluation is equivariant under relabelling. -/
theorem xyzEvaluation_rename_equiv {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (e : σ ≃ σ) (P : MvPolynomial σ ℂ) :
    xyzEvaluation ρ w shape (rename e P) =
      xyzEvaluation ρ w (shape ∘ e) P := by
  classical
  have hword (d : σ →₀ ℕ) :
      (shapedModes shape Finset.univ.toList (d.mapDomain e)).Perm
        (shapedModes (shape ∘ e) Finset.univ.toList d) := by
    have hp : (Finset.univ.toList.map (e : σ → σ)).Perm
        (Finset.univ.toList : List σ) := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (Finset.nodup_toList _).map e.injective
      · exact Finset.nodup_toList _
      · ext i
        simp
        exact e.surjective i
    have h := hp.map fun j => (shape j, d (e.symm j))
    simpa [shapedModes, List.map_map, Function.comp_def,
      Finsupp.mapDomain_equiv_apply] using h.symm
  induction P using MvPolynomial.induction_on' with
  | monomial d t =>
      have hm : (monomial d t : MvPolynomial σ ℂ) =
          t • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul]
      have hr : rename e (modeMonomial σ d) =
          modeMonomial σ (d.mapDomain e) := by
        simp [modeMonomial, rename_monomial]
      rw [hr]
      simp only [xyzEvaluation, modeWordEvaluation_monomial]
      exact congrArg (t • ·) (radicalWord_perm ρ w (hword d))
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ]

/-- The fixed-shape evaluation used at every stage of PAIR conversion. -/
noncomputable def pairRecolourEvaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k : ℕ) : MvPolynomial (PairSource a b c) ℂ →ₗ[ℂ] V :=
  xyzEvaluation ρ w (pairRecolourShape a b c k)

/-- Operator-valued evaluation before applying the current word to `w`. -/
noncomputable def pairRecolourOperator
    (ρ : CurrentModule D4sector.f V) (a b c k : ℕ) :
    MvPolynomial (PairSource a b c) ℂ →ₗ[ℂ] Module.End ℂ V :=
  (pairWordOpEvaluation ρ).comp
    (pairPolynomialWords (pairRecolourShape a b c k))

theorem pairRecolourOperator_apply
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k : ℕ) (P : MvPolynomial (PairSource a b c) ℂ) :
    pairRecolourOperator ρ a b c k P w =
      pairRecolourEvaluation ρ w a b c k P := by
  exact pairPolynomialWords_eval ρ w (pairRecolourShape a b c k) P

/-- Exact one-mode conversion at the `k`th fixed recolouring shape. -/
theorem pairRecolour_adjoint_one
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (P : MvPolynomial (PairSource a b c) ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRecolourOperator ρ a b c k P) w =
      -pairWordOpEvaluation ρ
        (pairPolynomialConvert (pairRecolourShape a b c k) r P) w := by
  simpa [pairRecolourOperator, pairPolynomialConvert, pairAdjoint,
    pairPolynomialConvertIter, pairWordConvertIter] using
    pairPolynomialConvertIter_adjoint_apply ρ w
      (pairRecolourShape a b c k) [r] P

/-- Exact iterated conversion at a fixed recolouring shape. This records
    all conversion paths with their multiplicities. -/
theorem pairRecolour_adjoint_iter
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k : ℕ) (rs : List ℕ)
    (P : MvPolynomial (PairSource a b c) ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs
        (pairRecolourOperator ρ a b c k P) w =
      (-1 : ℂ) ^ rs.length •
        pairWordOpEvaluation ρ
          (pairPolynomialConvertIter (pairRecolourShape a b c k) rs P) w := by
  exact pairPolynomialConvertIter_adjoint_apply ρ w
    (pairRecolourShape a b c k) rs P

theorem pairRecolourEvaluation_zero
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c : ℕ) :
    pairRecolourEvaluation ρ w a b c 0 =
      xyzEvaluation ρ w (pairSourceShape a b c) := by
  simp [pairRecolourEvaluation, pairRecolourShape_zero]

/-- At the final stage the paired X variables have become U' letters. -/
theorem pairRecolourEvaluation_final_monomial
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (d : PairSource a b c →₀ ℕ) :
    pairRecolourEvaluation ρ w a b c b
        (modeMonomial (PairSource a b c) d) =
      radicalWord ρ w
        (shapedModes (pairRecolourShape a b c b)
          Finset.univ.toList d) := by
  simp [pairRecolourEvaluation,
    xyzEvaluation, modeWordEvaluation_monomial]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_zero
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_paired_final
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_final_of_not_y
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_unpaired_at
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_step
#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_rename_equiv
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourOperator_apply
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_one
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_iter
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourEvaluation_zero
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourEvaluation_final_monomial
