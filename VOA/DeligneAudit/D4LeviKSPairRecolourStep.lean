import VOA.DeligneAudit.D4LeviKSPairRecolour

/-! The one-mode Θ5 conversion as a positional recolouring sum. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

/-- The word obtained by converting the X position `t` to U' and adding
    the current mode `r` at that position. -/
noncomputable def pairPositionWord {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6)
    (is : List σ) (d : σ →₀ ℕ) (t : σ) (r : ℕ) :
    List (Fin 6 × ℕ) :=
  shapedModes (Function.update shape t 3) is (Finsupp.single t r + d)

theorem pairPositionWord_cons_self {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6) (t : σ) (ts : List σ)
    (ht : t ∉ ts) (d : σ →₀ ℕ) (r : ℕ) :
    pairPositionWord shape (t :: ts) d t r =
      (3, r + d t) :: shapedModes shape ts d := by
  simp only [pairPositionWord, shapedModes, List.map_cons]
  congr 1
  · simp [Function.update, Finsupp.single_apply]
  · apply List.map_congr_left
    intro i hi
    have hit : i ≠ t := by
      intro heq
      exact ht (heq ▸ hi)
    simp [Function.update, Finsupp.single_apply, hit]

theorem pairPositionWord_cons_other {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6) (t i : σ) (ts : List σ)
    (hti : t ≠ i) (d : σ →₀ ℕ) (r : ℕ) :
    pairPositionWord shape (t :: ts) d i r =
      (shape t, d t) :: pairPositionWord shape ts d i r := by
  simp [pairPositionWord, shapedModes, Function.update,
    Finsupp.single_apply, hti, hti.symm]

/-- No U letters occur in any intermediate PAIR recolouring shape. -/
theorem pairRecolourShape_ne_u (a b c k : ℕ)
    (t : PairSource a b c) : pairRecolourShape a b c k t ≠ 2 := by
  rcases t with (y | x) | (y | z)
  · simp [pairRecolourShape]; split_ifs <;> decide
  · simp [pairRecolourShape]
  · simp [pairRecolourShape]
  · simp [pairRecolourShape]

/-- The recursive Θ5 list is the list of conversions at X positions.
    Keeping this as a list retains multiplicities of equal-mode words. -/
theorem threeWords_shapedModes_positions {σ : Type*}
    [DecidableEq σ] (shape : σ → Fin 6) (is : List σ)
    (his : is.Nodup) (hshape : ∀ t ∈ is, shape t ≠ 2)
    (d : σ →₀ ℕ) (r : ℕ) :
    threeWords r (shapedModes shape is d) =
      (is.filter fun t => shape t = 1).map
        (fun t => pairPositionWord shape is d t r) := by
  induction is with
  | nil => simp [threeWords, shapedModes]
  | cons t ts ih =>
      have ht : t ∉ ts := (List.nodup_cons.mp his).1
      have hts : ts.Nodup := (List.nodup_cons.mp his).2
      have hshapeTail : ∀ i ∈ ts, shape i ≠ 2 := by
        intro i hi
        exact hshape i (List.mem_cons_of_mem t hi)
      have ih' := ih hts hshapeTail
      change threeWords r (List.map (fun i => (shape i, d i)) ts) =
        (ts.filter fun i => shape i = 1).map
          (fun i => pairPositionWord shape ts d i r) at ih'
      have ht2 : shape t ≠ 2 := hshape t (List.mem_cons_self)
      by_cases ht1 : shape t = 1
      · simp only [shapedModes, List.map_cons, threeWords,
          ht1, if_true, List.singleton_append, List.filter_cons,
          List.map_cons, List.cons_append]
        rw [ih']
        simp only [List.nil_append, List.map_map,
          show decide True = true by decide, if_true]
        congr 1
        · exact (pairPositionWord_cons_self shape t ts ht d r).symm
        · apply List.map_congr_left
          intro i hi
          have hit : t ≠ i := by
            intro heq
            exact ht (heq ▸ (List.mem_filter.mp hi).1)
          simpa only [ht1, Function.comp_apply] using
            (pairPositionWord_cons_other shape t i ts hit d r).symm
      · simp only [shapedModes, List.map_cons, threeWords,
          ht1, if_false, ht2, List.filter_cons,
          List.nil_append]
        rw [ih']
        simp only [List.map_map,
          show decide False = false by decide, if_false]
        apply List.map_congr_left
        intro i hi
        have hit : t ≠ i := by
          intro heq
          exact ht (heq ▸ (List.mem_filter.mp hi).1)
        exact (pairPositionWord_cons_other shape t i ts hit d r).symm

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Sum of the words obtained by converting one X-labelled position. -/
noncomputable def pairPositionalEvaluation {σ : Type*} [Fintype σ]
    [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (r : ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] V :=
  modeWordEvaluation σ fun d =>
    ((Finset.univ.toList.filter fun t => shape t = 1).map
      fun t => radicalWord ρ w
        (pairPositionWord shape Finset.univ.toList d t r)).sum

/-- One selected term of the positional conversion sum is evaluation with
    that position recoloured and its mode shifted. -/
theorem pairPositionEvaluation_eq_shift
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (t : σ) (r : ℕ)
    (P : MvPolynomial σ ℂ) :
    modeWordEvaluation σ (fun d => radicalWord ρ w
        (pairPositionWord shape Finset.univ.toList d t r)) P =
      xyzEvaluation ρ w (Function.update shape t 3) (X t ^ r * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial σ ℂ) =
          z • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul, smul_eq_mul, mul_assoc,
        LinearMap.smul_apply]
      have hmul : X t ^ r * modeMonomial σ d =
          modeMonomial σ (Finsupp.single t r + d) := by
        simp [modeMonomial, X_pow_eq_monomial, monomial_mul]
      rw [show X t ^ r * (z • modeMonomial σ d) =
          z • (X t ^ r * modeMonomial σ d) by
        simp [smul_eq_mul, mul_comm, mul_left_comm]]
      rw [hmul]
      simp only [modeWordEvaluation_monomial,
        xyzEvaluation, map_smul, modeWordEvaluation_monomial,
        pairPositionWord]
  | add P Q ihP ihQ =>
      simp only [map_add, mul_add, ihP, ihQ]

/-- The positional conversion is a sum of independently recoloured
    polynomial evaluations. -/
theorem pairPositionalEvaluation_eq_sum
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (r : ℕ)
    (P : MvPolynomial σ ℂ) :
    pairPositionalEvaluation ρ w shape r P =
      ((Finset.univ.toList.filter fun t => shape t = 1).map
        fun t => xyzEvaluation ρ w (Function.update shape t 3)
          (X t ^ r * P)).sum := by
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial σ ℂ) =
          z • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      have hterm (t : σ) :
          xyzEvaluation ρ w (Function.update shape t 3)
              (X t ^ r * (z • modeMonomial σ d)) =
            z • xyzEvaluation ρ w (Function.update shape t 3)
              (X t ^ r * modeMonomial σ d) := by
        rw [mul_smul_comm, map_smul]
      simp_rw [hterm]
      rw [map_smul]
      have hsum (L : List σ) :
          (L.map
            fun t => z • xyzEvaluation ρ w (Function.update shape t 3)
              (X t ^ r * modeMonomial σ d)).sum =
            z • (L.map
              fun t => xyzEvaluation ρ w (Function.update shape t 3)
                (X t ^ r * modeMonomial σ d)).sum := by
        induction L with
        | nil => simp
        | cons t ts ih =>
            simp only [List.map_cons, List.sum_cons, smul_add]
            rw [ih]
      rw [hsum]
      apply congrArg (z • ·)
      rw [pairPositionalEvaluation, modeWordEvaluation_monomial]
      congr 1
      apply List.map_congr_left
      intro t ht
      simpa only [modeWordEvaluation_monomial] using
        pairPositionEvaluation_eq_shift ρ w shape t r
          (modeMonomial σ d)
  | add P Q ihP ihQ =>
      rw [map_add]
      simp only [mul_add, map_add]
      rw [List.sum_map_add]
      exact congrArg₂ (· + ·) ihP ihQ

/-- The free-word conversion evaluates to the positional sum. -/
theorem pairPolynomialConvert_monomial_positions
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (hshape : ∀ t, shape t ≠ 2)
    (r : ℕ) (d : σ →₀ ℕ) :
    pairWordOpEvaluation ρ
        (pairPolynomialConvert shape r (modeMonomial σ d)) w =
      pairPositionalEvaluation ρ w shape r (modeMonomial σ d) := by
  rw [pairPolynomialConvert_monomial]
  simp only [map_list_sum, List.map_map, Function.comp_def,
    pairWordOpEvaluation_single, pairRadicalOp_apply,
    pairPositionalEvaluation, modeWordEvaluation_monomial]
  rw [threeWords_shapedModes_positions shape Finset.univ.toList
    (Finset.nodup_toList _) (by intro t _; exact hshape t) d r]
  rw [pairRadicalOp_sum_apply]
  simp only [List.map_map, Function.comp_def]

/-- Exact one-mode Θ5 bridge from a polynomial to the positional sum. -/
theorem pairPolynomialConvert_evaluation_positions
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (hshape : ∀ t, shape t ≠ 2)
    (r : ℕ) (P : MvPolynomial σ ℂ) :
    pairWordOpEvaluation ρ (pairPolynomialConvert shape r P) w =
      pairPositionalEvaluation ρ w shape r P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d t =>
      have hm : (monomial d t : MvPolynomial σ ℂ) =
          t • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul, LinearMap.smul_apply]
      exact congrArg (t • ·)
        (pairPolynomialConvert_monomial_positions ρ w shape hshape r d)
  | add P Q ihP ihQ =>
      simp only [map_add, LinearMap.add_apply, ihP, ihQ]

/-- The f₃ adjoint of a recoloured polynomial is the negative positional
    sum over exactly its still-X-coloured letters. -/
theorem pairRecolour_adjoint_positions
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (P : MvPolynomial (PairSource a b c) ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRecolourOperator ρ a b c k P) w =
      -pairPositionalEvaluation ρ w (pairRecolourShape a b c k) r P := by
  rw [pairRecolour_adjoint_one]
  rw [pairPolynomialConvert_evaluation_positions ρ w
    (pairRecolourShape a b c k) (pairRecolourShape_ne_u a b c k) r P]

/-- One f₃ mode acts by converting each remaining X position in turn. -/
theorem pairRecolour_adjoint_shift_sum
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (P : MvPolynomial (PairSource a b c) ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRecolourOperator ρ a b c k P) w =
      -((Finset.univ.toList.filter fun t =>
          pairRecolourShape a b c k t = 1).map
        fun t => xyzEvaluation ρ w
          (Function.update (pairRecolourShape a b c k) t 3)
          (X t ^ r * P)).sum := by
  rw [pairRecolour_adjoint_positions]
  rw [pairPositionalEvaluation_eq_sum]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairPositionWord_cons_self
#print axioms VOA.DeligneAudit.D4Levi.pairPositionWord_cons_other
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_ne_u
#print axioms VOA.DeligneAudit.D4Levi.threeWords_shapedModes_positions
#print axioms VOA.DeligneAudit.D4Levi.pairPositionEvaluation_eq_shift
#print axioms VOA.DeligneAudit.D4Levi.pairPositionalEvaluation_eq_sum
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialConvert_monomial_positions
#print axioms VOA.DeligneAudit.D4Levi.pairPolynomialConvert_evaluation_positions
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_positions
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_shift_sum
