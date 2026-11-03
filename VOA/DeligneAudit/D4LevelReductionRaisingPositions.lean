import VOA.DeligneAudit.D4LevelReductionZeroModeConversion

/-! Exact positional conversion of central radical letters by the middle raising current. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- All single central-to-middle replacements, retaining repeated positional terms. -/
def centralRaisingWords (r : ℕ) : List (Fin 6 × ℕ) → List (List (Fin 6 × ℕ))
  | [] => []
  | (i, s) :: l =>
      (if i = 5 then [(4, r + s) :: l] else []) ++
        (centralRaisingWords r l).map ((i, s) :: ·)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Middle raising is exactly central-letter conversion on three-colour radical words. -/
theorem middleRaising_word_sum (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (r : ℕ)
    (l : List (Fin 6 × ℕ)) (hl : ∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) :
    ρ.op (leviColour (A3Sector.simpleE 1)) r (radicalWord ρ w l) =
      ((centralRaisingWords r l).map (radicalWord ρ w)).sum := by
  induction l with
  | nil =>
      have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
        simpa [ravFam] using h
      simpa [radicalWord, wordOp, centralRaisingWords] using
        (rs_raising hs (show D4sector.raising (leviColour (A3Sector.simpleE 1)) by
          change 4 ≤ (leviColour (A3Sector.simpleE 1)).val ∧
            (leviColour (A3Sector.simpleE 1)).val < 16
          decide) r)
  | cons q l ih =>
      have ht : ∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5 :=
        fun t ht => hl t (List.mem_cons_of_mem _ ht)
      have hs := hl q (by simp)
      rcases q with ⟨i, s⟩
      have hc := simple_raise_comm ρ 1 i r s (radicalWord ρ w l)
      rcases hs with rfl | rfl | rfl
      · rw [middleRaising_adjoint_word ρ w m h r s l, ih ht, map_list_sum]
        simp [centralRaisingWords, List.map_map, Function.comp_def, radicalWord, wordOp]
      · simp only [raiseAction] at hc
        change ρ.op (leviColour (A3Sector.simpleE 1)) r
          (ρ.op (radicalColour 4) s (radicalWord ρ w l)) = _
        rw [sub_eq_zero.mp hc, ih ht, map_list_sum]
        simp [centralRaisingWords, List.map_map, Function.comp_def, radicalWord, wordOp]
      · simp only [raiseAction, Int.cast_one, one_smul] at hc
        change ρ.op (leviColour (A3Sector.simpleE 1)) r
          (ρ.op (radicalColour 5) s (radicalWord ρ w l)) = _
        rw [sub_eq_iff_eq_add.mp hc, ih ht, map_list_sum]
        simp [centralRaisingWords, List.map_map, Function.comp_def, radicalWord, wordOp]

/-- The word obtained by converting the central position `t` to a middle letter and adding
    the current mode `r` at that position. -/
noncomputable def centralRaisingPositionWord {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6)
    (is : List σ) (d : σ →₀ ℕ) (t : σ) (r : ℕ) :
    List (Fin 6 × ℕ) :=
  shapedModes (Function.update shape t 4) is (Finsupp.single t r + d)

theorem centralRaisingPositionWord_cons_self {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6) (t : σ) (ts : List σ)
    (ht : t ∉ ts) (d : σ →₀ ℕ) (r : ℕ) :
    centralRaisingPositionWord shape (t :: ts) d t r =
      (4, r + d t) :: shapedModes shape ts d := by
  simp only [centralRaisingPositionWord, shapedModes, List.map_cons]
  congr 1
  · simp [Function.update, Finsupp.single_apply]
  · apply List.map_congr_left
    intro i hi
    have hit : i ≠ t := by
      intro heq
      exact ht (heq ▸ hi)
    simp [Function.update, Finsupp.single_apply, hit]

theorem centralRaisingPositionWord_cons_other {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6) (t i : σ) (ts : List σ)
    (hti : t ≠ i) (d : σ →₀ ℕ) (r : ℕ) :
    centralRaisingPositionWord shape (t :: ts) d i r =
      (shape t, d t) :: centralRaisingPositionWord shape ts d i r := by
  simp [centralRaisingPositionWord, shapedModes, Function.update,
    Finsupp.single_apply, hti, hti.symm]

/-- The recursive replacement list is exactly the list of central positions.
    Keeping this as a list retains multiplicities of equal-mode words. -/
theorem centralRaisingWords_positions {σ : Type*}
    [DecidableEq σ] (shape : σ → Fin 6) (is : List σ)
    (his : is.Nodup) (d : σ →₀ ℕ) (r : ℕ) :
    centralRaisingWords r (shapedModes shape is d) =
      (is.filter fun t => shape t = 5).map
        (fun t => centralRaisingPositionWord shape is d t r) := by
  induction is with
  | nil => simp [centralRaisingWords, shapedModes]
  | cons t ts ih =>
      have ht : t ∉ ts := (List.nodup_cons.mp his).1
      have hts : ts.Nodup := (List.nodup_cons.mp his).2
      have ih' := ih hts
      change centralRaisingWords r (List.map (fun i => (shape i, d i)) ts) =
        (ts.filter fun i => shape i = 5).map
          (fun i => centralRaisingPositionWord shape ts d i r) at ih'
      by_cases ht1 : shape t = 5
      · simp only [shapedModes, List.map_cons, centralRaisingWords,
          ht1, if_true, List.singleton_append, List.filter_cons,
          List.map_cons, List.cons_append]
        rw [ih']
        simp only [List.nil_append, List.map_map,
          show decide True = true by decide, if_true]
        congr 1
        · exact (centralRaisingPositionWord_cons_self shape t ts ht d r).symm
        · apply List.map_congr_left
          intro i hi
          have hit : t ≠ i := by
            intro heq
            exact ht (heq ▸ (List.mem_filter.mp hi).1)
          simpa only [ht1, Function.comp_apply] using
            (centralRaisingPositionWord_cons_other shape t i ts hit d r).symm
      · simp only [shapedModes, List.map_cons, centralRaisingWords,
          ht1, if_false, List.filter_cons,
          List.nil_append]
        rw [ih']
        simp only [List.map_map,
          show decide False = false by decide, if_false]
        apply List.map_congr_left
        intro i hi
        have hit : t ≠ i := by
          intro heq
          exact ht (heq ▸ (List.mem_filter.mp hi).1)
        exact (centralRaisingPositionWord_cons_other shape t i ts hit d r).symm

/-- Sum of the words obtained by converting one central-labelled position. -/
noncomputable def centralRaisingPositionalEvaluation {σ : Type*} [Fintype σ]
    [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (r : ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] V :=
  modeWordEvaluation σ fun d =>
    ((Finset.univ.toList.filter fun t => shape t = 5).map
      fun t => radicalWord ρ w
        (centralRaisingPositionWord shape Finset.univ.toList d t r)).sum

/-- One selected term of the positional conversion sum is evaluation with
    that position recoloured and its mode shifted. -/
theorem centralRaisingPositionEvaluation_eq_shift
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (t : σ) (r : ℕ)
    (P : MvPolynomial σ ℂ) :
    modeWordEvaluation σ (fun d => radicalWord ρ w
        (centralRaisingPositionWord shape Finset.univ.toList d t r)) P =
      xyzEvaluation ρ w (Function.update shape t 4) (X t ^ r * P) := by
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
        centralRaisingPositionWord]
  | add P Q ihP ihQ =>
      simp only [map_add, mul_add, ihP, ihQ]

/-- The positional conversion is a sum of independently recoloured
    polynomial evaluations. -/
theorem centralRaisingPositionalEvaluation_eq_sum
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (r : ℕ)
    (P : MvPolynomial σ ℂ) :
    centralRaisingPositionalEvaluation ρ w shape r P =
      ((Finset.univ.toList.filter fun t => shape t = 5).map
        fun t => xyzEvaluation ρ w (Function.update shape t 4)
          (X t ^ r * P)).sum := by
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial σ ℂ) =
          z • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      have hterm (t : σ) :
          xyzEvaluation ρ w (Function.update shape t 4)
              (X t ^ r * (z • modeMonomial σ d)) =
            z • xyzEvaluation ρ w (Function.update shape t 4)
              (X t ^ r * modeMonomial σ d) := by
        rw [mul_smul_comm, map_smul]
      simp_rw [hterm]
      rw [map_smul]
      have hsum (L : List σ) :
          (L.map
            fun t => z • xyzEvaluation ρ w (Function.update shape t 4)
              (X t ^ r * modeMonomial σ d)).sum =
            z • (L.map
              fun t => xyzEvaluation ρ w (Function.update shape t 4)
                (X t ^ r * modeMonomial σ d)).sum := by
        induction L with
        | nil => simp
        | cons t ts ih =>
            simp only [List.map_cons, List.sum_cons, smul_add]
            rw [ih]
      rw [hsum]
      apply congrArg (z • ·)
      rw [centralRaisingPositionalEvaluation, modeWordEvaluation_monomial]
      congr 1
      apply List.map_congr_left
      intro t ht
      simpa only [modeWordEvaluation_monomial] using
        centralRaisingPositionEvaluation_eq_shift ρ w shape t r
          (modeMonomial σ d)
  | add P Q ihP ihQ =>
      rw [map_add]
      simp only [mul_add, map_add]
      rw [List.sum_map_add]
      exact congrArg₂ (· + ·) ihP ihQ

/-- Middle raising equals the positional recolouring evaluator at every mode polynomial. -/
theorem middleRaising_polynomial_positions {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (shape : σ → Fin 6) (hc : ∀ i, shape i = 1 ∨ shape i = 4 ∨ shape i = 5)
    (r : ℕ) (P : MvPolynomial σ ℂ) :
    ρ.op (leviColour (A3Sector.simpleE 1)) r (xyzEvaluation ρ w shape P) =
      centralRaisingPositionalEvaluation ρ w shape r P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have hm : (monomial d z : MvPolynomial σ ℂ) = z • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm, map_smul, map_smul, map_smul]
      congr 1
      simp only [xyzEvaluation, centralRaisingPositionalEvaluation, modeWordEvaluation_monomial]
      rw [middleRaising_word_sum ρ w m h]
      · rw [centralRaisingWords_positions shape _ (Finset.nodup_toList _)]
        simp only [List.map_map, Function.comp_def]
      · rintro t ht
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        exact hc i
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- Iterate positional conversion, keeping every central-slot choice with its multiplicity. -/
def centralRaisingIteratedEvaluation {σ : Type*} [Fintype σ] [DecidableEq σ] :
    List ℕ → (σ → Fin 6) → MvPolynomial σ ℂ → V
  | [], shape, P => xyzEvaluation ρ w shape P
  | r :: rs, shape, P =>
      ((Finset.univ.toList.filter fun t => shape t = 5).map fun t =>
        centralRaisingIteratedEvaluation rs (Function.update shape t 4) (X t ^ r * P)).sum

/-- Arbitrary raising words have an exact iterated positional conversion formula. -/
theorem middleRaising_polynomial_iterated {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (rs : List ℕ)
    (shape : σ → Fin 6) (hc : ∀ i, shape i = 1 ∨ shape i = 4 ∨ shape i = 5)
    (P : MvPolynomial σ ℂ) :
    middleRaisingProduct ρ rs.reverse (xyzEvaluation ρ w shape P) =
      centralRaisingIteratedEvaluation ρ w rs shape P := by
  induction rs generalizing shape P with
  | nil => simp [middleRaisingProduct, centralRaisingIteratedEvaluation]
  | cons r rs ih =>
      have he : middleRaisingProduct ρ (r :: rs).reverse =
          middleRaisingProduct ρ rs.reverse * ρ.op (leviColour (A3Sector.simpleE 1)) r := by
        simp [middleRaisingProduct, List.reverse_cons, List.map_append, List.prod_append]
      rw [he, Module.End.mul_apply, middleRaising_polynomial_positions ρ w m h shape hc,
        centralRaisingPositionalEvaluation_eq_sum, map_list_sum]
      simp only [centralRaisingIteratedEvaluation, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro t ht
      apply ih
      intro i
      by_cases hi : i = t
      · subst i; simp
      · simpa [Function.update_of_ne hi] using hc i

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaising_word_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingPositionWord_cons_self
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingPositionWord_cons_other
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingWords_positions
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingPositionEvaluation_eq_shift
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingPositionalEvaluation_eq_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaising_polynomial_positions

#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaising_polynomial_iterated
