import VOA.DeligneAudit.D4LeviKSPairRecolourStep

/-! Transposition symmetry collapses the positional Θ5 sum. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

/-- Swapping two positions of the same original colour transports a
    one-position recolouring from one to the other. -/
theorem pairUpdate_comp_swap {σ : Type*} [DecidableEq σ]
    (shape : σ → Fin 6) (s t : σ) (h : shape s = shape t) :
    Function.update shape t 3 ∘ Equiv.swap s t =
      Function.update shape s 3 := by
  funext x
  by_cases hs : x = s
  · subst x
    simp [Function.update, Equiv.swap_apply_left]
  by_cases ht : x = t
  · subst x
    have hst : s ≠ t := Ne.symm hs
    simp [Function.update, Equiv.swap_apply_right, hs, h, hst]
  · simp [Function.update, Equiv.swap_apply_of_ne_of_ne hs ht,
      hs, ht]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The next shape is a single function update at the first remaining
    paired X position. -/
theorem pairRecolourShape_succ_eq_update
    (a b c k : ℕ) (hk : k < b) :
    pairRecolourShape a b c (k + 1) =
      Function.update (pairRecolourShape a b c k)
        (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) 3 := by
  funext t
  rw [pairRecolourShape_step a b c k hk t]
  simp [Function.update]

/-- A transposition-invariant polynomial has equal converted summands. -/
theorem pairConvertedTerm_eq_of_swap
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (s t : σ) (hcolour : shape s = shape t)
    (r : ℕ) (P : MvPolynomial σ ℂ)
    (hsym : rename (Equiv.swap s t) P = P) :
    xyzEvaluation ρ w (Function.update shape t 3) (X t ^ r * P) =
      xyzEvaluation ρ w (Function.update shape s 3) (X s ^ r * P) := by
  let e := Equiv.swap s t
  have hrename : rename e (X s ^ r * P) = X t ^ r * P := by
    simp [e, hsym, Equiv.swap_apply_left]
  rw [← hrename]
  rw [xyzEvaluation_rename_equiv]
  rw [pairUpdate_comp_swap shape s t hcolour]

/-- At a symmetric X polynomial, every surviving Θ5 summand equals the
    converted summand at the first unpaired position. -/
theorem pairRecolour_adjoint_symmetric
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (hk : k < b)
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hsym : ∀ t : PairSource a b c,
      pairRecolourShape a b c k t = 1 →
        rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t) P = P) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRecolourOperator ρ a b c k P) w =
      -((Finset.univ.toList.filter fun t : PairSource a b c =>
          pairRecolourShape a b c k t = 1).length •
        xyzEvaluation ρ w
          (Function.update (pairRecolourShape a b c k)
            (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) 3)
          (X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ r * P)) := by
  let s : PairSource a b c := Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))
  let shape := pairRecolourShape a b c k
  have hs : shape s = 1 := by
    exact pairRecolourShape_unpaired_at a b c k ⟨k, hk⟩ (le_refl k)
  let C := xyzEvaluation ρ w (Function.update shape s 3) (X s ^ r * P)
  have hsum (L : List (PairSource a b c))
      (hL : ∀ t ∈ L, shape t = 1) :
      (L.map fun t => xyzEvaluation ρ w (Function.update shape t 3)
        (X t ^ r * P)).sum = L.length • C := by
    induction L with
    | nil => simp
    | cons t ts ih =>
        have ht : shape t = 1 := hL t (List.mem_cons_self)
        have hts : ∀ u ∈ ts, shape u = 1 := by
          intro u hu
          exact hL u (List.mem_cons_of_mem t hu)
        have hterm : xyzEvaluation ρ w (Function.update shape t 3)
            (X t ^ r * P) = C := by
          exact pairConvertedTerm_eq_of_swap ρ w shape s t
            (hs.trans ht.symm) r P (hsym t ht)
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          hterm, ih hts]
        simp [succ_nsmul, add_comm]
  rw [pairRecolour_adjoint_shift_sum]
  congr 1
  apply hsum
  intro t ht
  exact of_decide_eq_true (List.mem_filter.mp ht).2

/-- Operator form of the one-step symmetric conversion, ready to iterate. -/
theorem pairRecolour_adjoint_symmetric_op
    (ρ : CurrentModule D4sector.f V)
    (a b c k r : ℕ) (hk : k < b)
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hsym : ∀ t : PairSource a b c,
      pairRecolourShape a b c k t = 1 →
        rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t) P = P) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRecolourOperator ρ a b c k P) =
      -((Finset.univ.toList.filter fun t : PairSource a b c =>
          pairRecolourShape a b c k t = 1).length •
        pairRecolourOperator ρ a b c (k + 1)
          (X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ r * P)) := by
  apply LinearMap.ext
  intro w
  simp only [LinearMap.neg_apply]
  rw [pairRecolour_adjoint_symmetric ρ w a b c k r hk P hsym]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  congr 1
  rw [pairRecolourOperator_apply]
  simp only [pairRecolourEvaluation,
    pairRecolourShape_succ_eq_update a b c k hk]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairUpdate_comp_swap
#print axioms VOA.DeligneAudit.D4Levi.pairRecolourShape_succ_eq_update
#print axioms VOA.DeligneAudit.D4Levi.pairConvertedTerm_eq_of_swap
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_symmetric
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_symmetric_op
