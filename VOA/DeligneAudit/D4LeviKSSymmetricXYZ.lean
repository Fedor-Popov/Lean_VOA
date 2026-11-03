import VOA.DeligneAudit.D4LeviKSSymmetricIntertwine
import VOA.DeligneAudit.D4LeviKSSymmetricWordShift

/-! Positional mode shifts on a fixed shape of XYZ radical words. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def shapedModes {σ : Type*} (shape : σ → Fin 6)
    (is : List σ) (a : σ →₀ ℕ) : List (Fin 6 × ℕ) :=
  is.map fun i => (shape i, a i)

/-- The recursive colour shift equals the sum of shifts at labelled positions. -/
theorem colourPowerShift_shapedModes {σ : Type*}
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (is : List σ) (his : is.Nodup)
    (a : σ →₀ ℕ) (j : Fin 6) (r : ℕ) :
    colourPowerShift ρ w j r (shapedModes shape is a) =
      (is.map fun i => if shape i = j then
        radicalWord ρ w (shapedModes shape is (Finsupp.single i r + a))
        else 0).sum := by
  classical
  induction is with
  | nil => simp [shapedModes, colourPowerShift]
  | cons t ts ih =>
      have ht : t ∉ ts := (List.nodup_cons.mp his).1
      have hts : ts.Nodup := (List.nodup_cons.mp his).2
      have htail (i : σ) (hi : i ∈ ts) :
          (Finsupp.single i r + a) t = a t := by
        have hit : i ≠ t := by
          intro heq
          exact ht (heq ▸ hi)
        simp [hit]
      have htail_t : shapedModes shape ts (Finsupp.single t r + a) =
          shapedModes shape ts a := by
        simp only [shapedModes]
        apply List.map_congr_left
        intro i hi
        have hit : t ≠ i := by
          intro heq
          exact ht (heq ▸ hi)
        simp [hit]
      have ih' :
          colourPowerShift ρ w j r (List.map (fun i => (shape i, a i)) ts) =
            (ts.map fun i => if shape i = j then
              radicalWord ρ w
                (List.map (fun t => (shape t, (Finsupp.single i r + a) t)) ts)
              else 0).sum := by
        simpa only [shapedModes] using ih hts
      simp only [shapedModes, List.map_cons, colourPowerShift,
        List.sum_cons]
      by_cases hj : shape t = j
      · simp only [hj, if_true]
        congr 1
        · congr 1
          simp only [List.cons.injEq]
          constructor
          · simp
          · simpa only [shapedModes] using htail_t.symm
        · rw [ih', map_list_sum]
          simp only [List.map_map, Function.comp_def]
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases hij : shape i = j
          · simp only [hij, if_true]
            rw [← htail i hi]
            simp [radicalWord, wordOp]
          · simp [hij]
      · simp only [hj, if_false, zero_add]
        rw [ih', map_list_sum]
        simp only [List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hij : shape i = j
        · simp only [hij, if_true]
          rw [← htail i hi]
          simp [radicalWord, wordOp]
        · simp [hij]

/-- A power sum over one colour in a fixed XYZ word shape. -/
noncomputable def colourPsum {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (j : Fin 6) (r : ℕ) : MvPolynomial σ ℂ :=
  (Finset.univ.toList.map fun i => if shape i = j then X i ^ r else 0).sum

theorem symmetricShiftAction_colourPsum {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (j : Fin 6) (r : ℕ) (a : σ →₀ ℕ) :
    symmetricShiftAction σ (colourPsum shape j r) (modeMonomial σ a) =
      (Finset.univ.toList.map fun i => if shape i = j then
        modeMonomial σ (Finsupp.single i r + a) else 0).sum := by
  classical
  simp [symmetricShiftAction_apply, colourPsum, modeMonomial,
    X_pow_eq_monomial, monomial_mul]

/-- Evaluation of a fixed-shape XYZ word with labelled mode positions. -/
noncomputable def xyzEvaluation {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) : MvPolynomial σ ℂ →ₗ[ℂ] V :=
  modeWordEvaluation σ fun a =>
    radicalWord ρ w (shapedModes shape Finset.univ.toList a)

/-- A selective Cartan current intertwines the corresponding positional
    power sum on every fixed-shape XYZ word combination. -/
theorem xyzEvaluation_psum_intertwine {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (shape : σ → Fin 6)
    (hshape : ∀ i, shape i = 1 ∨ shape i = 4 ∨ shape i = 5)
    (j : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (r : ℕ) (hr : 0 < r) (W : MvPolynomial σ ℂ) :
    selectiveCartan ρ (if j = 1 then 0 else if j = 4 then 1 else 2) r
        (xyzEvaluation ρ w shape W) =
      (if j = 5 then (1 : ℂ) else 2) •
        xyzEvaluation ρ w shape
          (symmetricShiftAction σ (colourPsum shape j r) W) := by
  classical
  induction W using MvPolynomial.induction_on' with
  | monomial a t =>
      have hm : (monomial a t : MvPolynomial σ ℂ) =
          t • modeMonomial σ a := by
        simp only [modeMonomial, smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul, map_smul]
      have hls : ∀ p ∈ shapedModes shape Finset.univ.toList a,
          p.1 = 1 ∨ p.1 = 4 ∨ p.1 = 5 := by
        intro p hp
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
        exact hshape i
      have hc := selective_cartan_xyz_power_shift ρ w m h r hr
        (shapedModes shape Finset.univ.toList a) hls
      have hs := colourPowerShift_shapedModes ρ w shape
        Finset.univ.toList (Finset.nodup_toList _) a j r
      have heval : xyzEvaluation ρ w shape
          (symmetricShiftAction σ (colourPsum shape j r) (modeMonomial σ a)) =
          colourPowerShift ρ w j r (shapedModes shape Finset.univ.toList a) := by
        rw [symmetricShiftAction_colourPsum]
        rw [map_list_sum]
        simp only [List.map_map, Function.comp_def]
        rw [hs]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hij : shape i = j
        · simp [hij, xyzEvaluation, modeWordEvaluation_monomial]
        · simp [hij]
      have hbase : xyzEvaluation ρ w shape (modeMonomial σ a) =
          radicalWord ρ w (shapedModes shape Finset.univ.toList a) := by
        exact modeWordEvaluation_monomial σ _ a
      rcases hj with rfl | rfl | rfl
      · simp only [map_smul]
        rw [hbase, heval]
        simp only [selectiveCartan, ↓reduceIte]
        rw [hc.1]
        exact smul_comm t (2 : ℂ) _
      · simp only [map_smul]
        rw [hbase, heval]
        simp only [selectiveCartan, show (4 : Fin 6) ≠ 1 by decide,
          show (1 : Fin 3) ≠ 0 by decide, show (4 : Fin 6) ≠ 5 by decide,
          ↓reduceIte]
        rw [hc.2.1]
        exact smul_comm t (2 : ℂ) _
      · simp only [map_smul]
        rw [hbase, heval]
        simpa [selectiveCartan] using congrArg (t • ·) hc.2.2
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, smul_add]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.colourPowerShift_shapedModes
#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_colourPsum
#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_psum_intertwine
