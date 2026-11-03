import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarCert
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCompiler
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishing

/-! Whole-current transfer of every valid static C-color certificate into the
literal quadratic/cubic polar ideal J, at the static coefficient 2m-3 and for
all m. Quadratic and cubic factors use their genuine J tails; a single color
factor has no coefficient at or past the mode cutoff m. The integer multiplier
is cancelled over Complex only after its validity check proves it nonzero.
Contact-word coverage and quotient counts are separate. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
open VOA.DeligneAudit.D4FusionContact.Polynomial
open QuarticReducedRows QuarticReduced
noncomputable section

/-- The actual polynomial of a generator, in un-divided cube orbits. -/
def Gen.poly : Gen → P8 ℂ
  | .qq a1 b1 c1 a2 b2 c2 => orbit ℂ 2 a1 b1 c1 * orbit ℂ 2 a2 b2 c2
  | .qc a1 b1 c1 a2 b2 c2 => orbit ℂ 2 a1 b1 c1 * orbit ℂ 3 a2 b2 c2
  | .lc i a2 b2 c2 => MvPolynomial.X i * orbit ℂ 3 a2 b2 c2

theorem Gen.row_eval (g : Gen) :
    eval (MvPolynomial.X : Fin 8 → P8 ℂ) g.row = g.poly := by
  cases g <;> simp [Gen.row,Gen.poly,eval_mul,orbitRow_eval,wordEval]

/-- One color has no current coefficient at or past the mode cutoff. -/
theorem actualCurrent_coeff_high (m k : ℕ) (i : Fin 8) (hk : m ≤ k) :
    PowerSeries.coeff k (actualCurrent m i) = 0 := by
  simp [actualCurrent_coeff,actualMode,modeX,show ¬ k < m by omega]

/-- Every generator's whole static coefficient lies in the literal ideal J. -/
theorem Gen.coeff_mem (m : ℕ) (g : Gen) :
    PowerSeries.coeff (2 * m - 3) (currentMap m g.poly) ∈
      quadraticCubicPolarIdeal m := by
  cases g with
  | qq a1 b1 c1 a2 b2 c2 =>
      simpa only [Gen.poly,map_mul,jetDerivative_zero] using
        coeff_jet_product_mem (quadraticCubicPolarIdeal m)
          (currentMap m (orbit ℂ 2 a1 b1 c1)) (currentMap m (orbit ℂ 2 a2 b2 c2))
          2 2 m 0 0 (2 * m - 3)
          (fun k hk => quadraticCubicPolar_coeff_mem m 2 a1 b1 c1 k (Or.inl rfl) hk)
          (fun k hk => quadraticCubicPolar_coeff_mem m 2 a2 b2 c2 k (Or.inl rfl) hk)
          (by omega)
  | qc a1 b1 c1 a2 b2 c2 =>
      simpa only [Gen.poly,map_mul,jetDerivative_zero] using
        coeff_jet_product_mem (quadraticCubicPolarIdeal m)
          (currentMap m (orbit ℂ 2 a1 b1 c1)) (currentMap m (orbit ℂ 3 a2 b2 c2))
          2 3 m 0 0 (2 * m - 3)
          (fun k hk => quadraticCubicPolar_coeff_mem m 2 a1 b1 c1 k (Or.inl rfl) hk)
          (fun k hk => quadraticCubicPolar_coeff_mem m 3 a2 b2 c2 k (Or.inr rfl) hk)
          (by omega)
  | lc i a2 b2 c2 =>
      simpa only [Gen.poly,map_mul,currentMap_X,jetDerivative_zero] using
        coeff_jet_product_mem (quadraticCubicPolarIdeal m)
          (actualCurrent m i) (currentMap m (orbit ℂ 3 a2 b2 c2))
          1 3 m 0 0 (2 * m - 3)
          (fun k hk => by
            rw [actualCurrent_coeff_high m k i (by omega)]
            exact zero_mem _)
          (fun k hk => quadraticCubicPolar_coeff_mem m 3 a2 b2 c2 k (Or.inr rfl) hk)
          (by omega)

theorem currentMap_wordEval (m : ℕ) (w : List (Fin 8)) :
    currentMap m (wordEval (MvPolynomial.X : Fin 8 → P8 ℂ) w) =
      (w.map (actualCurrent m)).prod := by
  simp only [wordEval,map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp

/-- A valid certificate puts the whole signed static word coefficient in J. -/
theorem Cert.actual_coeff_mem (C : Cert) (hC : C.valid) (m : ℕ) :
    PowerSeries.coeff (2 * m - 3) ((C.target.map (actualCurrent m)).prod) ∈
      quadraticCubicPolarIdeal m := by
  have hpoly := C.eval_identity (MvPolynomial.X : Fin 8 → P8 ℂ) hC.1
  simp only [Gen.row_eval] at hpoly
  have hcur := congrArg (fun p => PowerSeries.coeff (2 * m - 3) (currentMap m p)) hpoly
  simp only [map_zsmul,currentMap_wordEval,map_list_sum,List.map_map] at hcur
  have hm : C.mult • PowerSeries.coeff (2 * m - 3) ((C.target.map (actualCurrent m)).prod) ∈
      quadraticCubicPolarIdeal m := by
    rw [hcur]
    apply list_sum_mem
    intro x hx
    obtain ⟨t,-,rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp,map_zsmul]
    exact Submodule.smul_of_tower_mem _ t.1 (Gen.coeff_mem m t.2)
  have hc : ((C.mult : ℤ) : ℂ) • PowerSeries.coeff (2 * m - 3)
        ((C.target.map (actualCurrent m)).prod) ∈
      (quadraticCubicPolarIdeal m).restrictScalars ℂ := by
    simpa only [Int.cast_smul_eq_zsmul ℂ] using hm
  exact (Submodule.smul_mem_iff ((quadraticCubicPolarIdeal m).restrictScalars ℂ)
    (Int.cast_ne_zero.mpr hC.2)).mp hc

theorem cubeSign_ne_zero : ∀ i : Fin 8, cubeSign i ≠ 0 := by decide

/-- Signed normalized words are nonzero multiples of the original words. -/
theorem actual_word_prod (m : ℕ) (w : List (Fin 8)) :
    (w.map (actualCurrent m)).prod =
      (w.map fun i => (cubeSign i : ℂ)).prod •
        (w.map fun i => AllM.current m (cubeColor i)).prod := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [List.map_cons,List.prod_cons,ih,actualCurrent,smul_mul_smul_comm]

theorem sign_prod_ne_zero (w : List (Fin 8)) :
    (w.map fun i => (cubeSign i : ℂ)).prod ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [List.map_cons,List.prod_cons]
      exact mul_ne_zero (Int.cast_ne_zero.mpr (cubeSign_ne_zero i)) ih

/-- The original unsigned whole-current word of a valid certificate lies in J. -/
theorem Cert.original_coeff_mem (C : Cert) (hC : C.valid) (m : ℕ) :
    PowerSeries.coeff (2 * m - 3)
        ((C.target.map fun i => AllM.current m (cubeColor i)).prod) ∈
      quadraticCubicPolarIdeal m := by
  have h := C.actual_coeff_mem hC m
  rw [actual_word_prod,PowerSeries.coeff_smul] at h
  exact (Submodule.smul_mem_iff ((quadraticCubicPolarIdeal m).restrictScalars ℂ)
    (sign_prod_ne_zero C.target)).mp h

end
#print axioms Gen.coeff_mem
#print axioms Cert.actual_coeff_mem
#print axioms Cert.original_coeff_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
