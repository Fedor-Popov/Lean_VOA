import VOA.DeligneAudit.D4CharRogersGT

/-! Linearity over all four z coordinates, needed when taking theta moments of mixed Cauchy. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter

noncomputable section

/-- Multipliers which can be pulled out of the normalized theta functional. -/
def rsSpectator (g : D4K.R) : Prop := ∀ f, rsMoment (g * f) = g * rsMoment f

/-- Any Laurent monomial independent of x is a spectator. -/
theorem rsSpectator_mon (v : D4K.V) (hv : v 0 = 0) (c : D4K.Kq) :
    rsSpectator (D4K.mon v c) := by
  have h : D4K.ctTheta ∘ₗ LinearMap.mulLeft D4K.Kq (D4K.mon v c) =
      LinearMap.mulLeft D4K.Kq (D4K.mon v c) ∘ₗ D4K.ctTheta := by
    apply Finsupp.lhom_ext
    intro w d
    change D4K.ctTheta (D4K.mon v c * D4K.mon w d) =
      D4K.mon v c * D4K.ctTheta (D4K.mon w d)
    rw [D4K.mon_mul_mon, D4K.ctFun_mon, D4K.ctFun_mon, D4K.mon_mul_mon]
    have hk : D4K.killX (v + w) = v + D4K.killX w := by
      ext i
      by_cases hi : i = 0
      · subst i; simp [D4K.killX, hv]
      · simp [D4K.killX, Function.update, hi]
    rw [hk]
    simp only [Pi.add_apply, hv, zero_add, mul_assoc]
  intro f
  have he := LinearMap.congr_fun h f
  change D4K.ctTheta (D4K.mon v c * f) = D4K.mon v c * D4K.ctTheta f at he
  simp only [rsMoment, LinearMap.smul_apply, he, mul_smul_comm]

theorem rsSpectator_coeff (c : D4K.Kq) : rsSpectator (rsCoeff c) := by
  rw [← rsMon_zero]
  exact rsSpectator_mon 0 rfl c

theorem rsSpectator_mul {f g : D4K.R} (hf : rsSpectator f) (hg : rsSpectator g) :
    rsSpectator (f * g) := by
  intro h
  rw [mul_assoc, hf, hg, mul_assoc]

theorem rsSpectator_sum {ι : Type*} (s : Finset ι) (f : ι → D4K.R)
    (hf : ∀ i ∈ s, rsSpectator (f i)) : rsSpectator (∑ i ∈ s, f i) := by
  intro g
  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i hi => hf i hi g)

/-- All GT polynomials in x-free Laurent alphabets are spectators, at every rank. -/
theorem rsSpectator_gtEval (v : ℕ → D4K.V) (hv : ∀ i, v i 0 = 0)
    (N : ℕ) (lam : Fin N → ℤ) :
    rsSpectator (gtEval rsNome (fun i => rsMonUnit (v i)) N lam) := by
  induction N with
  | zero =>
      change rsSpectator 1
      intro f
      simp
  | succ N ih =>
      rw [gtEval]
      apply rsSpectator_sum
      intro μ _
      apply rsSpectator_mul _ (ih μ)
      apply rsSpectator_mul
      · have hp : gtPsi rsNome lam μ = rsCoeff (gtPsi D4K.qq lam μ) := by
          simp only [gtPsi, rsNome, map_prod, A2.map_qbinom]
        rw [hp]
        exact rsSpectator_coeff _
      · rw [rsMonUnit_zpow]
        apply rsSpectator_mon
        simp [hv]

/-- The four physical z coordinates, with harmless zero vectors beyond rank four. -/
def rsZVector (i : ℕ) : D4K.V := fun j => if j.val = i + 1 then 1 else 0

def rsZAlphabet (i : ℕ) : D4K.Rˣ := rsMonUnit (rsZVector i)

theorem rsZVector_zero (i : ℕ) : rsZVector i 0 = 0 := by simp [rsZVector]

theorem rsZVector_eq (i : Fin 4) : rsZVector i = D4K.zv i := by
  ext j
  simp only [rsZVector, D4K.zv, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    exact Fin.ext h
  · intro h
    subst j
    rfl

/-- Every ambient GL_4 GT factor can be pulled through the actual theta functional. -/
theorem rsMoment_gtEval_mul (lam : Fin 4 → ℤ) (f : D4K.R) :
    rsMoment (gtEval rsNome rsZAlphabet 4 lam * f) =
      gtEval rsNome rsZAlphabet 4 lam * rsMoment f :=
  rsSpectator_gtEval rsZVector rsZVector_zero 4 lam f

/-- Each term of mixed Cauchy collapses to equal positive and negative row gaps. -/
theorem rsMoment_mixed_term (a b c d : ℕ) (hab : b ≤ a) (hcd : d ≤ c) :
    rsMoment (gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(a : ℤ), (b : ℤ)] *
      gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(c : ℤ), (d : ℤ)] *
        gtEval rsNome rsZAlphabet 4 (gtMixedFourRow a b c d)) =
      if a - b = c - d then
        ((D4K.qpoch (a - b))⁻¹ * (D4K.qpoch b)⁻¹ * (D4K.qpoch d)⁻¹) •
          gtEval rsNome rsZAlphabet 4 (gtMixedFourRow a b c d)
      else 0 := by
  rw [mul_comm _ (gtEval _ _ _ _), rsMoment_gtEval_mul, rsMoment_Q_mul a b c d hab hcd]
  split_ifs
  · rw [mul_smul_comm, mul_one]
  · exact mul_zero _

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsSpectator_mon
#print axioms VOA.DeligneAudit.D4Char.rsSpectator_coeff
#print axioms VOA.DeligneAudit.D4Char.rsSpectator_mul
#print axioms VOA.DeligneAudit.D4Char.rsSpectator_sum
#print axioms VOA.DeligneAudit.D4Char.rsSpectator_gtEval
#print axioms VOA.DeligneAudit.D4Char.rsZVector_zero
#print axioms VOA.DeligneAudit.D4Char.rsZVector_eq
#print axioms VOA.DeligneAudit.D4Char.rsMoment_gtEval_mul
#print axioms VOA.DeligneAudit.D4Char.rsMoment_mixed_term
