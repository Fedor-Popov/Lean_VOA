import VOA.Huang.GenusOneG1WardAbstract

/-!
# Kernels rational in `t` with poles only at `t = 1`

Step 2 of the iterate-transport argument.

`RatRows E c d f`: for every outer level `p`, the `u^p`-row of `f ∈ ℂ⟦u⟧⟦t⟧`,
multiplied by `(1 − t)^E`, is a polynomial in `t` of degree `≤ c p + d`.
`RatSub` is the subalgebra of `Sub2` series with this property for SOME `E c d`.
It contains the genus-one kernels: `eis j` (each row is a monomial `t^p`) and
`piK m` (rows `p ≥ 1` are polynomials of degree `≤ 2p`; row `0` is
`Σ_{k ≥ 1} k^m t^k / m!`, which times `(1 − t)^{m+1}` is a polynomial of degree
`≤ m + 1` — the Eulerian-polynomial identity, proved with the Euler operator
`t d/dt`).
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open scoped BigOperators

/-- Polynomials as power series (a ring hom, so `map_*` lemmas apply). -/
abbrev pc : Polynomial ℂ →+* PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom

theorem coeff_pc (P : Polynomial ℂ) (k : ℕ) : PowerSeries.coeff k (pc P) = P.coeff k := by
  simp [pc, Polynomial.coeff_coe]

/-- `1 − t` as a power series. -/
abbrev omt : PowerSeries ℂ := 1 - PowerSeries.X

theorem pc_omt : pc (1 - Polynomial.X) = omt := by
  simp [pc, omt]

/-- Row `p` of `f`, times `(1 − t)^E`, is a polynomial of degree `≤ c p + d`. -/
def RatRows (E c d : ℕ) (f : R2) : Prop :=
  ∀ p : ℕ, ∃ P : Polynomial ℂ, P.natDegree ≤ c * p + d ∧
    omt ^ E * PowerSeries.coeff p f = pc P

theorem RatRows.mono {E c d c' d' : ℕ} {f : R2} (h : RatRows E c d f) (hc : c ≤ c')
    (hd : d ≤ d') : RatRows E c' d' f := fun p => by
  obtain ⟨P, hP, he⟩ := h p
  exact ⟨P, hP.trans (by nlinarith), he⟩

theorem natDegree_omt_pow_le (e : ℕ) : ((1 - Polynomial.X : Polynomial ℂ) ^ e).natDegree ≤ e := by
  refine (Polynomial.natDegree_pow_le).trans ?_
  have : (1 - Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp
  nlinarith

theorem RatRows.raise {E c d : ℕ} {f : R2} (h : RatRows E c d f) (e : ℕ) :
    RatRows (E + e) c (d + e) f := fun p => by
  obtain ⟨P, hP, he⟩ := h p
  refine ⟨(1 - Polynomial.X) ^ e * P, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := natDegree_omt_pow_le e
    omega
  · rw [map_mul, map_pow, pc_omt, ← he, pow_add]
    ring

theorem RatRows.add {E₁ c₁ d₁ E₂ c₂ d₂ : ℕ} {f g : R2} (hf : RatRows E₁ c₁ d₁ f)
    (hg : RatRows E₂ c₂ d₂ g) :
    RatRows (E₁ + E₂) (max c₁ c₂) (d₁ + d₂ + E₁ + E₂) (f + g) := fun p => by
  obtain ⟨P, hP, he⟩ := hf.raise E₂ p
  obtain ⟨Q, hQ, hq⟩ := hg.raise E₁ p
  refine ⟨P + Q, ?_, ?_⟩
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine hP.trans ?_
      have : c₁ * p ≤ max c₁ c₂ * p := Nat.mul_le_mul_right _ (le_max_left _ _)
      omega
    · refine hQ.trans ?_
      have : c₂ * p ≤ max c₁ c₂ * p := Nat.mul_le_mul_right _ (le_max_right _ _)
      omega
  · rw [show pc (P + Q) = pc P + pc Q from map_add pc P Q, ← he, ← hq, map_add,
      add_comm E₂ E₁]
    ring

theorem RatRows.mul {E₁ c₁ d₁ E₂ c₂ d₂ : ℕ} {f g : R2} (hf : RatRows E₁ c₁ d₁ f)
    (hg : RatRows E₂ c₂ d₂ g) :
    RatRows (E₁ + E₂) (max c₁ c₂) (d₁ + d₂) (f * g) := fun p => by
  classical
  choose P hP he using hf
  choose Q hQ hq using hg
  refine ⟨∑ x ∈ Finset.antidiagonal p, P x.1 * Q x.2, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h1 := hP x.1
    have h2 := hQ x.2
    have h3 : c₁ * x.1 ≤ max c₁ c₂ * x.1 := Nat.mul_le_mul_right _ (le_max_left _ _)
    have h4 : c₂ * x.2 ≤ max c₁ c₂ * x.2 := Nat.mul_le_mul_right _ (le_max_right _ _)
    have h5 : max c₁ c₂ * x.1 + max c₁ c₂ * x.2 = max c₁ c₂ * p := by
      rw [← Nat.mul_add, hx]
    omega
  · rw [PowerSeries.coeff_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, ← he, ← hq, pow_add]
    ring

theorem ratRows_algebraMap (a : ℂ) : RatRows 0 0 0 (algebraMap ℂ R2 a) := fun p => by
  refine ⟨if p = 0 then Polynomial.C a else 0, ?_, ?_⟩
  · split_ifs <;> simp
  · rw [pow_zero, one_mul]
    ext k
    rw [coeff_pc]
    change c2 (algebraMap ℂ R2 a) p k = _
    rw [c2_algebraMap]
    by_cases hp : p = 0
    · subst hp
      simp only [true_and, if_true, Polynomial.coeff_C]
    · simp [hp]

/-- The subalgebra of `Sub2` kernels whose rows are rational in `t` with poles only at
`t = 1`, of uniformly bounded pole order and linearly growing numerator degree. -/
def RatSub : Subalgebra ℂ R2 where
  carrier := {f | f ∈ Sub2 ∧ ∃ E c d, RatRows E c d f}
  mul_mem' := by
    rintro f g ⟨hf, E₁, c₁, d₁, hf'⟩ ⟨hg, E₂, c₂, d₂, hg'⟩
    exact ⟨Sub2.mul_mem hf hg, _, _, _, hf'.mul hg'⟩
  add_mem' := by
    rintro f g ⟨hf, E₁, c₁, d₁, hf'⟩ ⟨hg, E₂, c₂, d₂, hg'⟩
    exact ⟨Sub2.add_mem hf hg, _, _, _, hf'.add hg'⟩
  algebraMap_mem' := fun a => ⟨Sub2.algebraMap_mem a, 0, 0, 0, ratRows_algebraMap a⟩

theorem mem_RatSub {f : R2} : f ∈ RatSub ↔ f ∈ Sub2 ∧ ∃ E c d, RatRows E c d f := Iff.rfl

theorem RatSub_le_Sub2 : RatSub ≤ Sub2 := fun _ h => h.1

/-! ## The Eisenstein kernels -/

theorem eis_mem_RatSub (j : ℕ) : eis j ∈ RatSub := by
  refine ⟨eis_mem_Sub2 j, 0, 1, 0, fun p => ?_⟩
  refine ⟨Polynomial.monomial p (VOA.zhuG j p), ?_, ?_⟩
  · refine (Polynomial.natDegree_monomial_le _).trans ?_
    omega
  · rw [pow_zero, one_mul]
    ext k
    rw [coeff_pc, Polynomial.coeff_monomial]
    change c2 (eis j) p k = _
    simp only [eis, c2_mk2]

/-! ## The spatial kernels -/

/-- A power series with vanishing coefficients above `B` is a polynomial of degree `≤ B`. -/
theorem exists_poly_of_vanish {F : PowerSeries ℂ} {B : ℕ}
    (h : ∀ k, B < k → PowerSeries.coeff k F = 0) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ B ∧ F = pc P := by
  refine ⟨PowerSeries.trunc (B + 1) F, ?_, ?_⟩
  · have := PowerSeries.natDegree_trunc_lt F B
    omega
  · ext k
    rw [coeff_pc, PowerSeries.coeff_trunc]
    split_ifs with hk
    · rfl
    · exact h k (by omega)

/-- `Σ_{k ≥ 1} k^m t^k`. -/
def powSer (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => if k = 0 then 0 else ((k : ℂ)) ^ m

theorem powSer_succ (m : ℕ) :
    powSer (m + 1) = PowerSeries.X * PowerSeries.derivative ℂ (powSer m) := by
  ext k
  cases k with
  | zero => simp [powSer]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [powSer, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false]
    push_cast
    ring

theorem one_sub_X_mul_powSer_zero : omt * powSer 0 = PowerSeries.X := by
  ext k
  rw [omt, sub_mul, one_mul, map_sub]
  cases k with
  | zero => simp [powSer]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X]
    simp only [powSer, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false, pow_zero]
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]

/-- The Eulerian identity: `(1 − t)^{m+1} Σ_{k≥1} k^m t^k` is a polynomial of degree
`≤ m + 1`. -/
theorem eulerian (m : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m + 1 ∧ omt ^ (m + 1) * powSer m = pc P := by
  induction m with
  | zero =>
    refine ⟨Polynomial.X, by simp, ?_⟩
    rw [zero_add, pow_one, one_sub_X_mul_powSer_zero]
    simp [pc]
  | succ m ih =>
    obtain ⟨P, hP, he⟩ := ih
    refine ⟨(1 - Polynomial.X) * Polynomial.X * Polynomial.derivative P +
      ((m + 1 : ℕ) : Polynomial ℂ) * Polynomial.X * P, ?_, ?_⟩
    · have hd := Polynomial.natDegree_derivative_le P
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h1 : ((1 - Polynomial.X : Polynomial ℂ) * Polynomial.X).natDegree ≤ 2 := by
          refine (Polynomial.natDegree_mul_le).trans ?_
          have := natDegree_omt_pow_le 1
          rw [pow_one] at this
          have h2 : (Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := Polynomial.natDegree_X_le
          omega
        omega
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h1 : (((m + 1 : ℕ) : Polynomial ℂ) * Polynomial.X).natDegree ≤ 1 := by
          refine (Polynomial.natDegree_mul_le).trans ?_
          rw [Polynomial.natDegree_natCast]
          have h2 : (Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := Polynomial.natDegree_X_le
          omega
        omega
    · -- apply the derivation to `(1 - t)^{m+1} powSer m = P`
      have hD := congrArg (PowerSeries.derivative ℂ) he
      rw [Derivation.leibniz, Derivation.leibniz_pow] at hD
      have hX : PowerSeries.derivative ℂ omt = -1 := by
        simp [omt]
      rw [hX] at hD
      have hP' : PowerSeries.derivative ℂ (pc P) = pc (Polynomial.derivative P) := by
        simp only [pc, Polynomial.coeToPowerSeries.ringHom_apply]
        exact PowerSeries.derivative_coe P
      rw [hP'] at hD
      rw [powSer_succ]
      simp only [map_add, map_mul, map_sub, map_one, map_natCast, pc_omt, ← he]
      have hpc : pc (1 - Polynomial.X) = omt := pc_omt
      simp only [map_sub, map_one] at hpc
      have hXp : pc Polynomial.X = PowerSeries.X := by simp [pc]
      rw [hXp]
      simp only [smul_eq_mul, nsmul_eq_mul] at hD
      rw [show m + 1 - 1 = m by omega] at hD
      rw [← hD]
      push_cast
      ring

theorem row_piK_zero (m : ℕ) :
    PowerSeries.coeff 0 (piK m) = ((m.factorial : ℂ)⁻¹) • powSer m := by
  ext k
  change c2 (piK m) 0 k = _
  rw [c2_piK, PowerSeries.coeff_smul]
  simp only [powSer, PowerSeries.coeff_mk, Nat.dvd_zero, and_true, not_lt_zero', false_and,
    if_false, sub_zero, Nat.sub_zero, smul_eq_mul]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_pos (Nat.pos_of_ne_zero hk), if_neg hk, div_eq_inv_mul]

theorem row_piK_vanish (m : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ∀ k, 2 * p < k → PowerSeries.coeff k (PowerSeries.coeff p (piK m)) = 0 := by
  intro k hk
  change c2 (piK m) p k = 0
  rw [c2_piK]
  rw [if_neg, if_neg]
  · simp
  · omega
  · rintro ⟨_, hd⟩
    have := Nat.le_of_dvd (by omega) hd
    omega

theorem piK_mem_RatSub (m : ℕ) : piK m ∈ RatSub := by
  refine ⟨piK_mem_Sub2 m, m + 1, 2, m + 1, fun p => ?_⟩
  by_cases hp : p = 0
  · subst hp
    obtain ⟨P, hP, he⟩ := eulerian m
    refine ⟨Polynomial.C ((m.factorial : ℂ)⁻¹) * P, ?_, ?_⟩
    · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      omega
    · rw [row_piK_zero, mul_smul_comm, he, map_mul, PowerSeries.smul_eq_C_mul]
      simp [pc]
  · obtain ⟨P, hP, he⟩ := exists_poly_of_vanish (row_piK_vanish m (p := p) (by omega))
    refine ⟨(1 - Polynomial.X) ^ (m + 1) * P, ?_, ?_⟩
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have := natDegree_omt_pow_le (m + 1)
      omega
    · rw [he, map_mul, map_pow, pc_omt]

end VOA.Huang.GenusOneWard
