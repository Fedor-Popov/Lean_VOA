import VOA.Huang.DLNSmallCover
import VOA.Huang.DLNSmallThreeMatrices
import VOA.Huang.DLNSchurTwo

/-!
# Two-power inflation from a multiplier bound

Let `B = SL₂(ℤ/2^{a+1})`, `A = SL₂(ℤ/2^a)`, `a ≥ 2`, `q = 2^a`, `N = ker(B → A) = {1 + q W}`.
The functional `φ(n) = n₀₀ - 1 + n₀₁ + n₁₀` is additive on `N` and conjugation invariant, so
`V = ker φ ∩ N` is normal and `C = B/V` is a central extension of `A` by `ℤ/2`. The scalar
`ε = diag(1-q, 1+q) = ⁅y(2), x(2^{a-1})⁆` is a commutator with `φ ε = q ≠ 0`, so `C` is a
stem cover. By `inflationTrivial_of_cover`, the bound `MultAtMostTwo A` gives trivial
inflation `B → A`.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

section TwoArith

variable {a : ℕ}

theorem two_pow_succ_eq_zero (a : ℕ) : (2 : ZMod (2 ^ (a + 1))) ^ (a + 1) = 0 := by
  have : ((2 ^ (a + 1) : ℕ) : ZMod (2 ^ (a + 1))) = 0 := ZMod.natCast_self _
  exact_mod_cast this

theorem two_mul_two_pow (a : ℕ) : (2 : ZMod (2 ^ (a + 1))) * 2 ^ a = 0 := by
  rw [← pow_succ']; exact two_pow_succ_eq_zero a

theorem two_pow_mul_self {a : ℕ} (ha : 1 ≤ a) : (2 : ZMod (2 ^ (a + 1))) ^ a * 2 ^ a = 0 := by
  have : (2 : ZMod (2 ^ (a + 1))) ^ a * 2 ^ a = 2 ^ (a + 1) * 2 ^ (a - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [this, two_pow_succ_eq_zero, zero_mul]

theorem two_pow_ne_zero (a : ℕ) : (2 : ZMod (2 ^ (a + 1))) ^ a ≠ 0 := by
  intro h
  have h' : ((2 ^ a : ℕ) : ZMod (2 ^ (a + 1))) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by positivity) h'
  have : 2 ^ (a + 1) > 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem two_pow_mul_eq_zero_iff (r : ZMod (2 ^ (a + 1))) :
    (2 : ZMod (2 ^ (a + 1))) ^ a * r = 0 ↔
      ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) r = 0 := by
  constructor
  · intro h
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    have h' : ((2 ^ a * r.val : ℕ) : ZMod (2 ^ (a + 1))) = 0 := by
      push_cast; rw [ZMod.natCast_zmod_val]; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) (dvd_trans ⟨1, by ring⟩ h')
  · intro h
    obtain ⟨w, rfl⟩ := (castHom_eq_zero_iff_exists _ r).mp h
    push_cast
    rw [← mul_assoc, ← pow_succ, two_pow_succ_eq_zero, zero_mul]

end TwoArith

section TwoCover

variable (a : ℕ)

/-- `SL₂(ℤ/2^{a+1})`. -/
abbrev SLT := Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ (a + 1)))

/-- Reduction `SL₂(ℤ/2^{a+1}) → SL₂(ℤ/2^a)`. -/
noncomputable abbrev rhoTwo : SLT a →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ a)) :=
  reductionMod (2 ^ (a + 1)) (2 ^ a) (pow_dvd_pow 2 (Nat.le_succ a))

/-- Reduction `SL₂(ℤ/2^{a+1}) → SL₂(ℤ/2)`. -/
noncomputable abbrev rhoTwoOne : SLT a →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  reductionMod (2 ^ (a + 1)) 2 (dvd_pow_self 2 (Nat.succ_ne_zero a))

/-- The functional `φ(n) = n₀₀ - 1 + n₀₁ + n₁₀`. -/
def phiTwo (n : SLT a) : ZMod (2 ^ (a + 1)) := n 0 0 - 1 + n 0 1 + n 1 0

variable {a}

theorem mem_ker_rhoTwo_iff (n : SLT a) :
    n ∈ (rhoTwo a).ker ↔ ∃ W : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1))),
      (n : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) = 1 + (2 : ZMod (2 ^ (a + 1))) ^ a • W := by
  rw [mem_ker_reductionMod_iff]
  push_cast
  rfl

theorem phiTwo_of_eq {n : SLT a} {W : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))}
    (hW : (n : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) = 1 + (2 : ZMod (2 ^ (a + 1))) ^ a • W) :
    phiTwo a n = 2 ^ a * (W 0 0 + W 0 1 + W 1 0) := by
  have e00 := congrFun (congrFun hW 0) 0
  have e01 := congrFun (congrFun hW 0) 1
  have e10 := congrFun (congrFun hW 1) 0
  simp at e00 e01 e10
  unfold phiTwo
  rw [e00, e01, e10]; ring

theorem phiTwo_mul (ha : 1 ≤ a) {n n' : SLT a} (hn : n ∈ (rhoTwo a).ker)
    (hn' : n' ∈ (rhoTwo a).ker) : phiTwo a (n * n') = phiTwo a n + phiTwo a n' := by
  obtain ⟨W, hW⟩ := (mem_ker_rhoTwo_iff n).mp hn
  obtain ⟨W', hW'⟩ := (mem_ker_rhoTwo_iff n').mp hn'
  have hprod : ((n * n' : SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      1 + (2 : ZMod (2 ^ (a + 1))) ^ a • (W + W') := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hW, hW', one_add_smul_mul_one_add_smul,
      two_pow_mul_self ha, zero_smul, add_zero, smul_add, add_assoc]
  rw [phiTwo_of_eq hprod, phiTwo_of_eq hW, phiTwo_of_eq hW']
  simp only [Matrix.add_apply]; ring

theorem phiTwo_one : phiTwo a 1 = 0 := by simp [phiTwo]

theorem phiTwo_inv (ha : 1 ≤ a) {n : SLT a} (hn : n ∈ (rhoTwo a).ker) :
    phiTwo a n⁻¹ = -phiTwo a n := by
  have h := phiTwo_mul ha hn (inv_mem hn)
  rw [mul_inv_cancel, phiTwo_one] at h
  linear_combination -h

/-- `φ` is invariant mod 2 on traceless matrices: a finite check over `SL₂(ℤ/2)`. -/
theorem phi_conj_mod_two : ∀ b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ∀ W : Matrix (Fin 2) (Fin 2) (ZMod 2), W.trace = 0 →
      let X := (b : Matrix (Fin 2) (Fin 2) (ZMod 2)) * W * ((b⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))
      X 0 0 + X 0 1 + X 1 0 = W 0 0 + W 0 1 + W 1 0 := by
  decide +kernel

theorem phiTwo_conj (ha : 1 ≤ a) (b : SLT a) {n : SLT a} (hn : n ∈ (rhoTwo a).ker) :
    phiTwo a (b * n * b⁻¹) = phiTwo a n := by
  obtain ⟨W, hW⟩ := (mem_ker_rhoTwo_iff n).mp hn
  set q : ZMod (2 ^ (a + 1)) := 2 ^ a with hqdef
  have hq : q * q = 0 := two_pow_mul_self ha
  set X := (b : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) * W * ((b⁻¹ : SLT a) :
    Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1))))
  have hconj : ((b * n * b⁻¹ : SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      1 + q • X := by
    have hinv : (b : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) * ((b⁻¹ : SLT a) :
        Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, hW, X]
    rw [mul_add, add_mul, mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul]
  rw [phiTwo_of_eq hconj, phiTwo_of_eq hW]
  -- reduce modulo 2
  set F := (ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2)).mapMatrix
    (m := Fin 2) with hF
  have hdet : (n : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))).det = 1 := n.2
  rw [hW, Matrix.det_fin_two] at hdet
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add] at hdet
  have htr0 : q * (W 0 0 + W 1 1) = 0 := by
    linear_combination hdet - (W 0 0 * W 1 1 - W 0 1 * W 1 0) * hq
  have htr : (F W).trace = 0 := by
    rw [Matrix.trace_fin_two]
    have := (two_pow_mul_eq_zero_iff (W 0 0 + W 1 1)).mp htr0
    rw [map_add] at this
    exact this
  have key := phi_conj_mod_two (rhoTwoOne a b) (F W) htr
  have hFb : F (b : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      ((rhoTwoOne a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) := rfl
  have hFbi : F ((b⁻¹ : SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      (((rhoTwoOne a b)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    rw [← map_inv]; rfl
  have hFX : F X = ((rhoTwoOne a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
      Matrix (Fin 2) (Fin 2) (ZMod 2)) * F W *
      (((rhoTwoOne a b)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    simp only [X, map_mul, hFb, hFbi]
  have hdiff : q * ((X 0 0 + X 0 1 + X 1 0) - (W 0 0 + W 0 1 + W 1 0)) = 0 := by
    apply (two_pow_mul_eq_zero_iff _).mpr
    simp only [map_sub, map_add]
    have h00 : ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) (X 0 0) = F X 0 0 := rfl
    have h01 : ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) (X 0 1) = F X 0 1 := rfl
    have h10 : ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) (X 1 0) = F X 1 0 := rfl
    have g00 : ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) (W 0 0) = F W 0 0 := rfl
    have g01 : ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) (W 0 1) = F W 0 1 := rfl
    have g10 : ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2) (W 1 0) = F W 1 0 := rfl
    rw [h00, h01, h10, g00, g01, g10, hFX, key, sub_self]
  linear_combination hdiff

/-- `V = ker φ ∩ N`. -/
noncomputable def vTwo (ha : 1 ≤ a) : Subgroup (SLT a) where
  carrier := {n | n ∈ (rhoTwo a).ker ∧ phiTwo a n = 0}
  mul_mem' := by
    rintro n n' ⟨hn, hφ⟩ ⟨hn', hφ'⟩
    exact ⟨mul_mem hn hn', by rw [phiTwo_mul ha hn hn', hφ, hφ', add_zero]⟩
  one_mem' := ⟨one_mem _, phiTwo_one⟩
  inv_mem' := by
    rintro n ⟨hn, hφ⟩
    exact ⟨inv_mem hn, by rw [phiTwo_inv ha hn, hφ, neg_zero]⟩

theorem vTwo_le (ha : 1 ≤ a) : vTwo ha ≤ (rhoTwo a).ker := fun _ h => h.1

instance vTwo_normal (ha : 1 ≤ a) : (vTwo ha).Normal := by
  constructor
  rintro n ⟨hn, hφ⟩ b
  exact ⟨(rhoTwo a).normal_ker.conj_mem n hn b, by rw [phiTwo_conj ha b hn, hφ]⟩

/-- The scalar `ε = diag(1 - q, 1 + q)` as a commutator. -/
theorem epsTwo_eq (ha : 2 ≤ a) :
    ((⁅lowerRoot (2 : ZMod (2 ^ (a + 1))), upperRoot ((2 : ZMod (2 ^ (a + 1))) ^ (a - 1))⁆ :
      SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      !![1 - 2 ^ a, 0; 0, 1 + 2 ^ a] := by
  have hq : (2 : ZMod (2 ^ (a + 1))) * 2 ^ (a - 1) = 2 ^ a := by
    rw [← pow_succ']; congr 1; omega
  have h1 : (2 : ZMod (2 ^ (a + 1))) * (2 ^ (a - 1)) ^ 2 = 0 := by
    have : (2 : ZMod (2 ^ (a + 1))) * (2 ^ (a - 1)) ^ 2 = 2 ^ (a + 1) * 2 ^ (a - 2) := by
      rw [← pow_mul, ← pow_succ', ← pow_add]; congr 1; omega
    rw [this, two_pow_succ_eq_zero, zero_mul]
  have h2 : (2 : ZMod (2 ^ (a + 1))) ^ 2 * 2 ^ (a - 1) = 0 := by
    have : (2 : ZMod (2 ^ (a + 1))) ^ 2 * 2 ^ (a - 1) = 2 ^ (a + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this, two_pow_succ_eq_zero]
  have h3 : ((2 : ZMod (2 ^ (a + 1))) ^ a) ^ 2 = 0 := by
    rw [sq]; exact two_pow_mul_self (by omega)
  have h4 := two_mul_two_pow a
  rw [commutatorElement_def]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, upperRoot, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  all_goals first | linear_combination -hq | linear_combination h1 | linear_combination -h2 |
    linear_combination 2 * h1 + hq

theorem epsTwo_mem_ker (ha : 2 ≤ a) :
    (⁅lowerRoot (2 : ZMod (2 ^ (a + 1))), upperRoot ((2 : ZMod (2 ^ (a + 1))) ^ (a - 1))⁆ :
      SLT a) ∈ (rhoTwo a).ker := by
  rw [mem_ker_rhoTwo_iff, epsTwo_eq ha]
  refine ⟨!![-1, 0; 0, 1], ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp; ring

theorem phiTwo_epsTwo (ha : 2 ≤ a) :
    phiTwo a ⁅lowerRoot (2 : ZMod (2 ^ (a + 1))), upperRoot ((2 : ZMod (2 ^ (a + 1))) ^ (a - 1))⁆ =
      -2 ^ a := by
  unfold phiTwo
  rw [epsTwo_eq ha]
  simp

theorem rhoTwo_surjective (a : ℕ) : Function.Surjective (rhoTwo a) := by
  intro g
  obtain ⟨γ, rfl⟩ := reduction_surjective (2 ^ a) g
  refine ⟨VOA.Huang.DLN.reduction (2 ^ (a + 1)) γ, ?_⟩
  have := congrArg (fun f => f γ) (reductionMod_comp_reduction (2 ^ (a + 1)) (2 ^ a)
    (pow_dvd_pow 2 (Nat.le_succ a)))
  exact this

/-- **Two-power inflation from the multiplier bound at the target level.** -/
theorem inflationTrivial_rhoTwo_of_mult (ha : 2 ≤ a)
    (hA : MultAtMostTwo (Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ a)))) :
    InflationTrivial (rhoTwo a) := by
  have ha1 : 1 ≤ a := by omega
  set V := vTwo ha1
  let ρC : SLT a ⧸ V →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ a)) :=
    QuotientGroup.lift V (rhoTwo a) (vTwo_le ha1)
  have hfac : rhoTwo a = ρC.comp (QuotientGroup.mk' V) := by ext; rfl
  rw [hfac]
  apply inflationTrivial_comp
  set ε : SLT a :=
    ⁅lowerRoot (2 : ZMod (2 ^ (a + 1))), upperRoot ((2 : ZMod (2 ^ (a + 1))) ^ (a - 1))⁆ with hε
  have hεN : ε ∈ (rhoTwo a).ker := epsTwo_mem_ker ha
  apply inflationTrivial_of_cover ρC _ _ (QuotientGroup.mk' V ε) _ _ _ hA
  · intro g
    obtain ⟨b, rfl⟩ := rhoTwo_surjective a g
    exact ⟨QuotientGroup.mk b, rfl⟩
  · intro y hy
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V y
    have hb : b ∈ (rhoTwo a).ker := hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective V w
    have hcomm : ⁅d, b⁆ ∈ V := by
      have hdb : d * b * d⁻¹ ∈ (rhoTwo a).ker := (rhoTwo a).normal_ker.conj_mem b hb d
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]; exact mul_mem hdb (inv_mem hb)
      · rw [commutatorElement_def, phiTwo_mul ha1 hdb (inv_mem hb), phiTwo_conj ha1 d hb,
          phiTwo_inv ha1 hb, add_neg_cancel]
    have h1 : (QuotientGroup.mk' V) ⁅d, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · have hmap : (commutator (SLT a)).map (QuotientGroup.mk' V) ≤ commutator (SLT a ⧸ V) := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap ⟨ε, Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),
      rfl⟩
  · exact hεN
  · intro h
    have hmem : ε ∈ V := (QuotientGroup.eq_one_iff ε).mp h
    have := hmem.2
    rw [phiTwo_epsTwo ha, neg_eq_zero] at this
    exact two_pow_ne_zero a this

end TwoCover

/-! ## Reductions of `TwoPowerInflationFromTwo` -/

/-- Homology-free `|H₂(SL₂(ℤ/2^a))| ≤ 2` for all `a ≥ 2`. TRUE (Beyl 1986: the multiplier is
`ℤ/2`). -/
def TwoPowerMultAtMostTwo : Prop :=
  ∀ a : ℕ, 2 ≤ a → MultAtMostTwo (Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ a)))

/-- **`TwoPowerInflationFromTwo` from the multiplier bound.** -/
theorem twoPowerInflationFromTwo_of_mult (h : TwoPowerMultAtMostTwo) :
    TwoPowerInflationFromTwo := fun a ha =>
  inflationTrivial_rhoTwo_of_mult ha (h a ha)

/-- The base case `|H₂(SL₂(ℤ/4))| ≤ 2`. TRUE (Beyl 1986). -/
def TwoBaseMult : Prop := MultAtMostTwo (Matrix.SpecialLinearGroup (Fin 2) (ZMod 4))

/-- The two-adic layer bound: for `a ≥ 2`, in every central extension of `SL₂(ℤ/2^{a+1})`,
`⁅E, π⁻¹N⁆ ∩ ker π` has at most two elements, `N = ker(SL₂(ℤ/2^{a+1}) → SL₂(ℤ/2^a))`.
TRUE: it is contained in `[E,E] ∩ ker π`, of order at most `|H₂(SL₂(ℤ/2^{a+1}))| = 2`. -/
def TwoLayerAtMostTwo : Prop := ∀ a : ℕ, 2 ≤ a → LayerAtMostTwo (rhoTwo a)

theorem twoLayerAtMostTwo_of_mult (h : TwoPowerMultAtMostTwo) : TwoLayerAtMostTwo :=
  fun a ha => layerAtMostTwo_of_multAtMostTwo _ (h (a + 1) (by omega))

/-- **Induction on the exponent.** The base case and the two-adic layer bound give the
multiplier bound at every level. -/
theorem twoPowerMultAtMostTwo_of_base_layer (hbase : TwoBaseMult) (hL : TwoLayerAtMostTwo) :
    TwoPowerMultAtMostTwo := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => simpa using hbase
  | succ a ha ih =>
    exact multAtMostTwo_of_inflation_layer (rhoTwo a) (rhoTwo_surjective a)
      (inflationTrivial_rhoTwo_of_mult ha ih) (hL a ha)

theorem twoPowerMultAtMostTwo_iff_base_layer :
    TwoPowerMultAtMostTwo ↔ TwoBaseMult ∧ TwoLayerAtMostTwo :=
  ⟨fun h => ⟨h 2 le_rfl, twoLayerAtMostTwo_of_mult h⟩,
    fun h => twoPowerMultAtMostTwo_of_base_layer h.1 h.2⟩

/-- **`TwoPowerInflationFromTwo` from the base case and the two-adic layer bound.** -/
theorem twoPowerInflationFromTwo_of_base_layer (hbase : TwoBaseMult) (hL : TwoLayerAtMostTwo) :
    TwoPowerInflationFromTwo :=
  twoPowerInflationFromTwo_of_mult (twoPowerMultAtMostTwo_of_base_layer hbase hL)

end VOA.Huang.DLNSchur
