import VOA.Huang.DLNBeylSplit

/-!
# Reduction of Beyl's inflation theorem to prime powers

Residual propositions (TRUE, unproved here):

* `OddPrimePowerSchur`: `SL₂(ℤ/pᵏ)` has trivial Schur multiplier for odd primes `p`
  (Mennicke 1967; Beyl 1986, Thm. 3.9; DLN Thm. 2.1, first statement).
* `TwoPowerInflation`: inflation along `SL₂(ℤ/2^{a+1}) → SL₂(ℤ/2^a)` vanishes for `a ≥ 1`
  (Beyl 1986, Cor. 3.10 for `a ≥ 2`; for `a = 1` the multiplier of `SL₂(ℤ/2) ≅ S₃` is trivial).

Proved: `OddPrimePowerSchur ∧ TwoPowerInflation → BeylInflationSL2`, via the Chinese remainder
splitting `SL₂(ℤ/mn) ≅ SL₂(ℤ/m) × SL₂(ℤ/n)` and the coprime-exponent splitting lemma
`inflationTrivial_of_split`; the abelianization of `SL₂(ℤ/q)` has exponent dividing `q`.
-/

namespace VOA.Huang.DLNBeyl

open VOA.Huang.DLN

local notation "SLm(" n ")" => Matrix.SpecialLinearGroup (Fin 2) (ZMod n)

/-! ## Reduction maps -/

theorem reductionMod_comp (L M K : ℕ) (h₁ : M ∣ L) (h₂ : K ∣ M) :
    (reductionMod M K h₂).comp (reductionMod L M h₁) = reductionMod L K (h₂.trans h₁) := by
  ext g i j
  simp only [reductionMod, MonoidHom.comp_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  exact congrArg (fun f : ZMod L →+* ZMod K => f (g i j)) (ZMod.castHom_comp h₂ h₁)

theorem reductionMod_self (N : ℕ) : reductionMod N N dvd_rfl = MonoidHom.id _ := by
  ext g i j
  simp [reductionMod]

/-- `SL₂(ℤ/1)` is trivial. -/
instance subsingleton_SL_one : Subsingleton (SLm(1)) :=
  ⟨fun _ _ => Subtype.ext (Matrix.ext fun _ _ =>
    (inferInstance : Subsingleton (Fin 1)).elim _ _)⟩

theorem inflationTrivial_to_one {L n : ℕ} (hn : n = 1) (h : n ∣ L) :
    InflationTrivial (reductionMod L n h) := by
  subst hn
  exact inflationTrivial_of_subsingleton _

/-! ## The Chinese remainder splitting -/

theorem crt_cast_eq {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ZMod.chineseRemainder h x =
      (ZMod.castHom (dvd_mul_right m n) (ZMod m) x,
        ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := by
  have key : ((ZMod.chineseRemainder h : ZMod (m * n) ≃+* ZMod m × ZMod n) :
      ZMod (m * n) →+* ZMod m × ZMod n) =
      (ZMod.castHom (dvd_mul_right m n) (ZMod m)).prod
        (ZMod.castHom (dvd_mul_left n m) (ZMod n)) := RingHom.ext_zmod _ _
  exact congrArg (fun f : ZMod (m * n) →+* ZMod m × ZMod n => f x) key

theorem crt_cast_injective {m n : ℕ} (h : m.Coprime n) :
    Function.Injective fun x : ZMod (m * n) =>
      (ZMod.castHom (dvd_mul_right m n) (ZMod m) x,
        ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := by
  intro x y hxy
  apply (ZMod.chineseRemainder h).injective
  rw [crt_cast_eq, crt_cast_eq]; exact hxy

theorem crt_cast_surjective {m n : ℕ} (h : m.Coprime n) (u : ZMod m) (v : ZMod n) :
    ∃ x : ZMod (m * n), ZMod.castHom (dvd_mul_right m n) (ZMod m) x = u ∧
      ZMod.castHom (dvd_mul_left n m) (ZMod n) x = v := by
  obtain ⟨x, hx⟩ := (ZMod.chineseRemainder h).surjective (u, v)
  rw [crt_cast_eq, Prod.mk.injEq] at hx
  exact ⟨x, hx⟩

/-- **Chinese remainder theorem for `SL₂`.** -/
theorem sl_crt_bijective {m n : ℕ} (h : m.Coprime n) :
    Function.Bijective fun g : SLm(m * n) =>
      (reductionMod (m * n) m (dvd_mul_right m n) g,
        reductionMod (m * n) n (dvd_mul_left n m) g) := by
  constructor
  · intro g g' hgg
    simp only [Prod.mk.injEq] at hgg
    ext i j
    apply crt_cast_injective h
    have h1 := congrArg (fun x : SLm(m) => (x : Matrix (Fin 2) (Fin 2) (ZMod m)) i j) hgg.1
    have h2 := congrArg (fun x : SLm(n) => (x : Matrix (Fin 2) (Fin 2) (ZMod n)) i j) hgg.2
    simp only [reductionMod, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1 h2
    simp only [h1, h2]
  · rintro ⟨M₁, M₂⟩
    choose X hX using fun i j => crt_cast_surjective h (M₁ i j) (M₂ i j)
    let Xm : Matrix (Fin 2) (Fin 2) (ZMod (m * n)) := Matrix.of X
    have hdet : Xm.det = 1 := by
      apply crt_cast_injective h
      simp only [RingHom.map_det, map_one]
      have e1 : (ZMod.castHom (dvd_mul_right m n) (ZMod m)).mapMatrix Xm = M₁ := by
        ext i j; exact (hX i j).1
      have e2 : (ZMod.castHom (dvd_mul_left n m) (ZMod n)).mapMatrix Xm = M₂ := by
        ext i j; exact (hX i j).2
      rw [e1, e2, M₁.2, M₂.2]
    refine ⟨⟨Xm, hdet⟩, ?_⟩
    simp only [Prod.mk.injEq]
    constructor <;> ext i j <;>
      simp [reductionMod, Xm, (hX i j).1, (hX i j).2]

theorem sl_crt_bijective' {L m n : ℕ} (hL : L = m * n) (h : m.Coprime n) :
    Function.Bijective fun g : SLm(L) =>
      (reductionMod L m (hL ▸ dvd_mul_right m n) g,
        reductionMod L n (hL ▸ dvd_mul_left n m) g) := by
  subst hL; exact sl_crt_bijective h

/-! ## Abelianization exponent of `SL₂(ℤ/q)` -/

private theorem S_four' : ModularGroup.S ^ 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ST_three' : (ModularGroup.S * ModularGroup.T) ^ 3 = ModularGroup.S ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, ModularGroup.T, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- A character of `SL₂(ℤ)` is determined in exponent by its value on `T`. -/
theorem character_pow_of_T {A : Type*} [CommGroup A] (χ : SL2Z →* A) (n : ℕ)
    (hT : χ ModularGroup.T ^ n = 1) (γ : SL2Z) : χ γ ^ n = 1 := by
  have hST : χ ModularGroup.S * χ ModularGroup.T ^ 3 = 1 := by
    have h := congrArg χ ST_three'
    simp only [map_pow, map_mul, mul_pow] at h
    apply mul_left_cancel (a := χ ModularGroup.S ^ 2)
    calc
      χ ModularGroup.S ^ 2 * (χ ModularGroup.S * χ ModularGroup.T ^ 3) =
          χ ModularGroup.S ^ 3 * χ ModularGroup.T ^ 3 := by
            rw [← mul_assoc, ← pow_succ]
      _ = χ ModularGroup.S ^ 2 * 1 := by simpa using h
  have hS : χ ModularGroup.S ^ n = 1 := by
    have hs : χ ModularGroup.S = (χ ModularGroup.T ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hST
    rw [hs, inv_pow, ← pow_mul, mul_comm, pow_mul, hT, one_pow, inv_one]
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  | one => simp
  | mul x y _ _ hx hy => simp [map_mul, mul_pow, hx, hy]
  | inv x _ hx => simp [map_inv, inv_pow, hx]

/-- **The abelianization of `SL₂(ℤ/q)` has exponent dividing `q`.** -/
theorem pow_mem_commutator_SL (q : ℕ) [NeZero q] (b : SLm(q)) : b ^ q ∈ commutator (SLm(q)) := by
  obtain ⟨g, rfl⟩ := reduction_surjective q b
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, ← map_pow]
  have hT : ((Abelianization.of).comp (reduction q)) ModularGroup.T ^ q = 1 := by
    have hmem : ModularGroup.T ^ (q : ℤ) ∈ CongruenceSubgroup.Gamma q :=
      NSFinish.T_pow_mem_Gamma q
    have h1 : reduction q (ModularGroup.T ^ (q : ℤ)) = 1 := hmem
    rw [← map_pow]
    simp only [MonoidHom.comp_apply, map_pow]
    rw [← map_pow, ← map_pow]
    simpa only [zpow_natCast, map_pow] using congrArg Abelianization.of h1
  have := character_pow_of_T ((Abelianization.of).comp (reduction q)) q hT g
  simpa only [MonoidHom.comp_apply, map_pow] using this

/-! ## Residuals and the assembly -/

/-- **Mennicke / Beyl:** `SL₂(ℤ/pᵏ)` has trivial Schur multiplier for odd primes `p`.
TRUE (Beyl, Math. Z. 191 (1986), Thm. 3.9; DLN arXiv:1201.6644, Thm. 2.1), unproved here. -/
def OddPrimePowerSchur : Prop :=
  ∀ p k : ℕ, p.Prime → p ≠ 2 → 0 < k → SchurTrivial (SLm(p ^ k))

/-- **Beyl:** inflation `SL₂(ℤ/2^{a+1}) → SL₂(ℤ/2^a)` vanishes on Schur multipliers (`a ≥ 1`).
TRUE (Beyl, Math. Z. 191 (1986), Cor. 3.10 for `a ≥ 2`; `H₂(SL₂(ℤ/2)) = H₂(S₃) = 0` for
`a = 1`), unproved here. -/
def TwoPowerInflation : Prop :=
  ∀ a : ℕ, 1 ≤ a → InflationTrivial
    (reductionMod (2 ^ (a + 1)) (2 ^ a) (pow_dvd_pow 2 (Nat.le_succ a)))

/-- Product of two coprime moduli, identity inflation. -/
theorem schurTrivial_mul {m n : ℕ} (h : m.Coprime n) (hm : 0 < m) (hn : 0 < n)
    (sm : SchurTrivial (SLm(m))) (sn : SchurTrivial (SLm(n))) : SchurTrivial (SLm(m * n)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  exact inflationTrivial_of_split (MonoidHom.id _)
    (reductionMod (m * n) m (dvd_mul_right m n)) (reductionMod (m * n) n (dvd_mul_left n m))
    (reductionMod (m * n) m (dvd_mul_right m n)) (reductionMod (m * n) n (dvd_mul_left n m))
    (MonoidHom.id _) (MonoidHom.id _) (sl_crt_bijective h) (sl_crt_bijective h)
    (by ext; rfl) (by ext; rfl) h (pow_mem_commutator_SL m) (pow_mem_commutator_SL n) sm sn

/-- Odd moduli have trivial multiplier, from the odd prime-power case. -/
theorem schurTrivial_odd (hodd : OddPrimePowerSchur) :
    ∀ m : ℕ, Odd m → SchurTrivial (SLm(m)) := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd'
    refine hodd p k hp ?_ hk
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd') (by
      rw [Nat.even_pow]; exact ⟨even_two, hk.ne'⟩)
  | zero => intro h; exact absurd h (by decide)
  | one =>
    intro _
    exact inflationTrivial_of_subsingleton _
  | coprime a b ha hb hab iha ihb =>
    intro hodd'
    exact schurTrivial_mul hab (by omega) (by omega)
      (iha (Nat.Odd.of_mul_left hodd')) (ihb (Nat.Odd.of_mul_right hodd'))

/-- **Beyl's inflation theorem for all moduli from the prime-power residuals.** -/
theorem beylInflationSL2_of_local (hodd : OddPrimePowerSchur) (htwo : TwoPowerInflation) :
    BeylInflationSL2 := by
  intro N hN
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have hm0 : 0 < m := hm.pos
  have hcopA : (2 ^ a).Coprime m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hcopB : (2 ^ (a + 1)).Coprime m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hB : 2 * (2 ^ a * m) = 2 ^ (a + 1) * m := by ring
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (2 ^ (a + 1)) := ⟨by positivity⟩
  have i₁ : InflationTrivial
      (reductionMod (2 ^ (a + 1)) (2 ^ a) (pow_dvd_pow 2 (Nat.le_succ a))) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact inflationTrivial_to_one (by norm_num) _
    · exact htwo a ha
  have i₂ : InflationTrivial (MonoidHom.id (SLm(m))) := schurTrivial_odd hodd m hm
  refine inflationTrivial_of_split
    (reductionMod (2 * (2 ^ a * m)) (2 ^ a * m) (dvd_mul_left _ 2))
    (reductionMod (2 * (2 ^ a * m)) (2 ^ (a + 1)) (hB ▸ dvd_mul_right _ m))
    (reductionMod (2 * (2 ^ a * m)) m (hB ▸ dvd_mul_left m _))
    (reductionMod (2 ^ a * m) (2 ^ a) (dvd_mul_right _ m))
    (reductionMod (2 ^ a * m) m (dvd_mul_left m _))
    (reductionMod (2 ^ (a + 1)) (2 ^ a) (pow_dvd_pow 2 (Nat.le_succ a)))
    (MonoidHom.id _)
    (sl_crt_bijective hcopA) (sl_crt_bijective' hB hcopB) ?_ ?_ hcopB
    (pow_mem_commutator_SL _) (pow_mem_commutator_SL m) i₁ i₂
  · rw [reductionMod_comp, reductionMod_comp]
  · rw [reductionMod_comp, MonoidHom.id_comp]

/-- **Headline: DLN Theorem 2.3 (matrix form) from the prime-power Beyl residuals.** -/
theorem matrixDLNLifting_of_local (hodd : OddPrimePowerSchur) (htwo : TwoPowerInflation) :
    DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_beyl (beylInflationSL2_of_local hodd htwo)

theorem centralCongruenceSL2_of_local (hodd : OddPrimePowerSchur) (htwo : TwoPowerInflation) :
    DLNLifting.CentralCongruenceSL2 :=
  centralCongruenceSL2_of_beyl (beylInflationSL2_of_local hodd htwo)

end VOA.Huang.DLNBeyl
