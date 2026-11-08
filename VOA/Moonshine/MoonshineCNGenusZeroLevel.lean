/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroHeckeStep
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Genus zero on the abstract interface: the symmetry group contains some `Γ₁(N′)`

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. The `Γ₁` version of the group-theoretic
proposition (Cummins (2002), Prop. 2.1; Cummins–Gannon's Prop. 5.1 is not usable for `Γ₁`, see
the dead ends recorded in the blueprint). Throughout,
`F` is a replicable family of period `N > 0` satisfying the prime Hecke identity at every
admissible prime `p ≡ 1 (mod N)`, `f = qSeriesFun (F.c k)` and `G = symmetryGroup f`.

* **Rationality** (Cummins–Gannon, Lemma 5.4): for `(a b; c d) ∈ G` with `c ≠ 0`, `a / c ∈ ℚ`
  (`exists_rat_upperLeft_div_lowerLeft`): the Hecke step at admissible primes `p > |c|` produces
  elements with lower-left entry `c` and upper-left entry `p a`; if `a / c` were irrational the
  residues `fract (p a / c)` would be pairwise distinct, against the finiteness of residues.
  Applied to `g T g⁻¹`, also `c² ∈ ℚ` (`exists_rat_lowerLeft_sq`).
* **An integral element** (`exists_integral_mem_symmetryGroup`): nontriviality (`f` is not
  injective modulo `ℤ`, proved on the LR side) and property P give `g ∈ G` with `c ≠ 0`; then
  `g T^H g⁻¹`, `H` clearing the denominators of `a c`, `a²`, `c²` and divisible by `N`, is an
  integral matrix of `G` with `N ∣ C ≠ 0` and `D ≡ 1 (mod N)`.
* **Integrality of the Hecke step** (Cummins–Gannon, Lemma 5.7): for an integral
  `(A B; C D) ∈ G` and an admissible prime `p > |C|` dividing `D`, `(p A, B; C, D / p) ∈ G`
  (`exists_mem_symmetryGroup_heckeStep_of_integral`). Otherwise the Hecke step with `j ≠ 0`
  starts a sequence with lower-left entry `C` whose lower-right entries have exact denominator
  `p^(n+1)`, giving infinitely many residues `fract (d / C)`.
* **A lower unipotent** (`exists_glLowerUnipotent_mem_symmetryGroup`): Dirichlet's theorem
  gives an admissible prime `p ≡ D (mod |C|)`, `p > |C|`; integrality turns `(A B; C D) T^t` into
  `(p A, B'; C, 1)`, and a translation turns this into `(1 0; C 1)`.
* **All first columns, hence `Γ₁(|L|) ≤ G`** (`gamma1GL_le_symmetryGroup_of_lowerUnipotent`): for
  `L ∣ c₀`, `a₀ ≡ 1 (mod L)`, `gcd (a₀, c₀) = 1`, Dirichlet's theorem gives a prime
  `q ≡ a₀ (mod |c₀|)`, and integrality applied to `(1 0; c₀ 1) T^t` gives an element of `G` with
  first column `(a₀, c₀)`. Every element of `Γ₁(|L|)` is such an element times a translation.

Headline: `ReplicableFamily.exists_gamma1GL_le_symmetryGroup`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-! ### Preliminaries -/

/-- The admissible primes above any bound form an infinite set. -/
lemma infinite_admissible_primes_gt {N : ℕ} (hN : 0 < N) (x : ℝ) :
    {p : ℕ | p.Prime ∧ p ≡ 1 [MOD N] ∧ x < p}.Infinite := by
  have h := Nat.infinite_setOf_prime_modEq_one hN.ne'
  have hfin : {p : ℕ | (p : ℝ) ≤ x}.Finite :=
    (Set.finite_Iic ⌊x⌋₊).subset fun p hp => Nat.le_floor hp
  exact (h.diff hfin).mono fun p hp => ⟨hp.1.1, hp.1.2, not_le.mp hp.2⟩

lemma rat_mul_den_eq_num_real (q : ℚ) : (q : ℝ) * q.den = q.num := by
  exact_mod_cast Rat.mul_den_eq_num q

lemma glLowerUnipotent_mul (x y : ℝ) :
    glLowerUnipotent x * glLowerUnipotent y = glLowerUnipotent (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glLowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma glLowerUnipotent_zero : glLowerUnipotent 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glLowerUnipotent]

lemma glLowerUnipotent_inv (y : ℝ) : (glLowerUnipotent y)⁻¹ = glLowerUnipotent (-y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [glLowerUnipotent_mul, add_neg_cancel, glLowerUnipotent_zero]

lemma glFinTwo_mul_glUpperUnipotent_apply (g : GL (Fin 2) ℝ) (t : ℝ) :
    (g * glUpperUnipotent t) 0 0 = g 0 0 ∧ (g * glUpperUnipotent t) 0 1 = g 0 0 * t + g 0 1 ∧
      (g * glUpperUnipotent t) 1 0 = g 1 0 ∧ (g * glUpperUnipotent t) 1 1 = g 1 0 * t + g 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [glFinTwo_mul_apply] <;> simp [glUpperUnipotent]

lemma glUpperUnipotent_mul_glFinTwo_apply (g : GL (Fin 2) ℝ) (t : ℝ) :
    (glUpperUnipotent t * g) 0 0 = g 0 0 + t * g 1 0 ∧
      (glUpperUnipotent t * g) 0 1 = g 0 1 + t * g 1 1 ∧
      (glUpperUnipotent t * g) 1 0 = g 1 0 ∧ (glUpperUnipotent t * g) 1 1 = g 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [glFinTwo_mul_apply] <;> simp [glUpperUnipotent]

section Level

variable {N : ℕ} (F : ReplicableFamily N) (k : ℕ)

/-! ### Rationality -/

/-- **Rationality of `a / c`** (Cummins–Gannon, Lemma 5.4). -/
theorem exists_rat_upperLeft_div_lowerLeft (hN : 0 < N) (hB1 : PrimeHeckeIdentity F k)
    {g : GL (Fin 2) ℝ} (hg : g ∈ symmetryGroup (qSeriesFun (F.c k))) (hc0 : g 1 0 ≠ 0) :
    ∃ q : ℚ, g 0 0 / g 1 0 = q := by
  by_contra hirr
  have hfin := finite_fract_upperLeft_div_lowerLeft (F.isJDominated k) hc0
  apply hfin.not_infinite
  refine Set.infinite_of_injOn_mapsTo (f := fun p : ℕ => Int.fract ((p : ℝ) * (g 0 0 / g 1 0)))
    ?_ ?_ (infinite_admissible_primes_gt hN |g 1 0|)
  · intro p₁ _ p₂ _ heq
    obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp heq
    by_contra hne
    have hne' : ((p₁ : ℝ) - p₂) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    refine hirr ⟨z / ((p₁ : ℚ) - p₂), ?_⟩
    push_cast
    rw [eq_div_iff hne']
    linear_combination hz
  · intro p hp
    obtain ⟨j, -, h, hh, h00, -, h10, -⟩ :=
      exists_heckeStep_mem_symmetryGroup F k hp.1 (hB1 p hp.1 hp.2.1) hg hc0 hp.2.2
    refine ⟨h, ⟨hh, h10⟩, ?_⟩
    simp only
    rw [h00, mul_div_assoc]

/-- **Rationality of `c²`**: apply rationality of `a / c` to `g T g⁻¹`, whose first column is
`(1 - a c, -c²)`. -/
theorem exists_rat_lowerLeft_sq (hN : 0 < N) (hB1 : PrimeHeckeIdentity F k)
    {g : GL (Fin 2) ℝ} (hg : g ∈ symmetryGroup (qSeriesFun (F.c k))) (hc0 : g 1 0 ≠ 0) :
    ∃ q : ℚ, g 1 0 ^ 2 = q := by
  obtain ⟨q₀, hq₀⟩ := exists_rat_upperLeft_div_lowerLeft F k hN hB1 hg hc0
  have hX : g * glUpperUnipotent 1 * g⁻¹ ∈ symmetryGroup (qSeriesFun (F.c k)) :=
    (symmetryGroup _).mul_mem ((symmetryGroup _).mul_mem hg
      (glUpperUnipotent_one_mem_symmetryGroup_qSeriesFun _)) ((symmetryGroup _).inv_mem hg)
  rw [conj_glUpperUnipotent (det_val_eq_one_of_mem_symmetryGroup hg)] at hX
  have hX0 : -(1 * g 1 0 ^ 2) ≠ 0 := by
    rw [one_mul, neg_ne_zero]; exact pow_ne_zero 2 hc0
  obtain ⟨q₁, hq₁⟩ := exists_rat_upperLeft_div_lowerLeft F k hN hB1 hX
    (by rw [glOfDetOne_apply_one_zero]; exact hX0)
  rw [glOfDetOne_apply_zero_zero, glOfDetOne_apply_one_zero] at hq₁
  rw [div_eq_iff hc0] at hq₀
  rw [div_eq_iff hX0] at hq₁
  refine ⟨(q₀ - q₁)⁻¹, ?_⟩
  push_cast
  refine eq_inv_of_mul_eq_one_left ?_
  linear_combination -(g 1 0 * hq₀) - hq₁

/-! ### An integral element -/

/-- **An integral element with lower-left entry in `N ℤ ∖ {0}`.** -/
theorem exists_integral_mem_symmetryGroup (hN : 0 < N) (hB1 : PrimeHeckeIdentity F k)
    (hD7 : ¬ IsInjectiveModTranslations (qSeriesFun (F.c k))) :
    ∃ m ∈ symmetryGroup (qSeriesFun (F.c k)), ∃ A B C D : ℤ, m 0 0 = A ∧ m 0 1 = B ∧
      m 1 0 = C ∧ m 1 1 = D ∧ C ≠ 0 ∧ (N : ℤ) ∣ C ∧ D ≡ 1 [ZMOD N] := by
  have hc := F.isJDominated k
  -- a symmetry that is not a translation
  obtain ⟨γ, hγ, hγ0⟩ : ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)), γ 1 0 ≠ 0 := by
    by_contra hnone
    apply hD7
    intro σ τ hστ
    obtain ⟨γ, hγ, hγστ⟩ := exists_mem_symmetryGroup_smul_eq hN F k hB1 hστ
    have h0 : γ 1 0 = 0 := by
      by_contra h0
      exact hnone ⟨γ, hγ, h0⟩
    obtain ⟨n, hn⟩ := exists_int_smul_eq_add_of_lowerLeft_eq_zero hc hγ h0
    refine ⟨-n, ?_⟩
    have h1 := hn σ
    rw [hγστ] at h1
    rw [h1]
    push_cast
    ring
  obtain ⟨q₀, hq₀⟩ := exists_rat_upperLeft_div_lowerLeft F k hN hB1 hγ hγ0
  obtain ⟨v, hv⟩ := exists_rat_lowerLeft_sq F k hN hB1 hγ hγ0
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hγ0
    have : γ 1 0 ^ 2 = 0 := by rw [hv]; simp
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  set r₁ : ℚ := q₀ * v with hr₁
  set r₂ : ℚ := q₀ ^ 2 * v with hr₂
  set H : ℕ := N * r₁.den * r₂.den * v.den with hH
  have hX : γ * glUpperUnipotent ((H : ℤ) : ℝ) * γ⁻¹ ∈ symmetryGroup (qSeriesFun (F.c k)) :=
    (symmetryGroup _).mul_mem ((symmetryGroup _).mul_mem hγ
      (glUpperUnipotent_intCast_mem_symmetryGroup _ H)) ((symmetryGroup _).inv_mem hγ)
  rw [conj_glUpperUnipotent (det_val_eq_one_of_mem_symmetryGroup hγ)] at hX
  -- the real identities `a c = r₁`, `a² = r₂`, `c² = v`
  have ha : γ 0 0 = q₀ * γ 1 0 := by rw [← hq₀]; field_simp
  have hac : γ 0 0 * γ 1 0 = (r₁ : ℝ) := by
    rw [hr₁, ha]; push_cast; rw [← hv]; ring
  have haa : γ 0 0 ^ 2 = (r₂ : ℝ) := by
    rw [hr₂, ha]; push_cast; rw [← hv]; ring
  set e₁ : ℤ := N * r₂.den * v.den * r₁.num with he₁
  set e₂ : ℤ := N * r₁.den * v.den * r₂.num with he₂
  set e₃ : ℤ := N * r₁.den * r₂.den * v.num with he₃
  have hHr₁ : (H : ℝ) * r₁ = e₁ := by
    rw [he₁, hH]; push_cast; rw [← rat_mul_den_eq_num_real r₁]; ring
  have hHr₂ : (H : ℝ) * r₂ = e₂ := by
    rw [he₂, hH]; push_cast; rw [← rat_mul_den_eq_num_real r₂]; ring
  have hHv : (H : ℝ) * v = e₃ := by
    rw [he₃, hH]; push_cast; rw [← rat_mul_den_eq_num_real v]; ring
  refine ⟨_, hX, 1 - e₁, e₂, -e₃, 1 + e₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [glOfDetOne_apply_zero_zero]; push_cast; rw [← hHr₁, ← hac]; ring
  · rw [glOfDetOne_apply_zero_one]; push_cast; rw [haa, hHr₂]
  · rw [glOfDetOne_apply_one_zero, hv]; push_cast; rw [← hHv]
  · rw [glOfDetOne_apply_one_one]; push_cast; rw [← hHr₁, ← hac]; ring
  · rw [neg_ne_zero, he₃]
    have h1 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have h2 : (r₁.den : ℤ) ≠ 0 := by exact_mod_cast r₁.den_nz
    have h3 : (r₂.den : ℤ) ≠ 0 := by exact_mod_cast r₂.den_nz
    have h4 : v.num ≠ 0 := Rat.num_ne_zero.mpr hv0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
  · exact ⟨-(r₁.den * r₂.den * v.num), by rw [he₃]; ring⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨-(r₂.den * v.den * r₁.num), by rw [he₁]; ring⟩

/-! ### Integrality of the Hecke step -/

/-- **Integrality of the Hecke step** (Cummins–Gannon, Lemma 5.7): for an integral `(A B; C D)`
in the symmetry group, `C ≠ 0`, and a prime `p > |C|` with the prime Hecke identity at `p` and
`p ∣ D`, also `(p A, B; C, D / p)` lies in the symmetry group. -/
theorem exists_mem_symmetryGroup_heckeStep_of_integral {p : ℕ} (hp : p.Prime)
    (hB1p : PrimeHeckeIdentityAt F k p hp.pos) {m : GL (Fin 2) ℝ}
    (hm : m ∈ symmetryGroup (qSeriesFun (F.c k))) {A B C D : ℤ} (hA : m 0 0 = A)
    (hB : m 0 1 = B) (hC : m 1 0 = C) (hD : m 1 1 = D) (hC0 : C ≠ 0) (hCp : |C| < p)
    (hpD : (p : ℤ) ∣ D) :
    ∃ m' ∈ symmetryGroup (qSeriesFun (F.c k)), m' 0 0 = p * A ∧ m' 0 1 = B ∧ m' 1 0 = C ∧
      m' 1 1 = D / p := by
  have hc := F.isJDominated k
  have hC0R : (C : ℝ) ≠ 0 := by exact_mod_cast hC0
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hCpR : |(C : ℝ)| < p := by
    rw [← Int.cast_abs]; exact_mod_cast hCp
  have hc0 : m 1 0 ≠ 0 := by rw [hC]; exact hC0R
  have hcp : |m 1 0| < p := by rw [hC]; exact hCpR
  have hpC : ¬ (p : ℤ) ∣ C := by
    intro hd
    have h1 : p ∣ C.natAbs := Int.natCast_dvd.mp hd
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hC0) h1
    have h3 : (C.natAbs : ℤ) < p := by rw [Int.natCast_natAbs]; exact hCp
    omega
  obtain ⟨j, hj, h, hh, h00, h01, h10, h11⟩ :=
    exists_heckeStep_mem_symmetryGroup F k hp hB1p hm hc0 hcp
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨h, hh, by rw [h00, hA], ?_, by rw [h10, hC], ?_⟩
    · rw [h01, hB]; simp
    · rw [h11, hD, hC]; simp
  exfalso
  -- the denominators of the lower-right entries grow
  have claim : ∀ n : ℕ, ∃ h ∈ symmetryGroup (qSeriesFun (F.c k)), h 1 0 = (C : ℝ) ∧
      ∃ E : ℤ, h 1 1 * (p : ℝ) ^ (n + 1) = E ∧ ¬ (p : ℤ) ∣ E := by
    intro n
    induction n with
    | zero =>
      refine ⟨h, hh, by rw [h10, hC], D - j * C, ?_, ?_⟩
      · rw [h11, hD, hC, pow_one]; push_cast; field_simp
      · intro hdvd
        have h2 : (p : ℤ) ∣ (j : ℤ) * C := by
          have h3 := dvd_sub hpD hdvd
          rwa [sub_sub_cancel] at h3
        rcases Int.Prime.dvd_mul' hp h2 with h3 | h3
        · have h4 : p ∣ j := by exact_mod_cast h3
          exact hj0 (Nat.eq_zero_of_dvd_of_lt h4 hj)
        · exact hpC h3
    | succ n ih =>
      obtain ⟨h', hh', h'10, E, hE, hEp⟩ := ih
      obtain ⟨j', -, h'', hh'', -, -, h''10, h''11⟩ :=
        exists_heckeStep_mem_symmetryGroup F k hp hB1p hh' (by rw [h'10]; exact hC0R)
          (by rw [h'10]; exact hCpR)
      refine ⟨h'', hh'', by rw [h''10, h'10], E - j' * C * (p : ℤ) ^ (n + 1), ?_, ?_⟩
      · rw [h''11, h'10]
        push_cast
        rw [← hE, pow_succ]
        field_simp
      · intro hdvd
        apply hEp
        have h3 : (p : ℤ) ∣ (j' : ℤ) * C * (p : ℤ) ^ (n + 1) :=
          dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero n)) _
        have h4 := dvd_add hdvd h3
        rwa [sub_add_cancel] at h4
  choose hs hsmem hs10 hsE using claim
  choose E hE hEp using hsE
  have hfin := finite_fract_lowerRight_div_lowerLeft hc hC0R
  apply hfin.not_infinite
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => Int.fract (hs n 1 1 / C)) ?_
    fun n => ⟨hs n, ⟨hsmem n, hs10 n⟩, rfl⟩
  refine Function.Injective.of_lt_imp_ne fun n n' hlt heq => ?_
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp heq
  have hz' : hs n' 1 1 = hs n 1 1 - z * C := by
    rw [div_sub_div_same, div_eq_iff hC0R] at hz
    linear_combination -hz
  have hpow : (p : ℝ) ^ (n' + 1) = (p : ℝ) ^ (n + 1) * (p : ℝ) ^ (n' - n) := by
    rw [← pow_add]; congr 1; omega
  have key : (E n' : ℝ) = E n * (p : ℝ) ^ (n' - n) - z * C * (p : ℝ) ^ (n' + 1) := by
    rw [← hE n', ← hE n, hz', hpow]
    ring
  have keyZ : E n' = E n * (p : ℤ) ^ (n' - n) - z * C * (p : ℤ) ^ (n' + 1) := by
    exact_mod_cast key
  apply hEp n'
  rw [keyZ]
  exact dvd_sub (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _)
    (dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero n')) _)

/-! ### A lower unipotent element -/

/-- **A lower unipotent element** `(1 0; L 1) ∈ G` with `N ∣ L ≠ 0`. -/
theorem exists_glLowerUnipotent_mem_symmetryGroup (hN : 0 < N) (hB1 : PrimeHeckeIdentity F k)
    (hD7 : ¬ IsInjectiveModTranslations (qSeriesFun (F.c k))) :
    ∃ L : ℤ, L ≠ 0 ∧ (N : ℤ) ∣ L ∧ glLowerUnipotent L ∈ symmetryGroup (qSeriesFun (F.c k)) := by
  obtain ⟨m, hm, A, B, C, D, hA, hB, hC, hD, hC0, hNC, hD1⟩ :=
    exists_integral_mem_symmetryGroup F k hN hB1 hD7
  have hdet := det_entries_of_mem_symmetryGroup hm
  have hdetZ : A * D - B * C = 1 := by
    rw [hA, hB, hC, hD] at hdet; exact_mod_cast hdet
  have hcop : IsCoprime D (C.natAbs : ℤ) := by
    have h1 : IsCoprime D C := ⟨A, -B, by linear_combination hdetZ⟩
    rw [Int.natCast_natAbs]
    rcases abs_choice C with h | h <;> rw [h]
    · exact h1
    · exact h1.neg_right
  obtain ⟨p, hpgt, hp, hpD⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq C.natAbs (Int.natAbs_ne_zero.mpr hC0) hcop
  -- `p = D + t C`
  have hCdvd : C ∣ (p : ℤ) - D := by
    have := Int.modEq_iff_dvd.mp hpD.symm
    exact Int.natAbs_dvd.mp this
  obtain ⟨s, hs⟩ := hCdvd
  have hp1 : p ≡ 1 [MOD N] := by
    have h1 : (p : ℤ) ≡ D [ZMOD N] := by
      rw [Int.modEq_iff_dvd]
      exact (hNC.trans ⟨-s, by linear_combination -hs⟩)
    have h2 : (p : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD N] := by
      simpa using h1.trans hD1
    exact Int.natCast_modEq_iff.mp h2
  have hCp : |C| < (p : ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast hpgt
  have hsR : (p : ℝ) - D = C * s := by exact_mod_cast hs
  set m' := m * glUpperUnipotent ((s : ℤ) : ℝ) with hm'
  have hm'mem : m' ∈ symmetryGroup (qSeriesFun (F.c k)) :=
    (symmetryGroup _).mul_mem hm (glUpperUnipotent_intCast_mem_symmetryGroup _ s)
  obtain ⟨e00, e01, e10, e11⟩ := glFinTwo_mul_glUpperUnipotent_apply m ((s : ℤ) : ℝ)
  obtain ⟨m'', hm'', f00, f01, f10, f11⟩ :=
    exists_mem_symmetryGroup_heckeStep_of_integral F k hp (hB1 p hp hp1) hm'mem
      (A := A) (B := A * s + B) (C := C) (D := p) (by rw [hm', e00, hA])
      (by rw [hm', e01, hA, hB]; push_cast; ring) (by rw [hm', e10, hC])
      (by rw [hm', e11, hC, hD]; push_cast; linear_combination -hsR) hC0 hCp dvd_rfl
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have f11' : m'' 1 1 = 1 := by rw [f11]; push_cast; exact div_self hp0
  have hdet'' := det_entries_of_mem_symmetryGroup hm''
  refine ⟨C, hC0, hNC, ?_⟩
  have heq : glUpperUnipotent ((-(A * s + B) : ℤ) : ℝ) * m'' = glLowerUnipotent C := by
    obtain ⟨g00, g01, g10, g11⟩ := glUpperUnipotent_mul_glFinTwo_apply m'' ((-(A * s + B) : ℤ) : ℝ)
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [g00, f00, f10]
      simp only [glLowerUnipotent, glOfDetOne_val, Fin.isValue, of_apply, cons_val',
        cons_val_zero, empty_val', cons_val_fin_one]
      rw [f00, f01, f10, f11'] at hdet''
      push_cast at hdet'' ⊢
      linear_combination hdet''
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      rw [g01, f01, f11']
      simp [glLowerUnipotent]
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]
      rw [g10, f10]
      simp [glLowerUnipotent]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [g11, f11']
      simp [glLowerUnipotent]
  rw [← heq]
  exact (symmetryGroup _).mul_mem (glUpperUnipotent_intCast_mem_symmetryGroup _ _) hm''

/-! ### All first columns, and `Γ₁(|L|) ≤ G` -/

lemma glLowerUnipotent_intCast_mul_mem {L : ℤ}
    (hLmem : glLowerUnipotent L ∈ symmetryGroup (qSeriesFun (F.c k))) (n : ℤ) :
    glLowerUnipotent ((n * L : ℤ) : ℝ) ∈ symmetryGroup (qSeriesFun (F.c k)) := by
  induction n using Int.induction_on with
  | zero => simp [glLowerUnipotent_zero]
  | succ i ih =>
    have e : (((i + 1 : ℤ) * L : ℤ) : ℝ) = ((i * L : ℤ) : ℝ) + (L : ℝ) := by push_cast; ring
    rw [e, ← glLowerUnipotent_mul]
    exact (symmetryGroup _).mul_mem ih hLmem
  | pred i ih =>
    have e : (((-(i : ℤ) - 1) * L : ℤ) : ℝ) = ((-(i : ℤ) * L : ℤ) : ℝ) + -(L : ℝ) := by
      push_cast; ring
    rw [e, ← glLowerUnipotent_mul, ← glLowerUnipotent_inv]
    exact (symmetryGroup _).mul_mem ih ((symmetryGroup _).inv_mem hLmem)

/-- **All first columns** (Cummins (2002), Prop. 2.1, last step): if `(1 0; L 1) ∈ G` with
`N ∣ L ≠ 0`, every primitive column `(a₀, c₀)` with `L ∣ c₀`, `a₀ ≡ 1 (mod L)` is the first
column of an integral element of `G`. -/
theorem exists_mem_symmetryGroup_firstColumn (hB1 : PrimeHeckeIdentity F k)
    {L : ℤ} (hNL : (N : ℤ) ∣ L)
    (hLmem : glLowerUnipotent L ∈ symmetryGroup (qSeriesFun (F.c k))) {a₀ c₀ : ℤ}
    (hc₀ : L ∣ c₀) (ha₀ : a₀ ≡ 1 [ZMOD L]) (hcop : IsCoprime a₀ c₀) :
    ∃ m ∈ symmetryGroup (qSeriesFun (F.c k)), ∃ B D : ℤ, m 0 0 = a₀ ∧ m 0 1 = B ∧
      m 1 0 = c₀ ∧ m 1 1 = D := by
  by_cases hc0 : c₀ = 0
  · subst hc0
    rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp hcop) with h | h <;> subst h
    · exact ⟨1, (symmetryGroup _).one_mem, 0, 1, by simp, by simp, by simp, by simp⟩
    · exact ⟨-1, neg_one_mem_symmetryGroup _, 0, -1, by simp, by simp, by simp, by simp⟩
  obtain ⟨b, hb⟩ := hc₀
  have hmemc : glLowerUnipotent (c₀ : ℝ) ∈ symmetryGroup (qSeriesFun (F.c k)) := by
    have h1 := glLowerUnipotent_intCast_mul_mem F k hLmem b
    rwa [show b * L = c₀ by rw [hb]; ring] at h1
  have hcop' : IsCoprime a₀ (c₀.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    rcases abs_choice c₀ with h | h <;> rw [h]
    · exact hcop
    · exact hcop.neg_right
  obtain ⟨q, hqgt, hq, hqa⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq c₀.natAbs (Int.natAbs_ne_zero.mpr hc0) hcop'
  have hcdvd : c₀ ∣ a₀ - q := Int.natAbs_dvd.mp (Int.modEq_iff_dvd.mp hqa)
  obtain ⟨s, hs⟩ := hcdvd
  have hq1 : q ≡ 1 [MOD N] := by
    have h1 : (q : ℤ) ≡ a₀ [ZMOD N] := by
      rw [Int.modEq_iff_dvd]
      exact hNL.trans ((show L ∣ c₀ from ⟨b, hb⟩).trans ⟨s, hs⟩)
    have h2 : a₀ ≡ 1 [ZMOD N] := by
      rw [Int.modEq_iff_dvd] at ha₀ ⊢
      exact hNL.trans ha₀
    have h3 : (q : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD N] := by simpa using h1.trans h2
    exact Int.natCast_modEq_iff.mp h3
  have hqc : |c₀| < (q : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hqgt
  -- `q ∣ 1 + t c₀`
  have hcopq : IsCoprime (q : ℤ) c₀ := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hnd : ¬ q ∣ c₀.natAbs := fun hd =>
      absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) hd) (by
        have : (c₀.natAbs : ℤ) < q := by rw [Int.natCast_natAbs]; exact hqc
        omega)
    have := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
    simpa [Int.gcd] using this
  obtain ⟨u, v, huv⟩ := hcopq
  have huvR : (u : ℝ) * q + v * c₀ = 1 := by exact_mod_cast huv
  set m₁ := glLowerUnipotent (c₀ : ℝ) * glUpperUnipotent ((-v : ℤ) : ℝ) with hm₁
  have hm₁mem : m₁ ∈ symmetryGroup (qSeriesFun (F.c k)) :=
    (symmetryGroup _).mul_mem hmemc (glUpperUnipotent_intCast_mem_symmetryGroup _ _)
  obtain ⟨e00, e01, e10, e11⟩ := glFinTwo_mul_glUpperUnipotent_apply (glLowerUnipotent (c₀ : ℝ))
    ((-v : ℤ) : ℝ)
  obtain ⟨m₂, hm₂, f00, f01, f10, f11⟩ :=
    exists_mem_symmetryGroup_heckeStep_of_integral F k hq (hB1 q hq hq1) hm₁mem
      (A := 1) (B := -v) (C := c₀) (D := u * q)
      (by rw [hm₁, e00]; simp [glLowerUnipotent])
      (by rw [hm₁, e01]; simp [glLowerUnipotent])
      (by rw [hm₁, e10]; simp [glLowerUnipotent])
      (by rw [hm₁, e11]; simp [glLowerUnipotent]; linear_combination -huvR)
      hc0 hqc (dvd_mul_left _ _)
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have f11' : m₂ 1 1 = u := by
    rw [f11]; push_cast; field_simp
  obtain ⟨g00, g01, g10, g11⟩ := glUpperUnipotent_mul_glFinTwo_apply m₂ ((s : ℤ) : ℝ)
  refine ⟨glUpperUnipotent ((s : ℤ) : ℝ) * m₂,
    (symmetryGroup _).mul_mem (glUpperUnipotent_intCast_mem_symmetryGroup _ _) hm₂,
    -v + s * u, u, ?_, ?_, ?_, ?_⟩
  · have hsR : (a₀ : ℝ) - q = c₀ * s := by exact_mod_cast hs
    rw [g00, f00, f10]; push_cast; linear_combination -hsR
  · rw [g01, f01, f11']; push_cast; ring
  · rw [g10, f10]
  · rw [g11, f11']

/-- **`Γ₁(|L|)` is contained in the symmetry group** once `(1 0; L 1)` is, `N ∣ L ≠ 0`. -/
theorem gamma1GL_le_symmetryGroup_of_lowerUnipotent (hB1 : PrimeHeckeIdentity F k)
    {L : ℤ} (hNL : (N : ℤ) ∣ L)
    (hLmem : glLowerUnipotent L ∈ symmetryGroup (qSeriesFun (F.c k))) :
    gamma1GL L.natAbs ≤ symmetryGroup (qSeriesFun (F.c k)) := by
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem _ γ).mp hγ
  have hc : L ∣ γ 1 0 :=
    Int.natAbs_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10)
  have ha : γ 0 0 ≡ 1 [ZMOD L] := by
    have h1 : γ 0 0 ≡ 1 [ZMOD (L.natAbs : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using h00)
    rw [Int.modEq_iff_dvd] at h1 ⊢
    exact Int.natAbs_dvd.mp h1
  have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hcop : IsCoprime (γ 0 0) (γ 1 0) := ⟨γ 1 1, -γ 0 1, by linear_combination hdetγ⟩
  obtain ⟨m, hm, B, D, m00, m01, m10, m11⟩ :=
    exists_mem_symmetryGroup_firstColumn F k hB1 hNL hLmem hc ha hcop
  have hdetm := det_entries_of_mem_symmetryGroup hm
  rw [m00, m01, m10, m11] at hdetm
  have hdetγR : (γ 0 0 : ℝ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetγ
  set t : ℤ := D * γ 0 1 - B * γ 1 1 with ht
  have hmap : ∀ i j, (mapGL ℝ γ : GL (Fin 2) ℝ) i j = ((γ i j : ℤ) : ℝ) := by
    intro i j; simp
  have heq : mapGL ℝ γ = m * glUpperUnipotent ((t : ℤ) : ℝ) := by
    obtain ⟨g00, g01, g10, g11⟩ := glFinTwo_mul_glUpperUnipotent_apply m ((t : ℤ) : ℝ)
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [g00, m00]; simp
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      rw [hmap, g01, m00, m01, ht]
      push_cast
      linear_combination -(γ 0 1 : ℝ) * hdetm + (B : ℝ) * hdetγR
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]
      rw [g10, m10]; simp
    · simp only [Fin.mk_one, Fin.isValue]
      rw [hmap, g11, m10, m11, ht]
      push_cast
      linear_combination -(γ 1 1 : ℝ) * hdetm + (D : ℝ) * hdetγR
  rw [heq]
  exact (symmetryGroup _).mul_mem hm (glUpperUnipotent_intCast_mem_symmetryGroup _ _)

end Level

/-- **The symmetry group contains a `Γ₁(N′)`** (Cummins (2002), Prop. 2.1 in its `Γ₁` form). For
a replicable family of period `N > 0` satisfying the prime Hecke identity (proved on the LR side)
whose member `k` is not injective modulo translations (proved on the LR side), the symmetry group of
`f = qSeriesFun (F.c k)` contains `Γ₁(N′)` for some `N′ > 0` divisible by `N`. -/
theorem ReplicableFamily.exists_gamma1GL_le_symmetryGroup {N : ℕ} (hN : 0 < N)
    (F : ReplicableFamily N) (k : ℕ) (hB1 : PrimeHeckeIdentity F k)
    (hD7 : ¬ IsInjectiveModTranslations (qSeriesFun (F.c k))) :
    ∃ N' : ℕ, 0 < N' ∧ N ∣ N' ∧ gamma1GL N' ≤ symmetryGroup (qSeriesFun (F.c k)) := by
  obtain ⟨L, hL0, hNL, hLmem⟩ := exists_glLowerUnipotent_mem_symmetryGroup F k hN hB1 hD7
  exact ⟨L.natAbs, Int.natAbs_pos.mpr hL0, Int.natCast_dvd.mp hNL,
    gamma1GL_le_symmetryGroup_of_lowerUnipotent F k hB1 hNL hLmem⟩

end VOA.Moonshine.ConwayNorton
