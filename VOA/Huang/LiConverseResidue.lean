import VOA.Modules.FZBimodule
import VOA.Modules.Translation
import VOA.Foundations.IotaZExpansion
import Mathlib.Algebra.Polynomial.Laurent

/-! # A residue calculus for weak modules, with Laurent-polynomial test functions

For a weak module `A` on `M`, a state `a` and `w ∈ M`, `res A a w φ` is the residue
`Res_z φ(z) Y_M(a,z) w = ∑ₙ φₙ a₍ₙ₎ w`, for a Laurent polynomial `φ`. It is linear in
`φ`, `a` and `w`. The divided derivatives `dd i` (`T m ↦ C(m,i) T (m-i)`) satisfy the
Leibniz rule (from the generalized Vandermonde identity `cbz_vandermonde`).

The module Jacobi identity becomes a single statement `res_jacobi` with arbitrary
Laurent-polynomial test functions `f, g` and an integer `l`. At `l = 0` it is the
commutator formula, at `l = -1` the iterate formula used in Zhu's associativity argument.
This turns the Frenkel–Zhu bimodule computations into identities in the commutative ring
`ℂ[T;T⁻¹]`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiConverse

open VOA VOA.FZ LaurentPolynomial
open scoped BigOperators

/-- Constants in `ℂ[T;T⁻¹]` (avoids the clash with `VOA.C`). -/
scoped notation "LC" => LaurentPolynomial.C

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## The residue pairing -/

section Res

variable (A : WeakModule W M)

/-- `res A a w φ = Res_z φ(z) Y_M(a,z) w = ∑ₙ φₙ a₍ₙ₎ w`. -/
noncomputable def res (a : V) (w : M) : ℂ[T;T⁻¹] →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ (fun n : ℤ => mode (A.YM a) n w)

theorem res_single (a : V) (w : M) (n : ℤ) (c : ℂ) :
    res A a w (Finsupp.single n c) = c • mode (A.YM a) n w :=
  Finsupp.linearCombination_single ℂ _ _

theorem res_CT (a : V) (w : M) (n : ℤ) (c : ℂ) :
    res A a w (LC c * T n) = c • mode (A.YM a) n w := by
  rw [← single_eq_C_mul_T]; exact res_single A a w n c

theorem res_T (a : V) (w : M) (n : ℤ) : res A a w (T n) = mode (A.YM a) n w := by
  simpa using res_CT A a w n 1

theorem res_add_w (a : V) (w w' : M) (φ : ℂ[T;T⁻¹]) :
    res A a (w + w') φ = res A a w φ + res A a w' φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]; abel
  | C_mul_T n c => rw [res_CT, res_CT, res_CT, map_add, smul_add]

theorem res_smul_w (a : V) (c : ℂ) (w : M) (φ : ℂ[T;T⁻¹]) :
    res A a (c • w) φ = c • res A a w φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, smul_add]
  | C_mul_T n d => rw [res_CT, res_CT, map_smul, smul_comm]

theorem res_zero_w (a : V) (φ : ℂ[T;T⁻¹]) : res A a 0 φ = 0 := by
  simpa using res_smul_w A a 0 0 φ

theorem res_add_a (a b : V) (w : M) (φ : ℂ[T;T⁻¹]) :
    res A (a + b) w φ = res A a w φ + res A b w φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]; abel
  | C_mul_T n c =>
    rw [res_CT, res_CT, res_CT, map_add, mode_add, LinearMap.add_apply, smul_add]

theorem res_smul_a (c : ℂ) (a : V) (w : M) (φ : ℂ[T;T⁻¹]) :
    res A (c • a) w φ = c • res A a w φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, smul_add]
  | C_mul_T n d =>
    rw [res_CT, res_CT, map_smul, mode_smul, LinearMap.smul_apply, smul_comm]

theorem res_zero_a (w : M) (φ : ℂ[T;T⁻¹]) : res A 0 w φ = 0 := by
  simpa using res_smul_a A 0 0 w φ

theorem res_sum_w {ι : Type*} (s : Finset ι) (a : V) (w : ι → M) (φ : ℂ[T;T⁻¹]) :
    res A a (∑ i ∈ s, w i) φ = ∑ i ∈ s, res A a (w i) φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [res_zero_w]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, res_add_w, ih]

theorem res_sum_a {ι : Type*} (s : Finset ι) (a : ι → V) (w : M) (φ : ℂ[T;T⁻¹]) :
    res A (∑ i ∈ s, a i) w φ = ∑ i ∈ s, res A (a i) w φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [res_zero_a]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, res_add_a, ih]

/-- Lower truncation of the module modes, transported to residues: shifting a test
function far enough to the right kills the residue. -/
theorem res_shift_eventually_zero (a : V) (w : M) (φ : ℂ[T;T⁻¹]) :
    ∃ J : ℤ, ∀ j : ℤ, J ≤ j → res A a w (T j * φ) = 0 := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨J, hJ⟩ := hp
    obtain ⟨J', hJ'⟩ := hq
    exact ⟨max J J', fun j hj => by
      rw [mul_add, map_add, hJ j (le_trans (le_max_left _ _) hj),
        hJ' j (le_trans (le_max_right _ _) hj), add_zero]⟩
  | C_mul_T n c =>
    obtain ⟨N, hN⟩ := A.truncation a w
    refine ⟨N - n, fun j hj => ?_⟩
    rw [show T j * (LC c * T n) = LC c * T (j + n) by rw [T_add]; ring, res_CT,
      hN _ (by omega), smul_zero]

end Res

/-! ## Divided derivatives -/

section DD

/-- The divided derivative `T m ↦ C(m,i) T^(m-i)` (zero for `i < 0`). -/
noncomputable def dd (i : ℤ) : ℂ[T;T⁻¹] →ₗ[ℂ] ℂ[T;T⁻¹] :=
  Finsupp.linearCombination ℂ (fun m : ℤ => cbz m i • (T (m - i) : ℂ[T;T⁻¹]))

theorem dd_single (i m : ℤ) (c : ℂ) :
    dd i (Finsupp.single m c) = c • cbz m i • (T (m - i) : ℂ[T;T⁻¹]) :=
  Finsupp.linearCombination_single ℂ _ _

theorem dd_CT (i m : ℤ) (c : ℂ) :
    dd i (LC c * T m) = LC (c * cbz m i) * T (m - i) := by
  rw [← single_eq_C_mul_T, dd_single, smul_smul, smul_eq_C_mul]

theorem dd_T (i m : ℤ) : dd i (T m) = LC (cbz m i) * T (m - i) := by
  simpa using dd_CT i m 1

theorem dd_neg {i : ℤ} (hi : i < 0) (φ : ℂ[T;T⁻¹]) : dd i φ = 0 := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, add_zero]
  | C_mul_T n c => rw [dd_CT, cbz_apply_neg n hi, mul_zero, map_zero, zero_mul]

theorem dd_zero (φ : ℂ[T;T⁻¹]) : dd 0 φ = φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq]
  | C_mul_T n c => rw [dd_CT, cbz_zero, mul_one, sub_zero]

/-- The generalized Vandermonde identity on a finite range. -/
theorem vandermonde_range (m n : ℤ) (i : ℕ) :
    ∑ s ∈ Finset.range (i + 1), cbz m s * cbz n ((i : ℤ) - s) = cbz (m + n) i := by
  rw [← cbz_vandermonde, cbzConvol]
  symm
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (i + 1)).map Nat.castEmbedding)]
  · rw [Finset.sum_map]; rfl
  · intro s hs
    rw [Function.mem_support] at hs
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply]
    by_contra hcon
    apply hs
    rcases lt_or_ge s 0 with h | h
    · rw [cbz_apply_neg m h, zero_mul]
    · have : (i : ℤ) < s := by
        by_contra h'
        exact hcon ⟨s.toNat, by omega, by omega⟩
      rw [cbz_apply_neg n (by omega), mul_zero]

/-- **Leibniz rule for divided derivatives.** -/
theorem dd_mul (i : ℕ) (f g : ℂ[T;T⁻¹]) :
    dd i (f * g) = ∑ s ∈ Finset.range (i + 1), dd s f * dd ((i : ℤ) - s) g := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_mul, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_add, add_mul]
  | C_mul_T m c =>
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [mul_add, map_add, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_add, mul_add]
    | C_mul_T n d =>
      rw [show LC c * T m * (LC d * T n) = LC (c * d) * T (m + n) by
        rw [T_add, map_mul]; ring, dd_CT]
      simp only [dd_CT]
      have h : ∀ s ∈ Finset.range (i + 1),
          LC (c * cbz m (s : ℤ)) * T (m - s) * (LC (d * cbz n ((i : ℤ) - s)) * T (n - (i - s)))
            = LC (c * d) * LC (cbz m s * cbz n ((i : ℤ) - s)) * T (m + n - i) := by
        intro s _
        rw [show m + n - (i : ℤ) = (m - s) + (n - (i - s)) by ring, T_add]
        simp only [map_mul]; ring
      rw [Finset.sum_congr rfl h, ← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, vandermonde_range,
        ← map_mul]

/-- The variable `z`. -/
noncomputable abbrev z : ℂ[T;T⁻¹] := T 1

theorem z_mul_T (n : ℤ) : z * T n = T (n + 1) := by
  rw [z, ← T_add, add_comm]

theorem cbz_nat_self (K : ℕ) : cbz (K : ℤ) (K : ℤ) = 1 := by
  rw [cbz_natCast_eq_choose le_rfl, Nat.choose_self, Nat.cast_one]

theorem dd_one_add_z_zero : dd 0 (1 + z) = 1 + z := dd_zero _

theorem dd_one_add_z_one : dd 1 (1 + z) = 1 := by
  rw [map_add, show (1 : ℂ[T;T⁻¹]) = T 0 from T_zero.symm, dd_T, dd_T,
    cbz_apply_neg 0 (show (0 : ℤ) - 1 < 0 by norm_num) |> fun _ => cbz_zero_left 1]
  rw [if_neg (by norm_num), map_zero, zero_mul, zero_add,
    show (1 : ℤ) - 1 = 0 by norm_num, T_zero, mul_one]
  have : cbz 1 1 = 1 := by simpa using cbz_nat_self 1
  rw [this, map_one]

theorem dd_one_add_z_ge_two {t : ℤ} (ht : 2 ≤ t) : dd t (1 + z) = 0 := by
  rw [map_add, show (1 : ℂ[T;T⁻¹]) = T 0 from T_zero.symm, dd_T, dd_T, cbz_zero_left,
    if_neg (by omega), cbz_lt (by norm_num) (by omega)]
  simp

theorem dd_one_add_z_pow (K : ℕ) (s : ℕ) :
    dd s ((1 + z) ^ K) = LC (cbz K s) * (1 + z) ^ (K - s) := by
  induction K generalizing s with
  | zero =>
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [dd_zero]
    · have h1 : dd (s : ℤ) (1 : ℂ[T;T⁻¹]) = 0 := by
        rw [← T_zero, dd_T, cbz_zero_left, if_neg (by omega)]; simp
      rw [pow_zero, h1, Nat.cast_zero, cbz_lt (p := 0) (c := (s : ℤ)) le_rfl (by omega)]
      simp
  | succ K ih =>
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [dd_zero]
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    rw [pow_succ, dd_mul, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun s' hs' => by
      rw [Finset.mem_range] at hs'
      rw [dd_one_add_z_ge_two (by push_cast; omega), mul_zero])]
    rw [show ((s₀ + 1 : ℕ) : ℤ) - (s₀ : ℕ) = 1 by push_cast; ring,
      show ((s₀ + 1 : ℕ) : ℤ) - ((s₀ + 1 : ℕ) : ℤ) = 0 by ring,
      dd_one_add_z_one, dd_one_add_z_zero, ih, ih, zero_add, mul_one]
    have hp : cbz ((K + 1 : ℕ) : ℤ) ((s₀ + 1 : ℕ) : ℤ)
        = cbz (K : ℤ) ((s₀ + 1 : ℕ) : ℤ) + cbz (K : ℤ) (s₀ : ℤ) := by
      have := cbz_pascal_up (K : ℤ) ((s₀ + 1 : ℕ) : ℤ)
      push_cast at this ⊢
      simpa using this
    rw [hp, show K + 1 - (s₀ + 1) = K - s₀ by omega, map_add]
    rcases lt_or_ge s₀ K with h | h
    · rw [show K - s₀ = (K - (s₀ + 1)) + 1 by omega, pow_succ]; ring
    · rw [show (((s₀ + 1 : ℕ) : ℤ)) = (s₀ : ℤ) + 1 by push_cast; ring,
        cbz_lt (p := (K : ℤ)) (c := (s₀ : ℤ) + 1) (by positivity) (by omega)]
      simp

end DD


/-! ## The module Jacobi identity with Laurent-polynomial test functions -/

section Jacobi

variable (A : WeakModule W M)

/-- Left summand of the residue Jacobi identity. -/
noncomputable def jacL (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (j : ℤ) : M :=
  (negOnePow j * cbz l j) •
    (res A a (res A b w (T j * g)) (T (l - j) * f)
      - negOnePow l • res A b (res A a w (T j * f)) (T (l - j) * g))

/-- Right summand of the residue Jacobi identity. -/
noncomputable def jacR (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (i : ℤ) : M :=
  res A (W.smul a (l + i) b) w (dd i f * g)

theorem jacL_support_finite (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (Function.support (jacL A a b w l f g)).Finite := by
  obtain ⟨J₁, hJ₁⟩ := res_shift_eventually_zero A b w g
  obtain ⟨J₂, hJ₂⟩ := res_shift_eventually_zero A a w f
  apply (Set.finite_Icc 0 (max J₁ J₂)).subset
  intro j hj
  rw [Function.mem_support] at hj
  refine ⟨not_lt.mp fun h => hj ?_, not_lt.mp fun h => hj ?_⟩
  · simp [jacL, cbz_apply_neg l h]
  · rw [jacL, hJ₁ j (le_trans (le_max_left _ _) h.le), hJ₂ j (le_trans (le_max_right _ _) h.le),
      res_zero_w, res_zero_w, smul_zero, sub_zero, smul_zero]

theorem jacR_support_finite (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (Function.support (jacR A a b w l f g)).Finite := by
  obtain ⟨N, hN⟩ := W.regularity a b
  apply (Set.finite_Icc 0 (N - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [jacR, dd_neg h, zero_mul, map_zero]
  · have h0 : W.smul a (l + i) b = 0 := hN _ (by omega)
    rw [jacR, h0, res_zero_a]

theorem jacL_add_left (a b : V) (w : M) (l : ℤ) (f f' g : ℂ[T;T⁻¹]) (j : ℤ) :
    jacL A a b w l (f + f') g j = jacL A a b w l f g j + jacL A a b w l f' g j := by
  simp only [jacL, mul_add, map_add, res_add_w, smul_add, smul_sub]
  abel

theorem jacL_add_right (a b : V) (w : M) (l : ℤ) (f g g' : ℂ[T;T⁻¹]) (j : ℤ) :
    jacL A a b w l f (g + g') j = jacL A a b w l f g j + jacL A a b w l f g' j := by
  simp only [jacL, mul_add, map_add, res_add_w, smul_add, smul_sub]
  abel

theorem jacR_add_left (a b : V) (w : M) (l : ℤ) (f f' g : ℂ[T;T⁻¹]) (i : ℤ) :
    jacR A a b w l (f + f') g i = jacR A a b w l f g i + jacR A a b w l f' g i := by
  simp only [jacR, map_add, add_mul]

theorem jacR_add_right (a b : V) (w : M) (l : ℤ) (f g g' : ℂ[T;T⁻¹]) (i : ℤ) :
    jacR A a b w l f (g + g') i = jacR A a b w l f g i + jacR A a b w l f g' i := by
  simp only [jacR, map_add, mul_add]

theorem jac_monomial (a b : V) (w : M) (l : ℤ) (c d : ℂ) (m n : ℤ) :
    (∑ᶠ j : ℤ, jacL A a b w l (LC c * T m) (LC d * T n) j)
      = ∑ᶠ i : ℤ, jacR A a b w l (LC c * T m) (LC d * T n) i := by
  have hL : ∀ j, jacL A a b w l (LC c * T m) (LC d * T n) j = (c * d) •
      ((negOnePow j * cbz l j) •
        (mode (A.YM a) (l + m - j) (mode (A.YM b) (n + j) w)
          - negOnePow l • mode (A.YM b) (l + n - j) (mode (A.YM a) (m + j) w))) := by
    intro j
    have e1 : T j * (LC d * T n) = LC d * T (n + j) := by rw [T_add]; ring
    have e2 : T (l - j) * (LC c * T m) = LC c * T (l + m - j) := by
      rw [show l + m - j = (l - j) + m by ring, T_add]; ring
    have e3 : T j * (LC c * T m) = LC c * T (m + j) := by rw [T_add]; ring
    have e4 : T (l - j) * (LC d * T n) = LC d * T (l + n - j) := by
      rw [show l + n - j = (l - j) + n by ring, T_add]; ring
    rw [jacL, e1, e2, e3, e4, res_CT, res_CT, res_CT, res_CT]
    simp only [map_smul]
    module
  have hR : ∀ i, jacR A a b w l (LC c * T m) (LC d * T n) i = (c * d) •
      (cbz m i • mode (A.YM (W.smul a (l + i) b)) (m + n - i) w) := by
    intro i
    rw [jacR, dd_CT, show LC (c * cbz m i) * T (m - i) * (LC d * T n)
        = LC (c * cbz m i * d) * T (m + n - i) by
      rw [show m + n - i = (m - i) + n by ring, T_add]; simp only [map_mul]; ring, res_CT,
      smul_smul]
    congr 1; ring
  rw [finsum_congr hL, finsum_congr hR, ← smul_finsum, ← smul_finsum, A.jacobi]

/-- **The module Jacobi identity with test functions.** For Laurent polynomials
`f, g` and `l ∈ ℤ`:
`∑ⱼ (-1)ʲ C(l,j) [Res(z^{l-j}f, a) Res(z^j g, b) w − (-1)^l Res(z^{l-j}g, b) Res(z^j f, a) w]`
`= ∑ᵢ Res((∂^{(i)}f)·g, a₍ₗ₊ᵢ₎b) w`. -/
theorem res_jacobi (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (∑ᶠ j : ℤ, jacL A a b w l f g j) = ∑ᶠ i : ℤ, jacR A a b w l f g i := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [finsum_congr (jacL_add_left A a b w l p q g), finsum_congr (jacR_add_left A a b w l p q g),
      finsum_add_distrib (jacL_support_finite A a b w l p g) (jacL_support_finite A a b w l q g),
      finsum_add_distrib (jacR_support_finite A a b w l p g) (jacR_support_finite A a b w l q g),
      hp, hq]
  | C_mul_T m c =>
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [finsum_congr (jacL_add_right A a b w l _ p q),
        finsum_congr (jacR_add_right A a b w l _ p q),
        finsum_add_distrib (jacL_support_finite A a b w l _ p)
          (jacL_support_finite A a b w l _ q),
        finsum_add_distrib (jacR_support_finite A a b w l _ p)
          (jacR_support_finite A a b w l _ q), hp, hq]
    | C_mul_T n d => exact jac_monomial A a b w l c d m n

end Jacobi

/-! ## Bridges to the Frenkel–Zhu operations -/

section Bridge

variable (A : WeakModule W M)

theorem one_add_z_pow_eq (K : ℕ) :
    (1 + z) ^ K = ∑ i ∈ Finset.range (K + 1), LC (cbz (K : ℤ) (i : ℤ)) * T (i : ℤ) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [one_pow, mul_one, cbz_natCast_eq_choose (by omega), z, T_pow, mul_one, map_natCast]
  ring

theorem res_binom (a : V) (w : M) (K : ℕ) (s : ℤ) :
    res A a w ((1 + z) ^ K * T s)
      = ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) • mode (A.YM a) ((i : ℤ) + s) w := by
  rw [one_add_z_pow_eq, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← T_add, res_CT]

theorem fzLeft_eq_res (p : ℕ) (a : V) (w : M) :
    fzLeft A p a w = res A a w ((1 + z) ^ p * T (-1)) := by
  rw [res_binom, fzLeft]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (i : ℤ) + -1 = (i : ℤ) - 1 by ring]

theorem fzRes_eq_res (p k : ℕ) (a : V) (w : M) :
    fzRes A p k a w = res A a w ((1 + z) ^ (p + k) * T (-2 - k)) := by
  rw [res_binom, fzRes]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [show (i : ℤ) + (-2 - k) = (i : ℤ) - 2 - k by ring]

theorem fzRight_eq_res {p : ℕ} (hp : 1 ≤ p) (a : V) (w : M) :
    fzRight A p a w = res A a w ((1 + z) ^ (p - 1) * T (-1)) := by
  rw [res_binom, fzRight, show p - 1 + 1 = p by omega, Finset.sum_range_succ,
    show ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hp]; ring,
    cbz_lt (p := ((p - 1 : ℕ) : ℤ)) (c := (p : ℤ)) (by positivity) (by omega), zero_smul,
    add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (i : ℤ) + -1 = (i : ℤ) - 1 by ring]

/-- `a ∗ w − w ∗ a = Res (1+z)^{p-1} Y(a,z) w` for `p ≥ 1`. -/
theorem fzLeft_sub_fzRight_eq_res {p : ℕ} (hp : 1 ≤ p) (a : V) (w : M) :
    fzLeft A p a w - fzRight A p a w = res A a w ((1 + z) ^ (p - 1)) := by
  rw [fzLeft_sub_fzRight, show (1 + z) ^ (p - 1) = (1 + z) ^ (p - 1) * T 0 by
    rw [T_zero, mul_one], res_binom, show p - 1 + 1 = p by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_zero, show ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hp]; ring]

/-- `(L₋₁a)₍ₙ₎ = −n a₍ₙ₋₁₎`, in residue form: `Res φ Y(L₋₁a)` is `−Res φ' Y(a)`. -/
theorem res_L_neg_one (a : V) (w : M) (φ : ℂ[T;T⁻¹]) :
    res A (W.L (-1) a) w φ = -res A a w (dd 1 φ) := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, neg_add]
  | C_mul_T n c =>
    rw [res_CT, dd_CT, res_CT, ← WeakModule.act_def, act_T_covariance, WeakModule.act_def]
    have : cbz n 1 = (n : ℂ) := by
      rw [cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]
    rw [this, smul_smul, ← neg_smul]
    congr 1; ring

end Bridge

end VOA.Huang.LiConverse
