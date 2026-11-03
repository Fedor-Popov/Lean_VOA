import VOA.Huang.LiConverseInvolution
import VOA.Huang.LiRegularThreeW

/-! # The inversion frame change for the restricted three-point identities

Li's regular representation `D_{P(z)}(M)` realizes a trilinear form on `M × P₂ × P₃'` with `M` at
`∞` (opposite modes), `P₃'` at `0` and `P₂` at `z`.  The target intertwiner wants `P₃` at `∞`.  The
inversion `t ↦ 1/t` (which fixes `z = −1`) exchanges `0 ↔ ∞`, and on the two exchanged slots it is
the defining twist of the opposite modes (`oppB_homog`) and its inverse (`mode_eq_oppB_twist`).

For a bilinear form `H` on `E × M` and a fixed `P₂`-zero-mode term `Z`, this file proves that the
*restricted* identities (test functions vanishing at `−1` to order `≥ wt − 1`, so that only the
`P₂`-zero mode survives) transfer from the source frame to the inverted frame, by induction on the
weight (the `L(1)`-tail of the twist is strictly restricted) — `frame_change`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra LaurentPolynomial
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M E : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup E] [Module ℂ E]

/-! ## Residues against ordinary modes -/

/-- `Res_x φ(x) Y(a, x)` for a Laurent test function: `Σₙ φₙ aₙ`. -/
noncomputable def nres (A : WeakModule W M) (a : V) (φ : ℂ[T;T⁻¹]) : Module.End ℂ M :=
  Finsupp.linearCombination ℂ (fun n => mode (A.YM a) n) φ

theorem nres_CT (A : WeakModule W M) (a : V) (c : ℂ) (n : ℤ) :
    nres A a (LaurentPolynomial.C c * T n) = c • mode (A.YM a) n := by
  rw [nres, ← single_eq_C_mul_T, Finsupp.linearCombination_single]

theorem nres_add (A : WeakModule W M) (a : V) (φ ψ : ℂ[T;T⁻¹]) :
    nres A a (φ + ψ) = nres A a φ + nres A a ψ := map_add _ _ _

theorem nres_smul (A : WeakModule W M) (a : V) (c : ℂ) (φ : ℂ[T;T⁻¹]) :
    nres A a (c • φ) = c • nres A a φ := map_smul _ _ _

theorem nres_sub (A : WeakModule W M) (a : V) (φ ψ : ℂ[T;T⁻¹]) :
    nres A a (φ - ψ) = nres A a φ - nres A a ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, nres_add, nres_smul, neg_one_smul, ← sub_eq_add_neg]

theorem nres_T (A : WeakModule W M) (a : V) (n : ℤ) : nres A a (T n) = mode (A.YM a) n := by
  simpa using nres_CT A a 1 n

theorem nres_sum (A : WeakModule W M) (a : V) {ι : Type*} (s : Finset ι) (f : ι → ℂ[T;T⁻¹]) :
    nres A a (∑ i ∈ s, f i) = ∑ i ∈ s, nres A a (f i) := map_sum _ _ _

theorem nres_add_a (A : WeakModule W M) (a b : V) (φ : ℂ[T;T⁻¹]) :
    nres A (a + b) φ = nres A a φ + nres A b φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [nres_add, nres_add, nres_add, hp, hq]; abel
  | C_mul_T n c => rw [nres_CT, nres_CT, nres_CT, map_add, mode_add, smul_add]

theorem nres_smul_a (A : WeakModule W M) (c : ℂ) (a : V) (φ : ℂ[T;T⁻¹]) :
    nres A (c • a) φ = c • nres A a φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [nres_add, nres_add, hp, hq, smul_add]
  | C_mul_T n d => rw [nres_CT, nres_CT, map_smul, mode_smul, smul_comm]

/-- The vacuum has the same residues as an ordinary and as an opposite mode system. -/
theorem nres_vacuum_eq (N : OrdVModule W M) (φ : ℂ[T;T⁻¹]) :
    nres N.toWeakModule W.vacuum φ = (oppBase N).bres W.vacuum φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [nres_add, hf, hg, OppBase.bres_add]
  | C_mul_T n c =>
    rw [nres_CT, OppBase.bres_CT]
    congr 1
    ext y
    change mode (N.YM W.vacuum) n y = oppB N W.vacuum n y
    rw [oppB_vacuum, N.vacuum_YM, mode_one]
    by_cases h : n = -1
    · subst h; simp
    · rw [if_neg h, if_neg (by omega)]; rfl

/-! ## The inversion of test functions -/

/-- `ι_c φ(s) = s^c φ(1/s)`. -/
noncomputable def inv (c : ℤ) (φ : ℂ[T;T⁻¹]) : ℂ[T;T⁻¹] := T c * invert φ

theorem inv_CT (c : ℤ) (d : ℂ) (n : ℤ) :
    inv c (LaurentPolynomial.C d * T n) = LaurentPolynomial.C d * T (c - n) := by
  rw [inv, map_mul, invert_C, invert_T, mul_left_comm, ← T_add, ← sub_eq_add_neg]

theorem inv_add (c : ℤ) (φ ψ : ℂ[T;T⁻¹]) : inv c (φ + ψ) = inv c φ + inv c ψ := by
  rw [inv, map_add, mul_add]; rfl

/-- **The opposite modes as twisted ordinary modes**, on test functions. -/
theorem oppBres_twist (N : OrdVModule W M) {K : ℕ} {a : V} (ha : a ∈ W.grading K)
    (φ : ℂ[T;T⁻¹]) :
    (oppBase N).bres a φ = (-1 : ℂ) ^ K • ∑ j ∈ Finset.range (K + 1),
      ((j.factorial : ℂ)⁻¹) • nres N.toWeakModule ((W.L 1 ^ j) a)
        (inv (2 * (K : ℤ) - 2 - j) φ) := by
  induction φ using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    rw [OppBase.bres_add, hf, hg, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inv_add, nres_add, smul_add]
  | C_mul_T n c =>
    rw [OppBase.bres_CT]
    change c • oppB N a n = _
    rw [oppB_homog N ha, Int.toNat_natCast]
    simp only [inv_CT, nres_CT, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * (K : ℤ) - 2 - j - n = 2 * K - n - 2 - j by ring]
    congr 1; rw [zpow_natCast]; ring

/-- **The ordinary modes as twisted opposite modes**, on test functions. -/
theorem nres_twist (N : OrdVModule W M) {K : ℕ} {a : V} (ha : a ∈ W.grading K)
    (φ : ℂ[T;T⁻¹]) :
    nres N.toWeakModule a φ = (-1 : ℂ) ^ K • ∑ j ∈ Finset.range (K + 1),
      ((j.factorial : ℂ)⁻¹) • (oppBase N).bres ((W.L 1 ^ j) a)
        (inv (2 * (K : ℤ) - 2 - j) φ) := by
  induction φ using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    rw [nres_add, hf, hg, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inv_add, OppBase.bres_add, smul_add]
  | C_mul_T n c =>
    rw [nres_CT]
    change c • mode (N.YM a) n = _
    rw [mode_eq_oppB_twist N ha, Int.toNat_natCast]
    simp only [inv_CT, OppBase.bres_CT, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * (K : ℤ) - 2 - j - n = 2 * K - n - 2 - j by ring]
    congr 1; rw [zpow_natCast]; ring

/-! ## Evaluation at `−1` -/

/-- Evaluation of a Laurent polynomial at `−1`. -/
noncomputable def ev1 : ℂ[T;T⁻¹] →+* ℂ := LaurentPolynomial.eval₂ (RingHom.id ℂ) (-1 : ℂˣ)

theorem ev1_T (n : ℤ) : ev1 (T n : ℂ[T;T⁻¹]) = (-1 : ℂ) ^ n := by
  rw [ev1, eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one]

theorem ev1_C (c : ℂ) : ev1 (LaurentPolynomial.C c) = c := by
  rw [ev1, eval₂_C]; rfl

theorem ev1_X_add_one : ev1 (Polynomial.toLaurent (Polynomial.X + 1 : ℂ[X])) = 0 := by
  rw [map_add, Polynomial.toLaurent_X, map_one, map_add, ev1_T, map_one]; norm_num

theorem ev1_invert (φ : ℂ[T;T⁻¹]) : ev1 (invert φ) = ev1 φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | C_mul_T n c =>
    rw [map_mul, invert_C, invert_T, map_mul, map_mul, ev1_T, ev1_T, zpow_neg]
    congr 1
    rcases Int.even_or_odd n with h | h
    · rw [h.neg_one_zpow]; norm_num
    · rw [h.neg_one_zpow]; norm_num

/-! ## The frame change -/

section Frame

variable (A : OrdVModule W M) (Q : OrdVModule W E) (H : E →ₗ[ℂ] M →ₗ[ℂ] ℂ)

/-- The source difference `Res φ (⟨α, Y°_M(a)·⟩ − ⟨Y_{Q}(a)ᵀα, ·⟩)`. -/
noncomputable def sdiff (a : V) (φ : ℂ[T;T⁻¹]) (g : E) (w : M) : ℂ :=
  H g ((oppBase A).bres a φ w) - H (nres Q.toWeakModule a φ g) w

/-- The target difference `Res ψ (⟨Y°_Q(b)ᵀ λ, ·⟩ − ⟨λ, Y_M(b)·⟩)`. -/
noncomputable def tdiff (b : V) (ψ : ℂ[T;T⁻¹]) (g : E) (w : M) : ℂ :=
  H ((oppBase Q).bres b ψ g) w - H g (nres A.toWeakModule b ψ w)

theorem sdiff_add (a : V) (φ φ' : ℂ[T;T⁻¹]) (g : E) (w : M) :
    sdiff A Q H a (φ + φ') g w = sdiff A Q H a φ g w + sdiff A Q H a φ' g w := by
  simp only [sdiff, OppBase.bres_add, nres_add, LinearMap.add_apply, map_add]; ring

theorem sdiff_smul (a : V) (c : ℂ) (φ : ℂ[T;T⁻¹]) (g : E) (w : M) :
    sdiff A Q H a (c • φ) g w = c * sdiff A Q H a φ g w := by
  simp only [sdiff, OppBase.bres_smul, nres_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

theorem tdiff_add (b : V) (ψ ψ' : ℂ[T;T⁻¹]) (g : E) (w : M) :
    tdiff A Q H b (ψ + ψ') g w = tdiff A Q H b ψ g w + tdiff A Q H b ψ' g w := by
  simp only [tdiff, OppBase.bres_add, nres_add, LinearMap.add_apply, map_add]; ring

theorem tdiff_smul (b : V) (c : ℂ) (ψ : ℂ[T;T⁻¹]) (g : E) (w : M) :
    tdiff A Q H b (c • ψ) g w = c * tdiff A Q H b ψ g w := by
  simp only [tdiff, OppBase.bres_smul, nres_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

theorem tdiff_add_a (b b' : V) (ψ : ℂ[T;T⁻¹]) (g : E) (w : M) :
    tdiff A Q H (b + b') ψ g w = tdiff A Q H b ψ g w + tdiff A Q H b' ψ g w := by
  simp only [tdiff, OppBase.bres_add_a, nres_add_a, LinearMap.add_apply, map_add]; ring

theorem tdiff_smul_a (c : ℂ) (b : V) (ψ : ℂ[T;T⁻¹]) (g : E) (w : M) :
    tdiff A Q H (c • b) ψ g w = c * tdiff A Q H b ψ g w := by
  simp only [tdiff, OppBase.bres_smul_a, nres_smul_a, LinearMap.smul_apply, map_smul,
    smul_eq_mul]; ring

theorem tdiff_zero_a (ψ : ℂ[T;T⁻¹]) (g : E) (w : M) : tdiff A Q H 0 ψ g w = 0 := by
  have := tdiff_smul_a A Q H 0 0 ψ g w
  rw [zero_smul, zero_mul] at this; exact this

theorem tdiff_vacuum (ψ : ℂ[T;T⁻¹]) (g : E) (w : M) : tdiff A Q H W.vacuum ψ g w = 0 := by
  rw [tdiff, ← nres_vacuum_eq, nres_vacuum_eq A]
  induction ψ using LaurentPolynomial.induction_on' with
  | add f g' hf hg =>
    rw [nres_add, OppBase.bres_add, LinearMap.add_apply, LinearMap.add_apply, map_add, map_add,
      LinearMap.add_apply]
    linear_combination hf + hg
  | C_mul_T n c =>
    rw [nres_CT, OppBase.bres_CT, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      map_smul, LinearMap.smul_apply]
    change c • H (mode (Q.YM W.vacuum) n g) w - c • H g (oppB A W.vacuum n w) = 0
    rw [oppB_vacuum, Q.vacuum_YM, mode_one]
    by_cases h : n = -1
    · subst h; simp
    · rw [if_neg h, if_neg (by omega)]; simp

/-- Weight-`0` and negative-weight states have vanishing target difference. -/
theorem tdiff_low {k : ℤ} (hk : k ≤ 0) {b : V} (hb : b ∈ W.grading k) (ψ : ℂ[T;T⁻¹]) (g : E)
    (w : M) : tdiff A Q H b ψ g w = 0 := by
  rcases lt_or_eq_of_le hk with hk | rfl
  · have : b = 0 := by
      have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hb (j := 0) (by omega)
      simpa using h
    subst this; exact tdiff_zero_a A Q H ψ g w
  · rw [W.vacuum_grade, Submodule.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [tdiff_smul_a, tdiff_vacuum, mul_zero]

/-- The inversion identity `sdiff = (−1)^{K−1} Σⱼ (1/j!) tdiff(L(1)ʲa, ιⱼ φ)`. -/
theorem sdiff_eq_tdiff {K : ℕ} {a : V} (ha : a ∈ W.grading K) (φ : ℂ[T;T⁻¹]) (g : E) (w : M) :
    sdiff A Q H a φ g w = -((-1 : ℂ) ^ K * ∑ j ∈ Finset.range (K + 1),
      (j.factorial : ℂ)⁻¹ * tdiff A Q H ((W.L 1 ^ j) a) (inv (2 * (K : ℤ) - 2 - j) φ) g w) := by
  rw [sdiff, oppBres_twist A ha, nres_twist Q ha]
  simp only [tdiff, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, map_smul,
    map_sum, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem toL_X_add_one_pow (k : ℕ) :
    Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) = (T 1 + 1) ^ k := by
  rw [map_pow, map_add, Polynomial.toLaurent_X, map_one]

/-- The inversion of the chosen preimage. -/
theorem inv_preimage (k j : ℕ) (σ : ℂ[T;T⁻¹]) :
    inv (2 * ((k + 1 : ℕ) : ℤ) - 2 - j)
        (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * (T k * invert σ))
      = Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * (T (-(j : ℤ)) * σ) := by
  rw [inv, toL_X_add_one_pow, map_mul, map_mul, map_pow, map_add, map_one, invert_T,
    show invert (invert σ) = σ from involutive_invert σ, invert_T]
  have h1 : (T (2 * ((k + 1 : ℕ) : ℤ) - 2 - j) : ℂ[T;T⁻¹]) = T 1 ^ k * T (-(j : ℤ)) * T k := by
    rw [T_pow, ← T_add, ← T_add]; congr 1; push_cast; ring
  have h2 : (T 1 : ℂ[T;T⁻¹]) * (T (-1) + 1) = T 1 + 1 := by
    rw [mul_add, ← T_add, mul_one]; norm_num [T_zero]; ring
  have h3 : (T (k : ℤ) : ℂ[T;T⁻¹]) * T (-(k : ℤ)) = 1 := by rw [← T_add, add_neg_cancel, T_zero]
  calc T (2 * ((k + 1 : ℕ) : ℤ) - 2 - j) * ((T (-1) + 1) ^ k * (T (-(k : ℤ)) * σ))
      = (T 1 * (T (-1) + 1)) ^ k * (T (-(j : ℤ)) * σ) * (T k * T (-(k : ℤ))) := by
        rw [h1, mul_pow]; ring
    _ = (T 1 + 1) ^ k * (T (-(j : ℤ)) * σ) := by rw [h2, h3, mul_one]

theorem ev1_preimage (k : ℕ) (σ : ℂ[T;T⁻¹]) :
    ev1 (T k * invert σ) = (-1 : ℂ) ^ k * ev1 σ := by
  rw [map_mul, ev1_T, ev1_invert, zpow_natCast]

/-- **The frame change.** Restricted source identities for every homogeneous state of
positive weight imply the restricted target identities. -/
theorem frame_change (Z : V → E → M → ℂ)
    (hS : ∀ (k : ℕ) (a : V), a ∈ W.grading ((k : ℤ) + 1) → ∀ (ρ : ℂ[T;T⁻¹]) (g : E) (w : M),
      sdiff A Q H a (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * ρ) g w
        = ev1 ρ * Z a g w) :
    ∀ (k : ℕ) (b : V), b ∈ W.grading ((k : ℤ) + 1) → ∀ (σ : ℂ[T;T⁻¹]) (g : E) (w : M),
      tdiff A Q H b (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * σ) g w
        = ev1 σ * Z b g w := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro b hb σ g w
  have hb' : b ∈ W.grading ((k + 1 : ℕ) : ℤ) := by push_cast; exact hb
  have hsrc := hS k b hb (T k * invert σ) g w
  rw [sdiff_eq_tdiff A Q H hb', ev1_preimage, Finset.sum_range_succ'] at hsrc
  have htail : ∑ j ∈ Finset.range (k + 1), ((j + 1).factorial : ℂ)⁻¹ *
      tdiff A Q H ((W.L 1 ^ (j + 1)) b) (inv (2 * ((k + 1 : ℕ) : ℤ) - 2 - ((j + 1 : ℕ) : ℤ))
        (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * (T k * invert σ))) g w = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [inv_preimage]
    have hmem := L_one_pow_mem W hb (j + 1)
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hjk | hjk
    · -- weight `(k − j − 1) + 1`, strictly restricted: apply the induction hypothesis
      have hmem' : (W.L 1 ^ (j + 1)) b ∈ W.grading (((k - j - 1 : ℕ) : ℤ) + 1) := by
        rw [show (((k - j - 1 : ℕ) : ℤ) + 1) = (k : ℤ) + 1 - ((j + 1 : ℕ) : ℤ) by omega]
        exact hmem
      have hsplit : Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
            * (T (-(((j + 1 : ℕ) : ℤ))) * σ)
          = Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ (k - j - 1))
            * (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ (j + 1))
              * (T (-(((j + 1 : ℕ) : ℤ))) * σ)) := by
        conv_rhs => rw [← mul_assoc, ← map_mul, ← pow_add, show k - j - 1 + (j + 1) = k by omega]
      rw [hsplit, ih (k - j - 1) (by omega) _ hmem', map_mul, map_mul, map_pow, map_pow,
        ev1_X_add_one,
        zero_pow (by omega), zero_mul, zero_mul, mul_zero]
    · -- weight `0`
      rw [tdiff_low A Q H (k := (k : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) (by push_cast; omega) hmem,
        mul_zero]
  rw [htail, zero_add, inv_preimage] at hsrc
  simp only [CharP.cast_eq_zero, neg_zero, T_zero, one_mul, pow_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, Module.End.one_apply] at hsrc
  have hsign : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]; norm_num
  have hK : (-1 : ℂ) ^ (k + 1) = -((-1 : ℂ) ^ k) := by rw [pow_succ]; ring
  rw [hK] at hsrc
  linear_combination ((-1 : ℂ) ^ k) * hsrc
    - (tdiff A Q H b (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * σ) g w
      - ev1 σ * Z b g w) * hsign

end Frame

end VOA.Huang.LiRegular
