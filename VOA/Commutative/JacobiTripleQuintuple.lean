/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTriplePentagonal
import VOA.Commutative.JacobiTripleFiber

/-!
# The quintuple product identity: the pentagonal collapse

Write `J₁(z) = ∑_n (-1)ⁿ zⁿ p^{n(n-1)/2}` and `J₂(z) = ∑_m z^m p^{m²}` (two Jacobi triple
products).  The quintuple product identity is the statement that the coefficient of `z^k` in
`J₁J₂` collapses, by Euler's pentagonal theorem, to `(p;p)_∞` times a single monomial:

  `∑_{n+m=k} (-1)ⁿ p^{n(n-1)/2 + m²} = (p;p)_∞ · c_k`, with `c_{3j} = p^{j(3j-1)}`,
  `c_{3j+1} = -p^{j(3j+1)}`, `c_{3j+2} = 0`.

We prove it in the weighted form (`quintuple_collapse₀`): for any weight `g : ℤ → R`,

  `∑_{n,m} (-1)ⁿ g(n+m) p^{n(n-1)/2+m²}`
  `  = (p;p)_∞ (∑_j g(3j) p^{j(3j-1)} - ∑_j g(3j+1) p^{j(3j+1)})`,

and the companion with `z = p` (`quintuple_collapse₁`).  Taking `g(k) = uᵏ` gives the quintuple
product identity (sum side); taking `g(k) = k` gives its `z`-derivatives at the zeros `z = 1`,
`z = p` of `J₁`, i.e. the weight-3/2 product identities

  `∑_j (6j+1) p^{j(3j+1)} = (p;p)_∞² φ(p)`          (`quintuple_deriv₀`)
  `2 ∑_j (3j+1) p^{j(3j+2)} = (p;p)_∞² ∑_m p^{m(m+1)}`  (`quintuple_deriv₁`)

(the first is `∑(6j+1)q^{j(3j+1)/2} = (q;q)⁵/(q²;q²)²` with `q = p²`).
-/

namespace VOA.QSeries.JTP

open PowerSeries VOA.QSeries

open scoped BigOperators

noncomputable section

/-! ## Exponents and signs -/

section Aux

theorem nat_eq_of_two_mul {a b : ℕ} (h : 2 * (a : ℤ) = 2 * (b : ℤ)) : a = b := by omega

/-- `j ↦ j(3j+2)`. -/
def qe2 (j : ℤ) : ℕ := (j * (3 * j + 2)).toNat

/-- `j ↦ (j+1)(3j+1)`. -/
def qe3 (j : ℤ) : ℕ := ((j + 1) * (3 * j + 1)).toNat

theorem cast_qe2 (j : ℤ) : ((qe2 j : ℕ) : ℤ) = j * (3 * j + 2) := by
  rw [qe2, Int.toNat_of_nonneg]
  rcases le_or_gt 0 j with h | h
  · positivity
  · nlinarith

theorem cast_qe3 (j : ℤ) : ((qe3 j : ℕ) : ℤ) = (j + 1) * (3 * j + 1) := by
  rw [qe3, Int.toNat_of_nonneg]
  rcases le_or_gt 0 j with h | h
  · positivity
  · rcases lt_or_eq_of_le (show j ≤ -1 by omega) with h' | h'
    · nlinarith
    · subst h'; norm_num

theorem natAbs_le_qe2 (j : ℤ) : j.natAbs ≤ qe2 j + 1 := by
  have h := cast_qe2 j
  zify; rw [h]
  rcases le_or_gt 0 j with hj | hj
  · rw [abs_of_nonneg hj]; nlinarith
  · rw [abs_of_neg hj]; nlinarith

theorem natAbs_le_qe3 (j : ℤ) : j.natAbs ≤ qe3 j + 1 := by
  have h := cast_qe3 j
  zify; rw [h]
  rcases le_or_gt 0 j with hj | hj
  · rw [abs_of_nonneg hj]; nlinarith
  · rw [abs_of_neg hj]; nlinarith

theorem natAbs_le_pentagonal_neg (j : ℤ) : j.natAbs ≤ pentagonal (-j) + 1 := by
  have := natAbs_le_pentagonal (-j); rwa [Int.natAbs_neg] at this

theorem natAbs_le_pentExp_neg (j : ℤ) : j.natAbs ≤ pentExp (-j) + 1 := by
  have := natAbs_le_pentExp (-j); rwa [Int.natAbs_neg] at this

variable {R : Type*} [CommRing R]

theorem negSign_neg (r : ℤ) : (negSign (-r) : R) = negSign r := by
  simp [negSign]

theorem negSign_add_two_mul (r j : ℤ) : (negSign (r + 2 * j) : R) = negSign r := by
  simp only [negSign_eq]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem negSign_add_two_mul_add_one (r j : ℤ) : (negSign (r + 2 * j + 1) : R) = -negSign r := by
  simp only [negSign_eq]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem finFib_pentExp : FinFib pentExp := finFib_of_natAbs_le _ natAbs_le_pentExp
theorem finFib_sqExp : FinFib sqExp := finFib_of_natAbs_le _ natAbs_le_sqExp
theorem finFib_pentagonal : FinFib pentagonal := finFib_of_natAbs_le _ natAbs_le_pentagonal
theorem finFib_pentagonal_neg : FinFib fun j => pentagonal (-j) :=
  finFib_of_natAbs_le _ natAbs_le_pentagonal_neg
theorem finFib_pentExp_neg : FinFib fun j => pentExp (-j) :=
  finFib_of_natAbs_le _ natAbs_le_pentExp_neg
theorem finFib_qe2 : FinFib qe2 := finFib_of_natAbs_le _ natAbs_le_qe2
theorem finFib_qe3 : FinFib qe3 := finFib_of_natAbs_le _ natAbs_le_qe3

/-- The pentagonal series as an `fsr`. -/
theorem pentSeries_eq_fsr : (pentSeries : PowerSeries R) = fsr (fun r => negSign r) pentagonal :=
  zSeries_eq_fsr _ _ natAbs_le_pentagonal

/-- The pentagonal series with `r ↦ -r`. -/
theorem euler_eq_fsr_neg :
    (euler : PowerSeries R) = fsr (fun r => negSign r) (fun r => pentagonal (-r)) := by
  rw [euler_eq_pentagonal, pentSeries_eq_fsr, ← fsr_equiv (Equiv.neg ℤ)]
  exact fsr_congr (fun r => negSign_neg r) (fun r => rfl)

end Aux

/-! ## The three reindexing maps `(r, j) ↦ (n, m)` with `n + m = 3j + t` -/

section Maps

/-- `t = 0`: `(r + 2j, j - r)`. -/
def qmap0 (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + 2 * x.2, x.2 - x.1)
/-- `t = 1`: `(r + 2j + 1, j - r)`. -/
def qmap1 (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + 2 * x.2 + 1, x.2 - x.1)
/-- `t = 2`: `(r + 2j + 1, j + 1 - r)`. -/
def qmap2 (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + 2 * x.2 + 1, x.2 + 1 - x.1)

theorem qmap0_injective : Function.Injective qmap0 := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [qmap0, Prod.mk.injEq] at h
  ext <;> simp <;> omega

theorem qmap1_injective : Function.Injective qmap1 := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [qmap1, Prod.mk.injEq] at h
  ext <;> simp <;> omega

theorem qmap2_injective : Function.Injective qmap2 := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [qmap2, Prod.mk.injEq] at h
  ext <;> simp <;> omega

theorem qmap_cover (p : ℤ × ℤ) :
    p ∈ Set.range qmap0 ∨ p ∈ Set.range qmap1 ∨ p ∈ Set.range qmap2 := by
  obtain ⟨n, m⟩ := p
  have h := Int.emod_emod_of_dvd (n + m) (dvd_refl 3)
  have h3 : (n + m) % 3 = 0 ∨ (n + m) % 3 = 1 ∨ (n + m) % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · left; refine ⟨(n - 2 * ((n + m) / 3), (n + m) / 3), ?_⟩
    simp only [qmap0, Prod.mk.injEq]; omega
  · right; left; refine ⟨(n - 2 * ((n + m) / 3) - 1, (n + m) / 3), ?_⟩
    simp only [qmap1, Prod.mk.injEq]; omega
  · right; right; refine ⟨(n - 2 * ((n + m) / 3) - 1, (n + m) / 3), ?_⟩
    simp only [qmap2, Prod.mk.injEq]; omega

theorem qmap01 (x y : ℤ × ℤ) : qmap0 x ≠ qmap1 y := by
  simp only [qmap0, qmap1, ne_eq, Prod.mk.injEq]; omega
theorem qmap02 (x y : ℤ × ℤ) : qmap0 x ≠ qmap2 y := by
  simp only [qmap0, qmap2, ne_eq, Prod.mk.injEq]; omega
theorem qmap12 (x y : ℤ × ℤ) : qmap1 x ≠ qmap2 y := by
  simp only [qmap1, qmap2, ne_eq, Prod.mk.injEq]; omega

/-- The involution `(r, j) ↦ (1 - r, j)`. -/
def qflip : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (1 - x.1, x.2)
  invFun x := (1 - x.1, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

end Maps

/-! ## The collapse -/

section Collapse

variable {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]

/-- **The pentagonal collapse** (quintuple product identity, weighted coefficient form):
`∑_{n,m} (-1)ⁿ g(n+m) p^{n(n-1)/2+m²}`
`  = (p;p)_∞ (∑_j g(3j) p^{j(3j-1)} - ∑_j g(3j+1) p^{j(3j+1)})`. -/
theorem quintuple_collapse₀ (g : ℤ → R) :
    fsr (fun p : ℤ × ℤ => negSign p.1 * g (p.1 + p.2)) (fun p => pentExp p.1 + sqExp p.2) =
      euler * (fsr (fun j => g (3 * j)) (fun j => 2 * pentagonal j) -
        fsr (fun j => g (3 * j + 1)) (fun j => 2 * pentagonal (-j))) := by
  have hF : FinFib fun p : ℤ × ℤ => pentExp p.1 + sqExp p.2 := finFib_pentExp.prod finFib_sqExp
  rw [fsr_split3 qmap0 qmap1 qmap2 qmap0_injective qmap1_injective qmap2_injective qmap_cover
    qmap01 qmap02 qmap12 _ hF]
  -- `t = 2` vanishes
  have h2 : fsr (fun x => negSign (qmap2 x).1 * g ((qmap2 x).1 + (qmap2 x).2))
      (fun x => pentExp (qmap2 x).1 + sqExp (qmap2 x).2) = (0 : PowerSeries R) := by
    apply fsr_eq_zero_of_antisymm qflip
    · intro x
      obtain ⟨r, j⟩ := x
      simp only [qflip, Equiv.coe_fn_mk, qmap2]
      apply nat_eq_of_two_mul
      push_cast
      have h1 := two_mul_cast_pentExp (1 - r + 2 * j + 1)
      have h2 := two_mul_cast_pentExp (r + 2 * j + 1)
      rw [cast_sqExp, cast_sqExp]
      linear_combination h1 - h2
    · intro x
      obtain ⟨r, j⟩ := x
      simp only [qflip, Equiv.coe_fn_mk, qmap2]
      rw [show 1 - r + 2 * j + 1 + (j + 1 - (1 - r)) = r + 2 * j + 1 + (j + 1 - r) by ring]
      rw [show 1 - r + 2 * j + 1 = (-(r + 2 * j + 1)) + 2 * (2 * j + 1) + 1 by ring,
        negSign_add_two_mul_add_one, negSign_neg]
      ring
    · exact hF.comp_injective _ qmap2_injective
  rw [h2, add_zero]
  -- `t = 0`
  have h0 : fsr (fun x => negSign (qmap0 x).1 * g ((qmap0 x).1 + (qmap0 x).2))
      (fun x => pentExp (qmap0 x).1 + sqExp (qmap0 x).2) =
      euler * fsr (fun j => g (3 * j)) (fun j => 2 * pentagonal j) := by
    rw [euler_eq_pentagonal, pentSeries_eq_fsr, fsr_mul _ _ finFib_pentagonal
      (finFib_pentagonal.mul_const two_pos)]
    refine fsr_congr (fun x => ?_) (fun x => ?_)
    · obtain ⟨r, j⟩ := x
      simp only [qmap0]
      rw [negSign_add_two_mul, show r + 2 * j + (j - r) = 3 * j by ring]
    · obtain ⟨r, j⟩ := x
      simp only [qmap0]
      apply nat_eq_of_two_mul
      push_cast
      have h1 := two_mul_cast_pentExp (r + 2 * j)
      have h2 := two_mul_natCast_pentagonal r
      have h3 := two_mul_natCast_pentagonal j
      rw [cast_sqExp]
      linear_combination h1 - h2 - 2 * h3
  -- `t = 1`
  have h1 : fsr (fun x => negSign (qmap1 x).1 * g ((qmap1 x).1 + (qmap1 x).2))
      (fun x => pentExp (qmap1 x).1 + sqExp (qmap1 x).2) =
      -(euler * fsr (fun j => g (3 * j + 1)) (fun j => 2 * pentagonal (-j))) := by
    rw [euler_eq_fsr_neg, fsr_mul _ _ finFib_pentagonal_neg
      (finFib_pentagonal_neg.mul_const two_pos),
      ← fsr_neg _ (finFib_pentagonal_neg.prod (finFib_pentagonal_neg.mul_const two_pos))]
    refine fsr_congr (fun x => ?_) (fun x => ?_)
    · obtain ⟨r, j⟩ := x
      simp only [qmap1]
      rw [negSign_add_two_mul_add_one, show r + 2 * j + 1 + (j - r) = 3 * j + 1 by ring]
      ring
    · obtain ⟨r, j⟩ := x
      simp only [qmap1]
      apply nat_eq_of_two_mul
      push_cast
      have h1 := two_mul_cast_pentExp (r + 2 * j + 1)
      have h2 := two_mul_natCast_pentagonal_neg r
      have h3 := two_mul_natCast_pentagonal_neg j
      rw [cast_sqExp]
      linear_combination h1 - h2 - 2 * h3
  rw [h0, h1]
  ring

/-- **The pentagonal collapse at `z = p`**:
`∑_{n,m} (-1)ⁿ g(n+m) p^{n(n+1)/2+m(m+1)}`
`  = (p;p)_∞ (∑_j g(3j) p^{j(3j+2)} - ∑_j g(3j+1) p^{(j+1)(3j+1)})`. -/
theorem quintuple_collapse₁ (g : ℤ → R) :
    fsr (fun p : ℤ × ℤ => negSign p.1 * g (p.1 + p.2))
        (fun p => pentExp (-p.1) + 2 * pentExp (-p.2)) =
      euler * (fsr (fun j => g (3 * j)) qe2 - fsr (fun j => g (3 * j + 1)) qe3) := by
  have hF : FinFib fun p : ℤ × ℤ => pentExp (-p.1) + 2 * pentExp (-p.2) :=
    finFib_pentExp_neg.prod (finFib_pentExp_neg.mul_const two_pos)
  rw [fsr_split3 qmap0 qmap1 qmap2 qmap0_injective qmap1_injective qmap2_injective qmap_cover
    qmap01 qmap02 qmap12 _ hF]
  have h2 : fsr (fun x => negSign (qmap2 x).1 * g ((qmap2 x).1 + (qmap2 x).2))
      (fun x => pentExp (-(qmap2 x).1) + 2 * pentExp (-(qmap2 x).2)) = (0 : PowerSeries R) := by
    apply fsr_eq_zero_of_antisymm qflip
    · intro x
      obtain ⟨r, j⟩ := x
      simp only [qflip, Equiv.coe_fn_mk, qmap2]
      apply nat_eq_of_two_mul
      push_cast
      have h1 := two_mul_cast_pentExp (-(1 - r + 2 * j + 1))
      have h2 := two_mul_cast_pentExp (-(j + 1 - (1 - r)))
      have h3 := two_mul_cast_pentExp (-(r + 2 * j + 1))
      have h4 := two_mul_cast_pentExp (-(j + 1 - r))
      linear_combination h1 + 2 * h2 - h3 - 2 * h4
    · intro x
      obtain ⟨r, j⟩ := x
      simp only [qflip, Equiv.coe_fn_mk, qmap2]
      rw [show 1 - r + 2 * j + 1 + (j + 1 - (1 - r)) = r + 2 * j + 1 + (j + 1 - r) by ring]
      rw [show 1 - r + 2 * j + 1 = (-(r + 2 * j + 1)) + 2 * (2 * j + 1) + 1 by ring,
        negSign_add_two_mul_add_one, negSign_neg]
      ring
    · exact hF.comp_injective _ qmap2_injective
  rw [h2, add_zero]
  have h0 : fsr (fun x => negSign (qmap0 x).1 * g ((qmap0 x).1 + (qmap0 x).2))
      (fun x => pentExp (-(qmap0 x).1) + 2 * pentExp (-(qmap0 x).2)) =
      euler * fsr (fun j => g (3 * j)) qe2 := by
    rw [euler_eq_pentagonal, pentSeries_eq_fsr, fsr_mul _ _ finFib_pentagonal finFib_qe2]
    refine fsr_congr (fun x => ?_) (fun x => ?_)
    · obtain ⟨r, j⟩ := x
      simp only [qmap0]
      rw [negSign_add_two_mul, show r + 2 * j + (j - r) = 3 * j by ring]
    · obtain ⟨r, j⟩ := x
      simp only [qmap0]
      apply nat_eq_of_two_mul
      push_cast
      have h1 := two_mul_cast_pentExp (-(r + 2 * j))
      have h2 := two_mul_cast_pentExp (-(j - r))
      have h3 := two_mul_natCast_pentagonal r
      have h4 := cast_qe2 j
      linear_combination h1 + 2 * h2 - h3 - 2 * h4
  have h1 : fsr (fun x => negSign (qmap1 x).1 * g ((qmap1 x).1 + (qmap1 x).2))
      (fun x => pentExp (-(qmap1 x).1) + 2 * pentExp (-(qmap1 x).2)) =
      -(euler * fsr (fun j => g (3 * j + 1)) qe3) := by
    rw [euler_eq_fsr_neg, fsr_mul _ _ finFib_pentagonal_neg finFib_qe3,
      ← fsr_neg _ (finFib_pentagonal_neg.prod finFib_qe3)]
    refine fsr_congr (fun x => ?_) (fun x => ?_)
    · obtain ⟨r, j⟩ := x
      simp only [qmap1]
      rw [negSign_add_two_mul_add_one, show r + 2 * j + 1 + (j - r) = 3 * j + 1 by ring]
      ring
    · obtain ⟨r, j⟩ := x
      simp only [qmap1]
      apply nat_eq_of_two_mul
      push_cast
      have h1 := two_mul_cast_pentExp (-(r + 2 * j + 1))
      have h2 := two_mul_cast_pentExp (-(j - r))
      have h3 := two_mul_natCast_pentagonal_neg r
      have h4 := cast_qe3 j
      linear_combination h1 + 2 * h2 - h3 - 2 * h4
  rw [h0, h1]
  ring

/-- **The quintuple product identity (sum side).** For a unit `u`,
`J₁(u) J₂(u) = (p;p)_∞ ∑_j (u^{3j} p^{j(3j-1)} - u^{3j+1} p^{j(3j+1)})`, where
`J₁(u) = ∑ (-1)ⁿ uⁿ p^{n(n-1)/2} = (1-u)∏(1-up^k)(1-u⁻¹p^k)(1-p^k)` (`jacobiTriple`) and
`J₂(u) = ∑ u^m p^{m²}`.  With `q = p²` this is the classical quintuple product identity. -/
theorem quintuple_sum (u : Rˣ) :
    fsr (fun n : ℤ => negSign n * ((u ^ n : Rˣ) : R)) pentExp *
        fsr (fun m : ℤ => ((u ^ m : Rˣ) : R)) sqExp =
      euler * (fsr (fun j : ℤ => ((u ^ (3 * j) : Rˣ) : R)) (fun j => 2 * pentagonal j) -
        fsr (fun j : ℤ => ((u ^ (3 * j + 1) : Rˣ) : R)) (fun j => 2 * pentagonal (-j))) := by
  rw [fsr_mul _ _ finFib_pentExp finFib_sqExp,
    ← quintuple_collapse₀ (fun k : ℤ => ((u ^ k : Rˣ) : R))]
  refine fsr_congr (fun p => ?_) (fun _ => rfl)
  rw [zpow_add, Units.val_mul, mul_assoc]

end Collapse

/-! ## `z`-derivatives at the zeros `z = 1`, `z = p` of `J₁` -/

section Deriv

theorem two_ne_zero_PS : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h; have := congrArg constantCoeff h; rw [map_ofNat, map_zero] at this; norm_num at this

/-- Reindexing a `ℤ`-sum along an equivalence, in the form used for rewriting. -/
theorem fsr_reindex (σ : ℤ ≃ ℤ) {R : Type*} [CommRing R] {c c' : ℤ → R} {e e' : ℤ → ℕ}
    (hc : ∀ n, c' n = c (σ n)) (he : ∀ n, e' n = e (σ n)) : fsr c' e' = fsr c e :=
  (fsr_congr hc he).trans (fsr_equiv σ c e)

/-- Jacobi's cube identity as an `fsr`: `∑_a (-1)^a (2a+1) p^{a(a+1)/2} = 2 (p;p)³`. -/
theorem cube_fsr :
    fsr (fun a : ℤ => (negSign a : ℚ) * (2 * (a : ℚ) + 1)) (fun a => pentExp (-a)) =
      2 * euler ^ 3 := by
  apply expand_injective 4 (by norm_num)
  rw [expand_fsr 4 (by norm_num) _ finFib_pentExp_neg, map_mul, map_ofNat, ← jacobi_cube,
    ← zetaSeries_eq, zetaSeries, zSeries_eq_fsr _ _ natAbs_le_triExp]
  refine fsr_congr (fun a => by push_cast; ring) (fun a => ?_)
  apply nat_eq_of_two_mul
  push_cast
  have h1 := two_mul_cast_pentExp (-a)
  rw [cast_triExp]
  linear_combination 4 * h1

/-- `J₁(1) = ∑ (-1)ⁿ p^{n(n-1)/2} = 0`. -/
theorem jtp_one_eq_zero : fsr (fun n : ℤ => (negSign n : ℚ)) pentExp = 0 := by
  apply fsr_eq_zero_of_antisymm (Equiv.subLeft 1)
  · intro n
    simp only [Equiv.subLeft_apply]
    apply nat_eq_of_two_mul
    have h1 := two_mul_cast_pentExp (1 - n)
    have h2 := two_mul_cast_pentExp n
    linear_combination h1 - h2
  · intro n
    simp only [Equiv.subLeft_apply]
    rw [show (1 : ℤ) - n = -n + 2 * 0 + 1 by ring, negSign_add_two_mul_add_one, negSign_neg]
  · exact finFib_pentExp

/-- `J₁(p) = ∑ (-1)ⁿ p^{n(n+1)/2} = 0`. -/
theorem jtp_p_eq_zero : fsr (fun n : ℤ => (negSign n : ℚ)) (fun n => pentExp (-n)) = 0 := by
  apply fsr_eq_zero_of_antisymm (Equiv.subLeft (-1))
  · intro n
    simp only [Equiv.subLeft_apply]
    apply nat_eq_of_two_mul
    have h1 := two_mul_cast_pentExp (-(-1 - n))
    have h2 := two_mul_cast_pentExp (-n)
    linear_combination h1 - h2
  · intro n
    simp only [Equiv.subLeft_apply]
    rw [show (-1 : ℤ) - n = -n + 2 * (-1) + 1 by ring, negSign_add_two_mul_add_one, negSign_neg]
  · exact finFib_pentExp_neg

/-- `(z d/dz) J₁ |_{z=1} = ∑ (-1)ⁿ n p^{n(n-1)/2} = -(p;p)³`. -/
theorem jtp_deriv_one :
    fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) pentExp = -euler ^ 3 := by
  have h2 : (2 : PowerSeries ℚ) * fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) pentExp =
      fsr (fun n : ℤ => (negSign n : ℚ) * (2 * (n : ℚ) - 1)) pentExp +
        fsr (fun n : ℤ => (negSign n : ℚ)) pentExp := by
    rw [← fsr_add _ _ finFib_pentExp, show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
      rw [map_ofNat], ← fsr_const_mul _ _ finFib_pentExp]
    exact fsr_congr (fun n => by ring) (fun _ => rfl)
  have h3 : fsr (fun n : ℤ => (negSign n : ℚ) * (2 * (n : ℚ) - 1)) pentExp =
      -fsr (fun a : ℤ => (negSign a : ℚ) * (2 * (a : ℚ) + 1)) (fun a => pentExp (-a)) := by
    rw [← fsr_neg _ finFib_pentExp_neg]
    refine fsr_reindex (Equiv.neg ℤ) (fun n => ?_) (fun n => ?_)
    · simp only [Equiv.neg_apply, negSign_neg, Int.cast_neg]; ring
    · simp
  rw [jtp_one_eq_zero, add_zero, h3, cube_fsr] at h2
  apply mul_left_cancel₀ two_ne_zero_PS
  rw [h2]; ring

/-- `(z d/dz) J₁ |_{z=p} = ∑ (-1)ⁿ n p^{n(n+1)/2} = (p;p)³`. -/
theorem jtp_deriv_p :
    fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) (fun n => pentExp (-n)) = euler ^ 3 := by
  have : fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) (fun n => pentExp (-n)) =
      -fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) pentExp := by
    rw [← fsr_neg _ finFib_pentExp]
    refine fsr_reindex (Equiv.neg ℤ) (fun n => ?_) (fun n => ?_)
    · simp only [Equiv.neg_apply, negSign_neg, Int.cast_neg]; ring
    · simp
  rw [this, jtp_deriv_one, neg_neg]

/-- The theta series `φ(p) = ∑_m p^{m²}` and `Ψ(p) = ∑_m p^{m(m+1)}`. -/
def phiF : PowerSeries ℚ := fsr (fun _ : ℤ => (1 : ℚ)) sqExp
def psiF : PowerSeries ℚ := fsr (fun _ : ℤ => (1 : ℚ)) (fun m => 2 * pentExp (-m))

theorem finFib_two_pentExp_neg : FinFib fun m : ℤ => 2 * pentExp (-m) :=
  finFib_pentExp_neg.mul_const two_pos

/-- **`∑_j (6j+1) p^{j(3j+1)} = (p;p)_∞² φ(p)`** (the `z`-derivative of the quintuple product
identity at `z = 1`). -/
theorem quintuple_deriv₀ :
    fsr (fun j : ℤ => 6 * (j : ℚ) + 1) (fun j => 2 * pentagonal (-j)) = euler ^ 2 * phiF := by
  have hD := quintuple_collapse₀ (R := ℚ) (fun k => (k : ℚ))
  have hF : FinFib fun p : ℤ × ℤ => pentExp p.1 + sqExp p.2 := finFib_pentExp.prod finFib_sqExp
  have hP : fsr (fun p : ℤ × ℤ => (negSign p.1 : ℚ) * ((p.1 + p.2 : ℤ) : ℚ))
      (fun p => pentExp p.1 + sqExp p.2) = -euler ^ 3 * phiF := by
    have hsplit : fsr (fun p : ℤ × ℤ => (negSign p.1 : ℚ) * ((p.1 + p.2 : ℤ) : ℚ))
        (fun p => pentExp p.1 + sqExp p.2) =
        fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) pentExp * phiF +
          fsr (fun n : ℤ => (negSign n : ℚ)) pentExp *
            fsr (fun m : ℤ => (m : ℚ)) sqExp := by
      rw [phiF, fsr_mul _ _ finFib_pentExp finFib_sqExp, fsr_mul _ _ finFib_pentExp finFib_sqExp,
        ← fsr_add _ _ hF]
      exact fsr_congr (fun p => by push_cast; ring) (fun _ => rfl)
    rw [hsplit, jtp_one_eq_zero, jtp_deriv_one]; ring
  have hS0 : fsr (fun j : ℤ => (((3 * j : ℤ) : ℚ))) (fun j => 2 * pentagonal j) =
      fsr (fun j : ℤ => -3 * (j : ℚ)) (fun j => 2 * pentagonal (-j)) := by
    symm
    refine fsr_reindex (Equiv.neg ℤ) (fun n => ?_) (fun n => ?_)
    · simp only [Equiv.neg_apply]; push_cast; ring
    · simp
  have hS : fsr (fun j : ℤ => ((3 * j : ℤ) : ℚ)) (fun j => 2 * pentagonal j) -
      fsr (fun j : ℤ => ((3 * j + 1 : ℤ) : ℚ)) (fun j => 2 * pentagonal (-j)) =
      -fsr (fun j : ℤ => 6 * (j : ℚ) + 1) (fun j => 2 * pentagonal (-j)) := by
    rw [hS0, ← fsr_sub _ _ (finFib_pentagonal_neg.mul_const two_pos),
      ← fsr_neg _ (finFib_pentagonal_neg.mul_const two_pos)]
    exact fsr_congr (fun j => by push_cast; ring) (fun j => rfl)
  rw [hP, hS] at hD
  apply (isUnit_euler (R := ℚ)).mul_left_cancel
  linear_combination hD

/-- **`2 ∑_j (3j+1) p^{j(3j+2)} = (p;p)_∞² Ψ(p)`** (the `z`-derivative of the quintuple product
identity at `z = p`). -/
theorem quintuple_deriv₁ :
    2 * fsr (fun j : ℤ => 3 * (j : ℚ) + 1) qe2 = euler ^ 2 * psiF := by
  have hD := quintuple_collapse₁ (R := ℚ) (fun k => (k : ℚ))
  have hF : FinFib fun p : ℤ × ℤ => pentExp (-p.1) + 2 * pentExp (-p.2) :=
    finFib_pentExp_neg.prod finFib_two_pentExp_neg
  have hP : fsr (fun p : ℤ × ℤ => (negSign p.1 : ℚ) * ((p.1 + p.2 : ℤ) : ℚ))
      (fun p => pentExp (-p.1) + 2 * pentExp (-p.2)) = euler ^ 3 * psiF := by
    have hsplit : fsr (fun p : ℤ × ℤ => (negSign p.1 : ℚ) * ((p.1 + p.2 : ℤ) : ℚ))
        (fun p => pentExp (-p.1) + 2 * pentExp (-p.2)) =
        fsr (fun n : ℤ => (negSign n : ℚ) * (n : ℚ)) (fun n => pentExp (-n)) * psiF +
          fsr (fun n : ℤ => (negSign n : ℚ)) (fun n => pentExp (-n)) *
            fsr (fun m : ℤ => (m : ℚ)) (fun m => 2 * pentExp (-m)) := by
      rw [psiF, fsr_mul _ _ finFib_pentExp_neg finFib_two_pentExp_neg,
        fsr_mul _ _ finFib_pentExp_neg finFib_two_pentExp_neg, ← fsr_add _ _ hF]
      exact fsr_congr (fun p => by push_cast; ring) (fun _ => rfl)
    rw [hsplit, jtp_p_eq_zero, jtp_deriv_p]; ring
  have hS1 : fsr (fun j : ℤ => ((3 * j + 1 : ℤ) : ℚ)) qe3 =
      fsr (fun j : ℤ => -3 * (j : ℚ) - 2) qe2 := by
    symm
    refine fsr_reindex (Equiv.subLeft (-1)) (fun n => ?_) (fun n => ?_)
    · simp only [Equiv.subLeft_apply]; push_cast; ring
    · simp only [Equiv.subLeft_apply]
      have h1 := cast_qe3 (-1 - n)
      have h2 := cast_qe2 n
      have : ((qe3 (-1 - n) : ℕ) : ℤ) = ((qe2 n : ℕ) : ℤ) := by rw [h1, h2]; ring
      exact_mod_cast this.symm
  have hS : fsr (fun j : ℤ => ((3 * j : ℤ) : ℚ)) qe2 -
      fsr (fun j : ℤ => ((3 * j + 1 : ℤ) : ℚ)) qe3 =
      2 * fsr (fun j : ℤ => 3 * (j : ℚ) + 1) qe2 := by
    rw [hS1, ← fsr_sub _ _ finFib_qe2, show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
      rw [map_ofNat], ← fsr_const_mul _ _ finFib_qe2]
    exact fsr_congr (fun j => by push_cast; ring) (fun j => rfl)
  rw [hP, hS] at hD
  apply (isUnit_euler (R := ℚ)).mul_left_cancel
  linear_combination -hD

end Deriv

end

end VOA.QSeries.JTP

section AxiomAudit
#print axioms VOA.QSeries.JTP.quintuple_collapse₀
#print axioms VOA.QSeries.JTP.quintuple_collapse₁
#print axioms VOA.QSeries.JTP.quintuple_sum
#print axioms VOA.QSeries.JTP.quintuple_deriv₀
#print axioms VOA.QSeries.JTP.quintuple_deriv₁
end AxiomAudit
