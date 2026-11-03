import VOA.Modules.C2RigidContraFHL

/-!
# Port of `Modules/ContragredientFHLBase.lean` from `OrdVModule` to `GWModule`

Input to the McRae rigidity argument.  Statements and proofs are those of the original file, with the
structure `OrdVModule` replaced by `C2Rigid.GWModule` (graded weak modules, `L₀` possibly
non-semisimple) and the namespace `VOA` replaced by `VOA.C2Rigid`.  See
`Modules/C2RigidGraded.lean` for why this is the only change needed.
-/


namespace VOA.C2Rigid
open scoped BigOperators

/-- `gBinom 0 (k+1) = 0`. -/
theorem gBinom_zero_succ' (k : ℕ) : gBinom 0 (k + 1) = 0 := by
  unfold gBinom
  rw [Finset.prod_range_succ' (fun i => ((0 : ℤ) : ℂ) - (i : ℂ)) k]
  simp

noncomputable def vsum (A C : ℤ) (r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (r + 1), (-1:ℂ)^k * gBinom A k * gBinom (C - k) (r - k)

theorem vsum_rec (A C : ℤ) (r : ℕ) :
    vsum A C (r + 1) = vsum (A - 1) C (r + 1) - vsum (A - 1) (C - 1) r := by
  unfold vsum
  rw [Finset.sum_range_succ' (fun k => (-1:ℂ)^k * gBinom A k * gBinom (C - (k:ℤ)) (r + 1 - k)) (r + 1),
      Finset.sum_range_succ' (fun k => (-1:ℂ)^k * gBinom (A - 1) k * gBinom (C - (k:ℤ)) (r + 1 - k)) (r + 1)]
  simp only [pow_zero, gBinom_zero, one_mul, mul_one, Nat.cast_zero, sub_zero, Nat.sub_zero]
  rw [add_sub_right_comm, add_left_inj]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_add_right]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [gBinom_succ_pascal A k]
  have hC : (C - (↑k + 1) : ℤ) = C - 1 - ↑k := by ring
  rw [hC, pow_succ]
  ring

theorem vsum_at_zero (C : ℤ) (r : ℕ) : vsum 0 C r = gBinom C r := by
  unfold vsum
  rw [Finset.sum_range_succ' (fun k => (-1:ℂ)^k * gBinom 0 k * gBinom (C - (k:ℤ)) (r - k)) r]
  have htail : ∀ k ∈ Finset.range r,
      (-1:ℂ)^(k+1) * gBinom 0 (k+1) * gBinom (C - ((k+1:ℕ):ℤ)) (r - (k+1)) = 0 := by
    intro k _; rw [gBinom_zero_succ' k]; ring
  rw [Finset.sum_eq_zero htail]
  simp

theorem vsum_eq (r : ℕ) : ∀ A C : ℤ, vsum A C r = gBinom (C - A) r := by
  induction r with
  | zero =>
      intro A C
      unfold vsum
      simp
  | succ r ih =>
      intro A C
      induction A using Int.induction_on with
      | zero =>
          rw [vsum_at_zero]; simp
      | succ i ihp =>
          rw [vsum_rec ((i : ℤ) + 1) C r]
          rw [show ((i : ℤ) + 1) - 1 = (i : ℤ) by ring]
          rw [ihp, ih i (C - 1)]
          have hpas := gBinom_succ_pascal (C - (i : ℤ)) r
          rw [show (C - (i : ℤ)) - 1 = (C - 1) - (i : ℤ) by ring] at hpas
          rw [show C - ((i : ℤ) + 1) = (C - 1) - (i : ℤ) by ring]
          rw [hpas]; ring
      | pred i ihn =>
          have hrec := vsum_rec (-(i : ℤ)) C r
          rw [show (-(i : ℤ)) - 1 = -(i : ℤ) - 1 by ring] at hrec
          have hgoal : vsum (-(i : ℤ) - 1) C (r + 1)
              = vsum (-(i : ℤ)) C (r + 1) + vsum (-(i : ℤ) - 1) (C - 1) r := by
            rw [hrec]; ring
          rw [hgoal, ihn, ih (-(i : ℤ) - 1) (C - 1)]
          have hpas := gBinom_succ_pascal (C - (-(i : ℤ) - 1)) r
          rw [show C - (-(i : ℤ) - 1) = C + (i : ℤ) + 1 by ring] at hpas
          rw [show (C + (i : ℤ) + 1) - 1 = C + (i : ℤ) by ring] at hpas
          rw [show C - (-(i : ℤ)) = C + (i : ℤ) by ring,
              show (C - 1) - (-(i : ℤ) - 1) = C + (i : ℤ) by ring,
              show C - (-(i : ℤ) - 1) = C + (i : ℤ) + 1 by ring]
          rw [hpas]

theorem vandermonde_neg (A C : ℤ) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (-1:ℂ)^k * gBinom A k * gBinom (C - k) (r - k)
      = gBinom (C - A) r := vsum_eq r A C


open VertexOperatorAlgebra
open Module (End Dual)

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `(j!)⁻¹ * ∏_{l<j}((X-l:ℤ):ℂ) = gBinom X j`. -/
theorem gBinom_scalar (X : ℤ) (j : ℕ) :
    ((j.factorial : ℂ)⁻¹) * (∏ l ∈ Finset.range j, ((X - (l:ℤ) : ℤ) : ℂ)) = gBinom X j := by
  unfold gBinom; rw [div_eq_inv_mul]; congr 1
  exact Finset.prod_congr rfl (fun l _ => by push_cast; ring)

theorem negOne_zpow_even (k : ℤ) : (-1:ℂ)^(2*k) = 1 := by rw [zpow_mul]; norm_num

theorem negOne_zpow_add (a b : ℤ) : (-1:ℂ)^(a+b) = (-1:ℂ)^a * (-1:ℂ)^b :=
  zpow_add₀ (by norm_num) a b

theorem negOne_neg_zpow (a : ℤ) : -((-1:ℂ)^a) = (-1:ℂ)^(a+1) := by
  rw [negOne_zpow_add]; ring

theorem negOne_zpow_eq (a b : ℤ) (h : ∃ k, a - b = 2*k) : (-1:ℂ)^a = (-1:ℂ)^b := by
  obtain ⟨k, hk⟩ := h
  have : a = b + 2*k := by omega
  rw [this, negOne_zpow_add, zpow_mul]; norm_num

/-- **Skew transported + sign collapsed** into a `gBinom` tower:
`Y_M(v₍s₎u)₍k₎ x = ∑ᶠ j, (-(-1)^s · gBinom k j) • Y_M(u₍s+j₎v)₍k-j₎ x`. -/
theorem mode_skew_gbinom (N : GWModule W M) (u v : 𝒱) (s k : ℤ) (x : M) :
    mode (N.YM (W.smul v s u)) k x
      = ∑ᶠ j : ℕ, ((- (-1:ℂ)^s) * gBinom k j) •
            mode (N.YM (W.smul u (s + (j:ℤ)) v)) (k - (j:ℤ)) x := by
  rw [mode_skew_reduction N u v s k x]
  refine finsum_congr (fun j => ?_)
  have hsign : sgn (-s - 1 - (j:ℤ)) * ((-1:ℂ)^j) = - (-1:ℂ)^s := by
    show negOnePow (-s - 1 - (j:ℤ)) * ((-1:ℂ)^j) = - (-1:ℂ)^s
    rw [← negOnePow_natCast j, ← negOnePow_add]
    rw [show (-s - 1 - (j:ℤ)) + (j:ℤ) = -s - 1 from by ring]
    have hr : (-1:ℂ)^(-s-1) = - (-1:ℂ)^s := by
      have h2 : (-1:ℂ)^(-2*s) = 1 := by rw [show (-2*s:ℤ)=2*(-s) from by ring]; exact negOne_zpow_even _
      have e : (-1:ℂ)^(-s-1) = (-1:ℂ)^s * (-1:ℂ)^(-2*s-1) := by
        rw [← zpow_add₀ (by norm_num : (-1:ℂ)≠0)]; congr 1; ring
      rw [e, show (-2*s-1:ℤ)=(-2*s)+(-1) from by ring, zpow_add₀ (by norm_num:(-1:ℂ)≠0), h2]; ring
    rw [negOnePow_eq_zpow, hr]
  rw [show ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j:ℤ))) •
        ((-1 : ℂ) ^ j • (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ)) •
          mode (N.YM (W.smul u (s + (j : ℤ)) v)) (k - (j : ℤ)) x)
      = (((j.factorial : ℂ)⁻¹) * sgn (-s - 1 - (j:ℤ)) * (-1:ℂ)^j *
          (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ))) •
          mode (N.YM (W.smul u (s + (j : ℤ)) v)) (k - (j : ℤ)) x from by
    rw [smul_smul, smul_smul, smul_smul]]
  congr 1
  rw [show ((j.factorial : ℂ)⁻¹) * sgn (-s - 1 - (j:ℤ)) * (-1:ℂ)^j *
        (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ))
      = (sgn (-s - 1 - (j:ℤ)) * (-1:ℂ)^j) *
          (((j.factorial : ℂ)⁻¹) * (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ))) from by ring]
  rw [hsign, gBinom_scalar]

/-- The `dualAdj` `gBinom` tower term vanishes for `j` above the weight `p+q-s-1`. -/
theorem gbinom_term_zero (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (s K : ℤ) {α : ℂ} {xα : M}
    (j : ℕ) (hj : (p+q-s-1) - (j:ℤ) < 0) :
    ((-1:ℂ)^(p+q-s-1) * gBinom (2*p - s - 2) j) •
        mode (N.YM (W.smul u (s + (j:ℤ)) v)) (2*(p+q-s-1) - K - 2 - (j:ℤ)) xα = 0 := by
  have hsmul : W.smul u s v ∈ W.grading (p + q - s - 1) := W.smul_mem_grading hu hv s
  have hzero : ((W.L 1)^j) (W.smul u s v) = 0 := L_one_pow_eq_zero W hsmul hj
  have hgen := L1pow_smul_qp_gen W hu hqpu hqpv s j
  rw [hzero] at hgen
  rw [mul_smul]
  apply smul_eq_zero_of_right
  rw [← gBinom_scalar (2*p-s-2) j, mul_smul]
  apply smul_eq_zero_of_right
  rw [← LinearMap.smul_apply, ← mode_smul, ← map_smul, ← hgen, map_zero]
  rfl

/-- `dualAdj` of `u₍s₎v` (quasi-primary) as a finite `gBinom`-tower sum. -/
theorem dualAdj_smul_range (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (s K : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N (p + q - s - 1) (W.smul u s v) K α xα
      = ∑ j ∈ Finset.range ((p+q-s-1).toNat + 1), ((-1:ℂ)^(p+q-s-1) * gBinom (2*p - s - 2) j) •
            mode (N.YM (W.smul u (s + (j:ℤ)) v)) (2*(p+q-s-1) - K - 2 - (j:ℤ)) xα := by
  have hsmul : W.smul u s v ∈ W.grading (p + q - s - 1) := W.smul_mem_grading hu hv s
  rw [dualAdj_clean N hsmul K hxα, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [L1pow_smul_qp_gen W hu hqpu hqpv s j, map_smul, mode_smul, LinearMap.smul_apply]
  rw [smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, gBinom_scalar (2*p-s-2) j]

/-- `dualAdj` of `u₍s₎v` (quasi-primary) as a `gBinom`-tower `∑ᶠ`. -/
theorem dualAdj_smul_gbinom (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (s K : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N (p + q - s - 1) (W.smul u s v) K α xα
      = ∑ᶠ j : ℕ, ((-1:ℂ)^(p+q-s-1) * gBinom (2*p - s - 2) j) •
            mode (N.YM (W.smul u (s + (j:ℤ)) v)) (2*(p+q-s-1) - K - 2 - (j:ℤ)) xα := by
  rw [dualAdj_smul_range N hu hqpu hv hqpv s K hxα]
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range ((p+q-s-1).toNat + 1))]
  intro j hj
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  apply hj
  exact gbinom_term_zero N hu hqpu hv hqpv s K (α := α) (xα := xα) j (by omega)

/-! ## The per-`r` Vandermonde collapse (`gBinom` coefficient matching). -/

/-- **Generic per-`r` Vandermonde finsum collapse.** -/
theorem vand_finsum (D B : ℤ) (r : ℕ) :
    (∑ᶠ j : ℕ, (-1:ℂ)^j * cbz D (r - (j:ℤ)) * gBinom (B - (r - (j:ℤ))) j)
      = (-1:ℂ)^r * gBinom (B - D) r := by
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (r+1))]
  · rw [← Finset.sum_range_reflect
        (fun j => (-1:ℂ)^j * cbz D (r - (j:ℤ)) * gBinom (B - (r - (j:ℤ))) j) (r+1)]
    have hcongr : ∀ k ∈ Finset.range (r+1),
        ((-1:ℂ)^(r+1-1-k) * cbz D (r - ((r+1-1-k:ℕ):ℤ)) * gBinom (B - (r - ((r+1-1-k:ℕ):ℤ))) (r+1-1-k))
          = (-1:ℂ)^r * ((-1:ℂ)^k * gBinom D k * gBinom (B - (k:ℤ)) (r - k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hkr : k ≤ r := by omega
      have h1 : (r+1-1-k) = r - k := by omega
      rw [h1]
      have h2 : (r - ((r-k:ℕ):ℤ)) = (k:ℤ) := by
        have : ((r-k:ℕ):ℤ) = (r:ℤ) - (k:ℤ) := by omega
        omega
      rw [h2, cbz_apply_nonneg D (by positivity), Int.toNat_natCast]
      have hsgn : (-1:ℂ)^(r-k) = (-1:ℂ)^r * (-1:ℂ)^k := by
        have he : (-1:ℂ)^r = (-1:ℂ)^((r-k)+k) := by rw [Nat.sub_add_cancel hkr]
        rw [he, pow_add]
        have hkk : (-1:ℂ)^k * (-1:ℂ)^k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
        rw [mul_assoc, hkk, mul_one]
      rw [hsgn]; ring
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, vandermonde_neg D B r]
  · intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    apply hj
    rw [cbz_apply_neg D (by omega : (r:ℤ) - (j:ℤ) < 0), mul_zero, zero_mul]

/-! ## LHS and RHS reductions to the common antidiagonal form. -/

theorem negOne_zpow_natCast (j : ℕ) : (-1:ℂ)^(j:ℤ) = (-1:ℂ)^j := by
  rw [zpow_natCast]

/-- Sign split: `(-1)^(ℓ+r-j) = (-1)^(ℓ+r) * (-1)^j` (zpow → ℕ-pow on `j`). -/
theorem signSplit (a : ℤ) (j : ℕ) : (-1:ℂ)^(a - (j:ℤ)) = (-1:ℂ)^a * (-1:ℂ)^j := by
  rw [show (a - (j:ℤ)) = a + (-(j:ℤ)) from by ring, negOne_zpow_add, zpow_neg,
      negOne_zpow_natCast]
  congr 1
  rw [inv_eq_iff_eq_inv]
  have : (-1:ℂ)^j * (-1:ℂ)^j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  field_simp at this ⊢
  linear_combination this

/-- **LHS reduction to the antidiagonal flattened form.** -/
theorem lhs_flat (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualAdj N q v (n + i) (matchIdx p (ℓ + m - i) α) (dualAdj N p u (ℓ + m - i) α xα)
          - negOnePow ℓ • dualAdj N p u (m + i) (matchIdx q (ℓ + n - i) α)
              (dualAdj N q v (ℓ + n - i) α xα)))
      = ∑ᶠ i : ℤ, ∑ᶠ j : ℕ,
          ((-1:ℂ)^(p+q) * cbz (2*q-ℓ-n-2) i * (- (-1:ℂ)^(ℓ+i)) * gBinom (2*p+2*q-2*ℓ-m-n-4 - i) j) •
            mode (N.YM (W.smul u (ℓ + (i + (j:ℤ))) v)) ((2*p+2*q-2*ℓ-m-n-4) - (i + (j:ℤ))) xα := by
  rw [lhs_qp_eq N hu hqpu hv hqpv ℓ m n hxα]
  rw [smul_finsum]
  refine finsum_congr (fun i => ?_)
  rw [show (2*q-ℓ-n-2)+(2*p-ℓ-m-2)-i = (2*p+2*q-2*ℓ-m-n-4) - i from by ring]
  rw [show (W.smul v (ℓ+i) u) = (W.smul v (ℓ+i) u) from rfl]
  rw [mode_skew_gbinom N u v (ℓ+i) ((2*p+2*q-2*ℓ-m-n-4) - i) xα]
  rw [smul_finsum, smul_finsum]
  refine finsum_congr (fun j : ℕ => ?_)
  rw [show ((ℓ+i) + (j:ℤ)) = ℓ + (i + (j:ℤ)) from by ring,
      show ((2*p+2*q-2*ℓ-m-n-4) - i) - (j:ℤ) = (2*p+2*q-2*ℓ-m-n-4) - (i + (j:ℤ)) from by ring]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- **RHS reduction to the antidiagonal flattened form.** -/
theorem rhs_flat (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    (∑ᶠ i : ℤ, cbz m i •
          dualAdj N (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα)
      = ∑ᶠ i : ℤ, ∑ᶠ j : ℕ,
          (cbz m i * ((-1:ℂ)^(p+q-(ℓ+i)-1) * gBinom (2*p-(ℓ+i)-2) j)) •
            mode (N.YM (W.smul u (ℓ + (i + (j:ℤ))) v)) ((2*p+2*q-2*ℓ-m-n-4) - (i + (j:ℤ))) xα := by
  refine finsum_congr (fun i => ?_)
  rw [dualAdj_smul_gbinom N hu hqpu hv hqpv (ℓ + i) (m + n - i) hxα]
  rw [smul_finsum]
  refine finsum_congr (fun j : ℕ => ?_)
  rw [show ((ℓ+i) + (j:ℤ)) = ℓ + (i + (j:ℤ)) from by ring,
      show 2*(p+q-(ℓ+i)-1) - (m+n-i) - 2 - (j:ℤ) = (2*p+2*q-2*ℓ-m-n-4) - (i + (j:ℤ)) from by ring]
  rw [smul_smul]

/-! ## Generic finiteness of the antidiagonal supports. -/

/-- The three antidiagonal finiteness side-goals, for `g` vanishing when the first arg `< 0`
and `V` vanishing for `B ≤ r`. -/
theorem antidiag_fins (g : ℤ → ℕ → ℂ) (V : ℤ → M) (B : ℤ)
    (hg : ∀ i : ℤ, i < 0 → ∀ j : ℕ, g i j = 0)
    (hV : ∀ r : ℤ, B ≤ r → V r = 0) :
    (Function.support (fun pr : ℤ × ℕ => g pr.1 pr.2 • V (pr.1 + (pr.2 : ℤ)))).Finite
    ∧ (Function.support (fun pr : ℤ × ℕ => g (pr.1 - (pr.2 : ℤ)) pr.2 • V pr.1)).Finite
    ∧ (∀ r : ℤ, (Function.support (fun j : ℕ => g (r - (j : ℤ)) j)).Finite) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Finite.subset (Set.finite_Icc (0, 0) (B, B.toNat))
    intro pr hpr
    rw [Function.mem_support] at hpr
    have h1 : ¬ pr.1 < 0 := fun h => hpr (by rw [hg pr.1 h pr.2, zero_smul])
    have h2 : ¬ B ≤ pr.1 + (pr.2 : ℤ) := fun h => hpr (by rw [hV _ h, smul_zero])
    rw [Set.mem_Icc]
    refine ⟨⟨by omega, Nat.zero_le _⟩, by omega, by omega⟩
  · apply Set.Finite.subset (Set.finite_Icc (0, 0) (B, B.toNat))
    intro pr hpr
    rw [Function.mem_support] at hpr
    have h1 : ¬ pr.1 - (pr.2 : ℤ) < 0 := fun h => hpr (by rw [hg _ h pr.2, zero_smul])
    have h2 : ¬ B ≤ pr.1 := fun h => hpr (by rw [hV _ h, smul_zero])
    rw [Set.mem_Icc]
    refine ⟨⟨by omega, Nat.zero_le _⟩, by omega, by omega⟩
  · intro r
    apply Set.Finite.subset (Set.finite_Icc 0 r.toNat)
    intro j hj
    rw [Function.mem_support] at hj
    have h1 : ¬ r - (j : ℤ) < 0 := fun h => hj (hg _ h j)
    rw [Set.mem_Icc]
    refine ⟨Nat.zero_le _, by omega⟩

/-! ## Per-`r` coefficient equality (both sides → the same canonical coefficient). -/

/-- The canonical per-`r` coefficient. -/
noncomputable def canCoeff (p q ℓ m r : ℤ) : ℂ :=
  (-1:ℂ)^(p+q-ℓ-1) * gBinom (2*p-ℓ-m-2) r.toNat

/-- LHS per-`r` coefficient collapses (via Vandermonde) to `canCoeff`. -/
theorem lhs_coeff_eq (p q ℓ m n : ℤ) (r : ℕ) :
    (∑ᶠ j : ℕ, (-1:ℂ)^(p+q) * cbz (2*q-ℓ-n-2) (r - (j:ℤ)) * (- (-1:ℂ)^(ℓ + (r - (j:ℤ))))
        * gBinom ((2*p+2*q-2*ℓ-m-n-4) - (r - (j:ℤ))) j)
      = canCoeff p q ℓ m (r:ℤ) := by
  have hcongr : ∀ j : ℕ,
      (-1:ℂ)^(p+q) * cbz (2*q-ℓ-n-2) (r - (j:ℤ)) * (- (-1:ℂ)^(ℓ + (r - (j:ℤ))))
        * gBinom ((2*p+2*q-2*ℓ-m-n-4) - (r - (j:ℤ))) j
      = ((-1:ℂ)^(p+q) * (- (-1:ℂ)^(ℓ + (r:ℤ)))) *
          ((-1:ℂ)^j * cbz (2*q-ℓ-n-2) ((r:ℤ) - (j:ℤ)) * gBinom ((2*p+2*q-2*ℓ-m-n-4) - ((r:ℤ) - (j:ℤ))) j) := by
    intro j
    rw [show (ℓ + ((r:ℤ) - (j:ℤ))) = (ℓ + (r:ℤ)) - (j:ℤ) from by ring, signSplit (ℓ + (r:ℤ)) j]
    ring
  rw [finsum_congr hcongr, ← mul_finsum]
  rw [vand_finsum (2*q-ℓ-n-2) (2*p+2*q-2*ℓ-m-n-4) r]
  unfold canCoeff
  rw [Int.toNat_natCast]
  rw [show (2*p+2*q-2*ℓ-m-n-4) - (2*q-ℓ-n-2) = 2*p-ℓ-m-2 from by ring]
  rw [show ((-1:ℂ)^(p+q) * (- (-1:ℂ)^(ℓ + (r:ℤ)))) * ((-1:ℂ)^r * gBinom (2*p-ℓ-m-2) r)
      = ((-1:ℂ)^(p+q) * (- (-1:ℂ)^(ℓ + (r:ℤ))) * (-1:ℂ)^r) * gBinom (2*p-ℓ-m-2) r from by ring]
  congr 1
  rw [← negOne_zpow_natCast r]
  rw [show ((-1:ℂ)^(p+q) * (- (-1:ℂ)^(ℓ + (r:ℤ))) * (-1:ℂ)^(r:ℤ))
      = -((-1:ℂ)^(p+q) * (-1:ℂ)^(ℓ + (r:ℤ)) * (-1:ℂ)^(r:ℤ)) from by ring]
  rw [← negOne_zpow_add, ← negOne_zpow_add, negOne_neg_zpow]
  exact negOne_zpow_eq _ _ ⟨ℓ + (r:ℤ) + 1, by ring⟩

/-- RHS per-`r` coefficient collapses (via Vandermonde) to `canCoeff`. -/
theorem rhs_coeff_eq (p q ℓ m n : ℤ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz m (r - (j:ℤ))
        * ((-1:ℂ)^(p+q-(ℓ+(r - (j:ℤ)))-1) * gBinom (2*p-(ℓ+(r - (j:ℤ)))-2) j))
      = canCoeff p q ℓ m (r:ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz m ((r:ℤ) - (j:ℤ))
        * ((-1:ℂ)^(p+q-(ℓ+((r:ℤ) - (j:ℤ)))-1) * gBinom (2*p-(ℓ+((r:ℤ) - (j:ℤ)))-2) j)
      = (-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) *
          ((-1:ℂ)^j * cbz m ((r:ℤ) - (j:ℤ)) * gBinom ((2*p-ℓ-2) - ((r:ℤ) - (j:ℤ))) j) := by
    intro j
    rw [show (p+q-(ℓ+((r:ℤ) - (j:ℤ)))-1) = (p+q-ℓ-(r:ℤ)-1) + (j:ℤ) from by ring,
        negOne_zpow_add, negOne_zpow_natCast,
        show (2*p-(ℓ+((r:ℤ) - (j:ℤ)))-2) = (2*p-ℓ-2) - ((r:ℤ) - (j:ℤ)) from by ring]
    ring
  rw [finsum_congr hcongr, ← mul_finsum]
  rw [vand_finsum m (2*p-ℓ-2) r]
  unfold canCoeff
  rw [Int.toNat_natCast, show (2*p-ℓ-2) - m = 2*p-ℓ-m-2 from by ring]
  rw [← negOne_zpow_natCast r,
      show ((-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) * ((-1:ℂ)^(r:ℤ) * gBinom (2*p-ℓ-m-2) r))
      = ((-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) * (-1:ℂ)^(r:ℤ)) * gBinom (2*p-ℓ-m-2) r from by ring]
  congr 1
  rw [← negOne_zpow_add]
  exact negOne_zpow_eq _ _ ⟨0, by ring⟩

/-! ## The quasi-primary base case. -/

/-- **The quasi-primary base case of the module FHL Borcherds identity.** -/
theorem dualAdjResidualMvecAt_qp (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    DualAdjResidualMvecAt N p u q v ℓ m n α xα := by
  unfold DualAdjResidualMvecAt
  set C : ℤ := 2*p+2*q-2*ℓ-m-n-4 with hC
  set V : ℤ → M := fun r => mode (N.YM (W.smul u (ℓ + r) v)) (C - r) xα with hV
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  have hVzero : ∀ r : ℤ, (Ns - ℓ) ≤ r → V r = 0 := by
    intro r hr
    show mode (N.YM (W.smul u (ℓ + r) v)) (C - r) xα = 0
    rw [show W.smul u (ℓ + r) v = 0 from hNs (ℓ + r) (by omega), map_zero]
    rfl
  set gL : ℤ → ℕ → ℂ := fun i j =>
    (-1:ℂ)^(p+q) * cbz (2*q-ℓ-n-2) i * (- (-1:ℂ)^(ℓ+i)) * gBinom (C - i) j with hgL
  set gR : ℤ → ℕ → ℂ := fun i j =>
    cbz m i * ((-1:ℂ)^(p+q-(ℓ+i)-1) * gBinom (2*p-(ℓ+i)-2) j) with hgR
  rw [lhs_flat N hu hqpu hv hqpv ℓ m n hxα]
  rw [rhs_flat N hu hqpu hv hqpv ℓ m n hxα]
  have hLshape : (∑ᶠ i : ℤ, ∑ᶠ j : ℕ,
        ((-1:ℂ)^(p+q) * cbz (2*q-ℓ-n-2) i * (- (-1:ℂ)^(ℓ+i)) * gBinom (C - i) j) • V (i + (j:ℤ)))
      = ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), gL i j • V (i + (j:ℤ)) := rfl
  have hRshape : (∑ᶠ i : ℤ, ∑ᶠ j : ℕ,
        (cbz m i * ((-1:ℂ)^(p+q-(ℓ+i)-1) * gBinom (2*p-(ℓ+i)-2) j)) • V (i + (j:ℤ)))
      = ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), gR i j • V (i + (j:ℤ)) := rfl
  rw [hLshape, hRshape]
  obtain ⟨hLfin, hLfin2, hLfinr⟩ := antidiag_fins gL V (Ns - ℓ)
    (fun i hi j => by simp only [hgL]; rw [cbz_apply_neg _ hi]; ring) hVzero
  obtain ⟨hRfin, hRfin2, hRfinr⟩ := antidiag_fins gR V (Ns - ℓ)
    (fun i hi j => by simp only [hgR]; rw [cbz_apply_neg _ hi]; ring) hVzero
  rw [antidiag_reindex gL V hLfin hLfin2 hLfinr,
      antidiag_reindex gR V hRfin hRfin2 hRfinr]
  refine finsum_congr (fun r => ?_)
  congr 1
  simp only [hgL, hgR, hC]
  rcases lt_or_ge r 0 with hr | hr
  · rw [show (∑ᶠ j : ℕ, (-1:ℂ)^(p+q) * cbz (2*q-ℓ-n-2) (r - (j:ℤ)) * (- (-1:ℂ)^(ℓ+(r - (j:ℤ))))
          * gBinom ((2*p+2*q-2*ℓ-m-n-4) - (r - (j:ℤ))) j) = (∑ᶠ _j : ℕ, (0:ℂ)) from
        finsum_congr (fun j => by
          rw [cbz_apply_neg (2*q-ℓ-n-2) (by omega : r - (j:ℤ) < 0)]; ring)]
    rw [show (∑ᶠ j : ℕ, cbz m (r - (j:ℤ))
          * ((-1:ℂ)^(p+q-(ℓ+(r - (j:ℤ)))-1) * gBinom (2*p-(ℓ+(r - (j:ℤ)))-2) j)) = (∑ᶠ _j : ℕ, (0:ℂ)) from
        finsum_congr (fun j => by
          rw [cbz_apply_neg m (by omega : r - (j:ℤ) < 0)]; ring)]
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    rw [lhs_coeff_eq p q ℓ m n rn, rhs_coeff_eq p q ℓ m n rn]

end VOA.C2Rigid