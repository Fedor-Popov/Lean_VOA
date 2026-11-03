import VOA.Classification.COne.OrbIcoForms

/-! # OrbIco: divisibility of invariant binary forms by `psi J₁₅`

`J15_dvd`: if `D` is `ico`-invariant and `xy ∣ psi D`, then `psi J₁₅ ∣ psi D`.

Proof. `psi(lin b)` vanishes exactly at the binary points whose null vector `pt r` is orthogonal to
`b`. Transporting the `z`-axis (`b2_reach`) along the spin lifts (`ico_lift`) writes every
`psi (lin (b2 i))` as `κ ℓᵢ ℓᵢ'` with linear forms `ℓᵢ, ℓᵢ'` dividing `psi D`. Two different
axes have no common root: a nonzero null vector orthogonal to `a` and `b` forces
`(a·b)² = (a·a)(b·b)` (`gram_of_null`), excluded by `b2_dot`. So the thirty prime linear factors
are pairwise non-associated, and their product divides `psi D`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## Null points -/

/-- The null vector of the binary point `r`. -/
def pt (r : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![r 0 ^ 2 - r 1 ^ 2, I * (r 0 ^ 2 + r 1 ^ 2), -2 * eps1 * (r 0 * r 1)]

theorem eval_psi (r : Fin 2 → ℂ) (F : P3) : eval r (psi F) = eval (pt r) F := by
  have h : (aeval r : P2 →ₐ[ℂ] ℂ).comp psi = aeval (pt r) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [psi, pt]
  have := congrArg (fun φ : P3 →ₐ[ℂ] ℂ => φ F) h
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

theorem eval_lin (v x : Fin 3 → ℂ) : eval x (lin v) = v ⬝ᵥ x := by
  rw [lin_apply]
  simp [dotProduct, Fin.sum_univ_three]

theorem pt_null (r : Fin 2 → ℂ) : pt r ⬝ᵥ pt r = 0 := by
  simp only [pt, dotProduct, Fin.sum_univ_three]
  simp
  have h := eps1_sq
  linear_combination (4 * (r 0 * r 1) ^ 2) * h + ((r 0 ^ 2 + r 1 ^ 2) ^ 2) * I_sq

theorem pt_ne_zero {r : Fin 2 → ℂ} (hr : r ≠ 0) : pt r ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [pt] at h0 h1
  have hs : r 0 ^ 2 = 0 := by linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1
  have ht : r 1 ^ 2 = 0 := by linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1
  apply hr
  funext k
  fin_cases k
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ht

/-! ## The Gram lemma -/

/-- A nonzero null vector orthogonal to `a` and `b` forces `(a·b)² = (a·a)(b·b)`. -/
theorem gram_of_null (a b p : Fin 3 → ℂ) (hp : p ≠ 0) (hpp : p ⬝ᵥ p = 0) (ha : a ⬝ᵥ p = 0)
    (hb : b ⬝ᵥ p = 0) : (a ⬝ᵥ b) ^ 2 = (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  simp only [dotProduct, Fin.sum_univ_three] at hpp ha hb ⊢
  set a0 := a 0; set a1 := a 1; set a2 := a 2
  set b0 := b 0; set b1 := b 1; set b2 := b 2
  set p0 := p 0; set p1 := p 1; set p2 := p 2
  have h1 : p0 * a0 + p1 * a1 + p2 * a2 = 0 := by linear_combination ha
  have h2 : p0 * b0 + p1 * b1 + p2 * b2 = 0 := by linear_combination hb
  have h3 : p0 ^ 2 + p1 ^ 2 + p2 ^ 2 = 0 := by linear_combination hpp
  set G := (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) -
    (a0 * b0 + a1 * b1 + a2 * b2) ^ 2 with hG
  have e0 : G * p0 ^ 2 = 0 := by
    rw [hG]
    linear_combination (a0*b1^2*p0 + a0*b2^2*p0 - 2*a1*b0*b1*p0 - a1*b1^2*p1 - a1*b2^2*p1 -
      2*a2*b0*b2*p0 - a2*b1^2*p2 - a2*b2^2*p2) * h1 + (a1^2*b0*p0 + a1^2*b1*p1 - a1^2*b2*p2 +
      2*a1*a2*b1*p2 + 2*a1*a2*b2*p1 + a2^2*b0*p0 - a2^2*b1*p1 + a2^2*b2*p2) * h2 +
      (a1*b2 - a2*b1)^2 * h3
  have e1 : G * p1 ^ 2 = 0 := by
    rw [hG]
    linear_combination (a1*b2^2*p1 + a1*b0^2*p1 - 2*a2*b1*b2*p1 - a2*b2^2*p2 - a2*b0^2*p2 -
      2*a0*b1*b0*p1 - a0*b2^2*p0 - a0*b0^2*p0) * h1 + (a2^2*b1*p1 + a2^2*b2*p2 - a2^2*b0*p0 +
      2*a2*a0*b2*p0 + 2*a2*a0*b0*p2 + a0^2*b1*p1 - a0^2*b2*p2 + a0^2*b0*p0) * h2 +
      (a2*b0 - a0*b2)^2 * h3
  have e2 : G * p2 ^ 2 = 0 := by
    rw [hG]
    linear_combination (a2*b0^2*p2 + a2*b1^2*p2 - 2*a0*b2*b0*p2 - a0*b0^2*p0 - a0*b1^2*p0 -
      2*a1*b2*b1*p2 - a1*b0^2*p1 - a1*b1^2*p1) * h1 + (a0^2*b2*p2 + a0^2*b0*p0 - a0^2*b1*p1 +
      2*a0*a1*b0*p1 + 2*a0*a1*b1*p0 + a1^2*b2*p2 - a1^2*b0*p0 + a1^2*b1*p1) * h2 +
      (a0*b1 - a1*b0)^2 * h3
  have hG0 : G = 0 := by
    by_contra hne
    apply hp
    funext k
    fin_cases k
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp e0).resolve_left hne)
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp e1).resolve_left hne)
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp e2).resolve_left hne)
  linear_combination -hG0

/-- Two different two-fold axes have no common binary root. -/
theorem no_common_root {i j : Fin 15} (hij : i ≠ j) {r : Fin 2 → ℂ} (hr : r ≠ 0)
    (hi : eval r (psi (lin (b2 i))) = 0) (hj : eval r (psi (lin (b2 j))) = 0) : False := by
  rw [eval_psi, eval_lin] at hi hj
  have := gram_of_null (b2 i) (b2 j) (pt r) (pt_ne_zero hr) (pt_null r) hi hj
  rw [b2_dot_self, b2_dot_self] at this
  exact b2_dot i j hij (by rw [this]; norm_num)

/-! ## Linear forms -/

/-- The linear form `a x + b y`. -/
def lf (a b : ℂ) : P2 := MvPolynomial.C a * X 0 + MvPolynomial.C b * X 1

theorem eval_lf (a b : ℂ) (r : Fin 2 → ℂ) : eval r (lf a b) = a * r 0 + b * r 1 := by
  simp [lf]

theorem lf_root (a b : ℂ) : eval ![b, -a] (lf a b) = 0 := by
  rw [eval_lf]; simp; ring

theorem root_ne_zero {a b : ℂ} (h : lf a b ≠ 0) : (![b, -a] : Fin 2 → ℂ) ≠ 0 := by
  intro h0
  apply h
  have hb : b = 0 := by simpa using congrFun h0 0
  have ha : a = 0 := by simpa using congrFun h0 1
  rw [lf, ha, hb]; simp

/-- The substitution `x ↦ a x + b y`, `y ↦ y` (for `a ≠ 0`), an automorphism. -/
def shearEquiv (a b : ℂ) (ha : a ≠ 0) : P2 ≃ₐ[ℂ] P2 :=
  AlgEquiv.ofAlgHom (binSub a b 0 1) (binSub a⁻¹ (-b / a) 0 1)
    (by
      rw [binSub_comp]
      convert binSub_id using 2 <;> field_simp <;> ring)
    (by
      rw [binSub_comp]
      convert binSub_id using 2 <;> field_simp <;> ring)

theorem prime_lf {a b : ℂ} (h : lf a b ≠ 0) : Prime (lf a b) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb; apply h; rw [lf, ha, hb]; simp
    rw [lf, ha, map_zero, zero_mul, zero_add]
    exact (associated_unit_mul_left (X 1 : P2) (MvPolynomial.C b)
      ((Ne.isUnit hb).map MvPolynomial.C)).symm.prime X_prime
  · have hX : (shearEquiv a b ha) (X 0) = lf a b := by
      simp [shearEquiv, binSub_X0, lf]
    rw [← hX]
    exact (MulEquiv.prime_iff (shearEquiv a b ha)).mpr X_prime


theorem eval_eq_zero_of_dvd {ℓ f : P2} {r : Fin 2 → ℂ} (hr : eval r ℓ = 0) (h : ℓ ∣ f) :
    eval r f = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [map_mul, hr, zero_mul]

theorem psi_lin_ne_zero {v : Fin 3 → ℂ} (hv : v ≠ 0) : psi (lin v) ≠ 0 := by
  intro h
  have e1 := congrArg (eval ![1, 0]) h
  have e2 := congrArg (eval ![0, 1]) h
  have e3 := congrArg (eval ![1, 1]) h
  rw [eval_psi, eval_lin, map_zero] at e1 e2 e3
  simp [pt, dotProduct, Fin.sum_univ_three] at e1 e2 e3
  have h0 : v 0 = 0 := by linear_combination (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2
  have h1 : v 1 * I = 0 := by linear_combination (1 / 2 : ℂ) * e1 + (1 / 2 : ℂ) * e2
  have h1' : v 1 = 0 := (mul_eq_zero.mp h1).resolve_right I_ne_zero
  rw [h1'] at e3
  have h2 : v 2 * eps1 = 0 := by linear_combination (-1 / 2 : ℂ) * e3
  have h2' : v 2 = 0 := (mul_eq_zero.mp h2).resolve_right eps1_ne_zero
  apply hv
  funext k
  fin_cases k
  · exact h0
  · exact h1'
  · exact h2'

theorem b2_ne_zero (i : Fin 15) : b2 i ≠ 0 := by
  intro h
  have := b2_dot_self i
  rw [h] at this
  simp at this

theorem lin_b2_zero : lin (b2 0) = MvPolynomial.C (2 : ℂ) * X 2 := by
  rw [lin_apply]; simp [b2]

/-- Transport of the factorization `psi z = -2ε x y` to every two-fold axis. -/
theorem transport_axis {D : P3} (hD : IcoInv D) (h : X 0 * X 1 ∣ psi D) (i : Fin 15) :
    ∃ a b c d κ : ℂ, κ ≠ 0 ∧ psi (lin (b2 i)) = MvPolynomial.C κ * (lf a b * lf c d) ∧
      lf a b * lf c d ∣ psi D := by
  obtain ⟨g, hg, c₀, hc₀, he⟩ := b2_reach i
  obtain ⟨a, b, c, d, hβ⟩ := ico_lift g hg
  refine ⟨a, b, c, d, c₀⁻¹ * (2 * (-2 * eps1)), mul_ne_zero (inv_ne_zero hc₀)
    (mul_ne_zero two_ne_zero (mul_ne_zero (by norm_num) eps1_ne_zero)), ?_, ?_⟩
  · have hl : lin (b2 i) = c₀⁻¹ • phiE g (lin (b2 0)) := by
      rw [phiE_lin, he, map_smul, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
    rw [hl, map_smul, hβ, lin_b2_zero, map_mul, map_mul, psi]
    simp only [aeval_X, aeval_C, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [map_mul, binSub_X0, binSub_X1, MvPolynomial.algHom_C, algebraMap_eq,
      smul_eq_C_mul, lf]
    ring
  · have := map_dvd (binSub a b c d) h
    rw [map_mul, binSub_X0, binSub_X1, ← hβ, hD g hg] at this
    exact this

/-- **Divisibility by `psi J₁₅`.** -/
theorem J15_dvd {D : P3} (hD : IcoInv D) (h : X 0 * X 1 ∣ psi D) : psi J15 ∣ psi D := by
  choose a b c d κ hκ hQ hdvd using transport_axis hD h
  have hne : ∀ i, lf (a i) (b i) ≠ 0 ∧ lf (c i) (d i) ≠ 0 := by
    intro i
    have h0 := psi_lin_ne_zero (b2_ne_zero i)
    rw [hQ i] at h0
    exact ⟨fun h1 => h0 (by rw [h1]; ring), fun h1 => h0 (by rw [h1]; ring)⟩
  -- the root of a factor kills the corresponding quadric
  have hroot : ∀ i (r : Fin 2 → ℂ), (eval r (lf (a i) (b i)) = 0 ∨ eval r (lf (c i) (d i)) = 0) →
      eval r (psi (lin (b2 i))) = 0 := by
    intro i r hr
    rw [hQ i, map_mul, map_mul]
    rcases hr with hr | hr <;> simp [hr]
  have hnot : ∀ (S : Finset (Fin 15)) (k : Fin 15), k ∉ S → ∀ (u v : ℂ), lf u v ≠ 0 →
      (lf u v = lf (a k) (b k) ∨ lf u v = lf (c k) (d k)) →
      ¬ lf u v ∣ ∏ i ∈ S, (lf (a i) (b i) * lf (c i) (d i)) := by
    intro S k hk u v huv hkuv hdv
    obtain ⟨i, hi, hdi⟩ := ((prime_lf huv).dvd_finsetProd_iff _).mp hdv
    have hik : i ≠ k := fun he => hk (he ▸ hi)
    set r : Fin 2 → ℂ := ![v, -u]
    have hr0 : eval r (lf u v) = 0 := lf_root u v
    have hri : eval r (psi (lin (b2 i))) = 0 := by
      apply hroot i r
      rcases (prime_lf huv).dvd_or_dvd hdi with h1 | h1
      · exact Or.inl (eval_eq_zero_of_dvd hr0 h1)
      · exact Or.inr (eval_eq_zero_of_dvd hr0 h1)
    have hrk : eval r (psi (lin (b2 k))) = 0 := by
      apply hroot k r
      rcases hkuv with h1 | h1
      · exact Or.inl (h1 ▸ hr0)
      · exact Or.inr (h1 ▸ hr0)
    exact no_common_root hik (root_ne_zero huv) hri hrk
  have hall : ∀ S : Finset (Fin 15), ∏ i ∈ S, (lf (a i) (b i) * lf (c i) (d i)) ∣ psi D := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      rw [Finset.prod_insert hk]
      obtain ⟨E, hE⟩ := ih
      have hk1 : lf (a k) (b k) ∣ (∏ i ∈ S, (lf (a i) (b i) * lf (c i) (d i))) * E := by
        rw [← hE]; exact dvd_trans (dvd_mul_right _ _) (hdvd k)
      rcases (prime_lf (hne k).1).dvd_or_dvd hk1 with h1 | h1
      · exact absurd h1 (hnot S k hk _ _ (hne k).1 (Or.inl rfl))
      obtain ⟨E', hE'⟩ := h1
      have hk2 : lf (c k) (d k) ∣ (∏ i ∈ S, (lf (a i) (b i) * lf (c i) (d i))) * E' := by
        have h2 := hdvd k
        rw [hE, hE', show (∏ i ∈ S, (lf (a i) (b i) * lf (c i) (d i))) * (lf (a k) (b k) * E') =
          lf (a k) (b k) * ((∏ i ∈ S, (lf (a i) (b i) * lf (c i) (d i))) * E') by ring] at h2
        exact (mul_dvd_mul_iff_left (hne k).1).mp h2
      rcases (prime_lf (hne k).2).dvd_or_dvd hk2 with h3 | h3
      · exact absurd h3 (hnot S k hk _ _ (hne k).2 (Or.inr rfl))
      obtain ⟨E'', hE''⟩ := h3
      exact ⟨E'', by rw [hE, hE', hE'']; ring⟩
  have hJ : psi J15 = MvPolynomial.C (∏ i, κ i) *
      ∏ i, (lf (a i) (b i) * lf (c i) (d i)) := by
    rw [J15, map_prod, Finset.prod_congr rfl (fun i _ => hQ i), Finset.prod_mul_distrib,
      map_prod]
  rw [hJ]
  exact (IsUnit.mul_left_dvd ((Ne.isUnit (Finset.prod_ne_zero_iff.mpr
    (fun i _ => hκ i))).map MvPolynomial.C)).mpr (hall Finset.univ)

end VOA.Classification.COne.OrbIco
