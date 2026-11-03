import VOA.Classification.COne.OrbIcoDiv

/-! # OrbIco: the binary invariant theory of `ico`, reduction steps

* `psi_surj_hom`: every binary form of degree `2m` is `psi` of a ternary form of degree `m`;
* `hc_mul`: homogeneous components of a product with a homogeneous factor;
* `eval_smul_hom`: `F(c v) = cⁿ F(v)` for homogeneous `F`;
* `eval_phiE`, `rotZ`, `rotX`: the coordinate half-turns;
* `xy_dvd_of_odd`: for `ico`-invariant `F` of odd degree, `xy ∣ psi F`;
* `xy_dvd_of_eval`: for `ico`-invariant `D` with `D(1, i, 0) = 0`, `xy ∣ psi D`;
* `split_J15`: if moreover `xy ∣ psi D`, then `psi D = psi (J₁₅ E)` for an `ico`-invariant `E`
  of degree `n - 15` (or `psi D = 0`).
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## Homogeneous components -/

theorem hc_mul {σ : Type*} {P Q : MvPolynomial σ ℂ} {p : ℕ} (hP : P.IsHomogeneous p) (k : ℕ) :
    homogeneousComponent (p + k) (P * Q) = P * homogeneousComponent k Q := by
  conv_lhs => rw [← sum_homogeneousComponent Q]
  rw [Finset.mul_sum, map_sum]
  have hterm : ∀ j, homogeneousComponent (p + k) (P * homogeneousComponent j Q) =
      if j = k then P * homogeneousComponent k Q else 0 := by
    intro j
    rw [homogeneousComponent_of_mem (m := p + k) (n := p + j)
      ((mem_homogeneousSubmodule _ _).mpr (hP.mul (homogeneousComponent_isHomogeneous j Q)))]
    by_cases hj : j = k
    · subst hj; simp
    · rw [if_neg (by omega), if_neg hj]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hk
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), mul_zero]

theorem hc_mul_lt {σ : Type*} {P Q : MvPolynomial σ ℂ} {p : ℕ} (hP : P.IsHomogeneous p) {k : ℕ}
    (hk : k < p) : homogeneousComponent k (P * Q) = 0 := by
  conv_lhs => rw [← sum_homogeneousComponent Q]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [homogeneousComponent_of_mem (m := k) (n := p + j)
    ((mem_homogeneousSubmodule _ _).mpr (hP.mul (homogeneousComponent_isHomogeneous j Q))),
    if_neg (by omega)]

theorem hc_self {σ : Type*} {P : MvPolynomial σ ℂ} {n : ℕ} (hP : P.IsHomogeneous n) :
    homogeneousComponent n P = P := by
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hP), if_pos rfl]

/-! ## `psi` is onto the even binary forms -/

theorem psi_monomial_preimage (a b : ℕ) (hab : Even (a + b)) :
    ∃ E : P3, E.IsHomogeneous ((a + b) / 2) ∧ psi E = X 0 ^ a * X 1 ^ b := by
  rcases Nat.even_or_odd b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨d, hd⟩ : Even a := by
      rcases Nat.even_or_odd a with h | h
      · exact h
      · exfalso; rw [Nat.even_add] at hab; exact (Nat.not_even_iff_odd.mpr h) (hab.mpr ⟨c, rfl⟩)
    subst hd
    refine ⟨uP ^ d * vP ^ c, ?_, ?_⟩
    · have := (uP_hom.pow d).mul (vP_hom.pow c)
      simp only [one_mul] at this
      rwa [show (d + d + (c + c)) / 2 = d + c by omega]
    · rw [map_mul, map_pow, map_pow, psi_uP, psi_vP, ← pow_mul, ← pow_mul]
      ring_nf
  · obtain ⟨d, hd⟩ : Odd a := by
      rcases Nat.even_or_odd a with h | h
      · exfalso; rw [Nat.even_add] at hab
        exact (Nat.not_even_iff_odd.mpr ⟨c, rfl⟩) (hab.mp h)
      · exact h
    subst hd
    refine ⟨uP ^ d * vP ^ c * wP, ?_, ?_⟩
    · have := ((uP_hom.pow d).mul (vP_hom.pow c)).mul wP_hom
      simp only [one_mul] at this
      rwa [show (2 * d + 1 + (2 * c + 1)) / 2 = d + c + 1 by omega]
    · rw [map_mul, map_mul, map_pow, map_pow, psi_uP, psi_vP, psi_wP]
      ring

/-- `psi` maps the forms of degree `m` onto the binary forms of degree `2m`. -/
theorem psi_surj_hom {B : P2} {m : ℕ} (hB : B.IsHomogeneous (2 * m)) :
    ∃ E : P3, E.IsHomogeneous m ∧ psi E = B := by
  suffices h : ∀ x ∈ binDeg (2 * m), ∃ E : P3, E.IsHomogeneous m ∧ psi E = x from
    h B (mem_binDeg_of_hom hB)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    simp only [Set.mem_setOf_eq] at he
    obtain ⟨E, hE, hψ⟩ := psi_monomial_preimage (e 0) (e 1) ⟨m, by omega⟩
    refine ⟨E, by rwa [show (e 0 + e 1) / 2 = m by omega] at hE, ?_⟩
    have hfe : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
      ext i; fin_cases i <;> simp
    rw [hψ, binMono_eq, hfe]
  | zero => exact ⟨0, isHomogeneous_zero _ _ _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨E, hE, rfl⟩ := hx
    obtain ⟨E', hE', rfl⟩ := hy
    exact ⟨E + E', hE.add hE', map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨E, hE, rfl⟩ := hx
    refine ⟨c • E, ?_, map_smul _ _ _⟩
    rw [smul_eq_C_mul]
    simpa using hE.C_mul c

/-! ## Evaluations -/

theorem eval_smul_hom {F : P3} {n : ℕ} (hF : F.IsHomogeneous n) (c : ℂ) (v : Fin 3 → ℂ) :
    eval (c • v) F = c ^ n * eval v F := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hF (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring

theorem eval_phiE (g : Aut V1) (F : P3) (v : Fin 3 → ℂ) :
    eval v (phiE g F) = eval (fun k => autL g (Pi.single k 1) ⬝ᵥ v) F := by
  have h : (aeval v : P3 →ₐ[ℂ] ℂ).comp (phiE g).toAlgHom =
      aeval (fun k => autL g (Pi.single k 1) ⬝ᵥ v) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, aeval_X]
    change aeval v (phiE g (X k)) = _
    rw [phiE_X]
    change eval v (lin _) = _
    rw [eval_lin]
  have := congrArg (fun φ : P3 →ₐ[ℂ] ℂ => φ F) h
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

theorem autL_rotZ (v : Fin 3 → ℂ) : autL rotZ v = ![-v 0, -v 1, v 2] := by
  apply xyzL_injective
  rw [xyzL_autL]
  simp only [xyzL_apply, rotZ_xyz]
  simp

theorem icoHom_sigZ : icoHom ⟨sigZ, by simp [Perm.mem_alternatingGroup, sigZ, Perm.sign_mul]⟩ =
    rotZ := (icoFun_spec _).unique isIco_rotZ

theorem rotZ_mem : rotZ ∈ ico := ⟨_, icoHom_sigZ⟩

/-- The half-turn about the `x`-axis. -/
def rotX : Aut V1 := (rotC * rotC) * rotZ * rotC

theorem rotX_mem : rotX ∈ ico :=
  ico.mul_mem (ico.mul_mem (ico.mul_mem rotC_mem rotC_mem) rotZ_mem) rotC_mem

theorem autL_rotX (v : Fin 3 → ℂ) : autL rotX v = ![v 0, -v 1, -v 2] := by
  simp only [rotX, autL_mul, LinearMap.comp_apply, autL_rotC, autL_rotZ]
  funext k
  fin_cases k <;> simp

theorem eval_rotZ_inv {F : P3} (hF : IcoInv F) (v : Fin 3 → ℂ) :
    eval v F = eval ![-v 0, -v 1, v 2] F := by
  conv_lhs => rw [← hF rotZ rotZ_mem]
  rw [eval_phiE]
  apply congrArg (fun x => eval x F)
  funext k
  fin_cases k <;> simp [autL_rotZ, dotProduct, Fin.sum_univ_three, Pi.single_apply]

theorem eval_rotX_inv {F : P3} (hF : IcoInv F) (v : Fin 3 → ℂ) :
    eval v F = eval ![v 0, -v 1, -v 2] F := by
  conv_lhs => rw [← hF rotX rotX_mem]
  rw [eval_phiE]
  apply congrArg (fun x => eval x F)
  funext k
  fin_cases k <;> simp [autL_rotX, dotProduct, Fin.sum_univ_three, Pi.single_apply]

/-! ## Divisibility by `xy` -/

theorem eval_binary_scale {B : P2} {d : ℕ} (hB : B.IsHomogeneous d) (c : ℂ) (r : Fin 2 → ℂ) :
    eval (c • r) B = c ^ d * eval r B := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ i, e i = d := by
    have := hB (mem_support_iff.mp he)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem dvd_sub_subst1 (B : P2) : (X 1 : P2) ∣ B - aeval ![X 0, 0] B := by
  set I : Ideal P2 := Ideal.span {(X 1 : P2)}
  have key : (Ideal.Quotient.mkₐ ℂ I).comp (aeval ![X 0, 0]) = Ideal.Quotient.mkₐ ℂ I := by
    apply MvPolynomial.algHom_ext
    intro k
    fin_cases k
    · simp
    · simp only [AlgHom.comp_apply, aeval_X]
      rw [show (![X 0, 0] : Fin 2 → P2) ⟨1, by norm_num⟩ = 0 from rfl, map_zero]
      symm
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      rfl
  have h2 : Ideal.Quotient.mkₐ ℂ I (B - aeval ![X 0, 0] B) = 0 := by
    rw [map_sub, ← AlgHom.comp_apply, key, sub_self]
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2

theorem X1_dvd_of_eval {B : P2} {d : ℕ} (hB : B.IsHomogeneous d) (h : eval ![1, 0] B = 0) :
    (X 1 : P2) ∣ B := by
  have h0 : aeval ![(X 0 : P2), 0] B = 0 := by
    apply MvPolynomial.funext
    intro x
    have hc : (aeval x : P2 →ₐ[ℂ] ℂ).comp (aeval ![(X 0 : P2), 0]) = aeval (x 0 • ![1, 0]) := by
      apply MvPolynomial.algHom_ext
      intro k
      fin_cases k <;> simp
    have := congrArg (fun φ : P2 →ₐ[ℂ] ℂ => φ B) hc
    simp only [AlgHom.comp_apply] at this
    change eval x (aeval ![(X 0 : P2), 0] B) = eval (x 0 • ![1, 0]) B at this
    rw [this, eval_binary_scale hB, h, mul_zero, map_zero]
  have := dvd_sub_subst1 B
  rwa [h0, sub_zero] at this

theorem X0_dvd_of_eval {B : P2} {d : ℕ} (hB : B.IsHomogeneous d) (h : eval ![0, 1] B = 0) :
    (X 0 : P2) ∣ B := by
  set sw : P2 ≃ₐ[ℂ] P2 := renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)
  have hB' : (sw B).IsHomogeneous d := by
    simpa using hB.rename_isHomogeneous (f := Equiv.swap (0 : Fin 2) 1)
  have h' : eval ![1, 0] (sw B) = 0 := by
    rw [show sw B = rename (Equiv.swap (0 : Fin 2) 1) B from rfl, eval_rename]
    have hv : ((![1, 0] : Fin 2 → ℂ) ∘ (Equiv.swap (0 : Fin 2) 1)) = ![0, 1] := by
      funext k; fin_cases k <;> rfl
    rw [hv]; exact h
  have := X1_dvd_of_eval hB' h'
  have := map_dvd sw.symm this
  rw [AlgEquiv.symm_apply_apply] at this
  convert this using 1
  simp [sw, Equiv.swap_apply_def]

theorem xy_dvd {B : P2} {d : ℕ} (hB : B.IsHomogeneous d) (h1 : eval ![1, 0] B = 0)
    (h2 : eval ![0, 1] B = 0) : (X 0 * X 1 : P2) ∣ B := by
  obtain ⟨B', rfl⟩ := X1_dvd_of_eval hB h1
  have h0 := X0_dvd_of_eval hB h2
  rcases (X_prime (i := (0 : Fin 2)) (R := ℂ)).dvd_or_dvd h0 with h | h
  · exfalso
    have := (X_dvd_X (R := ℂ)).mp h
    exact absurd this (by decide)
  · obtain ⟨B'', rfl⟩ := h
    exact ⟨B'', by ring⟩

theorem pt_one_zero : pt ![1, 0] = ![1, I, 0] := by
  funext k; fin_cases k <;> simp [pt]

theorem pt_zero_one : pt ![0, 1] = ![-1, I, 0] := by
  funext k; fin_cases k <;> simp [pt]

/-- Odd degree: `xy ∣ psi F`. -/
theorem xy_dvd_of_odd {F : P3} {n : ℕ} (hF : IcoInv F) (hh : F.IsHomogeneous n) (hn : Odd n) :
    (X 0 * X 1 : P2) ∣ psi F := by
  refine xy_dvd (psi_hom hh) ?_ ?_
  · rw [eval_psi, pt_one_zero]
    have h1 := eval_rotZ_inv hF ![1, I, 0]
    have h2 := eval_smul_hom hh (-1) ![1, I, 0]
    have he : ![-(![1, I, 0] : Fin 3 → ℂ) 0, -(![1, I, 0] : Fin 3 → ℂ) 1,
        (![1, I, 0] : Fin 3 → ℂ) 2] = (-1 : ℂ) • ![1, I, 0] := by
      funext k; fin_cases k <;> simp
    rw [he, h2, hn.neg_one_pow] at h1
    linear_combination h1 / 2
  · rw [eval_psi, pt_zero_one]
    have h1 := eval_rotZ_inv hF ![-1, I, 0]
    have h2 := eval_smul_hom hh (-1) ![-1, I, 0]
    have he : ![-(![-1, I, 0] : Fin 3 → ℂ) 0, -(![-1, I, 0] : Fin 3 → ℂ) 1,
        (![-1, I, 0] : Fin 3 → ℂ) 2] = (-1 : ℂ) • ![-1, I, 0] := by
      funext k; fin_cases k <;> simp
    rw [he, h2, hn.neg_one_pow] at h1
    linear_combination h1 / 2

/-- Vanishing at `(1, i, 0)`: `xy ∣ psi D`. -/
theorem xy_dvd_of_eval {D : P3} {n : ℕ} (hD : IcoInv D) (hh : D.IsHomogeneous n)
    (h0 : eval ![1, I, 0] D = 0) : (X 0 * X 1 : P2) ∣ psi D := by
  refine xy_dvd (psi_hom hh) ?_ ?_
  · rw [eval_psi, pt_one_zero, h0]
  · rw [eval_psi, pt_zero_one]
    have h1 := eval_rotX_inv hD ![1, I, 0]
    have he : (![-1, I, 0] : Fin 3 → ℂ) = (-1 : ℂ) • ![(![1, I, 0] : Fin 3 → ℂ) 0,
        -(![1, I, 0] : Fin 3 → ℂ) 1, -(![1, I, 0] : Fin 3 → ℂ) 2] := by
      funext k; fin_cases k <;> simp
    rw [he, eval_smul_hom hh, ← h1, h0, mul_zero]


/-! ## Splitting off `J₁₅` -/

theorem psi_J15_ne_zero : psi J15 ≠ 0 := by
  rw [J15, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => psi_lin_ne_zero (b2_ne_zero i)

theorem psi_J15_hom : (psi J15).IsHomogeneous 30 := psi_hom J15_hom

/-- If `xy ∣ psi D`, then `psi D = psi (J₁₅ E)` with `E` invariant of degree `n - 15`. -/
theorem split_J15 {D : P3} {n : ℕ} (hD : IcoInv D) (hh : D.IsHomogeneous n)
    (hxy : (X 0 * X 1 : P2) ∣ psi D) :
    psi D = 0 ∨ (15 ≤ n ∧ ∃ E : P3, IcoInv E ∧ E.IsHomogeneous (n - 15) ∧
      psi D = psi (J15 * E)) := by
  obtain ⟨B, hB⟩ := J15_dvd hD hxy
  by_cases hn : 15 ≤ n
  · right
    refine ⟨hn, ?_⟩
    set B' := homogeneousComponent (2 * (n - 15)) B with hB'def
    have hDB : psi D = psi J15 * B' := by
      rw [← hc_self (psi_hom hh), hB, show 2 * n = 30 + 2 * (n - 15) by omega, hc_mul psi_J15_hom]
    have hB'h : B'.IsHomogeneous (2 * (n - 15)) := homogeneousComponent_isHomogeneous _ _
    obtain ⟨E₀, hE₀, hψ⟩ := psi_surj_hom hB'h
    have hinv : ∀ g ∈ ico, psi (phiE g E₀) = B' := by
      intro g hg
      have h1 : psi (J15 * E₀) = psi D := by rw [map_mul, hψ, hDB]
      have h2 := psi_phiE_congr hg h1
      rw [map_mul, icoInv_J15 g hg, map_mul, hD g hg, hDB] at h2
      exact mul_left_cancel₀ psi_J15_ne_zero h2
    refine ⟨reyI E₀, icoInv_reyI E₀, reyI_hom hE₀, ?_⟩
    rw [map_mul, psi_reyI hinv, hDB]
  · left
    rw [← hc_self (psi_hom hh), hB, hc_mul_lt psi_J15_hom (by omega)]

/-! ## The monomials -/

/-- The monomials `J₆ᵃ J₁₀ᵇ J₁₅ᶜ` of degree `n`. -/
def monoSet (J10 : P3) (n : ℕ) : Set P3 :=
  {F | ∃ a b c : ℕ, 6 * a + 10 * b + 15 * c = n ∧ F = J6 ^ a * J10 ^ b * J15 ^ c}

theorem J15_mul_span {J10 : P3} {n : ℕ} {P : P2}
    (hP : P ∈ Submodule.span ℂ (psi '' monoSet J10 n)) :
    psi J15 * P ∈ Submodule.span ℂ (psi '' monoSet J10 (n + 15)) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨a, b, c, hd, rfl⟩, rfl⟩ := hx
    refine Submodule.subset_span ⟨J6 ^ a * J10 ^ b * J15 ^ (c + 1), ⟨a, b, c + 1, by omega, rfl⟩,
      ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, pow_succ]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem gp_im : gp.im = 0 := by simp [gp, s5]

theorem eval_J6 : eval ![1, I, 0] J6 ≠ 0 := by
  rw [J6, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [eval_lin]
  have hgp : gp ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [gp_re] at this
    norm_num at this; linarith [Real.sqrt_nonneg 5]
  fin_cases i <;> simp [a5, dotProduct, Fin.sum_univ_three, hgp, I_ne_zero]
  · intro h; have := congrArg Complex.re h; simp [gp_im] at this
  · intro h; have := congrArg Complex.re h; simp [gp_im] at this

theorem exists_six_ten {n : ℕ} (hev : Even n) (h0 : n ≠ 0) (h2 : n ≠ 2) (h4 : n ≠ 4)
    (h8 : n ≠ 8) (h14 : n ≠ 14) : ∃ a b : ℕ, 6 * a + 10 * b = n := by
  obtain ⟨m, rfl⟩ := hev
  rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with h | h | h
  · exact ⟨m / 3, 0, by omega⟩
  · exact ⟨(m - 10) / 3, 2, by omega⟩
  · exact ⟨(m - 5) / 3, 1, by omega⟩

/-- **The invariant theory of `ico` on binary forms**: modulo `r²`, every invariant of degree
`n` is a combination of the monomials `J₆ᵃ J₁₀ᵇ J₁₅ᶜ`, for any degree-ten invariant `J₁₀` with
`J₁₀(1, i, 0) ≠ 0`, given the vanishing in degrees `2, 4, 8, 14`. -/
theorem icoInvariantSpan_of_small (J10 : P3) (h10 : IcoInv J10) (h10h : J10.IsHomogeneous 10)
    (h10v : eval ![1, I, 0] J10 ≠ 0)
    (hsmall : ∀ (n : ℕ) (F : P3), (n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 14) → IcoInv F →
      F.IsHomogeneous n → psi F = 0) :
    ∀ (n : ℕ) (F : P3), IcoInv F → F.IsHomogeneous n →
      psi F ∈ Submodule.span ℂ (psi '' monoSet J10 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hh
  -- the step through `J₁₅`
  have hstep : ∀ D : P3, IcoInv D → D.IsHomogeneous n → (X 0 * X 1 : P2) ∣ psi D →
      psi D ∈ Submodule.span ℂ (psi '' monoSet J10 n) := by
    intro D hD hDh hxy
    rcases split_J15 hD hDh hxy with h0 | ⟨hn, E, hE, hEh, hDE⟩
    · rw [h0]; exact Submodule.zero_mem _
    · have := J15_mul_span (ih (n - 15) (by omega) E hE hEh)
      rw [show n - 15 + 15 = n by omega, ← map_mul] at this
      rwa [hDE]
  rcases Nat.even_or_odd n with hev | hodd
  · by_cases hn0 : n = 0
    · subst hn0
      have hC : F = MvPolynomial.C (coeff 0 F) := by
        rw [← homogeneousComponent_zero, hc_self hh]
      rw [hC, show (MvPolynomial.C (coeff 0 F) : P3) = coeff 0 F • (1 : P3) by
        rw [smul_eq_C_mul, mul_one], map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, ⟨0, 0, 0, rfl, by simp⟩,
        rfl⟩)
    by_cases hsm : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 14
    · rw [hsmall n F hsm hF hh]; exact Submodule.zero_mem _
    push Not at hsm
    obtain ⟨a, b, hab⟩ := exists_six_ten hev hn0 hsm.1 hsm.2.1 hsm.2.2.1 hsm.2.2.2
    set M := J6 ^ a * J10 ^ b with hM
    have hMv : eval ![1, I, 0] M ≠ 0 := by
      rw [hM, map_mul, map_pow, map_pow]
      exact mul_ne_zero (pow_ne_zero _ eval_J6) (pow_ne_zero _ h10v)
    have hMinv : IcoInv M := (icoInv_J6.pow a).mul (h10.pow b)
    have hMh : M.IsHomogeneous n := by
      have := (J6_hom.pow a).mul (h10h.pow b)
      rwa [show 6 * a + 10 * b = n by omega] at this
    set c := eval ![1, I, 0] F / eval ![1, I, 0] M
    set D := F - c • M with hDdef
    have hD : IcoInv D := hF.sub (hMinv.smul c)
    have hDh : D.IsHomogeneous n := by
      rw [hDdef, sub_eq_add_neg, ← neg_smul, smul_eq_C_mul]
      exact hh.add (by simpa using hMh.C_mul (-c))
    have hDv : eval ![1, I, 0] D = 0 := by
      rw [hDdef, map_sub, MvPolynomial.smul_eval, div_mul_cancel₀ _ hMv, sub_self]
    have hFD : psi F = c • psi M + psi D := by
      rw [hDdef, map_sub, map_smul]; abel
    rw [hFD]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨M, ⟨a, b, 0, by omega, by rw [hM, pow_zero, mul_one]⟩, rfl⟩)) ?_
    exact hstep D hD hDh (xy_dvd_of_eval hD hDh hDv)
  · exact hstep F hF hh (xy_dvd_of_odd hF hh hodd)

end VOA.Classification.COne.OrbIco
