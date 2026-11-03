import VOA.Classification.COne.OrbIcoInv

/-! # OrbIco: no invariant binary forms in degrees `4, 8, 16, 28`

`psi_small_zero`: an `ico`-invariant ternary form `F` of degree `n ∈ {2, 4, 8, 14}` has
`psi F = 0`.

Proof. `F` is `A₄`-invariant (`ico` contains the coordinate half-turns and `rotC`), so by the
tetrahedral invariant theory (`OrbPrim.mem_span_genMon_of_isHomogeneous`) and `psi r² = 0`,
`psi F` is a combination of `psi I₄` (`n = 4`), `psi I₄²` (`n = 8`), or `psi (I₃² I₄²)`,
`psi (I₄² I₆)` (`n = 14`); there is nothing for `n = 2`. Invariance under the half-turn `rotR`,
evaluated at the two null points `(±1, i, 0)` and their images, forces the coefficients to vanish.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## `ico`-invariants are `A₄`-invariants -/

theorem phiE_rotX_eq (F : P3) : phiE rotX F = s1 F := by
  have h : (phiE rotX).toAlgHom = s1 := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE rotX (X k) = _
    rw [phiE_X, autL_rotX, lin_apply]
    fin_cases k <;> simp [s1, Pi.single_apply]
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

theorem phiE_rotY_eq (F : P3) : phiE (rotZ * rotX) F = s2 F := by
  have h : (phiE (rotZ * rotX)).toAlgHom = s2 := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE (rotZ * rotX) (X k) = _
    rw [phiE_X, autL_mul, LinearMap.comp_apply, autL_rotX, autL_rotZ, lin_apply]
    fin_cases k <;> simp [s2, Pi.single_apply]
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

theorem phiE_rotCC_eq (F : P3) : phiE (rotC * rotC) F = rename cyc F := by
  have h : (phiE (rotC * rotC)).toAlgHom = rename cyc := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE (rotC * rotC) (X k) = _
    rw [phiE_X, autL_mul, LinearMap.comp_apply, autL_rotC, autL_rotC, lin_apply, rename_X]
    fin_cases k <;> simp [Pi.single_apply, cyc] <;> rfl
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

theorem isA4Inv_of_ico {F : P3} (hF : IcoInv F) : IsA4Inv F := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← phiE_rotX_eq]; exact hF _ rotX_mem
  · rw [← phiE_rotY_eq]; exact hF _ (ico.mul_mem rotZ_mem rotX_mem)
  · rw [← phiE_rotCC_eq]; exact hF _ (ico.mul_mem rotC_mem rotC_mem)

/-! ## The `r²`-free generator monomials of small degree -/

theorem psi_genMon_of_r2 (t : ℕ × ℕ × ℕ × ℕ) (h : 1 ≤ t.1) : psi (genMon t) = 0 := by
  obtain ⟨a, b, c, d⟩ := t
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by simp at h; omega⟩
  simp [genMon, pow_succ, psi_r2]

theorem psi_mem_span_rfree {F : P3} {n : ℕ} (hF : IcoInv F) (hh : F.IsHomogeneous n) :
    psi F ∈ Submodule.span ℂ ((fun t => psi (genMon t)) '' {t | gdeg t = n ∧ t.1 = 0}) := by
  have h := Submodule.mem_map_of_mem (f := psi.toLinearMap)
    (mem_span_genMon_of_isHomogeneous (isA4Inv_of_ico hF) hh)
  rw [Submodule.map_span] at h
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  by_cases h0 : t.1 = 0
  · exact Submodule.subset_span ⟨t, ⟨ht, h0⟩, rfl⟩
  · change psi (genMon t) ∈ _
    rw [psi_genMon_of_r2 t (by omega)]
    exact Submodule.zero_mem _

theorem rfree_two (t : ℕ × ℕ × ℕ × ℕ) (h : gdeg t = 2 ∧ t.1 = 0) : False := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [gdeg] at h
  omega

theorem rfree_four (t : ℕ × ℕ × ℕ × ℕ) (h : gdeg t = 4 ∧ t.1 = 0) : t = (0, 0, 1, 0) := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [gdeg] at h
  have : a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0 := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
  rfl

theorem rfree_eight (t : ℕ × ℕ × ℕ × ℕ) (h : gdeg t = 8 ∧ t.1 = 0) : t = (0, 0, 2, 0) := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [gdeg] at h
  have : a = 0 ∧ b = 0 ∧ c = 2 ∧ d = 0 := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
  rfl

theorem rfree_fourteen (t : ℕ × ℕ × ℕ × ℕ) (h : gdeg t = 14 ∧ t.1 = 0) :
    t = (0, 2, 2, 0) ∨ t = (0, 0, 2, 1) := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [gdeg] at h
  have : a = 0 ∧ ((b = 2 ∧ c = 2 ∧ d = 0) ∨ (b = 0 ∧ c = 2 ∧ d = 1)) := by omega
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ := this
  · left; rfl
  · right; rfl

/-! ## The rotated null points -/

def w1 : Fin 3 → ℂ := ![gq / 2 + I * gp / 2, gp / 2 - I / 2, 1 / 2 + I * gq / 2]
def w2 : Fin 3 → ℂ := ![-gq / 2 + I * gp / 2, -gp / 2 - I / 2, -1 / 2 + I * gq / 2]

theorem eval_R_10 (F : P3) : eval ![1, I, 0] (phiE rotR F) = eval w1 F := by
  rw [eval_phiE]
  apply congrArg (fun x => eval x F)
  funext k
  fin_cases k <;> simp [autL_rotR, w1, dotProduct, Fin.sum_univ_three, Pi.single_apply] <;> ring

theorem eval_R_01 (F : P3) : eval ![-1, I, 0] (phiE rotR F) = eval w2 F := by
  rw [eval_phiE]
  apply congrArg (fun x => eval x F)
  funext k
  fin_cases k <;> simp [autL_rotR, w2, dotProduct, Fin.sum_univ_three, Pi.single_apply] <;> ring

theorem s5_pow_six : s5 ^ 6 = 125 := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, s5_sq]; norm_num

theorem I_pow_eight : I ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, I_pow_four, one_pow]

theorem eval_w1_I4 : eval w1 I4 = -1 / 2 - s5 * I / 2 := by
  simp [I4, w1, gp, gq]
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, s5_sq, s5_pow_three, s5_pow_four]
  ring_nf

theorem eval_w2_I4 : eval w2 I4 = -1 / 2 + s5 * I / 2 := by
  simp [I4, w2, gp, gq]
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, s5_sq, s5_pow_three, s5_pow_four]
  ring_nf

theorem eval_w1_I3 : eval w1 I3 = (5 - s5) / 16 + I * (5 + s5) / 16 := by
  simp [I3, w1, gp, gq]
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, s5_sq, s5_pow_three, s5_pow_four]
  ring_nf

theorem eval_w2_I3 : eval w2 I3 = (-5 + s5) / 16 + I * (5 + s5) / 16 := by
  simp [I3, w2, gp, gq]
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, s5_sq, s5_pow_three, s5_pow_four]
  ring_nf

theorem eval_w1_I6 : eval w1 I6 = 73 / 64 + 11 * s5 * I / 32 := by
  simp [I6, w1, gp, gq]
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, s5_sq, s5_pow_three,
    s5_pow_four, s5_pow_five, s5_pow_six]
  ring_nf

theorem eval_w2_I6 : eval w2 I6 = 73 / 64 - 11 * s5 * I / 32 := by
  simp [I6, w2, gp, gq]
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, s5_sq, s5_pow_three,
    s5_pow_four, s5_pow_five, s5_pow_six]
  ring_nf

theorem eval_v_I3 : eval ![1, I, 0] I3 = 0 := by simp [I3]
theorem eval_v_I4 : eval ![1, I, 0] I4 = 2 := by
  simp [I4, I_pow_four] <;> norm_num
theorem eval_v_I6 : eval ![1, I, 0] I6 = 2 := by
  simp [I6] <;> ring_nf <;> simp [I_sq, I_pow_four] <;> ring_nf
theorem eval_v'_I3 : eval ![-1, I, 0] I3 = 0 := by simp [I3]
theorem eval_v'_I4 : eval ![-1, I, 0] I4 = 2 := by
  simp [I4, I_pow_four] <;> norm_num
theorem eval_v'_I6 : eval ![-1, I, 0] I6 = 2 := by
  simp [I6] <;> ring_nf <;> simp [I_sq, I_pow_four] <;> ring_nf

theorem s5_re : s5.re = Real.sqrt 5 := by simp [s5]
theorem s5_im : s5.im = 0 := by simp [s5]

/-! ## The vanishing -/

/-- From `psi F = c • psi m` and invariance under `rotR`. -/
theorem coeff_rel {F m : P3} {c : ℂ} (hF : IcoInv F) (h : psi F = c • psi m) (r : Fin 2 → ℂ) :
    c * eval (pt r) m = c * eval (pt r) (phiE rotR m) := by
  obtain ⟨a, b, c', d, hβ⟩ := lifts_rotR
  have h1 : psi (phiE rotR F) = c • psi (phiE rotR m) := by
    rw [hβ, hβ, h, map_smul]
  rw [hF rotR rotR_mem, h] at h1
  have := congrArg (eval r) h1
  simpa only [MvPolynomial.smul_eval, eval_psi] using this

/-- No `ico`-invariant binary forms in degrees `4, 8, 16, 28`. -/
theorem psi_small_zero (n : ℕ) (F : P3) (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 14) (hF : IcoInv F)
    (hh : F.IsHomogeneous n) : psi F = 0 := by
  have hspan := psi_mem_span_rfree hF hh
  rcases hn with rfl | rfl | rfl | rfl
  · have : ((fun t => psi (genMon t)) '' {t | gdeg t = 2 ∧ t.1 = 0}) = ∅ := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t, ht, -⟩; exact rfree_two t ht
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hspan
    exact hspan
  · have hs : ((fun t => psi (genMon t)) '' {t | gdeg t = 4 ∧ t.1 = 0}) ⊆ {psi I4} := by
      rintro _ ⟨t, ht, rfl⟩
      rw [rfree_four t ht, Set.mem_singleton_iff]
      simp [genMon]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Submodule.span_mono hs hspan)
    have hr := coeff_rel hF hc.symm ![1, 0]
    rw [pt_one_zero, eval_v_I4, eval_R_10, eval_w1_I4] at hr
    have hne : (2 : ℂ) - (-1 / 2 - s5 * I / 2) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp [s5_im] at this; norm_num at this
    have hc0 : c = 0 := by
      have : c * ((2 : ℂ) - (-1 / 2 - s5 * I / 2)) = 0 := by linear_combination hr
      exact (mul_eq_zero.mp this).resolve_right hne
    rw [← hc, hc0, zero_smul]
  · have hs : ((fun t => psi (genMon t)) '' {t | gdeg t = 8 ∧ t.1 = 0}) ⊆ {psi (I4 ^ 2)} := by
      rintro _ ⟨t, ht, rfl⟩
      rw [rfree_eight t ht, Set.mem_singleton_iff]
      simp [genMon]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Submodule.span_mono hs hspan)
    have hr := coeff_rel hF hc.symm ![1, 0]
    rw [pt_one_zero, map_pow, eval_v_I4, eval_R_10, map_pow, eval_w1_I4] at hr
    have hne : (2 : ℂ) ^ 2 - (-1 / 2 - s5 * I / 2) ^ 2 ≠ 0 := by
      intro h0
      have h1 : (5 : ℂ) - s5 * I / 2 = 0 := by
        linear_combination h0 + (1 / 4 : ℂ) * I ^ 2 * s5_sq + (5 / 4 : ℂ) * I_sq
      have := congrArg Complex.re h1; simp [s5_im] at this
    have hc0 : c = 0 := by
      have : c * ((2 : ℂ) ^ 2 - (-1 / 2 - s5 * I / 2) ^ 2) = 0 := by linear_combination hr
      exact (mul_eq_zero.mp this).resolve_right hne
    rw [← hc, hc0, zero_smul]
  · have hs : ((fun t => psi (genMon t)) '' {t | gdeg t = 14 ∧ t.1 = 0}) ⊆
        {psi (I3 ^ 2 * I4 ^ 2), psi (I4 ^ 2 * I6)} := by
      rintro _ ⟨t, ht, rfl⟩
      rcases rfree_fourteen t ht with rfl | rfl
      · left; simp [genMon]
      · right; simp [genMon]
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (Submodule.span_mono hs hspan)
    obtain ⟨α, β, γ, δ, hβR⟩ := lifts_rotR
    have hrel : ∀ r : Fin 2 → ℂ,
        a * eval (pt r) (I3 ^ 2 * I4 ^ 2) + b * eval (pt r) (I4 ^ 2 * I6) =
        a * eval (pt r) (phiE rotR (I3 ^ 2 * I4 ^ 2)) +
          b * eval (pt r) (phiE rotR (I4 ^ 2 * I6)) := by
      intro r
      have h1 : psi (phiE rotR F) = a • psi (phiE rotR (I3 ^ 2 * I4 ^ 2)) +
          b • psi (phiE rotR (I4 ^ 2 * I6)) := by
        rw [hβR, hβR, hβR, ← hab, map_add, map_smul, map_smul]
      rw [hF rotR rotR_mem, ← hab] at h1
      have := congrArg (eval r) h1
      simpa only [map_add, MvPolynomial.smul_eval, eval_psi] using this
    have e1 := hrel ![1, 0]
    have e2 := hrel ![0, 1]
    rw [pt_one_zero, eval_R_10, eval_R_10] at e1
    rw [pt_zero_one, eval_R_01, eval_R_01] at e2
    simp only [map_mul, map_pow, eval_v_I3, eval_v_I4, eval_v_I6, eval_v'_I3, eval_v'_I4,
      eval_v'_I6, eval_w1_I3, eval_w1_I4, eval_w1_I6, eval_w2_I3, eval_w2_I4, eval_w2_I6] at e1 e2
    ring_nf at e1 e2
    simp only [I_sq, I_pow_three, I_pow_four, s5_sq, s5_pow_three, s5_pow_four] at e1 e2
    ring_nf at e1 e2
    have hb : b = 0 := by linear_combination (e1 + e2) / 20
    rw [hb] at e1
    have ha : a = 0 := by
      have : a * I = 0 := by linear_combination (128 / 45 : ℂ) * e1
      exact (mul_eq_zero.mp this).resolve_right I_ne_zero
    rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]

/-- **The invariant theory of `ico` on binary forms.** -/
theorem icoInvariantSpan (J10 : P3) (h10 : IcoInv J10) (h10h : J10.IsHomogeneous 10)
    (h10v : eval ![1, I, 0] J10 ≠ 0) :
    ∀ (n : ℕ) (F : P3), IcoInv F → F.IsHomogeneous n →
      psi F ∈ Submodule.span ℂ (psi '' monoSet J10 n) :=
  icoInvariantSpan_of_small J10 h10 h10h h10v psi_small_zero

end VOA.Classification.COne.OrbIco
