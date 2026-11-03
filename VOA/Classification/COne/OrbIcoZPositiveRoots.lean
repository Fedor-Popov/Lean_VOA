import VOA.Classification.COne.OrbIcoZFactors

/-! Every root of the certified candidate is zero or has strictly positive real part. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

private theorem linearFactor_zero_or_positive (n d : ℕ) (hd : 0 < d)
    (hn : n = 0 ∨ 0 < n) (h : ℂ)
    (he : (zp [-(n : ℚ), (d : ℚ)]).eval h = 0) : h = 0 ∨ 0 < h.re := by
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have heq : h = (n : ℂ) / (d : ℂ) := by
    apply (eq_div_iff hdc).mpr
    norm_num [zp] at he
    linear_combination he
  rcases hn with hn | hn
  · left
    rw [heq, hn]
    simp
  · right
    rw [heq]
    have hh : (n : ℂ) / (d : ℂ) = ((n : ℝ) / (d : ℝ) : ℝ) := by
      simp
    rw [hh, Complex.ofReal_re]
    exact div_pos (by exact_mod_cast hn) (by exact_mod_cast hd)

theorem candidate_root_zero_or_positive {h : ℂ} (hp : (zp icoCandidateList).eval h = 0) :
    h = 0 ∨ 0 < h.re := by
  rw [icoCandidate_factorization, Polynomial.eval_list_prod] at hp
  have hm := List.prod_eq_zero_iff.mp hp
  simp only [icoFactorLists, List.map_map, Function.comp_def, List.mem_map] at hm
  obtain ⟨p, hp, he⟩ := hm
  obtain ⟨hd, hn⟩ := icoFactors_positive p hp
  exact linearFactor_zero_or_positive p.1 p.2 hd hn h he

/-- The two coprime extra factors can never vanish simultaneously. -/
theorem icoExtra_no_common_root (h : ℂ) :
    ¬ ((zp icoExtra9).eval h = 0 ∧ (zp icoExtra10).eval h = 0) := by
  rintro ⟨h9, h10⟩
  have he := congrArg (fun P : ℂ[X] => P.eval h) icoExtra_bezout
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, h9, h10,
    mul_zero, add_zero] at he
  exact zero_ne_one he

end VOA.Classification.COne.OrbIcoZ
