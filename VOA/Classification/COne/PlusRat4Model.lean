import VOA.Classification.COne.PlusRat4Top
import VOA.Classification.COne.PlusRat3Eight

/-! # Degree-two weight spaces of the models

* `exists_comb_of_span_pair` (linear algebra): two independent vectors in the span of two vectors
  span it.
* `RQ_indep`: on a top vector `y` of a `V⁺`-module with `h ≠ 0`, `4h ≠ 1`, the vectors
  `L(-1)²y` and `L(-2)y` are linearly independent (`L(1)`, `L(2)` and the Kac determinant
  `(4h-1)²`).
* `lat_weight_two_mem_span`: for a charged row `s ≤ m - 3`, the weight-`(h_s + 2)` space of the
  lattice model `V_{L+λ_s}` lies in the span of `x₁ ⊗ e⁰` and `x₀² ⊗ e⁰`.
* `lat_deg2`: every degree-two vector of that model is `a L(-1)²e + b L(-2)e`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-! ## §1  Linear algebra -/

theorem exists_comb_of_span_pair {E : Type*} [AddCommGroup E] [Module ℂ E] {f1 f2 u1 u2 v : E}
    (hv : v ∈ Submodule.span ℂ {f1, f2}) (hu1 : u1 ∈ Submodule.span ℂ {f1, f2})
    (hu2 : u2 ∈ Submodule.span ℂ {f1, f2})
    (hind : ∀ s t : ℂ, s • u1 + t • u2 = 0 → s = 0 ∧ t = 0) :
    ∃ a b : ℂ, v = a • u1 + b • u2 := by
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hv
  obtain ⟨a1, b1, h1⟩ := Submodule.mem_span_pair.mp hu1
  obtain ⟨a2, b2, h2⟩ := Submodule.mem_span_pair.mp hu2
  by_cases hd : a1 * b2 - a2 * b1 = 0
  · exfalso
    have hb := hind b2 (-b1) (by
      rw [← h1, ← h2]
      have : (b2 * a1 - b1 * a2) • f1 = 0 := by
        rw [show b2 * a1 - b1 * a2 = a1 * b2 - a2 * b1 by ring, hd, zero_smul]
      rw [← this]; module)
    obtain ⟨hb2, hb1⟩ := hb
    have hb1' : b1 = 0 := by simpa using hb1
    subst hb2 hb1'
    have ha := hind a2 (-a1) (by rw [← h1, ← h2]; module)
    obtain ⟨ha2, ha1⟩ := ha
    have ha1' : a1 = 0 := by simpa using ha1
    subst ha1'
    have := (hind 1 0 (by rw [← h1]; simp)).1
    exact one_ne_zero this
  · refine ⟨(p * b2 - q * a2) / (a1 * b2 - a2 * b1), (a1 * q - b1 * p) / (a1 * b2 - a2 * b1), ?_⟩
    have hd2 : b2 * a1 - a2 * b1 ≠ 0 := fun h => hd (by linear_combination h)
    rw [← hpq, ← h1, ← h2]
    match_scalars <;> field_simp <;> ring

/-! ## §2  Independence of `L(-1)²y` and `L(-2)y` -/

section Indep
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {N : Type} [AddCommGroup N] [Module ℂ N]
  (B : WeakModule (V2mPlus m hm) N) {y : N} {h : ℂ}

include hm2 in
theorem RQ_indep (hyΩ : y ∈ Omega B) (hyL : L0 B y = h • y) (hy0 : y ≠ 0) (hh : h ≠ 0)
    (h14 : 4 * h - 1 ≠ 0) (s t : ℂ)
    (hst : s • mode (B.YM (V2mPlus m hm).conformalVector) 0
        (mode (B.YM (V2mPlus m hm).conformalVector) 0 y) +
      t • mode (B.YM (V2mPlus m hm).conformalVector) (-1) y = 0) : s = 0 ∧ t = 0 := by
  have hL0 : mode (B.YM (V2mPlus m hm).conformalVector) 0 y ≠ 0 := by
    intro h0
    have := L1_L B hyΩ hyL
    rw [h0, map_zero] at this
    rcases smul_eq_zero.mp this.symm with h1 | h1
    · exact hh (by linear_combination h1 / 2)
    · exact hy0 h1
  have e1 := congrArg (fun v => mode (B.YM (V2mPlus m hm).conformalVector) 2 v) hst
  have e2 := congrArg (fun v => mode (B.YM (V2mPlus m hm).conformalVector) 3 v) hst
  simp only at e1 e2
  have q1 := L1_Q1 m hm B hyΩ hm2
  have q2 := L2_Q1 m hm B hyΩ hyL hm2
  rw [HP_one] at q1 q2
  rw [map_add, map_smul, map_smul, L1_R B hyΩ hyL, q1, map_zero, smul_smul, smul_smul,
    ← add_smul] at e1
  rw [map_add, map_smul, map_smul, L2_R B hyΩ hyL, q2, map_zero, smul_smul, smul_smul,
    ← add_smul] at e2
  have f1 : s * (4 * h + 2) + t * 3 = 0 := by
    rcases smul_eq_zero.mp e1 with h1 | h1
    · exact h1
    · exact absurd h1 hL0
  have f2 : s * (6 * h) + t * (4 * h + 1 / 2) = 0 := by
    rcases smul_eq_zero.mp e2 with h1 | h1
    · exact h1
    · exact absurd h1 hy0
  have hdet : (4 * h - 1) ^ 2 ≠ 0 := pow_ne_zero 2 h14
  have hs : (4 * h - 1) ^ 2 * s = 0 := by linear_combination (4 * h + 1 / 2) * f1 - 3 * f2
  have ht : (4 * h - 1) ^ 2 * t = 0 := by linear_combination (4 * h + 2) * f2 - 6 * h * f1
  exact ⟨(mul_eq_zero.mp hs).resolve_left hdet, (mul_eq_zero.mp ht).resolve_left hdet⟩

end Indep

/-! ## §3  The charged lattice model at degree two -/

section Lat
variable (m : ℕ) (hm : 1 ≤ m)

/-- The weight-`(h_s + 2)` space of `V_{L+λ_s}` (`s ≤ m - 3`). -/
theorem lat_weight_two_mem_span (r : Fin (m - 1)) (hs : r.val + 4 ≤ m) {v : LatModuleGen (latP m)}
    (hv : v ∈ (latticeModule m hm ((r.val + 1 : ℕ) : ℤ)).weight (hC m r + 2)) :
    v ∈ Submodule.span ℂ {latStateGen (latP m) (X ((1 : ℕ), a0 m)) 0,
      latStateGen (latP m) (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) 0} := by
  set s : ℤ := ((r.val + 1 : ℕ) : ℤ) with hsdef
  change v ∈ shiftWeightSpace (latP m) (glueLat m s) (glueIota m s) (glueDelta m s) (hC m r + 2) at hv
  refine (iSup₂_le (fun p hp => ?_) : shiftWeightSpace (latP m) (glueLat m s) (glueIota m s)
    (glueDelta m s) (hC m r + 2) ≤ _) hv
  obtain ⟨w, n⟩ := p
  change ℤ at n
  obtain ⟨hw, hwt⟩ := hp
  simp only at hw hwt
  rw [shiftWeight_rankOne m hm s, hC_eq] at hwt
  have hre := congrArg Complex.re hwt
  simp only [Complex.ofReal_re, Complex.add_re] at hre
  have h2re : (2 : ℂ).re = 2 := by norm_num
  rw [h2re] at hre
  have hwn : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hw
  rw [hwn] at hre
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hZ : (4 * m * w + (2 * m * n + s) ^ 2 : ℤ) = s ^ 2 + 8 * m := by
    have hsR : ((s : ℤ) : ℝ) = (r.val : ℝ) + 1 := by rw [hsdef]; push_cast; ring
    have : ((4 * m * w + (2 * m * n + s) ^ 2 : ℤ) : ℝ) = ((s ^ 2 + 8 * m : ℤ) : ℝ) := by
      push_cast
      field_simp at hre
      push_cast at hre
      rw [hsR]
      rw [hsR] at hre
      linarith
    exact_mod_cast this
  have hmZ : (3 : ℤ) ≤ m - s := by omega
  have hs1 : (1 : ℤ) ≤ s := by omega
  have hmz : (0 : ℤ) < m := by omega
  have hkey : w + m * n ^ 2 + n * s = 2 := by
    have h4 : (4 * m : ℤ) * (w + m * n ^ 2 + n * s) = 4 * m * 2 := by nlinarith [hZ]
    exact mul_left_cancel₀ (by positivity) h4
  have hn : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have h1 : (1 : ℤ) ≤ -n := by omega
      have h2 : (3 : ℤ) ≤ m * (-n) - s := by nlinarith
      have h3 : (m : ℤ) * n ^ 2 + n * s = (-n) * (m * (-n) - s) := by ring
      have h4 : (1 : ℤ) * 3 ≤ (-n) * (m * (-n) - s) := mul_le_mul h1 h2 (by norm_num) (by omega)
      omega
    · exact h
    · have : m * n ^ 2 + n * s ≥ 3 := by nlinarith
      omega
  subst hn
  have hw2 : w = 2 := by simpa using hkey
  subst hw2
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  have hq2 : q ∈ gradingWN (rank (latP m)) 2 := by
    rw [gradingZN_of_nonneg (by norm_num)] at hq; exact hq
  have hspan := fock_weight_two_mem_span m hq2
  have hmap := Submodule.mem_map_of_mem (f := mkEα (latP m) ((0 : ℤ) : (latP m).carrier)) hspan
  rw [Submodule.map_span, Set.image_pair] at hmap
  exact hmap

variable (hm2 : 2 ≤ m)

/-- The lattice top as `TopData`. -/
theorem lat_topData (r : Fin (m - 1)) (hs : r.val + 3 ≤ m) :
    TopData (Ns m hm r).toWeakModule (chiT m hm hm2 (.inl r)) (hC m r) (latVacuumGen (latP m)) where
  omega := es_Omega m hm r
  char := lat_top_char m hm hm2 r
  L0 := es_L0 m hm r
  line := by
    intro j c hc
    have hte : mode ((Ns m hm r).YM c) (j - 2) (latVacuumGen (latP m)) ∈
        (Ns m hm r).weight (hC m r + 1) := by
      have h := mode_mem_weight (Ns m hm r) hc (es_weight m hm r) (j - 2)
      have hc' : hC m r + (j : ℂ) - ((j - 2 : ℤ) : ℂ) - 1 = hC m r + 1 := by push_cast; ring
      rwa [hc'] at h
    exact lat_weight_next_eq m hm hm2 r hs hte

include hm2 in
/-- Every degree-two vector of the charged model (`s ≤ m - 3`, `4h ≠ 1`) is
`a L(-1)²e + b L(-2)e`. -/
theorem lat_deg2 (r : Fin (m - 1)) (hs : r.val + 4 ≤ m) (h14 : 4 * hC m r - 1 ≠ 0)
    {k : ℤ} {t : VP m hm} (ht : t ∈ (V2mPlus m hm).grading k) :
    ∃ a b : ℂ, mode ((Ns m hm r).YM t) (k - 3) (latVacuumGen (latP m)) =
      a • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0
          (mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0 (latVacuumGen (latP m))) +
        b • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (-1) (latVacuumGen (latP m)) := by
  set e := latVacuumGen (latP m)
  set ω := (V2mPlus m hm).conformalVector
  have hw : ∀ {j : ℤ} {c : VP m hm}, c ∈ (V2mPlus m hm).grading j →
      mode ((Ns m hm r).YM c) (j - 3) e ∈ (Ns m hm r).weight (hC m r + 2) := by
    intro j c hc
    have h := mode_mem_weight (Ns m hm r) hc (es_weight m hm r) (j - 3)
    have hc' : hC m r + (j : ℂ) - ((j - 3 : ℤ) : ℂ) - 1 = hC m r + 2 := by push_cast; ring
    rwa [hc'] at h
  have hR : mode ((Ns m hm r).YM ω) 0 (mode ((Ns m hm r).YM ω) 0 e) ∈
      (Ns m hm r).weight (hC m r + 2) := by
    have h1 := mode_mem_weight (Ns m hm r) (V2mPlus m hm).conformal_mem (es_weight m hm r) 0
    have h2 := mode_mem_weight (Ns m hm r) (V2mPlus m hm).conformal_mem h1 0
    have hc' : hC m r + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 =
        hC m r + 2 := by push_cast; ring
    rwa [hc'] at h2
  have hQ : mode ((Ns m hm r).YM ω) (-1) e ∈ (Ns m hm r).weight (hC m r + 2) := by
    have := hw (V2mPlus m hm).conformal_mem
    rwa [show ((2 : ℤ) - 3) = -1 by norm_num] at this
  have hs3 : r.val + 3 ≤ m := by omega
  have hh := hC_ne_zero m hm2 r
  exact exists_comb_of_span_pair (lat_weight_two_mem_span m hm r hs (hw ht))
    (lat_weight_two_mem_span m hm r hs hR) (lat_weight_two_mem_span m hm r hs hQ)
    (RQ_indep m hm hm2 (Ns m hm r).toWeakModule (es_Omega m hm r) (es_L0 m hm r)
      (latVacuumGen_ne_zero' m hm) hh h14)

end Lat

end VOA.Classification.COne.PlusRat4
