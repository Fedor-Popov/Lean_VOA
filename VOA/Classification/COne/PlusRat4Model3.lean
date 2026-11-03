import VOA.Classification.COne.PlusRat4Top3
import VOA.Classification.COne.PlusRat4SignModel

/-! # Level three: Kac, and the degree-three space of the charged model

* `exists_comb_of_span_triple`: three independent vectors in the span of three vectors span it.
* `kac3`: on a top vector (`h ≠ 0`, `4h ≠ 1`, `h ≠ 1`), `L(1)` and `L(2)` separate
  `V₁ = L(-1)³y`, `V₂ = L(-1)L(-2)y`, `V₃ = L(-3)y` (determinant `-36(h-1)²` after `L(-1)²y`,
  `L(-2)y` are separated by `RQ_indep`).
* `lat_weight_three_mem_span`, `lat_deg3`: every vector of weight `h_s + 3` of `V_{L+λ_s}`
  (`s ≤ m - 4`) is `aV₁ + bV₂ + cV₃`.
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

theorem exists_comb_of_span_triple {E : Type*} [AddCommGroup E] [Module ℂ E]
    {f1 f2 f3 u1 u2 u3 v : E}
    (hv : v ∈ Submodule.span ℂ (Set.range ![f1, f2, f3]))
    (hu1 : u1 ∈ Submodule.span ℂ (Set.range ![f1, f2, f3]))
    (hu2 : u2 ∈ Submodule.span ℂ (Set.range ![f1, f2, f3]))
    (hu3 : u3 ∈ Submodule.span ℂ (Set.range ![f1, f2, f3]))
    (hind : ∀ a b c : ℂ, a • u1 + b • u2 + c • u3 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ a b c : ℂ, v = a • u1 + b • u2 + c • u3 := by
  classical
  set S := Submodule.span ℂ (Set.range ![f1, f2, f3])
  set T := Submodule.span ℂ (Set.range ![u1, u2, u3])
  have hli : LinearIndependent ℂ ![u1, u2, u3] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    obtain ⟨h0, h1, h2⟩ := hind _ _ _ hg
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hTS : T ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu1
    · exact hu2
    · exact hu3
  have hT : Module.finrank ℂ T = 3 := by
    rw [finrank_span_eq_card hli]; simp
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hS : Module.finrank ℂ S ≤ 3 := by
    have := finrank_range_le_card (R := ℂ) (b := ![f1, f2, f3])
    rw [Set.finrank] at this
    simpa using this
  have hTeq : T = S := Submodule.eq_of_le_of_finrank_le hTS (by rw [hT]; exact hS)
  rw [← hTeq] at hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hc
  exact ⟨c 0, c 1, c 2, hc.symm⟩

/-! ## §2  Kac at level three -/

section Kac3
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {N : Type} [AddCommGroup N] [Module ℂ N]
  (B : WeakModule (V2mPlus m hm) N) {y : N} {h : ℂ}

theorem kac3_scalars (h1 : h - 1 ≠ 0) (a b c : ℂ) (e1 : a * (6 * h + 6) + b * 3 = 0)
    (e2 : b * (2 * h + 4) + c * 4 = 0)
    (e3 : a * (18 * h + 6) + b * (4 * h + 19 / 2) + c * 5 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hd : (-36 * (h - 1) ^ 2 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 h1)
  have ha : (-36 * (h - 1) ^ 2) * a = 0 := by
    linear_combination (-18 - 6 * h) * e1 - 15 * e2 + 12 * e3
  have hb : (-36 * (h - 1) ^ 2) * b = 0 := by
    linear_combination (24 + 72 * h) * e1 + (30 + 30 * h) * e2 - (24 + 24 * h) * e3
  have hc : (-36 * (h - 1) ^ 2) * c = 0 := by
    linear_combination (-24 - 84 * h - 36 * h ^ 2) * e1 + (-39 - 27 * h - 24 * h ^ 2) * e2 +
      (24 + 36 * h + 12 * h ^ 2) * e3
  exact ⟨(mul_eq_zero.mp ha).resolve_left hd, (mul_eq_zero.mp hb).resolve_left hd,
    (mul_eq_zero.mp hc).resolve_left hd⟩

include hm2 in
/-- `L(1)` and `L(2)` of `aV₁ + bV₂ + cV₃`. -/
theorem L12_V (hyΩ : y ∈ Omega B) (hyL : L0 B y = h • y) (a b c : ℂ) :
    mode (B.YM (V2mPlus m hm).conformalVector) 2
        (a • mode (B.YM (V2mPlus m hm).conformalVector) 0 (mode (B.YM (V2mPlus m hm).conformalVector) 0
          (mode (B.YM (V2mPlus m hm).conformalVector) 0 y)) +
          b • mode (B.YM (V2mPlus m hm).conformalVector) 0 (mode (B.YM (V2mPlus m hm).conformalVector) (-1) y) +
          c • mode (B.YM (V2mPlus m hm).conformalVector) (-2) y) =
        (a * (6 * h + 6) + b * 3) • mode (B.YM (V2mPlus m hm).conformalVector) 0
          (mode (B.YM (V2mPlus m hm).conformalVector) 0 y) +
          (b * (2 * h + 4) + c * 4) • mode (B.YM (V2mPlus m hm).conformalVector) (-1) y ∧
      mode (B.YM (V2mPlus m hm).conformalVector) 3
        (a • mode (B.YM (V2mPlus m hm).conformalVector) 0 (mode (B.YM (V2mPlus m hm).conformalVector) 0
          (mode (B.YM (V2mPlus m hm).conformalVector) 0 y)) +
          b • mode (B.YM (V2mPlus m hm).conformalVector) 0 (mode (B.YM (V2mPlus m hm).conformalVector) (-1) y) +
          c • mode (B.YM (V2mPlus m hm).conformalVector) (-2) y) =
        (a * (18 * h + 6) + b * (4 * h + 19 / 2) + c * 5) •
          mode (B.YM (V2mPlus m hm).conformalVector) 0 y := by
  constructor
  · rw [map_add, map_add, map_smul, map_smul, map_smul, L1_V1 m hm hm2 B hyΩ hyL,
      L1_V2 m hm hm2 B hyΩ hyL, L1_V3 m hm hm2 B hyΩ hyL]
    module
  · rw [map_add, map_add, map_smul, map_smul, map_smul, L2_V1 m hm hm2 B hyΩ hyL,
      L2_V2 m hm hm2 B hyΩ hyL, L2_V3 m hm hm2 B hyΩ hyL]
    module

include hm2 in
/-- Kac at level three: `V₁, V₂, V₃` are independent. -/
theorem kac3 (hyΩ : y ∈ Omega B) (hyL : L0 B y = h • y) (hy0 : y ≠ 0) (hh : h ≠ 0)
    (h14 : 4 * h - 1 ≠ 0) (h1 : h - 1 ≠ 0) (a b c : ℂ)
    (habc : a • mode (B.YM (V2mPlus m hm).conformalVector) 0 (mode (B.YM (V2mPlus m hm).conformalVector) 0
          (mode (B.YM (V2mPlus m hm).conformalVector) 0 y)) +
          b • mode (B.YM (V2mPlus m hm).conformalVector) 0 (mode (B.YM (V2mPlus m hm).conformalVector) (-1) y) +
          c • mode (B.YM (V2mPlus m hm).conformalVector) (-2) y = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨g1, g2⟩ := L12_V m hm hm2 B hyΩ hyL a b c
  rw [habc, map_zero] at g1 g2
  obtain ⟨e1, e2⟩ := RQ_indep m hm hm2 B hyΩ hyL hy0 hh h14 _ _ g1.symm
  have hL0 : mode (B.YM (V2mPlus m hm).conformalVector) 0 y ≠ 0 := by
    intro h0
    have := L1_L B hyΩ hyL
    rw [h0, map_zero] at this
    rcases smul_eq_zero.mp this.symm with h2 | h2
    · exact hh (by linear_combination h2 / 2)
    · exact hy0 h2
  have e3 := (smul_eq_zero.mp g2.symm).resolve_right hL0
  exact kac3_scalars h1 a b c e1 e2 e3

end Kac3

/-! ## §3  The charged lattice model at weight `h + 3` -/

section Lat3
variable (m : ℕ) (hm : 1 ≤ m)

theorem range_three {E : Type*} (a b c : E) : Set.range ![a, b, c] = {a, b, c} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- The weight-`(h_s + 3)` space of `V_{L+λ_s}` (`s ≤ m - 4`). -/
theorem lat_weight_three_mem_span (r : Fin (m - 1)) (hs : r.val + 5 ≤ m) {v : LatModuleGen (latP m)}
    (hv : v ∈ (latticeModule m hm ((r.val + 1 : ℕ) : ℤ)).weight (hC m r + 3)) :
    v ∈ Submodule.span ℂ (Set.range ![latStateGen (latP m) (X ((2 : ℕ), a0 m)) 0,
      latStateGen (latP m) (X ((1 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) 0,
      latStateGen (latP m) (X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m) * X ((0 : ℕ), a0 m)) 0]) := by
  rw [range_three]
  set s : ℤ := ((r.val + 1 : ℕ) : ℤ) with hsdef
  change v ∈ shiftWeightSpace (latP m) (glueLat m s) (glueIota m s) (glueDelta m s) (hC m r + 3) at hv
  refine (iSup₂_le (fun p hp => ?_) : shiftWeightSpace (latP m) (glueLat m s) (glueIota m s)
    (glueDelta m s) (hC m r + 3) ≤ _) hv
  obtain ⟨w, n⟩ := p
  change ℤ at n
  obtain ⟨hw, hwt⟩ := hp
  simp only at hw hwt
  rw [shiftWeight_rankOne m hm s, hC_eq] at hwt
  have hre := congrArg Complex.re hwt
  simp only [Complex.ofReal_re, Complex.add_re] at hre
  have h3re : (3 : ℂ).re = 3 := by norm_num
  rw [h3re] at hre
  have hwn : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hw
  rw [hwn] at hre
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hZ : (4 * m * w + (2 * m * n + s) ^ 2 : ℤ) = s ^ 2 + 12 * m := by
    have hsR : ((s : ℤ) : ℝ) = (r.val : ℝ) + 1 := by rw [hsdef]; push_cast; ring
    have : ((4 * m * w + (2 * m * n + s) ^ 2 : ℤ) : ℝ) = ((s ^ 2 + 12 * m : ℤ) : ℝ) := by
      push_cast
      field_simp at hre
      push_cast at hre
      rw [hsR]
      rw [hsR] at hre
      linarith
    exact_mod_cast this
  have hmZ : (4 : ℤ) ≤ m - s := by omega
  have hs1 : (1 : ℤ) ≤ s := by omega
  have hmz : (0 : ℤ) < m := by omega
  have hkey : w + m * n ^ 2 + n * s = 3 := by
    have h4 : (4 * m : ℤ) * (w + m * n ^ 2 + n * s) = 4 * m * 3 := by nlinarith [hZ]
    exact mul_left_cancel₀ (by positivity) h4
  have hn : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have h1 : (1 : ℤ) ≤ -n := by omega
      have h2 : (4 : ℤ) ≤ m * (-n) - s := by nlinarith
      have h3 : (m : ℤ) * n ^ 2 + n * s = (-n) * (m * (-n) - s) := by ring
      have h4 : (1 : ℤ) * 4 ≤ (-n) * (m * (-n) - s) := mul_le_mul h1 h2 (by norm_num) (by omega)
      omega
    · exact h
    · have : m * n ^ 2 + n * s ≥ 5 := by nlinarith
      omega
  subst hn
  have hw3 : w = 3 := by simpa using hkey
  subst hw3
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  have hq3 : q ∈ gradingWN (rank (latP m)) 3 := by
    rw [gradingZN_of_nonneg (by norm_num)] at hq; exact hq
  have hspan := fock_weight_three_mem_span m hq3
  have hmap := Submodule.mem_map_of_mem (f := mkEα (latP m) ((0 : ℤ) : (latP m).carrier)) hspan
  rw [Submodule.map_span, Set.image_insert_eq, Set.image_pair] at hmap
  exact hmap

variable (hm2 : 2 ≤ m)

include hm2 in
/-- Every vector of weight `h_s + 3` of the charged model (`s ≤ m - 4`, `h ∉ {1/4, 1}`) is
`aV₁ + bV₂ + cV₃`. -/
theorem lat_deg3 (r : Fin (m - 1)) (hs : r.val + 5 ≤ m) (h14 : 4 * hC m r - 1 ≠ 0)
    (h1 : hC m r - 1 ≠ 0) {v : LatModuleGen (latP m)} (hv : v ∈ (Ns m hm r).weight (hC m r + 3)) :
    ∃ a b c : ℂ, v = a • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0
          (mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0
            (mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0 (latVacuumGen (latP m)))) +
        b • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0
          (mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (-1) (latVacuumGen (latP m))) +
        c • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (-2) (latVacuumGen (latP m)) := by
  set e := latVacuumGen (latP m)
  set ω := (V2mPlus m hm).conformalVector
  have hw0 := es_weight m hm r
  have hwt : ∀ {μ : ℂ} {v' : LatModuleGen (latP m)}, v' ∈ (Ns m hm r).weight μ → ∀ n : ℤ,
      mode ((Ns m hm r).YM ω) n v' ∈ (Ns m hm r).weight (μ + 1 - n) := by
    intro μ v' hv' n
    have h' := mode_mem_weight (Ns m hm r) (V2mPlus m hm).conformal_mem hv' n
    have hc' : μ + ((2 : ℤ) : ℂ) - (n : ℂ) - 1 = μ + 1 - n := by push_cast; ring
    rwa [hc'] at h'
  have hV1 : mode ((Ns m hm r).YM ω) 0 (mode ((Ns m hm r).YM ω) 0 (mode ((Ns m hm r).YM ω) 0 e)) ∈
      (Ns m hm r).weight (hC m r + 3) := by
    have := hwt (hwt (hwt hw0 0) 0) 0
    convert this using 2; push_cast; ring
  have hV2 : mode ((Ns m hm r).YM ω) 0 (mode ((Ns m hm r).YM ω) (-1) e) ∈
      (Ns m hm r).weight (hC m r + 3) := by
    have := hwt (hwt hw0 (-1)) 0
    convert this using 2; push_cast; ring
  have hV3 : mode ((Ns m hm r).YM ω) (-2) e ∈ (Ns m hm r).weight (hC m r + 3) := by
    have := hwt hw0 (-2)
    convert this using 2; push_cast; ring
  have hs3 : r.val + 3 ≤ m := by omega
  exact exists_comb_of_span_triple (lat_weight_three_mem_span m hm r hs hv)
    (lat_weight_three_mem_span m hm r hs hV1) (lat_weight_three_mem_span m hm r hs hV2)
    (lat_weight_three_mem_span m hm r hs hV3)
    (kac3 m hm hm2 (Ns m hm r).toWeakModule (es_Omega m hm r) (es_L0 m hm r)
      (latVacuumGen_ne_zero' m hm) (hC_ne_zero m hm2 r) h14 h1)

end Lat3

end VOA.Classification.COne.PlusRat4
