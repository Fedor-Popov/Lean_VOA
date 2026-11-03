import VOA.Classification.COne.PlusRat6TwTop
import VOA.Classification.COne.PlusRat5Final

/-! # The twisted kernels split: `V_{2m}⁺` is rational for every `m ≥ 2`

* Arithmetic on the twisted spectrum `φT a = (16a-1)/128`, `ψT b = (8b+1)/256`:
  `16384(5φ² - 5φ + 9ψ - 1)` is odd (`P1_tw`), `φ + 2 ≠ 0` (`P2_tw`), and for even `m`
  `128(c₁ φ + c₀) = 2·odd` with `c₁ = 2(4m-1)(m-1)`, `c₀ = 2n((m+n)² - s'²)` (`PE_tw`).
* `pairSplitting_twistedKernel`: every positive pair with lower weight `1/16` or `9/16` splits
  (`split_uniformG`; kernel rows: charged rows with their lattice models, twisted rows with the
  FLM twisted models `modelSpecG_twisted`; twisted kernels force `4 ∣ m`).
* `twistedKernelPairs_holds : TwistedKernelPairs`, `v2mPlusRationalFactGe2_holds`,
  `V2mPlus_stronglyRational_all`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4 PlusRational PlusRat5

/-! ## §1  Arithmetic of the twisted spectrum -/

theorem P1_tw (a b : ℕ) :
    polyV [((5 : ℂ), 2, 0), (-5, 1, 0), (9, 0, 1), (-1, 0, 0)] (φT a) (ψT b) ≠ 0 := by
  intro h
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, φT, ψT] at h
  have hZ : (((2 * (640 * (a : ℤ) ^ 2 - 5200 * a + 2304 * b - 7582) + 1 : ℤ)) : ℂ) = 0 := by
    push_cast
    linear_combination 16384 * h
  have hZ' : (2 * (640 * (a : ℤ) ^ 2 - 5200 * a + 2304 * b - 7582) + 1 : ℤ) = 0 := by
    exact_mod_cast hZ
  generalize 640 * (a : ℤ) ^ 2 - 5200 * a + 2304 * b - 7582 = K at hZ'
  omega

theorem P2_tw (a b : ℕ) : polyV [((1 : ℂ), 1, 0), (2, 0, 0)] (φT a) (ψT b) ≠ 0 := by
  intro h
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, φT] at h
  have hZ : (((16 * a + 255 : ℕ)) : ℂ) = 0 := by
    push_cast
    linear_combination 128 * h
  have := Nat.cast_eq_zero.mp hZ
  omega

theorem PE_tw (m k : ℕ) (hmk : m = 2 * k) (h' : ℂ) (s' : ℕ)
    (hre : 4 * (m : ℝ) * h'.re = (s' : ℝ) ^ 2) (n a b : ℕ) :
    polyV [(((2 * (2 * (m : ℝ)) ^ 2 - 5 * (2 * (m : ℝ)) + 2 : ℝ) : ℂ), 1, 0),
      (((2 * n * (((m : ℝ) + n) ^ 2 - 4 * m * h'.re) : ℝ) : ℂ), 0, 0)] (φT a) (ψT b) ≠ 0 := by
  rw [hre]
  intro h
  simp only [polyV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, φT] at h
  subst hmk
  have hZ : (((2 * (128 * (k : ℤ) ^ 2 * a - 8 * k ^ 2 - 80 * k * a + 5 * k + 8 * a - 1 +
      64 * n * ((2 * k + n) ^ 2 - s' ^ 2)) + 1 : ℤ)) : ℂ) = 0 := by
    push_cast at h ⊢
    linear_combination 64 * h
  have hZ' : (2 * (128 * (k : ℤ) ^ 2 * a - 8 * k ^ 2 - 80 * k * a + 5 * k + 8 * a - 1 +
      64 * n * ((2 * k + n) ^ 2 - s' ^ 2)) + 1 : ℤ) = 0 := by exact_mod_cast hZ
  generalize 128 * (k : ℤ) ^ 2 * a - 8 * k ^ 2 - 80 * k * a + 5 * k + 8 * a - 1 +
      64 * n * ((2 * k + n) ^ 2 - s' ^ 2) = K at hZ'
  omega

/-! ## §2  The twisted-kernel pairs -/

variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

theorem kernel_rows_of_twisted (l : Label m) (hm2 : 2 ≤ m)
    (hl : weight m l = 1 / 16 ∨ weight m l = 9 / 16) :
    (∃ r : Fin (m - 1), l = .inl r) ∨ ∃ i : Fin 8, l = .inr i ∧ 4 ≤ i.val := by
  rcases l with r | i
  · exact Or.inl ⟨r, rfl⟩
  · right
    refine ⟨i, rfl, ?_⟩
    have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm2
    have hhalf : ¬ ((m : ℚ) / 4 = 1 / 16 ∨ (m : ℚ) / 4 = 9 / 16) := by
      rintro (h | h)
      · linarith
      · have h4 : (4 * (m : ℚ)) = 9 := by linarith
        have : 4 * m = 9 := by exact_mod_cast h4
        omega
    fin_cases i
    · norm_num [weight] at hl
    · norm_num [weight] at hl
    · exact absurd (by simpa [weight] using hl) hhalf
    · exact absurd (by simpa [weight] using hl) hhalf
    all_goals simp

include hm2 in
/-- **Twisted kernels split.** -/
theorem pairSplitting_twistedKernel (p : Label m × Label m) (hp : p ∈ positivePairs m)
    (htw : weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16) :
    PairSplitting m hm p.1 p.2 := by
  -- twisted kernels force `4 ∣ m`
  have h4 : 4 ∣ m := by
    by_contra h4
    exact noTwistedKernel_of_not_four_dvd m hm2 h4 p hp htw
  obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨2 * (m / 4), by omega⟩
  obtain ⟨z, hz, hgap⟩ := gap_pos m hp
  have hw1ne : weight m p.1 ≠ 0 := by rcases htw with h | h <;> rw [h] <;> norm_num
  have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hz
  -- the upper rows are charged or half rows
  have hU : ∀ l : Label m, weight m l = weight m p.2 → PlusRat5.IsCH m l := by
    intro l hl
    rw [hgap] at hl
    rcases l with r | i
    · exact Or.inl ⟨r, rfl⟩
    · by_cases h2 : i = 2
      · subst h2; exact Or.inr (Or.inl rfl)
      by_cases h3 : i = 3
      · subst h3; exact Or.inr (Or.inr rfl)
      exfalso
      rcases exceptional_weights m i h2 h3 with h | h | h | h <;> rw [h] at hl <;>
        rcases htw with ht | ht <;> rw [ht] at hl
      all_goals linarith
  intro M _ _ A P hP hQ hb ht
  obtain ⟨z', hz', he⟩ := (mem_positivePairs_iff m p.1 p.2).mp hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨s', hs'1, hs'm, hws'⟩ := weight_CH m hm p.2 (hU p.2 rfl)
  have hd : ((weight m p.2 : ℚ) : ℂ) = ((weight m p.1 : ℚ) : ℂ) + ((z'.toNat : ℕ) : ℂ) := by
    rw [he]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hz'.le).symm
  have hwre : ((weight m p.2 : ℚ) : ℂ).re = (s' : ℝ) ^ 2 / (4 * m) := by
    rw [hws', Complex.ofReal_re]
  have hre4 : 4 * (m : ℝ) * ((weight m p.2 : ℚ) : ℂ).re = (s' : ℝ) ^ 2 := by
    rw [hwre]; field_simp
  have hdiff : ∀ jm : ℕ, ((weight m p.1 : ℚ) : ℂ) = ((((jm : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ) →
      s' ≠ jm := by
    intro jm hjm hs
    subst hs
    rw [← hjm, he] at hws'
    have : ((z' : ℂ)) = 0 := by linear_combination hws'
    have : z' = 0 := by exact_mod_cast this
    omega
  have hKpos : (0 : ℝ) < 2 * (2 * (m : ℝ)) ^ 2 - 5 * (2 * (m : ℝ)) + 2 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    nlinarith
  have hpos : ∀ n : ℕ, 1 ≤ n → 4 * (m : ℝ) * ((weight m p.2 : ℚ) : ℂ).re < ((m : ℝ) + n) ^ 2 := by
    intro n hn
    rw [hre4]
    have : (s' : ℝ) ≤ m := by exact_mod_cast hs'm
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (0 : ℝ) ≤ s' := by positivity
    nlinarith
  apply split_uniformG m hm hm2 A P hP hQ (h := ((weight m p.1 : ℚ) : ℂ))
    (h' := ((weight m p.2 : ℚ) : ℂ)) z'.toNat (by omega) hd hb ht
  · intro l hl
    rcases hU l (PlusRat5.weight_cast_inj m hl) with ⟨r, rfl⟩ | rfl | rfl
    · exact ⟨chiT_HP_zero m hm hm2 r 2 (Or.inl rfl), chiT_HP_zero m hm hm2 r 3 (Or.inr rfl)⟩
    · exact ⟨chiT_half_HP_zero m hm hm2 2 (Or.inl rfl) 2 (Or.inl rfl),
        chiT_half_HP_zero m hm hm2 2 (Or.inl rfl) 3 (Or.inr rfl)⟩
    · exact ⟨chiT_half_HP_zero m hm hm2 3 (Or.inr rfl) 2 (Or.inl rfl),
        chiT_half_HP_zero m hm hm2 3 (Or.inr rfl) 3 (Or.inr rfl)⟩
  · simp
  · exact hpos
  · intro l hl
    have hlw : weight m l = 1 / 16 ∨ weight m l = 9 / 16 := by
      rw [PlusRat5.weight_cast_inj m hl]; exact htw
    rcases kernel_rows_of_twisted m l hm2 hlw with ⟨r, rfl⟩ | ⟨i, rfl, hi⟩
    · -- a charged kernel row: its lattice model, natural spectrum
      refine ⟨_, _, modelSpecG_of_modelSpec m hm hm2 (modelSpec_charged m hm hm2 r _ ?_),
        fun s t => polyV_P1_ne s t, fun s t => polyV_P2_ne s t, fun n hn _ s t => ?_⟩
      · intro N n hfib
        rw [hws'] at hfib
        refine fiber_pos m hm _ (by omega) (by have := r.isLt; omega) s' hs'1 hs'm ?_ hfib
        have hne := hdiff (r.val + 1) (by rw [← hl]; simp [weight])
        intro h0; apply hne; exact_mod_cast h0
      · apply polyV_PE_ne _ _ hKpos
        have := hpos n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        nlinarith
    · -- a twisted kernel row: the FLM twisted model
      obtain ⟨t, odd, hto⟩ := twLabel_surj m i hi
      rw [← hto]
      exact ⟨φT, ψT, modelSpecG_twisted m hm hm2 t odd _, P1_tw, P2_tw,
        fun n _ _ a b => PE_tw m k hk _ s' hre4 n a b⟩

end VOA.Classification.COne.PlusRat6

namespace VOA.Classification.COne
open PlusRat6 PlusRat5 PlusRat2 PlusResonantPairs PlusCharacterTable

/-- **`TwistedKernelPairs` holds.** -/
theorem twistedKernelPairs_holds : TwistedKernelPairs :=
  fun m hm hm2 p hp htw => pairSplitting_twistedKernel m hm hm2 p hp htw

/-- **`V_{2m}⁺` is rational for every `m ≥ 2`.** -/
theorem v2mPlusRationalFactGe2_holds : V2mPlusRationalFactGe2 :=
  rationality_of_twistedKernel twistedKernelPairs_holds

/-- **`V_{2m}⁺` is strongly rational for every `m ≥ 2`.** -/
theorem V2mPlus_stronglyRational_all (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    StronglyRational (V2mPlus m hm) :=
  V2mPlus_stronglyRational_of_unordered m hm hm2
    (unordered_of_twisted m hm hm2 (fun p hp htw => pairSplitting_twistedKernel m hm hm2 p hp htw))

end VOA.Classification.COne
