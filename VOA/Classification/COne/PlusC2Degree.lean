/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.LatticeC2

/-!
# The polynomial-degree filtration of a lattice VOA and the modes of Fock states

For an even positive-definite lattice `L`, filter `V_L = Fock ⊗ ℂ[L]` by the **total polynomial
degree** of the Fock part, charge by charge: `Fil e γ = span{x^s ⊗ e^γ : |s| ≤ e}` (`e : ℤ`, so
`Fil e γ = 0` for `e < 0`).

## Main results (general `L`)

* `smul_bosonState_latStateGen` — all modes of `h_a(−1)𝟙` on `p ⊗ e^γ`: multiplication
  (`n < 0`), the charge `⟨γ⟩_a` (`n = 0`), a derivation (`n > 0`).
* `word_smul_mem_Fil` — for a creation word `u = h(−n₁)⋯h(−n_r)𝟙` of length `r` (charge 0), every
  mode `u₍N₎` maps `Fil e γ` into `Fil (e + r) γ`, and into `Fil (e + r − 1) γ` when `N ≥ 0`.
* `word_smul_neg_one_sub_mem_Fil` — the **leading term of the normal-ordered product**:
  `u₍₋₁₎(p ⊗ e^γ) − (u·p) ⊗ e^γ ∈ Fil (e + r − 1) γ` for `p` of degree `≤ e`.

Both are proved by induction on the word, through the Borcherds iterate `mode_iterate`
(`u = h₍₋ₖ₋₁₎u'`): every summand is `h₍neg₎(u'₍·₎x)` or `u'₍·₎(h₍≥0₎x)`, and `h₍≥0₎` does not raise
the degree while `u'₍≥0₎` loses one.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.IntegralLattice HeisenbergN MvPolynomial

namespace PlusC2

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

/-! ## §1  The filtration -/

/-- The Fock filtration by total degree: `span{x^s : |s| ≤ e}`. -/
noncomputable def FilF (e : ℤ) : Submodule ℂ (FockN (rank L)) :=
  Submodule.span ℂ {p | ∃ s : (ℕ × Fin (rank L)) →₀ ℕ, ((s.sum fun _ k => k : ℕ) : ℤ) ≤ e ∧
    p = monomial s 1}

/-- The charge-`γ` embedding `p ↦ p ⊗ e^γ`. -/
noncomputable def stateMap (γ : L.carrier) : FockN (rank L) →ₗ[ℂ] LatModuleGen L :=
  (TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip (eGen L γ)

theorem stateMap_apply (γ : L.carrier) (p : FockN (rank L)) :
    stateMap L γ p = latStateGen L p γ := rfl

/-- `Fil e γ = FilF e ⊗ e^γ`. -/
noncomputable def Fil (e : ℤ) (γ : L.carrier) : Submodule ℂ (LatModuleGen L) :=
  (FilF L e).map (stateMap L γ)

theorem FilF_mono {e e' : ℤ} (h : e ≤ e') : FilF L e ≤ FilF L e' := by
  apply Submodule.span_mono
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, hs.trans h, rfl⟩

theorem Fil_mono {e e' : ℤ} (h : e ≤ e') (γ : L.carrier) : Fil L e γ ≤ Fil L e' γ :=
  Submodule.map_mono (FilF_mono L h)

theorem monomial_mem_FilF (s : (ℕ × Fin (rank L)) →₀ ℕ) (c : ℂ) {e : ℤ}
    (h : ((s.sum fun _ k => k : ℕ) : ℤ) ≤ e) : monomial s c ∈ FilF L e := by
  have : monomial s c = c • monomial s (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, h, rfl⟩)

theorem mem_FilF_of_totalDegree_le (p : FockN (rank L)) {e : ℤ} (h : (p.totalDegree : ℤ) ≤ e) :
    p ∈ FilF L e := by
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s hs => monomial_mem_FilF L s _ ?_
  have := le_totalDegree hs
  exact le_trans (by exact_mod_cast this) h

theorem latStateGen_mem_Fil (p : FockN (rank L)) (γ : L.carrier) {e : ℤ}
    (h : (p.totalDegree : ℤ) ≤ e) : latStateGen L p γ ∈ Fil L e γ :=
  ⟨p, mem_FilF_of_totalDegree_le L p h, rfl⟩

/-- Multiplication by a variable raises the degree by one. -/
theorem X_mul_mem_FilF (v : ℕ × Fin (rank L)) {e : ℤ} {p : FockN (rank L)} (hp : p ∈ FilF L e) :
    X v * p ∈ FilF L (e + 1) := by
  refine Submodule.span_induction (p := fun p _ => X v * p ∈ FilF L (e + 1)) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨s, hs, rfl⟩
    rw [X, monomial_mul, one_mul]
    refine monomial_mem_FilF L _ _ ?_
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Nat.cast_add, Nat.cast_one]
    omega
  · simp only [mul_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- A partial derivative lowers the degree by one. -/
theorem pderiv_mem_FilF (v : ℕ × Fin (rank L)) {e : ℤ} {p : FockN (rank L)} (hp : p ∈ FilF L e) :
    pderiv v p ∈ FilF L (e - 1) := by
  refine Submodule.span_induction (p := fun p _ => pderiv v p ∈ FilF L (e - 1)) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨s, hs, rfl⟩
    rw [pderiv_monomial]
    by_cases hsv : s v = 0
    · rw [hsv, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
    · refine monomial_mem_FilF L _ _ ?_
      have hle : Finsupp.single v 1 ≤ s := by
        intro w
        rw [Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · exact Nat.zero_le _
      have hsum : ((s - Finsupp.single v 1).sum fun _ k => k) + 1 = s.sum fun _ k => k := by
        have := Finsupp.sum_add_index' (f := s - Finsupp.single v 1) (g := Finsupp.single v 1)
          (h := fun _ k => k) (fun _ => rfl) (fun _ _ _ => rfl)
        rw [tsub_add_cancel_of_le hle, Finsupp.sum_single_index rfl] at this
        exact this.symm
      omega
  · simp only [map_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [(pderiv v).map_smul]; exact Submodule.smul_mem _ _ hx

theorem FilF_neg {e : ℤ} (he : e < 0) : FilF L e = ⊥ := by
  rw [FilF, Submodule.span_eq_bot]
  rintro _ ⟨s, hs, rfl⟩
  exfalso
  have : (0 : ℤ) ≤ ((s.sum fun _ k => k : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

theorem Fil_neg {e : ℤ} (he : e < 0) (γ : L.carrier) : Fil L e γ = ⊥ := by
  rw [Fil, FilF_neg L he, Submodule.map_bot]

/-! ## §2  The modes of `h_a(−1)𝟙` -/

/-- All modes of the boson state on `p ⊗ e^γ`. -/
theorem smul_bosonState_latStateGen (a : Fin (rank L)) (n : ℤ) (p : FockN (rank L))
    (γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (bosonState L a) n (latStateGen L p γ)
      = latStateGen L (oscN (rank L) 1 a n p) γ +
        (if n = 0 then chargeCoord L γ a • latStateGen L p γ else 0) := by
  rw [PreVertexAlgebra.smul_def, latVOA_Y_bosonState, mode_apply, alphaLatGen_apply]
  rw [LinearMap.add_apply]
  congr 1
  · simp only [latStateGen, LinearMap.rTensor_tmul, currentN_apply]
    rw [show -(-n - 1) - 1 = n by ring]
  · by_cases hn : n = 0
    · subst hn
      rw [if_pos (by ring), if_pos rfl, zGradeOpGen_latStateGen]
    · rw [if_neg (by omega), if_neg hn, LinearMap.zero_apply]

theorem oscN_mem_FilF (a : Fin (rank L)) (n : ℤ) {e : ℤ} {p : FockN (rank L)} (hp : p ∈ FilF L e) :
    oscN (rank L) 1 a n p ∈ FilF L (e + if n < 0 then 1 else 0) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [oscN_neg _ _ _ hn, mulXN_apply, if_pos hn]
    exact X_mul_mem_FilF L _ hp
  · subst hn; rw [oscN_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  · rw [oscN_pos _ _ _ hn, if_neg (by omega), add_zero]
    simp only [LinearMap.smul_apply, pderivLMN_apply]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact FilF_mono L (by omega) (pderiv_mem_FilF L _ hp)

/-- The boson modes on the filtration: `h₍ₙ₎` raises the degree by one if `n < 0`, else not. -/
theorem smul_bosonState_mem_Fil (a : Fin (rank L)) (n : ℤ) {e : ℤ} {γ : L.carrier}
    {x : LatModuleGen L} (hx : x ∈ Fil L e γ) :
    (latticeVOAGen L hEven hPos).smul (bosonState L a) n x ∈ Fil L (e + if n < 0 then 1 else 0) γ := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [stateMap_apply, smul_bosonState_latStateGen]
  refine Submodule.add_mem _ ⟨_, oscN_mem_FilF L a n hp, rfl⟩ ?_
  by_cases h0 : n = 0
  · rw [if_pos h0]
    refine Submodule.smul_mem _ _ ⟨p, ?_, rfl⟩
    rw [if_neg (by omega), add_zero]; exact hp
  · rw [if_neg h0]; exact Submodule.zero_mem _

theorem smul_bosonState_neg_latStateGen (a : Fin (rank L)) (k : ℕ) (p : FockN (rank L))
    (γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (bosonState L a) (-(k : ℤ) - 1) (latStateGen L p γ)
      = latStateGen L (X (k, a) * p) γ :=
  latVOA_smul_bosonState L hEven hPos a k p γ

/-! ## §3  Creation words -/

theorem body_support_finite {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (u a b : 𝒱) (ℓ N : ℤ) :
    (Function.support (fun i : ℕ => ((-1:ℂ)^i * gBinom ℓ i) •
      (W.smul u (ℓ - i) (W.smul a (N + i) b)
        - ((-1:ℂ)^ℓ) • W.smul a (ℓ + N - i) (W.smul u i b)))).Finite := by
  obtain ⟨Nab, hNab⟩ := W.toPreVertexAlgebra.smul_eventually_zero a b
  obtain ⟨Nub, hNub⟩ := W.toPreVertexAlgebra.smul_eventually_zero u b
  apply Set.Finite.subset (Set.finite_Iio ((max (Nab - N) Nub).toNat))
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_Iio, not_lt] at hc
  apply hi
  have hge : (max (Nab - N) Nub : ℤ) ≤ (i : ℤ) := by
    rcases le_or_gt 0 (max (Nab - N) Nub) with h0 | h0
    · rw [← Int.toNat_of_nonneg h0]; exact_mod_cast hc
    · omega
  rw [hNab (N + i) (by omega), hNub i (by omega)]
  simp

theorem word_nil : wordStateLatGen L [] 0 = (latticeVOAGen L hEven hPos).vacuum := by
  rw [wordStateLatGen_nil, latChargeGen_zero]; rfl

theorem word_cons (k : ℕ) (a : Fin (rank L)) (rest : List (ℕ × Fin (rank L))) :
    wordStateLatGen L ((k, a) :: rest) 0
      = (latticeVOAGen L hEven hPos).smul (bosonState L a) (-(k : ℤ) - 1) (wordStateLatGen L rest 0) := by
  rw [wordStateLatGen_eq, wordStateLatGen_eq, ← latStateGen, ← latStateGen,
    latVOA_smul_bosonState, wordStateN_cons]

/-- **Degree bound for the modes of a creation word** (charge 0, length `r`): `u₍N₎` raises the
degree by at most `r`, and by at most `r − 1` when `N ≥ 0`. -/
theorem word_smul_mem_Fil : ∀ (l : List (ℕ × Fin (rank L))) (N e : ℤ) (γ : L.carrier)
    (x : LatModuleGen L), x ∈ Fil L e γ →
    (latticeVOAGen L hEven hPos).smul (wordStateLatGen L l 0) N x ∈ Fil L (e + l.length) γ ∧
      (0 ≤ N → (latticeVOAGen L hEven hPos).smul (wordStateLatGen L l 0) N x ∈
        Fil L (e + l.length - 1) γ)
  | [], N, e, γ, x, hx => by
    rw [word_nil L hEven hPos, PreVertexAlgebra.smul_vacuum_left]
    refine ⟨?_, fun hN => ?_⟩
    · split_ifs
      · simpa using hx
      · exact Submodule.zero_mem _
    · rw [if_neg (by omega)]; exact Submodule.zero_mem _
  | (k, a) :: rest, N, e, γ, x, hx => by
    set W := latticeVOAGen L hEven hPos
    set H := bosonState L a
    set u' := wordStateLatGen L rest 0
    have IH := fun N' e' x' (hx' : x' ∈ Fil L e' γ) => word_smul_mem_Fil rest N' e' γ x' hx'
    rw [word_cons L hEven hPos, VertexOperatorAlgebra.mode_iterate W H u' (-(k : ℤ) - 1) N x]
    have hlen : (((k, a) :: rest).length : ℤ) = rest.length + 1 := by simp
    have hH0 : ∀ (i : ℕ) (y : LatModuleGen L) (e' : ℤ), y ∈ Fil L e' γ → W.smul H i y ∈ Fil L e' γ := by
      intro i y e' hy
      have := smul_bosonState_mem_Fil L hEven hPos a (i : ℤ) hy
      rwa [if_neg (by omega), add_zero] at this
    have hHn : ∀ (j : ℤ) (y : LatModuleGen L) (e' : ℤ), j < 0 → y ∈ Fil L e' γ →
        W.smul H j y ∈ Fil L (e' + 1) γ := by
      intro j y e' hj hy
      have := smul_bosonState_mem_Fil L hEven hPos a j hy
      rwa [if_pos hj] at this
    refine ⟨?_, fun hN => ?_⟩
    · refine finsum_mem_submodule_pd _ _ fun i => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · have h1 := (IH (N + i) e x hx).1
        have h2 := hHn (-(k : ℤ) - 1 - i) _ _ (by omega) h1
        refine Fil_mono L ?_ γ h2
        rw [hlen]; omega
      · refine Submodule.smul_mem _ _ ?_
        have h1 := (IH (-(k : ℤ) - 1 + N - i) e _ (hH0 i x e hx)).1
        refine Fil_mono L ?_ γ h1
        rw [hlen]; omega
    · refine finsum_mem_submodule_pd _ _ fun i => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · have h1 := (IH (N + i) e x hx).2 (by omega)
        have h2 := hHn (-(k : ℤ) - 1 - i) _ _ (by omega) h1
        refine Fil_mono L ?_ γ h2
        rw [hlen]; omega
      · refine Submodule.smul_mem _ _ ?_
        have h1 := (IH (-(k : ℤ) - 1 + N - i) e _ (hH0 i x e hx)).1
        refine Fil_mono L ?_ γ h1
        rw [hlen]; omega

/-- **The leading term of a creation word's `(−1)`-mode**:
`u₍₋₁₎(p ⊗ e^γ) − (u·p) ⊗ e^γ ∈ Fil (e + r − 1) γ` for `p` of degree `≤ e`. -/
theorem word_smul_neg_one_sub_mem_Fil : ∀ (l : List (ℕ × Fin (rank L))) (e : ℤ) (γ : L.carrier)
    (p : FockN (rank L)), p ∈ FilF L e →
    (latticeVOAGen L hEven hPos).smul (wordStateLatGen L l 0) (-1) (latStateGen L p γ)
      - latStateGen L (wordStateN l * p) γ ∈ Fil L (e + l.length - 1) γ
  | [], e, γ, p, _ => by
    rw [word_nil L hEven hPos, PreVertexAlgebra.smul_vacuum_left, if_pos rfl, wordStateN_nil, one_mul, sub_self]
    exact Submodule.zero_mem _
  | (k, a) :: rest, e, γ, p, hp => by
    set W := latticeVOAGen L hEven hPos
    set H := bosonState L a
    set u' := wordStateLatGen L rest 0
    set x := latStateGen L p γ with hxdef
    have hx : x ∈ Fil L e γ := ⟨p, hp, rfl⟩
    have hlen : (((k, a) :: rest).length : ℤ) = rest.length + 1 := by simp
    set Q := Fil L (e + ((k, a) :: rest).length - 1) γ with hQ
    have hH0 : ∀ (i : ℕ) (y : LatModuleGen L) (e' : ℤ), y ∈ Fil L e' γ → W.smul H i y ∈ Fil L e' γ := by
      intro i y e' hy
      have := smul_bosonState_mem_Fil L hEven hPos a (i : ℤ) hy
      rwa [if_neg (by omega), add_zero] at this
    have hHn : ∀ (j : ℤ) (y : LatModuleGen L) (e' : ℤ), j < 0 → y ∈ Fil L e' γ →
        W.smul H j y ∈ Fil L (e' + 1) γ := by
      intro j y e' hj hy
      have := smul_bosonState_mem_Fil L hEven hPos a j hy
      rwa [if_pos hj] at this
    set lead := latStateGen L (wordStateN ((k, a) :: rest) * p) γ with hlead
    rw [word_cons L hEven hPos, VertexOperatorAlgebra.mode_iterate W H u' (-(k : ℤ) - 1) (-1) x]
    set f : ℕ → LatModuleGen L := fun i => ((-1:ℂ)^i * gBinom (-(k : ℤ) - 1) i) •
      (W.smul H (-(k : ℤ) - 1 - i) (W.smul u' (-1 + i) x)
        - ((-1:ℂ)^(-(k : ℤ) - 1)) • W.smul u' (-(k : ℤ) - 1 + -1 - i) (W.smul H i x)) with hf
    set g : ℕ → LatModuleGen L := fun i => if i = 0 then lead else 0 with hg
    have hfin : (Function.support f).Finite := body_support_finite W H u' x (-(k : ℤ) - 1) (-1)
    have hgfin : (Function.support g).Finite := by
      apply Set.Finite.subset (Set.finite_singleton 0)
      intro i hi
      rw [Function.mem_support] at hi
      by_contra h
      exact hi (by rw [hg]; simp only [if_neg (show i ≠ 0 from h)])
    have hgsum : ∑ᶠ i, g i = lead := by
      rw [hg, finsum_eq_single _ 0 (fun i hi => by simp only [if_neg hi])]
      simp
    have hterm : ∀ i, f i - g i ∈ Q := by
      intro i
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        simp only [hf, hg, if_pos, pow_zero, gBinom_zero, mul_one, one_smul, Nat.cast_zero, sub_zero,
          add_zero]
        -- `H₍₋ₖ₋₁₎(u'₍₋₁₎x) − lead ∈ Q` and the second summand is in `Q`
        have hIH := word_smul_neg_one_sub_mem_Fil rest e γ p hp
        set y := W.smul u' (-1) x - latStateGen L (wordStateN rest * p) γ with hy
        have hy' : W.smul u' (-1) x = latStateGen L (wordStateN rest * p) γ + y := by
          rw [hy]; abel
        have hl : latStateGen L (X (k, a) * (wordStateN rest * p)) γ = lead := by
          rw [hlead, wordStateN_cons, mul_assoc]
        rw [hy', PreVertexAlgebra.smul_add_right, smul_bosonState_neg_latStateGen, hl]
        have hA : W.smul H (-(k : ℤ) - 1) y ∈ Q := by
          have := hHn (-(k : ℤ) - 1) y _ (by omega) hIH
          refine Fil_mono L ?_ γ this
          rw [hlen]; omega
        have hB : ((-1:ℂ)^(-(k : ℤ) - 1)) • W.smul u' (-(k : ℤ) - 1 + -1) (W.smul H 0 x) ∈ Q := by
          refine Submodule.smul_mem _ _ ?_
          have := (word_smul_mem_Fil L hEven hPos rest (-(k : ℤ) - 1 + -1) e γ _ (hH0 0 x e hx)).1
          refine Fil_mono L ?_ γ this
          rw [hlen]; omega
        have := Submodule.sub_mem _ hA hB
        convert this using 1
        abel
      · have hg0 : g i = 0 := by rw [hg]; simp only [if_neg (show i ≠ 0 by omega)]
        rw [hg0, sub_zero]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
        · have h1 := (word_smul_mem_Fil L hEven hPos rest (-1 + i) e γ x hx).2 (by omega)
          have h2 := hHn (-(k : ℤ) - 1 - i) _ _ (by omega) h1
          refine Fil_mono L ?_ γ h2
          rw [hlen]; omega
        · have h1 := (word_smul_mem_Fil L hEven hPos rest (-(k : ℤ) - 1 + -1 - i) e γ _ (hH0 i x e hx)).1
          refine Fil_mono L ?_ γ h1
          rw [hlen]; omega
    rw [← hgsum, ← finsum_sub_distrib hfin hgfin]
    exact finsum_mem_submodule_pd _ _ hterm

end PlusC2

end VOA.Classification.COne
