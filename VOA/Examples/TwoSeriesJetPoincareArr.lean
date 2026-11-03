/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesJetPoincareTwo

/-!
# The jet-ideal Poincaré lemma for every `n`, from an arrangement inclusion

The duality argument of `TwoSeriesJetPoincareTwo` works for every `n` once the commutative-algebra
step is available.  That step is isolated as the named input

  `ArrangementInclusion n`: a symmetric polynomial `f ∈ ℂ[x_0, …, x_{k-1}]` vanishing on every
  `n`-fold diagonal `{x_s = x_{s'} for s, s' ∈ S}`, `|S| = n`, and lying in
  `(x_0^N, …, x_{k-1}^N)`, is a combination `Σ_l x_l^N Y_l` with `Y_l` vanishing on every
  `n`-fold diagonal not involving `x_l`.

* `collapseTo s₀ S`, `VanishOn S Y` (`Y` vanishes on the diagonal of `S`), `Wn`;
* `coeff_rename_collapse` — the coefficients of `Y|_{diagonal of S}` are the fibre sums
  `Σ_{|l| = j} Y_{e' + l}`;
* `pol_prod_X_mul` — the polarization of `T_{l_1} ⋯ T_{l_n} c`;
* `dot_pol_jet_n` — `⟨R pol_B(G), Y⟩ = 0` for `G ∈ J_n` and `Y` vanishing on the `n`-fold
  diagonals inside `B`;
* `jetPoincare_of_arrangement` — **`ArrangementInclusion n → JetPoincare n N k E`** (all slots),
  hence `JetPoincareCoreT0 n`;
* `arrangementInclusion_two` — the input holds for `n = 2` (`JetPoincareVdm`).

Everything is proved outright.  `ArrangementInclusion n` is the named input; it is
proved for every `n ≥ 2`: `GenIncl.arrangementInclusion` (`TwoSeriesGenIncl.lean`).
-/

namespace VOA.TwoSeries.JetPoincareArr

open MvPolynomial Finset JetPoincareVdm JetPoincareDual JetPoincareTwo StrictModel HighJet LiftDegN

noncomputable section

variable {k : ℕ}

/-! ### Diagonals -/

/-- The substitution `x_s ↦ x_{s₀}` for `s ∈ S`. -/
def collapseTo (s₀ : Fin k) (S : Finset (Fin k)) (i : Fin k) : Fin k := if i ∈ S then s₀ else i

/-- `Y` vanishes on the diagonal `{x_s = x_{s'} : s, s' ∈ S}`. -/
def VanishOn (S : Finset (Fin k)) (Y : XP k) : Prop := ∀ s₀ ∈ S, rename (collapseTo s₀ S) Y = 0

/-- `W_n = span {x_l^N Y : Y vanishes on every n-fold diagonal not involving x_l}`. -/
def Wn (k N n : ℕ) : Submodule ℂ (XP k) :=
  Submodule.span ℂ {Z | ∃ (l : Fin k) (Y : XP k),
    (∀ S : Finset (Fin k), #S = n → l ∉ S → VanishOn S Y) ∧ Z = X l ^ N * Y}

/-- **The arrangement inclusion** (the named input for `n ≥ 3`). -/
def ArrangementInclusion (n : ℕ) : Prop :=
  ∀ (k N : ℕ) (f : XP k), (∀ σ : Equiv.Perm (Fin k), rename σ f = f) → f ∈ Lid k N →
    (∀ S : Finset (Fin k), #S = n → VanishOn S f) → f ∈ Wn k N n

/-! ### Coefficients of a collapse -/

theorem mapDomain_coord (g : Fin k → Fin k) (e : Fin k →₀ ℕ) (a : Fin k) :
    (e.mapDomain g) a = ∑ i ∈ e.support, if g i = a then e i else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  simp only [Finsupp.single_apply]

theorem coeff_rename_sum (g : Fin k → Fin k) (p : XP k) (d : Fin k →₀ ℕ) :
    coeff d (rename g p) = ∑ e ∈ p.support, if e.mapDomain g = d then coeff e p else 0 := by
  classical
  conv_lhs => rw [as_sum p]
  rw [map_sum, coeff_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [rename_monomial, coeff_monomial]

/-- **The fibre sums**: for `e'` free of `S = τ(Fin n)` and `s₀ ∈ S`, the coefficient of
`x_{s₀}^j x^{e'}` in `Y|_{x_S = x_{s₀}}` is `Σ_{|l| = j} Y_{e' + τ_* l}`. -/
theorem coeff_rename_collapse {n : ℕ} {τ : Fin n → Fin k} (hτ : Function.Injective τ)
    {s₀ : Fin k} (hs₀ : s₀ ∈ univ.image τ) {e' : Fin k →₀ ℕ}
    (he' : ∀ i ∈ univ.image τ, e' i = 0) (j : ℕ) (Y : XP k) :
    coeff (e' + Finsupp.single s₀ j) (rename (collapseTo s₀ (univ.image τ)) Y) =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j, coeff (e' + l.mapDomain τ) Y := by
  classical
  set S := univ.image τ with hS
  set ρ := collapseTo s₀ S with hρ
  set d := e' + Finsupp.single s₀ j with hd
  have hρS : ∀ i ∈ S, ρ i = s₀ := fun i hi => by simp [hρ, collapseTo, hi]
  have hρn : ∀ i ∉ S, ρ i = i := fun i hi => by simp [hρ, collapseTo, hi]
  -- the image of an arrangement
  have himg : ∀ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j,
      (e' + l.mapDomain τ).mapDomain ρ = d := by
    intro l hl
    rw [mem_finsuppAntidiag] at hl
    rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, hd]
    congr 1
    · ext a
      rw [mapDomain_coord]
      have : ∀ i ∈ e'.support, (if ρ i = a then e' i else 0) = if i = a then e' i else 0 := by
        intro i hi
        have hiS : i ∉ S := fun h => (Finsupp.mem_support_iff.mp hi) (he' i h)
        rw [hρn i hiS]
      rw [sum_congr rfl this, sum_ite_eq']
      split_ifs with h
      · rfl
      · exact (Finsupp.notMem_support_iff.mp h).symm
    · have hc : (ρ ∘ τ) = fun _ => s₀ := funext fun r => hρS _ (mem_image_of_mem τ (mem_univ r))
      rw [hc, Finsupp.mapDomain, Finsupp.sum, ← Finsupp.single_finsetSum]
      congr 1
      rw [← hl.1]
      exact sum_subset (subset_univ _) fun r _ hr => Finsupp.notMem_support_iff.mp hr
  -- every preimage is an arrangement
  have hpre : ∀ e, e.mapDomain ρ = d →
      ∃ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j, e' + l.mapDomain τ = e := by
    intro e he
    refine ⟨Finsupp.equivFunOnFinite.symm fun r => e (τ r), ?_, ?_⟩
    · rw [mem_finsuppAntidiag]
      refine ⟨?_, fun _ _ => mem_univ _⟩
      have h1 := congrArg (fun f : Fin k →₀ ℕ => f s₀) he
      simp only [hd, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, he' s₀ hs₀,
        zero_add, mapDomain_coord] at h1
      rw [← h1]
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      rw [← sum_image (f := fun i => e i) (fun x _ y _ h => hτ h)]
      have : ∀ i ∈ e.support, (if ρ i = s₀ then e i else 0) = if i ∈ S then e i else 0 := by
        intro i _
        by_cases hiS : i ∈ S
        · rw [hρS i hiS, if_pos rfl, if_pos hiS]
        · rw [hρn i hiS, if_neg (fun h : i = s₀ => hiS (h ▸ hs₀)), if_neg hiS]
      rw [sum_congr rfl this, ← sum_filter]
      refine (sum_subset (fun i hi => (mem_filter.mp hi).2) fun i hiS hi => ?_).symm
      by_contra hne
      exact hi (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hiS⟩)
    · ext a
      rw [Finsupp.coe_add, Pi.add_apply]
      by_cases haS : a ∈ S
      · obtain ⟨r, -, rfl⟩ := mem_image.mp haS
        rw [he' _ haS, zero_add, Finsupp.mapDomain_apply hτ]
        rfl
      · rw [Finsupp.mapDomain_notin_range _ _ (fun ⟨r, hr⟩ => haS (hr ▸ mem_image_of_mem τ
          (mem_univ r))), add_zero]
        have h1 := congrArg (fun f : Fin k →₀ ℕ => f a) he
        have hsa : s₀ ≠ a := fun h => haS (h ▸ hs₀)
        simp only [hd, Finsupp.coe_add, Pi.add_apply, mapDomain_coord, Finsupp.single_apply,
          if_neg hsa, add_zero] at h1
        rw [← h1]
        have : ∀ i ∈ e.support, (if ρ i = a then e i else 0) = if i = a then e i else 0 := by
          intro i _
          by_cases hiS : i ∈ S
          · rw [hρS i hiS, if_neg hsa, if_neg (fun h : i = a => haS (h ▸ hiS))]
          · rw [hρn i hiS]
        rw [sum_congr rfl this, sum_ite_eq']
        split_ifs with h
        · rfl
        · exact (Finsupp.notMem_support_iff.mp h).symm
  -- compare the two sums
  have himage := sum_image (s := finsuppAntidiag (univ : Finset (Fin n)) j)
    (g := fun l => e' + l.mapDomain τ) (f := fun e => coeff e Y)
    (fun x _ y _ h => Finsupp.mapDomain_injective hτ (add_left_cancel h))
  rw [coeff_rename_sum, ← sum_filter, ← himage]
  refine sum_subset (fun e he => ?_) fun e he hne => ?_
  · obtain ⟨he1, he2⟩ := mem_filter.mp he
    obtain ⟨l, hl, rfl⟩ := hpre e he2
    exact mem_image_of_mem _ hl
  · obtain ⟨l, hl, rfl⟩ := mem_image.mp he
    by_contra h0
    exact hne (mem_filter.mpr ⟨mem_support_iff.mpr h0, himg l hl⟩)

/-! ### The jets of `Tⁿ` and their polarization -/

theorem jg_eq_sum (n j : ℕ) :
    jg n j = ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j, ∏ r : Fin n, (X (l r) : TPoly) := by
  classical
  have h : (tSer ^ n : PowerSeries TPoly) = ∏ _r : Fin n, tSer := by
    rw [prod_const, card_univ, Fintype.card_fin]
  rw [jg, h, PowerSeries.coeff_prod]
  refine sum_congr rfl fun l _ => prod_congr rfl fun r _ => ?_
  rw [tSer, PowerSeries.coeff_mk]

/-- The injective `n`-tuples of points of `B`. -/
def Inj (n : ℕ) (B : Finset (Fin k)) : Finset (Fin n → Fin k) :=
  univ.filter fun τ => Function.Injective τ ∧ ∀ r, τ r ∈ B

theorem mem_Inj {n : ℕ} {B : Finset (Fin k)} {τ : Fin n → Fin k} :
    τ ∈ Inj n B ↔ Function.Injective τ ∧ ∀ r, τ r ∈ B := by
  simp [Inj]

/-- **The polarization of `T_{l_0} ⋯ T_{l_{n-1}} c`**: a sum over injective `n`-tuples. -/
theorem pol_prod_X_mul : ∀ (n : ℕ) (B : Finset (Fin k)) (l : Fin n → ℕ) (c : TPoly),
    pol B ((∏ r : Fin n, X (l r)) * c) =
      ∑ τ ∈ Inj n B, (∏ r : Fin n, (X (τ r) : XP k) ^ (l r)) * pol (B \ univ.image τ) c
  | 0, B, l, c => by
    classical
    have hI : Inj 0 B = univ := by
      ext τ
      simp only [mem_Inj, mem_univ, iff_true]
      exact ⟨Function.injective_of_subsingleton _, fun r => r.elim0⟩
    rw [hI, Fintype.sum_unique]
    simp only [univ_eq_empty, prod_empty, one_mul, image_empty, sdiff_empty]
  | n + 1, B, l, c => by
    classical
    rw [Fin.prod_univ_succ, mul_assoc, pol_X_mul]
    simp only [pol_prod_X_mul n, mul_sum]
    rw [sum_sigma']
    refine sum_bij' (fun x _ => Fin.cons x.1 x.2) (fun τ _ => ⟨τ 0, Fin.tail τ⟩)
      (fun x hx => ?_) (fun τ hτ => ?_) (fun x _ => ?_) (fun τ _ => ?_) (fun x hx => ?_)
    · obtain ⟨hi, hτ'⟩ := mem_sigma.mp hx
      obtain ⟨hinj, hmem⟩ := mem_Inj.mp hτ'
      refine mem_Inj.mpr ⟨Fin.cons_injective_iff.mpr ⟨fun ⟨r, hr⟩ => ?_, hinj⟩, fun r => ?_⟩
      · exact (ne_of_mem_erase (hr ▸ hmem r)) rfl
      · refine Fin.cases ?_ (fun r => ?_) r
        · simpa using hi
        · simpa using mem_of_mem_erase (hmem r)
    · obtain ⟨hinj, hmem⟩ := mem_Inj.mp hτ
      refine mem_sigma.mpr ⟨hmem 0, mem_Inj.mpr ⟨fun a b h => ?_, fun r => ?_⟩⟩
      · exact Fin.succ_injective _ (hinj h)
      · exact mem_erase.mpr ⟨fun h => Fin.succ_ne_zero r (hinj h), hmem _⟩
    · simp
    · simp
    · obtain ⟨hi, hτ'⟩ := mem_sigma.mp hx
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have himg : B \ univ.image (Fin.cons x.1 x.2 : Fin (n + 1) → Fin k) =
          (B.erase x.1) \ univ.image x.2 := by
        ext a
        simp only [mem_sdiff, mem_image, mem_univ, true_and, mem_erase, Fin.exists_fin_succ,
          Fin.cons_zero, Fin.cons_succ, not_or]
        tauto
      rw [himg]; ring

theorem prod_X_pow_eq_monomial {n : ℕ} (τ : Fin n → Fin k) (l : Fin n →₀ ℕ) :
    (∏ r : Fin n, (X (τ r) : XP k) ^ (l r)) = monomial (l.mapDomain τ) 1 := by
  classical
  have h : l.mapDomain τ = ∑ r : Fin n, Finsupp.single (τ r) (l r) := by
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => Finsupp.single_zero _)]
  rw [h, monomial_sum_one]
  exact prod_congr rfl fun r _ => X_pow_eq_monomial

theorem dot_monomial_mul_left (m : Fin k →₀ ℕ) (P Y : XP k) :
    dot (monomial m 1 * P) Y = ∑ e' ∈ P.support, coeff e' P * coeff (e' + m) Y := by
  conv_lhs => rw [as_sum P]
  rw [mul_sum, dot_sum_left]
  refine sum_congr rfl fun e' _ => ?_
  rw [monomial_mul, one_mul, dot_comm, dot_monomial_right, add_comm, mul_comm]

/-- **Orthogonality to `J_n`**: `⟨R pol_B(G), Y⟩ = 0` for `G ∈ J_n` (`n ≥ 1`), `R` free of the
`x_i` (`i ∈ B`) and `Y` vanishing on every `n`-fold diagonal inside `B`. -/
theorem dot_pol_jet_n {n : ℕ} (hn : 1 ≤ n) {G : TPoly} (hG : G ∈ jetIdealT n)
    (B : Finset (Fin k)) {R : XP k} (hR : ∀ i ∈ B, i ∉ R.vars) {Y : XP k}
    (hY : ∀ S ⊆ B, #S = n → VanishOn S Y) : dot (R * pol B G) Y = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  rw [Finsupp.sum, pol_sum, mul_sum, dot_sum_left]
  refine sum_eq_zero fun j _ => ?_
  have hj : (PowerSeries.coeff j (tSer ^ n) : TPoly) = jg n j := rfl
  rw [smul_eq_mul, hj, mul_comm (c j), jg_eq_sum, sum_mul, pol_sum]
  simp only [pol_prod_X_mul, mul_sum, dot_sum_left]
  rw [sum_comm]
  refine sum_eq_zero fun τ hτ => ?_
  obtain ⟨hinj, hmem⟩ := mem_Inj.mp hτ
  set S := univ.image τ with hS
  set P := R * pol (B \ S) (c j) with hP
  have hPS : ∀ e' ∈ P.support, ∀ i ∈ S, e' i = 0 := by
    intro e' he' i hi
    have hiB : i ∈ B := by obtain ⟨r, -, rfl⟩ := mem_image.mp hi; exact hmem r
    refine coeff_eq_zero_of_not_mem_vars (fun h => ?_) he'
    rcases mem_union.mp (vars_mul _ _ h) with h | h
    · exact hR i hiB h
    · exact pol_vars _ _ i (fun h' => (mem_sdiff.mp h').2 hi) h
  have hterm : ∀ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j,
      dot (R * ((∏ r : Fin n, (X (τ r) : XP k) ^ (l r)) * pol (B \ S) (c j))) Y =
        ∑ e' ∈ P.support, coeff e' P * coeff (e' + l.mapDomain τ) Y := by
    intro l _
    rw [prod_X_pow_eq_monomial, mul_left_comm, dot_monomial_mul_left]
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_eq_zero fun e' he' => ?_
  rw [← mul_sum]
  refine mul_eq_zero_of_right _ ?_
  have hs₀ : τ ⟨0, hn⟩ ∈ S := mem_image_of_mem τ (mem_univ _)
  rw [← coeff_rename_collapse hinj hs₀ (hPS e' he') j Y]
  have hSB : S ⊆ B := fun i hi => by obtain ⟨r, -, rfl⟩ := mem_image.mp hi; exact hmem r
  have hcard : #S = n := by rw [hS, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  rw [hY S hSB hcard (τ ⟨0, hn⟩) hs₀, coeff_zero]

/-- `⟨pol(F), x_l^N Y⟩ = 0` for `Y` vanishing on the `n`-fold diagonals avoiding `x_l`, when
`∂F/∂T_M ∈ J_n` for all `M ≥ N`. -/
theorem dot_pol_pow_mul_n {n : ℕ} (hn : 1 ≤ n) {N : ℕ} {F : TPoly}
    (hF : ∀ M, N ≤ M → pderiv M F ∈ jetIdealT n) (l : Fin k) {Y : XP k}
    (hY : ∀ S : Finset (Fin k), #S = n → l ∉ S → VanishOn S Y) :
    dot (pol univ F) ((X l : XP k) ^ N * Y) = 0 := by
  classical
  rw [pol_expand (subset_refl _) (mem_univ l), dot_sum_left]
  refine sum_eq_zero fun M _ => ?_
  rw [X_pow_eq_monomial, X_pow_eq_monomial,
    dot_shift l (pol_vars _ _ l (fun h => (ne_of_mem_erase h) rfl)) Y]
  split_ifs with hNM
  · refine dot_pol_jet_n hn (hF M hNM) (univ.erase l) (fun i hi h => ?_)
      (fun S hS hcard => hY S hcard (fun hl => (ne_of_mem_erase (hS hl)) rfl))
    rw [vars_monomial one_ne_zero] at h
    have : i = l := by
      by_contra hne
      have := Finsupp.mem_support_iff.mp h
      rw [Finsupp.single_apply, if_neg (Ne.symm hne)] at this
      exact this rfl
    exact (ne_of_mem_erase hi) this
  · rfl

/-- **`⟨pol(F), W_n⟩ = 0`** when `∂F/∂T_M ∈ J_n` for all `M ≥ N`. -/
theorem dot_pol_Wn {n : ℕ} (hn : 1 ≤ n) {N : ℕ} {F : TPoly}
    (hF : ∀ M, N ≤ M → pderiv M F ∈ jetIdealT n) {w : XP k} (hw : w ∈ Wn k N n) :
    dot (pol univ F) w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, Y, hY, rfl⟩ := hx
    exact dot_pol_pow_mul_n hn hF l hY
  | zero => exact dot_zero_right _
  | add x y _ _ hx hy => rw [dot_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [dot_smul_right, hx, mul_zero]

/-! ### The dual polynomial: vanishing on the diagonals and symmetry -/

theorem degree_mapDomain {n : ℕ} (τ : Fin n → Fin k) (l : Fin n →₀ ℕ) :
    (l.mapDomain τ).degree = l.degree := by
  rw [Finsupp.mapDomain, map_finsuppSum]
  simp only [Finsupp.degree_single]
  rfl

theorem toMS_split {n : ℕ} {τ : Fin n → Fin k} (hτ : Function.Injective τ) {e' : Fin k →₀ ℕ}
    (he' : ∀ i ∈ univ.image τ, e' i = 0) (l : Fin n →₀ ℕ) :
    toMS univ (e' + l.mapDomain τ) =
      toMS (univ \ univ.image τ) e' + ∑ r : Fin n, Finsupp.single (l r) 1 := by
  classical
  rw [toMS, ← sum_sdiff (subset_univ (univ.image τ)), toMS]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi' : i ∉ univ.image τ := (mem_sdiff.mp hi).2
    rw [Finsupp.coe_add, Pi.add_apply, Finsupp.mapDomain_notin_range _ _ (fun ⟨r, hr⟩ =>
      hi' (hr ▸ mem_image_of_mem τ (mem_univ r))), add_zero]
  · rw [sum_image (fun x _ y _ h => hτ h)]
    refine sum_congr rfl fun r _ => ?_
    rw [Finsupp.coe_add, Pi.add_apply, he' _ (mem_image_of_mem τ (mem_univ r)), zero_add,
      Finsupp.mapDomain_apply hτ]

theorem monomial_add_sum_single {n : ℕ} (μ : ℕ →₀ ℕ) (l : Fin n →₀ ℕ) :
    (monomial (μ + ∑ r : Fin n, Finsupp.single (l r) 1) 1 : TPoly) =
      monomial μ 1 * ∏ r : Fin n, X (l r) := by
  rw [show (monomial (μ + ∑ r : Fin n, Finsupp.single (l r) 1) (1 : ℂ) : TPoly) =
      monomial μ 1 * monomial (∑ r : Fin n, Finsupp.single (l r) 1) 1 by
    rw [monomial_mul, one_mul], monomial_sum_one]
  rfl

/-! ### The reduction -/

/-- **The jet-ideal Poincaré lemma from the arrangement inclusion**, in every slot. -/
theorem jetPoincare_of_arrangement {n : ℕ} (hn : 1 ≤ n) (hA : ArrangementInclusion n)
    (N k E : ℕ) : JetPoincare n N k E := by
  classical
  intro F hF hder
  have hFh : F.IsHomogeneous k := homogeneous_of_tMonW hF
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  set U : Submodule ℂ TPoly := (jetIdealT n).restrictScalars ℂ ⊔ boxSpan N k E with hUdef
  suffices hU : F ∈ U by
    obtain ⟨j, hj, P, hP, rfl⟩ := Submodule.mem_sup.mp hU
    have hjm : Ideal.Quotient.mk (jetIdealT n) (j + P) = Ideal.Quotient.mk (jetIdealT n) P := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add]
    rw [hjm]
    exact mk_mem_boxW_of_mem_boxSpan hP
  by_contra hFU
  obtain ⟨ψ, hψF, hUψ⟩ := Submodule.exists_le_ker_of_notMem hFU
  have hψJ : ∀ G ∈ jetIdealT n, ψ G = 0 := fun G hG =>
    hUψ (Submodule.mem_sup_left (by simpa using hG))
  have hψB : ∀ G ∈ boxSpan N k E, ψ G = 0 := fun G hG => hUψ (Submodule.mem_sup_right hG)
  rcases Nat.lt_or_ge E k with hEk | hEk
  · exact hψF (by rw [HighDegSucc.eq_zero_of_wt_lt hFh hFw hEk, map_zero])
  set d := E - k with hd
  set f : XP k := ∑ e ∈ Ek k d,
    monomial e (ψ (monomial (toMS univ e) 1) / (k.factorial : ℂ)) with hfdef
  have hcoeff : ∀ e, coeff e f =
      if e ∈ Ek k d then ψ (monomial (toMS univ e) 1) / (k.factorial : ℂ) else 0 := by
    intro e
    rw [hfdef, coeff_sum]
    simp only [coeff_monomial]
    rw [sum_ite_eq']
  have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  -- `ψ = ⟨pol(·), f⟩` on the monomials of `F`
  have hC1 : ∀ s ∈ F.support, dot (pol univ (monomial s 1)) f = ψ (monomial s 1) := by
    intro s hs
    have hsk : s.degree = k := by
      have := hFh (mem_support_iff.mp hs)
      rwa [Finsupp.degree_eq_weight_one]
    have hsE : Finsupp.weight wT s = E := hFw (mem_support_iff.mp hs)
    rw [hfdef, dot_sum_right]
    simp only [dot_monomial_right]
    have h1 : ∀ e ∈ Ek k d, coeff e (pol univ (monomial s 1)) *
        (ψ (monomial (toMS univ e) 1) / (k.factorial : ℂ)) =
        coeff e (pol univ (monomial s 1)) * (ψ (monomial s 1) / (k.factorial : ℂ)) := by
      intro e _
      by_cases he : e ∈ (pol univ (monomial s 1)).support
      · rw [pol_monomial_support s univ e he]
      · rw [notMem_support_iff.mp he, zero_mul, zero_mul]
    rw [sum_congr rfl h1, ← sum_mul]
    have hsub : (pol univ (monomial s 1)).support ⊆ Ek k d := by
      intro e he
      have h2 := pol_monomial_support s univ e he
      have h3 := weight_wT_toMS e
      rw [h2, hsE] at h3
      rw [mem_Ek, ← Finsupp.degree_eq_sum, hd]
      omega
    have hsum : ∑ e ∈ Ek k d, coeff e (pol univ (monomial s 1)) = (k.factorial : ℂ) := by
      rw [← sum_subset hsub (fun e _ he => notMem_support_iff.mp he)]
      have := pol_monomial_eval (k := k) s univ
      rw [card_univ, Fintype.card_fin, if_pos hsk, eval_eq] at this
      rw [← this]
      exact sum_congr rfl fun e _ => by simp
    rw [hsum, mul_div_cancel₀ _ hk0]
  have hC2 : dot (pol univ F) f = ψ F := by
    conv_rhs => rw [as_sum F]
    conv_lhs => rw [as_sum F]
    rw [pol_sum, dot_sum_left, map_sum]
    refine sum_congr rfl fun s hs => ?_
    have hmon : (monomial s (coeff s F) : TPoly) = coeff s F • monomial s 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, pol_smul, dot_smul_left, hC1 s hs, map_smul, smul_eq_mul]
  -- `f ∈ L`
  have hC3 : f ∈ Lid k N := by
    refine mem_Lid_of fun e he => ?_
    rw [mem_support_iff, hcoeff] at he
    split_ifs at he with hE
    · by_contra hlow
      push Not at hlow
      refine he ?_
      rw [hψB _ (Submodule.subset_span ⟨toMS univ e, rfl, ?_, ?_, ?_⟩), zero_div]
      · rw [degree_toMS, card_univ, Fintype.card_fin]
      · rw [weight_wT_toMS, Finsupp.degree_eq_sum, mem_Ek.mp hE]; omega
      · intro m hm
        obtain ⟨i, _, rfl⟩ := mem_support_toMS hm
        exact hlow i
    · exact absurd rfl he
  -- `f` vanishes on the `n`-fold diagonals
  have hC4 : ∀ S : Finset (Fin k), #S = n → VanishOn S f := by
    intro S hS s₀ hs₀
    set τ := S.orderEmbOfFin hS with hτdef
    have hτ : Function.Injective τ := τ.injective
    have himS : univ.image τ = S := Finset.image_orderEmbOfFin_univ S hS
    ext c
    rw [coeff_zero]
    by_cases hc : ∃ i ∈ S, i ≠ s₀ ∧ c i ≠ 0
    · obtain ⟨i, hiS, his, hci⟩ := hc
      by_contra hc0
      have hfree : i ∉ (rename (collapseTo s₀ S) f).vars := fun h => by
        obtain ⟨i', -, hi'⟩ := mem_image.mp (vars_rename _ _ h)
        unfold collapseTo at hi'
        split_ifs at hi' with h'
        · exact his hi'.symm
        · exact h' (hi' ▸ hiS)
      exact hci (coeff_eq_zero_of_not_mem_vars hfree (mem_support_iff.mpr hc0))
    push Not at hc
    set j := c s₀ with hj
    set e' := c - Finsupp.single s₀ j with he'def
    have he' : ∀ i ∈ univ.image τ, e' i = 0 := by
      intro i hi
      rw [himS] at hi
      by_cases his : i = s₀
      · subst his; simp [he'def, hj]
      · simp [he'def, Ne.symm his, hc i hi his]
    have hce : c = e' + Finsupp.single s₀ j := by
      ext i
      by_cases his : i = s₀
      · subst his; simp [he'def, hj]
      · simp [he'def, Ne.symm his]
    have hfib := coeff_rename_collapse hτ (himS ▸ hs₀) he' j f
    rw [himS] at hfib
    rw [hce, hfib]
    simp only [hcoeff]
    by_cases hdeg : e'.degree + j = d
    · have hin : ∀ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j, e' + l.mapDomain τ ∈ Ek k d := by
        intro l hl
        rw [mem_finsuppAntidiag] at hl
        have hdl : l.degree = j := by rw [Finsupp.degree_eq_sum]; exact hl.1
        rw [mem_Ek, ← Finsupp.degree_eq_sum, map_add, degree_mapDomain, hdl, hdeg]
      rw [sum_congr rfl fun l hl => if_pos (hin l hl), ← sum_div, ← map_sum]
      have hmon : ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j,
          (monomial (toMS univ (e' + l.mapDomain τ)) (1 : ℂ) : TPoly) =
          monomial (toMS (univ \ univ.image τ) e') 1 * jg n j := by
        rw [jg_eq_sum, mul_sum]
        exact sum_congr rfl fun l _ => by rw [toMS_split hτ he', monomial_add_sum_single]
      rw [hmon, hψJ _ (Ideal.mul_mem_left _ _ (jg_mem n j)), zero_div]
    · refine sum_eq_zero fun l hl => ?_
      rw [if_neg]
      rw [mem_finsuppAntidiag] at hl
      have hdl : l.degree = j := by rw [Finsupp.degree_eq_sum]; exact hl.1
      rw [mem_Ek, ← Finsupp.degree_eq_sum, map_add, degree_mapDomain, hdl]
      exact hdeg
  -- `f` is symmetric
  have hC5 : ∀ σ : Equiv.Perm (Fin k), rename σ f = f := by
    intro σ
    ext e
    obtain ⟨e₁, rfl⟩ : ∃ e₁ : Fin k →₀ ℕ, e = e₁.mapDomain σ :=
      ⟨e.mapDomain σ.symm, by rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm,
        Finsupp.mapDomain_id]⟩
    have hEk' : e₁.mapDomain σ ∈ Ek k d ↔ e₁ ∈ Ek k d := by
      rw [mem_Ek, mem_Ek, ← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, degree_mapDomain]
    have htoMS : toMS univ (e₁.mapDomain σ) = toMS univ e₁ := by
      rw [toMS, toMS, ← Equiv.sum_comp σ]
      exact sum_congr rfl fun i _ => by rw [Finsupp.mapDomain_apply σ.injective]
    rw [coeff_rename_mapDomain _ σ.injective, hcoeff, hcoeff, htoMS]
    simp only [hEk']
  exact hψF (hC2 ▸ dot_pol_Wn hn hder (hA k N f hC5 hC3 hC4))

/-- The core input of the endpoint from the arrangement inclusion. -/
theorem jetPoincareCoreT0_of_arrangement {n : ℕ} (hn : 1 ≤ n) (hA : ArrangementInclusion n) :
    PoincareZero.JetPoincareCoreT0 n :=
  fun N k E _ _ _ _ => jetPoincare_of_arrangement hn hA N k E

/-! ### The case `n = 2` -/

theorem collapseTo_pair {a b : Fin k} (hab : a ≠ b) :
    collapseTo a {a, b} = JetPoincareVdm.subst a b := by
  funext i
  unfold collapseTo JetPoincareVdm.subst
  by_cases hia : i = a
  · subst hia; simp [hab]
  · by_cases hib : i = b
    · subst hib; simp
    · simp [hia, hib]

theorem vanishOn_pair_of_dvd {a b : Fin k} (hab : a ≠ b) {Y : XP k}
    (h : (X b - X a : XP k) ∣ Y) : VanishOn {a, b} Y := by
  intro s₀ hs₀
  rcases mem_insert.mp hs₀ with rfl | hs
  · rw [collapseTo_pair hab]; exact rename_subst_eq_zero_of_dvd h
  · rw [mem_singleton] at hs
    subst hs
    rw [pair_comm, collapseTo_pair hab.symm]
    refine rename_subst_eq_zero_of_dvd ?_
    obtain ⟨u, rfl⟩ := h
    exact ⟨-u, by ring⟩

/-- **`ArrangementInclusion 2`** (from the Vandermonde argument of `JetPoincareVdm`). -/
theorem arrangementInclusion_two : ArrangementInclusion 2 := by
  intro k N f _ hL hV
  have hd : ∀ a b : Fin k, a < b → (X b - X a : XP k) ∣ f := by
    intro a b hab
    have := hV {a, b} (card_pair (ne_of_lt hab)) a (mem_insert_self _ _)
    rw [collapseTo_pair (ne_of_lt hab)] at this
    exact dvd_of_rename_subst_eq_zero this
  have hW := mem_Wid_of_mem_Lid hL hd
  refine Submodule.iSup_induction (p := fun l : Fin k =>
    Ideal.span {(X l ^ N : XP k)} * Qid k l) (motive := fun w => w ∈ Wn k N 2) hW
    (fun l x hx => ?_) (Submodule.zero_mem _) (fun x y hx hy => add_mem hx hy)
  refine Submodule.mul_induction_on hx (fun a ha y hy => ?_) (fun x y hx hy => add_mem hx hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [show c * (X l : XP k) ^ N * y = (X l : XP k) ^ N * (c * y) by ring]
  refine Submodule.subset_span ⟨l, c * y, fun S hS hlS => ?_, rfl⟩
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hS
  have hal : a ≠ l := fun h => hlS (h ▸ mem_insert_self _ _)
  have hbl : b ≠ l := fun h => hlS (h ▸ mem_insert_of_mem (mem_singleton_self _))
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact vanishOn_pair_of_dvd hab
      (dvd_mul_of_dvd_right ((mem_Qid.mp hy) a b hlt hal hbl) c)
  · rw [pair_comm]
    exact vanishOn_pair_of_dvd hab.symm
      (dvd_mul_of_dvd_right ((mem_Qid.mp hy) b a hlt hbl hal) c)

end

end VOA.TwoSeries.JetPoincareArr
