/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharFS
import VOA.Examples.TwoSeriesModelCharIndep

/-!
# Evaluating Feigin–Stoyanovsky functionals on products of blocks

Work over `ℂ[T_j]` (`R = TPoly`, `t_j = T_j`).  Index `m + s` blocks so that the first `m` have
colour `0` and the last `s` have colour `1` (`col m s`).  For a symmetric `F(x_1, …, x_s)`, the
functional `Λ_{λ,α} ∘ Φ_{ψ_F}` (the level-one functional `[u_λ v_0^l] ∘ E_α` after applying
`ψ_F` to the `T`-coefficients) takes on the block product `pblk (col m s) g a` the value

  `[t^a] ( F(t_{m+1}, …, t_{m+s}) · e^α(t) · Apol_{λ,g}(t) )`        (`lam_ψF_pblk`).

The proof: the higher-`T`-degree parts of the blocks are invisible to `ψ_F` (`LowM`, `ψ_F` reads
`T`-degree exactly `s`); the lowest parts multiply out to `Σ_{b+d=a} T_b^{[col]} · P_{g,d}`;
`ψ_F (Π_{colour-one} T_{b_i}) = [t^b] F(t_A)`; and `Λ_{λ,α} (P_{g,d}) = [t^d] (e^α Apol)`.

Also: the pushforward `ℂ[T_j][u,v] → R_n[u,v]` maps the model into the model (`map_modelDeg`), and
`vdm s = Π_{i ≠ j} (x_i - x_j)` gives the FS functions `vdm s · e^β` (symmetric, divisible by
`x_0 - x_1`, homogeneous, `vdm s ≠ 0`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

/-! ### The Vandermonde-type FS functions -/

/-- `Π_{i ≠ j} (x_i - x_j)`. -/
def vdm (s : ℕ) : MvPolynomial (Fin s) ℂ :=
  ∏ p ∈ (Finset.univ : Finset (Fin s)).offDiag, (X p.1 - X p.2)

theorem vdm_symm (s : ℕ) : Symm (vdm s) := by
  intro σ
  rw [vdm, map_prod]
  simp only [map_sub, rename_X]
  refine Finset.prod_nbij' (fun p => (σ p.1, σ p.2)) (fun p => (σ.symm p.1, σ.symm p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
    exact fun h => hp (σ.injective h)
  · intro p hp
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
    exact fun h => hp (σ.symm.injective h)
  · intro p _; simp
  · intro p _; simp
  · intro p _; rfl

theorem vdm_ne_zero (s : ℕ) : vdm s ≠ 0 := by
  rw [vdm, Finset.prod_ne_zero_iff]
  intro p hp
  rw [Finset.mem_offDiag] at hp
  rw [sub_ne_zero]
  exact fun h => hp.2.2 (X_injective h)

theorem vdm_isHomogeneous (s : ℕ) : (vdm s).IsHomogeneous (s * s - s) := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin s)).offDiag
    (fun p => (X p.1 - X p.2 : MvPolynomial (Fin s) ℂ)) (fun _ => 1)
    (fun p _ => (isHomogeneous_X ℂ p.1).sub (isHomogeneous_X ℂ p.2))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_fin] at h
  exact h

theorem vdm_div (s : ℕ) : DivX01 (vdm s) := by
  intro h
  refine ⟨∏ p ∈ ((Finset.univ : Finset (Fin s)).offDiag).erase (⟨0, by omega⟩, ⟨1, by omega⟩),
    (X p.1 - X p.2), ?_⟩
  have hmem : ((⟨0, by omega⟩ : Fin s), (⟨1, by omega⟩ : Fin s)) ∈
      (Finset.univ : Finset (Fin s)).offDiag := by
    rw [Finset.mem_offDiag]
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    intro h'
    exact absurd (congrArg Fin.val h') (by simp)
  rw [vdm, ← Finset.mul_prod_erase _ _ hmem]

/-- The FS function `vdm s · e^β`. -/
def fsF (s : ℕ) (β : Fin s → ℕ) : MvPolynomial (Fin s) ℂ := vdm s * esymmPow β

theorem esymmPow_symm {s : ℕ} (β : Fin s → ℕ) : Symm (esymmPow β) := by
  intro σ
  rw [esymmPow, map_prod]
  simp only [map_pow, rename_esymm]

theorem fsF_symm (s : ℕ) (β : Fin s → ℕ) : Symm (fsF s β) := by
  intro σ; rw [fsF, map_mul, vdm_symm s σ, esymmPow_symm β σ]

theorem fsF_div (s : ℕ) (β : Fin s → ℕ) : DivX01 (fsF s β) := by
  intro h
  obtain ⟨G, hG⟩ := vdm_div s h
  exact ⟨G * esymmPow β, by rw [fsF, hG, mul_assoc]⟩

theorem fsF_isHomogeneous (s : ℕ) (β : Fin s → ℕ) :
    (fsF s β).IsHomogeneous (s * s - s + awt β) :=
  (vdm_isHomogeneous s).mul (esymmPow_isHomogeneous β)

/-! ### Pushing the model forward to `R_n` -/

/-- The coefficient reduction `ℂ[T_j][u, v] → R_n[u, v]`. -/
def pushN (n : ℕ) : MPoly TPoly →ₐ[ℂ] MPoly (Rn n) :=
  MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ ℂ (jetIdealT n))

theorem pushN_mletter (n : ℕ) (l : VOA.AffineVOA.CorrectedR.Generator × ℕ) :
    pushN n (mletter TPoly X l) = mletter (Rn n) (tn n) l := by
  obtain ⟨g, k⟩ := l
  cases g with
  | current a =>
    change pushN n (ι TPoly _) = ι (Rn n) _
    simp only [pushN, ι, MvPolynomial.mapAlgHom_apply]
    rw [MvPolynomial.map_map]
    rfl
  | sugawara =>
    change pushN n (ι TPoly _ + MvPolynomial.C (X k)) = ι (Rn n) _ + MvPolynomial.C (tn n k)
    rw [map_add]
    congr 1
    · simp only [pushN, ι, MvPolynomial.mapAlgHom_apply]
      rw [MvPolynomial.map_map]
      rfl
    · simp [pushN, tn]

theorem pushN_mword (n : ℕ) (w : List (VOA.AffineVOA.CorrectedR.Generator × ℕ)) :
    pushN n (mword TPoly X w) = mword (Rn n) (tn n) w := by
  induction w with
  | nil => simp
  | cons l w ih => rw [mword_cons, mword_cons, map_mul, ih, pushN_mletter]

/-- The pushforward maps the model into the model. -/
theorem map_modelDeg (n r : ℕ) (d : ℤ) {x : MPoly TPoly} (hx : x ∈ modelDeg TPoly X r d) :
    pushN n x ∈ modelDeg (Rn n) (tn n) r d := by
  have h : (modelDeg TPoly X r d).map (pushN n).toLinearMap ≤ modelDeg (Rn n) (tn n) r d := by
    rw [modelDeg, Submodule.map_span_le]
    rintro _ ⟨w, hw, hwt, rfl⟩
    rw [AlgHom.toLinearMap_apply, pushN_mword]
    exact Submodule.subset_span ⟨w, hw, hwt, rfl⟩
  exact h (Submodule.mem_map_of_mem hx)

theorem Φ_pushN {n : ℕ} (φ : Rn n →ₗ[ℂ] ℂ) (x : MPoly TPoly) :
    VOA.TwoSeries.StrictModel.Φ (Rn n) φ (pushN n x) =
      VOA.TwoSeries.StrictModel.Φ TPoly (φ ∘ₗ (Ideal.Quotient.mkₐ ℂ (jetIdealT n)).toLinearMap)
        x := by
  ext e
  rw [VOA.TwoSeries.StrictModel.coeff_Φ, VOA.TwoSeries.StrictModel.coeff_Φ]
  simp [pushN, coeff_map]

/-! ### The colouring and the lowest parts of the blocks -/

/-- The colouring: the first `m` blocks have colour `0`, the last `s` colour `1`. -/
def col (m s : ℕ) : Fin (m + s) → Fin 2 := Fin.append (fun _ => 0) (fun _ => 1)

theorem sum_col (m s : ℕ) : ∑ i, ((col m s i : ℕ) + 1) = m + 2 * s := by
  rw [Fin.sum_univ_add]
  simp [col, Fin.append_left, Fin.append_right]
  ring

theorem sum_col' (m s : ℕ) : ∑ i, (col m s i : ℕ) = s := by
  rw [Fin.sum_univ_add]
  simp [col, Fin.append_left, Fin.append_right]

/-- The `T`-part of the lowest term of a block. -/
def tp (c : Fin 2) (b : ℕ) : TPoly := if c = 0 then (if b = 0 then 1 else 0) else X b

/-- The lowest part `Σ_{b+d=a} tp_c(b) · G_{g,d}` of a block coefficient. -/
def lowC (c : Fin 2) (g : Fin 4) (a : ℕ) : MPoly TPoly :=
  ∑ p ∈ Finset.antidiagonal a, MvPolynomial.C (tp c p.1) * ι TPoly (genCoeff g p.2)

theorem tp_lowDeg (c : Fin 2) (b : ℕ) : lowDeg (c : ℕ) (tp c b) := by
  unfold tp
  split_ifs with h
  · subst h; exact lowDeg_zero_left _
  · subst h; exact lowDeg_zero_left _
  · have : (c : ℕ) = 1 := by
      have := c.2
      have : (c : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
      omega
    rw [this]; exact lowDeg_X b

theorem lowC_lowM (c : Fin 2) (g : Fin 4) (a : ℕ) : LowM (c : ℕ) (lowC c g a) :=
  LowM.sum _ _ fun p _ => LowM.C_mul_ι (tp_lowDeg c p.1) _

theorem coeff_gS_T (g : Fin 4) (a : ℕ) :
    PowerSeries.coeff a (gS TPoly g) = lowC 0 g a := by
  rw [coeff_gS, lowC, Finset.sum_eq_single (0, a)]
  · simp [tp]
  · rintro ⟨b, d⟩ hp hne
    have : b ≠ 0 := by
      intro hb; apply hne; subst hb
      simp only [Finset.mem_antidiagonal, zero_add] at hp; rw [hp]
    simp [tp, this]
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (zero_add a)) h

theorem coeff_tS_mul_gS (g : Fin 4) (a : ℕ) :
    PowerSeries.coeff a (tS TPoly X * gS TPoly g) = lowC 1 g a := by
  rw [PowerSeries.coeff_mul, lowC]
  apply Finset.sum_congr rfl
  intro p _
  rw [tS, PowerSeries.coeff_mk, coeff_gS]
  simp [tp]

theorem LowM.neg' {k : ℕ} {P : MPoly TPoly} (hP : LowM k P) : LowM k (-P) :=
  fun m => by rw [coeff_neg]; exact lowDeg_neg (hP m)

theorem blk_coeff_sub_lowM_00 (g : Fin 4) (hg : g ≠ 3) (a : ℕ) :
    PowerSeries.coeff a (blk TPoly X 0 g) - lowC 0 g a = 0 := by
  have hb : blk TPoly X 0 g = gS TPoly g := by simp [blk, hg]
  rw [hb, coeff_gS_T, sub_self]

theorem blk_coeff_sub_lowM_03 (a : ℕ) :
    PowerSeries.coeff a (blk TPoly X 0 3) - lowC 0 3 a = -MvPolynomial.C (X a) := by
  have hb : blk TPoly X 0 3 = gS TPoly 3 - tS TPoly X := by simp [blk]
  rw [hb, map_sub, coeff_gS_T, sub_sub_cancel_left, tS, PowerSeries.coeff_mk]

theorem blk_coeff_sub_lowM_10 (g : Fin 4) (hg : g ≠ 3) (a : ℕ) :
    PowerSeries.coeff a (blk TPoly X 1 g) - lowC 1 g a = 0 := by
  have hb : blk TPoly X 1 g = tS TPoly X * gS TPoly g := by simp [blk, hg]
  rw [hb, coeff_tS_mul_gS, sub_self]

theorem blk_coeff_sub_lowM_13 (a : ℕ) :
    PowerSeries.coeff a (blk TPoly X 1 3) - lowC 1 3 a =
      -((1 / 2 : ℂ) • ∑ p ∈ Finset.antidiagonal a, MvPolynomial.C (X p.1 * X p.2)) := by
  have hb : blk TPoly X 1 3 = tS TPoly X * gS TPoly 3 -
      (1 / 2 : ℂ) • (tS TPoly X * tS TPoly X) := by simp [blk]
  rw [hb, map_sub, coeff_tS_mul_gS, sub_sub_cancel_left, PowerSeries.coeff_smul,
    PowerSeries.coeff_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  rw [tS, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_mul]

/-- Each block coefficient is its lowest part plus higher `T`-degree. -/
theorem blk_coeff_sub_lowM (c : Fin 2) (g : Fin 4) (a : ℕ) :
    LowM ((c : ℕ) + 1) (PowerSeries.coeff a (blk TPoly X c g) - lowC c g a) := by
  have hc : c = 0 ∨ c = 1 := by
    rcases c with ⟨c, hc⟩
    interval_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with rfl | rfl
  · by_cases hg : g = 3
    · subst hg
      rw [blk_coeff_sub_lowM_03]
      exact LowM.neg' (LowM.C (lowDeg_X a))
    · rw [blk_coeff_sub_lowM_00 g hg]; exact LowM.zero _
  · by_cases hg : g = 3
    · subst hg
      rw [blk_coeff_sub_lowM_13]
      refine LowM.neg' (LowM.smul _ (LowM.sum _ _ fun p _ => LowM.C ?_))
      exact lowDeg_mul (lowDeg_X _) (lowDeg_X _)
    · rw [blk_coeff_sub_lowM_10 g hg]; exact LowM.zero _

/-- Products: the difference between the product and the product of the lowest parts has
`T`-degree `≥ Σ c_i + 1`. -/
theorem prod_sub_lowM : ∀ {K : ℕ} (c : Fin K → ℕ) (x y : Fin K → MPoly TPoly),
    (∀ i, LowM (c i) (x i)) → (∀ i, LowM (c i + 1) (y i - x i)) →
      LowM (∑ i, c i + 1) (∏ i, y i - ∏ i, x i) ∧ LowM (∑ i, c i) (∏ i, y i)
  | 0, c, x, y, _, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, Finset.sum_empty]
    refine ⟨LowM.zero _, fun m => ?_⟩
    rw [coeff_one]
    split_ifs
    · exact lowDeg_zero_left _
    · exact lowDeg_zero _
  | K + 1, c, x, y, hx, hy => by
    have ih := prod_sub_lowM (fun i => c i.succ) (fun i => x i.succ) (fun i => y i.succ)
      (fun i => hx i.succ) (fun i => hy i.succ)
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have hy0 : LowM (c 0) (y 0) := by
      have := (hx 0).add ((hy 0).mono (Nat.le_succ _))
      simpa using this
    refine ⟨?_, hy0.mul ih.2⟩
    have e : y 0 * ∏ i : Fin K, y i.succ - x 0 * ∏ i : Fin K, x i.succ =
        (y 0 - x 0) * ∏ i : Fin K, y i.succ +
          x 0 * (∏ i : Fin K, y i.succ - ∏ i : Fin K, x i.succ) := by ring
    rw [e]
    refine LowM.add ?_ ?_
    · have h := (hy 0).mul ih.2
      rwa [show c 0 + 1 + ∑ i : Fin K, c i.succ = c 0 + ∑ i : Fin K, c i.succ + 1 by ring] at h
    · have h := (hx 0).mul ih.1
      rwa [show c 0 + (∑ i : Fin K, c i.succ + 1) = c 0 + ∑ i : Fin K, c i.succ + 1 by ring] at h

/-! ### Expanding the lowest parts and evaluating -/

theorem prod_lowC {K : ℕ} (c : Fin K → Fin 2) (g : Fin K → Fin 4) (a : Fin K → ℕ) :
    ∏ i, lowC (c i) (g i) (a i) = ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
      MvPolynomial.C (∏ i, tp (c i) (p i).1) * ι TPoly (Pga g (toF fun i => (p i).2)) := by
  simp only [lowC]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod]
  simp [Pga]

theorem Φ_pblk {K S : ℕ} (F : MvPolynomial (Fin S) ℂ) (c : Fin K → Fin 2) (hc : ∑ i, (c i : ℕ) = S)
    (g : Fin K → Fin 4) (a : Fin K → ℕ) :
    VOA.TwoSeries.StrictModel.Φ TPoly (ψF F) (pblk TPoly X c g a) =
      ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
        ψF F (∏ i, tp (c i) (p i).1) • Pga g (toF fun i => (p i).2) := by
  have hlow := (prod_sub_lowM (fun i => (c i : ℕ)) (fun i => lowC (c i) (g i) (a i))
    (fun i => PowerSeries.coeff (a i) (blk TPoly X (c i) (g i)))
    (fun i => lowC_lowM _ _ _) (fun i => blk_coeff_sub_lowM _ _ _)).1
  rw [hc] at hlow
  have h0 := Φ_ψF_eq_zero F hlow
  rw [map_sub, sub_eq_zero] at h0
  rw [pblk, h0, prod_lowC, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact VOA.TwoSeries.StrictModel.Φ_C_mul_ι TPoly _ _ _

theorem coeff_rename_natAdd {m s : ℕ} (F : MvPolynomial (Fin s) ℂ) (b : Fin (m + s) → ℕ) :
    coeff (toF b) (rename (Fin.natAdd m) F) =
      if ∀ k : Fin m, b (Fin.castAdd s k) = 0 then coeff (toF fun j => b (Fin.natAdd m j)) F
      else 0 := by
  classical
  split_ifs with hb
  · have he : toF b = Finsupp.mapDomain (Fin.natAdd m) (toF fun j => b (Fin.natAdd m j)) := by
      ext i
      refine Fin.addCases (fun k => ?_) (fun j => ?_) i
      · rw [toF_apply, hb k, Finsupp.mapDomain_notin_range]
        rintro ⟨j, hj⟩
        exact absurd (congrArg Fin.val hj) (by simp; omega)
      · rw [toF_apply, Finsupp.mapDomain_apply (Fin.natAdd_injective s m), toF_apply]
    rw [he, coeff_rename_mapDomain _ (Fin.natAdd_injective s m)]
  · apply coeff_rename_eq_zero
    intro u hu
    exfalso
    apply hb
    intro k
    have := congrArg (· (Fin.castAdd s k)) hu
    simp only [toF_apply] at this
    rw [← this, Finsupp.mapDomain_notin_range]
    rintro ⟨j, hj⟩
    exact absurd (congrArg Fin.val hj) (by simp; omega)

theorem ψF_tp_col {m s : ℕ} {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (b : Fin (m + s) → ℕ) :
    ψF F (∏ i, tp (col m s i) (b i)) = coeff (toF b) (rename (Fin.natAdd m) F) := by
  classical
  rw [coeff_rename_natAdd, Fin.prod_univ_add]
  simp only [col, Fin.append_left, Fin.append_right, tp, if_true,
    show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [Finset.prod_boole]
  split_ifs with h1 h2 h2
  · rw [one_mul, ψF_prod_X hF]
  · exact absurd (fun k => h1 k (Finset.mem_univ _)) h2
  · exact absurd (fun k _ => h2 k) h1
  · rw [zero_mul, map_zero]

theorem sum_piFinset_antidiagonal {K : ℕ} {M : Type*} [AddCommMonoid M] (a : Fin K → ℕ)
    (f : (Fin K →₀ ℕ) → (Fin K →₀ ℕ) → M) :
    ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
        f (toF fun i => (p i).1) (toF fun i => (p i).2) =
      ∑ x ∈ Finset.antidiagonal (toF a), f x.1 x.2 := by
  refine Finset.sum_nbij' (fun p => ((toF fun i => (p i).1), (toF fun i => (p i).2)))
    (fun x i => (x.1 i, x.2 i)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Fintype.mem_piFinset, Finset.mem_antidiagonal] at hp ⊢
    ext i; simp [hp i]
  · intro x hx
    simp only [Fintype.mem_piFinset, Finset.mem_antidiagonal] at hx ⊢
    intro i
    have := congrArg (· i) hx
    simpa using this
  · intro p _; funext i; simp
  · intro x _; ext i <;> simp
  · intro p _; rfl

/-- **The evaluation**: `Λ_{λ,α} ∘ Φ_{ψ_F}` on a block product is the `t^a` coefficient of
`F(t_A) · e^α · Apol_{λ,g}`. -/
theorem lam_ψF_pblk {m s : ℕ} {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (ms : Multiset ℕ)
    (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l) (α : Fin (m + s) → ℕ) (g : Fin (m + s) → Fin 4)
    (a : Fin (m + s) → ℕ) :
    Lam ms l α (VOA.TwoSeries.StrictModel.Φ TPoly (ψF F) (pblk TPoly X (col m s) g a)) =
      coeff (toF a) (rename (Fin.natAdd m) F * (esymmPow α * Apol ms l g)) := by
  rw [Φ_pblk F (col m s) (sum_col' m s), map_sum, coeff_mul]
  simp only [map_smul, smul_eq_mul, ψF_tp_col hF]
  have h := sum_piFinset_antidiagonal a (fun b d =>
    coeff b (rename (Fin.natAdd m) F) * coeff d (esymmPow α * Apol ms l g))
  simp only at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_esymmPow_mul_Apol ms l hms]

end

end VOA.TwoSeries.ModelChar
