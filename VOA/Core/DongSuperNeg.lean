/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.DongSuper

/-!
# Dong's lemma, super case, `n < 0`: the normal-ordered product

`Core.DongSuper` proves the `n ≥ 0` half (`dong_nonnegε`).  This file is the `n < 0` half — the
one that matters for *building* super vertex algebras, since reconstruction produces `Y` on
general states as an iterated normal-ordered product.

## The super normal ordering

`normalOrderedε ε a b m n = if 0 ≤ m then a m * b n else ε • (b n * a m)` — the Koszul sign
appears exactly on the reordered (annihilation) half, which is the only place `a` and `b` swap.

## The decomposition, and why it costs nothing

The three-variable bracket `[:ab:, c]` splits as in the bosonic case, with two scalars inserted:

`[:ab:,c]_{εac εbc} = εab • b[a,c]_{εac} + (εab εac) • [b,c]_{εbc}a + gate·[[a,b]_{εab},c]_{εac εbc}`

The pleasant surprise is that this is a **pure telescoping identity requiring no `ε² = 1`**:
in `b[a,c]_{εac} + εac • [b,c]_{εbc}a = b(ac - εac·ca) + εac(bc - εbc·cb)a` the two `εac·bca`
terms cancel outright, leaving `bac - εac εbc·cba`.  The gated `m ≥ 0` branch then cancels
against the ungated base with no relations either.  So the sign hypotheses that `dong_coreε`
carries (`hab2 : εab * εab = 1`) are needed only downstream, never here.
-/

namespace VOA

open Module (End)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The super normal-ordered product**, two-variable: the Koszul sign `ε` sits on the
reordered half, where `a` and `b` actually swap. -/
def normalOrderedε (ε : ℂ) (a b : FormalDist (End ℂ V)) : FormalDist₂ (End ℂ V) :=
  fun m n => if 0 ≤ m then a m * b n else ε • (b n * a m)

@[simp] theorem normalOrderedε_apply (ε : ℂ) (a b : FormalDist (End ℂ V)) (m n : ℤ) :
    normalOrderedε ε a b m n = if 0 ≤ m then a m * b n else ε • (b n * a m) := rfl

/-- At `ε = 1` the super normal ordering is the bosonic one. -/
theorem normalOrderedε_one (a b : FormalDist (End ℂ V)) :
    normalOrderedε 1 a b = normalOrdered a b := by
  funext m n
  rw [normalOrderedε_apply, normalOrdered_apply]
  split_ifs <;> simp

/-- **The `ε`-twisted three-variable bracket of the normal-ordered product with `c`.**
The outer sign is `εac * εbc`, since `:ab:` carries the parity of `a` plus that of `b` — the
same sign `dong_nonnegε` concludes with. -/
def normalOrderedBracketε (εabc εab : ℂ) (a b c : FormalDist (End ℂ V)) :
    FormalDist₃ (End ℂ V) :=
  fun m n p => normalOrderedε εab a b m n * c p - εabc • (c p * normalOrderedε εab a b m n)

@[simp] theorem normalOrderedBracketε_apply (εabc εab : ℂ) (a b c : FormalDist (End ℂ V))
    (m n p : ℤ) :
    normalOrderedBracketε εabc εab a b c m n p
      = normalOrderedε εab a b m n * c p - εabc • (c p * normalOrderedε εab a b m n) := rfl

/-- **The super normal-ordering split.**  Mirrors `normalOrderedBracket_decomp`, with the two
scalars `εab` and `εab * εac` on the ungated pieces and the gated triple bracket carrying the
composite sign `εac * εbc`.

No `ε² = 1` hypothesis: both branches close by cancellation alone (see the module docstring). -/
theorem normalOrderedBracketε_decomp (εab εac εbc : ℂ) (a b c : FormalDist (End ℂ V)) :
    normalOrderedBracketε (εac * εbc) εab a b c
      = εab • lmulB b (bracketDistε εac a c)
        + (εab * εac) • rmulA (bracketDistε εbc b c) a
        + gateM (outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c) := by
  apply FormalDist₃.ext; intro m n p
  show normalOrderedε εab a b m n * c p - (εac * εbc) • (c p * normalOrderedε εab a b m n)
    = εab • (b n * bracketDistε εac a c m p)
      + (εab * εac) • (bracketDistε εbc b c n p * a m)
      + (if 0 ≤ m then outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c m n p else 0)
  simp only [normalOrderedε_apply, bracketDistε_apply, outerC₁₂ε_apply]
  split_ifs with h
  · simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    ring_nf
    module
  · simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    ring_nf
    module

/-- **The three-variable locality of the super normal-ordered bracket.**  For fields pairwise
`ε`-local with common order `r`, `(z₁-z₃)ʳ (z₂-z₃)³ʳ [:a(z₁)b(z₂):, c(z₃)] = 0`.

Structurally identical to the bosonic `mulBySub_normalOrderedBracket_eq_zero`: the two ungated
pieces die against `hac` and `hbc`, and the gated triple bracket dies by `dong_coreε` — which is
where `hab2 : εab * εab = 1` finally enters, the decomposition itself having needed no relation. -/
theorem mulBySub_normalOrderedBracketε_eq_zero (εab εac εbc : ℂ) (hab2 : εab * εab = 1)
    (a b c : FormalDist (End ℂ V)) {r : ℕ}
    (hab : mulBySubPow r (bracketDistε εab a b) = 0)
    (hac : mulBySubPow r (bracketDistε εac a c) = 0)
    (hbc : mulBySubPow r (bracketDistε εbc b c) = 0) :
    mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (normalOrderedBracketε (εac * εbc) εab a b c)) = 0 := by
  have h1 : mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (lmulB b (bracketDistε εac a c))) = 0 := by
    rw [← reorder₂₃₁₃, mulBySub₁₃Pow_lmulB, hac, lmulB_zero, map_zero]
  have h2 : mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (rmulA (bracketDistε εbc b c) a)) = 0 := by
    rw [mulBySub₂₃Pow_rmulA, mulBySubPow_mono₂ (show r ≤ 3 * r by omega) hbc, rmulA_zero,
      map_zero]
  have h3 : mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r)
      (gateM (outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c))) = 0 := by
    have hdc : mulBySub₂₃Pow (3 * r) (outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c) = 0 := by
      have h := dong_coreε εab εac εbc hab2 a b c hab hac hbc 0 (2 * r) le_rfl
      rw [show mulBySub₁₂Pow 0 (outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c)
            = outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c from rfl] at h
      rwa [show (2 * r + r : ℕ) = 3 * r from by ring] at h
    rw [mulBySub₂₃Pow_gateM, hdc, gateM_zero, map_zero]
  rw [normalOrderedBracketε_decomp]
  simp only [map_add, map_smul, h1, h2, h3, smul_zero, add_zero]

/-! ## The same-variable super normal product, and the diagonal collapse -/

/-- The diagonal support of the super normal ordering is finite: it sits inside the bosonic one,
since the two differ only by the scalar `ε` on the `m < 0` half. -/
theorem normalOrderedε_diag_support_finite (ε : ℂ) {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (s : ℤ) (x : V) :
    (Function.support (fun m : ℤ => normalOrderedε ε a b m (s - m) x)).Finite := by
  apply (normalOrdered_diag_support_finite ha hb s x).subset
  intro m hm
  rw [Function.mem_support] at hm ⊢
  intro h
  apply hm
  rw [normalOrderedε_apply]
  rw [normalOrdered_apply] at h
  split_ifs at h ⊢ with hmm
  · exact h
  · rw [LinearMap.smul_apply, h, smul_zero]

/-- The `z^s`-coefficient of the super `:a(z)b(z):`, by its action on each vector. -/
noncomputable def nprodCoeffε (ε : ℂ) {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (s : ℤ) : V →ₗ[ℂ] V where
  toFun x := ∑ᶠ m : ℤ, normalOrderedε ε a b m (s - m) x
  map_add' x y := by
    rw [← finsum_add_distrib (normalOrderedε_diag_support_finite ε ha hb s x)
        (normalOrderedε_diag_support_finite ε ha hb s y)]
    exact finsum_congr fun m => map_add _ x y
  map_smul' c x := by
    rw [RingHom.id_apply, smul_finsum' c (normalOrderedε_diag_support_finite ε ha hb s x)]
    exact finsum_congr fun m => map_smul _ c x

/-- **The same-variable super normal-ordered product** `:a(z)b(z):`. -/
noncomputable def nprodε (ε : ℂ) {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) : FormalDist (End ℂ V) :=
  fun s => nprodCoeffε ε ha hb s

@[simp] theorem nprodε_apply (ε : ℂ) {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (s : ℤ) (x : V) :
    nprodε ε ha hb s x = ∑ᶠ m : ℤ, normalOrderedε ε a b m (s - m) x := rfl

/-- Collapsing `z₁ = z₂`: the two-variable bracket of the same-variable product is the diagonal
of the three-variable bracket. -/
theorem appVec2_bracketDistε_nprodε (εabc εab : ℂ) {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (c : FormalDist (End ℂ V)) (x : V) :
    appVec2 x (bracketDistε εabc (nprodε εab ha hb) c)
      = diag3 (appVec3 x (normalOrderedBracketε εabc εab a b c)) := by
  apply FormalDist₂.ext; intro s p
  rw [appVec2_apply, bracketDistε_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.mul_apply, nprodε_apply, nprodε_apply,
    map_finsum (c p) (normalOrderedε_diag_support_finite εab ha hb s x),
    smul_finsum' εabc (((normalOrderedε_diag_support_finite εab ha hb s x).image (fun m => m)).subset
      (fun m hm => by
        rw [Function.mem_support] at hm
        exact ⟨m, by rw [Function.mem_support]; exact fun h => hm (by rw [h, map_zero]), rfl⟩)),
    ← finsum_sub_distrib (normalOrderedε_diag_support_finite εab ha hb s (c p x))
      (((normalOrderedε_diag_support_finite εab ha hb s x).image (fun m => m)).subset
        (fun m hm => by
          rw [Function.mem_support] at hm
          exact ⟨m, by rw [Function.mem_support]; exact fun h => hm (by
            rw [h, map_zero, smul_zero]), rfl⟩)),
    diag3_apply]
  exact finsum_congr fun m => by
    rw [appVec3_apply, normalOrderedBracketε_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.mul_apply]

/-- The diagonal antidiagonals of `[:a(z₁)b(z₂):, c]` on `x` are finite sums. -/
theorem diagSummable_appVec3_normalOrderedBracketε (εabc εab : ℂ) {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (c : FormalDist (End ℂ V)) (x : V) :
    DiagSummable (appVec3 x (normalOrderedBracketε εabc εab a b c)) := by
  intro s p
  apply Set.Finite.subset ((normalOrderedε_diag_support_finite εab ha hb s (c p x)).union
    (normalOrderedε_diag_support_finite εab ha hb s x))
  intro m hm
  rw [Function.mem_support, appVec3_apply, normalOrderedBracketε_apply, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply] at hm
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra hcon
  push_neg at hcon
  exact hm (by rw [hcon.1, hcon.2, map_zero, smul_zero, sub_zero])

/-- **Dong's lemma, super `n < 0` case**: for pairwise `ε`-local fields, the super
normal-ordered product `:a(z)b(z):` is `ε`-local with `c` at the composite sign `εac * εbc`.

Same architecture as the bosonic `dong_neg`: `(z₁-z₃)ʳ(z₂-z₃)³ʳ` annihilates the three-variable
bracket, and collapsing the diagonal (where both powers become `(z-z₃)`) gives `(z-z₃)⁴ʳ`. -/
theorem dong_negε {εab εac εbc : ℂ} (hab2 : εab * εab = 1) {a b c : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b)
    (hab : Localε εab a b) (hac : Localε εac a c) (hbc : Localε εbc b c) :
    Localε (εac * εbc) (nprodε εab ha hb) c := by
  obtain ⟨Nab, hNab⟩ := hab
  obtain ⟨Nac, hNac⟩ := hac
  obtain ⟨Nbc, hNbc⟩ := hbc
  set r := max Nab (max Nac Nbc) with hr
  have hab' : mulBySubPow r (bracketDistε εab a b) = 0 :=
    mulBySubPow_mono₂ (le_max_left _ _) hNab
  have hac' : mulBySubPow r (bracketDistε εac a c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_left _ _) (le_max_right _ _)) hNac
  have hbc' : mulBySubPow r (bracketDistε εbc b c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_right _ _) (le_max_right _ _)) hNbc
  refine ⟨r + 3 * r, ?_⟩
  apply FormalDist₂.ext; intro s p
  apply LinearMap.ext; intro x
  have hDS : DiagSummable (appVec3 x (normalOrderedBracketε (εac * εbc) εab a b c)) :=
    diagSummable_appVec3_normalOrderedBracketε (εac * εbc) εab ha hb c x
  have key : appVec2 x (mulBySubPow (r + 3 * r)
      (bracketDistε (εac * εbc) (nprodε εab ha hb) c)) = 0 := by
    rw [appVec2_mulBySubPow, appVec2_bracketDistε_nprodε, mulBySubPow_add_gen,
      diag3_mulBySub₂₃Pow (3 * r) hDS, diag3_mulBySub₁₃Pow r (hDS.mulBySub₂₃pow (3 * r)),
      ← appVec3_mulBySub₂₃Pow, ← appVec3_mulBySub₁₃Pow,
      mulBySub_normalOrderedBracketε_eq_zero εab εac εbc hab2 a b c hab' hac' hbc',
      appVec3_zero, diag3_zero]
  have h := congrFun (congrFun key s) p
  rw [appVec2_apply] at h
  exact h

/-- **The super normal-ordered product of two fields is a field.**  Same bound as the bosonic
`IsField.nprod`: the `ε` on the `m < 0` half is a scalar, so it cannot resurrect a vanishing
summand. Needed by reconstruction, which iterates the product. -/
theorem IsField.nprodε (ε : ℂ) {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    IsField (nprodε ε ha hb) := by
  intro x
  classical
  obtain ⟨Ba, hBa⟩ := ha x
  obtain ⟨Bb, hBb⟩ := hb x
  set S0 : Finset ℤ := Finset.Icc (min Ba 0) 0 with hS0
  have hS0ne : S0.Nonempty := by rw [hS0, Finset.nonempty_Icc]; exact min_le_right _ _
  let Bbm : ℤ → ℤ := fun m => Classical.choose (hb (a m x))
  have hBbm : ∀ m : ℤ, ∀ j : ℤ, j < Bbm m → b j (a m x) = 0 :=
    fun m => Classical.choose_spec (hb (a m x))
  set B : ℤ := S0.inf' hS0ne (fun m => Bbm m + m) with hB
  refine ⟨min B Bb, fun n hn => ?_⟩
  rw [nprodε_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  rw [normalOrderedε_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    show a m (b (n - m) x) = 0
    have hbz : b (n - m) x = 0 := hBb (n - m) (by
      have : n < Bb := lt_of_lt_of_le hn (min_le_right _ _); omega)
    rw [hbz, map_zero]
  · rw [if_neg h0, LinearMap.smul_apply]
    show ε • b (n - m) (a m x) = 0
    by_cases hmem : m ∈ S0
    · rw [hBbm m (n - m) (by
        have hle : B ≤ Bbm m + m := Finset.inf'_le (fun m => Bbm m + m) hmem
        have hnB : n < B := lt_of_lt_of_le hn (min_le_left _ _)
        omega), smul_zero]
    · rw [hS0, Finset.mem_Icc, not_and_or] at hmem
      have hlt : m < min Ba 0 := by
        rcases hmem with h | h
        · exact lt_of_not_ge h
        · exact absurd (lt_of_not_ge h) (by omega)
      have haz : a m x = 0 := hBa m (lt_of_lt_of_le hlt (min_le_left _ _))
      rw [haz, map_zero, smul_zero]

/-! ## The bosonic theory is the instance `ε = 1`

Not decoration: this is the check that every Koszul sign above is in the right place.  If any
were wrong, the specialization would fail to be `rfl`-close to the bosonic statement. -/

/-- At `ε = 1` the super normal product is the bosonic one. -/
theorem nprodε_one {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    nprodε 1 ha hb = nprod ha hb := by
  funext s
  apply LinearMap.ext; intro x
  rw [nprodε_apply, nprod_apply]
  exact finsum_congr fun m => by rw [normalOrderedε_one]

/-- **The bosonic `dong_neg` is the `ε = 1` case** — a generalization, not a parallel
development, exactly as `dong_nonneg_of_dong_nonnegε` is for the `n ≥ 0` half. -/
theorem dong_neg_of_dong_negε {a b c : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b)
    (hab : Local a b) (hac : Local a c) (hbc : Local b c) :
    Local (nprod ha hb) c := by
  have h := dong_negε (V := V) (εab := 1) (εac := 1) (εbc := 1) (by norm_num) ha hb
    ((localε_one_iff a b).mpr hab) ((localε_one_iff a c).mpr hac)
    ((localε_one_iff b c).mpr hbc)
  rw [nprodε_one, one_mul] at h
  exact (localε_one_iff _ _).mp h

end VOA
