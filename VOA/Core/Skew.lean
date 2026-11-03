import VOA.Core.Reconstruction
import VOA.Foundations.Substitution

/-!
# Consolidated skew / FLM weak-associativity base

This file is the `sorry`-free base of the skew-symmetry argument.

It collects:

* **`subst` z₁-multiplicativity** (z₀-dominant substitution): `subst_add`, `subst_shiftZ₂`,
  `subst_shiftZ₁`, `subst_sub`, `shiftSum`/`shiftSum_apply`, `shiftZ₁_iterate_apply`,
  `subst_shiftZ₁_pow`.
* **`IsBddBelow₁` + `subst2`** (z₂-dominant substitution) with finiteness on the doubly-bounded
  class, and the keystone `subst2_mulBySub`, `subst2_mulBySubPow`.
* **`comp`** (the composite-field coefficient `(u₍₋a₋₁₎v)₍₋b₋₁₎x`) with its OPE/normal-ordered
  columns `comp_nonneg_col`, `comp_neg_col`, and the lower-truncation `comp_bddBelow₁`.
* **Locality assembly**: `bracketDist_add_left`, `Local.add`, `Local.sum`, `locality_smul`,
  `dong_nonneg_Y`, `dong_neg_Y`.
* **The skew scaffold**: `sgn`, `skewCoeffFun`/`skewOp`/`skewDist`, the vacuum condition
  `skewCoeffFun_vacuum`, and the reduction `skew_eq_Y_of_local` together with the mode-form
  output `skew_mode_of_field_eq`.

## Status
Complete & `sorry`-free / axiom-free.  The `subst`/`subst2` substitution
calculus, the `comp` composite-field columns, the locality assembly and the skew scaffold are
all proved (`#print axioms = [propext, Classical.choice, Quot.sound]`); the skew-locality
reduction `skew_eq_Y_of_local` is discharged in `Core.WeakAssoc`/`Core.SkewSymmetry`.
-/

namespace VOA

open scoped BigOperators
open Module (End)

universe u

/-! ## §1. The z₀-dominant substitution `subst`: z₁-multiplicativity

`subst_add` is the additivity lemma. -/

section Subst
variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- `shiftZ₂` preserves lower-truncation in `z₂` (shifts the bound by 1). -/
theorem IsBddBelow₂.shiftZ₂ {f : FormalDist₂ 𝒲} (h : IsBddBelow₂ f) :
    IsBddBelow₂ (VOA.shiftZ₂ f) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B + 1, fun m n hn => ?_⟩
  rw [shiftZ₂_apply, hB m (n - 1) (by omega)]

/-- `shiftZ₁` preserves lower-truncation in `z₂` (the bound is unchanged). -/
theorem IsBddBelow₂.shiftZ₁ {f : FormalDist₂ 𝒲} (h : IsBddBelow₂ f) :
    IsBddBelow₂ (VOA.shiftZ₁ f) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun m n hn => ?_⟩
  rw [shiftZ₁_apply, hB (m - 1) n hn]

/-- `shiftZ₁^[N]` preserves lower-truncation in `z₂`. -/
theorem isBddBelow₂_shiftZ₁_iterate {f : FormalDist₂ 𝒲} (h : IsBddBelow₂ f) (N : ℕ) :
    IsBddBelow₂ ((VOA.shiftZ₁^[N]) f) := by
  induction N with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply]; exact IsBddBelow₂.shiftZ₁ ih

/-- **subst additivity**: `subst (f + g) = subst f + subst g` for `f g` bddBelow₂. -/
theorem subst_add {f g : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) (hg : IsBddBelow₂ g) :
    subst (f + g) = subst f + subst g := by
  ext a b
  rw [subst_apply]
  show (∑ᶠ k : ℤ, cbz (a + k) k • (f (a + k) (b - k) + g (a + k) (b - k))) = _
  rw [show (∑ᶠ k : ℤ, cbz (a + k) k • (f (a + k) (b - k) + g (a + k) (b - k)))
        = ∑ᶠ k : ℤ, (cbz (a + k) k • f (a + k) (b - k) + cbz (a + k) k • g (a + k) (b - k)) from
      finsum_congr fun k => by rw [smul_add]]
  rw [finsum_add_distrib
      (subst_summand_finite hf a b 0 _ (fun k hk => cbz_apply_neg _ hk))
      (subst_summand_finite hg a b 0 _ (fun k hk => cbz_apply_neg _ hk))]
  rfl

/-- **subst commutes with `shiftZ₂`**: `subst (shiftZ₂ f) = shiftZ₂ (subst f)`. -/
theorem subst_shiftZ₂ (f : FormalDist₂ 𝒲) :
    subst (shiftZ₂ f) = shiftZ₂ (subst f) := by
  ext a b
  rw [shiftZ₂_apply, subst_apply, subst_apply]
  refine finsum_congr fun k => ?_
  rw [shiftZ₂_apply, show b - k - 1 = b - 1 - k from by ring]

/-- **subst on `shiftZ₁`**: `subst (shiftZ₁ f) = shiftZ₁ (subst f) + shiftZ₂ (subst f)`,
using `shiftZ₁ = mulBySub + shiftZ₂` and additivity of `subst`. -/
theorem subst_shiftZ₁ {f : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) :
    subst (shiftZ₁ f) = shiftZ₁ (subst f) + shiftZ₂ (subst f) := by
  have hsplit : shiftZ₁ f = mulBySub f + shiftZ₂ f := by
    ext m n
    rw [shiftZ₁_apply]
    show f (m - 1) n = (mulBySub f + shiftZ₂ f) m n
    rw [show (mulBySub f + shiftZ₂ f) m n = mulBySub f m n + shiftZ₂ f m n from rfl,
      mulBySub_apply, shiftZ₂_apply]
    abel
  rw [hsplit, subst_add (IsBddBelow₂.mulBySub hf) (IsBddBelow₂.shiftZ₂ hf),
    subst_mulBySub hf, subst_shiftZ₂ f]

/-- The two coordinate shifts commute. -/
theorem shiftZ₂_shiftZ₁ (f : FormalDist₂ 𝒲) : shiftZ₂ (shiftZ₁ f) = shiftZ₁ (shiftZ₂ f) := by
  ext m n; rw [shiftZ₂_apply, shiftZ₁_apply, shiftZ₁_apply, shiftZ₂_apply]

/-- The endomorphism `z₀+z₂ = shiftZ₁ + shiftZ₂` on `(z₀,z₂)`-distributions. -/
noncomputable def shiftSum : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲 := shiftZ₁ + shiftZ₂

@[simp] theorem shiftSum_apply (f : FormalDist₂ 𝒲) (m n : ℤ) :
    shiftSum f m n = f (m - 1) n + f m (n - 1) := by
  show (shiftZ₁ f + shiftZ₂ f) m n = _
  rw [show (shiftZ₁ f + shiftZ₂ f) m n = shiftZ₁ f m n + shiftZ₂ f m n from rfl,
    shiftZ₁_apply, shiftZ₂_apply]

/-- **`subst` distributes over subtraction of lower-truncated distributions.** -/
theorem subst_sub {f g : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) (hg : IsBddBelow₂ g) :
    subst (f - g) = subst f - subst g := by
  ext a b
  show subst (f - g) a b = subst f a b - subst g a b
  rw [subst_apply, subst_apply, subst_apply,
    ← finsum_sub_distrib
      (subst_summand_finite hf a b 0 _ (fun k _ => cbz_apply_neg _ (by omega)))
      (subst_summand_finite hg a b 0 _ (fun k _ => cbz_apply_neg _ (by omega)))]
  refine finsum_congr fun k => ?_
  show cbz (a + k) k • (f - g) (a + k) (b - k) = _
  rw [show (f - g) (a + k) (b - k) = f (a + k) (b - k) - g (a + k) (b - k) from rfl, smul_sub]

/-- Function-iterate form of `shiftZ₁` on coefficients: `(shiftZ₁^[k] f) m n = f (m-k) n`. -/
theorem shiftZ₁_iterate_apply (k : ℕ) (f : FormalDist₂ 𝒲) (m n : ℤ) :
    ((shiftZ₁^[k]) f) m n = f (m - (k : ℤ)) n := by
  induction k generalizing m with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ', Function.comp_apply, shiftZ₁_apply, ih]
      congr 1; omega

/-- **The iterated `z₁`-shift keystone**: `subst(z₁ᴺ·f) = (z₀+z₂)ᴺ·subst(f)`, i.e.
`subst(shiftZ₁^[N] f) = shiftSum^[N] (subst f)`. -/
theorem subst_shiftZ₁_pow {f : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) (N : ℕ) :
    subst ((shiftZ₁^[N]) f) = (shiftSum^[N]) (subst f) := by
  induction N with
  | zero => simp
  | succ k ih =>
      have hfk : IsBddBelow₂ ((shiftZ₁^[k]) f) := by
        obtain ⟨B, hB⟩ := hf
        refine ⟨B, fun m n hn => ?_⟩
        rw [shiftZ₁_iterate_apply]; exact hB _ _ hn
      rw [Function.iterate_succ', Function.comp_apply, subst_shiftZ₁ hfk, ih,
        Function.iterate_succ', Function.comp_apply]
      show shiftZ₁ ((shiftSum^[k]) (subst f)) + shiftZ₂ ((shiftSum^[k]) (subst f)) = _
      rw [shiftSum]; rfl

end Subst

/-! ## §2. The z₂-dominant substitution `subst2` -/

section Subst2
variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- **Lower-truncated in `z₁`**: the `z₁`-support is bounded below, uniformly in `z₂`-power. -/
def IsBddBelow₁ (f : FormalDist₂ 𝒲) : Prop := ∃ B : ℤ, ∀ m n : ℤ, m < B → f m n = 0

/-- Lower truncation in `z₁` is preserved by `(z₁-z₂)·`. -/
theorem IsBddBelow₁.mulBySub {f : FormalDist₂ 𝒲} (h : IsBddBelow₁ f) :
    IsBddBelow₁ (mulBySub f) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun m n hn => ?_⟩
  rw [mulBySub_apply, hB (m - 1) n (by omega), hB m (n - 1) hn, sub_zero]

theorem IsBddBelow₁.mulBySubPow (N : ℕ) {f : FormalDist₂ 𝒲} (h : IsBddBelow₁ f) :
    IsBddBelow₁ (mulBySubPow N f) := by
  induction N with
  | zero => simpa using h
  | succ k ih => rw [mulBySubPow_succ, LinearMap.comp_apply]; exact ih.mulBySub

/-- The **z₂-dominant substitution** `z₁ ↦ z₀+z₂` (z₀ small): expand each `(z₀+z₂)ᵐ` in
nonnegative powers of `z₀`.  Coeff of `z₀ᵃz₂ᵇ` is `∑_k C(a+k,a)·f(a+k, b-k)`.  Algebraically
defined on the doubly lower-truncated class `IsBddBelow₁ f ∧ IsBddBelow₂ f`. -/
noncomputable def subst2 (f : FormalDist₂ 𝒲) : FormalDist₂ 𝒲 :=
  fun a b => ∑ᶠ k : ℤ, cbz (a + k) a • f (a + k) (b - k)

@[simp] theorem subst2_apply (f : FormalDist₂ 𝒲) (a b : ℤ) :
    subst2 f a b = ∑ᶠ k : ℤ, cbz (a + k) a • f (a + k) (b - k) := rfl

/-- For `f` lower-truncated in BOTH variables, every summand `c k • f(a+k, b-k)` has finite
support in `k`. -/
theorem subst2_summand_finite {f : FormalDist₂ 𝒲} (h1 : IsBddBelow₁ f) (h2 : IsBddBelow₂ f)
    (a b : ℤ) (c : ℤ → ℂ) :
    (Function.support (fun k : ℤ => c k • f (a + k) (b - k))).Finite := by
  obtain ⟨B₁, hB₁⟩ := h1
  obtain ⟨B₂, hB₂⟩ := h2
  apply Set.Finite.subset (Set.finite_Icc (B₁ - a) (b - B₂))
  intro k hk
  rw [Function.mem_support] at hk
  rw [Set.mem_Icc]
  exact ⟨not_lt.mp fun h => hk (by rw [hB₁ (a + k) (b - k) (by omega), smul_zero]),
         not_lt.mp fun h => hk (by rw [hB₂ (a + k) (b - k) (by omega), smul_zero])⟩

/-- `subst2 f` is algebraically defined on the doubly-bounded class. -/
theorem subst2_coeff_finite {f : FormalDist₂ 𝒲} (h1 : IsBddBelow₁ f) (h2 : IsBddBelow₂ f)
    (a b : ℤ) :
    (Function.support (fun k : ℤ => cbz (a + k) a • f (a + k) (b - k))).Finite :=
  subst2_summand_finite h1 h2 a b _

/-- The keystone: `subst2((z₁-z₂)·f) = z₀·subst2(f)`, i.e.
`subst2 (mulBySub f) = shiftZ₁ (subst2 f)`, on the doubly-bounded class. -/
theorem subst2_mulBySub {f : FormalDist₂ 𝒲} (h1 : IsBddBelow₁ f) (h2 : IsBddBelow₂ f) :
    subst2 (mulBySub f) = shiftZ₁ (subst2 f) := by
  ext a b
  rw [shiftZ₁_apply, subst2_apply, subst2_apply]
  have hLHS : (∑ᶠ k : ℤ, cbz (a + k) a • mulBySub f (a + k) (b - k))
      = (∑ᶠ k : ℤ, cbz (a + k) a • f (a - 1 + k) (b - k))
        - (∑ᶠ k : ℤ, cbz (a + k) a • f (a + k) (b - 1 - k)) := by
    rw [← finsum_sub_distrib
        (subst2_summand_finite h1 h2 (a - 1) b _)
        (subst2_summand_finite h1 h2 a (b - 1) _)]
    refine finsum_congr fun k => ?_
    rw [mulBySub_apply, smul_sub,
      show a + k - 1 = a - 1 + k from by ring, show b - k - 1 = b - 1 - k from by ring]
  rw [hLHS, sub_eq_iff_eq_add]
  have hAR : (∑ᶠ k : ℤ, cbz (a + k) a • f (a - 1 + k) (b - k))
      - (∑ᶠ k : ℤ, cbz (a - 1 + k) (a - 1) • f (a - 1 + k) (b - k))
      = ∑ᶠ k : ℤ, cbz (a + k) a • f (a + k) (b - 1 - k) := by
    rw [← finsum_sub_distrib
        (subst2_summand_finite h1 h2 (a - 1) b _)
        (subst2_summand_finite h1 h2 (a - 1) b _)]
    rw [show (∑ᶠ k : ℤ, (cbz (a + k) a • f (a - 1 + k) (b - k)
              - cbz (a - 1 + k) (a - 1) • f (a - 1 + k) (b - k)))
          = ∑ᶠ k : ℤ, cbz (a - 1 + k) a • f (a - 1 + k) (b - k) from
        finsum_congr fun k => by
          rw [← sub_smul]; congr 1
          have hp := cbz_pascal (a + k) a
          rw [show a + k - 1 = a - 1 + k from by ring] at hp
          rw [hp]; ring]
    rw [← finsum_int_succ_shift
        (fun k : ℤ => cbz (a - 1 + k) a • f (a - 1 + k) (b - k))]
    refine finsum_congr fun k => ?_
    dsimp only
    rw [show a - 1 + (k + 1) = a + k from by ring, show b - (k + 1) = b - 1 - k from by ring]
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp hAR

/-- The iterated keystone: `subst2((z₁-z₂)ᴺ·f) = z₀ᴺ·subst2(f)`. -/
theorem subst2_mulBySubPow {f : FormalDist₂ 𝒲} (h1 : IsBddBelow₁ f) (h2 : IsBddBelow₂ f)
    (N : ℕ) : subst2 (mulBySubPow N f) = (shiftZ₁^[N]) (subst2 f) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply,
        subst2_mulBySub (h1.mulBySubPow k) (h2.mulBySubPow k), ih,
        Function.iterate_succ', Function.comp_apply]

end Subst2

/-! ## §3. The composite-field coefficient `comp` and the locality assembly engine -/

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ### §3a. The composite coefficient `comp` and its columns. -/

/-- The composite field coefficient `(u₍₋a₋₁₎v)₍₋b₋₁₎x` as a two-variable distribution:
the `z₀ᵃz₂ᵇ`-coefficient of `Y(Y(u,z₀)v, z₂)x`. -/
noncomputable def comp (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) : FormalDist₂ 𝒱 :=
  fun a b => mode (W.Y (W.smul u (-a-1) v)) (-b-1) x

@[simp] theorem comp_apply (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (a b : ℤ) :
    comp W u v x a b = mode (W.Y (W.smul u (-a-1) v)) (-b-1) x := rfl

theorem comp_apply' (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (a b : ℤ) :
    comp W u v x a b = (W.Y (W.smul u (-a-1) v)) b x := by
  rw [comp_apply, mode_apply, show (-(-b-1)-1 : ℤ) = b by ring]

/-- **The positive (`nth_product`) columns of `comp` are the OPE residue.**  For `a ≤ -1`,
the `z₀ᵃ`-column of the composite `Y(Y(u,z₀)v,z₂)x` is the `(k=-a-1)`-th residue. -/
theorem comp_nonneg_col (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {a : ℤ} (ha : a ≤ -1) (b : ℤ) :
    comp W u v x a b
      = mulBySubPow (-a-1).toNat (bracketDist (W.Y u) (W.Y v)) (-1) b x := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (-a-1).toNat = k := ⟨(-a-1).toNat, rfl⟩
  have hak : W.smul u (-a-1) v = W.smul u (k : ℤ) v := by
    congr 1; omega
  rw [comp_apply', hak, ← nth_product, hk, cCoeff_apply]

/-- **The negative (`assoc_neg`) columns of `comp` are the normal-ordered product.**  For
`a ≥ 0`, the `z₀ᵃ`-column of `Y(Y(u,z₀)v,z₂)x` is the `negProd` applied to `x`. -/
theorem comp_neg_col (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {a : ℤ} (ha : 0 ≤ a) (b : ℤ) :
    comp W u v x a b
      = negProd (W.isField_Y u) (W.isField_Y v) a.toNat b x := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a.toNat = k := ⟨a.toNat, rfl⟩
  have hak : W.smul u (-a-1) v = W.smul u (-(k:ℤ)-1) v := by
    congr 1; omega
  rw [comp_apply', hak, assoc_neg, hk]

/-- **`comp` is doubly lower-truncated.**  It is `IsBddBelow₁` (truncated in the z₀-power `a`):
`W.smul u (-a-1) v = u₍₋ₐ₋₁₎v = 0` for `a ≪ 0`, by VA5 regularity of `Y(u)` on `v`. -/
theorem comp_bddBelow₁ (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) :
    IsBddBelow₁ (comp W u v x) := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.regularity u v
  refine ⟨-N, fun a b ha => ?_⟩
  rw [comp_apply']
  have hu : W.smul u (-a - 1) v = 0 := hN (-a - 1) (by omega)
  rw [show W.smul u (-a-1) v = W.smul u (-a - 1) v from by ring_nf, hu, map_zero]
  rfl

/-! ### §3b. The locality assembly engine. -/

/-- The OPE-coefficient field `Res_{z₁}((z₁-z)ᵏ[Y(u,z₁),Y(v,z)])` is local with every `Y(c)`.
This is `dong_nonneg` specialized to vertex operators. -/
theorem dong_nonneg_Y (W : VertexOperatorAlgebra 𝒱) (u v c : 𝒱) (k : ℕ) :
    Local (cCoeff k (bracketDist (W.Y u) (W.Y v))) (W.Y c) :=
  dong_nonneg (W.locality u v) (W.locality u c) (W.locality v c) k

/-- The negative normal-ordered product `:Y(u,z)Y(v,z):` (`nprod`) is local with every `Y(c)`.
This is `dong_neg` specialized to vertex operators. -/
theorem dong_neg_Y (W : VertexOperatorAlgebra 𝒱) (u v c : 𝒱) :
    Local (nprod (W.isField_Y u) (W.isField_Y v)) (W.Y c) :=
  dong_neg (W.isField_Y u) (W.isField_Y v)
    (W.locality u v) (W.locality u c) (W.locality v c)

/-- **Every product mode is local with every `Y(c)`** (immediate from VA4).
`Y(u₍ₙ₎v)` is mutually local with `Y(c)` for ALL `n : ℤ`. -/
theorem locality_smul (W : VertexOperatorAlgebra 𝒱) (u v c : 𝒱) (n : ℤ) :
    Local (W.Y (W.smul u n v)) (W.Y c) :=
  W.locality (W.smul u n v) c

/-- `bracketDist` is additive in its first argument. -/
theorem bracketDist_add_left (a a' b : FormalDist (End ℂ 𝒱)) :
    bracketDist (a + a') b = bracketDist a b + bracketDist a' b := by
  apply FormalDist₂.ext; intro m n
  show (a m + a' m) * b n - b n * (a m + a' m)
    = (a m * b n - b n * a m) + (a' m * b n - b n * a' m)
  rw [add_mul, mul_add]; abel

/-- **Locality is additive (two summands).**  If `F` and `F'` are each local with `G`, so is
`F + F'` — with locality power `max N N'`. -/
theorem Local.add {F F' G : FormalDist (End ℂ 𝒱)} (h : Local F G) (h' : Local F' G) :
    Local (F + F') G := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := h'
  refine ⟨max N N', ?_⟩
  rw [bracketDist_add_left, map_add,
    mulBySubPow_eq_zero_mono (le_max_left N N') hN,
    mulBySubPow_eq_zero_mono (le_max_right N N') hN', add_zero]

/-- **Locality assembles over finite index sets.**  A finite `Finset`-sum of fields, each
local with `G`, is local with `G`. -/
theorem Local.sum {ι : Type*} (s : Finset ι) (F : ι → FormalDist (End ℂ 𝒱))
    {G : FormalDist (End ℂ 𝒱)} (h : ∀ i ∈ s, Local (F i) G) :
    Local (∑ i ∈ s, F i) G := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      exact ⟨0, by rw [mulBySubPow_zero]; apply FormalDist₂.ext; intro m n
                   show (0 : End ℂ 𝒱) * G n - G n * 0 = 0; simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Local.add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## §4. The skew scaffold

`skewDist` + vacuum + `skew_eq_Y_of_local` + `skew_mode_of_field_eq`. -/

end VertexOperatorAlgebra

/-- Integer sign `(-1)^n`, defined locally. -/
def sgn (n : ℤ) : ℂ := if Even n then 1 else -1

theorem sgn_succ (n : ℤ) : sgn (n + 1) = - sgn n := by
  simp only [sgn]
  by_cases h : Even n
  · rw [if_neg (by rw [Int.even_add_one]; exact not_not.mpr h), if_pos h]
  · rw [if_pos (Int.even_add_one.mpr h), if_neg h]; norm_num

theorem sgn_natCast (k : ℕ) : sgn (k : ℤ) = (-1 : ℂ) ^ k := by
  induction k with
  | zero => simp [sgn]
  | succ k ih => rw [Nat.cast_succ, sgn_succ, ih, pow_succ]; ring

theorem sgn_mul_self (n : ℤ) : sgn n * sgn n = 1 := by
  rw [sgn]; split_ifs <;> norm_num

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The `z^t`-coefficient of the candidate skew field, applied to `b`:
`A t b = ∑ⱼ (1/j!) (-1)^{t-j} Tʲ ((Y b)(t-j) u)`. -/
noncomputable def skewCoeffFun (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (b : 𝒱) : 𝒱 :=
  ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (t - j)) •
    ((W.toPreVertexAlgebra.T ^ j) ((W.Y b) (t - j) u))

/-- **Finiteness of the skew finsum.**  For fixed `b`, only finitely many `j` contribute. -/
theorem skew_support_finite (W : VertexOperatorAlgebra 𝒱) (u b : 𝒱) (t : ℤ) :
    (Function.support (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn (t - j)) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y b) (t - j) u)))).Finite := by
  obtain ⟨N, hN⟩ := W.regularity b u
  apply Set.Finite.subset (Set.finite_Icc 0 (N + t).toNat)
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hjbig
  rw [not_le] at hjbig
  apply hj
  have hzero : (W.Y b) (t - (j : ℤ)) u = 0 := by
    have h := hN (-(t - (j : ℤ)) - 1) (by omega)
    rwa [mode_apply, show (-(-(t - (j : ℤ)) - 1) - 1) = t - (j : ℤ) by ring] at h
  rw [hzero, map_zero, smul_zero, smul_zero]

/-- `(Y 𝟙) k u = if k = 0 then u else 0` (VA2). -/
theorem Y_vacuum_apply (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (u : 𝒱) :
    (W.Y W.vacuum) k u = if k = 0 then u else 0 := by
  rw [W.vacuum_Y]
  show (1 : FormalDist (End ℂ 𝒱)) k u = _
  rw [FormalDist.one_apply]
  split_ifs with h
  · rfl
  · rfl

/-- **VACUUM ACTION (the tractable piece).** With `b = 𝟙`, the candidate skew field creates
`e^{zT}u`: `A t 𝟙 = (Y u) t 𝟙`. -/
theorem skewCoeffFun_vacuum (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) :
    skewCoeffFun W u t W.vacuum = (W.Y u) t W.vacuum := by
  rw [skewCoeffFun]
  by_cases ht : 0 ≤ t
  · obtain ⟨T₀, rfl⟩ : ∃ T₀ : ℕ, t = (T₀ : ℤ) := ⟨t.toNat, by omega⟩
    rw [finsum_eq_single _ T₀ (fun j hj => ?_)]
    · rw [show ((T₀ : ℤ) - (T₀ : ℕ)) = 0 by ring, Y_vacuum_apply, if_pos rfl,
        sgn, if_pos (by norm_num : Even (0 : ℤ)), one_smul]
      rw [show (W.Y u) (T₀ : ℤ) W.vacuum = W.smul u (-(T₀:ℤ) - 1) W.vacuum from by
            rw [PreVertexAlgebra.smul_def, mode_apply, show (-(-(T₀:ℤ) - 1) - 1) = (T₀:ℤ) by ring]]
      rw [creation_pow]
    · rw [Y_vacuum_apply, if_neg (by
            intro h; apply hj; omega), map_zero, smul_zero, smul_zero]
  · rw [not_le] at ht
    rw [show (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn ((t : ℤ) - j)) •
          ((W.toPreVertexAlgebra.T ^ j) ((W.Y W.vacuum) ((t : ℤ) - j) u))) = 0 from ?_,
      PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra u ht]
    refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
    rw [Y_vacuum_apply, if_neg (by omega), map_zero, smul_zero, smul_zero]

/-- `A t` as a linear endomorphism of `𝒱` (linear in `b`). -/
noncomputable def skewOp (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) : End ℂ 𝒱 where
  toFun b := skewCoeffFun W u t b
  map_add' b₁ b₂ := by
    rw [skewCoeffFun, skewCoeffFun, skewCoeffFun,
      ← finsum_add_distrib (skew_support_finite W u b₁ t) (skew_support_finite W u b₂ t)]
    refine finsum_congr fun j => ?_
    rw [show (W.Y (b₁ + b₂)) (t - (j:ℤ)) u = (W.Y b₁) (t - (j:ℤ)) u + (W.Y b₂) (t - (j:ℤ)) u from by
          rw [map_add]; rfl, map_add, smul_add, smul_add]
  map_smul' c b := by
    rw [RingHom.id_apply, skewCoeffFun, skewCoeffFun,
      smul_finsum' c (skew_support_finite W u b t)]
    refine finsum_congr fun j => ?_
    rw [show (W.Y (c • b)) (t - (j:ℤ)) u = c • (W.Y b) (t - (j:ℤ)) u from by
          rw [map_smul]; rfl, map_smul]
    rw [smul_comm (sgn (t - (j:ℤ))) c, smul_comm ((j.factorial:ℂ)⁻¹) c]

@[simp] theorem skewOp_apply (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (b : 𝒱) :
    skewOp W u t b = skewCoeffFun W u t b := rfl

/-- The candidate skew field `A` as a one-variable operator-valued distribution. -/
noncomputable def skewDist (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : FormalDist (End ℂ 𝒱) :=
  fun t => skewOp W u t

@[simp] theorem skewDist_apply (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (b : 𝒱) :
    skewDist W u t b = skewCoeffFun W u t b := rfl

/-- **THE REDUCTION (the precise gate).**  *If* the candidate skew field `A = skewDist W u`
is mutually local with every vertex operator `Y(c,z)`, then `A = Y(u,·)`. -/
theorem skew_eq_Y_of_local (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (hloc : ∀ c : 𝒱, Local (skewDist W u) (W.Y c)) :
    skewDist W u = W.Y u :=
  W.toPreVertexAlgebra.goddard_uniqueness (skewDist W u) u hloc
    (fun t => by rw [skewDist_apply]; exact skewCoeffFun_vacuum W u t)

/-- The substitution applies to the iterated product field (which is `IsBddBelow₂`), and the
keystone `subst_mulBySubPow` clears `(z₁-z₂)^N` into `z₀^N`. -/
theorem subst_Yprod_pole_clearing (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (N : ℕ) :
    subst (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x))
      = (shiftZ₁^[N]) (subst (W.toPreVertexAlgebra.Yprod u v x)) :=
  subst_mulBySubPow (W.toPreVertexAlgebra.Yprod_bddBelow u v x) N

/-- **SKEW from the field identity.**  Given `skewDist W u = W.Y u`, read off the
`z^{-n-1}`-coefficient applied to `v`. -/
theorem skew_mode_of_field_eq (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (n : ℤ)
    (hfield : skewDist W u = W.Y u) :
    W.smul u n v
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-n - 1 - j) u)) := by
  have h := congrFun hfield (-n - 1)
  have happ := congrFun (congrArg (fun (f : End ℂ 𝒱) => (f : 𝒱 → 𝒱)) h) v
  simp only [skewDist_apply] at happ
  rw [PreVertexAlgebra.smul_def, mode_apply]
  rw [← happ, skewCoeffFun]

/-! ## The FLM lower-truncation gain

`(z₁-z₂)ᴺ·Yprod` for `N` at least the `(u,v)`-locality bound is **doubly** lower-truncated
(`IsBddBelow₁ ∧ IsBddBelow₂`) — the class on which `subst2` is algebraically defined.  The
`z₁`-truncation, absent from the two-sided `Yprod`, is donated by the swapped product `Yswap`
(which equals `Yprod` after `(z₁-z₂)ᴺ` by locality). -/

/-- The **swapped** iterated product field `Y(v,z₂)Y(u,z₁)x`: `z₁ᵐz₂ⁿ`-coeff is `(Y v)ₙ((Y u)ₘ x)`. -/
def Yswap (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) : FormalDist₂ 𝒱 :=
  fun m n => (W.Y v) n ((W.Y u) m x)

@[simp] theorem Yswap_apply (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (m n : ℤ) :
    Yswap W u v x m n = (W.Y v) n ((W.Y u) m x) := rfl

/-- **`Yswap` is `IsBddBelow₁`.** `(Y u)ₘ x = u₍₋ₘ₋₁₎ x = 0` for `m ≪ 0` (VA5 regularity of
`Y(u)` on the FIXED `x`), uniformly in `n`. -/
theorem Yswap_bddBelow₁ (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) :
    IsBddBelow₁ (Yswap W u v x) := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.regularity u x
  refine ⟨-N, fun m n hm => ?_⟩
  rw [Yswap_apply]
  have hu : (W.Y u) m x = 0 := by
    have h := hN (-m - 1) (by omega)
    rwa [mode_apply, show (-(-m - 1) - 1 : ℤ) = m by ring] at h
  rw [hu, map_zero]

/-- Evaluating the commutator distribution on `x`: `[Y(u),Y(v)]ₘₙ x = Yprod − Yswap`. -/
theorem applyVec_bracketDist_Y (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) :
    applyVec x (bracketDist (W.Y u) (W.Y v))
      = W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x := by
  ext m n
  have hsub : (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) m n
      = W.toPreVertexAlgebra.Yprod u v x m n - Yswap W u v x m n := rfl
  rw [hsub, applyVec_apply, bracketDist_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    PreVertexAlgebra.Yprod_apply, Yswap_apply]

/-- **The locality bridge** `(z₁-z₂)ᴺ·Yprod = (z₁-z₂)ᴺ·Yswap` for `N` ≥ the `(u,v)`-locality
bound (VA4 kills the commutator). -/
theorem Yprod_swap_bridge (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱)
    {N : ℕ} (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0) :
    mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x) = mulBySubPow N (Yswap W u v x) := by
  have key : mulBySubPow N (applyVec x (bracketDist (W.Y u) (W.Y v))) = 0 := by
    rw [← applyVec_mulBySubPow, hN, applyVec_zero]
  rw [applyVec_bracketDist_Y, map_sub, sub_eq_zero] at key
  exact key

/-- **`(z₁-z₂)ᴺ·Yprod` is `IsBddBelow₁`** for `N` ≥ the locality bound (via the bridge). -/
theorem mulBySubPow_Yprod_bddBelow₁ (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱)
    {N : ℕ} (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0) :
    IsBddBelow₁ (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) := by
  rw [Yprod_swap_bridge W u v x hN]
  exact (Yswap_bddBelow₁ W u v x).mulBySubPow N

/-- **`(z₁-z₂)ᴺ·Yprod` is `IsBddBelow₂`** for every `N` (`Yprod_bddBelow`, preserved by `(z₁-z₂)ᴺ·`). -/
theorem mulBySubPow_Yprod_bddBelow₂ (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (N : ℕ) :
    IsBddBelow₂ (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) :=
  (W.toPreVertexAlgebra.Yprod_bddBelow u v x).mulBySubPow N

/-- **`(z₁-z₂)ᴺ·Yprod` is DOUBLY lower-truncated** for `N` ≥ the `(u,v)`-locality bound — the
class on which `subst2 ((z₁-z₂)ᴺ·Yprod)` is well-defined. -/
theorem mulBySubPow_Yprod_doublyBdd (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱)
    {N : ℕ} (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0) :
    IsBddBelow₁ (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x))
      ∧ IsBddBelow₂ (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) :=
  ⟨mulBySubPow_Yprod_bddBelow₁ W u v x hN, mulBySubPow_Yprod_bddBelow₂ W u v x N⟩

/-- Packaged with the existence of the locality bound (VA4). -/
theorem exists_mulBySubPow_Yprod_doublyBdd (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) :
    ∃ N : ℕ, IsBddBelow₁ (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x))
      ∧ IsBddBelow₂ (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) := by
  obtain ⟨N, hN⟩ := W.locality u v
  exact ⟨N, mulBySubPow_Yprod_doublyBdd W u v x hN⟩

/-! ## The reduction of skew-symmetry to weak associativity

The whole skew theorem is reduced to a single predicate `FLMCoeff` (the FLM weak
associativity, in vector-applied pole-clearing form): once `FLMCoeff W u` holds, the candidate
field `skewDist W u` is local with every `Y(c)` (Goddard's hypothesis), hence equals `W.Y u`,
hence the skew mode formula. -/

/-- An operator-valued two-variable distribution vanishes iff it vanishes on every vector. -/
theorem formalDist₂_End_eq_zero_iff (g : FormalDist₂ (End ℂ 𝒱)) :
    g = 0 ↔ ∀ b : 𝒱, applyVec b g = 0 := by
  constructor
  · intro hg b; rw [hg, applyVec_zero]
  · intro h
    refine FormalDist₂.ext fun m n => ?_
    refine LinearMap.ext fun b => ?_
    have := congrFun (congrFun (h b) m) n
    rw [applyVec_apply] at this
    rw [this]; rfl

/-- **Assembly bridge.** If `(z₁−z₂)ᴺ` annihilates the bracket applied to *every* test vector
(uniform `N`), it annihilates the bracket as an operator distribution — upgrading the
per-vector pole-clearing to the operator-level `Local` hypothesis Goddard needs. -/
theorem local_of_applyVec_annihilation {A G : FormalDist (End ℂ 𝒱)} (N : ℕ)
    (h : ∀ b : 𝒱, mulBySubPow N (applyVec b (bracketDist A G)) = 0) :
    mulBySubPow N (bracketDist A G) = 0 := by
  rw [formalDist₂_End_eq_zero_iff]
  intro b
  rw [applyVec_mulBySubPow]
  exact h b

/-- **Weak associativity, in vector-applied pole-clearing form.** For the candidate skew field
and every `c`, a uniform power `(z₁−z₂)ᴺ` annihilates the composite-minus-product difference on
every test vector. -/
def WeakAssocLoc (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : Prop :=
  ∀ c : 𝒱, ∃ N : ℕ, ∀ b : 𝒱,
    mulBySubPow N (applyVec b (bracketDist (skewDist W u) (W.Y c))) = 0

/-- **The connection** (round-1's open step): weak associativity ⇒ the operator-level
skew-locality gate. -/
theorem skewLocal_of_weakAssoc (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (hWA : WeakAssocLoc W u) :
    ∀ c : 𝒱, Local (skewDist W u) (W.Y c) := by
  intro c
  obtain ⟨N, hN⟩ := hWA c
  exact ⟨N, local_of_applyVec_annihilation N hN⟩

/-- **Skew from weak associativity** (Goddard): `skewDist W u = W.Y u`. -/
theorem skewDist_eq_Y_of_weakAssoc (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (hWA : WeakAssocLoc W u) :
    skewDist W u = W.Y u :=
  skew_eq_Y_of_local W u (skewLocal_of_weakAssoc W u hWA)

/-- **The skew mode formula from weak associativity** (Gannon 5.1.8):
`u₍ₙ₎v = ∑ⱼ (1/j!)(-1)^{-n-1-j} Tʲ (v₍−n−1−j₎u)`. -/
theorem skew_mode_of_weakAssoc (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (n : ℤ)
    (hWA : WeakAssocLoc W u) :
    W.smul u n v
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-n - 1 - j) u)) :=
  skew_mode_of_field_eq W u v n (skewDist_eq_Y_of_weakAssoc W u hWA)

/-- The `(m,n)`-coefficient of the skew bracket on `b` is the composite-minus-product
difference `(skewDist u)ₘ((Y c)ₙ b) − (Y c)ₙ((skewDist u)ₘ b)`. -/
theorem applyVec_bracketDist_skew_coeff (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m n : ℤ)
    (b : 𝒱) :
    applyVec b (bracketDist (skewDist W u) (W.Y c)) m n
      = skewCoeffFun W u m ((W.Y c) n b) - (W.Y c) n (skewCoeffFun W u m b) := by
  rw [applyVec_apply, bracketDist_apply]
  show (skewDist W u) m ((W.Y c) n b) - (W.Y c) n ((skewDist W u) m b) = _
  rw [skewDist_apply, skewDist_apply]

/-- **`FLMCoeff`** — the FLM weak-associativity, stated directly at the level of the skew
bracket coefficient: for every `c`, a uniform `(z₁−z₂)ᴺ` annihilates
`m,n ↦ (skewDist u)ₘ((Y c)ₙ b) − (Y c)ₙ((skewDist u)ₘ b)` for every `b`.  This is the single
remaining open lemma; everything else in skew-symmetry is reduced to it. -/
def FLMCoeff (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : Prop :=
  ∀ c : 𝒱, ∃ N : ℕ, ∀ b : 𝒱,
    mulBySubPow N (fun m n =>
      skewCoeffFun W u m ((W.Y c) n b) - (W.Y c) n (skewCoeffFun W u m b)) = 0

/-- `FLMCoeff` ⇒ `WeakAssocLoc` (the bracket coefficient unfolds to exactly `FLMCoeff`'s field). -/
theorem weakAssocLoc_of_flm_coeff (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (h : FLMCoeff W u) : WeakAssocLoc W u := by
  intro c
  obtain ⟨N, hN⟩ := h c
  refine ⟨N, fun b => ?_⟩
  rw [show applyVec b (bracketDist (skewDist W u) (W.Y c))
        = (fun m n => skewCoeffFun W u m ((W.Y c) n b)
            - (W.Y c) n (skewCoeffFun W u m b)) from
      FormalDist₂.ext fun m n => applyVec_bracketDist_skew_coeff W u c m n b]
  exact hN b

/-- **Skew-symmetry, modulo `FLMCoeff`**: the candidate field equals the vertex operator. -/
theorem skewDist_eq_Y_of_flm_coeff (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (h : FLMCoeff W u) : skewDist W u = W.Y u :=
  skewDist_eq_Y_of_weakAssoc W u (weakAssocLoc_of_flm_coeff W u h)

/-- **The skew mode formula, modulo `FLMCoeff`** (Gannon 5.1.8). -/
theorem skew_mode_of_flm_coeff (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (n : ℤ)
    (h : FLMCoeff W u) :
    W.smul u n v
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-n - 1 - j) u)) :=
  skew_mode_of_field_eq W u v n (skewDist_eq_Y_of_flm_coeff W u h)

end VertexOperatorAlgebra

end VOA
