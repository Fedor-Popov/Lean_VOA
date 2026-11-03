/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeadingKoszulBicomplex
import VOA.Examples.LeadingKoszulWeyl

set_option linter.unusedSectionVars false

/-!
# Bicomplexes whose rows are Koszul complexes of Weyl data

This file glues `LeadingKoszulWeyl` (Koszul acyclicity) to `LeadingKoszulBicomplex` (the
collapse onto the Koszul row). For each ghost count `q` let `W q` be a Weyl datum on a module
`P q` (in the coset note: the coefficients `gr A ⊗ B ⊗ Λ^q(c)` tensored with the free
auxiliary polynomial variables, `LeadingKoszulTensor`). The row `q` of the bicomplex is the
Koszul complex of `W q`, graded by Koszul degree (`kdeg`); `d_K` is `kd` (`row`). The
Chevalley–Eilenberg components and their relations are *data* supplied by the user.

## Results

* `WeylDatum.row_exact` : the rows are exact in positive Koszul degree.
* `WeylDatum.rowH0Equiv` : **Koszul `H₀` of a row is the augmentation target `Q`**.
* `LeadingBicomplex.ofKoszulRows` : the Koszul-exactness fields of `LeadingBicomplex` are
  discharged for such bicomplexes; only the CE components and the relations of
  `(d_K + d_CE)² = 0` remain as input.

Everything is proved outright.
-/

namespace VOA.LeadingKoszul

open Finset

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]
variable {P : Type v} [AddCommGroup P] [Module R P]

namespace WeylDatum

variable (W : WeylDatum R ι P)

variable (R ι P) in
/-- Koszul chains concentrated in Koszul degree `l`. -/
def kdeg (l : ℕ) : Submodule R (Finset ι → P) where
  carrier := {f | ∀ S : Finset ι, S.card ≠ l → f S = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg S hS => by simp [hf S hS, hg S hS]
  smul_mem' := fun c f hf S hS => by simp [hf S hS]

theorem kd_mem_kdeg {l : ℕ} {f : Finset ι → P} (hf : f ∈ kdeg R ι P (l + 1)) : W.kd f ∈ kdeg R ι P l := by
  intro S hS
  rw [kd_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hf (insert i S) (by rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hi)]; omega),
    map_zero, smul_zero]

/-- The Koszul differential `kdeg (l+1) → kdeg l` (the row differential `d_K`). -/
def row (l : ℕ) : kdeg R ι P (l + 1) →ₗ[R] kdeg R ι P l :=
  W.kd.restrict fun _ hf => W.kd_mem_kdeg hf

@[simp] theorem row_apply (l : ℕ) (f : kdeg R ι P (l + 1)) : (W.row l f : Finset ι → P) = W.kd f := rfl

/-- **The rows are exact in positive Koszul degree.** -/
theorem row_exact (l : ℕ) (x : kdeg R ι P (l + 1)) (hx : W.row l x = 0) :
    ∃ y : kdeg R ι P (l + 2), W.row (l + 1) y = x := by
  have hd : W.kd x = 0 := by
    have := congrArg Subtype.val hx
    simpa using this
  obtain ⟨g, hg, hgx⟩ := W.exists_kd_eq l x x.2 hd
  exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩

theorem mem_kdeg_zero {f : Finset ι → P} (hf : f ∈ kdeg R ι P 0) {S : Finset ι} (hS : S ≠ ∅) :
    f S = 0 :=
  hf S (by rwa [Ne, Finset.card_eq_zero])

/-- The degree-one chain `g {i} = D i v` used to realize `L v` as a Koszul boundary. -/
def lift1 (v : P) : Finset ι → P := fun S => ∑ i, if S = {i} then W.D i v else 0

theorem lift1_single (v : P) (j : ι) : W.lift1 v {j} = W.D j v := by
  rw [lift1]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro i _ hij
    rw [if_neg (fun h => hij (Finset.singleton_inj.mp h).symm)]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem lift1_mem (v : P) : W.lift1 v ∈ kdeg R ι P 1 := by
  intro S hS
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg]
  rintro rfl
  exact hS (Finset.card_singleton i)

/-- **Koszul `H₀` of a row is the augmentation target.** -/
noncomputable def rowH0Equiv {Q : Type*} [AddCommGroup Q] [Module R Q] (Aug : W.Augmentation Q) :
    (kdeg R ι P 0 ⧸ LinearMap.range (W.row 0)) ≃ₗ[R] Q := by
  let φ : kdeg R ι P 0 →ₗ[R] Q := Aug.ε.comp ((LinearMap.proj (∅ : Finset ι)).comp (kdeg R ι P 0).subtype)
  have hφ : Function.Surjective φ := by
    intro q
    refine ⟨⟨fun S => if S = ∅ then Aug.σ q else 0, fun S hS => ?_⟩, ?_⟩
    · dsimp only
      rw [if_neg]; rwa [Ne, Finset.card_eq_zero] at hS
    · change Aug.ε (if (∅ : Finset ι) = ∅ then Aug.σ q else 0) = q
      rw [if_pos rfl, Aug.ε_σ]
  have hker : LinearMap.range (W.row 0) = LinearMap.ker φ := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [LinearMap.mem_ker]
      change Aug.ε (W.kd g ∅) = 0
      rw [W.kd_empty, ← LinearMap.mem_ker, ← Aug.range_L_eq_ker, W.range_L_eq]
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
    · intro f hf
      have hf' : (f : Finset ι → P) ∅ ∈ LinearMap.range W.L := by
        rw [Aug.range_L_eq_ker]; exact hf
      obtain ⟨v, hv⟩ := hf'
      refine ⟨⟨W.lift1 v, W.lift1_mem v⟩, Subtype.ext ?_⟩
      funext S
      rw [row_apply]
      by_cases hS : S = ∅
      · subst hS
        rw [W.kd_empty, ← hv, W.L_apply]
        exact Finset.sum_congr rfl fun i _ => by
          change W.u i (W.lift1 v {i}) = _
          rw [W.lift1_single]
      · rw [mem_kdeg_zero f.2 hS, kd_apply]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hcard : (insert i S).card ≠ 1 := by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hi)]
          have : S.card ≠ 0 := by rwa [Ne, Finset.card_eq_zero]
          omega
        change ksign i S • W.u i (W.lift1 v (insert i S)) = 0
        rw [W.lift1_mem v _ hcard, map_zero, smul_zero]
  exact (Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hφ)

theorem rowH0Equiv_mk {Q : Type*} [AddCommGroup Q] [Module R Q] (Aug : W.Augmentation Q)
    (f : kdeg R ι P 0) :
    W.rowH0Equiv Aug (Submodule.Quotient.mk f) = Aug.ε ((f : Finset ι → P) ∅) := rfl

end WeylDatum

/-! ### Bicomplexes with Koszul rows -/

namespace LeadingBicomplex

variable (R ι)
variable (P : ℕ → Type v) [∀ q, AddCommGroup (P q)] [∀ q, Module R (P q)]
variable (W : ∀ q, WeylDatum R ι (P q))

/-- `X p = T^{p,p}`: row `p`, Koszul degree `p`. -/
abbrev KX (p : ℕ) : Type _ := WeylDatum.kdeg R ι (P p) p
/-- `Y p = T^{p+1,p}`: row `p`, Koszul degree `p + 1`. -/
abbrev KY (p : ℕ) : Type _ := WeylDatum.kdeg R ι (P p) (p + 1)
/-- `Z p = T^{p,p+1}`: row `p + 1`, Koszul degree `p`. -/
abbrev KZ (p : ℕ) : Type _ := WeylDatum.kdeg R ι (P (p + 1)) p
/-- `G p = T^{p,p+2}`: row `p + 2`, Koszul degree `p`. -/
abbrev KG (p : ℕ) : Type _ := WeylDatum.kdeg R ι (P (p + 2)) p

/-- **A leading bicomplex whose rows are Koszul complexes of Weyl data.** The Koszul
exactness fields are proved (`WeylDatum.row_exact`); the Chevalley–Eilenberg components and
the relations of `(d_K + d_CE)² = 0` are the remaining input. -/
noncomputable def ofKoszulRows
    (dCEY : ∀ p, KY R ι P p →ₗ[R] KX R ι P (p + 1))
    (dCEX : ∀ p, KX R ι P p →ₗ[R] KZ R ι P p)
    (dCEZ : ∀ p, KZ R ι P p →ₗ[R] KG R ι P p)
    (rel_YZ : ∀ p y, dCEX p ((W p).row p y) + (W (p + 1)).row p (dCEY p y) = 0)
    (rel_YY : ∀ p y, dCEX (p + 1) (dCEY p y) = 0)
    (rel_XG : ∀ p x, (W (p + 2)).row p (dCEX (p + 1) x) + dCEZ p ((W (p + 1)).row p x) = 0)
    (rel_CC : ∀ p x, dCEZ p (dCEX p x) = 0) :
    LeadingBicomplex R (KX R ι P) (KY R ι P)
      (KZ R ι P) (KG R ι P) where
  dKY p := (W p).row p
  dCEY := dCEY
  dKX p := (W (p + 1)).row p
  dCEX := dCEX
  dKZ p := (W (p + 2)).row p
  dCEZ := dCEZ
  rel_YZ := rel_YZ
  rel_YY := rel_YY
  rel_KK p y := by
    apply Subtype.ext
    simp only [WeylDatum.row_apply, (W (p + 1)).kd_kd]
    rfl
  rel_XG := rel_XG
  rel_CC := rel_CC
  exact_X p x hx := (W (p + 1)).row_exact p x hx
  exact_Z p z hz := (W (p + 2)).row_exact p z hz

end LeadingBicomplex

end VOA.LeadingKoszul
