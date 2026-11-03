/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SCLie
import VOA.DeligneAudit.E6SectorDefs
import VOA.DeligneAudit.DeligneSectorData

/-!
# Sparse bridges from structure-constant tables to the sector-chain interfaces

For a checked structure-constant table `T` (`SCLie.Checks N T`) with coefficient function
`scF T N x y c = sc T x y c`:

* `jacobiCoord_of_checks`: `JacobiCoord (scF T N)`;
* `adDer_quadP`: the coadjoint derivation of an in-range sparse quadratic is the sparse quadratic
  `adS T x l`;
* `adDer_comm_X`, `stable_of_bracket`: stability of a submodule under `adDer` passes from `a`, `b` to `c`
  when `⁅b_a, b_b⁆ = κ b_c` (`κ ≠ 0`), by Jacobi;
* `slotA_vecC`: a coadjoint operator on a sparse vector is the sparse vector `slotS`.

These turn the E₆ sector data into finite Boolean checks on sparse lists.
-/

namespace VOA.DeligneAudit.E6SectorSparse

open MvPolynomial VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.DeligneSector VOA.QuadraticJetCoefficientPairing

noncomputable section

variable {N : ℕ} {T : Table}

/-- Structure constants as a function on `Fin N`. -/
def scF (T : Table) (N : ℕ) (x y c : Fin N) : ℂ := sc T x y c

/-! ## Jacobi -/

theorem jacobiCoord_of_checks (hc : Checks N T) : JacobiCoord (scF T N) := by
  intro a b x c
  have h := leib_coord hc b a x c
  have hanti : ∑ m : Fin N, sc T b a m * sc T m x c = -∑ m : Fin N, sc T a b m * sc T m x c := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti hc b.2 a.2]; ring
  simp only [scF]
  linear_combination h + hanti

/-! ## The coadjoint derivation on sparse quadratics -/

/-- `Σ c · X_k` for a sparse linear form. -/
def linP (N : ℕ) (l : List (ℕ × ℤ)) : MvPolynomial (Fin N) ℂ :=
  (l.map fun p => (p.2 : MvPolynomial (Fin N) ℂ) * Xn N p.1).sum

theorem sum_X_eq_linP (l : List (ℕ × ℤ)) (hl : ∀ p ∈ l, p.1 < N) :
    ∑ c : Fin N, ((coef l c : ℂ) • X c : MvPolynomial (Fin N) ℂ) = linP N l := by
  induction l with
  | nil => simp [linP, coef]
  | cons p l ih =>
    rw [linP, List.map_cons, List.sum_cons, ← linP, ← ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    have hp : p.1 < N := hl p List.mem_cons_self
    simp only [coef_cons, Int.cast_add, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨p.1, hp⟩]
    · simp [Xn, hp, smul_eq_C_mul]
    · intro b _ hb
      have : p.1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp

theorem adDer_Xn (hb : boundOK T N = true) (x : Fin N) {i : ℕ} (hi : i < N) :
    adDer (scF T N) x (Xn N i) = linP N (entry T x i) := by
  rw [Xn, dif_pos hi, adDer, mkDerivation_X]
  simp only [scF, sc]
  exact sum_X_eq_linP _ (bound_of' hb x.2 hi)

theorem quadP_append (l₁ l₂ : List (ℕ × ℕ × ℤ)) : quadP N (l₁ ++ l₂) = quadP N l₁ + quadP N l₂ := by
  simp [quadP]

theorem quadP_flatMap {α : Type*} (l : List α) (g : α → List (ℕ × ℕ × ℤ)) :
    quadP N (l.flatMap g) = (l.map fun a => quadP N (g a)).sum := by
  induction l with
  | nil => simp [quadP]
  | cons a l ih => simp [List.flatMap_cons, quadP_append, ih]

theorem quadP_mapL (l : List (ℕ × ℤ)) (j : ℕ) (c : ℤ) :
    quadP N (l.map fun p => (p.1, j, c * p.2)) = (c : MvPolynomial (Fin N) ℂ) * linP N l * Xn N j := by
  induction l with
  | nil => simp [quadP, linP]
  | cons p l ih =>
    simp only [quadP, linP, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    push_cast; ring

theorem quadP_mapR (l : List (ℕ × ℤ)) (i : ℕ) (c : ℤ) :
    quadP N (l.map fun p => (i, p.1, c * p.2)) = (c : MvPolynomial (Fin N) ℂ) * Xn N i * linP N l := by
  induction l with
  | nil => simp [quadP, linP]
  | cons p l ih =>
    simp only [quadP, linP, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    push_cast; ring

theorem adDer_intCast (x : Fin N) (c : ℤ) : adDer (scF T N) x (c : MvPolynomial (Fin N) ℂ) = 0 := by
  have : (c : MvPolynomial (Fin N) ℂ) = algebraMap ℂ _ (c : ℂ) := by simp
  rw [this, Derivation.map_algebraMap]

/-- **The coadjoint derivation of a sparse quadratic.** -/
theorem adDer_quadP (hb : boundOK T N = true) (x : Fin N) (l : List (ℕ × ℕ × ℤ))
    (hl : qInRange N l = true) : adDer (scF T N) x (quadP N l) = quadP N (adS T x l) := by
  induction l with
  | nil => simp [quadP, adS]
  | cons t l ih =>
    simp only [qInRange, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    have ih' := ih hl.2
    rw [adS, List.flatMap_cons, ← adS, quadP_append, quadP_append, ← ih', quadP_mapL, quadP_mapR,
      quadP, List.map_cons, List.sum_cons, ← quadP, map_add, Derivation.leibniz, Derivation.leibniz,
      adDer_intCast, adDer_Xn hb x hl.1.1, adDer_Xn hb x hl.1.2]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring

/-! ## Commutators of coadjoint derivations -/

theorem adDer_comm_X (hJ : JacobiCoord (scF T N)) (a b i : Fin N) :
    adDer (scF T N) a (adDer (scF T N) b (X i)) - adDer (scF T N) b (adDer (scF T N) a (X i))
      = ∑ e, scF T N a b e • adDer (scF T N) e (X i) := by
  have hX : ∀ y j, adDer (scF T N) y (X j) = ∑ d, scF T N y j d • (X d : MvPolynomial (Fin N) ℂ) :=
    fun y j => by rw [adDer, mkDerivation_X]
  rw [hX b i, hX a i, map_sum, map_sum]
  simp only [Derivation.map_smul, hX, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (f := fun c d => (scF T N b i c * scF T N a c d) • (X d : MvPolynomial (Fin N) ℂ)),
    Finset.sum_comm (f := fun c d => (scF T N a i c * scF T N b c d) • (X d : MvPolynomial (Fin N) ℂ)),
    Finset.sum_comm (f := fun e d => (scF T N a b e * scF T N e i d) • (X d : MvPolynomial (Fin N) ℂ)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_smul, ← sub_smul, ← Finset.sum_smul]
  congr 1
  have := hJ a b i d
  simp only [scF] at this ⊢
  linear_combination -this

theorem derSum_apply (s : Fin N → ℂ)
    (D : Fin N → Derivation ℂ (MvPolynomial (Fin N) ℂ) (MvPolynomial (Fin N) ℂ)) (q : MvPolynomial (Fin N) ℂ) :
    (∑ e, s e • D e) q = ∑ e, s e • D e q := by
  show Derivation.coeFnAddMonoidHom (∑ e, s e • D e) q = _
  rw [map_sum, Finset.sum_apply]
  rfl

/-- The derivation commutator in terms of `adDer`, as an equation of derivations. -/
theorem adDer_comm (hJ : JacobiCoord (scF T N)) (a b : Fin N) (q : MvPolynomial (Fin N) ℂ) :
    adDer (scF T N) a (adDer (scF T N) b q) - adDer (scF T N) b (adDer (scF T N) a q)
      = ∑ e, scF T N a b e • adDer (scF T N) e q := by
  have h : ⁅adDer (scF T N) a, adDer (scF T N) b⁆ = ∑ e, scF T N a b e • adDer (scF T N) e := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [Derivation.commutator_apply, adDer_comm_X hJ, derSum_apply]
  have := congrArg (fun D : Derivation ℂ (MvPolynomial (Fin N) ℂ) (MvPolynomial (Fin N) ℂ) => D q) h
  simp only [Derivation.commutator_apply] at this
  rw [this, derSum_apply]

/-- **Stability passes along a single-term bracket.** -/
theorem stable_of_bracket (hJ : JacobiCoord (scF T N)) (S : Submodule ℂ (MvPolynomial (Fin N) ℂ))
    (a b c : Fin N) (κ : ℂ) (hκ : κ ≠ 0) (hab : ∀ e, scF T N a b e = if e = c then κ else 0)
    (ha : ∀ q ∈ S, adDer (scF T N) a q ∈ S) (hb : ∀ q ∈ S, adDer (scF T N) b q ∈ S) :
    ∀ q ∈ S, adDer (scF T N) c q ∈ S := by
  intro q hq
  have h := adDer_comm hJ a b q
  simp only [hab, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hmem : κ • adDer (scF T N) c q ∈ S := by
    rw [← h]; exact S.sub_mem (ha _ (hb q hq)) (hb _ (ha q hq))
  have := S.smul_mem κ⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this

/-! ## Coadjoint operators on sparse vectors -/

/-- The vector with sparse coordinates `l`. -/
def vecC (N : ℕ) (l : List (ℕ × ℤ)) : Fin N → ℂ := fun y => (coef l y : ℂ)

theorem coef_filter_ne_zero (l : List (ℕ × ℤ)) (k : ℕ) : coef (l.filter fun p => p.2 != 0) k = coef l k := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases hp : p.2 = 0
    · rw [List.filter_cons_of_neg (by simp [hp]), ih, coef_cons]; simp [hp]
    · rw [List.filter_cons_of_pos (by simp [hp]), coef_cons, coef_cons, ih]

theorem coef_range_map (h : ℕ → ℤ) (y : ℕ) (hy : y < N) :
    coef ((List.range N).map fun y => (y, h y)) y = h y := by
  unfold coef
  rw [List.map_map]
  have : ∀ z ∈ List.range N, ((fun p : ℕ × ℤ => if p.1 = y then p.2 else 0) ∘ fun y => (y, h y)) z
      = if z = y then h y else 0 := by
    intro z _; simp only [Function.comp_apply]; split_ifs with hz <;> simp [hz]
  rw [List.map_congr_left this, List.sum_map_ite_eq]
  simp [List.count_range, hy]

/-- **`slotA` on a sparse vector.** -/
theorem slotA_vecC (x : Fin N) (l : List (ℕ × ℤ)) (hl : ∀ p ∈ l, p.1 < N) :
    slotA (scF T N) x (vecC N l) = vecC N (slotS T N x l) := by
  funext y
  simp only [slotA, vecC, slotS]
  rw [coef_filter_ne_zero, coef_range_map _ y y.2]
  push_cast
  rw [neg_inj]
  have := sum_pairs l hl (fun d => (coef (entry T x y) d : ℂ))
  simp only [scF, sc]
  rw [List.map_map] at *
  calc ∑ d : Fin N, (coef (entry T x y) d : ℂ) * (coef l d : ℂ)
      = ∑ d : Fin N, (coef l d : ℂ) * (coef (entry T x y) d : ℂ) :=
        Finset.sum_congr rfl fun d _ => mul_comm _ _
    _ = _ := this.symm
    _ = _ := by
        congr 1
        apply List.map_congr_left
        intro p _
        simp

theorem slotS_inRange (x : ℕ) (l : List (ℕ × ℤ)) : ∀ p ∈ slotS T N x l, p.1 < N := by
  intro p hp
  simp only [slotS, List.mem_filter, List.mem_map, List.mem_range] at hp
  obtain ⟨⟨y, hy, rfl⟩, _⟩ := hp
  exact hy

theorem wordA_vecC (l : List (Fin N)) (v : List (ℕ × ℤ)) (hv : ∀ p ∈ v, p.1 < N) :
    wordA (scF T N) l (vecC N v) = vecC N (wordS T N (l.map Fin.val) v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [wordA, List.map_cons, wordS]
    rw [ih, slotA_vecC]
    cases l with
    | nil => simpa [wordS] using hv
    | cons y l' => exact slotS_inRange _ _

theorem single_eq_vecC (c : Fin N) : (Pi.single c 1 : Fin N → ℂ) = vecC N [((c : ℕ), 1)] := by
  funext y
  simp only [vecC, coef_cons, coef_nil, add_zero, Pi.single_apply]
  by_cases h : y = c
  · subst h; simp
  · have : (c : ℕ) ≠ y := fun h' => h (Fin.ext h'.symm)
    simp [h, this]

theorem vecC_eq_of_zeroL {l₁ l₂ : List (ℕ × ℤ)} (c : ℤ) (h : zeroL (l₁ ++ scale (-c) l₂) = true) :
    vecC N l₁ = (c : ℂ) • vecC N l₂ := by
  funext k
  have := coef_eq_zero_of_zeroL h k
  rw [coef_append, coef_scale] at this
  show (coef l₁ k : ℂ) = (c : ℂ) * (coef l₂ k : ℂ)
  have : coef l₁ k = c * coef l₂ k := by linarith
  exact_mod_cast this

theorem vecC_append (l₁ l₂ : List (ℕ × ℤ)) : vecC N (l₁ ++ l₂) = vecC N l₁ + vecC N l₂ := by
  funext k; simp [vecC, coef_append]

theorem vecC_scale (c : ℤ) (l : List (ℕ × ℤ)) : vecC N (scale c l) = (c : ℂ) • vecC N l := by
  funext k; simp [vecC, coef_scale]

end

end VOA.DeligneAudit.E6SectorSparse
