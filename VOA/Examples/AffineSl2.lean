/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.AffineLie
import VOA.Foundations.FormalCalculus
import VOA.Foundations.Locality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin

/-!
# The level-`k` affine `𝔰𝔩₂` VOA — the single-module realization

## Status
The single-module level-`k` affine `𝔰𝔩₂` current algebra — the FULL
affine commutator `current_comm` (both the structure-constant term `∑_c f^{ab}_c J^c_{m+n}` and
the central term `m·k·κ(a,b)·δ_{m+n,0}·id` on one `End`) and the current-field `N = 2` mutual
locality `Jfield_local` — is proved, `sorry`-free / axiom-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`; these operator/commutator/locality
results do **not** reach the theorem `VOA.pbw` — it enters only
the *separate* vacuum-nonvanishing layer `vacuumVector_ne_zero` in `Foundations.AffineLie`, consumed
downstream). The all-states VOA reconstruction `YA` and the full `VertexOperatorAlgebra` instance
are the SEPARATE `Examples/AffineSl2VOA` / `Examples/Affine` row.

This file replaces a split construction (where the non-abelian
structure-constant currents live on the loop module `LoopMod` at level `0`, and the central
`m·k·κ(a,b)·δ` term lives separately on `Sl2Fock`) by a **single module** carrying **both**
halves of the affine commutator simultaneously, at genuine level `k`.

## Route taken: the abstract route (reuse `Foundations.AffineLie`)

The technical heart — a faithful `End`-realization carrying the structure constants AND the
central charge at once — is exactly the level-`k` **vacuum module** `𝒱(𝔰𝔩₂, k)`, which the
project already builds in `Foundations.AffineLie` (`vacuumModule`, carrying the proved
`ell0`-grading and the theorem `pbw`). We:

1. realize `𝔰𝔩₂` concretely as the Chevalley-basis Lie algebra `Sl2 := Fin 3 → ℂ`
   (colours `e,f,h`) with structure constants `fabc` (`[h,e]=2e`, `[h,f]=-2f`, `[e,f]=h`) —
   `LieRing`/`LieAlgebra ℂ` instances, Jacobi from a `Fin 3` bash;
2. build the normalised Killing form `kappaForm : BilinForm ℂ Sl2` (`κ(e,f)=1`, `κ(h,h)=2`)
   and prove it `IsInvariant` (symmetric + ad-invariant);
3. instantiate `AffineLie Sl2 kappaForm hκ` and its level-`k` vacuum module `vacuumSpace`;
4. define the **current modes** `J a m := vacuumRho (ofLoop (basis a) m)` — genuine
   endomorphisms of the *single* module;
5. derive the **FULL affine commutator** on this one module
   `⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}·id`
   directly from `vacuumRho.map_lie`, `affine_bracket`, and `vacuum_acts_central` — both the
   structure-constant term and the central term, on the *same* `End`;
6. package the current fields `Jfield` and prove **mutual locality with bound `N = 2`**.

The central term is genuine: `C` acts as `k·id` (`vacuum_acts_central`), so the level is
visible to the action — which is precisely what no adjoint/loop action on a free module could
see (the Stage-1 obstruction note).

## Axioms
`#print axioms` on the main results (`kappaForm_isInvariant`, `J`, `current_comm`,
`Jfield_mode`, `Jfield_local`) ⇒ `[propext, Classical.choice, Quot.sound]` — **`pbw`-free**: these
operator / commutator / locality results do not reach the vacuum-nonvanishing axiom.
(`VOA.pbw` is consumed only by the *separate* vacuum-nonvanishing layer
`vacuumVector_ne_zero` in `Foundations.AffineLie`, used downstream in `Examples/AffineSl2VOA`.)  No
`sorry`/`admit`, no new axioms.

## References
* Gannon §3.2 (affine bracket), §5.2.2 (affine VOA); Kac §10; Frenkel–Zhu; Lepowsky–Li Ch. 6.
-/

namespace VOA.AffineVOA

open scoped BigOperators
open VOA.AffineLie

universe u

/-! ## §1  The `𝔰𝔩₂` structure constants and normalised Killing form -/

/-- The Chevalley basis colours `e = 0`, `f = 1`, `h = 2` of `𝔰𝔩₂`. -/
abbrev colE : Fin 3 := 0
abbrev colF : Fin 3 := 1
abbrev colH : Fin 3 := 2

/-- The `𝔰𝔩₂` **structure constants** `f^{ab}_c` in the Chevalley basis
`[h,e]=2e`, `[h,f]=-2f`, `[e,f]=h` (with antisymmetrisations). -/
def fabc : Fin 3 → Fin 3 → Fin 3 → ℂ
  | 2, 0, 0 => 2    -- ⁅h,e⁆ = 2e
  | 0, 2, 0 => -2   -- ⁅e,h⁆ = -2e
  | 2, 1, 1 => -2   -- ⁅h,f⁆ = -2f
  | 1, 2, 1 => 2    -- ⁅f,h⁆ = 2f
  | 0, 1, 2 => 1    -- ⁅e,f⁆ = h
  | 1, 0, 2 => -1   -- ⁅f,e⁆ = -h
  | _, _, _ => 0

/-- The **normalised Killing form** `κ` on `𝔰𝔩₂`: `κ(e,f)=κ(f,e)=1`, `κ(h,h)=2`, else `0`. -/
def kappa : Fin 3 → Fin 3 → ℂ
  | 0, 1 => 1
  | 1, 0 => 1
  | 2, 2 => 2
  | _, _ => 0

/-- The structure constants are **antisymmetric** in the upper indices: `f^{ab}_c = -f^{ba}_c`. -/
theorem fabc_antisymm (a b c : Fin 3) : fabc a b c = - fabc b a c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [fabc]

/-- The Killing form is **symmetric**: `κ(a,b) = κ(b,a)`. -/
theorem kappa_symm (a b : Fin 3) : kappa a b = kappa b a := by
  fin_cases a <;> fin_cases b <;> simp [kappa]

/-! ## §2  The concrete Chevalley `𝔰𝔩₂` as a Lie algebra on `Fin 3 → ℂ` -/

/-- The concrete `𝔰𝔩₂`: the free `ℂ`-module on the Chevalley basis `{e, f, h}`. -/
abbrev Sl2 : Type := Fin 3 → ℂ

/-- The basis vector for colour `a` (`δ_a`): `e₀ = e`, `e₁ = f`, `e₂ = h`. -/
noncomputable def basis (a : Fin 3) : Sl2 := Pi.single a 1

/-- The `c`-component of the Chevalley bracket `⁅x, y⁆ = ∑_{a,b} xₐ y_b f^{ab}_c`. -/
def brComp (x y : Sl2) (c : Fin 3) : ℂ := ∑ a, ∑ b, x a * y b * fabc a b c

/-- The Chevalley bracket on `Sl2`. -/
instance : Bracket Sl2 Sl2 where
  bracket x y := fun c => brComp x y c

@[simp] theorem bracket_apply (x y : Sl2) (c : Fin 3) :
    ⁅x, y⁆ c = ∑ a, ∑ b, x a * y b * fabc a b c := rfl

theorem add_lie_sl2 (x y z : Sl2) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  funext c
  simp only [bracket_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lie_add_sl2 (x y z : Sl2) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  funext c
  simp only [bracket_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lie_self_sl2 (x : Sl2) : ⁅x, x⁆ = 0 := by
  funext c
  simp only [bracket_apply, Pi.zero_apply, Fin.sum_univ_three]
  -- ∑_{a,b} xₐ x_b f^{ab}_c = 0 by antisymmetry of f in (a,b); explicit `Fin 3` bash.
  fin_cases c <;> simp [fabc] <;> ring

theorem leibniz_lie_sl2 (x y z : Sl2) : ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  funext c
  simp only [bracket_apply, Pi.add_apply]
  -- Every element of `Sl2 = Fin 3 → ℂ` is determined by its three components; expand all
  -- inner brackets to explicit `Fin 3`-sums and reduce the Jacobi identity to a polynomial
  -- identity in `x i, y j, z l` and the structure constants, killed by `ring`.
  simp only [Fin.sum_univ_three]
  fin_cases c <;> simp [fabc] <;> ring

theorem smul_lie_sl2 (r : ℂ) (x y : Sl2) : ⁅r • x, y⁆ = r • ⁅x, y⁆ := by
  funext c
  simp only [bracket_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lie_smul_sl2 (r : ℂ) (x y : Sl2) : ⁅x, r • y⁆ = r • ⁅x, y⁆ := by
  funext c
  simp only [bracket_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The Chevalley `𝔰𝔩₂` is a `LieRing` (Jacobi from `leibniz_lie_sl2`). -/
noncomputable instance : LieRing Sl2 where
  add_lie := add_lie_sl2
  lie_add := lie_add_sl2
  lie_self := lie_self_sl2
  leibniz_lie := leibniz_lie_sl2

/-- The Chevalley `𝔰𝔩₂` is a `ℂ`-Lie algebra. -/
noncomputable instance : LieAlgebra ℂ Sl2 where
  lie_smul := lie_smul_sl2

/-- The bracket on basis vectors realises the structure constants:
`⁅eₐ, e_b⁆ = ∑_c f^{ab}_c e_c`, i.e. `⁅eₐ, e_b⁆ c = f^{ab}_c`. -/
@[simp] theorem basis_bracket_component (a b c : Fin 3) :
    ⁅basis a, basis b⁆ c = fabc a b c := by
  simp only [bracket_apply, basis, Pi.single_apply]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'; simp [hb']
  · intro h; exact absurd (Finset.mem_univ b) h
  · intro a' _ ha'
    rw [Finset.sum_eq_zero]; intro b' _; simp [ha']
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## §3  The normalised Killing form `κ : BilinForm ℂ Sl2` and its invariance -/

/-- The normalised Killing form `κ(x, y) = ∑_{a,b} xₐ y_b κ(a,b)` as a `ℂ`-bilinear form. -/
noncomputable def kappaForm : LinearMap.BilinForm ℂ Sl2 where
  toFun x := { toFun := fun y => ∑ a, ∑ b, x a * y b * kappa a b
               map_add' := fun y y' => by
                 simp only [Pi.add_apply]
                 rw [← Finset.sum_add_distrib]
                 refine Finset.sum_congr rfl fun a _ => ?_
                 rw [← Finset.sum_add_distrib]
                 refine Finset.sum_congr rfl fun b _ => ?_; ring
               map_smul' := fun r y => by
                 simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
                 refine Finset.sum_congr rfl fun a _ => ?_
                 refine Finset.sum_congr rfl fun b _ => ?_; ring }
  map_add' x x' := by
    refine LinearMap.ext fun y => ?_
    show (∑ a, ∑ b, (x a + x' a) * y b * kappa a b)
        = (∑ a, ∑ b, x a * y b * kappa a b) + ∑ a, ∑ b, x' a * y b * kappa a b
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_; ring
  map_smul' r x := by
    refine LinearMap.ext fun y => ?_
    show (∑ a, ∑ b, (r • x) a * y b * kappa a b)
        = r • ∑ a, ∑ b, x a * y b * kappa a b
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_; ring

@[simp] theorem kappaForm_apply (x y : Sl2) :
    kappaForm x y = ∑ a, ∑ b, x a * y b * kappa a b := rfl

/-- `κ` on basis vectors: `κ(eₐ, e_b) = κ(a,b)`. -/
@[simp] theorem kappaForm_basis (a b : Fin 3) : kappaForm (basis a) (basis b) = kappa a b := by
  simp only [kappaForm_apply, basis, Pi.single_apply]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'; simp [hb']
  · intro h; exact absurd (Finset.mem_univ b) h
  · intro a' _ ha'
    rw [Finset.sum_eq_zero]; intro b' _; simp [ha']
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The normalised Killing form is **invariant** (symmetric + ad-invariant): the input the
affine algebra `AffineLie Sl2 kappaForm` needs. Proved by reducing to component bashes. -/
theorem kappaForm_isInvariant : kappaForm.IsInvariant where
  symm x y := by
    simp only [kappaForm_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [kappa_symm a b]; ring
  invariant x y z := by
    -- ∑_{c,d} (⁅x,y⁆ c) z d κ(c,d) = ∑_{a,d} x a (⁅y,z⁆ d) κ(a,d)
    simp only [kappaForm_apply, bracket_apply]
    simp only [Fin.sum_univ_three, kappa, fabc]
    ring

/-! ## §4  The affine algebra, the level-`k` vacuum module, and the current modes -/

/-- The affine `𝔰𝔩₂` algebra `ĝ = (𝔰𝔩₂ ⊗ ℂ[t,t⁻¹]) ⊕ ℂC ⊕ ℂℓ₀` with the normalised Killing
form (Gannon §3.2). -/
noncomputable abbrev AffSl2 : Type := AffineLie Sl2 kappaForm kappaForm_isInvariant

/-- The level-`k` **vacuum module** `𝒱(𝔰𝔩₂, k)` — the single module carrying both halves of
the affine commutator (Gannon §3.2). -/
noncomputable abbrev WakModule (k : ℂ) : Type :=
  vacuumSpace kappaForm kappaForm_isInvariant k

/-- The affine current **mode** `J^a_m` on the *single* module `𝒱(𝔰𝔩₂, k)`: the action of the
loop generator `eₐ ⊗ tᵐ`. These are genuine endomorphisms of one module — the structure
constants and the central charge both act here. -/
noncomputable def J (k : ℂ) (a : Fin 3) (m : ℤ) : Module.End ℂ (WakModule k) :=
  vacuumRho kappaForm kappaForm_isInvariant k (ofLoop kappaForm kappaForm_isInvariant (basis a) m)

/-- The current modes are linear in the colour, matching `∑_c (·) J^c`. -/
theorem J_eq (k : ℂ) (a : Fin 3) (m : ℤ) :
    J k a m = vacuumRho kappaForm kappaForm_isInvariant k
      (ofLoop kappaForm kappaForm_isInvariant (basis a) m) := rfl

/-! ## §5  The FULL affine commutator on the single module (the technical heart)

`⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}·id`,
with the structure-constant term AND the central term living on the **same** `End`. -/

/-- The Chevalley bracket decomposed in the basis: `⁅eₐ, e_b⁆ = ∑_c f^{ab}_c • e_c`. -/
theorem basis_bracket_eq (a b : Fin 3) :
    ⁅basis a, basis b⁆ = ∑ c, fabc a b c • basis c := by
  funext d
  rw [basis_bracket_component]
  simp only [Finset.sum_apply, Pi.smul_apply, basis, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · intro h; exact absurd (Finset.mem_univ d) h

/-- The loop element of the structure-constant bracket expands as a sum of basis loop modes:
`(⁅eₐ, e_b⁆) ⊗ tᵖ = ∑_c f^{ab}_c (e_c ⊗ tᵖ)`. -/
theorem ofLoop_bracket_eq (a b : Fin 3) (p : ℤ) :
    ofLoop kappaForm kappaForm_isInvariant ⁅basis a, basis b⁆ p
      = ∑ c, fabc a b c • ofLoop kappaForm kappaForm_isInvariant (basis c) p := by
  rw [← ofLoopₗ_apply, basis_bracket_eq, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ofLoopₗ_apply]

/-- The Killing form on basis vectors equals the structure-constant Killing form `κ(a,b)`. -/
theorem kappaForm_basis_eq_kappa (a b : Fin 3) :
    kappaForm (basis a) (basis b) = kappa a b := kappaForm_basis a b

/-- **The FULL affine commutator on `𝒱(𝔰𝔩₂, k)` (the technical heart).**
On the *single* level-`k` vacuum module,
`⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}·id`.
Both the non-abelian structure-constant term and the central term act on the **same** `End`.
Proof: `vacuumRho.map_lie` turns the operator commutator into `ρ ⁅eₐ⊗tᵐ, e_b⊗tⁿ⁆`; the
defining `affine_bracket` (Gannon §3.2.2) splits it into the loop bracket and the cocycle; the
loop bracket expands by `ofLoop_bracket_eq` into the `∑_c f^{ab}_c`-sum, and the cocycle term
acts as `k·id` via `vacuum_acts_central` — the genuine level-`k` centre. -/
theorem current_comm (k : ℂ) (a b : Fin 3) (m n : ℤ) :
    J k a m * J k b n - J k b n * J k a m
      = (∑ c, fabc a b c • J k c (m + n))
        + (if m + n = 0 then ((m : ℂ) * k * kappa a b) • LinearMap.id else 0) := by
  set κ := kappaForm
  set hκ := kappaForm_isInvariant
  -- Operator commutator = ρ of the Lie bracket.
  have hml := (vacuumRho κ hκ k).map_lie
      (ofLoop κ hκ (basis a) m) (ofLoop κ hκ (basis b) n)
  rw [LieRing.of_associative_ring_bracket] at hml
  -- `J a m * J b n - J b n * J a m = vacuumRho ⁅eₐ⊗tᵐ, e_b⊗tⁿ⁆`.
  rw [J_eq, J_eq]
  rw [show vacuumRho κ hκ k (ofLoop κ hκ (basis a) m) * vacuumRho κ hκ k (ofLoop κ hκ (basis b) n)
        - vacuumRho κ hκ k (ofLoop κ hκ (basis b) n) * vacuumRho κ hκ k (ofLoop κ hκ (basis a) m)
      = vacuumRho κ hκ k ⁅ofLoop κ hκ (basis a) m, ofLoop κ hκ (basis b) n⁆ from hml.symm]
  -- Apply the affine bracket (Gannon §3.2.2).
  rw [affine_bracket κ hκ (basis a) (basis b) m n, map_add]
  congr 1
  · -- Structure-constant term: ρ ((⁅eₐ,e_b⁆) ⊗ t^{m+n}) = ∑_c f^{ab}_c J^c_{m+n}.
    rw [ofLoop_bracket_eq, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, J_eq]
  · -- Central term: ρ (if m+n=0 then m·κ(eₐ,e_b) • C) = if m+n=0 then m·k·κ(a,b) • id.
    by_cases hmn : m + n = 0
    · rw [if_pos hmn, if_pos hmn, map_smul, vacuum_acts_central, kappaForm_basis_eq_kappa,
        smul_smul]
      congr 1
      ring
    · rw [if_neg hmn, if_neg hmn, map_zero]

/-- The full affine commutator stated with the Lie bracket `⁅·,·⁆` of `End ℂ 𝒱(𝔰𝔩₂, k)`. -/
theorem current_lie_comm (k : ℂ) (a b : Fin 3) (m n : ℤ) :
    ⁅J k a m, J k b n⁆
      = (∑ c, fabc a b c • J k c (m + n))
        + (if m + n = 0 then ((m : ℂ) * k * kappa a b) • LinearMap.id else 0) := by
  rw [Ring.lie_def (J k a m) (J k b n)]; exact current_comm k a b m n

/-! ## §6  The current fields and `(z₁-z₂)²` locality (bound `N = 2`) -/

/-- The **current field** `J^a(z) = ∑_m J^a_m z^{-m-1}` as a formal distribution of
`End ℂ 𝒱(𝔰𝔩₂, k)`. Its `zʲ`-coefficient is `J^a_{-j-1}`, so its `m`-th mode is `J^a_m`. -/
noncomputable def Jfield (k : ℂ) (a : Fin 3) : FormalDist (Module.End ℂ (WakModule k)) :=
  fun j => J k a (-j - 1)

@[simp] theorem Jfield_apply (k : ℂ) (a : Fin 3) (j : ℤ) : Jfield k a j = J k a (-j - 1) := rfl

/-- The modes of the current field are the current modes: `mode (J^a(z)) m = J^a_m`. -/
theorem Jfield_mode (k : ℂ) (a : Fin 3) (m : ℤ) : mode (Jfield k a) m = J k a m := by
  rw [mode_apply, Jfield_apply, show -(-m - 1) - 1 = m from by ring]

/-- The **non-abelian OPE coefficient** `c⁰(z₂) = ∑_c f^{ab}_c J^c(z₂)`: the `∂⁰δ`-piece of the
commutator (the simple-pole / structure-constant term, `∼ 1/(z₁-z₂)`). -/
noncomputable def opeCoeff0 (k : ℂ) (a b : Fin 3) :
    FormalDist (Module.End ℂ (WakModule k)) :=
  fun j => ∑ c, fabc a b c • Jfield k c j

/-- The **central OPE coefficient** `c¹(z₂) = k·κ(a,b)·id`: the `∂¹δ`-piece (the double-pole /
central term, `∼ k·κ(a,b)/(z₁-z₂)²`). -/
noncomputable def opeCoeff1 (k : ℂ) (a b : Fin 3) :
    FormalDist (Module.End ℂ (WakModule k)) :=
  fun t => if t = 0 then (k * kappa a b) • LinearMap.id else 0

/-- The commutator distribution of two current fields decomposes as a sum of a `∂⁰δ` term (the
non-abelian structure-constant currents) and a `∂¹δ` term (the central charge):
`[J^a(z₁), J^b(z₂)] = (∑_c f^{ab}_c J^c(z₂))·δ(z₁/z₂) + k·κ(a,b)·∂_{z₂}δ(z₁/z₂)`. -/
theorem bracketDist_Jfield_eq (k : ℂ) (a b : Fin 3) :
    bracketDist (Jfield k a) (Jfield k b)
      = deltaDeriv 0 (opeCoeff0 k a b) + deltaDeriv 1 (opeCoeff1 k a b) := by
  refine FormalDist₂.ext fun m n => ?_
  rw [bracketDist_apply, Jfield_apply, Jfield_apply, current_comm]
  show (∑ c, fabc a b c • J k c ((-m - 1) + (-n - 1)))
      + (if (-m - 1) + (-n - 1) = 0 then
          (((-m - 1 : ℤ) : ℂ) * k * kappa a b) • LinearMap.id else 0)
    = deltaDeriv 0 (opeCoeff0 k a b) m n + deltaDeriv 1 (opeCoeff1 k a b) m n
  rw [deltaDeriv_apply, deltaDeriv_apply]
  simp only [opeCoeff0, opeCoeff1]
  -- `(-m-1)+(-n-1) = -(m+n+2)`, and `J^c_{-(m+n+2)} = Jfield c (m+n+1)`.
  rw [Finset.range_zero, Finset.prod_empty, one_smul,
    Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Nat.cast_one]
  congr 1
  · -- Structure-constant term.
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Jfield_apply, show -(m + n + 1 + 0) - 1 = -m - 1 + (-n - 1) from by ring]
  · -- Central term: index `(-m-1)+(-n-1)=0 ↔ m+n+1+1=0`, and scalar `(-m-1)`.
    by_cases hmn : (-m - 1) + (-n - 1) = 0
    · rw [if_pos hmn, if_pos (by omega : m + n + 1 + 1 = 0),
        ← Int.cast_smul_eq_zsmul ℂ (-m - 1 : ℤ)
          ((k * kappa a b) • LinearMap.id : Module.End ℂ (WakModule k)),
        smul_smul, mul_assoc]
    · rw [if_neg hmn, if_neg (by omega : ¬ m + n + 1 + 1 = 0)]
      exact (smul_zero _).symm

/-- **Self/mutual locality with bound `N = 2`**: two factors of `(z₁-z₂)` annihilate the
commutator of any two current fields, `(z₁-z₂)²·[J^a(z₁), J^b(z₂)] = 0`. The commutator is the
sum of a `∂⁰δ` term (killed by `(z₁-z₂)¹`) and a `∂¹δ` central term (killed by `(z₁-z₂)²`);
both are killed by `mulBySubPow 2`. This is the Stage-1.5 input to the vertex-algebra locality
axiom VA4. -/
theorem Jfield_self_local (k : ℂ) (a b : Fin 3) :
    mulBySubPow 2 (bracketDist (Jfield k a) (Jfield k b)) = 0 := by
  rw [bracketDist_Jfield_eq, map_add,
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 0 + 1 ≤ 2) (opeCoeff0 k a b),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 1 + 1 ≤ 2) (opeCoeff1 k a b), add_zero]

/-- The current fields are **mutually local** (`Local` with `N = 2`) for every pair of colours
`a, b` — the locality hypothesis behind VA4. -/
theorem Jfield_local (k : ℂ) (a b : Fin 3) : Local (Jfield k a) (Jfield k b) :=
  ⟨2, Jfield_self_local k a b⟩

/-! ## §7  Smoke tests -/

/-- The `[e_m, e_n]` commutator: `e` is null (`f^{ee}_c = 0`, `κ(e,e)=0`), so it vanishes —
the abelian (Heisenberg) subalgebra check. -/
example (k : ℂ) (m n : ℤ) : J k colE m * J k colE n - J k colE n * J k colE m = 0 := by
  rw [current_comm]
  rw [show (∑ c, fabc colE colE c • J k c (m + n)) = 0 from
    Finset.sum_eq_zero fun c _ => by simp [fabc]]
  rw [show (if m + n = 0 then ((m : ℂ) * k * kappa colE colE) • LinearMap.id else 0)
      = (0 : Module.End ℂ (WakModule k)) from by simp [kappa]]
  rw [add_zero]

/-- The `[e_m, f_n]` commutator carries the Cartan current `h` plus the level-`k` centre:
`⁅e_m, f_n⁆ = J^h_{m+n} + m·k·δ_{m+n,0}·id` (since `f^{ef}_h = 1`, `κ(e,f)=1`). -/
example (k : ℂ) (m n : ℤ) :
    J k colE m * J k colF n - J k colF n * J k colE m
      = J k colH (m + n) + (if m + n = 0 then ((m : ℂ) * k) • LinearMap.id else 0) := by
  rw [current_comm]
  congr 1
  · rw [Fin.sum_univ_three]
    simp [fabc]
  · by_cases h : m + n = 0
    · rw [if_pos h, if_pos h]; congr 1; simp [kappa]
    · rw [if_neg h, if_neg h]

end VOA.AffineVOA
