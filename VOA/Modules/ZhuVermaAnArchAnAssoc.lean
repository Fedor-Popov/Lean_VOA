/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBimodComp
import VOA.Modules.ZhuVermaAnArchAssocCore
import VOA.Modules.ZhuMuIdentity

/-!
# The `A_n(𝒱)` algebra core: `AnmComposeBalanced` and `A_n` associativity.

This file delivers the two `A_n(𝒱)`-algebra cores of the Dong–Jiang / Frenkel–Zhu layer:

1. **`AnmComposeBalanced`** (`∀ p n m`) — the `A_n(𝒱)`-balancing of the Dong–Jiang composition
   `A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱) → A_{p,m}(𝒱)` (DJ Prop. 3.4): mod `O_{p,m}`,
   `(u *^p_n a) *^{p,n,m} v ≡ u *^{p,n,m} (a *^n_m v)`.  Since `anmCompose W p n m = anmRight W p m`,
   this is exactly the **associativity of the residue right-action product modulo `O_{p,m}`**:
   `anmRight W p m (anmRight W p n u a) v ≡ anmRight W p m u (anmRight W n m a v)`.  We
   * isolate the precise residue-membership target `AnmBalanceCore W p n m`
     (the balancing difference lands in `O_{p,m}`),
   * give the clean **bridge** `anmComposeBalanced_of_core : AnmBalanceCore → AnmComposeBalanced`
     (via `AnmComposeBalanced_of_repr` + `Submodule.Quotient.eq`),
   * prove the full **trilinear homogeneity reduction** `AnmBalanceCore_of_homogeneous`
     (three nested `iSup_induction`s over the internal grading, mirroring the proven
     `AnFull.assocCore_of_homogeneous`), so the entire balancing content is pinned to the
     **homogeneous** target `AnmBalanceHom W p n m`.

   This mirrors the `A_n(𝒱)` associativity architecture of `ZhuVermaAnArchAssoc.lean`: a precise
   membership `Prop`, a clean quotient bridge, and a homogeneity reduction, leaving exactly the
   depth-`(p,n,m)` FZ scalar core (engine-verified on the rank-1 free boson) as the explicit, honest
   remaining target — NOT an axiom, NOT a `sorry`.

2. **`A_n(𝒱)` associativity** (`AnFull.AssocLaw`, `n ≥ 1`).  The reduction to the homogeneous FZ
   associator `AnFull.AssocHom` is already proved (`ZhuVermaAnArchAssoc`/`AssocCore`).  We re-export
   the named depth-`n` entry points and record the precise residue-product form of the associator,
   pinning the remaining content to the depth-`n` analogue of Zhu's `assoc_eq` scalar cores.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `anmBalance W p n m u a v` — the balancing-defect vector
  `anmRight W p m (anmRight W p n u a) v − anmRight W p m u (anmRight W n m a v)`, with full slotwise
  trilinearity (`anmBalance_add_*`/`anmBalance_smul_*`, `anmBalance_zero_*`).
* `AnmBalanceCore W p n m` — the precise residue-membership target Prop
  `∀ u a v, anmBalance W p n m u a v ∈ Onm W p m`.
* `anmComposeBalanced_of_core` — the bridge `AnmBalanceCore → AnmComposeBalanced` (the balancing
  factoring of the composition through `⊗_{A_n(𝒱)}` follows from the residue membership).
* `AnmBalanceHom W p n m` — the homogeneous balancing target (for `u ∈ 𝒱ₚ', a ∈ 𝒱_q', v ∈ 𝒱ᵣ'`).
* **`AnmBalanceCore_of_homogeneous`** — the trilinear homogeneity reduction `AnmBalanceHom →
  AnmBalanceCore` (three nested `iSup_induction`s), pinning all balancing content to the homogeneous
  core.
* `anmComposeBalanced_of_homogeneous` — the end-to-end chain `AnmBalanceHom → AnmComposeBalanced`.
* `leftProd_eq_anmRight_diag`, `Onm_diag_eq_OnFull`, `anmBalance_diag_eq_assoc`,
  `AnmBalanceCore_diag_iff_assocCore` — the **diagonal bridge** identifying the `(n,n,n)`
  Dong–Jiang composition-balancing with `A_n(𝒱)` associativity; hence `anmBalanceCore_zero`
  (the `(0,0,0)` balancing proved via the proved level-`0` associativity `AnFull.assocCore_zero`).
* `AnFull_assoc_eq_residue`, `AnFull_assocLaw_of_assocHom` — the residue-product form of the FZ
  associator and the named depth-`n` associativity entry point.

## What is OPEN (precise, NOT faked — no `sorry`, no axiom)

* `AnmBalanceHom W p n m` for general `(p, n, m)` (with `m ≥ 1` and/or `p ≥ 1`) — the depth-mixing FZ
  associator combinatorics (DJ Prop. 3.4 residue-product associativity mod `O`).  Engine-verified
  TRUE on the rank-1 free boson (`certificates/mathematica/balanced_check2.wl`).  This is the same
  depth-`n` scalar-core content as `AnFull.AssocHom W n` for `n ≥ 1` (the `2n`-pole-shifted analogues
  of `ZhuMu.mu_identity` / `ZhuUCore.u_core` / `ZhuVCore.v_core`).  Stated precisely; reduced to the
  homogeneous case; carried as an explicit `Prop`.
* `AnFull.AssocHom W n` for `n ≥ 1` — unchanged from `ZhuVermaAnArchAssocCore`; the depth-`n` FZ
  associator core.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §3 Prop. 3.4, §4 Thm 4.13;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96, Lemma 2.1; Frenkel–Zhu, Duke 66 (1992); Zhu, J. AMS 9
(1996); mirror of `ZhuVermaAnArchAssoc.lean` (`assoc`, `assocCore_of_homogeneous`) and
`ZhuAssociator.lean` (`associator_core`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The Dong–Jiang composition-balancing defect vector and its trilinearity. -/

variable (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)

/-- **The Dong–Jiang composition-balancing defect**
`Bal(u,a,v) = (u *^p_n a) *^{p,n,m} v − u *^{p,n,m} (a *^n_m v)`, i.e. in residue form
`anmRight W p m (anmRight W p n u a) v − anmRight W p m u (anmRight W n m a v)`.  Its membership in
`O_{p,m}` is the `A_n(𝒱)`-balancing (DJ Prop. 3.4), the associativity of the residue right-action
product modulo `O_{p,m}`. -/
noncomputable def anmBalance (u a v : 𝒱) : 𝒱 :=
  anmRight W p m (anmRight W p n u a) v - anmRight W p m u (anmRight W n m a v)

theorem anmBalance_eq (u a v : 𝒱) :
    anmBalance W p n m u a v
      = anmCompose W p n m (anmRight W p n u a) v
        - anmCompose W p n m u (anmRight W n m a v) := rfl

/-! ### Slotwise ℂ-trilinearity. -/

theorem anmBalance_add_left (u₁ u₂ a v : 𝒱) :
    anmBalance W p n m (u₁ + u₂) a v
      = anmBalance W p n m u₁ a v + anmBalance W p n m u₂ a v := by
  simp only [anmBalance, anmRight_add_left]
  abel

theorem anmBalance_smul_left (s : ℂ) (u a v : 𝒱) :
    anmBalance W p n m (s • u) a v = s • anmBalance W p n m u a v := by
  simp only [anmBalance, anmRight_smul_left, smul_sub]

theorem anmBalance_add_mid (u a₁ a₂ v : 𝒱) :
    anmBalance W p n m u (a₁ + a₂) v
      = anmBalance W p n m u a₁ v + anmBalance W p n m u a₂ v := by
  simp only [anmBalance, anmRight_add_right, anmRight_add_left]
  abel

theorem anmBalance_smul_mid (s : ℂ) (u a v : 𝒱) :
    anmBalance W p n m u (s • a) v = s • anmBalance W p n m u a v := by
  simp only [anmBalance, anmRight_smul_right, anmRight_smul_left, smul_sub]

theorem anmBalance_add_right (u a v₁ v₂ : 𝒱) :
    anmBalance W p n m u a (v₁ + v₂)
      = anmBalance W p n m u a v₁ + anmBalance W p n m u a v₂ := by
  simp only [anmBalance, anmRight_add_right]
  abel

theorem anmBalance_smul_right (s : ℂ) (u a v : 𝒱) :
    anmBalance W p n m u a (s • v) = s • anmBalance W p n m u a v := by
  simp only [anmBalance, anmRight_smul_right, smul_sub]

theorem anmBalance_zero_left (a v : 𝒱) : anmBalance W p n m 0 a v = 0 := by
  rw [← zero_smul ℂ (0 : 𝒱), anmBalance_smul_left]; simp

theorem anmBalance_zero_mid (u v : 𝒱) : anmBalance W p n m u 0 v = 0 := by
  rw [← zero_smul ℂ (0 : 𝒱), anmBalance_smul_mid]; simp

theorem anmBalance_zero_right (u a : 𝒱) : anmBalance W p n m u a 0 = 0 := by
  rw [← zero_smul ℂ (0 : 𝒱), anmBalance_smul_right]; simp

/-! ## The balancing-membership targets (Props, NOT axioms). -/

/-- **The balancing-membership target** `AnmBalanceCore W p n m`: the DJ composition-balancing defect
lies in `O_{p,m}(𝒱)` for ALL `u, a, v` (DJ Prop. 3.4).  Equivalent to `AnmComposeBalanced` (see
`anmComposeBalanced_of_core`). -/
def AnmBalanceCore : Prop := ∀ u a v : 𝒱, anmBalance W p n m u a v ∈ Onm W p m

/-- **The homogeneous balancing-membership target** `AnmBalanceHom W p n m`: the balancing defect
lies in `O_{p,m}(𝒱)` for HOMOGENEOUS `u ∈ 𝒱ₚ', a ∈ 𝒱_q', v ∈ 𝒱ᵣ'`.  This is the depth-`(p,n,m)`
analogue of the `(0,0,0)` Zhu associator membership.  The remaining combinatorial content (the
depth-mixing FZ scalar cores). -/
def AnmBalanceHom : Prop :=
  ∀ (P Q R : ℤ), ∀ u ∈ W.grading P, ∀ a ∈ W.grading Q, ∀ v ∈ W.grading R,
    anmBalance W p n m u a v ∈ Onm W p m

/-! ## Trilinear homogeneity reduction: `AnmBalanceHom ⟹ AnmBalanceCore`. -/

/-- Reduce the right (`v`) slot of `AnmBalanceCore` to homogeneous `v`, given homogeneous `u, a`. -/
theorem AnmBalanceCore_right_of_hom (hH : AnmBalanceHom W p n m) {P Q : ℤ} {u a : 𝒱}
    (hu : u ∈ W.grading P) (ha : a ∈ W.grading Q) (v : 𝒱) :
    anmBalance W p n m u a v ∈ Onm W p m := by
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => anmBalance W p n m u a v ∈ Onm W p m) hvtop ?_ ?_ ?_
  · intro R v hv
    exact hH P Q R u hu a ha v hv
  · change anmBalance W p n m u a 0 ∈ Onm W p m
    rw [anmBalance_zero_right]; exact (Onm W p m).zero_mem
  · intro v₁ v₂ h₁ h₂
    change anmBalance W p n m u a (v₁ + v₂) ∈ Onm W p m
    rw [anmBalance_add_right]; exact (Onm W p m).add_mem h₁ h₂

/-- Reduce the middle (`a`) slot to homogeneous `a`, given homogeneous `u`. -/
theorem AnmBalanceCore_mid_of_hom (hH : AnmBalanceHom W p n m) {P : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading P) (a v : 𝒱) :
    anmBalance W p n m u a v ∈ Onm W p m := by
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => ∀ v : 𝒱, anmBalance W p n m u a v ∈ Onm W p m) hatop ?_ ?_ ?_ v
  · intro Q a ha v
    exact AnmBalanceCore_right_of_hom W p n m hH hu ha v
  · intro v
    change anmBalance W p n m u 0 v ∈ Onm W p m
    rw [anmBalance_zero_mid]; exact (Onm W p m).zero_mem
  · intro a₁ a₂ h₁ h₂ v
    change anmBalance W p n m u (a₁ + a₂) v ∈ Onm W p m
    rw [anmBalance_add_mid]; exact (Onm W p m).add_mem (h₁ v) (h₂ v)

/-- **The trilinear homogeneity reduction**: the homogeneous balancing membership `AnmBalanceHom`
implies the full balancing membership `AnmBalanceCore`.  (Three nested `iSup_induction`s over the
internal grading `W.isInternal`, using slotwise trilinearity and submodule closure of `O_{p,m}` —
the exact mirror of `AnFull.assocCore_of_homogeneous`.) -/
theorem AnmBalanceCore_of_homogeneous (hH : AnmBalanceHom W p n m) : AnmBalanceCore W p n m := by
  intro u a v
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => ∀ a v : 𝒱, anmBalance W p n m u a v ∈ Onm W p m) hutop ?_ ?_ ?_ a v
  · intro P u hu a v
    exact AnmBalanceCore_mid_of_hom W p n m hH hu a v
  · intro a v
    change anmBalance W p n m 0 a v ∈ Onm W p m
    rw [anmBalance_zero_left]; exact (Onm W p m).zero_mem
  · intro u₁ u₂ h₁ h₂ a v
    change anmBalance W p n m (u₁ + u₂) a v ∈ Onm W p m
    rw [anmBalance_add_left]; exact (Onm W p m).add_mem (h₁ a v) (h₂ a v)

/-! ## The balancing membership discharges `AnmComposeBalanced`. -/

/-- **The bridge `AnmBalanceCore ⟹ AnmComposeBalanced`.**  If the DJ composition-balancing defect
lies in `O_{p,m}(𝒱)` for all `u, a, v`, then the descended composition map is balanced over
`A_n(𝒱)` — i.e. it factors through `A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱)` (DJ Prop. 3.4).  Proof: the
balancing in `Anm W p m` is the equality of the two `mkAnm` classes, i.e. their difference in
`O_{p,m}`, which is exactly `AnmBalanceCore`. -/
theorem anmComposeBalanced_of_core (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m)
    (hcore : AnmBalanceCore W p n m) :
    AnmComposeBalanced W p n m hL hR := by
  refine AnmComposeBalanced_of_repr W p n m hL hR ?_
  intro u a v
  -- `mkAnm W p m = (Onm W p m).mkQ`; two classes are equal iff their difference ∈ `Onm W p m`.
  have hmem : anmCompose W p n m (anmRight W p n u a) v
      - anmCompose W p n m u (anmRight W n m a v) ∈ Onm W p m := by
    have h := hcore u a v; rwa [anmBalance_eq] at h
  exact (Submodule.Quotient.eq (Onm W p m)).mpr hmem

/-- **The end-to-end chain `AnmBalanceHom ⟹ AnmComposeBalanced`**: discharging the homogeneous
balancing core (the depth-`(p,n,m)` FZ scalar cores) flips the `A_n(𝒱)`-balancing of the Dong–Jiang
composition with zero extra wiring. -/
theorem anmComposeBalanced_of_homogeneous (hL : AnmComposeDescL W p n m)
    (hR : AnmComposeDescR W p n m) (hH : AnmBalanceHom W p n m) :
    AnmComposeBalanced W p n m hL hR :=
  anmComposeBalanced_of_core W p n m hL hR (AnmBalanceCore_of_homogeneous W p n m hH)

/-! ## The `n = m = p = 0` Zhu-bottom balancing — residue form.

At the bottom `(p,n,m) = (0,0,0)` all three residue products are the Zhu product `zhuMul`
(`anmRight_zero_zero`), so the balancing defect is exactly the **Zhu associator**
`(u·a)·v − u·(a·v)`.  Its membership in the target ideal `Onm W 0 0` (`= OnFull W 0 = O(𝒱)`, the
diagonal bridge `Onm_diag_eq_OnFull` at `n = 0`) is proved unconditionally below
(`anmBalanceCore_zero`) via the proved level-`0` FZ associativity. -/

/-- At `(p,n,m) = (0,0,0)` the balancing defect is the Zhu associator
`(u·a)·v − u·(a·v)`. -/
theorem anmBalance_zero_zero_zero (W : VertexOperatorAlgebra 𝒱) (u a v : 𝒱) :
    anmBalance W 0 0 0 u a v
      = zhuMul W (zhuMul W u a) v - zhuMul W u (zhuMul W a v) := by
  unfold anmBalance
  rw [anmRight_zero_zero, anmRight_zero_zero, anmRight_zero_zero, anmRight_zero_zero]

/-! ## The DIAGONAL bridge `(p,n,m) = (n,n,n)`: balancing **is** `A_n(𝒱)` associativity.

At the diagonal the Dong–Jiang composition `anmCompose W n n n = anmRight W n n` coincides with the
Frenkel–Zhu `A_n(𝒱)` product `leftProd W n`, and the target ideal `Onm W n n` coincides with the
corrected `OnFull W n`.  Hence the balancing defect `anmBalance W n n n` is exactly the FZ associator
`AnFull.assoc W n`, and `AnmBalanceCore W n n n ⟺ AnFull.assocCore W n`.  This **unifies** the two
`A_n(𝒱)`-algebra cores: the diagonal Dong–Jiang composition-balancing is the depth-`n` FZ
associativity, so the diagonal balancing inherits the proved level-`0` associativity. -/

section Diagonal

variable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)

/-- **`circ W n = resHom W n (2n+2)`** — the FZ circle product is the generic residue at shift `n`,
pole `2n+2` (the families `circFamily W n` and `resFamily W n (2n+2)` are equal:
`i − 2n − 2 = i − (2n+2)`). -/
theorem circ_eq_resHom (a b : 𝒱) : circ W n a b = resHom W n (2 * (n : ℤ) + 2) a b := by
  have hfam : circFamily W n b = resFamily W n (2 * (n : ℤ) + 2) b := by
    funext k
    refine LinearMap.ext fun ak => ?_
    show (∑ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
          cbz (k + (n : ℤ)) i • W.smul (ak : 𝒱) ((i : ℤ) - 2 * (n : ℤ) - 2) b)
        = ∑ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
          cbz (k + (n : ℤ)) i • W.smul (ak : 𝒱) ((i : ℤ) - (2 * (n : ℤ) + 2)) b
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (i : ℤ) - 2 * (n : ℤ) - 2 = (i : ℤ) - (2 * (n : ℤ) + 2) from by ring]
  show (DFinsupp.lsum ℂ (circFamily W n b)) _
      = (DFinsupp.lsum ℂ (resFamily W n (2 * (n : ℤ) + 2) b)) _
  rw [hfam]

/-- **`anmCirc W n n = circ W n`** — at the diagonal `m = n` the Dong–Jiang circle generator is the
FZ circle product (both are `resHom W n (2n+2)`). -/
theorem anmCirc_diag_eq_circ (a b : 𝒱) : anmCirc W n n a b = circ W n a b := by
  rw [anmCirc, circ_eq_resHom,
    show (n : ℤ) + (n : ℤ) + 2 = 2 * (n : ℤ) + 2 from by ring]

/-- **`leftProd W n = anmRight W n n`** — at the diagonal `m = n` the Frenkel–Zhu `A_n(𝒱)` product
is the Dong–Jiang right action.  Both are the same alternating residue tower; the only difference is
the binomial argument (`cbz (j+n) n` vs `cbz (n+j) j`), reconciled by `cbz_symm`
(`C(j+n, n) = C(j+n, j)`). -/
theorem leftProd_eq_anmRight_diag (a b : 𝒱) :
    leftProd W n a b = anmRight W n n a b := by
  rw [leftProd, anmRight]
  refine Finset.sum_congr rfl fun j hj => ?_
  -- the residue factor `resHom W n (n+j+1)` is identical on both sides; reconcile only the scalar
  -- coefficient `(-1)^j * cbz (j+n) n = (-1)^j * cbz (n+j) j` via `cbz_symm` (`C(j+n,n)=C(j+n,j)`).
  have hcbz : cbz ((j : ℤ) + (n : ℤ)) (n : ℤ) = cbz ((n : ℤ) + (j : ℤ)) (j : ℤ) := by
    rw [show ((j : ℤ) + (n : ℤ)) = (((j + n : ℕ)) : ℤ) from by push_cast; ring,
        ZhuMu.cbz_symm (j + n) (n : ℤ),
        show (((j + n : ℕ)) : ℤ) - (n : ℤ) = (j : ℤ) from by push_cast; ring,
        show (((j + n : ℕ)) : ℤ) = (n : ℤ) + (j : ℤ) from by push_cast; ring]
  rw [hcbz]

/-- **`OnmL W n n = OnL W`** — at the diagonal the Dong–Jiang grading generators are exactly Zhu's
`(L₋₁ + L₀)`-generators (`anmLgen W n n u = L₋₁ u + L₀ u`). -/
theorem OnmL_diag_eq_OnL : OnmL W n n = OnL W := by
  unfold OnmL OnL
  congr 1
  ext x
  constructor
  · rintro ⟨u, rfl⟩; exact ⟨u, (anmLgen_diag W n u)⟩
  · rintro ⟨u, rfl⟩; exact ⟨u, (anmLgen_diag W n u).symm⟩

/-- **`Onm W n n = OnFull W n`** — at the diagonal the (partial) Dong–Jiang ideal `O'_{n,n}` is the
corrected FZ ideal `OnFull W n = On W n ⊔ OnL W` (DJ Prop. 4.6 `A_{n,n}(𝒱) = A_n(𝒱)`).  The circle
spans agree (`anmCirc W n n = circ W n`) and the grading spans agree (`OnmL W n n = OnL W`). -/
theorem Onm_diag_eq_OnFull : Onm W n n = OnFull W n := by
  rw [Onm, OnFull, OnmL_diag_eq_OnL, On]
  congr 2
  ext x
  constructor
  · rintro ⟨u, v, rfl⟩; exact ⟨u, v, (anmCirc_diag_eq_circ W n u v)⟩
  · rintro ⟨u, v, rfl⟩; exact ⟨u, v, (anmCirc_diag_eq_circ W n u v).symm⟩

/-- **The diagonal balancing defect is the FZ associator**: `anmBalance W n n n a b c =
AnFull.assoc W n a b c`.  (Both products are `leftProd W n = anmRight W n n`.) -/
theorem anmBalance_diag_eq_assoc (a b c : 𝒱) :
    anmBalance W n n n a b c = AnFull.assoc W n a b c := by
  rw [anmBalance, AnFull.assoc, leftProd_eq_anmRight_diag, leftProd_eq_anmRight_diag,
    leftProd_eq_anmRight_diag, leftProd_eq_anmRight_diag]

/-- **The diagonal balancing core is `A_n(𝒱)` associativity**: `AnmBalanceCore W n n n ⟺
AnFull.assocCore W n`.  (Pointwise, the membership `anmBalance ∈ Onm W n n` equals
`AnFull.assoc ∈ OnFull W n` via `anmBalance_diag_eq_assoc` and `Onm_diag_eq_OnFull`.) -/
theorem AnmBalanceCore_diag_iff_assocCore :
    AnmBalanceCore W n n n ↔ AnFull.assocCore W n := by
  unfold AnmBalanceCore AnFull.assocCore
  constructor
  · intro h a b c
    have := h a b c
    rwa [anmBalance_diag_eq_assoc, Onm_diag_eq_OnFull] at this
  · intro h u a v
    have := h u a v
    rwa [← anmBalance_diag_eq_assoc, ← Onm_diag_eq_OnFull] at this

/-- **The diagonal balancing follows from the depth-`n` FZ associator** `AnFull.AssocHom W n`:
discharging the FZ associator core flips the diagonal Dong–Jiang composition-balancing
`AnmBalanceCore W n n n` (hence `AnmComposeBalanced W n n n`) with zero extra wiring. -/
theorem AnmBalanceCore_diag_of_assocHom (hH : AnFull.AssocHom W n) :
    AnmBalanceCore W n n n :=
  (AnmBalanceCore_diag_iff_assocCore W n).mpr (AnFull.assocCore_of_homogeneous W n hH)

end Diagonal

/-! ## The `(0,0,0)` balancing — proved unconditionally (via the proved level-`0` associativity).

At `(0,0,0)` the diagonal bridge gives `AnmBalanceCore W 0 0 0 ⟺ AnFull.assocCore W 0`, and
`AnFull.assocCore W 0` is the proved Zhu associativity (`AnFull.assocCore_zero`).  Hence the bottom
Dong–Jiang composition-balancing is unconditionally true, anchoring the depth-`(p,n,m)` balancing
induction. -/

/-- **`AnmBalanceCore W 0 0 0`** — the Zhu-bottom Dong–Jiang composition-balancing, proved
unconditionally via the proved level-`0` FZ associativity `AnFull.assocCore_zero`. -/
theorem anmBalanceCore_zero (W : VertexOperatorAlgebra 𝒱) : AnmBalanceCore W 0 0 0 :=
  (AnmBalanceCore_diag_iff_assocCore W 0).mpr (AnFull.assocCore_zero W)

/-- **`AnmComposeBalanced W 0 0 0`** — the descended `A_0(𝒱)`-balancing of the Dong–Jiang
composition at the bottom, proved unconditionally (given the two bottom descents `hL`, `hR`). -/
theorem anmComposeBalanced_zero (W : VertexOperatorAlgebra 𝒱)
    (hL : AnmComposeDescL W 0 0 0) (hR : AnmComposeDescR W 0 0 0) :
    AnmComposeBalanced W 0 0 0 hL hR :=
  anmComposeBalanced_of_core W 0 0 0 hL hR (anmBalanceCore_zero W)

/-! ## `A_n(𝒱)` associativity (Part 2): the named depth-`n` entry points and the residue form.

The reduction `AnFull.AssocHom W n ⟹ AnFull.AssocLaw W n` is already proved
(`ZhuVermaAnArchAssoc`/`AssocCore`).  We re-export the named depth-`n` associativity entry point and
record the residue-product form of the FZ associator, isolating the remaining content as the
depth-`n` analogue of Zhu's `assoc_eq` scalar cores (`ZhuMu.mu_identity` / `ZhuUCore.u_core` /
`ZhuVCore.v_core`). -/

/-- **The FZ associator in residue form**: `AnFull.assoc W n a b c =
anmRight W n n (anmRight W n n a b) c − anmRight W n n a (anmRight W n n b c)` — the depth-`n`
double-tower of higher-pole residues `resHom W n (n+·+1)`.  This is the precise object whose
membership in `OnFull W n` (`= Onm W n n`) is the remaining `AnFull.AssocHom W n` content. -/
theorem AnFull_assoc_eq_residue (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b c : 𝒱) :
    AnFull.assoc W n a b c
      = anmRight W n n (anmRight W n n a b) c - anmRight W n n a (anmRight W n n b c) := by
  rw [← anmBalance_diag_eq_assoc, anmBalance]

/-- **Named depth-`n` associativity entry point**: a proof of the homogeneous FZ associator
membership `AnFull.AssocHom W n` discharges the full quotient associativity `AnFull.AssocLaw W n`
(re-export of `AnFull.assocLaw_of_assocHom`; a future depth-`n` core flips `A_n(𝒱)` associativity
unconditionally). -/
theorem AnFull_assocLaw_of_assocHom (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hH : AnFull.AssocHom W n) :
    AnFull.AssocLaw W n (anIdeal_holds W n) :=
  AnFull.assocLaw_of_assocHom W n hH

end VOA

/-
## Status

**Axiom-clean (`[propext, Classical.choice, Quot.sound]`; engine-verified TRUE on the
rank-1 free boson, `certificates/mathematica/balanced_fast.wl`):**

PART 1 — the Dong–Jiang composition `A_n(𝒱)`-balancing:
* `anmBalance` + slotwise trilinearity — the balancing-defect vector.
* `AnmBalanceCore` / `AnmBalanceHom` — the residue-membership target and its homogeneous form.
* `AnmBalanceCore_of_homogeneous` — the trilinear homogeneity reduction (three `iSup_induction`s).
* `anmComposeBalanced_of_core` / `anmComposeBalanced_of_homogeneous` — the bridge to
  `AnmComposeBalanced` (DJ Prop. 3.4 factoring through `⊗_{A_n(𝒱)}`).

DIAGONAL bridge (unifies Part 1 + Part 2):
* `circ_eq_resHom`, `anmCirc_diag_eq_circ`, `leftProd_eq_anmRight_diag`, `OnmL_diag_eq_OnL`,
  `Onm_diag_eq_OnFull` — `anmCompose W n n n = leftProd W n` and `Onm W n n = OnFull W n`.
* `anmBalance_diag_eq_assoc`, `AnmBalanceCore_diag_iff_assocCore` — the diagonal balancing **is**
  `A_n(𝒱)` associativity.
* `anmBalanceCore_zero`, `anmComposeBalanced_zero` — the `(0,0,0)` balancing proved unconditionally
  via the proved level-`0` FZ associativity `AnFull.assocCore_zero`.

PART 2 — `A_n(𝒱)` associativity:
* `AnFull_assoc_eq_residue` — the residue-product form of the FZ associator.
* `AnFull_assocLaw_of_assocHom` — the named depth-`n` entry point (`AssocHom W n ⟹ AssocLaw W n`).

**OPEN (stated precisely; NOT `sorry`, NOT axioms):**
* `AnmBalanceHom W p n m` for general `(p,n,m)` with `m ≥ 1` and/or `p ≥ 1` — the depth-mixing FZ
  associator combinatorics (DJ Prop. 3.4); same depth-`n` scalar-core content as `AnFull.AssocHom`.
* `AnFull.AssocHom W n` for `n ≥ 1` — the depth-`n` FZ associator (unchanged upstream open target).

`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmComposeBalanced_of_core
  #print axioms VOA.AnmBalanceCore_of_homogeneous
  #print axioms VOA.anmComposeBalanced_of_homogeneous
  #print axioms VOA.leftProd_eq_anmRight_diag
  #print axioms VOA.Onm_diag_eq_OnFull
  #print axioms VOA.AnmBalanceCore_diag_iff_assocCore
  #print axioms VOA.anmBalanceCore_zero
  #print axioms VOA.anmComposeBalanced_zero
  #print axioms VOA.AnFull_assoc_eq_residue
  #print axioms VOA.AnFull_assocLaw_of_assocHom
-/
