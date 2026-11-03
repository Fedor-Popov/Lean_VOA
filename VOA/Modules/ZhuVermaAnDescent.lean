/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnBimodule

/-!
# The descent of the FZ products to `A_n(𝒱)` (`O_n(𝒱)` is a sub-bimodule)

Building on the tower foundation (`Modules.ZhuVermaAn`: `circ`/`On`/`An`) and the `V`-level FZ
products (`Modules.ZhuVermaAnBimodule`: `leftProd`/`rightProd`/`resHom`), this file proves that
`O_n(𝒱)` is a sub-`A(𝒱)`-bimodule, so the products descend to bilinear maps
`A(𝒱) × A_n(𝒱) → A_n(𝒱)` and `A_n(𝒱) × A(𝒱) → A_n(𝒱)`.

## The keystone `Pres_mem_On` (depth-`n` higher-pole residue membership)

The principal technical input is the `O_n`-analog of `Modules.ZhuModule.Pres_mem_O`: the FZ
higher-pole residue tower carrying the extra `(1+z)^{+n}/z^{+2n}` weighting still lands in
`O_n(𝒱)`.  Concretely, for homogeneous `a ∈ 𝒱_M`, define the **depth-`(n,d)` residue**

  `PresOn a M n d b := ∑_{i=0}^{M+n+d} C(M+n+d, i) · a₍ᵢ₋₂ₙ₋₂₋d₎ b`
                    `  (= Res_z Y(a,z)b (1+z)^{M+n+d}/z^{2n+2+d})`.

At `d = 0` this is exactly the circle product `circ W n a b` (`PresOn_zero`, ∈ `On W n` by
`circ_mem_On`).  The integration-by-parts recursion `(d+2n+2)·PresOn(d+1) = PresOn_{L₋₁a}(d) +
(M+n+d+1)·PresOn(d)` (the *same* Pascal/upper-absorption step as `Pres_mem_O`, since the binomial
top `M+n+d` and pole `2n+2+d` move together) then gives `PresOn … ∈ O_n W` for all `d` by
induction (`Pres_mem_On`).  This is the `O_n`-analog of Frenkel–Zhu Lemma 2.1.2, the deep step.

## Status

* **`Pres_mem_On` keystone proved, axiom-clean** (`[propext, Classical.choice, Quot.sound]`).
* The `span_le`/`comap` **descent reductions** `leftProd_On_of_gen`/`rightProd_On_of_gen` (reduce
the right-slot memberships to circle generators).  The **descended bimodule actions**
`An.lAct : A(𝒱) →ₗ A_n(𝒱) →ₗ A_n(𝒱)` and `An.rAct : A_n(𝒱) →ₗ A(𝒱) →ₗ A_n(𝒱)`, parametric in the
bundled membership hypotheses `LeftDescends`/`RightDescends` (each is exactly the corresponding
`*_mem_On` statement — propositions about the *existing* products, NOT new axioms), with their
representative-level reduction lemmas and the **`n = 0` anchor** (`An.lAct_zero_mk`/`An.rAct_zero_mk`:
the bottom rung agrees with the Zhu product `[a]·[x] = [a*x]`).

**Not proved here.** The **four circle-generator memberships** themselves (`LeftDescends`/`RightDescends`) are left as
PRECISE stated targets at the file end (NOT `sorry`, NOT axiomatized): they are the `A_n`-analog of
Zhu's two-sided-ideal theorem (Zhu Thm 2.1.1, `ZhuHR.right_ideal_core`), reduced via the keystone
`Pres_mem_On` + the depth-`n` generalization of the binomial identity `ZhuRes.zhu_right_binom`.

## References
* Gannon §5.3.2, Thm 5.3.4; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The depth-`(n,d)` higher-pole residue and its keystone membership in `O_n(𝒱)`. -/

/-- The depth-`(n,d)` FZ residue `∑_i C(M+n+d, i) · a₍ᵢ₋₂ₙ₋₂₋d₎ b`
(`= Res_z Y(a,z)b (1+z)^{M+n+d}/z^{2n+2+d}`).  At `d = 0` it is `circ W n a b` for `a ∈ 𝒱_M`. -/
noncomputable def PresOn (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (a b : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + d + 1),
    cbz ((M : ℤ) + n + d) (i : ℤ) • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 2 - d) b

/-- The per-outer-index scalar identity driving the recursion (upper absorption, same as
`pres_coeff_identity` with top/pole both shifted by `2n`):
`(d+2n+2)·C(M+n+d+1,i) = C(M+n+d+1,i)·(-(i-2n-2-d)) + (M+n+d+1)·C(M+n+d,i-1)`. -/
theorem presOn_coeff_identity (M n d : ℕ) (i : ℤ) :
    ((d : ℂ) + 2 * n + 2) * cbz ((M : ℤ) + n + d + 1) i
      = cbz ((M : ℤ) + n + d + 1) i * (-((i : ℂ) - 2 * n - 2 - d))
        + ((M : ℂ) + n + d + 1) * cbz ((M : ℤ) + n + d) (i - 1) := by
  have hua := cbz_upper_absorption (M + n + d + 1) i
  rw [show ((((M + n + d + 1 : ℕ)) : ℤ) - 1) = (M : ℤ) + n + d from by push_cast; ring,
      show (((M + n + d + 1 : ℕ)) : ℤ) = (M : ℤ) + n + d + 1 from by push_cast; ring] at hua
  push_cast at hua ⊢
  linear_combination hua

/-- At `d = 0` the residue is the `n`-th circle product `circ W n a b` (for `a ∈ 𝒱_M`). -/
theorem PresOn_zero (W : VertexOperatorAlgebra 𝒱) {M n : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) : PresOn W M n 0 a b = circ W n a b := by
  rw [circ_homogeneous W n ha b, PresOn,
    show (((M : ℤ) + (n : ℤ)).toNat + 1) = M + n + 0 + 1 from by
      rw [show ((M : ℤ) + (n : ℤ)) = ((M + n : ℕ) : ℤ) from by push_cast; ring,
        Int.toNat_natCast]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((M : ℤ) + (n : ℤ) + (0 : ℕ)) = (M : ℤ) + (n : ℤ) from by push_cast; ring,
    show ((i : ℤ) - 2 * (n : ℤ) - 2 - (0 : ℕ)) = (i : ℤ) - 2 * (n : ℤ) - 2 from by push_cast; ring]

/-- **The keystone `(★ₙ)`: depth-`(n,d)` higher-pole residue membership** (Frenkel–Zhu Lemma 2.1.2,
`O_n`-form): for homogeneous `a ∈ 𝒱_M` and all `d`, `PresOn W M n d a b ∈ O_n(𝒱)`.

Proved by induction on `d`: the base `d = 0` is `circ W n a b ∈ O_n` (`circ_mem_On`); the step uses
the integration-by-parts recursion `(d+2n+2)·PresOn(d+1) = PresOn_{L₋₁a}(d) + (M+n+d+1)·PresOn(d)`
(both summands in `O_n` by the IH applied to `L₋₁a ∈ 𝒱_{M+1}` and to `a`). -/
theorem Pres_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) (d : ℕ) : PresOn W M n d a b ∈ On W n := by
  induction d generalizing M a with
  | zero =>
    rw [PresOn_zero W ha b]; exact circ_mem_On W n a b
  | succ d ih =>
    have haL : W.L (-1) a ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W ha
    -- IH for L₋₁a at level M+1:
    have hG : PresOn W (M + 1) n d (W.L (-1) a) b ∈ On W n := by
      have := ih (M := M + 1) (a := W.L (-1) a) (by
        rwa [show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 from by push_cast; ring])
      exact this
    have hP : PresOn W M n d a b ∈ On W n := ih ha
    -- Express G_d with (L₋₁a)₍·₎ expanded to a₍·₎ via smul_L_neg_one, on range(M+n+d+2).
    have hGeq : PresOn W (M + 1) n d (W.L (-1) a) b
        = ∑ i ∈ Finset.range (M + n + d + 2),
            (cbz ((M : ℤ) + n + d + 1) (i : ℤ) * (-((i : ℂ) - 2 * n - 2 - d)))
              • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 3 - d) b := by
      unfold PresOn
      rw [show M + 1 + n + d + 1 = M + n + d + 2 from by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcast1 : (((M + 1 : ℕ) : ℤ)) + (n : ℤ) + (d : ℤ) = (M : ℤ) + n + d + 1 := by
        push_cast; ring
      rw [hcast1, smul_L_neg_one W a b ((i : ℤ) - 2 * (n : ℤ) - 2 - d),
        show ((i : ℤ) - 2 * (n : ℤ) - 2 - d - 1) = (i : ℤ) - 2 * (n : ℤ) - 3 - d from by ring,
        ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - 2 * (n : ℤ) - 2 - d))
          (W.smul a ((i : ℤ) - 2 * (n : ℤ) - 3 - d) b), smul_smul]
      congr 2
      push_cast
      ring
    -- The cleared sum identity over range(M+n+d+2), inner mode a₍ᵢ₋₂ₙ₋₃₋d₎b.
    have hsum : ((d : ℂ) + 2 * n + 2) • PresOn W M n (d + 1) a b
        = PresOn W (M + 1) n d (W.L (-1) a) b
          + ((M : ℂ) + n + d + 1) • PresOn W M n d a b := by
      rw [hGeq]
      have hLHS : ((d : ℂ) + 2 * n + 2) • PresOn W M n (d + 1) a b
          = ∑ i ∈ Finset.range (M + n + d + 2),
              (((d : ℂ) + 2 * n + 2) * cbz ((M : ℤ) + n + (d + 1)) (i : ℤ))
                • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 2 - (d + 1)) b := by
        unfold PresOn
        rw [show M + n + (d + 1) + 1 = M + n + d + 2 from by ring, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
        congr 2 <;> push_cast <;> ring
      have hPn : ((M : ℂ) + n + d + 1) • PresOn W M n d a b
          = ∑ i ∈ Finset.range (M + n + d + 2),
              (((M : ℂ) + n + d + 1) * cbz ((M : ℤ) + n + d) ((i : ℤ) - 1))
                • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 3 - d) b := by
        unfold PresOn
        rw [Finset.smul_sum]
        rw [Finset.sum_range_succ' (fun i => (((M : ℂ) + n + d + 1) * cbz ((M : ℤ) + n + d) ((i : ℤ) - 1))
            • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 3 - d) b) (M + n + d + 1)]
        rw [show cbz ((M : ℤ) + n + d) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
          mul_zero, zero_smul, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul]
        congr 2
        · push_cast; ring_nf
        · push_cast; ring_nf
      rw [hLHS, hPn, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmode : ((i : ℤ) - 2 * (n : ℤ) - 2 - ((d : ℤ) + 1)) = (i : ℤ) - 2 * (n : ℤ) - 3 - d := by
        push_cast; ring
      rw [show ((M : ℤ) + n + ((d : ℤ) + 1)) = (M : ℤ) + n + d + 1 from by push_cast; ring, hmode,
        ← add_smul]
      congr 1
      have := presOn_coeff_identity M n d (i : ℤ)
      push_cast at this ⊢
      linear_combination this
    -- conclude: PresOn(d+1) = (1/(d+2n+2))•RHS ∈ O_n.
    have hne : ((d : ℂ) + 2 * n + 2) ≠ 0 := by
      have : ((d : ℂ) + 2 * n + 2) = ((d + 2 * n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.succ_ne_zero (d + 2 * n + 1)
    have : PresOn W M n (d + 1) a b
        = (((d : ℂ) + 2 * n + 2)⁻¹)
          • (PresOn W (M + 1) n d (W.L (-1) a) b + ((M : ℂ) + n + d + 1) • PresOn W M n d a b) := by
      rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hG (Submodule.smul_mem _ _ hP))

/-! ## Linear-map wrappers and the `span_le` reduction principles for the descent. -/

/-- Right multiplication `x ↦ a *ₙ x` (`leftProd W n a ·`) as a `ℂ`-linear map. -/
noncomputable def leftProdR (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun x := leftProd W n a x
  map_add' := leftProd_add_right W n a
  map_smul' c x := leftProd_smul_right W n c a x

/-- Left multiplication `x ↦ x *ₙ a` (`rightProd W n · a`) as a `ℂ`-linear map (linear in the `A_n`
factor `x`). -/
noncomputable def rightProdL (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun x := rightProd W n x a
  map_add' x₁ x₂ := rightProd_add_left W n x₁ x₂ a
  map_smul' c x := rightProd_smul_left W n c x a

/-- Right multiplication `a ↦ x *ₙ a` (`rightProd W n x ·`) as a `ℂ`-linear map (linear in the
`A(𝒱)` factor `a`). -/
noncomputable def rightProdR (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun a := rightProd W n x a
  map_add' a₁ a₂ := rightProd_add_right W n x a₁ a₂
  map_smul' c a := rightProd_smul_right W n c x a

@[simp] theorem leftProdR_apply (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a x : 𝒱) :
    leftProdR W n a x = leftProd W n a x := rfl

@[simp] theorem rightProdL_apply (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a x : 𝒱) :
    rightProdL W n a x = rightProd W n x a := rfl

@[simp] theorem rightProdR_apply (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x a : 𝒱) :
    rightProdR W n x a = rightProd W n x a := rfl

/-- `O_n(𝒱)` as the span of the circle generators (definitional unfold). -/
theorem On_eq_span (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    On W n = Submodule.span ℂ {x | ∃ a b : 𝒱, x = circ W n a b} := rfl

/-- **Left-slot reduction:** if `a *ₙ (c ∘ₙ d) ∈ O_n` for every circle generator `c ∘ₙ d`, then
`a *ₙ x ∈ O_n` for all `x ∈ O_n` (`leftProd W n a ·` is linear, so `comap`/`span_le`). -/
theorem leftProd_On_of_gen (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱)
    (hgen : ∀ c d : 𝒱, leftProd W n a (circ W n c d) ∈ On W n) :
    ∀ x ∈ On W n, leftProd W n a x ∈ On W n := by
  intro x hx
  have hle : On W n ≤ (On W n).comap (leftProdR W n a) := by
    rw [On_eq_span, Submodule.span_le]
    rintro g ⟨c, d, rfl⟩
    simpa [Submodule.mem_comap] using hgen c d
  have : x ∈ (On W n).comap (leftProdR W n a) := hle hx
  simpa [Submodule.mem_comap] using this

/-- **Right-slot reduction:** if `(c ∘ₙ d) *ₙ a ∈ O_n` for every circle generator `c ∘ₙ d`, then
`x *ₙ a ∈ O_n` for all `x ∈ O_n` (`rightProd W n · a` is linear). -/
theorem rightProd_On_of_gen (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱)
    (hgen : ∀ c d : 𝒱, rightProd W n (circ W n c d) a ∈ On W n) :
    ∀ x ∈ On W n, rightProd W n x a ∈ On W n := by
  intro x hx
  have hle : On W n ≤ (On W n).comap (rightProdL W n a) := by
    rw [On_eq_span, Submodule.span_le]
    rintro g ⟨c, d, rfl⟩
    simpa [Submodule.mem_comap] using hgen c d
  have : x ∈ (On W n).comap (rightProdL W n a) := hle hx
  simpa [Submodule.mem_comap] using this

/-! ## The descended `A(𝒱)`-bimodule actions on `A_n(𝒱)`.

Once the four descent memberships hold, both FZ products descend to bilinear maps on the quotients.
We package the memberships as the bundled hypotheses below (each is exactly the corresponding
`*_mem_On` target), so these actions are genuine, immediately-usable defs.  The hypotheses are
*propositions about the existing `leftProd`/`rightProd`*, NOT new axioms; discharging them (via the
keystone `Pres_mem_On` + the depth-`n` generalization of `ZhuHR.right_ideal_core`) makes the actions
unconditional.

The left action `A(𝒱) × A_n(𝒱) → A_n(𝒱)`, `([a], [x]) ↦ [a *ₙ x]`, is built by descending the
second slot of `leftProd` through `A_n = 𝒱/O_n` (needs the `on_mem` half) and then the first slot
through `A(𝒱) = 𝒱/O` (needs the `gen_mem` half, i.e. `O(𝒱) *ₙ 𝒱 ⊆ O_n`). -/

variable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)

/-- The bundled left-slot/right-slot well-definedness hypotheses for the left FZ product:
`O(𝒱) *ₙ 𝒱 ⊆ O_n` and `𝒱 *ₙ O_n ⊆ O_n`. -/
structure LeftDescends : Prop where
  /-- `O(𝒱) *ₙ 𝒱 ⊆ O_n`: a left factor in `O(𝒱)` lands in `O_n`. -/
  gen_mem : ∀ g ∈ O W, ∀ b : 𝒱, leftProd W n g b ∈ On W n
  /-- `𝒱 *ₙ O_n ⊆ O_n`: a right factor in `O_n` lands in `O_n`. -/
  on_mem : ∀ a : 𝒱, ∀ x ∈ On W n, leftProd W n a x ∈ On W n

/-- The bundled well-definedness hypotheses for the right FZ product:
`O_n *ₙ 𝒱 ⊆ O_n` and `𝒱 *ₙ O(𝒱) ⊆ O_n`. -/
structure RightDescends : Prop where
  /-- `O_n *ₙ 𝒱 ⊆ O_n`: a left factor in `O_n` lands in `O_n`. -/
  on_mem : ∀ x ∈ On W n, ∀ a : 𝒱, rightProd W n x a ∈ On W n
  /-- `𝒱 *ₙ O(𝒱) ⊆ O_n` (right slot in `O(𝒱)`): a right factor in `O(𝒱)` lands in `O_n`. -/
  gen_mem : ∀ x : 𝒱, ∀ g ∈ O W, rightProd W n x g ∈ On W n

/-- For fixed `a`, the right-slot descent `[x] ↦ [a *ₙ x]` as `A_n →ₗ A_n` (needs `h.on_mem`). -/
noncomputable def An.lActAux (h : LeftDescends W n) (a : 𝒱) : An W n →ₗ[ℂ] An W n :=
  (On W n).mapQ (On W n) (leftProdR W n a) (by
    intro x hx
    rw [Submodule.mem_comap, leftProdR_apply]
    exact h.on_mem a x hx)

@[simp] theorem An.lActAux_mk (h : LeftDescends W n) (a x : 𝒱) :
    An.lActAux W n h a (mkAn W n x) = mkAn W n (leftProd W n a x) := rfl

/-- `a ↦ An.lActAux a` bundled as a linear map `𝒱 →ₗ (A_n →ₗ A_n)` (linear in `a`). -/
noncomputable def An.lActHom (h : LeftDescends W n) : 𝒱 →ₗ[ℂ] An W n →ₗ[ℂ] An W n where
  toFun := An.lActAux W n h
  map_add' a₁ a₂ := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    simp only [LinearMap.add_apply]
    rw [show (Submodule.Quotient.mk x : An W n) = mkAn W n x from rfl,
      An.lActAux_mk, An.lActAux_mk, An.lActAux_mk, leftProd_add_left, map_add]
  map_smul' c a := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [show (Submodule.Quotient.mk x : An W n) = mkAn W n x from rfl,
      An.lActAux_mk, An.lActAux_mk, leftProd_smul_left, map_smul]

@[simp] theorem An.lActHom_apply (h : LeftDescends W n) (a x : 𝒱) :
    An.lActHom W n h a (mkAn W n x) = mkAn W n (leftProd W n a x) :=
  An.lActAux_mk W n h a x

/-- **The descended left action** `A(𝒱) →ₗ A_n(𝒱) →ₗ A_n(𝒱)`, `([a], [x]) ↦ [a *ₙ x]`
(Frenkel–Zhu).  Descends the `A_n` (right) slot via `h.on_mem`, then the `A(𝒱)` (left) slot via
`h.gen_mem` (`O(𝒱) ≤ ker`). -/
noncomputable def An.lAct (h : LeftDescends W n) : A W →ₗ[ℂ] An W n →ₗ[ℂ] An W n :=
  (O W).liftQ (An.lActHom W n h) (by
    intro g hg
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    show An.lActHom W n h g (mkAn W n x) = (0 : An W n →ₗ[ℂ] An W n) (mkAn W n x)
    rw [An.lActHom_apply, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero (On W n)).mpr (h.gen_mem g hg x))

/-- The descended left action on representatives: `[a] · [x] = [a *ₙ x]`. -/
@[simp] theorem An.lAct_mk (h : LeftDescends W n) (a x : 𝒱) :
    An.lAct W n h (mk W a) (mkAn W n x) = mkAn W n (leftProd W n a x) :=
  An.lActAux_mk W n h a x

/-- For fixed `x`, the right-slot descent `[a] ↦ [x *ₙ a]` as `A(𝒱) →ₗ A_n` (needs `h.gen_mem`). -/
noncomputable def An.rActAux (h : RightDescends W n) (x : 𝒱) : A W →ₗ[ℂ] An W n :=
  (O W).liftQ ((mkAn W n).comp (rightProdR W n x)) (by
    intro g hg
    rw [LinearMap.mem_ker, LinearMap.comp_apply, rightProdR_apply, mkAn, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h.gen_mem x g hg))

@[simp] theorem An.rActAux_mk (h : RightDescends W n) (x a : 𝒱) :
    An.rActAux W n h x (mk W a) = mkAn W n (rightProd W n x a) := rfl

/-- `x ↦ An.rActAux x` bundled as a linear map `𝒱 →ₗ (A(𝒱) →ₗ A_n)` (linear in `x`). -/
noncomputable def An.rActHom (h : RightDescends W n) : 𝒱 →ₗ[ℂ] A W →ₗ[ℂ] An W n where
  toFun := An.rActAux W n h
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun a => ?_
    simp only [LinearMap.add_apply]
    rw [show (Submodule.Quotient.mk a : A W) = mk W a from rfl,
      An.rActAux_mk, An.rActAux_mk, An.rActAux_mk, rightProd_add_left, map_add]
  map_smul' c x := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun a => ?_
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [show (Submodule.Quotient.mk a : A W) = mk W a from rfl,
      An.rActAux_mk, An.rActAux_mk, rightProd_smul_left, map_smul]

@[simp] theorem An.rActHom_apply (h : RightDescends W n) (x a : 𝒱) :
    An.rActHom W n h x (mk W a) = mkAn W n (rightProd W n x a) :=
  An.rActAux_mk W n h x a

/-- **The descended right action** `A_n(𝒱) →ₗ A(𝒱) →ₗ A_n(𝒱)`, `([x], [a]) ↦ [x *ₙ a]`
(Frenkel–Zhu).  Descends the `A(𝒱)` (right) slot via `h.gen_mem`, then the `A_n` (left) slot via
`h.on_mem` (`O_n ≤ ker`). -/
noncomputable def An.rAct (h : RightDescends W n) : An W n →ₗ[ℂ] A W →ₗ[ℂ] An W n :=
  (On W n).liftQ (An.rActHom W n h) (by
    intro x hx
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun a => ?_
    show An.rActHom W n h x (mk W a) = (0 : A W →ₗ[ℂ] An W n) (mk W a)
    rw [An.rActHom_apply, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero (On W n)).mpr (h.on_mem x hx a))

/-- The descended right action on representatives: `[x] · [a] = [x *ₙ a]`. -/
@[simp] theorem An.rAct_mk (h : RightDescends W n) (x a : 𝒱) :
    An.rAct W n h (mkAn W n x) (mk W a) = mkAn W n (rightProd W n x a) :=
  An.rActAux_mk W n h x a

/-! ## The `n = 0` correctness anchor: the descended actions reduce to Zhu multiplication.

`A_0(𝒱) = 𝒱/O_0(𝒱)` is the bottom of the FZ tower; at `n = 0` both FZ products are the Zhu product
(`leftProd_zero`/`rightProd_zero`).  So on representatives both descended actions agree with the
descent of the Zhu product `[a] · [x] = [a * x]`, pinning the construction to the existing Zhu ring
multiplication on `A(𝒱)` (`ZhuRingInstance`) at the bottom rung. -/

/-- **`n = 0` anchor (left):** the descended left action on representatives is the Zhu product
`[a] · [x] = [a * x]ₙ₌₀` (`leftProd W 0 = zhuMul`). -/
@[simp] theorem An.lAct_zero_mk (h : LeftDescends W 0) (a x : 𝒱) :
    An.lAct W 0 h (mk W a) (mkAn W 0 x) = mkAn W 0 (zhuMul W a x) := by
  rw [An.lAct_mk, leftProd_zero]

/-- **`n = 0` anchor (right):** the descended right action on representatives is the Zhu product
`[x] · [a] = [x * a]ₙ₌₀` (`rightProd W 0 = zhuMul`). -/
@[simp] theorem An.rAct_zero_mk (h : RightDescends W 0) (x a : 𝒱) :
    An.rAct W 0 h (mkAn W 0 x) (mk W a) = mkAn W 0 (zhuMul W x a) := by
  rw [An.rAct_mk, rightProd_zero]

/-!
## 2b — the four descent memberships: PRECISE remaining targets (NOT `sorry`)

The descended actions above are unconditional once the bundled hypotheses `LeftDescends W n` /
`RightDescends W n` are discharged.  Each unfolds (via `leftProd_On_of_gen`/`rightProd_On_of_gen`
and the `O`-span reduction `O_eq_span`) to the following four circle-generator memberships, the
`A_n`-analog of Zhu's two-sided-ideal theorem (Zhu Thm 2.1.1, `ZhuHR.right_ideal_core`):

* **Right-slot (`A_n` argument), `leftProd_On_mem_On`** : `∀ c d a, leftProd W n a (circ W n c d) ∈
  On W n`.  *Reduction:* for homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, expand via `leftProd_homogeneous`
  + `circ_homogeneous`, `mode_split` (`ZhuHR.mode_split`) each `a₍α₎(c₍β₎d)` into the `c`-first
  term (a circle product `∈ On`) plus the commutator term; expand the commutator via
  `ZhuHR.mode_commutator_uniform`, reindex to the mode value, and collapse the `(j,i,p)`-sum (via the
  depth-`n` generalization of the binomial identity `ZhuRes.zhu_right_binom`, carrying the extra
  `(1+z)^n/z^{2n}` weighting) into `PresOn`-towers based at `w := a₍ₛ₎c ∈ 𝒱_{K+M-s-1}`, each
  `∈ On W n` by the keystone **`Pres_mem_On`**.

* **Right-slot (`A_n` argument), `rightProd_On_mem_On`** : `∀ c d a, rightProd W n (circ W n c d) a ∈
  On W n` (same reduction with the right-product coefficients `C(j+n,j)`, shift `s = j`).

* **Left-slot (`A(𝒱)` argument), `leftProd_gen_mem_On`** : for a generator
  `g = (L₋₁u + L₀u) * v ∈ O(𝒱)`, `∀ b, leftProd W n g b ∈ On W n`, i.e. `O(𝒱) *ₙ 𝒱 ⊆ O_n`.

* **Left-slot (`A(𝒱)` argument), `rightProd_gen_mem_On`** : `∀ x, rightProd W n x g ∈ On W n` for
  `g ∈ O(𝒱)` a generator, i.e. `𝒱 *ₙ O(𝒱) ⊆ O_n`.

Packaging the four into `LeftDescends`/`RightDescends` then yields the descended bimodule actions
`An.lAct`/`An.rAct` unconditionally.  The keystone `Pres_mem_On` (the deep higher-pole residue
membership) is already proved; the remaining work is the binomial bookkeeping generalizing
`ZhuHR.right_ideal_core` to depth `n`. -/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.circ_homogeneous
  #print axioms VOA.PresOn
  #print axioms VOA.presOn_coeff_identity
  #print axioms VOA.PresOn_zero
  #print axioms VOA.Pres_mem_On
  #print axioms VOA.leftProd_On_of_gen
  #print axioms VOA.rightProd_On_of_gen
  #print axioms VOA.An.lAct
  #print axioms VOA.An.rAct
  #print axioms VOA.An.lAct_mk
  #print axioms VOA.An.rAct_mk
  #print axioms VOA.An.lAct_zero_mk
  #print axioms VOA.An.rAct_zero_mk
-/
