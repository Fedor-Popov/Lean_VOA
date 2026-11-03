/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVirasoro

/-!
# Background charge on the general even-lattice VOA — the vertex-operator route

The **linear-dilaton / Feigin–Fuks deformation** of the lattice conformal vector.  Fix a background
charge `λ` (a vector of the ambient `ℝ^{rank L}`, given by its coordinates in the orthonormal frame
that `LatGen.chargeOsc` uses).  The deformed conformal vector is the **state**

  `ω_λ  =  ω  +  λ(-2)|0⟩`      (`omegaBG`)

and this file follows the vertex-operator side: it identifies `Y(ω_λ, z)` as
`T(z) + ∂_z λ(z)` (`YfullGen_omegaBG`), reads off the deformed modes

  `L^λ_n  =  L_n  −  (n+1)·λ(n)`   (`LBG`, `mode_YfullGen_omegaBG`)

and proves the Virasoro relation with

  `c  =  rank L  −  12⟨λ,λ⟩`      (`LBG_virasoro`).

## The sign convention

The sign is pinned by the **weight of the charged vacua**.  `L^λ_0 e^β = (½⟨β,β⟩ − ⟨λ,β⟩) e^β`
(`LBG_zero_latChargeGen`), so for the triplet lattice `⟨α,α⟩ = 2p`, `λ = (p−1)/(2p)·α` one gets
`⟨λ,α⟩ = p−1` and hence

  `wt(e^{α}) = p − (p−1) = 1`,      `wt(e^{−α}) = p + (p−1) = 2p−1`,

which is the demanded normalization (the scalar arithmetic is `bgWeight_triplet`, which mentions no
VOA).  Note `c` is even in `λ`, so the sign
convention is invisible in the central charge and only visible in the weights.

## Structure of the argument (the "vertex-operator route")

1. `omegaBG = ω + ∑ₐ λₐ · (aᵃ(-2)|0⟩ ⊗ e⁰)` is an explicit **state** of `LatModuleGen L`, a
   `ℂ`-combination of `wordStateLatGen` word states (`bgState_eq_mkEα` displays it as `λ(-2)|0⟩`).
2. `YfullGen` is `ℂ`-**linear**, and its value on those word states is already known
   (`YfullGen_word`, `YfullGen_omega_eq`), so `Y(ω_λ,z) = T(z) + ∂_z λ(z)` needs no new
   reconstruction — only `nprod_eq_left_of_right_one`, the fact that the normal-ordered product
   with the unit field `Y(e⁰,z) = 1` is the identity (`Yeαvec_zero_eq_one`).
3. Taking modes turns `∂_z` into the factor `−(n+1)` and gives `L^λ_n = L_n − (n+1)λ(n)`.
4. The Virasoro relation is assembled from the **already proved** `LLGen_comm_tmul`
   (`c = rank L`) plus the two cross brackets `[L_m, λ(n)] = −n λ(m+n)` and
   `[λ(m), λ(n)] = m δ_{m+n,0} ⟨λ,λ⟩`.  The `−12⟨λ,λ⟩` is exactly the `(m+1)(n+1)m` term at
   `n = −m`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.BgB

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction
open VOA.LatGen

variable (L : IntegralLattice)

/-! ## §0  The background charge and its oscillators

A background charge is recorded by its **orthonormal-frame coordinates** `lam : Fin (rank L) → ℂ`,
exactly the way `LatGen.chargeOsc` records a lattice charge through `chargeCoord`.  This is strictly
more general than a lattice vector: the interesting `λ`s (`(p−1)/(2p)·α` for the triplet) are
rational, not integral, points of `L ⊗ ℚ`. -/

/-- The background-charge oscillator `λ(m) = ∑ₐ λₐ aᵃ(m)` on the boson factor. -/
noncomputable def bgOsc (lam : Fin (rank L) → ℂ) (m : ℤ) : End ℂ (FockN (rank L)) :=
  ∑ a : Fin (rank L), lam a • oscN (rank L) 1 a m

theorem bgOsc_apply (lam : Fin (rank L) → ℂ) (m : ℤ) (y : FockN (rank L)) :
    bgOsc L lam m y = ∑ a : Fin (rank L), lam a • oscN (rank L) 1 a m y := by
  rw [bgOsc, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- The zero mode of `λ(z)` vanishes on the boson factor (the momentum lives on the charge
factor, see `bgMode_mkEα`). -/
theorem bgOsc_zero_mode (lam : Fin (rank L) → ℂ) : bgOsc L lam 0 = 0 := by
  rw [bgOsc]
  exact Finset.sum_eq_zero fun a _ => by rw [oscN_zero, smul_zero]

/-- A lattice charge is the special case `lam = chargeCoord α`. -/
theorem chargeOsc_eq_bgOsc (α : L.carrier) (m : ℤ) :
    chargeOsc L α m = bgOsc L (chargeCoord L α) m := rfl

/-- The euclidean pairing of two background charges, `⟨λ,μ⟩ = ∑ₐ λₐ μₐ`. -/
noncomputable def bgInner (lam mu : Fin (rank L) → ℂ) : ℂ := ∑ a : Fin (rank L), lam a * mu a

theorem bgInner_comm (lam mu : Fin (rank L) → ℂ) : bgInner L lam mu = bgInner L mu lam :=
  Finset.sum_congr rfl fun a _ => mul_comm (lam a) (mu a)

/-- The pairing of a background charge with a lattice vector, `⟨λ,β⟩`. -/
noncomputable def bgPair (lam : Fin (rank L) → ℂ) (β : L.carrier) : ℂ :=
  bgInner L lam (chargeCoord L β)

/-- `⟨λ,β⟩` computed from the lattice side agrees with `bgInner`. -/
theorem bgPair_eq (lam : Fin (rank L) → ℂ) (β : L.carrier) :
    bgPair L lam β = ∑ a : Fin (rank L), lam a * chargeCoord L β a := rfl

/-- **The Heisenberg bracket of two background-charge oscillators**:
`[λ(m), μ(n)] = ⟨λ,μ⟩ · m · δ_{m+n,0}`.  (Generalizes `LatGen.chargeOsc_comm` off the lattice; the
frame is orthonormal so no `PosDef` hypothesis is needed here.) -/
theorem bgOsc_comm (lam mu : Fin (rank L) → ℂ) (m n : ℤ) :
    bgOsc L lam m * bgOsc L mu n - bgOsc L mu n * bgOsc L lam m
      = (if m + n = 0 then bgInner L lam mu * (m : ℂ) else 0) • LinearMap.id := by
  have e1 : bgOsc L lam m * bgOsc L mu n
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          (lam a * mu b) • (oscN (rank L) 1 a m * oscN (rank L) 1 b n) := by
    simp only [bgOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have e2 : bgOsc L mu n * bgOsc L lam m
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          (lam a * mu b) • (oscN (rank L) 1 b n * oscN (rank L) 1 a m) := by
    simp only [bgOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [mul_comm (mu b) (lam a)]
  have hexpand : bgOsc L lam m * bgOsc L mu n - bgOsc L mu n * bgOsc L lam m
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          (lam a * mu b) • (oscN (rank L) 1 a m * oscN (rank L) 1 b n
            - oscN (rank L) 1 b n * oscN (rank L) 1 a m) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_sub]
  have hbr : ∀ a b : Fin (rank L),
      oscN (rank L) 1 a m * oscN (rank L) 1 b n - oscN (rank L) 1 b n * oscN (rank L) 1 a m
        = (if a = b ∧ m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
    intro a b
    rw [oscN_comm (rank L) 1 a b m n, mul_one]
  rw [hexpand]
  simp only [hbr, smul_smul]
  by_cases hP : m + n = 0
  · rw [if_pos hP]
    simp only [← Finset.sum_smul]
    congr 1
    have hb : ∀ a : Fin (rank L),
        (∑ b : Fin (rank L), (lam a * mu b) * (if a = b ∧ m + n = 0 then (m : ℂ) else 0))
          = (lam a * mu a) * (m : ℂ) := by
      intro a
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
          (fun h => absurd (Finset.mem_univ a) h)]
      simp [hP]
    simp only [hb]
    rw [← Finset.sum_mul]
    rfl
  · rw [if_neg hP, zero_smul]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    simp [hP]

/-- **`[Lₘ, λ(n)] = −n·λ(m+n)`** in vector form (the boson-Virasoro / background-charge bracket).
Generalizes `LatGen.LvirN_chargeOsc` from a lattice charge to an arbitrary background charge. -/
theorem LvirN_bgOsc (lam : Fin (rank L) → ℂ) (m n : ℤ) (y : FockN (rank L)) :
    LvirN (rank L) 1 m (bgOsc L lam n y)
      = (-(n : ℂ)) • bgOsc L lam (m + n) y + bgOsc L lam n (LvirN (rank L) 1 m y) := by
  rw [bgOsc_apply, map_sum,
    Finset.sum_congr rfl (fun a _ => by
      rw [map_smul, LvirN_oscN (rank L) 1 one_ne_zero a m n y, smul_add,
        smul_comm (lam a) (-(n : ℂ))]),
    Finset.sum_add_distrib, ← Finset.smul_sum, ← bgOsc_apply, ← bgOsc_apply]

/-! ## §A  The background-charge current on `V_L`, its modes, and the Fock-side avatars -/

/-- The **background-charge current** `λ(z) = ∑ₐ λₐ α^a(z)` on `V_L` (the lattice-momentum zero
mode included, since `alphaLatGen` carries it at index `-1`). -/
noncomputable def bgCurrent (lam : Fin (rank L) → ℂ) : FormalDist (End ℂ (LatModuleGen L)) :=
  ∑ a : Fin (rank L), lam a • alphaLatGen L a

theorem bgCurrent_apply (lam : Fin (rank L) → ℂ) (j : ℤ) :
    bgCurrent L lam j = ∑ a : Fin (rank L), lam a • alphaLatGen L a j :=
  Finset.sum_apply (s := Finset.univ) (g := fun a : Fin (rank L) => lam a • alphaLatGen L a) j

/-- The mode `λ(n) = mode (λ(z)) n` as an operator on `V_L`. -/
noncomputable def bgMode (lam : Fin (rank L) → ℂ) (n : ℤ) : End ℂ (LatModuleGen L) :=
  mode (bgCurrent L lam) n

theorem bgMode_eq_sum (lam : Fin (rank L) → ℂ) (n : ℤ) :
    bgMode L lam n = ∑ a : Fin (rank L), lam a • mode (alphaLatGen L a) n := by
  rw [bgMode, mode_apply, bgCurrent_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- The **Fock-side avatar of `λ(n)` in the charge sector `γ`**: the boson oscillator plus the
lattice momentum `⟨λ,γ⟩` at `n = 0`. -/
noncomputable def bgFock (lam : Fin (rank L) → ℂ) (γ : L.carrier) (n : ℤ) :
    End ℂ (FockN (rank L)) :=
  bgOsc L lam n + (if n = 0 then bgPair L lam γ else 0) • LinearMap.id

/-- The **Fock-side avatar of the lattice Virasoro mode `Lₘ` in the charge sector `γ`**
(repackaging `LatGen.LLGen_tmul`). -/
noncomputable def LFock (γ : L.carrier) (m : ℤ) : End ℂ (FockN (rank L)) :=
  LvirN (rank L) 1 m + chargeOsc L γ m
    + (if m = 0 then (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ) else 0) • LinearMap.id

theorem latStateGen_eq_mkEα (q : FockN (rank L)) (γ : L.carrier) :
    latStateGen L q γ = mkEα L γ q := rfl

/-- **Extensionality on the charged basis states**: two operators on `V_L` agreeing on every
`q ⊗ e^γ` are equal.  (The `TensorProduct`/`Finsupp` induction used throughout
`LatticeGenVirasoro`, factored out.) -/
theorem latExt {f g : End ℂ (LatModuleGen L)}
    (h : ∀ (q : FockN (rank L)) (γ : L.carrier),
      f (mkEα L γ q) = g (mkEα L γ q)) : f = g := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 hy1 hy2 => rw [map_add, map_add, hy1, hy2]
  | tmul q x =>
      induction x using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero, map_zero]
      | add x1 x2 h1 h2 => erw [TensorProduct.tmul_add]; rw [map_add, map_add, h1, h2]
      | single c b =>
          rw [(Finsupp.smul_single_one c b).symm,
            show (Finsupp.single c 1 : L.carrier →₀ ℂ) = eGen L c from rfl]
          erw [TensorProduct.tmul_smul]
          rw [map_smul, map_smul, show q ⊗ₜ[ℂ] eGen L c = mkEα L c q from rfl, h]

/-- `Lₘ` on a charged basis state is its Fock-side avatar. -/
theorem LLGen_mkEα (hPos : L.PosDef) (m : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    LLGen L m (mkEα L γ q) = mkEα L γ (LFock L γ m q) := by
  change LLGen L m (latStateGen L q γ) = mkEα L γ (LFock L γ m q)
  rw [LLGen_tmul L hPos, LFock]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    latStateGen_eq_mkEα, map_add, map_smul]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, zero_smul]

/-- The mode `α^a_n` on a charged basis state. -/
theorem mode_alphaLatGen_mkEα (a : Fin (rank L)) (n : ℤ) (q : FockN (rank L))
    (γ : L.carrier) :
    mode (alphaLatGen L a) n (mkEα L γ q)
      = mkEα L γ (oscN (rank L) 1 a n q)
        + (if n = 0 then chargeCoord L γ a else 0) • mkEα L γ q := by
  rw [mode_apply, alphaLatGen_apply, LinearMap.add_apply]
  congr 1
  · rw [mkEα_apply, LinearMap.rTensor_tmul, currentN_apply,
      show -(-n - 1) - 1 = n from by ring, mkEα_apply]
  · by_cases hn : n = 0
    · rw [if_pos (show (-n - 1 : ℤ) = -1 from by omega), if_pos hn,
        show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen]
    · rw [if_neg (show ¬((-n - 1 : ℤ) = -1) from by omega), if_neg hn, LinearMap.zero_apply,
        zero_smul]

/-- **`λ(n)` on a charged basis state is its Fock-side avatar `bgFock`.** -/
theorem bgMode_mkEα (lam : Fin (rank L) → ℂ) (n : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    bgMode L lam n (mkEα L γ q) = mkEα L γ (bgFock L lam γ n q) := by
  rw [bgMode_eq_sum, LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl (fun a _ => by
      rw [LinearMap.smul_apply, mode_alphaLatGen_mkEα, smul_add, smul_smul]),
    Finset.sum_add_distrib, bgFock]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_add, map_smul]
  congr 1
  · rw [bgOsc_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ =>
      (map_smul (mkEα L γ) (lam a) ((oscN (rank L) 1 a n) q)).symm
  · rw [← Finset.sum_smul]
    congr 1
    by_cases hn : n = 0
    · rw [if_pos hn, bgPair_eq]
      exact Finset.sum_congr rfl fun a _ => by rw [if_pos hn]
    · rw [if_neg hn, Finset.sum_eq_zero fun a _ => by rw [if_neg hn, mul_zero]]

/-! ## §B  The three brackets, as operator identities on `V_L` -/

/-- Scalars are central: adding scalar multiples of the identity changes no commutator. -/
theorem comm_add_smul_id {V : Type*} [AddCommGroup V] [Module ℂ V] (A B : End ℂ V) (c d : ℂ) :
    (A + c • LinearMap.id) * (B + d • LinearMap.id)
        - (B + d • LinearMap.id) * (A + c • LinearMap.id)
      = A * B - B * A := by
  simp only [show (LinearMap.id : End ℂ V) = 1 from rfl, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, mul_one, one_mul, smul_add, smul_smul, mul_comm c d]
  abel

/-- `[λ(m), μ(n)]` on the Fock side, momentum included: the momentum is central, so the answer is
the pure oscillator bracket `⟨λ,μ⟩ · m · δ_{m+n,0}`. -/
theorem bgFock_comm (lam mu : Fin (rank L) → ℂ) (γ : L.carrier) (m n : ℤ) :
    bgFock L lam γ m * bgFock L mu γ n - bgFock L mu γ n * bgFock L lam γ m
      = (if m + n = 0 then bgInner L lam mu * (m : ℂ) else 0) • LinearMap.id := by
  rw [bgFock, bgFock, comm_add_smul_id, bgOsc_comm]

/-- The operator form of `LvirN_bgOsc`. -/
theorem LvirN_bgOsc_comm (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    LvirN (rank L) 1 m * bgOsc L lam n - bgOsc L lam n * LvirN (rank L) 1 m
      = (-(n : ℂ)) • bgOsc L lam (m + n) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LvirN_bgOsc]
  abel

/-- **`[Lₘ, λ(n)] = −n λ(m+n)` on the Fock side** (charge sector `γ`).  The `⟨λ,γ⟩` produced by the
charge oscillator at `m+n = 0` is exactly the momentum piece of `−n λ(m+n)` — this is the
compatibility that makes the deformation work uniformly in the charge sector. -/
theorem LFock_bgFock_comm (lam : Fin (rank L) → ℂ) (γ : L.carrier) (m n : ℤ) :
    LFock L γ m * bgFock L lam γ n - bgFock L lam γ n * LFock L γ m
      = (-(n : ℂ)) • bgFock L lam γ (m + n) := by
  rw [LFock, bgFock, show LvirN (rank L) 1 m + chargeOsc L γ m
      + (if m = 0 then (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ) else 0) • LinearMap.id
      = (LvirN (rank L) 1 m + chargeOsc L γ m)
        + (if m = 0 then (1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ) else 0) • LinearMap.id from rfl,
    comm_add_smul_id, add_mul, mul_add,
    show LvirN (rank L) 1 m * bgOsc L lam n + chargeOsc L γ m * bgOsc L lam n
        - (bgOsc L lam n * LvirN (rank L) 1 m + bgOsc L lam n * chargeOsc L γ m)
      = (LvirN (rank L) 1 m * bgOsc L lam n - bgOsc L lam n * LvirN (rank L) 1 m)
        + (chargeOsc L γ m * bgOsc L lam n - bgOsc L lam n * chargeOsc L γ m) from by abel,
    LvirN_bgOsc_comm, chargeOsc_eq_bgOsc, bgOsc_comm, bgFock, smul_add, smul_smul]
  congr 2
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, bgInner_comm]
    have hn : (n : ℂ) = -(m : ℂ) := by
      have : n = -m := by omega
      rw [this]; push_cast; ring
    rw [hn, bgPair]
    ring
  · rw [if_neg hmn, if_neg hmn, mul_zero]

/-- **`[Lₘ, Lₙ]` as an operator identity** (the operator form of `LatGen.LLGen_comm_tmul`,
i.e. of `LatGen.YfullGen_virasoro`), central charge `rank L`. -/
theorem LLGen_comm_op (hPos : L.PosDef) (m n : ℤ) :
    LLGen L m * LLGen L n - LLGen L n * LLGen L m
      = ((m : ℂ) - n) • LLGen L (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ) else 0)
            • (1 : End ℂ (LatModuleGen L)) := by
  have h := latExt L (f := LLGen L m * LLGen L n - LLGen L n * LLGen L m)
    (g := ((m : ℂ) - n) • LLGen L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ))
            • (1 : End ℂ (LatModuleGen L)) else 0))
    (fun q γ => LLGen_comm_tmul L hPos m n q γ)
  rw [h]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
  · rw [if_neg hmn, if_neg hmn, zero_smul]

/-- **`[Lₘ, λ(n)] = −n λ(m+n)` on `V_L`.** -/
theorem LLGen_bgMode_comm (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    LLGen L m * bgMode L lam n - bgMode L lam n * LLGen L m
      = (-(n : ℂ)) • bgMode L lam (m + n) := by
  refine latExt L fun q γ => ?_
  have h := congrArg (fun T : End ℂ (FockN (rank L)) => T q) (LFock_bgFock_comm L lam γ m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
  simp only [bgMode_mkEα, LLGen_mkEα L hPos]
  rw [← map_sub, ← map_smul]
  exact congrArg (mkEα L γ) h

/-- **`[λ(m), μ(n)] = ⟨λ,μ⟩ m δ_{m+n,0}` on `V_L`.** -/
theorem bgMode_comm (lam mu : Fin (rank L) → ℂ) (m n : ℤ) :
    bgMode L lam m * bgMode L mu n - bgMode L mu n * bgMode L lam m
      = (if m + n = 0 then bgInner L lam mu * (m : ℂ) else 0) • (1 : End ℂ (LatModuleGen L)) := by
  refine latExt L fun q γ => ?_
  have h := congrArg (fun T : End ℂ (FockN (rank L)) => T q) (bgFock_comm L lam mu γ m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  simp only [bgMode_mkEα]
  rw [← map_sub, ← map_smul]
  exact congrArg (mkEα L γ) h

/-! ## §C  The deformed conformal vector `ω_λ`, its field, and its modes -/

/-- The normal-ordered product with the **unit field** on the right is the identity:
`:a(z)·1: = a(z)`.  (This is the only new field-theoretic input the route needs.) -/
theorem nprod_eq_left_of_right_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) (hb1 : b = 1) :
    nprod ha hb = a := by
  funext s
  refine LinearMap.ext fun x => ?_
  rw [nprod_apply,
    finsum_eq_single (fun m : ℤ => normalOrdered a b m (s - m) x) s (fun m hm => by
      change normalOrdered a b m (s - m) x = 0
      rw [normalOrdered_apply, hb1, FormalDist.one_apply,
        if_neg (show ¬ (s - m = 0) from fun h => hm (by omega))]
      by_cases h0 : 0 ≤ m
      · rw [if_pos h0, Module.End.mul_apply, LinearMap.zero_apply, map_zero]
      · rw [if_neg h0, Module.End.mul_apply, LinearMap.zero_apply])]
  change normalOrdered a b s (s - s) x = a s x
  rw [normalOrdered_apply, hb1, FormalDist.one_apply, if_pos (show s - s = 0 from by ring)]
  by_cases h0 : 0 ≤ s
  · rw [if_pos h0, mul_one]
  · rw [if_neg h0, one_mul]

/-- **`Y(aᵃ(-2)|0⟩, z) = ∂_z α^a(z)`**: the one-letter word field is the derivative of the
current, because the word field is `:∂α^a(z) · Y(e⁰,z):` and `Y(e⁰,z) = 1`. -/
theorem YwordLatGen_single (a : Fin (rank L)) :
    YwordLatGen L [(1, a)] 0 = VOA.deriv (alphaLatGen L a) := by
  rw [YwordLatGen_cons,
    nprod_eq_left_of_right_one (genFieldLatGen_isField L a 1) (YwordLatGen_isField L [] 0)
      (by rw [YwordLatGen_nil]; exact Yeαvec_zero_eq_one L),
    genFieldLatGen]
  simp

/-- The state `λ(-2)|0⟩ ⊗ e⁰`, written as a `ℂ`-combination of one-letter word states. -/
noncomputable def bgState (lam : Fin (rank L) → ℂ) : LatModuleGen L :=
  ∑ a : Fin (rank L), lam a • wordStateLatGen L [(1, a)] 0

/-- `bgState` really is the state `λ(-2)|0⟩` of the charge-`0` sector. -/
theorem bgState_eq_mkEα (lam : Fin (rank L) → ℂ) :
    bgState L lam = mkEα L 0 (bgOsc L lam (-2) (vacuumN (rank L))) := by
  rw [bgState, bgOsc_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  congr 1

/-- **The background-charge conformal vector** `ω_λ = ω + λ(-2)|0⟩`. -/
noncomputable def omegaBG (lam : Fin (rank L) → ℂ) : LatModuleGen L :=
  omegaLatGen L + bgState L lam

/-- **`Y(ω_λ, z) = T(z) + ∂_z λ(z)`** — the vertex-operator side of the deformation, obtained
from `ℂ`-linearity of `YfullGen` alone. -/
theorem YfullGen_omegaBG (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) :
    YfullGen L hEven hPos (omegaBG L lam)
      = sugFieldGen L + VOA.deriv (bgCurrent L lam) := by
  rw [omegaBG, map_add, YfullGen_omega_eq, bgState, map_sum, bgCurrent, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, YfullGen_word, YwordLatGen_single, map_smul]

/-- The **deformed Virasoro modes** `L^λ_n = Lₙ − (n+1)·λ(n)`. -/
noncomputable def LBG (lam : Fin (rank L) → ℂ) (n : ℤ) : End ℂ (LatModuleGen L) :=
  LLGen L n - ((n : ℂ) + 1) • bgMode L lam n

theorem mode_sugFieldGen (n : ℤ) : mode (sugFieldGen L) (n + 1) = LLGen L n := by
  rw [mode_apply, LLGen, show -(n + 1) - 1 = -n - 2 from by ring]

/-- Taking modes turns `∂_z` into the factor `−j`: `mode (∂_z f) j = −j · mode f (j−1)`. -/
theorem mode_deriv (f : FormalDist (End ℂ (LatModuleGen L))) (j : ℤ) :
    mode (VOA.deriv f) j = (-(j : ℂ)) • mode f (j - 1) := by
  change (VOA.deriv f) (-j - 1) = (-(j : ℂ)) • f (-(j - 1) - 1)
  rw [deriv_apply, show -j - 1 + 1 = -j from by ring, show -(j - 1) - 1 = -j from by ring,
    show (-(j : ℂ)) = (((-j : ℤ)) : ℂ) from by push_cast; ring,
    Int.cast_smul_eq_zsmul]

/-- **The deformed modes read off the deformed field**: `mode (Y(ω_λ,z)) (n+1) = L^λ_n`. -/
theorem mode_YfullGen_omegaBG (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (n : ℤ) :
    mode (YfullGen L hEven hPos (omegaBG L lam)) (n + 1) = LBG L lam n := by
  rw [YfullGen_omegaBG L hEven hPos, mode_add, mode_sugFieldGen, mode_deriv,
    show n + 1 - 1 = n from by ring, LBG, ← bgMode]
  push_cast
  module

/-! ## §D  The Virasoro relation, `c = rank L − 12⟨λ,λ⟩` -/

/-- The **background-charge central charge** `c_λ = rank L − 12⟨λ,λ⟩`. -/
noncomputable def bgCentralCharge (lam : Fin (rank L) → ℂ) : ℂ :=
  (rank L : ℂ) - 12 * bgInner L lam lam

/-- **The background-charge Virasoro relation** on the general even-lattice VOA:
`[L^λ_m, L^λ_n] = (m−n)L^λ_{m+n} + δ_{m+n,0}·(m³−m)/12·(rank L − 12⟨λ,λ⟩)`.

The `rank L` comes from the already-proved Sugawara relation `LLGen_comm_op`; the `−12⟨λ,λ⟩` is the
`(m+1)(n+1)·m·⟨λ,λ⟩` term of the current–current bracket evaluated at `n = −m`, where
`(m+1)(1−m)m = −(m³−m)`.  The two cross brackets `[L_m, λ(n)] = −n λ(m+n)` conspire to reproduce
exactly the `−(m−n)(m+n+1)λ(m+n)` needed by `(m−n)L^λ_{m+n}`. -/
theorem LBG_virasoro (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    LBG L lam m * LBG L lam n - LBG L lam n * LBG L lam m
      = ((m : ℂ) - n) • LBG L lam (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * bgCentralCharge L lam else 0)
            • (1 : End ℂ (LatModuleGen L)) := by
  have hexpand : LBG L lam m * LBG L lam n - LBG L lam n * LBG L lam m
      = (LLGen L m * LLGen L n - LLGen L n * LLGen L m)
        - ((n : ℂ) + 1) • (LLGen L m * bgMode L lam n - bgMode L lam n * LLGen L m)
        - ((m : ℂ) + 1) • (bgMode L lam m * LLGen L n - LLGen L n * bgMode L lam m)
        + (((m : ℂ) + 1) * ((n : ℂ) + 1))
            • (bgMode L lam m * bgMode L lam n - bgMode L lam n * bgMode L lam m) := by
    simp only [LBG, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    module
  have hcross : bgMode L lam m * LLGen L n - LLGen L n * bgMode L lam m
      = ((m : ℂ)) • bgMode L lam (m + n) := by
    have h := LLGen_bgMode_comm L hPos lam n m
    rw [add_comm n m] at h
    rw [← neg_sub, h]
    module
  rw [hexpand, LLGen_comm_op L hPos, LLGen_bgMode_comm L hPos, hcross, bgMode_comm,
    LBG, bgCentralCharge]
  by_cases hmn : m + n = 0
  · obtain rfl : n = -m := by omega
    have h0 : m + -m = (0 : ℤ) := by ring
    rw [if_pos h0, if_pos h0, if_pos h0, h0]
    push_cast
    module
  · simp only [if_neg hmn]
    push_cast
    module

/-- **VOA1 shape** for the deformed conformal vector: the Virasoro relation written for
`mode (Y(ω_λ,z))`, matching `LatGen.YfullGen_virasoro`. -/
theorem YfullGen_omegaBG_virasoro (hEven : L.Even) (hPos : L.PosDef)
    (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    ⁅mode (YfullGen L hEven hPos (omegaBG L lam)) (m + 1),
      mode (YfullGen L hEven hPos (omegaBG L lam)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YfullGen L hEven hPos (omegaBG L lam)) (m + n + 1)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * bgCentralCharge L lam else 0)
            • (1 : End ℂ (LatModuleGen L)) := by
  rw [mode_YfullGen_omegaBG, mode_YfullGen_omegaBG,
    show m + n + 1 = (m + n) + 1 from by ring, mode_YfullGen_omegaBG,
    LieRing.of_associative_ring_bracket]
  exact LBG_virasoro L hPos lam m n

/-! ## §E  The deformed weights — the sign convention -/

/-- **`L^λ_0 e^β = (½⟨β,β⟩ − ⟨λ,β⟩) e^β`** — the deformed conformal weight of a charged vacuum.
This is the statement that pins the sign in `ω_λ = ω + λ(-2)|0⟩`. -/
theorem LBG_zero_latChargeGen (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (β : L.carrier) :
    LBG L lam 0 (latChargeGen L β)
      = ((1 / 2 : ℂ) * ((L.form β β : ℤ) : ℂ) - bgPair L lam β) • latChargeGen L β := by
  have hL : LFock L β 0 (vacuumN (rank L))
      = ((1 / 2 : ℂ) * ((L.form β β : ℤ) : ℂ)) • vacuumN (rank L) := by
    rw [LFock, if_pos rfl, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LvirN_vacuum (rank L) 1 (by omega : (-1 : ℤ) ≤ 0), chargeOsc_eq_bgOsc,
      bgOsc_zero_mode, LinearMap.zero_apply, zero_add, zero_add]
  have hb : bgFock L lam β 0 (vacuumN (rank L)) = (bgPair L lam β) • vacuumN (rank L) := by
    rw [bgFock, if_pos rfl, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      bgOsc_zero_mode, LinearMap.zero_apply, zero_add]
  have hv : latChargeGen L β = mkEα L β (vacuumN (rank L)) := rfl
  rw [hv, LBG, LinearMap.sub_apply, LLGen_mkEα L hPos, LinearMap.smul_apply, bgMode_mkEα,
    hL, hb, map_smul, map_smul]
  push_cast
  module

/-- **The triplet-lattice check of the sign convention.**  Take `⟨α,α⟩ = 2p` and
`λ = (p−1)/(2p)·α`, so `⟨λ,α⟩ = p−1` and `⟨λ,−α⟩ = −(p−1)`.  Feeding these into the weight
formula `wt(e^β) = ½⟨β,β⟩ − ⟨λ,β⟩` of `LBG_zero_latChargeGen` gives exactly the demanded
`wt(e^{α}) = 1` and `wt(e^{−α}) = 2p−1`.

**Pure arithmetic**: the statement is two ring identities in `p : ℂ`; it mentions no lattice, no
VOA and no `L^λ_0`.  The connection to weights is only through `LBG_zero_latChargeGen`. -/
theorem bgWeight_triplet (p : ℂ) :
    ((1 / 2 : ℂ) * (2 * p) - (p - 1) = 1) ∧
      ((1 / 2 : ℂ) * (2 * p) - (-(p - 1)) = 2 * p - 1) := by
  constructor <;> ring

/-- The triplet central charge in closed form: `rank = 1` and `⟨λ,λ⟩ = (p−1)²/(2p)` give
`c = 1 − 6(p−1)²/p`.  **Pure arithmetic** (a field identity in `p : ℂ`); it is not a statement
about the central charge of any VOA. -/
theorem bgCentralCharge_triplet (p : ℂ) (hp : p ≠ 0) :
    (1 : ℂ) - 12 * ((p - 1) ^ 2 / (2 * p)) = 1 - 6 * (p - 1) ^ 2 / p := by
  field_simp
  ring

/-- The numeral `1 − 12·(1²/4) = −2` (the `p = 2` value of the triplet central-charge formula).
Pure arithmetic; no VOA is mentioned. -/
theorem bgCentralCharge_triplet_two :
    (1 : ℂ) - 12 * (((2 : ℂ) - 1) ^ 2 / (2 * 2)) = -2 := by norm_num

end VOA.LatGen.BgB
