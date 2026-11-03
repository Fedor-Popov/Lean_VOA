/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSliceMapSugawara
import VOA.Examples.TwoSeriesDSVirSymbol
import VOA.Examples.TwoSeriesCharacterGU
import VOA.Examples.TwoSeriesStrictEndpoint
import VOA.Examples.VirasoroPartitionBasis

/-!
# The Virasoro vacuum module is the Whittaker coinvariant space

Let `Lt n` be the descended Sugawara modes on `E = ℂ[X₀, X₁, …]`
(`TwoSeriesSliceMapSugawara`).  Using the partition basis of the universal Virasoro vacuum module
`Vir^c` (sorted creation words, `VirasoroPartitionBasis`), define

`φ : Vir^c → E`, `L_{-n₁-2} ⋯ L_{-n_b-2} |0⟩ ↦ Lt(-n₁-2) ⋯ Lt(-n_b-2) 1` on sorted words.

## Results

* `phi_negWordVir` — the formula holds for **all** words (the straightening identities agree on
  both sides, since `Lt` satisfies the Virasoro relations without central term);
* `phi_Lop` — `φ` intertwines `L_{-n-2}` with `Lt(-n-2)`;
* `phi_injective` — leading terms `cL^b X_{n₁} ⋯ X_{n_b}` of sorted words are independent;
* `Dg_le_map_vLen` — every polynomial of total degree `≤ d` is `φ` of a vector of Virasoro
  length `≤ d` (triangularity, `Lt_tri`); in particular `φ` is surjective;
* `psi` — the inverse linear equivalence `E ≃ Vir^c`, with `psi_one`, `psi_Lt`, `psi_Dg`.

The central charge `c` is arbitrary.  Everything is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA MvPolynomial VOA.VirModule VOA.TwoSeries.DSSlice

noncomputable section

variable (c : ℂ)

/-! ## §1  The partition basis of `Vir^c` -/

theorem sorted_span_eq_top :
    Submodule.span ℂ (Set.range fun w : {w : List ℕ // SortedWord w} => negWordVir c w.1) = ⊤ := by
  rw [eq_top_iff, ← negSpanVir_eq_top c, negSpanVir, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  have h := negWordVir_mem_sortedSpanVir c w
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨u, hu, _, rfl⟩
  exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩

/-- The partition basis of the universal Virasoro vacuum module. -/
def virBasis : Module.Basis {w : List ℕ // SortedWord w} ℂ (VirUniv c) :=
  Module.Basis.mk (sortedWord_linearIndependent c) (sorted_span_eq_top c).ge

theorem virBasis_apply (w : {w : List ℕ // SortedWord w}) : virBasis c w = negWordVir c w.1 :=
  Module.Basis.mk_apply _ _ _

/-! ## §2  Straightening of Virasoro words -/

/-- Inversions for the weakly decreasing order. -/
def invVir : List ℕ → ℕ
  | [] => 0
  | q :: l => (l.filter fun r => q < r).length + invVir l

theorem invVir_swap (pre post : List ℕ) (i j : ℕ) (hij : i < j) :
    invVir (pre ++ j :: i :: post) < invVir (pre ++ i :: j :: post) := by
  induction pre with
  | nil =>
      have hji : ¬j < i := by omega
      simp only [List.nil_append, invVir, List.filter_cons]
      simp [hij, hji]
      omega
  | cons q pre ih =>
      simp only [List.cons_append, invVir, List.filter_append, List.length_append,
        List.filter_cons]
      split_ifs <;> simp only [List.length_cons] at ih ⊢ <;> omega

theorem exists_inversion_vir :
    ∀ l : List ℕ, ¬SortedWord l →
      ∃ (pre : List ℕ) (i j : ℕ) (post : List ℕ), i < j ∧ l = pre ++ i :: j :: post
  | [], h => by simp [SortedWord] at h
  | [_], h => by simp [SortedWord] at h
  | a :: b :: l, h => by
      by_cases hab : b ≤ a
      · have ht : ¬SortedWord (b :: l) := by
          intro ht
          exact h ((List.pairwise_cons_cons_iff_of_trans).mpr ⟨hab, ht⟩)
        obtain ⟨pre, c, d, post, hcd, heq⟩ := exists_inversion_vir (b :: l) ht
        exact ⟨a :: pre, c, d, post, hcd, by simp [heq]⟩
      · exact ⟨[], a, b, l, by omega, rfl⟩

theorem negWordVir_swap_pre (pre post : List ℕ) (i j : ℕ) :
    negWordVir c (pre ++ i :: j :: post) =
      negWordVir c (pre ++ j :: i :: post) +
        ((j : ℂ) - (i : ℂ)) • negWordVir c (pre ++ (i + j + 2) :: post) := by
  induction pre with
  | nil => exact negWordVir_swap c i j post
  | cons q pre ih =>
      simp only [List.cons_append, negWordVir_cons]
      rw [ih, map_add, map_smul]

/-! ## §3  The map `φ` -/

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The `Lt`-word: `Lt(-n₁-2) ⋯ Lt(-n_b-2) 1`. -/
def LtWord : List ℕ → EPoly
  | [] => 1
  | n :: w => Lt k hk (-(n : ℤ) - 2) (LtWord w)

theorem LtWord_swap_pre (pre post : List ℕ) (i j : ℕ) :
    LtWord k hk (pre ++ i :: j :: post) =
      LtWord k hk (pre ++ j :: i :: post) +
        ((j : ℂ) - (i : ℂ)) • LtWord k hk (pre ++ (i + j + 2) :: post) := by
  induction pre with
  | nil =>
      simp only [List.nil_append, LtWord]
      rw [Lt_comm k hk (by omega) (by omega)]
      congr 2
      · push_cast; ring
      · congr 1; push_cast; ring_nf
  | cons q pre ih =>
      simp only [List.cons_append, LtWord]
      rw [ih, map_add, map_smul]

/-- **The map** `φ : Vir^c → E`. -/
def phi : VirUniv c →ₗ[ℂ] EPoly := (virBasis c).constr ℂ fun w => LtWord k hk w.1

theorem phi_negWordVir (w : List ℕ) : phi c k hk (negWordVir c w) = LtWord k hk w := by
  by_cases hs : SortedWord w
  · have h := (virBasis c).constr_basis ℂ (fun w => LtWord k hk w.1) ⟨w, hs⟩
    rw [virBasis_apply] at h
    exact h
  · obtain ⟨pre, i, j, post, hij, heq⟩ := exists_inversion_vir w hs
    subst w
    rw [negWordVir_swap_pre, map_add, map_smul, phi_negWordVir (pre ++ j :: i :: post),
      phi_negWordVir (pre ++ (i + j + 2) :: post), LtWord_swap_pre k hk pre post i j]
termination_by (w.length, invVir w)
decreasing_by
  · rw [heq]
    rw [show (pre ++ j :: i :: post).length = (pre ++ i :: j :: post).length by simp]
    apply Prod.Lex.right
    exact invVir_swap pre post i j hij
  · rw [heq]
    apply Prod.Lex.left
    simp

theorem phi_vac : phi c k hk (vacVec c) = 1 := by
  rw [← negWordVir_nil c, phi_negWordVir]; rfl

/-- `φ` intertwines the creation modes. -/
theorem phi_Lop (n : ℕ) (v : VirUniv c) :
    phi c k hk (Lop c (-(n : ℤ) - 2) v) = Lt k hk (-(n : ℤ) - 2) (phi c k hk v) := by
  have h : (phi c k hk).comp (Lop c (-(n : ℤ) - 2)) =
      (Lt k hk (-(n : ℤ) - 2)).comp (phi c k hk) := by
    apply LinearMap.ext_on_range (v := negWordVir c)
    · have := negSpanVir_eq_top c
      rwa [negSpanVir] at this
    · intro w
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← negWordVir_cons, phi_negWordVir,
        phi_negWordVir]
      rfl
  exact LinearMap.congr_fun h v

/-! ## §4  Leading terms and injectivity -/

/-- Strictly lower total degree. -/
def Dlow : ℕ → Submodule ℂ EPoly
  | 0 => ⊥
  | d + 1 => Dg d

theorem Dlow_le_Dg (d : ℕ) : Dlow d ≤ Dg d := by
  cases d with
  | zero => exact bot_le
  | succ d => exact Dg_mono (Nat.le_succ d)

theorem X_mul_Dlow (j d : ℕ) {P : EPoly} (hP : P ∈ Dlow d) : X j * P ∈ Dlow (d + 1) := by
  cases d with
  | zero =>
      rw [Dlow, Submodule.mem_bot] at hP
      rw [hP, mul_zero]; exact Submodule.zero_mem _
  | succ d =>
      have h := Dg_mul (mem_Dg.mpr (le_of_eq (totalDegree_X (R := ℂ) j))) hP
      rw [add_comm] at h
      exact h

/-- The product of variables of a word. -/
def prodX (w : List ℕ) : EPoly := (w.map X).prod

theorem prodX_mem (w : List ℕ) : prodX w ∈ Dg w.length := by
  induction w with
  | nil => simp [prodX, mem_Dg]
  | cons n w ih =>
      have h := Dg_mul (mem_Dg.mpr (le_of_eq (totalDegree_X (R := ℂ) n))) ih
      simpa [prodX, add_comm] using h

theorem LtWord_mem (w : List ℕ) : LtWord k hk w ∈ Dg w.length := by
  induction w with
  | nil => simp [LtWord, mem_Dg]
  | cons n w ih =>
      rw [LtWord, List.length_cons]
      have h := Lt_tri k hk n ih
      have h2 := Dg_mul (mem_Dg.mpr (le_of_eq (totalDegree_X (R := ℂ) n))) ih
      rw [← sub_add_cancel (Lt k hk _ _) (cL k • (X n * LtWord k hk w))]
      refine Submodule.add_mem _ (Dg_mono (by omega) h) (Submodule.smul_mem _ _ ?_)
      simpa [add_comm] using h2

theorem LtWord_sub_lead (w : List ℕ) :
    LtWord k hk w - cL k ^ w.length • prodX w ∈ Dlow w.length := by
  induction w with
  | nil => simp [LtWord, prodX, Dlow]
  | cons n w ih =>
      rw [LtWord, List.length_cons]
      have h := Lt_tri k hk n (LtWord_mem k hk w)
      have h2 := X_mul_Dlow n _ ih
      have : Lt k hk (-(n : ℤ) - 2) (LtWord k hk w) - cL k ^ (w.length + 1) • prodX (n :: w) =
          (Lt k hk (-(n : ℤ) - 2) (LtWord k hk w) - cL k • (X n * LtWord k hk w)) +
            cL k • (X n * (LtWord k hk w - cL k ^ w.length • prodX w)) := by
        simp only [prodX, List.map_cons, List.prod_cons, mul_sub, mul_smul_comm, smul_sub,
          smul_smul, pow_succ]
        rw [mul_comm (cL k ^ w.length) (cL k)]
        abel
      rw [this]
      exact Submodule.add_mem _ h (Submodule.smul_mem _ _ h2)

theorem prodX_isHomogeneous (w : List ℕ) : IsHomogeneous (prodX w) w.length := by
  induction w with
  | nil => simpa [prodX] using isHomogeneous_one ℕ ℂ
  | cons n w ih =>
      have := (isHomogeneous_X ℂ n).mul ih
      simpa [prodX, add_comm] using this

theorem homogeneousComponent_LtWord (w : List ℕ) :
    homogeneousComponent w.length (LtWord k hk w) = cL k ^ w.length • prodX w := by
  have h := LtWord_sub_lead k hk w
  have hlow : homogeneousComponent w.length (LtWord k hk w - cL k ^ w.length • prodX w) = 0 := by
    cases hw : w.length with
    | zero =>
        rw [hw, Dlow, Submodule.mem_bot] at h
        rw [h, map_zero]
    | succ d =>
        rw [hw, Dlow] at h
        exact homogeneousComponent_eq_zero _ _ (by have := mem_Dg.mp h; omega)
  have hsame : homogeneousComponent w.length (prodX w) = prodX w := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (prodX_isHomogeneous w)),
      if_pos rfl]
  rw [map_sub, sub_eq_zero, map_smul, hsame] at hlow
  exact hlow

theorem prodX_eq_monomial (w : List ℕ) :
    prodX w = monomial (Multiset.toFinsupp (w : Multiset ℕ)) 1 := by
  rw [← prod_X_toMultiset, Multiset.toFinsupp_toMultiset, Multiset.map_coe, Multiset.prod_coe]
  rfl

theorem sorted_toFinsupp_injective :
    Function.Injective fun w : {w : List ℕ // SortedWord w} =>
      Multiset.toFinsupp (w.1 : Multiset ℕ) := by
  intro w w' h
  have h' : (w.1 : Multiset ℕ) = w'.1 := Multiset.toFinsupp.injective h
  apply Subtype.ext
  exact (Multiset.coe_eq_coe.mp h').eq_of_pairwise' w.2 w'.2

theorem lead_linearIndependent (hk : k + 2 ≠ 0) :
    LinearIndependent ℂ fun w : {w : List ℕ // SortedWord w} =>
      cL k ^ w.1.length • prodX w.1 := by
  have hmono : LinearIndependent ℂ fun w : {w : List ℕ // SortedWord w} =>
      (monomial (Multiset.toFinsupp (w.1 : Multiset ℕ)) (1 : ℂ) : EPoly) := by
    have := (basisMonomials ℕ ℂ).linearIndependent.comp _ (sorted_toFinsupp_injective)
    simpa [Function.comp_def, coe_basisMonomials] using this
  have hu := hmono.units_smul fun w => Units.mk0 (cL k ^ w.1.length)
    (pow_ne_zero _ (cL_ne_zero k hk))
  convert hu using 1
  funext w
  simp [Units.smul_def, prodX_eq_monomial]

theorem LtWord_linearIndependent :
    LinearIndependent ℂ fun w : {w : List ℕ // SortedWord w} => LtWord k hk w.1 := by
  have hself : ∀ w : {w : List ℕ // SortedWord w},
      homogeneousComponent (OrderDual.ofDual (OrderDual.toDual w.1.length)) (LtWord k hk w.1) =
        cL k ^ w.1.length • prodX w.1 := fun w => homogeneousComponent_LtWord k hk w.1
  have hlower : ∀ (w : {w : List ℕ // SortedWord w}) (d : ℕᵒᵈ),
      d < OrderDual.toDual w.1.length →
        homogeneousComponent (OrderDual.ofDual d) (LtWord k hk w.1) = 0 := by
    intro w d hd
    have hd' : w.1.length < OrderDual.ofDual d := hd
    exact homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt (mem_Dg.mp (LtWord_mem k hk w.1)) hd')
  have key := AffineSl2WakimotoLiLeading.linearIndependent_of_lowerLeading_linearOrder
    (R := ℂ) (M := EPoly) (D := ℕᵒᵈ) (ι := {w : List ℕ // SortedWord w})
    (fun w => OrderDual.toDual w.1.length) (fun w => LtWord k hk w.1)
    (fun w => cL k ^ w.1.length • prodX w.1)
    (fun d => (homogeneousComponent (OrderDual.ofDual d) : EPoly →ₗ[ℂ] EPoly))
  have k4 := key hself hlower (lead_linearIndependent k hk)
  exact k4

theorem phi_basis_linearIndependent :
    LinearIndependent ℂ (phi c k hk ∘ virBasis c) := by
  have hf : phi c k hk ∘ virBasis c = fun w => LtWord k hk w.1 := by
    funext w
    rw [Function.comp_apply, virBasis_apply, phi_negWordVir]
  rw [hf]
  exact LtWord_linearIndependent k hk

theorem phi_injective : Function.Injective (phi c k hk) := by
  intro x y hxy
  have hli := phi_basis_linearIndependent c k hk
  have hrepr : ∀ z, phi c k hk z =
      Finsupp.linearCombination ℂ (phi c k hk ∘ virBasis c) ((virBasis c).repr z) := by
    intro z
    conv_lhs => rw [← (virBasis c).linearCombination_repr z]
    rw [Finsupp.apply_linearCombination]
  rw [hrepr, hrepr] at hxy
  have := hli hxy
  exact (virBasis c).repr.injective this

/-! ## §5  Surjectivity with length control -/

theorem Lop_vLen (n : ℕ) {d : ℕ} {v : VirUniv c} (hv : v ∈ vLen c d) :
    Lop c (-(n : ℤ) - 2) v ∈ vLen c (d + 1) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [← negWordVir_cons]
      exact negWordVir_mem_vLen c (by simp; omega)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **Triangular surjectivity**: `Dg d ⊆ φ(vLen d)`. -/
theorem Dg_le_map_vLen (d : ℕ) : Dg d ≤ (vLen c d).map (phi c k hk) := by
  induction d with
  | zero =>
      intro P hP
      rw [eq_C_of_mem_Dg0 hP, C_eq_smul_one]
      refine Submodule.smul_mem _ _ ⟨vacVec c, ?_, phi_vac c k hk⟩
      exact negWordVir_mem_vLen c (w := []) (by simp)
  | succ d ih =>
      intro P hP
      rw [P.as_sum]
      refine Submodule.sum_mem _ fun ν hν => ?_
      have hdeg : (ν.sum fun _ e => e) ≤ d + 1 := (le_totalDegree hν).trans (mem_Dg.mp hP)
      have hm : monomial ν (coeff ν P) = coeff ν P • monomial ν (1 : ℂ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hm]
      refine Submodule.smul_mem _ _ ?_
      by_cases hlow : (ν.sum fun _ e => e) ≤ d
      · have h1 : monomial ν (1 : ℂ) ∈ Dg d := by
          rw [mem_Dg, totalDegree_monomial _ one_ne_zero]; exact hlow
        exact Submodule.map_mono (vLen_mono c (Nat.le_succ d)) (ih h1)
      · have hne : ν ≠ 0 := by
          rintro rfl
          simp at hlow
        obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
        have hj1 : Finsupp.single j 1 ≤ ν := by
          rw [Finsupp.single_le_iff]
          simp at hj
          omega
        set ν' := ν - Finsupp.single j 1 with hν'
        have hνeq : ν = ν' + Finsupp.single j 1 := (tsub_add_cancel_of_le hj1).symm
        have hdeg' : (ν'.sum fun _ e => e) = d := by
          have hs : (ν.sum fun _ e => e) = (ν'.sum fun _ e => e) + 1 := by
            conv_lhs => rw [hνeq]
            rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
              Finsupp.sum_single_index rfl]
          omega
        have h1 : monomial ν' (1 : ℂ) ∈ Dg d := by
          rw [mem_Dg, totalDegree_monomial _ one_ne_zero]; exact hdeg'.le
        obtain ⟨v', hv', hφv'⟩ := ih h1
        have htri := Lt_tri k hk j h1
        obtain ⟨vR, hvR, hφvR⟩ := ih htri
        have hX : monomial ν (1 : ℂ) = X j * monomial ν' 1 := by
          rw [hνeq, X, monomial_mul, one_mul, add_comm]
        refine ⟨(cL k)⁻¹ • (Lop c (-(j : ℤ) - 2) v' - vR),
          Submodule.smul_mem _ _ (Submodule.sub_mem _ (Lop_vLen c j hv')
            (vLen_mono c (Nat.le_succ d) hvR)), ?_⟩
        rw [map_smul, map_sub, phi_Lop, hφv', hφvR, hX, sub_sub_cancel, smul_smul,
          inv_mul_cancel₀ (cL_ne_zero k hk), one_smul]

theorem phi_surjective : Function.Surjective (phi c k hk) := by
  intro P
  obtain ⟨v, _, hv⟩ := Dg_le_map_vLen c k hk P.totalDegree (mem_Dg.mpr le_rfl)
  exact ⟨v, hv⟩

/-! ## §6  The inverse `ψ` -/

/-- **The inverse** `ψ : E ≃ Vir^c`. -/
def psi : EPoly ≃ₗ[ℂ] VirUniv c :=
  (LinearEquiv.ofBijective (phi c k hk) ⟨phi_injective c k hk, phi_surjective c k hk⟩).symm

theorem phi_psi (P : EPoly) : phi c k hk (psi c k hk P) = P :=
  (LinearEquiv.ofBijective (phi c k hk)
    ⟨phi_injective c k hk, phi_surjective c k hk⟩).apply_symm_apply P

theorem psi_phi (v : VirUniv c) : psi c k hk (phi c k hk v) = v :=
  (LinearEquiv.ofBijective (phi c k hk)
    ⟨phi_injective c k hk, phi_surjective c k hk⟩).symm_apply_apply v

theorem psi_one : psi c k hk 1 = vacVec c := by
  rw [← phi_vac c k hk, psi_phi]

theorem psi_Lt (n : ℕ) (P : EPoly) :
    psi c k hk (Lt k hk (-(n : ℤ) - 2) P) = Lop c (-(n : ℤ) - 2) (psi c k hk P) := by
  apply phi_injective c k hk
  rw [phi_psi, phi_Lop, phi_psi]

theorem psi_Dg {d : ℕ} {P : EPoly} (hP : P ∈ Dg d) : psi c k hk P ∈ vLen c d := by
  obtain ⟨v, hv, rfl⟩ := Dg_le_map_vLen c k hk d hP
  rwa [psi_phi]

end

end VOA.TwoSeries.SliceMap
