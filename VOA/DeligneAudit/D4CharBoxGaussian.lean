import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWeight
import VOA.DeligneAudit.LeviTypeA2CertBoxCard
import VOA.DeligneAudit.DeligneFusionCLCount

/-! The exact current-degree count of a mode box is a Gaussian coefficient. -/

namespace VOA.DeligneAudit.D4Char

open Sl2Weyl A3Sector

noncomputable section

theorem modeList_injective : Function.Injective CLAssembly.lst := by
  intro f g h
  have hm := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
  dsimp only at hm
  rw [CLAssembly.lst_coe, CLAssembly.lst_coe] at hm
  simpa only [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp hm

theorem modeBoxList_image (m a d : ℕ) (ha : a ≤ m) :
    CLAssembly.lst ''
      (↑((a2BoxModeSet m a).filter fun f => (Finsupp.weight om f).2 = d) :
        Set (ℕ →₀ ℕ)) = CL.Inc (m - a) a d := by
  classical
  ext l
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨hf, hd⟩ := Finset.mem_filter.mp hf
    obtain ⟨hlen, hbox⟩ := (mem_a2BoxModeSet m a ha f).mp hf
    refine ⟨⟨CLAssembly.lst_sorted f, fun i hi => ?_⟩,
      (CLAssembly.length_lst f).trans hlen, (a2_lst_sum f).trans hd⟩
    have hh := hbox i (CLAssembly.mem_lst.mp hi)
    rw [hlen] at hh
    exact_mod_cast (show i ≤ m - a by omega)
  · rintro ⟨⟨hls, hlb⟩, hlen, hsum⟩
    let f := Multiset.toFinsupp (l : Multiset ℕ)
    have hl : CLAssembly.lst f = l := by
      unfold CLAssembly.lst f
      rw [Multiset.toFinsupp_toMultiset]
      exact (List.mergeSort_eq_self _ hls).trans rfl
    have hfdeg : Finsupp.degree f = a := by
      rw [← CLAssembly.length_lst, hl, hlen]
    refine ⟨f, Finset.mem_filter.mpr ⟨?_, ?_⟩, hl⟩
    · apply (mem_a2BoxModeSet m a ha f).mpr
      refine ⟨hfdeg, fun i hi => ?_⟩
      have hh := hlb i (by rw [← hl]; exact CLAssembly.mem_lst.mpr hi)
      rw [hfdeg]
      have hh' : i ≤ m - a := by exact_mod_cast hh
      omega
    · rw [← a2_lst_sum, hl, hsum]

/-- This is the degree refinement of `card_a2BoxModeSet`, with all degrees retained. -/
theorem modeBox_card_degree (m a d : ℕ) (ha : a ≤ m) :
    ((a2BoxModeSet m a).filter fun f => (Finsupp.weight om f).2 = d).card =
      A2.qbinomCoeff m a d := by
  have h := congrArg Set.ncard (modeBoxList_image m a d ha)
  rw [Set.ncard_image_of_injective _ modeList_injective, Set.ncard_coe_finset,
    CL.ncard_inc, Nat.sub_add_cancel ha] at h
  exact h

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.modeList_injective
#print axioms VOA.DeligneAudit.D4Char.modeBoxList_image
#print axioms VOA.DeligneAudit.D4Char.modeBox_card_degree
