import VOA.Classification.COne.PlusRat5Final

/-! # `V_{2m}⁺` for `2 ≤ m ≤ 100`

`TwistArithFree m` is decided by the kernel for every `m ≤ 100` outside
`{16, 36, 64, 68, 100}`; hence `V_{2m}⁺` is strongly rational for all those `m`.
The five exceptional `m` are exactly those `≤ 100` with a twisted-kernel obligation
(`TwistedKernelPairs`, OPEN).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat5

-- `interval_cases` over 99 values, each closed by a kernel `decide` on a bounded search.
set_option maxHeartbeats 8000000 in
theorem twistArithFree_upTo100 (m : ℕ) (hm2 : 2 ≤ m) (h100 : m ≤ 100)
    (hbad : m ≠ 16 ∧ m ≠ 36 ∧ m ≠ 64 ∧ m ≠ 68 ∧ m ≠ 100) : TwistArithFree m := by
  obtain ⟨h16, h36, h64, h68, h100'⟩ := hbad
  interval_cases m <;> first | decide +kernel | simp_all

end VOA.Classification.COne.PlusRat5

namespace VOA.Classification.COne
open PlusRat5

/-- **`V_{2m}⁺` is strongly rational for every `2 ≤ m ≤ 100`, `m ∉ {16, 36, 64, 68, 100}`.** -/
theorem V2mPlus_stronglyRational_upTo100 (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) (h100 : m ≤ 100)
    (hbad : m ≠ 16 ∧ m ≠ 36 ∧ m ≠ 64 ∧ m ≠ 68 ∧ m ≠ 100) : StronglyRational (V2mPlus m hm) :=
  V2mPlus_stronglyRational_of_twistArithFree m hm hm2 (twistArithFree_upTo100 m hm2 h100 hbad)

end VOA.Classification.COne
