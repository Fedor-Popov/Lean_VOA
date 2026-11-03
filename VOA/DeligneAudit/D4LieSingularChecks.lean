/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieSingularOneCheck00
import VOA.DeligneAudit.D4LieSingularOneCheck01
import VOA.DeligneAudit.D4LieSingularOneCheck02
import VOA.DeligneAudit.D4LieSingularOneCheck03
import VOA.DeligneAudit.D4LieSingularOneCheck04
import VOA.DeligneAudit.D4LieSingularOneCheck05
import VOA.DeligneAudit.D4LieSingularOneCheck06
import VOA.DeligneAudit.D4LieSingularOneCheck10
import VOA.DeligneAudit.D4LieSingularOneCheck11
import VOA.DeligneAudit.D4LieSingularOneCheck12
import VOA.DeligneAudit.D4LieSingularOneCheck13
import VOA.DeligneAudit.D4LieSingularOneCheck14
import VOA.DeligneAudit.D4LieSingularOneCheck15
import VOA.DeligneAudit.D4LieSingularOneCheck16
import VOA.DeligneAudit.D4LieSingularOneCheck20
import VOA.DeligneAudit.D4LieSingularOneCheck21
import VOA.DeligneAudit.D4LieSingularOneCheck22
import VOA.DeligneAudit.D4LieSingularOneCheck23
import VOA.DeligneAudit.D4LieSingularOneCheck24
import VOA.DeligneAudit.D4LieSingularOneCheck25
import VOA.DeligneAudit.D4LieSingularOneCheck26
import VOA.DeligneAudit.D4LieSingularTwoCheck0
import VOA.DeligneAudit.D4LieSingularTwoCheck1
import VOA.DeligneAudit.D4LieSingularTwoCheck2

/-! Assemble typed small checks without evaluating a large closed checker. -/
namespace VOA.DeligneAudit.D4Lie

theorem oneZ_eq : ∀ r c e, oneZ r c e = 0 := by
  intro r c e
  fin_cases r
  · by_cases h0 : c.val < 4
    · exact oneZ_block_0_0 c e (by omega) h0
    · by_cases h1 : c.val < 8
      · exact oneZ_block_0_1 c e (by omega) h1
      · by_cases h2 : c.val < 12
        · exact oneZ_block_0_2 c e (by omega) h2
        · by_cases h3 : c.val < 16
          · exact oneZ_block_0_3 c e (by omega) h3
          · by_cases h4 : c.val < 20
            · exact oneZ_block_0_4 c e (by omega) h4
            · by_cases h5 : c.val < 24
              · exact oneZ_block_0_5 c e (by omega) h5
              · exact oneZ_block_0_6 c e (by omega) c.isLt
  · by_cases h0 : c.val < 4
    · exact oneZ_block_1_0 c e (by omega) h0
    · by_cases h1 : c.val < 8
      · exact oneZ_block_1_1 c e (by omega) h1
      · by_cases h2 : c.val < 12
        · exact oneZ_block_1_2 c e (by omega) h2
        · by_cases h3 : c.val < 16
          · exact oneZ_block_1_3 c e (by omega) h3
          · by_cases h4 : c.val < 20
            · exact oneZ_block_1_4 c e (by omega) h4
            · by_cases h5 : c.val < 24
              · exact oneZ_block_1_5 c e (by omega) h5
              · exact oneZ_block_1_6 c e (by omega) c.isLt
  · by_cases h0 : c.val < 4
    · exact oneZ_block_2_0 c e (by omega) h0
    · by_cases h1 : c.val < 8
      · exact oneZ_block_2_1 c e (by omega) h1
      · by_cases h2 : c.val < 12
        · exact oneZ_block_2_2 c e (by omega) h2
        · by_cases h3 : c.val < 16
          · exact oneZ_block_2_3 c e (by omega) h3
          · by_cases h4 : c.val < 20
            · exact oneZ_block_2_4 c e (by omega) h4
            · by_cases h5 : c.val < 24
              · exact oneZ_block_2_5 c e (by omega) h5
              · exact oneZ_block_2_6 c e (by omega) c.isLt

theorem twoZ_eq : ∀ r c, twoZ r c = 0 := by
  intro r c
  fin_cases r
  · exact twoZ_row_0 c
  · exact twoZ_row_1 c
  · exact twoZ_row_2 c

end VOA.DeligneAudit.D4Lie
