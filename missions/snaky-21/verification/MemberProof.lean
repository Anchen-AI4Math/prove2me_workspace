import Definitions.Def_Snaky21Data11
import Solutions.Snaky21.Certificate00
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

example : card_727 = combine (8, 8) [placed 0 (4, 3) card_648, placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] := by
  apply computed_card_ext
  · ext x
    simp only [card_727, combine, unionRequired, unionEnvelope, commonEnvelope, maxHeight, placed, placement, orient, Prod.add_def, card_648, card_708, card_712, card_713, card_725, card_726]
    simp
    tauto
  · ext x
    simp only [card_727, combine, unionRequired, unionEnvelope, commonEnvelope, maxHeight, placed, placement, orient, Prod.add_def, card_648, card_708, card_712, card_713, card_725, card_726]
    simp
    tauto
  · norm_num [card_727, combine, unionRequired, unionEnvelope, commonEnvelope, maxHeight, placed, placement, orient, Prod.add_def, card_648, card_708, card_712, card_713, card_725, card_726]
