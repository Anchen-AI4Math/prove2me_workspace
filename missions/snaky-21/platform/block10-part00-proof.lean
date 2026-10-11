import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_group03_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem solution : Valid card_640 ∧ Valid card_641 ∧ Valid card_642 ∧ Valid card_643 ∧ Valid card_644 ∧ Valid card_645 ∧ Valid card_646 ∧ Valid card_647 ∧ Valid card_648 ∧ Valid card_649 ∧ Valid card_650 ∧ Valid card_651 ∧ Valid card_652 ∧ Valid card_653 ∧ Valid card_654 ∧ Valid card_655 ∧ True :=
  ⟨block10_part00_group00_valid.1, block10_part00_group00_valid.2.1, block10_part00_group00_valid.2.2.1, block10_part00_group00_valid.2.2.2.1, block10_part00_group01_valid.1, block10_part00_group01_valid.2.1, block10_part00_group01_valid.2.2.1, block10_part00_group01_valid.2.2.2.1, block10_part00_group02_valid.1, block10_part00_group02_valid.2.1, block10_part00_group02_valid.2.2.1, block10_part00_group02_valid.2.2.2.1, block10_part00_group03_valid.1, block10_part00_group03_valid.2.1, block10_part00_group03_valid.2.2.1, block10_part00_group03_valid.2.2.2.1, True.intro⟩
