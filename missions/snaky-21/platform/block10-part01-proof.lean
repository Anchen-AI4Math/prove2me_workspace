import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part01_group03_valid
import Definitions.Def_Snaky21Data10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block10_part00_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem solution : Valid card_656 ∧ Valid card_657 ∧ Valid card_658 ∧ Valid card_659 ∧ Valid card_660 ∧ Valid card_661 ∧ Valid card_662 ∧ Valid card_663 ∧ Valid card_664 ∧ Valid card_665 ∧ Valid card_666 ∧ Valid card_667 ∧ Valid card_668 ∧ Valid card_669 ∧ Valid card_670 ∧ Valid card_671 ∧ True :=
  ⟨block10_part01_group00_valid.1, block10_part01_group00_valid.2.1, block10_part01_group00_valid.2.2.1, block10_part01_group00_valid.2.2.2.1, block10_part01_group01_valid.1, block10_part01_group01_valid.2.1, block10_part01_group01_valid.2.2.1, block10_part01_group01_valid.2.2.2.1, block10_part01_group02_valid.1, block10_part01_group02_valid.2.1, block10_part01_group02_valid.2.2.1, block10_part01_group02_valid.2.2.2.1, block10_part01_group03_valid.1, block10_part01_group03_valid.2.1, block10_part01_group03_valid.2.2.1, block10_part01_group03_valid.2.2.2.1, True.intro⟩
