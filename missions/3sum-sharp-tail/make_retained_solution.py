"""Assemble the checked exact-work lemmas into one self-contained platform proof."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
parts = []
for name in ['RetainedTileWork.lean', 'RetainedTailCount.lean']:
    text = (HERE / 'lean' / name).read_text(encoding='utf-8')
    text = re.sub(r'^import .*\n', '', text, flags=re.M)
    text = re.sub(r'^#print axioms .*\n?', '', text, flags=re.M)
    parts.append(text)

signature = '''(c m nB : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    (Light.Sec4.tAllTiles (c * m) m ⌈θ * (m : ℝ)⌉₊ nB : ℝ) ≤
      1600 * ((c : ℝ) * m + 1) *
        ((nB : ℝ) ^ 2 * (((m : ℝ) + 1) *
          ((ThreeSumSharpTail.boxCount c m 0 : ℝ) *
            (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
              Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) + 1)) +
          nB + 1)'''
preamble = '''import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSPSource_RemainingDefinitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
'''
proof = ''' := by
  open ThreeSumSharpTail in
  have hbox := raw_tile_lists_sharp c m hc hm θ hθ0 hθ9
  change (ThreeSumSharpTail.tileBoxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ : ℝ) ≤ _ at hbox
  have hraw := ThreeSumSharpTail.tAllTiles_le_boxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ nB
  have hrawR : (Light.Sec4.tAllTiles (c * m) m ⌈θ * (m : ℝ)⌉₊ nB : ℝ) ≤
      1600 * ((c : ℝ) * m + 1) *
        ((nB : ℝ) * nB *
          ((ThreeSumSharpTail.tileBoxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ : ℝ) + m + 1) + nB + 1) := by
    exact_mod_cast hraw
  calc
    _ ≤ _ := hrawR
    _ ≤ _ := by
      have hinside : (ThreeSumSharpTail.tileBoxWork (c * m) m ⌈θ * (m : ℝ)⌉₊ : ℝ) + m + 1 ≤
          ((m : ℝ) + 1) *
            ((ThreeSumSharpTail.boxCount c m 0 : ℝ) *
              (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
                Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) + 1) := by
        nlinarith [hbox]
      have hmul := mul_le_mul_of_nonneg_left hinside
        (show 0 ≤ (nB : ℝ) * nB by positivity)
      have hmul' := mul_le_mul_of_nonneg_left
        (add_le_add_right (add_le_add_right hmul (nB : ℝ)) 1)
        (show 0 ≤ 1600 * ((c : ℝ) * m + 1) by positivity)
      convert hmul' using 1 <;> first | rfl | ring
'''
(ROOT / 'Theorems/Thm_ThreeSumSharpTail_retained_tiles_cost.lean').write_text(
    preamble + '\ntheorem ThreeSumSharpTail.retained_tiles_cost ' + signature + ' := by sorry\n',
    encoding='utf-8')
(ROOT / 'Solutions/Sol_ThreeSumSharpTail_retained_tiles_cost.lean').write_text(
    preamble.replace('set_option autoImplicit false', '''import Theorems.Thm_ThreeSumApsp_Spec_length_nineStrs
import Theorems.Thm_ThreeSumSharpTail_sharp_normalized_tail

set_option autoImplicit false''') + '\n'.join(parts) + '\ntheorem solution ' + signature + proof + '\n#print axioms solution\n',
    encoding='utf-8')
print('Assembled retained_tiles_cost proof and exact statement.')
