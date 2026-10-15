"""Repair reviewed generic predicate views and rendered safety-tactic layout.

Only unsubmitted or terminally rejected proof sources are eligible. Statements,
accepted proofs, and sources whose verification is in flight are immutable here.
The public segment lemmas remain real proof dependencies through typed views.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
assert (VER / 'machine-server-first.pause').exists()
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
digest = lambda b: hashlib.sha256(b).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
state = read(VER / 'machine-platform-publish.json')
conversion_path = VER / 'server-macro-apply-state.json'
conversion = read(conversion_path)
prefix = '_root_.ThreeSum1960614.Machine.Light.'
# This matches only the exact three-line rendering of the already-expanded
# scalar-safety macro, not declarations, terms, or mathematical dependencies.
safe_render = re.compile(
    r'\(\( \(try have := ' + re.escape(prefix) + r'Std\.space_le \(by assumption\)\)\n'
    r'[ ]+\(try have := ' + re.escape(prefix) + r'Std\.const_le \(by assumption\)\)\n'
    r'[ ]+(simp \[[^\n]*\] <;> omega)\)\)')


def render_safe(match):
    return ('(( (try have := ' + prefix + 'Std.space_le (by assumption)); '
            '(try have := ' + prefix + 'Std.const_le (by assumption)); '
            + match[1] + '))')


def align_memory_macros(source):
    marker = '(( try refine ' + prefix + 'SameOn.cell ?_'
    tail = 'its condition K x does not follow from the hypotheses.")))'
    edits = []
    cursor = 0
    while True:
        start = source.find(marker, cursor)
        if start < 0:
            break
        end = source.index(tail, start) + len(tail)
        assert source.find(marker, start + len(marker), end) < 0
        original = source[start:end]
        lines = original.splitlines()
        assert len(lines) > 2 and lines[1].lstrip().startswith('intro ')
        line_start = source.rfind('\n', 0, start) + 1
        preceding = source[line_start:start]
        standalone = not preceding.strip()
        base_indent = len(preceding) - len(preceding.lstrip())
        target = len(preceding) if standalone else base_indent + 4
        old_indent = min(len(line) - len(line.lstrip()) for line in lines[1:] if line.strip())
        following = [' ' * (len(line) - len(line.lstrip()) - old_indent + target + 3) + line.lstrip()
                     if line.strip() else '' for line in lines[1:]]
        revised = ('' if standalone else '\n' + ' ' * target) + lines[0] + '\n' + '\n'.join(following)
        if revised != original:
            edits.append((start, end, revised))
        cursor = end
    for start, end, revised in reversed(edits):
        source = source[:start] + revised + source[end:]
    return source, len(edits)


prepared = []
for record in manifest['theorems']:
    item = state['items'].get(record['name'], {})
    if item.get('submission_id') and item.get('proof_status') not in ('CE', 'WA', 'SORRY', 'FAILED', 'ERROR'):
        continue
    assert not item.get('verify_intent') or item.get('submission_id'), record['name']
    path = ROOT / record['solution_path']
    original = path.read_bytes()
    assert digest(original) == record['solution_sha256'], record['name']
    source = original.decode('utf-8')
    source = source.replace('≤stop', '≤ stop')
    source = source.replace('≤selected', '≤ selected')
    source = source.replace('≤mask', '≤ mask')
    source = source.replace('∣_root_', '∣ _root_')
    source = source.replace('<m ass','< mass').replace('<mass','< mass')
    source = source.replace('≤m asks','≤ masks').replace('≤s elected','≤ selected').replace('≤s top','≤ stop')
    compiler_updates = re.compile(
        r'\(\(repeat\n[ ]+\(first\n[ ]+\| rw \[_root_\.Function\.update_self\]\n'
        r'[ ]+\| rw \[_root_\.Function\.update_of_ne .*?\n[ ]+exact R\.(?:fp|mem a ha)\)\)', re.S)
    def flatten_compiler_update(match):
        assert '"' not in match[0]
        return ' '.join(match[0].split())
    source = compiler_updates.sub(flatten_compiler_update, source)
    cursor = 0
    compiler_edits = []
    while True:
        start = source.find('((repeat\n', cursor)
        if start < 0:break
        depth = 0
        for end in range(start,len(source)):
            if source[end]=='(':depth+=1
            elif source[end]==')':
                depth-=1
                if depth==0:break
        assert depth==0
        block=source[start:end+1]
        lines=block.splitlines()
        if ('| rw [_root_.Function.update_self]' in block and
            len(lines)>2 and lines[-2].rstrip().endswith(';') and
            lines[-1].lstrip().startswith('exact ') and '"' not in block and '--' not in block):
            compiler_edits.append((start,end+1,' '.join(block.split())))
        cursor=end+1
    for start,end,revised_block in reversed(compiler_edits):
        source=source[:start]+revised_block+source[end:]
    private_lengths=re.findall(r'private theorem (private_[0-9a-f]+_length_bodiesCode)\b',source)
    if private_lengths:
        assert len(set(private_lengths))==1
        source=re.sub(r'(?<![\w.])length_bodiesCode G bs\b',private_lengths[0]+' G bs',source)
    for stem in ('straight_digitsCode','le_endPos','straight_frameInit'):
        helpers_found=re.findall(r'private theorem (private_[0-9a-f]+_'+stem+r')\b',source)
        if helpers_found:
            assert len(set(helpers_found))==1
            source=re.sub(r'(?<![\w.])'+stem+r'\b',helpers_found[0],source)
    if record['name']=='ThreeSum1960614.Machine.Light.pow_spec':
        source = source.replace('((pow_spec hn a μ κ', '((pow_spec__implementation_d1cc9bc2b7 hn a μ κ')
    if record['name']=='ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le':
        source=re.sub(r'(?<![\w.])initialTheta\b','_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta',source)
    if record['name']=='ThreeSum1960614.Machine.Light.Compiler.effects_newFrame':
        frame_update=re.compile(r'(?m)^    · \(\(repeat [^\n]+exact val i \(by omega\)\)\)$')
        replacement='''    · have hstack : _root_.Light.Compiler.cStack (q'+i) ≠ _root_.Light.Compiler.cStack (q'+F') := by
        simp only [_root_.Light.Compiler.cStack]
        omega
      have haddr : _root_.Light.Compiler.cStack (q'+i) ≠ _root_.Light.Compiler.cADDR := by
        simp only [_root_.Light.Compiler.cStack,_root_.Light.Compiler.cADDR]
        omega
      rw [Function.update_of_ne hstack,Function.update_of_ne haddr]
      exact val i (by omega)'''
        source=frame_update.sub(replacement,source)
    source = source.replace('Finset.antidiagonal (K+M)', 'Finset.HasAntidiagonal.antidiagonal (K+M)')
    if '_root_.ThreeSum.WantedPairs.pairs' in source:
        source = source.replace('| zero => intro _; simp\n', '| zero => intro _; simp [_root_.ThreeSum.WantedPairs.pairs]\n')
        source = source.replace('by simp [_root_.ThreeSum.WantedPairs.cells]',
                                'by simp [_root_.ThreeSum.WantedPairs.cells,_root_.ThreeSum.WantedPairs.pairs]')
    source = source.replace(
        '''theorem count_bound (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) : _root_.ThreeSum.BandRawA.count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
''',
        '''theorem count_bound (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) : _root_.ThreeSum.BandRawA.count n g rs i ≤ g*i := by
  induction i with
  | zero => simp [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum.BandRawA.firstRows]
''')
    source = re.sub(r'(?<![\w.])LightSourceBandStep\.word', '_root_.ThreeSum.LightSourceBandStep.word', source)
    source = re.sub(r'(?<![\w.])(hPrepared[A-C][₀₁₂₃₄₅₆₇₈₉]*)\.transfer\b',
                    r'_root_.ThreeSum.LightSortedBands.Prepared.transfer \1',source)
    source = re.sub(r'(?<![\w.])(hPrepared[A-C][₀₁₂₃₄₅₆₇₈₉]*)\.family\b',
                    r'_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared.family \1',source)
    source = re.sub(r'(?<![\w.])(hrep([ABC]))\.keep\b',
                    lambda match:'_root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hs'+match[2]+') '+match[1],source)
    for label in ('repA','repB','repC'):
        source = source.replace('h_root_.ThreeSum.LightBandPreprocessing.Represents.keep '+label+' hkeep',
                                'h'+label+'.keep hkeep')
        source = re.sub(r'(?<![\w.])'+label+r'\.keep hk\b',
                        '_root_.ThreeSum.LightBandPreprocessing.Represents.keep '+label+' hk',source)
        source = source.replace('_root_.ThreeSum.LightBandPreprocessing.Represents.keep '+label+' hk',
                                '_root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hs'+label[-1]+') '+label+' hk')
    source = source.replace(
        '    have he : _root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit j = i := by apply Fin.ext; simp [j]; omega',
        '''    have he : _root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit j = i := by
      apply Fin.ext
      change offset+(i.val-offset)=i.val
      omega''')
    if record['name']=='ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower.meets':
        source = source.replace(
            'simpa [_root_.ThreeSum.ReportingHostSuffix.liftSet] using _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff',
            'simpa [_root_.ThreeSum.ReportingHostSuffix.liftSet,_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding] using _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff')
        source = source.replace(
            '      simpa [_root_.ThreeSum.ReportingHostSuffix.liftSet,_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding] using _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S) (_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit ⟨j,hj⟩)',
            '''      have H := _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S) (_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit ⟨j,hj⟩)
      change (_root_.ThreeSum.MaskErase.eraseMask W (offset+j) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S)) ≠ _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S)) ↔
        (_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit ⟨j,hj⟩) ∈ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S at H
      simpa [_root_.ThreeSum.ReportingHostSuffix.liftSet] using H''')
    source, safe_count = safe_render.subn(render_safe, source)
    helpers = []
    suffix = hashlib.sha256(record['name'].encode()).hexdigest()[:10]
    segment_count = 0
    for lemma in ('cons', 'append'):
        if any('private theorem platform_seg_' + kind + '_' + suffix in source for kind in ('cons', 'append')):
            break
        public = '_root_.Light.seg_' + lemma
        if public not in source:
            continue
        # All eligible occurrences are fully-qualified references in the
        # extracted source; the typed view preserves their original proof.
        local = 'platform_seg_' + lemma + '_' + suffix
        segment_count += source.count(public)
        source = source.replace(public, local)
        if lemma == 'cons':
            helpers.append(f'''private theorem {local} {{μ : ℕ → ℤ}} {{a : ℕ}} {{x : ℤ}} {{l : List ℤ}} :
    {prefix}Seg μ a (x :: l) ↔ μ a = x ∧ {prefix}Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons
''')
        else:
            helpers.append(f'''private theorem {local} {{μ : ℕ → ℤ}} {{a : ℕ}} {{l₁ l₂ : List ℤ}} :
    {prefix}Seg μ a (l₁ ++ l₂) ↔ {prefix}Seg μ a l₁ ∧ {prefix}Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append
''')
    if helpers:
        helpers.append(f'''@[simp] private theorem platform_seg_nil_{suffix} (μ : ℕ → ℤ) (a : ℕ) :
    {prefix}Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim
''')
        imports = list(re.finditer(r'(?m)^import [\w.]+\r?$', source))
        assert imports
        end = imports[-1].end()
        source = source[:end] + '\n\n' + '\n'.join(helpers) + source[end:]
    power_view='private theorem ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.add_same'
    if '.add_same' in source and power_view not in source:
        imports=list(re.finditer(r'(?m)^import [\w.]+\r?$',source));assert imports
        end=imports[-1].end()
        view=f'''\n\n{power_view} {{f g : ℕ → ℕ}} {{a : ℝ}}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a)
    (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n+g n) a := by
  exact _root_.ThreeSum.StageBounds.PowerBound.add_same hf hg
'''
        source=source[:end]+view+source[end:]
    radix_instance = 'platformRadixNonzero_' + suffix
    if (('_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n' in source or
         'import Definitions.Def_ThreeSum1960614_Machine_Bundle007' in source) and
        radix_instance not in source):
        imports = list(re.finditer(r'(?m)^import [\w.]+\r?$', source))
        assert imports
        end = imports[-1].end()
        instance = f'''\n\nlocal instance {radix_instance} (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩
'''
        source = source[:end] + instance + source[end:]
    source, memory_layout_count = align_memory_macros(source)
    revised = source.encode('utf-8')
    if revised == original:
        continue
    entry = conversion['items'][record['solution_path']]
    assert entry['result_sha256'] == digest(original)
    backup = VER / 'server-proof-originals' / (path.stem + '-' + digest(original)[:12] + '.lean.txt')
    if backup.exists():
        assert backup.read_bytes() == original
    else:
        backup.write_bytes(original)
    change = {'name': record['name'], 'path': record['solution_path'],
              'previous_sha256': digest(original), 'current_sha256': digest(revised),
              'scalar_safety_layout_repairs': safe_count,
              'memory_macro_layout_repairs': memory_layout_count,
              'segment_reference_views': segment_count, 'changed_statement': False,
              'reason': 'typed views of public segment lemmas and explicit safety-tactic sequencing',
              'backup': str(backup.relative_to(ROOT))}
    prepared.append((record, path, revised, entry, change))

for record, path, revised, entry, change in prepared:
    path.write_bytes(revised)
    record['solution_sha256'] = digest(revised)
    entry.setdefault('post_conversion_changes', []).append(change)
    entry['result_sha256'] = digest(revised)
if prepared:
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    conversion_path.write_text(json.dumps(conversion, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    receipt_path = VER / 'server-predicate-layout-repairs.json'
    previous = read(receipt_path) if receipt_path.exists() else {}
    receipt = {'updated_at_utc': datetime.now(timezone.utc).isoformat(),
               'changes': previous.get('changes', []) + [row[-1] for row in prepared],
               'manifest_sha256': digest(manifest_path.read_bytes()),
               'accepted_and_inflight_proofs_unchanged': True}
    receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Reviewed proof sources repaired:', len(prepared),
      '; safety layout:', sum(row[-1]['scalar_safety_layout_repairs'] for row in prepared),
      '; memory layout:', sum(row[-1]['memory_macro_layout_repairs'] for row in prepared),
      '; segment references:', sum(row[-1]['segment_reference_views'] for row in prepared))
