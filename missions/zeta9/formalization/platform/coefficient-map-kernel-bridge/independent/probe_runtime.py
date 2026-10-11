"""Actually resolve all inherited/new mission objects in the separate own caches."""
from run_step import *

verify()
enrollment = load(OUT / 'execution-preparation.json')
native_modules = ['missions.zeta9.formalization.' + name for name in enrollment['native_order']]
native_modules += ['Definitions.Def_ZetaNine_HarmonicStability', 'NativeKernelAuthorControl', 'NativeKernelIndependentControl',
                   'NativeValueComparisonDefinition', 'NativeKernelValueComparisonDefinition', 'NativeRootNodeValueComparison']
platform_modules = ['Definitions.Def_ZetaNine_' + name for name in ['HarmonicStability'] + enrollment['native_order']]
platform_modules += [row['root_relative_destination'].removesuffix('.lean').replace('/', '.')
                     for row in load(BATCH / 'root-copy-plan.json')['files']
                     if not row['root_relative_destination'].startswith('Definitions/')]
platform_modules += ['StagedValueComparisonDefinition', 'StagedKernelValueComparisonDefinition', 'StagedRootNodeValueComparison']
for context, cache, modules in [('native', N, native_modules), ('staged', P, platform_modules)]:
    code = 'import Lean\nopen Lean\nrun_meta do\n'
    code += '  let envPath ← IO.getEnv "LEAN_PATH"\n'
    code += '  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),("LEAN_PATH",Json.str (envPath.getD "")),("Lean_version",Json.str Lean.versionString)]).compress\n'
    code += '  let search ← searchPathRef.get\n'
    code += '  for name in [' + ', '.join('`' + module for module in modules) + '] do\n'
    code += '    let path ← findOLean name\n'
    code += '    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str name.toString),("resolved_olean",Json.str path.toString)]).compress\n'
    source = OUT / ('rn.lean' if context == 'native' else 'rp.lean')
    write(source, code)
    run(context + ' actual independent environment and module resolver', source, cache)
dump(OUT / 'runtime-probe-plan.json', {'native_modules': native_modules, 'staged_modules': platform_modules,
    'expected_actual_resolutions': len(native_modules) + len(platform_modules), 'borrowed_mission_objects_allowed': False})
