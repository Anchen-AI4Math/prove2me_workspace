"""Normalize one genuine public AST rfl helper after exact equation admission.

The formal equation Name is an available compiler CI, never a synthetic AST
unit. Only the real shiftEquiv_apply source command receives the workflow's
public/private classification field, proved by its AST and Graph metadata.
"""
from __future__ import annotations
import hashlib
import types
import validate_namespace_context_providers as context

EQUATION='OAI.PiExponent.FormalLogTruncation.shiftMap.eq_1'
PRIMARY='OAI.PiExponent.FormalLogTruncation.shiftMap'
MODULE='OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation'
HELPER='OAI.PiExponent.FormalLogTruncation.shiftEquiv_apply'
UNIT=MODULE+':5444'
CERT_SHA='aa61a7f0b4854577f978588ece7345013220b79b2d3359db0583bc8d7a6207eb'

def install(n,equation):
    d=equation['data']
    context.fail(equation['sha256']!=CERT_SHA or d['validated'] is not True or d['required_source_equation']!=EQUATION
        or d['inverse_primary']!=PRIMARY or d['getter']!='Lean.Meta.getEqnsFor?'
        or d['inverse_getter']!='Lean.Meta.isEqnThm?' or any(d[k] is not True for k in
            ['primary_closed_type_equal','primary_full_safe_def_value_equal','equation_closed_type_equal','equation_Std3_equal']),
        'Only exact current formal getter/inverse/full-primary certificate may admit equation CI')
    preserved=n.g.unit_plan['preserved_generated_commands']
    if EQUATION not in preserved:
        n.g.unit_plan=dict(n.g.unit_plan,preserved_generated_commands=[*preserved,EQUATION])
    old=n.g.elaboration_helpers;ledger={}
    def normalized(g,module,data,facts,inventory,selected_units,accessible_modules):
        helpers,records=old(module,data,facts,inventory,selected_units,accessible_modules)
        result=[]
        for u in helpers:
            if 'private' in u:
                result.append(u);continue
            context.fail(u['id']!=UNIT or u['module']!=MODULE or u['graph_names']!=[HELPER]
                or u['graph_kinds']!=['theorem'] or u['privateTok'] is not None or u['deprivate'] is not False,
                'Only exact actual AST singleton public shiftEquiv_apply helper may be normalized')
            row=g.graph[HELPER]
            context.fail(row['module']!=MODULE or row['kind']!='theorem' or row['isPrivate'] is not False
                or row['isInstance'] is not False or row['startLine']==0,'Helper Graph identity/public AST owner differs')
            actual=next(a for a in inventory['units'] if a['start']==u['start'])
            context.fail(any(u[k]!=actual[k] for k in actual) or (u['start']['offset'],u['valueStart']['offset'],u['end']['offset'])!=(5444,5631,5637)
                or data[5631:5637]!=b':= rfl','Exact authoritative rfl helper source bytes/ranges differ')
            context.fail(EQUATION in u['graph_names'] or u['is_instance_command'] or u['is_local_instance'],
                'Equation companions are not AST helper commands')
            normalized_unit=dict(u,private=False)
            result.append(normalized_unit)
            ledger[UNIT]={'unit':UNIT,'source_graph_name':HELPER,'source_module':MODULE,
                'source_command_range':{'start':u['start'],'end':u['end']},
                'source_command_sha256':hashlib.sha256(data[5444:5637]).hexdigest(),
                'value_range':{'start':u['valueStart'],'end':u['end']},'exact_value':':= rfl',
                'classification_field':'private','classification_value':False,'AST_privateTok_is_null':True,
                'Graph_isPrivate_is_false':True,'AST_scope_and_binding_checked_by_frozen_elaboration_helpers':True,
                'source_plan_classification_changed':False,'equation_CI_not_copied_as_AST':True,
                'equation_certificate_sha256':equation['sha256']}
        return result,records
    n.g.elaboration_helpers=types.MethodType(normalized,n.g)
    n.certified_rfl_helper_normalization=ledger
    return n
