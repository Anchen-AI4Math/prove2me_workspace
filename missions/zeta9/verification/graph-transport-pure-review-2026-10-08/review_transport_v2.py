from pathlib import Path
import io,json,hashlib,sys,threading,time
TASK=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(TASK/'scripts'))
import graph_platform_client_2026_10_08 as g
before={n:hashlib.sha256((TASK/'scripts'/n).read_bytes()).hexdigest() for n in ['graph_platform_client_2026_10_08.py','publish_graph_integration_2026_10_08.py']}
original_init=g.official.Client.__init__
constructor_reads=[]
def fake_init(self):constructor_reads.append(True)
g.official.Client.__init__=fake_init
g.check_documents=lambda:None
rows=[]
uid='12345678-1234-4234-8234-123456789abc'
def jwrite(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v)+'\n',encoding='utf-8')
def setup(label):
 root=OUT/'fixtures-v2'/label;assert not root.exists();root.mkdir(parents=True)
 g.TASK=root;g.OUT=root/'out';g.OUT.mkdir()
 source=root/'source.lean';source.write_bytes(b'-- fixture source only\n')
 bind={'task_relative':'source.lean','bytes':source.stat().st_size,'sha256':g.sha(source)}
 body=g.json_wire({'problems':[{'theorem_name':'Fixture.expected'}]})
 op={'method':'POST','path':'/submit-problem','body_sha256':hashlib.sha256(body).hexdigest(),'body_bytes':len(body),'content_type':'application/json'}
 pin={'all_required_native_and_platform_independent_checks_passed':True,'new_mission_id':g.MISSION,'env':g.ENV,'bindings':[bind],'operations':{'op1':op,'op2':op}}
 plan={'all_required_native_and_platform_independent_checks_passed':True,'reviewed_labels':['A'],'sources':{'A':{'definition':bind,'reference':bind,'solution':bind}}}
 jwrite(g.OUT/'Root-reviewed-publication-pin.json',pin);jwrite(g.OUT/'Root-reviewed-source-plan.json',plan)
 jwrite(g.OUT/'Root-reviewed-api-compatibility.json',{'latest_official_document_pins':g.PINS,'latest_main_skill_sha256':g.PINS['SKILL.md'],'used_endpoint_contracts_personally_reviewed':True,'observed_platform_version':'0.12.2'})
 jwrite(root/'verification/graph-integration-root-2026-10-08/phase-registration-recovery/Root-complete-readonly-reconciliation.json',{'history_complete_total':236,'exact_current_name_search_total':0})
 return root,body
class FakeOpen:
 def __init__(self,value=None,error=False,block=None):self.value=value;self.error=error;self.calls=0;self.block=block
 def open(self,request,timeout):
  self.calls+=1
  if self.block:self.block[0].set();self.block[1].wait(5)
  if self.error:raise IOError('synthetic uncertain transport failure')
  return io.BytesIO(json.dumps(self.value).encode())
def client(value=None,error=False,block=None):
 c=g.Client.__new__(g.Client);c.token='synthetic-offline-token';c.opener=FakeOpen(value,error,block);return c
def business(c,body,op='op1'):return c.business(op,'POST','/submit-problem',body,'application/json')
def check(name,fn):
 try:fn();rows.append({'name':name,'passed':True})
 except Exception as e:rows.append({'name':name,'passed':False,'error_type':type(e).__name__,'error':str(e)})
def expect_error(fn):
 try:fn()
 except Exception:return
 raise AssertionError('expected rejection')
def missing(which):
 root,b=setup('missing-'+which);(g.OUT/('Root-reviewed-'+which+'.json')).unlink();count=len(constructor_reads);expect_error(g.Client);assert len(constructor_reads)==count
check('missing PIN blocks constructor credential entry',lambda:missing('publication-pin'))
check('missing source plan blocks constructor credential entry',lambda:missing('source-plan'))
def damaged():
 root,b=setup('damaged-source');(root/'source.lean').write_bytes(b'changed');count=len(constructor_reads);expect_error(g.Client);assert len(constructor_reads)==count
check('source hash mutation blocks constructor credential entry',damaged)
def normal():
 root,b=setup('normal');c=client({'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.expected'}]});v=business(c,b);assert v['jobs'][0]['job_id']==uid;assert business(c,b)==v;assert c.opener.calls==1;assert g.load(g.OUT/'business-post-journal.json')['attempts'][0]['receipt_saved']
check('normal once plus saved receipt resume yields no duplicate business',normal)
def uncertain(label,value=None,error=False):
 root,b=setup(label);c=client(value,error);expect_error(lambda:business(c,b));j=g.load(g.OUT/'business-post-journal.json');assert not j['attempts'][0]['receipt_saved'];expect_error(lambda:business(c,b,'op2'));assert c.opener.calls==1
check('invalid 200 receipt keeps global unknown barrier',lambda:uncertain('invalid-json',{}))
check('wrong echoed theorem name keeps global unknown barrier',lambda:uncertain('wrong-name',{'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.other'}]}))
check('network uncertainty keeps global unknown barrier',lambda:uncertain('network-error',error=True))
def changed_after_init():
 root,b=setup('changed-before-business');c=client({'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.expected'}]});(root/'source.lean').write_bytes(b'changed');expect_error(lambda:business(c,b));assert c.opener.calls==0
check('source change checked again immediately before business',changed_after_init)
def changed_wire():
 root,b=setup('changed-wire');c=client({'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.expected'}]});business(c,b);j=g.load(g.OUT/'business-post-journal.json');(g.OUT/j['attempts'][0]['wire']).write_bytes(b'changed');expect_error(lambda:business(c,b,'op2'));assert c.opener.calls==1
check('stored wire mutation blocks batch',changed_wire)
def concurrency():
 root,b=setup('concurrency');events=(threading.Event(),threading.Event());c=client({'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.expected'}]},block=events);results=[]
 t=threading.Thread(target=lambda:results.append(business(c,b)));t.start();assert events[0].wait(3)
 try:expect_error(lambda:business(client({'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.expected'}]}),b))
 finally:events[1].set();t.join(5)
 assert not t.is_alive() and c.opener.calls==1 and len(results)==1
check('actual msvcrt exclusive writer prevents concurrency duplicate',concurrency)
def stored_shape():
 root,b=setup('saved-invalid-shape');c=client({'errors':[],'jobs':[{'job_id':uid,'name':'Fixture.expected'}]});business(c,b);jp=g.OUT/'business-post-journal.json';j=g.load(jp);rp=g.OUT/j['attempts'][0]['receipt'];jwrite(rp,{});j['attempts'][0]['receipt_sha256']=g.sha(rp);jwrite(jp,j);expect_error(lambda:business(c,b,'op2'));assert c.opener.calls==1
check('resume validates saved receipt semantic shape as well as SHA',stored_shape)
after={n:hashlib.sha256((TASK/'scripts'/n).read_bytes()).hexdigest() for n in before};assert before==after,'Source changed during pure review'
report={'scope':'isolated fake transport and fake credential constructor only','real_API_calls':0,'real_credential_reads':0,'real_Lean_calls':0,'source_hashes':before,'checks':rows,'passed':sum(x['passed'] for x in rows),'failed':sum(not x['passed'] for x in rows)}
jwrite(OUT/'pure-mock-review-v2.json',report)
print(json.dumps({k:v for k,v in report.items() if k!='source_hashes'},indent=2))
g.official.Client.__init__=original_init
