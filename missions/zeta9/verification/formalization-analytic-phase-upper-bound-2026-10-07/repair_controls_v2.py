"""Control-only V2 repairs command namespace shadowing of generic IO lifting."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p

def main():
    for name in ['APTypes.lean','APKernel.lean','APBoundary.lean']:
        source=(p.OUT/'controls-v1'/name).read_text(encoding='utf-8')
        assert source.count('liftIO <| IO.println')==1
        source=source.replace('liftIO <| IO.println','liftM <| IO.println')
        p.write(p.OUT/'controls-v2'/name,source);p.write(p.PROJECT/name,source)
    p.dump(p.OUT/'controls-v2-repair.json',dict(change='Use generic MonadLift for IO in MetaM instead of shadowed Command.liftIO',
      controls=[p.binding(p.PROJECT/name) for name in ['APTypes.lean','APKernel.lean','APBoundary.lean']],
      canonical_sources_unchanged=True,failed_attempt_retained='actual-runs/control-types-v1-01'))
    print('Control V2 generic IO lifting prepared.',flush=True)
if __name__=='__main__':main()
