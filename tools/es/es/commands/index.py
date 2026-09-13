import json
from pathlib import Path
from es.artifacts import put_json
from es.commands.automation import result
from es.shadow_index import compare
from es.spec import Arg,CommandSpec,command


def shadow(ctx,baseline,targeted,oracle):
    value=compare(*(json.loads(Path(p).read_text()) for p in (baseline,targeted,oracle)))
    ref=put_json(ctx.cfg,value,'shadow-index-comparison-v1')
    return result(ctx,{k:v for k,v in value.items() if k!='merged'}|{'comparison':ref})


command(CommandSpec('index_shadow',['index','shadow'],'Compare an incremental merge to a full oracle; never publishes an index.',shadow,
    [Arg('baseline','baseline manifest JSON',required=True),Arg('targeted','targeted compiled manifest JSON',required=True),Arg('oracle','full compiled oracle manifest JSON',required=True)]))
