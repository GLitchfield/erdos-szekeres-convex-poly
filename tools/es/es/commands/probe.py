import json
from pathlib import Path
from es import probes
from es.commands.automation import result
from es.spec import Arg, CommandSpec, command

command(CommandSpec('probe_run',['probe','run'],'Queue a versioned finite probe; negative results are bounded and give no proof credit.',
    lambda ctx,spec,window=None:result(ctx,probes.submit(ctx.cfg,ctx.agent,json.loads(Path(spec).read_text()),window=window)),
    [Arg('spec','JSON probe specification',required=True),Arg('window','usage window ID')]))
command(CommandSpec('probe_replay',['probe','replay'],'Independently replay a saved witness under the same source and semantic version.',
    lambda ctx,id:result(ctx,probes.replay(ctx.cfg,id)),[Arg('id','probe result artifact ID',positional=True,required=True)]))
