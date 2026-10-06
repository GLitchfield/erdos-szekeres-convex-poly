# Guarded original-source audit retry

Job 20261001-182853-b90582 runs synchronous targeted es check on the exact
accepted public critical proof under explicit20G reservation, review5min.
The command's JSON output is retained in the shared durable job log. On
terminal completion, preserve that exact output and receipt in this directory.
No output JSON is inferred merely from process success. This output directory
was declared at submission and created immediately afterwards; compiler and
extractor progress use the shared job/check/extract logs.

Prior async audit182444-9c639e was refused before Lean: inner20G request
exceeded4G reservation. Do not credit that attempt or silently requeue it.
No shared configuration/worker intervention or approval bypass was used.
