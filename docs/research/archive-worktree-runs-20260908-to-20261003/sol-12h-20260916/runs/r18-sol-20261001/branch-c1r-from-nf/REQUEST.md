Create node/CtxBoundChildRunContractionOneLevelRootOfNormalForm from local main
f112ce1d346d150c0c5f9eb85392f0fb4bba5042 (current main, guidance-only successor
of b231fee6ae19ad8623809d48131cdb535234ab01). This is independent of the ROOT-NF
registration branch. Wait for current grid115602-22d1a0 to finish before switching,
because that grid imports the NF branch's newly registered falsifier.
Grid finished complete rc2, with no-end candidate sharpness failures and zero
actual paired failures. Branch creation is a guarded es job; no merge/push/
primary checkout mutation.
