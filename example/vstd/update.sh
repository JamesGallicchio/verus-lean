( cd ../../verus/source; source ../tools/activate; vargo build )
( mv ../../verus/source/vir.json . )

( cd ../..;
  lake exe verus-lean example/vstd/vir.json example/vstd/Example.lean
  )
