( cd example_verus; bash build.sh ) &&

( cd ..;
  lake exe verus-lean example/example_verus/vir.json example/example_verus/Example.lean;
)
