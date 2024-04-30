( cd example_verus; verus src/main.rs ) &&

( cd ..;
  lake exe verus-lean example/example_verus/vir.json example/example_verus/Example.lean; )
