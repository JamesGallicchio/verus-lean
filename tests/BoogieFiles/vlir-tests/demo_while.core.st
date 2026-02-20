program Core;

procedure find_max(v: Map bv32 bv64, v_len: bv32) returns (result: bv64)
spec {
  requires ((v_len > bv{32}(0)));
  ensures (exists x0: bv32 :: (((bv{32}(0) <= x0) && (x0 < v_len)) && (result == (v[x0]))));
  ensures (forall x0: bv32 :: (((bv{32}(0) <= x0) && (x0 < v_len)) ==> (result >= (v[x0]))));
}
{
  var max : bv64 := (v[bv{32}(0)]);
  var i : bv32 := bv{32}(1);
  while ((i < v_len))
    invariant ((((((bv{32}(1) <= i) && (i <= v_len)) && exists x0: bv32 :: (((bv{32}(0) <= x0) && (x0 < i)) && (max == (v[x0])))) && forall x0: bv32 :: (((bv{32}(0) <= x0) && (x0 < i)) ==> (max >= (v[x0])))) && (v_len > bv{32}(0))))
  {
    if (((v[i]) > max)) {
      max := (v[i]);
    } else {
    }
    i := (i + bv{32}(1));
  }
  result := max;
};
