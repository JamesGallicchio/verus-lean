program Core;

procedure find_max(v: Map bv64 bv64, v_len: bv64) returns (result: bv64)
spec {
  requires ((v_len > bv{64}(0)));
  ensures (exists x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < v_len)) && (result == (v[x0]))));
  ensures (forall x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < v_len)) ==> (result >= (v[x0]))));
}
{
  var max : bv64 := (v[bv{64}(0)]);
  var i : bv64 := bv{64}(1);
  while ((i < v_len))
    invariant ((((((bv{64}(1) <= i) && (i <= v_len)) && exists x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < i)) && (max == (v[x0])))) && forall x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < i)) ==> (max >= (v[x0])))) && (v_len > bv{64}(0))))
  {
    if (((v[i]) > max)) {
      max := (v[i]);
    } else {
    }
    i := (i + bv{64}(1));
  }
  result := max;
};
