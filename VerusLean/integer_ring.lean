import VerusLean.Macro
import VerusLean.VerusBuiltins

namespace VerusLean

#eval show IO Unit from do
  let d ← System.FilePath.walkDir "verus/source/rust_verify_test"
  let filtered := d.filter (fun path => path.extension.any (· = "json"))
  let contents ← filtered.mapM (IO.FS.readFile ·)
  let jsons ← IO.ofExcept <| contents.mapM (Lean.Json.parse · >>= Lean.fromJson? (α := Theorem))
  let res := Lean.toJson <| jsons.map (Decl.Theorem ·)
  IO.FS.writeFile "integer_ring.json" res.pretty

def square (x: Int ) := x * x
def quad (x: Int) := x * x * x * x

#generate_verus_funcs ↑"out.json" {{
  theorem test.«46638» (x : Int) (y : Int) (z : Int) :
      (x + y + z) * (x + y + z) = x * x + y * y + z + 2 * (x * y + y * z + z * x) := by sorry
  theorem test.«31097» (x : Int) (y : Int) (z : Int) :
      (x + y + z) * (x + y + z) = x * x + y * y + z * z + 2 * (x * y + y * z + z * x) := by sorry
  theorem test.«23083» (x : Int) (y : Int) (z : Int) (m : Int) : (x - y) % m > 0 → (x * z + y * z) % m = 0 := by sorry
  theorem may_div_zero.«49052» (x : Int) : x % x = 0 := by sorry
  theorem test.«2876» (B : Int) (p0 : Int) (p1 : Int) (p2 : Int) (p3 : Int) (p4 : Int) (p5 : Int) (p6 : Int) (p7 : Int)
      (p8 : Int) (p9 : Int) (p10 : Int) (p11 : Int) (p12 : Int) (p13 : Int) (p14 : Int) (p15 : Int) (x : Int)
      (x_0 : Int) (x_1 : Int) (x_2 : Int) (x_3 : Int) (y : Int) (y_0 : Int) (y_1 : Int) (y_2 : Int) (y_3 : Int) :
      x = x_0 + x_1 * B + x_2 * B * B + x_3 * B * B * B →
        y = y_0 + y_1 * B + y_2 * B * B + y_3 * B * B * B →
          p0 = x_0 * y_0 →
            p1 = x_1 * y_0 →
              p2 = x_0 * y_1 →
                p3 = x_2 * y_0 →
                  p4 = x_1 * y_1 →
                    p5 = x_0 * y_2 →
                      p6 = x_3 * y_0 →
                        p7 = x_2 * y_2 →
                          p8 = x_1 * y_2 →
                            p9 = x_0 * y_3 →
                              p10 = x_3 * y_1 →
                                p11 = x_2 * y_2 →
                                  p12 = x_1 * y_3 →
                                    p13 = x_3 * y_2 →
                                      p14 = x_2 * y_3 →
                                        p15 = x_3 * y_3 →
                                          x * y =
                                            p0 + (p1 + p2) * B + (p3 + p4 + p5) * B * B +
                                                    (p6 + p7 + p8 + p9) * B * B * B +
                                                  (p10 + p11 + p12) * B * B * B * B +
                                                (p13 + p14) * B * B * B * B * B +
                                              p15 * B * B * B * B * B * B :=
    by sorry
  theorem test.«5639» (x : Int) (y : Int) (m : Int) :
      x % m * y % m = x * y % m ∧ x * (y % m) % m = x * y % m ∧ x % m * (y % m) % m = x * y % m := by sorry
  theorem test.«36238» (x : Int) (y : Int) (z : Int) (m : Int) : (x - y) % m = 0 → (x * z + y * z) % m = 0 := by sorry
  theorem test.«18354» (x : Int) (y : Int) (m : Int) :
      (square x - square y) % m = 0 →
        square x = x * x →
          square y = y * y → quad x = x * x * x * x → quad y = y * y * y * y → (quad x - quad y) % m = 0 :=
    by sorry
  theorem test.«42782» (singular_tmp_1 : Int) (y : Int) (z : Int) (m : Int) :
      (singular_tmp_1 - y) % m = 0 → (singular_tmp_1 * z - y * z) % m = 0 := by sorry
  theorem test.«33266» (x : Int) (y : Int) (z : Int) (m : Int) : !(x - y) % m = 0 → (x * z + y * z) % m = 0 := by sorry
  theorem test.«63242» (x : Int) (y : Int) (z : Int) (m : Int) : True := by sorry
  theorem test.«28094» (B : Int) (p0 : Int) (p1 : Int) (p2 : Int) (p3 : Int) (p4 : Int) (p5 : Int) (p6 : Int) (p7 : Int)
      (p8 : Int) (p9 : Int) (p10 : Int) (p11 : Int) (p12 : Int) (p13 : Int) (p14 : Int) (p15 : Int) (x : Int)
      (x_0 : Int) (x_1 : Int) (x_2 : Int) (x_3 : Int) (y : Int) (y_0 : Int) (y_1 : Int) (y_2 : Int) (y_3 : Int) :
      x = x_0 + x_1 * B + x_2 * B * B + x_3 * B * B * B →
        y = y_0 + y_1 * B + y_2 * B * B + y_3 * B * B * B →
          p0 = x_0 * y_0 →
            p1 = x_1 * y_0 →
              p2 = x_0 * y_1 →
                p3 = x_2 * y_0 →
                  p4 = x_1 * y_1 →
                    p5 = x_0 * y_2 →
                      p6 = x_3 * y_0 →
                        p7 = x_2 * y_1 →
                          p8 = x_1 * y_2 →
                            p9 = x_0 * y_3 →
                              p10 = x_3 * y_1 →
                                p11 = x_2 * y_2 →
                                  p12 = x_1 * y_3 →
                                    p13 = x_3 * y_2 →
                                      p14 = x_2 * y_3 →
                                        p15 = x_3 * y_3 →
                                          x * y =
                                            p0 + (p1 + p2) * B + (p3 + p4 + p5) * B * B +
                                                    (p6 + p7 + p8 + p9) * B * B * B +
                                                  (p10 + p11 + p12) * B * B * B * B +
                                                (p13 + p14) * B * B * B * B * B +
                                              p15 * B * B * B * B * B * B :=
    by sorry
  theorem test.«51840» (x : Int) (y : Int) (z : Int) (m : Int) : True := by sorry
  theorem test.«47720» (B : Int) (p0 : Int) (p1 : Int) (p2 : Int) (p3 : Int) (p4 : Int) (p5 : Int) (p6 : Int) (p7 : Int)
      (p8 : Int) (p9 : Int) (p10 : Int) (p11 : Int) (p12 : Int) (p13 : Int) (p14 : Int) (p15 : Int) (x : Int)
      (x_0 : Int) (x_1 : Int) (x_2 : Int) (x_3 : Int) (y : Int) (y_0 : Int) (y_1 : Int) (y_2 : Int) (y_3 : Int) :
      True := by sorry
  theorem test.«62323» (x : Int) (y : Int) (z : Int) : True := by sorry
  theorem test.«2706» (x : Int) (y : Int) (m : Int) :
      x % m * y % m = x * y % m ∧ x % m * (y % m) % m = x % m ∧ x * (y % m) % m = x * y % m := by sorry
  theorem test.«5192» (x : Int) (y : Int) (z : Int) (m : Int) : (x - y) % m = 0 → (x * z + y * z) % m < 0 := by sorry
  theorem test.«2059» (x : Int) (y : Int) (m : Int) : True := by sorry
  theorem test.«26010» (x : Int) (y : Int) (m : Int) : True := by sorry
  theorem test.«17114» (x : Int) (y : Int) (z : Int) (m : Int) : (x - y) % m = 0 → (x * z - y * z) % m = 0 := by sorry
  theorem test.«3481» (x : Int) (y : Int) (z : Int) (m : Int) : True := by sorry
  theorem test.«45660» (x : Int) (y : Int) (m : Int) :
      x % m * y % m = x * y % m ∧ x % m * (y % m) % m = x % m ∧ x * (y % m) % m = x % m := by sorry
  theorem test.«10806» (x : Int) (y : Int) (z : Int) (m : Int) : True := by sorry
  theorem test.«13912» (a : Int) (s : Int) (R : Int) (M : Int) (RR : Int) (R_INV : Int) :
      (a * R - RR * s) % M = 0 → (R_INV * R - 1) % M = 0 → RR - R * R % M = 0 → (a - s * R) % M = 0 := by sorry
  theorem test.«22701» (p2_full : Int) (BASE : Int) (ui : Int) (m0 : Int) (m0d : Int) (p1_lh : Int) (p1_full : Int) :
      p2_full = ui * m0 + p1_lh →
        (p1_full - p1_lh) % BASE = 0 →
          (m0d * m0 - (BASE - 1)) % BASE = 0 → (ui - p1_full * m0d) % BASE = 0 → p2_full % BASE = 0 :=
    by sorry

}}
