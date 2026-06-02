{-# OPTIONS --safe #-}

module Tait.Fundamental.SumLemmas where

open import Data.Nat using (ℕ ; _+_ ; _<_ ; _≤_)
open import Data.Nat.Properties using (≤-trans ; <⇒≤)

open import Tait.FundMeasure using (≤-sum-l ; ≤-sum-r ; ≤-sum-extend-r)

≤-sum-1-of-3 : {a b c : ℕ} -> a ≤ a + b + c
≤-sum-1-of-3 {a = a} {b = b} {c = c} =
  ≤-sum-extend-r {k = c} (≤-sum-l {m = a} {n = b})

≤-sum-2-of-3 : {a b c : ℕ} -> b ≤ a + b + c
≤-sum-2-of-3 {a = a} {b = b} {c = c} =
  ≤-sum-extend-r {k = c} (≤-sum-r {m = b} {n = a})

≤-sum-3-of-3 : {a b c : ℕ} -> c ≤ a + b + c
≤-sum-3-of-3 {a = a} {b = b} {c = c} =
  ≤-sum-r {m = c} {n = a + b}

≤-sum-1-of-4 : {a b c d : ℕ} -> a ≤ a + b + c + d
≤-sum-1-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-extend-r {k = d} (≤-sum-1-of-3 {a = a} {b = b} {c = c})

≤-sum-2-of-4 : {a b c d : ℕ} -> b ≤ a + b + c + d
≤-sum-2-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-extend-r {k = d} (≤-sum-2-of-3 {a = a} {b = b} {c = c})

≤-sum-3-of-4 : {a b c d : ℕ} -> c ≤ a + b + c + d
≤-sum-3-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-extend-r {k = d} (≤-sum-3-of-3 {a = a} {b = b} {c = c})

≤-sum-4-of-4 : {a b c d : ℕ} -> d ≤ a + b + c + d
≤-sum-4-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-r {m = d} {n = a + b + c}

≤-sum-1-of-5 : {a b c d e : ℕ} -> a ≤ a + b + c + d + e
≤-sum-1-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-1-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-2-of-5 : {a b c d e : ℕ} -> b ≤ a + b + c + d + e
≤-sum-2-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-2-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-3-of-5 : {a b c d e : ℕ} -> c ≤ a + b + c + d + e
≤-sum-3-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-3-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-4-of-5 : {a b c d e : ℕ} -> d ≤ a + b + c + d + e
≤-sum-4-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-4-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-5-of-5 : {a b c d e : ℕ} -> e ≤ a + b + c + d + e
≤-sum-5-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-r {m = e} {n = a + b + c + d}

≤-sum-1-of-8 : {a b c d e f g h : ℕ} -> a ≤ a + b + c + d + e + f + g + h
≤-sum-1-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-1-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-2-of-8 : {a b c d e f g h : ℕ} -> b ≤ a + b + c + d + e + f + g + h
≤-sum-2-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-2-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-3-of-8 : {a b c d e f g h : ℕ} -> c ≤ a + b + c + d + e + f + g + h
≤-sum-3-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-3-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-4-of-8 : {a b c d e f g h : ℕ} -> d ≤ a + b + c + d + e + f + g + h
≤-sum-4-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-4-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-5-of-8 : {a b c d e f g h : ℕ} -> e ≤ a + b + c + d + e + f + g + h
≤-sum-5-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-5-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-6-of-8 : {a b c d e f g h : ℕ} -> f ≤ a + b + c + d + e + f + g + h
≤-sum-6-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-r {m = f} {n = a + b + c + d + e}))

≤-sum-7-of-8 : {a b c d e f g h : ℕ} -> g ≤ a + b + c + d + e + f + g + h
≤-sum-7-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-r {m = g} {n = a + b + c + d + e + f})

≤-sum-8-of-8 : {a b c d e f g h : ℕ} -> h ≤ a + b + c + d + e + f + g + h
≤-sum-8-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-r {m = h} {n = a + b + c + d + e + f + g}

≤-sum1-3 : (a b c : ℕ) -> a ≤ a + b + c
≤-sum1-3 a b c = ≤-sum-1-of-3 {a = a} {b = b} {c = c}

≤-sum2-3 : (a b c : ℕ) -> b ≤ a + b + c
≤-sum2-3 a b c = ≤-sum-2-of-3 {a = a} {b = b} {c = c}

≤-sum3-3 : (a b c : ℕ) -> c ≤ a + b + c
≤-sum3-3 a b c = ≤-sum-3-of-3 {a = a} {b = b} {c = c}

≤-sum1-4 : (a b c d : ℕ) -> a ≤ a + b + c + d
≤-sum1-4 a b c d = ≤-sum-1-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum2-4 : (a b c d : ℕ) -> b ≤ a + b + c + d
≤-sum2-4 a b c d = ≤-sum-2-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum3-4 : (a b c d : ℕ) -> c ≤ a + b + c + d
≤-sum3-4 a b c d = ≤-sum-3-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum4-4 : (a b c d : ℕ) -> d ≤ a + b + c + d
≤-sum4-4 a b c d = ≤-sum-4-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum1-5 : (a b c d e : ℕ) -> a ≤ a + b + c + d + e
≤-sum1-5 a b c d e = ≤-sum-1-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum2-5 : (a b c d e : ℕ) -> b ≤ a + b + c + d + e
≤-sum2-5 a b c d e = ≤-sum-2-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum3-5 : (a b c d e : ℕ) -> c ≤ a + b + c + d + e
≤-sum3-5 a b c d e = ≤-sum-3-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum4-5 : (a b c d e : ℕ) -> d ≤ a + b + c + d + e
≤-sum4-5 a b c d e = ≤-sum-4-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum5-5 : (a b c d e : ℕ) -> e ≤ a + b + c + d + e
≤-sum5-5 a b c d e = ≤-sum-5-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum1-8 : (a b c d e f g h : ℕ) -> a ≤ a + b + c + d + e + f + g + h
≤-sum1-8 a b c d e f g h =
  ≤-sum-1-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-sum2-8 : (a b c d e f g h : ℕ) -> b ≤ a + b + c + d + e + f + g + h
≤-sum2-8 a b c d e f g h =
  ≤-sum-2-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-sum6-8 : (a b c d e f g h : ℕ) -> f ≤ a + b + c + d + e + f + g + h
≤-sum6-8 a b c d e f g h =
  ≤-sum-6-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-sum8-8 : (a b c d e f g h : ℕ) -> h ≤ a + b + c + d + e + f + g + h
≤-sum8-8 a b c d e f g h =
  ≤-sum-8-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-via-< : {a b c : ℕ} -> a ≤ b -> b < c -> a ≤ c
≤-via-< a≤b b<c = ≤-trans a≤b (<⇒≤ b<c)
