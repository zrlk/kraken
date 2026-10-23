import Scc.Lower.Obj

/-!
# Tests of the object layout (`Scc.Obj`)

* The width law `n + m = wc + ext` (`wc` = WeakCore's model
  width, `Ty.rawWords`), on ten cases, with the expected `(n, m, ext)`
  for each.  Eight of them are sums, which are not in the accepted fragment:
  `regE` covers them so that the law is checked where it has content.
* The layout map `slots` on fragment types: region and index of every word in
  value order, consistent with `regE` (`ext` = the number of locatives).
* 16-byte pairs (`pairRegion`, `place`, `strideOf`, `allocGap`): every pair
  of a value, of an array element and of a freshly allocated object is one
  aligned 16-byte granule in its region, under both header placements; on
  types without pairs `place` agrees with `slots`.
* The header encoding: the default field widths fill a word, and a header
  decodes to the fields it was built from.
-/

open CoreLang

namespace Scc.Test.LayoutTest
open Scc.Obj

def P : Ty := .ptr .pub .int
def L : Ty := .loc .pub .int

/-- Ten cases of the width law with the expected `(n, m, ext)` and `wc`. -/
def l1Cases : List (String × Ty × (Nat × Nat × Nat) × Nat) :=
  [ ("Loc + Loc (niche)", .sum L L, (1, 1, 1), 1),
    ("Int + Loc pub (wide)", .sum .int L, (2, 1, 1), 2),
    ("10-arm all-reference sum (wide)",
      (List.range 9).foldr (fun _ t => .sum P t) P, (1, 1, 0), 2),
    ("Int + Ptr (wide)", .sum .int P, (2, 1, 1), 2),
    ("Ptr + Loc (niche)", .sum P L, (1, 1, 1), 1),
    ("Loc × Loc", .prod L L, (2, 2, 2), 2),
    ("Int + U8 (wide)", .sum .int (.fix false .w8), (2, 0, 0), 2),
    ("Ptr + Ptr (niche)", .sum P P, (0, 1, 0), 1),
    ("claim option: (∃a. Ptr × Tok) + Unit",
      .sum (.iex (.prod P (.tok (.var 0) none))) .unit, (1, 1, 0), 2),
    ("Int × Ptr × Loc", .prod .int (.prod P L), (2, 2, 1), 3) ]

/-- Each case: `regE` is the note's triple, `wc` is the model width, and the
law holds. -/
def l1Check : List (String × Bool) :=
  l1Cases.map fun (name, t, r, w) =>
    (name, regE t == some r && t.rawWords == some w &&
      match regE t, t.rawWords with
      | some (n, m, e), some wc => n + m == wc + e
      | _, _ => false)

/-- info: [true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval l1Check.map (·.2)

#guard l1Check.length == 10 && l1Check.all (·.2)

-- A `ThreadId` is exactly one word: one trace (reference) word, no scalar
-- word, no locative.  A wider layout would be a mistake.
#guard regE .tid == some (0, 1, 0)

/-! ## The layout map on fragment types -/

-- `Int × Ptr × Loc`: words in value order `[int, ptr, loc.base, loc.off]`;
-- scalars `int ↦ 0`, `loc.off ↦ 1`; traces `ptr ↦ 0`, `loc.base ↦ 1`.
#guard slots (.prod .int (.prod P L)) 0 0 == some [(false, 0), (true, 0), (true, 1), (false, 1)]

-- A product's components keep their own contiguous ranges in each region,
-- so a locative to the second component is `(base, offWord 8·n₁ 8·m₁)`.
#guard slots (.prod (.prod P .int) (.prod .int P)) 0 0 ==
  some [(true, 0), (false, 0), (false, 1), (true, 1)]

#guard stride 1 1 == 8 + 8 * 2 ^ 32

/-- Fragment types: on them `slots` agrees with `regE`, and `ext` counts the
locatives (each one model word, two target words). -/
def fragTypes : List Ty :=
  [.unit, .int, P, L, .prod L L, .prod .int (.prod P L), .refine (.prod P .int) .tt,
   .iex (.prod (.intS (.var 0)) L)]

#guard fragTypes.all fun t =>
  match regOf t, regE t, t.rawWords, valWords t with
  | some (n, m), some (n', m', e), some w, some vw => n == n' && m == m' && vw == w + e
  | _, _, _, _ => false

/-! ## Mixed units -/

#guard inlineMixed L && inlineMixed (.prod .int L) && !inlineMixed (.prod .int P) &&
  !inlineMixed (.ptr .pub L) && inlineMixed (.sum .int P) && !inlineMixed (.sum .int (.fix false .w8)) &&
  !inlineMixed (.sum P P) && inlineMixed (.sum P L)

/-! ## 16-byte pairs -/

/-- Both header placements. -/
def placements : List ObjLayout := [{ headerBeforeTrace := false }, { headerBeforeTrace := true }]

def pr2 : Proto2 := { clauses := [], trans := [] }
/-- A protocol pair and an epoch pair: scalar pairs. -/
def W2 : Ty := .word2 (.lit 0) pr2
def EP : Ty := .epair (.lit 0) (.pair pr2)
/-- A scalar wide sum of two words. -/
def SW : Ty := .sum .int (.fix false .w8)
/-- Coupled packages of two scalars and of two references. -/
def CS : Ty := .iex (.prod (.intS (.var 0)) (.intS (.var 0)))
def CT : Ty := .iex (.prod (.ptr .pub (.intS (.var 0))) (.ptr .pub (.intS (.var 0))))
/-- A mixed pair (a tag and a reference): no layout here. -/
def MX : Ty := .sum .int P

#guard [W2, EP, SW, CS].all (pairRegion · == some false) && pairRegion CT == some true &&
  pairRegion MX == none && pairRegion (.prod .int .int) == none

-- A scalar pair after one scalar word skips index 1; a trace pair after one
-- reference skips the trace index that would misalign it, which depends on
-- the header placement (`traceBias` 16 by default, 8 otherwise).
#guard placeWords {} (.prod .int W2) 0 0 == some [(false, 0), (false, 2), (false, 3)]
#guard placeWords {} (.prod P CT) 0 0 == some [(true, 0), (true, 1), (true, 2)]
#guard placeWords { headerBeforeTrace := true } (.prod P CT) 0 0 == some [(true, 0), (true, 2), (true, 3)]
#guard place {} MX 0 0 == none

/-- Types with pairs (and gaps), for the alignment checks below. -/
def pairTypes : List Ty :=
  [W2, EP, SW, CS, CT, .prod .int W2, .prod P CT, .prod (.prod L CT) (.prod .int EP),
   .prod CT (.prod P (.prod CT .int)), .prod (.prod W2 .int) (.prod SW L), .prod CS (.prod CS CT)]

/-- The byte offset from a 16-aligned base of the lowest word of every pair
in a value laid out from `(s, r)`: `8i` for scalar words `i, i + 1`,
`−traceBias − 8(j + 1)` for trace words `j, j + 1`. -/
def pairOffsets (o : ObjLayout) (t : Ty) (s r : Nat) : Option (List Int) :=
  (place o t s r).map fun (us, _, _) => us.filterMap fun u =>
    if !u.pair then none
    else if u.trace then some (-(traceBias o) - 8 * ((u.idx : Int) + 1)) else some (8 * (u.idx : Int))

-- Every pair is one aligned granule: in a cell at the object's base and in
-- the first four elements of an array (element `k` at `(k·n, k·m)` with
-- `(n, m) = strideOf`), under both placements.
#guard placements.all fun o => pairTypes.all fun t =>
  match strideOf o t with
  | none => false
  | some (n, m) => (List.range 4).all fun k =>
      match pairOffsets o t (k * n) (k * m) with
      | some offs => !offs.isEmpty && offs.all (· % 16 == 0)
      | none => false

-- Element `k` is element 0 shifted by `k` strides: the same words, the same gaps.
#guard placements.all fun o => pairTypes.all fun t =>
  match strideOf o t, placeWords o t 0 0 with
  | some (n, m), some w0 => (List.range 4).all fun k =>
      placeWords o t (k * n) (k * m) ==
        some (w0.map fun (tr, i) => (tr, if tr then i + k * m else i + k * n))
  | _, _ => false

-- The regions of a stride are even where they hold a pair, and the gaps are
-- the only extra words: `Int × W2` takes 4 scalar words, one of them a gap.
-- With the header at `base − 8` a trace pair cannot start at trace index 0
-- (its granule would start at `base − 24`), so `CT` alone takes 4 trace
-- words; with the header before the trace region it takes 2.
#guard strideOf {} (.prod .int W2) == some (4, 0) && strideOf {} (.prod W2 .int) == some (4, 0) &&
  strideOf {} (.prod P CT) == some (0, 4) && strideOf {} CT == some (0, 4) &&
  strideOf { headerBeforeTrace := true } CT == some (0, 2) &&
  placeWords {} CT 0 0 == some [(true, 1), (true, 2)]

-- Without pairs `place` leaves no gap and agrees with `slots` (whatever the
-- start indices and the placement), and `strideOf` with `regOf`.
#guard placements.all fun o => fragTypes.all fun t =>
  (List.range 3).all fun s => (List.range 3).all fun r =>
    placeWords o t s r == slots t s r && strideOf o t == regOf t

/-- The trace indices of an object of `len` elements of type `t` (header
counts `Obj.counts`) that no unit uses: its trace fillers. -/
def traceFillers (o : ObjLayout) (t : Ty) (len : Nat) : Option (List Nat) := do
  let (n, m) ← counts o t
  let used ← (List.range len).flatMapM fun k => placeWords o t (k * n) (k * m)
  pure ((List.range (len * m)).filter fun j => !used.contains (true, j))

-- **The size formula covers the gaps.** For an object of `len ≤ 4` elements
-- with the header's counts `(n, m) = counts`, every word of every element
-- lies in its region of the `1 + len·(n + m)` words (scalar index `< len·n`,
-- trace index `< len·m`), no two elements share a word, and the words no
-- unit uses are exactly the gaps: `len·(n + m)` minus the elements' words.
#guard placements.all fun o => (pairTypes ++ fragTypes).all fun t =>
  match counts o t with
  | none => false
  | some (n, m) => (List.range 5).all fun len =>
      match (List.range len).flatMapM fun k => placeWords o t (k * n) (k * m) with
      | none => false
      | some ws =>
          ws.all (fun (tr, i) => if tr then i < len * m else i < len * n) &&
          ws.eraseDups.length == ws.length &&
          match (placeWords o t 0 0).map List.length, traceFillers o t len with
          | some w, some tf =>
              ws.length == len * w &&
              len * (n + m) - ws.length ==
                tf.length + ((List.range (len * n)).filter fun i => !ws.contains (false, i)).length
          | _, _ => false

-- The trace fillers lie inside the object (born null in the zero-filled
-- arena; no store targets them, since stores go to the words of units).
-- `CT` with the header at `base − 8` has trace fillers 0 and 3 in every
-- element; with the header before the trace region it has none.
#guard traceFillers {} CT 2 == some [0, 3, 4, 7] &&
  traceFillers { headerBeforeTrace := true } CT 2 == some [] &&
  placements.all fun o => fragTypes.all fun t => traceFillers o t 3 == some []

-- The allocator's gap makes the base `c + 8·(gap + M + 1)` a multiple of 16,
-- for every 8-aligned cursor and trace size.
#guard (List.range 8).all fun c => (List.range 6).all fun M =>
  (8 * c + 8 * (allocGap (8 * c) M + M + 1)) % 16 == 0 && allocGap (8 * c) M ≤ 1

/-! ## Headers -/

#guard wellFormed ({} : ObjLayout)

#guard (header0 {} .array 3 2).map (fun h => decode {} (h + 5 * 2 ^ lenShift {})) == some (1, 0, 3, 2, 5)

#guard header0 {} .obj (2 ^ 14) 0 == none

end Scc.Test.LayoutTest
