/-
**A code segment across a label** (x86-64, P5): the return site's label
(between the teardown and `ret`) and the checked add's fall-through label
(between `jc` and the store) split what the emitter writes into two
label-free runs; read as one segment, the code is the same.

- `CodeAt.append`: sized segments at consecutive addresses concatenate;
- `codeAt_across_x64`: a block after a label, then the block after the next
  label (`labelGap`), are one `CodeAt` at the first block's address. The
  twin of `Spike.Lib.LowerA64.codeAt_across`.
-/
import Scc.Cert.Rt.LaysX64

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Cert.Rt.X64

namespace Spike.Lib.X64

/-- **Code segments concatenate**: `a` at `pc` and `b` right after `a`'s
bytes are `a ++ b` at `pc`. -/
theorem CodeAt.append {st : State} {pc : Int64} {a b : List (Directive × Nat)} (ha : CodeAt st pc a)
    (hb : CodeAt st (pc + Int64.ofNat ((a.map (·.2)).sum)) b) : CodeAt st pc (a ++ b) := by
  intro j d z h
  rcases Nat.lt_or_ge j a.length with hj | hj
  · rw [List.getElem?_append_left hj] at h
    have e : cellOff (a ++ b) j = cellOff a j := by
      unfold cellOff; rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
    rw [e]; exact ha j d z h
  · rw [List.getElem?_append_right hj] at h
    have e : cellOff (a ++ b) j = (a.map (·.2)).sum + cellOff b (j - a.length) := by
      unfold cellOff
      rw [List.take_append, List.take_of_length_le hj, List.map_append, List.sum_append]
    have := hb (j - a.length) d z h
    rw [e, Int64.ofNat_add, ← Int64.add_assoc]; exact this

end Spike.Lib.X64

open Spike.Lib.X64 in
/-- **A block across a label** (x86-64): the cells of `a` at `label l + off`
(`k` cells after `l`), then, at the label `m` right after them, the cells of
`b` — one code segment `a ++ b`. The x86-64 twin of `codeAt_across` (A64). -/
theorem codeAt_across_x64 {exe : _root_.Executable} [Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {p : Nat} (hp : Lays exe cells p) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe cells p) {l m : Label} {k off : Nat} {a b : List (Directive × Nat)}
    (ha : blockAt cells l k off a = true)
    (hg : labelGap cells l m (k + a.length) (off + (a.map (·.2)).sum) = true)
    (hb : blockAt cells m 0 0 b = true) :
    CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat off) (a ++ b) := by
  refine CodeAt.append (codeAt_blockAt_lays hp he hend ha) ?_
  have h2 := codeAt_blockAt_lays hp he hend hb
  rw [label_labelGap_lays hp hg] at h2
  have e0 : Int64.ofNat 0 = 0 := rfl
  rwa [e0, Int64.add_zero, Int64.ofNat_add, ← Int64.add_assoc] at h2

