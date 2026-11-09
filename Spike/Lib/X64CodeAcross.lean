/-
**Code across a label** (x86-64): the x86-64 twin of
`Spike/Lib/A64CodeAcross.lean`. A block `a` read from label `l` (its cells
before it `off` bytes) and the block `b` right after the next label `m` are
one sized code segment `a ++ b`, when the layout check `labelGap` puts `m`
exactly after `a` (`off` plus `a`'s sizes).

A label is 0 bytes, so splitting a run of instructions with a new label (a
return label, P5) does not move any instruction. A proof that read the run
as one `blockAt` keeps the same code fact `CodeAt … (a ++ b)` through
`codeAt_across`, with one more decided check (`labelGap`); its steps stay as
they are.

- `cellOff_append_left`, `cellOff_append_right`: the offsets of a
  concatenation's cells;
- `CodeAt.append`: a sized code segment's concatenation;
- `codeAt_across`: `a` after `label l` and `b` after `label m`, one segment;
- `codeAt_acrossB`: the same from the byte-offset checks (`blockAtB`,
  `labelGapB`);
- `codeAt_blockAcrossB`, `code_field_blockAcrossB`: the same from the one
  decided check `blockAcrossB`, and as a `Code` field at a node's pc.
-/
import Scc.Cert.Rt.LaysX64
import Scc.Cert.Rt.CodeX64

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays)

/-- The offset of a cell of the first part of a concatenation. -/
theorem cellOff_append_left (a b : List (Directive × Nat)) {j : Nat} (h : j ≤ a.length) :
    cellOff (a ++ b) j = cellOff a j := by
  unfold cellOff
  rw [List.take_append_of_le_length h]

/-- The offset of a cell of the second part of a concatenation: the first
part's sizes, then the offset in the second. -/
theorem cellOff_append_right (a b : List (Directive × Nat)) {j : Nat} (h : a.length ≤ j) :
    cellOff (a ++ b) j = (a.map (·.2)).sum + cellOff b (j - a.length) := by
  unfold cellOff
  rw [List.take_append, List.take_of_length_le h, List.map_append, List.sum_append]

/-- **A sized code segment's concatenation**: `a` at `pc`, `b` right after
its cells' sizes. -/
theorem CodeAt.append {st : State} {pc : Int64} {a b : List (Directive × Nat)} (ha : CodeAt st pc a)
    (hb : CodeAt st (pc + Int64.ofNat (a.map (·.2)).sum) b) : CodeAt st pc (a ++ b) := by
  intro j d z hd
  rw [List.getElem?_append] at hd
  split at hd
  · rename_i hj
    rw [cellOff_append_left a b (Nat.le_of_lt hj)]
    exact ha j d z hd
  · rename_i hj
    have := hb (j - a.length) d z hd
    rwa [cellOff_append_right a b (by omega), Int64.ofNat_add, ← Int64.add_assoc]

/-- **Code across a label**: the block `a` from the `k`-th cell after
`label l` (the cells before it `off` bytes), then the block `b` after
`label m`, where `m` is the first label after `l` and follows `a` directly
(`labelGap`), are one sized code segment. -/
theorem codeAt_across {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
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

/-- **Code across a label, from the byte-offset checks** (`blockAtB`,
`labelGapB`, as `Scc.Cert.Rt.X64.rtIn` gives them): `a` at `off` bytes after
`label l`, `label m` right after it, and `b` after `label m`, one segment. -/
theorem codeAt_acrossB {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {p : Nat} (hp : Lays exe cells p) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe cells p) {l m : Label} {off : Nat} {a b : List (Directive × Nat)}
    (ha : Scc.Cert.Rt.X64.blockAtB cells l off a = true)
    (hg : Scc.Cert.Rt.X64.labelGapB cells l m (off + (a.map (·.2)).sum) = true)
    (hb : Scc.Cert.Rt.X64.blockAtB cells m 0 b = true) :
    CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat off) (a ++ b) := by
  refine CodeAt.append (Scc.Cert.Rt.X64.codeAt_blockAtB hp he hend ha) ?_
  have h2 := Scc.Cert.Rt.X64.codeAt_blockAtB hp he hend hb
  rw [Scc.Cert.Rt.X64.label_labelGapB hp hg] at h2
  have e0 : Int64.ofNat 0 = 0 := rfl
  rwa [e0, Int64.add_zero, Int64.ofNat_add, ← Int64.add_assoc] at h2

/-- **Code across a label, from the one check** `blockAcrossB` (as
`Scc.Cert.Rt.X64.rtIn` gives it): `codeAt_acrossB` with its three checks read
off the Boolean conjunction. -/
theorem codeAt_blockAcrossB {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {p : Nat} (hp : Lays exe cells p) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe cells p) {l m : Label} {off : Nat} {a b : List (Directive × Nat)}
    (h : Scc.Cert.Rt.X64.blockAcrossB cells l off a m b = true) :
    CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat off) (a ++ b) := by
  simp only [Scc.Cert.Rt.X64.blockAcrossB, Bool.and_eq_true] at h
  exact codeAt_acrossB hp he hend h.1.1 h.1.2 h.2

/-- **A `Code` field across a label, from `blockAcrossB`**:
`codeAt_blockAcrossB` at the pc `q` of a node, in every state of the
executable, for the run `c` the two parts make up (`hc` is
`List.take_append_drop` for a split block). -/
theorem code_field_blockAcrossB {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {p : Nat} (hp : Lays exe cells p) {endPc : Int64}
    (hend : endPc = endOf exe cells p) {l m : Label} {off : Nat} {a b c : List (Directive × Nat)}
    (h : Scc.Cert.Rt.X64.blockAcrossB cells l off a m b = true) (hc : a ++ b = c)
    {q : Int64} (e : (_root_.Executable.labels exe).label l + Int64.ofNat off = q) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q c :=
  fun _ hs hn => e ▸ hc ▸ codeAt_blockAcrossB hp hs (hn.trans hend) h

end Spike.Lib.X64
