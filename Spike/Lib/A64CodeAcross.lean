/-
**Code across a label** (AArch64): a block `a` read from label `l` and the
block `b` right after the next label `m` are one code segment `a ++ b`, when
the layout check `labelGap` puts `m` exactly after `a`.

A label is 0 bytes, so splitting a run of instructions with a new label (a
return label, P5) does not move any instruction. A proof that read the run
as one `blockAt` keeps the same code fact `CodeAt … (a ++ b)` through
`codeAt_across`, with one more decided check (`labelGap`); its steps stay as
they are.

- `codeAt_across`: `a` after `label l` and `b` after `label m`, one segment
  (the concatenation inlined: `Spike.Lib.LowerA64.CodeAt.append` is the same
  step, in a module with many more imports; a second `CodeAt.append` here
  would be ambiguous where both namespaces are open);
- `codeAt_blockAcross`, `code_field_blockAcross`: the same from the one
  decided check `blockAcross`, and as a `Code` field at a node's pc.
-/
import Spike.Lib.A64Block
import Scc.Cert.Rt.LayoutA64

namespace Spike.Lib.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap blockAcross codeAt_blockAt label_labelGap)

/-- **Code across a label**: the block `a` from the `k`-th instruction after
`label l`, then the block `b` after `label m`, where `m` is the first label
after `l` and follows `a` directly (`labelGap`), are one code segment. -/
theorem codeAt_across {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {p : Nat} (hp : Lays exe prog p) {st : State} (he : st.exe = exe) (hend : st.endPc = endOf exe prog p)
    {l m : Label} {k : Nat} {a b : List Directive} (ha : blockAt prog l k a = true)
    (hg : labelGap prog l m (k + a.length) = true) (hb : blockAt prog m 0 b = true) :
    CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) (a ++ b) := by
  have h1 := codeAt_blockAt hp he hend ha
  have h2 := codeAt_blockAt hp he hend hb
  rw [label_labelGap hp hg] at h2
  intro j d hd
  rw [List.getElem?_append] at hd
  split at hd
  · exact h1 j d hd
  · rename_i hj
    have := h2 (j - a.length) d hd
    have hpc : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + a.length)) + Int64.ofNat (4 * 0)
        + Int64.ofNat (4 * (j - a.length)) =
        (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j) := by
      rw [Int64.add_assoc, Int64.add_assoc, ← Int64.ofNat_add, ← Int64.ofNat_add, Int64.add_assoc,
        ← Int64.ofNat_add]
      exact congrArg (_ + Int64.ofNat ·) (by omega)
    rwa [hpc] at this

/-- **Code across a label, from the one check** `blockAcross` (as
`Scc.Cert.Rt.A64.rtIn` gives it): `codeAt_across` with its three checks read
off the Boolean conjunction. -/
theorem codeAt_blockAcross {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {prog : List Directive} {p : Nat} (hp : Lays exe prog p) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe prog p) {l m : Label} {k : Nat} {a b : List Directive}
    (h : blockAcross prog l k a m b = true) :
    CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) (a ++ b) := by
  simp only [blockAcross, Bool.and_eq_true] at h
  exact codeAt_across hp he hend h.1.1 h.1.2 h.2

/-- **A `Code` field across a label, from `blockAcross`**: `codeAt_blockAcross`
at the pc `q` of a node, in every state of the executable, for the run `c`
the two parts make up (`hc` is `List.take_append_drop` for a split block). -/
theorem code_field_blockAcross {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {prog : List Directive} {p : Nat} (hp : Lays exe prog p) {endPc : Int64} (hend : endPc = endOf exe prog p)
    {l m : Label} {k : Nat} {a b c : List Directive} (h : blockAcross prog l k a m b = true) (hc : a ++ b = c)
    {q : Int64} (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = q) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q c :=
  fun _ hs hn => e ▸ hc ▸ codeAt_blockAcross hp hs (hn.trans hend) h

end Spike.Lib.A64
