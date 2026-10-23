import Scc.Cert.Rt.LayoutX64
import Spike.Lib.X64

/-!
# Code at labels of a laid-out x64 program, the end address at the code's end

`Scc/Cert/Rt/LayoutX64.lean` finds blocks in an executable's whole cell
list, with its end address at the end of the cells. The canonical loader's
thread (`Scc.Sem.X64.threadAt`) lays out the code cells `cells` first, then
padding and label cells for the data symbols, and halts at the end of the
code. `Lays exe cells` is that shape (`cells` a prefix of `exe.2`), `endOf
exe cells` that end address (the x64 twins of `Scc/Cert/Rt/LayoutA64.lean`'s).

- `cellAt_prefix`: a non-label cell of the prefix is the `CellAt` at its
  address (it is short of the end of the code: every non-label cell of a
  valid layout has a positive size, and the cells do not wrap);
- `codeAt_blockAt_lays`: `blockAt cells l k off b` gives Spike's sized
  `CodeAt` of `b` at `label l + off`, in every state of the executable;
- `label_labelGap_lays`: `labelGap cells a b n off` gives
  `label b = label a + off`.

The checks only read `cells`, so a certificate decides them on the parsed
code cells alone (`Scc.Sem.X64.cellsOf`), not the thread's whole cell list.
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- **`exe` lays out the code cells `cells` first** (then any cells: the
data symbols' padding and labels). -/
def Lays (exe : _root_.Executable) (cells : List (Directive × Nat)) : Prop := ∃ ext, exe.2 = cells ++ ext

/-- The end of the code cells `cells` in `exe`: where a thread running them
halts. -/
def endOf (exe : _root_.Executable) (cells : List (Directive × Nat)) : Int64 :=
  exe.1 + .ofNat (cells.map (·.2)).sum

/-- An executable of `cells` alone lays them out. -/
theorem Lays.of_eq {exe : _root_.Executable} {cells : List (Directive × Nat)} (h : exe.2 = cells) :
    Lays exe cells := ⟨[], by simp [h]⟩

/-- In an executable of `cells` alone, they end at the end of the cells. -/
theorem endOf_of_eq {exe : _root_.Executable} {cells : List (Directive × Nat)} (h : exe.2 = cells) :
    endOf exe cells = exe.1 + .ofNat (exe.2.map (·.2)).sum := by
  rw [endOf, h]

/-- The cells of `cells` are those of `exe`. -/
theorem Lays.getElem? {exe : _root_.Executable} {cells : List (Directive × Nat)} (hp : Lays exe cells)
    {m : Nat} {c : Directive × Nat} (h : cells[m]? = some c) : exe.2[m]? = some c := by
  obtain ⟨ext, he⟩ := hp
  have hm : m < cells.length := by
    rcases Nat.lt_or_ge m cells.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h; cases h
  rw [he, List.getElem?_append_left hm, h]

theorem Lays.take {exe : _root_.Executable} {cells : List (Directive × Nat)} (hp : Lays exe cells)
    {m : Nat} (hm : m ≤ cells.length) : exe.2.take m = cells.take m := by
  obtain ⟨ext, he⟩ := hp
  rw [he, List.take_append_of_le_length hm]

private theorem sum_take_succ_le (l : List (Directive × Nat)) {m : Nat} {c : Directive × Nat}
    (hc : l[m]? = some c) : ((l.take m).map (·.2)).sum + c.2 ≤ (l.map (·.2)).sum := by
  conv => rhs; rw [← List.take_append_drop (m + 1) l]
  rw [List.take_add_one, hc]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]
  omega

/-- **A non-label cell of the code is the `CellAt` at its address**, in any
machine data. -/
theorem cellAt_prefix {st : State} [hv : Executable.ValidLayout st.exe] {cells : List (Directive × Nat)}
    (hp : Lays st.exe cells) (hend : st.endPc = endOf st.exe cells) {m : Nat} {d : Directive} {z : Nat}
    (hm : cells[m]? = some (d, z)) (hd : d.isLabel = false) (md : MachineData) :
    CellAt { st with st := (md, Kraken.Executable.addrOf st.exe m) } d z := by
  have he := hp.getElem? hm
  have hlt : m < st.exe.2.length := by
    rcases Nat.lt_or_ge m st.exe.2.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at he; cases he
  refine ⟨hv, ?_, st.exe.2.drop (m + 1), ?_⟩
  · -- short of the end of the code
    have hnl : ∀ l, d ≠ Directive.label l := by
      intro l hl; subst hl; simp [Directive.isLabel] at hd
    have hz : 0 < z := hv.instr_size m d z he hnl
    have hle := sum_take_succ_le cells hm
    have hcs : (cells.map (·.2)).sum ≤ (st.exe.2.map (·.2)).sum := by
      obtain ⟨ext, hx⟩ := hp
      rw [hx, List.map_append, List.sum_append]; omega
    have hw := hv.no_wrap
    have htk : st.exe.2.take m = cells.take m := hp.take (by
      rcases Nat.lt_or_ge m cells.length with hc | hc
      · omega
      · rw [List.getElem?_eq_none hc] at hm; cases hm)
    simp only at hle
    apply beq_false_of_ne
    intro heq
    have h4 := congrArg Int64.toBitVec heq
    simp only [hend, endOf, Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, htk, Int64.toBitVec_add,
      Int64.toBitVec_ofNat'] at h4
    have h5 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h4)
    simp only [BitVec.toNat_ofNat] at h5
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
    omega
  · show Executable.codeAt st.exe (Kraken.Executable.addrOf st.exe m) = _
    rw [Executable.codeAt_addrOf_drop st.exe (Nat.le_of_lt hlt), List.drop_eq_getElem_cons hlt,
      show st.exe.2[m] = (d, z) by rw [List.getElem?_eq_getElem hlt] at he; exact Option.some.inj he,
      List.dropWhile_cons]
    simp [hd]

/-- **A block of the run after a label is code at its address**: Spike's
sized `CodeAt` of `b` at `label l + off`, in every state of a layout of
`cells` halting at their end. -/
theorem codeAt_blockAt_lays {exe : _root_.Executable} [hv : Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} (hp : Lays exe cells) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe cells) {l : Label} {k off : Nat} {b : List (Directive × Nat)}
    (h : blockAt cells l k off b = true) :
    Spike.Lib.X64.CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat off) b := by
  subst he
  simp only [blockAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hoff⟩, hb⟩ := h
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨⟨z0, hz0⟩, hfirst⟩ := labelIdx_spec hn
  simp only [run, hn] at hoff hb
  generalize hR : (cells.drop (n + 1)).takeWhile (fun c => !c.1.isLabel) = R at hoff hb
  have hnl : n < cells.length := by
    rcases Nat.lt_or_ge n cells.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hz0; cases hz0
  have hz0' := hp.getElem? hz0
  have hzz := hv.label_size n l z0 hz0'
  subst hzz
  have hlab : (_root_.Executable.labels st.exe).label l = Kraken.Executable.addrOf st.exe n :=
    Executable.label_addrOf st.exe l n hz0' (by rw [hp.take (Nat.le_of_lt hnl)]; exact hfirst)
  -- the run, then the rest of the cells after the label
  obtain ⟨rest, hsplit⟩ : ∃ rest, cells.drop (n + 1) = R ++ rest :=
    ⟨_, by rw [← hR]; exact (List.takeWhile_append_dropWhile).symm⟩
  intro j d z hj
  have hjb : j < b.length := by
    rcases Nat.lt_or_ge j b.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hj; cases hj
  have hblen : b.length ≤ (R.drop k).length := by
    rw [← hb]; exact List.length_take_le' _ _
  have hkj : k + j < R.length := by simp at hblen; omega
  have hRj : R[k + j]? = some (d, z) := by
    rw [← hj, ← hb, List.getElem?_take_of_lt hjb, List.getElem?_drop]
  have hdl : d.isLabel = false := by
    have := mem_takeWhile (p := fun c : Directive × Nat => !c.1.isLabel) (x := (d, z))
      (by rw [hR]; exact List.mem_of_getElem? hRj)
    simpa using this
  have hcm : cells[n + 1 + (k + j)]? = some (d, z) := by
    rw [← List.getElem?_drop, hsplit, List.getElem?_append_left hkj, hRj]
  have hc := cellAt_prefix hp hend hcm hdl st.st.1
  -- its address
  have hlen : k + j ≤ (st.exe.2.drop (n + 1)).length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp (hp.getElem? hcm)
    simp only [List.length_drop]; omega
  have haddr := addrOf_past hz0' (k + j) hlen
  have htk : (st.exe.2.drop (n + 1)).take (k + j) = R.take k ++ b.take j := by
    obtain ⟨ext, hx⟩ := hp
    rw [hx, List.drop_append_of_le_length (by omega), hsplit, List.append_assoc,
      List.take_append_of_le_length (by omega), List.take_add, ← hb, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hjb)]
  rw [htk, List.map_append, List.sum_append, hoff, ← hlab] at haddr
  have hpc : (_root_.Executable.labels st.exe).label l + Int64.ofNat off + Int64.ofNat (Spike.Lib.X64.cellOff b j) =
      Kraken.Executable.addrOf st.exe (n + 1 + (k + j)) := by
    rw [haddr, Spike.Lib.X64.cellOff, Int64.add_assoc]
    congr 1
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat', ← BitVec.ofNat_add]
  rw [hpc]
  exact hc

theorem labelIdx_append {l : Label} {ext : List (Directive × Nat)} :
    ∀ {cells : List (Directive × Nat)} {n : Nat}, labelIdx cells l = some n → labelIdx (cells ++ ext) l = some n
  | [], _, h => by simp [labelIdx] at h
  | c :: cs, n, h => by
    unfold labelIdx at h ⊢
    simp only [List.cons_append]
    split at h
    · simp only [↓reduceIte, *]
    · simp only [↓reduceIte, *]
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [labelIdx_append hm]; rfl

/-- **The distance between two labels**, in a layout of `cells`. -/
theorem label_labelGap_lays {exe : _root_.Executable} [hv : Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} (hp : Lays exe cells) {a b : Label} {n off : Nat}
    (h : labelGap cells a b n off = true) :
    (_root_.Executable.labels exe).label b = (_root_.Executable.labels exe).label a + Int64.ofNat off := by
  obtain ⟨ext, hx⟩ := hp
  apply label_labelGap (exe := exe) (n := n)
  unfold labelGap at h
  split at h
  next i j hi hj =>
    obtain ⟨⟨zj, hzj⟩, -⟩ := labelIdx_spec hj
    have hjl : j < cells.length := by
      rcases Nat.lt_or_ge j cells.length with hc | hc
      · exact hc
      · rw [List.getElem?_eq_none hc] at hzj; cases hzj
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hnl⟩, hsum⟩ := h
    have htk : (exe.2.drop (i + 1)).take n = (cells.drop (i + 1)).take n := by
      rw [hx, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    unfold labelGap
    have hi' : labelIdx exe.2 a = some i := by rw [hx]; exact labelIdx_append hi
    have hj' : labelIdx exe.2 b = some (i + 1 + n) := by rw [hx]; exact labelIdx_append hj
    simp only [hi', hj', htk, hnl, hsum, BEq.rfl, Bool.and_self]
  next => simp at h

end Scc.Cert.Rt.X64
