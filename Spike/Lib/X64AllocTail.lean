/-
**The allocator's tail past the counter's add** (x86-64; the twin of
`Spike/Lib/A64AllocTail.lean`): `scc_rt_alloc` (`Spike/Lib/X64Alloc.lean`)
from the node `c2` after the counter's add (`lock xaddq`) on, as one
segment inside a predicate `W` asked only at the tail's nodes (`AllocWT`),
not at the add nor before it.

**No back edge to the add.** The tail's nodes `TN` (`c2`, `j2`, `slow`,
`j3`, `full`, `ok`, `f1`, `o1`, `f2`, `o2`, `s2`, `o3`, `f3`, `o4`, `f4`,
`o5`, `f5`, `o6`, `f6`, `o7`, `f7`, `o8`, `hdr`, `o9`, `ret`) are closed
under the allocator's edges: from each, the code's next node is again a
tail node or an exit (`c2 → slow | j2`, `j2 → ok`, `slow → j3` (the spin
branch dead within the cells), `j3 → full`, `full → abort`, `ok → f1 → o1 →
… → o8 → hdr → o9 → ret → return`). `seg_allocW_tailA` proves it: its node
graph is `TN` alone (`fn_segW` at `fun i => N … i.an`), each node's edge
landing at a `TN` node or an exit, so no tail node reaches `cnt` or the add
`rmw` (nor `e`, `entry`, `j1`, `c1`).

Where x86-64 differs from AArch64: the add's successor is `c2` (AArch64's
`n4`), the tail longer (the `ok` path's flag-setting single instructions
`f1`…`f7`, `s2`); the code is from the layout (`hp`, `hend`, `hin`), as in
`seg_allocW_at`.

- `TN`, `TN.an`: the tail's nodes among `AN`;
- `AllocWT`: the tail's states inside `W`, none moved by `K`; `AllocW.tail`:
  from `AllocW`;
- `seg_allocW_tailA`: the tail one segment inside `W` from any tail node to
  the heap abort alone (`EA`: the return's row is the allocation, landing in
  `xa`); `seg_allocW_tail`: to the allocator's exits.
-/
import Spike.Lib.X64Alloc

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')

set_option linter.unusedSimpArgs false

/-- **The tail's nodes**: `scc_rt_alloc`'s nodes from the counter's add's
successor `c2` on. -/
inductive TN where
  | c2 | j2 | slow | j3 | full | ok | f1 | o1 | f2 | o2 | s2 | o3 | f3 | o4 | f4 | o5 | f5 | o6 | f6 | o7
  | f7 | o8 | hdr | o9 | ret

/-- A tail node as an allocator node. -/
def TN.an : TN → AN
  | .c2 => .c2 | .j2 => .j2 | .slow => .slow | .j3 => .j3 | .full => .full | .ok => .ok | .f1 => .f1
  | .o1 => .o1 | .f2 => .f2 | .o2 => .o2 | .s2 => .s2 | .o3 => .o3 | .f3 => .f3 | .o4 => .o4 | .f4 => .f4
  | .o5 => .o5 | .f5 => .f5 | .o6 => .o6 | .f6 => .f6 | .o7 => .o7 | .f7 => .f7 | .o8 => .o8 | .hdr => .hdr
  | .o9 => .o9 | .ret => .ret

section Spec

variable (ms : MemSide isa) (q : Call)

/-- **The tail's states inside `W`**, none moved by `K`: `AllocW`'s
obligations at the tail's nodes only. -/
structure AllocWT (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  c2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .c2) bC2
  j2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .j2) bJ2
  slow : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .slow) bSlow
  j3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .j3) bJ3
  full : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .full) bFull
  ok : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok) bO0
  f1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f1)
  o1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o1) bO1
  f2 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f2)
  o2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o2) bO2
  s2 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .s2)
  o3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o3) bO3
  f3 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f3)
  o4 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o4) bO4
  f4 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f4)
  o5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o5) bO5
  f5 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f5)
  o6 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o6) bO6
  f6 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f6)
  o7 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o7) bO7
  f7 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f7)
  o8 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o8) bO8
  hdr : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .hdr)
  o9 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o9) bO9
  ret : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ret)

variable {ms q}

/-- **`AllocW`'s tail.** -/
theorem AllocW.tail {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} (h : AllocW ms q W K exe endPc R F) :
    AllocWT ms q W K exe endPc R F :=
  ⟨h.c2, h.j2, h.slow, h.j3, h.full, h.ok, h.f1, h.o1, h.f2, h.o2, h.s2, h.o3, h.f3, h.o4, h.f4, h.o5, h.f5,
    h.o6, h.f6, h.o7, h.f7, h.o8, h.hdr, h.o9, h.ret⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {q : Call} {cells : List (Directive × Nat)}

set_option hygiene false in
/-- A block node at `l + k`: the block, its `okBlk`, its `W` obligation; the
edge is left. -/
local macro "anode " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax`, at `okL + k`
(`z` bytes), to node `j`; the invariant's facts are left. -/
local macro "fnode " fi:term:max k:term:max z:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine flag_ndW (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := okL) (off := $k) rfl) $w
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **The tail's exits**: the allocator's heap abort (`E`'s), and no state
at its return (`ret`'s row is the allocation, landing in `xa`). -/
def EA (lab : Label → Int64) (ms : MemSide isa) (q : Call) (lbl : WeakMem.AllocLabel → Option Nat) :
    AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oR, fun _ _ => False⟩
  | .abort => E lab ms q lbl .abort

/-- **`scc_rt_alloc`'s tail is one segment inside `W` from any tail node
`i0` to its heap abort alone**, `W` asked at the tail's nodes only
(`AllocWT`): the node graph is `TN` (no tail node reaches the counter's add,
the module's note), each node's edge as `seg_allocW_at`'s; the return's row
is the allocation (`alloc_ndW`), whose successor is in `ms.xa` (`hxa`), so
no state leaves at the return. -/
theorem seg_allocW_tailA {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocWT ms q W K exe endPc R F) (i0 : TN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0.an))
      (At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl .abort)) := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  have hk := Call.k_toNat hq.n_lt
  have hu := Call.u_toNat hq.units
  have hcl := hq.cells
  have hU := hq.units
  refine (fn_segW (N := fun i : TN => N _ ms q i.an) (E := EA (_root_.Executable.labels exe).label ms q lbl)
    (fun i => ?_) i0).mono_post ?_
  rotate_left
  · rintro s c ⟨x, h⟩
    cases x
    · obtain ⟨-, -, -, -, -, -, -, ⟨⟩⟩ := h
    · exact h
  cases i
  case c2 =>
    anode bC2 bC2_ok cntL 24 hW.c2
    dsimp only [TN.an, N] at hJ ⊢
    rw [bC2_run]
    obtain ⟨o, rfl, ho, ⟨h0, h8, h16, h24, h32⟩, hn28, hax, hlo⟩ := hJ
    have hr : (σ.regs.rax.toNat : Int) = o.toNat := by rw [← hax]; rfl
    have hol := o.isLt
    rw [h32, hax, hr, hu]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      have hlt : ms.cells < o.toNat + ms.units q.n q.τ := by
        rw [hcl]
        by_cases he : ms.units q.n q.τ + o.toNat = 4194304
        · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits, hu] at he ⊢
          omega
        · omega
      refine .inl ⟨TN.slow, rfl, rfl, o, rfl, ho, hlt, ?_, ?_⟩
      · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
      · simp [upd_apply]
    · rename_i h
      have hle : o.toNat + ms.units q.n q.τ ≤ ms.cells := by
        rw [hcl]
        by_cases he : ms.units q.n q.τ + o.toNat = 4194304
        · omega
        · refine Decidable.byContradiction fun hc => h ⟨by omega, fun h' => he ?_⟩
          have := congrArg BitVec.toNat h'
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits, hu] at this
          omega
      refine .inl ⟨TN.j2, ofNat_add' _ 24 35, rfl, o, rfl, hle, ?_, hn28, ?_, hlo⟩
      · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
      · simp [upd_apply]
  case j2 =>
    anode bJ2 bJ2_ok cntL 59 hW.j2
    dsimp only [TN.an, N] at hJ ⊢
    rw [bJ2_run]
    exact .inl ⟨TN.ok, rfl, rfl, hJ⟩
  case slow =>
    anode bSlow bSlow_ok slowL 0 hW.slow
    dsimp only [TN.an, N] at hJ ⊢
    rw [bSlow_run]
    obtain ⟨o, hJ⟩ := hJ
    have ⟨_, ho, _, _, h48⟩ := hJ
    rw [h48]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      refine absurd (BitVec.eq_of_toNat_eq ?_) h2
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Width.bits] at h1 ⊢
      have := o.isLt
      omega
    · exact .inl ⟨TN.j3, rfl, rfl, o, hJ⟩
  case j3 =>
    anode bJ3 bJ3_ok slowL 16 hW.j3
    dsimp only [TN.an, N] at hJ ⊢
    rw [bJ3_run]
    obtain ⟨o, hc, ho, hx, -⟩ := hJ
    exact .inl ⟨TN.full, rfl, rfl, .inr ⟨o, hc, ho, hx⟩⟩
  case full =>
    anode bFull bFull_ok fullL 0 hW.full
    dsimp only [TN.an, N] at hJ ⊢
    rw [bFull_run]
    exact .inr ⟨AX.abort, rfl, rfl, by simp [Reg64s.set64, Reg64s.get64], hJ⟩
  case ok =>
    anode bO0 bO0_ok okL 0 hW.ok
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO0_run]
    obtain ⟨o, rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩ := hJ
    refine .inl ⟨TN.f1, rfl, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo]
  case f1 =>
    fnode (.shr_cl .rax) 11 3 TN.o1 hW.f1
    obtain ⟨o, hJo, ha, hc⟩ := hJ
    exact ⟨o, hJo, (shr_rax ha hc fl).trans (by rw [cl_vals.1])⟩
  case o1 =>
    anode bO1 bO1_ok okL 14 hW.o1
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO1_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ha⟩ := hJ
    refine .inl ⟨TN.f2, ofNat_add' _ 14 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, ha]
  case f2 =>
    fnode (.and_rr .rax .rcx) 29 3 TN.o2 hW.f2
    obtain ⟨o, hJo, ha, hc⟩ := hJ
    exact ⟨o, hJo, and_rax ha hc fl⟩
  case o2 =>
    anode bO2 bO2_ok okL 32 hW.o2
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO2_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ha⟩ := hJ
    refine .inl ⟨TN.s2, ofNat_add' _ 32 4, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, ha]
  case s2 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_heap") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := okL) (off := 36) rfl) hW.s2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.o3, ofNat_add' _ 36 7, rfl, ?_⟩⟩
    obtain ⟨o, hJo, h72⟩ := hJ
    exact ⟨o, hJo, h72, by simp [SI.step, SI.regs, Reg64s.set64]⟩
  case o3 =>
    anode bO3 bO3_ok okL 43 hW.o3
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO3_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h72, ha⟩ := hJ
    refine .inl ⟨TN.f3, ofNat_add' _ 43 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h72, ha]
  case f3 =>
    fnode (.shl_cl .rax) 58 3 TN.o4 hW.f3
    obtain ⟨o, hJo, h72, h80, ha, hc⟩ := hJ
    exact ⟨o, hJo, h72, h80, (shl_rax ha hc fl).trans (by rw [cl_vals.2.1])⟩
  case o4 =>
    anode bO4 bO4_ok okL 61 hW.o4
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO4_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h72, h80, ha⟩ := hJ
    refine .inl ⟨TN.f4, ofNat_add' _ 61 27, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h72, h80, ha, BitVec.add_comm]
  case f4 =>
    fnode (.imul_rr .rax .rcx) 88 4 TN.o5 hW.f4
    obtain ⟨o, hJo, h96, ha, hc⟩ := hJ
    exact ⟨o, hJo, h96, imul_rax ha hc fl⟩
  case o5 =>
    anode bO5 bO5_ok okL 92 hW.o5
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO5_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h96, ha⟩ := hJ
    refine .inl ⟨TN.f5, ofNat_add' _ 92 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h96, ha]
  case f5 =>
    fnode (.shl_cl .rax) 107 3 TN.o6 hW.f5
    obtain ⟨o, hJo, h96, ha, hc⟩ := hJ
    exact ⟨o, hJo, h96, (shl_rax ha hc fl).trans (by rw [cl_vals.2.2.1])⟩
  case o6 =>
    anode bO6 bO6_ok okL 110 hW.o6
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO6_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h96, ha⟩ := hJ
    refine .inl ⟨TN.f6, ofNat_add' _ 110 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h96, ha]
  case f6 =>
    fnode (.shl_cl .rax) 125 3 TN.o7 hW.f6
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    exact ⟨o, hJo, hb, (shl_rax ha hc fl).trans (by rw [cl_vals.2.2.2])⟩
  case o7 =>
    anode bO7 bO7_ok okL 128 hW.o7
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO7_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩, ha⟩ := hJ
    refine .inl ⟨TN.f7, ofNat_add' _ 128 12, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h96, h112, ha]
  case f7 =>
    fnode (.or_rr .rax .rcx) 140 3 TN.o8 hW.f7
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    exact ⟨o, hJo, hb, or_rax ha hc fl⟩
  case o8 =>
    anode bO8 bO8_ok okL 143 hW.o8
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO8_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩, ha⟩ := hJ
    refine .inl ⟨TN.hdr, ofNat_add' _ 143 27, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h96, h112, ha, BitVec.add_comm]
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := okL) (off := 170) rfl) hW.hdr fun m σ c _ hD hJ => ?_
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    have ⟨_, hle, _, hn28, _, hlo⟩ := hJo
    have hra : bAddr σ.regs .rcx 0 = H (_root_.Executable.labels exe).label + o <<< 4 + (q.k * mOf q.h) <<< 3 := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hAeq : (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, base_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = bAddr σ.regs .rcx 0 := by
      rw [← hAeq]; simp
    obtain ⟨hrt, hmp, hG⟩ := hq.hdr o.toNat hlo hle
    have hv : σ.regs.get64 .rax = q.hdr := ha
    refine ⟨hAeq ▸ hrt, hofn ▸ hmp, ?_, hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) _ hD, c, .refl c,
      .inl ⟨TN.o9, ofNat_add' _ 170 3, rfl, o, hJo, hb⟩⟩
    rw [← hofn, hv]
    exact hG
  case o9 =>
    anode bO9 bO9_ok okL 173 hW.o9
    dsimp only [TN.an, N] at hJ ⊢
    rw [bO9_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩⟩ := hJ
    refine .inl ⟨TN.ret, ofNat_add' _ 173 53, rfl, o, rfl, hle, hn28, ?_, ?_, ?_, hlo⟩
    · simp [Reg64s.set64, Reg64s.get64, h96, h112]
      ac_rfl
    · simp [Reg64s.set64, Reg64s.get64, h8]
    · simp [upd_apply, h0]
  case ret =>
    refine alloc_ndW (Ea ms q) (a := .ret) (z := 1) (lo := -160) (hi := 8) rfl (by rintro w op ⟨⟩) hF
      hR hlo hhi (code_field hp hend (by simp only [hin']) (l := okL) (off := 226) rfl) hxa hW.ret
      fun σ c hJ => ?_
    obtain ⟨o, rfl, hle, hn28, h0, h29, h30, hlo⟩ := hJ
    have hA : σ.regs.rax.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
      rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk, hq.off]
    obtain ⟨us, hus⟩ := hq.accs
    refine ⟨σ.regs.rax.toBitVec, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, TermRun.cst (.num o.toNat), o.toNat, us,
      hq.term, hq.ev, hq.num, rfl, rfl, hA, hle, hus, fun l ini _ =>
        ⟨?_, rfl, ini, o.toNat, rfl, ?_, hA, hle, hlo, ?_, us, hus, rfl⟩⟩
    · simp [TN.an, N, Ea, AI.tgt, h30]
    · simp [iRet, AI.step, Reg64s.set64, Reg64s.get64]
    · simp [iRet, AI.step, Reg64s.set64, Reg64s.get64, h29]

/-- **`scc_rt_alloc`'s tail is one segment inside `W` from any tail node
`i0`** to its return or its heap abort, `W` asked at the tail's nodes only
(`AllocWT`): `seg_allocW_tailA`, the abort one of the exits. -/
theorem seg_allocW_tail {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocWT ms q W K exe endPc R F) (i0 : TN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0.an))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  (seg_allocW_tailA hp hend hin hF hR hlo hhi hq hmem hxa hW i0).mono_post fun _ _ h => ⟨.abort, h⟩

end Proof

/-- info: 'Spike.Lib.X64.Alloc.AllocW.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocW.tail

/-- info: 'Spike.Lib.X64.Alloc.seg_allocW_tailA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_allocW_tailA

/-- info: 'Spike.Lib.X64.Alloc.seg_allocW_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_allocW_tail

end Spike.Lib.X64.Alloc
