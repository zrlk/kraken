/-
**The x86-64 runtime's segments, parametric in the program**: the hand
`alloc_tcb_segW`, `stack_take_segW`, `thread_init_segW` and the
`scc_rt_start` pieces (`Spike/Lib/X64Ret0.lean`) with the code checks
(`allocTcbIn cells`, ...) premises instead of their `ret0` instances, and
`scc_rt_main` parametric (`mainU_segW`), so that each is proved once. The
x86-64 twin of `Spike/Lib/Rt/A64Segs.lean`.

- The proofs are the hand ones; only the code premises move. The node
  obligations (`TcbW`, `TakeW`, `TiW`, `St0W`, `X0W`) and the memory-side
  facts (`StOk`, `TcbOk`, `TakeOk`) stay premises; their discharge over the
  placement check is later work.
- **From the switch on** (`startSwitchU_segW`): the switch into a new
  region of depth `L`, `call scc_rt_main` (`call_nd_FWK`, its callee's
  region `8` below the new top, as in the hand proof), then `mainU_segW`
  with `scc_rt_main`'s own obligations (`MainUW`) and the user function's
  interface (`UserCallW`) as premises (`SwUW`).
- **`scc_rt_start` whole** (`startU_segW`): `startX0_segW`, then
  `startX0Sw_segW` (the take nested), then `startSwitchU_segW`.
- **Oracle**: on `ret0` the hand theorems follow from these with the hand
  code checks (`Spike/Lib/Rt/X64SegsRet0.lean`).

Where x86-64 differs from AArch64: `scc_rt_start`'s pieces follow the hand
x86-64 proof (`.x0`, then `.x0` to the switch through `.x1`), and
`scc_rt_main` is entered by a `call` (its region the callee's of the new
stack's region), so `MainUW` and `UserCallW` are asked in that callee's
region; there is no `tiSpIn`; `_start` is not here (its x86-64 segment,
`entry_segW'`, is in `Spike/Lib/Rt/X64Entry.lean`).
-/
import Spike.Lib.Rt.X64Main

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_alloc_tcb` -/

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W`: the block, its `okBlk`, its code, its
obligation; the edge is left. -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _)) $w
      fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax` inside `W`, at `l + k`
(`z` bytes), to node `j`, its obligation `w`; the invariant's facts are left. -/
local macro "fnodeW " fi:term:max l:term:max k:term:max z:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine flag_ndW (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) rfl) $w
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **`scc_rt_alloc_tcb` is one segment inside `W`** (`alloc_tcb_seg`, its
states' obligations `hW`): in any valid layout of any cells with its code (`hin`), from its
entry to its return, for any region holding its frame of 176, the saved
`%rbp` and the return address, and any frame condition implying `F0`,
given: room for the TCB below `2^17` (`hn`), the header word's facts
(`hhdr`), and the counter's add's (`htcb`). -/
theorem allocTcb_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : AllocTcb.allocTcbIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) (hW : ∀ i, TcbW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, AllocTcb.fiAt, AllocTcb.siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := AllocTcb.fnL) (b := AllocTcb.entryL) (off := 19) hp (by simp only [hin'])
  have pv := AllocTcb.path_vals
  refine fn_segW (N := tcbN _ q) (E := tcbX _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 20 (hW TN.j1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ1_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.len, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case len =>
    tnodeW AllocTcb.atL0 AllocTcb.atL0_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL0_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.shr1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr1 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 11 3 TN.l1 (hW TN.shr1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.1⟩
  case l1 =>
    tnodeW AllocTcb.atL1 AllocTcb.atL1_ok AllocTcb.lenL 14 (hW TN.l1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL1_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and1, by rw [h1]; exact ofNat_add' _ 14 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and1 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 29 3 TN.l2 (hW TN.and1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.1⟩
  case l2 =>
    tnodeW AllocTcb.atL2 AllocTcb.atL2_ok AllocTcb.lenL 32 (hW TN.l2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL2_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shr2, by rw [h1]; exact ofNat_add' _ 32 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr2 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 47 3 TN.l3 (hW TN.shr2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.2.2.1⟩
  case l3 =>
    tnodeW AllocTcb.atL3 AllocTcb.atL3_ok AllocTcb.lenL 50 (hW TN.l3)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL3_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and2, by rw [h1]; exact ofNat_add' _ 50 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and2 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 65 3 TN.l4 (hW TN.and2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.2.2.1⟩
  case l4 =>
    tnodeW AllocTcb.atL4 AllocTcb.atL4_ok AllocTcb.lenL 68 (hW TN.l4)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL4_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul1, by rw [h1]; exact ofNat_add' _ 68 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul1 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.lenL 95 4 TN.l5 (hW TN.imul1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.imul_rax ha hc fl).trans pv.2.2.2.2.1⟩
  case l5 =>
    tnodeW AllocTcb.atL5 AllocTcb.atL5_ok AllocTcb.lenL 99 (hW TN.l5)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL5_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl1, by rw [h1]; exact ofNat_add' _ 99 33, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl1 =>
    fnodeW (.shl_cl .rax) AllocTcb.lenL 132 3 TN.l6 (hW TN.shl1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.1⟩
  case l6 =>
    tnodeW AllocTcb.atL6 AllocTcb.atL6_ok AllocTcb.lenL 135 (hW TN.l6)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atL6_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.lea1, by rw [h1]; exact ofNat_add' _ 135 4, by rw [h2]; rfl, rfl, h3⟩
  case lea1 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned_next") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 139) rfl) (hW TN.lea1)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ofNat_add' _ 139 7, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 146 (hW TN.arg)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.rmw, by rw [h1]; exact ofNat_add' _ 146 12, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 158) rfl) htcb.own (hW TN.rmw)
      fun m σ c _ hD hJ => ?_
    dsimp only [tcbN] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pnA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.tcbLen := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htcb.next.rt, htcb.next.mp, htcb.next.G, htcb.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TN.bnd, ofNat_add' _ 158 5, rfl, rfl, by simpa [ownStep, AllocTcb.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 163 (hW TN.bnd)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walk (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨TN.j2, by rw [h1]; exact ofNat_add' _ 163 35, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 198 (hW TN.j2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ2_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.ok, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 0) (ofNat_zero' _)) (hW TN.ok)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.o1, ?_, rfl, ?_⟩⟩
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case o1 =>
    tnodeW AllocTcb.atO1 AllocTcb.atO1_ok AllocTcb.okL 7 (hW TN.o1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO1_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul2, by rw [h1]; exact ofNat_add' _ 7 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul2 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.okL 34 4 TN.o2 (hW TN.imul2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.imul_rax ha hc fl).trans pv.2.2.2.2.2.2.1⟩
  case o2 =>
    tnodeW AllocTcb.atO2 AllocTcb.atO2_ok AllocTcb.okL 38 (hW TN.o2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO2_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl2, by rw [h1]; exact ofNat_add' _ 38 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl2 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 53 3 TN.o3 (hW TN.shl2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2.2.1⟩
  case o3 =>
    tnodeW AllocTcb.atO3 AllocTcb.atO3_ok AllocTcb.okL 56 (hW TN.o3)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO3_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl3, by rw [h1]; exact ofNat_add' _ 56 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl3 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 74 3 TN.o4 (hW TN.shl3)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2.2.2⟩
  case o4 =>
    tnodeW AllocTcb.atO4 AllocTcb.atO4_ok AllocTcb.okL 77 (hW TN.o4)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO4_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.or1, by rw [h1]; exact ofNat_add' _ 77 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case or1 =>
    fnodeW (.or_rr .rax .rcx) AllocTcb.okL 95 3 TN.o5 (hW TN.or1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.or_rax ha hc fl⟩
  case o5 =>
    tnodeW AllocTcb.atO5 AllocTcb.atO5_ok AllocTcb.okL 98 (hW TN.o5)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO5_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.hdr, by rw [h1]; exact ofNat_add' _ 98 42, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 140) rfl) (hW TN.hdr)
      fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pinA (_root_.Executable.labels exe).label + q.n0 := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.hdr0 ||| 1#64 <<< 36 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨hhdr.rt, hhdr.mp, hhdr.G, hhdr.unmapped m (hFF m hD), q.c0,
      .refl q.c0, .inl ⟨TN.ret, ofNat_add' _ 140 3, rfl, rfl, hJ⟩⟩
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 143 (hW TN.ret)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


end TcbProof

/-! ## `scc_rt_stack_take` -/

section TakeProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_stack_take` inside `W`: the block, its `okBlk`,
its code, its obligation; the edge is left. -/
local macro "knodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at a label's address into `%rax` at `l + k`, to node `j`, inside
`W`; the invariant's facts are left. -/
local macro "lnodeW " L:term:max l:term:max k:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine si_ndW (si := .leaRip .rax $L) (z := 7) rfl hFb
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, .inl ⟨$j, ?_, rfl, ?_⟩⟩)



/-- **`scc_rt_stack_take` is one segment inside `W`, the take its outside
move**: `stack_take_seg` with the take site the kernel's take of `rS`
(`TakeK`, `take_ndW`) instead of a `nop`, so at the return `rS` is in
private memory (`StackM`). Given the node obligations (`hW`), the region's
cells off `rS` (`hRS`), every aligned word of `rS` off the region (`hout`),
and the frame condition kept by the take (`hFt`). -/
theorem stackTake_segW {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TakeW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS)
      q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e))
      (fun s c => ∃ x, At exe endPc R (fun m => F m ∧ StackM rS m)
        (takeXG (_root_.Executable.labels exe).label q true x) s c) := by
  have hin' := hin
  simp only [StackTake.stackTakeIn, AllocTcb.siAt, unlBlk_eq, swpBlk_eq, ldnBlk_eq, nxtBlk_eq,
    Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := StackTake.fnL) (b := StackTake.entryL) (off := 15) hp (by simp only [hin'])
  have eSite := label_labelGapB (a := StackTake.takenL) (b := StackTake.siteL) (off := 11) hp (by simp only [hin'])
  let lab := (_root_.Executable.labels exe).label
  have hAbs : ∀ {m : MachineData} {σ : AS} {pm : _root_.Mem 64}, Abs R StackTake.oI m σ →
      Abs R StackTake.oI (takeMem pm rS m) σ := fun hA =>
    ⟨hA.regs, hA.zmms, hA.status, hA.so, fun k hk => by rw [loadInt_takeMem (hRS k hk)]; exact hA.slot k hk⟩
  have hSM := stackM_stable hfit hout
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := takeNG lab q) (E := takeXG lab q)
    (fun b i => ?_) false TK.e).mono_pre fun s c h => ?_).mono_post fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, rfl, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  have hWb : ∀ i, TakeW W (TakeK (lab StackTake.siteL) rS) exe endPc R (takeF F rS b) (StackM rS) q i :=
    fun i => (hW i).mono fun m h => h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    knodeW StackTake.stPro StackTake.stPro_ok StackTake.fnL 0 (hWb TK.e)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    knodeW StackTake.stInit StackTake.stInit_ok StackTake.entryL 0 (hWb TK.entry)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stInit_walk lab _ hJ
    exact .inl ⟨TK.cls, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case cls =>
    refine seg_fixW b ?_
    knodeW StackTake.stCls StackTake.stCls_ok StackTake.clsL 0 (hWb TK.cls)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stCls_walk lab _ hJ
    exact .inl ⟨TK.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 13 (hWb TK.j1)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ1_walk lab _ hJ
    exact .inl ⟨TK.d0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case d0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_free_n" StackTake.doneL 0 TK.d7 (hWb TK.d0)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 7 (hWb TK.d7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ ha
    exact .inl ⟨TK.d26, by rw [h1]; exact ofNat_add' _ 7 19, by rw [h2]; rfl, rfl, h3⟩
  case d26 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_free" StackTake.doneL 26 TK.d33 (hWb TK.d26)
    · exact ofNat_add' _ 26 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ⟩
  case d33 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFree StackTake.stFree_ok StackTake.doneL 33 (hWb TK.d33)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d52, by rw [h1]; exact ofNat_add' _ 33 19, by rw [h2]; rfl, rfl, h3⟩
  case d52 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_lock" StackTake.doneL 52 TK.d59 (hWb TK.d52)
    · exact ofNat_add' _ 52 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d59 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLock StackTake.stLock_ok StackTake.doneL 59 (hWb TK.d59)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ ha
    exact .inl ⟨TK.sp0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case sp0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSwp StackTake.stSwp_ok StackTake.spinL 0 (hWb TK.sp0)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSwp_walk lab _ hJ
    exact .inl ⟨TK.swp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case swp =>
    refine seg_fixW b ?_
    refine ownXchg_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.spinL) (off := 11) rfl) htk.ownLock
      (hWb TK.swp) fun m σ c _ hD hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = lockA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htk.lock1.rt, htk.lock1.mp, htk.lock1.G, htk.lock1.unmapped m (hFFb m hD),
      q.c0, .refl q.c0,
        .inl ⟨TK.sp14, ofNat_add' _ 11 3, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case sp14 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 14 (hWb TK.sp14)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ ha
    exact .inl ⟨TK.lk0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case lk0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLdN StackTake.stLdN_ok StackTake.lockedL 0 (hWb TK.lk0)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := StackTake.stLdN_walk lab _ hJ
    exact .inl ⟨TK.ldn, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case ldn =>
    refine seg_fixW b ?_
    refine ownLd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.lockedL) (off := 4) rfl) htk.ownFreeN
      (hWb TK.ldn) fun m σ c _ hD hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = freeNA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    rw [hb]
    exact ⟨rfl, htk.freeN.rt, htk.freeN.mp, htk.freeN.unmapped m (hFFb m hD),
      q.c0, .refl q.c0,
        .inl ⟨TK.lk7, ofNat_add' _ 4 3, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case lk7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 7 (hWb TK.lk7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ ha
    exact .inl ⟨TK.b0, h1.symm, by rw [h2]; rfl, rfl, h3.mono (StackTake.s3_s0 _ _ _)⟩
  case b0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_lock" StackTake.bumpL 0 TK.b7 (hWb TK.b0)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 7 (hWb TK.b7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ ha
    exact .inl ⟨TK.unl, by rw [h1]; exact ofNat_add' _ 7 21, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine seg_fixW b ?_
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 28) rfl)
      (hWb TK.unl) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = lockA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 0#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨htk.lock0.rt, htk.lock0.mp, htk.lock0.G, htk.lock0.unmapped m (hFFb m hD),
      q.c0,
      .refl q.c0, .inl ⟨TK.b31, ofNat_add' _ 28 3, rfl, rfl, hJ⟩⟩
  case b31 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_next" StackTake.bumpL 31 TK.b38 (hWb TK.b31)
    · exact ofNat_add' _ 31 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b38 =>
    refine seg_fixW b ?_
    knodeW StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 38 (hWb TK.b38)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ ha
    exact .inl ⟨TK.nxt, by rw [h1]; exact ofNat_add' _ 38 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine seg_fixW b ?_
    refine ownXadd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 56) rfl) htk.ownNext
      (hWb TK.nxt) fun m σ c _ hD hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, hc, ha⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = nextA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = StackTake.size0 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htk.next.rt, htk.next.mp, htk.next.G, htk.next.unmapped m (hFFb m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TK.b61, ofNat_add' _ 56 5, rfl, rfl, by simpa [ownStep, StackTake.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case b61 =>
    refine seg_fixW b ?_
    knodeW StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 61 (hWb TK.b61)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ ha hk
    exact .inl ⟨TK.b108, by rw [h1]; exact ofNat_add' _ 61 47, by rw [h2]; rfl, rfl, h3⟩
  case b108 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 108 (hWb TK.b108)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ2_walk lab _ hJ
    exact .inl ⟨TK.ok0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stacks" StackTake.okL 0 TK.ok7 (hWb TK.ok0)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case ok7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stOk StackTake.stOk_ok StackTake.okL 7 (hWb TK.ok7)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ ha
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    refine seg_fixW b ?_
    knodeW StackTake.stSite StackTake.stSite_ok StackTake.takenL 0 (hWb TK.tk)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine seg_movedW (j := TK.ret) ((take_ndW (n' := takeNG lab q true TK.ret) rfl
      (code_field hp hend (by simp only [nopBlk, hin']) (l := StackTake.siteL) (off := 0) (ofNat_zero' _))
      (hWb TK.site) (fun m σ pm hA hD => ⟨hAbs hA, hFt m pm hD.1, fun _ => stackM_takeMem⟩)
      fun σ c hJ => ⟨rfl, c, .refl c, rfl, hJ.1, hJ.2.1⟩).mono_post fun _ _ h => ⟨true, h⟩)
  case ret =>
    cases b
    · exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => Bool.false_ne_true h
    refine seg_fixW true ?_
    knodeW StackTake.stRet StackTake.stRet_ok StackTake.siteL 1 (blkW_mono (F := fun m => F m ∧ StackM rS m)
      (F' := takeF F rS true) (hW TK.ret) fun m h => ⟨h.1, h.2 rfl⟩)
    dsimp only [takeNG, takeXG] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩


end TakeProof

/-! ## `scc_rt_thread_init` -/

section TiWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_init` inside `W`. -/
local macro "inodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR (by omega) hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at the store of field `i` (`8·i(%rcx)`, `z` bytes) at `.x7 + k`,
to node `j`, inside `W`, after the take. -/
local macro "snodeW " i:term:max d:term:max k:term:max z:term:max v:term:max j:term:max w:term:max : tactic =>
  `(tactic| (
    refine rtst_ndW (b := .rcx) (k := $d) (r := .rax) (z := $z)
      (code_field hp hend (by simp only [hin']) (l := ThreadInit.x7L) (off := $k) rfl) $w
      fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, ha, hc⟩ := hJ
    have hfi := hfld (8 * $i, $v) (by simp [ThreadInit.fields])
    rw [bAddr_rcx hc, show BitVec.ofInt 64 (Int64.toInt $d) = BitVec.ofNat 64 (8 * $i) by decide,
      show σ.regs.get64 .rax = σ.regs.rax.toBitVec from rfl, ha]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0,
      .refl q.c0, .inl ⟨$j, ofNat_add' _ $k $z, rfl, rfl, rfl, hJ⟩⟩))

/-- **`scc_rt_thread_init` is one segment inside `W`, the take its outside
move**: `thread_init_seg` with `stackTake_segW` at the call, so at the
return the stack range `rS` is in private memory (`StackM`). Given the node
obligations (`hW`), the region's cells off `rS` (`hRS`), every aligned word
of `rS` off the region (`hout`), and the frame condition kept by the take
(`hFt`). -/
theorem threadInit_segW {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [ThreadInit.threadInitIn, ThreadInit.storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_left,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := ThreadInit.fnL) (b := ThreadInit.entryL) (off := 12) hp (by simp only [hin'])
  have eX7 := label_labelGapB (a := ThreadInit.entryL) (b := ThreadInit.x7L) (off := 12) hp (by simp only [hin'])
  have hcall : blockAtB cells ThreadInit.entryL 7 tiCall = true :=
    (by simp only [hin'] : blockAtB cells ThreadInit.entryL 7 ThreadInit.callBlk = true)
  let lab := (_root_.Executable.labels exe).label
  have hSM := stackM_stable hfit hout
  -- the take's callee region, and `rS` off it
  have hb' := Region.callee_base (hi' := 8) hR (show R.lo ≤ (-48 - 0) + -200 by omega) (by decide)
    (show (-48 - 0 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48 - 0) (-200) 8).Off k → ∀ i < 8,
      (R.callee (-48 - 0) (-200) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ (-48 - 0) + -200 by omega) (show (-48 - 0 : Int) + 8 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48 - 0) (-200) 8).base.toNat + (R.callee (-48 - 0) (-200) 8).lo ∨
        ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + (R.callee (-48 - 0) (-200) 8).hi ≤ a :=
    fun a h8 ha ha7 => by
      show (a : Int) + 8 ≤ ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + -200 ∨
        ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + 8 ≤ a
      rcases hout a h8 ha ha7 with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := tiNG (_root_.Executable.labels exe).label q) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0 (blkW_mono (hW TI.e) fun m h => h.1)
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiArg ThreadInit.tiArg_ok ThreadInit.entryL 0 (blkW_mono (hW TI.entry) fun m h => h.1)
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := ThreadInit.tiArg_walk lab _ hJ
    exact .inl ⟨TI.c7, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case c7 =>
    refine seg_fixW b ?_
    refine seg_ndW (by simp [tiCall]) tiCall_ok hFb hR (by omega) hhi
      (code_field hp hend hcall rfl) (blkW_mono (hW TI.c7) fun m h => h.1) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, ⟨hsp, hfp, hs⟩, hdi⟩ := hJ
    rw [tiCall_run]
    refine .inl ⟨TI.call, rfl, rfl, ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p hp'
      have hp48 : p.1 ≠ -48 := by
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> simp
      simp only [upd_apply, hp48, ↓reduceIte]
      exact hs p hp'
    · simp [Reg64s.set64, hsp]; bv_omega
    · simp [Reg64s.set64, hfp]
    · simp [Reg64s.set64, hdi]
    · simp only [upd_apply, ↓reduceIte]
      rw [eX7, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
  case call =>
    refine seg_fixW true ?_
    refine call_nd_FW (e0 := 0) (lo' := -200) (hi' := 8) (M := StackM rS)
      (Ne := fun g => takeNG lab (tiTake q g) false .e) (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hFb (by show R.lo ≤ -48 - 0 + -200; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h.1, fun _ => hM⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab ThreadInit.x7L).toBitVec := by
          have e : lab ThreadInit.x7L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (stackTake_segW hp hend hst hF' hR' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk htk
          (fun i => (hW TI.call g' hr i).mono fun m h => (hFF' m h).1) hRS' hfit hout'
          (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, -, -, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hs, hsp, hfp, -⟩, h48⟩ ⟨-, hsp', hfp', hra', -⟩ ⟨-, rfl, hPost⟩ hregs - - hslot
      have hk' : ∀ k : Int, k % 8 = 0 → R.lo ≤ k → k + 8 ≤ R.hi → -48 < k → σR.slot k = σC.slot k :=
        fun k h1 h2 h3 h4 => hslot k ⟨h1, h2, h3⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiNG, tiN] at h; omega
      refine .inl ⟨TI.x7, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, rfl, rfl, ⟨?_, ?_, ?_⟩,
        ?_⟩
      · show lab ThreadInit.x7L = Int64.ofBitVec g.ra
        rw [← hra']
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · show σR.regs.rsp.toBitVec = _
        rw [hregs, hPost.1, ← hsp']
        show σC.regs.rsp.toBitVec + 8#64 = _
        rw [hsp]; bv_omega
      · show σR.regs.rbp.toBitVec = _
        rw [hregs, hPost.2.1, ← hfp']
        exact hfp
      · intro p hp'
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl
        · rw [hk' 0 (by decide) (by omega) (by omega) (by decide)]; exact hs (0, q.g.ra) (by simp)
        · rw [hk' (-8) (by decide) (by omega) (by omega) (by decide)]; exact hs (-8, q.g.fp) (by simp)
        · rw [hk' (-16) (by decide) (by omega) (by omega) (by decide)]; exact hs (-16, q.tcb) (by simp)
      · show σR.regs.rax.toBitVec = _
        rw [hregs]; exact hPost.2.2
  case x7 =>
    refine seg_fixW b ?_
    refine SegW.mono_pre (P := At exe endPc R (takeF F rS b) (tiA b (tiX7 lab q))) ?_
      fun _ _ h => At.rbp h fun σ c ⟨_, _, ⟨hsp, hfp, _⟩, _⟩ => by
        simp only [Reg64s.get64]; rw [hsp, hfp]; bv_omega
    refine seg_ndW (by simp [ThreadInit.tiSp]) ThreadInit.tiSp_ok hFb hR (by omega) hhi
      (code_field hp hend (by simp only [hin']) (l := ThreadInit.x7L) (off := 0) (ofNat_zero' _))
      (blkW_tiS (hW TI.x7)) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNG, tiA, tiX7, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ ha
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    snodeW 0 0 48 3 q.tcb TI.f1 (nodeW_tiS (hW TI.st0))
  case f1 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF1 ThreadInit.tiF1_ok ThreadInit.x7L 51 (blkW_tiS (hW TI.f1))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1]; exact ofNat_add' _ 51 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    snodeW 1 8 59 4 (tiBase (_root_.Executable.labels exe).label q + 4096#64) TI.f2
      (nodeW_tiS (hW TI.st1))
  case f2 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiZ ThreadInit.tiZ_ok ThreadInit.x7L 63 (blkW_tiS (hW TI.f2))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1]; exact ofNat_add' _ 63 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    snodeW 2 16 74 4 (0#64) TI.f3 (nodeW_tiS (hW TI.st2))
  case f3 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiZ ThreadInit.tiZ_ok ThreadInit.x7L 78 (blkW_tiS (hW TI.f3))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1]; exact ofNat_add' _ 78 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    snodeW 3 24 89 4 (0#64) TI.f4 (nodeW_tiS (hW TI.st3))
  case f4 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF4 ThreadInit.tiF4_ok ThreadInit.x7L 93 (blkW_tiS (hW TI.f4))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1]; exact ofNat_add' _ 93 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    snodeW 4 32 101 4 (tiBase (_root_.Executable.labels exe).label q) TI.f5
      (nodeW_tiS (hW TI.st4))
  case f5 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF5 ThreadInit.tiF5_ok ThreadInit.x7L 105 (blkW_tiS (hW TI.f5))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1]; exact ofNat_add' _ 105 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    snodeW 5 40 113 4 (tiBase (_root_.Executable.labels exe).label q + 16384#64) TI.ret
      (nodeW_tiS (hW TI.st5))
  case ret =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiRet ThreadInit.tiRet_ok ThreadInit.x7L 117 (blkW_tiS (hW TI.ret))
    dsimp only [tiNG, tiA, tiN, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩


end TiWProof

/-! ## `scc_rt_start` up to the switch -/

section StartProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start` from `.x1` to the switch, inside `W`**
(`start_x1_sw_seg`, its states' obligations `hfs`, `hsys`, `hsw`). -/
theorem startX1Sw_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl)
    (hfs : BlkW W K exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0) startFs)
    (hsys : NodeW W K exe endPc R F
      (startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0))
    (hsw : BlkW W K exe endPc R F
      (startN5 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw) :
    SegW W K p lbl ms (At exe endPc R F (startN3 (_root_.Executable.labels exe).label n0 k0 c0))
      (At exe endPc R F (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  let top := stacksA lab + k0 + 16384#64
  simp only [startTailIn, Bool.and_eq_true] at hin
  refine SegW.seq (Q := At exe endPc R F (startN4 lab tcb top c0)) ?_
    (SegW.seq (Q := At exe endPc R F (startN5 lab tcb top c0)) ?_ ?_)
  · -- `.x1`'s block
    refine seg_oneW (seg_ndW (by simp [startFs]) startFs_ok hF hR hlo hhi
      (code_field hp hend hin.1.1.1.1.1 (ofNat_zero' _)) hfs fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN3, startN4]; rw [startFs_run]; rfl
    · dsimp only [startN3, startN4]; rw [startFs_run]; rfl
    · dsimp only [startN3, startN4] at hJ ⊢; rw [startFs_run]
      obtain ⟨⟨rfl, hax, h32⟩, -⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (simp [Reg64s.set64, Reg64s.get64, upd_apply, hax, h32]; done)
        | (simp [Reg64s.set64, Reg64s.get64, upd_apply, hax, h32]; rfl)
  · -- `arch_prctl(ARCH_SET_FS, tcb)`
    refine seg_oneW (archSetFs_ndW hK hF (code_field hp hend hin.1.1.1.1.2 rfl) hsys fun σ c hJ => ?_)
    obtain ⟨rfl, hax, hdi, hsi, h40, h32⟩ := hJ
    refine ⟨_, syscallCall_archSetFs hax hdi, c, .refl c, .inl ⟨(), ofNat_add' _ 18 2,
      by show SO.le oS (syscallSO oS) = true; decide, rfl, ?_, h40, h32⟩⟩
    show UInt64.ofNat σ.regs.rsi.toNat = _
    rw [← hsi]; rfl
  · -- the block after it
    refine seg_oneW (seg_ndW (by simp [startSw]) startSw_ok hF hR hlo hhi
      (code_field hp hend hin.1.1.1.2 rfl) hsw fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [startN5, startN6]; rw [startSw_run]; exact ofNat_add' _ 20 8
    · dsimp only [startN5, startN6]; rw [startSw_run]; rfl
    · dsimp only [startN5, startN6] at hJ ⊢; rw [startSw_run]
      obtain ⟨rfl, htp, h40, h32⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, h40]; rfl
      · simp only [Reg64s.set64]; exact htp

/-- **`scc_rt_start` from `.x0` to the switch, inside `W`, the take its
outside move** (`start_x0_x1_seg` then `start_x1_sw_seg`, their states'
obligations `hW`, with `thread_init_segW` at the call): from `.x1` on the
stack range `rS` is in private memory (`StackM`). Given the take's facts at
the region (`hRS`, `hfit`, `hout`, `hFt`). -/
theorem startX0Sw_segW {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : X0W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  simp only [startCall2In, Bool.and_eq_true] at hin
  have ex1 := label_labelGapB hp hin.2
  have hSM := stackM_stable hfit hout
  have hF2 : FStable R (fun m => F m ∧ StackM rS m) := fun m m' h hd => ⟨hF m m' h.1 hd, hSM m m' h.2 hd⟩
  -- `scc_rt_thread_init`'s region, and `rS` off it
  have hb' := Region.callee_base (hi' := 8) hR (show R.lo ≤ (-48 - 0) + -248 by omega) (by decide)
    (show (-48 - 0 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48 - 0) (-248) 8).Off k → ∀ i < 8,
      (R.callee (-48 - 0) (-248) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ (-48 - 0) + -248 by omega) (show (-48 - 0 : Int) + 8 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48 - 0) (-248) 8).base.toNat + (R.callee (-48 - 0) (-248) 8).lo ∨
        ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + (R.callee (-48 - 0) (-248) 8).hi ≤ a :=
    fun a h8 ha ha7 => by
      show (a : Int) + 8 ≤ ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + -248 ∨
        ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + 8 ≤ a
      rcases hout a h8 ha ha7 with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
  refine SegW.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (startN3 lab n0 k0 c0))
      ((seg_oneW (n := ⟨lab x1L, ⟨-40, []⟩, (startN3 lab n0 k0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2)
      (startX1Sw_segW hp hend htail hK hF2 hR (by omega) (by omega) n0 k0 c0 hW.fs hW.sys hW.sw))
  · -- the call's block
    refine (seg_oneW (seg_ndW (n := startN2R lab n0 c0) (by simp [startCall2]) startCall2_ok hF hR (by omega)
      (by omega) (code_field hp hend hin.1 (ofNat_zero' _)) hW.b0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN2R, startN2, startNC2]; rw [startCall2_run]
    · dsimp only [startN2R, startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [startN2R, startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨⟨⟨rfl, hax⟩, -⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x1L = _ from ex1, Int64.toBitVec_add]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_thread_init`
    refine call_nd_FW (e0 := 0) (lo' := -248) (hi' := 8) (M := StackM rS)
      (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e) (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -248; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (TakeK.kstable hFt)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h, hM⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48, -⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab x1L).toBitVec := by
          have e : lab x1L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (threadInit_segW hp hend hti hst hF' hR' hlo' hhi' hFF' ⟨g', tcb, k0, c0⟩ hk hfld htk
          (fun i => (hW.ti g' hr i).mono hFF') hRS' hfit hout' (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, -⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - hslot
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_, ?_⟩, ?_⟩
      · show lab x1L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

/-- **`scc_rt_start` up to `.x0` inside `W`** (`start_x0_seg`, its states'
obligations `hW`). The call of `scc_rt_alloc_tcb` asks no closure under `K`
of it (`call_nd_FWK` with `KC := False`): no outside move is in it. -/
theorem startX0_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startCallIn cells = true)
    (hstart : startIn cells = true) (hat : AllocTcb.allocTcbIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -232) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) (hW : St0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startCallIn, Bool.and_eq_true] at hin
  have ex0 := label_labelGapB hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine SegW.seq (start_seg_ofW hp hend hstart hK hF hR (by omega) (by omega) (nC := startN1 lab c0)
      (by show lab startE + Int64.ofNat 43 = lab startE + 7 + 34 + 2; rw [Int64.add_assoc, Int64.add_assoc]; rfl)
      (by show SO.le oS oS = true; decide) hW.start fun _ _ h => h)
    (SegW.seq (Q := At exe endPc R F (startNC lab c0)) ?_
      ((seg_oneW (n := ⟨lab x0L, ⟨-40, []⟩, (startN2 lab n0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2))
  · -- the call's block
    refine (seg_oneW (seg_ndW (n := startN1R lab c0) (by simp [startCall]) startCall_ok hF hR hlo48 hhi
      (code_field hp hend hin.1 rfl) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN1R, startN1, startNC]; rw [startCall_run]
    · dsimp only [startN1R, startN1, startNC]; rw [startCall_run]; rfl
    · dsimp only [startN1R, startN1, startNC] at hJ ⊢; rw [startCall_run]
      obtain ⟨rfl, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x0L = _ from ex0, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_alloc_tcb`
    refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -184) (hi' := 8) (M := fun _ => True)
      (Ne := fun g => tcbN lab ⟨g, n0, c0⟩ .e) (Ex := fun g => tcbX lab ⟨g, n0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -184; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48, -⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab x0L).toBitVec := by
          have e : lab x0L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (allocTcb_segW hp hend hat hF' hR' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr htcb
          fun i => (hW.tcb g' hr i).mono hFF).mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, h1⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g x σC c σx c' σR ⟨-, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - -
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_⟩, ?_⟩
      · show lab x0L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

end StartProof

/-! ## From the switch on, `scc_rt_main` parametric -/

section SwitchU

/-- No write inside the new region (depth `L`) breaks `swF`, when the limit
word lies outside the region below `top`. -/
theorem swF_stableL {top a v : BitVec 64} {L : Int} (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ a.toNat) :
    FStable (swR v (-L) 0) (swF top a v) := by
  rintro m m' ⟨rfl, h⟩ hd
  exact ⟨rfl, (hd a hfit hout).trans h⟩

/-- **The frame condition after the switch** into a region of depth `L`:
`swF`, and the stack range off the new region in private memory. -/
def swFSL (L : Int) (rS : Scc.Sem.Range) (top a v : BitVec 64) (m : MachineData) : Prop :=
  swF top a v m ∧ StackOff rS (swR v (-L) 0) m

/-- `call scc_rt_main` from the new stack's top: covered in a region of
depth at least `8`. -/
theorem startMain_okL {L : Int} (hL : 8 ≤ L) : okBlk (-L) 0 SO.entry startMain = true :=
  okBlk_callB (o := SO.entry) "scc_rt_main" (by simp [Spike.Lib.offOk, SO.entry]; omega)

/-- **The switch's and `scc_rt_main`'s states inside `W`**, `scc_rt_main`
parametric (`mc`) and its user function an interface: the switch,
`xorl %ebp, %ebp` and the call block in the new region of depth `L`, and
`scc_rt_main`'s own states and the user function's segment in the call's
callee region (`8` below the new top, the caller's cells outside it holding
values), for every value of the new `%rsp`. The user function's interface
is asked for every frame condition stronger than the callee's (`call_nd_FWK`
hands `scc_rt_main` such a one; the interface's entry names the caller's
frame condition, so it is not monotone in it). -/
structure SwUW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (ms : MemSide isa)
    (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int) (ZU : Int64)
    (Post : Ctl → BitVec 64 → Prop) : Prop where
  sw : NodeW W K exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)
  xor : ∀ v, NodeW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v)
    (startN7 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v)
    (startN8 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainUW W K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
    (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) ms mc Post
    ⟨top - 8#64, tpOf tcb, c0⟩
  user : ∀ v (F' : MachineData → Prop),
    (∀ m, F' m → swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
    UserCallW W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8) F' mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0 (tpOf tcb)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- `scc_rt_main`'s own obligations under a weaker frame condition hold
under a stronger one. -/
theorem MainUW.mono {W : Frag isa} {K : State → State → Prop} {F' : MachineData → Prop} {mc : MainCode}
    {Post : Ctl → BitVec 64 → Prop} {g : MainG} (h : MainUW W K exe endPc R F ms mc Post g)
    (hFF : ∀ m, F' m → F m) : MainUW W K exe endPc R F' ms mc Post g :=
  ⟨proW_mono h.pro hFF, blkW_mono h.call hFF, ⟨blkW_mono h.exit.w0 hFF, nodeW_mono h.exit.w1 hFF⟩⟩

/-- **From the switch on, inside `W`, `scc_rt_main` parametric** (hand
`start_switch_segW`): the switch into the new region of depth `L`,
`xorl %ebp, %ebp`, `call scc_rt_main` (`call_nd_FWK` with `KC := False`),
then `mainU_segW` in the callee's region, which holds `scc_rt_main`'s
frame, the return address it pushes and the user function's `D` (`hL`).
The new stack's cells hold values at the switch since the stack range is in
private memory then (`hFS`) and the new region lies in it (`hsub`). -/
theorem startSwitchU_segW {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hlimM : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : SwUW W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (tpOf tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-L) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine sw_seqW (lo := -L) (hi := 0) (F' := swFSL L rS top a) (n' := startN7 lab tcb top c0)
    (sw_ndW rfl (code_field hp hend hin.1.1.2 rfl) (ofNat_add' _ 28 3) rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv => ?_
  · obtain ⟨rfl, hax, htp⟩ := hJ
    obtain ⟨hsp, htp'⟩ := swStep (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ
    have hsp2 : (AI.step (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3)
        (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.get64 .rsp = top := by
      show (UInt64.toBitVec _) = _; rw [hsp]; exact hax
    rw [hsp2]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨hok, ⟨⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, by rw [hsp]; exact hax,
      htp'.trans htp⟩
  · have hF2 : FStable (swR v (-L) 0) (swFSL L rS top a v) := fun m m' h hd =>
      ⟨swF_stableL hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
    let g : MainG := ⟨top - 8#64, tpOf tcb, c0⟩
    refine (SegW.seq (Q := At exe endPc (swR v (-L) 0) (swFSL L rS top a v) (startN8 lab tcb top c0))
      (seg_oneW (flag_ndW (n := startN7 lab tcb top c0) (fi := .xor_rr32_self .rbp) rfl hF2
        (code_field hp hend hin.1.2 rfl) (hW.xor v)
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(),
          show lab x1L + Int64.ofNat 33 = lab x1L + Int64.ofNat 31 + Int64.ofNat 2 from ofNat_add' _ 31 2,
          by show SO.le SO.entry ((FI.xor_rr32_self .rbp).so SO.entry) = true; decide, ?_⟩⟩))
      (SegW.seq (Q := At exe endPc (swR v (-L) 0) (swFSL L rS top a v) (startNM lab tcb top c0))
      (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (by omega)) hF2 hv (Int.le_refl _) (Int.le_refl _)
        (code_field hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (call_nd_FWK (KC := False) (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0)
        (lo' := 8 - L) (hi' := 8) (M := fun _ => True)
        (Ne := fun _ : Unit => mainN0 lab g) (Ex := fun _ (e : Empty) => e.elim)
        hv hF2 (by show -L ≤ -8 - 0 + (8 - L); omega) (by omega) (by show (-8 : Int) - 0 < 0; decide)
        (by show (-8 : Int) - 0 + 8 ≤ 0; decide) (by show ((-8 : Int) - 0) % 8 = 0; decide) (by omega) (by decide)
        (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc _ _ _ => by
          subst hR'e
          exact mainU_segW hp hend hmain hZ hZ8 hps hk hD0 hD8 hK hF' hR' (by omega) (by omega) g
            ⟨hlimM.rt, hlimM.mp, fun _ h => (hFF _ h).1.2, hlimM.room⟩
            ⟨hlimU.rt, hlimU.mp, fun _ h => (hFF _ h).1.2, hlimU.room⟩
            (hW.user v F' fun m h => ⟨hFF m h, hcc m h⟩)
            (fun s c x hP hAt => hexit _ _ s c x hP hAt)
            ((hW.main v).mono fun m h => ⟨hFF m h, hcc m h⟩))
        (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ⟩) fun _ x => x.elim))).mono_post
      fun _ _ h => h.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim
    · dsimp only [startN7, startN8] at hJ ⊢
      obtain ⟨rfl, hsp, htp⟩ := hJ
      exact ⟨rfl, hsp, htp⟩
    · dsimp only [startN8, startNM]; rw [startMain_run]
    · dsimp only [startN8, startNM]; rw [startMain_run]; rfl
    · dsimp only [startN8, startNM] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, hsp]
      · simp [Reg64s.set64, htp]

end SwitchU

/-! ## `scc_rt_start` whole, `scc_rt_main` parametric -/

section StartU

/-- **`scc_rt_start`'s states inside `W`**, `scc_rt_main` parametric: up to
`.x0`, from `.x0` to the switch, and from the switch on (with the stack
range in private memory) into the new region of depth `L`. -/
structure StartAllUW (W : Frag isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0W W K exe endPc R F rS n0 k0 c0
  s3 : SwUW W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start` never returns, inside `W`, the take its outside move,
`scc_rt_main` parametric** (hand `start_segW`): `startX0_segW`, then
`startX0Sw_segW`, then `startSwitchU_segW`, in any valid layout of any
cells with the runtime's code checks and `scc_rt_main`'s (`hmain`). -/
theorem startU_segW {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hcall : startCallIn cells = true) (hstart : startIn cells = true)
    (hat : AllocTcb.allocTcbIn cells = true) (hcall2 : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hkm : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllUW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F ms rS
      n0 k0 c0 L mc D ZU Post)
    {Q : Frag isa} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (startX0_segW hp hend hcall hstart hat hK hF hR (by omega) (by omega) n0 c0 hn hhdr htcb hW.s1).seq
    ((startX0Sw_segW hp hend hcall2 htail hti hst hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS
      hFt).seq
      (startSwitchU_segW hp hend htail hmain hZ hZ8 hps hkm hD0 hD8 hL hL8 hK _ _ c0 hok (fun _ h => h.2) hfitS
        hsub hfit hout (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit hW.s3))

end StartU

end Spike.Lib.X64.Rt
