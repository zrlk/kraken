/-
**`scc_rt_alloc_tcb` at a header `h` with the counter's owned value at the
node's states** (x86-64): `allocTcbG_segW` with its `OwnAt` (every state
at the counter's `lock xadd`) weakened to the `lock xadd` node's states
(`TcbOkGA.own`). The x86-64 twin of `Spike/Lib/Rt/A64RtTcbGA.lean`.
`scc_rt_alloc_tcb` runs twice in wake.w, at the same pc with different old
values (`0`, `80`), so `OwnAt` at one pc cannot hold at an owned-words map
telling the calls apart by `sp` (`ownG`); the node's states carry the
call's frame, so at them it can.

- `ownXadd_ndWA` (in `Rt.X64OwnA`): `ownXadd_ndW` with the owned value at
  the node's states;
- `TcbOkGA`: `TcbOkG` with `own` at `tcbNG q .rmw`'s states;
- `TcbOkGA.of_tcbOkG`: `TcbOkG` gives it;
- `allocTcbG_segWA`: `allocTcbG_segW` at `TcbOkGA`.
-/
import Spike.Lib.Rt.X64RtTcbGN
import Spike.Lib.Rt.X64OwnA

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-- **The counter's add at `q`, owned at the `lock xadd` node's states**
(`TcbOkG` with `own` at `tcbNG q .rmw`'s states in the callee's region `R`
under its frame condition `F`). -/
structure TcbOkGA (ms : MemSide isa) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : TcbGG) : Prop where
  next : StOk ms F0 (pnA (_root_.Executable.labels exe).label) (q.n0 + AllocTcb.lenOf q.h)
  own : ∀ s c, At exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .rmw) s c →
    (⟨pnA (_root_.Executable.labels exe).label, 8⟩, q.n0.setWidth 128) ∈ ms.own s

/-- `TcbOkG` (owned at every state at the pc) gives `TcbOkGA`. -/
theorem TcbOkGA.of_tcbOkG {ms : MemSide isa} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbGG} (h : TcbOkG ms F0 exe endPc q.h q.n0) : TcbOkGA ms F0 exe endPc R F q :=
  ⟨h.next, fun s _ hA => h.own s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `TcbOkGA` under a stronger frame condition. -/
theorem TcbOkGA.mono {ms : MemSide isa} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbGG} (h : TcbOkGA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TcbOkGA ms F0 exe endPc R F' q :=
  ⟨h.next, fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.own s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

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

/-- **`scc_rt_alloc_tcb` at `h` is one segment inside `W`, the counter
owned at the `lock xadd` node's states** (`allocTcbG_segW` at `TcbOkGA`). -/
theorem allocTcbG_segWA {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : AllocTcb.allocTcbIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbGG) (hn : q.n0.toNat + (AllocTcb.lenOf q.h).toNat ≤ 131072)
    (hhdr : StOk ms F0 (hdrA (_root_.Executable.labels exe).label q) (q.h ||| 1#64 <<< 36))
    (htcb : TcbOkGA ms F0 exe endPc R F q) (hW : ∀ i, TcbWG W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbXG (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, AllocTcb.fiAt, AllocTcb.siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := AllocTcb.fnL) (b := AllocTcb.entryL) (off := 19) hp (by simp only [hin'])
  have pv := AllocTcb.path_valsG q.h
  refine fn_segW (N := tcbNG _ q) (E := tcbXG _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 20 (hW TN.j1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ1_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.len, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case len =>
    tnodeW AllocTcb.atL0 AllocTcb.atL0_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL0_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.shr1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr1 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 11 3 TN.l1 (hW TN.shr1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.1⟩
  case l1 =>
    tnodeW AllocTcb.atL1 AllocTcb.atL1_ok AllocTcb.lenL 14 (hW TN.l1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL1_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and1, by rw [h1]; exact ofNat_add' _ 14 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and1 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 29 3 TN.l2 (hW TN.and1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.1⟩
  case l2 =>
    tnodeW AllocTcb.atL2 AllocTcb.atL2_ok AllocTcb.lenL 32 (hW TN.l2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL2_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shr2, by rw [h1]; exact ofNat_add' _ 32 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr2 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 47 3 TN.l3 (hW TN.shr2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.2.2.1⟩
  case l3 =>
    tnodeW AllocTcb.atL3 AllocTcb.atL3_ok AllocTcb.lenL 50 (hW TN.l3)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL3_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and2, by rw [h1]; exact ofNat_add' _ 50 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and2 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 65 3 TN.l4 (hW TN.and2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.2.2.1⟩
  case l4 =>
    tnodeW AllocTcb.atL4 AllocTcb.atL4_ok AllocTcb.lenL 68 (hW TN.l4)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL4_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul1, by rw [h1]; exact ofNat_add' _ 68 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul1 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.lenL 95 4 TN.l5 (hW TN.imul1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.imul_rax ha hc fl⟩
  case l5 =>
    tnodeW AllocTcb.atL5 AllocTcb.atL5_ok AllocTcb.lenL 99 (hW TN.l5)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL5_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl1, by rw [h1]; exact ofNat_add' _ 99 33, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl1 =>
    fnodeW (.shl_cl .rax) AllocTcb.lenL 132 3 TN.l6 (hW TN.shl1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.1⟩
  case l6 =>
    tnodeW AllocTcb.atL6 AllocTcb.atL6_ok AllocTcb.lenL 135 (hW TN.l6)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atL6_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.lea1, by rw [h1]; exact ofNat_add' _ 135 4, by rw [h2]; rfl, rfl, h3⟩
  case lea1 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned_next") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 139) rfl) (hW TN.lea1)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ofNat_add' _ 139 7, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 146 (hW TN.arg)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.rmw, by rw [h1]; exact ofNat_add' _ 146 12, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_ndWA (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 158) rfl) htcb.own (hW TN.rmw)
      fun m σ c _ hD hJ => ?_
    dsimp only [tcbNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pnA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.lenOf q.h := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htcb.next.rt, htcb.next.mp, htcb.next.G, htcb.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TN.bnd, ofNat_add' _ 158 5, rfl, rfl, by simpa [ownStep, AllocTcb.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 163 (hW TN.bnd)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walkG (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨TN.j2, by rw [h1]; exact ofNat_add' _ 163 35, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 198 (hW TN.j2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ2_walkG (_root_.Executable.labels exe).label _ hJ
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
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO1_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul2, by rw [h1]; exact ofNat_add' _ 7 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul2 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.okL 34 4 TN.o2 (hW TN.imul2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.imul_rax ha hc fl⟩
  case o2 =>
    tnodeW AllocTcb.atO2 AllocTcb.atO2_ok AllocTcb.okL 38 (hW TN.o2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO2_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl2, by rw [h1]; exact ofNat_add' _ 38 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl2 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 53 3 TN.o3 (hW TN.shl2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.1⟩
  case o3 =>
    tnodeW AllocTcb.atO3 AllocTcb.atO3_ok AllocTcb.okL 56 (hW TN.o3)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO3_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl3, by rw [h1]; exact ofNat_add' _ 56 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl3 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 74 3 TN.o4 (hW TN.shl3)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2⟩
  case o4 =>
    tnodeW AllocTcb.atO4 AllocTcb.atO4_ok AllocTcb.okL 77 (hW TN.o4)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO4_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.or1, by rw [h1]; exact ofNat_add' _ 77 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case or1 =>
    fnodeW (.or_rr .rax .rcx) AllocTcb.okL 95 3 TN.o5 (hW TN.or1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.or_rax ha hc fl⟩
  case o5 =>
    tnodeW AllocTcb.atO5 AllocTcb.atO5_ok AllocTcb.okL 98 (hW TN.o5)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO5_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.hdr, by rw [h1]; exact ofNat_add' _ 98 42, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 140) rfl) (hW TN.hdr)
      fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = hdrA (_root_.Executable.labels exe).label q := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = q.h ||| 1#64 <<< 36 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨hhdr.rt, hhdr.mp, hhdr.G, hhdr.unmapped m (hFF m hD), q.c0,
      .refl q.c0, .inl ⟨TN.ret, ofNat_add' _ 140 3, rfl, rfl, hJ⟩⟩
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 143 (hW TN.ret)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


end TcbProof

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.TcbOkGA.of_tcbOkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TcbOkGA.of_tcbOkG

/-- info: 'Spike.Lib.X64.Rt.TcbOkGA.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TcbOkGA.mono

/-- info: 'Spike.Lib.X64.Rt.allocTcbG_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.allocTcbG_segWA
