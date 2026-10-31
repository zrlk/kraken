/-
**The x86-64 runtime's start segments with the callees' own words owned at
their nodes' states and an extra frame `P` up to the take site**
(`Spike/Lib/Rt/X64Segs.lean`, `Spike/Lib/Rt/X64SegsAt.lean` with
`TcbOkA`/`TakeOkA` for `TcbOk`/`TakeOk` and `P`): the x86-64 twin of the
`…_segWA` lemmas of `Spike/Lib/Rt/A64Segs.lean`.

The frame `P` is a fact of the caller's memory, stable under writes inside
the region (`FStable R P`), that holds from the segment's entry up to the
take site. It is not stable under the take (its use is `¬ StackM rS0`, which
the take makes false), so it cannot sit in the frame condition `F` that the
take keeps (`hFt`). Instead the segments carry it as
`takeF F rS b ∧ (b = false → P)` along the take's ghost `b`, and the take
site's obligation may assume it (`TakeWP`). That is how a `¬ StackM`
premise of the start's states reaches the take site
(`Spike/Lib/X64WakeX0.lean`'s `X0W`).

- `tiB`, `tiNPAt`, `takeNP`: the nodes with the take's ghost, gated on both
  sides (AArch64's `tiB`, `tiNP`, `takeNP`);
- `TakeWP`, `TiWAtP`, `X0WAtP`: `TakeW`, `TiWAt`, `X0WAt` with the take
  site's obligation under `F ∧ P` (and `.mono`);
- `allocTcb_segWA`, `startX0_segWA`: with `TcbOkA`;
- `stackTake_segWA`, `threadInit_segWAtA`, `startX0Sw_segWAtA`: with
  `TakeOkA` and `P` (the calls by `call_nd_FWP`, `P` into the callee's
  region by `FStable.callee`).

**Unlike AArch64**: the thread init's nodes and obligations are the
any-return-point ones (`tiNGAt`, `TiWAt`, `X0WAt`) of
`Spike/Lib/Rt/X64SegsAt.lean`, and the call into `scc_rt_thread_init` is
at `.x0`'s second call (`startX0Sw`, AArch64's `startSp2Sw`). The P-free
statements are those of `X64Segs`/`X64SegsAt` and are not re-derived here.
-/
import Spike.Lib.Rt.X64SegsAt
import Spike.Lib.Rt.X64OwnA
import Spike.Lib.X64CallP

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The nodes with the take's ghost, gated on both sides -/

section NodesP

variable (lab : Label → Int64)

/-- A node before the take's call: its invariant, with the take not done (`b`). -/
def tiB (b : Bool) (n : ND) : ND := ⟨n.pc, n.o, fun σ c => b = false ∧ n.J σ c⟩

/-- **`tiNGAt` with both sides gated**: the nodes up to the call of
`scc_rt_stack_take` only before the take is done (`tiB`), the rest only
after it. -/
def tiNPAt (q : TiG) (x : Label) (b : Bool) : TI → ND
  | .e => tiB b (tiNAt lab q x .e)
  | .entry => tiB b (tiNAt lab q x .entry)
  | .c7 => tiB b (tiNAt lab q x .c7)
  | .call => tiB b (tiNAt lab q x .call)
  | i => tiNGAt lab q x b i

/-- **The take's nodes with the ghost, the rest after the take empty**:
`takeNG`, after the take (`b = true`) only the node past the site. -/
def takeNP (q : TakeG) (b : Bool) (i : TK) : ND :=
  match b with
  | false => takeNG lab q false i
  | true => match i with
    | .ret => takeNG lab q true .ret
    | i => ⟨(takeNG lab q true i).pc, (takeNG lab q true i).o, fun _ _ => False⟩

end NodesP

/-! ## The obligations with `P` at the take site -/

/-- **`TakeW` with the take site's frame condition also `P`** (AArch64's
`TakeW … P`): the site's obligation is asked only under `F ∧ P`; the other
nodes' are `TakeW`'s. -/
def TakeWP (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TakeG) (P : MachineData → Prop) : TK → Prop
  | .site => ∀ s c, At exe endPc R (fun m => F m ∧ P m)
      (takeNG (_root_.Executable.labels exe).label q true .site) s c → W s c
  | i => TakeW W K exe endPc R F M q i

/-- **`TiWAt` with the take site's frame condition also `P`**: at the call,
`TakeWP` in the callee's region; the other nodes' are `TiWAt`'s. -/
def TiWAtP (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TiG) (x : Label) (P : MachineData → Prop) : TI → Prop
  | .call => ∀ g, g.ra = ((_root_.Executable.labels exe).label x).toBitVec → ∀ i,
      TakeWP W K exe endPc (R.callee (-48 - 0) (-200) 8) F M (tiTake q g) P i
  | i => TiWAt W K exe endPc R F M q x i

/-- **`X0WAt` with the take site's frame condition also `P`**: as `X0WAt`,
with `scc_rt_thread_init`'s obligations `TiWAtP … P`. -/
structure X0WAtP (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (x : Label)
    (P : MachineData → Prop) : Prop where
  b0 : BlkW W K exe endPc R F (Flow.Ret0.startN2R (_root_.Executable.labels exe).label n0 c0) startCall2
  ti : ∀ g, g.ra = ((_root_.Executable.labels exe).label x1L).toBitVec → ∀ i,
    TiWAtP W K exe endPc (R.callee (-48 - 0) (-248) 8) F (StackM rS)
    ⟨g, pinA (_root_.Executable.labels exe).label + n0 + 8#64, k0, c0⟩ x P i
  fs : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (Flow.Ret0.startN3 (_root_.Executable.labels exe).label n0 k0 c0) startFs
  sys : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (Flow.Ret0.startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)
  sw : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (Flow.Ret0.startN5 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw

section MonoP

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- Off the site, `TakeWP` is `TakeW`. -/
theorem takeWP_eq {M P : MachineData → Prop} {q : TakeG} {i : TK} (hi : i ≠ .site) :
    TakeWP W K exe endPc R F M q P i = TakeW W K exe endPc R F M q i := by
  cases i <;> first | rfl | exact absurd rfl hi

/-- Off the call, `TiWAtP` is `TiWAt`. -/
theorem tiWAtP_eq {M P : MachineData → Prop} {q : TiG} {x : Label} {i : TI} (hi : i ≠ .call) :
    TiWAtP W K exe endPc R F M q x P i = TiWAt W K exe endPc R F M q x i := by
  cases i <;> first | rfl | exact absurd rfl hi

/-- `TakeWP` under a stronger frame condition. -/
theorem TakeWP.mono {F' M P : MachineData → Prop} {q : TakeG} {i : TK}
    (h : TakeWP W K exe endPc R F M q P i) (hFF : ∀ m, F' m → F m) : TakeWP W K exe endPc R F' M q P i := by
  by_cases hi : i = .site
  · subst hi
    exact fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hFF _ hD.1, hD.2⟩, hJ⟩
  · rw [takeWP_eq hi] at h ⊢
    exact h.mono hFF

/-- `TakeW` gives `TakeWP` at any `P` (the site's frame condition only
stronger). -/
theorem TakeWP.of_takeW {M P : MachineData → Prop} {q : TakeG} {i : TK}
    (h : TakeW W K exe endPc R F M q i) : TakeWP W K exe endPc R F M q P i := by
  by_cases hi : i = .site
  · subst hi
    exact fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hD.1, hJ⟩
  · rw [takeWP_eq hi]; exact h

/-- `TiWAtP` under a stronger frame condition. -/
theorem TiWAtP.mono {F' M P : MachineData → Prop} {q : TiG} {x : Label} {i : TI}
    (h : TiWAtP W K exe endPc R F M q x P i) (hFF : ∀ m, F' m → F m) : TiWAtP W K exe endPc R F' M q x P i := by
  by_cases hi : i = .call
  · subst hi
    exact fun g hg i => (h g hg i).mono hFF
  · rw [tiWAtP_eq hi] at h ⊢
    exact h.mono hFF

/-- `TiWAt` gives `TiWAtP` at any `P`. -/
theorem TiWAtP.of_tiWAt {M P : MachineData → Prop} {q : TiG} {x : Label} {i : TI}
    (h : TiWAt W K exe endPc R F M q x i) : TiWAtP W K exe endPc R F M q x P i := by
  by_cases hi : i = .call
  · subst hi
    exact fun g hg i => .of_takeW (h g hg i)
  · rw [tiWAtP_eq hi]; exact h

/-- `X0WAt` gives `X0WAtP` at any `P`. -/
theorem X0WAtP.of_x0WAt {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl} {x : Label} {P : MachineData → Prop}
    (h : X0WAt W K exe endPc R F rS n0 k0 c0 x) : X0WAtP W K exe endPc R F rS n0 k0 c0 x P :=
  ⟨h.b0, fun g hg i => .of_tiWAt (h.ti g hg i), h.fs, h.sys, h.sw⟩

/-- `X0WAtP` under a stronger frame condition. -/
theorem X0WAtP.mono {F' : MachineData → Prop} {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl} {x : Label}
    {P : MachineData → Prop} (h : X0WAtP W K exe endPc R F rS n0 k0 c0 x P) (hFF : ∀ m, F' m → F m) :
    X0WAtP W K exe endPc R F' rS n0 k0 c0 x P :=
  ⟨blkW_mono h.b0 hFF, fun g hg i => (h.ti g hg i).mono hFF, blkW_mono h.fs fun m h => ⟨hFF m h.1, h.2⟩,
    nodeW_mono h.sys fun m h => ⟨hFF m h.1, h.2⟩, blkW_mono h.sw fun m h => ⟨hFF m h.1, h.2⟩⟩

/-- `blkW_tiS` under the gated frame condition. -/
theorem blkW_tiSP {rS : Scc.Sem.Range} {n : ND} {blk : List (Directive × Nat)} {b : Bool}
    {P : MachineData → Prop} (h : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m) n blk) :
    BlkW W K exe endPc R (fun m => takeF F rS b m ∧ (b = false → P m)) (tiA b n) blk :=
  blkW_mono (blkW_tiS h) fun _ h => h.1

/-- `nodeW_tiS` under the gated frame condition. -/
theorem nodeW_tiSP {rS : Scc.Sem.Range} {n : ND} {b : Bool} {P : MachineData → Prop}
    (h : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m) n) :
    NodeW W K exe endPc R (fun m => takeF F rS b m ∧ (b = false → P m)) (tiA b n) :=
  nodeW_mono (nodeW_tiS h) fun _ h => h.1

end MonoP

/-! ## `scc_rt_alloc_tcb`, owned at the node -/

section TcbProofA

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

/-- **`allocTcb_segW` with the counter owned at the `lock xadd` node's
states** (`htcb : TcbOkA`, AArch64's `allocTcb_segWA`): the same segment,
the add by `ownXadd_ndWA`. -/
theorem allocTcb_segWA {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : AllocTcb.allocTcbIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOkA ms F0 exe endPc R F q) (hW : ∀ i, TcbW W K exe endPc R F q i) :
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
    refine ownXadd_ndWA (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
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

end TcbProofA

/-! ## `scc_rt_stack_take`, owned at the nodes, with `P` to the site -/

section TakeProofA

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



/-- **`stackTake_segW` with the take's words owned at the nodes' states
(`htk : TakeOkA`) and an extra frame `P` (`FStable R P`) from the entry to
the take site** (AArch64's `stackTake_segWA`): the site's obligation may
assume `P` (`TakeWP`); `P` is not claimed after the take (nodes `takeNP`,
frame `takeF F rS b ∧ (b = false → P)`). -/
theorem stackTake_segWA {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOkA ms F0 exe endPc R F q) {P : MachineData → Prop} (hP : FStable R P)
    (hW : ∀ i, TakeWP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS)
      q P i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (fun s c => At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e) s c ∧ P s.st.1)
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
  -- `P` held until the take (`b = false`); after it only the node past the site (`takeNP`)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R)
      (Fg := fun b m => takeF F rS b m ∧ (b = false → P m)) (N := takeNP lab q) (E := takeXG lab q)
    (fun b i => ?_) false TK.e).mono_pre fun s c h => ?_).mono_post fun s c h => ?_
  rotate_left
  · obtain ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hPs⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, nofun⟩, fun _ => hPs⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hM⟩, -⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, rfl, hJ⟩
  have hFb : FStable R (fun m => takeF F rS b m ∧ (b = false → P m)) := fun m m' ⟨⟨hD, hM⟩, hPm⟩ hd =>
    ⟨⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩, fun hb => hP m m' (hPm hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m ∧ (b = false → P m) → F0 m := fun m h => hFF m h.1.1
  have htkb := htk.mono (F' := fun m => takeF F rS b m ∧ (b = false → P m)) fun m h => h.1.1
  have hWb : ∀ i, TakeWP W (TakeK (lab StackTake.siteL) rS) exe endPc R
      (fun m => takeF F rS b m ∧ (b = false → P m)) (StackM rS) q P i :=
    fun i => (hW i).mono fun m h => h.1.1
  have hWt : ∀ i, i ≠ TK.site → TakeW W (TakeK (lab StackTake.siteL) rS) exe endPc R
      (fun m => takeF F rS b m ∧ (b = false → P m)) (StackM rS) q i := fun i hi => takeWP_eq hi ▸ hWb i
  have hW0 : ∀ i, i ≠ TK.site → TakeW W (TakeK (lab StackTake.siteL) rS) exe endPc R F (StackM rS) q i :=
    fun i hi => takeWP_eq hi ▸ hW i
  cases b
  case true =>
    cases i
    case ret =>
      refine seg_fixW true ?_
      knodeW StackTake.stRet StackTake.stRet_ok StackTake.siteL 1 (blkW_mono (F := fun m => F m ∧ StackM rS m)
        (F' := fun m => takeF F rS true m ∧ (true = false → P m)) (hW0 TK.ret nofun) fun m h => ⟨h.1.1, h.1.2 rfl⟩)
      dsimp only [takeNP, takeNG, takeXG] at hJ ⊢
      obtain ⟨-, rfl, hJ⟩ := hJ
      obtain ⟨h1, h2, h3⟩ := StackTake.stRet_walk lab _ hJ
      exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩
    all_goals exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h⟩ => h
  let b := false  -- before the take
  cases i <;> dsimp only [takeNP]
  case e =>
    refine seg_fixW b ?_
    knodeW StackTake.stPro StackTake.stPro_ok StackTake.fnL 0 (hWt TK.e nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    knodeW StackTake.stInit StackTake.stInit_ok StackTake.entryL 0 (hWt TK.entry nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stInit_walk lab _ hJ
    exact .inl ⟨TK.cls, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case cls =>
    refine seg_fixW b ?_
    knodeW StackTake.stCls StackTake.stCls_ok StackTake.clsL 0 (hWt TK.cls nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stCls_walk lab _ hJ
    exact .inl ⟨TK.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 13 (hWt TK.j1 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ1_walk lab _ hJ
    exact .inl ⟨TK.d0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case d0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_free_n" StackTake.doneL 0 TK.d7 (hWt TK.d0 nofun)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 7 (hWt TK.d7 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ ha
    exact .inl ⟨TK.d26, by rw [h1]; exact ofNat_add' _ 7 19, by rw [h2]; rfl, rfl, h3⟩
  case d26 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_free" StackTake.doneL 26 TK.d33 (hWt TK.d26 nofun)
    · exact ofNat_add' _ 26 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ⟩
  case d33 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFree StackTake.stFree_ok StackTake.doneL 33 (hWt TK.d33 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d52, by rw [h1]; exact ofNat_add' _ 33 19, by rw [h2]; rfl, rfl, h3⟩
  case d52 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_lock" StackTake.doneL 52 TK.d59 (hWt TK.d52 nofun)
    · exact ofNat_add' _ 52 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case d59 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLock StackTake.stLock_ok StackTake.doneL 59 (hWt TK.d59 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ ha
    exact .inl ⟨TK.sp0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case sp0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSwp StackTake.stSwp_ok StackTake.spinL 0 (hWt TK.sp0 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSwp_walk lab _ hJ
    exact .inl ⟨TK.swp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case swp =>
    refine seg_fixW b ?_
    refine ownXchg_ndWA (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.spinL) (off := 11) rfl) (htkb.ownLock b)
      (hWt TK.swp nofun) fun m σ c _ hD hJ => ?_
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
    knodeW StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 14 (hWt TK.sp14 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ ha
    exact .inl ⟨TK.lk0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case lk0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLdN StackTake.stLdN_ok StackTake.lockedL 0 (hWt TK.lk0 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := StackTake.stLdN_walk lab _ hJ
    exact .inl ⟨TK.ldn, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case ldn =>
    refine seg_fixW b ?_
    refine ownLd_ndWA (b := .rcx) (k := 0) (r := .rax) (z := 3) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.lockedL) (off := 4) rfl) (htkb.ownFreeN b)
      (hWt TK.ldn nofun) fun m σ c _ hD hJ => ?_
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
    knodeW StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 7 (hWt TK.lk7 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ ha
    exact .inl ⟨TK.b0, h1.symm, by rw [h2]; rfl, rfl, h3.mono (StackTake.s3_s0 _ _ _)⟩
  case b0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stack_lock" StackTake.bumpL 0 TK.b7 (hWt TK.b0 nofun)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 7 (hWt TK.b7 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ ha
    exact .inl ⟨TK.unl, by rw [h1]; exact ofNat_add' _ 7 21, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine seg_fixW b ?_
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 28) rfl)
      (hWt TK.unl nofun) fun m σ c _ hD hJ => ?_
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
    lnodeW "scc_rt_stack_next" StackTake.bumpL 31 TK.b38 (hWt TK.b31 nofun)
    · exact ofNat_add' _ 31 7
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case b38 =>
    refine seg_fixW b ?_
    knodeW StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 38 (hWt TK.b38 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ ha
    exact .inl ⟨TK.nxt, by rw [h1]; exact ofNat_add' _ 38 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine seg_fixW b ?_
    refine ownXadd_ndWA (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hFb
      (code_field hp hend (by simp only [hin']) (l := StackTake.bumpL) (off := 56) rfl) (htkb.ownNext b)
      (hWt TK.nxt nofun) fun m σ c _ hD hJ => ?_
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
    knodeW StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 61 (hWt TK.b61 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ ha hk
    exact .inl ⟨TK.b108, by rw [h1]; exact ofNat_add' _ 61 47, by rw [h2]; rfl, rfl, h3⟩
  case b108 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 108 (hWt TK.b108 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stJ2_walk lab _ hJ
    exact .inl ⟨TK.ok0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok0 =>
    refine seg_fixW b ?_
    lnodeW "scc_rt_stacks" StackTake.okL 0 TK.ok7 (hWt TK.ok0 nofun)
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, StackTake.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case ok7 =>
    refine seg_fixW b ?_
    knodeW StackTake.stOk StackTake.stOk_ok StackTake.okL 7 (hWt TK.ok7 nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ ha
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    refine seg_fixW b ?_
    knodeW StackTake.stSite StackTake.stSite_ok StackTake.takenL 0 (hWt TK.tk nofun)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine seg_movedW (j := TK.ret) ((take_ndW (n := takeNG lab q false TK.site) (n' := takeNG lab q true TK.ret) rfl
      (code_field hp hend (by simp only [nopBlk, hin']) (l := StackTake.siteL) (off := 0) (ofNat_zero' _))
      (fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => hWb TK.site s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, hD.2 rfl⟩, hJ⟩)
      (fun m σ pm hA hD => ⟨hAbs hA, ⟨hFt m pm hD.1.1, fun _ => stackM_takeMem⟩, nofun⟩)
      fun σ c hJ => ⟨rfl, c, .refl c, rfl, hJ.1, hJ.2.1⟩).mono_post fun _ _ h => ⟨true, h⟩)
  case ret =>
    exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => Bool.false_ne_true h

end TakeProofA

/-! ## `scc_rt_thread_init`, the take owned at its nodes, with `P` to the call -/

section TiWProofAtA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_init` inside `W`. -/
local macro "inodeWA " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR (by omega) hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at the store of field `i` (`8·i(%rcx)`, `z` bytes) at `x + k`,
to node `j`, inside `W`, after the take. -/
local macro "snodeWA " i:term:max d:term:max k:term:max z:term:max v:term:max j:term:max w:term:max : tactic =>
  `(tactic| (
    refine rtst_ndW (b := .rcx) (k := $d) (r := .rax) (z := $z)
      (code_field hp hend (by simp only [hin']) (l := xr) (off := $k) rfl) $w
      fun m σ c _ hD hJ => ?_
    dsimp only [tiNGAt, tiA, tiNAt] at hJ
    obtain ⟨rfl, rfl, hJ, ha, hc⟩ := hJ
    have hfi := hfld (8 * $i, $v) (by simp [ThreadInit.fields])
    rw [bAddr_rcx hc, show BitVec.ofInt 64 (Int64.toInt $d) = BitVec.ofNat 64 (8 * $i) by decide,
      show σ.regs.get64 .rax = σ.regs.rax.toBitVec from rfl, ha]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0,
      .refl q.c0, .inl ⟨$j, ofNat_add' _ $k $z, rfl, rfl, rfl, hJ⟩⟩))

/-- **`threadInit_segWAt` with the take's words owned at its nodes' states
(`htk : TakeOkA`, for every ghost) and an extra frame `P` (`FStable R P`)
to the take's call** (AArch64's `threadInit_segWA`): `stackTake_segWA` at
the call (`call_nd_FWP`), `P` passed into the take's region
(`FStable.callee`); the nodes up to the call gated by `b = false`
(`tiNPAt`). -/
theorem threadInit_segWAtA {xr : Label} {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : ThreadInit.threadInitInAt cells xr = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, TakeOkA ms F0 exe endPc (R.callee (-48 - 0) (-200) 8) F (tiTake q g))
    {P : MachineData → Prop} (hP : FStable R P)
    (hW : ∀ i, TiWAtP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      xr P i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (fun s c => At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e) s c ∧ P s.st.1)
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [ThreadInit.threadInitInAt, ThreadInit.storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_left,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := ThreadInit.fnL) (b := ThreadInit.entryL) (off := 12) hp (by simp only [hin'])
  have eX7 := label_labelGapB (a := ThreadInit.entryL) (b := xr) (off := 12) hp (by simp only [hin'])
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
  -- `P` held until the take's call (`b = false`); the nodes up to it gated by `b = false` (`tiNPAt`)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R)
      (Fg := fun b m => takeF F rS b m ∧ (b = false → P m))
      (N := tiNPAt (_root_.Executable.labels exe).label q xr) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hPs⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, nofun⟩, fun _ => hPs⟩, rfl, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hM⟩, -⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFt0 : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFb : FStable R (fun m => takeF F rS b m ∧ (b = false → P m)) := fun m m' ⟨hD, hPm⟩ hd =>
    ⟨hFt0 m m' hD hd, fun hb => hP m m' (hPm hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m ∧ (b = false → P m) → F0 m := fun m h => hFF m h.1.1
  have hWt : ∀ i, i ≠ TI.call → TiWAt W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F (StackM rS) q xr i := fun i hi => tiWAtP_eq hi ▸ hW i
  cases i <;> dsimp only [tiNPAt]
  case e =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    inodeWA ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0
      (fun s σ c he hn hdc hpc hA hD hJ => hWt TI.e nofun s σ c he hn hdc hpc hA hD.1.1 hJ.2)
    dsimp only [tiNPAt, tiB, tiNAt] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, rfl, h3⟩
  case entry =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    inodeWA ThreadInit.tiArg ThreadInit.tiArg_ok ThreadInit.entryL 0
      (fun s σ c he hn hdc hpc hA hD hJ => hWt TI.entry nofun s σ c he hn hdc hpc hA hD.1.1 hJ.2)
    dsimp only [tiNPAt, tiB, tiNAt] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := ThreadInit.tiArg_walk lab _ hJ
    exact .inl ⟨TI.c7, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4⟩
  case c7 =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    refine seg_ndW (by simp [tiCall]) tiCall_ok hFb hR (by omega) hhi
      (code_field hp hend hcall rfl)
      (fun s σ c he hn hdc hpc hA hD hJ => hWt TI.c7 nofun s σ c he hn hdc hpc hA hD.1.1 hJ.2)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNPAt, tiB, tiNAt] at hJ ⊢
    obtain ⟨-, rfl, ⟨hsp, hfp, hs⟩, hdi⟩ := hJ
    rw [tiCall_run]
    refine .inl ⟨TI.call, rfl, rfl, rfl, ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
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
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW true ((call_nd_FWP (KC := True) (nC := tiNAt lab q xr .call) (e0 := 0) (lo' := -200)
      (hi' := 8) (M := StackM rS) (P := P)
      (Ne := fun g => takeNG lab (tiTake q g) false .e) (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hFt0 (by show R.lo ≤ -48 - 0 + -200; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun _ => TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun _ s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨⟨h.1, fun _ => hM⟩, nofun⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab xr).toBitVec := by
          have e : lab xr = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (stackTake_segWA hp hend hst hF' hR' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk
          ((htk g').mono fun m h => (hFF' m h).1)
          (FStable.callee hR (show R.lo ≤ -48 - 0 + -200 by omega) (by decide) (show (-48 - 0 : Int) < R.hi by omega)
            (show (-48 - 0 : Int) + 8 ≤ R.hi by omega) hP)
          (fun i => (hW TI.call g' hr i).mono fun m h => (hFF' m h).1) hRS' hfit hout'
          (takeMem_of_kstable (hK' trivial) exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_).mono_pre
        fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD.1, hD.2 rfl⟩, hJ.2⟩)
    · rintro σC c ⟨⟨rfl, -, -, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hs, hsp, hfp, -⟩, h48⟩ ⟨-, hsp', hfp', hra', -⟩ ⟨-, rfl, hPost⟩ hregs - - hslot
      have hk' : ∀ k : Int, k % 8 = 0 → R.lo ≤ k → k + 8 ≤ R.hi → -48 < k → σR.slot k = σC.slot k :=
        fun k h1 h2 h3 h4 => hslot k ⟨h1, h2, h3⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiNGAt, tiNAt] at h; omega
      refine .inl ⟨TI.x7, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, rfl, rfl, ⟨?_, ?_, ?_⟩,
        ?_⟩
      · show lab xr = Int64.ofBitVec g.ra
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
    refine SegW.mono_pre (P := At exe endPc R (fun m => takeF F rS b m ∧ (b = false → P m))
      (tiA b (tiX7At lab q xr))) ?_
      fun _ _ h => At.rbp h fun σ c ⟨_, _, ⟨hsp, hfp, _⟩, _⟩ => by
        simp only [Reg64s.get64]; rw [hsp, hfp]; bv_omega
    refine seg_ndW (by simp [ThreadInit.tiSp]) ThreadInit.tiSp_ok hFb hR (by omega) hhi
      (code_field hp hend (by simp only [hin']) (l := xr) (off := 0) (ofNat_zero' _))
      (blkW_tiSP (hWt TI.x7 nofun)) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNGAt, tiA, tiX7At, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ ha
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    snodeWA 0 0 48 3 q.tcb TI.f1 (nodeW_tiSP (hWt TI.st0 nofun))
  case f1 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF1 ThreadInit.tiF1_ok xr 51 (blkW_tiSP (hWt TI.f1 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1]; exact ofNat_add' _ 51 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    snodeWA 1 8 59 4 (tiBase (_root_.Executable.labels exe).label q + 4096#64) TI.f2
      (nodeW_tiSP (hWt TI.st1 nofun))
  case f2 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiZ ThreadInit.tiZ_ok xr 63 (blkW_tiSP (hWt TI.f2 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1]; exact ofNat_add' _ 63 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    snodeWA 2 16 74 4 (0#64) TI.f3 (nodeW_tiSP (hWt TI.st2 nofun))
  case f3 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiZ ThreadInit.tiZ_ok xr 78 (blkW_tiSP (hWt TI.f3 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1]; exact ofNat_add' _ 78 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    snodeWA 3 24 89 4 (0#64) TI.f4 (nodeW_tiSP (hWt TI.st3 nofun))
  case f4 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF4 ThreadInit.tiF4_ok xr 93 (blkW_tiSP (hWt TI.f4 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1]; exact ofNat_add' _ 93 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    snodeWA 4 32 101 4 (tiBase (_root_.Executable.labels exe).label q) TI.f5
      (nodeW_tiSP (hWt TI.st4 nofun))
  case f5 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF5 ThreadInit.tiF5_ok xr 105 (blkW_tiSP (hWt TI.f5 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1]; exact ofNat_add' _ 105 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    snodeWA 5 40 113 4 (tiBase (_root_.Executable.labels exe).label q + 16384#64) TI.ret
      (nodeW_tiSP (hWt TI.st5 nofun))
  case ret =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiRet ThreadInit.tiRet_ok xr 117 (blkW_tiSP (hWt TI.ret nofun))
    dsimp only [tiNGAt, tiA, tiNAt, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩

end TiWProofAtA
/-! ## `scc_rt_start` up to the switch, owned, with `P` to the take -/

section StartProofAtA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

/-- **`startX0Sw_segWAt` with the take's words owned at its nodes' states
(`htk : TakeOkA`, for every ghost) and an extra frame `P` (`FStable R P`)
from `.x0` to the take site** (AArch64's `startSp2Sw_segWA`):
`threadInit_segWAtA` at the call (`call_nd_FWP`), `P` passed into
`scc_rt_thread_init`'s region (`FStable.callee`) and its obligations
`X0WAtP`. -/
theorem startX0Sw_segWAtA {xr : Label} {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitInAt cells xr = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, TakeOkA ms F exe endPc ((R.callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F ⟨g, k0, c0⟩)
    {P : MachineData → Prop} (hP : FStable R P)
    (hW : X0WAtP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0 xr
      P)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R (fun m => F m ∧ P m) (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  simp only [startCall2In, Bool.and_eq_true] at hin
  have ex1 := label_labelGapB hp hin.2
  have hSM := stackM_stable hfit hout
  have hF2 : FStable R (fun m => F m ∧ StackM rS m) := fun m m' h hd => ⟨hF m m' h.1 hd, hSM m m' h.2 hd⟩
  have hFP : FStable R (fun m => F m ∧ P m) := fun m m' h hd => ⟨hF m m' h.1 hd, hP m m' h.2 hd⟩
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
  refine SegW.seq (Q := At exe endPc R (fun m => F m ∧ P m) (startNC2 lab tcb c0)) ?_
    (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (startN3 lab n0 k0 c0))
      ((seg_oneW (n := ⟨lab x1L, ⟨-40, []⟩, (startN3 lab n0 k0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2)
      (startX1Sw_segW hp hend htail hK hF2 hR (by omega) (by omega) n0 k0 c0 hW.fs hW.sys hW.sw))
  · -- the call's block
    refine (seg_oneW (seg_ndW (n := startN2R lab n0 c0) (by simp [startCall2]) startCall2_ok hFP hR (by omega)
      (by omega) (code_field hp hend hin.1 (ofNat_zero' _)) (blkW_mono hW.b0 fun m h => h.1)
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
    refine call_nd_FWP (KC := True) (e0 := 0) (lo' := -248) (hi' := 8) (M := StackM rS) (P := P)
      (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e) (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -248; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun _ => TakeK.kstable hFt)
      (fun _ s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
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
        exact (threadInit_segWAtA hp hend hti hst hF' hR' hlo' hhi' hFF' ⟨g', tcb, k0, c0⟩ hk hfld
          (fun g => (htk g).mono hFF')
          (FStable.callee hR (show R.lo ≤ -48 - 0 + -248 by omega) (by decide) (show (-48 - 0 : Int) < R.hi by omega)
            (show (-48 - 0 : Int) + 8 ≤ R.hi by omega) hP)
          (fun i => (hW.ti g' hr i).mono hFF') hRS' hfit hout' (takeMem_of_kstable (hK' trivial) exe endPc)).mono_post
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

end StartProofAtA
/-! ## `scc_rt_start` up to `.x0`, owned at the node -/

section StartX0A

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

/-- **`startX0_segW` with the counter owned at the `lock xadd` node's
states** (`htcb : TcbOkA` in `scc_rt_alloc_tcb`'s region, for every ghost):
`allocTcb_segWA` at the call. -/
theorem startX0_segWA {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startCallIn cells = true)
    (hstart : startIn cells = true) (hat : AllocTcb.allocTcbIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -232) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkA ms F exe endPc (R.callee (-48 - 0) (-184) 8) F ⟨g, n0, c0⟩)
    (hW : St0W W K exe endPc R F n0 c0) :
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
        exact (allocTcb_segWA hp hend hat hF' hR' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr ((htcb g').mono hFF)
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

end StartX0A

end Spike.Lib.X64.Rt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.takeWP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.takeWP_eq

/-- info: 'Spike.Lib.X64.Rt.tiWAtP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.tiWAtP_eq

/-- info: 'Spike.Lib.X64.Rt.TakeWP.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TakeWP.mono

/-- info: 'Spike.Lib.X64.Rt.TakeWP.of_takeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TakeWP.of_takeW

/-- info: 'Spike.Lib.X64.Rt.TiWAtP.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TiWAtP.mono

/-- info: 'Spike.Lib.X64.Rt.TiWAtP.of_tiWAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TiWAtP.of_tiWAt

/-- info: 'Spike.Lib.X64.Rt.X0WAtP.of_x0WAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.X0WAtP.of_x0WAt

/-- info: 'Spike.Lib.X64.Rt.X0WAtP.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.X0WAtP.mono

/-- info: 'Spike.Lib.X64.Rt.blkW_tiSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.blkW_tiSP

/-- info: 'Spike.Lib.X64.Rt.nodeW_tiSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.nodeW_tiSP

/-- info: 'Spike.Lib.X64.Rt.allocTcb_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.allocTcb_segWA

/-- info: 'Spike.Lib.X64.Rt.stackTake_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.stackTake_segWA

/-- info: 'Spike.Lib.X64.Rt.threadInit_segWAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.threadInit_segWAtA

/-- info: 'Spike.Lib.X64.Rt.startX0Sw_segWAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.startX0Sw_segWAtA

/-- info: 'Spike.Lib.X64.Rt.startX0_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.startX0_segWA
