/-
**The three threads of `mp_relay3_xchg.kl`, the `.kl` code verbatim, by
`vcgen`, over masked images**: the `code` block of
`Kraken/Examples/LockFree/X64/mp_relay3_xchg.kl` as written (`relayCodeV`:
the writer, `wdone: nop`, the relay, `rdone: nop`, the reader, `ddone:`), run
by all three threads in its image `relayImageV` (the code, then the `.kl`
runner's data trailer `relayDataV`: `d`, `f1`, `f2`). The x64 claim-conditional RMW proof's theorem
proves the per-thread texts `mpWriterX` (no labels, no `jmp wdone`), `relayX`
(labels `spin`/`done_y`, no `jmp rdone`) and `mpReaderX` (labels
`spin`/`done_r`, no `jmp ddone`), each laid out alone.

- **Masks** (`EnvG/X64MaskCore.lean`): each thread runs over a mask of the
  image keeping its own cells: the writer `relayImageW` (cells `0 … 6`,
  `writer:` to `wdone:`), the relay `relayImageY` (cells `8 … 16`, `relay:`
  to `rdone:`), the reader `relayImageR` (cells `18 … 24`, `reader:` to
  `ddone:`). The `nop`s after `wdone:`/`rdone:` and the other threads' code
  are data cells, so each mask halts at its exit label, and the reader's
  mask is phase-1 (the relay's `xchgl` is masked).
- **Placement**: `cfgEnv_partial_at` at the fragments `writerFragV`,
  `relayFragV`, `readerFragV` (the thread's blocks, with an empty exit block),
  whose blocks are the masks' and the image's (`Program.subBlocksOfE`).
- **The VCs are the x64 MP proof's and the x64 claim-conditional RMW proof's,
  unchanged** (`EnvG/X64MpVCGen.lean`,
  `EnvG/X64RelayXchgVCGen.lean`).

Contents: `writerW_envG` (on `EnvGX`), `relayY_envGTC` (on the counted
`EnvGTCX`), `readerR_envGT` (on the counted `EnvGTX`), each at the image's
labels; `writerV_noNT`, `relayV_noNT`, `readerV_noNT` (the all-release runs at
the unmasked image).
-/
import Kraken.Promising.SLR.EnvG.X64RelayXchgVCGen
import Kraken.Promising.SLR.EnvG.X64RelayXchgRelPure
import Kraken.Promising.SLR.EnvG.X64MpRelPure
import Kraken.Promising.SLR.EnvG.X64MaskLinkRmw
import Kraken.Promising.SLR.EnvG.X64MaskLinkMore
import Kraken.Promising.SLR.EnvG.X64MaskLinkTake
import Kraken.Promising.SLR.EnvG.X64ImageNoFault
import Kraken.EnvCfgAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.TakeMp Kraken.Promising.X64.EnvG.RelayX
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.RelayAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program, its image, the fragments and the masks -/

/-- **The `code` block of `mp_relay3_xchg.kl`, verbatim.** -/
def relayCodeV : Program := parse("
writer:
  movl $42,%eax
  movl %eax,(%rsi)
  movl $1,%ecx
  movl %ecx,(%rdi)
  jmp wdone
wdone:
  nop
relay:
  movl (%rdi),%eax
  cmpl $0,%eax
  je relay
  movl $43,(%rsi)
  movl $1,%ecx
  xchgl %ecx,(%rdx)
  jmp rdone
rdone:
  nop
reader:
  movl (%rdi),%eax
  cmpl $0,%eax
  je reader
  movl (%rsi),%ebx
  jmp ddone
ddone:
")

/-- info: 25 -/
#guard_msgs in
#eval relayCodeV.length

/-- The `.kl` runner's data trailer of `mp_relay3_xchg.kl`: each symbol a
label behind a padding cell, in the order of the init block (`d`, `f1`,
`f2`). -/
def relayDataV : Program :=
  [.byteArray (.mk #[]), .label "d", .byteArray (.mk #[]), .label "f1", .byteArray (.mk #[]), .label "f2"]

/-- The image: the code, then the data trailer. -/
def relayImageV : Program := relayCodeV ++ relayDataV

/-- The writer's fragment: the `writer` block, then the exit label `wdone`
(an empty last block; the image's `wdone` block, `nop`, is never run). -/
def writerFragV : Program := parse("
writer:
  movl $42,%eax
  movl %eax,(%rsi)
  movl $1,%ecx
  movl %ecx,(%rdi)
  jmp wdone
wdone:
")

/-- The relay's fragment: from `relay` to the exit label `rdone` (empty). -/
def relayFragV : Program := parse("
relay:
  movl (%rdi),%eax
  cmpl $0,%eax
  je relay
  movl $43,(%rsi)
  movl $1,%ecx
  xchgl %ecx,(%rdx)
  jmp rdone
rdone:
")

/-- The reader's fragment: from `reader` to the exit label `ddone`. -/
def readerFragV : Program := parse("
reader:
  movl (%rdi),%eax
  cmpl $0,%eax
  je reader
  movl (%rsi),%ebx
  jmp ddone
ddone:
")

/-- **The writer's mask**: cells `0 … 6` kept. -/
def relayImageW : Program := relayImageV.maskKeep (keepRange 0 7)

/-- **The relay's mask**: cells `8 … 16` kept. -/
def relayImageY : Program := relayImageV.maskKeep (keepRange 8 17)

/-- **The reader's mask**: cells `18 … 24` kept. -/
def relayImageR : Program := relayImageV.maskKeep (keepRange 18 25)

theorem relayImageV_wf : Program.WF relayImageV := by decide
theorem relayImageW_wf : Program.WF relayImageW := by decide
theorem relayImageY_wf : Program.WF relayImageY := by decide
theorem relayImageR_wf : Program.WF relayImageR := by decide

theorem writerFragV_sub : Program.subBlocksOfE writerFragV relayImageV = true := by decide
theorem relayFragV_sub : Program.subBlocksOfE relayFragV relayImageV = true := by decide
theorem readerFragV_sub : Program.subBlocksOfE readerFragV relayImageV = true := by decide
theorem writerFragW_sub : Program.subBlocksOfE writerFragV relayImageW = true := by decide
theorem relayFragY_sub : Program.subBlocksOfE relayFragV relayImageY = true := by decide
theorem readerFragR_sub : Program.subBlocksOfE readerFragV relayImageR = true := by decide

theorem writerFragV_eq : (relayImageV.drop 0).take (7 - 0) = writerFragV := by decide
theorem relayFragV_eq : (relayImageV.drop 8).take (17 - 8) = relayFragV := by decide
theorem readerFragV_eq : (relayImageV.drop 18).take (25 - 18) = readerFragV := by decide

/-- The writer's mask's cell at `wdone`'s `nop` is a data cell. -/
theorem relayImageW_7 : relayImageW[7]? = some (.byteArray (.mk #[])) := by decide

/-- The relay's mask's cell at `rdone`'s `nop` is a data cell. -/
theorem relayImageY_17 : relayImageY[17]? = some (.byteArray (.mk #[])) := by decide

/-- The reader's mask's cell after `ddone` is a data cell. -/
theorem relayImageR_25 : relayImageR[25]? = some (.byteArray (.mk #[])) := by decide

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labY (x : Label) : Int64 := (_root_.Executable.labels (layout relayImageV)).label x

/-- A symbol's address in the image. -/
abbrev symY (x : Label) : BitVec 64 := (labY x).toBitVec

theorem relayImageW_mask : MaskOf (layout relayImageV) (layout relayImageW) := maskOf_layout _ _
theorem relayImageY_mask : MaskOf (layout relayImageV) (layout relayImageY) := maskOf_layout _ _
theorem relayImageR_mask : MaskOf (layout relayImageV) (layout relayImageR) := maskOf_layout _ _

theorem labelsW_eq : _root_.Executable.labels (layout relayImageW) = _root_.Executable.labels (layout relayImageV) :=
  labels_mask relayImageW_mask
theorem labelsY_eq : _root_.Executable.labels (layout relayImageY) = _root_.Executable.labels (layout relayImageV) :=
  labels_mask relayImageY_mask
theorem labelsR_eq : _root_.Executable.labels (layout relayImageR) = _root_.Executable.labels (layout relayImageV) :=
  labels_mask relayImageR_mask

/-! ## The fragments' exits (any ambient code) -/

omit layout in
theorem writerFragV_last [CodeEnv] : ∀ l blk, Program.blockAt writerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label "wdone" :=
  Program.after_last_of (by decide)

omit layout in
theorem relayFragV_last [CodeEnv] : ∀ l blk, Program.blockAt relayFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label "rdone" :=
  Program.after_last_of (by decide)

omit layout in
theorem readerFragV_last [CodeEnv] : ∀ l blk, Program.blockAt readerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label "ddone" :=
  Program.after_last_of (by decide)

variable [Executable.ValidLayout (layout relayImageV)]

theorem relayImageW_valid : Executable.ValidLayout (layout relayImageW) := ValidLayout.of_mask relayImageW_mask
theorem relayImageY_valid : Executable.ValidLayout (layout relayImageY) := ValidLayout.of_mask relayImageY_mask
theorem relayImageR_valid : Executable.ValidLayout (layout relayImageR) := ValidLayout.of_mask relayImageR_mask

/-! ## The writer over its mask, on `EnvGX` -/

section Writer

local instance relayImageW.env : CodeEnv := ⟨layout relayImageW⟩

theorem writerFragW_placedIn : Program.PlacedIn writerFragV :=
  haveI := relayImageW_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relayImageW) relayImageW_wf rfl (by decide))
    writerFragW_sub

/-- The writer's table: `W1` at `writer`, `W3` at `wdone`. -/
abbrev writerTableW (P : Params) (tid : Nat) : Label → MachineData → (E P tid).State → Prop :=
  fun lb s σ => FrameRX P s ∧ ((lb = "writer" ∧ W1 P σ) ∨ (lb = "wdone" ∧ W3 P σ))

/-- The writer's run over its mask, at the mask's labels
(`mpWriterX_envG`'s VCs). -/
theorem writerW_envG' (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ W1 P g →
      Safely (cenv.instrStepEnv (E P tid))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "wdone" ∧ W3 P x.2) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "writer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := E P tid) (Q := fun _ σ => W3 P σ)
    (E := fun _ _ _ => False) (writerTableW P tid) ?_ rfl (by decide) writerFragW_placedIn
    writerFragV_last s g (by simpa [writerTableW] using hsg)
  cfg_cases_env [writerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre σ1 hf1 hl =>
    obtain ⟨⟨⟨-, hx1, -, -⟩, hT⟩, rfl, rfl⟩ := pre
    simp only [fenceMonoX_le_within, fenceMonoX_le_envG] at hf1
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx1
    exact vc_w1_ok hL tid σ1 (W1.fence hT hf1) (by simp [hx1]) (by simp [dataVal])
  case vc2 s σ pre σ1 hf1 dm σ2 hd σ3 hf2 hl2 =>
    obtain ⟨⟨⟨hx0, hx1, -, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp only [fenceMonoX_le_within, fenceMonoX_le_envG] at hf1 hf2
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    rcases hd with ⟨hsome, -, -⟩ | ⟨-, -, b, hst⟩
    · simp [hx1, hdd] at hsome
    · have hW2 := vc_w1_step hL tid σ1 (W1.fence hT hf1) (by simp [hx1]) (by simp [dataVal]) b σ2 hst
      exact vc_w2_ok hL tid σ3 (W2.fence hW2 hf2) (by simp [hx0]) (by simp)
  case vc3 s σ pre σ1 hf1 dm σ2 hd σ3 hf2 dm' σ4 hd' σ5 hf3 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp only [fenceMonoX_le_within, fenceMonoX_le_envG] at hf1 hf2 hf3
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    rcases hd with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst⟩
    · simp [hx1, hdd] at hsome
    · have hW2 := vc_w1_step hL tid σ1 (W1.fence hT hf1) (by simp [hx1]) (by simp [dataVal]) b σ2 hst
      rcases hd' with ⟨hsome, -, -⟩ | ⟨-, rfl, b', hst'⟩
      · simp [hx0, hdf] at hsome
      · have hW3 := vc_w2_step hL tid σ3 (W2.fence hW2 hf2) (by simp [hx0]) (by simp) b' σ4 hst'
        exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
          by simpa using hdd⟩, .inr ⟨rfl, W3.fence hW3 hf3⟩⟩, .inl (by decide)⟩
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Writer


/-! ## The relay over its mask, on the counted `EnvGTCX` -/

section Relay

local instance relayImageY.env : CodeEnv := ⟨layout relayImageY⟩

theorem relayFragY_placedIn : Program.PlacedIn relayFragV :=
  haveI := relayImageY_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relayImageY) relayImageY_wf rfl (by decide))
    relayFragY_sub

/-- The relay's table: `RK1` at `relay`, `RK4` at `rdone`. -/
abbrev relayTableY (rp : RP) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ERX rp tid)).State → Prop :=
  fun lb s σ => RFrameX rp s ∧ ((lb = "relay" ∧ RK1 rp σ.1) ∨ (lb = "rdone" ∧ RK4 rp σ.1))

/-- The relay's run over its mask, at the mask's labels (`relayX_envGTC`'s
script). -/
theorem relayY_envGTC' (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ∀ s g, RFrameX rp s ∧ RK1 rp g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ERX rp tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "rdone" ∧ RK4 rp x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "relay"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (ERX rp tid)) (Q := fun _ σ => RK4 rp σ.1)
    (E := fun _ _ _ => False) (relayTableY rp tid) ?_ rfl (by decide) relayFragY_placedIn
    relayFragV_last s g (by simpa [relayTableY] using hsg)
  cfg_cases_env [relayFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hl =>
    obtain ⟨⟨⟨hx0, -, -, -, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx0
    simp [hx0] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the back edge (`je` taken): `RK1` again; the counter moved
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK := (vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst.1).1 (by simpa using hz)
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf,
        by simpa using hdd, by simpa using hdg⟩, .inl ⟨rfl, RK1.fence (RK1.fence hK hf1.1) hf2.1⟩⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨-, hx1, -, -, hdd, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1, hdd]
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : RK2 rp σ3.1 := RK2.fence (RK2.fence
        ((vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst.1).2 (by simpa using hz)) hf1.1) hf2.1
      simp only [SharedEnv.counted_ok]
      exact vc_r2_ok_at hL σ3.1 hK2 (by simp [hx1]) (by decide)
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst σ5 hf3 =>
    obtain ⟨⟨⟨-, -, hx2, -, -, hdg⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx2
    simp [hx2, hdg]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst σ5 hf3 =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2 hf3
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : RK2 rp σ3.1 := RK2.fence (RK2.fence
        ((vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      have hK3 := vc_r2_at hL σ3.1 hK2 (by simp [hx1]) (by decide) b σ4.1 hst.1
      simp only [SharedEnv.counted_ok]
      exact vc_r3_ok_at hL σ5.1 (RK3.fence hK3 hf3.1) (by simp [hx2]) (rmwOp128_one (by simp))
  case vc7 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 b σ4 hst σ5 hf3 old σ6 hx σ7 hf4 =>
    obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdd, hdg⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTCX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : RK2 rp σ3.1 := RK2.fence (RK2.fence
        ((vc_r1_at σ.1 hT (by simp [hx0]) w σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      have hK3 := vc_r2_at hL σ3.1 hK2 (by simp [hx1]) (by decide) b σ4.1 hst.1
      have h4 := vc_r3_at hL σ5.1 (RK3.fence hK3 hf3.1) (by simp [hx2]) (rmwOp128_one (by simp)) old σ6.1 hx.1
      exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], hdf, hdd, hdg⟩,
        .inr ⟨rfl, RK4.fence h4 hf4.1⟩⟩, .inl (by decide)⟩
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Relay


/-! ## The reader over its mask, on the counted `EnvGTX` -/

section Reader

local instance relayImageR.env : CodeEnv := ⟨layout relayImageR⟩

theorem readerFragR_placedIn : Program.PlacedIn readerFragV :=
  haveI := relayImageR_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relayImageR) relayImageR_wf rfl (by decide))
    readerFragR_sub

/-- The reader's table on `f2`: `DK1` at `reader`; at `ddone`, `Own43` and,
under the clean flag, `ebx = 43`. -/
abbrev readerTableR (Q : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (EDX Q tid)).State → Prop :=
  fun lb s σ => FrameRX Q s ∧
    ((lb = "reader" ∧ DK1 Q σ.1) ∨
      (lb = "ddone" ∧ Own43 Q σ.1.r ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 43)))

/-- The reader's run over its mask, at the mask's labels (`readerX_envGT`'s
script). -/
theorem readerR_envGT' (Q : Params) (tid : Nat) :
    ∀ s g, FrameRX Q s ∧ DK1 Q g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EDX Q tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "ddone" ∧
          (Own43 Q x.2.1.r ∧ (x.2.1.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 43))) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "reader"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EDX Q tid))
    (Q := fun s σ => Own43 Q σ.1.r ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 43))
    (E := fun _ _ _ => False) (readerTableR Q tid) ?_ rfl (by decide) readerFragR_placedIn
    readerFragV_last s g (by simpa [readerTableR] using hsg)
  cfg_cases_env [readerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hl =>
    obtain ⟨⟨⟨hx0, -, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx0
    simp [hx0] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the back edge (`je` taken): `DK1` again; the counter moved
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK := (vc_d1_at σ.1 hT (by simp [hx0]) w σ1.1 hst.1).1 (by simpa using hz)
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inl ⟨rfl, DK1.fence (DK1.fence hK hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 hn =>
    obtain ⟨⟨⟨-, hx1, -, -⟩, -⟩, rfl, rfl⟩ := pre
    simp only [Reg64s.get64] at hx1
    simp [hx1] <;> trivial
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 w σ5 hld2 σ6 hf3 =>
    obtain ⟨⟨⟨hx0, hx1, hdf, hdd⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0 hx1
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3
    rcases hld with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hx0, hdf] at hm
    · have hK2 : DK2 Q σ3.1 := DK2.fence (DK2.fence
        ((vc_d1_at σ.1 hT (by simp [hx0]) u σ1.1 hst1.1).2 (by simpa using hz)) hf1.1) hf2.1
      rcases hld2 with ⟨y, hm, -, -⟩ | ⟨-, y, hst2, rfl⟩
      · simp [hx1, hdd] at hm
      · have h5 := vc_d2_at σ3.1 hK2 (by simp [hx1]) y σ5.1 hst2.1
        refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
          by simpa using hdd⟩, .inr ⟨rfl, by rw [hf3.1.r]; exact h5.1, fun hcl => ?_⟩⟩, .inl (by decide)⟩
        obtain rfl := h5.2 (hf3.1.cl ▸ hcl)
        simp
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Reader


/-! ## Only release writes, at the image -/

open Kraken.Promising.X64.EnvG.MpRelPure

/-- The frame of the writer and the reader: `%rdi = f`, `%rsi = d`, neither
word in `dmem`. -/
abbrev FrameM (f d : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none ∧ Mem.loadInt s.dmem d 4 = none

section Pure

local instance relayImageV.env : CodeEnv := ⟨layout relayImageV⟩

theorem writerFragV_placedIn : Program.PlacedIn writerFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relayImageV) relayImageV_wf rfl (by decide))
    writerFragV_sub

theorem relayFragV_placedIn : Program.PlacedIn relayFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relayImageV) relayImageV_wf rfl (by decide))
    relayFragV_sub

theorem readerFragV_placedIn : Program.PlacedIn readerFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := relayImageV) relayImageV_wf rfl (by decide))
    readerFragV_sub

/-- **The verbatim writer makes only release writes** (partial;
`mpWriterX_noNT`'s script). -/
theorem writerV_noNT (f d : BitVec 64) :
    ∀ s g, FrameM f d s →
      Safely (cenv.instrStepEnv (EnvR f d)) (fun x => (x.1.2 = labY "wdone" ∧ True) ∨ False)
        ((s, labY "writer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := EnvR f d) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun lb s _ => lb = "writer" → FrameM f d s) ?_ rfl (by decide)
    writerFragV_placedIn writerFragV_last s g (fun _ => hs)
  cfg_cases_env [writerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdf, hdd⟩ := hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals first
    | exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
    | (simp_all; done)
    | (simp_all; exact fun h => h rfl)
    | trivial

/-- **The verbatim relay makes only release writes** (counted, partial;
`relayX_noNT`'s script). -/
theorem relayV_noNT (f1 d f2 : BitVec 64) :
    ∀ s g, FrameY f1 d f2 s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRY f1 d f2)))
        (fun x => (x.1.2 = labY "rdone" ∧ True) ∨ False) ((s, labY "relay"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRY f1 d f2)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun lb s _ => lb = "relay" → FrameY f1 d f2 s) ?_ rfl (by decide)
    relayFragV_placedIn relayFragV_last s g (fun _ => hs)
  cfg_cases_env [relayFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc2 x σ1 hld _ _ =>
    -- the back edge: the frame again; the counter moved
    obtain ⟨hx0, hx1, hx2, hdf, hdd, hdg⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, -⟩
    · simp [hx0, hdf] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simp [hx2],
        by simpa using hdf, by simpa using hdd, by simpa using hdg⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      simp [SharedAccess.tick] at hn
  all_goals first
    | exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
    | (simp_all; done)
    | (simp_all; exact fun h => h rfl)
    | (simp_all; exact fun h => absurd rfl h)
    | (simp_all; trivial)
    | trivial

/-- **The verbatim reader makes only release writes** (counted, partial;
`MpInclAbs.readerV_noNT`'s script). -/
theorem readerV_noNT (f d : BitVec 64) :
    ∀ s g, FrameM f d s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvR f d))) (fun x => (x.1.2 = labY "ddone" ∧ True) ∨ False)
        ((s, labY "reader"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvR f d)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun lb s _ => lb = "reader" → FrameM f d s) ?_ rfl (by decide)
    readerFragV_placedIn readerFragV_last s g (fun _ => hs)
  cfg_cases_env [readerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdf, hdd⟩ := hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  case vc2 =>
    rename_i x σ1 hld hz _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      simp [SharedAccess.tick] at hn
  case vc4 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all
  all_goals trivial

end Pure

/-! ## The runs at the image's labels -/

/-- **The verbatim x64 MP writer on `EnvGX`, over its mask** (partial), at
the image's labels: from `W1` at `writer`, every run that reaches `wdone`
has `W3`. -/
theorem writerW_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    ∀ s g, FrameRX P s ∧ W1 P g →
      Safely ((layout relayImageW).instrStepEnv (E P tid))
        (fun x => (x.1.2 = labY "wdone" ∧ W3 P x.2) ∨ False) ((s, labY "writer"), g) := by
  have := writerW_envG' P hL tid
  change ∀ s g, FrameRX P s ∧ W1 P g →
      Safely ((layout relayImageW).instrStepEnv (E P tid))
        (fun x => (x.1.2 = (_root_.Executable.labels (layout relayImageW)).label "wdone" ∧ W3 P x.2) ∨ False)
        ((s, (_root_.Executable.labels (layout relayImageW)).label "writer"), g) at this
  rw [labelsW_eq] at this
  exact this

/-- **The verbatim x64 relay on `EnvGTCX`, over its mask** (counted,
partial), at the image's labels. -/
theorem relayY_envGTC (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    ∀ s g, RFrameX rp s ∧ RK1 rp g.1 →
      Safely ((layout relayImageY).instrStepEnv (SharedEnv.counted (ERX rp tid)))
        (fun x => (x.1.2 = labY "rdone" ∧ RK4 rp x.2.1) ∨ False) ((s, labY "relay"), g) := by
  have := relayY_envGTC' rp hL tid
  change ∀ s g, RFrameX rp s ∧ RK1 rp g.1 →
      Safely ((layout relayImageY).instrStepEnv (SharedEnv.counted (ERX rp tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels (layout relayImageY)).label "rdone" ∧ RK4 rp x.2.1) ∨ False)
        ((s, (_root_.Executable.labels (layout relayImageY)).label "relay"), g) at this
  rw [labelsY_eq] at this
  exact this

/-- **The verbatim x64 MP reader on `EnvGTX`, over its mask** (counted,
partial), at the image's labels. -/
theorem readerR_envGT (Q : Params) (tid : Nat) :
    ∀ s g, FrameRX Q s ∧ DK1 Q g.1 →
      Safely ((layout relayImageR).instrStepEnv (SharedEnv.counted (EDX Q tid)))
        (fun x => (x.1.2 = labY "ddone" ∧
          (Own43 Q x.2.1.r ∧ (x.2.1.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 43))) ∨ False)
        ((s, labY "reader"), g) := by
  have := readerR_envGT' Q tid
  change ∀ s g, FrameRX Q s ∧ DK1 Q g.1 →
      Safely ((layout relayImageR).instrStepEnv (SharedEnv.counted (EDX Q tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels (layout relayImageR)).label "ddone" ∧
          (Own43 Q x.2.1.r ∧ (x.2.1.cl → (x.1.1.regs.get64 .rbx).setWidth 32 = 43))) ∨ False)
        ((s, (_root_.Executable.labels (layout relayImageR)).label "reader"), g) at this
  rw [labelsR_eq] at this
  exact this

end Kraken.Promising.X64.EnvG.RelayAbs

#print axioms Kraken.Promising.X64.EnvG.RelayAbs.writerW_envG
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.relayY_envGTC
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.readerR_envGT
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.writerV_noNT
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.relayV_noNT
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.readerV_noNT
