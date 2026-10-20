/-
**The x64 SPSC queue of `spsc_queue.kl`, the `.kl` code verbatim, on
`EnvGTX` by `vcgen`, over masked images**: the `code`
block of `Kraken/Examples/LockFree/X64/spsc_queue.kl` as written
(`spscCodeV`: the producer with `(tail)`/`(head)` absolute, `pdone:`, the
consumer, `cdone:`), run by both threads in its image `spscImageV` (the
code, then the `.kl` runner's data trailer `spscDataV`: `buf0`, `buf1`,
`head`, `tail`). The x64 SPSC proof's theorem proves `spscProducerX`/`spscConsumerX`,
whose `(tail)`/`(head)` are `(%rdi)`/`(%rsi)`, each laid out alone.

- **Masks** (`EnvG/X64MaskCore.lean`): the producer runs over
  `spscImageP` (cells `0 … 19` kept: the consumer's code, which follows
  `pdone:`, is data, so the mask halts at `pdone`), the consumer over
  `spscImageC` (cells `20 … 53` kept).
- **Absolute operands**: `(tail)`/`(head)` are the x64 absolute-address proofs' `@[spec]` rules
  (`Kraken/EnvVCGenAbs.lean`); the address is `absAddr "tail"`, the label's
  address in the ambient code, which the runs take as hypotheses
  (`ht : absAddr "tail" = P.t`, `hh : absAddr "head" = P.h`).
- **The scripts and VCs are the x64 SPSC proof's** (`EnvG/X64SpscVCGen.lean`,
  `EnvG/X64SpscVC.lean`), mechanically adapted: the frame `FrameA`
  (`rbx = b`, no 4-byte word in the private memory) drops `rdi`/`rsi`, and
  the address equations are `ht`/`hh`.
- `spscProducerP_envGT`, `spscConsumerC_envGT`: the runs in the counted
  `EnvGTX`, over the masks, at the image's labels;
- `spscProducerV_noNT`, `spscConsumerV_noNT`: the runs in the all-release
  environment at the unmasked image (the x64 SPSC proof's `…_noNT` scripts, unchanged).
-/
import Kraken.Promising.SLR.EnvG.X64SpscVCGen
import Kraken.Promising.SLR.EnvG.X64SpscRelPure
import Kraken.Promising.SLR.EnvG.X64MaskLinkTake
import Kraken.Promising.SLR.EnvG.X64ImageNoFault
import Kraken.EnvVCGenAbs
import Kraken.EnvCfgAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpscX Kraken.Promising.X64.EnvG.TreiberX
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.SpscAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program, its image and the masks -/

/-- **The `code` block of `spsc_queue.kl`, verbatim.** -/
def spscCodeV : Program := parse("
producer:
  movl $1,%r8d
produce:
  movl (tail),%eax
  movl %eax,%ecx
  addl $1,%ecx
  andl $1,%ecx
pfull:
  movl (head),%edx
  cmpl %ecx,%edx
  je pfull
  movl %eax,%edx
  shll $8,%edx
  movl %r8d,(%rbx,%rdx,1)
  movl %ecx,(tail)
  addl $1,%r8d
  cmpl $4,%r8d
  jne produce
  jmp pdone
pdone:

consumer:
  movl (head),%eax
cempty0:
  movl (tail),%ecx
  cmpl %eax,%ecx
  je cempty0
  movl %eax,%edx
  shll $8,%edx
  movl (%rbx,%rdx,1),%r12d
  addl $1,%eax
  andl $1,%eax
  movl %eax,(head)
cempty1:
  movl (tail),%ecx
  cmpl %eax,%ecx
  je cempty1
  movl %eax,%edx
  shll $8,%edx
  movl (%rbx,%rdx,1),%r13d
  addl $1,%eax
  andl $1,%eax
  movl %eax,(head)
cempty2:
  movl (tail),%ecx
  cmpl %eax,%ecx
  je cempty2
  movl %eax,%edx
  shll $8,%edx
  movl (%rbx,%rdx,1),%r14d
  addl $1,%eax
  andl $1,%eax
  movl %eax,(head)
  jmp cdone
cdone:
")

/-- info: 54 -/
#guard_msgs in
#eval spscCodeV.length

/-- The `.kl` runner's data trailer of `spsc_queue.kl`: each symbol a label
behind a padding cell, in the order of the init block (`buf0`, `buf1`,
`head`, `tail`). -/
def spscDataV : Program :=
  [.byteArray (.mk #[]), .label "buf0", .byteArray (.mk #[]), .label "buf1",
   .byteArray (.mk #[]), .label "head", .byteArray (.mk #[]), .label "tail"]

/-- The image: the code, then the data trailer. -/
def spscImageV : Program := spscCodeV ++ spscDataV

/-- The producer's fragment of the image (cells `0 … 19`). -/
def producerFragV : Program := spscImageV.take 20

/-- The consumer's fragment of the image (cells `20 … 53`). -/
def consumerFragV : Program := (spscImageV.drop 20).take 34

/-- **The producer's mask**: cells `0 … 19` kept. -/
def spscImageP : Program := spscImageV.maskKeep (keepRange 0 20)

/-- **The consumer's mask**: cells `20 … 53` kept. -/
def spscImageC : Program := spscImageV.maskKeep (keepRange 20 54)

theorem spscImageV_wf : Program.WF spscImageV := by decide
theorem spscImageP_wf : Program.WF spscImageP := by decide
theorem spscImageC_wf : Program.WF spscImageC := by decide

theorem producerFragV_sub : Program.subBlocksOfE producerFragV spscImageV = true := by decide
theorem consumerFragV_sub : Program.subBlocksOfE consumerFragV spscImageV = true := by decide
theorem producerFragP_sub : Program.subBlocksOfE producerFragV spscImageP = true := by decide
theorem consumerFragC_sub : Program.subBlocksOfE consumerFragV spscImageC = true := by decide

theorem producerFragV_eq : producerFragV = Directive.label "producer" :: producerFragV.tail := by decide
theorem consumerFragV_eq : consumerFragV = Directive.label "consumer" :: consumerFragV.tail := by decide
theorem producerFragV_wf : Program.WF producerFragV := by decide
theorem consumerFragV_wf : Program.WF consumerFragV := by decide

/-- The producer's mask's first cell after `pdone:` and `consumer:` is a
data cell. -/
theorem spscImageP_21 : spscImageP[21]? = some (.byteArray (.mk #[])) := by decide

/-- The consumer's mask's cell after `cdone:` is a data cell. -/
theorem spscImageC_54 : spscImageC[54]? = some (.byteArray (.mk #[])) := by decide

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labS (x : Label) : Int64 := (_root_.Executable.labels (layout spscImageV)).label x

/-- A symbol's address in the image. -/
abbrev symS (x : Label) : BitVec 64 := (labS x).toBitVec

theorem spscImageP_mask : MaskOf (layout spscImageV) (layout spscImageP) := maskOf_layout _ _
theorem spscImageC_mask : MaskOf (layout spscImageV) (layout spscImageC) := maskOf_layout _ _

theorem labelsP_eq : _root_.Executable.labels (layout spscImageP) = _root_.Executable.labels (layout spscImageV) :=
  labels_mask spscImageP_mask
theorem labelsC_eq : _root_.Executable.labels (layout spscImageC) = _root_.Executable.labels (layout spscImageV) :=
  labels_mask spscImageC_mask

/-! ## The fragments' exits (any ambient code) -/

omit layout in
/-- The producer's only block without successor is `pdone`'s, empty. -/
theorem producerFragV_last [CodeEnv] : ∀ l blk, Program.blockAt producerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label "pdone" :=
  Program.after_last_of (by decide)

omit layout in
/-- The consumer's only block without successor is `cdone`'s, empty. -/
theorem consumerFragV_last [CodeEnv] : ∀ l blk, Program.blockAt consumerFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label "cdone" :=
  Program.after_last_of (by decide)

variable [Executable.ValidLayout (layout spscImageV)]

theorem spscImageP_valid : Executable.ValidLayout (layout spscImageP) := ValidLayout.of_mask spscImageP_mask
theorem spscImageC_valid : Executable.ValidLayout (layout spscImageC) := ValidLayout.of_mask spscImageC_mask

/-! ## The tables -/

/-- The frame of both threads: `rbx = b`, no 4-byte word in the private
memory (`FrameP` without `rdi`/`rsi`). -/
abbrev FrameA (P : SP) (s : MachineData) : Prop := s.regs.get64 .rbx = P.b ∧ DFrame s

/-- The producer's table (`prodTable` with `FrameA`). -/
abbrev prodTableA (P : SP) (tid : Nat) : Label → MachineData → (SharedEnv.counted (EP P tid)).State → Prop :=
  fun lb s σ => FrameA P s ∧
    ((lb = "producer" ∧ PR P 1 σ.1) ∨
     (lb = "produce" ∧ ∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧ (s.regs.get64 .r8).setWidth 32 = BitVec.ofNat 32 k ∧
        PR P k σ.1) ∨
     (lb = "pfull" ∧ ∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧ (s.regs.get64 .r8).setWidth 32 = BitVec.ofNat 32 k ∧
        (s.regs.get64 .rax).setWidth 32 = (eT k).setWidth 32 ∧ (s.regs.get64 .rcx).setWidth 32 = (tNew k).setWidth 32 ∧
        PR P k σ.1) ∨
     (lb = "pdone" ∧ (σ.1.r.wr P.T).q = 1))

/-- The consumer's table (`consTable` with `FrameA`). -/
abbrev consTableA (P : SP) (tid : Nat) : Label → MachineData → (SharedEnv.counted (EC P tid)).State → Prop :=
  fun lb s σ => FrameA P s ∧
    ((lb = "consumer" ∧ CS P σ.1) ∨ (lb = "cempty0" ∧ CR P 0 s σ.1) ∨ (lb = "cempty1" ∧ CR P 1 s σ.1) ∨
      (lb = "cempty2" ∧ CR P 2 s σ.1) ∨ (lb = "cdone" ∧ (σ.1.cl → Got 3 s)))

/-! ## The producer over its mask -/

section Producer

local instance spscImageP.env : CodeEnv := ⟨layout spscImageP⟩

theorem producerFragP_placedIn : Program.PlacedIn producerFragV :=
  haveI := spscImageP_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageP) spscImageP_wf rfl (by decide))
    producerFragP_sub

set_option maxHeartbeats 1000000 in
/-- The producer's run over its mask, at the mask's labels
(`spscProducerX_envGT`'s script). -/
theorem spscProducerP_envGT' (P : SP) (hL : SpscLocs P) (tid : Nat)
    (ht : absAddr "tail" = P.t) (hh : absAddr "head" = P.h) :
    ∀ s g, FrameA P s ∧ PR P 1 g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EP P tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "pdone" ∧ (x.2.1.r.wr P.T).q = 1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "producer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EP P tid)) (Q := fun _ σ => (σ.1.r.wr P.T).q = 1)
    (E := fun _ _ _ => False) (prodTableA P tid) ?_ producerFragV_eq producerFragV_wf producerFragP_placedIn
    producerFragV_last s g (by simpa [prodTableA] using hsg)
  cfg_cases_env [producerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre σ1 hf =>
    -- `producer` → `produce`
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf
    refine ⟨⟨by simp [hx0], by simpa using hdf⟩,
      .inr (.inl ⟨rfl, 1, .inl rfl, by simp, hT.fence hf.1⟩)⟩
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp [ht] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 σ3 hf2 af σ4 hf3 =>
    -- `produce` → `pfull`
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hr8
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [ht, hdf] at hm
    · obtain ⟨hv, hPR'⟩ := vcP_loadT_at hL hPR (by simp [ht]) hst.1
      refine ⟨⟨by simp [hx0], by simpa using hdf⟩,
        .inr (.inr (.inl ⟨rfl, k, hk, by simpa using hr8, ?_, ?_, ((hPR'.fence hf1.1).fence hf2.1).fence hf3.1⟩))⟩
      · subst hv; simp
      · subst hv; rcases hk with rfl | rfl | rfl <;> simp [eT, tNew]
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp [hh] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je pfull` back edge
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hh, hdf] at hm
    · have hz' : w.setWidth 32 = (tNew k).setWidth 32 := by
        have h0 : w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
        bv_omega
      have hPR' := (vcP_spin_at hL hk hPR (by simp [hh]) hst.1).1 hz'
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩,
        .inr (.inr (.inl ⟨rfl, k, hk, by simpa using hr8, by simpa using hax, by simpa using hcx,
          (hPR'.fence hf1.1).fence hf2.1⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
    · simp [hh, hdf] at hm
    · have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
        have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
        bv_omega
      have hPX := (vcP_spin_at hL hk hPR (by simp [hh]) hst.1).2 hz'
      have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
      refine vcP_storeB_ok_at hL hPX' ?_ ?_
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 dm σ6 hst hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hh, hdf] at hm
    have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
      bv_omega
    have hPX := (vcP_spin_at hL hk hPR (by simp [hh]) hst0.1).2 hz'
    have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hPD : PD P k σ6.1 := by
      refine vcP_storeB_at hL hPX' ?_ ?_ _ _ hs.1
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
    refine vcP_storeT_ok_at hL hk hPD (by simp [ht]) ?_
    simp [hcx]
    rcases hk with rfl | rfl | rfl <;> simp [tNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 dm σ6 hst dm2 σ7 hst2 σ8 hf5 σ9 hf6 hnz σ10 hf7 =>
    -- the `jne produce` back edge (rounds 1, 2)
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hh, hdf] at hm
    have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
      bv_omega
    have hPX := (vcP_spin_at hL hk hPR (by simp [hh]) hst0.1).2 hz'
    have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hPD : PD P k σ6.1 := by
      refine vcP_storeB_at hL hPX' ?_ ?_ _ _ hs.1
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
    rcases hst2 with ⟨hv, -⟩ | ⟨-, rfl, b2, hs2⟩
    · simp [hdf] at hv
    have hR := by
      refine vcP_storeT_at hL hk hPD ?_ ?_ _ _ hs2.1
      · simp [ht]
      · simp [hcx]
        rcases hk with rfl | rfl | rfl <;> simp [tNew]
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf5 hf6 hf7
    simp [hr8] at hnz
    have c0 := hst0.2; have c1 := hs.2; have c2 := hs2.2
    have e1 := hf1.2; have e2 := hf2.2; have e3 := hf3.2; have e4 := hf4.2
    have e5 := hf5.2; have e6 := hf6.2; have e7 := hf7.2
    rcases hk with rfl | rfl | rfl
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩,
        .inr (.inl ⟨rfl, 2, .inr (.inl rfl), by simp [hr8], (((hR.1 rfl).fence hf5.1).fence hf6.1).fence hf7.1⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg; simp [SharedAccess.tick] at c0 c1 c2; omega
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩,
        .inr (.inl ⟨rfl, 3, .inr (.inr rfl), by simp [hr8], (((hR.2.1 rfl).fence hf5.1).fence hf6.1).fence hf7.1⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg; simp [SharedAccess.tick] at c0 c1 c2; omega
    · exact absurd (by decide) hnz
  case vc7 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 dm σ6 hst dm2 σ7 hst2 σ8 hf5 σ9 hf6 hnz σ10 hf7
      σ11 hf8 =>
    -- the fall-through after round 3, `jmp pdone`
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨k, hk, hr8, hax, hcx, hPR⟩ := hT
    simp only [Reg64s.get64] at hx0 hr8 hax hcx
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hh, hdf] at hm
    have hz' : w.setWidth 32 ≠ (tNew k).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (tNew k).setWidth 32 = 0#32 := by simpa [hcx] using hz
      bv_omega
    have hPX := (vcP_spin_at hL hk hPR (by simp [hh]) hst0.1).2 hz'
    have hPX' := (((hPX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hPD : PD P k σ6.1 := by
      refine vcP_storeB_at hL hPX' ?_ ?_ _ _ hs.1
      · simp [hx0, hax, Reg64s.get_low32]
        rcases hk with rfl | rfl | rfl <;> simp [eT, slot]
      · simp [hr8]
        rcases hk with rfl | rfl | rfl <;> simp [kval]
    rcases hst2 with ⟨hv, -⟩ | ⟨-, rfl, b2, hs2⟩
    · simp [hdf] at hv
    have hR := by
      refine vcP_storeT_at hL hk hPD ?_ ?_ _ _ hs2.1
      · simp [ht]
      · simp [hcx]
        rcases hk with rfl | rfl | rfl <;> simp [tNew]
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf5 hf6 hf7 hf8
    have hq := q_fence (q_fence (q_fence (q_fence hR.2.2 hf5.1) hf6.1) hf7.1) hf8.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inr (.inr ⟨rfl, hq⟩))⟩, .inl (by decide)⟩
  case vc1 s σ pre =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    exact hT

end Producer

/-! ## The consumer over its mask -/

section Consumer

local instance spscImageC.env : CodeEnv := ⟨layout spscImageC⟩

theorem consumerFragC_placedIn : Program.PlacedIn consumerFragV :=
  haveI := spscImageC_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageC) spscImageC_wf rfl (by decide))
    consumerFragC_sub

set_option maxHeartbeats 1000000 in
/-- The consumer's run over its mask, at the mask's labels
(`spscConsumerX_envGT`'s script). -/
theorem spscConsumerC_envGT' (P : SP) (hL : SpscLocs P) (tid : Nat)
    (ht : absAddr "tail" = P.t) (hh : absAddr "head" = P.h) :
    ∀ s g, FrameA P s ∧ CS P g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EC P tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "cdone" ∧ (x.2.1.cl → Got 3 x.1.1)) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "consumer"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EC P tid)) (Q := fun s σ => σ.1.cl → Got 3 s)
    (E := fun _ _ _ => False) (consTableA P tid) ?_ consumerFragV_eq consumerFragV_wf consumerFragC_placedIn
    consumerFragV_last s g (by simpa [consTableA] using hsg)
  cfg_cases_env [consumerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp [hh] <;> trivial
  case vc2 s σ pre v σ1 hld =>
    -- `consumer` → `cempty0`
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hT
    simp only [Reg64s.get64] at hx0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [hh, hdf] at hm
    obtain ⟨rfl, hCE⟩ := vcC_loadH_at hL hT (by simp [hh]) hst0.1
    exact ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inl ⟨rfl, hCE, by simp [eC], fun _ => by simp⟩)⟩
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp [ht] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je cempty0` back edge
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 = (eC 0).setWidth 32 := by
      have h0 : w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCE' := (vcC_spin_at (k := 0) (by decide) hCE (by simp [ht]) hst0.1).1 hz'
    have hn := hst0.2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inl ⟨rfl, (hCE'.fence hf1.1).fence hf2.1,
      by simpa using hax, fun hc => ?_⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp
    · subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 0).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 0) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    simp [hx0, hax, Reg64s.get_low32, eC] <;> trivial
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 0).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 0) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 0 σ6.1 ∧ (σ6.1.cl → u = cval 0) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    refine vcC_storeH_ok_at hL (k := 0) (by decide) hCX8 (by simp [hh]) ?_
    simp [hax, eC, hNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 dm σ9 hst =>
    -- the end of round 0
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 0).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 0).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 0) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 0 σ6.1 ∧ (σ6.1.cl → u = cval 0) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hR : (((0 : Nat) = 0 → CE P 1 σ9.1) ∧ ((0 : Nat) = 1 → CE P 2 σ9.1)) ∧ σ9.1.cl = σ8.1.cl := by
      refine vcC_storeH_at hL (k := 0) (by decide) hCX8 ?_ ?_ _ _ hs.1
      · simp [hh]
      · simp [hax, eC, hNew]
    have hcl : σ9.1.cl → σ.1.cl ∧ u = cval 0 := fun hc => by
      have h6 : σ6.1.cl := cl_fence hf5.1 (cl_fence hf6.1 (hR.2 ▸ hc))
      exact ⟨(loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 (cl_fence hf3.1 (cl_fence hf4.1
        ((loadKeep hst1.1).cl h6))))), hD.2 h6⟩
    refine ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inr (.inl ⟨rfl, hR.1.1 rfl, by simp [hax, eC], fun hc => ?_⟩))⟩
    obtain ⟨hc0, rfl⟩ := hcl hc
    have := hgot hc0
    simp [cval] at this ⊢ <;> exact this
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp [ht] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je cempty1` back edge
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 = (eC 1).setWidth 32 := by
      have h0 : w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCE' := (vcC_spin_at (k := 1) (by decide) hCE (by simp [ht]) hst0.1).1 hz'
    have hn := hst0.2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inr (.inl ⟨rfl, (hCE'.fence hf1.1).fence hf2.1,
      by simpa using hax, fun hc => ?_⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · have := hgot ((loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 hc)))
      simpa using this
    · subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 1).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 1) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    simp [hx0, hax, Reg64s.get_low32, eC] <;> trivial
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 1).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 1) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 1 σ6.1 ∧ (σ6.1.cl → u = cval 1) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    refine vcC_storeH_ok_at hL (k := 1) (by decide) hCX8 (by simp [hh]) ?_
    simp [hax, eC, hNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 dm σ9 hst =>
    -- the end of round 1
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 1).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 1).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 1) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 1 σ6.1 ∧ (σ6.1.cl → u = cval 1) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hR : (((1 : Nat) = 0 → CE P 1 σ9.1) ∧ ((1 : Nat) = 1 → CE P 2 σ9.1)) ∧ σ9.1.cl = σ8.1.cl := by
      refine vcC_storeH_at hL (k := 1) (by decide) hCX8 ?_ ?_ _ _ hs.1
      · simp [hh]
      · simp [hax, eC, hNew]
    have hcl : σ9.1.cl → σ.1.cl ∧ u = cval 1 := fun hc => by
      have h6 : σ6.1.cl := cl_fence hf5.1 (cl_fence hf6.1 (hR.2 ▸ hc))
      exact ⟨(loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 (cl_fence hf3.1 (cl_fence hf4.1
        ((loadKeep hst1.1).cl h6))))), hD.2 h6⟩
    refine ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inr (.inr (.inl ⟨rfl, hR.1.2 rfl, by simp [hax, eC], fun hc => ?_⟩)))⟩
    obtain ⟨hc0, rfl⟩ := hcl hc
    have := hgot hc0
    simp [cval] at this ⊢ <;> exact this
  case vc1 s σ pre hdm =>
    obtain ⟨⟨⟨-, hdf⟩, -⟩, rfl, rfl⟩ := pre
    simp [ht] <;> trivial
  case vc2 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 =>
    -- the `je cempty2` back edge
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 = (eC 2).setWidth 32 := by
      have h0 : w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCE' := (vcC_spin_at (k := 2) (by decide) hCE (by simp [ht]) hst0.1).1 hz'
    have hn := hst0.2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inr (.inr (.inl ⟨rfl, (hCE'.fence hf1.1).fence hf2.1,
      by simpa using hax, fun hc => ?_⟩)))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · have := hgot ((loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 hc)))
      simpa using this
    · subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 => simp
  case vc4 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 2).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 2) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    simp [hx0, hax, Reg64s.get_low32, eC] <;> trivial
  case vc5 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 hdm =>
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 2).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 2) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 2 σ6.1 ∧ (σ6.1.cl → u = cval 2) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    refine vcC_storeH_ok_at hL (k := 2) (by decide) hCX8 (by simp [hh]) ?_
    simp [hax, eC, hNew]
  case vc6 s σ pre v σ1 hld σ2 hf1 hz σ3 hf2 σ4 hf3 fl σ5 hf4 v2 σ6 hld2 σ7 hf5 af σ8 hf6 dm σ9 hst σ10 hf7 =>
    -- the end of round 2
    obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
    obtain ⟨hCE, hax, hgot⟩ := hT
    simp only [Reg64s.get64] at hx0 hax hgot
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX] at hf1 hf2 hf3 hf4 hf5 hf6 hf7
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst0, rfl⟩
    · simp [ht, hdf] at hm
    have hz' : w.setWidth 32 ≠ (eC 2).setWidth 32 := by
      have h0 : ¬ w.setWidth 32 - (eC 2).setWidth 32 = 0#32 := by simpa [hax] using hz
      bv_omega
    have hCX := (vcC_spin_at (k := 2) (by decide) hCE (by simp [ht]) hst0.1).2 hz'
    have hCX' := (((hCX.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst1, rfl⟩
    · simp [hdf] at hm
    have hD : CX P 2 σ6.1 ∧ (σ6.1.cl → u = cval 2) := by
      refine vcC_data_at hL hCX' ?_ hst1.1
      simp [hx0, hax, Reg64s.get_low32, eC, cslot]
    have hCX8 := (hD.1.fence hf5.1).fence hf6.1
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, b, hs⟩
    · simp [hdf] at hv
    have hR : (((2 : Nat) = 0 → CE P 1 σ9.1) ∧ ((2 : Nat) = 1 → CE P 2 σ9.1)) ∧ σ9.1.cl = σ8.1.cl := by
      refine vcC_storeH_at hL (k := 2) (by decide) hCX8 ?_ ?_ _ _ hs.1
      · simp [hh]
      · simp [hax, eC, hNew]
    have hcl : σ9.1.cl → σ.1.cl ∧ u = cval 2 := fun hc => by
      have h6 : σ6.1.cl := cl_fence hf5.1 (cl_fence hf6.1 (hR.2 ▸ hc))
      exact ⟨(loadKeep hst0.1).cl (cl_fence hf1.1 (cl_fence hf2.1 (cl_fence hf3.1 (cl_fence hf4.1
        ((loadKeep hst1.1).cl h6))))), hD.2 h6⟩
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, .inr (.inr (.inr (.inr ⟨rfl, fun hc => ?_⟩)))⟩, .inl (by decide)⟩
    obtain ⟨hc0, rfl⟩ := hcl (cl_fence hf7.1 hc)
    have := hgot hc0
    simp [cval] at this ⊢ <;> exact this
  case vc1 s σ pre hcl =>
    obtain ⟨⟨-, hT⟩, rfl, rfl⟩ := pre
    simp (config := { decide := true }) only [true_and, false_and, false_or] at hT
    simpa using hT hcl

end Consumer

/-! ## Only release writes, at the image -/

section Pure

local instance spscImageV.env : CodeEnv := ⟨layout spscImageV⟩

theorem producerFragV_placedIn : Program.PlacedIn producerFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageV) spscImageV_wf rfl (by decide))
    producerFragV_sub

theorem consumerFragV_placedIn : Program.PlacedIn consumerFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spscImageV) spscImageV_wf rfl (by decide))
    consumerFragV_sub

/-- **The verbatim producer makes only release writes** (counted, partial;
`spscProducerX_noNT`'s script). -/
theorem spscProducerV_noNT :
    ∀ s g, DFrame s →
      Safely (cenv.instrStepEnv (SharedEnv.counted EnvRA))
        (fun x => (x.1.2 = labS "pdone" ∧ True) ∨ False) ((s, labS "producer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted EnvRA) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted EnvRA).State) => DFrame s) ?_
    producerFragV_eq producerFragV_wf producerFragV_placedIn producerFragV_last s g hs
  cfg_cases_env [producerFragV]
  spsc_noNT_producer

/-- **The verbatim consumer makes only release writes** (counted, partial;
`spscConsumerX_noNT`'s script). -/
theorem spscConsumerV_noNT :
    ∀ s g, DFrame s →
      Safely (cenv.instrStepEnv (SharedEnv.counted EnvRA))
        (fun x => (x.1.2 = labS "cdone" ∧ True) ∨ False) ((s, labS "consumer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted EnvRA) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted EnvRA).State) => DFrame s) ?_
    consumerFragV_eq consumerFragV_wf consumerFragV_placedIn consumerFragV_last s g hs
  cfg_cases_env [consumerFragV]
  spsc_noNT_consumer

end Pure

/-! ## The runs at the image's labels -/

/-- **The verbatim x64 SPSC producer on `EnvGTX`, over its mask** (counted,
partial), at the image's labels and symbols. -/
theorem spscProducerP_envGT (P : SP) (hL : SpscLocs P) (tid : Nat) (ht : symS "tail" = P.t)
    (hh : symS "head" = P.h) :
    ∀ s g, FrameA P s ∧ PR P 1 g.1 →
      Safely ((layout spscImageP).instrStepEnv (SharedEnv.counted (EP P tid)))
        (fun x => (x.1.2 = labS "pdone" ∧ (x.2.1.r.wr P.T).q = 1) ∨ False) ((s, labS "producer"), g) := by
  have := spscProducerP_envGT' P hL tid
    (by show ((_root_.Executable.labels (layout spscImageP)).label "tail").toBitVec = P.t
        rw [labelsP_eq]; exact ht)
    (by show ((_root_.Executable.labels (layout spscImageP)).label "head").toBitVec = P.h
        rw [labelsP_eq]; exact hh)
  change ∀ s g, FrameA P s ∧ PR P 1 g.1 →
      Safely ((layout spscImageP).instrStepEnv (SharedEnv.counted (EP P tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels (layout spscImageP)).label "pdone" ∧ (x.2.1.r.wr P.T).q = 1) ∨ False)
        ((s, (_root_.Executable.labels (layout spscImageP)).label "producer"), g) at this
  rw [labelsP_eq] at this
  exact this

/-- **The verbatim x64 SPSC consumer on `EnvGTX`, over its mask** (counted,
partial), at the image's labels and symbols. -/
theorem spscConsumerC_envGT (P : SP) (hL : SpscLocs P) (tid : Nat) (ht : symS "tail" = P.t)
    (hh : symS "head" = P.h) :
    ∀ s g, FrameA P s ∧ CS P g.1 →
      Safely ((layout spscImageC).instrStepEnv (SharedEnv.counted (EC P tid)))
        (fun x => (x.1.2 = labS "cdone" ∧ (x.2.1.cl → Got 3 x.1.1)) ∨ False) ((s, labS "consumer"), g) := by
  have := spscConsumerC_envGT' P hL tid
    (by show ((_root_.Executable.labels (layout spscImageC)).label "tail").toBitVec = P.t
        rw [labelsC_eq]; exact ht)
    (by show ((_root_.Executable.labels (layout spscImageC)).label "head").toBitVec = P.h
        rw [labelsC_eq]; exact hh)
  change ∀ s g, FrameA P s ∧ CS P g.1 →
      Safely ((layout spscImageC).instrStepEnv (SharedEnv.counted (EC P tid)))
        (fun x => (x.1.2 = (_root_.Executable.labels (layout spscImageC)).label "cdone" ∧ (x.2.1.cl → Got 3 x.1.1)) ∨ False)
        ((s, (_root_.Executable.labels (layout spscImageC)).label "consumer"), g) at this
  rw [labelsC_eq] at this
  exact this

end Kraken.Promising.X64.EnvG.SpscAbs

#print axioms Kraken.Promising.X64.EnvG.SpscAbs.spscProducerP_envGT
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.spscConsumerC_envGT
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.spscProducerV_noNT
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.spscConsumerV_noNT
