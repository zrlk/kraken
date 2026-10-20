/-
**Part 4: the x64 `msqueue2.kl`, the `.kl`
code verbatim, on `EnvGCAdjX` by `vcgen`.**

The `code` block of `Kraken/Examples/LockFree/X64/msqueue2.kl` as written
(`msq2CodeV`), in its image `msq2ImageV` (the code, then the `.kl` runner's
data trailer `msq2DataV`: `s`, `n1`, `n2`, `head`, `tail`). The threads run
their fragments of the image (`Program.subBlocksOfE`, by `decide`):

- the enqueuer (thread `0`) `enqFragV`, from `enqueuer` to `edone`, over the
  **mask** `msq2ImageM` (the cells from the dequeuer's code on are data
  cells, so the mask has no step at `edone`: `enqM_stuck`);
- the dequeuer (thread `1`) `deqFragV`, from `dequeuer` to `ddone`, over the
  image (its exit `ddone` is followed by the data trailer: `deqV_stuck`).

The absolute operands use `Kraken/EnvVCGenAbs64.lean` and
`Kraken/EnvVCGenAbs64b.lean` (`cmpq %r,(sym)`), the placement
`cfgEnv_partial_at` (`Kraken/EnvCfgAbs.lean`), the VCs
`EnvG/X64MsQueue2VC.lean`.

- `enqM_envGCAdj` (at the image's labels; `enqM_envGCAdj'` at the mask's),
  `deqV_envGCAdj'`: the runs in the counted `EnvGCAdjX … sAll`;
- `enqM_stuck`, `deqV_stuck`: the halts at the exit labels;
- `enqV_noNT`, `deqV_noNT`: the runs (the image) in the all-release
  environment `EnvRT sAll` (`cnt_all` collects the access counts).

Performance notes (the x64 states are large terms): copy a hypothesis with
`have` before destructuring it; `dsimp only` before landing on a table entry
(`Table.ofLabelsEnv_at`), else elaboration and the `.olean` blow up.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2VC
import Kraken.Promising.SLR.EnvG.X64Treiber2VCGen
import Kraken.Promising.SLR.EnvG.X64MaskCore
import Kraken.EnvCfgAbs
import Kraken.EnvVCGenAbs64
import Kraken.EnvVCGenAbs64b

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 sAll mem_sAll8)
open Kraken.Promising.X64.EnvG.Treiber2X (stepL stepS stepR okR ldN stN)
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MsQueueX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program, its image and the mask -/

/-- **The `code` block of `msqueue2.kl`, verbatim.** -/
def msq2CodeV : Program := parse("
enqueuer:
  movq $n1,%rsi
enq:
  movq (tail),%rbx
  movq (%rbx),%rcx
  cmpq %rbx,(tail)
  jne enq
  testq %rcx,%rcx
  jne enq_swing
  xorl %eax,%eax
  lock cmpxchgq %rsi,(%rbx)
  jne enq
  movq %rbx,%rax
  lock cmpxchgq %rsi,(tail)
  movq $n2,%rax
  cmpq %rax,%rsi
  je edone
  movq %rax,%rsi
  jmp enq
enq_swing:
  movq %rbx,%rax
  lock cmpxchgq %rcx,(tail)
  jmp enq
edone:

dequeuer:
  xorl %r13d,%r13d
deq:
  movq (head),%rbx
  movq (tail),%rdx
  movq (%rbx),%rcx
  cmpq %rbx,(head)
  jne deq
  cmpq %rbx,%rdx
  jne deq_pop
  testq %rcx,%rcx
  je deq
  movq %rbx,%rax
  lock cmpxchgq %rcx,(tail)
  jmp deq
deq_pop:
  movq %rbx,%rax
  lock cmpxchgq %rcx,(head)
  jne deq
  testq %r12,%r12
  jne deq_second
  movq %rcx,%r12
  jmp deq
deq_second:
  movq %rcx,%r13
  jmp ddone
ddone:
")

/-- The enqueuer's fragment (`enqueuer:` to `edone:`). -/
def enqFragV : Program := parse("
enqueuer:
  movq $n1,%rsi
enq:
  movq (tail),%rbx
  movq (%rbx),%rcx
  cmpq %rbx,(tail)
  jne enq
  testq %rcx,%rcx
  jne enq_swing
  xorl %eax,%eax
  lock cmpxchgq %rsi,(%rbx)
  jne enq
  movq %rbx,%rax
  lock cmpxchgq %rsi,(tail)
  movq $n2,%rax
  cmpq %rax,%rsi
  je edone
  movq %rax,%rsi
  jmp enq
enq_swing:
  movq %rbx,%rax
  lock cmpxchgq %rcx,(tail)
  jmp enq
edone:
")

/-- The dequeuer's fragment (`dequeuer:` to `ddone:`). -/
def deqFragV : Program := parse("
dequeuer:
  xorl %r13d,%r13d
deq:
  movq (head),%rbx
  movq (tail),%rdx
  movq (%rbx),%rcx
  cmpq %rbx,(head)
  jne deq
  cmpq %rbx,%rdx
  jne deq_pop
  testq %rcx,%rcx
  je deq
  movq %rbx,%rax
  lock cmpxchgq %rcx,(tail)
  jmp deq
deq_pop:
  movq %rbx,%rax
  lock cmpxchgq %rcx,(head)
  jne deq
  testq %r12,%r12
  jne deq_second
  movq %rcx,%r12
  jmp deq
deq_second:
  movq %rcx,%r13
  jmp ddone
ddone:
")

/-- The `.kl` runner's data trailer of `msqueue2.kl`: each symbol a label
behind a padding cell, in the order of first mention (`s`, `n1`, `n2`,
`head`, `tail`). -/
def msq2DataV : Program :=
  [.byteArray (.mk #[]), .label "s", .byteArray (.mk #[]), .label "n1", .byteArray (.mk #[]), .label "n2",
    .byteArray (.mk #[]), .label "head", .byteArray (.mk #[]), .label "tail"]

/-- The image: the code, then the data trailer. -/
def msq2ImageV : Program := msq2CodeV ++ msq2DataV

/-- **The enqueuer's mask of the image**: the cells `0 … 23` (`enqueuer:` to
`edone:`) kept, every later non-label cell a data cell. -/
def msq2ImageM : Program := msq2ImageV.maskKeep (keepRange 0 24)

/-- info: 51 -/
#guard_msgs in
#eval msq2CodeV.length

theorem msq2ImageV_wf : Program.WF msq2ImageV := by decide

theorem msq2ImageM_wf : Program.WF msq2ImageM := by decide

theorem enqFragM_sub : Program.subBlocksOfE enqFragV msq2ImageM = true := by decide

theorem enqFragV_sub : Program.subBlocksOfE enqFragV msq2ImageV = true := by decide

theorem deqFragV_sub : Program.subBlocksOfE deqFragV msq2ImageV = true := by decide

/-- The mask's cell after `edone:` and `dequeuer:` is a data cell. -/
theorem msq2ImageM_25 : msq2ImageM[25]? = some (.byteArray (.mk #[])) := by decide

/-- The image's cell after `ddone:` is the trailer's first padding cell. -/
theorem msq2ImageV_51 : msq2ImageV[51]? = some (.byteArray (.mk #[])) := by decide



/-! ## Step helpers of the counted, restricted run -/

section Helpers

variable {E : SharedEnv} {S : SharedEnv.Layout}

/-- **A shared 8-byte load** of the run (`dmem` maps no 8-byte word): a step
of `E`, the count up. -/
theorem ldC {d : Std.ExtHashMap (BitVec 64) UInt8} {a x : BitVec 64} {g g' : (SharedEnv.counted (E.within S)).State}
    (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g) ∨ (Mem.loadInt d a 8 = none ∧ ∃ v,
      (SharedEnv.counted (E.within S)).step (.load .plain false a 8) g v g' ∧ x = BitVec.setWidth 64 v)) :
    ∃ v, E.step (.load .plain false a 8) g.1 v g'.1 ∧ g.2 < g'.2 ∧ x = BitVec.setWidth 64 v := by
  rcases h with ⟨v, hv, -⟩ | ⟨-, v, ⟨hs, ht⟩, rfl⟩
  · rw [hd8] at hv; cases hv
  · exact ⟨v, hs, by simp only [SharedAccess.tick] at ht; omega, rfl⟩

/-- The count of a shared 8-byte load of the run goes up. -/
theorem ldC_lt {d : Std.ExtHashMap (BitVec 64) UInt8} {a x : BitVec 64} {g g' : (SharedEnv.counted (E.within S)).State}
    (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g) ∨ (Mem.loadInt d a 8 = none ∧ ∃ v,
      (SharedEnv.counted (E.within S)).step (.load .plain false a 8) g v g' ∧ x = BitVec.setWidth 64 v)) :
    g.2 < g'.2 :=
  let ⟨_, _, h, _⟩ := ldC hd8 h; h

/-- **An RMW** of the run: a step of `E`, the count up. -/
theorem rmwC {k : RmwKind} {a : BitVec 64} {n : Nat} {op : Val → Option Val} {old : BitVec 128}
    {g g' : (SharedEnv.counted (E.within S)).State}
    (h : (SharedEnv.counted (E.within S)).step (.rmw k a n op) g old g') :
    E.step (.rmw k a n op) g.1 old g'.1 ∧ g.2 < g'.2 :=
  ⟨h.1, by have := h.2; simp only [SharedAccess.tick] at this; omega⟩

/-- An RMW permitted by `E`, in the layout, is permitted in the run. -/
theorem okRC {k : RmwKind} {a : BitVec 64} {n : Nat} {op : Val → Option Val}
    {g : (SharedEnv.counted (E.within S)).State} (h : E.ok (.rmw k a n op) g.1) (hS : (a, n) ∈ S) :
    (SharedEnv.counted (E.within S)).ok (.rmw k a n op) g := ⟨h, hS⟩

/-- A fence step of the run: `FenceLe`, the count unchanged. -/
theorem fenC {tid : Nat} {pl : Plan} {g g' : (SharedEnv.counted ((EnvGCAdj isa Arch.tso tid pl).within S)).State}
    (h : SharedEnv.FenceMonoX.le g g') : FenceLe g.1 g'.1 ∧ g'.2 = g.2 := h

end Helpers

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labV (x : Label) : Int64 := (_root_.Executable.labels (layout msq2ImageV)).label x

/-- A symbol's address in the image. -/
abbrev symV (x : Label) : BitVec 64 := (labV x).toBitVec

/-- A label's address in the mask. -/
abbrev labM (x : Label) : Int64 := (_root_.Executable.labels (layout msq2ImageM)).label x

/-- A symbol's address in the mask. -/
abbrev symM (x : Label) : BitVec 64 := (labM x).toBitVec

theorem msq2ImageM_mask : MaskOf (layout msq2ImageV) (layout msq2ImageM) :=
  maskOf_layout _ _

theorem labM_eq (x : Label) : labM x = labV x := by
  show (_root_.Executable.labels (layout msq2ImageM)).label x = (_root_.Executable.labels (layout msq2ImageV)).label x
  rw [labels_mask msq2ImageM_mask]

/-- The parameters at the image's symbols. -/
abbrev paramsV : Params := ⟨symV "head", symV "tail", symV "s", symV "n1", symV "n2", false⟩

/-- The enqueuer's environment, restricted to `sAll`. -/
noncomputable abbrev EEX (P : Params) : SharedEnv := EnvGCAdjX Arch.tso 0 (planE P) sAll

/-- The dequeuer's environment, restricted to `sAll`. -/
noncomputable abbrev EDX (P : Params) : SharedEnv := EnvGCAdjX Arch.tso 1 (planD P) sAll

variable [Executable.ValidLayout (layout msq2ImageV)]

theorem msq2ImageM_valid : Executable.ValidLayout (layout msq2ImageM) :=
  ValidLayout.of_mask msq2ImageM_mask

/-! ## The enqueuer, over the mask -/

section Enq


set_option hygiene false in
/-- The enqueuer's three reads (`movq (tail),%rbx`, `movq (%rbx),%rcx`,
`cmpq %rbx,(tail)`): `h3 : E2` after them, `c1 c2 c3` the counts. -/
local macro "e_reads" : tactic => `(tactic| (
  have q1 := ldC hd8 ld1
  obtain ⟨w3, hs1, c1, e3⟩ := q1
  have h1 := vc_e_load_tail _ hT w3 g1.1 hs1
  have q2 := ldC hd8 ld2
  obtain ⟨w4, hs2, c2, e4⟩ := q2
  have h2 := vc_e_load_link _ h1 w4 g2.1 (stepL hs2 (by simp [e3]))
  have q3 := ldC hd8 ld3
  obtain ⟨w5, hs3, c3, -⟩ := q3
  have h3 := vc_e_load2 _ h2 w5 g3.1 hs3))

set_option hygiene false in
/-- Land at `enq` with `E0` (the back-edge: the count went up). -/
local macro "to_enq" t:term : tactic => `(tactic| (
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inl ⟨rfl, by simpa using $t⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
  subst hg))


set_option hygiene false in
/-- A path through the link `lock cmpxchgq` that contradicts its flags. -/
local macro "cas_absurd" : tactic => `(tactic| (
  simp at heq
  simp [CondCode.interp, StatusFlags.from_result] at cn
  first | exact absurd heq cn | exact absurd cn heq))

set_option hygiene false in
/-- After `e_reads`: the link `lock cmpxchgq` (`hc`: its two outcomes). -/
local macro "e_link" : tactic => `(tactic| (
  have hE := (((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1
  have hc := (vc_e_link hL _ hE).2 old g8.1 (stepR (rmwC hc).1 (by simp [e3]) (by funext x; simp [cmpxOp64]))
  simp at heq))

set_option hygiene false in
/-- After `e_link` on its success: `hLk : Linked` before the swing, `hs :
Linked` after it. -/
local macro "e_swing" : tactic => `(tactic| (
  rcases hc with ⟨hne, -⟩ | ⟨-, hLk⟩
  · exact absurd heq hne
  have hLk' := (hLk.fence (fenC f9).1).fence (fenC f10).1
  have hs := (vc_e_swing hL _ hLk').2 old2 g11.1 (stepR (rmwC hc2).1 rfl (by funext x; simp [cmpxOp64, e3]))))


set_option hygiene false in
/-- The counts along an enqueuer path (whichever of the named steps exist). -/
local macro "e_cnt" : tactic => `(tactic| (
  try have := (fenC f4).2
  try have := (fenC f5).2
  try have := (fenC f6).2
  try have := (fenC f7).2
  try have := (rmwC hc).2
  try have := (fenC f9).2
  try have := (fenC f10).2
  try have := (rmwC hc2).2
  try have := (fenC f12).2
  try have := (fenC f13).2
  try have := (fenC f14).2
  try have := (fenC f15).2
  try have := (fenC f16).2
  omega))

/-- The enqueuer's table: `dmem` maps no 8-byte word; `rsi` the node. -/
abbrev enqTable (P : Params) : Label → MachineData → (SharedEnv.counted (EEX P)).State → Prop :=
  fun lb s σ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    ((lb = "enqueuer" ∧ E0 P P.n1 σ.1) ∨ (lb = "enq" ∧ E0 P (s.regs.get64 .rsi) σ.1) ∨
      (lb = "enq_swing" ∧ ∃ y3 y4, s.regs.get64 .rbx = BitVec.setWidth 64 y3 ∧
        s.regs.get64 .rcx = BitVec.setWidth 64 y4 ∧ BitVec.setWidth 64 y4 ≠ 0 ∧
        E2 P (s.regs.get64 .rsi) y3 y4 σ.1) ∨
      (lb = "edone" ∧ ComE P σ.1))

omit layout [Executable.ValidLayout (layout msq2ImageV)] in
set_option maxHeartbeats 4000000 in
/-- **The verbatim x64 enqueuer on `EnvGCAdjX`** (counted, partial) in any
code environment in which `enqFragV` is placed with its exit at `edone`, the
labels `head`, `tail`, `n1`, `n2` at `P`'s addresses (shared with
`msqueue3.kl`, whose enqueuer is the same code). -/
theorem enq_envGCAdj_gen [CodeEnv] (P : Params) (hL : QLocs P) (hpl : Program.PlacedIn enqFragV)
    (hlast : ∀ l blk, Program.blockAt enqFragV l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label "edone")
    (hh : ((_root_.Executable.labels cenv).label "head").toBitVec = P.h)
    (ht : ((_root_.Executable.labels cenv).label "tail").toBitVec = P.t)
    (h1 : ((_root_.Executable.labels cenv).label "n1").toBitVec = P.n1)
    (h2 : ((_root_.Executable.labels cenv).label "n2").toBitVec = P.n2) :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ E0 P P.n1 g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EEX P)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "edone" ∧ ComE P x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "enqueuer"), g) := by
  obtain ⟨h, t, s0, n1, n2, trk⟩ := P
  simp only at hh ht h1 h2
  subst hh ht h1 h2
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EEX _))
    (Q := fun _ σ => ComE _ σ.1) (E := fun _ _ _ => False) (enqTable _) ?_ rfl
    (by decide) hpl hlast s g (by simpa [enqTable] using hsg)
  cfg_cases_env [enqFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [String.reduceEq, true_and, false_and, or_false, false_or] at hT
  -- `enqueuer`: `movq $n1,%rsi`, falls through to `enq`
  case vc1 =>
    rename_i g1 f1 _
    exact ⟨hd8, .inr (.inl ⟨rfl, by simpa using hT.fence (fenC f1).1⟩)⟩
  -- `enq`
  case vc1 => exact ⟨trivial, mem_sAll8 _⟩
  case vc2 => exact ⟨trivial, mem_sAll8 _⟩
  case vc3 => exact ⟨trivial, mem_sAll8 _⟩
  case vc4 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 _
    e_reads
    to_enq h3.e0.fence (fenC f4).1
    e_cnt
  case vc5 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 _
    e_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inl ⟨rfl, w3, w4, by simp [e3], by simp [e4], by simpa [e4] using ct,
      by simpa using ((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1⟩))⟩, .inl (by decide)⟩
  case vc6 => exact hd8 _
  case vc7 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 _
    e_reads
    have hE := (((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1
    exact okRC (okR (vc_e_link hL _ hE).1 (by simp [e3]) (by funext x; simp [cmpxOp64])) (mem_sAll8 _)
  case vc8 =>
    rename_i old g8 hc heq cn g9 f9 _
    cas_absurd
  case vc9 => exact hd8 _
  case vc10 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 _
    e_reads
    e_link
    rcases hc with ⟨hne, -⟩ | ⟨-, hLk⟩
    · exact absurd heq hne
    have hLk' := (hLk.fence (fenC f9).1).fence (fenC f10).1
    exact okRC (okR (vc_e_swing hL _ hLk').1 rfl (by funext x; simp [cmpxOp64, e3])) (mem_sAll8 _)
  case vc11 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 _
    e_reads
    e_link
    e_swing
    dsimp only
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr ⟨rfl,
      (((hs.fence (fenC f12).1).fence (fenC f13).1).fence (fenC f14).1).1⟩))⟩, .inl (by decide)⟩
  case vc12 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 g15 f15 g16 f16 _
    e_reads
    e_link
    e_swing
    dsimp only
    simp [CondCode.interp, StatusFlags.from_result] at cz2
    have hs21 := hs.2.1
    rcases hs21 with ⟨hn, -⟩ | hn
    · rw [hn] at hs
      to_enq (((((Linked.next hL hs).fence (fenC f12).1).fence (fenC f13).1).fence (fenC f14).1).fence
        (fenC f15).1).fence (fenC f16).1
      e_cnt
    · exact absurd (by simp [Reg64s.get64] at hn; rw [hn]; exact BitVec.sub_self _) cz2
  case vc13 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 _
    e_reads
    e_link
    e_swing
    dsimp only
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr ⟨rfl,
      (((hs.fence (fenC f12).1).fence (fenC f13).1).fence (fenC f14).1).1⟩))⟩, .inl (by decide)⟩
  case vc14 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 g15 f15 g16 f16 _
    e_reads
    e_link
    e_swing
    dsimp only
    simp [CondCode.interp, StatusFlags.from_result] at cz2
    have hs21 := hs.2.1
    rcases hs21 with ⟨hn, -⟩ | hn
    · rw [hn] at hs
      to_enq (((((Linked.next hL hs).fence (fenC f12).1).fence (fenC f13).1).fence (fenC f14).1).fence
        (fenC f15).1).fence (fenC f16).1
      e_cnt
    · exact absurd (by simp [Reg64s.get64] at hn; rw [hn]; exact BitVec.sub_self _) cz2
  case vc15 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 _
    e_reads
    e_link
    rcases hc with ⟨-, hE0⟩ | ⟨hz, -⟩
    · dsimp only
      to_enq hE0.fence (fenC f9).1
      e_cnt
    · exact absurd hz heq
  case vc16 => exact hd8 _
  case vc17 =>
    rename_i old g8 hc heq cn g9 f9 g10 f10 _
    cas_absurd
  case vc18 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 _
    cas_absurd
  case vc19 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 g15 f15 g16 f16 _
    cas_absurd
  case vc20 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 _
    cas_absurd
  case vc21 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 cz g4 f4 b5 g5 f5 ct g6 f6 b7 g7 f7 old g8 hc heq cn g9 f9 g10 f10 old2 g11 hc2 heq2 g12 f12 g13 f13 cz2 g14 f14 g15 f15 g16 f16 _
    cas_absurd
  -- `enq_swing`
  case vc1 => exact hd8 _
  case vc2 =>
    rename_i g1 f1 _
    obtain ⟨y3, y4, hb, hcx, hnz, h2⟩ := hT
    have hcx' := hcx; simp only [Reg64s.get64] at hcx'
    exact okRC (okR (vc_e_help hL _ (h2.fence (fenC f1).1) hnz).1 rfl
      (by funext x; simp [cmpxOp64, hb, hcx'])) (mem_sAll8 _)
  case vc3 | vc4 =>
    rename_i g1 f1 old g2 hc heq g3 f3 _
    obtain ⟨y3, y4, hb, hcx, hnz, h2⟩ := hT
    have hcx' := hcx; simp only [Reg64s.get64] at hcx'
    have hE := (vc_e_help hL _ (h2.fence (fenC f1).1) hnz).2 old g2.1
      (stepR (rmwC hc).1 rfl (by funext x; simp [cmpxOp64, hb, hcx']))
    dsimp only
    to_enq hE.fence (fenC f3).1
    have := (fenC f1).2; have := (rmwC hc).2; have := (fenC f3).2
    omega
  -- `edone`
  case vc1 => exact hT

local instance msq2ImageM.env : CodeEnv := ⟨layout msq2ImageM⟩

theorem enqFragM_placedIn : Program.PlacedIn enqFragV :=
  haveI := msq2ImageM_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := msq2ImageM) msq2ImageM_wf rfl (by decide))
    enqFragM_sub

omit [Executable.ValidLayout (layout msq2ImageV)] in
theorem enqFragM_last : ∀ l blk, Program.blockAt enqFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labM "edone" :=
  Program.after_last_of (by decide)


theorem enqM_envGCAdj' (P : Params) (hL : QLocs P) (hh : symM "head" = P.h) (ht : symM "tail" = P.t)
    (h1 : symM "n1" = P.n1) (h2 : symM "n2" = P.n2) :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ E0 P P.n1 g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EEX P)))
        (fun x => (x.1.2 = labM "edone" ∧ ComE P x.2.1) ∨ False) ((s, labM "enqueuer"), g) :=
  enq_envGCAdj_gen P hL enqFragM_placedIn enqFragM_last hh ht h1 h2

end Enq

/-! ## The dequeuer, over the image -/

/-- The frame of a dequeue: `r12` is `0` or the first dequeue's node. -/
def YR (P : Params) (x : BitVec 64) : EStateX → Prop := fun σ => x = 0 ∨ First P x σ

omit layout [Executable.ValidLayout (layout msq2ImageV)] in
/-- `YR` survives the dequeuer's fences, loads and RMWs. -/
theorem yok_r (P : Params) (x : BitVec 64) : YOk P (YR P x) where
  fence h hf := h.imp id fun h => (yok_first x).fence h hf
  load h hf := h.imp id fun h => (yok_first x).load h hf
  rmw h hs := h.imp id fun h => (yok_first x).rmw h hs

section Deq

local instance msq2ImageV.env : CodeEnv := ⟨layout msq2ImageV⟩

theorem deqFragV_placedIn : Program.PlacedIn deqFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := msq2ImageV) msq2ImageV_wf rfl (by decide))
    deqFragV_sub

omit [Executable.ValidLayout (layout msq2ImageV)] in
theorem deqFragV_last : ∀ l blk, Program.blockAt deqFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV "ddone" :=
  Program.after_last_of (by decide)


set_option hygiene false in
/-- The dequeuer's four reads (`movq (head),%rbx`, `movq (tail),%rdx`,
`movq (%rbx),%rcx`, `cmpq %rbx,(head)`): `h4 : D3` after them. -/
local macro "d_reads" : tactic => `(tactic| (
  have q1 := ldC hd8 ld1
  obtain ⟨w3, hs1, c1, e3⟩ := q1
  have h1 := vc_d_load_head (yok_r _ _) _ hT.1 hT.2 w3 g1.1 hs1
  have q2 := ldC hd8 ld2
  obtain ⟨wt, hs2, c2, e4⟩ := q2
  have h2 := vc_d_load_tail (yok_r _ _) _ h1 wt g2.1 hs2
  have q3 := ldC hd8 ld3
  obtain ⟨wu, hs3, c3, e5⟩ := q3
  have h3 := vc_d_load_link (yok_r _ _) _ h2 wu g3.1 (stepL hs3 (by simp [e3]))
  have q4 := ldC hd8 ld4
  obtain ⟨w6, hs4, c4, -⟩ := q4
  have h4 := vc_d_load3 (yok_r _ _) _ h3 w6 g4.1 hs4))


set_option hygiene false in
/-- Land at `deq` with `ComD` and the frame (the back-edge). -/
local macro "to_deq" t:ident : tactic => `(tactic| (
  dsimp only
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inl ⟨rfl, ($t).1, by simpa using ($t).2⟩)⟩,
    .inr fun ⟨_, hg⟩ => ?_⟩
  subst hg))

set_option hygiene false in
/-- The counts along a dequeuer path (whichever of the named steps exist).
(Scoped, shared with `EnvG/X64MsQueue3VCGen.lean`.) -/
scoped macro "d_cnt" : tactic => `(tactic| (
  try have := c1
  try have := c2
  try have := c3
  try have := c4
  try have := (fenC f1).2
  try have := (fenC f3).2
  try have := (fenC f4).2
  try have := (fenC f5).2
  try have := (fenC f6).2
  try have := (fenC f7).2
  try have := (fenC f8).2
  try have := (fenC f9).2
  try have := (fenC f10).2
  try have := (rmwC hc).2
  try have := (fenC f12).2
  omega))

set_option hygiene false in
/-- A path through the swing `lock cmpxchgq` that contradicts its flags.
(Scoped, shared with `EnvG/X64MsQueue3VCGen.lean`.) -/
scoped macro "p_absurd" : tactic => `(tactic| (
  try simp at heq
  simp [CondCode.interp, StatusFlags.from_result] at cn
  first | exact absurd heq cn | exact absurd cn heq | simp [heq] at cn |
    (simp only [BitVec.sub_eq_iff_eq_add, BitVec.zero_add] at cn
     first | exact absurd cn heq | exact absurd cn.symm heq)))

set_option hygiene false in
/-- At `deq_pop` after the swing: `hD1 : D3` before it, `hP` its outcome. -/
local macro "p_pop0" : tactic => `(tactic| (
  obtain ⟨y3, yt, u, hb, hcx, hne, hD⟩ := hT
  simp only [Reg64s.get64] at hb hcx
  have hD1 := hD.fence (yok_r _ _) (fenC f1).1
  have hP := (vc_d_pop hL rfl (yok_r _ _) _ hD1 hne).2 old g2.1
    (stepR (rmwC hc).1 rfl (by funext x; simp [cmpxOp64, hb, hcx]))))

set_option hygiene false in
/-- `p_pop0` on the swing's success: `heq'` its `old`. -/
local macro "p_pop" : tactic => `(tactic| (
  p_pop0
  simp at heq
  have heq' : BitVec.setWidth 64 old = BitVec.setWidth 64 y3 := by simpa [hb] using heq))

/-- The dequeuer's table: `dmem` maps no 8-byte word; `r12` the first
dequeue's node (or `0`), `r13` the second's. -/
abbrev deqTable (P : Params) : Label → MachineData → (SharedEnv.counted (EDX P)).State → Prop :=
  fun lb s σ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    ((lb = "dequeuer" ∧ ComD P σ.1 ∧ s.regs.get64 .r12 = 0) ∨
      (lb = "deq" ∧ ComD P σ.1 ∧ YR P (s.regs.get64 .r12) σ.1) ∨
      (lb = "deq_pop" ∧ ∃ y3 yt u, s.regs.get64 .rbx = BitVec.setWidth 64 y3 ∧
        s.regs.get64 .rcx = BitVec.setWidth 64 u ∧ BitVec.setWidth 64 yt ≠ BitVec.setWidth 64 y3 ∧
        D3 P (YR P (s.regs.get64 .r12)) y3 yt u σ.1) ∨
      (lb = "deq_second" ∧ ComD P σ.1 ∧ DoneD2 σ.1.snap.mem P (s.regs.get64 .r12) (s.regs.get64 .rcx)) ∨
      (lb = "ddone" ∧ Dn P (s.regs.get64 .r12) (s.regs.get64 .r13) σ.1))

set_option maxHeartbeats 4000000 in
theorem deqV_envGCAdj' (P : Params) (hL : QLocs P) (hpt : P.trk = false) (hh : symV "head" = P.h)
    (ht : symV "tail" = P.t) :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ ComD P g.1 ∧ s.regs.get64 .r12 = 0 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EDX P)))
        (fun x => (x.1.2 = labV "ddone" ∧ Dn P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) x.2.1) ∨ False)
        ((s, labV "dequeuer"), g) := by
  obtain ⟨h, t, s0, n1, n2, trk⟩ := P
  simp only at hh ht hpt
  subst hh ht hpt
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EDX _))
    (Q := fun s σ => Dn _ (s.regs.get64 .r12) (s.regs.get64 .r13) σ.1) (E := fun _ _ _ => False) (deqTable _) ?_ rfl
    (by decide) deqFragV_placedIn deqFragV_last s g (by simpa [deqTable] using hsg)
  cfg_cases_env [deqFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [String.reduceEq, true_and, false_and, or_false, false_or] at hT
  -- `dequeuer`
  case vc1 =>
    rename_i b1 g1 f1 _
    exact ⟨hd8, .inr (.inl ⟨rfl, hT.1.fence (fenC f1).1, .inl (by simpa using hT.2)⟩)⟩
  -- `deq`
  case vc1 | vc2 | vc3 | vc4 => exact ⟨trivial, mem_sAll8 _⟩
  case vc5 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 _
    d_reads
    have hb := (h4.fence (yok_r _ _) (fenC f5).1).back
    to_deq hb
    d_cnt
  case vc7 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 b8 g8 f8 ct g9 f9 _
    d_reads
    have hb := (((((h4.fence (yok_r _ _) (fenC f5).1).fence (yok_r _ _) (fenC f6).1).fence (yok_r _ _) (fenC f7).1).fence
      (yok_r _ _) (fenC f8).1).fence (yok_r _ _) (fenC f9).1).back
    to_deq hb
    d_cnt
  case vc8 => exact hd8 _
  case vc9 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 b8 g8 f8 ct g9 f9 g10 f10 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    have hE := (((((h4.fence (yok_r _ _) (fenC f5).1).fence (yok_r _ _) (fenC f6).1).fence (yok_r _ _) (fenC f7).1).fence
      (yok_r _ _) (fenC f8).1).fence (yok_r _ _) (fenC f9).1).fence (yok_r _ _) (fenC f10).1
    exact okRC (okR (vc_d_help hL (yok_r _ _) _ hE (by rw [← e5]; exact ct)).1 rfl
      (by funext x; simp [cmpxOp64, e3, e5])) (mem_sAll8 _)
  case vc10 | vc11 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 b8 g8 f8 ct g9 f9 g10 f10 old g11 hc heq g12 f12 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    have hE := (((((h4.fence (yok_r _ _) (fenC f5).1).fence (yok_r _ _) (fenC f6).1).fence (yok_r _ _) (fenC f7).1).fence
      (yok_r _ _) (fenC f8).1).fence (yok_r _ _) (fenC f9).1).fence (yok_r _ _) (fenC f10).1
    have hC := (vc_d_help hL (yok_r _ _) _ hE (by rw [← e5]; exact ct)).2 old g11.1
      (stepR (rmwC hc).1 rfl (by funext x; simp [cmpxOp64, e3, e5]))
    have hb : _ ∧ _ := ⟨hC.1.fence (fenC f12).1, (yok_r _ _).fence hC.2 (fenC f12).1⟩
    to_deq hb
    d_cnt
  case vc6 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at cr
    dsimp only
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inl ⟨rfl, w3, wt, wu, by simp [e3], by simp [e5],
      fun h => cr (by rw [e3, e4, h]; exact BitVec.sub_self _),
      by simpa using ((h4.fence (yok_r _ _) (fenC f5).1).fence (yok_r _ _) (fenC f6).1).fence (yok_r _ _) (fenC f7).1⟩))⟩, .inl (by decide)⟩
  -- `deq_pop`
  case vc1 => exact hd8 _
  case vc2 =>
    rename_i g1 f1 _
    obtain ⟨y3, yt, u, hb, hcx, hne, hD⟩ := hT
    simp only [Reg64s.get64] at hb hcx
    exact okRC (okR (vc_d_pop hL rfl (yok_r _ _) _ (hD.fence (yok_r _ _) (fenC f1).1) hne).1 rfl
      (by funext x; simp [cmpxOp64, hb, hcx])) (mem_sAll8 _)
  case vc3 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 _
    p_absurd
  case vc4 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 b4 g4 f4 c4 g5 f5 _
    p_pop
    simp [CondCode.interp, StatusFlags.from_result] at c4
    have hY := hD1.2.1
    rcases hY with h0 | hfst
    · exact absurd h0 c4
    have hd : Dn _ _ _ _ := ⟨hP.1, (hP.2.2 heq').2 _ hfst⟩
    have hd' := ((hd.fence (fenC f3).1).fence (fenC f4).1).fence (fenC f5).1
    dsimp only
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr (.inl ⟨rfl, hd'.1,
      by simpa [hcx] using hd'.2⟩)))⟩, .inl (by decide)⟩
  case vc5 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 b4 g4 f4 c4 g5 f5 g6 f6 g7 f7 _
    p_pop
    have hb0 : _ ∧ _ := ⟨hP.1, (Or.inr (hP.2.2 heq').1 : YR _ _ _)⟩
    have hb1 := ((((hb0.1.fence (fenC f3).1).fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1
    have hb2 := (yok_r _ _).fence ((yok_r _ _).fence ((yok_r _ _).fence ((yok_r _ _).fence
      ((yok_r _ _).fence hb0.2 (fenC f3).1) (fenC f4).1) (fenC f5).1) (fenC f6).1) (fenC f7).1
    dsimp only
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inl ⟨rfl, hb1, by simpa [hcx] using hb2⟩)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    d_cnt
  case vc6 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 _
    p_pop0
    have hb : _ ∧ _ := ⟨hP.1.fence (fenC f3).1, (yok_r _ _).fence hP.2.1 (fenC f3).1⟩
    to_deq hb
    d_cnt
  case vc7 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 b4 g4 f4 c4 g5 f5 _
    p_absurd
  case vc8 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 b4 g4 f4 c4 g5 f5 g6 f6 g7 f7 _
    p_absurd
  -- `deq_second`
  case vc1 =>
    rename_i g1 f1 g2 f2 _
    have hd : Dn _ _ _ _ := ⟨hT.1, hT.2⟩
    have hd' := (hd.fence (fenC f1).1).fence (fenC f2).1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr (.inr ⟨rfl, by simpa using hd'⟩)))⟩,
      .inl (by decide)⟩
  -- `ddone`
  case vc1 => exact hT

end Deq

/-! ## The runs at the image's labels; the exits -/

/-- **The verbatim x64 enqueuer on `EnvGCAdjX`, over the mask** (counted,
partial), at the image's labels. -/
theorem enqM_envGCAdj (P : Params) (hL : QLocs P) (hh : symV "head" = P.h) (ht : symV "tail" = P.t)
    (h1 : symV "n1" = P.n1) (h2 : symV "n2" = P.n2) :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ E0 P P.n1 g.1 →
      Safely ((layout msq2ImageM).instrStepEnv (SharedEnv.counted (EEX P)))
        (fun x => (x.1.2 = labV "edone" ∧ ComE P x.2.1) ∨ False) ((s, labV "enqueuer"), g) := by
  intro s g h
  have := enqM_envGCAdj' P hL (by unfold symM; rw [labM_eq]; exact hh) (by unfold symM; rw [labM_eq]; exact ht)
    (by unfold symM; rw [labM_eq]; exact h1) (by unfold symM; rw [labM_eq]; exact h2) s g h
  simp only [labM_eq] at this
  exact this

omit [Executable.ValidLayout (layout msq2ImageV)] in
set_option maxRecDepth 8000 in
/-- `edone`'s address is the mask's cell `25` (behind `edone:` and
`dequeuer:`). -/
theorem labV_edone [Executable.ValidLayout (layout msq2ImageV)] :
    labV "edone" = (layout msq2ImageM).addrOf 25 := by
  have hd : labV "edone" = (layout msq2ImageV).addrOf 23 :=
    Program.label_addrOf_drop msq2ImageV_wf.nodup (by decide) (by decide)
  have h23 : (layout msq2ImageV).2[23]? = some (Directive.label "edone", Kraken.Layout.size Directive 23) := by
    simp [Layout.apply_snd, Layout.frag, msq2ImageV, msq2CodeV, msq2DataV]
  have h24 : (layout msq2ImageV).2[24]? = some (Directive.label "dequeuer", Kraken.Layout.size Directive 24) := by
    simp [Layout.apply_snd, Layout.frag, msq2ImageV, msq2CodeV, msq2DataV]
  rw [addrOf_mask msq2ImageM_mask, Executable.addrOf_succ _ h24,
    Executable.ValidLayout.label_size 24 "dequeuer" _ h24, Executable.addrOf_succ _ h23,
    Executable.ValidLayout.label_size 23 "edone" _ h23, hd]
  simp

/-- **No step of the mask at the enqueuer's exit label `edone`.** -/
theorem enqM_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labV "edone" → ¬ (layout msq2ImageM).instrStepEnv env x R := by
  haveI := msq2ImageM_valid (layout := layout)
  rw [labV_edone]
  exact not_instrStepEnv_of_byteArray (i := 25) (b := .mk #[]) env msq2ImageM_25

set_option maxRecDepth 8000 in
/-- `ddone`'s address is the trailer's first padding cell. -/
theorem labV_ddone : labV "ddone" = (layout msq2ImageV).addrOf 51 := by
  have hd : labV "ddone" = (layout msq2ImageV).addrOf 50 :=
    Program.label_addrOf_drop msq2ImageV_wf.nodup (by decide) (by decide)
  have h50 : (layout msq2ImageV).2[50]? = some (Directive.label "ddone", Kraken.Layout.size Directive 50) := by
    simp [Layout.apply_snd, Layout.frag, msq2ImageV, msq2CodeV, msq2DataV]
  rw [Executable.addrOf_succ _ h50, Executable.ValidLayout.label_size 50 "ddone" _ h50, hd]
  simp

/-- **No instruction steps at the dequeuer's exit label `ddone`.** -/
theorem deqV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labV "ddone" → ¬ (layout msq2ImageV).instrStepEnv env x R := by
  rw [labV_ddone]
  exact not_instrStepEnv_of_byteArray (i := 51) (b := .mk #[]) env msq2ImageV_51

/-! ## Only release writes -/

open Lean Elab Tactic in
/-- Every count fact of the run's loads and RMWs among the hypotheses
(`hd8` the `dmem` frame), for `omega`. (Scoped, shared with
`EnvG/X64MsQueue3VCGen.lean`.) -/
scoped elab "cnt_all" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let e ← Term.exprToSyntax d.toExpr
    if ty.isAppOf ``Or && (ty.find? (·.isConstOf ``SharedEnv.step)).isSome then
      try evalTactic (← `(tactic| have := by with_reducible exact ldC_lt $(mkIdent `hd8) $e)) catch _ => pure ()
    else if ty.isAppOf ``SharedEnv.step then
      try evalTactic (← `(tactic| have := by with_reducible exact (rmwC $e).2)) catch _ => pure ()

set_option hygiene false in
/-- **The no-non-temporal-write run's case script** (after `cfg_cases_env`):
every VC of a thread whose writes are all `lock cmpxchgq`s (release RMWs)
in `EnvRT sAll`, with the `dmem` frame `hd8` and the counts by `cnt_all`.
(Shared by the four `*_noNT` runs of msqueue2 and msqueue3.) -/
scoped macro "msq_noNT_cases" : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : _ ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨hd8, rfl, rfl⟩ := hx
  all_goals first
    | exact hd8 _
    | exact hd8
    | (refine ⟨⟨?_, mem_sAll8 _⟩, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (exact Table.ofLabelsEnv_at ⟨by decide, hd8, .inl (by decide)⟩)
    | (dsimp only; refine Table.ofLabelsEnv_at ⟨by decide, hd8, .inr fun ⟨_, hg⟩ => ?_⟩; subst hg; cnt_all; omega)))

section NoNT

local instance msq2ImageV.envN : CodeEnv := ⟨layout msq2ImageV⟩

theorem enqFragV_placedIn : Program.PlacedIn enqFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := msq2ImageV) msq2ImageV_wf rfl (by decide))
    enqFragV_sub

omit [Executable.ValidLayout (layout msq2ImageV)] in
theorem enqFragV_last : ∀ l blk, Program.blockAt enqFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV "edone" :=
  Program.after_last_of (by decide)

set_option maxHeartbeats 1000000 in
open Kraken.Promising.X64.EnvG.TreiberX (EnvRT) in
/-- **The verbatim enqueuer makes only release writes** (counted, partial;
the image). -/
theorem enqV_noNT :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labV "edone" ∧ True) ∨ False) ((s, labV "enqueuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
      ∀ a, Mem.loadInt s.dmem a 8 = none) ?_ rfl (by decide) enqFragV_placedIn enqFragV_last s g hs
  cfg_cases_env [enqFragV]
  msq_noNT_cases

set_option maxHeartbeats 1000000 in
open Kraken.Promising.X64.EnvG.TreiberX (EnvRT) in
/-- **The verbatim dequeuer makes only release writes** (counted, partial). -/
theorem deqV_noNT :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labV "ddone" ∧ True) ∨ False) ((s, labV "dequeuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
      ∀ a, Mem.loadInt s.dmem a 8 = none) ?_ rfl (by decide) deqFragV_placedIn deqFragV_last s g hs
  cfg_cases_env [deqFragV]
  msq_noNT_cases

end NoNT

end Kraken.Promising.X64.EnvG.MsQueueX
