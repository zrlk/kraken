/-
**Msqueue3 part 4: the x64 `msqueue3.kl`, the
`.kl` code verbatim, on `EnvGCAdjX` by `vcgen`.**

The `code` block of `Kraken/Examples/LockFree/X64/msqueue3.kl` as written
(`msq3CodeV`), in its image `msq3ImageV` (the code, then the runner's data
trailer `msq2DataV`: `s`, `n1`, `n2`, `head`, `tail`):

- the enqueuer (thread `0`) runs `msqueue2.kl`'s fragment `enqFragV` over the
  mask `msq3ImageM` (`enq_envGCAdj_gen`; no step at `edone`: `enq3M_stuck`);
- the dequeuers (threads `1`, `2`) run `deqFragV3`, from `dequeuer` to
  `ddone`, over the image (`deq3V_envGCAdj'`, generic in the thread; no step
  at `ddone`, followed by the data trailer: `deq3V_stuck`);
- `enq3V_noNT`, `deq3V_noNT`: only release writes.

Performance notes as in `X64MsQueue2VCGen`.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue3VC

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 sAll mem_sAll8)
open Kraken.Promising.X64.EnvG.Treiber2X (stepL stepS stepR okR ldN stN)
open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MsQueue3X

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program, its image and the mask -/

/-- **The `code` block of `msqueue3.kl`, verbatim.** -/
def msq3CodeV : Program := parse("
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
deq:
  movq (head),%rbx
  movq (tail),%rdx
  movq (%rbx),%rcx
  cmpq %rbx,(head)
  jne deq
  cmpq %rbx,%rdx
  jne deq_pop
  testq %rcx,%rcx
  je deq_empty
  movq %rbx,%rax
  lock cmpxchgq %rcx,(tail)
  jmp deq
deq_pop:
  movq %rbx,%rax
  lock cmpxchgq %rcx,(head)
  jne deq
  movq %rcx,%r12
  jmp ddone
deq_empty:
  xorl %r12d,%r12d
  jmp ddone
ddone:")

/-- The dequeuers' fragment (`dequeuer` to `ddone`). -/
def deqFragV3 : Program := parse("
dequeuer:
deq:
  movq (head),%rbx
  movq (tail),%rdx
  movq (%rbx),%rcx
  cmpq %rbx,(head)
  jne deq
  cmpq %rbx,%rdx
  jne deq_pop
  testq %rcx,%rcx
  je deq_empty
  movq %rbx,%rax
  lock cmpxchgq %rcx,(tail)
  jmp deq
deq_pop:
  movq %rbx,%rax
  lock cmpxchgq %rcx,(head)
  jne deq
  movq %rcx,%r12
  jmp ddone
deq_empty:
  xorl %r12d,%r12d
  jmp ddone
ddone:")

/-- The image: the code, then the data trailer. -/
def msq3ImageV : Program := msq3CodeV ++ msq2DataV

/-- **The enqueuer's mask of the image**: the cells `0 … 23` (`enqueuer:` to
`edone:`) kept, every later non-label cell a data cell. -/
def msq3ImageM : Program := msq3ImageV.maskKeep (keepRange 0 24)

/-- info: 48 -/
#guard_msgs in
#eval msq3CodeV.length

/-- The enqueuer's code is `msqueue2.kl`'s. -/
theorem msq3CodeV_take : msq3CodeV.take 24 = msq2CodeV.take 24 := by decide

theorem msq3ImageV_wf : Program.WF msq3ImageV := by decide

theorem msq3ImageM_wf : Program.WF msq3ImageM := by decide

theorem enqFragM3_sub : Program.subBlocksOfE enqFragV msq3ImageM = true := by decide

theorem enqFragV3_sub : Program.subBlocksOfE enqFragV msq3ImageV = true := by decide

theorem deqFragV3_sub : Program.subBlocksOfE deqFragV3 msq3ImageV = true := by decide

/-- The mask's cell after `edone:`, `dequeuer:` and `deq:` is a data cell. -/
theorem msq3ImageM_26 : msq3ImageM[26]? = some (.byteArray (.mk #[])) := by decide

/-- The image's cell after `ddone:` is the trailer's first padding cell. -/
theorem msq3ImageV_48 : msq3ImageV[48]? = some (.byteArray (.mk #[])) := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labV3 (x : Label) : Int64 := (_root_.Executable.labels (layout msq3ImageV)).label x

/-- A symbol's address in the image. -/
abbrev symV3 (x : Label) : BitVec 64 := (labV3 x).toBitVec

/-- A label's address in the mask. -/
abbrev labM3 (x : Label) : Int64 := (_root_.Executable.labels (layout msq3ImageM)).label x

theorem msq3ImageM_mask : MaskOf (layout msq3ImageV) (layout msq3ImageM) :=
  maskOf_layout _ _

theorem labM3_eq (x : Label) : labM3 x = labV3 x := by
  show (_root_.Executable.labels (layout msq3ImageM)).label x = (_root_.Executable.labels (layout msq3ImageV)).label x
  rw [labels_mask msq3ImageM_mask]

/-- The parameters at the image's symbols, tracking the `head` swings. -/
abbrev params3V : Params := ⟨symV3 "head", symV3 "tail", symV3 "s", symV3 "n1", symV3 "n2", true⟩

/-- Dequeuer `w`'s environment, restricted to `sAll`. -/
noncomputable abbrev ED3X (P : Params) (w : Nat) : SharedEnv := EnvGCAdjX Arch.tso w (planD3 P w) sAll

variable [Executable.ValidLayout (layout msq3ImageV)]

theorem msq3ImageM_valid : Executable.ValidLayout (layout msq3ImageM) :=
  ValidLayout.of_mask msq3ImageM_mask

/-! ## The enqueuer, over the mask -/

section Enq

local instance msq3ImageM.env : CodeEnv := ⟨layout msq3ImageM⟩

theorem enqFragM3_placedIn : Program.PlacedIn enqFragV :=
  haveI := msq3ImageM_valid (layout := layout)
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := msq3ImageM) msq3ImageM_wf rfl (by decide))
    enqFragM3_sub

omit [Executable.ValidLayout (layout msq3ImageV)] in
theorem enqFragM3_last : ∀ l blk, Program.blockAt enqFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labM3 "edone" :=
  Program.after_last_of (by decide)

/-- **The verbatim x64 enqueuer on `EnvGCAdjX`, over the mask** (counted,
partial), at the image's labels. -/
theorem enq3M_envGCAdj (P : Params) (hL : QLocs P) (hh : symV3 "head" = P.h) (ht : symV3 "tail" = P.t)
    (h1 : symV3 "n1" = P.n1) (h2 : symV3 "n2" = P.n2) :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ E0 P P.n1 g.1 →
      Safely ((layout msq3ImageM).instrStepEnv (SharedEnv.counted (EEX P)))
        (fun x => (x.1.2 = labV3 "edone" ∧ ComE P x.2.1) ∨ False) ((s, labV3 "enqueuer"), g) := by
  intro s g h
  have := enq_envGCAdj_gen P hL enqFragM3_placedIn enqFragM3_last
    (by show (labM3 "head").toBitVec = _; rw [labM3_eq]; exact hh)
    (by show (labM3 "tail").toBitVec = _; rw [labM3_eq]; exact ht)
    (by show (labM3 "n1").toBitVec = _; rw [labM3_eq]; exact h1)
    (by show (labM3 "n2").toBitVec = _; rw [labM3_eq]; exact h2) s g h
  rwa [show (_root_.Executable.labels cenv).label "edone" = labV3 "edone" from labM3_eq _,
    show (_root_.Executable.labels cenv).label "enqueuer" = labV3 "enqueuer" from labM3_eq _] at this

end Enq

omit [Executable.ValidLayout (layout msq3ImageV)] in
set_option maxRecDepth 8000 in
/-- `edone`'s address is the mask's cell `26` (behind `edone:`, `dequeuer:`
and `deq:`). -/
theorem labV3_edone [Executable.ValidLayout (layout msq3ImageV)] :
    labV3 "edone" = (layout msq3ImageM).addrOf 26 := by
  have hd : labV3 "edone" = (layout msq3ImageV).addrOf 23 :=
    Program.label_addrOf_drop msq3ImageV_wf.nodup (by decide) (by decide)
  have h23 : (layout msq3ImageV).2[23]? = some (Directive.label "edone", Kraken.Layout.size Directive 23) := by
    simp [Layout.apply_snd, Layout.frag, msq3ImageV, msq3CodeV, msq2DataV]
  have h24 : (layout msq3ImageV).2[24]? = some (Directive.label "dequeuer", Kraken.Layout.size Directive 24) := by
    simp [Layout.apply_snd, Layout.frag, msq3ImageV, msq3CodeV, msq2DataV]
  have h25 : (layout msq3ImageV).2[25]? = some (Directive.label "deq", Kraken.Layout.size Directive 25) := by
    simp [Layout.apply_snd, Layout.frag, msq3ImageV, msq3CodeV, msq2DataV]
  rw [addrOf_mask msq3ImageM_mask, Executable.addrOf_succ _ h25,
    Executable.ValidLayout.label_size 25 "deq" _ h25, Executable.addrOf_succ _ h24,
    Executable.ValidLayout.label_size 24 "dequeuer" _ h24, Executable.addrOf_succ _ h23,
    Executable.ValidLayout.label_size 23 "edone" _ h23, hd]
  simp

/-- **No step of the mask at the enqueuer's exit label `edone`.** -/
theorem enq3M_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labV3 "edone" → ¬ (layout msq3ImageM).instrStepEnv env x R := by
  haveI := msq3ImageM_valid (layout := layout)
  rw [labV3_edone]
  exact not_instrStepEnv_of_byteArray (i := 26) (b := .mk #[]) env msq3ImageM_26

set_option maxRecDepth 8000 in
/-- `ddone`'s address is the trailer's first padding cell. -/
theorem labV3_ddone : labV3 "ddone" = (layout msq3ImageV).addrOf 48 := by
  have hd : labV3 "ddone" = (layout msq3ImageV).addrOf 47 :=
    Program.label_addrOf_drop msq3ImageV_wf.nodup (by decide) (by decide)
  have h47 : (layout msq3ImageV).2[47]? = some (Directive.label "ddone", Kraken.Layout.size Directive 47) := by
    simp [Layout.apply_snd, Layout.frag, msq3ImageV, msq3CodeV, msq2DataV]
  rw [Executable.addrOf_succ _ h47, Executable.ValidLayout.label_size 47 "ddone" _ h47, hd]
  simp

/-- **No instruction steps at the dequeuers' exit label `ddone`.** -/
theorem deq3V_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labV3 "ddone" → ¬ (layout msq3ImageV).instrStepEnv env x R := by
  rw [labV3_ddone]
  exact not_instrStepEnv_of_byteArray (i := 48) (b := .mk #[]) env msq3ImageV_48

/-! ## The dequeuers, over the image -/

section Deq

local instance msq3ImageV.env : CodeEnv := ⟨layout msq3ImageV⟩

theorem deqFragV3_placedIn : Program.PlacedIn deqFragV3 :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := msq3ImageV) msq3ImageV_wf rfl (by decide))
    deqFragV3_sub

omit [Executable.ValidLayout (layout msq3ImageV)] in
theorem deqFragV3_last : ∀ l blk, Program.blockAt deqFragV3 l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV3 "ddone" :=
  Program.after_last_of (by decide)

set_option hygiene false in
/-- The dequeuer's four reads (`movq (head),%rbx`, `movq (tail),%rdx`,
`movq (%rbx),%rcx`, `cmpq %rbx,(head)`): `h4 : L3` after them. -/
local macro "d_reads" : tactic => `(tactic| (
  have q1 := ldC hd8 ld1
  obtain ⟨w3, hs1, c1, e3⟩ := q1
  have h1 := vc3_load_head _ hT w3 g1.1 hs1
  have q2 := ldC hd8 ld2
  obtain ⟨wt, hs2, c2, e4⟩ := q2
  have h2 := vc3_load_tail _ h1 wt g2.1 hs2
  have q3 := ldC hd8 ld3
  obtain ⟨wu, hs3, c3, e5⟩ := q3
  have h3 := vc3_load_link _ h2 wu g3.1 (stepL hs3 (by simp [e3]))
  have q4 := ldC hd8 ld4
  obtain ⟨w6, hs4, c4, -⟩ := q4
  have h4 := vc3_load3 _ h3 w6 g4.1 hs4))

set_option hygiene false in
/-- Land at `deq` with `L0` (the back-edge). -/
local macro "to_deq" t:term : tactic => `(tactic| (
  dsimp only
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inl ⟨rfl, $t⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
  subst hg))

set_option hygiene false in
/-- At `deq_pop` after the swing: `hP` its outcome. -/
local macro "p_pop0" : tactic => `(tactic| (
  obtain ⟨y3, yt, u, hb, hcx, hne, hD⟩ := hT
  simp only [Reg64s.get64] at hb hcx
  have hD1 := hD.fence (fenC f1).1
  have hP := (vc3_pop hL hw _ hD1 hne).2 old g2.1
    (stepR (rmwC hc).1 rfl (by funext x; simp [cmpxOp64, hb, hcx]))))

/-- The dequeuers' table: `dmem` maps no 8-byte word. -/
abbrev deqTable3 (P : Params) (w : Nat) : Label → MachineData → (SharedEnv.counted (ED3X P w)).State → Prop :=
  fun lb s σ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    ((lb = "dequeuer" ∧ L0 P w σ.1) ∨ (lb = "deq" ∧ L0 P w σ.1) ∨
      (lb = "deq_pop" ∧ ∃ y3 yt u, s.regs.get64 .rbx = BitVec.setWidth 64 y3 ∧
        s.regs.get64 .rcx = BitVec.setWidth 64 u ∧ BitVec.setWidth 64 yt ≠ BitVec.setWidth 64 y3 ∧
        L3 P w y3 yt u σ.1) ∨
      (lb = "deq_empty" ∧ L0 P w σ.1) ∨
      (lb = "ddone" ∧ Dn3 P w (s.regs.get64 .r12) σ.1))

set_option maxHeartbeats 4000000 in
theorem deq3V_envGCAdj' (P : Params) (hL : QLocs P) {w : Nat} (hw : w = 1 ∨ w = 2) (hh : symV3 "head" = P.h)
    (ht : symV3 "tail" = P.t) :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ L0 P w g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ED3X P w)))
        (fun x => (x.1.2 = labV3 "ddone" ∧ Dn3 P w (x.1.1.regs.get64 .r12) x.2.1) ∨ False)
        ((s, labV3 "dequeuer"), g) := by
  have hw2 : w ≤ 2 := by omega
  obtain ⟨h, t, s0, n1, n2, trk⟩ := P
  simp only at hh ht
  subst hh ht
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (ED3X _ w))
    (Q := fun s σ => Dn3 _ w (s.regs.get64 .r12) σ.1) (E := fun _ _ _ => False) (deqTable3 _ w) ?_ rfl
    (by decide) deqFragV3_placedIn deqFragV3_last s g (by simpa [deqTable3] using hsg)
  cfg_cases_env [deqFragV3]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [String.reduceEq, true_and, false_and, or_false, false_or] at hT
  -- `dequeuer`
  case vc1 => exact ⟨hd8, .inr (.inl ⟨rfl, hT⟩)⟩
  -- `deq`
  case vc1 | vc2 | vc3 | vc4 => exact ⟨trivial, mem_sAll8 _⟩
  case vc5 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 _
    d_reads
    have hb := (h4.fence (fenC f5).1).back
    to_deq hb
    d_cnt
  case vc6 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at cr
    dsimp only
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inl ⟨rfl, w3, wt, wu, by simp [e3], by simp [e5],
      fun h => cr (by rw [e3, e4, h]; exact BitVec.sub_self _),
      by simpa using ((h4.fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1⟩))⟩, .inl (by decide)⟩
  case vc7 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 b8 g8 f8 ct g9 f9 _
    d_reads
    have hb := (((((h4.fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1).fence
      (fenC f9).1).back
    dsimp only
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr (.inl ⟨rfl, hb⟩)))⟩, .inl (by decide)⟩
  case vc8 => exact hd8 _
  case vc9 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 b8 g8 f8 ct g9 f9 g10 f10 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    have hE := (((((h4.fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1).fence
      (fenC f9).1).fence (fenC f10).1
    exact okRC (okR (vc3_help hL hw2 _ hE (by rw [← e5]; exact ct)).1 rfl
      (by funext x; simp [cmpxOp64, e3, e5])) (mem_sAll8 _)
  case vc10 | vc11 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 cz g5 f5 g6 f6 cr g7 f7 b8 g8 f8 ct g9 f9 g10 f10 old g11 hc heq g12 f12 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    have hE := (((((h4.fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1).fence
      (fenC f9).1).fence (fenC f10).1
    have hC := (vc3_help hL hw2 _ hE (by rw [← e5]; exact ct)).2 old g11.1
      (stepR (rmwC hc).1 rfl (by funext x; simp [cmpxOp64, e3, e5]))
    have hb := hC.fence (fenC f12).1
    to_deq hb
    d_cnt
  -- `deq_pop`
  case vc1 => exact hd8 _
  case vc2 =>
    rename_i g1 f1 _
    obtain ⟨y3, yt, u, hb, hcx, hne, hD⟩ := hT
    simp only [Reg64s.get64] at hb hcx
    exact okRC (okR (vc3_pop hL hw _ (hD.fence (fenC f1).1) hne).1 rfl
      (by funext x; simp [cmpxOp64, hb, hcx])) (mem_sAll8 _)
  case vc3 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 _
    p_absurd
  case vc4 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 g4 f4 g5 f5 _
    p_pop0
    simp at heq
    have heq' : BitVec.setWidth 64 old = BitVec.setWidth 64 y3 := by simpa [hb] using heq
    have hd : Dn3 _ w _ _ := ⟨hP.1, .inr (hP.2.1 heq')⟩
    have hd' := ((hd.fence (fenC f3).1).fence (fenC f4).1).fence (fenC f5).1
    dsimp only
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr (.inr ⟨rfl,
      by simpa [hcx] using hd'⟩)))⟩, .inl (by decide)⟩
  case vc5 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 _
    p_pop0
    have hne' : BitVec.setWidth 64 old ≠ BitVec.setWidth 64 y3 := by
      intro h'; simp [hb, h'] at heq
    have hb := (hP.2.2 hne').fence (fenC f3).1
    to_deq hb
    d_cnt
  case vc6 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 g4 f4 g5 f5 _
    p_absurd
  -- `deq_empty`
  case vc1 =>
    rename_i b1 g1 f1 g2 f2 _
    have hd : Dn3 _ w 0 _ := ⟨hT.1, .inl ⟨rfl, hT.2⟩⟩
    have hd' := (hd.fence (fenC f1).1).fence (fenC f2).1
    try dsimp only
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, .inr (.inr (.inr (.inr ⟨rfl, by simpa using hd'⟩)))⟩,
      .inl (by decide)⟩
  -- `ddone`
  case vc1 => exact hT

end Deq

/-! ## Only release writes -/

section NoNT

local instance msq3ImageV.envN : CodeEnv := ⟨layout msq3ImageV⟩

theorem enqFragV3_placedIn : Program.PlacedIn enqFragV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := msq3ImageV) msq3ImageV_wf rfl (by decide))
    enqFragV3_sub

omit [Executable.ValidLayout (layout msq3ImageV)] in
theorem enqFragV3_last : ∀ l blk, Program.blockAt enqFragV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV3 "edone" :=
  Program.after_last_of (by decide)

set_option maxHeartbeats 1000000 in
open Kraken.Promising.X64.EnvG.TreiberX (EnvRT) in
/-- **The verbatim enqueuer makes only release writes** (counted, partial;
the image). -/
theorem enq3V_noNT :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labV3 "edone" ∧ True) ∨ False) ((s, labV3 "enqueuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
      ∀ a, Mem.loadInt s.dmem a 8 = none) ?_ rfl (by decide) enqFragV3_placedIn enqFragV3_last s g hs
  cfg_cases_env [enqFragV]
  msq_noNT_cases

set_option maxHeartbeats 1000000 in
open Kraken.Promising.X64.EnvG.TreiberX (EnvRT) in
/-- **The verbatim dequeuer makes only release writes** (counted, partial). -/
theorem deq3V_noNT :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labV3 "ddone" ∧ True) ∨ False) ((s, labV3 "dequeuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
      ∀ a, Mem.loadInt s.dmem a 8 = none) ?_ rfl (by decide) deqFragV3_placedIn deqFragV3_last s g hs
  cfg_cases_env [deqFragV3]
  msq_noNT_cases

end NoNT

end Kraken.Promising.X64.EnvG.MsQueue3X
