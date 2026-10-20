/-
**The lowered Michael–Scott queue with a
bump-allocating enqueuer, on the Promising model, through the kit**
(`Kit.lower_promising`, `Kit.lower_promising_lse2`).
ISA: AArch64 (`isa`, and `isaLSE2` for `_lse2`); `Arch.armv8`; machine: the
executable Promising machine (`Reachable`).

Thread `0` runs `msqA` (`main_e`: two `bl alloc`, two `enq`), thread `1`
the MS queue pilot's `progD` (`KitMsq.deqT`, unchanged). The protocol is msqueue2's
(`MB2`, `ghost2`, `tRes2`, `erase_init2`, `msqueue2_final_of_hB`, unchanged)
at `pA h t d base`: the nodes are `n1 = base` and `n2 = base + 16`, the two
allocations from the enqueuer's arena (`x27 = base` at start).

Start hypotheses only: the threads' start states (`StartA`: `x27 = base`,
room for two nodes below `x28`; `MsqPilot.StartD`), the queue's initial words
(`head = tail = d`, `d`'s link `0`), the **pre-zeroed arena's links**
(`[base + 8] = [base + 16 + 8] = 0`; the data words are arbitrary; see the
emitter rule in `Lower/MsqAllocProg.lean`), and the disjointness of the
arena's words from `head`, `tail` and the dummy node. The code is not in the
data memory of this model (each thread's executable is `s.exe`), so no
code/arena disjointness is needed.
-/
import Kraken.Promising.Lower.MsqAllocMain
import Kraken.Promising.Lower.KitMsqLSE2

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.MsqAlloc

open Kraken.Promising.SLR.EnvG.MsQueue Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.MsqPilot (StartD progD threadD threadD_start layoutD)
open Kraken.Promising.Lower.KitMsq (deqT)

/-- **The protocol's parameters**: `head` at `h`, `tail` at `t`, the dummy
node `d`, and the two allocated nodes `n1 = base`, `n2 = base + 16`. -/
abbrev pA (h t d base : BitVec 64) : Params2 := ⟨⟨h, t, d, base⟩, base + 16⟩

/-- msqueue2's layout facts at `pA` from the arena's disjointness. -/
theorem qLocsA {h t d base : BitVec 64} (hht : h ≠ t) (hhd : h ≠ d + 8) (htd : t ≠ d + 8) (hb1 : h ≠ base + 8)
    (hb2 : h ≠ base + 16 + 8) (tb1 : t ≠ base + 8) (tb2 : t ≠ base + 16 + 8) (db1 : d ≠ base)
    (db2 : d ≠ base + 16) (hb0 : base ≠ 0) (hb16 : base + 16 ≠ 0) : QLocs2 (pA h t d base) :=
  ⟨⟨hht, hhd, hb1, htd, tb1, db1⟩, hb2, tb2, db2, by bv_omega, hb0, hb16⟩

theorem ghost2_pure {P : Params2} {l : Loc} (hl : ¬ P.IsW l) (v : Val) : Pred.Pure ((ghost2 P).rel l) v := by
  rw [ghost2_rel_ne hl]; exact Pred.emp_pure v

/-- `hB` of the enqueuer (`KitMsq.hB_E`'s proof, for `msqA`). -/
theorem hB_EA (l : _root_.Layout) (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) msqA (fun _ σ => ∃ _ : Nat, ComE2 P σ) (t.st.st, σ) → t.prom = [] →
    EnvRel 0 (planE2 P) σ c t r g cl → cl → MB2 P c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2.1
  · rw [hp] at hts; cases hts

/-- **The allocating enqueuer as a lowered thread** (thread `0`, `msqA` at
`l`). -/
noncomputable def enqTA (l : _root_.Layout) [Executable.ValidLayout (l msqA)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) (hn2 : P.n2 = P.n1 + 16) (hd : ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨P.n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨P.n1 + 16, 4⟩) v) :
    LowerThread Arch.armv8 0 (ghost2 P).rel (MB2 P) where
  l := l
  p := msqA
  valid := inferInstance
  pl := planE2 P
  hpl := planE2_valid P
  live := msqA_rmwLive (layout := l)
  shape := msqA_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q _ σ := ComE2 P σ.1
  hB := hB_EA l P
  PreR s _ := MainAPreR (layout := l) P.n1 s
  QR _ _ := True
  pure := mainA_pure (layout := l) _ P.n1 hd hd2
  Pre := MainAPre (layout := l) P
  main := mainA_partialTripleEnv (layout := l) P hL ht hn2

/-- **The threads**: the allocating enqueuer and the MS queue pilot's dequeuer. -/
noncomputable def msqAllocTs (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] (h t d base : BitVec 64) (hL : QLocs2 (pA h t d base)) (ht : t = h + 8) :
    ∀ tid, tid < 2 → LowerThread Arch.armv8 tid (ghost2 (pA h t d base)).rel (MB2 (pA h t d base))
  | 0, _ => enqTA l0 _ hL ht rfl (ghost2_pure (not_isW_dat _)) (ghost2_pure (not_isW_dat2 _))
  | 1, _ => deqT l1 _ hL ht
  | _ + 2, hh => absurd hh (by omega)

/-- **The enqueuer's start state** (the runtime's side): at the start of
`msqA`, returning to its end; `q = &head` in `x21`; the bump pointer
`x27 = base` with room for **two** nodes below `x28`; no `dmem` word. -/
structure StartA [layout : _root_.Layout] (h base : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msqA
  decls : s.decls = {}
  endPc : s.endPc = (layout msqA).addrOf msqA.length
  pc : s.st.2 = (layout msqA).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout msqA).addrOf msqA.length
  x21 : s.st.1.regs.X21.toBitVec = h
  x27 : s.st.1.regs.X27.toBitVec = base
  room1 : s.st.1.regs.X27.toBitVec + 16 ≤ s.st.1.regs.X28.toBitVec
  room2 : base + 16 + 16 ≤ s.st.1.regs.X28.toBitVec
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

theorem msqAllocTs_start (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] {h t d base : BitVec 64} (hL : QLocs2 (pA h t d base)) (ht : t = h + 8)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) h base s0)
    (h1 : StartD (layout := l1) h s1) (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem (pA h t d base)) :
    ∀ tid (hh : tid < [s0, s1].length), (msqAllocTs l0 l1 h t d base hL ht tid hh).Start
      (σInit (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem : Config isa).mem (pA h t d base) tid)
        (ghost2 (pA h t d base))) [s0, s1][tid] := by
  intro tid hh
  rcases tid with _ | _ | _
  · obtain ⟨he, hds, hend, hpc, h30, h21, h27, hr1, hr2, hd8, hd4⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, 0, h30, h27, hr1, hr2, hd8, hd4⟩, 0, h30, h21, h27, hr1, hr2, ⟨hd8, hd4⟩,
      start1_init _ _⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
  · simp at hh; omega

/-- **The lowered Michael–Scott queue with a bump-allocating enqueuer, on the
Promising model** (AArch64, `Arch.armv8`, `isa`, executable machine): for all
layouts `l0` of `msqA` and `l1` of `progD`, all addresses `h` of `head`,
`t = h + 8` of `tail` (passed as `q = h`), `d` of the dummy node and `base` of
the enqueuer's arena (nodes at `base` and `base + 16`: data word `[n]`, 4
bytes; link `[n + 8]`, 8 bytes), with the arena's words disjoint from `head`,
`tail` and `d`'s link and both nodes non-zero: if thread `0` starts `msqA`
with `q = h` and `x27 = base`, room for two nodes below `x28` (`StartA`),
thread `1` starts `progD` with `q = h` (`StartD`), the initial memory has
`head = tail = d`, `d`'s link `0` and the arena's two links `0` (pre-zeroed;
the data words are arbitrary), then every final configuration reachable under
`Arch.armv8` has `1:X10 = 1 ∧ 1:X11 = 2` (`MsQueue2Final`, msqueue2's FIFO
property). -/
theorem msqAlloc_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] (h t d base : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (htd : t ≠ d + 8) (hb1 : h ≠ base + 8) (hb2 : h ≠ base + 16 + 8) (tb1 : t ≠ base + 8)
    (tb2 : t ≠ base + 16 + 8) (db1 : d ≠ base) (db2 : d ≠ base + 16) (hb0 : base ≠ 0) (hb16 : base + 16 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) h base s0)
    (h1 : StartD (layout := l1) h s1)
    (hhead : BitVec.setWidth 64 ((Config.init [s0, s1] initMem).mem.initVal ⟨h, 8⟩) = d)
    (htail : BitVec.setWidth 64 ((Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩) = d)
    (hdl : BitVec.setWidth 64 ((Config.init [s0, s1] initMem).mem.initVal ⟨d + 8, 8⟩) = 0)
    (hl1 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem).mem.initVal ⟨base + 8, 8⟩) = 0)
    (hl2 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem).mem.initVal ⟨base + 16 + 8, 8⟩) = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2Final cfg := by
  have hL := qLocsA hht hhd htd hb1 hb2 tb1 tb2 db1 db2 hb0 hb16
  exact lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) rfl
    (msqAllocTs l0 l1 h t d base hL ht) (msqAllocTs_start l0 l1 hL ht h0 h1 ⟨⟨hhead, htail, hdl, hl1⟩, hl2⟩) hc hf
    fun rF' g' E' hle hsize hB => msqueue2_final_of_hB hL hf E' hle hsize hB

/-- **`msqAlloc_promising` on `isaLSE2`** (AArch64 with FEAT_LSE2, the
WeakCore lowering target; `Arch.armv8`, executable machine): for the
hypotheses of `msqAlloc_promising`, every final configuration of `isaLSE2`
reachable from the two start states satisfies `MsQueue2Final` (read in
`Config isa` through `ofL`). `hfree` from `WCLowerable.lse2Free`. -/
theorem msqAlloc_promising_lse2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] (h t d base : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (htd : t ≠ d + 8) (hb1 : h ≠ base + 8) (hb2 : h ≠ base + 16 + 8) (tb1 : t ≠ base + 8)
    (tb2 : t ≠ base + 16 + 8) (db1 : d ≠ base) (db2 : d ≠ base + 16) (hb0 : base ≠ 0) (hb16 : base + 16 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) h base s0)
    (h1 : StartD (layout := l1) h s1)
    (hhead : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨h, 8⟩) = d)
    (htail : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩) = d)
    (hdl : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨d + 8, 8⟩) = 0)
    (hl1 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨base + 8, 8⟩) = 0)
    (hl2 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨base + 16 + 8, 8⟩) = 0)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) := by
  have hL := qLocsA hht hhd htd hb1 hb2 tb1 tb2 db1 db2 hb0 hb16
  refine lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (msqAllocTs l0 l1 h t d base hL ht) (msqAllocTs_start l0 l1 hL ht h0 h1 ⟨⟨hhead, htail, hdl, hl1⟩, hl2⟩)
    (fun tid hh => ?_) (fun _ hf' rF' g' E' hle hsize hB => msqueue2_final_of_hB hL hf' E' hle hsize hB) hc hf
  rcases tid with _ | _ | _
  · exact msqA_lse2Free
  · exact MsqPilot.progD_wcLowerable.lse2Free
  · simp at hh; omega

/-! ## The concrete instance (`MsqAllocProg`'s explorer configuration) -/

section
attribute [local instance] layoutA

theorem threadA_start : StartA 0x1000 0x2000 threadA := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, fun a => ?_,
    fun a => ?_⟩ <;> simp [threadA, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **Non-vacuity**: `msqAlloc_promising` at the explorer's configuration
(`msqAllocRun`): `head` at `0x1000`, `tail` at `0x1008` (both initially the
dummy `0x1100`), the arena at `0x2000` (nodes `0x2000`, `0x2010`; links `0`,
data words garbage `7`). No hypothesis beyond reachability and finality. -/
theorem msqAlloc_promising_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadA, threadD] initMemA) c) (hf : c.final = true) :
    MsQueue2Final c :=
  msqAlloc_promising layoutA layoutD 0x1000 0x1008 0x1100 0x2000 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    threadA_start threadD_start (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    hc hf

/-- **Non-vacuity on `isaLSE2`**: `msqAlloc_promising_lse2` at the same
configuration. -/
theorem msqAlloc_promising_lse2_concrete {fuel : Nat} {c : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadA, threadD] initMemA : Config isaLSE2) c)
    (hf : c.final = true) : MsQueue2Final (ofL c) :=
  msqAlloc_promising_lse2 layoutA layoutD 0x1000 0x1008 0x1100 0x2000 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    threadA_start threadD_start (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    hc hf

end Kraken.Promising.Lower.MsqAlloc

#print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising
#print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2
#print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_concrete
#print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_concrete
