/-
**The lowered Michael–Scott queue on the
Promising model.**

`msqPilot_promising`: thread `0` runs `progE` (`main_e` calling `enq` twice),
thread `1` runs `progD` (`main_d` calling `deq` twice), each from a start state
of the runtime (`StartE`/`StartD`: `x30` the end of its text, `q = &head` in
`x21`, the nodes in `x22`/`x23`, empty `dmem`); every final configuration
reachable under `Arch.armv8` has the dequeuer's `x10 = 1`, `x11 = 2`
(`MsQueue2Final`, msqueue2's FIFO property).

The assembly is `msqueue2_envG` (`EnvG/MsQueue2Public.lean`) with the inline
threads replaced by the lowered texts: the rules from
`main{E,D}_partialTripleEnv`, purity from `main{E,D}_pure`; `MB2`, `tRes2`,
`ghost2`, `start1_init`, `comD2_init`, `erase_init2` and
`msqueue2_final_of_hB` are reused unchanged.
-/
import Kraken.Promising.Lower.MsqPilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue

/-! ## The rules -/

/-- **The enqueuer's rule** (`enq2Rule` for `progE`). -/
noncomputable def ruleE [layout : _root_.Layout] [Executable.ValidLayout (layout progE)] (P : Params2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB2 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postOf progE fun _ σ => ∃ _ : Nat, ComE2 P σ) (planE2_valid P)
    progE_rmwLive progE_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) fun c t r g cl σ hpost hp hrel _ => by
      obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
      rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
      · exact .inr hcom.2.2.1
      · rw [hp] at hts; cases hts

/-- **The dequeuer's rule** (`deq2Rule` for `progD`). -/
noncomputable def ruleD [layout : _root_.Layout] [Executable.ValidLayout (layout progD)] (P : Params2) :
    ThreadRuleRXF (I := isa) Arch.armv8 (MB2 P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postOf progD fun s σ => ∃ _ : Nat,
      Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ) (planD2_valid P)
    progD_rmwLive progD_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) fun c t r g cl σ hpost hp hrel _ => by
      obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
      have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
      rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
      · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
      · rw [hp] at hts; cases hts

/-! ## The start states -/

section Start

variable [layout : _root_.Layout]

/-- **The enqueuer's start state** (the runtime's side of the convention): at
the start of `progE`, returning to its end; `q = &head` in `x21`, the nodes
in `x22`/`x23`; no private copy of any 8- or 4-byte word. -/
structure StartE (h n1 n2 : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout progE
  decls : s.decls = {}
  endPc : s.endPc = (layout progE).addrOf progE.length
  pc : s.st.2 = (layout progE).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout progE).addrOf progE.length
  x21 : s.st.1.regs.X21.toBitVec = h
  x22 : s.st.1.regs.X22.toBitVec = n1
  x23 : s.st.1.regs.X23.toBitVec = n2
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- **The dequeuer's start state**: at the start of `progD`, returning to its
end; `q = &head` in `x21`; empty `dmem`. -/
structure StartD (h : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout progD
  decls : s.decls = {}
  endPc : s.endPc = (layout progD).addrOf progD.length
  pc : s.st.2 = (layout progD).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout progD).addrOf progD.length
  x21 : s.st.1.regs.X21.toBitVec = h
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Start

/-! ## The theorem -/

/-- The threads' purity specifications: `progE` at layout `l0` at thread `0`,
`progD` at layout `l1` elsewhere. -/
def msqPilotPureSpec (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := l0) progE fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := l1) progD fun _ _ => ∃ _ : Nat, True

/-- **The lowered Michael–Scott queue on the Promising model** (AArch64,
`Arch.armv8`, `isa`): for all layouts `l0` of `progE` and `l1` of `progD`, all
addresses `h` of `head`, `t = h + 8` of `tail` (the queue's two words, passed
as `q = h`), `d` of the dummy node and `n1`, `n2` of the enqueued nodes (data
`[n]`, 4 bytes; link `[n + 8]`, 8 bytes) with msqueue2's disequalities: if
thread `0` starts `progE` with `q = h`, nodes `n1`, `n2` (`StartE`), thread
`1` starts `progD` with `q = h` (`StartD`), and the initial memory has
`head = tail = d` and the three links `0` (`InitV2`), then every final
configuration reachable under `Arch.armv8` has `1:X10 = 1 ∧ 1:X11 = 2`
(the conclusion of `msqueue2_envG`). -/
theorem msqPilot_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2Final cfg := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  obtain ⟨he0, hds0, hend0, hpc0, h30, h21, h22, h23, hd8, hd4⟩ := h0
  obtain ⟨he1, hds1, hend1, hpc1, h30', h21', hd8', hd4'⟩ := h1
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB2 ⟨⟨h, t, d, n1⟩, n2⟩) (Φ := MsQueue2Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) (ghost2_pend _) (msqPilotPureSpec l0 l1 _)
    ?_ ?_ hc hf fun rF' g' E' hle hsize hB => msqueue2_final_of_hB hL hf E' hle hsize hB
  · rintro (_ | _ | _) s hs <;> cases hs
    · letI : CodeEnv := ⟨l0 progE⟩
      exact RelPureSpec.holds_of_partialTripleEnv (layout := l0)
        (mainE_pure (layout := l0) _ n1 n2 (fun v => by
          show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
          rw [ghost2_rel_ne (not_isW_dat _)]; exact Pred.emp_pure v) (fun v => by
          show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params2.dat2 ⟨⟨h, t, d, n1⟩, n2⟩)) v
          rw [ghost2_rel_ne (not_isW_dat2 _)]; exact Pred.emp_pure v)).uncount
        rfl he0 hds0 hend0 hpc0 ⟨0, h30, h22, h23, hd8, hd4⟩
    · letI : CodeEnv := ⟨l1 progD⟩
      exact RelPureSpec.holds_of_partialTripleEnv (layout := l1) (mainD_pure (layout := l1) _).uncount
        rfl he1 hds1 hend1 hpc1 ⟨0, h30', hd8', hd4'⟩
  · rintro (_ | _ | i) htid k j
    · letI : CodeEnv := ⟨l0 progE⟩
      have hI : (ruleE (layout := l0) ⟨⟨h, t, d, n1⟩, n2⟩).Inv True (Config.init [s0, s1] initMem)
          (tRes2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩ 0) (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩) :=
        invGFCAdj_init (tid := 0) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l0)
          (mainE_partialTripleEnv (layout := l0) _ hL ht).uncount rfl he0 hds0 hend0 hpc0
          ⟨0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩)
      exact NPSafeF.of_ruleRXF _ k j _ _ _ _ hI
    · letI : CodeEnv := ⟨l1 progD⟩
      have hI : (ruleD (layout := l1) ⟨⟨h, t, d, n1⟩, n2⟩).Inv True (Config.init [s0, s1] initMem)
          (tRes2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩ 1) (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩) :=
        invGFCAdj_init (tid := 1) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l1)
          (mainD_partialTripleEnv (layout := l1) _ hL ht).uncount rfl he1 hds1 hend1 hpc1
          ⟨0, h30', h21', ⟨hd8', hd4'⟩, comD2_init _ _ hi⟩)
      exact NPSafeF.of_ruleRXF _ k j _ _ _ _ hI
    · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## The concrete instance (`MsqPilotProg`'s explorer configuration) -/

section
attribute [local instance] layoutE

theorem threadE_start : StartE 0x1000 0x1200 0x1300 threadE := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [threadE, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] layoutD

theorem threadD_start : StartD 0x1000 threadD := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [threadD, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **Non-vacuity**: `msqPilot_promising` at the explorer's configuration
(`msqPilotRun`): `head` at `0x1000`, `tail` at `0x1008` (both initially the
dummy `0x1100`), the nodes at `0x1200`, `0x1300` (links `0`). -/
theorem msqPilot_promising_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadE, threadD] initMem) c) (hf : c.final = true) :
    MsQueue2Final c :=
  msqPilot_promising layoutE layoutD 0x1000 0x1008 0x1100 0x1200 0x1300 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) threadE_start threadD_start
    (by refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.Lower.MsqPilot
