/-
**The fully faithful WeakCore MS queue on the
Promising model** (shape A: one enqueuer `enq(1); enq(2)`, one dequeuer
`deq(); deq()`). ISA: AArch64 (`isa`, and `isaLSE2`);
machine: the executable machine (`Reachable Arch.armv8`).

`wcMsqF_promising` is `WcMsq.wcMsq_promising` with thread `0` running
`WcMsq.progE` (`MsqPilot`'s `main_e`, then WeakCore's `enqLoop` lowered with
plain `ldr`s, `wcEnqFrag`) in place of `MsqPilot`'s `ldar` enqueuer: the same
hypotheses (with `StartEF`, `MsqPilot.StartE` for this text) and conclusion
(`WcMsqFinal`). Thread `1` and the final reading are shape A's, unchanged.
`main`/`pure` of the enqueuer come from `mainE_fragL`/`mainE_pureL` at
`wcEnqFrag` by `Kit.partialTripleEnv_of_fragL`.
-/
import Kraken.Promising.Lower.WcEnqMain
import Kraken.Promising.Lower.WcMsqWhole
import Kraken.Promising.Lower.KitFrag

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue Kraken.Promising.Lower.Kit

open Kraken.AArch64.Parser in
/-- `WcMsq.progE` as one literal text (the static checks run on it). -/
def progEL : Program := parseAArch64("
main_e:
    mov x19, x30
    mov w9, #1
    str w9, [x22]
    mov x0, x21
    mov x1, x22
    bl enq
    mov w9, #2
    str w9, [x23]
    mov x0, x21
    mov x1, x23
    bl enq
    mov x30, x19
    ret
enq:
    mov x2, x1
    add x1, x0, #8
enq_loop:
    ldr x3, [x1]
    add x8, x3, #8
    ldr x4, [x8]
    cbnz x4, enq_fix
    mov x5, #0
    casal x5, x2, [x8]
    cbnz x5, enq_loop
    mov x5, x3
    casal x5, x2, [x1]
    ret
enq_fix:
    mov x5, x3
    casal x5, x4, [x1]
    b enq_loop
e_end:
")
/-- `progE` is the literal text. -/
theorem progE_eq : progE = progEL := by decide

section Static

variable [layout : _root_.Layout]

theorem progE_rmwLive : (layout progE).rmwLive = true := by rw [Layout.apply_rmwLive, progE_eq]; decide

theorem progE_phase1F [Executable.ValidLayout (layout progE)] : Phase1TreeF (layout progE) := by
  rw [progE_eq] at *; exact phase1TreeF_of_dirs (by dirs_phase1F progEL)

/-- **The enqueuer's start state**: `MsqPilot.StartE` for `WcMsq.progE`. -/
structure StartEF (h n1 n2 : BitVec 64) (s : isa.State) : Prop where
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

end Static

/-- WeakCore's `enq` text is in the WeakCore-lowerable fragment. -/
theorem progE_wcLowerable : progE.WCLowerable := by rw [progE_eq]; decide

/-- `hB` of the enqueuer (`WcMsq.hB_E` for `WcMsq.progE`). -/
theorem hB_EF (l : _root_.Layout) (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) progE (fun _ σ => ∃ _ : Nat, ComE2 P σ) (t.st.st, σ) → t.prom = [] →
    EnvRel 0 (planE2 P) σ c t r g cl → cl → WB P c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2.1
  · rw [hp] at hts; cases hts

/-- **The enqueuer** (thread `0`, `WcMsq.progE`): `enqT` with `main`/`pure`
from the generic `main_e` at `wcEnqFrag`. -/
noncomputable def enqTF (l : _root_.Layout) [Executable.ValidLayout (l progE)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) (hd : ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨P.n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨P.n2, 4⟩) v) :
    LowerThread Arch.armv8 0 (ghost2 P).rel (WB P) where
  l := l
  p := progE
  valid := inferInstance
  pl := planE2 P
  hpl := planE2_valid P
  live := progE_rmwLive (layout := l)
  shape := progE_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q _ σ := ComE2 P σ.1
  hB := hB_EF l P
  PreR s _ := Int64.ofBitVec s.regs.X30.toBitVec = (l progE).addrOf progE.length ∧ s.regs.X22.toBitVec = P.n1 ∧
    s.regs.X23.toBitVec = P.n2 ∧ Pilot.NoDmem s
  QR _ _ := True
  pure := partialTripleEnv_of_fragL (layout := l) (p := progE) (mainE_pureL _ P.n1 P.n2 hd hd2 (wcEnqFrag_pure _))
    (by decide) rfl (by decide) (by decide) (fun _ _ h => h) fun _ _ _ _ _ _ => trivial
  Pre := MainEPreF P ((l progE).addrOf progE.length)
  main := partialTripleEnv_of_fragL (layout := l) (p := progE) (mainE_fragL P hL fun ph hph => wcEnqFrag_spec P hL ht ph hph)
    (by decide) rfl (by decide) (by decide) (fun _ _ h => h) fun _ _ _ _ _ h => h

/-- **WeakCore's Michael–Scott queue, both operations lowered faithfully, on
the Promising model** (AArch64, `Arch.armv8`, `isa`; shape A):
`wcMsq_promising` with thread `0` running `WcMsq.progE` (plain-`ldr`
`enqLoop`) from `StartEF`. -/
theorem wcMsqF_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartEF (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : WcMsqFinal cfg := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  have hr : ∀ l, ¬ Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ l → ∀ v, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel l) v :=
    fun l hl v => by rw [ghost2_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) rfl
    (fun tid hh => match tid, hh with
      | 0, _ => enqTF l0 _ hL ht (hr _ (not_isW_dat _)) (hr _ (not_isW_dat2 _))
      | 1, _ => deqT l1 _ hL
      | _ + 2, hh => absurd hh (by simp))
    (fun tid hh => ?_) hc hf fun rF' g' E' hle hsize hB => wcMsq_final_of_hB hL hf E' hle hsize hB
  rcases tid with _ | _ | _
  · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
  · simp at hh; omega

/-- **`wcMsqF_promising` on `isaLSE2`**: `hfree` from `Program.WCLowerable`
of both texts. -/
theorem wcMsqF_promising_lse2 {fuel : Nat} (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 progE)] [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8)
    (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2)
    (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqFinal (ofL cfg) := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  have hr : ∀ l, ¬ Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ l → ∀ v, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel l) v :=
    fun l hl v => by rw [ghost2_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (fun tid hh => match tid, hh with
      | 0, _ => enqTF l0 _ hL ht (hr _ (not_isW_dat _)) (hr _ (not_isW_dat2 _))
      | 1, _ => deqT l1 _ hL
      | _ + 2, hh => absurd hh (by simp))
    (fun tid hh => ?_) (fun tid hh => ?_)
    (fun _ hf' rF' g' E' hle hsize hB => wcMsq_final_of_hB hL hf' E' hle hsize hB) hc hf
  · rcases tid with _ | _ | _
    · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
      exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩
    · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
      exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
    · simp at hh; omega
  · rcases tid with _ | _ | _
    · exact progE_wcLowerable.lse2Free
    · exact progD_wcLowerable.lse2Free
    · simp at hh; omega

/-! ## The concrete instance (`wcMsqRunA`'s configuration) -/

instance validE : Executable.ValidLayout (layoutE progE) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

section
attribute [local instance] layoutE

theorem threadE_start : StartEF 0x1000 0x1200 0x1300 threadE := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [threadE, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **Non-vacuity**: `wcMsqF_promising` at the explorer's configuration
(`wcMsqRunA`: shape A's `threadE` running `wcEnqFrag`, `threadD`). -/
theorem wcMsqF_promising_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadE, threadD] MsqPilot.initMem) c)
    (hf : c.final = true) : WcMsqFinal c :=
  wcMsqF_promising layoutE layoutD 0x1000 0x1008 0x1100 0x1200 0x1300 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) threadE_start threadD_start
    (by refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.Lower.WcMsq

#print axioms Kraken.Promising.Lower.WcMsq.wcMsqF_promising
#print axioms Kraken.Promising.Lower.WcMsq.wcMsqF_promising_lse2
#print axioms Kraken.Promising.Lower.WcMsq.wcMsqF_promising_concrete
