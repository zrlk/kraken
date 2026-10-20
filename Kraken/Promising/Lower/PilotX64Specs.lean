/-
**The function specifications of `push` and
`pop` on x64, once each.** ISA: x64; environment: the
x64 treiber2 ownership environment with value-restricted load answers,
`EWV P w = EnvGCAdjXV Arch.tso w (plan P w) (SL P) (GV P)`
(`Lower/PilotX64Bridge.lean`), counted.

Each spec is a `FunSpecPartialEnv` (`X64/EnvCallsPartial.lean`) at the
function's label in the laid-out `pilotX`, by `FunSpecPartialEnv.of_cfg`
with one `vcgen` call per function and the VCs of `EnvG/X64Treiber2VC.lean`
(the same VCs as the verbatim `treiber2.kl` worker,
`EnvG/X64Treiber2VCGen.lean`). The specs mention the caller only through
the draft convention's interface: arguments `rdi` (`&top`), `rsi` (the node, `push`), the
result `rax` (`pop`), the return address `ra` in the `dmem` slot at `rsp`
(`RetAt`), and the callee-saved frame (`Saved`: `rbx rbp r12 r13 r14 r15`
and `dmem` unchanged; `rsp` back above the slot).

The private memory is the private-stack layer's: the heap (`top` and both links, the bytes
of the layout `SL P`) is off `dmem` (`HeapOff (HP P)`), so every shared
access at a heap address is the shared event (`shared_of_heapOff_load`).
The layout `SL P` is the x64 link's `S`: `within (SL P)` asks every access to
be a location of it. `pop`'s link load is at the pointer read from `top`;
its answer is in `GV P` (`0`, `n0` or `n1`), non-null by the `je`, so it
names a node: in the layout and off `dmem`.
-/
import Kraken.Promising.Lower.PilotX64Prog
import Kraken.Promising.Lower.PilotX64Bridge
import Kraken.X64.EnvCallsPartial
import Kraken.Promising.Lower.DStack

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The environment, the heap and the frame -/

/-- **The value invariant**: `top` and the links hold `0`, `n0` or `n1` (as
the 128-bit payloads of 8-byte words). -/
def GV (P : Params) : Loc → Val → Prop :=
  fun _ v => v = 0 ∨ v = (P.n 0).setWidth 128 ∨ v = (P.n 1).setWidth 128

/-- **The shared layout**: `top` and both links. -/
abbrev SL (P : Params) : SharedEnv.Layout := [(P.t, 8), (P.n 0, 8), (P.n 1, 8)]

/-- **The heap**: the bytes of the shared layout. -/
abbrev HP (P : Params) : BitVec 64 → Prop := SharedLayout.Covers (SL P)

/-- Thread `w`'s environment. -/
noncomputable abbrev EWV (P : Params) (w : Nat) : SharedEnv := EnvGCAdjXV Arch.tso w (plan P w) (SL P) (GV P)

/-- **The callee-saved frame** of the draft calling convention (x64): `rbx rbp r12 r13`, the
allocator registers `r14 r15`, and the private memory unchanged (`rsp` is
stated separately). -/
def Saved (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ s.regs.get64 .rbp = t.regs.get64 .rbp ∧
    s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13 ∧
    s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15 ∧ s.dmem = t.dmem

theorem Saved.refl (t : MachineData) : Saved t t := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The return address `ra` in the `dmem` slot at `rsp`.** -/
def RetAt (s : MachineData) (ra : Int64) : Prop :=
  ∃ v, Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some v ∧ Int64.ofBitVec (BitVec.ofInt 64 v) = ra

/-- A node of the layout is a heap address. -/
theorem hp_n (P : Params) {w : Nat} (hw : w < 2) : HP P (P.n w) := by
  rcases w with _ | _ | w
  · exact covers_self (n := 8) (by simp) (by decide)
  · exact covers_self (n := 8) (by simp) (by decide)
  · omega

theorem hp_t (P : Params) : HP P P.t := covers_self (n := 8) (by simp) (by decide)

theorem sl_n (P : Params) {w : Nat} (hw : w < 2) : (P.n w, 8) ∈ SL P := by
  rcases w with _ | _ | w
  · simp
  · simp
  · omega

/-- **A non-null answer in `GV` names a node.** -/
theorem gv_node {P : Params} {l : Loc} {v : Val} (hg : GV P l v) (hnz : BitVec.setWidth 64 v ≠ 0) :
    ∃ w, w < 2 ∧ BitVec.setWidth 64 v = P.n w := by
  rcases hg with rfl | rfl | rfl
  · exact absurd rfl hnz
  · exact ⟨0, by decide, by simp⟩
  · exact ⟨1, by decide, by simp⟩

/-! ## Access helpers: a heap access is the shared event -/

/-- A combined load at a heap address: the environment's step, its answer in
`G`. -/
theorem ldH {E : SharedEnv} {G : Loc → Val → Prop} {H : BitVec 64 → Prop} {d : Mem 64} {a x : BitVec 64}
    {g g' : (SharedEnv.counted (valsEnv E G)).State} (hH : HeapOff H d) (ha : H a)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g) ∨ (Mem.loadInt d a 8 = none ∧ ∃ v,
      ((E.step (.load .plain false a 8) g.1 v g'.1 ∧ G ⟨a, 8⟩ v) ∧
        g'.2 = g.2 + (SharedAccess.load .plain false a 8).tick) ∧ x = BitVec.setWidth 64 v)) :
    ∃ v, E.step (.load .plain false a 8) g.1 v g'.1 ∧ G ⟨a, 8⟩ v ∧ g.2 < g'.2 ∧ x = BitVec.setWidth 64 v := by
  obtain ⟨v, ⟨⟨hs, hg⟩, ht⟩, rfl⟩ := shared_of_heapOff_load (n := 8) hH ha (by decide) h
  exact ⟨v, hs, hg, by simp only [SharedAccess.tick] at ht; omega, rfl⟩

/-- A combined store at a heap address: the environment's step, `dmem`
unchanged. -/
theorem stH {E : SharedEnv} {G : Loc → Val → Prop} {H : BitVec 64 → Prop} {d m : Mem 64} {a r : BitVec 64}
    {g g' : (SharedEnv.counted (valsEnv E G)).State}
    (hH : HeapOff H d) (ha : H a)
    (h : ((Mem.loadInt d a 8).isSome = true ∧ m = Mem.storeInt d a 8 r.toInt ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ m = d ∧ ∃ ok, (E.step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1 ∧
        True) ∧ g'.2 = g.2 + (SharedAccess.store .plain false a 8 (r.setWidth 128)).tick)) :
    m = d ∧ (∃ ok, E.step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1) ∧ g.2 < g'.2 := by
  obtain ⟨rfl, ok, ⟨hs, -⟩, ht⟩ := shared_of_heapOff_store (n := 8) hH ha (by decide) h
  exact ⟨rfl, ⟨ok, hs⟩, by simp only [SharedAccess.tick] at ht; omega⟩

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotX)]

local instance pilotX.env : CodeEnv := ⟨layout pilotX⟩

omit layout [Executable.ValidLayout (layout pilotX)] in
theorem pilotX_wf : Program.WF pilotX := by decide

/-- Where `pilotX`'s blocks sit. -/
theorem pilotX_placed : Program.Placed pilotX "main" :=
  Program.placed_of_layout pilotX_wf rfl (by decide)

/-! ## `push` -/

/-- `push`'s text, as a fragment of `pilotX`. -/
def pushFragX : Program := parse("
push:
    movq (%rdi), %rax
    movq %rax, (%rsi)
    lock cmpxchgq %rsi, (%rdi)
    jne push
    ret
")

/-- `push`'s precondition: `rdi = &top`, `rsi` the node, the return address
in its slot, the heap off `dmem`, before the push (`Pu`). -/
def PushPre (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EWV P w)).State) :
    Prop :=
  t.regs.get64 .rdi = P.t ∧ t.regs.get64 .rsi = P.n w ∧ RetAt t ra ∧ HeapOff (HP P) t.dmem ∧ Pu P w σ.1

/-- `push`'s postcondition: the frame kept, `rsp` above the slot, pushed
(`Po`). -/
def PushPost (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWV P w)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  Saved t s ∧ s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ Po P w σ.1

/-- `push`'s loop table. -/
abbrev pushTable (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWV P w)).State) :
    Label → MachineData → (SharedEnv.counted (EWV P w)).State → Prop :=
  fun lb s σ => lb = "push" ∧ s.regs.get64 .rdi = P.t ∧ s.regs.get64 .rsi = P.n w ∧ Saved t s ∧
    s.regs.get64 .rsp = t.regs.get64 .rsp ∧ Pu P w σ.1

/-- **`push`'s specification**, once, for every caller. -/
theorem push_specX (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "push")
      (PushPre P w) (PushPost P w) := by
  refine FunSpecPartialEnv.of_cfg (p := pushFragX) (pushTable P w) rfl (by decide)
    (Program.PlacedIn.of_placedE pilotX_placed (by decide))
    (fun ra t g ⟨h1, h2, _, _, h5⟩ => ⟨rfl, h1, h2, Saved.refl t, rfl, h5⟩) ?_
  rintro ra t g ⟨-, -, ⟨v0, hv0, hra⟩, hH, -⟩
  have ea : ∀ s : MachineData, s.regs.get64 .rdi = P.t → s.regs.get64 .rdi + Int64.toBitVec 0 = P.t :=
    fun s h => by simp [h]
  cfg_cases_env [pushFragX]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨⟨-, hdi, hsi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp, hT⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX, fenceMonoX_le_valsEnv,
    SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step, SharedEnv.within_ok_load,
    SharedEnv.within_ok_store, SharedEnv.within_ok_rmw, valsEnv_ok, valsEnv_step_load, valsEnv_step_store,
    valsEnv_step_rmw] at *
  all_goals rw [← fdm] at hH; rw [← fdm, ← hsp] at hv0
  all_goals have hdi' := hdi; have hsi' := hsi; have hv0' := hv0; simp only [Reg64s.get64] at hdi' hsi' hv0'
  case vc1 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc2 =>
    rename_i v σ1 _ hld _
    obtain ⟨v, hs, -, -, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    have h := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).1
    exact ⟨by simpa [hsi, hsi', Params.nd] using h, by simpa [SharedEnv.AccessIn, hsi, hsi'] using sl_n P hw⟩
  case vc3 =>
    rename_i v σ1 dm σ2 hld hst _
    obtain ⟨rfl, -, -⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    exact hH.loadInt_none (by simpa [hdi, hdi'] using hp_t P) (by decide)
  case vc4 =>
    rename_i v σ1 dm σ2 hld hst _
    obtain ⟨v, hs, -, -, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi, hsi', Params.nd]) (by simp))
    have h := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).1
    exact ⟨okR h (by simp [hdi, hdi', Params.top]) (by simp [hsi, hsi', cmpxOp64]), by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc5 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc6 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 hnone hld hst hcas hf _
    obtain ⟨rfl, -, -⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    simp [hv0, hv0'] at hnone
  case vc7 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 ra σ5 hld hst hcas hf hret _
    obtain ⟨v, hs, -, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, l2⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi, hsi', Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [hsi, hsi', cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd heq hne
    obtain ⟨u, hu, rfl, rfl⟩ := private_of_mapped_load (hc := hret) (by simp [hv0, hv0'])
    have e : u = v0 := by simp [hv0, hv0'] at hu; omega
    subst e
    refine .inr ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, hPo.fence hf.1⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc8 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 hld hst hcas hf _
    obtain ⟨v, hs, -, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, l2⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi, hsi', Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [hsi, hsi', cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPu⟩ | ⟨heq', -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_,
        Pu.fence hPu.pu hf.1⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      rotate_left 9
      · subst hg
        have h3 := hcas.2; have h4 := hf.2
        simp only [SharedAccess.tick] at h3
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
    · exact absurd heq' hne
  case vc9 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 hnone hld hst hcas hf _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne
  case vc10 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 ra σ5 hld hst hcas hf hret _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

/-! ## `pop` -/

/-- `pop`'s text, as a fragment of `pilotX`. -/
def popFragX : Program := parse("
pop:
    movq (%rdi), %rax
    testq %rax, %rax
    je pop
    movq (%rax), %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne pop
    ret
")

/-- `pop`'s precondition: `rdi = &top`, the return address in its slot, the
heap off `dmem`, pushed (`Po`). -/
def PopPre (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EWV P w)).State) :
    Prop :=
  t.regs.get64 .rdi = P.t ∧ RetAt t ra ∧ HeapOff (HP P) t.dmem ∧ Po P w σ.1

/-- `pop`'s postcondition: the frame kept, `rsp` above the slot, the popped
node in `rax` (`DnB`). -/
def PopPost (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWV P w)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  Saved t s ∧ s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ DnB P w (s.regs.get64 .rax) σ.1

/-- `pop`'s loop table. -/
abbrev popTable (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWV P w)).State) :
    Label → MachineData → (SharedEnv.counted (EWV P w)).State → Prop :=
  fun lb s σ => lb = "pop" ∧ s.regs.get64 .rdi = P.t ∧ Saved t s ∧ s.regs.get64 .rsp = t.regs.get64 .rsp ∧
    Po P w σ.1

/-- **`pop`'s specification**, once, for every caller. -/
theorem pop_specX (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "pop")
      (PopPre P w) (PopPost P w) := by
  refine FunSpecPartialEnv.of_cfg (p := popFragX) (popTable P w) rfl (by decide)
    (Program.PlacedIn.of_placedE pilotX_placed (by decide))
    (fun ra t g ⟨h1, _, _, h4⟩ => ⟨rfl, h1, Saved.refl t, rfl, h4⟩) ?_
  rintro ra t g ⟨-, ⟨v0, hv0, hra⟩, hH, -⟩
  have ea : ∀ s : MachineData, s.regs.get64 .rdi = P.t → s.regs.get64 .rdi + Int64.toBitVec 0 = P.t :=
    fun s h => by simp [h]
  cfg_cases_env [popFragX]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨⟨-, hdi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp, hT⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX, fenceMonoX_le_valsEnv,
    SharedEnv.counted_step, SharedEnv.counted_ok, valsEnv_ok, valsEnv_step_load, valsEnv_step_rmw] at *
  all_goals rw [← fdm] at hH; rw [← fdm, ← hsp] at hv0
  all_goals have hdi' := hdi; have hv0' := hv0; simp only [Reg64s.get64] at hdi' hv0'
  case vc1 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc2 =>
    rename_i v σ1 af σ2 hz σ3 hld hf1 hf2 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, hPl.po⟩,
      .inr fun ⟨_, hg'⟩ => ?_⟩)
    rotate_left 8
    · subst hg'
      have := hf1.2; have := hf2.2
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc3 =>
    rename_i v σ1 af σ2 hz σ3 hnone hld hf1 hf2 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    exact ⟨trivial, by simpa [SharedEnv.AccessIn, hn'] using sl_n P hw'⟩
  case vc4 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 hld hf1 hf2 hld2 _
    exact hH.loadInt_none (by simpa [hdi, hdi'] using hp_t P) (by decide)
  case vc5 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 hld hf1 hf2 hld2 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u, hs2, -, l2, rfl⟩ := ldH hH (by simp [hn']; exact hp_n P hw') hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    have h := (vc_pop_cas hw _ hPr hz').1
    exact ⟨okR h (by simp [hdi, hdi', Params.top]) (by simp [cmpxOp64]), by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc6 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 hld hf1 hf2 hld2 hcas hf3 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz2
  case vc7 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 hnone hld hf1 hf2 hld2 hcas hf3 _
    simp [hv0, hv0'] at hnone
  case vc8 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 ra σ7 hld hf1 hf2 hld2 hcas hf3 hret _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u, hs2, -, l2, rfl⟩ := ldH hH (by simp [hn']; exact hp_n P hw') hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    have hc := (vc_pop_cas hw _ hPr hz').2 old σ5.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd heq hne
    obtain ⟨u', hu, rfl, rfl⟩ := private_of_mapped_load (hc := hret) (by simp [hv0, hv0'])
    have e : u' = v0 := by simp [hv0, hv0'] at hu; omega
    subst e
    refine .inr ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, ?_⟩
    rotate_left 7
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hDn.fence hf3.1
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc9 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 hld hf1 hf2 hld2 hcas hf3 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u, hs2, -, l2, rfl⟩ := ldH hH (by simp [hn']; exact hp_n P hw') hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    have hc := (vc_pop_cas hw _ hPr hz').2 old σ5.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPo⟩ | ⟨heq', -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_,
        hPo.fence hf3.1⟩, .inr fun ⟨_, hg'⟩ => ?_⟩)
      rotate_left 8
      · subst hg'
        have := hf1.2; have := hf2.2; have := hf3.2; have h3 := hcas.2
        simp only [SharedAccess.tick] at h3
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
    · exact absurd heq' hne
  case vc10 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 hnone hld hf1 hf2 hld2 hcas hf3 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz2).symm hne
      | exact absurd hz2.symm hne
      | exact absurd hz2 hne
  case vc11 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 ra σ7 hld hf1 hf2 hld2 hcas hf3 hret _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz2).symm hne
      | exact absurd hz2.symm hne
      | exact absurd hz2 hne

end Kraken.Promising.Lower.PilotX
