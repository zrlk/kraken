/-
**Part 8: the x64 two-thread Treiber stack of
`treiber2.kl`, the `.kl` code verbatim, on `EnvGCAdjX` by `vcgen`.**

The `code` block of `Kraken/Examples/LockFree/X64/treiber2.kl` as written
(`treiber2CodeV`), run by both threads in its image `treiber2ImageV` (the
code, then the `.kl` runner's data trailer `treiber2DataV`: `top`, `n1`,
`n2`), from the entry label `worker` to the exit label `done`. The absolute
operands `(top)` use the 64-bit rules of `Kraken/EnvVCGenAbs64.lean`, the
placement `cfgEnv_partial_at` (`Kraken/EnvCfgAbs.lean`), the VCs
`EnvG/X64Treiber2VC.lean`.

- `workerV_envGCAdj`: thread `w`'s run in the counted `EnvGCAdjX … sAll`;
- `workerV_noNT`: the run in the all-release environment.
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2VC
import Kraken.Promising.SLR.EnvG.X64TreiberRelPure
import Kraken.EnvCfgAbs
import Kraken.EnvVCGenAbs64

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 sAll mem_sAll8)
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.Treiber2X

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The `code` block of `treiber2.kl`, verbatim.** -/
def treiber2CodeV : Program := parse("
worker:
push:
  movq (top),%rax
  movq %rax,(%rbx)
  lock cmpxchgq %rbx,(top)
  jne push
pop:
  movq (top),%rax
  testq %rax,%rax
  je pop
  movq (%rax),%rcx
  lock cmpxchgq %rcx,(top)
  jne pop
  movq %rax,%r12
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `treiber2.kl`: each symbol a label
behind a padding cell, in the order of first mention (`top`, `n1`, `n2`). -/
def treiber2DataV : Program :=
  [.byteArray (.mk #[]), .label "top", .byteArray (.mk #[]), .label "n1", .byteArray (.mk #[]), .label "n2"]

/-- The image: the code, then the data trailer. -/
def treiber2ImageV : Program := treiber2CodeV ++ treiber2DataV

/-- info: 16 -/
#guard_msgs in
#eval treiber2CodeV.length

theorem treiber2ImageV_wf : Program.WF treiber2ImageV := by decide

theorem treiber2CodeV_sub : Program.subBlocksOfE treiber2CodeV treiber2ImageV = true := by decide

/-- Back at `push` after a failed `lock cmpxchgq`: the link's maximal write
is at or below `coh`. -/
theorem Pu2.pu {P : Params} {w : Nat} {y : Val} {σ : EStateX} (h : Pu2 P w y σ) : Pu P w σ := by
  obtain ⟨h1, h2, h3, ⟨t, -, hm, -, hc⟩, h6⟩ := h
  exact ⟨h1, h2, h3, fun p hp => Nat.le_trans (hm p hp) hc, h6⟩

/-- Thread `w`'s environment, restricted to `sAll`. -/
noncomputable abbrev EWX (P : Params) (w : Nat) : SharedEnv := EnvGCAdjX Arch.tso w (plan P w) sAll

/-! ## Step helpers -/

section Helpers

variable {P : Params} {w : Nat}

/-- **A shared 8-byte load** of the run (`dmem` maps no 8-byte word): an `EW`
step, the count up. -/
theorem ldS {d : Std.ExtHashMap (BitVec 64) UInt8} {a x : BitVec 64} {g g' : (SharedEnv.counted (EWX P w)).State}
    (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g) ∨ (Mem.loadInt d a 8 = none ∧ ∃ v,
      ((EW P w).step (.load .plain false a 8) g.1 v g'.1 ∧ g'.2 = g.2 + (SharedAccess.load .plain false a 8).tick) ∧
        x = BitVec.setWidth 64 v)) :
    ∃ v, (EW P w).step (.load .plain false a 8) g.1 v g'.1 ∧ g.2 < g'.2 ∧ x = BitVec.setWidth 64 v := by
  rcases h with ⟨v, hv, -⟩ | ⟨-, v, ⟨hs, ht⟩, rfl⟩
  · rw [hd8] at hv; cases hv
  · exact ⟨v, hs, by simp only [SharedAccess.tick] at ht; omega, rfl⟩

/-- **A shared 8-byte store** of the run: `dmem` unchanged, an `EW` step, the
count up. -/
theorem stS {d m : Std.ExtHashMap (BitVec 64) UInt8} {a r : BitVec 64} {g g' : (SharedEnv.counted (EWX P w)).State}
    (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : ((Mem.loadInt d a 8).isSome = true ∧ m = Mem.storeInt d a 8 r.toInt ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ m = d ∧ ∃ ok, (EW P w).step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1 ∧
        g'.2 = g.2 + (SharedAccess.store .plain false a 8 (r.setWidth 128)).tick)) :
    m = d ∧ (∃ ok, (EW P w).step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1) ∧ g.2 < g'.2 := by
  rcases h with ⟨hv, -⟩ | ⟨-, rfl, ok, hs, ht⟩
  · rw [hd8] at hv; cases hv
  · exact ⟨rfl, ⟨ok, hs⟩, by simp only [SharedAccess.tick] at ht; omega⟩

/-- Transport a load step along an address equation. -/
theorem stepL {E : SharedEnv} {k : LoadKind} {xcl : Bool} {n : Nat} {a a' : BitVec 64} {g g' : E.State}
    {v : BitVec 128} (h : E.step (.load k xcl a n) g v g') (e : a = a') : E.step (.load k xcl a' n) g v g' := by
  subst e; exact h

/-- Transport a store step along address and value equations. -/
theorem stepS {E : SharedEnv} {k : StoreKind} {xcl : Bool} {n : Nat} {a a' : BitVec 64} {v v' : BitVec 128}
    {g g' : E.State} {b : Bool} (h : E.step (.store k xcl a n v) g b g') (e : a = a') (e' : v = v') :
    E.step (.store k xcl a' n v') g b g' := by
  subst e e'; exact h

/-- Transport an RMW step along address and operation equations. -/
theorem stepR {E : SharedEnv} {k : RmwKind} {n : Nat} {a a' : BitVec 64} {op op' : Val → Option Val}
    {g g' : E.State} {old : BitVec 128} (h : E.step (.rmw k a n op) g old g') (e : a = a') (e' : op = op') :
    E.step (.rmw k a' n op') g old g' := by
  subst e e'; exact h

/-- Transport an RMW permission along address and operation equations. -/
theorem okR {E : SharedEnv} {k : RmwKind} {n : Nat} {a a' : BitVec 64} {op op' : Val → Option Val}
    {g : E.State} (h : E.ok (.rmw k a n op) g) (e : a = a') (e' : op = op') : E.ok (.rmw k a' n op') g := by
  subst e e'; exact h

/-- A load of a counted run (`dmem` maps no 8-byte word) counts one. -/
theorem ldN {E : SharedEnv} {d : Std.ExtHashMap (BitVec 64) UInt8} {a x : BitVec 64}
    {g g' : (SharedEnv.counted E).State} (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g) ∨ (Mem.loadInt d a 8 = none ∧ ∃ v,
      (E.step (.load .plain false a 8) g.1 v g'.1 ∧ g'.2 = g.2 + 1) ∧ x = BitVec.setWidth 64 v)) :
    g'.2 = g.2 + 1 := by
  rcases h with ⟨v, hv, -⟩ | ⟨-, v, ⟨-, ht⟩, -⟩
  · rw [hd8] at hv; cases hv
  · exact ht

/-- A store of a counted run leaves `dmem` and counts one. -/
theorem stN {E : SharedEnv} {d m : Std.ExtHashMap (BitVec 64) UInt8} {a r : BitVec 64}
    {g g' : (SharedEnv.counted E).State} (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : ((Mem.loadInt d a 8).isSome = true ∧ m = Mem.storeInt d a 8 r.toInt ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ m = d ∧ ∃ ok, E.step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1 ∧
        g'.2 = g.2 + 1)) :
    m = d ∧ g'.2 = g.2 + 1 := by
  rcases h with ⟨hv, -⟩ | ⟨-, rfl, -, -, ht⟩
  · rw [hd8] at hv; cases hv
  · exact ⟨rfl, ht⟩

end Helpers

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labT2 (x : Label) : Int64 := (_root_.Executable.labels (layout treiber2ImageV)).label x

/-- A symbol's address in the image. -/
abbrev symT2 (x : Label) : BitVec 64 := (labT2 x).toBitVec

variable [Executable.ValidLayout (layout treiber2ImageV)]

local instance treiber2ImageV.env : CodeEnv := ⟨layout treiber2ImageV⟩

theorem treiber2CodeV_placedIn : Program.PlacedIn treiber2CodeV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiber2ImageV) treiber2ImageV_wf rfl (by decide))
    treiber2CodeV_sub

omit [Executable.ValidLayout (layout treiber2ImageV)] in
theorem treiber2CodeV_last : ∀ l blk, Program.blockAt treiber2CodeV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labT2 "done" :=
  Program.after_last_of (by decide)


/-! ## The worker -/

/-- The worker's table: `rbx` the node, `dmem` maps no 8-byte word. -/
abbrev workTableV (P : Params) (w : Nat) :
    Label → MachineData → (SharedEnv.counted (EWX P w)).State → Prop :=
  fun lb s σ => s.regs.get64 .rbx = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    ((lb = "worker" ∧ Pu P w σ.1) ∨ (lb = "push" ∧ Pu P w σ.1) ∨ (lb = "pop" ∧ Po P w σ.1) ∨
      (lb = "done" ∧ Dn P w (s.regs.get64 .r12) σ.1))

/-- **The verbatim x64 Treiber worker on `EnvGCAdjX`** (counted, partial):
from `Pu` at `worker`, every run that reaches `done` is in `Dn`. -/
theorem workerV_envGCAdj (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (ht : symT2 "top" = P.t) :
    ∀ s g, s.regs.get64 .rbx = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ Pu P w g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EWX P w)))
        (fun x => (x.1.2 = labT2 "done" ∧ Dn P w (x.1.1.regs.get64 .r12) x.2.1) ∨ False)
        ((s, labT2 "worker"), g) := by
  obtain ⟨t, n⟩ := P
  simp only at ht
  subst ht
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EWX ⟨symT2 "top", n⟩ w))
    (Q := fun s σ => Dn ⟨symT2 "top", n⟩ w (s.regs.get64 .r12) σ.1) (E := fun _ _ _ => False) (workTableV ⟨symT2 "top", n⟩ w) ?_ rfl
    (by decide) treiber2CodeV_placedIn treiber2CodeV_last s g (by simpa [workTableV] using hsg)
  cfg_cases_env [treiber2CodeV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx1, hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX,
    SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step, SharedEnv.within_ok_load,
    SharedEnv.within_ok_store, SharedEnv.within_ok_rmw] at *
  all_goals simp only [Reg64s.get64] at hx1
  all_goals try (simp [hx1, hd8]; done)
  -- `worker` falls through to `push`
  case vc1 => exact ⟨hx1, hd8, .inr (.inl ⟨trivial, hT⟩)⟩
  -- `push`
  case vc1 => exact ⟨trivial, mem_sAll8 _⟩
  case vc2 =>
    rename_i s σ0 v σ1 hnone hld _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    have h := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).1
    simpa [hx1, Params.nd] using ⟨h, mem_sAll8 (n w)⟩
  case vc3 =>
    rename_i s σ0 v σ1 dm σ2 hld hst _
    obtain ⟨rfl, -, -⟩ := stS hd8 hst
    exact hd8 _
  case vc4 =>
    rename_i s σ0 v σ1 dm σ2 hld hst _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stS hd8 hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hx1, Params.nd]) (by simp))
    have h := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).1
    exact ⟨okR h rfl (by simp [hx1, cmpxOp64]), mem_sAll8 _⟩
  case vc5 =>
    rename_i s σ0 v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz
  case vc6 =>
    rename_i s σ0 v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stS hd8 hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hx1, Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1 rfl (by simp [hx1, cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd heq hne
    · exact ⟨by simpa using hx1, hd8, .inr (.inr (.inl ⟨trivial, hPo.fence hf.1⟩))⟩
  case vc7 =>
    rename_i s σ0 v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    obtain ⟨v, hs, h1, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, h2⟩ := stS hd8 hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hx1, Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1 rfl (by simp [hx1, cmpxOp64]))
    simp at heq
    rcases hc with ⟨-, hPu⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hx1, hd8, .inr (.inl ⟨rfl,
        Pu.fence hPu.pu hf.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h3 := hcas.2; have h4 := hf.2
      simp only [SharedAccess.tick] at h3
      omega
    · exact absurd heq' heq
  case vc8 =>
    rename_i s σ0 v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hz) (Ne.symm heq)
  -- `pop`
  case vc1 => exact ⟨trivial, mem_sAll8 _⟩
  case vc2 =>
    rename_i s σ0 v σ1 af σ2 hz σ3 hld hf1 hf2 _
    obtain ⟨v, hs, h1, rfl⟩ := ldS hd8 hld
    have hPl := vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [Params.top] using hs)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hx1, hd8, .inr (.inr (.inl ⟨rfl,
      ((hPl.fence hf1.1).fence hf2.1).po⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have := hf1.2; have := hf2.2
    omega
  case vc3 => exact ⟨trivial, mem_sAll8 _⟩
  case vc5 =>
    rename_i s σ0 v σ1 af σ2 hz σ3 u σ4 hld hf1 hf2 hld2 _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [Params.top] using hs)).fence hf1.1).fence hf2.1
    obtain ⟨u, hs2, -, rfl⟩ := ldS hd8 hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have h := (vc_pop_cas hw _ hPr hz).1
    exact ⟨okR h rfl (by simp [cmpxOp64]), mem_sAll8 _⟩
  case vc6 =>
    rename_i s σ0 v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 hld hf1 hf2 hld2 hcas hf3 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz2
  case vc7 =>
    rename_i s σ0 v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 σ7 σ8 hld hf1 hf2 hld2 hcas hf3 hf4 hf5 _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [Params.top] using hs)).fence hf1.1).fence hf2.1
    obtain ⟨u, hs2, -, rfl⟩ := ldS hd8 hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hc := (vc_pop_cas hw _ hPr hz).2 old σ5.1 (stepR hcas.1 rfl (by simp [cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd heq hne
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hx1, hd8, .inr (.inr (.inr ⟨rfl, ?_⟩))⟩,
      .inl (by decide)⟩
    simp
    exact (((hDn.fence hf3.1).fence hf4.1).fence hf5.1).dn
  case vc8 =>
    rename_i s σ0 v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 hld hf1 hf2 hld2 hcas hf3 _
    obtain ⟨v, hs, h1, rfl⟩ := ldS hd8 hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [Params.top] using hs)).fence hf1.1).fence hf2.1
    obtain ⟨u, hs2, h2, rfl⟩ := ldS hd8 hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hc := (vc_pop_cas hw _ hPr hz).2 old σ5.1 (stepR hcas.1 rfl (by simp [cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPo⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hx1, hd8, .inr (.inr (.inl ⟨rfl,
        hPo.fence hf3.1⟩))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have := hf1.2; have := hf2.2; have := hf3.2; have h3 := hcas.2
      simp only [SharedAccess.tick] at h3
      omega
    · exact absurd heq' hne
  case vc9 =>
    rename_i s σ0 v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 σ7 σ8 hld hf1 hf2 hld2 hcas hf3 hf4 hf5 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hz2) (Ne.symm hne)
  -- `done`
  case vc1 => exact hT
  all_goals done

/-! ## Only release writes -/

open Kraken.Promising.X64.EnvG.TreiberX (EnvRT) in
/-- **The verbatim worker makes only release writes** (counted, partial). -/
theorem workerV_noNT :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labT2 "done" ∧ True) ∨ False) ((s, labT2 "worker"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
      ∀ a, Mem.loadInt s.dmem a 8 = none) ?_ rfl (by decide) treiber2CodeV_placedIn treiber2CodeV_last s g hs
  cfg_cases_env [treiber2CodeV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hd8, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step,
    SharedEnv.within_ok_load, SharedEnv.within_ok_store, SharedEnv.within_ok_rmw, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals first
    | (simp [hd8]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (exact Table.ofLabelsEnv_at ⟨by decide, hd8, .inl (by decide)⟩)
    | exact hd8
    | (rename_i hld hst hcas _
       obtain ⟨rfl, h2⟩ := stN hd8 hst
       have h1 := ldN hd8 hld; have h3 := hcas.2
       first
         | exact hd8 _
         | (refine Table.ofLabelsEnv_at ⟨by decide, hd8, .inr fun ⟨_, hg⟩ => ?_⟩; subst hg; omega))
    | (rename_i hld hst _; obtain ⟨rfl, -⟩ := stN hd8 hst; exact hd8 _)
    | (rename_i hld hld2 hcas _
       have h1 := ldN hd8 hld; have h2 := ldN hd8 hld2; have h3 := hcas.2
       refine Table.ofLabelsEnv_at ⟨by decide, hd8, .inr fun ⟨_, hg⟩ => ?_⟩; subst hg; omega)
    | (rename_i hld _
       have h1 := ldN hd8 hld
       refine Table.ofLabelsEnv_at ⟨by decide, hd8, .inr fun ⟨_, hg⟩ => ?_⟩; subst hg; omega)

end Kraken.Promising.X64.EnvG.Treiber2X
