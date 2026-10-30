/-
**The run invariant of the kernel model's machine** (AArch64, `n` slots):
the facts every configuration reachable from the load has, whatever the
threads do, so that a relation need not carry them (`WakeAssembly`'s
`post_wit` and `post_progress` take `RunInv` beside `Post`).

- `RunInv Λ E t`: the private-memory invariant `DmemPriv.PrivInv` (the
  domain invariant `Kernel.OwnDom` from the entry's initial stack, with the
  layout's pool) and the mapped regions as loaded (`KState.init`'s `rw` and
  `ro`).
- `map_step`, `map_run`: no step changes the mapped regions.
- `runInv_loadProg`, `runInv_load`: the invariant at the load
  (`loadProg`; `(target (kernel n) E).load` of a program of `wideIn`
  instructions).
- `runInv_step`, `runInv_run`: every step and run keeps it.
- `RunInv.ownDom`, `RunInv.pool`: the projections `WakeStack.stackOk` takes.
- `RunInv.mapped_rw`, `RunInv.mapped_ro`: a location inside one loaded
  region is mapped (any access for a read-write region, a read for a
  read-only one).
-/
import Spike.Lib.A64DmemPriv

namespace Spike.Lib.WakeRunInv

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Scc.Cert.WideA64 Spike.Lib.DmemPriv

/-! ## The mapped regions -/

section Map

variable {I : ISA} {K : Abi I}

/-- The mapped regions of `y` are those of `x`. -/
def MapEq (x y : KState) : Prop := y.rw = x.rw ∧ y.ro = x.ro

theorem map_take {tid : Nat} {c c' : Config I × KState} (h : takeStep K tid c = some c') : MapEq c.2 c'.2 := by
  simp only [takeStep] at h
  split at h
  · cases h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem map_release {tid : Nat} {c c' : Config I × KState} (h : releaseStep K tid c = some c') :
    MapEq c.2 c'.2 := by
  simp only [releaseStep] at h
  split at h
  · cases h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem map_spawn {tid j : Nat} {ctid : BitVec 64} {c c' : Config I × KState}
    (h : spawnStep K tid c j ctid = some c') : MapEq c.2 c'.2 := by
  unfold spawnStep at h
  (repeat' split at h) <;> (try cases h) <;> exact ⟨rfl, rfl⟩

theorem map_sys {A : Arch} {tid : Nat} {p : Pick} {es : List Ev} {c c' : Config I × KState}
    (h : sysStep K A tid c p = some (es, c')) : MapEq c.2 c'.2 := by
  unfold sysStep at h
  split at h
  · cases h
  rename_i t _
  split at h
  · cases h
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> cases p <;> simp only [hcall, back] at h <;> (repeat' split at h) <;> (try cases h) <;>
    (try exact ⟨rfl, rfl⟩)
  all_goals
    obtain ⟨⟨b, t'⟩, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨rfl, rfl⟩

variable {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

/-- **No step of the kernel model's machine changes the mapped regions.** -/
theorem map_step {tid : Nat} {es : List Ev} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Step μ tid c es c') : MapEq c.2 c'.2 := by
  cases h with
  | instr _ _ _ _ => exact ⟨rfl, rfl⟩
  | spawn _ hs => obtain ⟨j, r, hs, -⟩ := hs; exact map_spawn hs
  | sys _ hs => obtain ⟨p, hs, -⟩ := hs; exact map_sys hs
  | xfer k _ _ hx =>
    cases k
    · exact map_take hx
    · exact map_release hx

/-- **No run of the kernel model's machine changes the mapped regions.** -/
theorem map_run {tr : List Ev} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Run μ c tr c') : MapEq c.2 c'.2 := by
  unfold ExtMachine.Run at h
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ ih =>
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨h1, h2⟩ := map_step hs
    exact ⟨ih.1.trans h1, ih.2.trans h2⟩

end Map

/-! ## The invariant -/

variable {n : Nat} {Λ : Scc.Sem.Layout} {E : Entry} {μ : Marks}

/-- **The run invariant**: the private-memory invariant from the entry `E`
with the layout's pool, and the mapped regions as loaded. -/
def RunInv (Λ : Scc.Sem.Layout) (E : Entry) (t : Config isaLSE2 × KState) : Prop :=
  PrivInv abi WideSt Λ E t ∧ t.2.rw = (KState.init 0 E Λ).rw ∧ t.2.ro = (KState.init 0 E Λ).ro

/-- **At `loadProg`**, for a `WideSt` entry thread and an entry stack clear
of the layout. -/
theorem runInv_loadProg {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hw : WideSt (threadAt E Λ.code.lo prog syms)) (hE : E.clear Λ = true) :
    RunInv Λ E (loadProg (kernel n) E Λ prog syms mem) :=
  ⟨Spike.Lib.A64DmemPriv.privInv_load hw hE, rfl, rfl⟩

/-- **At the target's load**, for a program of `wideIn` instructions. -/
theorem runInv_load {asm : String} {t : (machine (kernel n)).Cfg}
    (hw : ∀ prog, (textProgram asm).toOption = some prog → wideIn prog = true)
    (h : (target (kernel n) E).load asm Λ = some t) : RunInv Λ E t := by
  simp only [target] at h
  rcases hp : (textProgram asm).toOption with _ | prog
  · simp [hp] at h
  rcases hs : dataSections asm with _ | secs
  · simp [hp, hs] at h
  simp only [hp, hs, Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    exact runInv_loadProg (wideSt_threadAt (hw prog hp) _ _ _) hc.2
  · cases h

/-- **Every step keeps the invariant.** -/
theorem runInv_step {tid : Nat} {es : List Ev} {c c' : (machine (kernel n)).Cfg} (hc : RunInv Λ E c)
    (h : (machine (kernel n)).Step μ tid c es c') : RunInv Λ E c' :=
  ⟨Spike.Lib.A64DmemPriv.privInv_step hc.1 h, (map_step h).1.trans hc.2.1, (map_step h).2.trans hc.2.2⟩

/-- **Every run keeps the invariant.** -/
theorem runInv_run {tr : List Ev} {c c' : (machine (kernel n)).Cfg} (hc : RunInv Λ E c)
    (h : (machine (kernel n)).Run μ c tr c') : RunInv Λ E c' :=
  ⟨Spike.Lib.A64DmemPriv.privInv_run hc.1 h, (map_run h).1.trans hc.2.1, (map_run h).2.trans hc.2.2⟩

namespace RunInv

variable {t : Config isaLSE2 × KState}

/-- The domain invariant. -/
theorem ownDom (h : RunInv Λ E t) : OwnDom abi (initDom E) WideSt t := h.1.own

/-- The pool is the layout's. -/
theorem pool (h : RunInv Λ E t) : t.2.pool = Λ.stackPool := h.1.pool

/-- **A location inside one read-write region** (`.data`, the heap arena,
the stack pool, the pinned region, the initial stack) is mapped, for any
access. -/
theorem mapped_rw (h : RunInv Λ E t) (wr : Bool) {l : Loc} {r : Range}
    (hr : r ∈ [Λ.data, Λ.heap, Λ.stackPool, Λ.pinned, E.stack])
    (hl : ∀ i < l.bytes, r.contains (l.addr.toNat + i)) : mapped t.2 wr l = true := by
  unfold mapped
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.any_eq_true]
  refine ⟨r, ?_, decide_eq_true (hl i hi)⟩
  simp only [mappedRegions, h.2.1, KState.init, List.mem_append]
  exact .inl (.inl hr)

/-- **A location inside one read-only region** (the code, `.rodata`) is
mapped for a read. -/
theorem mapped_ro (h : RunInv Λ E t) {l : Loc} {r : Range} (hr : r ∈ [Λ.code, Λ.rodata])
    (hl : ∀ i < l.bytes, r.contains (l.addr.toNat + i)) : mapped t.2 false l = true := by
  unfold mapped
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.any_eq_true]
  refine ⟨r, ?_, decide_eq_true (hl i hi)⟩
  simp only [mappedRegions, h.2.2, KState.init, List.mem_append]
  exact .inr hr

end RunInv

/-- info: 'Spike.Lib.WakeRunInv.runInv_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRunInv.runInv_load

/-- info: 'Spike.Lib.WakeRunInv.runInv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRunInv.runInv_step

/-- info: 'Spike.Lib.WakeRunInv.runInv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRunInv.runInv_run

/-- info: 'Spike.Lib.WakeRunInv.RunInv.mapped_rw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRunInv.RunInv.mapped_rw

/-- info: 'Spike.Lib.WakeRunInv.RunInv.mapped_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRunInv.RunInv.mapped_ro

end Spike.Lib.WakeRunInv
