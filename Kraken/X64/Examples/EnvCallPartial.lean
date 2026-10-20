import Kraken.X64.EnvCallsPartial
import Kraken.X64.Parser
import Kraken.SeparationMem

/-!
# A call to a `lock cmpxchg` retry loop, partial correctness

`incCall`'s caller does `call inc`. `inc` increments the shared counter at
`(%rdi)` by a `lock cmpxchgq` retry loop and returns. The environment is
`racy a` with a ghost access counter (`SharedEnv.counted`): another thread may
change the counter at any time, so every load and every compare-and-swap may
read any value. Under it the loop may retry forever, and `inc` has only a
partial specification.

- `inc_spec`: `inc`'s `FunSpecPartialEnv`, by `FunSpecPartialEnv.of_cfg`
  (the function rule with the `ret` exit) and one `vcgen` call on its one
  block. The back edge `jne inc` is admitted by the zero-step guard, because
  the ghost counter has moved. The `ret` reads the return address from the
  `dmem` slot that the caller's `call` wrote.
- `incCall_partialEnv`: the caller, through `inc_spec` by
  `PartialWpEnv.call` (the return-address slot is in `dmem`), and then its
  tail by `vcgen`. Every run that comes back has `rdx = rax + 1` (the value
  `inc` wrote is one more than the value it read), with `rsp` restored, or
  it runs forever.
- `incCall_partialEnv_uncounted`: the same in `racy a` itself
  (`PartialTripleEnv.uncount`).
-/

open Std.WP
open Kraken
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.X64.Examples.EnvCallPartial

/-- A counter at `a` that other threads may change at any time: an 8-byte
access at `a` is permitted, and a load or read-modify-write returns any
value. -/
def racy (a : BitVec 64) : SharedEnv where
  State := Unit
  ok acc _ := match acc with
    | .load _ _ addr n => addr = a ∧ n = 8
    | .store _ _ addr n _ => addr = a ∧ n = 8
    | .rmw _ addr n _ => addr = a ∧ n = 8
    | .fence _ => True
  step _ _ _ _ := True

instance (a : BitVec 64) : (racy a).Skips := ⟨fun _ _ => ⟨trivial, fun _ _ => rfl⟩⟩

@[simp] theorem racy_ok_load (a : BitVec 64) (k : LoadKind) (x : Bool) (addr : BitVec 64) (n : Nat)
    (g : (racy a).State) : (racy a).ok (.load k x addr n) g ↔ addr = a ∧ n = 8 := Iff.rfl

@[simp] theorem racy_ok_rmw (a : BitVec 64) (k : RmwKind) (addr : BitVec 64) (n : Nat) (op)
    (g : (racy a).State) : (racy a).ok (.rmw k addr n op) g ↔ addr = a ∧ n = 8 := Iff.rfl

@[simp] theorem racy_step (a : BitVec 64) (acc : SharedAccess) (g : (racy a).State) (r : acc.Ret)
    (g' : (racy a).State) :
    (racy a).step acc g r g' ↔ True := Iff.rfl

/-- A store to bytes that are all mapped maps no new byte (as in
`X64/Examples/EnvProcCall.lean`). -/
private theorem subDom_storeInt_of_mapped {m : Mem 64} {b : BitVec 64} {n : Nat} {v : Int}
    (hb : (m.loadInt b n).isSome = true) : Mem.SubDom (m.storeInt b n v) m := by
  intro k hk
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.union_eq, Std.ExtHashMap.mem_union_iff] at hk
  rcases hk with hk | hk
  · exact hk
  · obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hk
    rw [Int.toBytes_length] at hi
    simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff,
      List.forall_mem_map] at hb
    have := hb i (List.mem_range.mpr hi)
    rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.isSome_getElem?_iff_mem] at this
    exact this

/-- A load that fails before a store to mapped bytes fails after it. -/
private theorem loadInt_storeInt_of_none {m : Mem 64} {a b : BitVec 64} {n k : Nat} {v : Int}
    (hb : (m.loadInt b n).isSome = true) (ha : m.loadInt a k = none) :
    (m.storeInt b n v).loadInt a k = none := by
  cases h : (m.storeInt b n v).loadInt a k with
  | none => rfl
  | some x =>
    have := Mem.SubDom.loadInt_isSome (subDom_storeInt_of_mapped hb) (by rw [h]; rfl)
    rw [ha] at this
    cases this

section

open Kraken.X64.Parser

variable [layout : _root_.Layout]

/-- The caller, then the function it calls, then the end. -/
def incCall : Program := parse("
caller:
  call inc
  movq %rcx, %rdx
  jmp done
inc:
  movq (%rdi), %rax
  leaq 1(%rax), %rcx
  lock cmpxchgq %rcx, (%rdi)
  jne inc
  ret
done:
  nop
")

/-- The caller's two instructions. -/
abbrev incCall.caller : Program := parse("
  call inc
  movq %rcx, %rdx
")

/-- The function, as a fragment of `incCall`. -/
abbrev incCall.inc : Program := parse("
inc:
  movq (%rdi), %rax
  leaq 1(%rax), %rcx
  lock cmpxchgq %rcx, (%rdi)
  jne inc
  ret
")

local instance incCall.env : CodeEnv := ⟨layout incCall⟩

variable [Executable.ValidLayout (layout incCall)]

/-- Where `incCall`'s blocks sit. -/
private theorem incCall_placed : Program.Placed incCall "caller" :=
  Program.placed_of_layout (by decide) rfl (by decide)

/-- `inc`'s entry: the counter at `a = rdi` is shared (not in `dmem`), and
the slot at `rsp` holds the return address `ra`. -/
abbrev IncPre (a : BitVec 64) (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (racy a)).State) :
    Prop :=
  t.regs.get64 .rdi = a ∧ Mem.loadInt t.dmem a 8 = none ∧
    ∃ w, Mem.loadInt t.dmem (t.regs.get64 .rsp) 8 = some w ∧ Int64.ofBitVec (BitVec.ofInt 64 w) = ra

/-- `inc`'s exit: the value written (`rcx`) is one more than the value read
(`rax`); `rdi`, `dmem` kept, `rsp` back above the slot. -/
abbrev IncPost (_a : BitVec 64) (_ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (racy _a)).State)
    (s : MachineData) (_ : (SharedEnv.counted (racy _a)).State) : Prop :=
  s.regs.get64 .rcx = s.regs.get64 .rax + 1 ∧ s.regs.get64 .rdi = t.regs.get64 .rdi ∧ s.dmem = t.dmem ∧
    s.regs.get64 .rsp = t.regs.get64 .rsp + 8

/-- `inc`'s loop table, for the entry `t` and return address `ra`. -/
abbrev incTable (a : BitVec 64) (ra : Int64) (t : MachineData) (g : (SharedEnv.counted (racy a)).State) :
    Label → MachineData → (SharedEnv.counted (racy a)).State → Prop :=
  fun lb s _ => lb = "inc" ∧ s.regs.get64 .rdi = t.regs.get64 .rdi ∧ s.dmem = t.dmem ∧
    s.regs.get64 .rsp = t.regs.get64 .rsp ∧ IncPre a ra t g

/-- **`inc`'s partial specification**: every run from its entry returns to
`ra` with `IncPost`, or retries forever. -/
theorem inc_spec (a : BitVec 64) :
    FunSpecPartialEnv (SharedEnv.counted (racy a)) ((_root_.Executable.labels cenv).label "inc")
      (IncPre a) (IncPost a) := by
  refine FunSpecPartialEnv.of_cfg (p := incCall.inc) (incTable a) rfl (by decide)
    (Program.PlacedIn.of_placedE incCall_placed (by decide)) (fun ra t g h => ⟨rfl, rfl, rfl, rfl, h⟩) ?_
  intro ra t g hpre
  cfg_cases_env [incCall.inc]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨⟨-, hrdi, hdm, hrsp, hrdi0, hnone, w, hw, hra⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals subst hrdi0
  all_goals simp only [SharedEnv.counted_ok, SharedEnv.counted_step, racy_ok_load, racy_ok_rmw,
    racy_step, true_and] at *
  all_goals try simp_all
  case vc7 =>
    refine Table.ofLabelsEnv_at ⟨rfl, ⟨rfl, ?_, rfl, ?_⟩, .inr fun _ hg => ?_⟩
    · simp_all
    · simp_all
    · subst hg; omega
  case vc9 =>
    exfalso
    apply ‹¬BitVec.setWidth 64 _ = _›
    bv_omega

/-- **The caller, through `inc`'s partial spec.** From `rdi = a` (the shared
counter, not in `dmem`) and a mapped slot below `rsp = r`: every run that
falls through has `rdx = rax + 1` and `rsp = r` again, or runs forever (in
`inc`'s loop). -/
theorem incCall_partialEnv (a r : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (racy a))
      (fun s _ => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none ∧
        (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true ∧ s.regs.get64 .rsp = r)
      incCall.caller
      (fun s _ => s.regs.get64 .rdx = s.regs.get64 .rax + 1 ∧ s.regs.get64 .rsp = r)
      (fun _ _ _ => False) := by
  have h_rt : ∀ (m : DataMem) (a : BitVec 64) (x : Int),
      Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
    fun m a x => Mem.loadInt_storeInt m a 8 x (by decide)
  refine PartialTripleEnv.of_partialWpEnv fun s g ⟨hrdi, hnone, hslot, hrsp⟩ => ?_
  refine PartialWpEnv.call _ _ "inc" (inc_spec a) hslot fun ra => ⟨?_, fun s' g' hpost => ?_⟩
  · refine ⟨by simpa using hrdi, loadInt_storeInt_of_none hslot hnone, _, by simpa using h_rt _ _ _, ?_⟩
    simpa using Int64.ofBitVec_ofBytes_toBytes ra
  · obtain ⟨hrcx, -, -, hrsp'⟩ := hpost
    refine PartialWpEnv.of_tripleEnv (P := fun s _ => s = s') ?_ rfl
    apply TripleEnv.of_triple
    vcgen
    simp_all [BitVec.sub_add_cancel]

/-- The same, in `racy a` itself (no ghost counter). -/
theorem incCall_partialEnv_uncounted (a r : BitVec 64) :
    PartialTripleEnv (racy a)
      (fun s _ => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none ∧
        (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true ∧ s.regs.get64 .rsp = r)
      incCall.caller
      (fun s _ => s.regs.get64 .rdx = s.regs.get64 .rax + 1 ∧ s.regs.get64 .rsp = r)
      (fun _ _ _ => False) := fun s g hp pc hpl =>
  (PartialTripleEnv.uncount (incCall_partialEnv a r) s g ⟨0, hp⟩ pc hpl).mono fun _ h =>
    h.imp (fun ⟨ha, _, hq⟩ => ⟨ha, hq⟩) (fun ⟨_, h⟩ => h)

end

end Kraken.X64.Examples.EnvCallPartial
