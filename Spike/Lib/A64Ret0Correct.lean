/-
**`ret0.w` on AArch64: the assembly skeleton of `Correct`** (`correctA64`,
`Spike/Lib/A64Correct.lean`) at the program's source `ret0Src`, its listing
`ret0Asm` and layout `ret0Λ`.

What this file proves of `correctA64`'s (`correctA64P`'s) hypotheses for `ret0`:

- the parse boundary (`hpa`, `hd`), the image (`himg`), the wide check
  (`hw`), the layout (`hwf`) and the load (`hload`): the decided facts of
  `Spike/Lib/A64Ret0Code.lean`, the load by `load_of_loadOk`;
- the source side (`Spike/Lib/Ret0Src.lean`): `ret0Src`, `ret0P` (`hP`,
  `hinit` by definition), and `hsafe` (`SrcSafe`) for every fragment: no
  reachable source thread has a load, store or exchange (`reach_noMem`);
- no static label (`hss`), every word readable (`hrd`), the value invariant
  `ret0G` (`hG0`, `hGpl`), the loaded thread's owned words (`hown0`);
- the abort phase is empty (`Ab := False`, `hab0`).

`ret0_correct_parsed` states `Correct` from `correctA64P` over the target on
parsed texts (`TPar`) at the parsed values, with only the open items left as
premises: the consumer's obligations of the fragment (the
bundle `ret0_instR` of `Spike/Lib/A64Ret0I.lean` concludes: a fragment
holding the entry node, with `Nodes`, `TakePath` and an empty `AbortPath`),
the phase at load (`htk0`), and the two promise hypotheses (`hps`,
`hsvc`). The phase `Tk` is a parameter (the redesign of the take
site moves it off the pc). It has no parse premise.

**The trust boundary.** The only link from the listing `ret0Asm` to the
parsed values is the single compiled check `#guard parsesTo ret0Asm ret0Prog ret0Secs`
(`Spike/Lib/A64Ret0Code.lean`, line 1534), evaluated by the compiler and
not checked by the kernel. `ret0_correct_of` carries `ret0_correct_parsed`
to `ret0Asm` given that equation as the premise `hpa` (`correct_of_parsed`,
`Scc/Sem/LoadA64.lean`).

**The premise-free statement.** `ret0_correct` (section `Inst`) proves
`Correct` with no premise: the promise premise `PromShared` holds
(`promShared_a64`, `Spike/Lib/A64PromShared.lean`, derives it from the
node obligations, `TakePath` and the layout, and `correctA64P'`,
`Spike/Lib/A64CorrectP.lean`, discharges it), and `WriteNoProm` holds
from the fragment's `NoWrite` (`correctA64P''`, `Spike/Lib/A64CorrectNW.lean`).
The statements below that still take `hps`/`hsvc` are the earlier staging
forms, kept for their tests; their premises are discharged there.

**The budget.** `correctA64` holds at every budget `B`, and so do
`ret0_correct_parsed` and `ret0_correct_of`: `ret0` reaches no abort site (the abort phase is empty),
so the budget is never consulted. The certificate's natural budget is
`ret0B` (no heap word, one thread, one frame).
-/
import Spike.Lib.A64Correct
import Spike.Lib.A64CorrectNW
import Spike.Lib.A64Ret0I
import Spike.Lib.Ret0Src
import Scc.Sem.FixInv

namespace Spike.Lib.A64.Flow.Ret0.Correct

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64Consumer
open Spike.Lib.Consumer1
open SccCode (ret0Λ ret0Prog ret0Asm ret0Secs)
open Spike.Lib.Ret0Src

/-! ## No memory operation in the source (`hsafe`) -/

section NoMem

open A9NoSpawn TermRun Spike.Lib.Ret0Src

/-- **`hsafe` for `ret0`**, at every fragment: no reachable source thread is
at a load, a store or an exchange. -/
theorem ret0_safe (arch : WeakMem.Arch) (I : Inv) : SrcSafe (ret0P arch) ret0Src I := by
  have hR := fun {tr s} (h : (SrcSem.source (ret0P arch) ret0Src).Reach tr s) =>
    reach_noMem ret0Src_noMem (ret0P_hooks arch) (mainInit_noMem 1) h
  constructor
  · intro tr s th hr h0 lbl lsize st hd _ x a e ty w sa ht
    have hn := (hR hr 0 th h0).1
    rcases ht with ht | ⟨b, ht⟩ <;> rw [ht] at hn <;> exact (hn.1 trivial).elim
  · intro tr s th hr h0 lbl lsize st hd _ x sa u v e hx
    have hn := (hR hr 0 th h0).1
    obtain ⟨-, ⟨a, t, pw, μ, ht, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, k, ht, -⟩⟩ := hx <;>
      simp only at ht <;> rw [ht] at hn <;> exact (hn.1 trivial).elim

end NoMem

/-! ## The load and the layout -/

open Scc.Cert.Link Scc.Cert.Link.A64 Scc.Cert.WideA64

/-- The code labels the image check resolves `.quad` labels with. -/
abbrev ret0Code : String → Option Nat := codeOf ret0Λ.code.lo ret0Prog

/-- The loaded thread. -/
abbrev ret0S0 : State := threadAt Entry.linux ret0Λ.code.lo ret0Prog (loadSyms ret0Λ ret0Secs.rodata)

/-- The loaded memory's initial words. -/
abbrev ret0Init : List (Loc × Val) :=
  imageMem ret0Λ ++ wordsMem (rodataWords ret0Λ ret0Secs.rodata (quadCode ret0Λ ret0Prog))

/-- The loaded memory. -/
abbrev ret0Mem0 : Memory := { init := ret0Init, msgs := #[] }

/-- The entry stack is clear of the layout. -/
theorem ret0_clear : Entry.linux.clear ret0Λ = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The load of the parsed values** `(ret0Prog, ret0Secs)` on the target on
parsed texts (`TPar`): no parse equation. -/
theorem ret0_loadP : TPar.load (ret0Prog, ret0Secs) ret0Λ = some (loadProg (kernel 1) Entry.linux ret0Λ ret0Prog
      (loadSyms ret0Λ ret0Secs.rodata) ret0Init) :=
  loadParsed_of_loadOk (H := kernel 1) SccCode.ret0Λ_load ret0_clear

/-- **The load** of `ret0Asm`, from the parse (the trust boundary). -/
theorem ret0_load (hp : parsesTo ret0Asm ret0Prog ret0Secs = true) :
    T.load ret0Asm ret0Λ = some (loadProg (kernel 1) Entry.linux ret0Λ ret0Prog
      (loadSyms ret0Λ ret0Secs.rodata) ret0Init) :=
  load_of_loadOk hp SccCode.ret0Λ_load ret0_clear

/-- The loaded configuration's memory. -/
theorem ret0_mem {t0 : TPar.M.Cfg} (h : TPar.load (ret0Prog, ret0Secs) ret0Λ = some t0) : t0.1.mem = ret0Mem0 := by
  rw [ret0_loadP] at h
  cases h
  rfl

/-- `ret0` places no static label. -/
theorem ret0_static (l : WeakMem.AllocLabel) : ret0Λ.static l = none := rfl

theorem ret0_ss (lsize : Lsize) (name : WeakMem.AllocLabel → String) :
    StaticSyms ret0Λ ret0Secs ret0Code lsize name :=
  StaticSyms.of_none ret0_static

/-! ## The value invariant (`hG0`, `hGpl`) -/

/-- The TCB's limit word, the only word `G` fixes. -/
abbrev limW : Nat := 134217744

/-- The limit `scc_rt_thread_init` stores: the new stack's base plus the
guard (`stacksA + 4096`). -/
abbrev limV : Val := (268439552 : BitVec 128)

/-- **`ret0`'s value invariant**: the limit word holds its initial value or
the limit; any value elsewhere. -/
def ret0G : Loc → Val → Prop := FixG [(limW, limV)] ret0Mem0

theorem ret0_G0 : ∀ t0, TPar.load (ret0Prog, ret0Secs) ret0Λ = some t0 → MemInv ret0G t0.1.mem := by
  intro t0 h
  rw [ret0_mem h]
  exact memInv_fixG_load rfl rfl

theorem ret0_Gpl : ∀ a v, ret0Λ.heap.contains a ∨ ret0Λ.data.contains a → ret0G (wordLoc a) v := by
  intro a v ha a' w hm hl
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  have hb := congrArg (fun l : Loc => l.addr.toNat) hl
  simp only [wordLoc, BitVec.toNat_ofNat, limW] at hb
  have h1 : ret0Λ.heap = ⟨16777216, 67108864⟩ := rfl
  have h2 : ret0Λ.data = ⟨6291456, 524592⟩ := rfl
  rw [h1, h2] at ha
  simp only [Range.contains] at ha
  omega

/-! ## The owned words at load (`hown0`) -/

open Spike.Lib.A64.Flow.Ret0.Inst (own)

theorem ret0_own0 : ∀ t0, TPar.load (ret0Prog, ret0Secs) ret0Λ = some t0 → OwnInit (own ret0S0) t0.1.mem := by
  intro t0 h
  rw [ret0_mem h]
  intro L v hm
  exact (List.all_eq_true.mp (show (own ret0S0).all
    (fun p => p.1.bytes == 8 && ret0Mem0.initVal p.1 == p.2) = true by decide +kernel) _ hm) |> fun h => by
      simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h

/-! ## The entry node (`hst`) -/

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)
open Spike.Lib.A64.Flow.Ret0.Inst (labT ret0_labT)

/-- The entry stack's top, the loaded thread's `sp`. -/
abbrev sp0 : Nat := Entry.linux.sp

/-- **The entry region**: the whole entry stack, below `sp`; `entryR` of
`Spike/Lib/A64Ret0I.lean` (the canonical definition). -/
abbrev R0 : Region := Spike.Lib.A64.Flow.Ret0.Inst.entryR

/-- **The entry node**: `_start`, `sp` at the region's base, the source
control `c0` (`main`'s start). `entryN labT c0` of `Spike/Lib/A64Ret0.lean`. -/
def entry0 : ND := ⟨labT "_start", ⟨0, []⟩, fun _ c => c = c0⟩

/-- A byte of the entry stack's memory. -/
theorem stackMem_get (p : BitVec 64) :
    Entry.linux.stackMem.get? p =
      if (p - BitVec.ofNat 64 Entry.linux.stack.lo).toNat < 65536 then some 0 else none := by
  rw [Entry.stackMem, Kraken.Promising.Mem.get?_storeBytes]
  have hs : Entry.linux.stack.size = 65536 := rfl
  rw [Std.ExtHashMap.get?_eq_getElem?, get?_At _ _ _ (by rw [List.length_replicate, hs]; decide),
    List.getElem?_replicate, hs]
  split <;> simp

/-- A word of the entry stack below `sp` reads. -/
theorem stack_word {k : Int} (hk : R0.Off k) : (Mem.loadInt Entry.linux.stackMem (R0.addr k) 8).isSome := by
  obtain ⟨-, hlo, hhi⟩ := hk
  simp only [R0, Spike.Lib.A64.Flow.Ret0.Inst.entryR] at hlo hhi
  unfold Mem.loadInt
  rw [Option.isSome_map]
  unfold Mem.loadBytes
  rw [List.allSome_isSome_iff]
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have hi8 := List.mem_range.mp hi
  rw [stackMem_get, ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  · rfl
  · simp only [R0, Spike.Lib.A64.Flow.Ret0.Inst.entryR, Region.addr, Entry.linux, Entry.sp, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt,
      BitVec.toNat_ofNat]
    omega

/-- The loaded thread's counters are not in its private memory
(`ret0F_stackMem`: the loaded memory is the entry stack). -/
theorem ret0F_s0 : ret0F ret0S0.st.1 := Spike.Lib.A64.Flow.Ret0.Inst.ret0F_stackMem rfl

set_option maxRecDepth 100000 in
/-- **The loaded thread is at the entry node**, with the source at `main`'s
start (`hst`, given a fragment holding the entry node). -/
theorem ret0_entry : At ret0Exe ret0End R0 ret0F entry0 ret0S0 c0 := by
  refine ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt _ _ _ _ (by decide +kernel), rfl, ?_, ⟨ret0S0.st.1.regs, ret0S0.st.1.status, fun k =>
    BitVec.ofInt 64 ((Mem.loadInt ret0S0.st.1.dmem (R0.addr k) 8).getD 0)⟩, ⟨rfl, rfl, ?_, ?_⟩, ret0F_s0, rfl⟩
  · exact (by decide +kernel : Int64.ofNat 4194304 = labT "_start")
  · intro r k hr
    rcases r with x | _
    · simp [entry0, SO.get, lk] at hr
    · simp only [SO.get, Option.some.injEq] at hr
      subst hr
      decide +kernel
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (stack_word hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt Entry.linux.stackMem _ 8).getD 0)
    rw [hj]; rfl

/-! ## `Correct` for `ret0` -/

open Spike.Lib.A64.Flow.Ret0.Inst (μ0)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)
open Spike.Lib.A64.Flow (At)

/-- The certificate's natural budget for `ret0`: no heap word, one thread,
one frame. `ret0_correct_of` holds at every budget. -/
def ret0B : Budget := ⟨0, 1, 1⟩

/-- **The marks of the parsed values** are `μ0` (no parse equation). -/
theorem ret0_marksP : TPar.marks (ret0Prog, ret0Secs) ret0Λ = μ0 := by
  unfold Scc.Sem.Target.marks
  congr 1
  · funext k; cases k <;> decide +kernel
  · funext k; cases k <;> decide +kernel

/-- **`ret0` is correct on the parsed values**: `Correct` over the canonical
AArch64 target on parsed texts (`TPar`, `parsedTarget`) at
`(ret0Prog, ret0Secs)`, with no parse equation, at the source parameters
`ret0P arch`, every budget `B`, the value invariant `ret0G`, every word
readable, and the owned words `own`, given what is open:

- the consumer's obligations of a fragment `inv` holding the entry node
  (`hE`): `hN`, `hT`, `hA` (what `ret0_instR` of `Spike/Lib/A64Ret0I.lean`
  concludes, at `μ0`, the empty abort phase);
- the phase `Tk` (a parameter) not at load (`htk0`);
- the promise hypotheses `hps`, `hsvc` (the certification redesign).

Every other hypothesis of `correctA64P` is proved above.

**The trust boundary.** This statement is about the parsed values, not the
listing `ret0Asm`. The link from `ret0Asm` to `(ret0Prog, ret0Secs)` is the
single compiled check `#guard parsesTo ret0Asm ret0Prog ret0Secs`
(`Spike/Lib/A64Ret0Code.lean`, line 1534), evaluated by the compiler, not
checked by the kernel; `ret0_correct_of` carries this statement to `ret0Asm`
given that equation (`correct_of_parsed`).

The promise premises `hps`, `hsvc` hold for `ret0_instR`'s fragment:
`ret0_correct` discharges them (`correctA64P''`). -/
theorem ret0_correct_parsed {B : Budget} {arch : WeakMem.Arch} {ls0 : Lsize} {inv : Frag isaLSE2} {rS : Range}
    {Tk : State → Prop}
    (hE : ∀ s c, At ret0Exe ret0End R0 ret0F entry0 s c → inv s c)
    (hN : Nodes ret0Λ ret0Src μ0 (fun _ => True) ret0G own (IOf ret0Λ.static ls0 inv))
    (hT : TakePath ret0Λ ret0Src μ0 (IOf ret0Λ.static ls0 inv) rS Tk)
    (hA : AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False))
    (htk0 : ¬ Tk ret0S0)
    (hps : PromShared ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS Tk μ0)
    (hsvc : WriteNoProm ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS Tk μ0) :
    Correct TPar (SrcSem.source (ret0P arch) ret0Src) ret0Λ B (ret0Prog, ret0Secs) := by
  rw [← ret0_marksP] at hN hT hA hps hsvc
  exact correctA64P (lsize := ls0) (name := fun _ => "") SccCode.ret0Λ_image (ret0_ss ls0 _)
    SccCode.ret0_wide ⟨rfl, rfl, hE _ _ ret0_entry⟩ ⟨_, ret0_loadP⟩ (.none (ret0P_hooks arch)) (ret0P_init arch) hN
    (ret0_safe arch _) hT htk0 ret0_own0 hps hsvc (fun _ => trivial) SccCode.ret0Λ_wf ret0_G0
    ret0_Gpl hA (fun h => h)

/-- **`ret0` is correct** on the canonical AArch64 target at the listing
`ret0Asm`: `ret0_correct_parsed` carried to the text by the parse equation
`hpa` (`correct_of_parsed`). `hpa` is the compiled `#guard` of
`Spike/Lib/A64Ret0Code.lean` (line 1534), the trust boundary.

The promise premises are discharged in `ret0_correct_asm`. -/
theorem ret0_correct_of {B : Budget} {arch : WeakMem.Arch} {ls0 : Lsize} {inv : Frag isaLSE2} {rS : Range}
    {Tk : State → Prop} (hpa : parsesTo ret0Asm ret0Prog ret0Secs = true)
    (hE : ∀ s c, At ret0Exe ret0End R0 ret0F entry0 s c → inv s c)
    (hN : Nodes ret0Λ ret0Src μ0 (fun _ => True) ret0G own (IOf ret0Λ.static ls0 inv))
    (hT : TakePath ret0Λ ret0Src μ0 (IOf ret0Λ.static ls0 inv) rS Tk)
    (hA : AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False))
    (htk0 : ¬ Tk ret0S0)
    (hps : PromShared ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS Tk μ0)
    (hsvc : WriteNoProm ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS Tk μ0) :
    Correct T (SrcSem.source (ret0P arch) ret0Src) ret0Λ B ret0Asm :=
  let ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  correct_of_parsed _ _ h1 h2 (ret0_correct_parsed hE hN hT hA htk0 hps hsvc)

/-! ## `Correct` from the instantiated consumer (`ret0_instR`) -/

section Inst

open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA pnA lockA freeNA nextA StOk TcbOk TakeOk LimOk OwnAt)
open Spike.Lib.A64.Flow.Ret0.Inst (ret0_instR rS0 mainBody Tk own_at)
open Spike.Lib.A64.Flow.Ret0.Mem (labOf msR tcb0)

/-- `ret0Src`'s `main`. -/
theorem ret0_main : ∃ d, ret0Src.find? (·.name == "main") = some d ∧ d.body = mainBody := ⟨_, rfl, rfl⟩

/-- The memory side `ret0_correct_parsed` instantiates the consumer at. -/
abbrev ret0MS (ls0 : Lsize) : MemSide isaLSE2 := msOf ret0Λ μ0 (fun _ => True) ret0G own ret0Λ.static ls0

/-- `ret0G` allows a value at a word off the limit word, or the limit. -/
theorem ret0G_of {a : BitVec 64} {v : Val} (h : a ≠ BitVec.ofNat 64 limW ∨ v = limV) : ret0G ⟨a, 8⟩ v := by
  intro a' w hm hl
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  rcases h with h | h
  · exact absurd (congrArg Loc.addr hl) h
  · exact .inl h

set_option maxRecDepth 100000 in
/-- The limit word's initial value. -/
theorem ret0_limInit : ret0Mem0.initVal ⟨BitVec.ofNat 64 limW, 8⟩ = 0 := by decide +kernel

/-- The limit word's values under `ret0G`: the limit or its initial `0`. -/
theorem ret0G_lim {v : Val} (h : ret0G ⟨BitVec.ofNat 64 limW, 8⟩ v) : v = limV ∨ v = 0 := by
  rcases h limW limV (by simp) rfl with h | h
  · exact .inl h
  · exact .inr (h.trans ret0_limInit)

/-- The TCB header's store (`hhdr`), from `ret0G`. -/
theorem ret0_hhdrG (ls0 : Lsize) :
    StOk (ret0MS ls0) ret0F ret0Exe ret0End (pinA labT + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36) := by
  rw [← ret0_labT]
  exact Mem.ret0_hhdr (ret0G_of (.inl (by rw [Mem.ret0_pinA]; decide)))

/-- The TCB's fields' stores (`hfld`), from `ret0G`: the limit field stores
the limit. -/
theorem ret0_hfldG (ls0 : Lsize) :
    ∀ e ∈ ThreadInit.fields (pinA labT + 0#64 + 8#64) (stacksA labT + 0#64),
      StOk (ret0MS ls0) ret0F ret0Exe ret0End (pinA labT + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2 := by
  rw [← ret0_labT]
  refine Mem.ret0_hfld fun e he => ret0G_of ?_
  rw [Mem.ret0_stacksA] at he
  rw [tcb0, Mem.ret0_pinA]
  simp only [ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 100000 in
/-- An owned word's value at a pc, decided at the pc's phase. -/
theorem ret0_ownAt {pc : Int64} {a v : BitVec 64} (ls0 : Lsize)
    (h : (⟨a, 8⟩, v.setWidth 128) ∈ Inst.ownOf (Inst.ph pc.toBitVec.toNat)) :
    OwnAt (ret0MS ls0) ret0Exe ret0End pc a v := by
  intro s _ _ hpc
  show _ ∈ own s
  rw [own_at hpc]
  exact h

set_option maxRecDepth 100000 in
/-- The TCB allocation (`htcb`), from `ret0G` and the owned counter. -/
theorem ret0_tcbG (ls0 : Lsize) : TcbOk (ret0MS ls0) ret0F ret0Exe ret0End 0#64 :=
  Mem.ret0_tcbOk (ret0G_of (.inl (by rw [Mem.ret0_pnA]; decide)))
    (ret0_ownAt ls0 (by rw [Mem.ret0_pnA, show labOf ret0Exe = labT from ret0_labT]; decide +kernel))

set_option maxRecDepth 100000 in
/-- The stack take (`htk`), from `ret0G` and the owned counters. -/
theorem ret0_takeG (ls0 : Lsize) : TakeOk (ret0MS ls0) ret0F ret0Exe ret0End 0#64 :=
  Mem.ret0_takeOk (ret0G_of (.inl (by rw [Mem.ret0_lockA]; decide)))
    (ret0G_of (.inl (by rw [Mem.ret0_lockA]; decide))) (ret0G_of (.inl (by rw [Mem.ret0_nextA]; decide)))
    (ret0_ownAt ls0 (by rw [Mem.ret0_lockA, show labOf ret0Exe = labT from ret0_labT]; decide +kernel))
    (ret0_ownAt ls0 (by rw [Mem.ret0_freeNA, show labOf ret0Exe = labT from ret0_labT]; decide +kernel))
    (ret0_ownAt ls0 (by rw [Mem.ret0_nextA, show labOf ret0Exe = labT from ret0_labT]; decide +kernel))

/-- The limit word's loads against a bound `Z` at least the limit (`hlimM`,
`hlimW`), from `ret0G`. -/
theorem ret0_limG (ls0 : Lsize) {Z : BitVec 64} (hZ : 268439552 ≤ Z.toNat) :
    LimOk (ret0MS ls0) ret0F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + 0#64 + 8#64))) Z := by
  rw [← ret0_labT]
  refine Mem.ret0_limOk fun v hv => ?_
  have hl : limA (UInt64.ofBitVec tcb0) = BitVec.ofNat 64 limW := by rw [tcb0, Mem.ret0_pinA]; decide
  rw [hl] at hv
  rcases ret0G_lim hv with rfl | rfl
  · exact hZ
  · exact Nat.zero_le _

/-- **`ret0` is correct on the parsed values, the consumer instantiated**:
`ret0_correct_parsed` with `hE`, `hN`, `hT`, `hA` from `ret0_instR`
(`Spike/Lib/A64Ret0I.lean`) at the entry region `R0 = entryR`,
`F := ret0F`, the first take's range `rS0` and the phase `Tk` of
`Spike/Lib/A64Ret0I.lean`; the runtime's stores from `ret0G` and the owned
counters (`ret0_hhdrG`, `ret0_hfldG`, `ret0_tcbG`, `ret0_takeG`,
`ret0_limG`), `main` from `ret0_main`, the phase at load from
`not_tk_threadAt`, `WriteNoProm` from the fragment's `NoWrite`
(`writeNoProm_of_noWrite`: no state of `ret0_instR`'s fragment is at a
`write`). Open: of the fragment `ret0_instR` builds, `PromShared`. The trust
boundary is as for `ret0_correct_parsed`.

`PromShared` holds (`promShared_a64`); `ret0_correct` is the
premise-free form. -/
theorem ret0_correct_inst_parsed {B : Budget} {arch : WeakMem.Arch} {ls0 : Lsize} :
    ∃ inv : Frag isaLSE2, (∀ s c, At ret0Exe ret0End R0 ret0F entry0 s c → inv s c) ∧
      (PromShared ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS0 Tk μ0 →
       Correct TPar (SrcSem.source (ret0P arch) ret0Src) ret0Λ B (ret0Prog, ret0Secs)) := by
  obtain ⟨d, hd, hb⟩ := ret0_main
  have hst := Inst.labT_stacksA
  obtain ⟨inv, hE, hN, hT, hA, hW⟩ := ret0_instR (G := ret0G) (rd := fun _ => True) (ls0 := ls0) rfl (ret0_hhdrG ls0)
    (ret0_tcbG ls0) (ret0_hfldG ls0) (ret0_takeG ls0) (ret0_limG ls0 (by rw [hst]; decide))
    (ret0_limG ls0 (by rw [hst]; decide)) hd hb
  exact ⟨inv, hE, fun hps => ret0_correct_parsed hE hN hT hA Inst.not_tk_threadAt hps (writeNoProm_of_noWrite hW)⟩

/-- **`ret0_correct_inst_parsed` at the listing `ret0Asm`**, by the parse
equation `hpa` (`correct_of_parsed`; the compiled `#guard` of
`Spike/Lib/A64Ret0Code.lean`, line 1534).

`ret0_correct_asm` is the premise-free form. -/
theorem ret0_correct_inst {B : Budget} {arch : WeakMem.Arch} {ls0 : Lsize}
    (hpa : parsesTo ret0Asm ret0Prog ret0Secs = true) :
    ∃ inv : Frag isaLSE2, (∀ s c, At ret0Exe ret0End R0 ret0F entry0 s c → inv s c) ∧
      (PromShared ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS0 Tk μ0 →
       Correct T (SrcSem.source (ret0P arch) ret0Src) ret0Λ B ret0Asm) :=
  let ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  let ⟨inv, hE, h⟩ := ret0_correct_inst_parsed (B := B) (arch := arch) (ls0 := ls0)
  ⟨inv, hE, fun hps => correct_of_parsed _ _ h1 h2 (h hps)⟩

/-- **The release theorem, pending.** `Correct` over the target on parsed
texts at the parsed values, from exactly the premises still open:
the promise hypothesis `PromShared` (`hprom`), for every fragment holding the
entry node (the fragment is `ret0_instR`'s; a stronger form than
`ret0_correct_inst_parsed`'s, so that the conclusion has no existential).
**Staging form only**: `hprom`'s quantification over fragments exists to
state the release conclusion now; it disappears with the promise premise
and is not part of the release statement. `WriteNoProm` is discharged
(`ret0_correct_inst_parsed`).

The premise-free release theorem is `ret0_correct` below, through
`correctA64P''`, of the statement:

```
theorem ret0_correct {B : Budget} {arch : WeakMem.Arch} :
    Correct TPar (SrcSem.source (ret0P arch) ret0Src) ret0Λ B (ret0Prog, ret0Secs)
```

The trust boundary is as for `ret0_correct_parsed`: the only link from the
listing `ret0Asm` to `(ret0Prog, ret0Secs)` is the compiled `#guard parsesTo ret0Asm ret0Prog ret0Secs`
(`Spike/Lib/A64Ret0Code.lean`, line 1534), not checked by the kernel.

`PromShared` holds (`promShared_a64`); `ret0_correct` is the
premise-free form. -/
theorem ret0_correct_pending {B : Budget} {arch : WeakMem.Arch} {ls0 : Lsize}
    (hprom : ∀ inv : Frag isaLSE2, (∀ s c, At ret0Exe ret0End R0 ret0F entry0 s c → inv s c) →
      PromShared ret0Λ (ret0P arch) ret0Src ret0G own (IOf ret0Λ.static ls0 inv) rS0 Tk μ0) :
    Correct TPar (SrcSem.source (ret0P arch) ret0Src) ret0Λ B (ret0Prog, ret0Secs) :=
  let ⟨inv, hE, h⟩ := ret0_correct_inst_parsed (B := B) (arch := arch) (ls0 := ls0)
  h (hprom inv hE)


/-- **`ret0` is correct**, with no premise: `Correct` over the target on
parsed texts at the parsed values, at every budget `B` and memory
architecture `arch`. The fragment is `ret0_instR`'s (at the runtime's
stores from `ret0G`, as in `ret0_correct_inst_parsed`), and the consumer is
`correctA64P''` (`Spike/Lib/A64CorrectNW.lean`): the promise premise
`PromShared` is derived from the node obligations, `TakePath` and the layout
(`promShared_a64`, `Spike/Lib/A64PromShared.lean`), and `WriteNoProm`
from the fragment's `NoWrite`, which `ret0_instR` concludes.

The trust boundary is as for `ret0_correct_parsed`: the only link from the
listing `ret0Asm` to `(ret0Prog, ret0Secs)` is the compiled `#guard parsesTo ret0Asm ret0Prog ret0Secs`
(`Spike/Lib/A64Ret0Code.lean`, line 1534), not checked by the kernel;
`ret0_correct_asm` carries this statement to `ret0Asm` given that equation. -/
theorem ret0_correct {B : Budget} {arch : WeakMem.Arch} :
    Correct TPar (SrcSem.source (ret0P arch) ret0Src) ret0Λ B (ret0Prog, ret0Secs) := by
  obtain ⟨d, hd, hb⟩ := ret0_main
  have hst := Inst.labT_stacksA
  let ls0 : Lsize := fun _ => 0
  obtain ⟨inv, hE, hN, hT, hA, hW⟩ := ret0_instR (G := ret0G) (rd := fun _ => True) (ls0 := ls0) rfl (ret0_hhdrG ls0)
    (ret0_tcbG ls0) (ret0_hfldG ls0) (ret0_takeG ls0) (ret0_limG ls0 (by rw [hst]; decide))
    (ret0_limG ls0 (by rw [hst]; decide)) hd hb
  rw [← ret0_marksP] at hN hT hA
  exact correctA64P'' (lsize := ls0) (name := fun _ => "") SccCode.ret0Λ_image (ret0_ss ls0 _)
    SccCode.ret0_wide ⟨rfl, rfl, hE _ _ ret0_entry⟩ ⟨_, ret0_loadP⟩ (.none (ret0P_hooks arch)) (ret0P_init arch) hN
    (ret0_safe arch _) hT Inst.not_tk_threadAt ret0_own0 hW (fun _ => trivial) SccCode.ret0Λ_wf ret0_G0
    ret0_Gpl hA (fun h => h)

/-- **`ret0_correct` at the listing `ret0Asm`**, by the parse equation `hpa`
(`correct_of_parsed`; the compiled `#guard` of
`Spike/Lib/A64Ret0Code.lean`, line 1534, the trust boundary). -/
theorem ret0_correct_asm {B : Budget} {arch : WeakMem.Arch}
    (hpa : parsesTo ret0Asm ret0Prog ret0Secs = true) :
    Correct T (SrcSem.source (ret0P arch) ret0Src) ret0Λ B ret0Asm :=
  let ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  correct_of_parsed _ _ h1 h2 ret0_correct

end Inst

/-! ## Non-vacuity

The load is defined at the parse the `#guard` of `Spike/Lib/A64Ret0Code.lean`
checks (`ret0_load`), and the loaded thread is at the entry node
(`ret0_entry`). The run of the load (exit `42`) and the frontend's program
(`ret0Src`) are checked in `Spike/Test/A64Ret0Correct.lean`. -/

end Spike.Lib.A64.Flow.Ret0.Correct
