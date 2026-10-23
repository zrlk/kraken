/-
**The AArch64 runtime's layout, as a record** (`RuntimeLayout`): what the
runtime's segment specs (`Spike/Lib/A64Ret0.lean` and its parts) read of a
program's placement, so that they are proved once over the record and not
once per program.

- **The record.** The executable `exe` laying out the emitted text `prog`
  (`Lays`), the static link `Λ`, the six runtime data words (`pinA`, `pnA`,
  `stacksA`, `nextA`, `lockA`, `freeNA`) with the labels they are the
  addresses of (`lab_pin` …), and their side conditions: every word the
  start of a thread touches (`rtWords`: the four counters, the TCB's header
  and its six fields) lies below `2 ^ 32`, clear of the entry stack and of
  the stack pool, mapped in the loaded kernel state and shared; the pool
  fits the address space below the entry stack; the first stack is
  16-aligned and inside the pool.
- **Where the fields come from.** The words and their side conditions are
  the placement check's runtime-data-word component (`placeok_spec`, A8),
  the regions its link component (A1) and loader component (A2). Its
  extraction lemmas produce the record; on `ret0` the hand facts of
  `Spike/Lib/A64Ret0Mem.lean` and `Spike/Lib/A64Ret0I.lean` produce it
  (`Spike/Lib/Rt/A64LayoutRet0.lean`, the oracle instance).
- **Not fields.** The layout's constants (the TCB header `2307`, its length
  `80`, the pinned bound `131072`, the stack size `16384`, the pool bound
  `536870912`, the headroom `4096`, the limit word's offset `8`) are the
  default configuration's; they stay literals of the runtime's templates
  and specs, as `Ret0.AllocTcb.hdr0`, `Ret0.StackTake.size0` and `limA` have them.
  The phase pcs (`Ret0.AllocTcb.rmwPc`, `Ret0.StackTake.swpPc` …) are label-relative
  already; their per-node facts are owed to the placement check's offset and
  phase components (A5/A6), not to this record.
- **The memory side** (`rtF`, `RtFree`, `stOk_rt`, `ldOk_rt`, `limOk_rt`):
  the entry frame condition (every word of `rtWords` unmapped in private
  memory), its stability in the entry stack (`rtF_stable`), its truth on
  the entry stack's memory (`rtF_stackMem`) and across a take from the pool
  (`rtF_takeMem`); the builders of a runtime access's facts at a word of
  `rtWords` under `msOf`, given the value invariant there.
- **`start_segW`'s layout premises at the first thread** (`n0 = k0 = 0`):
  the arithmetic ones (`rt_h16`, `rt_hok`, `rt_hfit`, `rt_hout`), the
  memory-side ones (`rt_hhdr`, `rt_hfld`, `rt_tcbOk`, `rt_takeOk`,
  `rt_limOk`) and the first stack's range (`rS0`, `rS0_sub`, `rS0_subR`),
  each from the record.
-/
import Spike.Lib.A64Ret0
import Spike.Lib.A64Consumer
import Scc.Sem.CorrectE

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (pinA pnA stacksA nextA lockA freeNA limA StOk LdOk LimOk OwnAt TcbOk TakeOk
  takeMem loadInt_takeMem)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64Consumer (msOf K0 Own Lbl Lsize)
open Spike.Lib.Consumer1 (LocIn)

/-! ## The words -/

/-- **The words the start of a thread touches**, from the runtime's data
words: the counters `scc_rt_pinned_next`, `scc_rt_stack_next`,
`scc_rt_stack_lock`, `scc_rt_stack_free_n`; the first TCB's header at
`scc_rt_pinned`; its six fields from `scc_rt_pinned + 8` (the limit word
the second). -/
def rtWordsOf (pinA pnA nextA lockA freeNA : BitVec 64) : List (BitVec 64) :=
  [pnA, nextA, lockA, freeNA, pinA] ++ (List.range 6).map fun i => pinA + BitVec.ofNat 64 (8 * (i + 1))

/-- The word `a` is clear of the range `r` (its 8 bytes outside). -/
def Clear (r : Scc.Sem.Range) (a : BitVec 64) : Prop := a.toNat + 8 ≤ r.lo ∨ r.lo + r.size ≤ a.toNat

/-- **The runtime's layout**: the executable and its text, the static
link, the runtime's data words at their labels, and the side conditions
the runtime's specs need of them. -/
structure RuntimeLayout where
  /-- The loaded executable. -/
  exe : _root_.Executable
  /-- The emitted text. -/
  prog : List Directive
  /-- The static link. -/
  Λ : Scc.Sem.Layout
  /-- The executable lays out the text. -/
  lays : Lays exe prog
  /-- The executable's cells are a valid layout. -/
  valid : Kraken.Executable.ValidLayout exe
  /-- `scc_rt_pinned`. -/
  pinA : BitVec 64
  /-- `scc_rt_pinned_next`. -/
  pnA : BitVec 64
  /-- `scc_rt_stacks`. -/
  stacksA : BitVec 64
  /-- `scc_rt_stack_next`. -/
  nextA : BitVec 64
  /-- `scc_rt_stack_lock`. -/
  lockA : BitVec 64
  /-- `scc_rt_stack_free_n`. -/
  freeNA : BitVec 64
  lab_pin : Ret0.pinA (_root_.Executable.labels exe).label = pinA
  lab_pn : Ret0.pnA (_root_.Executable.labels exe).label = pnA
  lab_stacks : Ret0.stacksA (_root_.Executable.labels exe).label = stacksA
  lab_next : Ret0.nextA (_root_.Executable.labels exe).label = nextA
  lab_lock : Ret0.lockA (_root_.Executable.labels exe).label = lockA
  lab_freeN : Ret0.freeNA (_root_.Executable.labels exe).label = freeNA
  /-- The words lie below `2 ^ 32`. -/
  words_small : ∀ a ∈ rtWordsOf pinA pnA nextA lockA freeNA, a.toNat < 2 ^ 32
  /-- The words are clear of the stack pool. -/
  words_pool : ∀ a ∈ rtWordsOf pinA pnA nextA lockA freeNA, Clear Λ.stackPool a
  /-- The words are mapped in the loaded kernel state for reading and
  writing, their bytes in `data` or `pinned`. -/
  words_mapped : ∀ a ∈ rtWordsOf pinA pnA nextA lockA freeNA,
    Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true ∧ Scc.Sem.Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true ∧
      ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i)
  /-- The stack pool fits the address space. -/
  pool_fit : Λ.stackPool.lo + Λ.stackPool.size < 2 ^ 64
  /-- The first stack is 16-aligned. -/
  stacks_al : stacksA.toNat % 16 = 0
  /-- The first stack lies in the pool. -/
  stacks_sub : (⟨stacksA.toNat, 16384⟩ : Scc.Sem.Range).Sub Λ.stackPool

namespace RuntimeLayout

variable (L : RuntimeLayout)

attribute [instance] RuntimeLayout.valid

/-- The executable's labels. -/
abbrev lab : Label → Int64 := (_root_.Executable.labels L.exe).label

/-- Where a thread running the text halts. -/
abbrev endPc : Int64 := endOf L.exe L.prog

/-- The stack pool. -/
abbrev pool : Scc.Sem.Range := L.Λ.stackPool

/-- The pinned region. -/
abbrev pinned : Scc.Sem.Range := L.Λ.pinned

/-- **The words the start of a thread touches** (`rtWordsOf`). -/
abbrev rtWords : List (BitVec 64) := rtWordsOf L.pinA L.pnA L.nextA L.lockA L.freeNA

theorem pin_mem : L.pinA ∈ L.rtWords := by simp [rtWordsOf]
theorem pn_mem : L.pnA ∈ L.rtWords := by simp [rtWordsOf]
theorem next_mem : L.nextA ∈ L.rtWords := by simp [rtWordsOf]
theorem lock_mem : L.lockA ∈ L.rtWords := by simp [rtWordsOf]
theorem freeN_mem : L.freeNA ∈ L.rtWords := by simp [rtWordsOf]

/-- The TCB's field `i` is a word. -/
theorem fld_mem {i : Nat} (hi : i < 6) : L.pinA + BitVec.ofNat 64 (8 * (i + 1)) ∈ L.rtWords := by
  simp only [rtWordsOf, List.mem_append, List.mem_map, List.mem_range]
  exact .inr ⟨i, hi, rfl⟩

end RuntimeLayout

/-! ## The entry frame condition -/

section Frame

variable (L : RuntimeLayout)

/-- **The entry frame condition**: every word of `rtWords` unmapped in
the thread's private memory. -/
def rtF (m : MachineData) : Prop := ∀ a ∈ L.rtWords, Mem.loadInt m.dmem a 8 = none

/-- **The entry stack's region** at the entry state `E`: from the stack
pointer down by `65536`, the top 64 KiB of the stack (all of it at an
admissible `E`'s least size, `entryR_sub`). -/
def entryR (E : Scc.Sem.Entry) : Region := ⟨BitVec.ofNat 64 E.sp, -65536, 0⟩

/-- An admissible stack pointer: at least `65536`, a user address, 16-aligned. -/
theorem entry_sp {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) :
    65536 ≤ E.sp ∧ E.sp < 2 ^ 63 ∧ E.sp % 16 = 0 :=
  ⟨by have := hE.2.2.1; unfold Scc.Sem.Entry.sp; omega, hE.2.2.2, hE.2.1⟩

/-- The region's base is the stack pointer. -/
theorem entryR_base {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) : (entryR E).base.toNat = E.sp := by
  show (BitVec.ofNat 64 E.sp).toNat = E.sp
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := hE.2.2.2; omega)

/-- **The region lies in the entry stack** (its least size `65536`). -/
theorem entryR_sub {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) :
    (⟨E.sp - 65536, 65536⟩ : Scc.Sem.Range).Sub E.stack := by
  have := hE.2.2.1
  simp only [Scc.Sem.Range.Sub, Scc.Sem.Entry.sp]
  omega

/-- The entry stack's region does not wrap. -/
theorem entryR_ok {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) : (entryR E).OK := by
  have hb := entryR_base hE
  have := entry_sp hE
  refine ⟨?_, ?_⟩ <;> rw [hb]
  · show (0 : Int) ≤ (E.sp : Int) + -65536; omega
  · show (E.sp : Int) + 0 ≤ 2 ^ 64; omega

/-- Its top is 16-aligned. -/
theorem entryR_al {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) : (entryR E).base.toNat % 16 = 0 := by
  rw [entryR_base hE]; exact hE.2.1

/-- **The words are clear of an entry stack clear of the layout**: their
bytes lie in `data` or `pinned` (`words_mapped`), regions of the layout. -/
theorem words_clear {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) : ∀ a ∈ L.rtWords, Clear E.stack a := by
  intro a ha
  obtain ⟨-, hr⟩ := Scc.Sem.Entry.clear_disjoint hE.1
  have hsz := hE.2.2.1
  have hD := hr _ (by simp [Scc.Sem.Layout.regions] : L.Λ.data ∈ L.Λ.regions)
  have hP := hr _ (by simp [Scc.Sem.Layout.regions] : L.Λ.pinned ∈ L.Λ.regions)
  have hb := (L.words_mapped a ha).2.2
  simp only [Scc.Sem.Range.Disjoint] at hD hP
  unfold Clear
  refine Decidable.byContradiction fun hc => ?_
  by_cases hlt : a.toNat < E.stack.lo
  · rcases hb (E.stack.lo - a.toNat) (by omega) with h | h <;>
      simp only [Scc.Sem.Range.contains] at h <;> omega
  · rcases hb 0 (by omega) with h | h <;> simp only [Scc.Sem.Range.contains] at h <;> omega

/-- **The pool is clear of an entry stack clear of the layout.** -/
theorem pool_clear {E : Scc.Sem.Entry} (hE : E.clear L.Λ = true) : L.Λ.stackPool.Disjoint E.stack :=
  (Scc.Sem.Entry.clear_disjoint hE).2 _ (by simp [Scc.Sem.Layout.regions])

/-- A word clear of an entry stack, the stack in the address space
(`hfit`), is unmapped in the stack's private memory. -/
theorem stackMem_loadInt {E : Scc.Sem.Entry} {a : BitVec 64} (hfit : E.stack.lo + E.stack.size ≤ 2 ^ 64)
    (ha : Clear E.stack a) : Mem.loadInt E.stackMem a 8 = none := by
  have hne : E.stackMem[a]? = none := by
    rw [← Std.ExtHashMap.get?_eq_getElem?]
    unfold Scc.Sem.Entry.stackMem
    rw [Mem.get?_storeBytes_of_not_mem]
    · simp
    · rw [mem_At_iff]
      rintro ⟨i, hi, he⟩
      rw [List.length_replicate] at hi
      have h1 := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1
      unfold Clear at ha
      rw [Nat.mod_eq_of_lt (a := E.stack.lo) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)] at h1
      omega
  unfold Mem.loadInt Mem.loadBytes
  rw [show List.range 8 = 0 :: List.range' 1 7 from rfl, List.map_cons]
  simp [List.allSome, List.mapM_cons, hne]

/-- **The entry frame condition holds of the initial private memory**: the
entry stack's zero bytes map no word, the words lying clear of it
(`words_clear`, the stack clear of the layout). -/
theorem rtF_stackMem {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {m : MachineData} (h : m.dmem = E.stackMem) :
    rtF L m := by
  intro a ha
  rw [h]
  exact stackMem_loadInt (Scc.Sem.Entry.clear_disjoint hE.1).1 (words_clear L hE a ha)

/-- A byte of an entry stack's memory: zero inside the stack. -/
theorem stackMem_getE {E : Scc.Sem.Entry} (hsz : E.stack.size ≤ 2 ^ 64) (p : BitVec 64) :
    E.stackMem.get? p = if (p - BitVec.ofNat 64 E.stack.lo).toNat < E.stack.size then some 0 else none := by
  rw [Scc.Sem.Entry.stackMem, Kraken.Promising.Mem.get?_storeBytes]
  rw [Std.ExtHashMap.get?_eq_getElem?, get?_At _ _ _ (by rw [List.length_replicate]; exact hsz),
    List.getElem?_replicate]
  split <;> simp

/-- **A word of the entry stack's region reads** in the initial private
memory, at an admissible entry state `E` (the region in the stack:
`entryR_sub`). -/
theorem stack_wordE {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) {k : Int} (hk : (entryR E).Off k) :
    (Mem.loadInt E.stackMem ((entryR E).addr k) 8).isSome := by
  have ha := (entryR E).addr_toNat (entryR_ok hE) hk
  have hs := entryR_sub hE
  have hsp := entry_sp hE
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  obtain ⟨-, hlo, hhi⟩ := hk
  have hlo' : (entryR E).lo = -65536 := rfl
  have hhi' : (entryR E).hi = 0 := rfl
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  rw [entryR_base hE] at ha
  simp only [Scc.Sem.Range.Sub] at hs
  unfold Mem.loadInt
  rw [Option.isSome_map]
  unfold Mem.loadBytes
  rw [List.allSome_isSome_iff]
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have hi8 := List.mem_range.mp hi
  rw [stackMem_getE (by omega), ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  · rfl
  · rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-- **The take keeps the entry frame condition**: the taken range lies in
the stack pool (`hsub`), which the words are clear of. -/
theorem rtF_takeMem {rS : Scc.Sem.Range} (hsub : rS.Sub L.pool) {pm : _root_.Mem 64} {m : MachineData}
    (h : rtF L m) : rtF L (takeMem pm rS m) := by
  unfold RuntimeLayout.pool at hsub
  intro a ha
  rw [loadInt_takeMem ?_]
  · exact h a ha
  intro i hi hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have hs := L.words_small a ha
  have hp := L.words_pool a ha
  have hf := L.pool_fit
  obtain ⟨h1, h2⟩ := hsub
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  unfold Clear at hp
  omega

/-- **The entry frame condition is stable in the entry stack**: every word
lies clear of it, so a write inside it keeps each one. -/
theorem rtF_stable {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) : FStable (entryR E) (rtF L) := by
  intro m m' h hD a ha
  rw [hD a (by have := L.words_small a ha; omega) ?_]
  · exact h a ha
  have hc := words_clear L hE a ha
  have hs := entryR_sub hE
  have hsp := entry_sp hE
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  simp only [Clear, entryR, Scc.Sem.Range.Sub] at hc hs ⊢
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A range in the pool fits the address space.** -/
theorem fitS_of_sub {rS : Scc.Sem.Range} (hsub : rS.Sub L.pool) : rS.lo + rS.size ≤ 2 ^ 64 := by
  unfold RuntimeLayout.pool at hsub
  have := L.pool_fit; obtain ⟨-, h⟩ := hsub; omega

/-- **A range in the pool is off the entry stack's region**, word by
word. -/
theorem outS_of_sub {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {rS : Scc.Sem.Range} (hsub : rS.Sub L.pool) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (entryR E).base.toNat + (entryR E).lo ∨ ((entryR E).base.toNat : Int) + (entryR E).hi ≤ a := by
  unfold RuntimeLayout.pool at hsub
  intro a _ ha ha7
  have hb := pool_clear L hE.1
  have hs := entryR_sub hE
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  obtain ⟨h0, h⟩ := hsub
  simp only [Scc.Sem.Range.contains] at ha ha7
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hb hs
  rw [entryR_base hE]
  show (a : Int) + 8 ≤ (E.sp : Int) + -65536 ∨ (E.sp : Int) + 0 ≤ a
  omega

/-- **The entry stack's cells are off a range in the pool.** -/
theorem rS_of_sub {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {rS : Scc.Sem.Range} (hsub : rS.Sub L.pool) :
    ∀ k, (entryR E).Off k → ∀ i < 8, (entryR E).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := by
  unfold RuntimeLayout.pool at hsub
  intro k hk i hi hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have hb := pool_clear L hE.1
  have hs := entryR_sub hE
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  have hf := L.pool_fit
  obtain ⟨h0, h⟩ := hsub
  have ha := (entryR E).addr_toNat (entryR_ok hE) hk
  have hfit := (entryR E).addr_fit (entryR_ok hE) hk
  obtain ⟨-, h3, h4⟩ := hk
  have h1 := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  have hlo : (entryR E).lo = -65536 := rfl
  rw [entryR_base hE] at ha
  have hhi : (entryR E).hi = 0 := rfl
  rw [hlo] at h3
  rw [hhi] at h4
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hb hs
  omega

end Frame

/-! ## The memory side -/

section MemSide

variable (L : RuntimeLayout) {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own}
  {lbl : Lbl} {lsize : Lsize}

/-- **No placed label covers a word**: the runtime owns each of them under
the labels' memory side. -/
def RtFree (lbl : Lbl) (lsize : Lsize) : Prop :=
  ∀ a ∈ L.rtWords, ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains a.toNat

/-- With no label placed, no label covers a word. -/
theorem rtFree_none (h : ∀ l, lbl l = none) : RtFree L lbl lsize := by
  rintro a - ⟨l, b, hl, -⟩
  rw [h l] at hl
  cases hl

variable {L}

theorem mp_rt {a : BitVec 64} (ha : a ∈ L.rtWords) (w : Bool) :
    (msOf L.Λ μ rd G own lbl lsize).mp ⟨a, 8⟩ w := by
  obtain ⟨h1, h2, h3⟩ := L.words_mapped a ha
  refine ⟨by cases w <;> assumption, fun _ i hi => ?_⟩
  rcases h3 i (by simpa [Scc.Sem.Kernel.locBytes] using hi) with h | h
  · exact .inl h
  · exact .inr (.inr h)

/-- **A runtime store's facts** at a word, given the value invariant
there. -/
theorem stOk_rt (hfree : RtFree L lbl lsize) {a v : BitVec 64} (ha : a ∈ L.rtWords)
    (hG : G ⟨a, 8⟩ (v.setWidth 128)) : StOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc a v :=
  ⟨hfree a ha, mp_rt ha true, hG, fun _ hm => hm a ha⟩

/-- **A runtime load's facts** at a word. -/
theorem ldOk_rt (hfree : RtFree L lbl lsize) {a : BitVec 64} (ha : a ∈ L.rtWords) :
    LdOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc a :=
  ⟨hfree a ha, mp_rt ha false, fun _ hm => hm a ha⟩

/-- **A limit load's facts** at a word, given its room. -/
theorem limOk_rt (hfree : RtFree L lbl lsize) {a Z : BitVec 64} (ha : a ∈ L.rtWords)
    (hroom : ∀ v : Val, G ⟨a, 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat) :
    LimOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc a Z :=
  ⟨hfree a ha, mp_rt ha false, fun _ hm => hm a ha, hroom⟩

end MemSide

/-! ## `start_segW`'s layout premises at `n0 = k0 = 0` -/

section Start

variable (L : RuntimeLayout) {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own}
  {lbl : Lbl} {lsize : Lsize}

/-- The limit word of a small thread pointer: `8` past it. -/
theorem limA_small {t : BitVec 64} (ht : t.toNat < 2 ^ 32) : limA (UInt64.ofBitVec t) = t + 8#64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (UInt64.ofBitVec t).toBitVec.toInt = (t.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by simp; omega)
  simp only [limA, BitVec.toNat_ofInt, h1, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show ((8 : Int64).toInt) = 8 from rfl]
  omega

/-- The first TCB's address is its field `0`. -/
theorem tcb0_eq : L.pinA + 0#64 + 8#64 = L.pinA + BitVec.ofNat 64 (8 * (0 + 1)) := by
  rw [BitVec.add_zero]

/-- **The first TCB's limit word** is its field `1`. -/
theorem limA_tcb0 : limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64)) = L.pinA + BitVec.ofNat 64 (8 * (1 + 1)) := by
  rw [limA_small (by rw [tcb0_eq]; exact L.words_small _ (L.fld_mem (by decide))), BitVec.add_zero,
    BitVec.add_assoc]
  rfl

/-- The first stack's top: its base plus `16384`, in the address space. -/
theorem top0_toNat : (L.stacksA + 0#64 + 16384#64).toNat = L.stacksA.toNat + 16384 := by
  have := L.pool_fit
  obtain ⟨h1, h2⟩ := L.stacks_sub
  rw [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only at h1 h2
  rw [Nat.mod_eq_of_lt (a := 16384) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rt_h16 : (L.stacksA + 0#64 + 16384#64).toNat % 16 = 0 := by
  have := L.stacks_al
  rw [top0_toNat]
  omega

theorem rt_hok : (swR (L.stacksA + 0#64 + 16384#64) (-80) 0).OK := by
  have := L.pool_fit
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only at h1 h2
  refine ⟨?_, ?_⟩ <;> simp only [swR, top0_toNat] <;> omega

theorem rt_hfit : (limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
  rw [limA_tcb0]
  have := L.words_small _ (L.fld_mem (i := 1) (by decide))
  omega

theorem rt_hout : ((limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64))).toNat : Int) + 8 ≤
      (L.stacksA + 0#64 + 16384#64).toNat + -80 ∨
    ((L.stacksA + 0#64 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64))).toNat := by
  rw [limA_tcb0, top0_toNat]
  have hp := L.words_pool _ (L.fld_mem (i := 1) (by decide))
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only [Clear] at hp
  simp only at h1 h2
  omega

variable {L}

theorem rt_hhdr (hfree : RtFree L lbl lsize)
    (hG : G ⟨L.pinA + 0#64, 8⟩ ((Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128)) :
    StOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc (L.pinA + 0#64) (Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36) :=
  stOk_rt hfree (by rw [BitVec.add_zero]; exact L.pin_mem) hG

theorem rt_hfld (hfree : RtFree L lbl lsize)
    (hG : ∀ e ∈ Ret0.ThreadInit.fields (L.pinA + 0#64 + 8#64) (L.stacksA + 0#64),
      G ⟨L.pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128)) :
    ∀ e ∈ Ret0.ThreadInit.fields (L.pinA + 0#64 + 8#64) (L.stacksA + 0#64),
      StOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc (L.pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1)
        e.2 := by
  intro e he
  refine stOk_rt hfree ?_ (hG e he)
  have : ∃ i < 6, e.1 = 8 * i := by
    simp only [Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩
  obtain ⟨i, hi, he1⟩ := this
  have hq : L.pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1 = L.pinA + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [he1, BitVec.add_zero, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hq]
  exact L.fld_mem hi

theorem rt_tcbOk (hfree : RtFree L lbl lsize)
    (hG : G ⟨L.pnA, 8⟩ ((0#64 + Ret0.AllocTcb.tcbLen).setWidth 128))
    (hown : OwnAt (msOf L.Λ μ rd G own lbl lsize) L.exe L.endPc (Ret0.AllocTcb.rmwPc L.lab) L.pnA 0#64) :
    TcbOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc 0#64 := by
  have h := L.lab_pn
  refine ⟨?_, ?_⟩
  · rw [h]; exact stOk_rt hfree L.pn_mem hG
  · rw [h]; exact hown

theorem rt_takeOk (hfree : RtFree L lbl lsize)
    (hG1 : G ⟨L.lockA, 8⟩ ((1#64).setWidth 128))
    (hG0 : G ⟨L.lockA, 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨L.nextA, 8⟩ ((0#64 + Ret0.StackTake.size0).setWidth 128))
    (hownL : OwnAt (msOf L.Λ μ rd G own lbl lsize) L.exe L.endPc (Ret0.StackTake.swpPc L.lab) L.lockA 0#64)
    (hownF : OwnAt (msOf L.Λ μ rd G own lbl lsize) L.exe L.endPc (Ret0.StackTake.freeNPc L.lab) L.freeNA 0#64)
    (hownN : OwnAt (msOf L.Λ μ rd G own lbl lsize) L.exe L.endPc (Ret0.StackTake.nextPc L.lab) L.nextA 0#64) :
    TakeOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc 0#64 := by
  have hl := L.lab_lock
  have hf := L.lab_freeN
  have hn := L.lab_next
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]; exact stOk_rt hfree L.lock_mem hG1
  · rw [hf]; exact ldOk_rt hfree L.freeN_mem
  · rw [hl]; exact stOk_rt hfree L.lock_mem hG0
  · rw [hn]; exact stOk_rt hfree L.next_mem hGn
  · rw [hl]; exact hownL
  · rw [hf]; exact hownF
  · rw [hn]; exact hownN

/-- **The limit word's facts** for any bound `Z`, given its room. -/
theorem rt_limOk (hfree : RtFree L lbl lsize) {Z : BitVec 64}
    (hroom : ∀ v : Val, G ⟨limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64)), 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat) :
    LimOk (msOf L.Λ μ rd G own lbl lsize) (rtF L) L.exe L.endPc (limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64))) Z :=
  limOk_rt hfree (by rw [limA_tcb0]; exact L.fld_mem (by decide)) hroom

variable (L)

/-- **The first take's range**: the first stack. -/
abbrev rS0 : Scc.Sem.Range := ⟨(L.stacksA + 0#64).toNat, 16384⟩

/-- `rS0` is in the stack pool. -/
theorem rS0_sub : (rS0 L).Sub L.pool := by
  rw [rS0, BitVec.add_zero]; exact L.stacks_sub

/-- The new stack's switch region lies in `rS0`, word by word. -/
theorem rS0_subR : ∀ k, (swR (L.stacksA + 0#64 + 16384#64) (-80) 0).Off k →
    ((swR (L.stacksA + 0#64 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
    (rS0 L).contains ((swR (L.stacksA + 0#64 + 16384#64) (-80) 0).addr k).toNat ∧
    (rS0 L).contains (((swR (L.stacksA + 0#64 + 16384#64) (-80) 0).addr k).toNat + 7) := by
  intro k hk
  have ha := Region.addr_toNat (rt_hok L) hk
  have h16 := L.stacks_al
  obtain ⟨h8, h1, h2⟩ := hk
  simp only [swR] at h1 h2
  rw [show (swR (L.stacksA + 0#64 + 16384#64) (-80) 0).base = L.stacksA + 0#64 + 16384#64 from rfl,
    top0_toNat] at ha
  have h0 : (L.stacksA + 0#64).toNat = L.stacksA.toNat := by rw [BitVec.add_zero]
  simp only [Scc.Sem.Range.contains, h0]
  omega

end Start

end Spike.Lib.A64.Rt
