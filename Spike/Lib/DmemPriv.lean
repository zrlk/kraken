/-
**Private memory never holds a byte of the heap or the static image**
(`DmemPriv`, any ISA): along every run of the kernel model's machine
(`Kernel.hooks`), every address thread `tid`'s private memory (`Abi.dmem`)
maps is in the entry state's initial stack or in the layout's stack pool.
Both are disjoint from `Λ.heap` and `Λ.data` (`Layout.WF.disjoint`,
`Entry.clear_disjoint`), so the byte of a placed label (`MemRel.lbl_range`)
is never private: the kernel's `write` reads it from shared memory
(`Kernel.readByte`). This is the consumer's premise `hpriv` of a byte step.

The invariant is `Kernel.OwnDom` (`Scc/Sem/OwnDom.lean`: every thread maps
exactly its initial stack and the ranges it holds, which lie in the pool)
with the pool the layout's (`PrivInv`). Its preservation per instruction is
the ISA's `DomHyps` (a leaf of `exec` maps the addresses mapped before:
Kraken's private store fires only when the private load of the same bytes
hits; `Scc.Cert.DomA64.domHyps`, `Scc.Cert.DomX64.domHyps`, with
`P := WideSt`; `Spike/Lib/A64DmemPriv.lean`, `Spike/Lib/X64DmemPriv.lean`);
the kernel's `setDmem` and `copyRange` (take, release, `clone`) move only
held ranges, inside the pool (`OwnDom.take`, `OwnDom.release`,
`OwnDom.spawn`); no step changes the pool (`pool_step`).

- `pool_step`, `pool_run`: every step keeps `KState.pool`.
- `mem_stackMem`: the initial stack's private memory maps the stack.
- `PrivInv`, `PrivInv.init`, `PrivInv.init_list`, `PrivInv.step`,
  `PrivInv.run`: the invariant at load time and along every step and run.
- `PrivKeys` (one state), `DmemPriv` (every thread), `PrivInv.dmemPriv`:
  the key range of private memory.
- `PrivKeys.not_mem`: no address of the heap or the static image is
  private.
- `PrivKeys.hpriv_of_range`, `PrivKeys.hpriv`: the byte `b + k` of a
  placed label is not a private byte (the form of `hpriv`).
- `WordIn`, `WordsNone`, `wordsNone_of_keys`, `PrivKeys.wordsNone`, `disjoint_of_sub`: no word of the
  heap or the static image loads (the word-level form a frame condition
  can take: `FStable` keeps 8-byte loads, not keys).
-/
import Scc.Sem.OwnDom
import Scc.Sem.MemRel

namespace Spike.Lib.DmemPriv

open Kraken Kraken.Promising Scc.Sem Scc.Sem.Kernel

variable {I : ISA} {K : Abi I}

/-! ## The pool -/

theorem pool_take {tid : Nat} {c c' : Config I × KState} (h : takeStep K tid c = some c') :
    c'.2.pool = c.2.pool := by
  simp only [takeStep] at h
  split at h
  · cases h
  split at h
  · cases h; rfl
  · cases h

theorem pool_release {tid : Nat} {c c' : Config I × KState} (h : releaseStep K tid c = some c') :
    c'.2.pool = c.2.pool := by
  simp only [releaseStep] at h
  split at h
  · cases h
  split at h
  · cases h; rfl
  · cases h

theorem pool_spawn {tid j : Nat} {ctid : BitVec 64} {c c' : Config I × KState}
    (h : spawnStep K tid c j ctid = some c') : c'.2.pool = c.2.pool := by
  unfold spawnStep at h
  (repeat' split at h) <;> (try cases h) <;> rfl

theorem pool_sys {A : Arch} {tid : Nat} {p : Pick} {es : List Ev} {c c' : Config I × KState}
    (h : sysStep K A tid c p = some (es, c')) : c'.2.pool = c.2.pool := by
  unfold sysStep at h
  split at h
  · cases h
  rename_i t _
  split at h
  · cases h
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> cases p <;> simp only [hcall, back] at h <;> (repeat' split at h) <;> (try cases h) <;>
    (try rfl)
  all_goals
    obtain ⟨⟨b, t'⟩, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rfl

variable {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

/-- **No step of the kernel model's machine changes the stack pool.** -/
theorem pool_step {tid : Nat} {es : List Ev} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Step μ tid c es c') : c'.2.pool = c.2.pool := by
  cases h with
  | instr _ _ _ _ => rfl
  | spawn _ hs => obtain ⟨j, r, hs, -⟩ := hs; exact pool_spawn hs
  | sys _ hs => obtain ⟨p, hs, -⟩ := hs; exact pool_sys hs
  | xfer k _ _ hx =>
    cases k
    · exact pool_take hx
    · exact pool_release hx

/-- **No run of the kernel model's machine changes the stack pool.** -/
theorem pool_run {tr : List Ev} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Run μ c tr c') : c'.2.pool = c.2.pool := by
  unfold ExtMachine.Run at h
  induction h with
  | refl => rfl
  | step hs _ ih => obtain ⟨tid, hs⟩ := hs; exact ih.trans (pool_step hs)

/-! ## The initial stack -/

/-- **The initial stack's private memory maps exactly the stack**, the
stack in the address space. -/
theorem mem_stackMem {Ent : Entry} (hfit : Ent.stack.lo + Ent.stack.size ≤ 2 ^ 64) (a : BitVec 64) :
    a ∈ Ent.stackMem ↔ Ent.stack.contains a.toNat := by
  simp only [Entry.stackMem, Mem.storeBytes, Std.ExtHashMap.union_eq, Std.ExtHashMap.mem_union_iff,
    Std.ExtHashMap.not_mem_empty, false_or, mem_At_iff, List.length_replicate, Range.contains]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Ent.stack.lo) (by omega),
      Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨a.toNat - Ent.stack.lo, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Ent.stack.lo) (by omega),
      Nat.mod_eq_of_lt (a := a.toNat - Ent.stack.lo) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## The invariant -/

/-- **Every key of a state's private memory is private**: in the entry
state's initial stack or in the layout's stack pool. -/
def PrivKeys (K : Abi I) (Λ : Layout) (Ent : Entry) (s : I.State) : Prop :=
  ∀ a, a ∈ K.dmem s → Ent.stack.contains a.toNat ∨ Λ.stackPool.contains a.toNat

/-- **Every thread's private memory is private** (`PrivKeys`). -/
def DmemPriv (K : Abi I) (Λ : Layout) (Ent : Entry) (c : Config I × KState) : Prop :=
  ∀ (tid : Nat) (t : Thread I), c.1.threads[tid]? = some t → PrivKeys K Λ Ent t.st

/-- **The invariant behind `DmemPriv`**: the domain invariant `OwnDom` from
the entry state's initial stack (`initDom`), over the fragment `P`, with the
layout's stack pool. -/
structure PrivInv (K : Abi I) (P : I.State → Prop) (Λ : Layout) (Ent : Entry) (c : Config I × KState) :
    Prop where
  own : OwnDom K (initDom Ent) P c
  pool : c.2.pool = Λ.stackPool

/-- **At load time** (`KState.init`), as `OwnDom.init`. -/
theorem PrivInv.init {P : I.State → Prop} {m : Nat} {Ent : Entry} {Λ : Layout} {c1 : Config I}
    (h0 : ∀ t, c1.threads[0]? = some t → ∀ a, a ∈ K.dmem t.st ↔ Ent.stack.contains a.toNat)
    (hk : ∀ (k : Nat) (t : Thread I), 0 < k → c1.threads[k]? = some t → ∀ a, a ∉ K.dmem t.st)
    (hP : ∀ (k : Nat) (t : Thread I), c1.threads[k]? = some t → P t.st) (hd : Λ.stackPool.Disjoint Ent.stack) :
    PrivInv K P Λ Ent (c1, KState.init m Ent Λ) :=
  ⟨OwnDom.init h0 hk hP hd, rfl⟩

/-- **At load, one entry thread and dormant ones**: the configuration of
`s0` (mapping the initial stack) and `m` copies of `sd` (mapping nothing),
both in `P`, with the kernel state as loaded. -/
theorem PrivInv.init_list {P : I.State → Prop} {m n : Nat} {Ent : Entry} {Λ : Layout} {s0 sd : I.State}
    {mem : List (Loc × Val)} (h0 : ∀ a, a ∈ K.dmem s0 ↔ Ent.stack.contains a.toNat) (hd : ∀ a, a ∉ K.dmem sd)
    (hP0 : P s0) (hPd : P sd) (hpool : Λ.stackPool.Disjoint Ent.stack) :
    PrivInv K P Λ Ent (Config.init (s0 :: List.replicate m sd) mem, KState.init n Ent Λ) := by
  refine PrivInv.init (fun t ht a => ?_) (fun k t hk ht a => ?_) (fun k t ht => ?_) hpool
  · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, List.getElem?_cons_zero,
      Option.map_some, Option.some.injEq] at ht
    subst ht
    exact h0 a
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, List.getElem?_cons_succ,
      List.getElem?_replicate] at ht
    split at ht
    · simp only [Option.map_some, Option.some.injEq] at ht
      subst ht
      exact hd a
    · simp at ht
  · rcases k with _ | k
    · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, List.getElem?_cons_zero,
        Option.map_some, Option.some.injEq] at ht
      subst ht; exact hP0
    · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, List.getElem?_cons_succ,
        List.getElem?_replicate] at ht
      split at ht
      · simp only [Option.map_some, Option.some.injEq] at ht
        subst ht; exact hPd
      · simp at ht

/-- **Every step keeps the invariant**, given the ISA's `DomHyps`. -/
theorem PrivInv.step {P : I.State → Prop} {Λ : Layout} {Ent : Entry} (hD : DomHyps K P) {tid : Nat}
    {es : List Ev} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg} (hc : PrivInv K P Λ Ent c)
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Step μ tid c es c') : PrivInv K P Λ Ent c' :=
  ⟨hc.own.step hD h, (pool_step h).trans hc.pool⟩

/-- **Every run keeps the invariant**, given the ISA's `DomHyps`. -/
theorem PrivInv.run {P : I.State → Prop} {Λ : Layout} {Ent : Entry} (hD : DomHyps K P) {tr : List Ev}
    {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg} (hc : PrivInv K P Λ Ent c)
    (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Run μ c tr c') : PrivInv K P Λ Ent c' :=
  ⟨hc.own.run hD h, (pool_run h).trans hc.pool⟩

/-- **The key range**: a thread maps its initial stack (thread 0) and the
ranges it holds, inside the pool. -/
theorem PrivInv.dmemPriv {P : I.State → Prop} {Λ : Layout} {Ent : Entry} {c : Config I × KState}
    (hc : PrivInv K P Λ Ent c) : DmemPriv K Λ Ent c := by
  intro tid t ht a ha
  rcases (hc.own.dom tid t ht a).mp ha with ⟨-, hs⟩ | ⟨r, hm, hr⟩
  · exact .inl hs
  · have hsub : r.Sub c.2.pool := (hc.own.held_ok _ hm).2.1
    rw [hc.pool] at hsub
    unfold Range.Sub at hsub; unfold Range.contains at *
    exact .inr ⟨by omega, by omega⟩

/-! ## The heap and the static image are shared -/

/-- **No address of the heap or the static image is private.** -/
theorem PrivKeys.not_mem {Λ : Layout} {Ent : Entry} {s : I.State} (hd : PrivKeys K Λ Ent s)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) {a : BitVec 64}
    (ha : Λ.heap.contains a.toNat ∨ Λ.data.contains a.toNat) : a ∉ K.dmem s := by
  intro hm
  have hs := (Entry.clear_disjoint hE).2
  have hhs := hs Λ.heap (by simp [Layout.regions])
  have hds := hs Λ.data (by simp [Layout.regions])
  obtain ⟨-, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  unfold Range.Disjoint at hhs hds hdp hhp
  rcases hd a hm with h | h <;> rcases ha with h' | h' <;> unfold Range.contains at h h' <;> omega

/-- **The byte `r.lo + k` of a range in the heap or the static image is not
a private byte** (the form of the consumer's `hpriv`). -/
theorem PrivKeys.hpriv_of_range {Λ : Layout} {Ent : Entry} {s : I.State} (hd : PrivKeys K Λ Ent s)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) {r : Range} (hr : r.Sub Λ.heap ∨ r.Sub Λ.data) {k : Nat}
    (hk : k < r.size) (x : UInt8) : (K.dmem s).loadBytes (BitVec.ofNat 64 (r.lo + k)) 1 ≠ some [x] := by
  have hh := (hwf.inSpace Λ.heap (by simp [Layout.regions])).2
  have hdt := (hwf.inSpace Λ.data (by simp [Layout.regions])).2
  have hlt : r.lo + k < 2 ^ 64 := by
    rcases hr with h | h <;> unfold Range.Sub at h <;> omega
  have hn := hd.not_mem hwf hE (a := BitVec.ofNat 64 (r.lo + k)) (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rcases hr with h | h <;> unfold Range.Sub at h
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr ⟨by omega, by omega⟩)
  have h0 : (K.dmem s)[BitVec.ofNat 64 (r.lo + k)]? = none := Std.ExtHashMap.getElem?_eq_none hn
  simp [Mem.loadBytes, List.allSome, h0]

/-- **The byte `b + k` of a placed label is not a private byte**
(`MemRel.lbl_range`). -/
theorem PrivKeys.hpriv {Λ : Layout} {Ent : Entry} {s : I.State} (hd : PrivKeys K Λ Ent s)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Memory} {sm : WeakMem.Memory} {pairs : List Nat} (hm : MemRel Λ lbl lsize ts tm sm pairs)
    {l : WeakMem.AllocLabel} {b k : Nat} (hl : lbl l = some b) (hk : k < 8 * lsize l) (x : UInt8) :
    (K.dmem s).loadBytes (BitVec.ofNat 64 (b + k)) 1 ≠ some [x] :=
  hd.hpriv_of_range hwf hE (r := lrange lsize l b) (hm.lbl_range l b hl).2 hk x

/-! ## The word-level form

`PrivKeys` speaks of keys, bytes: a frame condition of that form is not
kept by a frame step (`DFrame` keeps 8-byte loads, and a lone byte changes
none; `Spike/Lib/PrivByteVacuous.lean`). The consumers' frame conditions
take its word-level consequence, `WordsNone`. -/

/-- **A word inside a range**: its eight bytes `a … a + 7`. -/
def WordIn (r : Range) (a : Nat) : Prop := r.contains a ∧ r.contains (a + 7)

/-- **No word of the heap or the static image loads** from `d`: none whose
eight bytes lie inside the heap or inside the image. -/
def WordsNone (Λ : Layout) (d : _root_.Mem 64) : Prop :=
  ∀ a : BitVec 64, (WordIn Λ.heap a.toNat ∨ WordIn Λ.data a.toNat) → Mem.loadInt d a 8 = none

/-- **A memory whose keys are private loads no word of the heap or the
static image**: the word's first byte is not a key. -/
theorem wordsNone_of_keys {Λ : Layout} {Ent : Entry} {d : _root_.Mem 64}
    (hd : ∀ a, a ∈ d → Ent.stack.contains a.toNat ∨ Λ.stackPool.contains a.toNat)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) : WordsNone Λ d := by
  intro a ha
  replace ha := ha.imp And.left And.left
  have hn : a ∉ d := by
    intro hm
    have hs := (Entry.clear_disjoint hE).2
    have hhs := hs Λ.heap (by simp [Layout.regions])
    have hds := hs Λ.data (by simp [Layout.regions])
    obtain ⟨-, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
    unfold Range.Disjoint at hhs hds hdp hhp
    rcases hd a hm with h | h <;> rcases ha with h' | h' <;> unfold Range.contains at h h' <;> omega
  have h0 : d[a]? = none := Std.ExtHashMap.getElem?_eq_none hn
  simp [Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ_eq_map, h0]

/-- **`PrivKeys` gives `WordsNone`.** -/
theorem PrivKeys.wordsNone {Λ : Layout} {Ent : Entry} {s : I.State} (hd : PrivKeys K Λ Ent s)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) : WordsNone Λ (K.dmem s) :=
  wordsNone_of_keys hd hwf hE

/-- **A range inside the entry stack or the stack pool is off the heap and
the static image** (a frame region's cells, for `FStable` of `WordsNone`). -/
theorem disjoint_of_sub {Λ : Layout} {Ent : Entry} (hwf : Λ.WF) (hE : Ent.clear Λ = true) {r : Range}
    (hS : r.Sub Ent.stack ∨ r.Sub Λ.stackPool) : r.Disjoint Λ.heap ∧ r.Disjoint Λ.data := by
  have hs := (Entry.clear_disjoint hE).2
  have hhs := hs Λ.heap (by simp [Layout.regions])
  have hds := hs Λ.data (by simp [Layout.regions])
  obtain ⟨-, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  unfold Range.Disjoint at *
  unfold Range.Sub at hS
  constructor <;> omega

end Spike.Lib.DmemPriv
