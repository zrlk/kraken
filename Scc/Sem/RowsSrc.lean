/-
**The source side of the one-thread memory rows** (`Scc/DESIGN.md` §9.0,
"Never-mirror for M1"): the source steps of WeakCore's promise machine that
the target rows of `Scc/Sem/Rows1.lean` pair with, one word, one thread.

Under never-mirror the source thread makes no promise, so its store always
appends, and its load can always read the latest message to the address:

- `stepStore_append`: `Promises.stepStore` can append, whatever the thread's
  promises;
- `stepStore_noProm`: with no promise, appending is all it can do;
- `stepLoad_latest`: `Promises.stepLoad` can read the latest message to the
  address (`MemRel.readable_latest`), whatever the read bound;
- `Inv1.store_src`: a target store and a promise-free source store keep
  `Inv1`, for every source outcome;
- `Inv1.load_src`: a target load and the source load of the latest message:
  the source has an outcome reading it, and the target's value represents
  it;
- `wordAddr_of_valRep_loc0`, `wordLoc_toNat`: from an untagged locative
  the target address represents to the word the rows take;
- `readByte_cohP`, `readByte_tlatestP`: the kernel's byte read of a `write`
  buffer keeps the cover and reads the latest unpromised write of the word,
  with promises (`Scc/Sem/Coh.lean` `readByte_coh`, `readByte_tlatest`);
- `byteOf_laneN`, `MemRelP.latestP_byte`: a byte of a word holding a number
  is WeakCore's 8-bit lane of it;
- `Inv1.readByte`, `Inv1.readByte_src`, `Inv1.readByte_src_num`: the
  kernel's byte read keeps `Inv1`, and the byte it reads is the byte of the
  source's latest message to the cell.

Not here: the lift through `TermRun.storeUnits`/`loadUnits` and the `Out`
rows of `Spike/Lib/Seg.lean`.
-/
import Scc.Sem.Rows1

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **A source store can always append** the message of its value and view
at `mem.size`. -/
theorem stepStore_append (k : Promises.Knobs) (arch : WeakMem.Arch) (mem : WeakMem.Memory) (th : Promises.Thread)
    (a : WeakMem.Address) (e : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    ∃ th', (mem.push ⟨a, Promises.rmwNewVal th.regs e, Promises.storeMview th e deps rel⟩, th') ∈
      Promises.stepStore k arch mem th a e deps rel := by
  cases e <;> exact ⟨_, List.mem_append_left _ (List.mem_singleton.mpr rfl)⟩

/-- **A promise-free source store only appends.** -/
theorem stepStore_noProm {k : Promises.Knobs} {arch : WeakMem.Arch} {mem : WeakMem.Memory} {th : Promises.Thread}
    {a : WeakMem.Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} (hp : th.promises = [])
    {x : WeakMem.Memory × Promises.Thread} (hx : x ∈ Promises.stepStore k arch mem th a e deps rel) :
    x.1 = mem.push ⟨a, Promises.rmwNewVal th.regs e, Promises.storeMview th e deps rel⟩ ∧ x.2.promises = [] := by
  unfold Promises.stepStore at hx
  simp only [hp, List.filterMap_nil, List.append_nil, List.mem_singleton] at hx
  subst hx
  exact ⟨by cases e <;> rfl, rfl⟩

/-- **A source load can always read the latest message** to its address:
the outcome whose destination register holds that message's value, view
and timestamp. -/
theorem stepLoad_latest (arch : WeakMem.Arch) {mem : WeakMem.Memory} (pairs : List Nat) (th : Promises.Thread)
    (dst : WeakMem.Reg) {a : WeakMem.Address} (deps : List WeakMem.Reg) (acq : Bool) {j : Nat}
    (hj : MemRel.SLatest mem a j) {m : WeakMem.Msg} (hm : mem[j]? = some m) :
    ∃ th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq, th'.regs dst = ⟨m.val, m.view, j⟩ := by
  have hjs : j < mem.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hmj : mem[j]! = m := by
    rw [getElem!_pos mem j hjs]; exact (Array.getElem?_eq_some_iff.mp hm).2
  refine ⟨_, List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hjs, MemRel.readable_latest hj⟩, rfl⟩, ?_⟩
  simp [hmj]

/-- **An untagged locative's word**: a target word representing `.loc sa 0`
is the word address of `sa`. -/
theorem wordAddr_of_valRep_loc0 {lbl : WeakMem.AllocLabel → Option Nat} {sa : WeakMem.Address} {v : Nat}
    (h : ValRep lbl (.loc sa 0) v) : wordAddr lbl sa = some v := by
  obtain ⟨-, x, hx, rfl⟩ := h
  simpa using hx

/-- The 8-byte location of a 64-bit address is the word location of its
value. -/
theorem wordLoc_toNat (A : BitVec 64) : wordLoc A.toNat = ⟨A, 8⟩ := by
  simp [wordLoc]

/-! ## The kernel's byte read of a `write` buffer -/

section KernelByte

variable {I : ISA} {K : Kernel.Abi I}

/-- **The kernel's byte read keeps the cover with promises** (it is a plain
load, or reads private memory). -/
theorem readByte_cohP {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : Kernel.readByte K A t mem a rd = some (b, t')) (hc : CohCoversP t.views t.prom mem) :
    CohCoversP t'.views t'.prom mem := by
  rw [Kernel.readByte_prom h]
  unfold Kernel.readByte at h
  split at h
  · cases h; exact hc
  · split at h
    · rename_i x v c' hx
      cases h
      have hm := List.mem_of_getElem? hx
      obtain ⟨-, -, -, he⟩ := readSuccs_shape A _ hm
      refine hc.mono fun l => ?_
      have hv := congrArg (fun c : Ctx => c.views.getCoh l) he
      simp only at hv
      show t.views.getCoh l ≤ c'.views.getCoh l
      rw [hv]; exact getCoh_le_setCoh _ _ _ _
    · cases h

/-- **The kernel's byte read of shared memory is of the latest write not
promised** (`Kernel.readByte_tlatest` with promises): unless the byte is in
the thread's private memory, it is byte `a % 8` of a value read at the
latest write of the word at `a - a % 8` that is not one of the thread's
promises. -/
theorem readByte_tlatestP {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : Kernel.readByte K A t mem a rd = some (b, t')) (hc : CohCoversP t.views t.prom mem) :
    (t' = t ∧ ∃ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 = some [x]) ∨
      ∃ ts v, TLatestP mem t.prom (a - a % 8) ts ∧ mem.read? (wordLoc (a - a % 8)) ts = some v ∧
        b = Kernel.byteOf v (a % 8) := by
  unfold Kernel.readByte at h
  split at h
  · rename_i x hx; cases h; exact .inl ⟨rfl, x, hx⟩
  · split at h
    · rename_i x v c' hx
      cases h
      have hm := List.mem_of_getElem? hx
      obtain ⟨hl, hv⟩ := readSuccs_tlatestP A _ (a := a - a % 8) hm hc
      exact .inr ⟨x, v, hl, hv, rfl⟩
    · cases h

end KernelByte

/-- **A byte of a number's word is its 8-bit lane**: the kernel's byte `i`
of a word holding `n` is WeakCore's lane `i` of width 8 of `n`. -/
theorem byteOf_laneN {n : Nat} {v : Val} (hv : v.toNat = n) (i : Nat) :
    (Kernel.byteOf v i).val = TermRun.laneN .w8 n i := by
  subst hv
  simp [Kernel.byteOf, TermRun.laneN, TermRun.fmask, TermRun.pw2, CoreLang.Wd.bits]

namespace MemRelP

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq : List Time} {sp : List Nat}

/-- **The byte side of `latestP`**: if the target reads `val` at the latest
unpromised write of the word `a` placed for `sa`, and the source's latest
unpromised message to `sa` holds the number `n`, then byte `i` of `val` is
lane `i` of width 8 of `n`. -/
theorem latestP_byte (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hn : MemRel.Narrow tm)
    {sa : WeakMem.Address} {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatestP sm sp sa j)
    (hk : TLatestP tm (tp ++ tq) a k') {val : Val} (hr : tm.read? (wordLoc a) k' = some val)
    {m : WeakMem.Msg} (hm : sm[j]? = some m) {n : Nat} (hmv : m.val = .num n) (i : Nat) :
    (Kernel.byteOf val i).val = TermRun.laneN .w8 n i := by
  obtain ⟨m', hm', hv⟩ := h.latestP_read hwf hn ha hj hk hr
  rw [hm] at hm'; cases hm'
  rw [hmv] at hv
  exact byteOf_laneN hv.2 i

end MemRelP

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The store row, both sides**: a target store of `v` to the word `a`
placed for the source address `sa`, and any outcome of a promise-free
source store to `sa` of a value `v` represents: the invariant holds after
both, the source outcome having no promise. -/
theorem store_src (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {k : Promises.Knobs} {arch : WeakMem.Arch} {th : Promises.Thread} {sa : WeakMem.Address}
    {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} (hp : th.promises = [])
    (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    (hv : ValRep lbl (Promises.rmwNewVal th.regs e) v.toNat)
    {x : WeakMem.Memory × Promises.Thread} (hx : x ∈ Promises.stepStore k arch sm th sa e deps rel) :
    o.thread.st = s ∧ x.2.promises = [] ∧
      ∃ q, Inv1 Λ lbl lsize (fun k => if k = sm.size then some q else ts k) o.thread o.mem x.1 := by
  obtain ⟨hx1, hx2⟩ := stepStore_noProm hp hx
  obtain ⟨hst, q, hi⟩ := h.store A hex hstep ho (m := ⟨sa, _, Promises.storeMview th e deps rel⟩) ha hoff hv
  exact ⟨hst, hx2, q, hx1 ▸ hi⟩

/-- **The load row, both sides**: a target load of the word `a` placed for
the source address `sa`, whose latest source message is `j`: the source
load has an outcome reading `j`, and the target's value represents the
value read. -/
theorem load_src (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some a) (hj : MemRel.SLatest sm sa j)
    (arch : WeakMem.Arch) (pairs : List Nat) (th : Promises.Thread) (dst : WeakMem.Reg) (deps : List WeakMem.Reg)
    (acq : Bool) :
    o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm ∧
      ∃ v, o.thread.st = g v ∧ ∃ m th', sm[j]? = some m ∧ th' ∈ Promises.stepLoad arch sm pairs th dst sa deps acq ∧
        th'.regs dst = ⟨m.val, m.view, j⟩ ∧ ValRep lbl m.val v.toNat := by
  obtain ⟨hm, -, hi, v, hst, m, hmj, hv⟩ := h.load hwf A hex hstep ho ha hj
  obtain ⟨th', hth', hreg⟩ := stepLoad_latest arch pairs th dst deps acq hj hmj
  exact ⟨hm, hi, v, hst, m, th', hmj, hth', hreg, hv⟩

/-- **The kernel's byte read keeps the invariant**: it leaves memory and
promises alone and only raises coherence views. -/
theorem readByte {K : Kernel.Abi I} (h : Inv1 Λ lbl lsize ts t tm sm) {A : Arch} {t' : Thread I} {a rd : Nat}
    {b : Fin 256} (hb : Kernel.readByte K A t tm a rd = some (b, t')) : Inv1 Λ lbl lsize ts t' tm sm :=
  ⟨(Kernel.readByte_prom hb) ▸ h.mem, readByte_cohP hb h.coh, h.narrow⟩

/-- **The byte read of a `write` buffer, both sides**: the kernel's read of
byte `a`, outside the thread's private memory, of the word `a - a % 8`
placed for the source address `sa` whose latest source message is `j`:
the invariant holds after it, and the byte is byte `a % 8` of a value that
represents `j`'s. -/
theorem readByte_src {K : Kernel.Abi I} (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) {A : Arch}
    {t' : Thread I} {a rd : Nat} {b : Fin 256} (hb : Kernel.readByte K A t tm a rd = some (b, t'))
    (hpriv : ∀ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x])
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some (a - a % 8)) (hj : MemRel.SLatest sm sa j) :
    Inv1 Λ lbl lsize ts t' tm sm ∧
      ∃ m v, sm[j]? = some m ∧ ValRep lbl m.val v.toNat ∧ b = Kernel.byteOf v (a % 8) := by
  refine ⟨h.readByte hb, ?_⟩
  rcases readByte_tlatestP hb h.coh with ⟨-, x, hx⟩ | ⟨k', v, hk, hr, rfl⟩
  · exact absurd hx (hpriv x)
  · obtain ⟨m, hm, hv⟩ := h.mem.latestP_read hwf h.narrow ha (SLatestP.nil_iff.mpr hj) hk hr
    exact ⟨m, v, hm, hv, rfl⟩

/-- **`readByte_src` for a number**: when the source's latest message to
`sa` holds the number `n`, the kernel's byte is lane `a % 8` of width 8 of
`n`. -/
theorem readByte_src_num {K : Kernel.Abi I} (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) {A : Arch}
    {t' : Thread I} {a rd : Nat} {b : Fin 256} (hb : Kernel.readByte K A t tm a rd = some (b, t'))
    (hpriv : ∀ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x])
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some (a - a % 8)) (hj : MemRel.SLatest sm sa j)
    {m : WeakMem.Msg} (hm : sm[j]? = some m) {n : Nat} (hmv : m.val = .num n) :
    Inv1 Λ lbl lsize ts t' tm sm ∧ b.val = TermRun.laneN .w8 n (a % 8) := by
  obtain ⟨hi, m', v, hm', hv, rfl⟩ := h.readByte_src hwf hb hpriv ha hj
  rw [hm] at hm'; cases hm'
  rw [hmv] at hv
  exact ⟨hi, byteOf_laneN hv.2 _⟩

end Inv1

end Scc.Sem
