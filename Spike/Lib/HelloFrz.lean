/-
**hello.w: the frozen buffer after the spawn** (the memory
side; ISA-generic). The setup publishes the two words of `rodata`'s buffer
(`newBuf`) before the `clone`; after it neither thread writes them, so

* on the source, each word's latest message stays the one the setup
  published: premise `hM` of `HelloPrintSrcPub.loadCP_byte_i`;
* on the target, the kernel's read of a byte of the worker's `write(1, buf,
  n)` (`Kernel.readByte` at thread 1's views) is the byte of that message's
  number.

`Inv2Core` (`Spike/Lib/Inv2Core.lean`) carries the location half for any
frozen word (`frzS`, `frzT`: no message to it after the spawn; `frz_cov`,
`cov1`: thread 1's coherence covers it). The value half is `FrzBuf`, a
predicate of the source memory alone: carried as a conjunct of hello's
`Prot` argument of `Inv2` (`fun … sm … => HelloProt … ∧ FrzBuf R.S l w 2
sm`), kept by every source step of either thread (`FrzBuf.mono`: the memory
only grows, `TermCert.MemExt`) and established at the spawn (`frzBuf_start`).

- `FrzWord S sm sa v`, `FrzBuf S l w N sm`: below the spawn's source size
  `S`, the latest message to `sa` (to `⟨l, i⟩`, `i < N`) holds `.num v`
  (`.num (w i)`).
- `FrzWord.mono`, `FrzBuf.mono`, `FrzBuf.push`: kept as the memory grows.
- `frzWord_start`, `frzBuf_start`: from the latest messages at `S =
  sm.size`.
- `slatest_of_frzWord`, `slatest_frzBuf`, `hM_frz`: with `Inv2Core.frzS`,
  the latest message to a frozen buffer word holds its value (`hM_frz`:
  `loadCP_byte_i`'s `hM` at the byte `k`).
- `readByte_cohL`, `readByte_tlatestL`: `Scc.Sem.readByte_cohP`,
  `readByte_tlatestP` under the location-restricted cover
  (`Inv2Core.CohCoversL`).
- `frz_tlatest`: the latest write to a frozen word that thread 1 has not
  promised is no promise of either thread, and none follows it.
- `latest_frz`: `MemRelP.latestP` for a word with no later target write,
  from `MemRel.SLatest` (no source-promise premise).
- `FrzBufL`, `FrzBufL.mono`, `frzBufL_start`, `slatest_lt_frzBufL`, `hRd_frz`, `hRd_frzI`:
  with the latest messages strictly below `S - 1` (before the box's `new`),
  a buffer read's `pairTop` and view are at most `S - 1` (`hRd`,
  C4's certification inside the print).
- `readByte_frz`: **the kernel's read at thread 1 of a byte of a frozen
  word** is the byte of the number the source's latest message there holds;
  thread 1's promises and cover kept.

**The instance's premise** (B8): hello's `Inv2Params` must put both words
`⟨l, 0⟩`, `⟨l, 1⟩` of `newBuf` in `frzS` and their target words
`wordLoc (b0 + 8 i)` in `frz`, place `newBuf` at the spawn
(`R.lbl l = some b0`) with `lsize l ≥ 2`, and keep it apart from the label
of `c`. Non-vacuity of `FrzBuf` at the spawn (`frzBuf_start`) needs the
source fact that the latest message to `⟨l, i⟩`, `i < 2`, holds `.num (w i)`
at the clone (through `ClonePreH`).
-/
import Spike.Lib.Inv2CohL
import Scc.Sem.RowsSrc
import WeakCore.TermCert
import WeakCore.TermViewInv

namespace Spike.Lib.HelloFrz

open Kraken.Promising Scc.Sem Spike.Lib.Inv2Core
open Scc.Sem.MemRel (SLatest)

/-! ## The frozen words' values (source) -/

/-- **A frozen word's value at the spawn**: the source memory has at least
`S` messages, and the latest message to `sa` below `S` holds `.num v`. -/
def FrzWord (S : Nat) (sm : WeakMem.Memory) (sa : WeakMem.Address) (v : Nat) : Prop :=
  S ≤ sm.size ∧ ∃ j m, j < S ∧ sm[j]? = some m ∧ m.loc = sa ∧ m.val = .num v ∧
    ∀ k m', j < k → k < S → sm[k]? = some m' → m'.loc ≠ sa

/-- **The frozen buffer**: the words `⟨l, i⟩`, `i < N`, hold `w i` at the
spawn. -/
def FrzBuf (S : Nat) (l : WeakMem.AllocLabel) (w : Nat → Nat) (N : Nat) (sm : WeakMem.Memory) : Prop :=
  ∀ i < N, FrzWord S sm ⟨l, i⟩ (w i)

/-- `FrzWord` is kept as the memory grows. -/
theorem FrzWord.mono {S : Nat} {sm sm' : WeakMem.Memory} {sa : WeakMem.Address} {v : Nat}
    (h : FrzWord S sm sa v) (he : TermCert.MemExt sm sm') : FrzWord S sm' sa v := by
  obtain ⟨hS, j, m, hjS, hm, hl, hv, hn⟩ := h
  refine ⟨Nat.le_trans hS (TermFul.memExt_size he), j, m, hjS, he j m hm, hl, hv, fun k m' hjk hkS hk' => ?_⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, sm[k]? = some m2 := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have h2 := he k m2 hm2
  rw [hk'] at h2
  obtain rfl := Option.some.inj h2
  exact hn k m' hjk hkS hm2

/-- **`FrzBuf` is kept by every source step** (of either thread): the
memory only grows. -/
theorem FrzBuf.mono {S : Nat} {l : WeakMem.AllocLabel} {w : Nat → Nat} {N : Nat} {sm sm' : WeakMem.Memory}
    (h : FrzBuf S l w N sm) (he : TermCert.MemExt sm sm') : FrzBuf S l w N sm' :=
  fun i hi => (h i hi).mono he

/-- `FrzBuf` is kept by an append. -/
theorem FrzBuf.push {S : Nat} {l : WeakMem.AllocLabel} {w : Nat → Nat} {N : Nat} {sm : WeakMem.Memory}
    (h : FrzBuf S l w N sm) (m : WeakMem.Msg) : FrzBuf S l w N (sm.push m) :=
  h.mono (TermCert.MemExt.push sm m)

/-- **A word's value at the spawn** from its latest message there (`S =
sm.size`). -/
theorem frzWord_start {sm : WeakMem.Memory} {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg} {v : Nat}
    (hj : SLatest sm sa j) (hm : sm[j]? = some m) (hv : m.val = .num v) : FrzWord sm.size sm sa v := by
  obtain ⟨⟨m0, hm0, hl⟩, hn⟩ := hj
  rw [hm] at hm0
  obtain rfl := Option.some.inj hm0
  exact ⟨Nat.le_refl _, j, m, (Array.getElem?_eq_some_iff.mp hm).1, hm, hl, hv,
    fun k m' hjk _ hk => hn k m' hjk hk⟩

/-- **The frozen buffer at the spawn** (`S = sm.size`): each word
`⟨l, i⟩`, `i < N`, has a latest message holding `.num (w i)`. -/
theorem frzBuf_start {sm : WeakMem.Memory} {l : WeakMem.AllocLabel} {w : Nat → Nat} {N : Nat}
    (h : ∀ i < N, ∃ j m, SLatest sm ⟨l, i⟩ j ∧ sm[j]? = some m ∧ m.val = .num (w i)) :
    FrzBuf sm.size l w N sm := fun i hi =>
  let ⟨_, _, hj, hm, hv⟩ := h i hi
  frzWord_start hj hm hv

/-- **The latest message to a frozen word** holds its value at the spawn,
when no message after the spawn is to a frozen word (`Inv2Core.frzS`). -/
theorem slatest_of_frzWord {S : Nat} {frzS : WeakMem.Address → Prop} {sm : WeakMem.Memory}
    {sa : WeakMem.Address} {v : Nat} (h : FrzWord S sm sa v)
    (hfS : ∀ k m, sm[k]? = some m → S ≤ k → ¬ frzS m.loc) (hf : frzS sa) :
    ∃ j msg, SLatest sm sa j ∧ sm[j]? = some msg ∧ msg.val = .num v := by
  obtain ⟨-, j, m, hjS, hm, hl, hv, hn⟩ := h
  refine ⟨j, m, ⟨⟨m, hm, hl⟩, fun k m' hjk hk hl' => ?_⟩, hm, hv⟩
  rcases Nat.lt_or_ge k S with hkS | hkS
  · exact hn k m' hjk hkS hk hl'
  · exact hfS k m' hk hkS (hl' ▸ hf)

/-! ## Strictly below the spawn (the buffer reads' views) -/

/-- **`FrzBuf` with each word's latest message strictly below `S - 1`**
(`j + 1 < S`: rodata's stores come before the box's `new`, the last
message before the spawn). -/
def FrzBufL (S : Nat) (l : WeakMem.AllocLabel) (w : Nat → Nat) (N : Nat) (sm : WeakMem.Memory) : Prop :=
  FrzBuf S l w N sm ∧ ∀ i < N, ∀ j m, j < S → sm[j]? = some m → m.loc = ⟨l, i⟩ →
    (∀ k m', j < k → k < S → sm[k]? = some m' → m'.loc ≠ ⟨l, i⟩) → j + 1 < S

/-- `FrzBufL` is kept as the memory grows. -/
theorem FrzBufL.mono {S : Nat} {l : WeakMem.AllocLabel} {w : Nat → Nat} {N : Nat} {sm sm' : WeakMem.Memory}
    (h : FrzBufL S l w N sm) (he : TermCert.MemExt sm sm') : FrzBufL S l w N sm' := by
  refine ⟨h.1.mono he, fun i hi j m hjS hm hl hn => h.2 i hi j m hjS ?_ hl fun k m' hjk hkS hk => ?_⟩
  · obtain ⟨S1, -⟩ := h.1 i hi
    obtain ⟨m2, hm2⟩ : ∃ m2, sm[j]? = some m2 := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    have h2 := he j m2 hm2
    rw [hm] at h2; rw [hm2, ← h2]
  · exact hn k m' hjk hkS (he k m' hk)

/-- **`FrzBufL` at the spawn** (`S = sm.size`): each word `⟨l, i⟩`, `i < N`,
has a latest message holding `.num (w i)`, not the last message. -/
theorem frzBufL_start {sm : WeakMem.Memory} {l : WeakMem.AllocLabel} {w : Nat → Nat} {N : Nat}
    (h : ∀ i < N, ∃ j m, SLatest sm ⟨l, i⟩ j ∧ sm[j]? = some m ∧ m.val = .num (w i) ∧ j + 1 < sm.size) :
    FrzBufL sm.size l w N sm := by
  refine ⟨frzBuf_start fun i hi => let ⟨j, m, hj, hm, hv, _⟩ := h i hi; ⟨j, m, hj, hm, hv⟩,
    fun i hi j m _ hm hl hn => ?_⟩
  obtain ⟨j0, m0, ⟨⟨m1, hm1, hl1⟩, hn0⟩, -, -, hlt⟩ := h i hi
  rcases Nat.lt_trichotomy j j0 with hjj | rfl | hjj
  · exact absurd hl1 (hn j0 m1 hjj (Array.getElem?_eq_some_iff.mp hm1).1 hm1)
  · exact hlt
  · exact absurd hl (hn0 j m hjj hm)

/-- **The latest message to a frozen word is strictly below `S - 1`**
when no message from `S` on is to a frozen word. -/
theorem slatest_lt_frzBufL {frzS : WeakMem.Address → Prop} {S : Nat} {l : WeakMem.AllocLabel}
    {w : Nat → Nat} {N : Nat} {sm : WeakMem.Memory} (hb : FrzBufL S l w N sm)
    (hfS : ∀ k m, sm[k]? = some m → S ≤ k → ¬ frzS m.loc) {i : Nat} (hi : i < N) (hf : frzS ⟨l, i⟩)
    {j : Nat} {msg : WeakMem.Msg} (hj : SLatest sm ⟨l, i⟩ j) (hm : sm[j]? = some msg) : j + 1 < S := by
  obtain ⟨⟨m0, hm0, hl⟩, hn⟩ := hj
  rw [hm] at hm0; obtain rfl := Option.some.inj hm0
  have hjS : j < S := Nat.lt_of_not_ge fun hjS => hfS j msg hm hjS (hl ▸ hf)
  exact hb.2 i hi j msg hjS hm hl fun k m' hjk _ hk => hn k m' hjk hk

/-- **The buffer reads' bound** (`hRd` for C4): the latest message
to a frozen buffer word `⟨l, i⟩` has its `pairTop` and its view at most
`S - 1` (`TermViewInv.MsgV`: a message's view is at most its index). -/
theorem hRd_frz {frzS : WeakMem.Address → Prop} {S : Nat} {l : WeakMem.AllocLabel}
    {w : Nat → Nat} {N : Nat} {sm : WeakMem.Memory} (hb : FrzBufL S l w N sm)
    (hfS : ∀ k m, sm[k]? = some m → S ≤ k → ¬ frzS m.loc) (hmv : TermViewInv.MsgV sm)
    {i : Nat} (hi : i < N) (hf : frzS ⟨l, i⟩) (pairs : List Nat) :
    ∀ j msg, SLatest sm ⟨l, i⟩ j → sm[j]? = some msg →
      Promises.pairTop pairs j ≤ S - 1 ∧ msg.view ≤ S - 1 := by
  intro j msg hj hm
  have hlt := slatest_lt_frzBufL hb hfS hi hf hj hm
  have h1 := TermViewInv.pairTop_le' pairs j
  have h2 := hmv j msg hm
  exact ⟨Nat.le_trans h1 (by omega), Nat.le_trans h2 (by omega)⟩

section Inv2

variable {I : ISA} {Λ : Layout} {R : SpawnRec} {P : Inv2Params I} {G : Loc → Val → Prop}
  {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {sm : WeakMem.Memory}
  {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- **The frozen buffer's words under the two-thread relation**: the latest
source message to a frozen word `⟨l, i⟩` holds `w i`. -/
theorem slatest_frzBuf (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {l : WeakMem.AllocLabel}
    {w : Nat → Nat} {N : Nat} (hb : FrzBuf R.S l w N sm) {i : Nat} (hi : i < N) (hf : P.frzS ⟨l, i⟩) :
    ∃ j msg, SLatest sm ⟨l, i⟩ j ∧ sm[j]? = some msg ∧ msg.val = .num (w i) :=
  slatest_of_frzWord (hb i hi) h.frzS hf

/-- **`HelloPrintSrcPub.loadCP_byte_i`'s `hM`** at the byte `k` of the
frozen buffer: `slatest_frzBuf` at the word `k / 8`. -/
theorem hM_frz (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {l : WeakMem.AllocLabel}
    {w : Nat → Nat} {N : Nat} (hb : FrzBuf R.S l w N sm) {k : Nat} (hk : k / 8 < N) (hf : P.frzS ⟨l, k / 8⟩) :
    ∃ j msg, SLatest sm ⟨l, k / 8⟩ j ∧ sm[j]? = some msg ∧ msg.val = .num (w (k / 8)) :=
  slatest_frzBuf h hb hk hf

/-- **`hRd_frz` under the two-thread relation** (`Inv2Core.frzS`). -/
theorem hRd_frzI (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {l : WeakMem.AllocLabel}
    {w : Nat → Nat} {N : Nat} (hb : FrzBufL R.S l w N sm) (hmv : TermViewInv.MsgV sm) {i : Nat} (hi : i < N)
    (hf : P.frzS ⟨l, i⟩) (pairs : List Nat) :
    ∀ j msg, SLatest sm ⟨l, i⟩ j → sm[j]? = some msg →
      Promises.pairTop pairs j ≤ R.S - 1 ∧ msg.view ≤ R.S - 1 :=
  hRd_frz hb h.frzS hmv hi hf pairs

end Inv2

/-! ## The kernel's byte read under the restricted cover (target) -/

section KernelByte

variable {I : ISA} {K : Kernel.Abi I}

/-- **The kernel's byte read keeps the restricted cover** (`readByte_cohP`'s
proof). -/
theorem readByte_cohL {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256} {L : Loc → Prop}
    (h : Kernel.readByte K A t mem a rd = some (b, t')) (hc : CohCoversL t.views t.prom mem L) :
    CohCoversL t'.views t'.prom mem L := by
  rw [Kernel.readByte_prom h]
  unfold Kernel.readByte at h
  split at h
  · cases h; exact hc
  · split at h
    · rename_i x v c' hx
      cases h
      have hm := List.mem_of_getElem? hx
      obtain ⟨-, -, -, he⟩ := readSuccs_shape A _ hm
      refine hc.mono' fun l => ?_
      have hv := congrArg (fun c : Ctx => c.views.getCoh l) he
      simp only at hv
      show t.views.getCoh l ≤ c'.views.getCoh l
      rw [hv]; exact getCoh_le_setCoh _ _ _ _
    · cases h

/-- **The kernel's byte read of shared memory is of the latest write not
promised** of a word in the restricted cover (`readByte_tlatestP`'s
proof, `readSuccs_tlatestL`). -/
theorem readByte_tlatestL {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    {L : Loc → Prop} (h : Kernel.readByte K A t mem a rd = some (b, t')) (hc : CohCoversL t.views t.prom mem L)
    (hL : L (wordLoc (a - a % 8))) :
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
      obtain ⟨hl, hv⟩ := readSuccs_tlatestL A _ L (a := a - a % 8) hm hc hL
      exact .inr ⟨x, v, hl, hv, rfl⟩
    · cases h

end KernelByte

/-! ## The latest write of a frozen word -/

section Latest

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}

/-- **`MemRelP.latestP` for a word with no later target write** (`hno`),
from the source's latest message (`MemRel.SLatest`, whatever the source
promises): the latest source message's image is the target's latest write
there and represents its value. (`latestP` asks `j ∉ sp` only to place the
image of `j` at or before `k'` when a later target write is a mirrored
promise; with no later write the image is at or before `k'` outright.) -/
theorem latest_frz (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hn : MemRel.Narrow tm)
    {sa : WeakMem.Address} {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatest sm sa j)
    (hk : TLatestP tm (tp ++ tq) a k')
    (hno : ∀ k'' w, k' < k'' → tm.get? k'' = some w → w.loc = wordLoc a → False) :
    ts j = some k' ∧ ∃ m v, sm[j]? = some m ∧ wordAt tm a k' = some v ∧ ValRep lbl m.val v := by
  obtain ⟨⟨m, hm, hml⟩, hjl⟩ := hj
  obtain ⟨kj, a', v, hts, ha', hw, hv⟩ := h.mem_rep j m hm
  rw [hml, ha] at ha'; cases ha'
  have hoa : sa.offset < lsize sa.label := by
    obtain ⟨b, -, hb⟩ := h.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm)); rw [← hml]; exact hb
  have hal := h.addr_lt hwf ha hoa
  -- the image of `j` is at most `k'`: there is no later write there
  have hle : kj ≤ k' := by
    rcases Nat.eq_zero_or_pos kj with rfl | hpos
    · exact Nat.zero_le _
    · obtain ⟨w, hg, hwl, -⟩ := MemRel.wordAt_msg hn hpos hw
      rcases Nat.lt_or_ge k' kj with hlt | hge
      · exact (hno kj w hlt hg hwl).elim
      · exact hge
  have heq : kj = k' := by
    rcases hk.1 with rfl | ⟨w, hg, hwl, hkp⟩
    · omega
    · have hkpos : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with rfl | hp
        · simp [Memory.get?] at hg
        · exact hp
      have hin : ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains w.loc.addr.toNat := by
        simp only [wordAddr, Option.map_eq_some_iff] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        refine ⟨sa.label, b, hb, ?_⟩
        rw [hwl]
        simp only [lrange, Range.contains, wordLoc, BitVec.toNat_ofNat, mul_offset]
        have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := hoa
        rw [mul_offset] at hal
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      obtain ⟨k2, hk2, ht2⟩ := (h.mem_onto k' w hg hin).resolve_right
        fun hq => hkp (List.mem_append_right _ hq)
      obtain ⟨m2, hm2⟩ : ∃ m2, sm[k2]? = some m2 := ⟨_, Array.getElem?_eq_getElem hk2⟩
      obtain ⟨k2', x, v2, ht2', hx, hw2, -⟩ := h.mem_rep k2 m2 hm2
      rw [ht2] at ht2'; cases ht2'
      obtain ⟨w', hg', hwl', -⟩ := MemRel.wordAt_msg hn hkpos hw2
      rw [hg] at hg'; cases hg'
      have ho2 : m2.loc.offset < lsize m2.loc.label := by
        obtain ⟨b, -, hb⟩ := h.lbl_mem m2 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm2)); exact hb
      have hxl := h.addr_lt hwf hx ho2
      have hxa : x = a := MemRel.wordLoc_inj (by omega) (by omega) (hwl'.symm.trans hwl)
      subst hxa
      have hloc : m2.loc = sa := h.wordAddr_inj hx ha ho2 hoa
      rcases Nat.lt_trichotomy k2 j with hlt | rfl | hgt
      · rcases Nat.eq_zero_or_pos kj with rfl | hpos
        · exact absurd hloc (by rw [← hml]; exact h.ts_first j m hm hts k2 m2 hlt hm2)
        · have := h.ts_mono k2 j k' kj m2 m hm2 hm (hloc.trans hml.symm) ht2 hts hkpos hpos hlt
          omega
      · rw [hts] at ht2; cases ht2; rfl
      · exact absurd hloc (hjl k2 m2 hgt hm2)
  subst heq
  exact ⟨hts, m, v, hm, hw, hv⟩

end Latest

/-! ## The kernel's read of the frozen buffer at thread 1 -/

section Read

variable {I : ISA} {Λ : Layout} {R : SpawnRec} {P : Inv2Params I} {G : Loc → Val → Prop}
  {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {sm : WeakMem.Memory}
  {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- **The latest write to a frozen word that thread 1 has not promised**
is no promise of either thread (`tp`), and no write follows it: every write
after the spawn is to an unfrozen word (`frzT`) and every promise is after
the spawn (`prom0`, `prom1`). -/
theorem frz_tlatest (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {a k' : Nat}
    (hk : TLatestP tm t1.prom a k') (hf : P.frz (wordLoc a)) :
    TLatestP tm (tp ++ []) a k' ∧ ∀ k'' w, k' < k'' → tm.get? k'' = some w → w.loc = wordLoc a → False := by
  have hno : ∀ k'' w, k' < k'' → tm.get? k'' = some w → w.loc = wordLoc a → False := fun k'' w hlt hg hl =>
    h.frzT k'' w hg (h.prom1 k'' (hk.2 k'' w hlt hg hl)).1 (hl ▸ hf)
  refine ⟨⟨?_, fun k'' w hlt hg hl => (hno k'' w hlt hg hl).elim⟩, hno⟩
  rcases hk.1 with h0 | ⟨w, hg, hl, -⟩
  · exact .inl h0
  · refine .inr ⟨w, hg, hl, fun hp => ?_⟩
    have hT : R.T < k' := by
      rcases h.tp_prom k' (by simpa using hp) with h0 | h1
      · exact (h.prom0 k' h0).1
      · exact (h.prom1 k' h1).1
    exact h.frzT k' w hg hT (hl ▸ hf)

/-- **The kernel's read at thread 1 of a byte of a frozen word**: the byte
`a`, not in thread 1's private memory (`hpriv`), of the frozen word at
`a - a % 8` (`hf`) placed for the source address `sa` (`ha`) whose latest
source message `j` holds the number `n`: the byte is lane `a % 8` of width 8
of `n`; thread 1's promises and its cover are kept. -/
theorem readByte_frz (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) (hwf : Λ.WF)
    {K : Kernel.Abi I} {A : Arch} {t1' : Thread I} {a rd : Nat} {b : Fin 256}
    (hb : Kernel.readByte K A t1 tm a rd = some (b, t1'))
    (hpriv : ∀ x, (K.dmem t1.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x])
    (hf : P.frz (wordLoc (a - a % 8))) {sa : WeakMem.Address} {j : Nat}
    (ha : wordAddr R.lbl sa = some (a - a % 8)) (hj : SLatest sm sa j)
    {m : WeakMem.Msg} (hm : sm[j]? = some m) {n : Nat} (hmv : m.val = .num n) :
    b.val = TermRun.laneN .w8 n (a % 8) ∧ t1'.prom = t1.prom ∧ CohCoversL t1'.views t1'.prom tm (P.cov 1) := by
  have hL : P.cov 1 (wordLoc (a - a % 8)) := h.frz_cov 1 _ (by decide) hf
  refine ⟨?_, Kernel.readByte_prom hb, readByte_cohL hb h.cov1⟩
  rcases readByte_tlatestL hb h.cov1 hL with ⟨-, x, hx⟩ | ⟨k', v, hk, hr, rfl⟩
  · exact absurd hx (hpriv x)
  · obtain ⟨hk', hno⟩ := frz_tlatest h hk hf
    obtain ⟨-, m', v', hm', hw, hv⟩ := latest_frz h.mem hwf h.narrow ha hj hk' hno
    rw [wordAt_of_read hr] at hw
    obtain rfl := Option.some.inj hw
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    rw [hmv] at hv
    exact byteOf_laneN hv.2 _

end Read

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.HelloFrz.hM_frz' does not depend on any axioms -/
#guard_msgs in #print axioms hM_frz

/-- info: 'Spike.Lib.HelloFrz.readByte_frz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readByte_frz

/-- info: 'Spike.Lib.HelloFrz.hRd_frzI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hRd_frzI

end Spike.Lib.HelloFrz
